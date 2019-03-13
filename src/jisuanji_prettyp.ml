open Prettyp
   
(** ---------------------- INCLUDE COPY prettyp.ml ------------------------- **)

open Pp
open CErrors
open Util
open CAst
open Names
open Nameops
open Termops
open Declarations
open Environ
open Impargs
open Libobject
open Libnames
open Globnames
open Recordops
open Printer
open Jisuanji_printmod
open Context.Rel.Declaration

(* module RelDecl = Context.Rel.Declaration *)
module NamedDecl = Context.Named.Declaration

(**
type object_pr = {
  print_inductive           : MutInd.t -> UnivNames.univ_name_list option -> Pp.t;
  print_constant_with_infos : Constant.t -> UnivNames.univ_name_list option -> Pp.t;
  print_section_variable    : env -> Evd.evar_map -> variable -> Pp.t;
  print_syntactic_def       : env -> KerName.t -> Pp.t;
  print_module              : bool -> ModPath.t -> Pp.t;
  print_modtype             : ModPath.t -> Pp.t;
  print_named_decl          : env -> Evd.evar_map -> Constr.named_declaration -> Pp.t;
  print_library_entry       : env -> Evd.evar_map -> bool -> (object_name * Lib.node) -> Pp.t option;
  print_context             : env -> Evd.evar_map -> bool -> int option -> Lib.library_segment -> Pp.t;
  print_typed_value_in_env  : Environ.env -> Evd.evar_map -> EConstr.constr * EConstr.types -> Pp.t;
  print_eval                : Reductionops.reduction_function -> env -> Evd.evar_map -> Constrexpr.constr_expr -> EConstr.unsafe_judgment -> Pp.t;
}
**)
               
let gallina_print_module  = print_module
let gallina_print_modtype = print_modtype

(**************)
(** Utilities *)

let print_closed_sections = ref false

let pr_infos_list l = v 0 (prlist_with_sep cut (fun x -> x) l)

let with_line_skip l = if List.is_empty l then mt() else fnl() ++ fnl () ++ pr_infos_list l

let blankline = mt() (* add a blank sentence in the list of infos *)

let add_colon prefix = if ismt prefix then mt () else prefix ++ str ": "

let int_or_no n = if Int.equal n 0 then str "no" else int n

(*******************)
(** Basic printing *)

let print_basename sp = pr_global (ConstRef sp)

let print_ref reduce ref udecl =
  let env = Global.env () in
  let typ, univs = Typeops.type_of_global_in_context env ref in
  let inst = Univ.make_abstract_instance univs in
  let bl = UnivNames.universe_binders_with_opt_names (Environ.universes_of_global env ref) udecl in
  let sigma = Evd.from_ctx (UState.of_binders bl) in
  let typ = EConstr.of_constr typ in
  let typ =
    if reduce then
      let ctx,ccl = Reductionops.splay_prod_assum env sigma typ
      in EConstr.it_mkProd_or_LetIn ccl ctx
    else typ in
  let variance = match ref with
    | VarRef _ | ConstRef _ -> None
    | IndRef (ind,_) | ConstructRef ((ind,_),_) ->
      let mind = Environ.lookup_mind ind env in
      mind.Declarations.mind_variance
  in
  let inst =
    if Global.is_polymorphic ref
    then Printer.pr_universe_instance sigma inst
    else mt ()
  in
  let priv = None in (* We deliberately don't print private univs in About. *)
  hov 0 (pr_global ref ++ inst ++ str " :" ++ spc () ++ pr_letype_env env sigma typ ++ 
         Printer.pr_abstract_universe_ctx sigma ?variance univs ?priv)

(********************************)
(** Printing implicit arguments *)

let pr_impl_name imp = Id.print (name_of_implicit imp)

let print_impargs_by_name max = function
  | []  -> []
  | impls ->
     let n = List.length impls in
     [hov 0 (str (String.plural n "Argument") ++ spc() ++
      prlist_with_sep pr_comma pr_impl_name impls ++ spc() ++
      str (String.conjugate_verb_to_be n) ++ str" implicit" ++
      (if max then strbrk " and maximally inserted" else mt()))]

let print_one_impargs_list l =
  let imps = List.filter is_status_implicit l in
  let maximps = List.filter Impargs.maximal_insertion_of imps in
  let nonmaximps = List.subtract Pervasives.(=) imps maximps in (* FIXME *)
  print_impargs_by_name false nonmaximps @
  print_impargs_by_name true maximps

let print_impargs_list prefix l =
  let l = extract_impargs_data l in
  List.flatten (List.map (fun (cond,imps) ->
    match cond with
    | None ->
	List.map (fun pp -> add_colon prefix ++ pp)
	  (print_one_impargs_list imps)
    | Some (n1,n2) ->
       [v 2 (prlist_with_sep cut (fun x -> x)
	 [(if ismt prefix then str "When" else prefix ++ str ", when") ++
	   str " applied to " ++
	   (if Int.equal n1 n2 then int_or_no n2 else
	    if Int.equal n1 0 then str "no more than " ++ int n2
	    else int n1 ++ str " to " ++ int_or_no n2) ++
	    str (String.plural n2 " argument") ++ str ":";
          v 0 (prlist_with_sep cut (fun x -> x)
	    (if List.exists is_status_implicit imps
	    then print_one_impargs_list imps
	    else [str "No implicit arguments"]))])]) l)

let print_renames_list prefix l =
  if List.is_empty l then [] else
  [add_colon prefix ++ str "Arguments are renamed to " ++
    hv 2 (prlist_with_sep pr_comma (fun x -> x) (List.map Name.print l))]

let need_expansion impl ref =
  let typ, _ = Typeops.type_of_global_in_context (Global.env ()) ref in
  let ctx = Term.prod_assum typ in
  let nprods = List.count is_local_assum ctx in
  not (List.is_empty impl) && List.length impl >= nprods &&
    let _,lastimpl = List.chop nprods impl in
      List.exists is_status_implicit lastimpl

let print_impargs ref =
  let ref = Smartlocate.smart_global ref in
  let impl = implicits_of_global ref in
  let has_impl = not (List.is_empty impl) in
  (* Need to reduce since implicits are computed with products flattened *)
  pr_infos_list
    ([ print_ref (need_expansion (select_impargs_size 0 impl) ref) ref None;
       blankline ] @
    (if has_impl then print_impargs_list (mt()) impl
     else [str "No implicit arguments"]))

(*********************)
(** Printing Scopes  *)

let print_argument_scopes prefix = function
  | [Some sc] ->
      [add_colon prefix ++ str"Argument scope is [" ++ str sc ++ str"]"]
  | l when not (List.for_all Option.is_empty l) ->
     [add_colon prefix ++ hov 2 (str"Argument scopes are" ++ spc() ++
      str "[" ++
      pr_sequence (function Some sc -> str sc | None -> str "_") l ++
      str "]")]
  | _  -> []

(*********************)
(** Printing Opacity *)

type opacity =
  | FullyOpaque
  | TransparentMaybeOpacified of Conv_oracle.level

let opacity env =
  function
  | VarRef v when NamedDecl.is_local_def (Environ.lookup_named v env) ->
      Some(TransparentMaybeOpacified
        (Conv_oracle.get_strategy (Environ.oracle env) (VarKey v)))
  | ConstRef cst ->
      let cb = Environ.lookup_constant cst env in
      (match cb.const_body with
        | Undef _ | Primitive _ -> None
	| OpaqueDef _ -> Some FullyOpaque
	| Def _ -> Some
          (TransparentMaybeOpacified
            (Conv_oracle.get_strategy (Environ.oracle env) (ConstKey cst))))
  | _ -> None

let print_opacity ref =
  match opacity (Global.env()) ref with
    | None -> []
    | Some s ->
       [pr_global ref ++ str " is " ++
        match s with
          | FullyOpaque -> str "opaque"
          | TransparentMaybeOpacified Conv_oracle.Opaque ->
              str "basically transparent but considered opaque for reduction"
          | TransparentMaybeOpacified lev when Conv_oracle.is_transparent lev ->
              str "transparent"
          | TransparentMaybeOpacified (Conv_oracle.Level n) ->
              str "transparent (with expansion weight " ++ int n ++ str ")"
          | TransparentMaybeOpacified Conv_oracle.Expand ->
              str "transparent (with minimal expansion weight)"]

(*******************)

let print_if_is_coercion ref =
  if Classops.coercion_exists ref then [pr_global ref ++ str " is a coercion"] else []

(*******************)
(* *)

let print_polymorphism ref =
  let poly = Global.is_polymorphic ref in
  let template_poly = Global.is_template_polymorphic ref in
  [ pr_global ref ++ str " is " ++ str
      (if poly then "universe polymorphic"
       else if template_poly then
	 "template universe polymorphic"
       else "not universe polymorphic") ]

let print_type_in_type ref =
  let unsafe = Global.is_type_in_type ref in
  if unsafe then
    [ pr_global ref ++ str " relies on an unsafe universe hierarchy"]
  else []

let print_primitive_record recflag mipv = function
  | PrimRecord _ ->
    let eta = match recflag with
    | CoFinite | Finite -> str" without eta conversion"
    | BiFinite -> str " with eta conversion"
    in
    [Id.print mipv.(0).mind_typename ++ str" has primitive projections" ++ eta ++ str"."]
  | FakeRecord | NotRecord -> []

let print_primitive ref =
  match ref with 
  | IndRef ind -> 
    let mib,_ = Global.lookup_inductive ind in
      print_primitive_record mib.mind_finite mib.mind_packets mib.mind_record
  | _ -> []

let print_name_infos ref =
  let impls = implicits_of_global ref in
  let scopes = Notation.find_arguments_scope ref in
  let renames =
    try Arguments_renaming.arguments_names ref with Not_found -> [] in
  let type_info_for_implicit =
    if need_expansion (select_impargs_size 0 impls) ref then
      (* Need to reduce since implicits are computed with products flattened *)
      [str "Expanded type for implicit arguments";
       print_ref true ref None; blankline]
    else
      [] in
  print_type_in_type ref @
  print_primitive ref @
  type_info_for_implicit @
  print_renames_list (mt()) renames @
  print_impargs_list (mt()) impls @
  print_argument_scopes (mt()) scopes @
  print_if_is_coercion ref

let print_id_args_data test pr id l =
  if List.exists test l then
    pr (str "For " ++ Id.print id) l
  else
    []

let print_args_data_of_inductive_ids get test pr sp mipv =
  List.flatten (Array.to_list (Array.mapi
    (fun i mip ->
      print_id_args_data test pr mip.mind_typename (get (IndRef (sp,i))) @
      List.flatten (Array.to_list (Array.mapi
	(fun j idc ->
	  print_id_args_data test pr idc (get (ConstructRef ((sp,i),j+1))))
        mip.mind_consnames)))
    mipv))

let print_inductive_implicit_args =
  print_args_data_of_inductive_ids
    implicits_of_global (fun l -> not (List.is_empty (positions_of_implicits l)))
    print_impargs_list

let print_inductive_renames =
  print_args_data_of_inductive_ids
    (fun r ->
      try Arguments_renaming.arguments_names r with Not_found -> [])
    ((!=) Anonymous)
    print_renames_list

let print_inductive_argument_scopes =
  print_args_data_of_inductive_ids
    Notation.find_arguments_scope (Option.has_some) print_argument_scopes

(*********************)
(* "Locate" commands *)

type 'a locatable_info = {
  locate : qualid -> 'a option;
  locate_all : qualid -> 'a list;
  shortest_qualid : 'a -> qualid;
  name : 'a -> Pp.t;
  print : 'a -> Pp.t;
  about : 'a -> Pp.t;
}

type locatable = Locatable : 'a locatable_info -> locatable

type logical_name =
  | Term of GlobRef.t
  | Dir of Nametab.GlobDirRef.t
  | Syntactic of KerName.t
  | ModuleType of ModPath.t
  | Other : 'a * 'a locatable_info -> logical_name
  | Undefined of qualid

(** Generic table for objects that are accessible through a name. *)
let locatable_map : locatable String.Map.t ref = ref String.Map.empty

let register_locatable name f =
  locatable_map := String.Map.add name (Locatable f) !locatable_map

exception ObjFound of logical_name

let locate_any_name qid =
  try Term (Nametab.locate qid)
  with Not_found ->
  try Syntactic (Nametab.locate_syndef qid)
  with Not_found ->
  try Dir (Nametab.locate_dir qid)
  with Not_found ->
  try ModuleType (Nametab.locate_modtype qid)
  with Not_found ->
    let iter _ (Locatable info) = match info.locate qid with
    | None -> ()
    | Some ans -> raise (ObjFound (Other (ans, info)))
    in
    try String.Map.iter iter !locatable_map; Undefined qid
    with ObjFound obj -> obj

let pr_located_qualid = function
  | Term ref ->
      let ref_str = match ref with
	  ConstRef _ -> "Constant"
	| IndRef _ -> "Inductive"
	| ConstructRef _ -> "Constructor"
	| VarRef _ -> "变量" (* "变量" "bianliang" ; OLD: "Variable" *) in
      str ref_str ++ spc () ++ pr_path (Nametab.path_of_global ref)
  | Syntactic kn ->
      str "Notation" ++ spc () ++ pr_path (Nametab.path_of_syndef kn)
  | Dir dir ->
      let s,dir =
        let open Nametab in
        let open GlobDirRef in match dir with
        | DirOpenModule { obj_dir ; _ } -> "Open Module", obj_dir
        | DirOpenModtype { obj_dir ; _ } -> "Open Module Type", obj_dir
        | DirOpenSection { obj_dir ; _ } -> "Open Section", obj_dir
        | DirModule { obj_dir ; _ } -> "Module", obj_dir
      in
      str s ++ spc () ++ DirPath.print dir
  | ModuleType mp ->
      str "Module Type" ++ spc () ++ pr_path (Nametab.path_of_modtype mp)
  | Other (obj, info) -> info.name obj
  | Undefined qid ->
      pr_qualid qid ++ spc () ++ str "not a defined object."

let canonize_ref = function
  | ConstRef c ->
    let kn = Constant.canonical c in
    if KerName.equal (Constant.user c) kn then None
    else Some (ConstRef (Constant.make1 kn))
  | IndRef (ind,i) ->
    let kn = MutInd.canonical ind in
    if KerName.equal (MutInd.user ind) kn then None
    else Some (IndRef (MutInd.make1 kn, i))
  | ConstructRef ((ind,i),j) ->
    let kn = MutInd.canonical ind in
    if KerName.equal (MutInd.user ind) kn then None
    else Some (ConstructRef ((MutInd.make1 kn, i),j))
  | VarRef _ -> None

let display_alias = function
  | Term r ->
    begin match canonize_ref r with
    | None -> mt ()
    | Some r' ->
      let q' = Nametab.shortest_qualid_of_global Id.Set.empty r' in
      spc () ++ str "(alias of " ++ pr_qualid q' ++ str ")"
    end
  | _ -> mt ()

let locate_term qid =
  let expand = function
    | TrueGlobal ref ->
        Term ref, Nametab.shortest_qualid_of_global Id.Set.empty ref
    | SynDef kn ->
        Syntactic kn, Nametab.shortest_qualid_of_syndef Id.Set.empty kn
  in
  List.map expand (Nametab.locate_extended_all qid)

let locate_module qid =
  let all = Nametab.locate_extended_all_dir qid in
  let map dir = let open Nametab.GlobDirRef in match dir with
  | DirModule { Nametab.obj_mp ; _ } -> Some (Dir dir, Nametab.shortest_qualid_of_module obj_mp)
  | DirOpenModule _ -> Some (Dir dir, qid)
  | _ -> None
  in
  List.map_filter map all

let locate_modtype qid =
  let all = Nametab.locate_extended_all_modtype qid in
  let map mp = ModuleType mp, Nametab.shortest_qualid_of_modtype mp in
  let modtypes = List.map map all in
  (* Don't forget the opened module types: they are not part of the same name tab. *)
  let all = Nametab.locate_extended_all_dir qid in
  let map dir = let open Nametab.GlobDirRef in match dir with
  | DirOpenModtype _ -> Some (Dir dir, qid)
  | _ -> None
  in
  modtypes @ List.map_filter map all

let locate_other s qid =
  let Locatable info = String.Map.find s !locatable_map in
  let ans = info.locate_all qid in
  let map obj = (Other (obj, info), info.shortest_qualid obj) in
  List.map map ans

type locatable_kind =
| LocTerm
| LocModule
| LocOther of string
| LocAny

let print_located_qualid name flags qid =
  let located = match flags with
  | LocTerm -> locate_term qid
  | LocModule -> locate_modtype qid @ locate_module qid
  | LocOther s -> locate_other s qid
  | LocAny ->
    locate_term qid @
    locate_modtype qid @
    locate_module qid @
    String.Map.fold (fun s _ accu -> locate_other s qid @ accu) !locatable_map []
  in
  match located with
    | [] ->
	let (dir,id) = repr_qualid qid in
	if DirPath.is_empty dir then
	  str "No " ++ str name ++ str " of basename" ++ spc () ++ Id.print id
	else
	  str "No " ++ str name ++ str " of suffix" ++ spc () ++ pr_qualid qid
    | l ->
	prlist_with_sep fnl
	(fun (o,oqid) ->
	  hov 2 (pr_located_qualid o ++
	  (if not (qualid_eq oqid qid) then
	    spc() ++ str "(shorter name to refer to it in current context is "
            ++ pr_qualid oqid ++ str")"
	   else mt ()) ++
          display_alias o)) l

let print_located_term ref = print_located_qualid "term" LocTerm ref
let print_located_other s ref = print_located_qualid s (LocOther s) ref
let print_located_module ref = print_located_qualid "module" LocModule ref
let print_located_qualid ref = print_located_qualid "object" LocAny ref

(******************************************)
(**** Printing declarations and judgments *)
(****  Gallina layer                  *****)

let gallina_print_typed_value_in_env env sigma (trm,typ) =
  (pr_leconstr_env env sigma trm ++ fnl () ++
     str "     : " ++ pr_letype_env env sigma typ)

(* To be improved; the type should be used to provide the types in the
   abstractions. This should be done recursively inside pr_lconstr, so that
   the pretty-print of a proposition (P:(nat->nat)->Prop)(P [u]u)
   synthesizes the type nat of the abstraction on u *)

let print_named_def env sigma name body typ =
  let pbody = pr_lconstr_env env sigma body in
  let ptyp = pr_ltype_env env sigma typ in
  let pbody = if Constr.isCast body then surround pbody else pbody in
  (str "*** [" ++ str name ++ str " " ++
     hov 0 (str ":=" ++ brk (1,2) ++ pbody ++ spc () ++
	      str ":" ++ brk (1,2) ++ ptyp) ++
	   str "]")

let print_named_assum env sigma name typ =
  str "*** [" ++ str name ++ str " : " ++ pr_ltype_env env sigma typ ++ str "]"

let gallina_print_named_decl env sigma =
  let open Context.Named.Declaration in
  function
  | LocalAssum (id, typ) ->
     print_named_assum env sigma (Id.to_string id) typ
  | LocalDef (id, body, typ) ->
     print_named_def env sigma (Id.to_string id) body typ

let assumptions_for_print lna =
  List.fold_right (fun na env -> add_name na env) lna empty_names_context

(*********************)
(* *)

let gallina_print_inductive sp udecl =
  let env = Global.env() in
  let mib = Environ.lookup_mind sp env in
  let mipv = mib.mind_packets in
  pr_mutual_inductive_body env sp mib udecl ++
  with_line_skip
    (print_primitive_record mib.mind_finite mipv mib.mind_record @
     print_inductive_renames sp mipv @
     print_inductive_implicit_args sp mipv @
     print_inductive_argument_scopes sp mipv)

let print_named_decl env sigma id =
  gallina_print_named_decl env sigma (Global.lookup_named id) ++ fnl ()

let gallina_print_section_variable env sigma id =
  print_named_decl env sigma id ++
  with_line_skip (print_name_infos (VarRef id))

let print_body env evd = function
  | Some c  -> pr_lconstr_env env evd c
  | None -> (str"<no body>")

let print_typed_body env evd (val_0,typ) =
  (print_body env evd val_0 ++ fnl () ++ str "     : " ++ pr_ltype_env env evd typ)

let print_instance sigma cb =
  if Declareops.constant_is_polymorphic cb then
    let univs = Declareops.constant_polymorphic_context cb in
    let inst = Univ.make_abstract_instance univs in
    pr_universe_instance sigma inst
  else mt()
				
let print_constant with_values sep sp udecl =
  let cb = Global.lookup_constant sp in
  let val_0 = Global.body_of_constant_body cb in
  let typ = cb.const_type in
  let univs =
    let open Univ in
    let otab = Global.opaque_tables () in
    match cb.const_body with
    | Undef _ | Def _ | Primitive _ -> cb.const_universes
    | OpaqueDef o ->
      let body_uctxs = Opaqueproof.force_constraints otab o in
      match cb.const_universes with
      | Monomorphic ctx ->
        Monomorphic (ContextSet.union body_uctxs ctx)
      | Polymorphic ctx ->
        assert(ContextSet.is_empty body_uctxs);
        Polymorphic ctx
  in
  let ctx =
    UState.of_binders
      (UnivNames.universe_binders_with_opt_names (Declareops.constant_polymorphic_context cb) udecl)
  in
  let env = Global.env () and sigma = Evd.from_ctx ctx in
  let pr_ltype = pr_ltype_env env sigma in
  hov 0 (
    match val_0 with
    | None ->
	str"*** [ " ++
	print_basename sp ++ print_instance sigma cb ++ str " : " ++ cut () ++ pr_ltype typ ++
	str" ]" ++
        Printer.pr_universes sigma univs ?priv:cb.const_private_poly_univs
    | Some (c, ctx) ->
	print_basename sp ++ print_instance sigma cb ++ str sep ++ cut () ++
	(if with_values then print_typed_body env sigma (Some c,typ) else pr_ltype typ)++
        Printer.pr_universes sigma univs ?priv:cb.const_private_poly_univs)

let gallina_print_constant_with_infos sp udecl =
  print_constant true " = " sp udecl ++
  with_line_skip (print_name_infos (ConstRef sp))

let gallina_print_syntactic_def env kn =
  let qid = Nametab.shortest_qualid_of_syndef Id.Set.empty kn
  and (vars,a) = Syntax_def.search_syntactic_definition kn in
  let c = Notation_ops.glob_constr_of_notation_constr a in
  hov 2
    (hov 4
       (str "Notation " ++ pr_qualid qid ++
        prlist (fun id -> spc () ++ Id.print id) (List.map fst vars) ++
        spc () ++ str ":=") ++
     spc () ++
     Constrextern.without_specific_symbols
       [Notation.SynDefRule kn] (pr_glob_constr_env env) c)

let gallina_print_leaf_entry env sigma with_values ((sp,kn as oname),lobj) =
  let sep = if with_values then " = " else " : "
  and tag = object_tag lobj in
    match (oname,tag) with
      | (_,"VARIABLE") ->
	  (* Outside sections, VARIABLES still exist but only with universes
             constraints *)
          (try Some(print_named_decl env sigma (basename sp)) with Not_found -> None)
      | (_,"CONSTANT") ->
          Some (print_constant with_values sep (Constant.make1 kn) None)
      | (_,"INDUCTIVE") ->
          Some (gallina_print_inductive (MutInd.make1 kn) None)
      | (_,"MODULE") ->
          let (mp,l) = KerName.repr kn in
	    Some (print_module with_values (MPdot (mp,l)))
      | (_,"MODULE TYPE") ->
          let (mp,l) = KerName.repr kn in
	  Some (print_modtype (MPdot (mp,l)))
      | (_,("AUTOHINT"|"GRAMMAR"|"SYNTAXCONSTANT"|"PPSYNTAX"|"TOKEN"|"CLASS"|
	    "COERCION"|"REQUIRE"|"END-SECTION"|"STRUCTURE")) -> None
      (* To deal with forgotten cases... *)
      | (_,s) -> None

let gallina_print_library_entry env sigma with_values ent =
  let pr_name (sp,_) = Id.print (basename sp) in
  match ent with
    | (oname,Lib.Leaf lobj) ->
        gallina_print_leaf_entry env sigma with_values (oname,lobj)
    | (oname,Lib.OpenedSection (dir,_)) ->
        Some (str " >>>>>>> Section " ++ pr_name oname)
    | (_,Lib.CompilingLibrary { Nametab.obj_dir; _ }) ->
        Some (str " >>>>>>> Library " ++ DirPath.print obj_dir)
    | (oname,Lib.OpenedModule _) ->
	Some (str " >>>>>>> Module " ++ pr_name oname)

let gallina_print_context env sigma with_values =
  let rec prec n = function
    | h::rest when Option.is_empty n || Option.get n > 0 ->
        (match gallina_print_library_entry env sigma with_values h with
	  | None -> prec n rest
	  | Some pp -> prec (Option.map ((+) (-1)) n) rest ++ pp ++ fnl ())
    | _ -> mt ()
  in
  prec

let gallina_print_eval red_fun env sigma _ {uj_val=trm;uj_type=typ} =
  let ntrm = red_fun env sigma trm in
  (str "     = " ++ gallina_print_typed_value_in_env env sigma (ntrm,typ))

(******************************************)
(**** Printing abstraction layer          *)

let default_object_pr = {
  print_inductive           = gallina_print_inductive;
  print_constant_with_infos = gallina_print_constant_with_infos;
  print_section_variable    = gallina_print_section_variable;
  print_syntactic_def       = gallina_print_syntactic_def;
  print_module              = gallina_print_module;
  print_modtype             = gallina_print_modtype;
  print_named_decl          = gallina_print_named_decl;
  print_library_entry       = gallina_print_library_entry;
  print_context             = gallina_print_context;
  print_typed_value_in_env  = gallina_print_typed_value_in_env;
  print_eval                = gallina_print_eval;
}

(**
let object_pr = ref default_object_pr
let set_object_pr = (:=) object_pr
... **)                         

(** ---------------------- START MODIFICATION ------------------------- **)
                         
let _ = set_object_pr default_object_pr
