open Ppconstr      

(** ---------------------- INCLUDE COPY ppconstr.ml ------------------------- **)
   
open CErrors
open Util
open Pp
open CAst
open Names
open Libnames
open Pputils
open Ppextend
open Glob_term
open Constrexpr
open Constrexpr_ops
open Notation_gram
open Decl_kinds
open Namegen

module Tag =
struct
  let keyword   = "constr.keyword"
  let evar      = "constr.evar"
  let univ      = "constr.type"
  let notation  = "constr.notation"
  let variable  = "constr.variable"
  let reference = "constr.reference"
  let path      = "constr.path"

end

let do_not_tag _ x = x
let tag t s = Pp.tag t s
let tag_keyword     = tag Tag.keyword
let tag_evar        = tag Tag.evar
let tag_type        = tag Tag.univ
let tag_unparsing   = function
| UnpTerminal s -> tag Tag.notation
| _ -> do_not_tag ()
let tag_constr_expr = do_not_tag
let tag_path = tag Tag.path
let tag_ref = tag Tag.reference
let tag_var = tag Tag.variable


  let keyword s = tag_keyword (str s)
  let sep_v = fun _ -> str"," ++ spc()
  let pr_tight_coma () = str "," ++ cut ()

  let latom = 0
  let lprod = 200
  let llambda = 200
  let lif = 200
  let lletin = 200
  let lletpattern = 200
  let lfix = 200
  let lcast = 100
  let larg = 9
  let lapp = 10
  let lposint = 0
  let lnegint = 35 (* must be consistent with Notation "- x" *)
  let ltop = (200,E)
  let lproj = 1
  let ldelim = 1
  let lsimpleconstr = (8,E)
  let lsimplepatt = (1,E)

  let prec_less child (parent,assoc) =
    if parent < 0 && Int.equal child lprod then true
    else
      let parent = abs parent in
      match assoc with
        | E -> (<=) child parent
        | L -> (<) child parent
        | Prec n -> child<=n
        | Any -> true

  let prec_of_prim_token = function
    | Numeral (_,b) -> if b then lposint else lnegint
    | String _ -> latom

  let print_hunks n pr pr_patt pr_binders (terms, termlists, binders, binderlists) unps =
    let env = ref terms and envlist = ref termlists and bl = ref binders and bll = ref binderlists in
    let pop r = let a = List.hd !r in r := List.tl !r; a in
    let return unp pp1 pp2 = (tag_unparsing unp pp1) ++ pp2 in
    (* Warning:
       The following function enforces a very precise order of
       evaluation of sub-components.
       Do not modify it unless you know what you are doing! *)
    let rec aux = function
      | [] ->
        mt ()
      | UnpMetaVar (_, prec) as unp :: l ->
        let c = pop env in
        let pp2 = aux l in
        let pp1 = pr (n, prec) c in
        return unp pp1 pp2
      | UnpBinderMetaVar (_, prec) as unp :: l ->
        let c = pop bl in
        let pp2 = aux l in
        let pp1 = pr_patt (n, prec) c in
        return unp pp1 pp2
      | UnpListMetaVar (_, prec, sl) as unp :: l ->
        let cl = pop envlist in
        let pp1 = prlist_with_sep (fun () -> aux sl) (pr (n,prec)) cl in
        let pp2 = aux l in
        return unp pp1 pp2
      | UnpBinderListMetaVar (_, isopen, sl) as unp :: l ->
        let cl = pop bll in
        let pp2 = aux l in
        let pp1 = pr_binders (fun () -> aux sl) isopen cl in
        return unp pp1 pp2
      | UnpTerminal s as unp :: l ->
        let pp2 = aux l in
        let pp1 = str s in
        return unp pp1 pp2
      | UnpBox (b,sub) as unp :: l ->
        let pp1 = ppcmd_of_box b (aux (List.map snd sub)) in
        let pp2 = aux l in
        return unp pp1 pp2
      | UnpCut cut as unp :: l ->
        let pp2 = aux l in
        let pp1 = ppcmd_of_cut cut in
        return unp pp1 pp2
    in
    aux unps

  let pr_notation pr pr_patt pr_binders s env =
    let unpl, level = find_notation_printing_rule s in
    print_hunks level pr pr_patt pr_binders env unpl, level

  let pr_delimiters key strm =
    strm ++ str ("%"^key)

  let pr_generalization bk ak c =
    let hd, tl =
      match bk with
        | Implicit -> "{", "}"
        | Explicit -> "(", ")"
    in (* TODO: syntax Abstraction Kind *)
    str "`" ++ str hd ++ c ++ str tl

  let pr_com_at n =
    if !Flags.beautify && not (Int.equal n 0) then comment (Pputils.extract_comments n)
    else mt()

  let pr_with_comments ?loc pp = pr_located (fun x -> x) (loc, pp)

  let pr_sep_com sep f c = pr_with_comments ?loc:(constr_loc c) (sep() ++ f c)

  let pr_univ_expr = function
    | Some (x,n) ->
       pr_qualid x ++ (match n with 0 -> mt () | _ -> str"+" ++ int n)
    | None -> str"_"

  let pr_univ l =
    match l with
      | [x] -> pr_univ_expr x
      | l -> str"max(" ++ prlist_with_sep (fun () -> str",") pr_univ_expr l ++ str")"

  let pr_univ_annot pr x = str "@{" ++ pr x ++ str "}"

  let pr_glob_sort = let open Glob_term in function
    | GProp -> tag_type (str "Prop")
    | GSet -> tag_type (str "Set")
    | GType [] -> tag_type (str "类型" (* "类型" "leixing" ; OLD: "Type" *))
    | GType u -> hov 0 (tag_type (str "类型" (* "类型" "leixing" ; OLD: "Type" *)) ++ pr_univ_annot pr_univ u)

  let pr_glob_level = let open Glob_term in function
    | GProp -> tag_type (str "Prop")
    | GSet -> tag_type (str "Set")
    | GType UUnknown -> tag_type (str "类型" (* "类型" "leixing" ; OLD: "Type" *))
    | GType UAnonymous -> tag_type (str "_")
    | GType (UNamed u) -> tag_type (pr_qualid u)

  let pr_qualid sp =
    let (sl, id) = repr_qualid sp in
    let id = tag_ref (Id.print id) in
    let sl = match List.rev (DirPath.repr sl) with
    | [] -> mt ()
    | sl ->
      let pr dir = tag_path (Id.print dir) ++ str "." in
      prlist pr sl
    in
    sl ++ id

  let pr_id = Id.print
  let pr_qualid = pr_qualid
  let pr_patvar = pr_id

  let pr_glob_sort_instance = let open Glob_term in function
    | GProp ->
      tag_type (str "Prop")
    | GSet ->
      tag_type (str "Set")
    | GType u ->
      (match u with
        | UNamed u -> pr_qualid u
        | UAnonymous -> tag_type (str "类型" (* "类型" "leixing" ; OLD: "Type" *))
        | UUnknown -> tag_type (str "_"))

  let pr_universe_instance l =
    pr_opt_no_spc (pr_univ_annot (prlist_with_sep spc pr_glob_sort_instance)) l

  let pr_reference qid =
    if qualid_is_ident qid then tag_var (pr_id @@ qualid_basename qid)
    else pr_qualid qid

  let pr_cref ref us =
    pr_reference ref ++ pr_universe_instance us

  let pr_expl_args pr (a,expl) =
    match expl with
      | None -> pr (lapp,L) a
      | Some {v=ExplByPos (n,_id)} ->
        anomaly (Pp.str "Explicitation by position not implemented.")
      | Some {v=ExplByName id} ->
        str "(" ++ pr_id id ++ str ":=" ++ pr ltop a ++ str ")"

  let pr_opt_type_spc pr = function
    | { CAst.v = CHole (_,IntroAnonymous,_) } -> mt ()
    | t ->  str " :" ++ pr_sep_com (fun()->brk(1,2)) (pr ltop) t

  let pr_prim_token = function
    | Numeral (n,s) -> str (if s then n else "-"^n)
    | String s -> qs s

  let pr_evar pr id l =
    hov 0 (
      tag_evar (str "?" ++ pr_id id) ++
        (match l with
          | [] -> mt()
          | l ->
            let f (id,c) = pr_id id ++ str ":=" ++ pr ltop c in
            str"@{" ++ hov 0 (prlist_with_sep pr_semicolon f (List.rev l)) ++ str"}"))

  let las = lapp
  let lpator = 100
  let lpatrec = 0

  let rec pr_patt sep inh p =
    let (strm,prec) = match CAst.(p.v) with
      | CPatRecord l ->
        let pp (c, p) =
          pr_reference c ++ spc() ++ str ":=" ++ pr_patt spc (lpatrec, Any) p
        in
        str "{| " ++ prlist_with_sep pr_semicolon pp l ++ str " |}", lpatrec

      | CPatAlias (p, na) ->
        pr_patt mt (las,E) p ++ str " as " ++ pr_lname na, las

      | CPatCstr (c, None, []) ->
        pr_reference c, latom

      | CPatCstr (c, None, args) ->
        pr_reference c ++ prlist (pr_patt spc (lapp,L)) args, lapp

      | CPatCstr (c, Some args, []) ->
        str "@" ++ pr_reference c ++ prlist (pr_patt spc (lapp,L)) args, lapp

      | CPatCstr (c, Some expl_args, extra_args) ->
        surround (str "@" ++ pr_reference c ++ prlist (pr_patt spc (lapp,L)) expl_args)
        ++ prlist (pr_patt spc (lapp,L)) extra_args, lapp

      | CPatAtom (None) ->
        str "_", latom

      | CPatAtom (Some r) ->
        pr_reference r, latom

      | CPatOr pl ->
        hov 0 (prlist_with_sep pr_spcbar (pr_patt mt (lpator,L)) pl), lpator

      | CPatNotation ((_,"( _ )"),([p],[]),[]) ->
        pr_patt (fun()->str"(") (max_int,E) p ++ str")", latom

      | CPatNotation (s,(l,ll),args) ->
        let strm_not, l_not = pr_notation (pr_patt mt) (fun _ _ -> mt ()) (fun _ _ _ -> mt()) s (l,ll,[],[]) in
        (if List.is_empty args||prec_less l_not (lapp,L) then strm_not else surround strm_not)
        ++ prlist (pr_patt spc (lapp,L)) args, if not (List.is_empty args) then lapp else l_not

      | CPatPrim p ->
        pr_prim_token p, latom

      | CPatDelimiters (k,p) ->
        pr_delimiters k (pr_patt mt lsimplepatt p), 1
      | CPatCast _ ->
        assert false
    in
    let loc = p.CAst.loc in
    pr_with_comments ?loc
      (sep() ++ if prec_less prec inh then strm else surround strm)

  let pr_patt = pr_patt mt

  let pr_eqn pr {loc;v=(pl,rhs)} =
    spc() ++ hov 4
      (pr_with_comments ?loc
         (str "| " ++
            hov 0 (prlist_with_sep pr_spcbar (prlist_with_sep sep_v (pr_patt ltop)) pl
                   ++ str " =>") ++
            pr_sep_com spc (pr ltop) rhs))

  let begin_of_binder l_bi =
    let b_loc l = fst (Option.cata Loc.unloc (0,0) l) in
    match l_bi with
    | CLocalDef({loc},_,_) -> b_loc loc
    | CLocalAssum({loc}::_,_,_) -> b_loc loc
    | CLocalPattern{loc} -> b_loc loc
    | _ -> assert false

  let begin_of_binders = function
    | b::_ -> begin_of_binder b
    | _ -> 0

  let surround_impl k p =
    match k with
      | Explicit -> str"(" ++ p ++ str")"
      | Implicit -> str"{" ++ p ++ str"}"

  let surround_implicit k p =
    match k with
      | Explicit -> p
      | Implicit -> (str"{" ++ p ++ str"}")

  let pr_binder many pr (nal,k,t) =
    match k with
      | Generalized (b, b', t') ->
        assert (match b with Implicit -> true | _ -> false);
        begin match nal with
          |[{loc; v=Anonymous}] ->
            hov 1 (str"`" ++ (surround_impl b'
                                ((if t' then str "!" else mt ()) ++ pr t)))
          |[{loc; v=Name id}] ->
            hov 1 (str "`" ++ (surround_impl b'
                                 (pr_lident CAst.(make ?loc id) ++ str " : " ++
                                    (if t' then str "!" else mt()) ++ pr t)))
          |_ -> anomaly (Pp.str "List of generalized binders have alwais one element.")
        end
      | Default b ->
        match t with
          | { CAst.v = CHole (_,IntroAnonymous,_) } ->
            let s = prlist_with_sep spc pr_lname nal in
            hov 1 (surround_implicit b s)
          | _ ->
            let s = prlist_with_sep spc pr_lname nal ++ str " : " ++ pr t in
            hov 1 (if many then surround_impl b s else surround_implicit b s)

  let pr_binder_among_many pr_c = function
    | CLocalAssum (nal,k,t) ->
      pr_binder true pr_c (nal,k,t)
    | CLocalDef (na,c,topt) ->
      surround (pr_lname na ++
                pr_opt_no_spc (fun t -> str " :" ++ ws 1 ++ pr_c t) topt ++
                str" :=" ++ spc() ++ pr_c c)
    | CLocalPattern {CAst.loc; v = p,tyo} ->
      let p = pr_patt lsimplepatt p in
      match tyo with
        | None ->
          str "'" ++ p
        | Some ty ->
          str "'" ++ surround (p ++ spc () ++ str ":" ++ ws 1 ++ pr_c ty)

  let pr_undelimited_binders sep pr_c =
    prlist_with_sep sep (pr_binder_among_many pr_c)

  let pr_delimited_binders kw sep pr_c bl =
    let n = begin_of_binders bl in
    match bl with
      | [CLocalAssum (nal,k,t)] ->
        kw n ++ pr_binder false pr_c (nal,k,t)
      | (CLocalAssum _ | CLocalPattern _ | CLocalDef _) :: _ as bdl ->
        kw n ++ pr_undelimited_binders sep pr_c bdl
      | [] -> anomaly (Pp.str "The ast is malformed, found lambda/prod without proper binders.")

  let pr_binders_gen pr_c sep is_open =
    if is_open then pr_delimited_binders pr_com_at sep pr_c
    else pr_undelimited_binders sep pr_c

  let pr_recursive_decl pr pr_dangling dangling_with_for id bl annot t c =
    let pr_body =
      if dangling_with_for then pr_dangling else pr in
    pr_id id ++ (if bl = [] then mt () else str" ") ++
      hov 0 (pr_undelimited_binders spc (pr ltop) bl ++ annot) ++
      pr_opt_type_spc pr t ++ str " :=" ++
      pr_sep_com (fun () -> brk(1,2)) (pr_body ltop) c

  let pr_guard_annot pr_aux bl (n,ro) =
    match n with
      | None -> mt ()
      | Some {loc; v = id} ->
        match (ro : Constrexpr.recursion_order_expr) with
          | CStructRec ->
            let names_of_binder = function
              | CLocalAssum (nal,_,_) -> nal
              | CLocalDef (_,_,_) -> []
              | CLocalPattern _ -> assert false
            in let ids = List.flatten (List.map names_of_binder bl) in
               if List.length ids > 1 then
                 spc() ++ str "{" ++ keyword "struct" ++ spc () ++ pr_id id ++ str"}"
               else mt()
          | CWfRec c ->
            spc() ++ str "{" ++ keyword "wf" ++ spc () ++ pr_aux c ++ spc() ++ pr_id id ++ str"}"
          | CMeasureRec (m,r) ->
            spc() ++ str "{" ++ keyword "measure" ++ spc () ++ pr_aux m ++ spc() ++ pr_id id++
              (match r with None -> mt() | Some r -> str" on " ++ pr_aux r) ++ str"}"

  let pr_fixdecl pr prd dangling_with_for ({v=id},ro,bl,t,c) =
    let annot = pr_guard_annot (pr lsimpleconstr) bl ro in
    pr_recursive_decl pr prd dangling_with_for id bl annot t c

  let pr_cofixdecl pr prd dangling_with_for ({v=id},bl,t,c) =
    pr_recursive_decl pr prd dangling_with_for id bl (mt()) t c

  let pr_recursive pr_decl id = function
    | [] -> anomaly (Pp.str "(co)fixpoint with no definition.")
    | [d1] -> pr_decl false d1
    | dl ->
      prlist_with_sep (fun () -> fnl() ++ keyword "with" ++ spc ())
        (pr_decl true) dl ++
        fnl() ++ keyword "for" ++ spc () ++ pr_id id

  let pr_asin pr na indnalopt =
    (match na with (* Decision of printing "_" or not moved to constrextern.ml *)
      | Some na -> spc () ++ keyword "as" ++ spc () ++  pr_lname na
      | None -> mt ()) ++
      (match indnalopt with
        | None -> mt ()
        | Some t -> spc () ++ keyword "in" ++ spc () ++ pr_patt lsimplepatt t)

  let pr_case_item pr (tm,as_clause, in_clause) =
    hov 0 (pr (lcast,E) tm ++ pr_asin pr as_clause in_clause)

  let pr_case_type pr po =
    match po with
      | None | Some { CAst.v = CHole (_,IntroAnonymous,_) } -> mt()
      | Some p ->
        spc() ++ hov 2 (keyword "return" ++ pr_sep_com spc (pr lsimpleconstr) p)

  let pr_simple_return_type pr na po =
    (match na with
      | Some {v=Name id} ->
        spc () ++ keyword "as" ++ spc () ++ pr_id id
      | _ -> mt ()) ++
      pr_case_type pr po

  let pr_proj pr pr_app a f l =
    hov 0 (pr (lproj,E) a ++ cut() ++ str ".(" ++ pr_app pr f l ++ str ")")

  let pr_appexpl pr (f,us) l =
    hov 2 (
      str "@" ++ pr_reference f ++
        pr_universe_instance us ++
        prlist (pr_sep_com spc (pr (lapp,L))) l)

  let pr_app pr a l =
    hov 2 (
      pr (lapp,L) a  ++
        prlist (fun a -> spc () ++ pr_expl_args pr a) l)

  let pr_record_body_gen pr l =
    spc () ++
    prlist_with_sep pr_semicolon
      (fun (id, c) -> h 1 (pr_reference id ++ spc () ++ str":=" ++ pr ltop c)) l

  let pr_forall n = keyword "forall" ++ pr_com_at n ++ spc ()

  let pr_fun n = keyword "fun" ++ pr_com_at n ++ spc ()

  let pr_fun_sep = spc () ++ str "=>"

  let pr_dangling_with_for sep pr inherited a =
    match a.v with
      | (CFix (_,[_])|CCoFix(_,[_])) ->
        pr sep (latom,E) a
      | _ ->
        pr sep inherited a

(** ---------------------- START MODIFICATION ------------------------- **)

  let pr_forall n = keyword "对于所有" ++ pr_com_at n ++ spc ()

  let my_modular_constr_pr pr sep inherited a =
    let return (cmds, prec) = (tag_constr_expr a cmds, prec) in
    let loc = constr_loc a in

    match CAst.(a.v) with

      | CIf (c,(na,po),b1,b2) ->
      (* On force les parenthèses autour d'un "if" sous-terme (même si le
         parsing est lui plus tolérant) *)
       let (strm, prec) = 
        return (
          hv 0 (
              hov 1 (keyword "若" (* "若" "ruo" ; OLD: "if" *) ++ spc () ++ pr mt ltop c
                   ++ pr_simple_return_type (pr mt) na po) ++
              spc () ++
                hov 0 (keyword "则" (* "则" "ze" ; OLD:"then" *)
                     ++ pr (fun () -> brk (1,1)) ltop b1) ++ spc () ++
              hov 0 (keyword "否则" (* "否则" "fouze" ; OLD: "else" *)  ++ pr (fun () -> brk (1,1)) ltop b2)),
        lif
        ) in
       pr_with_comments ?loc
         (sep() ++ if prec_less prec inherited then strm else surround strm) 

      | CProdN (bl,a) ->
       let (strm, prec) = 
         return (
             hov 0 (
                 hov 2 (pr_delimited_binders pr_forall spc
                          (pr mt ltop) bl) ++
                   str "," ++ pr spc ltop a),
             lprod
           ) in
       pr_with_comments ?loc
         (sep() ++ if prec_less prec inherited then strm else surround strm) 
       
    | _ -> modular_constr_pr pr sep inherited a

         
  let rec fix rf x = rf (fix rf) x
  let my_pr = fix my_modular_constr_pr mt

  let my_default_term_pr = {
      pr_constr_expr   = my_pr lsimpleconstr;
      pr_lconstr_expr  = my_pr ltop;
      pr_constr_pattern_expr  = my_pr lsimpleconstr;
      pr_lconstr_pattern_expr = my_pr ltop
    }

  let _ = set_term_pr my_default_term_pr
            
