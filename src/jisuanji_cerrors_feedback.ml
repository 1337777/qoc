open CErrors
open Pp
open ExplainErr

(** -----errors----- *)

let rec transf : Pp.doc_view -> Pp.doc_view =
function
  | Ppcmd_glue l -> Ppcmd_glue (List.map (fun x -> Pp.unrepr (transf (Pp.repr x))) l)
  | Ppcmd_box (x , y) -> Ppcmd_box (x , Pp.unrepr (transf (Pp.repr y)))
  | Ppcmd_tag (x , y) -> Ppcmd_tag (x , Pp.unrepr (transf (Pp.repr y)))
  | Ppcmd_print_break (x , y) -> Ppcmd_print_break (x , y)
  | Ppcmd_force_newline -> Ppcmd_force_newline
  | Ppcmd_comment x -> Ppcmd_comment x

  | Ppcmd_string "Last block to end has name " ->
    Ppcmd_string "已结束的最后一个块名为 "
  | Ppcmd_string " already exists" ->
    Ppcmd_string " 已经存在"
  | Ppcmd_string x -> Ppcmd_string x

let where = function
| None -> mt ()
| Some s ->
  if !Flags.debug then str "in " ++ str s ++ str ":" ++ spc () else mt ()

let _ = register_handler begin function
  | UserError(s, pps) ->
    where s ++ (Pp.unrepr (transf (Pp.repr pps))) ++ str " ----USERERROR"
(*processed as EvaluatedError:  | AlreadyDeclared(pps) -> pps ++ str " ----ALREADYDECLARED" *)
  (* Basic interaction exceptions *)
  | Stream.Error txt -> hov 0 (str "Syntax errorRORORORO: " ++ str txt ++ str ".")
  | CLexer.Error.E err -> hov 0 (str (CLexer.Error.to_string err))
(*  | Sys_error msg -> hov 0 (str "System error: " ++ guill msg) *)
  | Out_of_memory -> hov 0 (str "Out of memory.")
  | Stack_overflow -> hov 0 (str "Stack overflow.")
  | Dynlink.Error e -> hov 0 (str "Dynlink error: " ++ str Dynlink.(error_message e))
  | Timeout -> hov 0 (str "Timeout!")
  | Sys.Break -> hov 0 (fnl () ++ str "User interrupt.")
  (* Exceptions with pre-evaluated error messages *)
  | EvaluatedError (msg,None) -> let msg = (Pp.unrepr (transf (Pp.repr msg))) in
    msg  ++ str " ----EVALUATEDERROR NONE"
  | EvaluatedError (msg,Some reraise) -> let msg = (Pp.unrepr (transf (Pp.repr msg))) in
    msg ++ str " ----EVALUATEDERROR ADDED~~~ " ++ CErrors.print reraise
  (* Otherwise, not handled here *)
  | _ -> raise CErrors.Unhandled
end

(** -----feedback----- *)

let rec transf : Pp.doc_view -> Pp.doc_view =
function
  | Ppcmd_glue l -> Ppcmd_glue (List.map (fun x -> Pp.unrepr (transf (Pp.repr x))) l)
  | Ppcmd_box (x , y) -> Ppcmd_box (x , Pp.unrepr (transf (Pp.repr y)))
  | Ppcmd_tag (x , y) -> Ppcmd_tag (x , Pp.unrepr (transf (Pp.repr y)))
  | Ppcmd_print_break (x , y) -> Ppcmd_print_break (x , y)
  | Ppcmd_force_newline -> Ppcmd_force_newline
  | Ppcmd_comment x -> Ppcmd_comment x

  | Ppcmd_string " is defined" ->
    Ppcmd_string " 是定义了"
  | Ppcmd_string x -> Ppcmd_string x

open Feedback

let coqloop_feed (fb : Feedback.feedback) = let open Feedback in
  match fb.contents with
  | Processed   -> ()
  | Incomplete  -> ()
  | Complete    -> ()
  | ProcessingIn _ -> ()
  | InProgress _ -> ()
  | WorkerStatus (_,_) -> ()
  | AddedAxiom  -> ()
  | GlobRef (_,_,_,_,_) -> ()
  | GlobDef (_,_,_,_) -> ()
  | FileDependency (_,_) -> ()
  | FileLoaded (_,_) -> ()
  | Custom (_,_,_) -> ()
  | Message (lvl,loc,msg) ->
    let msg = (Pp.unrepr (transf (Pp.repr msg))) in
    let fb' = { doc_id   = fb.doc_id; 
    	        span_id  = fb.span_id;
		route    = fb.route;
		contents = (Message (lvl,loc,msg)); } in
    Coqloop.coqloop_feed fb'

let _fhandle = Feedback.add_feeder coqloop_feed
let _ = Feedback.del_feeder (3) (* _fhandle - 1 *)

