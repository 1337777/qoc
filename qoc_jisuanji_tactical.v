From Qoc Require Import Jisuanji .

Goal forall n : nat + nat , forall b : bool + bool , pair n  b = pair n  b.
  intros n b.
  destruct n; swap 1 2 . Undo.
  Fail (destruct n; destruct b); [ | ] . Undo.

  destruct n; (destruct b;$ inner [ | ]) . Undo.
  destruct n; (destruct b; [ | ]) . Undo.
  (* BUG : refman says:  _ ; [ _ ] should precedes _ ; _ *)
  Fail destruct n; destruct b; [ | ] .


  destruct n; (destruct b; [ | ]) . Undo.
  Fail destruct n; (destruct b; [> | ]) . Undo.
  Fail destruct n; (destruct b;$ outer [ | ]) . Undo.
  
Abort .

















(*

Goal forall n : nat + nat , forall b : bool + bool , (n , b) = (n , b).
  intros n b.
  destruct n; only 2: destruct b. Undo.
  destruct n; only 2: [>  ] .
  1,2: destruct b.
  Restart. intros n b.
  destruct n; destruct b; only 2-4 : swap 1 2.
  Fail !: reflexivity.
  2 : { !: reflexivity. }
  repeat idtac. Fail progress idtac.
  all: destruct n; destruct b; reflexivity. Undo.
  par: destruct n; destruct b; reflexivity.
  all: reflexivity.
  par: reflexivity.
  
Abort .
*)
Ltac time_constr1 tac :=
  let eval_early := match goal with _ => restart_timer "(depth 1)" end in
  let ret := tac () in
  let eval_early := match goal with _ => finish_timing ( "Tactic evaluation" ) "(depth 1)" end in
  ret.

Goal True.
let v := time_constr
       ltac:(fun _ =>
               let x := time_constr1 ltac:(fun _ => (constr: ( 10 - 3))) in
               let y := time_constr1 ltac:(fun _ => eval compute in x) in
               ( constr : (  y  ) ) ) in
  pose v.
Abort.

Goal  True.

  let t  m := match m with
             (fun k => ( 3 + ?j ))  => let p := constr:(fun k : nat => 9 + j) in idtac p
           end in
  t  (fun n => 3 + (n + 2)) .
  
  let t  m := match m with
                (fun k => ( 3 + @?j k ))  => let p :=  constr:(fun c : nat => 9 + j c)  in
                                          let q :=  eval hnf in p in
  idtac p "------" q
           end in
  t  (fun n => 3 + (n + 2)) .

Abort.
