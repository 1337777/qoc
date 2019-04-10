From Qoc Require Import Jisuanji .

(** 

短 :: 一个命令/策略“A”可以对目标/问题起作用并产生许多新的较小的子目标。然后，许多“替代”命令中的一些命令“D”可以在这些子目标中的一个附近“序列”。但是这个“序列”子目标是哪个，这是“替代”命令？

Short :: one command/tactic "A" may act on a goal/problem and generate many new smaller subgoals . Then some command "D" among many "alternative" commands may be in "sequence" near one of these subgoals . But which is this "sequence" subgoal and which is this "alternative" command ?

 Example :  "A ; sequence [> ( alternative ( B1 => C | B2 => D ) ) & E ]"

Outline ::
* PART1 : SEQUENCING TACTICS
* PART2 : ALTERNATING TACTICS  *)

(** PART1 : SEQUENCING TACTICS *)

Goal forall n : nat + nat , forall b : bool + bool , ( n = n /\ b = b ) .
  intros n b.
  解构 n. destruct b.  Undo 2.
  解构 n  ; 解构 b . Undo .

  解构 n; ( 解构 b ;
                [> idtac & idtac & idtac & idtac ] ) . Undo.
  解构 n; ( 内: 解构 b ;
               [> idtac & idtac ] ) . Undo.
  解构 n; 内: 解构 b ;
                       [> idtac & idtac ]  . Undo.
  解构 n; ( 解构 b;
                [ idtac & idtac ] ) . Undo.
  
Abort .

Goal forall B C D : Prop, (False /\ B) /\ (C /\ D).
  split. Undo.
  split; split. Undo.
  做 2 split. Undo.
  重复 split. Undo.
  进展 重复 split.
  1 : {
    失败 进展 重复 split.
    尝试 进展 重复 split.
    承认.
  }

Abort.

(*
Goal forall n: Nat + nat, forall b: Bool + bool, (n = n/\ b = b).
  Intros n b.
  Jiěgòu n. Undo.
  Jiěgòu n  ; jiěgòu b. Undo.

  Jiěgòu n; (jiěgòu b;
                [> idtac & idtac & idtac & idtac] ). Undo.
  Jiěgòu n; (inner: Jiěgòu b;
               [> idtac & idtac] ). Undo.
  Jiěgòu n; inner: Jiěgòu b;
                       [> idtac & idtac]  . Undo.
  Jiěgòu n; (jiěgòu b;
                [idtac & idtac] ). Undo.

  (** Nei*)
  jiěgòu n; (nèi: Jiěgòu b;
               [> idtac & idtac] ). Undo.
  
Abort.

Goal forall B C D: Prop, (False/\ B)/\ (C/\ D).
  Split; split. Undo.
  Zuò 2 split. Undo.
  Chóngfù split. Undo.
  Jìnzhǎn chóngfù split.
  1: {
    Shībài jìnzhǎn chóngfù split.
    Chángshì jìnzhǎn chóngfù split.
    Chéngrèn.
  }

Abort.

*)

(** --------------------------------------------------- *)




Goal forall n : nat + nat , forall b : bool + bool , ( n = n /\ b = b ) .
  intros n b.
  destruct n. Undo.
  destruct n  ; destruct b . Undo .

  destruct n; ( destruct b ;
                [> idtac & idtac & idtac & idtac ] ) . Undo.
  destruct n; ( inner: destruct b ;
               [> idtac & idtac ] ) . Undo.
  destruct n; inner: destruct b ;
                       [> idtac & idtac ]  . Undo.
  destruct n; ( destruct b;
                [ idtac & idtac ] ) . Undo.

  (** nei *)
  destruct n; ( 内: destruct b ;
               [> idtac & idtac ] ) . Undo.
  
Abort .

Goal forall B C D : Prop, (False /\ B) /\ (C /\ D).
  split; split. Undo.
  do 2 split. Undo.
  repeat split. Undo.
  progress repeat split.
  1 : {
    Fail progress repeat split.
    try progress repeat split.
    admit.
  }

Abort.


(** PART2 : ALTERNATING TACTICS  *)

Goal forall n : nat + nat , forall b : bool + bool , ( n = n /\ b = b ) .
  intros.
  Fail outer alts [ ] .
  outer alts [fail | idtac].
  Fail alts [ ] .
  alts [fail | idtac].

  Fail outer alts [ fail | idtac "a" | idtac "b"  ]; idtac "c"; fail .
  (* a c b c *)
  Fail alts [ fail | idtac "a" | idtac "b"  ]; idtac "c"; fail .
  (* a c *)
  Fail no_outer (outer alts [ idtac "a" | idtac "b"  ]); idtac "c"; fail .
  (* a c *)

  Fail (          outer inner alter idtac "a" then outer alts [idtac "b" | idtac "b'"]; fail
                           else outer alts [idtac "i" | idtac "i'"] ); idtac "o"; fail .
  (*  a b b' i o i' o *)
  Fail (                inner alter idtac "a" then outer alts [idtac "b" | idtac "b'"]; fail
                          else outer alts [idtac "i" | idtac "i'"] ); idtac "o"; fail .
  (* a b b' i o *)
  Fail ( no_outer outer inner alter idtac "a" then outer alts [idtac "b" | idtac "b'"]; fail
                           else outer alts [idtac "i" | idtac "i'"] ); idtac "o"; fail .
  (* a b b' i o *)
  Fail (          outer       alter idtac "a" then outer alts [idtac "b" | idtac "b'"]; fail
                          else outer alts [idtac "i" | idtac "i'"] ); idtac "o"; fail .
  (* a b b' *)
  Fail (no_outer  outer       alter idtac "a" then outer alts [idtac "b" | idtac "b'"]; fail
                          else outer alts [idtac "i" | idtac "i'"] ); idtac "o"; fail .
  (* a b b' *)
  Fail (                      alter idtac "a" then outer alts [idtac "b" | idtac "b'"]; fail
                          else outer alts [idtac "i" | idtac "i'"] ); idtac "o"; fail .
  (* a b b' *)

  Fail (          outer       alter idtac "a" then outer alts [idtac "b" | idtac "b'"]
                          else outer alts [idtac "i" | idtac "i'"] ); idtac "o"; fail .
  (* a b o b' o *)
  Fail (no_outer  outer       alter idtac "a" then outer alts [idtac "b" | idtac "b'"]
                          else outer alts [idtac "i" | idtac "i'"] ); idtac "o"; fail .
  (* a b o *)
  Fail (                      alter idtac "a" then outer alts [idtac "b" | idtac "b'"]
                          else outer alts [idtac "i" | idtac "i'"] ); idtac "o"; fail .
  (* a b o *)

Abort.
