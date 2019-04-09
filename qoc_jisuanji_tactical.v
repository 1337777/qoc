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
  解构 n. Undo.
  解构 n  ; 解构 b . Undo .

  解构 n; ( 解构 b ;
                [> idtac | idtac | idtac | idtac ] ) . Undo.
  解构 n; ( inner: 解构 b ;
               [> idtac | idtac ] ) . Undo.
  解构 n; inner: 解构 b ;
                       [> idtac | idtac ]  . Undo.
  解构 n; ( 解构 b;
                [ idtac | idtac ] ) . Undo.

  (** nei *)
  解构 n; ( 内: 解构 b ;
               [> idtac | idtac ] ) . Undo.
  
Abort .

Goal forall B C D : Prop, (False /\ B) /\ (C /\ D).
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




(** --------------------------------------------------- *)




Goal forall n : nat + nat , forall b : bool + bool , ( n = n /\ b = b ) .
  intros n b.
  destruct n. Undo.
  destruct n  ; destruct b . Undo .

  destruct n; ( destruct b ;
                [> idtac | idtac | idtac | idtac ] ) . Undo.
  destruct n; ( inner: destruct b ;
               [> idtac | idtac ] ) . Undo.
  destruct n; inner: destruct b ;
                       [> idtac | idtac ]  . Undo.
  destruct n; ( destruct b;
                [ idtac | idtac ] ) . Undo.

  (** nei *)
  destruct n; ( 内: destruct b ;
               [> idtac | idtac ] ) . Undo.
  
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
