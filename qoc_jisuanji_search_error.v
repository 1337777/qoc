From Qoc Require Import Jisuanji .

(** 

短 :: 示例：“A ; [> W & [+ T1 | T2 ] ]”。

Short :: Example : "A ; [> W & [+ T1 | T2 ] ]" .


Outline ::
 * PART 1 : SEARCH , ERRORS . 第1部分 : 
 * PART 2 :  . 第2部分 : 


*)


(** * PART 1 : SEARCH , ERRORS . *)

(**
Nat.add = 
固定 add (n m : nat) {构 n} : nat := 匹配 n 与
                                  | 0 => m
                                  | S p => S (add p m)
                                  结束
     : nat -> nat -> nat
*)

Search Nat.add .
(** f_equal2_plus  用 x1 y1 x2 y2 : nat, x1 = y1 -> x2 = y2 -> x1 + x2 = y1 + y2
plus_n_O  用 n : nat, n = n + 0
plus_O_n  用 n : nat, 0 + n = n
plus_n_Sm  用 n m : nat, S (n + m) = n + S m
...
 *)
Search ( ?n + 0 ) .
(** plus_n_O  用 n : nat, n = n + 0 *)
SearchRewrite ( ?n + 0 )  .
(** plus_n_O  用 n : nat, n = n + 0 *)
Search ( ?n = ?n + 0 ) .
(** plus_n_O  用 n : nat, n = n + 0 *)
Search ( ?n + 0 = ?n ) .
(** ___ *)

Lemma mylemma : forall n : nat, 0 + n = n .
Proof .
  intros n .
  reflexivity .
Qed .

(* Lemma mylemma : forall n : nat, n + 0 = n . *)
Fail Lemma mylemma : forall n : nat, n + 0 = n .

Lemma mylemma' : forall n : nat, n + 0 = n .
Proof .
  intros n .
  (** reflexivity . *)
  Fail reflexivity .
  
  Search ( ?n + 0 ) .
  (** plus_n_O  用 n : nat, n = n + 0 *)
  rewrite <- plus_n_O .
  reflexivity .
Qed.


(*
Lemma 
Section s.
  Fail End e.
End s.
Fail Print ff.
Definition a := 1.
Fail Definition a := 1.
(*Dddefinition a := 1.*)
Fail Definition b := 1 + true. 
Local Set SsrIdents .
Print Table SsrIdents .
Unset SsrIdents .
Print Table SsrIdents .
Module BB .
Module Export AA.
Export Set jisuanji_SsrIdents .
Print Table SsrIdents .
End AA.
Print Table SsrIdents .
End BB.
Print Table SsrIdents .
Unset jisuanji_SsrIdents .
Print Table SsrIdents .
Print Tables.
*)

(** ** alt
----------------------------------------------------------------------------- *)

(**
----------------------------------------------------------------------------- *)


(** * PART 2 :  *)
