From Qoc Require Import Jisuanji .
Import ssreflect .

(**MEMO: 

  短 :: 为了从“A”到“E”的目标，搜索/猜测某些“S”从“A”到“S”然后从“S”变为“E”可能更明智/更具策略性“。
  
  Short :: for the goal of going from "A" to "E" , it may be more sensible/tactical to search/guess some "S" such to go from "A" to "S" then to go from "S" to "E" .

  It may be more-sensible to refine/start/open the top of some deduction/proof of some end/goal [A |- E] by sequencing this deduction into two more-sensible parts/halves [A |- S] and [A |- S -> E] , where oneself shall search/guess/devine the mediator [S] by using the contextual sense of the end/goal . 

  In the most general text , [E] is the END/goal . And [S] is some SEARCHED/guessed/devined weaker SUB-end/goal which suffices ( expressed as [ S -> E ] ) for the end/goal [E] .

  In the less general text , [W] is some searched/guessed/devined WEAKENER which defines this particular sub-end/goal [ S := (W -> E) ] ( the end UNDER [W] ) , which suffices ( [ (W -> E) -> E ] ) for the end/goal [E] . Alternatively , oneself may transpose this precedent result and view the sufficiency expression as [ W -> E ] and the sub-end/goal as [ S := ( (W -> E) -> E ) ] ( the RELATIVE [W] , which is some style of double negation of [W] above the end [E] not the bottom [False] )

  Everythere , the identifier [p] is some outer-argument/parameter and [x] is some (varying) inner-argument . And the sense for the identifier [x] is not binary , possible senses are : [simultaneous] identifier , [parametric]/singly/pointwise identifier , [none] identifier .

-----

+ simultaneous have s_ , s_x : x / S p x
  1(instance): x |- S p x
  2(generalized): x ; s_ : (forall x , S p x) ; s_x : S x |- E p x
  * have s : S
    1(instance): |- S
    2(generalized): s : S |- E

+ simultaneous suffices s_ : x / S p x
  1(generalized): x ; s_ : (forall x , S p x) |- E p x
  2(instance): x |- S p x
  * suffices s : S
    1(generalized): s : S |- E
    2(instance): |- S

+ parametric have_relatively w : x / W p x
  1(instance): x |- (forall x , W p x -> E p x) -> E p x
  2(generalized): x ; w : W p x |- E p x
  * have_relatively w : W
    1(instance): |- (W -> E) -> E
    2(generalized): w : W |- E
  * have_under m : W
    1(instance): |- W -> E
    2(generalized): m : (W -> E) |- E

+ parametric suffices_relatively w : x / W p x
  1(generalized): x ; w : W p x |- E p x
  2(instance): x |- (forall x , W p x -> E p x) -> E p x
  * suffices_relatively w : W
    1(generalized): w : W |- E
    2(instance): |- (W -> E) -> E
  * suffices_under m : W
    1(generalized): m : (W -> E) |- E
    2(instance): |- W -> E

-----

+ simultaneous have s_ , s_x : x / S p x
  := gen have s_ , s_x : x / S p x
  * have s : S
    := have s : S

+ simultaneous suffices s_ : x / S p x
  := wlog suff s_ : x / S p x
  * suffices s : S
    := suff s : S

+ parametric have_relatively w : x / W p x
  := wlog w : x / W a x
  * have_relatively w : W
  := ??
  * have_under m : W
    := have suff m : W

+ parametric suffices_relatively w : x / W p x
  := ??
  * suffices_relatively w : W
    := suff have w : W
  * suffices_under m : W
    := ??

*)

Module Tactics .
  
Module Generalization .
Parameter A : forall (p : bool) , Type .
Parameter E : forall (p : bool) (x : bool) , Type .
Parameter S : forall (p : bool) (x : bool) , Type .
Parameter W : forall (p : bool) (x : bool) , Type .

Section section1 .

  Variable p : bool .

  Lemma lemma1 : A p -> forall x : bool , E p x .
  Proof.
    intros a x .

    simultaneous have s_ , s_x : x / S p x . Show 2 . Undo .
    (** Tóngshí jùyǒu *)
    同时 具有 s_ , s_x : x / S p x . Show 2 . Undo .
    (** 1(instance): x |- S p x
       2(generalized): x ; s_ : (forall x , S p x) ; s_x : S x |- E p x *)
    have s : S p x . Show 2. Undo.
    (** Jùyǒu *)
    具有 s : S p x . Show 2. Undo.
    (** 1(instance): |- S
       2(generalized): s : S |- E *)
  Abort .

  Lemma lemma1 : A p ->  forall x : bool , E p x .
  Proof.
    intros a x .

    simultaneous suffices s_ : x / S p x . Show 2 . Undo .
    (** Tóngshí mǎnzú *)
    同时 满足 s_ : x / S p x . Show 2 . Undo .
    (** 1(generalized): x ; s_ : (forall x , S p x) |- E p x
        2(instance): x |- S p x *)
    suffices s : S p x . Show 2 . Undo .
    (** mǎnzú *)
    满足 s : S p x . Show 2 . Undo .
    (** 1(generalized): s : S |- E
        2(instance): |- S *)
  Abort .

  Lemma lemma1 : A p -> forall x : bool , E p x .
  Proof.
    intros a x .

    parametric have_relatively w : x / W p x . Show 2 . Undo .
    (** Cān jùyǒu_xiāngduì *)
    参 具有_相对 w : x / W p x . Show 2 . Undo .
    (** 1(instance): x |- (forall x , W p x -> E p x) -> E p x
        2(generalized): x ; w : W p x |- E p x *)
    have_relatively w : W p x . Show 2 . Undo .
    (** Cān jùyǒu_xiāngduì *)
    具有_相对 w : W p x . Show 2 . Undo .
    (** 1(instance): |- (W -> E) -> E
       2(generalized): w : W |- E *)
    have_under m : W p x . Show 2 . Undo .
    (** Jùyǒu_xià *)
    具有_下 m : W p x . Show 2 . Undo .
    (** 1(instance): |- W -> E
       2(generalized): m : (W -> E) |- E *)
  Abort .

  Lemma lemma1 : A p -> forall x : bool , E p x .
  Proof.
    intros a x .
    
    parametric suffices_relatively w : x / W p x . Show 2 . Undo .
    (** Cān mǎnzú_xiāngduì *)
    参 满足_相对 w : x / W p x . Show 2 . Undo .
    (** 1(generalized): x ; w : W p x |- E p x
        2(instance): x |- (forall x , W p x -> E p x) -> E p x *)
    suffices_relatively w : W p x . Show 2 . Undo .
    (** Mǎnzú_xiāngduì *)
    满足_相对 w : W p x . Show 2 . Undo .
    (** 1(generalized): w : W |- E
        2(instance): |- (W -> E) -> E *)
    suffices_under m : W p x . Show 2 . Undo .
    (** Mǎnzú_xià *)
    满足_下 m : W p x . Show 2 . Undo .
    (** 1(generalized): m : (W -> E) |- E
        2(instance): |- W -> E *)
  Abort.
End section1.

Section Generalization_example .

Lemma quo_rem_unicity ( d : nat) :
  forall ( q1 q2 r1 r2 : nat ) ,
    q1*d + r1 = q2*d + r2 ->
    r1 < d -> r2 < d ->
    (pair q1 r1) = (pair q2 r2) .
Proof .
  intros q1 q2 r1 r2 .

  wlog: q1 q2 r1 r2 / q1 <= q2 . Show 2 . Undo .
  parametric have_relatively w : q1 q2 r1 r2 / q1 <= q2 . Show 2 . Undo .
  (** Cān jùyǒu_xiāngduì *)
  参 具有_相对 w : q1 q2 r1 r2 / q1 <= q2 . Show 2 . Undo .
  (** 1(instance): (用 q3 q4 r3 r4 : nat, q3 <= q4 -> 
                       q3 * d + r3 = q4 * d + r4 -> r3 < d -> r4 < d -> (q3, r3) = (q4, r4)) 
                  -> q1 * d + r1 = q2 * d + r2 -> r1 < d -> r2 < d -> (q1, r1) = (q2, r2) 
      2(generalized): w : q1 <= q2 |- q1 * d + r1 = q2 * d + r2 -> r1 < d -> r2 < d -> (q1, r1) = (q2, r2) *)

Abort .

End Generalization_example .
End Generalization .

Definition tactics_move_apply_exact_elim_case
  : forall n : nat , nat .
Proof .
  move => m . Undo .
  (** Yídòng *)
  移动 => m .

  apply : m . Undo .
  (** Yìngyòng *)
  应用 : m . Undo .

  exact : m . Undo .
  (** Quèqiè *)
  确切 : m . Undo .

  elim : m . Undo .
  (** Xiāochú *)
  消除 : m . Undo .

  case : m . Undo .
  (** Lìzi *)
  例子 : m . Undo .
  
Abort.

Lemma tactics_abstract (n m : nat) : True.

  have [:Sm] @plus_n_Sm : nat .
  { apply: (plus n).
    abstract: Sm.
    { exact: (S m).
    }
  }

  Restart .

  (** Jùyǒu *)
  具有 [:Sm] @plus_n_Sm : nat .
  { (** Yìngyòng *)
    应用: (plus n).
    (** Chōuxiàng *)
    抽象: Sm.
    { (** Quèqiè *)
      确切: (S m).
    }
  }

Abort.

Definition tactics_rewrite : forall n m : nat , n = m -> m = n .
Proof .
  intros n m H.
  rewrite H . Undo .
  (** Gǎixiě *)
  改写 H . Undo .
Abort.


Lemma tactic_pose : True.
  pose f x y := x + y . Undo .
  (** Bǎi *)
  摆 f x y := x + y. Undo .

  pose fix f (x y : nat) {struct x} : nat :=
    if x is S p then S (f p y) else 0 . 
  Undo .
  (** Bǎi gùdìng *)
  摆 固定 f (x y : nat) {struct x} : nat :=
    if x is S p then S (f p y) else 0 .
  Undo .
Abort .

Lemma tactic_set (x y z : nat) :  x + y = z.
  set t := _ x.  Undo .
  (** Bǎiliè *)
  摆列 t := _ x . Undo .
Abort .

Lemma tactic_lock n m : (S n) + m = match (S n) with
                               S p => m + (S p)
                             | 0 => m + 0
                             end.
  rewrite {1}[S]lock .
  rewrite -lock. Undo.
  unlock .
  move: (S n) . Restart .

  (** Gǎixiě *)
  改写 {1}[S]lock .
  (** Kāisuǒ *)
  开锁 .
  (** Yídòng *)
  移动: (S n). 
Abort.

Definition add :=
( 固定 add (n m : nat) {构 n} : nat := 匹配 n 与
                                  | 0 => m
                                  | S p => S (add p m)
                                  结束 ) .
(** Bù jiǎnhuà *)
Definition addn := 不简化 add .

Lemma notation_nosimpl : forall n m,
    ( if (addn (S n) (S m))
      is (S p ) then p
      else 0 )
    =  (addn (S m) n) .

  intros n m .

  simpl . fold addn . 
  move: (S m).
Abort.

Lemma tactic_congr x y :
  x + (y * (y + x - x)) = (x * 1) + (y + 0) * y.

  congr plus . Undo .
  (** Cítóu *)
  词头 plus . Undo .

  congr ( _ + (_ * _)) . Undo .
  (** Cítóu *)
  词头 ( _ + (_ * _)) . Undo .
Abort .

Inductive test : nat -> Prop :=
| C1 : forall n , n = 1 -> test n
| C2 : forall n , n = 2 -> test n
| C3 : forall n , n = 3 -> test n
| C4 : forall n , n = 4 -> test n 
| C5 : forall n , n = 5 -> test n .

Lemma tactic_last n (t : test n) : True.
  case : t ;
    last 2 [ move => k3
           | move => k4 ] . Undo .
  (** Lìzi *)
  例子 : t ;
    (** Hòu *)
    后 2 [ (** Yídòng *) 移动 => k3
         | (** Yídòng *) 移动 => k4 ] . Undo .

  case : t ;
     first last . Undo .
  (** Lìzi *)
  例子 : t ;
    (** Qián hòu *)
    前 后 .
Abort.

End Tactics .

Print Tactics .