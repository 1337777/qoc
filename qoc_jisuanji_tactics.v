From Qoc Require Import Jisuanji .
Import ssreflect .

(**MEMO: 

  In the most general text , [E] is the END/goal . And [S] is some weaker SUB-end/goal which suffices ( expressed as [ S -> E ] ) for the end/goal [E] .

  In the less general text , [W] is some WEAKENER which defines this sub-end/goal [ S := (W -> E) ] ( the end UNDER [W] ) , which suffices ( [ (W -> E) -> E ] ) for the end/goal [E] . Alternatively , oneself may transpose this precedent result and view the sufficiency expression as [ W -> E ] and the sub-end/goal as [ S := ( (W -> E) -> E ) ] ( the RELATIVE [W] , which is some style of double negation of [W] above the end [E] not the bottom [False] )

  Everythere , the identifier [p] is some outer-parameter and [x] is some (varying) inner-argument . And the sense for the identifier [x] is not binary , possible senses are : [simultaneous] identifier , [parametric]/singly/pointwise identifier , [none] identifier .

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

Section Generalization .

  Variable E : forall (p : bool) (x : bool) , Type .
  Variable S : forall (p : bool) (x : bool) , Type .
  Variable W : forall (p : bool) (x : bool) , Type .
  Variable p : bool .

  Lemma lemma1 : forall x : bool , E p x .
  Proof.
    intros x .

    simultaneous have s_ , s_x : x / S p x . Show 2 . Undo .
    同时 具有 s_ , s_x : x / S p x . Show 2 . Undo .
    (** 1(instance): x |- S p x
       2(generalized): x ; s_ : (forall x , S p x) ; s_x : S x |- E p x *)
    have s : S p x . Show 2. Undo.
    具有 s : S p x . Show 2. Undo.
    (** 1(instance): |- S
       2(generalized): s : S |- E *)
  Abort .

  Lemma lemma1 : forall x : bool , E p x .
  Proof.
    intros x .

    simultaneous suffices s_ : x / S p x . Show 2 . Undo .
    同时 满足 s_ : x / S p x . Show 2 . Undo .
    (** 1(generalized): x ; s_ : (forall x , S p x) |- E p x
        2(instance): x |- S p x *)
    suffices s : S p x . Show 2 . Undo .
    满足 s : S p x . Show 2 . Undo .
    (** 1(generalized): s : S |- E
        2(instance): |- S *)
  Abort .

  Lemma lemma1 : forall x : bool , E p x .
  Proof.
    intros x .

    parametric have_relatively w : x / W p x . Show 2 . Undo .
    参 具有_相对 w : x / W p x . Show 2 . Undo .
    (** 1(instance): x |- (forall x , W p x -> E p x) -> E p x
        2(generalized): x ; w : W p x |- E p x *)
    have_relatively w : W p x . Show 2 . Undo .
    具有_相对 w : W p x . Show 2 . Undo .
    (** 1(instance): |- (W -> E) -> E
       2(generalized): w : W |- E *)
    have_under m : W p x . Show 2 . Undo .
    具有_下 m : W p x . Show 2 . Undo .
    (** 1(instance): |- W -> E
       2(generalized): m : (W -> E) |- E *)
  Abort .

  Lemma lemma1 : forall x : bool , E p x .
  Proof.
    intros x .
    
    parametric suffices_relatively w : x / W p x . Show 2 . Undo .
    参 满足_相对 w : x / W p x . Show 2 . Undo .
    (** 1(generalized): x ; w : W p x |- E p x
        2(instance): x |- (forall x , W p x -> E p x) -> E p x *)
    suffices_relatively w : W p x . Show 2 . Undo .
    满足_相对 w : W p x . Show 2 . Undo .
    (** 1(generalized): w : W |- E
        2(instance): |- (W -> E) -> E *)
    suffices_under m : W p x . Show 2 . Undo .
    满足_下 m : W p x . Show 2 . Undo .
    (** 1(generalized): m : (W -> E) |- E
        2(instance): |- W -> E *)
  Abort. 
End Generalization .

Section Generalization_example .

Lemma quo_rem_unicity ( d : nat) :
  forall ( q1 q2 r1 r2 : nat ) ,
    q1*d + r1 = q2*d + r2 ->
    r1 < d -> r2 < d ->
    (pair q1 r1) = (pair q2 r2) .
Proof .
  intros q1 q2 r1 r2 .

  wlog: q1 q2 r1 r2 / q1 <= q2 . Undo .
  parametric have_relatively w : q1 q2 r1 r2 / q1 <= q2 . Show 2 . Undo .
  (** 1(instance): (用 q3 q4 r3 r4 : nat, q3 <= q4 -> 
                       q3 * d + r3 = q4 * d + r4 -> r3 < d -> r4 < d -> (q3, r3) = (q4, r4)) 
                  -> q1 * d + r1 = q2 * d + r2 -> r1 < d -> r2 < d -> (q1, r1) = (q2, r2) 
      2(generalized): w : q1 <= q2 |- q1 * d + r1 = q2 * d + r2 -> r1 < d -> r2 < d -> (q1, r1) = (q2, r2) *)

Abort .

End Generalization_example .

Definition lem1 : forall n : nat , nat .
Proof .
  move => m . Undo .
  移动 => m .

  exact : m . Undo .
  确切 : m .
Abort.

Lemma tactic_pose : True.
  pose f x y := x + y . Undo .
  摆 f x y := x + y. Undo .

  pose fix f (x y : nat) {struct x} : nat :=
    if x is S p then S (f p y) else 0 . 
  Undo .
  摆 固定 f (x y : nat) {struct x} : nat :=
    if x is S p then S (f p y) else 0 .
  Undo .
Abort .

Lemma tactic_set (x y z : nat) :  x + y = z.
  set t := _ x.  Undo .
  摆列 t := _ x . Undo .
Abort .

Inductive test : nat -> Prop :=
| C1 : forall n , n = 1 -> test n
| C2 : forall n , n = 2 -> test n
| C3 : forall n , n = 3 -> test n
| C4 : forall n , n = 4 -> test n 
| C5 : forall n , n = 5 -> test n .

Lemma tactic_last n (t : test n) : True.
  case : t ;
    last 2 [ move => k3 | move => k4 ] . Undo .
  例子 : t ;
    后 2 [ 移动 => k3 | 移动 => k4 ] . Undo .

  case : t ;
     first last . Undo .
  例子 : t ;
    前 后 .
Abort.

End Tactics .

Print Tactics .