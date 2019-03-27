From Qoc Require Import Jisuanji .

(**

(**MEMO: [W] is the weakener and [E] is the end . And [ (W -> E) -> E ] is some style of double negation of [W] above the end [E] ( instead of the common bottom/end which is [False] ) *)
(**MEMO: the identifier [p] is some outer-parameter ; the sense  for the identifier [x] is not binary ,
	 possibilities are : [simultaneous] identifier , [parametric]/singly/pointwise identifier , [none] identifier *)

+ simultaneous have w_ , w_x : x / W p x
  1(instance): x |- W p x
  2(generalized): x ; w_ : (forall x , W p x) ; w_x : W x |- E p x
  * have w : W
    1(instance): |- W
    2(generalized): w : W |- E

+ simultaneous suffices w_ : x / W p x
  1(generalized): x ; w_ : (forall x , W p x) |- E p x
  2(instance): x |- W p x
  * suffices w : W
    1(generalized): w : W |- E
    2(instance): |- W

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

+ simultaneous have w_ , w_x : x / W p x
  := gen have w_ , w_x : x / W p x
  * have w : W
    := have w : W

+ simultaneous suffices w_ : x / W p x
  := wlog suff w_ : x / W p x
  * suffices w : W
    := suff w : W

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

Section Move .

  Definition lem1 : forall n : nat , nat .
  Proof .
    移动 => m . exact : m .
  Defined .

End Move .

Section Generalization .

  Variable E : forall (p : bool) (x : nat) , Type .
  Variable W : forall (p : bool) (x : nat) , Type .
  Variable p : bool .

  Lemma lemma1 : forall x : nat , E p x .
  Proof.
    intros x .

    simultaneous have w_ , w_x : x / W p x . Show 2 . Undo .
    同时 具有 w_ , w_x : x / W p x . Show 2 . Undo .
    (** 1(instance): x |- W p x
       2(generalized): x ; w_ : (forall x , W p x) ; w_x : W x |- E p x *)
    have w : W p x . Show 2. Undo.
    具有 w : W p x . Show 2. Undo.
    (** 1(instance): |- W
       2(generalized): w : W |- E *)

    (** ----- *)

    simultaneous suffices w_ : x / W p x . Show 2 . Undo .
    同时 满足 w_ : x / W p x . Show 2 . Undo .
    (** 1(generalized): x ; w_ : (forall x , W p x) |- E p x
        2(instance): x |- W p x *)
    suffices w : W p x . Show 2 . Undo .
    满足 w : W p x . Show 2 . Undo .
    (** 1(generalized): w : W |- E
        2(instance): |- W *)
    
    (** ----- *)

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
    
    (** ----- *)

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
    
  Abort All.  
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

End Tactics .

