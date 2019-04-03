From Qoc Require Import Jisuanji .

(**MEMO: 

  短 :: 。
  
  Short :: some parameter "p" which parametrizes many definitions and lemmas "d" , "l" may all be packaged into one , and then later this parameter may be instantiated to produce the instantiated definitions and lemmas "Q.d" , "Q.l" whose ( must-be-new ) names are prefixed by any chosen prefix name "Q" ... 



*)

(** simple parametrization *)
Module Type p_dl.

  Parameter p : Type .
  
  Definition d := prod p p .

  Definition l : p -> d .
  Proof.
    intros x.
    exact (pair x x).
  Defined.

End p_dl.

Declare Module nat_dl : p_dl with Definition p := nat.
Print nat_dl.l.
Eval compute in (nat_dl.l 3).
Declare Module bool_dl : let Definition p := bool in p_dl .
Eval compute in (bool_dl.l false).

(** complex parametrization *)  

Module Type MM.

Definition T := nat.

Definition x := 0.

Definition y : bool.
exact true.
Defined.
End MM.

Declare Module M : MM .

Module Type SIG.

Parameter T : Set.

Export Set Printing Notations.
Notation _carrier :=  T.

Local Parameter Inline x : T.

End SIG.

Module N : SIG with Definition T := nat  := M.
Reset N.

Module Type ZZ (M : MM).
   Definition z : nat := 1 + M.x .
End ZZ.

Module N : SIG with Definition T := nat .
   Include M.
   Fail Definition x :=  1 .

   (** may be bad *)
   Definition z : nat := 1 + M.x . Print z.
   Reset z.
   Include (ZZ M). Print z.
   Reset z.
   
   Definition z : nat := 1 + x . Print z.   
   Reset z.
   Include ZZ. Print z.
End N.

Print N.T.
Print N.x.
Fail Print N.y.
Fail Print N.z.

Declare Module B : SIG with Definition T := bool.

Module Type Two (X : SIG) (* outer-parameter *)
     <: SIG (* only-check that it is more precise than SIG *) .

Declare Module Y : SIG with Definition T := X.T . (* inner-parameter , which will also be component of the result *)

Print X.x.
Print Y.x.
Fail Print X.y.
Fail Print Y.y.

Definition T := (X.T * Y.T)%type.
Reset T.

Fail Check _carrier. (* Notation _carrier is not yet imported *)
Unset Printing Notations. (* disable for now *)
Import Y.
Print T. (* Y.T is imported *)
Check _carrier. (* Notation _carrier is imported *)
Check T.  (* Export Set Printing Notation is imported *)
(*output:
 _carrier
     : Set *)
Fail Print x. (* Y.x is local and therefore not imported *)

Definition T := (X.T * _carrier)%type. (* same as above because the Notation is imported *)
Print T . (* the imported Y.T is now masked *)
Reset T .
Definition T := (_carrier * _carrier)%type. (* same as above because the sharing constraint says that X.T = Y.T ( = _carrier ) *)

Definition x : T := (pair X.x Y.x) .

End Two.

Print Module Type Two.
Fail Declare Module P : (Two N) with Module Y := B .
Fail Declare Module P : (Two B) with Module Y := N .

Declare Module R : (Two M) with Module Y := N .
Print R.x. (* M.x is unfolded in ( R.x = (M.x , R.Y.x) ) because the component x of SIG is inlined ;
and certainly R.Y.x ( = N.x ) will not be unfolded because Y is some inner (not-outer) parameter of Two *)
Eval compute in (fst R.x + snd R.x).

Declare Module S : ! ( (Two M) with Module Y := N ) .
Print S.x. (* M.x is not unfolded in ( R.x = (M.x , S.Y.x) ) because the inlining of the component x of SIG is disabled by the command [!] *)
Eval compute in (fst S.x + snd S.x).

Declare Module Q : let Module Y := M in (Two N) .
Print Q.x. (* in ( Q.x = (N.x , Q.Y.x) ) , certainly  N.x is already not unfoldable *)
Eval compute in ( snd Q.x + fst Q.x).
