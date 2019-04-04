From Qoc Require Import Jisuanji .

(**MEMO: 

  短 :: 一些参数“p”参数化许多定义和引理“d”和“l”都可以打包成一个;然后可以实例化该参数“p”以产生实例化的定义和引理：“Q.d”和“Q.l”，其新名称以任何选择的前缀名称“Q”作为前缀 ...
  
  Short :: some parameter "p" which parametrizes many definitions and lemmas "d" and "l" may all be packaged into one ; and then later this parameter "p" may be instantiated to produce the instantiated definitions and lemmas : "Q.d" and "Q.l" whose new names are prefixed by any chosen prefix name "Q" ... 
*)

包裹 p_dl.
(** Bāoguǒ p_dl.  *)

  参数 p : 类型 .
  (** Cānshù p: Lèixíng. *)

  定义 d := prod p p .
  (** Dìngyì d:= Prod p p. *)
  定义 l : p -> d .
  (** Dìngyì l: P -> d. *)
  证明.
    (** Zhèngmíng.*)
    介绍们 x.
    (** Jièshàomen x. *)
    确切 (pair x x).
    (** Quèqiè (pair x x). *)
  定义了.
  (** Dìngyìle. *)
  
结束 p_dl.
(** Jiéshù p_dl. *)

包裹 词头了 参数 nat_dl : p_dl 跟 定义 p := nat.
(** Bāoguǒ cítóule cānshù nat_dl: P_dl gēn dìngyì p:= Nat. *)
打印 nat_dl.l.
(** Dǎyìn nat_dl.L. *)
计算 (nat_dl.l 3).
(** Jìsuàn (nat_dl.L 3). *)
包裹 词头了 参数 bool_dl : 让 定义 p := bool 在 p_dl .
(** Bāoguǒ cítóule cānshù bool_dl: Ràng dìngyì p:= Bool zài p_dl. *)
计算 (bool_dl.l false).
(** Jìsuàn (bool_dl.L false). *)
包裹 词头了 别号 NN := nat_dl .
(** Bāoguǒ cítóule bié hào NN:= Nat_dl. *)
打印 NN.l.
(** Dǎyìn NN.L. *)


(** ---------------------------------------------------- *)


Reset p_dl .

Modular p_dl.

  Parameter p : Type .
  
  Definition d := prod p p .

  Definition l : p -> d .
  Proof.
    intros x.
    exact (pair x x).
  Defined.

End p_dl.

Modular Prefixed Parameter nat_dl : p_dl with Definition p := nat.
Print nat_dl.l.
Compute (nat_dl.l 3).
Modular Prefixed Parameter bool_dl : let Definition p := bool in p_dl .
Compute (bool_dl.l false).
Modular Prefixed Alias NN := nat_dl .
Print NN.l.


(** --------------------------------------------- *)


Module Type NEXT .
  
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
Module NN := nat_dl .
Print NN.l.
(*begin new syntax *)
Reset NN.
Modular Prefixed Alias NN <: let Definition p := nat in p_dl
  := nat_dl .
Print NN.l.
(*end new syntax *)
      
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

(** this part :  X = N , Y = M *)

Declare Module R : (Two M) with Module Y := N .
Print R.x. (* M.x is unfolded in ( R.x = ( 0 (* M.x *) , R.Y.x) ) because the component x of SIG is inlined ;
and certainly R.Y.x ( = N.x ) will not be unfolded because Y is some inner (not-outer) parameter of Two *)
Eval compute in (fst R.x + snd R.x).

Declare Module S : ! ( (Two M) with Module Y := N ) .
Print S.x. (* M.x is not unfolded in ( R.x = (M.x , S.Y.x) ) because the inlining of the component x of SIG is disabled by the command [!] *)
Eval compute in (fst S.x + snd S.x).

(** now this part : X = N , Y = M *)

Declare Module U : (Two N) with Module Y := M .
Print U.x . (* in ( U.x = (N.x , U.Y.x) ) , certainly  N.x is already not unfoldable *)
Eval compute in ( snd U.x + fst U.x) .

Module Type Two_Y_X (Y : SIG) (X : SIG with Definition T := Y.T)
  := let Module Y := Y in (Two X) .
Declare Module V_Y'M_X'N : (Two_Y_X M N) .
Reset V_Y'M_X'N . (* same : *)
Declare Module V_Y_X (Y : SIG) (X : SIG with Definition T := Y.T)
  : (Two_Y_X Y X) .
Module V_Y'M_X'N <: (Two_Y_X M N) := (V_Y_X M N) .
Print V_Y'M_X'N.x . (* V_Y'M_X'N.Y.x is unfolded in ( V_Y'M_X'N.x = (N.x , 0 (* V_Y'M_X'N.Y.x *) ) ) , because the component x of SIG is inlined and the instantiation by M of the modular Two_Y_X or the prefixed V_Y_X to get the instance V_Y'M_X'N is via the (modular or prefixed) functor application  *)
Eval compute in ( snd V_Y'M_X'N.x + fst V_Y'M_X'N.x) .

End NEXT .