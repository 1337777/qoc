From Qoc Require Import Jisuanji .

(**MEMO: 

  短 :: 一些参数“p”参数化许多定义和引理“d”和“l”都可以打包成一个;然后可以实例化该参数“p”以产生实例化的定义和引理：“Q.d”和“Q.l”，其新名称以任何选择的前缀名称“Q”作为前缀 ...
  
  Short :: some parameter "p" which parametrizes many definitions and lemmas "d" and "l" may all be packaged into one ; and then later this parameter "p" may be instantiated to produce the instantiated definitions and lemmas : "Q.d" and "Q.l" whose new names are prefixed by any chosen prefix name "Q" ... 
*)

(** PART 1 : SIMPLE PARAMETRIZATION *)

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

Modular Prefixed Parameter nat_dl : (p_dl with Definition p := nat).
Print nat_dl.l.
Compute (nat_dl.l 3).
Modular Prefixed Parameter bool_dl : (let Definition p := bool in p_dl).
Compute (bool_dl.l false).
Modular Prefixed Alias NN := nat_dl .
Print NN.l.


(** --------------------------------------------- *)



(** PART 2 : COMPLEX PARAMETRIZATION *)  


(** Module without parameters . This is precisely for the prefix [M] below .*)
包裹 MOD_T'nat_x'0_y'true.

  定义 T := nat.

  定义 x := 0.
  
  定义 y : bool.
  证明.
    确切 true.
  定义了.

结束 MOD_T'nat_x'0_y'true.

包裹 词头了 参数 M : MOD_T'nat_x'0_y'true .

(** Module with 2 inner-parameters and with some environment which is enabled . *)
包裹 MOD_T_x.

  参数 T : Set.

  (** [Export] keyword says that this environment will be imported when this module is imported . *)
  出口 设置 Printing Notations.
  符号 _carrier :=  T.

  (** [本地] keyword says this identifier will never be imported . 
      [将展开] keyword says that this component of any prefixed-module input 
              will be unfolded in the output module during any outer/functor instantiation/application *)
  本地 参数 将展开 x : T.
  
结束 MOD_T_x.

(** Module instantiated and prefixed by the name [B] . *)
包裹 词头了 参数 B : (MOD_T_x 跟 定义 T := bool).
(** Another different instantiation . Module instantiated and prefixed by the name [N] . *)
包裹 词头了 参数 N : (MOD_T_x 跟 定义 T := nat) .
打印 N.T.
打印 N.x.

(** No more instantiation of [M] is possible. Oneself can only alias (here rename) , then check the precision . *)
包裹 词头了 别号 M' <: (MOD_T_x 跟 定义 T := nat) := M .

包裹 MOD_z (M'' : MOD_T'nat_x'0_y'true).
   定义 z : nat := 1 + M''.x .
结束 MOD_z.

(** Another form of the command to (anonymously) present the module components and to prefix the module at the same time (and also to check the precision). *)
包裹 词头了 别号 M_z <: (MOD_T_x 跟 定义 T := nat).
   包括 M.
   Fail 定义 x :=  1 .

   (** may be bad *)
   定义 z : nat := 1 + M.x . 打印 z.
   Reset z.
   包括 (MOD_z M). 打印 z.
   Reset z.
   
   定义 z : nat := 1 + x . 打印 z.   
   Reset z.
   包括 MOD_z. 打印 z.
结束 M_z.
打印 M_z.T.
打印 M_z.x.

(** Module with one outer-parameter [X]] . This module has also one inner-parameter [Y] , which will also be component of the result  *)
包裹 MODPARAMS (X : MOD_T_x) <: MOD_T_x .

  包裹 词头了 参数 Y : (MOD_T_x 跟 定义 T := X.T) .

  打印 X.x.
  打印 Y.x.
  Fail 打印 X.y.
  Fail 打印 Y.y.

  定义 T := (prod X.T Y.T)%type.
  Reset T.

  (** Notation _carrier is not yet imported *)
  Fail 校验 _carrier. 
  (** Disable the printing of notations for now *)
  未设置 Printing Notations. 
  进口 Y.
  (** Y.T is imported *)
  打印 T.
  (** Notation _carrier is imported *)
  校验 _carrier. 
  (** Export Set Printing Notation is imported *)
  校验 T.  (** output:  _carrier : Set *)
  (** [x] is 本地 and therefore not imported *)
  Fail 打印 x.

  (** Same as above because the Notation is imported *)
  定义 T := (prod X.T _carrier)%type. 
  (** The imported [Y.T] is now masked *)
  打印 T . 
  Reset T .
  (** Same as above because the sharing constraint says that [ X.T = Y.T ( = _carrier )] *)
  定义 T := (prod _carrier _carrier)%type. 

  定义 x : T := (pair X.x Y.x) .

结束 MODPARAMS.

打印 包裹 MODPARAMS.

(** Fails because the sharing constraints are not satisfied *)
Fail 包裹 词头了 参数 P : ((MODPARAMS N) 跟 包裹 词头了 Y := B) .
Fail 包裹 词头了 参数 P : ((MODPARAMS B) 跟 包裹 词头了 Y := N) .

(** In this section :  [X = M , Y = N] *)

包裹 词头了 参数 R : ((MODPARAMS M) 跟 包裹 词头了 Y := N) .
打印 包裹 词头了 R .
打印 R.x. (** M.x is unfolded in ( R.x = ( 0 (** M.x *) , R.Y.x) ) because the component x of MOD_T_x is inlined ;
and certainly R.Y.x ( = N.x ) will not be unfolded because Y is some inner (not-outer) parameter of MODPARAMS *)
计算 ( fst R.x + snd R.x ).

包裹 词头了 参数 S : (** HERE !!! *) ! ( (MODPARAMS M) 跟 包裹 词头了 Y := N ) .
(** [M.x]] is not unfolded in [ R.x = (M.x , S.Y.x) ] because the inlining of the component [x] of [MOD_T_x] is disabled by the command [!] *)
打印 S.x. 
计算 ( fst S.x + snd S.x ).

(** In this section : [X = N , Y = M] *)

包裹 词头了 参数 U : ((MODPARAMS N) 跟 包裹 词头了 Y := M) .
(** In [ U.x = (N.x , U.Y.x) ] , certainly  [N.x] is already not unfoldable *)
打印 U.x .
计算 ( snd U.x + fst U.x ) .

(** This section shows how the inner-parameter [Y] of the module [MODPARAMS] may be moved outside as some outer-parameter .
 Also the permutation of the sequence of the outer-parameters is possible . *)
包裹 MODPARAMS_Y_X (Y : MOD_T_x) (X : MOD_T_x 跟 定义 T := Y.T)
  := 让 包裹 词头了 Y := Y 在 (MODPARAMS X) .
打印 包裹 MODPARAMS_Y_X.
包裹 词头了 参数 V_Y'M_X'N : (MODPARAMS_Y_X M N) .
Reset V_Y'M_X'N . (** same : *)
包裹 词头了 参数 V_Y_X (Y : MOD_T_x) (X : (MOD_T_x 跟 定义 T := Y.T))
  : (MODPARAMS_Y_X Y X) .
包裹 词头了 别号 V_Y'M_X'N <: (MODPARAMS_Y_X M N) := (V_Y_X M N) .
(** [V_Y'M_X'N.Y.x] is unfolded in [ V_Y'M_X'N.x = (N.x , 0 (* V_Y'M_X'N.Y.x *) ) ] , 
  because the component [x] of [MOD_T_x] is inlined 
    and the instantiation by [M] of the module [MODPARAMS_Y_X] or the prefixed-module [V_Y_X] to get the instance [V_Y'M_X'N] 
      is via the (module or prefixed-module) outer/functor instantiation/application  *)
打印 V_Y'M_X'N.x . 
计算 ( snd V_Y'M_X'N.x + fst V_Y'M_X'N.x ) .



(** -nex--------------------------------------------------- *)



Reset MOD_T'nat_x'0_y'true.

(** Module without parameters . This is precisely for the prefix [M] below .*)
Modular MOD_T'nat_x'0_y'true.

  Definition T := nat.

  Definition x := 0.
  
  Definition y : bool.
  Proof.
    exact true.
  Defined.

End MOD_T'nat_x'0_y'true.

Modular Prefixed Parameter M : MOD_T'nat_x'0_y'true .

(** Module with 2 inner-parameters and with some environment which is enabled . *)
Modular MOD_T_x.

  Parameter T : Set.

  (** [Export] keyword says that this environment will be imported when this module is imported . *)
  Export Set Printing Notations.
  Notation _carrier :=  T.

  (** [Local] keyword says this identifier will never be imported . 
      [Inline] keyword says that this component of any prefixed-module input 
              will be unfolded in the output module during any outer/functor instantiation/application *)
  Local Parameter Inline x : T.
  
End MOD_T_x.

(** Module instantiated and prefixed by the name [B] . *)
Modular Prefixed Parameter B : (MOD_T_x with Definition T := bool).
(** Another different instantiation . Module instantiated and prefixed by the name [N] . *)
Modular Prefixed Parameter N : (MOD_T_x with Definition T := nat) .
Print N.T.
Print N.x.

(** No more instantiation of [M] is possible. Oneself can only alias (here rename) , then check the precision . *)
Modular Prefixed Alias M' <: (MOD_T_x with Definition T := nat) := M .

Modular MOD_z (M'' : MOD_T'nat_x'0_y'true).
   Definition z : nat := 1 + M''.x .
End MOD_z.

(** Another form of the command to (anonymously) present the module components and to prefix the module at the same time (and also to check the precision). *)
Modular Prefixed Alias M_z <: (MOD_T_x with Definition T := nat).
   Include M.
   Fail Definition x :=  1 .

   (** may be bad *)
   Definition z : nat := 1 + M.x . Print z.
   Reset z.
   Include (MOD_z M). Print z.
   Reset z.
   
   Definition z : nat := 1 + x . Print z.   
   Reset z.
   Include MOD_z. Print z.
End M_z.
Print M_z.T.
Print M_z.x.

(** Module with one outer-parameter [X]] . This module has also one inner-parameter [Y] , which will also be component of the result  *)
Modular MODPARAMS (X : MOD_T_x) <: MOD_T_x .

  Modular Prefixed Parameter Y : (MOD_T_x with Definition T := X.T) .

  Print X.x.
  Print Y.x.
  Fail Print X.y.
  Fail Print Y.y.

  Definition T := (prod X.T Y.T)%type.
  Reset T.

  (** Notation _carrier is not yet imported *)
  Fail Check _carrier. 
  (** Disable the printing of notations for now *)
  Unset Printing Notations. 
  Import Y.
  (** Y.T is imported *)
  Print T.
  (** Notation _carrier is imported *)
  Check _carrier. 
  (** Export Set Printing Notation is imported *)
  Check T.  (** output:  _carrier : Set *)
  (** [x] is Local and therefore not imported *)
  Fail Print x.

  (** Same as above because the Notation is imported *)
  Definition T := (prod X.T _carrier)%type. 
  (** The imported [Y.T] is now masked *)
  Print T . 
  Reset T .
  (** Same as above because the sharing constraint says that [ X.T = Y.T ( = _carrier )] *)
  Definition T := (prod _carrier _carrier)%type. 

  Definition x : T := (pair X.x Y.x) .

End MODPARAMS.

Print Modular MODPARAMS.

(** Fails because the sharing constraints are not satisfied *)
Fail Modular Prefixed Parameter P : ((MODPARAMS N) with Modular Prefixed Y := B) .
Fail Modular Prefixed Parameter P : ((MODPARAMS B) with Modular Prefixed Y := N) .

(** In this section :  [X = M , Y = N] *)

Modular Prefixed Parameter R : ((MODPARAMS M) with Modular Prefixed Y := N) .
Print Modular Prefixed R .
Print R.x. (** M.x is unfolded in ( R.x = ( 0 (** M.x *) , R.Y.x) ) because the component x of MOD_T_x is inlined ;
and certainly R.Y.x ( = N.x ) will not be unfolded because Y is some inner (not-outer) parameter of MODPARAMS *)
Compute ( fst R.x + snd R.x ).

Modular Prefixed Parameter S : (** HERE !!! *) ! ( (MODPARAMS M) with Modular Prefixed Y := N ) .
(** [M.x]] is not unfolded in [ R.x = (M.x , S.Y.x) ] because the inlining of the component [x] of [MOD_T_x] is disabled by the command [!] *)
Print S.x. 
Compute ( fst S.x + snd S.x ).

(** In this section : [X = N , Y = M] *)

Modular Prefixed Parameter U : ((MODPARAMS N) with Modular Prefixed Y := M) .
(** In [ U.x = (N.x , U.Y.x) ] , certainly  [N.x] is already not unfoldable *)
Print U.x .
Compute ( snd U.x + fst U.x ) .

(** This section shows how the inner-parameter [Y] of the module [MODPARAMS] may be moved outside as some outer-parameter .
 Also the permutation of the sequence of the outer-parameters is possible . *)
Modular MODPARAMS_Y_X (Y : MOD_T_x) (X : MOD_T_x with Definition T := Y.T)
  := let Modular Prefixed Y := Y in (MODPARAMS X) .
Print Modular MODPARAMS_Y_X.
Modular Prefixed Parameter V_Y'M_X'N : (MODPARAMS_Y_X M N) .
Reset V_Y'M_X'N . (** same : *)
Modular Prefixed Parameter V_Y_X (Y : MOD_T_x) (X : (MOD_T_x with Definition T := Y.T))
  : (MODPARAMS_Y_X Y X) .
Modular Prefixed Alias V_Y'M_X'N <: (MODPARAMS_Y_X M N) := (V_Y_X M N) .
(** [V_Y'M_X'N.Y.x] is unfolded in [ V_Y'M_X'N.x = (N.x , 0 (* V_Y'M_X'N.Y.x *) ) ] , 
  because the component [x] of [MOD_T_x] is inlined 
    and the instantiation by [M] of the modular [MODPARAMS_Y_X] or the modular prefixed [V_Y_X] to get the instance [V_Y'M_X'N] 
      is via the (modular or modular prefixed) outer/functor instantiation/application  *)
Print V_Y'M_X'N.x . 
Compute ( snd V_Y'M_X'N.x + fst V_Y'M_X'N.x ) .



(** ---------------------------------------------------- *)



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