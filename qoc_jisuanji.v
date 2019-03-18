From Qoc Require Import Jisuanji .

Module PolymorphismInductive .

Section section_polymorphism .

Variable data : Type .

Inductive optionPoly : Type := 
  Input_Invalid : (* unit -> *) optionPoly
| Input_Valid : data -> optionPoly .

End section_polymorphism .

Print optionPoly .

Section section_polymorphism_inductive .

Inductive listPoly (data : Type) : Type := 
  Empty : listPoly data
| JoinOne : forall (d : data), forall (l : listPoly data), listPoly data.

(** in some sense , the precise form/type of the output 
    ( precisely [unit] or [data] ? ) depends on the (parameter of the) input ( whether [l] is invalid or valid ? ) *)
Definition top_of_listPoly : forall (data : Type) (l : listPoly data), optionPoly data.
Proof .
  intros data l . elim l .
  - exact (Input_Invalid data). 
  - intros d l' IH_l' . clear IH_l' .
    exact (Input_Valid data d).
Defined .

End section_polymorphism_inductive .

End PolymorphismInductive .

Module PolymorphismParametrizedInductive .
(** memo that in some instances such as [top_of_listPoly] above , 
    then the parameters of the inputs is the same as the inputs *)

Inductive infiniteNumbers : Type :=
  Zero : infiniteNumbers
| NextOne : infiniteNumbers -> infiniteNumbers .

Section section_polymorphism .

Variable data : Type .

Inductive listParam : infiniteNumbers -> Type := 
  Empty : listParam Zero
| JoinOne : forall (d : data), forall (q : infiniteNumbers) (l : listParam q), listParam (NextOne q).

Section section_formulas .

  Variable formula_Zero : forall (l : listParam Zero), Type .
  Variable formula_NextOne : forall (q : infiniteNumbers) (l : listParam (NextOne q)), Type .

  Inductive decideParam : forall (p : infiniteNumbers) (l : listParam p), Type :=
    Param_Zero : forall (l : listParam Zero), forall (f : formula_Zero l), decideParam Zero l
  | Param_NextOne : forall (q : infiniteNumbers) (l : listParam (NextOne q)), forall (f : formula_NextOne q l), decideParam (NextOne q) l .

  Inductive decideParam_Zero :  forall (l : listParam Zero), decideParam Zero l -> Type :=
  | Param_Zero_decideParam_Zero : forall (l : listParam Zero), forall (f : formula_Zero l), decideParam_Zero l (Param_Zero l f : decideParam Zero l) .

  Inductive decideParam_NextOne : forall (q : infiniteNumbers) (l : listParam (NextOne q)), decideParam (NextOne q) l -> Type :=
  | Param_NextOne_decideParam_NextOne : forall (q : infiniteNumbers) (l : listParam (NextOne q)), forall (f : formula_NextOne q l),
        decideParam_NextOne q l (Param_NextOne q l f : decideParam (NextOne q) l) .

  (** this is the easy inversion lemma for [deciseParam_Zero] *)
  Lemma formula_Zero_of_decideParam_Zero : forall (l : listParam Zero) (f : decideParam Zero l), decideParam_Zero l f -> formula_Zero l .
  Proof.
    intros l f f_decideParam_Zero .
    destruct f_decideParam_Zero as [ l f ]. Undo.
    case f_decideParam_Zero . clear f_decideParam_Zero f l . intros l f .
    exact f.
  Defined.

  (** this is the easy inversion lemma for [deciseParam_NextOne] *)
  Lemma formula_NextOne_of_decideParam_NextOne : forall (q : infiniteNumbers) (l : listParam (NextOne q)) (f : decideParam (NextOne q) l), decideParam_NextOne q l f -> formula_NextOne q l .
  Proof .
    intros q l f f_decideParam_NextOne .
    destruct f_decideParam_NextOne as [ q l f ] . Undo .
    case f_decideParam_NextOne . clear f_decideParam_NextOne f l q . intros q l f .
    exact f.
  Defined .

  Definition computeDecideParam : forall (p : infiniteNumbers) (l : listParam p), decideParam p l -> Type .
  Proof.
    intros p . case p .
    - intros l f . refine (decideParam_Zero l f) .
    - intros p' l f . refine (decideParam_NextOne p' l f) .
  Defined.

  Definition computeDecideParam_of_decideParam :
    forall (p : infiniteNumbers) (l : listParam p) (f : decideParam p l), computeDecideParam p l f .
  Proof.
    intros p l f . case f.
    - intros l' f'. exact (Param_Zero_decideParam_Zero l' f').
    - intros q  l' f'. apply (Param_NextOne_decideParam_NextOne q l' f').
  Defined.

  (** this is the difficult inversion lemma for [decideParam Zero] *)
  Definition decideParam_Zero_of_decideParam__Zero :
    forall (l : listParam Zero) (f : decideParam Zero l), decideParam_Zero l f.
  Proof.
    intros l . exact (computeDecideParam_of_decideParam Zero l) .
  Defined.

  (** this is the difficult inversion lemma for [decideParam (NextOne _)] *)
  Definition decideParam_NextOne_of_decideParam__NextOne :
    forall (q : infiniteNumbers) (l : listParam (NextOne q)) (f : decideParam (NextOne q) l), decideParam_NextOne q l f.
  Proof.
    intros q l . exact (computeDecideParam_of_decideParam (NextOne q) l) .
  Defined.

End section_formulas .

Let formula_Zero : forall (l : listParam Zero), Type
  := (fun (l : listParam Zero) => listParam Zero) .

Let formula_NextOne : forall (q : infiniteNumbers) (l : listParam (NextOne q)), Type
  := (fun (q : infiniteNumbers) (l : listParam (NextOne q)) => listParam q) .

(** the precise form of the output
    ( precisely [formula_Zero l] or [formula_NextOne q l] ? ) depends on the parameter of the input ( whether [p] is Zero or [NextOne q] ? ) *)
Definition rest_of_listParam : forall (p : infiniteNumbers) (l : listParam p), decideParam formula_Zero formula_NextOne p l .
Proof .
  intros p l . elim l .
  - apply (Param_Zero formula_Zero formula_NextOne) .
    unfold formula_Zero . exact Empty .
  - intros d q l' IH_l'. clear IH_l' .
    apply (Param_NextOne formula_Zero formula_NextOne) .
    unfold formula_NextOne . exact l'.
Defined .

Definition rest_of_listParam_NextOne : forall (q : infiniteNumbers) (l : listParam (NextOne q)), listParam q .
Proof .
  intros q l . apply (formula_NextOne_of_decideParam_NextOne formula_Zero formula_NextOne q l (rest_of_listParam (NextOne q) l)) .
  apply (decideParam_NextOne_of_decideParam__NextOne formula_Zero formula_NextOne q l).
Defined .

Definition rest_of_listParam_Zero : forall (l : listParam Zero), listParam Zero .
Proof .
  intros l . apply (formula_Zero_of_decideParam_Zero formula_Zero formula_NextOne l (rest_of_listParam Zero l)) .
  apply (decideParam_Zero_of_decideParam__Zero formula_Zero formula_NextOne l).
Defined .

End section_polymorphism .

About formula_Zero.

Eval compute in (rest_of_listParam_NextOne bool (NextOne (NextOne Zero))
                                     (JoinOne bool true (NextOne (NextOne Zero))
                                                  (JoinOne bool false (NextOne Zero)
                                                                    (JoinOne bool true Zero
                                                                                       (Empty bool))))).
Eval compute in (rest_of_listParam_Zero bool (Empty bool)).

End  PolymorphismParametrizedInductive .


(** ------------------------- *)

    
Module infiniteNumbers .
  
Inductive infiniteNumbers : Type :=
  Zero : infiniteNumbers
| NextOne : infiniteNumbers -> infiniteNumbers .

Section Section1 .
  
  Variable pOutside : infiniteNumbers .
  
  Fixpoint addMore yInside : infiniteNumbers := 
    match yInside with
      Zero => pOutside
    | NextOne xInside => NextOne (addMore xInside)
    end .

End Section1 .

Print addMore .

Lemma lemma1 : forall ( pOutsideInside : infiniteNumbers ) ,
    addMore (NextOne Zero) pOutsideInside = addMore pOutsideInside (NextOne Zero) .
Proof .
  intros pOutsideInside.
  simpl .
  elim pOutsideInside .
  - (** pOutsideInside is ( Zero ) *)
    simpl .
    reflexivity .
  - (** pOutsideInside is ( NextOne qOutsideInside ) *)
    intros qOutsideInside .
    intros lemma1_qOutsideInside .
    simpl .
    rewrite lemma1_qOutsideInside .
    reflexivity .
Qed .

End infiniteNumbers .

Print infiniteNumbers .

包裹 无限数字包裹 .
(** Bāoguǒ wúxiàn shùzì bāoguǒ. *)  

归纳的 无限数字 : 类型 :=
  零 : 无限数字
| 下一个 : 无限数字 -> 无限数字 .
(** Guīnà yì wúxiàn shùzì: Lèixíng:=
  Líng: Wúxiàn shùzì
| xià yīgè: Wúxiàn shùzì -> wúxiàn shùzì. *)

部分 部分1 .
(** Bùfèn bùfèn 1. *)

  变量 p外 : 无限数字 .
  (** Biànliàng p wài: Wúxiàn shùzì. *)
  
  固定点 加更多 y内 : 无限数字 := 
    匹配 y内 与
      零 => p外
    | 下一个 x内 => 下一个 (加更多 x内)
    结束 .
  (** Gùdìng diǎn jiā gèng duō y nèi: Wúxiàn shùzì:= 
    Pǐpèi y nèi yǔ
      líng => p wài
    | xià yīgè x nèi => xià yīgè (jiā gèng duō x nèi)
    jiéshù. *)

结束 部分1 .
(** Jiéshù bùfèn 1. *)

打印 加更多 .
(** Dǎyìn jiā gèng duō. *)

论点 论点1 : 对全部 ( p外内 : 无限数字 ) ,
    加更多 (下一个 零) p外内 = 加更多 p外内 (下一个 零) .
(** Lùndiǎn lùndiǎn 1: Duì quánbù (p wài nèi: Wúxiàn shùzì),
    jiā gèng duō (xià yīgè líng) p wài nèi = jiā gèng duō p wài nèi (xià yīgè líng). *)
证明 .
(** Zhèngmíng. *)
  介绍 p外内 .
  (** Jièshào p wài nèi. *)
  简化 .
  (** Jiǎnhuà. *)
  消除 p外内 .
  (** Xiāochú p wài nèi. *)  
  - (** p外内 是 ( 零 ) *)
    (** P wài nèi shì (líng) *)
    简化 .
    (** jiǎnhuà. *)
    同一 .
    (** Tóngyī. *)
  - (** p外内 是 ( 下一个 q外内 ) *)
    (** P wài nèi shì (xià yīgè q wài nèi) *)
    介绍 q外内 .
    (** jièshào q wài nèi. *)
    介绍 论点1_q外内 .
    (** Jièshào lùndiǎn 1_q wài nèi. *)
    简化 .
    (** Jiǎnhuà. *)
    改写 论点1_q外内 .
    (** Gǎixiě lùndiǎn 1_q wài nèi. *)
    同一 .
    (** Tóngyī. *)
据证实 .
(** Jù zhèngshí. *)

结束 无限数字包裹 .
(** Jiéshù wúxiàn shùzì bāoguǒ. *)

打印 无限数字包裹 .
(** Dǎyìn wúxiàn shùzì bāoguǒ. *)



(** -------------------------------------------- **)



归纳的 我的二进制  := 真 : 我的二进制
                    | 假 : 我的二进制 .

定义 abc或 ( x : 我的二进制 ) ( y : 我的二进制 ) :=
  ( 若 x 则 真 否则 y ) . 

(** true or true = true. 1 + 1 = 1
true or false = true. 1 + 0 = 1
false or true  = true. 0 + 1 = 1
false or false = false. 0 + 0 = 0 *)
部分 我的分1.
  变量 x : 我的二进制.
  变量 y : 我的二进制.

  论点 我的论点1 :  abc或 x y  =  abc或 y x .
  证明.
    展开 abc或.
    例子 x.
    - (** x 真*)
      例子 y.
      + (** y 真 *) 同一.
      + (** y 假 *) 同一.
    - (** x 假 *)
      例子 y.
      + (** y 真 *) 同一.
      + (** y 假 *) 同一.
  据证实.
结束 我的分1.

(** Guīnà yì wǒ de èrjìnzhì  := Zhēn: Wǒ de èrjìnzhì | jiǎ: Wǒ de èrjìnzhì.

Dìngyì huò (x : Wǒ de èrjìnzhì) (y : Wǒ de èrjìnzhì):= (Ruò x zé zhēn fǒuzé y). 

Bùfèn wǒ de fēn 1.
  Biànliàng x: Wǒ de èrjìnzhì.
  Biànliàng y: Wǒ de èrjìnzhì.

  Lùndiǎn wǒ dì lùndiǎn 1: Huò x y  =  huò y x.
  Zhèngmíng.
    Zhǎnkāi huò.
    Lìzi x.
    - Lìzi y.
      + Tóngyī.
      + Tóngyī.
    - Lìzi y.
      + Tóngyī.
      + Tóngyī.
   Jù zhèngshí.
Jiéshù wǒ de fēn 1.
*)



(** -------------------------------------------- **)


