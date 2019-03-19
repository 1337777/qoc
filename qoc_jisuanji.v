From Qoc Require Import Jisuanji .

Module PolymorphismInductive .

Inductive listPoly (data : Type) : Type := 
  Empty : listPoly data
| JoinOne : forall (d : data) (l : listPoly data), listPoly data.

Section section_polymorphism .

  Variable data : Type .

  (** the precise form/type of the output 
      ( precisely [unit] or [data] ? ) depends on the input *)
  Inductive optionPoly : Type := 
    Input_Invalid : (* unit -> *) optionPoly
  | Input_Valid : data -> optionPoly .

End section_polymorphism .

Print optionPoly .  Print unit .

(** in some sense , the precise form/type of the output 
    ( precisely [unit] or [data] ? ) depends on the (parameter of the) input
    ( whether [l] is invalid or valid ? ) *)
Definition top_of_listPoly : forall (data : Type) (l : listPoly data), optionPoly data.
Proof .
  intros data l . elim l .
  - exact (Input_Invalid data). 
  - intros d l' IH_l' . clear IH_l' .
    exact (Input_Valid data d) .
Defined .

End PolymorphismInductive .



(** ------------------------------------------------------------------------- *)



Module PolymorphismParametrizedInductive .
(** memo that in some instances such as [top_of_listPoly] above , 
    then the parameters of the inputs is the same as the inputs *)

(** the parameters [infiniteNumbers] is computational , 
    its elements can be matched/decided along forms/constructors *)
Inductive infiniteNumbers : Type :=
  Zero : infiniteNumbers
| NextOne : infiniteNumbers -> infiniteNumbers .

Section section_parametrized .

  Variable inputParam : infiniteNumbers -> Type .
  Variable formula_Zero : forall (l : inputParam Zero), Type .
  Variable formula_NextOne : forall (q : infiniteNumbers) (l : inputParam (NextOne q)), Type .

  (** the precise form of the output
        ( precisely [formula_Zero l] or [formula_NextOne q l] ? ) 
        depends on the parameter of the input 
        ( whether [p] is Zero or [NextOne q] ? ) *)
  Inductive optionsPolyParam : forall (p : infiniteNumbers) (l : inputParam p), Type :=
    Param_Zero : forall (l : inputParam Zero),
      formula_Zero l -> optionsPolyParam Zero l
  | Param_NextOne : forall (q : infiniteNumbers) (l : inputParam (NextOne q)),
      formula_NextOne q l -> optionsPolyParam (NextOne q) l .

  (** this is possible because the parameters [infiniteNumbers] is computational , 
        its elements can be matched/decided along forms/constructors *)
  Definition structuredOptionsPolyParam :
    forall (p : infiniteNumbers) (l : inputParam p), Type .
  Proof .
    intros p . case p (** because [infiniteNumbers] is computational *) .
    - exact formula_Zero.
    - exact formula_NextOne .
  Defined .

  (** this is the inversion lemma for [optionsPolyParam] *)
  Definition structuredOptionsPolyParam_of_optionsPolyParam :
    forall (p : infiniteNumbers) (l : inputParam p) (f : optionsPolyParam p l),
      structuredOptionsPolyParam p l .
  Proof.
    intros p l f .
    refine (match f with
              Param_Zero l f => f
            | Param_NextOne q l f => f
            end) .
  Defined .

  (** this is the instance of the inversion lemma of [optionsPolyParam] for the parameter [Zero] *)
  Definition formula_Zero_of_optionsPolyParam__Zero :
    forall (l : inputParam Zero) (f : optionsPolyParam Zero l), formula_Zero l .
  Proof .
    intros l . exact (structuredOptionsPolyParam_of_optionsPolyParam Zero l) .
  Defined .

  (** this is the instance of the inversion lemma of [optionsPolyParam] for the parameter [NextOne _] *)
  Definition formula_NextOne_of_optionsPolyParam__NextOne :
    forall (q : infiniteNumbers) (l : inputParam (NextOne q)) (f : optionsPolyParam (NextOne q) l),
      formula_NextOne q l 
    := ( fun q l => (structuredOptionsPolyParam_of_optionsPolyParam (NextOne q) l) ) .
  
End section_parametrized .

Section section_polymorphism_parametrized .

  Variable data : Type .

  (**MEMO: this could be presented/accessed through some interface for abstract data types *)
  Inductive listPolyParam : infiniteNumbers -> Type := 
    Empty : listPolyParam Zero
  | JoinOne : forall (d : data) (q : infiniteNumbers) (l : listPolyParam q), listPolyParam (NextOne q) .

  Section rest_of_listPolyParam .

    Let formula_Zero : forall (l : listPolyParam Zero), Type
      := ( fun (l : listPolyParam Zero) => listPolyParam Zero ) .

    Let formula_NextOne : forall (q : infiniteNumbers) (l : listPolyParam (NextOne q)), Type
      := ( fun (q : infiniteNumbers) ( _ : listPolyParam (NextOne q) ) => listPolyParam q ) .

    (** the precise form of the output
      ( precisely [formula_Zero l] or [formula_NextOne q l] ? ) 
      depends on the parameter of the input 
      ( whether [p] is Zero or [NextOne q] ? ) *)
    Definition rest_of_listPolyParam : forall (p : infiniteNumbers) (l : listPolyParam p),
        optionsPolyParam listPolyParam formula_Zero formula_NextOne p l .
    Proof .
      intros p l . elim l .
      - apply (Param_Zero listPolyParam formula_Zero formula_NextOne) . unfold formula_Zero .
        exact Empty .
      - intros d q l' IH_l' . clear IH_l' .
        apply (Param_NextOne listPolyParam formula_Zero formula_NextOne) . unfold formula_NextOne .
        exact l' .
    Defined .

    Definition rest_of_listPolyParam_NextOne :
      forall (q : infiniteNumbers) (l : listPolyParam (NextOne q)), listPolyParam q .
    Proof .
      intros q l . apply (formula_NextOne_of_optionsPolyParam__NextOne listPolyParam formula_Zero formula_NextOne q l) .
      exact (rest_of_listPolyParam (NextOne q) l) .
    Defined .
    
    Definition rest_of_listPolyParam_Zero : forall (l : listPolyParam Zero), listPolyParam Zero
      := ( fun l => (formula_Zero_of_optionsPolyParam__Zero listPolyParam formula_Zero formula_NextOne l
                                                       (rest_of_listPolyParam Zero l)) ) .

  End rest_of_listPolyParam .

  Section bottom_of_listPolyParam .

    Print unit .
    Let formula_Zero : forall (l : listPolyParam Zero), Type
      := ( fun ( _ : listPolyParam Zero) => unit ) .

    Let formula_NextOne : forall (q : infiniteNumbers) (l : listPolyParam (NextOne q)), Type
      := ( fun (q : infiniteNumbers) ( _ : listPolyParam (NextOne q) ) => data ) .

    Fixpoint bottom_of_listPolyParam (p : infiniteNumbers) (l : listPolyParam p) {struct l} :
      optionsPolyParam listPolyParam formula_Zero formula_NextOne p l .
    Proof .
      case l .
      - apply (Param_Zero listPolyParam formula_Zero formula_NextOne) . unfold formula_Zero .
        exact tt .
      - clear p l . intros dat q l' .
        case (bottom_of_listPolyParam q l').
        + clear q l' ; intros l' . intros bottom_of_listPolyParam_q_l' .
          unfold formula_Zero in bottom_of_listPolyParam_q_l' . clear bottom_of_listPolyParam_q_l' .
          apply (Param_NextOne listPolyParam formula_Zero formula_NextOne) . unfold formula_NextOne .
          exact dat .
        + clear q l' ; intros r l' . intros bottom_of_listPolyParam_q_l' .
          unfold formula_NextOne in bottom_of_listPolyParam_q_l' .
          apply (Param_NextOne listPolyParam formula_Zero formula_NextOne) . unfold formula_NextOne .
          exact bottom_of_listPolyParam_q_l' .
    Defined .

    Definition bottom_of_listPolyParam_NextOne :
      forall (q : infiniteNumbers) (l : listPolyParam (NextOne q)), data .
    Proof .
      intros q l . apply (formula_NextOne_of_optionsPolyParam__NextOne listPolyParam formula_Zero formula_NextOne q l) .
      exact (bottom_of_listPolyParam (NextOne q) l) .
    Defined .

    Definition bottom_of_listPolyParam_Zero : forall (l : listPolyParam Zero), unit
      := ( fun l => (formula_Zero_of_optionsPolyParam__Zero listPolyParam formula_Zero formula_NextOne l
                                                       (bottom_of_listPolyParam Zero l)) ) .

  End bottom_of_listPolyParam .

End section_polymorphism_parametrized .

About formula_Zero . About rest_of_listPolyParam_NextOne .

Inductive binary : Type :=
  true : binary
| false : binary .

Eval compute in
  (rest_of_listPolyParam_NextOne binary (NextOne (NextOne Zero))
                                 (JoinOne binary false (NextOne (NextOne Zero))
                                          (JoinOne binary false (NextOne Zero)
                                                   (JoinOne binary true Zero
                                                            (Empty binary))))) .
Eval compute in (rest_of_listPolyParam_Zero binary (Empty binary)) .

Eval compute in
  (bottom_of_listPolyParam_NextOne binary (NextOne (NextOne Zero))
                                 (JoinOne binary false (NextOne (NextOne Zero))
                                          (JoinOne binary false (NextOne Zero)
                                                   (JoinOne binary true Zero
                                                            (Empty binary))))) .
Eval compute in (bottom_of_listPolyParam_Zero binary (Empty binary)) .

End PolymorphismParametrizedInductive .



(** ------------------------------------------------------------------------- *)



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



(** ------------------------------------------------------------------------- *)



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

