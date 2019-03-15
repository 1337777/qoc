From Qoc Require Import Jisuanji .

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

归纳义 无限数字 : 类型 :=
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



归纳义 我的二进制  := 真 : 我的二进制
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


