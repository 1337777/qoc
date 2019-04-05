From Qoc Require Import Jisuanji .

  
(**

（1.）有限二进制值为：真;假。

（2.）无限数是：0; 1; 2 =下一个1; 3 =接下来2; 4 =接下来3; ....
但这些数字无法携带额外的数据。 我将为数据定义一些新的容器结构，命名为“序列”或“列表”。

（3.）序列可以携带数据。例如，该序列的数据可以是动物：[]; [ 猫 ] ; [ 狗，猫 ] ; [鱼，狗，猫] ......
另一个例子，这个序列的数据可能是颜色：[]; [红]; [ 蓝，红 ] ; [金，蓝，红] ......

（4.）这个序列可能包含多种形式数据的想法被称为多态。

（5.）也符号允许隐藏这种多态性。那个我写的东西如（加入一个 动物 鱼（加入一个 动物 狗（加入一个 动物 猫（空的 动物））））; 然后我写了诸如[鱼，狗，猫]之类的东西，我隐藏了数据类型“动物”。

（6.）最后，我还可以为所有不同的数据类型编程一些多态性函数“底部”。我只编程一个，但我可以写一些东西，如（底部[鱼，狗，猫]）=猫; 我也可以写一些东西，如（底部[金，蓝，红]）=红。

（7.）我还将展示如何编写多态性函数“顶端”和“剩下”，这样（顶端 [鱼，狗，猫]）= 鱼，和（剩下 [鱼，狗，猫]）= [狗，猫 ] 。

（8.）除了多态 - 对象之外，参数值/箭头也可以是推断/隐式/符号。 这将在下一个实时转录中呈现 。

*)

模块 多态_归纳的_隐含_符号 .
(** Bāoguǒ duō tài_guīnà de_yǐn hán_fúhào. *)

归纳的 序列'多态 (数据 : 类型) : 类型 := 
  空的 : 序列'多态 数据
| 加入一个 : 用 (d : 数据) (l : 序列'多态 数据), 序列'多态 数据.
(** Guīnà de xùliè'duō tài (shùjù: Lèixíng): Lèixíng:= 
  Kōng de: Xùliè'duō tài shùjù
| jiārù yīgè: Yòng (d: Shùjù) (l: Xùliè'duō tài shùjù), xùliè'duō tài shùjù. *)

定义 剩下_对于_序列'多态 : 用 (数据 : 类型) (l : 序列'多态 数据), 序列'多态 数据 .
(** Dìngyì shèng xià_duìyú_xùliè'duō tài: Yòng (shùjù: Lèixíng) (l: Xùliè'duō tài shùjù), xùliè'duō tài shùjù. *)
证明 .
(** Zhèngmíng. *)
  介绍们 数据 l . 解构 l 如 [ | dat l' ] .
  (** Jièshàomen shùjù l. Jiěgòu l rú [| dat l' ]. *)
  - 确切 (空的 数据) .
  (**  Quèqiè (kōng de shùjù). *)
  - 确切 l' .
  (** Quèqiè l' . *)
定义了 .
(** Dìngyìle. *)

归纳的 二进制 : 类型 :=
  真 : 二进制
| 假 : 二进制 .
(** Guīnà de èrjìnzhì: Lèixíng:=
  Zhēn: Èrjìnzhì
| jiǎ: Èrjìnzhì. *)

计算 (剩下_对于_序列'多态 二进制 (加入一个 二进制 假
                                          (加入一个 二进制 假
                                                   (加入一个 二进制 真
                                                            (空的 二进制))))) .
(** Jìsuàn (shèng xià_duìyú_xùliè'duō tài èrjìnzhì (jiārù yīgè èrjìnzhì jiǎ
                                          (jiārù yīgè èrjìnzhì jiǎ
                                                   (jiārù yīgè èrjìnzhì zhēn
                                                            (kōng de èrjìnzhì))))). *)

归纳的 无限数字 : 类型 :=
  零 : 无限数字
| 下一个 : 无限数字 -> 无限数字 .
(** Guīnà de wúxiàn shùzì: Lèixíng:=
  Líng: Wúxiàn shùzì
| xià yīgè: Wúxiàn shùzì -> wúxiàn shùzì. *)

计算 (剩下_对于_序列'多态 无限数字 (加入一个 无限数字 (下一个 (下一个 零))
                                          (加入一个 无限数字 零
                                                   (加入一个 无限数字 (下一个 零)
                                                            (空的 无限数字))))) .
(** Jìsuàn (shèng xià_duìyú_xùliè'duō tài wúxiàn shùzì (jiārù yīgè wúxiàn shùzì (xià yīgè (xià yīgè líng))
                                          (jiārù yīgè wúxiàn shùzì líng
                                                   (jiārù yīgè wúxiàn shùzì (xià yīgè líng)
                                                            (kōng de wúxiàn shùzì))))). *)

计算 (加入一个 二进制 真 (空的 二进制)).
(** Jìsuàn (jiārù yīgè èrjìnzhì zhēn (kōng de èrjìnzhì)). *)
计算 (加入一个 _ 真 (空的 _)).
(** Jìsuàn (jiārù yīgè _ zhēn (kōng de _)). *)
计算 (加入一个 _ (下一个 (下一个 零)) (空的 _)).
(** Jìsuàn (jiārù yīgè _ (xià yīgè (xià yīgè líng)) (kōng de _)). *)
(**MEMO: 多态-对象可以通过[符号]命令推断 *)
符号 "d :: l" := (加入一个 _ d l) .
(** fúhào"d:: L" := (Jiārù yīgè _ d l). *)
符号 "!00!" := (空的 _) .
(** Fúhào"!00!" := (Kōng de _). *)
计算 ( 真 :: !00! ).
(** Jìsuàn (zhēn:: !00! ). *)
计算 ( (下一个 (下一个 零)) :: !00! ).
(** Jìsuàn ( (xià yīgè (xià yīgè líng)):: !00! ). *)


计算 (剩下_对于_序列'多态 _ ( 假 ::  假 ::  真 :: !00! ) ) .
(** Jìsuàn (shèng xià_duìyú_xùliè'duō tài _ (jiǎ::  Jiǎ::  Zhēn:: !00! ) ). *)
计算 (剩下_对于_序列'多态 _ ( (下一个 (下一个 零)) :: 零 :: (下一个 零) :: !00! ) ) .
(** Jìsuàn (shèng xià_duìyú_xùliè'duō tài _ ( (xià yīgè (xià yīgè líng)):: Líng:: (Xià yīgè líng):: !00! ) ). *)
符号 "'剩下'" := ( 剩下_对于_序列'多态 _ ) .
(** Fúhào"'shèng xià'" := (Shèng xià_duìyú_xùliè'duō tài _ ). *)
计算 (剩下 ( 假 ::  假 ::  真 :: !00! ) ) .
(** Jìsuàn (shèng xià (jiǎ::  Jiǎ::  Zhēn:: !00! ) ). *)
(**MEMO: 多态-对象可以通过[键入]命令推断 *)
键入 剩下_对于_序列'多态 [数据] l .
(** jiànrù shèng xià_duìyú_xùliè'duō tài [shùjù] l. *)
计算 (剩下_对于_序列'多态 ( 假 ::  假 ::  真 :: !00! ) ) .
(** Jìsuàn (shèng xià_duìyú_xùliè'duō tài (jiǎ::  Jiǎ::  Zhēn:: !00! ) ). *)


部分 部分_多态 .
(** Bùfèn bùfèn_duō tài. *)

  变量 数据 : 类型 .
  (** Biànliàng shùjù: Lèixíng.  *)

  (** 输出的精确形式/类型（精确地[单位]或[数据]？）取决于输入 *)
  归纳的 选项'多态 : 类型 := 
    键入_无效 : (* 单位 -> *) 选项'多态
  | 键入_效 : 数据 -> 选项'多态 .
  (** guīnà de xuǎnxiàng'duō tài: Lèixíng:= 
    Jiànrù_wúxiào: (* Dānwèi ->*) xuǎnxiàng'duō tài
  | jiànrù_xiào: Shùjù -> xuǎnxiàng'duō tài. *)
  
结束 部分_多态 .
(** Jiéshù bùfèn_duō tài. *)

打印 选项'多态 . 打印 单位 . 打印 unit .
(** Dǎyìn xuǎnxiàng'duō tài. Dǎyìn dānwèi. Dǎyìn unit. *)

设置 隐含 键入 .
(** Shèzhì yǐn hán jiànrù. *)

(** 在某种意义上，输出的精确形式/类型（精确地[单位]或[数据]？）
    取决于输入的（参数）（[l]是无效还是有效？） *)
定义 顶部_对于_序列'多态 : 用 (数据 : 类型) (l : 序列'多态 数据), 选项'多态 数据.
(** Dìngyì dǐngbù_duìyú_xùliè'duō tài: Yòng (shùjù: Lèixíng) (l: Xùliè'duō tài shùjù), xuǎnxiàng'duō tài shùjù. *)
证明 .
(** Zhèngmíng. *)
  介绍们 数据 l . 例子 l .
  (** Jièshàomen shùjù l. Lìzi l. *)
  - 确切 (键入_无效 数据).
    (** Quèqiè (jiànrù_wúxiào shùjù). *)
  - 介绍们 dat l' .
    (** Jièshàomen dat l' . *)
    应用 (键入_效 数据) .
    (** Yìngyòng (jiànrù_xiào shùjù). *)
    确切 dat .
    (** Quèqiè dat. *)
定义了 .
(** Dìngyìle. *)

计算 (顶部_对于_序列'多态 ( 假 ::  假 ::  真 :: !00! ) ) .
(** Jìsuàn (dǐngbù_duìyú_xùliè'duō tài (jiǎ::  Jiǎ::  Zhēn:: !00! ) ). *)

固定点 底部_对于_序列'多态 (数据 : 类型) (l : 序列'多态 数据) { 构 l } : 选项'多态 数据 .
(** Gùdìng diǎn dǐbù_duìyú_xùliè'duō tài (shùjù: Lèixíng) (l: Xùliè'duō tài shùjù) {gòu l}: Xuǎnxiàng'duō tài shùjù. *)
证明 .
(** Zhèngmíng. *)
  解构 l 如 [ | dat l' ] .
  (** Jiěgòu l rú [| dat l' ]. *)
  - 确切 (键入_无效 数据) .
    (** Quèqiè (jiànrù_wúxiào shùjù). *)
  - 例子 (底部_对于_序列'多态 数据 l') .
    (** Lìzi (dǐbù_duìyú_xùliè'duō tài shùjù l'). *)
    + 确切 (键入_效 数据 dat).
      (** Quèqiè (jiànrù_xiào shùjù dat). *)
    + 清除 l' . 介绍们 底部_对于_序列'多态_数据_l' .
      (** Qīngchú l' . Jièshàomen dǐbù_duìyú_xùliè'duō tài_shùjù_l' . *)
      应用 (键入_效 数据).
      (** Yìngyòng (jiànrù_xiào shùjù). *)
      确切 底部_对于_序列'多态_数据_l' .
      (** Quèqiè dǐbù_duìyú_xùliè'duō tài_shùjù_l' . *)
定义了 .
(** Dìngyìle. *)

计算 (底部_对于_序列'多态 ( 假 ::  假 ::  真 :: !00! )) .
(** Jìsuàn (dǐbù_duìyú_xùliè'duō tài (jiǎ::  Jiǎ::  Zhēn:: !00! )). *)

结束 多态_归纳的_隐含_符号 .



(** ------------------------------------------------------------------------- *)



(**

(1.) The finite binary values are : true ; false .

(2.) The infinite numbers are : 0 ; 1 ; 2 = next 1 ; 3 = next 2 ; 4 = next 3 ; ....
But the numbers cannot carry additional data .  I shall define some new container structure for data , which  is named "sequences" or "lists" .

(3.) The sequences can carry data . For example , this data of the sequence may be animals : [ ] ; [ cat ] ; [ dog , cat ] ; [ fish , dog , cat ] ...
Another example , this data of the sequence may be colors : [ ] ; [ red ] ; [ blue , red ] ; [ gold , blue , red  ] ...

(4.) This idea that the sequences may contain data of many forms is named as polymorphism .

(5.) The notations allow to hide this polymorphisms . So that instad that I write something such as (JoinOne animals fish (JoinOne animals dog (JoinOne animals cat (Empty animals)))) ; then I write something such as [ fish , dog , cat ] , and I have hidden the data type which is "animals" .

(6.) Finally , I may also program some polymorphism function "bottom" only once for all the different data types . I program only one , but I can write something such as ( bottom [ fish , dog , cat ] ) = cat ; and I can also write something such as ( bottom [ gold , blue , red  ] ) = red .

(7.) I will also show how to write the polymorphism functions "top" and "rest" , such that ( top [ fish , dog , cat ] ) = fish , and ( rest [ fish , dog , cat ] ) = [ dog , cat ] .

(8.) In addition to polymorphism-objects , parameters-values/arrows can also be inferred/implicit/notational . This will be presented in the next live transcription .
*)

Module PolymorphismInductiveImplicitNotations .

Inductive listPoly (data : Type) : Type := 
  Empty : listPoly data
| JoinOne : forall (d : data) (l : listPoly data), listPoly data.

Definition rest_of_listPoly : forall (data : Type) (l : listPoly data), listPoly data .
Proof .
  intros data l . destruct l as [ | dat l' ] .
  - exact (Empty data) .
  - exact l' .
Defined .

Inductive binary : Type :=
  true : binary
| false : binary .

Compute (rest_of_listPoly binary (JoinOne binary false
                                          (JoinOne binary false
                                                   (JoinOne binary true
                                                            (Empty binary))))) .

Inductive infiniteNumbers : Type :=
  Zero : infiniteNumbers
| NextOne : infiniteNumbers -> infiniteNumbers .

Compute (rest_of_listPoly infiniteNumbers (JoinOne infiniteNumbers (NextOne (NextOne Zero))
                                          (JoinOne infiniteNumbers Zero
                                                   (JoinOne infiniteNumbers (NextOne Zero)
                                                            (Empty infiniteNumbers))))) .


Compute (JoinOne binary true (Empty binary)).
Compute (JoinOne _ true (Empty _)).
Compute (JoinOne _ (NextOne (NextOne Zero)) (Empty _)).
(**MEMO: polymorphism-objects can be inferred-implicit , via [Notation] command *)
Notation "d :: l" := (JoinOne _ d l) .
Notation "!00!" := (Empty _) .
Compute ( true :: !00! ).
Compute ( (NextOne (NextOne Zero)) :: !00! ).


Compute (rest_of_listPoly _ ( false ::  false ::  true :: !00! ) ) .
Compute (rest_of_listPoly _ ( (NextOne (NextOne Zero)) :: Zero :: (NextOne Zero) :: !00! ) ) .
Notation "'rest'" := ( rest_of_listPoly _ ) .
Compute (rest ( false ::  false ::  true :: !00! ) ) .
(**MEMO: polymorphism-objects can be inferred-implicit , via [Arguments] command *)
Arguments rest_of_listPoly [data] l .
Compute (rest_of_listPoly ( false ::  false ::  true :: !00! ) ) .


Section section_polymorphism .

  Variable data : Type .

  (** the precise form/type of the output 
      ( precisely [unit] or [data] ? ) depends on the input *)
  Inductive optionPoly : Type := 
    Input_Invalid : (* unit -> *) optionPoly
  | Input_Valid : data -> optionPoly .

End section_polymorphism .

Print optionPoly .  Print unit .

Set Implicit Arguments .

(** in some sense , the precise form/type of the output 
    ( precisely [unit] or [data] ? ) depends on the (parameter of the) input
    ( whether [l] is invalid or valid ? ) *)
Definition top_of_listPoly : forall (data : Type) (l : listPoly data), optionPoly data.
Proof .
  intros data l . case l .
  - exact (Input_Invalid data). 
  - intros dat l' .
    apply (Input_Valid data) .
    exact dat .
Defined .

Compute (top_of_listPoly ( false ::  false ::  true :: !00! ) ) .

Fixpoint bottom_of_listPoly (data : Type) (l : listPoly data) {struct l} : optionPoly data .
Proof .
  destruct l as [ | dat l' ] .
  - exact (Input_Invalid data) .
  - case (bottom_of_listPoly data l') .
    + exact (Input_Valid data dat).
    + clear l' . intros bottom_of_listPoly_data_l' .
      apply (Input_Valid data).
      exact bottom_of_listPoly_data_l' .
Defined .

Compute (bottom_of_listPoly ( false ::  false ::  true :: !00! )) .

End PolymorphismInductiveImplicitNotations .
