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

包裹 多态_归纳的_隐含_符号 .
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



(** ------------------------------------------------------------------------- *)



(**
（1.）在先前的实时转录中，我确实展示了如何使用符号来隐藏隐含/推断的信息。例如，符号（[“fish”，“dog”，“cat”]）确实隐藏了关于类型的信息（“动物”）。此外，符号（[“gold”，“green”，“blue”，“red”]）确实隐藏了有关类型（“颜色”）的信息。

（2.）因此序列集合被写为（序列类型）。这被称为“多态”。

（3.）符号可以隐藏许多信息/参数。例如，符号（[“fish”，“dog”，“cat”]）确实隐藏了有关size / parameter（“3”）的信息。此外，符号（[“gold”，“green”，“blue”，“red”]）确实隐藏了有关size / parameter（“4”）的信息。

（4.）因此，序列集合现在写为（序列类型大小）。这被称为“参数化”。

（5.）记住定义函数“bottom”，例如（bottom [“fish”，“dog”，“cat”] =“cat”）。但是对于空序列会发生什么：（bottom [] = ???）。因此，函数输出的形式取决于大小/参数：输出的形式是一个选择/选项，它取决于大小/参数。

（6.）在先前的实时转录中，这个选择/选项非常简单：只有两个选择。但是现在在这个实时转录中，有许多选择通过大小/参数进行参数化。

（7.）因此选项集合被写为（选项类型大小序列）。这被称为“逻辑规范”。 
*)

包裹 多态'参数化了'归纳的隐含符号 .
(** Bāoguǒ duō tài'cānshù huàle'guīnà de yǐn hán fúhào. *)
(** 备忘录，在某些情况下，例如[顶部_对于_序列'多态]， 然后输入的参数与输入相同 *)

(** 参数[无限数字]是计算的，
    它的元素可以沿着表单/构造函数进行匹配/决定 *)
归纳的 无限数字 : 类型 :=
  零 : 无限数字
| 下一个 : 无限数字 -> 无限数字 .
(** guīnà de wúxiàn shùzì: Lèixíng:=
  Líng: Wúxiàn shùzì
| xià yīgè: Wúxiàn shùzì -> wúxiàn shùzì. *)

部分 部分_参数化了 .
(** Bùfèn bùfèn_cānshù huàle. *)
  变量 输入'参数 : 无限数字 -> 类型 .
  (** Biànliàng shūrù'cānshù: Wúxiàn shùzì -> lèixíng. *)
  变量 公式_零 : 用 (l : 输入'参数 零), 类型 .
  (** Biànliàng gōngshì_líng: Yòng (l: Shūrù'cānshù líng), lèixíng. *)
  变量 公式_下一个 : 用 (q : 无限数字) (l : 输入'参数 (下一个 q)), 类型 .
  (** Biànliàng gōngshì_xià yīgè: Yòng (q: Wúxiàn shùzì) (l: Shūrù'cānshù (xià yīgè q)), lèixíng. *)

  (** 输出的精确形式（恰好是[公式_零l]或[公式_下一个q l]？）
      取决于输入的参数（[p]是零还是[下一个q]？） *)
  归纳的 选项们'多态'参数 : 用 (p : 无限数字) (l : 输入'参数 p), 类型 :=
    参数_零 : 用 (l : 输入'参数 零),
      公式_零 l -> 选项们'多态'参数 零 l
  | 参数_下一个 : 用 (q : 无限数字) (l : 输入'参数 (下一个 q)),
      公式_下一个 q l -> 选项们'多态'参数 (下一个 q) l .
  (** Guīnà de xuǎnxiàngmen'duō tài'cānshù: Yòng (p: Wúxiàn shùzì) (l: Shūrù'cānshù p), lèixíng:=
    Cānshù_líng: Yòng (l: Shūrù'cānshù líng),
      gōngshì_líng l -> xuǎnxiàngmen'duō tài'cānshù líng l
  | cānshù_xià yīgè: Yòng (q: Wúxiàn shùzì) (l: Shūrù'cānshù (xià yīgè q)),
      gōngshì_xià yīgè q l -> xuǎnxiàngmen'duō tài'cānshù (xià yīgè q) l. *)
  
  (** 这是可能的，因为参数[无限数字]是计算的，其元素可以沿着表单/构造函数进行匹配/决定 *)
  定义 结构化的'选项们'多态'参数 :
    用 (p : 无限数字) (l : 输入'参数 p), 类型 .
  (** dìngyì jiégòu huà de'xuǎnxiàngmen'duō tài'cānshù:
    Yòng (p: Wúxiàn shùzì) (l: Shūrù'cānshù p), lèixíng. *)
  证明 .
  (** Zhèngmíng. *)
    介绍们 p . 例子 p (** 因为[无限数字]是计算的 *) .
    (** Jièshàomen p. Lìzi p . *)
    - 确切 公式_零.
    (** Quèqiè gōngshì_líng. *)
    - 确切 公式_下一个 .
    (** Quèqiè gōngshì_xià yīgè. *)
  定义了 .
  (** Dìngyìle. *)    

  (** 这是[选项们'多态'参数]的反转引理 *)
  定义 结构化的'选项们'多态'参数_对于_选项们'多态'参数 :
    用 (p : 无限数字) (l : 输入'参数 p) (f : 选项们'多态'参数 p l),
      结构化的'选项们'多态'参数 p l .
  (** dìngyì jiégòu huà de'xuǎnxiàngmen'duō tài'cānshù_duìyú_xuǎnxiàngmen'duō tài'cānshù:
    Yòng (p: Wúxiàn shùzì) (l: Shūrù'cānshù p) (f: Xuǎnxiàngmen'duō tài'cānshù p l),
      jiégòu huà de'xuǎnxiàngmen'duō tài'cānshù p l. *)
  证明.
  (** Zhèngmíng. *)
    介绍们 p l f .
    (** Jièshàomen p l f. *)
    加细 (匹配 f 与
              参数_零 l f => f
            | 参数_下一个 q l f => f
            结束) .
    (** Jiā xì (pǐpèi f yǔ
              cānshù_líng l f => f
            | cānshù_xià yīgè q l f => f
            jiéshù). *)
  定义了 .
  (** Dìngyìle. *)  

  (** 这是参数[零]的[选项们'多态'参数]的反转引理的实例 *)
  定义 公式_零_对于_选项们'多态'参数__零 :
    用 (l : 输入'参数 零) (f : 选项们'多态'参数 零 l), 公式_零 l .
  (** dìngyì gōngshì_líng_duìyú_xuǎnxiàngmen'duō tài'cānshù__líng:
    Yòng (l: Shūrù'cānshù líng) (f: Xuǎnxiàngmen'duō tài'cānshù líng l), gōngshì_líng l. *)
  证明 .
  (** Zhèngmíng. *)
    介绍们 l . 确切 (结构化的'选项们'多态'参数_对于_选项们'多态'参数 零 l) .
    (** Jièshàomen l. Quèqiè (jiégòu huà de'xuǎnxiàngmen'duō tài'cānshù_duìyú_xuǎnxiàngmen'duō tài'cānshù líng l). *)
  定义了 .
  (** Dìngyìle. *)  

  (** 这是参数[下一个_]的[选项们'多态'参数]的反转引理的实例 *)
  定义 公式_下一个_对于_选项们'多态'参数__下一个 :
    用 (q : 无限数字) (l : 输入'参数 (下一个 q)) (f : 选项们'多态'参数 (下一个 q) l),
      公式_下一个 q l 
    := ( 作用 q l => (结构化的'选项们'多态'参数_对于_选项们'多态'参数 (下一个 q) l) ) .
  (** dìngyì gōngshì_xià yīgè_duìyú_xuǎnxiàngmen'duō tài'cān shù__xià yīgè:
    Yòng (q: Wúxiàn shùzì) (l: Shūrù'cān shù (xià yīgè q)) (f: Xuǎnxiàngmen'duō tài'cān shù (xià yīgè q) l),
      gōngshì_xià yīgè q l 
    := (Zuòyòng q l => (jiégòu huà de'xuǎnxiàngmen'duō tài'cān shù_duìyú_xuǎnxiàngmen'duō tài'cān shù (xià yīgè q) l) ). *)

结束 部分_参数化了 .
(** Jiéshù bùfèn_cān shù huàle. *)

部分 部分_多态_参数化了 .
(** Bùfèn bùfèn_duō tài_cānshù huàle. *)

  变量 数据 : 类型 .
  (** Biànliàng shùjù: Lèixíng. *)
  
  归纳的 序列'多态'参数 : 无限数字 -> 类型 := 
    空的 : 序列'多态'参数 零
  | 加入一个 : 用 (d : 数据) (q : 无限数字) (l : 序列'多态'参数 q), 序列'多态'参数 (下一个 q) .
  (** Guīnà de xùliè'duō tài'cānshù: Wúxiàn shùzì -> lèixíng:= 
    Kōng de: Xùliè'duō tài'cānshù líng
  | jiārù yīgè: Yòng (d: Shùjù) (q: Wúxiàn shùzì) (l: Xùliè'duō tài'cānshù q), xùliè'duō tài'cānshù (xià yīgè q). *)
  
  部分 剩下_对于_序列'多态'参数 .
  (** Bùfèn shèng xià_duìyú_xùliè'duō tài'cānshù. *)

    让 公式_零 : 用 (l : 序列'多态'参数 零), 类型
      := ( 作用 (l : 序列'多态'参数 零) => 序列'多态'参数 零 ) .
    (** Ràng gōngshì_líng: Yòng (l: Xùliè'duō tài'cānshù líng), lèixíng
      := (Zuòyòng (l: Xùliè'duō tài'cānshù líng) => xùliè'duō tài'cānshù líng). *)
    
    让 公式_下一个 : 用 (q : 无限数字) (l : 序列'多态'参数 (下一个 q)), 类型
      := ( 作用 (q : 无限数字) ( _ : 序列'多态'参数 (下一个 q) ) => 序列'多态'参数 q ) .
    (** Ràng gōngshì_xià yīgè: Yòng (q: Wúxiàn shùzì) (l: Xùliè'duō tài'cānshù (xià yīgè q)), lèixíng
      := (Zuòyòng (q: Wúxiàn shùzì) ( _ : Xùliè'duō tài'cānshù (xià yīgè q) ) => xùliè'duō tài'cānshù q). *)
    
    (** 输出的精确形式（恰好是[公式_零l]或[公式_下一个q l]？）取决于输入的参数（[p]是零还是[下一个q]？） *)
    定义 剩下_对于_序列'多态'参数 : 用 (p : 无限数字) (l : 序列'多态'参数 p),
        选项们'多态'参数 序列'多态'参数 公式_零 公式_下一个 p l .
    (** Dìngyì shèng xià_duìyú_xùliè'duō tài'cānshù: Yòng (p: Wúxiàn shùzì) (l: Xùliè'duō tài'cānshù p),
        xuǎnxiàngmen'duō tài'cānshù xùliè'duō tài'cānshù gōngshì_líng gōngshì_xià yīgè p l. *)
    证明 .
    (** Zhèngmíng. *)
      介绍们 p l . 例子 l .
      (** Jièshàomen p l. Lìzi l. *)
      - 应用 (参数_零 序列'多态'参数 公式_零 公式_下一个) . 展开 公式_零 .
        (** Yìngyòng (cānshù_líng xùliè'duō tài'cānshù gōngshì_líng gōngshì_xià yīgè). Zhǎnkāi gōngshì_líng. *)
        确切 空的 .
        (** Quèqiè kōng de. *)
      - 介绍们 d q l' . 
        (** Jièshàomen d q l' .  *)
        应用 (参数_下一个 序列'多态'参数 公式_零 公式_下一个) . 展开 公式_下一个 .
        (** Yìngyòng (cānshù_xià yīgè xùliè'duō tài'cānshù gōngshì_líng gōngshì_xià yīgè). Zhǎnkāi gōngshì_xià yīgè. *)
        确切 l' .
        (** Quèqiè l' . *)
    定义了 .
    (** Dìngyìle. *)
    
    定义 剩下_对于_序列'多态'参数_零 : 用 (l : 序列'多态'参数 零), 序列'多态'参数 零 .
    (** Dìngyì shèng xià_duìyú_xùliè'duō tài'cānshù_líng: Yòng (l: Xùliè'duō tài'cānshù líng), xùliè'duō tài'cānshù líng. *)
    证明 .
    (** Zhèngmíng. *)
      介绍们 l .
      (** Jièshàomen l. *)
      应用(公式_零_对于_选项们'多态'参数__零 序列'多态'参数 公式_零 公式_下一个 l).
      (** Yìngyòng (gōngshì_líng_duìyú_xuǎnxiàngmen'duō tài'cānshù__líng xùliè'duō tài'cānshù gōngshì_líng gōngshì_xià yīgè l). *)
      确切 (剩下_对于_序列'多态'参数 零 l) .
      (** Quèqiè (shèng xià_duìyú_xùliè'duō tài'cānshù líng l). *)
    定义了 .
    (** Dìngyìle. *)
    
    定义 剩下_对于_序列'多态'参数_下一个 :
      用 (q : 无限数字) (l : 序列'多态'参数 (下一个 q)), 序列'多态'参数 q 
      := ( 作用 q l => (公式_下一个_对于_选项们'多态'参数__下一个 序列'多态'参数 公式_零 公式_下一个 q l
                                                               (剩下_对于_序列'多态'参数 (下一个 q) l)) ) .
    (** Dìngyì shèng xià_duìyú_xùliè'duō tài'cānshù_xià yīgè:
      Yòng (q: Wúxiàn shùzì) (l: Xùliè'duō tài'cānshù (xià yīgè q)), xùliè'duō tài'cānshù q 
      := (Zuòyòng q l => (gōngshì_xià yīgè_duìyú_xuǎnxiàngmen'duō tài'cānshù__xià yīgè xùliè'duō tài'cānshù gōngshì_líng gōngshì_xià yīgè q l
                                                               (shèng xià_duìyú_xùliè'duō tài'cānshù (xià yīgè q) l)) ). *)
    
  结束 剩下_对于_序列'多态'参数 .
  (** Jiéshù shèng xià_duìyú_xùliè'duō tài'cānshù. *)
  
  部分 顶部_对于_序列'多态'参数 .
  (** Bùfèn dǐngbù_duìyú_xùliè'duō tài'cānshù. *)
  
    打印 单位 . 打印 unit .
    (** Dǎyìn dānwèi. Dǎyìn unit. *)
    让 公式_零 : 用 (l : 序列'多态'参数 零), 类型
      := ( 作用 ( _ : 序列'多态'参数 零) => 单位 ) .
    (** Ràng gōngshì_líng: Yòng (l: Xùliè'duō tài'cānshù líng), lèixíng
      := (Zuòyòng ( _ : Xùliè'duō tài'cānshù líng) => dānwèi). *)
    
    让 公式_下一个 : 用 (q : 无限数字) (l : 序列'多态'参数 (下一个 q)), 类型
      := ( 作用 (q : 无限数字) ( _ : 序列'多态'参数 (下一个 q) ) => 数据 ) .
    (** Ràng gōngshì_xià yīgè: Yòng (q: Wúxiàn shùzì) (l: Xùliè'duō tài'cānshù (xià yīgè q)), lèixíng
      := (Zuòyòng (q: Wúxiàn shùzì) ( _ : Xùliè'duō tài'cānshù (xià yīgè q) ) => shùjù). *)
    
    定义 顶部_对于_序列'多态'参数 : 用 (p : 无限数字) (l : 序列'多态'参数 p),
      选项们'多态'参数 序列'多态'参数 公式_零 公式_下一个 p l .
    (** Dìngyì dǐngbù_duìyú_xùliè'duō tài'cānshù: Yòng (p: Wúxiàn shùzì) (l: Xùliè'duō tài'cānshù p),
      xuǎnxiàngmen'duō tài'cānshù xùliè'duō tài'cānshù gōngshì_líng gōngshì_xià yīgè p l. *)
    证明 .
    (** Zhèngmíng. *)
      介绍们 p l . 例子 l .
      (** Jièshàomen p l. Lìzi l. *)
      - 应用 (参数_零 序列'多态'参数 公式_零 公式_下一个) . 展开 公式_零 .
        (** Yìngyòng (cānshù_líng xùliè'duō tài'cānshù gōngshì_líng gōngshì_xià yīgè). Zhǎnkāi gōngshì_líng. *)
        确切 单 .
        (** Quèqiè dān. *)
      - 介绍们 dat q l' .
        (** Jièshàomen dat q l' . *)
        应用 (参数_下一个 序列'多态'参数 公式_零 公式_下一个) . 展开 公式_下一个 .
        (** Yìngyòng (cānshù_xià yīgè xùliè'duō tài'cānshù gōngshì_líng gōngshì_xià yīgè). Zhǎnkāi gōngshì_xià yīgè. *)
        确切 dat .
        (** Quèqiè dat. *)
    定义了 .
    (** Dìngyìle. *)
    
    定义 顶部_对于_序列'多态'参数_下一个 :
      用 (q : 无限数字) (l : 序列'多态'参数 (下一个 q)), 数据 .
    (** Dìngyì dǐngbù_duìyú_xùliè'duō tài'cānshù_xià yīgè:
      Yòng (q: Wúxiàn shùzì) (l: Xùliè'duō tài'cānshù (xià yīgè q)), shùjù. *)
    证明 .
      (** Zhèngmíng. *)
      介绍们 q l . 应用 (公式_下一个_对于_选项们'多态'参数__下一个 序列'多态'参数 公式_零 公式_下一个 q l) .
      (** Jièshàomen q l. Yìngyòng (gōngshì_xià yīgè_duìyú_xuǎnxiàngmen'duō tài'cānshù__xià yīgè xùliè'duō tài'cānshù gōngshì_líng gōngshì_xià yīgè q l). *)
      确切 (顶部_对于_序列'多态'参数 (下一个 q) l) .
      (** Quèqiè (dǐngbù_duìyú_xùliè'duō tài'cānshù (xià yīgè q) l). *)
    定义了 .
    (** Dìngyìle. *)
    
    定义 顶部_对于_序列'多态'参数_零 : 用 (l : 序列'多态'参数 零), 单位
      := ( 作用 l => (公式_零_对于_选项们'多态'参数__零 序列'多态'参数 公式_零 公式_下一个 l
                                                       (顶部_对于_序列'多态'参数 零 l)) ) .
    (** Dìngyì dǐngbù_duìyú_xùliè'duō tài'cānshù_líng: Yòng (l: Xùliè'duō tài'cānshù líng), dānwèi
      := (Zuòyòng l => (gōngshì_líng_duìyú_xuǎnxiàngmen'duō tài'cānshù__líng xùliè'duō tài'cānshù gōngshì_líng gōngshì_xià yīgè l
                                                       (dǐngbù_duìyú_xùliè'duō tài'cānshù líng l)) ). *)
    
  结束 顶部_对于_序列'多态'参数 .
  (** Jiéshù dǐngbù_duìyú_xùliè'duō tài'cānshù. *)
  
  部分 底部_对于_序列'多态'参数 .
    (** Bùfèn dǐbù_duìyú_xùliè'duō tài'cānshù. *)
  
    让 公式_零 : 用 (l : 序列'多态'参数 零), 类型
      := ( 作用 ( _ : 序列'多态'参数 零) => 单位 ) .
    (** Ràng gōngshì_líng: Yòng (l: Xùliè'duō tài'cānshù líng), lèixíng
      := (Zuòyòng ( _ : Xùliè'duō tài'cānshù líng) => dānwèi). *)
    
    让 公式_下一个 : 用 (q : 无限数字) (l : 序列'多态'参数 (下一个 q)), 类型
      := ( 作用 (q : 无限数字) ( _ : 序列'多态'参数 (下一个 q) ) => 数据 ) .
    (** Ràng gōngshì_xià yīgè: Yòng (q: Wúxiàn shùzì) (l: Xùliè'duō tài'cānshù (xià yīgè q)), lèixíng
      := (Zuòyòng (q: Wúxiàn shùzì) ( _ : Xùliè'duō tài'cānshù (xià yīgè q) ) => shùjù). *)
    
    固定点 底部_对于_序列'多态'参数 (p : 无限数字) (l : 序列'多态'参数 p) { 构 l } :
      选项们'多态'参数 序列'多态'参数 公式_零 公式_下一个 p l .
    (** Gùdìng diǎn dǐbù_duìyú_xùliè'duō tài'cānshù (p: Wúxiàn shùzì) (l: Xùliè'duō tài'cānshù p) {gòu l}:
      Xuǎnxiàngmen'duō tài'cānshù xùliè'duō tài'cānshù gōngshì_líng gōngshì_xià yīgè p l. *)
    证明 .
    (** Zhèngmíng. *)
      例子 l .
      (** Lìzi l. *)
      - 应用 (参数_零 序列'多态'参数 公式_零 公式_下一个) . 展开 公式_零 .
        (** Yìngyòng (cānshù_líng xùliè'duō tài'cānshù gōngshì_líng gōngshì_xià yīgè). Zhǎnkāi gōngshì_líng. *)
        确切 单 .
        (** Quèqiè dān. *)
      - 清除 p l . 介绍们 dat q l' .
        (** Qīngchú p l. Jièshàomen dat q l' . *)
        例子 (底部_对于_序列'多态'参数 q l').
        (** Lìzi (dǐbù_duìyú_xùliè'duō tài'cānshù q l'). *)
        + 清除 q l' ; 介绍们 l' . 介绍们 底部_对于_序列'多态'参数_q_l' .
          (** Qīngchú q l' ; jièshàomen l' . Jièshàomen dǐbù_duìyú_xùliè'duō tài'cānshù_q_l' . *)
          展开 公式_零 在 底部_对于_序列'多态'参数_q_l' . 清除 底部_对于_序列'多态'参数_q_l' .
          (** Zhǎnkāi gōngshì_líng zài dǐbù_duìyú_xùliè'duō tài'cānshù_q_l' . Qīngchú dǐbù_duìyú_xùliè'duō tài'cānshù_q_l' . *)
          应用 (参数_下一个 序列'多态'参数 公式_零 公式_下一个) . 展开 公式_下一个 .
          (** Yìngyòng (cānshù_xià yīgè xùliè'duō tài'cānshù gōngshì_líng gōngshì_xià yīgè). Zhǎnkāi gōngshì_xià yīgè. *)
          确切 dat .
          (** Quèqiè dat. *)
        + 清除 q l' ; 介绍们 r l' . 介绍们 底部_对于_序列'多态'参数_q_l' .
          (** Qīngchú q l' ; jièshàomen r l' . Jièshàomen dǐbù_duìyú_xùliè'duō tài'cānshù_q_l' . *)
          展开 公式_下一个 在 底部_对于_序列'多态'参数_q_l' .
          (** Zhǎnkāi gōngshì_xià yīgè zài dǐbù_duìyú_xùliè'duō tài'cānshù_q_l' . *)
          应用 (参数_下一个 序列'多态'参数 公式_零 公式_下一个) . 展开 公式_下一个 .
          (** Yìngyòng (cānshù_xià yīgè xùliè'duō tài'cānshù gōngshì_líng gōngshì_xià yīgè). Zhǎnkāi gōngshì_xià yīgè. *)
          确切 底部_对于_序列'多态'参数_q_l' .
          (** Quèqiè dǐbù_duìyú_xùliè'duō tài'cānshù_q_l' . *)
    定义了 .
    (** Dìngyìle. *)
    
    定义 底部_对于_序列'多态'参数_下一个 :
      用 (q : 无限数字) (l : 序列'多态'参数 (下一个 q)), 数据 .
    (** Dìngyì dǐbù_duìyú_xùliè'duō tài'cānshù_xià yīgè:
      Yòng (q: Wúxiàn shùzì) (l: Xùliè'duō tài'cānshù (xià yīgè q)), shùjù. *)
    证明 .
    (** Zhèngmíng. *)
      介绍们 q l . 应用 (公式_下一个_对于_选项们'多态'参数__下一个 序列'多态'参数 公式_零 公式_下一个 q l) .
      (** Jièshàomen q l. Yìngyòng (gōngshì_xià yīgè_duìyú_xuǎnxiàngmen'duō tài'cānshù__xià yīgè xùliè'duō tài'cānshù gōngshì_líng gōngshì_xià yīgè q l). *)
      确切 (底部_对于_序列'多态'参数 (下一个 q) l) .
      (** Quèqiè (dǐbù_duìyú_xùliè'duō tài'cānshù (xià yīgè q) l). *)
    定义了 .
    (** Dìngyìle. *)
    
    定义 底部_对于_序列'多态'参数_零 : 用 (l : 序列'多态'参数 零), 单位
      := ( 作用 l => (公式_零_对于_选项们'多态'参数__零 序列'多态'参数 公式_零 公式_下一个 l
                                                       (底部_对于_序列'多态'参数 零 l)) ) .
    (** Dìngyì dǐbù_duìyú_xùliè'duō tài'cānshù_líng: Yòng (l: Xùliè'duō tài'cānshù líng), dānwèi
      := (Zuòyòng l => (gōngshì_líng_duìyú_xuǎnxiàngmen'duō tài'cānshù__líng xùliè'duō tài'cānshù gōngshì_líng gōngshì_xià yīgè l
                                                       (dǐbù_duìyú_xùliè'duō tài'cānshù líng l)) ). *)
    
  结束 底部_对于_序列'多态'参数 .
  (** Jiéshù dǐbù_duìyú_xùliè'duō tài'cānshù. *)
  
结束 部分_多态_参数化了 .
(** Jiéshù bùfèn_duō tài_cān shù huàle. *)

关于 公式_零 . 关于 剩下_对于_序列'多态'参数_下一个 .
(** Guānyú gōngshì_líng. Guānyú shèng xià_duìyú_xùliè'duō tài'cān shù_xià yīgè. *)

归纳的 二进制 : 类型 :=
  真 : 二进制
| 假 : 二进制 .
(** Guīnà de èrjìnzhì: Lèixíng:=
  Zhēn: Èrjìnzhì
| jiǎ: Èrjìnzhì. *)

计算 (剩下_对于_序列'多态'参数_下一个 二进制 (下一个 (下一个 零))
                                 (加入一个 二进制 假 (下一个 (下一个 零))
                                          (加入一个 二进制 假 (下一个 零)
                                                   (加入一个 二进制 真 零
                                                            (空的 二进制))))) .
(** Jìsuàn (shèng xià_duìyú_xùliè'duō tài'cān shù_xià yīgè èrjìnzhì (xià yīgè (xià yīgè líng))
                                 (jiārù yīgè èrjìnzhì jiǎ (xià yīgè (xià yīgè líng))
                                          (jiārù yīgè èrjìnzhì jiǎ (xià yīgè líng)
                                                   (jiārù yīgè èrjìnzhì zhēn líng
                                                            (kōng de èrjìnzhì))))). *)
评估 计算 在 (剩下_对于_序列'多态'参数_零 二进制 (空的 二进制)) .
(** Pínggū jìsuàn zài (shèng xià_duìyú_xùliè'duō tài'cān shù_líng èrjìnzhì (kōng de èrjìnzhì)). *)

计算 (加入一个 二进制 真 零 (空的 二进制)) .
(** Jìsuàn (jiārù yīgè èrjìnzhì zhēn líng (kōng de èrjìnzhì)). *)
计算 (加入一个 _ 真 零 (空的 _)) .
(** Jìsuàn (jiārù yīgè _ zhēn líng (kōng de _)). *)
计算 (加入一个 _ 真 _ (空的 _)) .
(** Jìsuàn (jiārù yīgè _ zhēn _ (kōng de _)). *)
(**MEMO: 除了多态-对象之外，还可以通过[符号]命令推断出参数 *)
符号 "d :: l" := (加入一个 _ d _ l) .
(** fúhào"d:: L" := (Jiārù yīgè _ d _ l). *)
符号 "!00!" := (空的 _) .
(** Fúhào"!00!" := (Kōng de _). *)
计算 ( 真 :: !00! ).
(** Jìsuàn (zhēn:: !00! ). *)

计算 (剩下_对于_序列'多态'参数_下一个 _ _ ( 假 ::  假 ::  真 :: !00! ) ) .
(** Jìsuàn (shèng xià_duìyú_xùliè'duō tài'cān shù_xià yīgè _ _ (jiǎ::  Jiǎ::  Zhēn:: !00! ) ). *)
符号 "'剩下'" := ( 剩下_对于_序列'多态'参数_下一个 _ _ ) .
(** Fúhào"'shèng xià'" := (Shèng xià_duìyú_xùliè'duō tài'cān shù_xià yīgè _ _ ). *)
计算 (剩下 ( 假 ::  假 ::  真 :: !00! ) ) .
(** Jìsuàn (shèng xià (jiǎ::  Jiǎ::  Zhēn:: !00! ) ). *)
(**MEMO: 除了多态-对象之外，还可以通过[键入]命令推断出参数 *)
键入 剩下_对于_序列'多态'参数_下一个 [数据] [q] l .
(** jiànrù shèng xià_duìyú_xùliè'duō tài'cān shù_xià yīgè [shùjù] [q] l. *)
计算 (剩下_对于_序列'多态'参数_下一个 ( 假 ::  假 ::  真 :: !00! ) ) .
(** Jìsuàn (shèng xià_duìyú_xùliè'duō tài'cān shù_xià yīgè (jiǎ::  Jiǎ::  Zhēn:: !00! ) ). *)

计算 (顶部_对于_序列'多态'参数_下一个 _ _ ( 假 ::  假 ::  真 :: !00! )) .
(** Jìsuàn (dǐngbù_duìyú_xùliè'duō tài'cān shù_xià yīgè _ _ (jiǎ::  Jiǎ::  Zhēn:: !00! )). *)
计算 (顶部_对于_序列'多态'参数_零 二进制 ( !00! )  ) .
(** Jìsuàn (dǐngbù_duìyú_xùliè'duō tài'cān shù_líng èrjìnzhì ( !00! )  ). *)

计算 (底部_对于_序列'多态'参数_下一个 二进制 (下一个 (下一个 零))
                                 ( 假 ::  假 ::  真 :: !00! )) .
(** Jìsuàn (dǐbù_duìyú_xùliè'duō tài'cān shù_xià yīgè èrjìnzhì (xià yīgè (xià yīgè líng))
                                 (jiǎ::  Jiǎ::  Zhēn:: !00! )). *)
计算 (底部_对于_序列'多态'参数_零 二进制 (空的 二进制)) .
(** Jìsuàn (dǐbù_duìyú_xùliè'duō tài'cān shù_líng èrjìnzhì (kōng de èrjìnzhì)). *)

结束 多态'参数化了'归纳的隐含符号 .
(** Jiéshù duō tài'cān shù huàle'guīnà de yǐn hán fúhào. *)



(** ------------------------------------------------------------------------- *)



(**

(1.) In the precedent live transcription , I did show how the notations can be used to hide information which is implicit/inferred . For example , the notation  ( [ "fish" , "dog" , "cat" ] ) does hide the information about the type ( "animals" ) . Also , the notation  ( [ "gold" , "green" , "blue" , "red" ] ) does hide the information about the type ( "colors" ) . 

(2.) So the collection of sequences is written as ( sequences type ) . This was named as "polymorphism" . 

(3.) Many information/parameters can be hidden by the notations . For example , the notation  ( [ "fish" , "dog" , "cat" ] ) does hide the information about the size/parameter ( "3" ) . Also , the notation  ( [ "gold" , "green" , "blue" , "red" ] ) does hide the information about the size/parameter ( "4" ) . 

(4.) So the collection of sequences is now written as ( sequences type size ) . This is named as "parametrization" .

(5.) Remember that the function "bottom" is defined such as ( bottom [ "fish" , "dog" , "cat" ] = "cat" ) . But what happens for the empty sequence : ( bottom [  ] = ???  ) .  Therefore the form of the output of the function depends on the size/parameter : the form of the output is a selection/option which depends on the size/parameter . 

(6.)  In the precedent live transcription , this selection/option was very simple : only two choices . But now in this live transcription , there are many choices which are parametrized by the size/parameter .

(7.) So the collection of options is written as (options type size sequence) . This is named as "logical specification" .

*)

Module PolymorphismParametrizedInductiveImplicitNotations .
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
      intros p l . case l .
      - apply (Param_Zero listPolyParam formula_Zero formula_NextOne) . unfold formula_Zero .
        exact Empty .
      - intros d q l' . 
        apply (Param_NextOne listPolyParam formula_Zero formula_NextOne) . unfold formula_NextOne .
        exact l' .
    Defined .

    Definition rest_of_listPolyParam_Zero : forall (l : listPolyParam Zero), listPolyParam Zero .
    Proof .
      intros l .
      apply(formula_Zero_of_optionsPolyParam__Zero listPolyParam formula_Zero formula_NextOne l).
      exact (rest_of_listPolyParam Zero l) .
    Defined .

    Definition rest_of_listPolyParam_NextOne :
      forall (q : infiniteNumbers) (l : listPolyParam (NextOne q)), listPolyParam q 
      := ( fun q l => (formula_NextOne_of_optionsPolyParam__NextOne listPolyParam formula_Zero formula_NextOne q l
                                                               (rest_of_listPolyParam (NextOne q) l)) ) .

  End rest_of_listPolyParam .

  Section top_of_listPolyParam .

    Print unit .
    Let formula_Zero : forall (l : listPolyParam Zero), Type
      := ( fun ( _ : listPolyParam Zero) => unit ) .

    Let formula_NextOne : forall (q : infiniteNumbers) (l : listPolyParam (NextOne q)), Type
      := ( fun (q : infiniteNumbers) ( _ : listPolyParam (NextOne q) ) => data ) .

    Definition top_of_listPolyParam : forall (p : infiniteNumbers) (l : listPolyParam p),
      optionsPolyParam listPolyParam formula_Zero formula_NextOne p l .
    Proof .
      intros p l . case l .
      - apply (Param_Zero listPolyParam formula_Zero formula_NextOne) . unfold formula_Zero .
        exact tt .
      - intros dat q l' .
        apply (Param_NextOne listPolyParam formula_Zero formula_NextOne) . unfold formula_NextOne .
        exact dat .
    Defined .

    Definition top_of_listPolyParam_NextOne :
      forall (q : infiniteNumbers) (l : listPolyParam (NextOne q)), data .
    Proof .
      intros q l . apply (formula_NextOne_of_optionsPolyParam__NextOne listPolyParam formula_Zero formula_NextOne q l) .
      exact (top_of_listPolyParam (NextOne q) l) .
    Defined .

    Definition top_of_listPolyParam_Zero : forall (l : listPolyParam Zero), unit
      := ( fun l => (formula_Zero_of_optionsPolyParam__Zero listPolyParam formula_Zero formula_NextOne l
                                                       (top_of_listPolyParam Zero l)) ) .

  End top_of_listPolyParam .

  Section bottom_of_listPolyParam .

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

Compute (rest_of_listPolyParam_NextOne binary (NextOne (NextOne Zero))
                                 (JoinOne binary false (NextOne (NextOne Zero))
                                          (JoinOne binary false (NextOne Zero)
                                                   (JoinOne binary true Zero
                                                            (Empty binary))))) .
Compute (rest_of_listPolyParam_Zero binary (Empty binary)) .


Compute (JoinOne binary true Zero (Empty binary)) .
Compute (JoinOne _ true Zero (Empty _)) .
Compute (JoinOne _ true _ (Empty _)) .
(**MEMO: parameters can also be inferred-implicit , in addition to polymorphism-objects , via [Notation] command *)
Notation "d :: l" := (JoinOne _ d _ l) .
Notation "!00!" := (Empty _) .
Compute ( true :: !00! ).


Compute (rest_of_listPolyParam_NextOne _ _ ( false ::  false ::  true :: !00! ) ) .
Notation "'rest'" := ( rest_of_listPolyParam_NextOne _ _ ) .
Compute (rest ( false ::  false ::  true :: !00! ) ) .
(**MEMO: parameters can also be inferred-implicit , in addition to polymorphism-objects  , via [Arguments] command *)
Arguments rest_of_listPolyParam_NextOne [data] [q] l .
Compute (rest_of_listPolyParam_NextOne ( false ::  false ::  true :: !00! ) ) .

Compute (top_of_listPolyParam_NextOne _ _
                                 ( false ::  false ::  true :: !00! )) .
Compute (top_of_listPolyParam_Zero binary ( !00! )  ) .

Compute (bottom_of_listPolyParam_NextOne binary (NextOne (NextOne Zero))
                                 ( false ::  false ::  true :: !00! )) .
Compute (bottom_of_listPolyParam_Zero binary (Empty binary)) .

End PolymorphismParametrizedInductiveImplicitNotations .



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
(** Guīnà de wúxiàn shùzì: Lèixíng:=
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

论点 论点1 : 用 ( p外内 : 无限数字 ) ,
    加更多 (下一个 零) p外内 = 加更多 p外内 (下一个 零) .
(** Lùndiǎn lùndiǎn 1: Duì quánbù (p wài nèi: Wúxiàn shùzì),
    jiā gèng duō (xià yīgè líng) p wài nèi = jiā gèng duō p wài nèi (xià yīgè líng). *)
证明 .
(** Zhèngmíng. *)
  介绍们 p外内 .
  (** Jièshàomen p wài nèi. *)
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
    介绍们 q外内 .
    (** jièshàomen q wài nèi. *)
    介绍们 论点1_q外内 .
    (** Jièshàomen lùndiǎn 1_q wài nèi. *)
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

