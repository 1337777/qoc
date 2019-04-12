From Qoc Require Import Jisuanji .


(**
（1.）在先前的实时转录中，我确实展示了如何使用符号来隐藏隐含/推断的信息。例如，符号（[“fish”，“dog”，“cat”]）确实隐藏了关于类型的信息（“动物”）。此外，符号（[“gold”，“green”，“blue”，“red”]）确实隐藏了有关类型（“颜色”）的信息。

（2.）因此序列集合被写为（序列类型）。这被称为“多态”。

（3.）符号可以隐藏许多信息/参数。例如，符号（[“fish”，“dog”，“cat”]）确实隐藏了有关size / parameter（“3”）的信息。此外，符号（[“gold”，“green”，“blue”，“red”]）确实隐藏了有关size / parameter（“4”）的信息。

（4.）因此，序列集合现在写为（序列类型大小）。这被称为“参数化”。

（5.）记住定义函数“bottom”，例如（bottom [“fish”，“dog”，“cat”] =“cat”）。但是对于空序列会发生什么：（bottom [] = ???）。因此，函数输出的形式取决于大小/参数：输出的形式是一个选择/选项，它取决于大小/参数。

（6.）在先前的实时转录中，这个选择/选项非常简单：只有两个选择。但是现在在这个实时转录中，有许多选择通过大小/参数进行参数化。

（7.）因此选项集合被写为（选项类型大小序列）。这被称为“逻辑规范”。 
*)

模块 多态'参数化了'归纳的隐含符号 .
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
    移动外 p . 例子 p (** 因为[无限数字]是计算的 *) .
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
    移动外 p l f .
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
    移动外 l . 确切 (结构化的'选项们'多态'参数_对于_选项们'多态'参数 零 l) .
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
      移动外 p l . 例子 l .
      (** Jièshàomen p l. Lìzi l. *)
      - 应用 (参数_零 序列'多态'参数 公式_零 公式_下一个) . 展开 公式_零 .
        (** Yìngyòng (cānshù_líng xùliè'duō tài'cānshù gōngshì_líng gōngshì_xià yīgè). Zhǎnkāi gōngshì_líng. *)
        确切 空的 .
        (** Quèqiè kōng de. *)
      - 移动外 d q l' . 
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
      移动外 l .
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
      移动外 p l . 例子 l .
      (** Jièshàomen p l. Lìzi l. *)
      - 应用 (参数_零 序列'多态'参数 公式_零 公式_下一个) . 展开 公式_零 .
        (** Yìngyòng (cānshù_líng xùliè'duō tài'cānshù gōngshì_líng gōngshì_xià yīgè). Zhǎnkāi gōngshì_líng. *)
        确切 单 .
        (** Quèqiè dān. *)
      - 移动外 dat q l' .
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
      移动外 q l . 应用 (公式_下一个_对于_选项们'多态'参数__下一个 序列'多态'参数 公式_零 公式_下一个 q l) .
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
      - 清除 p l . 移动外 dat q l' .
        (** Qīngchú p l. Jièshàomen dat q l' . *)
        例子 (底部_对于_序列'多态'参数 q l').
        (** Lìzi (dǐbù_duìyú_xùliè'duō tài'cānshù q l'). *)
        + 清除 q l' ; 移动外 l' . 移动外 底部_对于_序列'多态'参数_q_l' .
          (** Qīngchú q l' ; jièshàomen l' . Jièshàomen dǐbù_duìyú_xùliè'duō tài'cānshù_q_l' . *)
          展开 公式_零 在 底部_对于_序列'多态'参数_q_l' . 清除 底部_对于_序列'多态'参数_q_l' .
          (** Zhǎnkāi gōngshì_líng zài dǐbù_duìyú_xùliè'duō tài'cānshù_q_l' . Qīngchú dǐbù_duìyú_xùliè'duō tài'cānshù_q_l' . *)
          应用 (参数_下一个 序列'多态'参数 公式_零 公式_下一个) . 展开 公式_下一个 .
          (** Yìngyòng (cānshù_xià yīgè xùliè'duō tài'cānshù gōngshì_líng gōngshì_xià yīgè). Zhǎnkāi gōngshì_xià yīgè. *)
          确切 dat .
          (** Quèqiè dat. *)
        + 清除 q l' ; 移动外 r l' . 移动外 底部_对于_序列'多态'参数_q_l' .
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
      移动外 q l . 应用 (公式_下一个_对于_选项们'多态'参数__下一个 序列'多态'参数 公式_零 公式_下一个 q l) .
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
