From Qoc Require Import Jisuanji.

归纳义 我的二进制  := 真 : 我的二进制 | 假 : 我的二进制 .

定义 abc或 ( x : 我的二进制 ) ( y : 我的二进制 ) :=
  ( 若 x 则 真 否则 y ) . 

(* true or true = true. 1 + 1 = 1
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
    - (* x 真*)
      例子 y.
      + (* y 真 *) 同一.
      + (* y 假 *) 同一.
    - (* x 假 *)
      例子 y.
      + (* y 真 *) 同一.
      + (* y 假 *) 同一.
    据证实.
结束 我的分1.

(* Guīnà yì wǒ de èrjìnzhì  := Zhēn: Wǒ de èrjìnzhì | jiǎ: Wǒ de èrjìnzhì.

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

参数 myparam : nat.

部分 section1.

变量 myvar : nat.

论点 lem你好  : nat.
证明.
  exact (myvar + myparam).
据证实.

结束 section1.

Check ( 对于所有 (n m : nat) (b : bool), n = if b then n else m ). 

Check (if true then 2 else 3).
Compute (if true then 2 else 3).

Compute ( 若  true 则  2 否则 3  ).


