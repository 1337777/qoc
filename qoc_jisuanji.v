From Qoc Require Import Jisuanji.

归纳义 我的二进制  := 真 : 我的二进制 | 假 : 我的二进制 .

定义 或 ( x : 我的二进制 ) ( y : 我的二进制 ) := ( 若 x 则 真 否则 y ) . 

部分 我的分1.
  变量 x : 我的二进制.
  变量 y : 我的二进制.

  论点 我的论点1 : 或 x y  =  或 y x .
  证明.
    展开 或.
    例子 x.
    - 例子 y.
      + 同一.
      + 同一.
    - 例子 y.
      + 同一.
      + 同一.
   据证实.
结束 我的分1.










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


