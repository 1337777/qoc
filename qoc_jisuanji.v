From Qoc Require Import Jisuanji.

参数 myparam : nat.

部分 section1.

变量 myvar : nat.

引理 lem你好  : nat.
证明.
  exact (myvar + myparam).
据证实.

结束 section1.

Check ( 对于所有 (n m : nat) (b : bool), n = if b then n else m ). 

Check (if true then 2 else 3).
Compute (if true then 2 else 3).
Compute ( 如果 true 然后 2 否则 3  ).
