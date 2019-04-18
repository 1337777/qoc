From Qoc Require Import Jisuanji .

(** 

短 :: 为了解决一些错误，自己应该围绕这个错误搜索一些东西。
例如：
<我> 你好鸡算计电脑，
如果我挫误，
你会失败，
你会找到错误。
<鸡算计> 错误：在第2行和第6列;在当前环境中未找到参考“挫误”。
<我> (*评论: 我去了这个包含所有已知单词的图书馆/词典： “https://translate.google.cn/#view=home&op=translate&sl=zh-CN&tl=en&text=不对” 。 我“搜索”这个相似的含义：“不对”。此搜索表明该库包含相关的动词“错误”。现在我更正了我的计算机程序。 *)
<我> 你好鸡算计电脑，
如果我错误，
你会失败，
你会找到错误。
<鸡算计> “目的”是定义的 。

Short :: To solve some error , oneself shall search for something around this error .
EXAMPLE:
<ME> Hello COQ computer ,
If I erors then ,
you will fail and you will locate the surrounding of the fault .
<COQ> Error: At line 2 and column 5 ; The reference "erors" was not found in the current environment. 
<ME> (*COMMENT: I go to the library/dictionary which contains all the known words : https://www.thefreedictionary.com/mistake . And I "search" this similar meaning : "mistake" . This search says that this library contains the related verb "err" . Now I correct my computer program . *)
<ME> Hello COQ computer ,
If I err then ,
you will fail and you will locate the fault .
<COQ> "Goal" is defined .


Outline ::
 * PART 1 : SEARCH , ERRORS . 第1部分 : 搜索，错误

*)


(** * PART 1 : SEARCH , ERRORS . 第1部分 : 搜索，错误 *)

打印 Nat.add .
(**INFO:
Nat.add = 
固定 add (n m : nat) {构 n} : nat := 匹配 n 与
                                  | 0 => m
                                  | S p => S (add p m)
                                  结束
     : nat -> nat -> nat
*)

搜索 Nat.add .
(**INFO:
 f_equal2_plus  用 x1 y1 x2 y2 : nat, x1 = y1 -> x2 = y2 -> x1 + x2 = y1 + y2
plus_n_O  用 n : nat, n = n + 0
plus_O_n  用 n : nat, 0 + n = n
plus_n_Sm  用 n m : nat, S (n + m) = n + S m
...
 *)
搜索 0 Nat.add .
(**INFO:
plus_O_n: 用 n : nat, 0 + n = n
plus_n_O: 用 n : nat, n = n + 0
*)
搜索 ( ?n + 0 ) .
(**INFO:
 plus_n_O  用 n : nat, n = n + 0 *)
搜索'改写 ( ?n + 0 )  .
(**INFO:
 plus_n_O  用 n : nat, n = n + 0 *)
搜索 ( ?n = ?n + 0 ) .
(**INFO:
 plus_n_O  用 n : nat, n = n + 0 *)
搜索 ( ?n + 0 = ?n ) .
(**INFO:
                                 *)

论点 我的论点 : 用 n : nat, 0 + n = n .
(**INFO:
1 子目的 (ID 3)
  
  ============================
  用 n : nat, 0 + n = n
*)
证明 .
  移动外 n .
  同一 .
  (**INFO:
   没有更多的子目的.
   *)
据证实 .
(**INFO:
 我的论点 是定义了
 *)

(** 论点 我的论点 : 用 n : nat, n + false = n . *)
失败了 论点 我的论点 : 用 n : nat, n + false = n .
(**INFO:
该命令确实因此消息而失败:
         在环境中
         n : nat
         术语 "false" 具有类型 "bool" 而预期类型为 "nat".
*)

(** 论点 我的论点 : 用 n : nat, n + 0 = n . *)
失败了 论点 我的论点 : 用 n : nat, n + 0 = n .
(**INFO:
该命令确实因此消息而失败:
         我的论点 已经存在.
*)

论点 我的另一个论点 : 用 n : nat, n + 0 = n .
(**INFO:
1 子目的 (ID 6)
  
  ============================
  用 n : nat, n + 0 = n
*)
证明 .
  移动外 n .
  (** 同一 . *)
  失败了 同一 .
  (**INFO:
     该命令确实因此消息而失败:
         在环境中
         n : nat
         无法统一 "n" 与 "n + 0".
   *)

  搜索 ( ?n + 0 ) .
  (**INFO:
     plus_n_O  用 n : nat, n = n + 0 *)
  改写 <- plus_n_O .
  同一 .
  (**INFO:
     没有更多的子目的.
   *)
据证实.
(**INFO:
我的另一个论点 是定义了
*)

(** ** alt
----------------------------------------------------------------------------- *)

Reset 我的论点.

Print Nat.add .
(**INFO:
Nat.add = 
固定 add (n m : nat) {构 n} : nat := 匹配 n 与
                                  | 0 => m
                                  | S p => S (add p m)
                                  结束
     : nat -> nat -> nat
*)

Search Nat.add .
(**INFO:
 f_equal2_plus  用 x1 y1 x2 y2 : nat, x1 = y1 -> x2 = y2 -> x1 + x2 = y1 + y2
plus_n_O  用 n : nat, n = n + 0
plus_O_n  用 n : nat, 0 + n = n
plus_n_Sm  用 n m : nat, S (n + m) = n + S m
...
 *)
Search 0 Nat.add .
(**INFO:
plus_O_n: 用 n : nat, 0 + n = n
plus_n_O: 用 n : nat, n = n + 0
*)
Search ( ?n + 0 ) .
(**INFO:
 plus_n_O  用 n : nat, n = n + 0 *)
SearchRewrite ( ?n + 0 )  .
(**INFO:
 plus_n_O  用 n : nat, n = n + 0 *)
Search ( ?n = ?n + 0 ) .
(**INFO:
 plus_n_O  用 n : nat, n = n + 0 *)
Search ( ?n + 0 = ?n ) .
(**INFO:
                                 *)

Lemma mylemma : forall n : nat, 0 + n = n .
(**INFO:
1 子目的 (ID 3)
  
  ============================
  用 n : nat, 0 + n = n
*)
Proof .
  intros n .
  reflexivity .
  (**INFO:
     No more subgoals. *)
Qed .
(**INFO:
mylemma 是定义了
*)

(** Lemma mylemma : forall n : nat, n + false = n . *)
Fail Lemma mylemma : forall n : nat, n + false = n .
(** Error:
In environment
n : nat
The term "false" has type "bool" while it is expected to have type "nat". *)

(** Lemma mylemma : forall n : nat, n + 0 = n . *)
Fail Lemma mylemma : forall n : nat, n + 0 = n .
(** Error: mylemma already exists.  *)

Lemma myotherlemma : forall n : nat, n + 0 = n .
Proof .
  intros n .
  (** reflexivity . *)
  Fail reflexivity .
  (** Error: In environment
      n : nat
      Unable to unify "n" with "n + 0". *)

  Search ( ?n + 0 ) .
  (** plus_n_O  用 n : nat, n = n + 0 *)
  rewrite <- plus_n_O .
  reflexivity .
Qed.
