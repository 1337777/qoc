From Qoc Require Import Jisuanji .

(** 

短 :: 示例：“A ; [> W & [+ T1 | T2 ] ]”。
建筑师“A”将主要问题“（1）”计划为两个“后续”子问题：工人“W”的子问题“（1> 1）”以及“并行”子问题“ （1> 2）”为工人“T”。
工人“W”尝试他的唯一战术“W”，解决了他的子问题“（1> 1）”。
与此同时，工人“T”尝试了他的第一个失败的战术“T1”;但他的“替代”策略“T2”解决了他的子问题“（1> 2）”。

Short :: Example : "A ; [> W & [+ T1 | T2 ] ]" .
The architech "A" plans the main problem "(1)" into two "subsequent" sub-problems : the sub-problem "(1>1)" for the worker "W" and also the "parallel" sub-problem "(1>2)" for the worker "T" . 
The worker "W" tries his only tactic "W" which solves his sub-problem "(1>1)" . 
Meanwhile the worker "T" tries his first tactic "T1" which fails ;  but his "alternative" tactic "T2" solves his sub-problem "(1>2)" .

Outline ::
 * PART 1 : PARALLEL SUBSEQUENT TACTICS . 第1部分 : 平行随后的战术
 * PART 2 : ALTERNATIVE TACTIC INSTEAD OF FAILED TACTIC . 第2部分 : 失败的战术的替代战术  *)


(** * PART 1 : PARALLEL SUBSEQUENT TACTICS . 第1部分 : 平行随后的战术 *)

Goal forall n : nat + nat , forall b : bool + bool , ( n = n /\ b = b ) .
  intros n b.
  解构 n. destruct b.  Undo 2.
  解构 n  ; 解构 b . Undo .

  解构 n; ( 解构 b ;
                [> idtac & idtac & idtac & idtac ] ) . Undo.
  解构 n; ( 内: 解构 b ;
               [> idtac & idtac ] ) . Undo.
  解构 n; 内: 解构 b ;
                       [> idtac & idtac ]  . Undo.
  解构 n; ( 解构 b;
                [ idtac & idtac ] ) . Undo.
  
Abort .

Goal forall B C D : Prop, (False /\ B) /\ (C /\ D).
  split. Undo.
  split; split. Undo.
  做 2 split. Undo.
  重复 split. Undo.
  进展 重复 split.
  1 : {
    失败 进展 重复 split.
    尝试 进展 重复 split.
    承认.
  }

Abort.


(** ** alt
----------------------------------------------------------------------------- *)

Goal forall n : nat + nat , forall b : bool + bool , ( n = n /\ b = b ) .
  intros n b.
  destruct n. Undo.
  destruct n  ; destruct b . Undo .

  destruct n; ( destruct b ;
                [> idtac & idtac & idtac & idtac ] ) . Undo.
  destruct n; ( inner: destruct b ;
               [> idtac & idtac ] ) . Undo.
  destruct n; inner: destruct b ;
                       [> idtac & idtac ]  . Undo.
  destruct n; ( destruct b;
                [ idtac & idtac ] ) . Undo.

  (** nei *)
  destruct n; ( 内: destruct b ;
               [> idtac & idtac ] ) . Undo.
  
Abort .

Goal forall B C D : Prop, (False /\ B) /\ (C /\ D).
  split; split. Undo.
  do 2 split. Undo.
  repeat split. Undo.
  progress repeat split.
  1 : {
    Fail progress repeat split.
    try progress repeat split.
    admit.
  }

Abort.


(**
----------------------------------------------------------------------------- *)


(** * PART 2 : ALTERNATIVE TACTIC INSTEAD OF FAILED TACTIC . 第2部分 : 失败的战术的替代战术  *)

(** _ + _ *)  (** first [ _ ] *)  (** tryif _ 否则 _ 则 *)
目的 True .
  [+ fail | idtac "a" ]. (** = _ + _ *)
  外 改变化 [fail | idtac "a" ]. (** = _ + _ *)
  改变化 [fail | idtac "a" ]. (** = first [ _ ] *)

  失败 外 改变化 [ ] .
  失败 改变化 [ ] .

  失败 外 改变化 [ fail | idtac "a" | idtac "b"  ]; idtac "c"; fail .
  (* a c b c *)
  失败 无外 (外 改变化 [ fail | idtac "a" | idtac "b"  ]); idtac "c"; fail .
  (* a c *)
  失败 改变化 [ fail | idtac "a" | idtac "b"  ]; idtac "c"; fail .
  (* a c *)

  外 内 改变 fail 则 idtac "a"
                    否则 idtac "b" .
  外 改变 fail 则 idtac "a"
                    否则 idtac "b" . (** = tryif _ 否则 _ 则 *)
  内 改变 fail 则 idtac "a"
                    否则 idtac "b" .
  改变 fail 则 idtac "a"
                    否则 idtac "b" .


  失败 (          外 内 改变 idtac "a" 则 外 改变化 [idtac "b" | idtac "b'"]; fail
                           否则 外 改变化 [idtac "i" | idtac "i'"] ); idtac "o"; fail .
  (*  a b b' i o i' o *)
  失败 (                内 改变 idtac "a" 则 外 改变化 [idtac "b" | idtac "b'"]; fail
                          否则 外 改变化 [idtac "i" | idtac "i'"] ); idtac "o"; fail .
  (* a b b' i o *)
  失败 (无外 (外 内 改变 idtac "a" 则 外 改变化 [idtac "b" | idtac "b'"]; fail
                           否则 外 改变化 [idtac "i" | idtac "i'"] )); idtac "o"; fail .
  (* a b b' i o *)
  失败 (          外       改变 idtac "a" 则 外 改变化 [idtac "b" | idtac "b'"]; fail
                          否则 外 改变化 [idtac "i" | idtac "i'"] ); idtac "o"; fail .
  (* a b b' *)
  失败 (无外 (外       改变 idtac "a" 则 外 改变化 [idtac "b" | idtac "b'"]; fail
                          否则 外 改变化 [idtac "i" | idtac "i'"] )); idtac "o"; fail .
  (* a b b' *)
  失败 (                      改变 idtac "a" 则 外 改变化 [idtac "b" | idtac "b'"]; fail
                          否则 外 改变化 [idtac "i" | idtac "i'"] ); idtac "o"; fail .
  (* a b b' *)

  失败 (          外       改变 idtac "a" 则 外 改变化 [idtac "b" | idtac "b'"]
                          否则 外 改变化 [idtac "i" | idtac "i'"] ); idtac "o"; fail .
  (* a b o b' o *)
  失败 (无外 (外       改变 idtac "a" 则 外 改变化 [idtac "b" | idtac "b'"]
                          否则 外 改变化 [idtac "i" | idtac "i'"] )); idtac "o"; fail .
  (* a b o *)
  失败 (                      改变 idtac "a" 则 外 改变化 [idtac "b" | idtac "b'"]
                          否则 外 改变化 [idtac "i" | idtac "i'"] ); idtac "o"; fail .
  (* a b o *)

Abort.

(** match 目的 与 _ 结束 *)  (** match 颠倒 目的 与 _ 结束 *)
目的 forall P N : Prop, P.
  intros P N.
  
  外 内 统一 目的 与
   |- N => idtac "a"
  | |- P => idtac "b"            
  结束 .
  外 统一 目的 与
   |- N => idtac "a"
  | |- P => idtac "b"            
  结束 .
  内 统一 目的 与
   |- N => idtac "a"
  | |- P => idtac "b"            
  结束 . (** = match 目的 与 _ 结束 *)
  统一 目的 与
   |- N => idtac "a"
  | |- P => idtac "b"            
  结束 .

  外 内 统一 颠倒 目的 与
   |- N => idtac "a"
  | |- P => idtac "b"            
  结束 .
  外 统一 颠倒 目的 与
   |- N => idtac "a"
  | |- P => idtac "b"            
  结束 .
  内 统一 颠倒 目的 与
   |- N => idtac "a"
  | |- P => idtac "b"            
  结束 . (** = match 颠倒 目的 与 _ 结束 *)
  统一 颠倒 目的 与
   |- N => idtac "a"
  | |- P => idtac "b"            
  结束 .
  
  失败          外 内 统一 目的 与
         |- P  =>  外 改变化 [idtac "b" | idtac "b'"]; fail
       | |- P  =>  外 改变化 [idtac "i" | idtac "i'"]
       结束; idtac "o"; fail .
  (* b b' i o i' o *)  (* compare: a b b' i o i' o *)
  失败                内 统一 目的 与
         |- P  =>  外 改变化 [idtac "b" | idtac "b'"]; fail
       | |- P  =>  外 改变化 [idtac "i" | idtac "i'"]
       结束; idtac "o"; fail .
  (* b b' i o *)   (* compare: a b b' i o *)
  失败 无外 (外 内 统一 目的 与
         |- P  =>  外 改变化 [idtac "b" | idtac "b'"]; fail
       | |- P  =>  外 改变化 [idtac "i" | idtac "i'"]
       结束); idtac "o"; fail .
  (* b b' i o *)   (* compare: a b b' i o *)
  失败          外       统一 目的 与
         |- P  =>  外 改变化 [idtac "b" | idtac "b'"]; fail
       | |- P  =>  外 改变化 [idtac "i" | idtac "i'"]
       结束; idtac "o"; fail .
  (* b b' *)   (* compare: a b b' *)
  失败 无外 (外       统一 目的 与
         |- P  =>  外 改变化 [idtac "b" | idtac "b'"]; fail
       | |- P  =>  外 改变化 [idtac "i" | idtac "i'"]
       结束); idtac "o"; fail .
  (* b b' *)   (* compare: a b b' *)
  失败                      统一 目的 与
         |- P  =>  外 改变化 [idtac "b" | idtac "b'"]; fail
       | |- P  =>  外 改变化 [idtac "i" | idtac "i'"]
       结束; idtac "o"; fail .
  (* b b' *)   (* compare: a b b' *)

  
  失败          外       统一 目的 与
         |- P  =>  外 改变化 [idtac "b" | idtac "b'"]
       | |- P  =>  外 改变化 [idtac "i" | idtac "i'"]
       结束; idtac "o"; fail .
  (* b o b' o *)   (* compare: a b o b' o *)
  失败 无外 (外       统一 目的 与
         |- P  =>  外 改变化 [idtac "b" | idtac "b'"]
       | |- P  =>  外 改变化 [idtac "i" | idtac "i'"]
       结束); idtac "o"; fail .
  (* b o *)   (* compare: a b o *)
  失败                      统一 目的 与
         |- P  =>  外 改变化 [idtac "b" | idtac "b'"]
       | |- P  =>  外 改变化 [idtac "i" | idtac "i'"]
       结束; idtac "o"; fail .
  (* b o *)   (* compare: a b o *)

Abort.

(** match _ 与 _ 结束 *)
目的 forall P N : Prop, True.
  intros P N.
  
  外 内 统一 P 与
    N => idtac "a"
  |  P => idtac "b"             
  结束 .
  外 统一 P 与
    N => idtac "a"
  |  P => idtac "b"             
  结束 .
  内 统一 P 与
    N => idtac "a"
  |  P => idtac "b"             
  结束 . (** = match _ 与 _ 结束 *)
  统一 P 与
    N => idtac "a"
  |  P => idtac "b"             
  结束 .

  
  失败          外 内 统一 P 与
          P  =>  外 改变化 [idtac "b" | idtac "b'"]; fail
       |  P  =>  外 改变化 [idtac "i" | idtac "i'"]
       结束; idtac "o"; fail .
  (* b b' i o i' o *)  (* compare: a b b' i o i' o *)
  失败                内 统一 P 与
          P  =>  外 改变化 [idtac "b" | idtac "b'"]; fail
       |  P  =>  外 改变化 [idtac "i" | idtac "i'"]
       结束; idtac "o"; fail .
  (* b b' i o *)   (* compare: a b b' i o *)
  失败 无外 (外 内 统一 P 与
          P  =>  外 改变化 [idtac "b" | idtac "b'"]; fail
       |  P  =>  外 改变化 [idtac "i" | idtac "i'"]
       结束); idtac "o"; fail .
  (* b b' i o *)   (* compare: a b b' i o *)
  失败          外       统一 P 与
          P  =>  外 改变化 [idtac "b" | idtac "b'"]; fail
       |  P  =>  外 改变化 [idtac "i" | idtac "i'"]
       结束; idtac "o"; fail .
  (* b b' *)   (* compare: a b b' *)
  失败 无外 (外       统一 P 与
          P  =>  外 改变化 [idtac "b" | idtac "b'"]; fail
       |  P  =>  外 改变化 [idtac "i" | idtac "i'"]
       结束); idtac "o"; fail .
  (* b b' *)   (* compare: a b b' *)
  失败                      统一 P 与
          P  =>  外 改变化 [idtac "b" | idtac "b'"]; fail
       |  P  =>  外 改变化 [idtac "i" | idtac "i'"]
       结束; idtac "o"; fail .
  (* b b' *)   (* compare: a b b' *)

  
  失败          外       统一 P 与
          P  =>  外 改变化 [idtac "b" | idtac "b'"]
       |  P  =>  外 改变化 [idtac "i" | idtac "i'"]
       结束; idtac "o"; fail .
  (* b o b' o *)   (* compare: a b o b' o *)
  失败 无外 (外       统一 P 与
          P  =>  外 改变化 [idtac "b" | idtac "b'"]
       |  P  =>  外 改变化 [idtac "i" | idtac "i'"]
       结束); idtac "o"; fail .
  (* b o *)   (* compare: a b o *)
  失败                      统一 P 与
          P  =>  外 改变化 [idtac "b" | idtac "b'"]
       |  P  =>  外 改变化 [idtac "i" | idtac "i'"]
       结束; idtac "o"; fail .
  (* b o *)   (* compare: a b o *)

Abort.


(** ** alt
----------------------------------------------------------------------------- *)


(** _ + _ *)  (** first [ _ ] *)  (** tryif _ else _ then *)
Goal True .
  [+ fail | idtac "a" ]. (** = _ + _ *)
  outer alts [fail | idtac "a" ]. (** = _ + _ *)
  alts [fail | idtac "a" ]. (** = first [ _ ] *)

  Fail outer alts [ ] .
  Fail alts [ ] .

  Fail outer alts [ fail | idtac "a" | idtac "b"  ]; idtac "c"; fail .
  (* a c b c *)
  Fail no_outer (outer alts [ fail | idtac "a" | idtac "b"  ]); idtac "c"; fail .
  (* a c *)
  Fail alts [ fail | idtac "a" | idtac "b"  ]; idtac "c"; fail .
  (* a c *)

  outer inner alter fail then idtac "a"
                    else idtac "b" .
  outer alter fail then idtac "a"
                    else idtac "b" . (** = tryif _ else _ then *)
  inner alter fail then idtac "a"
                    else idtac "b" .
  alter fail then idtac "a"
                    else idtac "b" .


  Fail (          outer inner alter idtac "a" then outer alts [idtac "b" | idtac "b'"]; fail
                           else outer alts [idtac "i" | idtac "i'"] ); idtac "o"; fail .
  (*  a b b' i o i' o *)
  Fail (                inner alter idtac "a" then outer alts [idtac "b" | idtac "b'"]; fail
                          else outer alts [idtac "i" | idtac "i'"] ); idtac "o"; fail .
  (* a b b' i o *)
  Fail (no_outer (outer inner alter idtac "a" then outer alts [idtac "b" | idtac "b'"]; fail
                           else outer alts [idtac "i" | idtac "i'"] )); idtac "o"; fail .
  (* a b b' i o *)
  Fail (          outer       alter idtac "a" then outer alts [idtac "b" | idtac "b'"]; fail
                          else outer alts [idtac "i" | idtac "i'"] ); idtac "o"; fail .
  (* a b b' *)
  Fail (no_outer (outer       alter idtac "a" then outer alts [idtac "b" | idtac "b'"]; fail
                          else outer alts [idtac "i" | idtac "i'"] )); idtac "o"; fail .
  (* a b b' *)
  Fail (                      alter idtac "a" then outer alts [idtac "b" | idtac "b'"]; fail
                          else outer alts [idtac "i" | idtac "i'"] ); idtac "o"; fail .
  (* a b b' *)

  Fail (          outer       alter idtac "a" then outer alts [idtac "b" | idtac "b'"]
                          else outer alts [idtac "i" | idtac "i'"] ); idtac "o"; fail .
  (* a b o b' o *)
  Fail (no_outer (outer       alter idtac "a" then outer alts [idtac "b" | idtac "b'"]
                          else outer alts [idtac "i" | idtac "i'"] )); idtac "o"; fail .
  (* a b o *)
  Fail (                      alter idtac "a" then outer alts [idtac "b" | idtac "b'"]
                          else outer alts [idtac "i" | idtac "i'"] ); idtac "o"; fail .
  (* a b o *)

Abort.

(** match goal with _ end *)  (** match reverse goal with _ end *)
Goal forall P N : Prop, P.
  intros P N.
  
  outer inner unify goal with
   |- N => idtac "a"
  | |- P => idtac "b"            
  end .
  outer unify goal with
   |- N => idtac "a"
  | |- P => idtac "b"            
  end .
  inner unify goal with
   |- N => idtac "a"
  | |- P => idtac "b"            
  end . (** = match goal with _ end *)
  unify goal with
   |- N => idtac "a"
  | |- P => idtac "b"            
  end .

  outer inner unify reverse goal with
   |- N => idtac "a"
  | |- P => idtac "b"            
  end .
  outer unify reverse goal with
   |- N => idtac "a"
  | |- P => idtac "b"            
  end .
  inner unify reverse goal with
   |- N => idtac "a"
  | |- P => idtac "b"            
  end . (** = match reverse goal with _ end *)
  unify reverse goal with
   |- N => idtac "a"
  | |- P => idtac "b"            
  end .
  
  Fail          outer inner unify goal with
         |- P  =>  outer alts [idtac "b" | idtac "b'"]; fail
       | |- P  =>  outer alts [idtac "i" | idtac "i'"]
       end; idtac "o"; fail .
  (* b b' i o i' o *)  (* compare: a b b' i o i' o *)
  Fail                inner unify goal with
         |- P  =>  outer alts [idtac "b" | idtac "b'"]; fail
       | |- P  =>  outer alts [idtac "i" | idtac "i'"]
       end; idtac "o"; fail .
  (* b b' i o *)   (* compare: a b b' i o *)
  Fail no_outer (outer inner unify goal with
         |- P  =>  outer alts [idtac "b" | idtac "b'"]; fail
       | |- P  =>  outer alts [idtac "i" | idtac "i'"]
       end); idtac "o"; fail .
  (* b b' i o *)   (* compare: a b b' i o *)
  Fail          outer       unify goal with
         |- P  =>  outer alts [idtac "b" | idtac "b'"]; fail
       | |- P  =>  outer alts [idtac "i" | idtac "i'"]
       end; idtac "o"; fail .
  (* b b' *)   (* compare: a b b' *)
  Fail no_outer (outer       unify goal with
         |- P  =>  outer alts [idtac "b" | idtac "b'"]; fail
       | |- P  =>  outer alts [idtac "i" | idtac "i'"]
       end); idtac "o"; fail .
  (* b b' *)   (* compare: a b b' *)
  Fail                      unify goal with
         |- P  =>  outer alts [idtac "b" | idtac "b'"]; fail
       | |- P  =>  outer alts [idtac "i" | idtac "i'"]
       end; idtac "o"; fail .
  (* b b' *)   (* compare: a b b' *)

  
  Fail          outer       unify goal with
         |- P  =>  outer alts [idtac "b" | idtac "b'"]
       | |- P  =>  outer alts [idtac "i" | idtac "i'"]
       end; idtac "o"; fail .
  (* b o b' o *)   (* compare: a b o b' o *)
  Fail no_outer (outer       unify goal with
         |- P  =>  outer alts [idtac "b" | idtac "b'"]
       | |- P  =>  outer alts [idtac "i" | idtac "i'"]
       end); idtac "o"; fail .
  (* b o *)   (* compare: a b o *)
  Fail                      unify goal with
         |- P  =>  outer alts [idtac "b" | idtac "b'"]
       | |- P  =>  outer alts [idtac "i" | idtac "i'"]
       end; idtac "o"; fail .
  (* b o *)   (* compare: a b o *)

Abort.

(** match _ with _ end *)
Goal forall P N : Prop, True.
  intros P N.
  
  outer inner unify P with
    N => idtac "a"
  |  P => idtac "b"             
  end .
  outer unify P with
    N => idtac "a"
  |  P => idtac "b"             
  end .
  inner unify P with
    N => idtac "a"
  |  P => idtac "b"             
  end . (** = match _ with _ end *)
  unify P with
    N => idtac "a"
  |  P => idtac "b"             
  end .

  
  Fail          outer inner unify P with
          P  =>  outer alts [idtac "b" | idtac "b'"]; fail
       |  P  =>  outer alts [idtac "i" | idtac "i'"]
       end; idtac "o"; fail .
  (* b b' i o i' o *)  (* compare: a b b' i o i' o *)
  Fail                inner unify P with
          P  =>  outer alts [idtac "b" | idtac "b'"]; fail
       |  P  =>  outer alts [idtac "i" | idtac "i'"]
       end; idtac "o"; fail .
  (* b b' i o *)   (* compare: a b b' i o *)
  Fail no_outer (outer inner unify P with
          P  =>  outer alts [idtac "b" | idtac "b'"]; fail
       |  P  =>  outer alts [idtac "i" | idtac "i'"]
       end); idtac "o"; fail .
  (* b b' i o *)   (* compare: a b b' i o *)
  Fail          outer       unify P with
          P  =>  outer alts [idtac "b" | idtac "b'"]; fail
       |  P  =>  outer alts [idtac "i" | idtac "i'"]
       end; idtac "o"; fail .
  (* b b' *)   (* compare: a b b' *)
  Fail no_outer (outer       unify P with
          P  =>  outer alts [idtac "b" | idtac "b'"]; fail
       |  P  =>  outer alts [idtac "i" | idtac "i'"]
       end); idtac "o"; fail .
  (* b b' *)   (* compare: a b b' *)
  Fail                      unify P with
          P  =>  outer alts [idtac "b" | idtac "b'"]; fail
       |  P  =>  outer alts [idtac "i" | idtac "i'"]
       end; idtac "o"; fail .
  (* b b' *)   (* compare: a b b' *)

  
  Fail          outer       unify P with
          P  =>  outer alts [idtac "b" | idtac "b'"]
       |  P  =>  outer alts [idtac "i" | idtac "i'"]
       end; idtac "o"; fail .
  (* b o b' o *)   (* compare: a b o b' o *)
  Fail no_outer (outer       unify P with
          P  =>  outer alts [idtac "b" | idtac "b'"]
       |  P  =>  outer alts [idtac "i" | idtac "i'"]
       end); idtac "o"; fail .
  (* b o *)   (* compare: a b o *)
  Fail                      unify P with
          P  =>  outer alts [idtac "b" | idtac "b'"]
       |  P  =>  outer alts [idtac "i" | idtac "i'"]
       end; idtac "o"; fail .
  (* b o *)   (* compare: a b o *)

Abort.
