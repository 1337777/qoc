From Qoc Require Import Jisuanji .

(** 

短 :: 一个命令/策略“A”可以对目标/问题起作用并产生许多新的较小的子目标。然后，许多“替代”命令中的一些命令“D”可以在这些子目标中的一个附近“序列”。但是这个“序列”子目标是哪个，这是“替代”命令？

Short :: one command/tactic "A" may act on a goal/problem and generate many new smaller subgoals . Then some command "D" among many "alternative" commands may be in "sequence" near one of these subgoals . But which is this "sequence" subgoal and which is this "alternative" command ?

 Example :  "A ; [> ( alts [ B | B' ] ) & E ]"

Outline ::
* PART1 : SEQUENCES TACTIC
* PART2 : ALTERNATIVES TACTIC  *)

(** PART1 : SEQUENCES TACTIC *)

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

(*
Goal forall n: Nat + nat, forall b: Bool + bool, (n = n/\ b = b).
  Intros n b.
  Jiěgòu n. Undo.
  Jiěgòu n  ; jiěgòu b. Undo.

  Jiěgòu n; (jiěgòu b;
                [> idtac & idtac & idtac & idtac] ). Undo.
  Jiěgòu n; (inner: Jiěgòu b;
               [> idtac & idtac] ). Undo.
  Jiěgòu n; inner: Jiěgòu b;
                       [> idtac & idtac]  . Undo.
  Jiěgòu n; (jiěgòu b;
                [idtac & idtac] ). Undo.

  (** Nei*)
  jiěgòu n; (nèi: Jiěgòu b;
               [> idtac & idtac] ). Undo.
  
Abort.

Goal forall B C D: Prop, (False/\ B)/\ (C/\ D).
  Split; split. Undo.
  Zuò 2 split. Undo.
  Chóngfù split. Undo.
  Jìnzhǎn chóngfù split.
  1: {
    Shībài jìnzhǎn chóngfù split.
    Chángshì jìnzhǎn chóngfù split.
    Chéngrèn.
  }

Abort.

*)

(** --------------------------------------------------- *)




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


(** PART2 : ALTERNATIVES TACTIC  *)

(** _ + _ *)  (** first [ _ ] *)  (** tryif _ 否则 _ 则 *)
目的 True .
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


(** ---------------------------------------------------- *)


(** _ + _ *)  (** first [ _ ] *)  (** tryif _ else _ then *)
Goal True .
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
