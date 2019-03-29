Require ssreflect .
Declare ML Module "jisuanji_plugin" .

(** Dānwèi *)
Notation 单位 := (unit) .
(** Dā *)
Notation 单 := (tt) .

(** Bù jiǎnhuà *)
Notation 不简化 t := (let: tt := tt in t) .