Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Applicative.

Generalizable All Variables.

(** The Traversable 类型类 (sequence/traverse), categorical reading （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/distributive+law
   nLab: https://ncatlab.org/nlab/show/applicative+functor

   本文件给出 Traversable 相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class Traversable@{d c} {T : Type@{d} → Type@{c}} :=
  (* 分配律 T ◯ F ⟹ F ◯ T any applicative F (Haskell's [sequenceA]) （已译） *)
  sequence : ∀ `{Applicative@{d c} F} {x : Type@{d}}, T (F x) → F (T x).

Arguments Traversable : clear implicits.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class Tupersable@{d c} {x : Type@{d}} {T : Type@{d} → Type@{c}} := {
  (* sequence T past the writer-shaped tuple functor, seeded by [a : x] *)
  sequenceT {y : Type@{d}} (a : x) : T (x * y)%type → x * T y
}.

Arguments Tupersable : clear implicits.
