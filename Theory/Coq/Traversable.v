Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Applicative.

Generalizable All Variables.

(** The Traversable type class (sequence/traverse), with its categorical reading *)

(*
 nLab: https://ncatlab.org/nlab/show/distributive+law
   nLab: https://ncatlab.org/nlab/show/applicative+functor

   本文件给出 Traversable 相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class Traversable@{d c} {T : Type@{d} → Type@{c}} :=
  (* the distributive law T ◯ F ⟹ F ◯ T for any applicative F (Haskell's [sequenceA]) *)
  sequence : ∀ `{Applicative@{d c} F} {x : Type@{d}}, T (F x) → F (T x).

Arguments Traversable : clear implicits.

(*
   本节说明相关定义、性质与动机。 [Tupersable] is project-specific specialization [Traversable] a. pairing (writer-style) shape [x * -]: it sequences [T] past tuple 函子 without requiring carrier [x] be [Applicative], simply threading seed value [a : x] through.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class Tupersable@{d c} {x : Type@{d}} {T : Type@{d} → Type@{c}} := {
  (* sequence T past the writer-shaped tuple functor, seeded by [a : x] *)
  sequenceT {y : Type@{d}} (a : x) : T (x * y)%type → x * T y
}.

Arguments Tupersable : clear implicits.
