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

(* [Tupersable] is a project-specific specialization of [Traversable] to a
   pairing (writer-style) shape [x * -]: it sequences [T] past the tuple
   functor without requiring the carrier [x] to be [Applicative], by simply
   threading the seed value [a : x] through.  There is no standard name for
   this class; it is the traversal whose "applicative" is the (non-applicative)
   writer-shaped functor [λ y, x * y].  Like the other classes here it is
   lawless, recording only the [sequenceT] operation. *)

Class Tupersable@{d c} {x : Type@{d}} {T : Type@{d} → Type@{c}} := {
  (* sequence T past the writer-shaped tuple functor, seeded by [a : x] *)
  sequenceT {y : Type@{d}} (a : x) : T (x * y)%type → x * T y
}.

Arguments Tupersable : clear implicits.
