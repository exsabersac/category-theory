Require Import Category.Lib.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Applicative.
Require Import Category.Structure.Monoidal.Closed.
Require Import Category.Natural.Transformation.Strong.
Require Import Category.Natural.Transformation.Monoidal.

Generalizable All Variables.

(** Morphisms of applicative functors. *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Applicative_functor

   本文件给出 Applicative 相关结构及其范畴解读。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class Applicative_Transform `{@ClosedMonoidal C}
  `{@Applicative C _ F}
  `{@Applicative C _ G} (N : F ⟹ G) := {
  applicative_transform_is_strong_transformation :
    @Strong_Transform C _ F _ G _ N;
  applicative_transform_is_lax_monoidal_transformation :
    @LaxMonoidal_Transform C _ F _ G _ N
}.
#[export] Existing Instance applicative_transform_is_strong_transformation.
#[export] Existing Instance applicative_transform_is_lax_monoidal_transformation.

Coercion applicative_transform_is_strong_transformation :
  Applicative_Transform >-> Strong_Transform.
Coercion applicative_transform_is_lax_monoidal_transformation :
  Applicative_Transform >-> LaxMonoidal_Transform.
