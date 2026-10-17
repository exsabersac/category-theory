Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.

(** * Monoidal natural transformations *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_natural_transformation

   本文件给出幺半相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class LaxMonoidal_Transform `{@Monoidal C}
      `{!LaxMonoidalFunctor F}
      `{!LaxMonoidalFunctor G} (N : F ⟹ G) := {
  lax_pure_transform : lax_pure[G] ≈ transform[N] _ ∘ lax_pure[F];

  lax_ap_transform {x y} :
    lax_ap[G] ∘ transform[N] x ⨂ transform[N] y ≈ transform[N] _ ∘ lax_ap[F]
}.

Notation "lax_pure_transform[ N ]" := (@lax_pure_transform _ _ _ _ _ _ N _)
  (at level 9, format "lax_pure_transform[ N ]") : morphism_scope.
