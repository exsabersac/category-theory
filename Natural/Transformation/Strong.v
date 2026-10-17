Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Monoidal.
Require Import Category.Functor.Strong.

Generalizable All Variables.

(** Strong natural transformations (compatible with tensorial strength) *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Strong_monad

   本文件给出（余）强度/强（余）单子相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class Strong_Transform {C : Category} `{@Monoidal C}
      {F : C ⟶ C} `{@StrongFunctor _ _ F}
      {G : C ⟶ C} `{@StrongFunctor _ _ G} (N : F ⟹ G) := {
  strength_transform {x y} :                         (* strength-compatibility square *)
    strength[G] ∘ id[x] ⨂ transform[N] y ≈ transform[N] _ ∘ strength[F]
}.
