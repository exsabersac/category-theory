Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(** * Wedges, ends and coends *)

(*
   nLab:      https://ncatlab.org/nlab/show/end#wedges
   Wikipedia: https://en.wikipedia.org/wiki/End_(category_theory)

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class Wedge `(F : C^op ∏ C ⟶ D) := {
  wedge_obj : D;                          (* the apex `w` of the wedge *)

  wedge_map {x : C} : wedge_obj ~{D}~> F (x, x);   (* leg `w ~> F (x, x)` *)

  (* wedge condition for `f : x ~> y`, both sides `w ~> F (x, y)`:
     `bimap[F] id f ∘ wedge_map[x] ≈ bimap[F] (op f) id ∘ wedge_map[y]` *)
  ump_wedges {x y : C} (f : x ~{C}~> y) :
    bimap[F] id f ∘ wedge_map ≈ bimap[F] (op f) id ∘ wedge_map
}.

Coercion Wedge_to_obj `(F : C^op ∏ C ⟶ D) (W : Wedge F) : D :=
  @wedge_obj _ _ _ W.

Notation "wedge_map[ C ]" := (@wedge_map _ _ _ C _)
  (at level 9, format "wedge_map[ C ]") : category_scope.

(*
   本节说明（余）端、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Cowedge `(F : C^op ∏ C ⟶ D) := @Wedge (C^op) (D^op) (F^op).
