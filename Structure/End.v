Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Wedge.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(** * Ends and coends *)

(*
   nLab:      https://ncatlab.org/nlab/show/end
   Wikipedia: https://en.wikipedia.org/wiki/End_(category_theory)

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class End `(F : C^op ∏ C ⟶ D) := {
  end_wedge : Wedge F;                     (* the universal wedge `(e, ω)` *)

  (* 相关说明。 （已译） *)
  ump_ends : ∀ W : Wedge F, ∃! u : W ~> end_wedge, ∀ x : C,
    wedge_map[end_wedge] ∘ u ≈ @wedge_map _ _ _ W x
}.

Arguments End {_%_category _%_category} F%_functor.
Arguments end_wedge {_%_category _%_category} F%_functor {_}.

(* An end `F` may used directly apex 对象 `D` (and hence,
 transitively through `Wedge`'s own coercion, wedge). （已译） *)
Coercion wedge_obj `(F : C^op ∏ C ⟶ D) (E : End F) := @end_wedge _ _ _ E.

Require Import Category.Functor.Opposite.

(*
   本节说明（余）端、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Coend `(F : C^op ∏ C ⟶ D) := @End (C^op) (D^op) (F^op).
