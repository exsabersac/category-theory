Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Relevance.
Require Import Category.Structure.Monoidal.Semicartesian.
Require Import Category.Structure.Monoidal.Semicartesian.Proofs.
Require Import Category.Structure.Monoidal.Heunen_Vicary.
Require Import Category.Structure.Monoidal.Heunen_Vicary.Proofs.

Generalizable All Variables.

(** The cartesian-monoidal tensor is the categorical product. *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Cartesian_monoidal_category

   本文件给出笛卡尔结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CartesianMonoidalCartesian.

Context `{@CartesianMonoidal C}.

Program Definition CartesianMonoidal_Cartesian : @Cartesian C := {|
  product_obj := fun x y => (x ⨂ y)%object;   (* x × y := x ⨂ y *)
  Cartesian.fork := @fork _ _;                 (* ⟨f, g⟩ := (f ⨂ g) ∘ ∆ *)
  exl  := fun _ _ => proj_left;                (* first projection  π₁ *)
  exr  := fun _ _ => proj_right                (* second projection π₂ *)
|}.
Next Obligation.
  (* ump_products: h ≈ ⟨f, g⟩ ↔ (exl ∘ h ≈ f) ∧ (exr ∘ h ≈ g).
     Forward: rewrite h to ⟨f, g⟩ = (f ⨂ g) ∘ ∆, slide each projection past
     the tensor by proj_*_natural, then collapse proj_* ∘ ∆ by the counit law
     proj_*_diagonal.  Backward: rebuild ⟨f, g⟩ from the two equations using
     bimap_comp, diagonal_natural, and the round-trip proj_left_right_diagonal. *)
  unfold fork.
  split; intros.
  - split.
    + rewrites.
      rewrite comp_assoc.
      rewrite proj_left_natural.
      rewrite <- comp_assoc.
      rewrite proj_left_diagonal; cat.
    + rewrites.
      rewrite comp_assoc.
      rewrite proj_right_natural.
      rewrite <- comp_assoc.
      rewrite proj_right_diagonal; cat.
  - rewrite <- (fst X), <- (snd X).
    rewrite bimap_comp.
    rewrite <- !comp_assoc.
    srewrite diagonal_natural.
    rewrite comp_assoc.
    rewrite proj_left_right_diagonal; cat.
Qed.

End CartesianMonoidalCartesian.

(* Every cartesian monoidal category is a cartesian category. *)
Coercion CartesianMonoidal_Cartesian : CartesianMonoidal >-> Cartesian.
