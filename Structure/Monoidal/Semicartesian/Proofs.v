Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Structure.Monoidal.Semicartesian.

Generalizable All Variables.

(*
   nLab:      https://ncatlab.org/nlab/show/semicartesian+monoidal+category
   Wikipedia: no dedicated article; the unit-terminal condition is noted under

   本文件给出相应结构的证明。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SemicartesianProofs.

Context `{@Monoidal C}.
Context `{@SemicartesianMonoidal C _}.

(*
   本节说明 Proofs 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma proj_left_tensor_id {x y z} :
  proj_left ⨂ id ≈ id[x] ⨂ @proj_right _ _ _ y z ∘ tensor_assoc.
Proof.
  unfold proj_left, proj_right.
  rewrite bimap_comp_id_right.
  rewrite triangle_identity.
  rewrite <- comp_assoc.
  rewrite <- to_tensor_assoc_natural.
  normal; reflexivity.
Qed.

(*
   本节说明 Proofs 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma proj_right_tensor_id {x y z} :
  id ⨂ proj_right ≈ @proj_left _ _ _ x y ⨂ id[z] ∘ tensor_assoc⁻¹.
Proof.
  unfold proj_left, proj_right.
  rewrite bimap_comp_id_left.
  rewrite inverse_triangle_identity.
  rewrite <- comp_assoc.
  rewrite <- from_tensor_assoc_natural.
  normal; reflexivity.
Qed.

(*
   本节说明 Proofs 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma proj_left_left {x y z} :
  proj_left ∘ proj_left ≈ @proj_left _ _ _ x (y ⨂ z) ∘ tensor_assoc.
Proof.
  unfold proj_left; normal.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ unit_right).
  rewrite to_unit_right_natural; normal.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite bimap_triangle_right.
  rewrite <- comp_assoc.
  rewrite <- to_tensor_assoc_natural.
  rewrite comp_assoc.
  apply compose_respects; [|reflexivity].
  normal.
  apply bimap_respects; [reflexivity|].
  apply unit_terminal.
Qed.

(*
   本节说明 Proofs 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma proj_right_right {x y z} :
  proj_right ∘ proj_right ≈ @proj_right _ _ _ (x ⨂ y) z ∘ tensor_assoc⁻¹.
Proof.
  unfold proj_right; normal.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ unit_left).
  rewrite to_unit_left_natural; normal.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite bimap_triangle_left.
  rewrite <- comp_assoc.
  rewrite <- from_tensor_assoc_natural.
  rewrite comp_assoc.
  apply compose_respects; [|reflexivity].
  normal.
  apply bimap_respects; [|reflexivity].
  apply unit_terminal.
Qed.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary proj_left_natural {x y z w} (f : x ~> y) (g : z ~> w) :
  proj_left ∘ f ⨂ g ≈ f ∘ proj_left.
Proof.
  unfold proj_left.
  rewrite comp_assoc.
  rewrite to_unit_right_natural.
  normal.
  rewrite eliminate_comp.
  reflexivity.
Qed.

(*
   本节说明 Proofs 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary proj_right_natural {x y z w} (f : x ~> y) (g : z ~> w) :
  proj_right ∘ f ⨂ g ≈ g ∘ proj_right.
Proof.
  unfold proj_right.
  rewrite comp_assoc.
  rewrite to_unit_left_natural.
  normal.
  rewrite eliminate_comp.
  reflexivity.
Qed.

End SemicartesianProofs.
