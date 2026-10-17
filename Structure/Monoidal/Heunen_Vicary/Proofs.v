Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Structure.Monoidal.Heunen_Vicary.

Generalizable All Variables.

(*
   nLab:      https://ncatlab.org/nlab/show/cartesian+monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Cartesian_monoidal_category

   本文件给出相应结构的证明。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CartesianMonoidal.

Context `{@CartesianMonoidal C}.

(*
   本节说明 Proofs 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary unit_left_eliminate {x y} (f : x ~> y) :
  unit_left ∘ eliminate ⨂ f ∘ ∆x ≈ f.
Proof.
  symmetry.
  rewrite <- id_left at 1.
  rewrite <- proj_right_diagonal.
  unfold proj_right.
  rewrite <- !comp_assoc.
  pose proof diagonal_natural as X0; simpl in X0.
  rewrite <- X0; clear X0.
  normal.
  rewrite eliminate_comp.
  reflexivity.
Qed.

(*
   本节说明 Proofs 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary unit_right_eliminate {x y} (f : x ~> y) :
  unit_right ∘ f ⨂ eliminate ∘ ∆x ≈ f.
Proof.
  symmetry.
  rewrite <- id_left at 1.
  rewrite <- proj_left_diagonal.
  unfold proj_left.
  rewrite <- !comp_assoc.
  pose proof diagonal_natural; simpl in X.
  rewrite <- X; clear X.
  normal.
  rewrite eliminate_comp.
  reflexivity.
Qed.

(* Copy x then delete right factor: 这是 pairing ⟨id, e⟩, is
 exactly inverse right unitor r⁻¹ product presentation. （已译） *)
Lemma eliminate_right_diagonal {x} :
  id[x] ⨂ eliminate ∘ ∆x ≈ unit_right⁻¹.
Proof.
  apply (iso_to_monic unit_right).
  rewrite comp_assoc.
  rewrite unit_right_eliminate.
  rewrite iso_to_from.
  reflexivity.
Qed.

(* 相关说明。 （已译） *)
Lemma eliminate_left_diagonal {x} :
  eliminate ⨂ id[x] ∘ ∆x ≈ unit_left⁻¹.
Proof.
  apply (iso_to_monic unit_left).
  rewrite comp_assoc.
  rewrite unit_left_eliminate.
  rewrite iso_to_from.
  reflexivity.
Qed.

(*
   本节说明 Proofs 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma proj_left_id_diagonal {x y} :
  proj_left ⨂ id ∘ ∆(x ⨂ y) ≈ tensor_assoc ∘ ∆x ⨂ id.
Proof.
  rewrite diagonal_braid2.
  remember (_ ∘ _ ∘ tensor_assoc) as p.
  spose (@braid2_natural _ _ x _ id x _ id y _ eliminate y _ id) as X0.
  rewrite !bimap_id_id in X0.
  rewrite !id_left, !id_right in X0.
  unfold proj_left.
  normal.
  rewrite bimap_comp_id_right.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc ((_ ⨂ _) ⨂ _)).
  unfold braid2 in X0.
  rewrite Heqp; clear Heqp p.
  rewrite X0; clear X0.
  normal.
  rewrite eliminate_left_diagonal.
  rewrite triangle_identity.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc tensor_assoc).
  rewrite iso_to_from.
  normal.
  rewrite <- triangle_identity_left.
  normal.
  rewrite unit_left_braid.
  rewrite triangle_identity.
  rewrite <- !comp_assoc.
  rewrite iso_to_from.
  normal.
  rewrite to_tensor_assoc_natural.
  normal.
  rewrite iso_to_from.
  reflexivity.
Qed.

(*
   本节说明 Proofs 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma proj_right_id_diagonal {x y} :
  proj_right ⨂ id ∘ ∆(x ⨂ y)
    ≈ tensor_assoc ∘ braid ⨂ id ∘ tensor_assoc⁻¹ ∘ id[x] ⨂ ∆y.
Proof.
  rewrite diagonal_braid2.
  remember (_ ∘ _ ∘ tensor_assoc) as p.
  spose (@braid2_natural _ _ x _ eliminate x _ id y _ id y _ id) as X0.
  rewrite !bimap_id_id in X0.
  rewrite !id_right in X0.
  unfold braid2 in X0.
  unfold proj_right.
  normal.
  rewrite bimap_comp_id_right.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc ((_ ⨂ _) ⨂ _)).
  rewrite Heqp; clear Heqp p.
  rewrite X0; clear X0.
  normal.
  rewrite eliminate_left_diagonal.
  rewrite triangle_identity_left.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc tensor_assoc).
  rewrite iso_to_from.
  normal.
  rewrite <- to_unit_left_natural.
  rewrite <- !comp_assoc.
  repeat comp_left.
  rewrite comp_assoc.
  rewrite <- triangle_identity_left.
  normal.
  rewrite iso_to_from.
  reflexivity.
Qed.

(* 相关说明。 （已译） *)
Corollary proj_right_left_diagonal {x y} :
  proj_right ⨂ proj_left ∘ ∆(x ⨂ y) ≈ braid.
Proof.
  rewrite <- bimap_id_left_right.
  rewrite <- comp_assoc.
  rewrite proj_right_id_diagonal.
  unfold proj_left, proj_right.
  normal.
  rewrite bimap_comp_id_left.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ tensor_assoc).
  rewrite to_tensor_assoc_natural.
  normal.
  rewrite <- comp_assoc.
  rewrite triangle_identity_right.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (tensor_assoc⁻¹)).
  rewrite iso_from_to.
  normal.
  rewrite <- bimap_id_right_left.
  rewrite !comp_assoc.
  rewrite <- to_unit_right_natural.
  symmetry.
  rewrite <- id_right at 1.
  rewrite <- !comp_assoc.
  comp_left.
  symmetry.
  normal.
  spose (@from_tensor_assoc_natural _ _ x _ y _ y _ id id eliminate) as X0.
  rewrite bimap_id_id in X0.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (bimap _ _)).
  rewrites.
  normal.
  rewrite eliminate_right_diagonal.
  rewrite <- triangle_identity_right.
  normal.
  rewrite iso_to_from.
  normal; reflexivity.
Qed.

(*
   本节说明 Proofs 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary proj_left_right_diagonal {x y} :
  proj_left ⨂ proj_right ∘ ∆(x ⨂ y) ≈ id[x ⨂ y].
Proof.
  rewrite <- bimap_id_left_right.
  rewrite <- comp_assoc.
  rewrite proj_left_id_diagonal.
  rewrite comp_assoc.
  unfold proj_right.
  rewrite bimap_comp_id_left.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ tensor_assoc).
  rewrite to_tensor_assoc_natural.
  normal.
  rewrite <- comp_assoc.
  rewrite eliminate_right_diagonal.
  normal.
  rewrite <- triangle_identity.
  normal.
  rewrite iso_to_from.
  normal; reflexivity.
Qed.

#[local] Obligation Tactic := intros; simplify; simpl in *; intros; normal.

(*
   本节说明 Proofs 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Instance diagonal_monic {x} :
  Monic ∆x.
Next Obligation.
  rewrite <- unit_left_eliminate.
  rewrite <- (unit_left_eliminate g2).
  rewrite <- (@eliminate_comp _ _ _ _ _ g1) at 1.
  rewrite <- (@eliminate_comp _ _ _ _ _ g2) at 1.
  rewrite <- (id_left g1) at 2.
  rewrite <- (id_left g2) at 2.
  rewrite !bimap_comp.
  rewrite <- !comp_assoc.
  srewrite diagonal_natural.
  rewrites.
  srewrite diagonal_natural.
  reflexivity.
Qed.

(* 相关说明。 （已译） *)
Corollary proj_left_braid {x y} :
  proj_left ∘ braid ≈ @proj_right _ _ _ x y.
Proof.
  unfold proj_left, proj_right.
  rewrite <- proj_right_left_diagonal.
  normal.
  rewrite eliminate_comp.
  rewrite unit_right_eliminate.
  reflexivity.
Qed.

(* Dually, projecting right after the braiding is projecting left. *)
Corollary proj_right_braid {x y} :
  proj_right ∘ braid ≈ @proj_left _ _ _ x y.
Proof.
  unfold proj_left, proj_right.
  rewrite <- proj_right_left_diagonal.
  normal.
  rewrite eliminate_comp.
  rewrite unit_left_eliminate.
  reflexivity.
Qed.

End CartesianMonoidal.
