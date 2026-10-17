Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.Proofs.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.CopyDiscard.
Require Import Category.Structure.Monoidal.Relevance.
Require Import Category.Structure.Monoidal.Semicartesian.
Require Import Category.Structure.Monoidal.Heunen_Vicary.
Require Import Category.Structure.Monoidal.Heunen_Vicary.Proofs.
Require Import Category.Structure.Monoidal.Hypergraph.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.CommutativeComonoid.
Require Import Category.Theory.Algebra.Frobenius.
Require Import Category.Theory.Algebra.CommutativeFrobenius.
Require Import Category.Theory.Algebra.SpecialCommutativeFrobenius.

Generalizable All Variables.

(*
    Reference: Fritz, "A synthetic approach to Markov kernels ..."
    Reference: Fox, "Coalgebras and cartesian categories",

   本文件给出相应结构的证明。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section MidSwapNatural.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma mid_swap_inv_natural {x x' y y'} (f : x ~> y) (f' : x' ~> y') :
  mid_swap_inv y y' ∘ ((f ⨂ f) ⨂ (f' ⨂ f'))
    ≈ ((f ⨂ f') ⨂ (f ⨂ f')) ∘ mid_swap_inv x x'.
Proof. exact (swap_inner_natural f f f' f'). Qed.

End MidSwapNatural.

Section Braid2Bridge.

Context {C : Category}.
Context `{R : @RelevanceMonoidal C}.

(*
   本节说明分配律相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma braid2_mid_swap_inv (x y : C) :
  @braid2 C R x x y y ≈ mid_swap_inv x y.
Proof.
  unfold braid2, mid_swap_inv.
  rewrite !bimap_comp_id_left.
  rewrite !comp_assoc.
  reflexivity.
Qed.

End Braid2Bridge.

Section CopyDiscardRewrites.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

(* The tensor-coherence fields of [CopyDiscard], unfolded through
   [canonical_tensor_delta] / [canonical_tensor_epsilon] into directly
   rewritable equations. *)

Corollary copy_tensor `{CD : @CopyDiscard C S} (X Y : C) :
  copy[(X ⨂ Y)%object] ≈ mid_swap_inv X Y ∘ (copy[X] ⨂ copy[Y]).
Proof.
  unfold copy.
  rewrite cd_tensor_delta.
  unfold canonical_tensor_delta.
  reflexivity.
Qed.

Corollary discard_tensor `{CD : @CopyDiscard C S} (X Y : C) :
  discard[(X ⨂ Y)%object]
    ≈ to (@unit_left C _ I) ∘ (discard[X] ⨂ discard[Y]).
Proof.
  unfold discard.
  rewrite cd_tensor_epsilon.
  unfold canonical_tensor_epsilon.
  reflexivity.
Qed.

(* 相关说明。 （已译） *)

Corollary copy_unit `{CD : @CopyDiscard C S} :
  copy[I] ≈ (@unit_left C _ I)⁻¹.
Proof. exact cd_unit_delta. Qed.

Corollary discard_unit `{CD : @CopyDiscard C S} : discard[I] ≈ id[I].
Proof. exact cd_unit_epsilon. Qed.

End CopyDiscardRewrites.

Section CDCartesian.

Context {C : Category}.
Context `{H : @CartesianMonoidal C}.

(*
   本节说明幺半结构、幺半群、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition CD_of_Cartesian :
  @CopyDiscard C (@relevance_is_symmetric C (@cartesian_is_relevance C H)) := {|
  cd_comonoid := fun X =>
    {| ccomon_comonoid :=
         {| delta   := @diagonal C _ X;
            epsilon := @eliminate C _ _ X |} |}
|}.
Next Obligation.
  (* delta_coassoc: reorient diagonal_tensor_assoc by cancelling α. *)
  rewrite <- comp_assoc.
  rewrite diagonal_tensor_assoc.
  rewrite !comp_assoc.
  rewrite iso_from_to, id_left.
  reflexivity.
Qed.
Next Obligation.
  (* delta_counit_left: (ε ⨂ id) ∘ ∆ ≈ λ⁻¹ is Fox's proj_right_diagonal. *)
  apply eliminate_left_diagonal.
Qed.
Next Obligation.
  (* delta_counit_right: (id ⨂ ε) ∘ ∆ ≈ ρ⁻¹ is Fox's proj_left_diagonal. *)
  apply eliminate_right_diagonal.
Qed.
Next Obligation.
  (* cocommutativity: braid ∘ ∆ ≈ ∆. *)
  apply braid_diagonal.
Qed.
Next Obligation.
  (*
   本节说明 Proofs 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  unfold ccomon_delta, canonical_tensor_delta; simpl.
  rewrite diagonal_braid2.
  comp_right.
  unfold mid_swap_inv.
  rewrite !bimap_comp_id_left.
  rewrite !comp_assoc.
  reflexivity.
Qed.
Next Obligation.
  (* cd_tensor_epsilon: both sides maps 进入 terminal unit. （已译） *)
  apply unit_terminal.
Qed.
Next Obligation.
  (* cd_unit_delta: ∆ at I is the canonical iso I ≅ I ⨂ I. *)
  apply diagonal_unit.
Qed.
Next Obligation.
  (* cd_unit_epsilon: both sides maps 进入 terminal unit. （已译） *)
  apply unit_terminal.
Qed.

End CDCartesian.

Section CDHypergraph.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.
Context `{H : @Hypergraph C S}.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition CD_of_Hypergraph : @CopyDiscard C S := {|
  cd_comonoid := fun X =>
    {| ccomon_comonoid :=
         @frob_comonoid C _ X
           (@cfrob_frobenius C S X (@scfa_commutative C S X (scfa X)));
       delta_cocommutative_of_ccomon :=
         @delta_cocommutative C S X (@scfa_commutative C S X (scfa X)) |}
|}.
Next Obligation.
  (* cd_tensor_delta ≈ scfa_tensor_delta, up to unfolding projections. *)
  apply scfa_tensor_delta.
Qed.
Next Obligation.
  apply scfa_tensor_epsilon.
Qed.
Next Obligation.
  apply scfa_unit_delta.
Qed.
Next Obligation.
  apply scfa_unit_epsilon.
Qed.

End CDHypergraph.
