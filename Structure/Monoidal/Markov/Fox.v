Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Relevance.
Require Import Category.Structure.Monoidal.Semicartesian.
Require Import Category.Structure.Monoidal.Heunen_Vicary.
Require Import Category.Structure.Monoidal.Braided.Proofs.
Require Import Category.Structure.Monoidal.Hypergraph.
Require Import Category.Structure.Monoidal.CopyDiscard.
Require Import Category.Structure.Monoidal.CopyDiscard.Proofs.
Require Import Category.Structure.Monoidal.CopyDiscard.Deterministic.
Require Import Category.Structure.Monoidal.Markov.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.CommutativeComonoid.

Generalizable All Variables.

(*
    nLab:      https://ncatlab.org/nlab/show/Markov+category
    Reference: Fox, "Coalgebras and cartesian categories",
    Reference: Heunen & Vicary, "Categories for Quantum Theory",
    Reference: Fritz, "A synthetic approach to Markov kernels ..."

   本文件给出幺半相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Fox.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Section AllDeterministicCartesian.

Context `{M : @MarkovCategory C S}.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma markov_deterministic_of_copy {x y : C} (f : x ~> y) :
  copy[y] ∘ f ≈ (f ⨂ f) ∘ copy[x] → deterministic f.
Proof.
  intro Hcopy.
  split.
  - exact Hcopy.
  - apply (@unit_terminal C _ markov_semicartesian).
Qed.

Corollary markov_deterministic_iff_copy {x y : C} (f : x ~> y) :
  deterministic f ↔ (copy[y] ∘ f ≈ (f ⨂ f) ∘ copy[x]).
Proof.
  split.
  - exact (copy_natural_on_deterministic f).
  - exact (markov_deterministic_of_copy f).
Qed.

(** ** All morphisms deterministic ⇒ cartesian monoidal *)

Context (D : ∀ x y (f : x ~> y), deterministic f).

(* The copy supply becomes a natural diagonal: naturality is the
   determinism hypothesis, and the remaining coherence fields are the
   comonoid laws of the supply re-oriented. *)
Program Definition Relevance_of_deterministic : @RelevanceMonoidal C := {|
  relevance_is_symmetric := S;
  diagonal := fun x => copy[x]
|}.
Next Obligation.
  (* diagonal_natural: exactly the δ-square of the determinism
     hypothesis, read right-to-left. *)
  symmetry.
  apply (copy_natural_on_deterministic _ (D _ _ _)).
Qed.
Next Obligation.
  (* diagonal_unit: the unit-coherence field of the supply. *)
  apply copy_unit.
Qed.
Next Obligation.
  (* diagonal_tensor_assoc: coassociativity of the comonoid on x,
     solved for the forward associator. *)
  unfold copy, ccomon_delta.
  rewrite <- comp_assoc.
  rewrite delta_coassoc.
  rewrite !comp_assoc.
  rewrite iso_to_from.
  rewrite id_left.
  reflexivity.
Qed.
Next Obligation.
  (* braid_diagonal: cocommutativity of the supply. *)
  unfold copy, ccomon_delta.
  apply delta_cocommutative_of_ccomon.
Qed.
Next Obligation.
  (* diagonal_braid2: the tensor-coherence field, with [braid2]
     recognized as [mid_swap_inv] (cf. braid2_mid_swap_inv). *)
  rewrite copy_tensor.
  comp_right.
  unfold mid_swap_inv.
  rewrite !bimap_comp_id_left.
  rewrite !comp_assoc.
  reflexivity.
Qed.

Program Definition all_deterministic_cartesian : @CartesianMonoidal C := {|
  cartesian_is_relevance     := Relevance_of_deterministic;
  cartesian_is_semicartesian := markov_semicartesian
|}.
Next Obligation.
  (* proj_left_diagonal: the right counit law across terminality. *)
  apply proj_left_copy.
Qed.
Next Obligation.
  (* proj_right_diagonal: the left counit law across terminality. *)
  apply proj_right_copy.
Qed.
Next Obligation.
  (* unit_left_braid: Joyal–Street ρ ≈ λ ∘ β (Braided/Proofs.v). *)
  apply braid_unit_left.
Qed.
Next Obligation.
  (* unit_right_braid: the mirror coherence λ ≈ ρ ∘ β. *)
  apply braid_unit_right.
Qed.

(*
   本节说明笛卡尔、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Corollary all_deterministic_cartesian_copy {x : C} :
  @copy C S (@CD_of_Cartesian C all_deterministic_cartesian) x ≈ copy[x].
Proof. reflexivity. Qed.

Corollary all_deterministic_cartesian_discard {x : C} :
  @discard C S (@CD_of_Cartesian C all_deterministic_cartesian) x
    ≈ discard[x].
Proof. apply (@unit_terminal C _ markov_semicartesian). Qed.

End AllDeterministicCartesian.

(** ** Cartesian monoidal ⇒ all morphisms deterministic *)

Section CartesianDeterministic.

Context `{H : @CartesianMonoidal C}.

(*
   本节说明幺半结构、幺半群、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem cartesian_all_deterministic :
  ∀ x y (f : x ~> y), @deterministic C _ (@CD_of_Cartesian C H) x y f.
Proof.
  intros x y f.
  split.
  - symmetry; apply diagonal_natural.
  - apply unit_terminal.
Qed.

End CartesianDeterministic.

End Fox.

(*
   本节说明幺半结构、幺半群、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section FoxPackaging.

Context {C : Category}.

Corollary markov_all_deterministic_iff_cartesian :
  (∃ (S : @SymmetricMonoidal C) (M : @MarkovCategory C S),
     ∀ x y (f : x ~> y), @deterministic C S (@markov_is_cd C S M) x y f)
    ↔ @CartesianMonoidal C.
Proof.
  split.
  - intros [S' [M' D]].
    exact (@all_deterministic_cartesian C S' M' D).
  - intro H.
    exists (@relevance_is_symmetric C (@cartesian_is_relevance C H)).
    exists (@Markov_of_Cartesian C H).
    intros x y f.
    exact (@cartesian_all_deterministic C H x y f).
Qed.

End FoxPackaging.
