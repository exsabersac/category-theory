Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.Frobenius.
Require Import Category.Theory.Algebra.CommutativeFrobenius.
Require Import Category.Theory.Algebra.SpecialCommutativeFrobenius.
Require Import Category.Structure.Monoidal.Hypergraph.

Generalizable All Variables.

(** * Compact closed categories *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Compact_closed_category

   本文件给出幺半相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab:  https://ncatlab.org/nlab/show/compact+closed+category
   Paper: Kelly, "Many-variable functorial calculus. I.", in Coherence
   Paper: Kelly, Laplaza, "Coherence for compact closed categories",
   Paper: Abramsky, Coecke, "A categorical semantics of quantum

   本节说明幺半结构、伴随、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CompactClosed.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Class CompactClosed : Type := {
  (* The chosen dual object [X^*] of each object [X]. *)
  dual : C -> C;

  (* Unit / coevaluation ("cup")    η_X : I ~> X^* ⨂ X. *)
  cc_unit   : forall X : C, I ~> dual X ⨂ X;
  (* Counit / evaluation ("cap")    ε_X : X ⨂ X^* ~> I. *)
  cc_counit : forall X : C, X ⨂ dual X ~> I;

  (* Left snake / zigzag, "yanking" the X-strand straight:
       λ ∘ (ε ⨂ id) ∘ α⁻¹ ∘ (id ⨂ η) ∘ ρ⁻¹ ≈ id[X]. *)
  snake_left : forall X : C,
    to (@unit_left C _ X)
      ∘ bimap (cc_counit X) id[X]
      ∘ from (@tensor_assoc C _ X (dual X) X)
      ∘ bimap id[X] (cc_unit X)
      ∘ from (@unit_right C _ X)
    ≈ id[X];

  (* Right snake / zigzag, "yanking" the X^*-strand straight:
       ρ ∘ (id ⨂ ε) ∘ α ∘ (η ⨂ id) ∘ λ⁻¹ ≈ id[X^*]. *)
  snake_right : forall X : C,
    to (@unit_right C _ (dual X))
      ∘ bimap id[dual X] (cc_counit X)
      ∘ to (@tensor_assoc C _ (dual X) X (dual X))
      ∘ bimap (cc_unit X) id[dual X]
      ∘ from (@unit_left C _ (dual X))
    ≈ id[dual X]
}.

End CompactClosed.

Arguments CompactClosed C {S}.
Arguments dual {C S _} X.
Arguments cc_unit {C S _} X.
Arguments cc_counit {C S _} X.

(* * * Every hypergraph 范畴 compact closed (self-dual) （已译） *)

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section HypergraphIsCompactClosed.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

(* Self-dual unit, given an SCFA on [X]. *)
Definition hcc_unit (X : C) `{F : @SpecialCommutativeFrobenius C S X}
  : I ~> X ⨂ X := scfa_delta F ∘ scfa_eta F.

(* Self-dual counit, given an SCFA on [X]. *)
Definition hcc_counit (X : C) `{F : @SpecialCommutativeFrobenius C S X}
  : X ⨂ X ~> I := scfa_epsilon F ∘ scfa_mu F.

End HypergraphIsCompactClosed.

(* 相关说明。 （已译） *)

(*
   本节说明幺半群、分配律相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section HypergraphToCompactClosed.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.
Context `{H : @Hypergraph C S}.

(* 相关说明。 （已译） *)
Lemma cc_unit_unfold (X : C) :
  hcc_unit X (F := scfa X) = scfa_delta (scfa X) ∘ scfa_eta (scfa X).
Proof. reflexivity. Qed.

Lemma cc_counit_unfold (X : C) :
  hcc_counit X (F := scfa X) = scfa_epsilon (scfa X) ∘ scfa_mu (scfa X).
Proof. reflexivity. Qed.

(* 相关说明。 （已译） *)
Lemma hypergraph_snake_left (X : C) :
  to (@unit_left C _ X)
    ∘ bimap (hcc_counit X (F := scfa X)) id[X]
    ∘ from (@tensor_assoc C _ X X X)
    ∘ bimap id[X] (hcc_unit X (F := scfa X))
    ∘ from (@unit_right C _ X)
  ≈ id[X].
Proof.
  unfold hcc_unit, hcc_counit.
  (* Distribute bimap over the SCFA composites. *)
  rewrite (bimap_comp_id_right (scfa_epsilon _) (scfa_mu _)).
  rewrite (bimap_comp_id_left (scfa_delta _) (scfa_eta _)).
  (* Bring frob_law_left into focus: bimap μ id ∘ α⁻¹ ∘ bimap id δ ≈ δ ∘ μ. *)
  (* Currently: unit_left ∘ (bimap ε id ∘ bimap μ id) ∘ α⁻¹
                 ∘ (bimap id δ ∘ bimap id η) ∘ unit_right⁻¹. *)
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (bimap (scfa_mu _) id)).
  rewrite (comp_assoc (bimap (scfa_mu _) id ∘ from tensor_assoc)).
  unfold scfa_mu, scfa_delta, scfa_epsilon, scfa_eta.
  rewrite (frob_law_left (Frobenius := scfa X)).
  (* Now: unit_left ∘ bimap ε id ∘ (δ ∘ μ) ∘ bimap id η ∘ unit_right⁻¹. *)
  rewrite <- !comp_assoc.
  rewrite (comp_assoc mu (bimap id eta)).
  rewrite (mu_unit_right (Monoid := scfa X)).
  rewrite iso_to_from, id_right.
  (* Now: unit_left ∘ (bimap ε id ∘ δ) ≈ id. *)
  rewrite (delta_counit_left (Comonoid := scfa X)).
  rewrite iso_to_from.
  reflexivity.
Qed.

(* The snake-right calculation, symmetric to [snake_left] under [paws]. *)
Lemma hypergraph_snake_right (X : C) :
  to (@unit_right C _ X)
    ∘ bimap id[X] (hcc_counit X (F := scfa X))
    ∘ to (@tensor_assoc C _ X X X)
    ∘ bimap (hcc_unit X (F := scfa X)) id[X]
    ∘ from (@unit_left C _ X)
  ≈ id[X].
Proof.
  unfold hcc_unit, hcc_counit.
  rewrite (bimap_comp_id_left  (scfa_epsilon _) (scfa_mu _)).
  rewrite (bimap_comp_id_right (scfa_delta _) (scfa_eta _)).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (bimap id (scfa_mu _))).
  rewrite (comp_assoc (bimap id (scfa_mu _) ∘ to tensor_assoc)).
  unfold scfa_mu, scfa_delta, scfa_epsilon, scfa_eta.
  rewrite (frob_law_right (Frobenius := scfa X)).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc mu (bimap eta id)).
  rewrite (mu_unit_left (Monoid := scfa X)).
  rewrite iso_to_from, id_right.
  rewrite (delta_counit_right (Comonoid := scfa X)).
  rewrite iso_to_from.
  reflexivity.
Qed.

(*
   本节说明 CompactClosed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Instance Hypergraph_CompactClosed : @CompactClosed C S := {|
  dual      := fun X => X;
  cc_unit   := fun X => hcc_unit X (F := scfa X);
  cc_counit := fun X => hcc_counit X (F := scfa X);

  snake_left  := hypergraph_snake_left;
  snake_right := hypergraph_snake_right
|}.

End HypergraphToCompactClosed.
