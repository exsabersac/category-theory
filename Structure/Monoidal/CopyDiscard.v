Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Hypergraph.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.CommutativeComonoid.

Generalizable All Variables.

(*
    nLab:      https://ncatlab.org/nlab/show/copy-discard+category
    Reference: Cho & Jacobs, "Disintegration and Bayesian inversion via
    Reference: Fritz, "A synthetic approach to Markov kernels, conditional
    Reference: Corradini & Gadducci, "An algebraic presentation of term

   本文件给出幺半相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CopyDiscard.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Class CopyDiscard : Type := {
  cd_comonoid (X : C) : CommutativeComonoid X;

  (* Tensor coherence: the comonoid on [X ⨂ Y] agrees with the canonical
     one assembled from those on [X] and [Y] through [mid_swap_inv]
     (Hypergraph.v):  δ_{X⨂Y} ≈ mid_swap_inv ∘ (δ_X ⨂ δ_Y). *)
  cd_tensor_delta (X Y : C) :
    ccomon_delta (cd_comonoid (X ⨂ Y))
      ≈ canonical_tensor_delta (cd_comonoid X) (cd_comonoid Y);

  (* ε_{X⨂Y} ≈ unit_left ∘ (ε_X ⨂ ε_Y). *)
  cd_tensor_epsilon (X Y : C) :
    ccomon_epsilon (cd_comonoid (X ⨂ Y))
      ≈ canonical_tensor_epsilon (cd_comonoid X) (cd_comonoid Y);

  (* Unit coherence: the comonoid on [I] is the trivial one,
     δ_I ≈ unit_left⁻¹ and ε_I ≈ id (cf. scfa_unit_delta/epsilon). *)
  cd_unit_delta   : ccomon_delta   (cd_comonoid I) ≈ from (@unit_left C _ I);
  cd_unit_epsilon : ccomon_epsilon (cd_comonoid I) ≈ id[I]
}.

(* [cd_comonoid] is deliberately NOT an [Existing Instance] (mirroring
   [scfa] in Hypergraph.v): typeclass resolution must never invent a
   comonoid structure on an object; access it via the projections below. *)

Definition copy `{CopyDiscard} (X : C) : X ~> (X ⨂ X)%object :=
  ccomon_delta (cd_comonoid X).

Definition discard `{CopyDiscard} (X : C) : X ~> I :=
  ccomon_epsilon (cd_comonoid X).

End CopyDiscard.

Arguments cd_comonoid {C S _} X.
Arguments copy {C S _} X.
Arguments discard {C S _} X.
Arguments CopyDiscard C {S}.

Notation "copy[ X ]" := (copy X)
  (at level 9, format "copy[ X ]") : morphism_scope.
Notation "discard[ X ]" := (discard X)
  (at level 9, format "discard[ X ]") : morphism_scope.
