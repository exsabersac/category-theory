Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Semicartesian.
Require Import Category.Structure.Monoidal.CopyDiscard.
Require Import Category.Structure.Monoidal.CopyDiscard.Proofs.
Require Import Category.Structure.Monoidal.Heunen_Vicary.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.CommutativeComonoid.

Generalizable All Variables.

(*
    nLab:      https://ncatlab.org/nlab/show/Markov+category
    Reference: Fritz, "A synthetic approach to Markov kernels, conditional
    Reference: Cho & Jacobs, "Disintegration and Bayesian inversion via

   本文件给出幺半相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   关于Markov categories的来源与用途

   nLab:  https://ncatlab.org/nlab/show/Stoch
   nLab:  https://ncatlab.org/nlab/show/Giry+monad

   本节说明Lawvere 理论、核/余核、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Markov.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Class MarkovCategory : Type := {
  (* The copy-discard structure: commutative comonoid every 对象,
 coherent tensor unit (but NOT natural). （已译） *)
  markov_is_cd : @CopyDiscard C S;

  (* The unit [I] terminal (范畴 semicartesian / affine):
 synthetically, "probability distributions normalized". （已译） *)
  markov_semicartesian :
    @SemicartesianMonoidal C
      (@braided_is_monoidal C (@symmetric_is_braided C S))
}.
#[export] Existing Instance markov_is_cd.

Coercion markov_is_cd : MarkovCategory >-> CopyDiscard.

(* 相关说明。 （已译） *)

Context `{M : MarkovCategory}.

(* Discarding IS eliminating: both are morphisms into the terminal [I].
   Some presentations of Markov categories take this identification as an
   axiom; in Fritz's redundancy-free formulation it is a corollary of
   terminality. *)
Corollary markov_discard_eliminate {x : C} :
  discard[x] ≈ @eliminate C _ markov_semicartesian x.
Proof. apply (@unit_terminal C _ markov_semicartesian). Qed.

(* Naturality of discard — "delete after doing anything is delete" — is
   likewise a corollary of terminality, never an axiom. *)
Corollary discard_natural {x y : C} (f : x ~> y) :
  discard[y] ∘ f ≈ discard[x].
Proof. apply (@unit_terminal C _ markov_semicartesian). Qed.

(*
   本节说明 Markov 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition state (x : C) : Type := I ~> x.

(* Normalization: every state has total mass one. *)
Lemma state_discard {x : C} (s : state x) :
  discard[x] ∘ s ≈ id[I].
Proof. apply (@unit_terminal C _ markov_semicartesian). Qed.

Definition marginal_left {x y : C} (s : state (x ⨂ y)%object) : state x :=
  @proj_left C _ markov_semicartesian x y ∘ s.

Definition marginal_right {x y : C} (s : state (x ⨂ y)%object) : state y :=
  @proj_right C _ markov_semicartesian x y ∘ s.

#[export] Program Instance marginal_left_respects {x y : C} :
  Proper (equiv ==> equiv) (@marginal_left x y).
Next Obligation.
  proper.
  unfold marginal_left.
  rewrites.
  reflexivity.
Qed.

#[export] Program Instance marginal_right_respects {x y : C} :
  Proper (equiv ==> equiv) (@marginal_right x y).
Next Obligation.
  proper.
  unfold marginal_right.
  rewrites.
  reflexivity.
Qed.

(* Copying then discarding one two copies 恒等: the
 comonoid counit laws, [eliminate] traded [discard] by
 terminality [I]. （已译） *)

Lemma proj_left_copy {x : C} :
  @proj_left C _ markov_semicartesian x x ∘ copy[x] ≈ id[x].
Proof.
  unfold proj_left.
  rewrite <- markov_discard_eliminate.
  rewrite <- comp_assoc.
  unfold copy, discard, ccomon_delta, ccomon_epsilon.
  rewrite delta_counit_right.
  apply iso_to_from.
Qed.

Lemma proj_right_copy {x : C} :
  @proj_right C _ markov_semicartesian x x ∘ copy[x] ≈ id[x].
Proof.
  unfold proj_right.
  rewrite <- markov_discard_eliminate.
  rewrite <- comp_assoc.
  unfold copy, discard, ccomon_delta, ccomon_epsilon.
  rewrite delta_counit_left.
  apply iso_to_from.
Qed.

(* Both marginals of a copied state recover the state: copying is a
   (synthetic) diagonal coupling. *)

Lemma marginal_left_copy {x : C} (s : state x) :
  marginal_left (copy[x] ∘ s) ≈ s.
Proof.
  unfold marginal_left.
  rewrite comp_assoc.
  rewrite proj_left_copy.
  apply id_left.
Qed.

Lemma marginal_right_copy {x : C} (s : state x) :
  marginal_right (copy[x] ∘ s) ≈ s.
Proof.
  unfold marginal_right.
  rewrite comp_assoc.
  rewrite proj_right_copy.
  apply id_left.
Qed.

End Markov.

Arguments MarkovCategory C {S}.

Section MarkovCartesian.

Context {C : Category}.
Context `{H : @CartesianMonoidal C}.

(*
   本节说明幺半结构、幺半群、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Markov_of_Cartesian :
  @MarkovCategory C
    (@relevance_is_symmetric C (@cartesian_is_relevance C H)) := {|
  markov_is_cd := @CD_of_Cartesian C H;
  markov_semicartesian := @cartesian_is_semicartesian C H
|}.

End MarkovCartesian.
