Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.Frobenius.
Require Import Category.Theory.Algebra.CommutativeFrobenius.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/Frobenius+algebra
 nLab:      https://ncatlab.org/nlab/show/classical+structure
 Wikipedia: https://en.wikipedia.org/wiki/Frobenius_algebra *)

   本文件给出特殊交换 Frobenius 结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SpecialCommutativeFrobenius.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Class SpecialCommutativeFrobenius (X : C) : Type := {
  (* underlying commutative Frobenius algebra ([mu], [eta], [delta], [epsilon]) *)
  scfa_commutative : @CommutativeFrobenius C _ X;

  (* the special law: [mu ∘ delta ≈ id[X]] *)
  mu_delta_id :
    (@mu _ _ _ (@frob_monoid _ _ _ (@cfrob_frobenius _ _ _ scfa_commutative)))
      ∘ (@delta _ _ _ (@frob_comonoid _ _ _ (@cfrob_frobenius _ _ _ scfa_commutative)))
    ≈ id[X]
}.
#[export] Existing Instance scfa_commutative.

Coercion scfa_commutative : SpecialCommutativeFrobenius >-> CommutativeFrobenius.

End SpecialCommutativeFrobenius.

Arguments scfa_commutative {C S X _}.

(* 相关说明。 （已译） *)

Section SCFAProjections.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Definition scfa_mu {X : C} (F : SpecialCommutativeFrobenius X)
  : X ⨂ X ~> X :=
  @mu _ _ _ (@frob_monoid _ _ _ (@cfrob_frobenius _ _ _ F)).

Definition scfa_eta {X : C} (F : SpecialCommutativeFrobenius X)
  : I ~> X :=
  @eta _ _ _ (@frob_monoid _ _ _ (@cfrob_frobenius _ _ _ F)).

Definition scfa_delta {X : C} (F : SpecialCommutativeFrobenius X)
  : X ~> X ⨂ X :=
  @delta _ _ _ (@frob_comonoid _ _ _ (@cfrob_frobenius _ _ _ F)).

Definition scfa_epsilon {X : C} (F : SpecialCommutativeFrobenius X)
  : X ~> I :=
  @epsilon _ _ _ (@frob_comonoid _ _ _ (@cfrob_frobenius _ _ _ F)).

End SCFAProjections.

Arguments scfa_mu      {C S X} F.
Arguments scfa_eta     {C S X} F.
Arguments scfa_delta   {C S X} F.
Arguments scfa_epsilon {C S X} F.
