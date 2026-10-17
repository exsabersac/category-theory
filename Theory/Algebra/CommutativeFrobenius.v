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

Generalizable All Variables.

(* * * Commutative Frobenius algebras symmetric 幺半范畴 （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/Frobenius+algebra
 nLab:      https://ncatlab.org/nlab/show/2-dimensional+TQFT
 Wikipedia: https://en.wikipedia.org/wiki/Frobenius_algebra *)

   本文件给出交换 Frobenius 结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CommutativeFrobenius.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Class CommutativeFrobenius (X : C) : Type := {
  cfrob_frobenius : @Frobenius C _ X;          (* underlying Frobenius algebra *)

  (* multiplication is invariant under the braiding: [mu ∘ braid ≈ mu] *)
  mu_commutative :
    (@mu _ _ _ (@frob_monoid _ _ _ cfrob_frobenius)) ∘ braid
      ≈ (@mu _ _ _ (@frob_monoid _ _ _ cfrob_frobenius));

  (* comultiplication is invariant under the braiding: [braid ∘ delta ≈ delta] *)
  delta_cocommutative :
    braid ∘ (@delta _ _ _ (@frob_comonoid _ _ _ cfrob_frobenius))
      ≈ (@delta _ _ _ (@frob_comonoid _ _ _ cfrob_frobenius))
}.
#[export] Existing Instance cfrob_frobenius.

Coercion cfrob_frobenius : CommutativeFrobenius >-> Frobenius.

End CommutativeFrobenius.

Arguments cfrob_frobenius {C S X _}.

(* 相关说明。 （已译） *)

Section CommutativeFrobeniusProjections.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Definition cfrob_mu {X : C} (F : CommutativeFrobenius X)
  : (X ⨂ X)%object ~> X :=
  @mu _ _ _ (@frob_monoid _ _ _ (cfrob_frobenius (X := X))).

Definition cfrob_eta {X : C} (F : CommutativeFrobenius X)
  : @I _ _ ~> X :=
  @eta _ _ _ (@frob_monoid _ _ _ (cfrob_frobenius (X := X))).

Definition cfrob_delta {X : C} (F : CommutativeFrobenius X)
  : X ~> (X ⨂ X)%object :=
  @delta _ _ _ (@frob_comonoid _ _ _ (cfrob_frobenius (X := X))).

Definition cfrob_epsilon {X : C} (F : CommutativeFrobenius X)
  : X ~> @I _ _ :=
  @epsilon _ _ _ (@frob_comonoid _ _ _ (cfrob_frobenius (X := X))).

End CommutativeFrobeniusProjections.

Arguments cfrob_mu      {C S X} F.
Arguments cfrob_eta     {C S X} F.
Arguments cfrob_delta   {C S X} F.
Arguments cfrob_epsilon {C S X} F.
