Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Theory.Algebra.Monoid.

Generalizable All Variables.

(* * * Commutative monoids symmetric 幺半范畴 （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/commutative+monoid
 nLab:      https://ncatlab.org/nlab/show/braided+monoidal+category
 Wikipedia: https://en.wikipedia.org/wiki/Monoid_(category_theory)

   本文件给出交换幺半群对象。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CommutativeMonoid.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Class CommutativeMonoid (X : C) : Type := {
  (* underlying 幺半群 对象, taken 幺半范畴
 underlying symmetric structure [S] （已译） *)
  cmon_monoid : @Monoid C
                  (@braided_is_monoidal C
                     (@symmetric_is_braided C S))
                  X;

  (* multiplication is invariant under the braiding: [mu ∘ braid ≈ mu] *)
  mu_commutative_of_cmon :
    (@mu _ _ _ cmon_monoid) ∘ braid
      ≈ (@mu _ _ _ cmon_monoid)
}.

#[export] Existing Instance cmon_monoid.

Coercion cmon_monoid : CommutativeMonoid >-> Monoid.

End CommutativeMonoid.

Arguments cmon_monoid {C S X _}.
Arguments mu_commutative_of_cmon {C S X _}.

(** Convenience aliases mirroring [scfa_mu] / [scfa_eta] from
    [SpecialCommutativeFrobenius.v]: project a [CommutativeMonoid X] to
    its underlying [mu] / [eta]. *)

Section CommutativeMonoidProjections.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Definition cmon_mu {X : C} (M : CommutativeMonoid X)
  : X ⨂ X ~> X :=
  @mu _ _ _ (cmon_monoid (X := X)).

Definition cmon_eta {X : C} (M : CommutativeMonoid X)
  : I ~> X :=
  @eta _ _ _ (cmon_monoid (X := X)).

End CommutativeMonoidProjections.

Arguments cmon_mu  {C S X} M.
Arguments cmon_eta {C S X} M.
