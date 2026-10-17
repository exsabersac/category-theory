Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Theory.Algebra.Comonoid.

Generalizable All Variables.

(** * Commutative comonoids in a symmetric monoidal category *)

(*
 nLab:      https://ncatlab.org/nlab/show/comonoid
 nLab:      https://ncatlab.org/nlab/show/braided+monoidal+category
 Wikipedia: https://en.wikipedia.org/wiki/Monoid_(category_theory)

   本文件给出交换余幺半群对象。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CommutativeComonoid.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Class CommutativeComonoid (X : C) : Type := {
  (* underlying comonoid object, taken in the monoidal category
     underlying the symmetric structure [S] *)
  ccomon_comonoid : @Comonoid C
                      (@braided_is_monoidal C
                         (@symmetric_is_braided C S))
                      X;

  (* comultiplication is invariant under the braiding: [braid ∘ delta ≈ delta] *)
  delta_cocommutative_of_ccomon :
    braid ∘ (@delta _ _ _ ccomon_comonoid)
      ≈ (@delta _ _ _ ccomon_comonoid)
}.

#[export] Existing Instance ccomon_comonoid.

Coercion ccomon_comonoid : CommutativeComonoid >-> Comonoid.

End CommutativeComonoid.

Arguments ccomon_comonoid {C S X _}.
Arguments delta_cocommutative_of_ccomon {C S X _}.

(** Convenience flat-projection aliases mirroring [scfa_delta] /
    [scfa_epsilon] from [SpecialCommutativeFrobenius.v]: project a
    [CommutativeComonoid X] to its underlying [delta] / [epsilon]. *)

Section CommutativeComonoidProjections.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Definition ccomon_delta {X : C} (M : CommutativeComonoid X)
  : X ~> (X ⨂ X)%object :=
  @delta _ _ _ (ccomon_comonoid (X := X)).

Definition ccomon_epsilon {X : C} (M : CommutativeComonoid X)
  : X ~> @I _ _ :=
  @epsilon _ _ _ (ccomon_comonoid (X := X)).

End CommutativeComonoidProjections.

Arguments ccomon_delta   {C S X} M.
Arguments ccomon_epsilon {C S X} M.
