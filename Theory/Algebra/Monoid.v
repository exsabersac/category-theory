Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.

(** * Internal monoids in a monoidal category *)

(*
 nLab: https://ncatlab.org/nlab/show/monoid+in+a+monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Monoid_(category_theory)

   本文件给出幺半范畴中的幺半群对象：乘法 μ、单位 η，以及结合律与左右单位律（插入结合子/单位子使态射可复合）。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Monoid.

Context {C : Category}.
Context `{M : @Monoidal C}.

Class Monoid (X : C) : Type := {
  mu  : X ⨂ X ~> X;             (* multiplication μ : X ⨂ X ~> X *)
  eta : I ~> X;                 (* unit           η : I     ~> X *)

  (* associativity: mu ∘ (mu ⨂ id) ≈ mu ∘ (id ⨂ mu) ∘ α *)
  mu_assoc :
    mu ∘ bimap mu id[X]
      ≈ mu ∘ bimap id[X] mu ∘ to tensor_assoc;

  (* left unit: mu ∘ (eta ⨂ id) ≈ λ (left unitor) *)
  mu_unit_left :
    mu ∘ bimap eta id[X]
      ≈ to (@unit_left C M X);

  (* right unit: mu ∘ (id ⨂ eta) ≈ ρ (right unitor) *)
  mu_unit_right :
    mu ∘ bimap id[X] eta
      ≈ to (@unit_right C M X)
}.

End Monoid.

Arguments mu  {C M X _}.
Arguments eta {C M X _}.

Notation "'mu[' Mon ]"  := (@mu _ _ _ Mon)
  (at level 9, format "'mu[' Mon ]") : morphism_scope.
Notation "'eta[' Mon ]" := (@eta _ _ _ Mon)
  (at level 9, format "'eta[' Mon ]") : morphism_scope.
