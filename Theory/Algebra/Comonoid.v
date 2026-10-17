Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.

(* * * Internal comonoids 幺半范畴 （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/comonoid
 Wikipedia: https://en.wikipedia.org/wiki/Monoid_(category_theory) *)

   本文件给出幺半范畴中的余幺半群对象（余乘法与余单位及相应定律）。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Comonoid.

Context {C : Category}.
Context `{M : @Monoidal C}.

Class Comonoid (X : C) : Type := {
  delta   : X ~> X ⨂ X;            (* comultiplication, dual of [mu]  *)
  epsilon : X ~> I;                (* counit, dual of [eta]           *)

  (* coassociativity: dual of [mu_assoc] *)
  delta_coassoc :
    bimap delta id[X] ∘ delta
      ≈ from (@tensor_assoc C M X X X) ∘ bimap id[X] delta ∘ delta;

  (* left counit law: dual of [mu_unit_left] *)
  delta_counit_left :
    bimap epsilon id[X] ∘ delta
      ≈ from (@unit_left C M X);

  (* right counit law: dual of [mu_unit_right] *)
  delta_counit_right :
    bimap id[X] epsilon ∘ delta
      ≈ from (@unit_right C M X)
}.

End Comonoid.

Arguments delta   {C M X _}.
Arguments epsilon {C M X _}.

Notation "'delta[' Co ]"   := (@delta _ _ _ Co)
  (at level 9, format "'delta[' Co ]") : morphism_scope.
Notation "'epsilon[' Co ]" := (@epsilon _ _ _ Co)
  (at level 9, format "'epsilon[' Co ]") : morphism_scope.
