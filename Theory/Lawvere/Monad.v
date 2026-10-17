Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Fun.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Monadicity.Crude.
Require Import Category.Structure.Coequalizer.Reflexive.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Theory.Lawvere.
Require Import Category.Theory.Lawvere.Model.
Require Import Category.Theory.Lawvere.Sets.

Generalizable All Variables.

(*
 nLab:      https://ncatlab.org/nlab/show/Lawvere+theory
 nLab:      https://ncatlab.org/nlab/show/monadicity+theorem
 Wikipedia: https://en.wikipedia.org/wiki/Lawvere_theory

   本文件给出单子相关定义或实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section LawvereMonad.

Context (T : LawvereTheory).
Context (L : Sets ⟶ Models T Sets).
Context (adj : L ⊣ ev1 T).

(** The induced monad on [Sets]: ret = η, join = U ε F, packaged
    transparently by [Adjunction_Induced_Monad]. *)

Definition Lawvere_Monad : @Monad Sets (ev1 T ◯ L) :=
  Adjunction_Induced_Monad adj.

(** The Eilenberg–Moore comparison 函子 at 伴随. （已译） *)

Definition Lawvere_EM_Comparison :
  Models T Sets ⟶ @EilenbergMoore Sets (ev1 T ◯ L) Lawvere_Monad :=
  EM_Comparison adj.

(* * ** Scoped monadicity

 The crude-monadicity hypotheses Monad/Monadicity/Crude.v,
 re-exposed verbatim at 伴随. （已译） *)

Context (RC : HasReflexiveCoequalizers (Models T Sets)).
Context (pres : PreservesReflexiveCoequalizers (ev1 T)).
Context (refl : ReflectsIsos (ev1 T)).

Corollary Lawvere_crude_monadicity :
  EquivalenceOfCategories Lawvere_EM_Comparison.
Proof using RC pres refl.
  exact (crude_monadicity adj RC pres refl).
Defined.

End LawvereMonad.

