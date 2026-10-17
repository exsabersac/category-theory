(*
   本文件为测试：ProbeDual359。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.StarAutonomous.
Require Import Category.Instance.Sets.
Require Import Category.Adjunction.Right.
Require Import Category.Structure.Monoidal.Dual.

Remove Hints Sets_Product_Monoidal : typeclass_instances.

Open Scope category_scope.

Generalizable All Variables.

Section ProbeDual359.

Context {C : Category}.
Context `{@SymMonClosed C}.
Context (d : C).

(* Controls.  Every constant a negative names is also named OUTSIDE a
   [Fail] and APPLIED, never left bare -- an unapplied polymorphic
   constant elaborates for reasons unrelated to the negative and so
   certifies nothing. *)
Check (dd_unit d).
Check (double_dual_unit d).
Check (dual_self_adjoint_on_the_right d).
Check (fun x : C => dd_unit d x).
Check (fun x : C => transform[double_dual_unit d] x).
Check (@aor C C (dual d) (dual d) (dual_self_adjoint_on_the_right d)).

(* CONVERSION 1 -- [dd_unit] is not the bare braid-transpose on the
   nose: the residue is `id ⨂ id`, and writing that residue out closes
   the very same statement at [eq_refl], which is what makes this
   negative discriminate rather than merely fail. *)
Fail Example probe359_braid_strict (x : C) :
  dd_unit d x = dcur (eval' ∘ braid) := eq_refl.

(* Control for CONVERSION 1, with the residue exhibited. *)
Example probe359_braid_residue (x : C) :
  dd_unit d x = dcur (eval' ∘ (id[x ⇒ d] ⨂ id[x]) ∘ braid) := eq_refl.

(* TYPING -- off the diagonal the two legs of the bijection do not even
   share a type, so `to = from` is not statable there at all.  This is
   the honest form of Mac Lane's symmetry remark. *)
Fail Example probe359_offdiagonal (a x : C) :
  to (@aor C C (dual d) (dual d) (dual_self_adjoint_on_the_right d) a x)
    = from (@aor C C (dual d) (dual d)
              (dual_self_adjoint_on_the_right d) a x) := eq_refl.

(* Control: ON the diagonal the two legs ARE the same term. *)
Example probe359_diagonal (a : C) :
  to (@aor C C (dual d) (dual d) (dual_self_adjoint_on_the_right d) a a)
    = from (@aor C C (dual d) (dual d)
              (dual_self_adjoint_on_the_right d) a a) := eq_refl.

End ProbeDual359.

(* Instrument check.  [Fail] is live in this build and does notice a
   conversion failure.  Scope-free deliberately, so that it cannot fail
   on a missing scope delimiter instead of on the proposition. *)
Fail Example probe359_instrument : (true = false) := eq_refl.
