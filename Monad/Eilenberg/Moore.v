Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Algebra.

Generalizable All Variables.

(** * The Eilenberg–Moore category of a monad. *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)

   本文件给出 Eilenberg–Moore 相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The monad instance is bound by name so that [TAlgebra]'s instance argument
   can be given explicitly in [obj]: were it left to Program, the elaborator
   would seal that argument behind a Qed-opaque obligation constant, and
   algebras built against the ambient instance [H] — such as the free algebras
   (T a, μ_a) of Moore/Adjunction.v — would not be recognized as objects of
   this category. *)

Program Definition EilenbergMoore `(T : C ⟶ C) `{H : @Monad C T} : Category := {|
  obj     := ∃ a : C, @TAlgebra C T H a;
  hom     := fun x y => TAlgebraHom T ``x ``y (projT2 x) (projT2 y);
  homset  := fun _ _ => {| equiv := fun f g => t_alg_hom[f] ≈ t_alg_hom[g] |};
  id      := fun _ => {| t_alg_hom := id |};
  compose := fun _ _ _ f g => {| t_alg_hom := t_alg_hom[f] ∘ t_alg_hom[g] |}
|}.
Next Obligation.
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite <- t_alg_hom_commutes.
  rewrite <- !comp_assoc.
  rewrite <- t_alg_hom_commutes.
  reflexivity.
Qed.
