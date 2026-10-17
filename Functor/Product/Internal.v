Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cartesian.
Require Import Category.Construction.Product.

Generalizable All Variables.

(** The internal product as a bifunctor ×(C) : C ∏ C ⟶ C. *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)

   本文件给出积（分量）构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[export]
Program Instance InternalProductFunctor `(C : Category) `{@Cartesian C} :
  C ∏ C ⟶ C := {
  fobj := fun p => fst p × snd p;
  fmap := fun _ _ p => (fst p ∘ exl) △ (snd p ∘ exr)
}.
Next Obligation.
  proper.
  simpl in *.
  rewrites.
  reflexivity.
Qed.
Next Obligation.
  simpl in *.
  rewrite <- fork_comp.
  rewrite <- !comp_assoc; cat.
Qed.

Notation "×( C )" := (@InternalProductFunctor C _)
  (at level 0, format "×( C )") : functor_scope.
