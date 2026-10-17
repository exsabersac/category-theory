Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Terminal.

Generalizable All Variables.

(** Terminal-object-preserving functors. *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Initial_and_terminal_objects

   本文件给出终对象相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section TerminalFunctor.

Context `{F : C ⟶ D}.
Context `{@Terminal C}.
Context `{@Terminal D}.

Class TerminalFunctor := {
  (* the comparison iso 1 ≅ F 1 witnessing terminal-object preservation *)
  fobj_one_iso : 1 ≅ F 1;

  (* 相关说明。 （已译） *)
  fmap_one {X : C} : fmap one ≈ to fobj_one_iso ∘ @one _ _ (F X)
}.

End TerminalFunctor.

(*
   本节说明函子、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Notation "'InitialFunctor' F" := (@TerminalFunctor _ _ (F^op) _ _)
  (at level 9) : category_theory_scope.
Notation "@InitialFunctor C D F" := (@TerminalFunctor (C^op) (D^op) (F^op) _ _)
  (at level 9) : category_theory_scope.
