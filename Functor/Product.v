Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.

(** The pointwise product of two functors into a monoidal category. *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category

   本文件给出积（分量）构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[export]
Program Instance Product
        {C : Category} {D : Category} `{@Monoidal D}
        {F : C ⟶ D} {G : C ⟶ D} : C ⟶ D := {
  fobj := fun x => (F x ⨂ G x)%object;          (* objectwise tensor: F x ⨂ G x *)
  fmap := fun _ _ f => fmap[F] f ⨂ fmap[G] f     (* arrowwise: bimap (F f) (G f) *)
}.
Next Obligation.
  proper;
  apply bimap_respects;
  now apply fmap_respects.
Qed.
Next Obligation. normal; reflexivity. Qed.

Notation "F :*: G" := (@Product _ _ _ F%functor G%functor)
  (at level 9) : functor_scope.
