Require Import Category.Lib.
Require Import Category.Theory.Category.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(** * The thin category of a preorder (proset) *)

(*
 nLab: https://ncatlab.org/nlab/show/thin+category
 Wikipedia: https://en.wikipedia.org/wiki/Preorder
 Wikipedia: "A category with at most one morphism from any object X to any

   本文件给出预序集相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Proset {A : Type} {R : relation A} (P : PreOrder R) :
  Category := {|
  obj     := A;
  hom     := R;
  (* Since there can be at most one arrow between any two objects, multiple
     arrows of the same type are equal. *)
  homset  := fun A B => {| Setoid.equiv := fun _ _ => True |};
  id      := fun x => @reflexivity A R (@PreOrder_Reflexive A R P) x;
  compose := fun x y z f g =>
    @transitivity A R (@PreOrder_Transitive A R P) x y z g f
|}.

(* The typical example found in Category Theory theories and lectures is ≤. *)

Definition LessThanEqualTo_Category : Category :=
  @Proset nat PeanoNat.Nat.le PeanoNat.Nat.le_preorder.
