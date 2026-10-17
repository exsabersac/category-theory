Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(** The terminal category 1 (the point). *)

(*
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_small_categories
 Wikipedia: https://en.wikipedia.org/wiki/Initial_and_terminal_objects

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition _1@{o h p} : Category@{o h p} := {|
  obj     := poly_unit@{o};            (* the single object *)
  hom     := fun _ _ => poly_unit@{h}; (* the single (identity) arrow *)
  homset  := Morphism_equality@{o h p}; (* hom-setoid is strict equality *)
  id      := fun _ => ttt;             (* identity = the lone arrow *)
  compose := fun _ _ _ _ _ => ttt      (* composition = the lone arrow *)
|}.
Next Obligation.
  now destruct f.
Qed.
Next Obligation.
  now destruct f.
Qed.

Notation "1" := _1 : category_scope.

(* `one[C]` names the unique functor `! : C ⟶ 1` at Cat's Terminal instance. *)
Notation "one[ C ]" := (@one Cat _ C)
  (at level 9, format "one[ C ]") : object_scope.

(* The unique functor `! : C ⟶ 1`, collapsing all of C onto the point. *)
#[export]
Program Instance Erase `(C : Category) : C ⟶ 1 := {
  fobj := fun _ => ttt;      (* every object goes to the lone object *)
  fmap := fun _ _ _ => id    (* every morphism goes to the identity *)
}.

(* 1 is the terminal object of Cat, witnessed by the unique functor [Erase]. *)
#[export]
Program Instance Cat_Terminal : @Terminal Cat := {
  terminal_obj := _1;        (* the terminal category 1 *)
  one := Erase               (* the unique functor ! : C ⟶ 1 *)
}.
Next Obligation.
  constructive; auto; try exact ttt.
  destruct (fmap[f] f0); auto.
Qed.
