Require Import Category.Lib.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.

Generalizable All Variables.

Local Set Warnings "-intuition-auto-with-star".

(** * Cartesian closure of [Sets] *)

(*
 nLab: https://ncatlab.org/nlab/show/exponential+object
 Wikipedia: https://en.wikipedia.org/wiki/Cartesian_closed_category
 Wikipedia: https://en.wikipedia.org/wiki/Exponential_object

   本文件给出闭结构实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[export]
Program Instance Sets_Closed : @Closed Sets _ := {
  exponent_obj := fun x y =>
    {| carrier := SetoidMorphism x y
     ; is_setoid := @SetoidMorphism_Setoid x y |};

  exp_iso := fun _ _ _ =>
    {| to   := {| morphism := fun f =>
                    {| morphism := fun x =>
                         {| morphism := fun y => f (x, y) |} |} |}
     ; from := {| morphism := fun f =>
                    {| morphism := fun p => f (fst p) (snd p) |} |} |}
}.
Next Obligation.
  proper; destruct f; simpl.
  apply proper_morphism.
  split; simpl; intuition; auto with *.
Qed.
Next Obligation.
  proper; destruct f; simpl.
  apply proper_morphism.
  split; simpl; intuition; auto with *.
Qed.
Next Obligation.
  proper; simpl in *.
  destruct f; simpl in *.
  unfold Proper, respectful, SetoidMorphism_equiv in proper_morphism.
  rewrite (proper_morphism _ _ X).
  destruct (morphism y).
  apply proper_morphism0; assumption.
Qed.
