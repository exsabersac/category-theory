Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(** * The strict category of categories *)

(*
 nLab: https://ncatlab.org/nlab/show/Cat
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_small_categories

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[export]
Instance StrictCat : Category := {
  obj     := Category;
  hom     := @Functor;
  homset  := @Functor_StrictEq_Setoid;
  id      := @Id;
  compose := @Compose;

  compose_respects := @Compose_respects_stricteq;
  id_left          := @fun_strict_equiv_id_left;
  id_right         := @fun_strict_equiv_id_right;
  comp_assoc       := @fun_strict_equiv_comp_assoc;
  comp_assoc_sym   := fun a b c d f g h =>
    symmetry (@fun_strict_equiv_comp_assoc a b c d f g h)
}.
