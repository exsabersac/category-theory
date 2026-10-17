Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.

Generalizable All Variables.

(** The core groupoid of a category C: its maximal sub-groupoid. *)

(*
   nLab: https://ncatlab.org/nlab/show/groupoid
   Wikipedia: https://en.wikipedia.org/wiki/Groupoid

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab:  https://ncatlab.org/nlab/show/groupoid
   Paper: Brandt, "Über eine Verallgemeinerung des Gruppenbegriffes",
   Paper: Brown, "From groups to groupoids: a brief survey", Bulletin of
   Paper: Weinstein, "Groupoids: Unifying Internal and External Symmetry",

   本节说明 Groupoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Groupoid (C : Category) : Category := {|
  obj     := @obj C;
  hom     := @Isomorphism C;
  homset  := @iso_setoid C;
  id      := @iso_id C;
  compose := @iso_compose C
|}.
