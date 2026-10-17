Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Lawvere.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.FinSet.

Generalizable All Variables.

(*
   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition FinSetOp_Lawvere : LawvereTheory := {|
  law_cat := FinSet^op;
  law_terminal := FinSet_Initial;
  law_cartesian := FinSet_Cocartesian;
  law_of_nat := fun n => n;
  law_zero_terminal := eq_refl;
  law_plus_product := fun m n => eq_refl
|}.
