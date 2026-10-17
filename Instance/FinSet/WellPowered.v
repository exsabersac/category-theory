Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Subobject.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.WellPowered.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Classifier.

Generalizable All Variables.

(** * FinSet is well-powered *)

(*
 nLab:      https://ncatlab.org/nlab/show/FinSet
 Wikipedia: https://en.wikipedia.org/wiki/Subobject_classifier

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition FinSet_WellPowered@{o h s t u v +|
    Set < u, h < t, o <= s, h <= s +} :
  WellPowered@{o h h s t} FinSet@{o h u v} :=
  Classifier_WellPowered FinSet@{o h u v}.

(* The index at [n]: the characteristic functions of the subsets of n. *)
Example FinSet_wp_index (n : FinSet) :
  wp_index (FinSet_WellPowered n) = (Fin.t n → Fin.t 2) := eq_refl.
