Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Strict.

Generalizable All Variables.

(*
   本文件给出严格情形。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)
Ltac strict_collapse :=
  repeat (rewrite ?strict_assoc_to ||
          rewrite ?strict_assoc_from ||
          rewrite ?strict_unit_left_to ||
          rewrite ?strict_unit_left_from ||
          rewrite ?strict_unit_right_to ||
          rewrite ?strict_unit_right_from).

(* * ** [strict_collapse_in H]: same, targeting 假设 [H]. （已译） *)
Tactic Notation "strict_collapse" "in" hyp(H) :=
  repeat (rewrite ?strict_assoc_to in H ||
          rewrite ?strict_assoc_from in H ||
          rewrite ?strict_unit_left_to in H ||
          rewrite ?strict_unit_left_from in H ||
          rewrite ?strict_unit_right_to in H ||
          rewrite ?strict_unit_right_from in H).

(* * ** [strict_collapse_all]: rewrite EVERYWHERE.

 Goal AND every 假设. （已译） *)
Ltac strict_collapse_all :=
  repeat (rewrite ?strict_assoc_to in * ||
          rewrite ?strict_assoc_from in * ||
          rewrite ?strict_unit_left_to in * ||
          rewrite ?strict_unit_left_from in * ||
          rewrite ?strict_unit_right_to in * ||
          rewrite ?strict_unit_right_from in *).
