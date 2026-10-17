Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

Import EqNotations.

(** * Discrete category *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Discrete_category

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* A discrete category has no arrows except for identity morphisms. *)

Definition Discrete (C : Category) :=
  (* jww (2017-06-02): Equality is too much here. *)
  ∀ x y (f : x ~> y), ∃ H : x = y, f ≈ rew H in id.
