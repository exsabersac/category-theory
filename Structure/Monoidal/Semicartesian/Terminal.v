Require Import Category.Lib.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Semicartesian.

Generalizable All Variables.

(* * * The unit semicartesian 幺半范畴 terminal （已译） *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Cartesian_monoidal_category

   本文件给出终对象相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SemicartesianMonoidalTerminal.

Context `{@Monoidal C}.
Context `{@SemicartesianMonoidal C _}.

Program Definition SemicartesianMonoidal_Terminal : @Terminal C := {|
  terminal_obj := I;                     (* the terminal object is the unit I *)
  one := @eliminate _ _ _;               (* ! := eliminate, the discard x ~> I *)
  one_unique := @unit_terminal _ _ _     (* uniqueness of x ~> I, up to ≈ *)
|}.

End SemicartesianMonoidalTerminal.
