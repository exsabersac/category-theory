Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Terminal.

Generalizable All Variables.

(* * * Embedded constants via 全局元素 （已译） *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Global_element

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class Constant `{@Terminal C} (A : Type) := {
  constant_obj : A → C;                       (* host object for each value of A *)
  constant (x : A) : 1 ~> constant_obj x       (* global element naming x in C *)
}.

Arguments constant_obj {_ _} A {_}.
