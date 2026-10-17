Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Initial.

Generalizable All Variables.

(*
   Wikipedia: https://en.wikipedia.org/wiki/Distributive_category

   本文件给出 Beck 分配律：使两单子可复合为单子的额外数据。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Distributive.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Cocartesian C}.
Context `{@Initial C}.

Class Distributive := {
  (* Binary distributivity: x × - preserves binary coproducts. *)
  distr_prod_coprod {x y z} : @Isomorphism C (x × (y + z)) (x × y + x × z);
  (* Nullary law: x × - preserves the initial (nullary coproduct) object. *)
  distr_zero {x} : x × 0 ≅ 0
}.

End Distributive.
