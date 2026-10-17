Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Monoidal.
Require Export Category.Structure.Monoidal.Internal.Product.

Generalizable All Variables.

(*
   Wikipedia: https://en.wikipedia.org/wiki/Cartesian_monoidal_category

   本文件给出笛卡尔结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CartesianIsMonoidal.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.

(* The cartesian monoidal structure: tensor := ×, unit := 1.  This is a plain
   [Definition] rather than an [Instance] (mirroring [CC_Monoidal]): making it
   an instance would let typeclass resolution silently pick the product as
   *the* monoidal structure on every cartesian category, conflicting with
   hand-rolled monoidal structures elsewhere.  Callers select it explicitly. *)
Definition Cartesian_Monoidal : @Monoidal C := CC_Monoidal.

End CartesianIsMonoidal.
