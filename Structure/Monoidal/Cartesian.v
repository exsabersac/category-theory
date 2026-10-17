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

(*
   本节说明幺半结构、幺半群、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Cartesian_Monoidal : @Monoidal C := CC_Monoidal.

End CartesianIsMonoidal.
