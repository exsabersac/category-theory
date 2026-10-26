Require Import Category.Lib.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Semicartesian.

Generalizable All Variables.

(* * * The unit of a semicartesian monoidal category is terminal / * * 半笛卡尔单范畴的单位是终端对象 *)

(*
 nLab: https://ncatlab.org/nlab/show/semicartesian+monoidal+category
 Wikipedia: https://en.wikipedia.org/wiki/Cartesian_monoidal_category

 A semicartesian (affine) monoidal category is a monoidal category whose
 unit object I is terminal: every object x has the discard map eliminate :
 x ~> I, and any two maps x ~> I agree (unit_terminal). This file repackages
 exactly that data as a Terminal structure on I,

 terminal_obj := I,
 one          := eliminate    (the unique x ~> I),
 one_unique   := unit_terminal (any two x ~> I agree under ≈),

 matching nLab (“the unit for the tensor product is a terminal object”) and
 Wikipedia (“in any cartesian monoidal category, the terminal object is the
 monoidal unit”; cartesian ⊆ semicartesian).

 The same definition, with the same name, is given at top level in
 Structure/Monoidal/Semicartesian.v; that copy is the one downstream files
 (e.g. Instance/Coq/Par.v) use. The version here is section-local, hence
 lives in the distinct module Category.Structure.Monoidal.Semicartesian.
 Terminal. 

 --------
 nLab：https://ncatlab.org/nlab/show/semicartesian+monoidal+category
 Wikipedia：https://en.wikipedia.org/wiki/Cartesian_monoidal_category

 半笛卡尔（仿射）幺半群范畴是指一种幺半群范畴，其单位对象 I 是终端对象：每个对象 x 都有丢弃映射 eliminate ：x ~> I，并且任意两个映射 x ~> I 都相同（unit_terminal）。这个文件将这些数据完全重新打包为 I 上的终端结构，

 terminal_obj := I,
 one          := eliminate    （唯一的 x ~> I），
 one_unique   := unit_terminal （任意两个 x ~> I 在 ≈ 下相同），

 与 nLab（“张量积的单位是终端对象”）和 Wikipedia（“在任何笛卡尔幺半群范畴中，终端对象是幺半群单位”；笛卡尔 ⊆ 半笛卡尔）相匹配。在 Structure/Monoidal/Semicartesian.v 的顶层给出了相同名称的相同定义；下游文件（例如 Instance/Coq/Par.v）使用的是那个副本。这里的版本是节内局部的，因此位于不同的模块 Category.Structure.Monoidal.Semicartesian。终结。
*)

Section SemicartesianMonoidalTerminal.

Context `{@Monoidal C}.
Context `{@SemicartesianMonoidal C _}.

Program Definition SemicartesianMonoidal_Terminal : @Terminal C := {|
  terminal_obj := I;                     (* the terminal object is the unit I / 终对象是单位 I *)
  one := @eliminate _ _ _;               (* ! := eliminate, the discard x ~> I / ! := 消除，丢弃 x ~> I *)
  one_unique := @unit_terminal _ _ _     (* uniqueness of x ~> I, up to ≈ / x 的唯一性 ~> I，至大约 ≈ *)
|}.

End SemicartesianMonoidalTerminal.
