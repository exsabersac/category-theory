Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Terminal.

Generalizable All Variables.

(* * * Embedded constants via global elements / * * 通过全局元素嵌入常量 *)

(*
 nLab: https://ncatlab.org/nlab/show/global+element
 Wikipedia: https://en.wikipedia.org/wiki/Global_element

 A global element of an object `x` in a category with a terminal object `1`
 is a morphism `1 ~> x`; in `Sets` (where `1` is a singleton) these are in
 bijection with the elements of `x`, which is what makes them "elements". A
 global element is the special case of a generalized (`T`-valued) element
 `T ~> x` where the stage `T` is the terminal object `1`.

 This structure bundles a whole Coq type `A` of foreign constants together
 with a way to embed them: each value `x : A` names a host object
 `constant_obj x : C` and is realized there by a global element
 `constant x : 1 ~> constant_obj x`. So `Constant A` is a family of global
 elements indexed by the constants of `A`. Used to host foreign values of a
 given Coq type inside a category (see Instance/Coq.v). Note that an object
 is not in general determined by its global elements, so this carries the
 embedding as structure rather than recovering it as a property. 

 --------
 nLab:  https://ncatlab.org/nlab/show/global+element 
 维基百科:  https://en.wikipedia.org/wiki/Global_element 

 在具有终对象 `1` 的范畴中，某个对象 `x` 的全局元是一个态射 `1 ~> x`；在 `Sets` 中（其中 `1` 是单元集合），这些与 `x` 的元素一一对应，这也正是它们被称为“元素”的原因。全局元是广义（`T`-值）元素 `T ~> x` 的特例，其中阶段 `T` 是终对象 `1`。该结构将整套 Coq 类型 `A` 的外部常量打包在一起，并提供一个嵌入它们的方法：每个值 `x : A` 指定一个宿主对象 `constant_obj x : C`，并通过全局元素 `constant x : 1 ~> constant_obj x` 在该对象中实现。因此，`Constant A` 是一族由 `A` 常量索引的全局元素。用于在一个范畴中承载给定 Coq 类型的外部值（参见 Instance/Coq.v）。注意，一个对象通常不能仅通过其全局元素确定，因此这里将嵌入作为结构携带，而不是将其作为属性恢复。
*)

Class Constant `{@Terminal C} (A : Type) := {
  constant_obj : A → C;                       (* host object for each value of A / A 的每个值的主机对象 *)
  constant (x : A) : 1 ~> constant_obj x       (* global element naming x in C / C 中的全局元素命名 x *)
}.

Arguments constant_obj {_ _} A {_}.
