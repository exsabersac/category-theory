(**
* Convenience umbrella: the core theory and basic structures.

   Re-exports a curated subset of the development — the foundational
   theory modules (categories, isomorphisms, functors, natural
   transformations, adjunctions) together with the elementary universal
   structures (cartesian/cocartesian/bicartesian, terminal, initial) —
   so that downstream files can [Require Import Category.Theory] for the
   common essentials rather than naming each module.  This is a
   hand-picked starting bundle, not an exhaustive export of [Theory/].

--------
* 便捷总览：核心理论与基本结构。

   再导出本开发的一个精选子集——基础理论模块（范畴、同构、函子、自然
   变换、伴随）以及初等普遍结构（笛卡尔/余笛卡尔/双笛卡尔、终对象、
   初始对象）——使下游文件可用 [Require Import Category.Theory] 取得
   常用要点，而不必逐个点名模块。这是手工挑选的起步捆绑，并非
   [Theory/] 的穷尽导出。
*)

Require Export Category.Theory.Category.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Theory.Natural.Transformation.
Require Export Category.Theory.Adjunction.
Require Export Category.Structure.Cartesian.
Require Export Category.Structure.Cocartesian.
Require Export Category.Structure.Bicartesian.
Require Export Category.Structure.Terminal.
Require Export Category.Structure.Initial.
