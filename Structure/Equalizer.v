Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Limit.
Require Import Category.Instance.Parallel.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(* nLab:      https://ncatlab.org/nlab/show/equalizer
   Wikipedia: https://en.wikipedia.org/wiki/Equaliser_(mathematics)

   给定 C 中平行对 f, g : x ~> y，等化子是对象 e 连同等化映射 i : e ~> x，使该对等化，

       f ∘ i ≈ g ∘ i,

   且对此性质普遍：对每个对象 n 与每个满足 f ∘ m ≈ g ∘ m 的映射 m : n ~> x，存在唯一
   u : n ~> e 满足 i ∘ u ≈ m（Wikipedia；nLab 称 i 为「等化映射」、e 为普遍此类对象）。
   等价地，等化子是平行对图

       e ~> x ⇉ y

   的极限，即两对象/两箭头形状 [Parallel] 上的极限（见 [Instance/Parallel.v]）。此处
   恰如此定义：[Equalizer] 是函子 F : Parallel ⟶ C 的 [Limit]。

   本文件不把等化映射或普遍性质重述为新字段；它们从 [Limit] 继承（见 [Structure/Limit.v]）。
   在形状 [Parallel] 下，极限锥的两条腿是等化映射 i（在 [ParX] 上、落入 x）及其与该对的
   复合（在 [ParY] 上、落入 y）；腿连贯定律强制 f ∘ i ≈ g ∘ i，[ump_limits] 为每个竞争锥
   供给唯一中介 u。用 [Instance/Parallel.v] 的 [APair f g : Parallel ⟶ C] 从实际平行对
   f, g 得到图 F。 *)

(*
   关于equalizers的来源与用途

   nLab:  https://ncatlab.org/nlab/show/coequalizer
   nLab:  https://ncatlab.org/nlab/show/regular+category
   Paper: Eckmann, Hilton, "Group-like structures in general categories

   本节说明（余）极限、等化子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明（余）极限、等化子、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Equalizer {C : Category} (F : Parallel ⟶ C) := Limit F.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Coequalizer {C : Category} (F : Parallel ⟶ C) := Colimit F.
