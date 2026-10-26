Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

Section Bicartesian.

(*
 nLab: https://ncatlab.org/nlab/show/bicartesian+category
 Wikipedia: none-exists (the term appears only within related articles such
 as “Distributive category” and “Cartesian closed category”)

 A bicartesian category is a category that is both cartesian and cocartesian:
 it has finite products (× with terminal unit 1) and finite coproducts (+ with
 initial unit 0), where the two structures need not coincide. (When they do
 coincide as biproducts the category is semiadditive: every semiadditive
 category is bicartesian, but not conversely.) The two directions of that
 remark are made precise in Structure/Semiadditive.v ([biproduct_addition],
 [bicartesian_preadditive]).

 This file does not introduce a [Bicartesian] class; the structure is simply
 the conjunction of [Cartesian] and [Cocartesian] in context, declared below.
 What it adds is [fork_merge], an interchange law relating the product pairing
 △ ([fork]) to the coproduct copairing ▽ ([merge]) — a fact available only
 when both structures are present. 

 --------
 nLab：https://ncatlab.org/nlab/show/bicartesian+category
 维基百科：不存在（该术语仅出现在相关条目中，例如“分配范畴”和“笛卡尔闭范畴”）

 双笛卡尔范畴是既是笛卡尔范畴又是余笛卡尔范畴的范畴：它具有有限积（×，末端单位为1）和有限余积（+，初始单位为0），这两种结构不必相同。（当它们作为双积一致时，该范畴是半加法的：每个半加法范畴都是双笛卡尔范畴，但反之不然。）这一观察的两个方向在Structure/Semiadditive.v（[biproduct_addition]，[bicartesian_preadditive]）中被明确说明。此文件并未引入 [Bicartesian] 类；该结构仅仅是在上下文中 [Cartesian] 和 [Cocartesian] 的结合，如下所示。它所增加的是 [fork_merge]，一条交换律，将乘积配对 △ ([fork]) 与余积共配对 ▽ ([merge]) 联系起来——这一事实仅在两种结构都存在时才可得知。
*)

Context {C : Category}.
Context `{@Cartesian C}.     (* finite products: x × y, terminal 1 / 有限乘积：x × y，终端 1 *)
Context `{@Cocartesian C}.   (* finite coproducts: x + y, initial 0 / 有限余积：x + y，初始 0 *)

(*
 Interchange of fork (△) and merge (▽): copairing two pairings equals pairing
 two copairings. Reading the four morphisms as the entries of a 2×2 matrix,
 both sides assemble the same morphism (x + w) ~> (y × z), so this is the
 “matrix transpose” / middle-four interchange of the bicartesian structure.
 The proof reduces the merge of forks to a fork of merges using [fork_comp]
 and [merge_comp], appealing to [fork_respects] both in C and dually in C^op. 

 --------
 叉子 (△) 与合并 (▽) 的互换：将两个配对联合起来等于将两个共配对配对。将这四个态射视为 2×2 矩阵的元素，双方组装出相同的态射 (x + w) ~> (y × z)，所以这是笛卡儿双积结构的“矩阵转置”/ 中间四互换。证明通过使用 [fork_comp] 和 [merge_comp] 将叉的合并化简为合并的叉，并在 C 中以及在 C^op 中对偶地调用 [fork_respects]。
*)
Corollary fork_merge {x y z w : C}
          (f : x ~> y) (g : x ~> z) (h : w ~> y) (i : w ~> z) :
  (f △ g) ▽ (h △ i) ≈ (f ▽ h) △ (g ▽ i).
Proof.
  rewrite <- id_left.
  rewrite <- fork_exl_exr.
  rewrite <- fork_comp.
  apply fork_respects;
  rewrite <- merge_comp; cat;
  apply (@fork_respects (C^op)); cat.
Qed.

End Bicartesian.
