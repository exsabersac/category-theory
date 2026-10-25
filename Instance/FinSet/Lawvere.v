Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Lawvere.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.FinSet.

Generalizable All Variables.

(*
   * * FinSet^op as a Lawvere theory

   The base example: [FinSet^op] is the Lawvere theory of EQUALITY — the
   theory with no operations and no equations, of which every presented
   theory is a quotient-extension.  Classically, every Lawvere theory
   receives an (identity-on-naturals) theory morphism from this one —
   the initiality that puts it at the base of the functorial-semantics
   development.  Theory morphisms are not formalized in-tree, so that
   remark is orienting context, not a citation of an artifact.

   The structure is pure bookkeeping over [Instance/FinSet.v]:

   - [Structure/Initial.v] defines [Initial C] as literal NOTATION for
   [@Terminal (C^op)], so [FinSet_Initial] IS the terminal-object
   structure of [FinSet^op]: its terminal object is [0%nat].

   - [Structure/Cocartesian.v] defines [Cocartesian C] as literal
   NOTATION for [@Cartesian (C^op)], so [FinSet_Cocartesian] IS the
   cartesian structure of [FinSet^op]: its product object on [m], [n]
   is [(m + n)%nat] definitionally.

   Consequently BOTH strictness equalities of [LawvereTheory] compute:
   [law_zero_terminal] and [law_plus_product] are each [eq_refl], the
   latter even at open variables [m n], because [FinSet_Cocartesian]'s
   [product_obj] is the function [fun m n => (m + n)%nat]. 

   --------
   * * FinSet^op 作为一个劳韦尔理论

   基本示例：[FinSet^op] 是相等性的劳韦尔理论——
   一个没有运算也没有方程的理论，每个呈现的理论都是其商-扩展。经典上，每个劳韦尔理论
   都接收来自该理论的（在自然数上的同一性）理论态射——
   这种初始性使它位于函子语义发展的基础。理论态射在树中未形式化，因此该说明是方向性背景，而不是文献引用。

   该结构是纯粹的 [Instance/FinSet.v] 上的簿记：

   - [Structure/Initial.v] 将 [Initial C] 定义为 [@Terminal (C^op)] 的字面符号，因此 [FinSet_Initial] 是 [FinSet^op] 的终对象结构：
   它的终对象是 [0%nat]。- [Structure/Cocartesian.v] 将 [Cocartesian C] 定义为 [@Cartesian (C^op)] 的字面符号，因此 [FinSet_Cocartesian] 是 [FinSet^op] 的笛卡尔结构：它在 [m] 上的乘积对象，[n] 定义上是 [(m + n)%nat]。

   因此，[LawvereTheory] 的两个严格相等都计算为：[law_zero_terminal] 和 [law_plus_product] 各自是 [eq_refl]，后者即使在开放变量 [m n] 下也是如此，因为 [FinSet_Cocartesian] 的 [product_obj] 是函数 [fun m n => (m + n)%nat]。
*)

Definition FinSetOp_Lawvere : LawvereTheory := {|
  law_cat := FinSet^op;
  law_terminal := FinSet_Initial;
  law_cartesian := FinSet_Cocartesian;
  law_of_nat := fun n => n;
  law_zero_terminal := eq_refl;
  law_plus_product := fun m n => eq_refl
|}.
