Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

Import EqNotations.

(** * Discrete category / * 离散类别 *)

(*
 nLab: https://ncatlab.org/nlab/show/discrete+category
 Wikipedia: https://en.wikipedia.org/wiki/Discrete_category

 A category is discrete when its only morphisms are the identity morphisms;
 equivalently, the hom-set `x ~> y` is a singleton when `x = y` and empty
 otherwise. The predicate [Discrete] expresses this directly: every morphism
 `f : x ~> y` forces its source and target to be equal (the witness `H : x =
 y`) and is then equal under `≈` to the identity transported along `H` (using
 the [EqNotations] `rew` for the dependent rewrite). This is the discrete
 *and* skeletal characterization. nLab notes that asking for object equality
 `x = y` rather than isomorphism violates the principle of equivalence — the
 caveat recorded in the [jww] note below; the equivalence-respecting variant
 would replace `x = y` with an isomorphism `x ≅ y`. A discrete category is
 the image of a set under the left adjoint, and the dual (codiscrete /
 indiscrete) construction is the further right adjoint; both adjunctions
 are now proved -- [Disc_Objects_Adjunction] (Instance/Cat/Objects.v) and
 [Objects_Indisc_Adjunction] (Instance/Indiscrete.v), composing as
 [adjoint_string]. The ambient is [Coq]/[StrictCat], NOT `Set ⟶ Cat`:
 [objects_not_functorial_over_Cat] refutes an objects functor on [Cat],
 and [disc_carrier_not_Sets_functor] refutes the [Sets] target. 

 --------
 nLab: https://ncatlab.org/nlab/show/discrete+category
 Wikipedia: https://en.wikipedia.org/wiki/Discrete_category当一个范畴唯一的态射是恒等态射时，该范畴是离散的;
 等价地，当 `x = y` 且空时，hom-set `x ~> y` 是单元素集
 否则。谓词[Discrete]直接表达了这一点：每个态射
 `f : x ~> y` 强制其源和目标相等（见证 'H ： x =
 y `) and is then equal under ` ≈ ` to the identity transported along ` H'（使用
 依赖重写的[EqNotations] `rew`）。这是离散的
 *以及*骨骼特征描述。nLab指出，要求对象相等
 `x = y`而非同构，违反了等价原则——
 注意事项见下文[jww]注;等价性尊重的变体
 将`x = y`替换为同构`x ≅ y`。离散范畴是集合在左伴随下的像，而双对偶（余离散/不可分离）构造是进一步的右伴随；现在两个伴随都已被证明 --  [Disc_Objects_Adjunction]  (Instance/Cat/Objects.v) 和  [Objects_Indisc_Adjunction]  (Instance/Indiscrete.v)，组合为 [adjoint_string] 。环境是 [Coq] / [StrictCat] ，而不是 `Set ⟶ Cat` ：[objects_not_functorial_over_Cat] 反驳 [Cat] 上的对象函子，[disc_carrier_not_Sets_functor] 反驳 [Sets] 的目标。
*)

(* A discrete category has no arrows except for identity morphisms. / 一个离散范畴除了恒等态射外没有其他箭头。 *)

Definition Discrete (C : Category) :=
  (* jww (2017-06-02): Equality is too much here. / jww (2017-06-02)：这里的平等太过分了。 *)
  ∀ x y (f : x ~> y), ∃ H : x = y, f ≈ rew H in id.
