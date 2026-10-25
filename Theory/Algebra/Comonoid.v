Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.

(** * Internal comonoids in a monoidal category / * 单体范畴中的内部余单体 *)

(*
The dual of [Monoid]: a comonoid on [X : C] is a comultiplication
   [delta : X ~> X ⨂ X] and a counit [epsilon : X ~> I] satisfying the dual
   of the associativity and unit laws.  Writing [α] for the associator
   [tensor_assoc], [λ] for [unit_left] and [ρ] for [unit_right], the laws in
   this library's notation are:

     coassociativity   (δ ⨂ 1) ∘ δ ≈ α⁻¹ ∘ (1 ⨂ δ) ∘ δ
     left counit       (ε ⨂ 1) ∘ δ ≈ λ⁻¹
     right counit      (1 ⨂ ε) ∘ δ ≈ ρ⁻¹

   These are exactly the [Monoid] axioms with every arrow reversed (and hence
   every composite read right-to-left, [to] iso directions becoming [from]).

   In principle [Comonoid X] could be obtained as [@Monoid (C^op) _ X], but
   defining a [Monoidal] instance on [C^op] requires extra machinery (the
   tensor reverses and the unit/associator flip), and the resulting class
   members would need to be re-unfolded everywhere.  Following the practice
   elsewhere in this library (cf. [Cocartesian], [Initial]) we instead state
   the dual class directly.

   nLab:      https://ncatlab.org/nlab/show/comonoid
   Wikipedia: https://en.wikipedia.org/wiki/Monoid_(category_theory)

--------
[Monoid] 的对偶：[X : C] 上的余单元是一个余乘法 [delta : X ~> X ⨂ X] 和一个余单位 [epsilon : X ~> I]，满足结合律和单位律的对偶。使用 [α] 表示结合子 [tensor_assoc]，[λ] 表示 [unit_left]，[ρ] 表示 [unit_right]，本库符号下的规律是：

协结合性   (δ ⨂ 1) ∘ δ ≈ α⁻¹ ∘ (1 ⨂ δ) ∘ δ
左伴元       (ε ⨂ 1) ∘ δ ≈ λ⁻¹
右伴元      (1 ⨂ ε) ∘ δ ≈ ρ⁻¹

这些恰好是 [Monoid] 公理，但每条箭头都被反转了（因此每个复合读作从右到左，[to] 的同构方向变成了 [from]）。

原则上，[Comonoid X] 可以被视为 [@Monoid (C^op) _ X]，但在 [C^op] 上定义 [Monoidal] 实例需要额外的机制（张量翻转以及单位/结合子翻转），并且生成的类成员需要在各处重新展开。按照本库中其他地方的做法（参见 [Cocartesian]、[Initial]），我们直接声明对偶类。

nLab：https://ncatlab.org/nlab/show/comonoid
维基百科：https://en.wikipedia.org/wiki/Monoid_(category_theory)
*)

Section Comonoid.

Context {C : Category}.
Context `{M : @Monoidal C}.

Class Comonoid (X : C) : Type := {
  delta   : X ~> X ⨂ X;            (* comultiplication, dual of [mu] / 余乘法，[mu] 的对偶  *)
  epsilon : X ~> I;                (* counit, dual of [eta] / counit，[eta] 的对偶           *)

  (* coassociativity: dual of [mu_assoc] / 共结合性：[mu_assoc] 的对偶 *)
  delta_coassoc :
    bimap delta id[X] ∘ delta
      ≈ from (@tensor_assoc C M X X X) ∘ bimap id[X] delta ∘ delta;

  (* left counit law: dual of [mu_unit_left] / 左余单位律：[mu_unit_left] 的对偶 *)
  delta_counit_left :
    bimap epsilon id[X] ∘ delta
      ≈ from (@unit_left C M X);

  (* right counit law: dual of [mu_unit_right] / 右余单位律：[mu_unit_right] 的对偶 *)
  delta_counit_right :
    bimap id[X] epsilon ∘ delta
      ≈ from (@unit_right C M X)
}.

End Comonoid.

Arguments delta   {C M X _}.
Arguments epsilon {C M X _}.

Notation "'delta[' Co ]"   := (@delta _ _ _ Co)
  (at level 9, format "'delta[' Co ]") : morphism_scope.
Notation "'epsilon[' Co ]" := (@epsilon _ _ _ Co)
  (at level 9, format "'epsilon[' Co ]") : morphism_scope.
