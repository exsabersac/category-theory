Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Theory.Algebra.Monoid.

Generalizable All Variables.

(** * Commutative monoids in a symmetric monoidal category / * 对称幺半群范畴中的交换幺半群 *)

(*
A commutative monoid in [(C, ⨂, I, σ)] is a [Monoid X] whose
   multiplication is invariant under the braiding.  This is the
   "commutative monoid" / "abelian monoid" of the symmetric-monoidal
   setting.

   In this library's notation, with [braid : X ⨂ X ~> X ⨂ X] the
   symmetry of the inputs, the commutativity law reads

       mu ∘ braid ≈ mu              (commutativity of the multiplication)

   This is the categorical version of [a * b = b * a]: precomposing
   the multiplication with the swap of its two arguments leaves it
   unchanged.  Stated for a braiding it makes sense in any braided
   monoidal category; here we work in the symmetric setting, where the
   braiding is additionally involutive ([braid ∘ braid ≈ id]).

   nLab:      https://ncatlab.org/nlab/show/commutative+monoid
   nLab:      https://ncatlab.org/nlab/show/braided+monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Monoid_(category_theory)

   This class is provided independently of [Frobenius] / [Comonoid] so
   that an object can carry a commutative monoid structure WITHOUT
   being forced to also carry a comultiplication.  Downstream callers
   that want to model element-wise multiplication of tensor values
   (where there is no natural co-multiplication) use this directly.

--------
在 [(C, ⨂, I, σ)] 中的交换幺半群是一个 [Monoid X]，其乘法在编织下是不变的。这就是对称单体环境中的“交换幺半群”/“阿贝尔幺半群”。

在这个库的表示法中，使用 [braid : X ⨂ X ~> X ⨂ X] 对输入的对称性，交换律表示为

mu ∘ braid ≈ mu （乘法的交换性）

这是 [a * b = b * a] 的范畴版本：将乘法与其两个参数的交换预组合不会改变它。对于一个编排来说，它在任何编排单范畴中都是有意义的；在这里，我们在对称环境下工作，其中编排额外地是自反的（[braid ∘ braid ≈ id]）。

nLab:      https://ncatlab.org/nlab/show/commutative+monoid
nLab:      https://ncatlab.org/nlab/show/braided+monoidal+category
维基百科: https://en.wikipedia.org/wiki/Monoid_(category_theory)

本类独立于 [Frobenius] / [Comonoid] 提供，以便一个对象可以拥有交换幺半群结构，而不被迫同时拥有余乘结构。下游调用者如果想对张量值进行元素逐个乘法建模（在没有自然余乘的情况下），可以直接使用此类。
*)

Section CommutativeMonoid.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Class CommutativeMonoid (X : C) : Type := {
  (*
underlying monoid object, taken in the monoidal category
     underlying the symmetric structure [S]

--------
底层单子对象，在对称结构 [S] 的单体范畴中采用
*)
  cmon_monoid : @Monoid C
                  (@braided_is_monoidal C
                     (@symmetric_is_braided C S))
                  X;

  (* multiplication is invariant under the braiding: [mu ∘ braid ≈ mu] / 乘法在编织下是不变的：[mu ∘ braid ≈ mu] *)
  mu_commutative_of_cmon :
    (@mu _ _ _ cmon_monoid) ∘ braid
      ≈ (@mu _ _ _ cmon_monoid)
}.

#[export] Existing Instance cmon_monoid.

Coercion cmon_monoid : CommutativeMonoid >-> Monoid.

End CommutativeMonoid.

Arguments cmon_monoid {C S X _}.
Arguments mu_commutative_of_cmon {C S X _}.

(**
Convenience aliases mirroring [scfa_mu] / [scfa_eta] from
    [SpecialCommutativeFrobenius.v]: project a [CommutativeMonoid X] to
    its underlying [mu] / [eta].

--------
便利别名镜像 [scfa_mu] / [scfa_eta] 来自 [SpecialCommutativeFrobenius.v]：将 [CommutativeMonoid X] 投影到其底层的 [mu] / [eta]。
*)

Section CommutativeMonoidProjections.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Definition cmon_mu {X : C} (M : CommutativeMonoid X)
  : X ⨂ X ~> X :=
  @mu _ _ _ (cmon_monoid (X := X)).

Definition cmon_eta {X : C} (M : CommutativeMonoid X)
  : I ~> X :=
  @eta _ _ _ (cmon_monoid (X := X)).

End CommutativeMonoidProjections.

Arguments cmon_mu  {C S X} M.
Arguments cmon_eta {C S X} M.
