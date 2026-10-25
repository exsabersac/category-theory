Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Theory.Algebra.Comonoid.

Generalizable All Variables.

(** * Commutative comonoids in a symmetric monoidal category / * 对称单体范畴中的交换余单体 *)

(*
The dual of [CommutativeMonoid]: a [Comonoid X] over a
   [SymmetricMonoidal] category is COCOMMUTATIVE when its
   comultiplication is invariant under the braiding.

   In this library's notation, with [braid : X ⨂ X ~> X ⨂ X] the
   symmetry of the two outputs, the cocommutativity law reads

       braid ∘ delta ≈ delta       (cocommutativity of the comultiplication)

   This is the categorical dual of [mu ∘ braid ≈ mu]: where the monoid
   law precomposes the multiplication with the swap of its two inputs,
   the comonoid law postcomposes the comultiplication with the swap of
   its two outputs (the braiding moves to the other side of the
   operation, matching [delta]'s reversed direction).  Stated for a
   braiding it makes sense in any braided monoidal category; here we
   work in the symmetric setting, where the braiding is additionally
   involutive ([braid ∘ braid ≈ id]).

   nLab:      https://ncatlab.org/nlab/show/comonoid
   nLab:      https://ncatlab.org/nlab/show/braided+monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Monoid_(category_theory)

   This class is provided independently of [CommutativeFrobenius] so
   that an object can carry a cocommutative-comonoid structure WITHOUT
   being forced to also carry a multiplication.  Downstream callers
   that want to model "duplicate a tensor wire" (the canonical [delta]
   on a hypergraph object) without committing to a corresponding
   fan-in operation use this directly.

--------
[CommutativeMonoid] 的对偶：在 [SymmetricMonoidal] 范畴上的 [Comonoid X] 当其余积在编织下保持不变时是共交换的。

在这个库的符号中，对于 [braid : X ⨂ X ~> X ⨂ X] 双输出的对称性，共交换律表示为

编织 ∘ Δ ≈ Δ       （余乘法的余交换性）

这是 [mu ∘ braid ≈ mu] 的范畴对偶：当幺半群定律将乘法与其两个输入的交换预合成时，共幺半群定律将共乘法与其两个输出的交换后合成（编织移到操作的另一侧，与 [delta] 的反向方向相匹配）。对于编织来说，这在任何编织单范畴中都是有意义的；在这里我们在对称环境中工作，其中编织额外具有自反性（[braid ∘ braid ≈ id]）。

nLab:      https://ncatlab.org/nlab/show/comonoid
nLab:      https://ncatlab.org/nlab/show/braided+monoidal+category
维基百科: https://en.wikipedia.org/wiki/Monoid_(category_theory)

这个类独立于 [CommutativeFrobenius] 提供，以便一个对象可以携带一个余交换-余单子结构，而不必被迫也携带一个乘法。下游调用者希望对“复制张量线”（在超图对象上的典型 [delta]）建模，而不承诺相应的汇入操作时，可以直接使用这个类。
*)

Section CommutativeComonoid.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Class CommutativeComonoid (X : C) : Type := {
  (*
underlying comonoid object, taken in the monoidal category
     underlying the symmetric structure [S]

--------
在单体范畴中取的底层幺半群对象，该单体范畴是对称结构 [S] 的底层
*)
  ccomon_comonoid : @Comonoid C
                      (@braided_is_monoidal C
                         (@symmetric_is_braided C S))
                      X;

  (* comultiplication is invariant under the braiding: [braid ∘ delta ≈ delta] / 余乘法在编织下是不变的：[braid ∘ delta ≈ delta] *)
  delta_cocommutative_of_ccomon :
    braid ∘ (@delta _ _ _ ccomon_comonoid)
      ≈ (@delta _ _ _ ccomon_comonoid)
}.

#[export] Existing Instance ccomon_comonoid.

Coercion ccomon_comonoid : CommutativeComonoid >-> Comonoid.

End CommutativeComonoid.

Arguments ccomon_comonoid {C S X _}.
Arguments delta_cocommutative_of_ccomon {C S X _}.

(**
Convenience flat-projection aliases mirroring [scfa_delta] /
    [scfa_epsilon] from [SpecialCommutativeFrobenius.v]: project a
    [CommutativeComonoid X] to its underlying [delta] / [epsilon].

--------
便利的平面投影别名镜像 [scfa_delta] / [scfa_epsilon] 来自 [SpecialCommutativeFrobenius.v]：将一个 [CommutativeComonoid X] 投影到其基础的 [delta] / [epsilon]。
*)

Section CommutativeComonoidProjections.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Definition ccomon_delta {X : C} (M : CommutativeComonoid X)
  : X ~> (X ⨂ X)%object :=
  @delta _ _ _ (ccomon_comonoid (X := X)).

Definition ccomon_epsilon {X : C} (M : CommutativeComonoid X)
  : X ~> @I _ _ :=
  @epsilon _ _ _ (ccomon_comonoid (X := X)).

End CommutativeComonoidProjections.

Arguments ccomon_delta   {C S X} M.
Arguments ccomon_epsilon {C S X} M.
