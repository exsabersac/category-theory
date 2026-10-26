Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Applicative.
Require Import Category.Monad.Distributive.
Require Import Category.Monad.Compose.
Require Import Category.Functor.Structure.Monoidal.Pure.
Require Import Category.Instance.Coq.
Require Export Category.Theory.Coq.Applicative.Proofs.
Require Export Category.Theory.Coq.Monad.

Generalizable All Variables.

(** Instance characterisations and lawfulness for the Coq monads / Coq 单子实例的特征和合法性 *)

(*
nLab: https://ncatlab.org/nlab/show/monad
   nLab: https://ncatlab.org/nlab/show/Kleisli+category
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(functional_programming)
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)

   This file relates the Haskell-style [Monad] class of [Theory.Coq.Monad]
   (carrying only [ret]/[bind]) to the categorical notion from [Theory.Monad],
   namely an endofunctor [F] with unit [η = ret : Id ⇒ F] and multiplication
   [μ = join : F ∘ F ⇒ F] satisfying the unit laws [μ ∘ Fη = μ ∘ ηF = id] and
   associativity [μ ∘ Fμ = μ ∘ μF].  In Kleisli terms these are the three
   monad laws: left identity [ret a >>= f ≈ f a], right identity [m >>= ret ≈ m]
   and associativity [(m >>= f) >>= g ≈ m >>= (λ x, f x >>= g)].

   [EndoMonad_Monad] builds the bind/return [Monad F] from a categorical monad
   on the endofunctor [F], using the standard [bind m f = μ (fmap f m)]
   (Wikipedia: [ma >>= f ↔ (join ∘ map f) ma]).  [IsMonad H A m] is the
   predicate “this [ret]/[bind] arises from such a lawful categorical monad”,
   and [Identity_IsMonad], [arrow_IsMonad] and [Compose_IsMonad] establish
   lawfulness of the identity, reader and composite monad instances by
   exhibiting that structure.  As in the rest of the applied layer, these
   discharge against Coq's [Type] category and so rest on the pre-existing
   [functional_extensionality_dep] axiom (not an additional assumption).

--------
nLab: https://ncatlab.org/nlab/show/monad
nLab: https://ncatlab.org/nlab/show/Kleisli+category
维基百科: https://en.wikipedia.org/wiki/Monad_(functional_programming)
维基百科: https://en.wikipedia.org/wiki/Monad_(category_theory)

该文件将 Haskell 风格的 [Monad] 类 [Theory.Coq.Monad]（仅携带 [ret]/[bind]）与 [Theory.Monad] 的范畴概念联系起来，即具有单元 [η = ret : Id ⇒ F] 和乘法 [μ = join : F ∘ F ⇒ F] 的自函子 [F]，满足单元律 [μ ∘ Fη = μ ∘ ηF = id] 和结合律 [μ ∘ Fμ = μ ∘ μF]。在 Kleisli 术语中，这些就是三个单子律：左单位律 [ret a >>= f ≈ f a]、右单位律 [m >>= ret ≈ m] 和结合律 [(m >>= f) >>= g ≈ m >>= (λ x, f x >>= g)]。

[EndoMonad_Monad] 构建了 bind/return [Monad F]，从范畴单子在 [F] 上的 endofunctor 使用标准的 [bind m f = μ (fmap f m)] (维基百科: [ma >>= f ↔ (join ∘ map f) ma])。[IsMonad H A m] 是谓词“这个 [ret]/[bind] 来源于这样的合法范畴单子”，而 [Identity_IsMonad]、[arrow_IsMonad] 和 [Compose_IsMonad] 通过展示该结构来建立恒等、读者和复合单子实例的合法性。正如在应用层的其他部分一样，这些针对 Coq 的 [Type] 范畴进行消解，因此依赖于预先存在的 [functional_extensionality_dep] 公理（而非额外假设）。
*)

Definition EndoMonad_Monad
  `(H : EndoFunctor F)
  `(A : @Functor.Applicative.Applicative _ _ (FromAFunctor H))
  `(M : @Theory.Monad.Monad _ (FromAFunctor H)) :
  Monad F := {|
  ret := @Pure.pure _ _ (FromAFunctor H) _ A;
  bind := λ x y m f,
    @Theory.Monad.join _ _ M y
      (@Theory.Functor.fmap _ _ (FromAFunctor H) x (F y) f m);
|}.

Definition IsMonad
  `(H : EndoFunctor F)
  `(A : @Functor.Applicative.Applicative _ _ (FromAFunctor H))
  `(Monad F) : Type :=
  Theory.Monad.Monad (ToAFunctor H).

Theorem Identity_IsMonad :
  IsMonad Identity_IsFunctor Identity_IsApplicative Identity_Monad.
Proof.
  construct; auto.
Qed.

Theorem arrow_IsMonad {x} :
  IsMonad arrow_IsFunctor arrow_IsApplicative (arrow_Monad x).
Proof.
  unfold arrow_Monad, arrow.
  construct; auto.
Qed.

Section Compose_Monad.

(*
If we have a monad [M] composed with an applicative [N], and we know that
   they distribute as in [N (M (N a)) ~> M (N a)], then the composition is
   also a monad.

--------
如果我们有一个由一个函子 [M] 与一个应用函子 [N] 组成的单子，并且我们知道它们按照 [N (M (N a)) ~> M (N a)] 分配，那么这个组合也是一个单子。
*)

Context `(HF : EndoFunctor F).
Context `(AF : @Functor.Applicative.Applicative _ _ (FromAFunctor HF)).
Context `(MF : @Theory.Monad.Monad _ (FromAFunctor HF)).
Context `(HG : EndoFunctor G).
Context `(AG : @Functor.Applicative.Applicative _ _ (FromAFunctor HG)).

(*
This is the essential condition, as explained by Mark P. Jones and Luc
   Duponcheel in their article “Composing monads”, Research Report
   YALEU/DCS/RR-1004, December 1993.

--------
这是基本条件，正如 Mark P. Jones 和 Luc Duponcheel 在他们的文章《Composing monads》中所解释的，研究报告 YALEU/DCS/RR-1004，1993 年 12 月。
*)
Context `{D : @Monad_Distributive _ _ (FromAFunctor HF) _ (FromAFunctor HG) _ AG}.

Definition EndoMonad_Distributes : Monad_Distributes F G :=
  @Monad.Distributive.mprod _ _ (FromAFunctor HF) _ (FromAFunctor HG) _ AG _.

Theorem Compose_IsMonad :
  IsMonad
    (Compose_IsFunctor HF HG)
    (Compose_IsApplicative HF AF HG AG)
    (@Compose_Monad
       _ (EndoMonad_Monad HF AF MF)
       _ (EndoApplicative_Applicative HG AG)
       EndoMonad_Distributes).
Proof.
  exact (@Monad_Compose _ _ _ _ _ _ _ D).
Qed.

End Compose_Monad.
