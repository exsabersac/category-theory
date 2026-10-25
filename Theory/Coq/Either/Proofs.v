Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Functor.Proofs.
Require Import Category.Theory.Coq.Either.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(** Law proofs for the Either/sum [a + b] instances / Either/sum [a + b] 实例的法律证明 *)

(*
nLab: https://ncatlab.org/nlab/show/coproduct
   Wikipedia: https://en.wikipedia.org/wiki/Coproduct

   The instances themselves live in [Theory/Coq/Either.v]; here we record their
   lawfulness.  Fixing the left summand [E], the endofunctor [b ↦ E + b] is a
   genuine endofunctor on [Coq], and [Either_Functor : IsFunctor] discharges the
   two functor laws -- identity [fmap id = id] and composition
   [fmap (g ∘ f) = fmap g ∘ fmap f] -- by exhibiting it as an [AFunctor], exactly
   as the sibling [Maybe] and [Tuple] proof files do.  The three obligations are
   the [AFunctor] fields: [fmap] respects pointwise equality, and the identity
   and composition laws, each proven by case analysis on the [Left]/[Right] tag.

   Following the house pattern, only the [Functor] instance is proven lawful
   here; lawfulness of the applicative/monad structure is discharged per
   concrete use.

--------
nLab: https://ncatlab.org/nlab/show/coproduct
   维基百科: https://en.wikipedia.org/wiki/Coproduct

   实例本身存在于 [Theory/Coq/Either.v]；在这里我们记录它们的合法性。固定左侧加数 [E]，函子 [b ↦ E + b] 是 [Coq] 上的真正函子，并且 [Either_Functor : IsFunctor] 通过将其展示为 [AFunctor] 来履行两条函子律——恒等律 [fmap id = id] 和复合法 [fmap (g ∘ f) = fmap g ∘ fmap f]——正如其兄弟 [Maybe] 和 [Tuple] 证明文件所做的那样。三个义务是 [AFunctor] 字段：[fmap] 尊重逐点相等，以及恒等律和复合法，每一条都通过对 [Left]/[Right] 标签的案例分析来证明。

遵循本领域惯例，这里仅证明 [Functor] 实例是合法的；应用/单子结构的合法性根据具体使用情况来验证。
*)

Program Definition Either_Functor {E} : IsFunctor (@Either_Functor E) := {|
  a_fmap := @Either_Functor E;
|}.
Next Obligation.
  proper.
  simpl.
  now rewrite H.
Qed.
Next Obligation.
  destruct x0; simpl; congruence.
Qed.
Next Obligation.
  destruct x0; simpl; congruence.
Qed.
