Require Import Category.Lib.

Generalizable All Variables.

(** The Foldable type class (foldr), with its categorical reading / 可折叠类型类（foldr），及其范畴论的解读 *)

(*
Wikipedia: https://en.wikipedia.org/wiki/Fold_(higher-order_function)
   nLab: https://ncatlab.org/nlab/show/monoid

   No dedicated nLab or Wikipedia page exists for "Foldable": the Wikipedia
   "fold" page above covers the underlying right fold, and the monoid page is
   the closest categorical reference (see the categorical reading below).  The
   Haskell-level account of the class lives on the HaskellWiki / Wikibooks
   rather than in the Wikipedia main namespace
   (https://wiki.haskell.org/Foldable_and_Traversable).

   FP reading.  A foldable container (in the Haskell sense) is a type
   constructor [F : Type → Type] whose elements can be collapsed left-to-right
   into a single summary value.  The defining operation recorded here is the
   right fold
     [foldr : (x → y → y) → y → F x → y],
   which threads a combining function [x → y → y] and an initial value [y]
   through the contents of [F x] — exactly Haskell's
   [foldr :: (a → b → b) → b → t a → b], with the element supplied first to
   the combining step.  The other members of the Haskell class ([foldMap],
   [fold], [toList], [length], …) are all derivable from this one operation;
   in particular [foldMap f] is [foldr (mappend ∘ f) mempty] and [fold] is
   [foldMap id], mapping each element into a monoid and combining.

   Categorical reading.  Folding is the universal property of the free monoid.
   The canonical foldable container is the list functor [L : Type → Type],
   which is the free-monoid (free-monad) functor on the category of types:
   [L x = ∐ₙ xⁿ].  A right fold [foldr (⊗) e] over a list is precisely the
   unique monoid homomorphism out of the free monoid [L x] determined, by that
   universal property, by the choice of where to send generators together with
   a target monoid structure ([⊗], [e]); equivalently it is the structure map
   of an [L]-algebra, so [foldr] is the catamorphism (fold) for the list (or,
   in general, the underlying container) functor.  More precisely, the
   category of foldable functors is the slice over the free-monoid functor
   [L]: a [Foldable F] is a functor [F] equipped with a natural way to send
   each [F x] into the free monoid [L x] (its [toList]), after which any fold
   factors through that map into an arbitrary monoid.  The monoid page above
   gives the target structure; [mempty]/[mappend] (see Monoid.v, Semigroup.v)
   supply the [e]/[⊗] that a fold consumes.

   As is usual for these Coq/Haskell-style classes, this class is ops-only,
   like [Functor], [Semigroup], and [Monoid] in this directory: it carries the
   [foldr] operation but records no laws, so any [F] with such an operation is
   an instance, and any laws (e.g. agreement of [foldr]/[foldMap], or that
   [toList] is a monoid action) are stated in prose rather than enforced.

--------
维基百科：https://en.wikipedia.org/wiki/Fold_(higher-order_function)
 nLab：https://ncatlab.org/nlab/show/monoid

不存在专门用于“可折叠”的 nLab 或维基百科页面：维基百科
 上面的“折叠”页面覆盖了底层的右折叠，而幺半群页面是
 最接近的分类参考（请参阅下面的分类阅读）。 的
 该类的 Haskell 级别说明位于 HaskellWiki / Wikibooks 上
 而不是在维基百科主命名空间中
 (https://wiki.haskell.org/Foldable_and_Traversable).

FP 阅读。 可折叠容器（在 Haskell 意义上）是一种类型
 构造函数 [F : Type → Type] 其元素可以从左到右折叠
 转化为单个汇总值。 这里记录的定义操作是
 右折
 [foldr : (x → y → y) → y → F x → y]，
 其中线程组合函数 [x → y → y] 和初始值 [y]
 通过 [F x] 的内容 — 正是 Haskell 的内容
 [foldr :: (a → b → b) → b → t a → b]，首先提供的元件
 合并步骤。 Haskell 类的其他成员（[foldMap]、
 [fold]、[toList]、[length]，...）都可以从这一操作中衍生出来；
 特别是 [foldMap f] 是 [foldr (mappend ∘ f) mempty]，[fold] 是
 [foldMap id]，将每个元素映射到一个幺半群并组合。

分类阅读。 折叠是自由幺半群的通用属性。 
规范的可折叠容器是列表函子 [L : Type → Type]，
 这是类型范畴上的自由幺半群 (free-monad) 函子：
 [L x = ∐ₙ xⁿ]。 在列表上右折叠 [foldr (⊗) e] 正是
 由自由幺半群 [L x] 确定的独特幺半群同态，由
 通用属性，通过选择将发电机发送到何处
 目标幺半群结构（[⊗]、[e]）； 等效地它是结构图
 [L] 代数的一个，所以 [foldr] 是列表的变形（折叠）（或者，
 一般来说，底层容器）函子。 更准确地说，
 可折叠函子的范畴是自由幺半群函子上的切片
 [L]：[Foldable F] 是函子 [F]，配备自然发送方式
 每个 [F x] 进入自由幺半群 [L x]（其 [toList]），之后任何折叠
 通过该映射分解为任意幺半群。 上面的幺半群页面
 给出目标结构； [mempty]/[mappend]（参见 Monoid.v、Semigroup.v）
 供应折叠消耗的[e]/[⊗]。

与这些 Coq/Haskell 风格的类一样，该类仅用于操作，
 例如此目录中的 [Functor]、[Semigroup] 和 [Monoid]：它携带
 [foldr] 操作但没有记录任何规律，因此任何具有此类操作的 [F]
 实例和任何法律（例如 [foldr]/[foldMap] 的协议，或
 [toList] 是一个幺半群动作）以散文形式表述而不是强制执行。
*)

Class Foldable@{d c} {F : Type@{d} → Type@{c}} :=
  foldr : ∀ {x y : Type@{d}}, (x -> y -> y) -> y -> F x -> y.
                              (* combining step, seed, container, summary / 组合步骤，种子，容器，总结 *)

Arguments Foldable : clear implicits.
