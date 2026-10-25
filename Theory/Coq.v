Require Import Category.Lib.

(*
   【Theory/Coq 衔接展开】/ Bridge walkthrough（薄）

   1) 本文件做什么 / Role
      聚合再导出 Theory/Coq/*：在 Coq 的 Type（「类型范畴」）上直接写
      Haskell 风格 Functor/Applicative/Monad/…，并标明与本库范畴定义的对应。
      Re-exports the Type-level FP tower and ties each class to its categorical twin.

   2) 宇宙/衔接直觉 / Universes & bridge
      Instance/Coq.v 等把 Type 做成 Category；此处类是「程序员 API」，
      定律在 Proofs 子模块，范畴侧在 Theory/Functor、Monad、Applicative 等。
      Type-as-category lives in Instance/Coq; this is the programmer-facing API.

   3) 阅读顺序 / Reading
      本聚合 → Theory/Coq/Functor → Applicative → Monad；对照 Functor.v / Monad.v。
      Start here → Coq/Functor → Applicative → Monad; compare with categorical files.
*)

(** Aggregator for the applied functional-programming layer over Coq types / 针对 Coq 类型的应用函数式编程层的聚合器 *)

(*
This module re-exports the [Theory/Coq/] cluster, which develops the
   familiar Haskell-style type classes directly over Coq types (the "category
   of types") and connects each one to its categorical counterpart.  Importing
   this single module brings the whole applied-FP layer into scope.

   The exported modules fall into two groups.  The functor/applicative/monad
   tower, with traversals over it:

     - Functor       (fmap)            ↔ endofunctor on the category of types
     - Applicative   (pure/ap)         ↔ lax monoidal endofunctor
     - Monad         (ret/bind)        ↔ monad (endofunctor with unit/mult)
     - Foldable      (foldr/foldMap)
     - Traversable   (traverse)        ↔ traversal through an applicative

   And the algebraic structures and concrete instances those classes act on:

     - Semigroup     (associative <>)
     - Monoid        (Semigroup with unit)
     - Maybe, Either, Tuple, List, Map  (concrete functor/monad instances)

   The per-module [Proofs] submodules under [Theory/Coq/] are auxiliary and
   are deliberately not re-exported here.

--------
本模块再导出 [Theory/Coq/] 簇，在 Coq 类型（「类型范畴」）上直接开发熟悉的
   Haskell 风格类型类，并把每一类连到其范畴对应物。导入本单一模块即可把整个
   应用 FP 层纳入作用域。

   导出模块分两组。函子/applicative/单子塔及其上的遍历：

     - Functor       (fmap)            ↔ 类型范畴上的自函子
     - Applicative   (pure/ap)         ↔ 松弛幺半自函子
     - Monad         (ret/bind)        ↔ 单子（带单位/乘法的自函子）
     - Foldable      (foldr/foldMap)
     - Traversable   (traverse)        ↔ 经 applicative 的遍历

   以及这些类所作用的代数结构与具体实例：

     - Semigroup     （结合的 <>）
     - Monoid        （带单位的 Semigroup）
     - Maybe, Either, Tuple, List, Map  （具体函子/单子实例）

   [Theory/Coq/] 下各模块的 [Proofs] 子模块是辅助性的，故意不在此再导出。
*)

(*
Why the tower exists, and what a categorical footing buys

   nLab:  https://ncatlab.org/nlab/show/monad+(in+computer+science)
   nLab:  https://ncatlab.org/nlab/show/applicative+functor
   Paper: Moggi, "Notions of Computation and Monads", Information and
          Computation 93(1):55-92, 1991
   Paper: McBride, Paterson, "Applicative programming with effects",
          Journal of Functional Programming 18(1):1-13, 2008
   Paper: Jaskelioff, Rypáček, "An Investigation of the Laws of
          Traversals", MSFP 2012, EPTCS 76 (arXiv 1202.2919)

   Each class re-exported here was discovered as the programming shadow of
   a categorical structure that predates it.  The aggregator deliberately
   records those correspondences, so that the informal type-class laws
   acquire a precise categorical meaning rather than living only in
   documentation.

   The monad layer is the oldest.  Moggi recognized that the common
   computational effects — state, exceptions, nondeterminism,
   continuations, reader and writer — are modelled uniformly by a strong
   monad on a cartesian closed category: T x is the type of computations
   returning x, the unit is the effect-free computation, and the
   multiplication is sequential composition (Moggi, "Computational
   Lambda-Calculus and Monads", LICS 1989; "Notions of Computation and
   Monads", 1991).  Wadler carried this into program structure and made
   the Kleisli-triple presentation familiar, whence the return and bind
   that [Monad] presents as [ret] and [bind] (Wadler, "The Essence of
   Functional Programming", POPL 1992; "Monads for Functional
   Programming", Marktoberdorf 1992).

   Applicative functors arrived later and from the other direction.
   McBride and Paterson coined the "idiom" — an abstraction weaker than a
   monad, and for that reason more widely applicable — gave it [pure] and
   [ap], and closed their paper by naming the structure: an applicative is
   a lax monoidal functor equipped with a tensorial strength (McBride,
   Paterson, 2008; nLab).  Over a closed symmetric monoidal base [pure] is
   the unit and [liftA2] the laxator, so the four applicative laws are
   lax-monoidal coherence.  Structure/Monoidal.v is the semantic anchor,
   Functor/Applicative.v the law-bearing counterpart, and Functor/Strong.v
   the strength that recovers [ap] from the laxator.

   Traversals were named in the same paper — a [Traversable] functor
   distributes over every applicative — but stated no laws.  Gibbons and
   Oliveira read [traverse] as the Iterator pattern, one combinator that
   maps and accumulates at once, gave the first axioms, and exposed bad
   traversals that skip or duplicate elements (Gibbons, Oliveira, "The
   Essence of the Iterator Pattern", JFP 2009).  Jaskelioff and Rypáček
   then settled the account with three laws — naturality in the
   applicative, unitarity, linearity — that hold for the finitary
   containers, the largest known class of traversable functors, and that
   rule out the bad traversals (Jaskelioff, Rypáček, 2012).  Those three
   laws are what Functor/Traversable.v carries and [traverse] here states
   without proof.

   That the three classes even form a tower was itself settled late.
   [Functor] before [Applicative] before [Monad] became a superclass
   requirement only in GHC 7.10, with the Applicative-Monad Proposal of
   2015; before it the identities relating the layers — [fmap] with liftM,
   [pure] with return, [ap] with the monad's own ap — went unstated, and
   this cluster is organized along that same settled chain (HaskellWiki,
   "Functor-Applicative-Monad Proposal").

   The categorical footing is what makes the correspondences carry weight.
   Because the language can neither state nor enforce the laws, a lawless
   [Applicative] or [Traversable] allows nonsense instances, the bad
   traversals among them; routing each class through its monoidal or
   distributive-law semantics is what forbids those instances, and the
   law-bearing modules under Functor/ carry the coherence proofs the
   classes here only assert.  The remaining exports supply the base and
   the witnesses.  [Semigroup] and [Monoid] are the monoid object of
   Theory/Algebra/Monoid.v specialized to (Set, ×), over which
   [Foldable]'s [foldr] is the list catamorphism — the unique monoid
   homomorphism out of the free monoid — realized through
   Instance/Coq/Lists.v and Theory/Recursion.v, while
   Instance/Coq/Applicative.v and Instance/Coq/Monad.v exhibit the bridge
   as honest categorical instances over the Coq-types category.

--------
为什么这座塔存在，以及分类基础能带来什么

nLab: https://ncatlab.org/nlab/show/monad+(in+computer+science)
nLab: https://ncatlab.org/nlab/show/applicative+functor
论文: Moggi, “计算和单子概念”, 信息与计算 93(1):55-92, 1991
论文: McBride, Paterson, “带副作用的应用式编程”, 函数式编程期刊 18(1):1-13, 2008
论文: Jaskelioff, Rypáček, “遍历定律的研究”, MSFP 2012, EPTCS 76 (arXiv 1202.2919)

这里重新导出的每个类都是作为早于它的范畴结构的编程影子被发现的。聚合器故意记录这些对应关系，以便非正式的类型类法则获得精确的范畴意义，而不仅仅存在于文档中。

单子层是最古老的。Moggi 认识到，常见的计算效应——状态、异常、非确定性、延续、读取器和写入器——在笛卡尔闭范畴上由一个强单子统一建模：T x 是返回 x 的计算类型，单位是无效应的计算，乘法是序列组合（Moggi，《计算λ演算与单子》，LICS 1989；《计算概念与单子》，1991）。Wadler 将其引入程序结构，并使 Kleisli 三元组的表示为人所熟知，从而 [Monad] 所表示的 return 和 bind 分别成为 [ret] 和 [bind]（Wadler，《函数式编程的精髓》，POPL 1992；《函数式编程的单子》，Marktoberdorf 1992）。

应用函子后来出现，并且来自另一个方向。McBride 和 Paterson 创造了“成语”（idiom）——一种比单子更弱的抽象，因此适用范围更广——并给它命名为 [pure] 和 [ap]，并在他们的论文结尾命名了这一结构：一个应用函子是一个带有张量强度的宽松幺半群函子（McBride, Paterson, 2008; nLab）。在一个闭对称幺半群基上，[pure] 是单位，[liftA2] 是宽松算子，因此四条应用函子定律是宽松-幺半群一致性。Structure/Monoidal.v 是语义锚点，Functor/Applicative.v 是承载定律的对应部分，而 Functor/Strong.v 是从宽松算子恢复 [ap] 的强度。

遍历在同一篇论文中被命名——一个 [Traversable] 函子会分配到每个应用函子上——但没有陈述任何定律。Gibbons 和 Oliveira 将 [traverse] 解释为迭代器模式，一个同时进行映射和累加的组合子，给出了第一个公理，并揭示了那些跳过或重复元素的错误遍历（Gibbons, Oliveira, “The Essence of the Iterator Pattern”, JFP 2009）。随后 Jaskelioff 和 Rypáček 通过三条定律——在应用函子中的自然性、单位性、线性——解决了这个问题，这些定律适用于有限容器，这是已知的最大可遍历函子类，并且排除了错误的遍历（Jaskelioff, Rypáček, 2012）。这三条定律就是 Functor/Traversable.v 所拥有的，而 [traverse] 在此陈述了这些定律但未给出证明。

三个类甚至能形成一个层级本身也是很晚才确定的。在 GHC 7.10 之前，[Functor] 在 [Applicative] 之前，在 [Monad] 成为超类要求之前，仅在 2015 年的 Applicative-Monad 提案中提出；在此之前，关联各层的恒等式——[fmap] 与 liftM，[pure] 与 return，[ap] 与 monad 自身的 ap——都没有明确说明，而这个类簇是沿着同样确定的链条组织起来的 (HaskellWiki，“Functor-Applicative-Monad Proposal”)。

范畴基础正是使对应关系具备分量的原因。因为语言既不能陈述也不能强制法律，所以一个无律的 [Applicative] 或 [Traversable] 允许荒谬的实例，它们之间产生不良的遍历；通过各个类走它们的幺半群或分配律语义，正是禁止这些实例的方式，而在 Functor/ 下承载法律的模块则携带了这些类在此仅声明的相干性证明。其余的导出提供了基础和证人。[Semigroup] 和 [Monoid] 是 Theory/Algebra/Monoid.v 中专门针对 (Set, ×) 的幺半群对象，其中 [Foldable] 的 [foldr] 是列表 catamorphism —— 从自由幺半群唯一的幺半群同态 —— 通过 Instance/Coq/Lists.v 和 Theory/Recursion.v 实现，而 Instance/Coq/Applicative.v 和 Instance/Coq/Monad.v 则展示了作为 Coq 类型范畴上真实范畴实例的桥接。
*)

Require Export Category.Theory.Coq.Applicative.
Require Export Category.Theory.Coq.Either.
Require Export Category.Theory.Coq.Foldable.
Require Export Category.Theory.Coq.Functor.
Require Export Category.Theory.Coq.List.
Require Export Category.Theory.Coq.Map.
Require Export Category.Theory.Coq.Maybe.
Require Export Category.Theory.Coq.Monad.
Require Export Category.Theory.Coq.Monoid.
Require Export Category.Theory.Coq.Semigroup.
Require Export Category.Theory.Coq.Traversable.
Require Export Category.Theory.Coq.Tuple.
