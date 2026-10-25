Require Import Category.Lib.
Require Import Category.Theory.Coq.Semigroup.

Generalizable All Variables.

(** The Monoid type class (mempty/mappend), with its categorical reading / 幺半群类型类（mempty/mappend），及其范畴论解读 *)

(*
nLab: https://ncatlab.org/nlab/show/monoid
   Wikipedia: https://en.wikipedia.org/wiki/Monoid

   FP reading.  A monoid (in the Haskell sense) is a type [m] with an
   associative binary operation [mappend] (Haskell's [(<>)], here written
   [⊗] and inherited from the [Semigroup] superclass) together with a unit
   element [mempty] (Haskell's [mempty]).  It is lawful when [⊗] is
   associative and [mempty] is a two-sided identity:
   [mempty ⊗ x ≈ x] and [x ⊗ mempty ≈ x].  A [Monoid] is thus exactly a
   [Semigroup] (see Semigroup.v) that additionally provides the unit; like
   [Semigroup], [Functor], and [Foldable] in this directory this class is
   ops-only, carrying [mempty] but not the laws, so any [m : Type] with an
   associative [⊗] and a unit is an instance and the monoid laws are stated
   in prose rather than enforced.

   Categorical reading.  A monoid is a set with an associative binary
   operation and a unit, i.e. the hom-set of a one-object category:
   composition is [⊗], the identity arrow is [mempty], and the category laws
   are exactly associativity and the unit laws.  Equivalently it is a monoid
   object in the cartesian monoidal category of sets — internalizing the same
   data and laws in any monoidal category V yields a monoid object in V.

   This is the FP/Haskell-style monoid type class on a Coq type, and is
   DISTINCT from Theory/Algebra/Monoid.v, which defines the monoid OBJECT
   internal to an arbitrary monoidal category (an object X with morphisms
   mu : X ⨂ X ~> X and eta : I ~> X).  The present file is the special case
   of that notion in (Set, ×): a monoid object in Set is an ordinary monoid,
   and that ordinary monoid is what this class describes.

--------
nLab：https://ncatlab.org/nlab/show/monoid
维基百科：https://en.wikipedia.org/wiki/Monoid

FP 阅读。一个单子（在 Haskell 的意义上）是一个类型 [m]，具有结合的二元操作 [mappend]（Haskell 的 [(<>)]，这里写作 [⊗] 并继承自 [Semigroup] 超类）以及一个单位元素 [mempty]（Haskell 的 [mempty]）。当 [⊗] 是结合的并且 [mempty] 是双边单位时，它是合法的：[mempty ⊗ x ≈ x] 和 [x ⊗ mempty ≈ x]。因此，一个 [Monoid] 正好是一个 [Semigroup]（参见 Semigroup.v），它额外提供了单位；像这个目录中的 [Semigroup]、[Functor] 和 [Foldable] 一样，该类只包含操作，携带 [mempty] 但不包含定律，因此任何具有结合的 [⊗] 和单位的 [m : Type] 都是其实例，单子定律以文字形式陈述而不是强制执行。

范畴视角阅读。一个幺半群是一个具有结合二元运算和单位元的集合，即一个单对象范畴的同态集：复合为 [⊗]，恒等箭头为 [mempty]，范畴定律恰好是结合律和单位元律。等价地，它是在笛卡尔幺半群范畴 Set 中的幺半群对象——在任何幺半群范畴 V 中对同样的数据和定律进行内部化会得到 V 中的幺半群对象。

这是在 Coq 类型上使用的 FP/Haskell 风格的幺半群类型类，与 Theory/Algebra/Monoid.v 完全不同，后者定义了任意单体范畴内部的幺半群对象（一个对象 X 及其态射 mu : X ⨂ X ~> X 和 eta : I ~> X）。本文件是该概念在 (Set, ×) 中的特殊情况：Set 中的幺半群对象就是一个普通的幺半群，而普通幺半群就是该类描述的内容。
*)

Class Monoid `{Semigroup m} := {
  mempty : m                   (* the unit element, Haskell's [mempty] / 单位元素，Haskell 的 [mempty] *)
}.

Arguments Monoid m {_}.
