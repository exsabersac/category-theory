Require Import Category.Lib.

Generalizable All Variables.

(** The Semigroup type class (mappend/⊗), with its categorical reading / 半群类型类（mappend/⊗），及其范畴论解读 *)

(*
nLab: https://ncatlab.org/nlab/show/semigroup
   Wikipedia: https://en.wikipedia.org/wiki/Semigroup

   FP reading.  A semigroup (in the Haskell sense) is a type [m] equipped with
   a binary operation [mappend : m → m → m] (Haskell's [(<>)], here written
   [⊗]).  It is lawful when [⊗] is associative: [(x ⊗ y) ⊗ z ≈ x ⊗ (y ⊗ z)].
   Unlike a monoid there is no unit element; a [Monoid] (see Monoid.v) is a
   semigroup that additionally provides [mempty].  This class is ops-only:
   like [Functor] and [Foldable] in this directory, it carries the operation
   but not the law, so any [m : Type] with an associative [⊗] is an instance,
   and the associativity law is stated in prose rather than enforced.

   Categorical reading.  A semigroup is a set with an associative binary
   operation, i.e. an associative magma (a magma being a set with an arbitrary
   binary operation, not necessarily associative).  Equivalently it is a
   semigroup object in the cartesian monoidal category of sets — internalizing
   the same data and law in any monoidal category V yields a semigroup object
   in V.  It is also the hom-set of a one-object semicategory (semigroupoid):
   composition there is exactly [⊗] and associativity is its sole law, with no
   identity required.  Adding a unit recovers a monoid (a one-object
   category).

--------
nLab：https://ncatlab.org/nlab/show/semigroup
维基百科：https://en.wikipedia.org/wiki/Semigroup

函数式编程阅读。一个半群（在 Haskell 的意义上）是一个类型 [m]，配备有二元运算 [mappend : m → m → m]（Haskell 的 [(<>)]，这里写作 [⊗]）。当 [⊗] 是结合的时，它是合法的：[(x ⊗ y) ⊗ z ≈ x ⊗ (y ⊗ z)]。与幺半群不同，没有单位元素；一个 [Monoid]（参见 Monoid.v）是一个半群，此外还提供 [mempty]。这个类只是操作符类：像此目录下的 [Functor] 和 [Foldable] 一样，它携带运算但不携带规律，因此任何具有结合性 [⊗] 的 [m : Type] 都是其实例，而且结合律以文字形式陈述，而非强制执行。

范畴化阅读。半群是一个具有结合性二元运算的集合，即一个结合性幺半群（幺半群是一个具有任意二元运算的集合，不一定结合）。等价地，它是在集合的笛卡尔幺半范畴中的半群对象——在任何幺半范畴 V 中内部化相同的数据和律将得到 V 中的半群对象。它也是单对象半范畴（半群类）的 Hom 集合：那里的复合正是结合运算，其唯一的律是结合律，不需要单位。加入单位则得到幺半群（单对象范畴）。
*)

Class Semigroup (m : Type) := {
  mappend : m -> m -> m       (* the associative binary operation, written [⊗] / 结合二元运算，写作 [⊗] *)
}.

Arguments mappend {m _ } _ _.

Infix "⊗" := mappend (at level 40).
