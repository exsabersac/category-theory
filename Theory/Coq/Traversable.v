Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Applicative.

Generalizable All Variables.

(** The Traversable type class (sequence/traverse), with its categorical reading / 可遍历类型类（序列/遍历），及其范畴学解释 *)

(*
nLab: https://ncatlab.org/nlab/show/distributive+law
   nLab: https://ncatlab.org/nlab/show/applicative+functor

   No dedicated nLab or Wikipedia page exists for "traversable functor": the
   nLab pages above are the closest (a traversable functor is precisely a
   functor carrying a distributive law over every applicative functor), and
   the Haskell-level account lives on the HaskellWiki / Wikibooks rather than
   in the Wikipedia main namespace
   (https://wiki.haskell.org/Foldable_and_Traversable).

   FP reading.  A traversable functor (in the Haskell sense) is a type
   constructor [T : Type → Type] that can be walked left-to-right while
   running an effect on each element, commuting [T] past any applicative
   functor [F].  The defining operation is
     [traverse : (x → F y) → T x → F (T y)],
   and the equivalent "no-op visitor" form recorded here is
     [sequence : T (F x) → F (T x)]   (Haskell's [sequenceA]).
   The two are interdefinable: [traverse f = sequence ∘ fmap f] and
   [sequence = traverse id].  Lawful instances satisfy three laws (with [η] the
   applicative-transformation / natural-transformation operations):
     naturality    [η ∘ traverse f ≈ traverse (η ∘ f)] for [η] an applicative
                   transformation;
     identity      [traverse Identity ≈ Identity] (the identity applicative);
     composition   [traverse (Compose ∘ fmap g ∘ f)
                      ≈ Compose ∘ fmap (traverse g) ∘ traverse f].
   A lawful [Traversable] is automatically a [Functor] ([fmap] = traverse with
   the identity applicative) and [Foldable] ([foldMap] = traverse with a
   constant applicative).

   Categorical reading.  Following McBride–Paterson, a traversable functor is a
   functor [T : C → C] equipped with a distributive law
     [δ_F : T ◯ F ⟹ F ◯ T]
   natural in the applicative functor [F] (a lax monoidal endofunctor with
   tensorial strength on the category of Coq types); equivalently a coalgebra
   for a parameterised comonad.  The three laws above are the coherence axioms
   making [δ] respect applicative transformations, the identity applicative,
   and applicative composition, so that [Traversable] functors form a monoidal
   category under composition.  By the Representation Theorem (Bird–Gibbons;
   Jaskelioff–O'Connor 2012) the lawful traversable functors on Set are
   exactly the finitary containers (sums of finite products), and that single
   theorem is equivalent to the conjunction of the three laws.

   As is usual for these Coq/Haskell-style classes, the laws are NOT recorded
   as fields here; [Traversable] carries only the [sequence] operation, and
   lawfulness is an obligation discharged for each concrete instance.  The
   fully categorical, law-bearing counterpart lives in
   [Category.Functor.Traversable].

--------
nLab：https://ncatlab.org/nlab/show/distributive+law
 nLab：https://ncatlab.org/nlab/show/applicative+functor

不存在专门用于“可遍历函子”的 nLab 或维基百科页面：
 上面的 nLab 页面是最接近的（可遍历函子恰好是
 函子在每个应用函子上都遵循分配律），并且
 Haskell 级别的帐户位于 HaskellWiki / Wikibooks 上，而不是
 在维基百科主命名空间中
 （https://wiki.haskell.org/Foldable_and_Traversable).

FP 阅读。 可遍历函子（在 Haskell 意义上）是一种类型
 构造函数 [T : Type → Type] 可以从左到右行走
 对每个元素运行效果，使 [T] 超越任何应用程序
 函子 [F]。 定义操作是
 [traverse : (x → F y) → T x → F (T y)]，
 此处记录的等效“无操作访问者”形式是
 [sequence : T (F x) → F (T x)]（Haskell 的 [sequenceA]）。 
两者是可以相互定义的：[traverse f = sequence ∘ fmap f] 和
 [sequence = traverse id]。 合法实例满足三个定律（[η]
 应用变换/自然变换操作）：
 自然性 [η ∘ traverse f ≈ traverse (η ∘ f)] 为 [η] 的一个应用程序
 转型；
 恒等 [traverse Identity ≈ Identity]（恒等应用程序）；
 组合[遍历（Compose ∘ fmap g ∘ f）
 ≈ 组合 ∘ fmap (遍历 g) ∘ 遍历 f]。 
合法的 [Traversable] 自动成为 [Functor]（[fmap] = 遍历
 恒等应用）和 [Foldable]（[foldMap] = 使用
 常数适用）。

分类阅读。 遵循 McBride–Paterson，可遍历函子是
 配备分配律的函子 [T : C → C]
 保护18X
 在应用函子 [F] 中自然存在（一个松散的幺半群内函子，
 Coq 类型范畴的张量强度）； 相当于一个余代数
 对于参数化的 comonad。 上述三个定律是相干公理
 使 [δ] 尊重应用变换、恒等应用、
 和应用组合，使 [Traversable] 函子形成幺半群
 构成下的范畴。 通过表示定理（Bird-Gibbons；
 Jaskelioff–O'Connor 2012) Set 上的合法可遍历函子是
 正是有限容器（有限乘积之和），并且单个
 定理等价于三个定律的合取。

对于这些 Coq/Haskell 风格的类来说，通常不会记录这些定律
 作为此处的字段； [Traversable] 仅承载 [sequence] 操作，并且
 合法性是针对每个具体情况履行的义务。 的
 完全绝对的、遵守法律的对应物生活在
 [Category.Functor.Traversable]。
*)

Class Traversable@{d c} {T : Type@{d} → Type@{c}} :=
  (* the distributive law T ◯ F ⟹ F ◯ T for any applicative F (Haskell's [sequenceA]) / 对于任何函子 F，分配律 T ◯ F ⟹ F ◯ T（Haskell 的 [sequenceA]） *)
  sequence : ∀ `{Applicative@{d c} F} {x : Type@{d}}, T (F x) → F (T x).

Arguments Traversable : clear implicits.

(*
[Tupersable] is a project-specific specialization of [Traversable] to a
   pairing (writer-style) shape [x * -]: it sequences [T] past the tuple
   functor without requiring the carrier [x] to be [Applicative], by simply
   threading the seed value [a : x] through.  There is no standard name for
   this class; it is the traversal whose "applicative" is the (non-applicative)
   writer-shaped functor [λ y, x * y].  Like the other classes here it is
   lawless, recording only the [sequenceT] operation.

--------
[Tupersable] 是 [Traversable] 的项目特定专门化，用于配对（writer 风格）形状 [x * -]：它将 [T] 序列化经过元组函子而不需要载体 [x] 是 [Applicative]，只需通过线程化种子值 [a : x] 即可。这个类没有标准名称；它是其“适用性”是（非适用性）writer 型函子 [λ y, x * y] 的遍历。像这里的其他类一样，它不受约束，只记录 [sequenceT] 操作。
*)

Class Tupersable@{d c} {x : Type@{d}} {T : Type@{d} → Type@{c}} := {
  (* sequence T past the writer-shaped tuple functor, seeded by [a : x] / 序列 T 经过作家形元组函子，由 [a : x] 种子化 *)
  sequenceT {y : Type@{d}} (a : x) : T (x * y)%type → x * T y
}.

Arguments Tupersable : clear implicits.
