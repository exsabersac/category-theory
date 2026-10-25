Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Instance.Sets.Cocartesian.

Generalizable All Variables.

Import EqNotations.

(* * * Small products and coproducts in [Sets] / * * [Sets] 中的小型产品和副产品 *)

(*
 nLab:      https://ncatlab.org/nlab/show/product
 nLab:      https://ncatlab.org/nlab/show/coproduct
 nLab:      https://ncatlab.org/nlab/show/complete+category
 Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)
 Wikipedia: https://en.wikipedia.org/wiki/Coproduct

 Sources transposed here, all cited BY LOCATION; the printed text of none of
 the three books was consulted while writing this file.  The one-line
 descriptions below are transcribed from the catalog entries of issue #254,
 not from the books:

 - Mac Lane, "Categories for the Working Mathematician", 2nd ed.
 (Springer GTM 5), section I.6, printed p. 24, exercises 1 and 2.  The
 exercises are the set-theoretic statement that a universe is closed
 under small cartesian products and small unions.  Their categorical
 transposition is this file: [Sets] at level [o] has products and
 coproducts of families indexed by any type at level [o] -- [o] being
 the universe of the carriers of [Sets]' objects, per the universe
 discipline recorded below.
 - Mac Lane, same book, section III.4, printed p. 72, exercise 2: the
 J-indexed cartesian product with its projections is the categorical
 product in Set.  That is [Sets_HasIndexedProducts] below.  (The same
 exercise also asks for the description in Top; see SCOPE, below.)
 - Awodey, "Category Theory", 1st ed. (Carnegie Mellon pre-print,
 September 2005), section 2.9 exercise 7, printed p. 56, parts (a) and
 (b).  Part (a) -- the universal property of an I-indexed product -- is
 already in the tree as [IsIndexedProduct], Structure/Limit/Product.v.
 Part (b) -- the function set X^I satisfies it for the constant family
 -- is [Sets_exponent_IsIndexedProduct] and
 [Sets_constant_iprod_exponent] below.
 - Riehl, "Category Theory in Context", 2nd ed., section 3.2, printed
 p. 94, example 5: the product of a J-indexed family of sets is the set
 of J-tuples.  Here an element of [Sets_iprod_obj F] literally IS a
 J-tuple, the dependent function [∀ i : A, F i].

 WHAT IS CONSTRUCTED

 [Sets_iprod_obj F]    carrier [∀ i : A, F i], with [g ≈ h] pointwise;
 [Sets_icoprod_obj F]  carrier [{ i : A & F i }], with [(i; x) ≈ (j; y)]
 iff some [e : i = j] carries [x] to a value
 equivalent to [y].

 [Sets_HasIndexedProducts] and [Sets_HasIndexedCoproducts] package these
 with their projections/injections and universal properties.  Before this
 file the tree had no [HasIndexedProducts] instance at any category, and no
 [HasIndexedCoproducts] vocabulary at all.

 WHAT THIS DOES NOT SETTLE ELSEWHERE

 Theory/WeaklyInitial.v takes its two products as explicit hypotheses
 "rather than harvested from a [Complete] / [HasIndexedProducts] instance",
 and that note is NOT a record of the absence just described: its reason is
 a universe one, and it survives an instance existing.  The second of its
 two products ranges over a hom-type, so "routing it through a class that
 quantifies over every index [Type] would over-commit the ambient
 universes", whereas the explicit form "leaves the smallness of the index
 (hence the relevant universe constraints) in the caller's hands".  Nothing
 below changes that, and the note stands as written.

 At [Sets], though, the obstacle it guards against is absent, and
 [Sets_endo_iprod] / [Sets_endo_iprod_ump] below record the fact: the
 endomorphism-indexed product of [P] with itself is supplied by
 [Sets_HasIndexedProducts], with its universal property, at the very same
 [Sets] --

 Sets_endo_iprod@{u u0} : obj[Sets@{u0 u}] → obj[Sets@{u0 u}]
 ( * with u0 < u * )

 -- no second [Sets] and no universe growth, because [Sets]' hom-type sits
 at exactly the index universe the instance accepts.  That is an observation
 about [Sets] alone; for an arbitrary category the hom universe need not sit
 where the class puts the index, which is the case the explicit hypotheses
 of Theory/WeaklyInitial.v exist to cover.

 THE UNIVERSE DISCIPLINE, WHICH IS THE POINT OF THE EXERCISE

 [Sets@{o so} : Category@{so o o}] (Instance/Sets.v): its objects are
 [SetoidObject@{o o}], whose carriers live at [Type@{o}], and its homs also
 live at [Type@{o}].  A dependent function type [∀ i : A, F i] over
 [A : Type@{u}] lands at [Type@{max(u,o)}], so it is a carrier of an object
 of [Sets@{o so}] exactly when [u <= o]; likewise [{ i : A & F i }].  The
 smallness side condition of Mac Lane I.6 is therefore, in this
 development, the universe level of the index type, and it is not imposed by
 hand -- it is what universe inference records.

 [HasIndexedProducts] of Structure/Limit/Product.v quantifies its index
 as [{A : Type}], and under the library's [Set Universe Polymorphism]
 (Lib.v) that [Type] is a universe PARAMETER of the class, not a quantifier
 over all universes.  Printing the class shows the three parameters, one per
 field:

 HasIndexedProducts@{u u0 u1 u2 u3 u4} (C : Category@{u3 u4 u4})
 { indexed_product      : ∀ A : Type@{u},  ...
 indexed_product_proj : ∀ A : Type@{u0}, ...
 indexed_product_ump  : ∀ A : Type@{u1}, ... }

 so the class as literally stated CAN be instantiated at [Sets], with those
 three universes taken to be [o].  That is what happens here;
 [About Sets_HasIndexedProducts] prints

 Sets_HasIndexedProducts@{u u0} : HasIndexedProducts@{u0 u0 u0 u0 u u0}
 Sets@{u0 u}     ( * with u0 < u * )

 -- [u0] is [o] and [u] is [so], the three index universes are all [u0], and
 the ambient [Category@{u3 u4 u4}] is [Category@{u u0 u0}], which is
 [Sets@{u0 u}].  There is no separate index universe variable to
 instantiate: the index universe is [o], the universe of the CARRIERS of
 [Sets]' objects -- the level at which the small sets themselves live.  It
 is NOT [so], the universe of [obj[Sets]], which is where [Sets] qua
 [Category@{so o o}] keeps its objects and which sits strictly above [o];
 indexing by [obj[Sets]] is exactly what the next paragraph shows to be
 rejected.  The coproduct instance is the same story through
 [Structure/Limit/Coproduct.v]'s definitional dual:

 Sets_HasIndexedCoproducts@{u u0} : HasIndexedCoproducts@{u u0 u0 u u0}
 Sets@{u0 u}   ( * with u0 < u * )

 where [Print HasIndexedCoproducts] shows [u0] in the second position to be
 the index universe and [Category@{u2 u3 u3}] with [u2 := u], [u3 := u0] to
 be [Sets].

 No universe-constrained VARIANT of the class was introduced: the instances
 above inhabit [Structure/Limit/Product.v]'s [HasIndexedProducts] itself.

 The condition bites in the expected direction.  Applying [indexed_product]
 at an index type one universe up -- [SetoidObject@{o o}] itself, which is
 [Type@{o+1}] -- is rejected by the elaborator with a universe
 inconsistency.  This was checked outside the tree rather than recorded as a
 command here, so that the [make todo] scan stays clean; a reader can
 reproduce it with

 Definition big@{o so}
 (F : SetoidObject@{o o} -> SetoidObject@{o o}) : SetoidObject@{o o} :=
 @indexed_product Sets@{o so} Sets_HasIndexedProducts@{so o}
 (SetoidObject@{o o}) F.

 which reports that [SetoidObject@{o o}] "has type Type@{o+1} while it is
 expected to have type Type@{o}".  Why a bound of this kind must exist at
 all is not argued here; Structure/Complete.v records Freyd's theorem
 that a category with products of families as large as its own morphism set
 is a preorder.

 NO FUNCTION EXTENSIONALITY

 Two elements of [Sets_iprod_obj F] are identified when they agree at every
 index up to the codomain's own [≈].  That is extensional equality of
 dependent functions realised as the object's chosen equivalence rather than
 as an axiom, exactly the move Instance/Sets.v makes for the hom-setoid.
 Nothing here appeals to [funext], choice, or [UIP]: the coproduct
 equivalence transports along an equality of indices and every proof about
 it proceeds by destructing that equality.  [Print Assumptions] reports
 "Closed under the global context" for every constant in this file; the
 Makefile's [print-assumptions] target audits the headline ones.

 WHICH EXISTING CONSTANTS DO THE WORK

 Reused unchanged: [IsIndexedProduct] and [HasIndexedProducts]
 (Structure/Limit/Product.v); [Sets], [SetoidObject],
 [SetoidMorphism] (Instance/Sets.v); [eq_Setoid] (Lib/Setoid.v) for the
 discrete setoid on an index type; and, for the Awodey comparison and the
 witnesses only,
 [Sets_Cartesian] (Instance/Sets/Cartesian.v), [Sets_Cocartesian]
 (Instance/Sets/Cocartesian.v), [Sets_Closed]
 (Instance/Sets/Cartesian/Closed.v), [Sets_Terminal] and [Sets_Initial]
 (Instance/Sets.v).  Genuinely new: every [Sets_*] constant below, together
 with the [HasIndexedCoproducts] vocabulary of Structure/Limit/Coproduct.v.

 NON-DEGENERACY OF THE WITNESSES

 An indexed product over an empty index is the terminal object and one over
 a singleton index is the family's only member -- [Sets_iprod_empty] and
 [Sets_iprod_unit] prove exactly that, and neither exercises the
 construction.  The witnesses that do are [Sets_iprod_bool] (two distinct
 indices: the product is the binary product of Instance/Sets/Cartesian.v --
 a statement whose right-hand side names two distinct members of the family,
 which the empty and singleton statements cannot do) and [Sets_iprod_nat]
 (an infinite index: the product satisfies the stream equation
 P ≅ F 0 × P', peeling a factor off and finding a product of the same shape
 underneath).  [Sets_icoprod_empty], [Sets_icoprod_unit],
 [Sets_icoprod_bool] and [Sets_icoprod_nat] are the four coproduct
 counterparts.

 Neither of those is by itself a SEPARATION: neither exhibits a property
 that holds at a degenerate index and is lost at a genuine one.  That is
 supplied by [Sets_iprod_unit_pigeonhole] together with
 [Sets_iprod_nat_no_pigeonhole].  The first proves, of the product of
 two-element setoids over a SINGLETON index, that no three elements are
 pairwise apart -- given [x y z], from [(x ≈ y) → False] and
 [(y ≈ z) → False] it concludes [x ≈ z].  The second refutes that same
 implication over [nat], by exhibiting three pairwise-apart elements.
 Together they are what makes the [nat] INDEX load-bearing rather than
 decorative; note that both statements are about
 [indexed_product (fun _ : nat => Sets_bool)] directly and neither mentions
 [Sets_iprod_nat], so what they separate is the index, not the stream
 decomposition.  [Sets_icoprod_unit_pigeonhole] and
 [Sets_icoprod_nat_no_pigeonhole] are the coproduct counterparts.

 SCOPE: WHAT IS DEFERRED

 Mac Lane section III.4 exercise 2 also asks for the analogous description
 of the J-indexed product in Top -- the product topology, its projections
 and its tupling universal property.  That is NOT delivered, here or
 anywhere in this development, and is deferred: the library has no category
 of topological spaces (tracked as issue #259).  It is an optional
 extension, not a prerequisite; every [Sets] result in this file stands
 without it.

 Two further limits of scope, stated so they are not mistaken for claims.
 First, [Sets_constant_iprod_exponent] compares the indexed product over an
 index TYPE [I] with the exponential at the DISCRETE setoid on [I], because
 [HasIndexedProducts] indexes by a bare [Type] while an exponential in
 [Sets] has a setoid for its base; no claim is made here about the
 exponential at a coarser setoid.  Second, this file supplies products and
 coproducts only; completeness of [Sets] is Instance/Sets/Complete.v, and
 cocompleteness is not addressed at all, here or anywhere else in the
 tree. 

 --------
 nLab:       https://ncatlab.org/nlab/show/product
 nLab:       https://ncatlab.org/nlab/show/coproduct
 nLab:       https://ncatlab.org/nlab/show/complete+category
 Wikipedia:  https://en.wikipedia.org/wiki/Product_(category_theory)
 Wikipedia:  https://en.wikipedia.org/wiki/Coproduct

 来源在此进行了转置，全部按位置引用；在编写此文件时没有查阅这三本书的印刷文本。下面的一行描述是从第254期的目录条目中抄录的，而不是来自书本：- Mac Lane，《为了工作的数学家而设的范畴》，第2版（Springer GTM 5），第I.6节，印刷第24页，练习1和2。这些练习是关于一个宇宙在小型笛卡尔积和小型并下封闭的集合论陈述。它们的范畴转置如下文件所示：[Sets] 在级别 [o] 上具有由任意级别 [o] 索引的族的积和余积——[o] 是按下面记录的宇宙纪律 [Sets] 对象的承载体的宇宙。 - Mac Lane，同书，第III.4节，印刷第72页，练习2：带有投影的 J 索引笛卡尔积在 Set 中是范畴积。即下面的 [Sets_HasIndexedProducts]。（相同的练习也要求在 Top 中给出描述；参见下文的 SCOPE。）
 - Awodey，《范畴论》，第一版（卡内基梅隆预印本，2005 年 9 月），第 2.9 节练习 7，印刷版第 56 页，部分 (a) 和 (b)。部分 (a)——I 索引乘积的泛性质——已在树中作为 [IsIndexedProduct] ，位于 Structure/Limit/Product.v。部分 (b)——函数集 X^I 对于常值族满足该性质——如下为 [Sets_exponent_IsIndexedProduct] 和 [Sets_constant_iprod_exponent]。
 - Riehl，《语境中的范畴论》，第二版，第 3.2 节，印刷版第 94 页，例 5：J 索引集合族的乘积是 J 元组的集合。这里 [Sets_iprod_obj F] 的元素实际上就是一个 J 元组，即依赖函数 [∀ i : A, F i]。

 已构造的是什么[Sets_iprod_obj F] 承载者 [∀ i : A, F i]，带有 [g ≈ h] 点态;
 [Sets_icoprod_obj F] 承载者 [{ i : A & F i }]，带有 [(i; x) ≈ (j; y)]
 当且仅当某个 [e : i = j] 将 [x] 携带到等价于 [y] 的值。

 [Sets_HasIndexedProducts] 和 [Sets_HasIndexedCoproducts] 将这些与它们的投影/注入及通用性质打包。在此之前
 文件中，树在任何范畴中都没有 [HasIndexedProducts] 实例，也完全没有 [HasIndexedCoproducts] 词汇。

 这在其他地方未解决的内容Theory/WeaklyInitial.v 将它的两个产物作为显式假设，而不是从 [Complete] / [HasIndexedProducts] 实例中获取，并且该注释并不是上述缺失的记录：它的理由是宇宙层面的，并且在实例存在时依然有效。它的两个产物中的第二个涵盖了一个同态类型，所以“通过一个对每个索引 [Type] 进行量化的类来路由它会过度约束环境宇宙”，而显式形式“将索引的小范围（因此相关的宇宙约束）保留在调用者手中”。下面的内容没有改变这一点，注释保持原样。然而，在 [Sets] 中，它所防护的障碍不存在，而下面的 [Sets_endo_iprod] / [Sets_endo_iprod_ump] 记录了这个事实：[P] 与自身的自同态索引积由 [Sets_HasIndexedProducts] 提供，并具有其泛性质，就在同一个 [Sets] 上——

 Sets_endo_iprod@{u u0} : obj [Sets@{u0 u}]  → obj [Sets@{u0 u}] 
 ( * 其中 u0 < u * )

 -- 没有第二个 [Sets]，也没有宇宙增长，因为 [Sets] 的 hom 类型恰好位于实例接受的索引宇宙。 这是关于 [Sets] 的一个观察；对于任意范畴，hom 宇宙不一定位于类放置索引的位置，这是 Theory/WeaklyInitial.v 的显式假设涵盖的情况。

 宇宙纪律，这是本练习的重点[Sets@{o so} : Category@{so o o}]（Instance/Sets.v）：它的对象是 [SetoidObject@{o o}]，其载体位于 [Type@{o}]，它的 Hom 也位于 [Type@{o}]。一个依赖函数类型 [∀ i : A, F i] 在 [A : Type@{u}] 上的取值位于 [Type@{max(u,o)}]，因此当且仅当 [u <= o] 时，它是 [Sets@{o so}] 的一个对象的载体；同样 [{ i : A & F i }]。Mac Lane I.6 的小性侧条件因此在本开发中是索引类型的宇宙级别，并不是人为施加的——它是宇宙推理记录的内容。 

 Structure/Limit/Product.v 的 [HasIndexedProducts] 将其索引量化为 [{A : Type}]，并且在库的 [Set Universe Polymorphism]（Lib.v）下，[Type] 是类的宇宙参数，而不是对所有宇宙的量词。打印该类显示三个参数，每个字段一个：HasIndexedProducts@{u u0 u1 u2 u3 u4} (C : Category@{u3 u4 u4})
 { indexed_product      : ∀ A : Type@{u}, ...
 indexed_product_proj : ∀ A : Type@{u0}, ...
 indexed_product_ump  : ∀ A : Type@{u1}, ... }

 因此，如字面所示，该类可以在 [Sets] 实例化，
 并且这三个宇宙被取为 [o]。事情就是这样发生的；
 [About Sets_HasIndexedProducts] 打印

 Sets_HasIndexedProducts@{u u0} : HasIndexedProducts@{u0 u0 u0 u0 u u0}
 Sets@{u0 u}     ( * u0 < u * )--  [u0] 是 [o]，ZWZ62WZZ 是 [so]，三个索引宇宙都是 [u0]，且环境 [Category@{u3 u4 u4}] 是 [Category@{u u0 u0}]，这就是 [Sets@{u0 u}]。没有单独的索引宇宙变量需要实例化：索引宇宙是 [o]，也就是 [Sets] 对象的 CARRIERS 的宇宙——即小集合自身存在的层次。它不是 [so]，也不是 [obj[Sets] 的宇宙，那是 [Sets] 作为 [Category@{so o o}] 保留其对象的地方，并且严格位于 [o] 之上；按 [obj[Sets] 索引正是下一段所展示被拒绝的。余积实例通过 [Structure/Limit/Coproduct.v] 的定义性对偶也是同样的情况：Sets_HasIndexedCoproducts@{u u0} : HasIndexedCoproducts@{u u0 u0 u u0}
 Sets@{u0 u}   ( * 其中 u0 < u * )

 其中 [Print HasIndexedCoproducts] 显示 [u0] 在第二个位置是索引宇宙，并且 [Category@{u2 u3 u3}] 与 [u2 := u] 、 [u3 := u0] 是 [Sets] 。

 类的无宇宙约束变体没有被引入：上述实例属于 [Structure/Limit/Product.v] 的 [HasIndexedProducts] 本身。

 条件按预期方向起作用。 在更高宇宙级别的索引类型上应用 [indexed_product] —— [SetoidObject@{o o}] 本身，它是 [Type@{o+1}] —— 被解释器因宇宙不一致而拒绝。 这在树之外进行了检查，而不是在此处记录为命令，因此 [make todo] 扫描保持干净；读者可以通过以下方式重现它定义 big@{o so} 
 (F : SetoidObject@{o o} -> SetoidObject@{o o}) : SetoidObject@{o o} :=
 @indexed_product Sets@{o so} Sets_HasIndexedProducts@{so o}
 (SetoidObject@{o o}) F。

 它报告说 [SetoidObject@{o o}] "的类型为 Type@{o+1}，而预期类型为 Type@{o}"。这里没有解释为什么必须存在这种界限；Structure/Complete.v 记录了 Freyd 的定理：一个具有和其自身态射集合一样大的族积的范畴是一个顺序范畴。

 不允许函数外延性当 [Sets_iprod_obj F] 的两个元素在每个索引上都与上同态 [≈] 相同时，就可以识别它们。也就是说，依赖函数的外延相等是作为对象选择的等价实现的，而不是作为公理，这正是 Instance/Sets.v 对同态集所做的操作。这里没有涉及 [funext]、选择，或 [UIP]：直和的等价关系沿索引的等式进行传输，关于它的每个证明都通过析构该等式进行。[Print Assumptions] 对此文件中的每个常量报告“在全局上下文下封闭”；Makefile 的 [print-assumptions] 目标审核主要的常量。

 哪些现有常量完成了这项工作不变重用：[IsIndexedProduct] 和 [HasIndexedProducts] （Structure/Limit/Product.v）；[Sets]、[SetoidObject]、[SetoidMorphism]（Instance/Sets.v）；[eq_Setoid]（Lib/Setoid.v）用于索引类型上的离散集合范畴；并且，仅用于 Awodey 对比和证人，[Sets_Cartesian]（Instance/Sets/Cartesian.v）、[Sets_Cocartesian]（Instance/Sets/Cocartesian.v）、[Sets_Closed]（Instance/Sets/Cartesian/Closed.v）、[Sets_Terminal] 和 [Sets_Initial]（Instance/Sets.v）。真正新的：下面每一个 [Sets_*] 常量，以及 Structure/Limit/Coproduct.v 的 [HasIndexedCoproducts] 词汇表。

 证人的非退化性在空索引上的索引积是终对象，而在单元素索引上的索引积是该族唯一的成员——[Sets_iprod_empty] 和 [Sets_iprod_unit] 正好证明了这一点，并且两者都没有使用该构造。真正使用该构造的证据是 [Sets_iprod_bool]（两个不同的索引：该积是 Instance/Sets/Cartesian.v 的二元积——一个等式的右侧指定了族中的两个不同成员，这是空族和单元素族无法做到的）以及 [Sets_iprod_nat]（一个无限索引：该积满足流方程 P ≅ F 0 × P'，剥离一个因子后在下面找到形状相同的积）。[Sets_icoprod_empty]、[Sets_icoprod_unit]、[Sets_icoprod_bool] 和 [Sets_icoprod_nat] 是四个余积对应的例子。这些本身都不是分离：都不展现出在退化索引下成立而在真正索引下失效的性质。这一性质由 [Sets_iprod_unit_pigeonhole] 和 [Sets_iprod_nat_no_pigeonhole] 提供。前者证明了，在单元素索引下的两个元素集合的乘积中，没有三个元素是两两分开的——在 [x y z] 的前提下，从 [(x ≈ y) → False] 和 [(y ≈ z) → False] 得出 [x ≈ z]。后者在 [nat] 上反驳了同样的蕴含关系，通过展示三个两两分开的元素。它们共同使得 [nat] 索引成为承重而非装饰；注意这两个陈述都是直接关于 [indexed_product (fun _ : nat => Sets_bool)] 的，并且都没有提到 [Sets_iprod_nat]，因此它们分离的是索引，而不是流分解。[Sets_icoprod_unit_pigeonhole] 和 [Sets_icoprod_nat_no_pigeonhole] 是其余积的对应物。范围：什么是推迟

 Mac Lane 第 III.4 节练习 2 同样要求对 Top 中的 J 索引积进行类似描述 —— 积拓扑、它的投影以及它的组元泛性质。这在这里或本开发的其他任何地方都没有提供，而是被推迟：库中没有拓扑空间的范畴（追踪为问题 #259）。这是一个可选扩展，而不是前提条件；本文件中的每一个 [Sets] 结果在没有它的情况下都成立。再说明两个范围的限制，以免被误认为是声明。
 首先，[Sets_constant_iprod_exponent] 将索引类型为 [I] 的索引积与 [I] 上离散集合的指数进行比较，因为 [HasIndexedProducts] 按裸 [Type] 进行索引，而 [Sets] 中的指数其底部有一个集合；这里并未对更粗的集合上的指数作出任何声明。其次，该文件仅提供积和余积；[Sets] 的完备性在 Instance/Sets/Complete.v 中，且余完备性在此或树中的任何其他地方都未讨论。
*)

(*
 The default obligation tactic is switched off for this file, as
 Instance/Sets/End.v does: where [Program] raises an obligation it is
 discharged by an explicit script below rather than by the library's [cat] /
 [cat_simpl] automation, and no script below invokes a proof-search tactic:
 none of them calls [auto], [eauto], [intuition], [firstorder] or [tauto].
 A few scripts do use the tacticals [now] (at the obligations of
 [Sets_iprod_tuple], [Sets_icoprod_obj] and [Sets_icoprod_case]) and
 [first [...]] (in the two singleton pigeonhole lemmas), which sequence and
 choose among explicit steps rather than search.  Note also that some
 [proper_morphism] fields never become obligations at all -- instance
 resolution closes them during elaboration -- which is why several tactic
 scripts further down use an [all:] selector, a no-op when no goal is
 left. 

 --------
 对于此文件，默认的义务策略已被关闭，因为 Instance/Sets/End.v 执行的操作是：当 [Program] 提出一个义务时，它是通过下面的显式脚本而不是库的 [cat] / [cat_simpl] 自动机制来解决的，并且下面没有脚本调用证明搜索策略：它们都没有调用 [auto]、[eauto]、[intuition]、[firstorder] 或 [tauto]。有些脚本确实使用了战术操作符 [now]（在 [Sets_iprod_tuple]、[Sets_icoprod_obj] 和 [Sets_icoprod_case] 的义务上）以及 [first [...]（在两个单元鸽巢引理中），它们对显式步骤进行序列化和选择，而不是搜索。还请注意，一些 [proper_morphism] 字段从来不会成为义务——实例解析在展开过程中就会关闭它们——这就是为什么在下面的几个策略脚本中使用 [all:] 选择器，当没有目标剩余时，它是一个无操作。
*)
#[local] Obligation Tactic := idtac.

(* * ** Indexed products: the dependent-function setoid / * ** 索引产品：依赖函数的等价关系集 *)

Definition Sets_iprod_equiv {A : Type} (F : A → SetoidObject) :
  crelation (∀ i : A, F i) :=
  fun g h => ∀ i : A, g i ≈ h i.

Program Definition Sets_iprod_obj {A : Type}
  (F : A → SetoidObject) : SetoidObject := {|
  carrier   := ∀ i : A, F i;
  is_setoid := {| equiv := Sets_iprod_equiv F |}
|}.
Next Obligation.
  intros A F.
  constructor.
  - intros g i; reflexivity.
  - intros g h Hgh i; symmetry; exact (Hgh i).
  - intros g h k Hgh Hhk i; transitivity (h i); [exact (Hgh i)|exact (Hhk i)].
Qed.

Program Definition Sets_iprod_proj {A : Type}
  (F : A → SetoidObject) (i : A) : Sets_iprod_obj F ~{Sets}~> F i := {|
  morphism := fun g => g i
|}.
Next Obligation. intros A F i g h Hgh; exact (Hgh i). Qed.

Program Definition Sets_iprod_tuple {A : Type}
  (F : A → SetoidObject) (c : SetoidObject)
  (pi : ∀ i : A, c ~{Sets}~> F i) : c ~{Sets}~> Sets_iprod_obj F := {|
  morphism := fun x i => pi i x
|}.
Next Obligation. intros A F c pi x y Hxy i; now rewrite Hxy. Qed.

Program Definition Sets_iprod_ump {A : Type} (F : A → SetoidObject)
  (c : SetoidObject) (pi : ∀ i : A, c ~{Sets}~> F i) :
  ∃! u : c ~{Sets}~> Sets_iprod_obj F,
    ∀ i : A, Sets_iprod_proj F i ∘ u ≈ pi i := {|
  unique_obj := Sets_iprod_tuple F c pi
|}.
Next Obligation. intros A F c pi i x; reflexivity. Qed.
Next Obligation. intros A F c pi v Hv x i; symmetry; exact (Hv i x). Qed.

Definition Sets_IsIndexedProduct {A : Type}
  (F : A → obj[Sets]) :
  IsIndexedProduct F (Sets_iprod_obj F) (Sets_iprod_proj F) :=
  @Build_IsIndexedProduct Sets A F (Sets_iprod_obj F) (Sets_iprod_proj F)
    (fun c pi => Sets_iprod_ump F c pi).

#[export]
Instance Sets_HasIndexedProducts : @HasIndexedProducts Sets :=
  @Build_HasIndexedProducts Sets
    (@Sets_iprod_obj) (@Sets_iprod_proj) (@Sets_IsIndexedProduct).

(*
   * ** The endomorphism-indexed product

   The index that Theory/WeaklyInitial.v declines to draw from a class,
   because for a general category it need not sit where the class puts the
   index: the endomorphisms of an object.  At [Sets] it does sit there.  The
   two constants below are the whole of the observation -- their existence,
   and the universe context they elaborate at, ARE the content, so both are
   stated as instances of what [Sets_HasIndexedProducts] already supplies
   rather than reproved.  See the header for what this does and does not say
   about the general note. 

   --------
   * ** 自同态索引的积

   Theory/WeaklyInitial.v 拒绝从一个类中取索引，
   因为对于一般范畴，它不一定位于类放置索引的位置：一个对象的自同态。在 [Sets] 中，它确实位于那里。
   下面的两个常量就是整个观察——它们的存在，以及它们所在的宇宙上下文，就是内容，因此两者都被作为 [Sets_HasIndexedProducts] 已经提供的实例来陈述，而不是重新证明。
   请参见标题，了解这对一般注释说了什么和没有说什么。
*)

Definition Sets_endo_iprod (P : obj[Sets]) : obj[Sets] :=
  indexed_product (fun _ : P ~{Sets}~> P => P).

Definition Sets_endo_iprod_ump (P : obj[Sets]) :
  IsIndexedProduct (fun _ : P ~{Sets}~> P => P) (Sets_endo_iprod P)
                   (indexed_product_proj (fun _ : P ~{Sets}~> P => P)) :=
  indexed_product_ump (fun _ : P ~{Sets}~> P => P).

(* * ** Indexed coproducts: the sigma setoid / * ** 索引余积：Sigma 集合等价类 *)

Definition Sets_icoprod_carrier {A : Type}
  (F : A → SetoidObject) : Type := { i : A & F i }.

Definition Sets_icoprod_equiv {A : Type} (F : A → SetoidObject) :
  crelation (Sets_icoprod_carrier F) :=
  fun p q =>
    { e : projT1 p = projT1 q
    & rew [fun i : A => carrier (F i)] e in projT2 p ≈ projT2 q }.

Program Definition Sets_icoprod_obj {A : Type}
  (F : A → SetoidObject) : SetoidObject := {|
  carrier   := Sets_icoprod_carrier F;
  is_setoid := {| equiv := Sets_icoprod_equiv F |}
|}.
Next Obligation.
  intros A F.
  constructor.
  - intros [i x]; exists eq_refl; reflexivity.
  - intros [i x] [j y] [e Hxy]; simpl in *; destruct e; simpl in *.
    exists eq_refl; simpl; now symmetry.
  - intros [i x] [j y] [k z] [e Hxy] [e' Hyz]; simpl in *.
    destruct e; destruct e'; simpl in *.
    exists eq_refl; simpl; now transitivity y.
Qed.

Program Definition Sets_icoprod_inj {A : Type}
  (F : A → SetoidObject) (i : A) : F i ~{Sets}~> Sets_icoprod_obj F := {|
  morphism := fun x => existT _ i x
|}.
Next Obligation. intros A F i x y Hxy; exists eq_refl; exact Hxy. Qed.

Program Definition Sets_icoprod_case {A : Type}
  (F : A → SetoidObject) (c : SetoidObject)
  (iota : ∀ i : A, F i ~{Sets}~> c) : Sets_icoprod_obj F ~{Sets}~> c := {|
  morphism := fun p => iota (projT1 p) (projT2 p)
|}.
Next Obligation.
  intros A F c iota [i x] [j y] [e Hxy]; simpl in *; destruct e; simpl in *.
  now rewrite Hxy.
Qed.

Program Definition Sets_icoprod_ump {A : Type} (F : A → SetoidObject)
  (c : SetoidObject) (iota : ∀ i : A, F i ~{Sets}~> c) :
  ∃! u : Sets_icoprod_obj F ~{Sets}~> c,
    ∀ i : A, u ∘ Sets_icoprod_inj F i ≈ iota i := {|
  unique_obj := Sets_icoprod_case F c iota
|}.
Next Obligation. intros A F c iota i x; reflexivity. Qed.
Next Obligation.
  intros A F c iota v Hv [i x]; simpl; symmetry; exact (Hv i x).
Qed.

Definition Sets_IsIndexedCoproduct {A : Type}
  (F : A → obj[Sets]) :
  IsIndexedCoproduct F (Sets_icoprod_obj F) (Sets_icoprod_inj F) :=
  @Build_IsIndexedCoproduct Sets A F
    (Sets_icoprod_obj F) (Sets_icoprod_inj F)
    (fun c iota => Sets_icoprod_ump F c iota).

#[export]
Instance Sets_HasIndexedCoproducts : @HasIndexedCoproducts Sets :=
  @Build_HasIndexedCoproducts Sets
    (@Sets_icoprod_obj) (@Sets_icoprod_inj)
    (@Sets_IsIndexedCoproduct).

(* * ** Awodey 2.9 Exercise 7(b): the function set as a constant-family product / * ** Awodey 2.9 练习 7(b)：将函数设为常数族的乘积 *)

Definition Sets_discrete (I : Type) : obj[Sets] :=
  {| carrier := I; is_setoid := eq_Setoid I |}.

(*
 The exponential X^I of Instance/Sets/Cartesian/Closed.v, taken at the
 discrete setoid on the index type I.  Written as a definition rather than
 inline so that the ambient category is pinned to [Sets] for elaboration. 

 --------
 指数 X^I 来自 Instance/Sets/Cartesian/Closed.v，在索引类型 I 上采用离散集合同构。作为定义而非内联书写，以便在推导时将环境类别固定为 [Sets]。
*)
Definition Sets_pow (I : Type) (X : obj[Sets]) : obj[Sets] :=
  (X ^ Sets_discrete I)%object.

Program Definition Sets_exponent_eval (I : Type) (X : obj[Sets]) (i : I) :
  Sets_pow I X ~{Sets}~> X := {|
  morphism := fun f => f i
|}.
Next Obligation. intros I X i f g Hfg; exact (Hfg i). Qed.

(*
 The element of X^I named by a family [pi] at a point [x].  Built with
 [unshelve refine] rather than [Program] so that the [proper_morphism]
 certificate is supplied by hand.  This is not a matter of taste: with the
 [Program] form, instance resolution closes that field during elaboration
 -- the definition raises no obligation at all -- and the constant comes out
 pinned to [Set]:

 ∀ (I : Type@{u}) (X c : obj[Sets@{Set u0}]), ...
 ( * with  Set < u0  and  Set = u * )

 The index universe [u] is [Set] by a universe EQUALITY, not merely bounded
 by it, and the ambient [Sets] is pinned along with it.  The [unshelve
 refine] form below instead prints
 [∀ (I : Type@{u}) (X c : obj[Sets@{u u0}])] with only [u < u0].  (Observed
 while writing this file; the mechanism behind the pinning was not
 investigated.) 

 --------
 在点 [x] 由族 [pi] 命名的 X^I 元素。使用 [unshelve refine] 构建，而不是 [Program]，这样 [proper_morphism] 证书可以手工提供。这不是品味问题：使用 [Program] 形式时，实例解析在展开过程中会关闭该字段——定义根本不会提出任何义务——常量最终固定为 [Set]：

 ∀ (I : Type@{u}) (X c : obj [Sets@{Set u0}] ), ...
 ( * 使用 Set < u0 且 Set = u * )

 索引宇宙 [u] 通过宇宙相等 [Set] 固定，而不仅仅是被其限制，环境 [Sets] 也随之固定。下面的 [unshelve refine] 形式则只打印 [∀ (I : Type@{u}) (X c : obj[Sets@{u u0}] )] 和 [u < u0]。（编写此文件时观察到；未调查固定背后的机制。）
*)
Definition Sets_exponent_elt (I : Type) (X c : obj[Sets])
  (pi : ∀ i : I, c ~{Sets}~> X) (x : c) : Sets_discrete I ~{Sets}~> X.
Proof.
  unshelve refine {| morphism := fun i => pi i x |}.
  intros i j Hij; destruct Hij; reflexivity.
Defined.

Program Definition Sets_exponent_tuple (I : Type) (X c : obj[Sets])
  (pi : ∀ i : I, c ~{Sets}~> X) : c ~{Sets}~> Sets_pow I X := {|
  morphism := Sets_exponent_elt I X c pi
|}.
Next Obligation.
  intros I X c pi x y Hxy i; exact (proper_morphism (pi i) x y Hxy).
Qed.

Program Definition Sets_exponent_ump (I : Type) (X c : obj[Sets])
  (pi : ∀ i : I, c ~{Sets}~> X) :
  ∃! u : c ~{Sets}~> Sets_pow I X,
    ∀ i : I, Sets_exponent_eval I X i ∘ u ≈ pi i := {|
  unique_obj := Sets_exponent_tuple I X c pi
|}.
Next Obligation. intros I X c pi i x; reflexivity. Qed.
Next Obligation. intros I X c pi v Hv x i; symmetry; exact (Hv i x). Qed.

Definition Sets_exponent_IsIndexedProduct (I : Type) (X : obj[Sets]) :
  IsIndexedProduct (fun _ : I => X) (Sets_pow I X)
                   (Sets_exponent_eval I X) :=
  @Build_IsIndexedProduct Sets I (fun _ : I => X) (Sets_pow I X)
    (Sets_exponent_eval I X) (fun c pi => Sets_exponent_ump I X c pi).

(*
 Each isomorphism below is assembled from two named setoid maps rather than
 through [Program] at the isomorphism itself: the isomorphism is a [refine]
 over two concrete morphisms, leaving exactly the two inverse laws.

 The maps themselves are built two ways.  Most are [unshelve refine], with
 the [proper_morphism] certificate discharged under an [all:] selector: for
 some of them instance resolution already closes that goal during
 elaboration, and [all:] is a no-op when no goal remains, so the script does
 not depend on which of the two happens.  The exception is the pair making
 up [Sets_constant_iprod_exponent] -- [Sets_exponent_tuple] above and
 [Sets_exponent_untuple] just below -- both of which are [Program].  For
 [Sets_exponent_untuple], whose SOURCE is the exponential [Sets_pow I X],
 this was measured: refining a record literal against a goal whose type has
 to be unfolded through [Sets_Closed] did not return within sixty seconds,
 where the [Program] form elaborates in well under a second.
 [Sets_exponent_tuple] was written as [Program] from the start and no such
 measurement was taken for it. 

 --------
 下面的每个同构都是由两个命名的集合对应映射组合而成，而不是通过同构本身的 [Program]：该同构是两个具体态射上的 [refine]，仅留下恰好两个逆律。地图本身有两种构建方式。大多数是 [unshelve refine]，通过 [all:] 选择器解除 [proper_morphism] 证书：对于其中的一些，实例解析在展开过程中已经关闭了该目标，而当没有剩余目标时 [all:] 是无操作的，因此脚本不依赖于发生哪一种情况。例外的是构成 [Sets_constant_iprod_exponent] 的那一对 —— 上面的 [Sets_exponent_tuple] 和下面的 [Sets_exponent_untuple] —— 两者都是 [Program]。对于 [Sets_exponent_untuple]，其 SOURCE 是指数 [Sets_pow I X]，进行了如下测量：针对需要通过 [Sets_Closed] 展开的类型的目标精炼记录字面量，在六十秒内没有返回，而 [Program] 形式的展开耗时不到一秒。[Sets_exponent_tuple] 从一开始就被写作 [Program]，对它没有进行这种测量。
*)
Program Definition Sets_exponent_untuple (I : Type) (X : obj[Sets]) :
  Sets_pow I X ~{Sets}~> indexed_product (fun _ : I => X) := {|
  morphism := fun f => fun i => f i
|}.
Next Obligation. intros I X f g Hfg i; exact (Hfg i). Qed.

Definition Sets_constant_iprod_exponent (I : Type) (X : obj[Sets]) :
  indexed_product (fun _ : I => X) ≅[Sets] Sets_pow I X.
Proof.
  refine {| to := Sets_exponent_tuple I X (indexed_product (fun _ : I => X))
                    (fun i => Sets_iprod_proj (fun _ : I => X) i)
          ; from := Sets_exponent_untuple I X |}.
  - intros f i; reflexivity.
  - intros g i; reflexivity.
Defined.

(*
   * ** Degenerate indices

   An indexed product over an empty index is the terminal object, and one
   over a singleton index is the family's only member; dually for
   coproducts.  Neither exercises the construction.  They are recorded here
   so that the contrast drawn with the non-degenerate cases of the next
   section is proved rather than asserted. 

   --------
   * ** 退化指标

   对空索引的索引乘积是终对象，而对单元素索引的乘积是该族的唯一成员；对于余积亦然。两者都不涉及构造。它们在这里记录下来，以便与下一节非退化情况的对比是被证明的，而不是断言的。
*)

Definition Sets_iprod_empty_to (F : False → obj[Sets]) :
  indexed_product F ~{Sets}~> 1%object.
Proof.
  unshelve refine {| morphism := fun _ => ttt |}.
  all: intros g h Hgh; reflexivity.
Defined.

Definition Sets_iprod_empty_from (F : False → obj[Sets]) :
  1%object ~{Sets}~> indexed_product F.
Proof.
  unshelve refine {| morphism := fun _ => fun i : False => match i with end |}.
  all: intros x y Hxy i; destruct i.
Defined.

Definition Sets_iprod_empty (F : False → obj[Sets]) :
  indexed_product F ≅[Sets] 1%object.
Proof.
  refine {| to := Sets_iprod_empty_to F; from := Sets_iprod_empty_from F |}.
  - intros u; destruct u; reflexivity.
  - intros g i; destruct i.
Defined.

Definition Sets_iprod_unit_to (F : poly_unit → obj[Sets]) :
  indexed_product F ~{Sets}~> F ttt.
Proof.
  unshelve refine {| morphism := fun g => g ttt |}.
  all: intros g h Hgh; exact (Hgh ttt).
Defined.

Definition Sets_iprod_unit_from (F : poly_unit → obj[Sets]) :
  F ttt ~{Sets}~> indexed_product F.
Proof.
  unshelve refine {| morphism := fun x =>
      fun i => match i return carrier (F i) with ttt => x end |}.
  all: intros x y Hxy i; destruct i; exact Hxy.
Defined.

Definition Sets_iprod_unit (F : poly_unit → obj[Sets]) :
  indexed_product F ≅[Sets] F ttt.
Proof.
  refine {| to := Sets_iprod_unit_to F; from := Sets_iprod_unit_from F |}.
  - intros x; reflexivity.
  - intros g i; destruct i; reflexivity.
Defined.

Definition Sets_icoprod_empty_to (F : False → obj[Sets]) :
  indexed_coproduct F ~{Sets}~> 0%object.
Proof.
  unshelve refine {| morphism := fun p => projT1 p |}.
  all: intros [i x]; destruct i.
Defined.

Definition Sets_icoprod_empty_from (F : False → obj[Sets]) :
  0%object ~{Sets}~> indexed_coproduct F.
Proof.
  unshelve refine {| morphism := fun x : False => match x with end |}.
  all: intros x; destruct x.
Defined.

Definition Sets_icoprod_empty (F : False → obj[Sets]) :
  indexed_coproduct F ≅[Sets] 0%object.
Proof.
  refine {| to := Sets_icoprod_empty_to F; from := Sets_icoprod_empty_from F |}.
  - intros x; destruct x.
  - intros [i x]; destruct i.
Defined.

Definition Sets_icoprod_unit_to (F : poly_unit → obj[Sets]) :
  indexed_coproduct F ~{Sets}~> F ttt.
Proof.
  unshelve refine {| morphism := fun p =>
      match p with
      | existT _ i x =>
          match i return carrier (F i) → carrier (F ttt) with
          | ttt => fun x => x
          end x
      end |}.
  all: intros [i x] [j y] [e Hxy]; simpl in *; destruct e; simpl in *;
       destruct i; exact Hxy.
Defined.

Definition Sets_icoprod_unit_from (F : poly_unit → obj[Sets]) :
  F ttt ~{Sets}~> indexed_coproduct F.
Proof.
  unshelve refine {| morphism := fun x => existT _ ttt x |}.
  all: intros x y Hxy; exists eq_refl; exact Hxy.
Defined.

Definition Sets_icoprod_unit (F : poly_unit → obj[Sets]) :
  indexed_coproduct F ≅[Sets] F ttt.
Proof.
  refine {| to := Sets_icoprod_unit_to F; from := Sets_icoprod_unit_from F |}.
  - intros x; reflexivity.
  - intros [i x]; destruct i; exists eq_refl; reflexivity.
Defined.

(* * ** Non-degenerate indices: two distinct indices, and an infinite index / * ** 非退化指标：两个不同的指标，和一个无限指标 *)

(*
 [bool] is the smallest non-degenerate index.  The product over it is the
 binary product of Instance/Sets/Cartesian.v -- a statement whose right-hand
 side names two distinct members of the family, which the empty and
 singleton statements cannot do.  ([Sets_iprod_empty] and [Sets_iprod_unit]
 above are their counterparts, and neither mentions two members.) 

 --------
 [bool] 是最小的非退化索引。对它的乘积是 Instance/Sets/Cartesian.v 的二元乘积——这是一个其右侧命名了该族中两个不同成员的语句，而空集合和单元素语句无法做到这一点。（上面的 [Sets_iprod_empty] 和 [Sets_iprod_unit] 是它们的对应物，并且都没有提到两个成员。）
*)

Definition Sets_iprod_bool_to (F : bool → obj[Sets]) :
  indexed_product F ~{Sets}~> (F true × F false)%object.
Proof.
  unshelve refine {| morphism := fun g => (g true, g false) |}.
  all: intros g h Hgh; split; [exact (Hgh true)|exact (Hgh false)].
Defined.

Definition Sets_iprod_bool_from (F : bool → obj[Sets]) :
  (F true × F false)%object ~{Sets}~> indexed_product F.
Proof.
  unshelve refine {| morphism := fun p =>
      fun b => match b return carrier (F b) with
               | true  => fst p
               | false => snd p
               end |}.
  all: intros p q [Hl Hr] b; destruct b; assumption.
Defined.

Definition Sets_iprod_bool (F : bool → obj[Sets]) :
  indexed_product F ≅[Sets] (F true × F false)%object.
Proof.
  refine {| to := Sets_iprod_bool_to F; from := Sets_iprod_bool_from F |}.
  - intros p; split; reflexivity.
  - intros g b; destruct b; reflexivity.
Defined.

(*
 [nat] is an infinite index.  The product over it satisfies the stream
 equation P ≅ F 0 × P': peel one factor off and a product of the same shape
 is underneath.  This exhibits the infinite case; it is not by itself a
 separation from the degenerate ones, which is what
 [Sets_iprod_unit_pigeonhole] and [Sets_iprod_nat_no_pigeonhole] at the end
 of this file are for. 

 --------
 [nat] 是一个无限索引。其上的乘积满足流方程 P ≅ F 0 × P'：剥去一个因子，下面是相同形状的乘积。这显示了无限的情况；它本身并不是与退化情况的分离，[Sets_iprod_unit_pigeonhole] 和 [Sets_iprod_nat_no_pigeonhole] 在此文件末尾就是用于此目的。
*)

Definition Sets_iprod_nat_to (F : nat → obj[Sets]) :
  indexed_product F
    ~{Sets}~> (F 0%nat × indexed_product (fun n => F (S n)))%object.
Proof.
  unshelve refine {| morphism := fun g => (g 0%nat, fun m => g (S m)) |}.
  all: intros g h Hgh; split; [exact (Hgh 0%nat)|intros m; exact (Hgh (S m))].
Defined.

Definition Sets_iprod_nat_from (F : nat → obj[Sets]) :
  (F 0%nat × indexed_product (fun n => F (S n)))%object
    ~{Sets}~> indexed_product F.
Proof.
  unshelve refine {| morphism := fun p =>
      fun n => match n return carrier (F n) with
               | O   => fst p
               | S m => snd p m
               end |}.
  all: intros p q [Hl Hr] n; destruct n; [exact Hl|exact (Hr n)].
Defined.

Definition Sets_iprod_nat (F : nat → obj[Sets]) :
  indexed_product F
    ≅[Sets] (F 0%nat × indexed_product (fun n => F (S n)))%object.
Proof.
  refine {| to := Sets_iprod_nat_to F; from := Sets_iprod_nat_from F |}.
  - intros p; split; [reflexivity|intros m; reflexivity].
  - intros g n; destruct n; reflexivity.
Defined.

(* The coproduct counterpart of [Sets_iprod_bool]: the sigma setoid over [bool] is the binary coproduct of Instance/Sets/Cocartesian.v. / [Sets_iprod_bool] 的余积对应物：[bool] 上的 sigma 等价类是 Instance/Sets/Cocartesian.v 的二元余积。 *)

Definition Sets_icoprod_bool_to (F : bool → obj[Sets]) :
  indexed_coproduct F ~{Sets}~> (F true + F false)%object.
Proof.
  unshelve refine {| morphism := fun p =>
      match p with
      | existT _ b x =>
          match b return carrier (F b) →
                         carrier (F true) + carrier (F false) with
          | true  => fun x => Datatypes.inl x
          | false => fun x => Datatypes.inr x
          end x
      end |}.
  all: intros [i x] [j y] [e Hxy]; simpl in *; destruct e; simpl in *;
       destruct i; exact Hxy.
Defined.

Definition Sets_icoprod_bool_from (F : bool → obj[Sets]) :
  (F true + F false)%object ~{Sets}~> indexed_coproduct F.
Proof.
  unshelve refine {| morphism := fun s =>
      match s with
      | Datatypes.inl x => existT _ true x
      | Datatypes.inr y => existT _ false y
      end |}.
  all: intros s t Hst; destruct s, t; try contradiction;
       exists eq_refl; exact Hst.
Defined.

Definition Sets_icoprod_bool (F : bool → obj[Sets]) :
  indexed_coproduct F ≅[Sets] (F true + F false)%object.
Proof.
  refine {| to := Sets_icoprod_bool_to F; from := Sets_icoprod_bool_from F |}.
  - intros s; destruct s; reflexivity.
  - intros [i x]; destruct i; exists eq_refl; reflexivity.
Defined.

(* The coproduct counterpart of [Sets_iprod_nat]: the sigma setoid over [nat] splits off its zeroth summand and reproduces itself underneath. / [Sets_iprod_nat] 的余积对应物：[nat] 上的 sigma 集团，将其零次求和拆分出来，并在其下方再现自身。 *)

Definition Sets_icoprod_nat_to (F : nat → obj[Sets]) :
  indexed_coproduct F
    ~{Sets}~> (F 0%nat + indexed_coproduct (fun n => F (S n)))%object.
Proof.
  unshelve refine {| morphism := fun p =>
      match p with
      | existT _ n x =>
          match n return carrier (F n) →
                         carrier (F 0%nat)
                         + Sets_icoprod_carrier (fun m => F (S m)) with
          | O   => fun x => Datatypes.inl x
          | S m => fun x => Datatypes.inr (existT _ m x)
          end x
      end |}.
  all: intros [i x] [j y] [e Hxy]; simpl in *; destruct e; simpl in *;
       destruct i;
       [ exact Hxy | exists eq_refl; exact Hxy ].
Defined.

Definition Sets_icoprod_nat_from (F : nat → obj[Sets]) :
  (F 0%nat + indexed_coproduct (fun n => F (S n)))%object
    ~{Sets}~> indexed_coproduct F.
Proof.
  unshelve refine {| morphism := fun s =>
      match s with
      | Datatypes.inl x => existT (fun i : nat => carrier (F i)) 0%nat x
      | Datatypes.inr q =>
          match q with
          | existT _ m x => existT (fun i : nat => carrier (F i)) (S m) x
          end
      end |}.
  all: intros s t Hst; destruct s as [x|[m x]], t as [y|[n y]];
       try contradiction; simpl in *;
       [ exists eq_refl; exact Hst
       | destruct Hst as [e Hxy]; simpl in *; destruct e; simpl in *;
         exists eq_refl; exact Hxy ].
Defined.

Definition Sets_icoprod_nat (F : nat → obj[Sets]) :
  indexed_coproduct F
    ≅[Sets] (F 0%nat + indexed_coproduct (fun n => F (S n)))%object.
Proof.
  refine {| to := Sets_icoprod_nat_to F; from := Sets_icoprod_nat_from F |}.
  - intros s; destruct s as [x|[m x]]; reflexivity.
  - intros [i x]; destruct i; simpl; exists eq_refl; reflexivity.
Defined.

(*
   * ** A separating property: pigeonhole at a singleton index, refuted at [nat]

   The isomorphisms above exhibit the construction at non-degenerate
   indices, but none of them is by itself a separation: none exhibits a
   property that holds at a degenerate index and is lost at a genuine one.
   The four results here do.  What is proved is the implication

   ((x ≈ y) → False) → ((y ≈ z) → False) → x ≈ z,

   read over the product -- and, separately, over the coproduct -- of
   two-element setoids: no three elements are pairwise apart.  It holds over
   a SINGLETON index and is refutable over [nat].  A property of the
   construction at a degenerate index is therefore provably lost at a
   genuine one.

   Two cautions on reading that implication.  It is NOT the disjunctive
   pigeonhole "of any three elements, two coincide"; no disjunction is
   proved anywhere below.  The two forms are interderivable for these
   particular objects only because [Sets_bool] carries decidable equality,
   and that decidability is used inside the proofs (the [destruct ... eqn:]
   on [bool]) rather than stated as a hypothesis.  Separately, the informal
   reason the singleton case holds -- the object there has only two elements
   up to [≈] -- is not itself proved; the implication is. 

   --------
   * ** 一个分离性质：在单元素索引处有鸽笼原理，在 [nat] 处被反驳

   上面的同构展示了在非退化索引处的构造，但它们本身都不是分离：没有一个展示在退化索引处成立而在真正索引处失效的性质。这里的四个结果则有这种性质。所证明的是含义

   ((x ≈ y) → False) → ((y ≈ z) → False) → x ≈ z，

   在两个元素的集合上乘积以及分开地在余积上阅读：没有三个元素两两分开。它在单元素索引上成立，并且在 [nat] 上可被反驳。因此，在退化索引处构造的性质在真正索引处可以被证明会丧失。关于解读该蕴涵，有两点需要注意。它并不是“任意三个元素中有两个相同”的析取鸽笼原理；在下面的证明中没有任何地方证明析取命题。对于这些特定对象，这两种形式是可相互推导的，仅因为 [Sets_bool] 具有可判定的相等性，并且该可判定性在证明内部（[bool] 上的 [destruct ... eqn:]）被使用，而不是作为假设陈述。另一方面，单元素情况成立的非正式原因——该对象在 [≈] 下只有两个元素——本身并未被证明；而蕴涵是被证明的。
*)

(* The two-element setoid, [bool] under Coq's equality. / 在 Coq 的等式下，两个元素的集合 [bool]。 *)
Definition Sets_bool : obj[Sets] :=
  {| carrier := bool; is_setoid := eq_Setoid bool |}.

Lemma Sets_iprod_unit_pigeonhole
  (x y z : carrier (indexed_product (fun _ : poly_unit => Sets_bool))) :
  ((x ≈ y) → False) → ((y ≈ z) → False) → x ≈ z.
Proof.
  intros Hxy Hyz.
  assert (Hb : ∀ a b : carrier (indexed_product (fun _ : poly_unit => Sets_bool)),
                 a ttt = b ttt → a ≈ b)
    by (intros a b H i; destruct i; exact H).
  destruct (x ttt) eqn:Hx, (y ttt) eqn:Hy, (z ttt) eqn:Hz;
  first [ apply Hb; rewrite Hx, Hz; reflexivity
        | exfalso; apply Hxy; apply Hb; rewrite Hx, Hy; reflexivity
        | exfalso; apply Hyz; apply Hb; rewrite Hy, Hz; reflexivity ].
Qed.

(* Three elements of the [nat]-indexed product of two-element setoids: the constantly-[false] tuple, and the tuples true at index 0 and at index 1. / 两个元素集合的 [nat] 索引乘积的三个元素：恒定的 [false] 元组，以及在索引 0 和索引 1 处为 true 的元组。 *)
Definition Sets_iprod_pt0 :
  carrier (indexed_product (fun _ : nat => Sets_bool)) := fun _ => false.

Definition Sets_iprod_pt1 :
  carrier (indexed_product (fun _ : nat => Sets_bool)) :=
  fun n => match n with O => true | S _ => false end.

Definition Sets_iprod_pt2 :
  carrier (indexed_product (fun _ : nat => Sets_bool)) :=
  fun n => match n with S O => true | _ => false end.

Lemma Sets_iprod_nat_no_pigeonhole :
  (∀ x y z : carrier (indexed_product (fun _ : nat => Sets_bool)),
     ((x ≈ y) → False) → ((y ≈ z) → False) → x ≈ z) → False.
Proof.
  intros H.
  assert (H01 : (Sets_iprod_pt0 ≈ Sets_iprod_pt1) → False)
    by (intros Heq; specialize (Heq 0%nat); simpl in Heq; discriminate).
  assert (H12 : (Sets_iprod_pt1 ≈ Sets_iprod_pt2) → False)
    by (intros Heq; specialize (Heq 0%nat); simpl in Heq; discriminate).
  specialize (H _ _ _ H01 H12 1%nat); simpl in H; discriminate.
Qed.

Lemma Sets_icoprod_unit_pigeonhole
  (x y z : carrier (indexed_coproduct (fun _ : poly_unit => Sets_bool))) :
  ((x ≈ y) → False) → ((y ≈ z) → False) → x ≈ z.
Proof.
  intros Hxy Hyz.
  assert (Hb : ∀ a b : carrier (indexed_coproduct (fun _ : poly_unit => Sets_bool)),
                 projT2 a = projT2 b → a ≈ b)
    by (intros [i a] [j b] Hab; simpl in *; destruct i, j;
        exists eq_refl; exact Hab).
  destruct (projT2 x) eqn:Hx, (projT2 y) eqn:Hy, (projT2 z) eqn:Hz;
  first [ apply Hb; rewrite Hx, Hz; reflexivity
        | exfalso; apply Hxy; apply Hb; rewrite Hx, Hy; reflexivity
        | exfalso; apply Hyz; apply Hb; rewrite Hy, Hz; reflexivity ].
Qed.

(* The [k]-th summand's [true]. Identifying two of these calls for an equality of the two indices, which is what the refutation below turns on. / [k]-次求和项的 [true]。识别其中两个需要两个指标相等，这正是下面反驳所依据的。 *)
Definition Sets_icoprod_pt (k : nat) :
  carrier (indexed_coproduct (fun _ : nat => Sets_bool)) :=
  existT (fun _ : nat => carrier Sets_bool) k true.

Lemma Sets_icoprod_nat_no_pigeonhole :
  (∀ x y z : carrier (indexed_coproduct (fun _ : nat => Sets_bool)),
     ((x ≈ y) → False) → ((y ≈ z) → False) → x ≈ z) → False.
Proof.
  intros H.
  assert (H01 : (Sets_icoprod_pt 0 ≈ Sets_icoprod_pt 1) → False)
    by (intros [e _]; simpl in e; discriminate).
  assert (H12 : (Sets_icoprod_pt 1 ≈ Sets_icoprod_pt 2) → False)
    by (intros [e _]; simpl in e; discriminate).
  destruct (H _ _ _ H01 H12) as [e _]; simpl in e; discriminate.
Qed.
