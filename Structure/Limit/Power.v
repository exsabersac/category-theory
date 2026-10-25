Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Instance.Discrete.

Generalizable All Variables.

(* * * Powers and copowers of a single object / * * 单个对象的幂和余幂 *)

(*
 nLab:      https://ncatlab.org/nlab/show/power
 nLab:      https://ncatlab.org/nlab/show/copower
 Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)

 Sources, cited BY LOCATION; the one-line descriptions are transcribed from
 the catalog entries of issue #321 rather than from the printed books:

 - Mac Lane, "Categories for the Working Mathematician", 2nd ed.
 (Springer GTM 5), section III.3, printed p. 64 (PDF p. 73), item
 [maclane:III.3:def3], and section III.4, printed p. 70 (PDF p. 79),
 item [maclane:III.4:def4].  The POWER [b^J] is the product of the
 constant J-indexed family at [b], characterized by
 [C(c, b^J) ≅ C(c, b)^J]; dually the COPOWER [J · b] is the
 constant-family coproduct, characterized by [C(J · b, c) ≅ C(b, c)^J].
 - Riehl, "Category Theory in Context", 2nd ed., section 3.5, printed
 p. 110 (PDF p. 130), item [riehl:3.5:example4]: iterated products of a
 single object are POWERS (cotensors), written [A^I], with the
 representable universal property [C(X, A^I) ≅ C(X, A)^I] given by
 composing with the projections [ev_i].  Printed p. 111 (PDF p. 131),
 item [riehl:3.5:example8]: iterated coproducts of a single object are
 COPOWERS (tensors), written [I · A], with [C(∐_I A, X) ≅ C(A, X)^I].
 - Awodey, "Category Theory", 1st ed. (Carnegie Mellon pre-print,
 September 2005), chapter 3, section 3.2, unnumbered remark, printed
 p. 61 (PDF p. 70), item [awodey:3.2:remark-finite-copower]: in Sets a
 finite set [A] is a coproduct of copies of the terminal object,
 [A ≅ 1 + 1 + ⋯ + 1] with [n = |A|].

 THIS FILE IS THE NAMING LAYER; THE ISOMORPHISMS ARE NEXT DOOR.

 Everything below is a constant-family reading of
 Structure/Limit/Product.v and Structure/Limit/Coproduct.v, with no proof
 obligation anywhere: every constant is supplied by [:=].  The two
 characterizing isomorphisms, the [Sets] identifications and the Awodey
 witness live in Structure/Limit/Power/Hom.v, which is separate for a
 DEPENDENCY reason and not a thematic one -- see that file's header, and
 the paragraph on Theory/WeaklyInitial.v below.

 WHY THESE NAMES

 [power] and [copower] are the words Mac Lane, Riehl and the nLab use, and
 both were free as top-level constants before this file.  Reproduce with

 rg -n -e '^\s*(Program\s+)?(Definition|Lemma|Theorem|Corollary|Fixpoint|Record|Class|Inductive|Instance|Example|Notation)\s+(power|copower)\b' \
 -g '*.v' -g '!Structure/Limit/Power*'

 -- excluding this file and its satellite, since they now declare exactly
 those names -- which returns nothing.  [Pow] was NOT free and is
 deliberately not used: two
 different in-tree notions already carry it, NEITHER of them Mac Lane's --
 Instance/Fun/Discrete.v's [Fixpoint Pow (B : Category) (n : nat) :
 Category], the n-fold product OF CATEGORIES, and Structure/Topos.v's
 [Definition Pow (a : C) := Ω ^ a], the topos power OBJECT.  A third
 near-name, [Sets_pow] (Instance/Sets/Products.v), IS the same notion at
 [Sets] and is not shadowed either: Structure/Limit/Power/Hom.v proves the
 two ISOMORPHIC rather than redefining it -- only that.  They are NOT
 convertible, and Test/ProbePower.v pins it: a power's carrier is the bare
 function type while the exponential's is setoid MORPHISMS out of the
 discrete setoid.

 Read "free" as scoped to top-level constant DECLARATIONS matching that
 pattern; the token "power" occurs widely in comments and inside longer
 names ([Powerset], [GrpCosetPower], [cogen_power], [law_pow], [mat_pow],
 [tpower]), none of which this file touches.

 NOTATION, AND WHY IT IS OPT-IN

 [J ⋔ b] for the power and [J · b] for the copower, in their own
 [power_scope] with key [%power], following the [addition_scope]
 precedent of Structure/Preadditive.v: a consumer opts in with
 [Open Scope power_scope] or the [%power] key, and nothing is imposed on a
 file that merely Requires this one.  [⋔] is the nLab's symbol for powering
 and was entirely free tree-wide:

 rg -c -e '⋔' -g '*.v' -g '!Structure/Limit/Power*' -g '!Test/ProbePower.v'

 returns no files.  [·] is Mac Lane's own symbol for the copower, and while
 it occurs in the tree it occurs in COMMENTS only -- no notation
 declaration mentions it, measured by

 rg -n -e '(Notation|Infix|Reserved)' -g '*.v' \
 -g '!Structure/Limit/Power*' | grep -c -e '·'

 which returns 0.  Both notations are declared at level 30, right
 associativity -- the level Structure/Cartesian/Closed.v gives the
 exponential, these being operators of the same kind.

 Mac Lane's own [b^J] is not available at all: [y ^ x] is already the
 exponential of a cartesian closed category, declared twice in
 Structure/Cartesian/Closed.v -- at [object_scope] inside the [Closed]
 section and at [category_scope] at the end of the file.
 [⊙], sometimes used for the copower, is also unavailable --
 Theory/Isomorphism.v declares [f ⊙ g] for isomorphism composition with
 NO scope annotation, so it is global.

 WHAT IS DELIVERED HERE

 At the ELEMENTARY level, [IsPower b p ev] is [IsIndexedProduct] at the
 constant family and [IsCopower b p inj] is that read in [C^op]; both are
 [Definition]s unfolding to their donors, so every lemma about an indexed
 (co)product applies to a (co)power with no adapter, and
 [IsCopower_is_IsIndexedCoproduct] records the coproduct reading by
 [eq_refl].  [power_desc] and [copower_desc] state the universal property
 with arrows in [C] -- the copower one covariantly, no [^op] visible.

 At the CLASS level, [power J b] and [copower J b] are the chosen
 (co)products of the constant family drawn from [HasIndexedProducts] /
 [HasIndexedCoproducts], with [power_ev] (Riehl's [ev_i]),
 [copower_inj], and their universal properties.

 At the LIMIT level, [power_of_limit] and [copower_of_colimit] read a
 limit of the constant discrete diagram, with [power_ump_of_limit] and
 [copower_ump_of_colimit] the universal properties.  These are provided
 because that is the shape Theory/WeaklyInitial.v actually consumes.

 UNIVERSES, MEASURED IN THE CONSTRAINT BLOCKS

 Reproduce with [Set Printing Universes.] and [About]; reading the binder
 alone gets this wrong.

 [power@{u u0 u1 u2 u3 u4}] takes [C : Category@{u3 u4 u4}] and an index
 [Type@{u}] with [u <= u0] and nothing else touching [u]: the index
 universe is bounded above by the class's own index parameter and is
 otherwise free.  No [Set] and no equality.

 [copower] is likewise IN SUBSTANCE -- no [Set], no equality, index not
 pinned -- but NOT in binder layout, and the difference is worth printing
 rather than waving through.  [copower@{u u0 u1 u2 u3}] has FIVE binders,
 its index is [Type@{u0}], and that index carries TWO constraints
 ([u0 < u] and [u0 <= u1]) where [power]'s carries one.  Going through
 [C^op] is what reshuffles them.  The asymmetry is visible in the probe:
 the two smallness negatives print DIFFERENT messages for the two
 operators, and that is why, not an accident of phrasing.

 RECORDED CORRECTION.  An earlier revision read: "[power_of_limit@{u
 u0 u1}] and [copower_of_colimit@{u u0 u1}] take
 [C : Category@{u1 Set Set}] -- [C]'s hom AND proof universes pinned to
 [Set] -- with the INDEX [Type@{u}] left FREE.  That pin is
 Structure/Limit/Product.v's, not this file's".  The attribution was
 one step short and the pin is now gone: it came from
 Instance/Discrete.v's then-unannotated [DiscreteCat_Functor], which
 was annotated in place there in the PR "algebraic carriers are
 sets" (2026-09-17).  Measured after it, [iprod] and its limit-shaped
 siblings are stated over [C : Category@{u1 u2 u2}] with no literal
 [Set], so these two constants no longer pin [C]'s hom and proof
 universes either.  What was said about the INDEX is unchanged and is
 still what matters for the consumer: it stays FREE, since
 Theory/WeaklyInitial.v's index is a hom-type.

 Nothing in this file mentions [Sets]; the universe situation of the two
 characterizing isomorphisms is Structure/Limit/Power/Hom.v's, and is
 measured there.

 THE GAFT SPINE: ONE OF THE TWO ANONYMOUS PRODUCTS IS A POWER AND THE
 OTHER IS NOT.

 Theory/WeaklyInitial.v forms
 [Limit (DiscreteCat_Functor (fun _ : (P0 ~> P0) => P0))].  The family is
 CONSTANT, so that is a power -- the endomorphism-indexed power of [P0] --
 and Theory/WeaklyInitial.v now says so, through [power_of_limit] and
 [power_ev_of_limit], which is why this file is kept free of the
 Instance/Sets SATELLITES.

 State that precisely, because the obvious phrasing is false.  [Instance/Sets]
 ITSELF is already in this file's dependency closure, one hop away:
 Structure/Cone.v Requires it, and this file Requires Structure/Cone.
 It is likewise already in Adjunction/GAFT.v's closure, through
 Structure/Limit.  So "kept free of Instance/Sets" would be wrong, and a
 textual grep of GAFT.v for [Instance.Sets] -- which returns zero -- measures
 that file's own text, not what it Requires.

 What the split actually buys, measured by comparing the two closures: a
 combined file would add TEN modules to GAFT's, namely Functor/Hom.v, the
 four Instance/Sets satellites (Cartesian, Cartesian/Closed, Cocartesian,
 Products), the three Structure ones (Cartesian, Cartesian/Closed,
 Cocartesian), Structure/Limit/Indexed/Hom.v and Structure/Limit/Power/Hom.v.
 That is the cost avoided, and it is why the naming layer is separated from
 the hom-bijection satellite -- the same split #320 made between
 Structure/Limit/Product.v and Structure/Limit/Indexed/Hom.v, and which
 Structure/Limit/Weighted.v shows is not obligatory for a
 Structure/Limit/ file.

 The change in Theory/WeaklyInitial.v is by conversion only: the statement
 of [initial_from_weakly_initial] is untouched.

 Adjunction/SAFT.v's [cogen_power] is NOT a power, despite the
 name, and this file makes no attempt to re-express it.  Its family is
 [cogen_power_fam G c p := cog_obj G (projT1 p)] over the Σ-index
 [{ j : cog_index G & c ~> cog_obj G j }] (Adjunction/SAFT.v),
 which varies with [projT1 p]; there is no single object [b] for which it
 is [fun _ => b].  It is a product of a genuinely indexed family, and the
 word "power" in that file names the classical phrase "the unit into the
 cogenerator power is monic" rather than the constant-family construction.

 WHAT IS NOT DELIVERED

 No (co)power of a family in the enriched sense -- [J] here is a bare
 [Type], not an object of a base of enrichment, so nothing below is a
 cotensor over a monoidal category; Structure/Limit/Weighted.v's
 [WeightedColimit] at a one-object shape is the enriched reading and is not
 connected to this file.  No functoriality of [power] or [copower] in
 either argument, in particular no [J ⋔ (-)] endofunctor and no action on
 maps of index types.  No comparison of [power] with a cartesian closed
 exponential in general -- only at [Sets], in Power/Hom.v.  No claim that a
 category has powers without having all indexed products.

 STATUS: axiom-free, no [Program], no tactic.  Every constant is a
 [Definition] supplied by [:=]; the two [Example]s close by [eq_refl].  All
 22 constants -- the whole of [Print Module Category.Structure.Limit.Power],
 which lists 22 [Definition]s and no opaque constants -- report "Closed
 under the global context"; the Makefile's [print-assumptions] target audits
 the headline ones. 

 --------
 nLab：       https://ncatlab.org/nlab/show/power
 nLab：       https://ncatlab.org/nlab/show/copower
 维基百科：  https://en.wikipedia.org/wiki/Product_(category_theory)

 来源，按位置引用；单行描述是从第321期的目录条目中转录的，而不是从印刷书籍中提取的：- Mac Lane，《从业数学家的范畴》，第2版（Springer GTM 5），第III.3节，印刷页64（PDF页73），条目 [maclane:III.3:def3]，以及第III.4节，印刷页70（PDF页79），条目 [maclane:III.4:def4]。幂 [b^J] 是恒定 J 索引族在 [b] 的乘积，其特征由 [C(c, b^J) ≅ C(c, b)^J] 描述；对偶地，余幂 [J · b] 是恒定族的余积，其特征由 [C(J · b, c) ≅ C(b, c)^J] 描述。- Riehl，《范畴论的语境》，第2版，第3.5节，印刷页110（PDF页130），条目 [riehl:3.5:example4]：单个对象的迭代乘积是幂（余张量），记作 [A^I]，其可表征的通用性质 [C(X, A^I) ≅ C(X, A)^I] 通过与投影 [ev_i] 组合给出。印刷页111（PDF页）131),
 项  [riehl:3.5:example8] : 单个对象的迭代余积是
 COPOWERS（张量），写作  [I · A] ，其中  [C(∐_I A, X) ≅ C(A, X)^I] 。 - Awodey，《范畴论》，第一版（卡内基梅隆预印本，
 2005年9月），第3章，第3.2节，无编号备注，打印页
 第61页（PDF第70页），项  [awodey:3.2:remark-finite-copower] : 在集合中，一个
 有限集合  [A]  是终对象的副本的余积，
 [A ≅ 1 + 1 + ⋯ + 1] ，其中  [n = |A|] 。

 该文件是命名层；同构在隔壁。下面的所有内容都是对 Structure/Limit/Product.v 和 Structure/Limit/Coproduct.v 的常量家族读取，没有任何证明义务：每个常量都是由 [:=] 提供的。两个表征同构、[Sets] 的识别以及 Awodey 见证都存在于 Structure/Limit/Power/Hom.v 中，这里是出于依赖原因而不是主题原因——参见该文件的头部，以及下面关于 Theory/WeaklyInitial.v 的段落。

 为什么使用这些名称

 [power] 和 [copower] 是 Mac Lane、Riehl 和 nLab 使用的词汇，并且在此文件之前，它们作为顶层常量都是空闲的。重复使用方法rg -n -e '^\s*(Program\s+)?(Definition|Lemma|Theorem|Corollary|Fixpoint|Record|Class|Inductive|Instance|Example|Notation)\s+(power|copower)\b' \
 -g '*.v' -g '!Structure/Limit/Power*'-- 排除此文件及其附属文件，因为它们现在正好声明这些名称 -- 返回为空。[Pow] 不是空闲的，因此故意没有使用：两个不同的树内概念已经使用了它，它们都不是 Mac Lane 的 -- Instance/Fun/Discrete.v 的 [Fixpoint Pow (B : Category) (n : nat) : Category]，即类别的 n 次乘积，以及 Structure/Topos.v 的 [Definition Pow (a : C) := Ω ^ a] ，即拓扑幂对象。第三个接近的名称 [Sets_pow] (Instance/Sets/Products.v) 与 [Sets] 表示同一概念，也未被遮蔽：Structure/Limit/Power/Hom.v 证明它们是同构的，而不是重新定义它 -- 仅此而已。它们不可转换，Test/ProbePower.v 也明确指出：幂的载体是裸函数类型，而指数的载体是离散集合的集合态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态状态 MORPHISMS。将“free”理解为适用于匹配该模式的顶级常量声明；“power”一词广泛出现在注释和较长的名称中（[Powerset]、[GrpCosetPower]、[cogen_power]、[law_pow]、[mat_pow]、[tpower]），而本文件并未涉及这些名称。

 符号表示及为何需要选择性使用

 [J ⋔ b] 表示乘方，[J · b] 表示余乘方，它们分别在自己的 [power_scope] 中带有键 [%power]，遵循 Structure/Preadditive.v 的 [addition_scope] 先例：消费者通过 [Open Scope power_scope] 或 [%power] 键选择使用，而单纯 Require 本文件的文件不会被强制要求使用。[⋔] 是 nLab 用于表示乘方的符号，并且在整个树中完全自由：

 rg -c -e '⋔' -g '*.v' -g '!Structure/Limit/Power*' -g '!Test/ProbePower.v'不返回文件。[·] 是 Mac Lane 自己为余幂所用的符号，虽然它出现在树中，但只出现在评论中——没有任何符号声明提到它，通过

 rg -n -e '(Notation|Infix|Reserved)' -g '*.v' \
 -g '!Structure/Limit/Power*' | grep -c -e '·'

 返回 0。两个符号都在等级 30 声明，右结合性——等级 Structure/Cartesian/Closed.v 给出了指数运算，它们是同类操作符。Mac Lane 自己的 [b^J] 完全不可用：[y ^ x] 已经是一个笛卡尔闭范畴的指数，在 Structure/Cartesian/Closed.v 中被声明了两次——在 [object_scope] 的 [Closed] 部分以及文件末尾的 [category_scope]。[⊙]，有时用于余幂，也不可用——Theory/Isomorphism.v 将 [f ⊙ g] 声明为同构组合且没有范围注解，因此它是全局的。

 这里交付的是什么在初级水平上，[IsPower b p ev] 在常量族中是 [IsIndexedProduct]，[IsCopower b p inj] 在 [C^op] 中读取；两者都是 [Definition] 展开到它们的给予者，因此关于索引 (co)积的每个引理都适用于没有适配器的 (co)幂，并且 [IsCopower_is_IsIndexedCoproduct] 通过 [eq_refl] 记录余积读取。[power_desc] 和 [copower_desc] 使用 [C] 中的箭头陈述了普遍性质——对于 copower 是协变的，没有可见的 [^op]。

 在类级别上，[power J b] 和 [copower J b] 是从 [HasIndexedProducts] / [HasIndexedCoproducts] 中抽取的常量族的所选 (co)积，带有 [power_ev]（Riehl 的 [ev_i]）、[copower_inj] 及其普遍性质。在 LIMIT 级别，[power_of_limit] 和 [copower_of_colimit] 读取常数离散图的极限，而 [power_ump_of_limit] 和 [copower_ump_of_colimit] 表示泛性质。这些是提供的，因为 Shape Theory/WeaklyInitial.v 实际上使用了它们。

 宇宙，以约束块为单位测量

 用 [Set Printing Universes.] 和 [About] 重现；单独读取绑定器会出错。

 [power@{u u0 u1 u2 u3 u4}] 接收 [C : Category@{u3 u4 u4}] 和索引 [Type@{u}] 及 [u <= u0]，而没有其他触及 [u] 的东西：索引宇宙由该类自身的索引参数在上方界定，其它方面是自由的。没有 [Set]，也没有等式。[copower] 在实质上也是如此——没有 [Set]，没有相等，索引未固定——但不在绑定器布局中，这种差异值得打印而不是忽略。[copower@{u u0 u1 u2 u3}] 有五个绑定器，它的索引是 [Type@{u0}]，并且该索引有两个约束（[u0 < u] 和 [u0 <= u1]），而 [power] 的索引只有一个。通过 [C^op] 可以重新排列它们。这种不对称可以通过探测看出：两个小型负值为两个运算符打印出不同的信息，这就是原因，而不是措辞的偶然。已记录的更正。早期的修订版写道：“[power_of_limit@{u u0 u1}] 和 [copower_of_colimit@{u u0 u1}] 取 [C : Category@{u1 Set Set}] -- [C] 的同态和证明宇宙固定在 [Set] -- 而索引 [Type@{u}] 保持自由。那个固定属于 Structure/Limit/Product.v，而不是这个文件的。”归属缺少了一步，现在固定已消失：它来自 Instance/Discrete.v 当时未标注的 [DiscreteCat_Functor] ，该常量在 PR “algebraic carriers are sets”（2026-09-17）中已在原位标注。在此之后测量，[iprod] 及其极限形状的同类在 [C : Category@{u1 u2 u2}] 上声明，没有字面上的 [Set]，因此这两个常量也不再固定 [C] 的同态和证明宇宙。关于 INDEX 的内容没有改变，仍然是消费者关心的：它保持 FREE，因为 Theory/WeaklyInitial.v 的索引是一个 hom 类型。

 这个文件中没有提到 [Sets]；两个表征同构的宇宙情况是在 Structure/Limit/Power/Hom.v 中，并在那里进行衡量。

 GAFT 脊柱：两个匿名积之一是幂，另一个不是。

 Theory/WeaklyInitial.v 形成 [Limit (DiscreteCat_Functor (fun _ : (P0 ~> P0) => P0))]。该族是 CONSTANT 的，因此它是一个幂——[P0] 的自同态索引幂——Theory/WeaklyInitial.v 现在也是这样说明的，通过 [power_of_limit] 和 [power_ev_of_limit]，这也是为什么这个文件保持为 Instance/Sets SATELLITES 免费的原因。要精确地说明这一点，因为明显的表述是错误的。[Instance/Sets] 本身已经在此文件的依赖闭包中，仅一步之遥：Structure/Cone.v 需要它，而此文件需要 Structure/Cone。同样，它已经通过 Structure/Limit 在 Adjunction/GAFT.v 的闭包中。因此，“保持 Instance/Sets 不包含它”是错误的，而对 GAFT.v 中文本进行 [Instance.Sets] 的文本搜索——结果为零——测量的是该文件自身的文本，而不是它所需要的内容。通过比较两个闭包来衡量拆分实际带来的好处：一个合并的文件将向 GAFT 添加 TEN 个模块，即 Functor/Hom.v、四个 Instance/Sets 卫星模块（Cartesian、Cartesian/Closed、Cocartesian、Products）、三个 Structure 模块（Cartesian、Cartesian/Closed、Cocartesian）、Structure/Limit/Indexed/Hom.v 和 Structure/Limit/Power/Hom.v。这就是避免的成本，这也是为什么命名层与同态-双射卫星分开的原因——同样的拆分 #320 曾在 Structure/Limit/Product.v 与 Structure/Limit/Indexed/Hom.v 之间进行过，而 Structure/Limit/Weighted.v 显示这对于 Structure/Limit/ 文件来说并非强制性的。

 Theory/WeaklyInitial.v 的变化只是转换：[initial_from_weakly_initial] 的陈述保持不变。Adjunction/SAFT.v 的 [cogen_power] 并不是一个幂，尽管名字如此，而且这个文件也没有尝试重新表达它。它的族是 Σ-索引上的 [cogen_power_fam G c p := cog_obj G (projT1 p)]，[{ j : cog_index G & c ~> cog_obj G j }] (Adjunction/SAFT.v)，它随 [projT1 p] 变化；没有单一对象 [b] 对应它是 [fun _ => b]。它是一个真正索引族的乘积，而文件中的“幂”一词指的是经典短语“单元到余生成元幂是单射”，而不是常值族的构造。

 未交付的内容是什么在增强意义下，家庭没有（共）幂——[J] 这里是一个裸的 [Type]，而不是一个增强基的对象，所以下面没有任何东西是单态范畴上的共张量；Structure/Limit/Weighted.v 的 [WeightedColimit] 在单对象形状下是增强的解读，并且与此文件无关。 [power] 或 [copower] 在任一参数上没有函子性，特别是没有 [J ⋔ (-)] 自函子，也没有对指标类型的箭头作用。没有一般意义上 [power] 与笛卡尔闭指数的对比——仅在 [Sets] ，在 Power/Hom.v 中。没有声称一个范畴具有幂而没有拥有所有指标积。状态：无公理，无 [Program]，无策略。每个常量都是由 [:=] 提供的 [Definition]；两个 [Example] 由 [eq_refl] 附近关闭。所有 22 个常量——整个 [Print Module Category.Structure.Limit.Power]，列出了 22 个 [Definition] 且无不透明常量——报告“在全局上下文下封闭”；Makefile 的 [print-assumptions] 目标会审核主要的常量。
*)

(* * ** The elementary universal properties, at a constant family / * ** 在一个恒定族下的基本通用性质 *)

(*
 A power of [b] by the index [J]: an object [p] with a family [ev] of
 evaluation maps that is universal among such families.  Mac Lane's [b^J];
 Riehl's [A^I] with [ev_i] the projections. 

 --------
 由指数 [J] 给出的 [b] 的幂：一个对象 [p]，带有一族 [ev] 的评估映射，在此类族中是普遍的。Mac Lane 的 [b^J]；Riehl 的 [A^I]，其中 [ev_i] 为投影。
*)
Definition IsPower {C : Category} {J : Type} (b p : C)
  (ev : ∀ _ : J, p ~> b) : Type :=
  IsIndexedProduct (fun _ : J => b) p ev.

(*
 A copower of [b] by [J]: dually, an object with a universal family of
 injections.  Mac Lane's [J · b]; Riehl's [I · A]. 

 --------
 由 [J] 定义的 [b] 的协积：对偶地，一个具有通用注入族的对象。Mac Lane 的 [J · b]；Riehl 的 [I · A]。
*)
Definition IsCopower {C : Category} {J : Type} (b p : C)
  (inj : ∀ _ : J, b ~> p) : Type :=
  @IsPower (C^op) J b p inj.

Example IsPower_is_IsIndexedProduct {C : Category} {J : Type} (b p : C)
  (ev : ∀ _ : J, p ~> b) :
  IsPower b p ev = IsIndexedProduct (fun _ : J => b) p ev := eq_refl.

Example IsCopower_is_IsIndexedCoproduct {C : Category} {J : Type} (b p : C)
  (inj : ∀ _ : J, b ~> p) :
  IsCopower b p inj = IsIndexedCoproduct (fun _ : J => b) p inj := eq_refl.

(*
 The universal property, read with arrows in [C].  The copower form is
 covariant: no [^op] appears in its statement. 

 --------
 普遍性质，在 [C] 中用箭头表示。余幂形式是协变的：在其陈述中没有出现 [^op]。
*)
Definition power_desc {C : Category} {J : Type} {b p : C}
  {ev : ∀ _ : J, p ~> b} (H : IsPower b p ev)
  {c : C} (pi : ∀ _ : J, c ~> b) :
  ∃! u : c ~> p, ∀ j : J, ev j ∘ u ≈ pi j :=
  @iprod_desc C J (fun _ : J => b) p ev H c pi.

Definition copower_desc {C : Category} {J : Type} {b p : C}
  {inj : ∀ _ : J, b ~> p} (H : IsCopower b p inj)
  {c : C} (iota : ∀ _ : J, b ~> c) :
  ∃! u : p ~> c, ∀ j : J, u ∘ inj j ≈ iota j :=
  @icoprod_desc C J (fun _ : J => b) p inj H c iota.

(* Smart constructors, taking the data in that same covariant form. / 智能构造函数，采用相同协变形式的数据。 *)
Definition Build_IsPower {C : Category} {J : Type} (b p : C)
  (ev : ∀ _ : J, p ~> b)
  (desc : ∀ (c : C) (pi : ∀ _ : J, c ~> b),
            ∃! u : c ~> p, ∀ j : J, ev j ∘ u ≈ pi j) :
  IsPower b p ev :=
  @Build_IsIndexedProduct C J (fun _ : J => b) p ev desc.

Definition Build_IsCopower {C : Category} {J : Type} (b p : C)
  (inj : ∀ _ : J, b ~> p)
  (desc : ∀ (c : C) (iota : ∀ _ : J, b ~> c),
            ∃! u : p ~> c, ∀ j : J, u ∘ inj j ≈ iota j) :
  IsCopower b p inj :=
  @Build_IsIndexedCoproduct C J (fun _ : J => b) p inj desc.

(* * ** The chosen power and copower, from the classes / * ** 选择的能力和共能力，来自各个职业 *)

Definition power {C : Category} {HP : @HasIndexedProducts C}
  (J : Type) (b : C) : C :=
  indexed_product (fun _ : J => b).

Definition power_ev {C : Category} {HP : @HasIndexedProducts C}
  (J : Type) (b : C) (j : J) : power J b ~> b :=
  indexed_product_proj (fun _ : J => b) j.

Definition power_ump {C : Category} {HP : @HasIndexedProducts C}
  (J : Type) (b : C) : IsPower b (power J b) (power_ev J b) :=
  indexed_product_ump (fun _ : J => b).

Definition copower {C : Category} {HC : @HasIndexedCoproducts C}
  (J : Type) (b : C) : C :=
  @power (C^op) HC J b.

Definition copower_inj {C : Category} {HC : @HasIndexedCoproducts C}
  (J : Type) (b : C) (j : J) : b ~> copower J b :=
  @power_ev (C^op) HC J b j.

Definition copower_ump {C : Category} {HC : @HasIndexedCoproducts C}
  (J : Type) (b : C) : IsCopower b (copower J b) (copower_inj J b) :=
  @power_ump (C^op) HC J b.

(*
   * ** The limit-shaped reading

   [power_of_limit] and [copower_of_colimit] carry the universe pin that
   Structure/Limit/Product.v's header describes: [DiscreteCat J]'s hom-setoid
   is strict equality, so forming the limit constrains [C]'s hom and proof
   universes (the index, measured in the header, stays free).  They are
   supplied because that is the shape Theory/WeaklyInitial.v consumes -- and
   only that file: Adjunction/SAFT.v's superficially similar [cogen_power] is
   not a power, per the header.  Note the second one reads a limit taken IN
   [C^op] -- the shape
   Structure/Limit/Coproduct.v's header records, NOT [Colimit] in the sense
   of Structure/Limit.v; no translation between the two is offered here
   either. 

   --------
   * ** 限制形状的极限

   [power_of_limit] 和 [copower_of_colimit] 带有宇宙引脚，
   其在 Structure/Limit/Product.v 的头文件中描述：[DiscreteCat J] 的同态集等式是严格相等的，因此构造极限会约束 [C] 的同态和证明宇宙（头文件中测量的索引保持自由）。它们之所以被提供，是因为 Shape Theory/WeaklyInitial.v 使用它们 —— 而且只有那个文件：Adjunction/SAFT.v 表面上类似的 [cogen_power] 并不是幂，如头文件所示。注意第二个读作在 [C^op] 中取得的极限 —— 形状 Structure/Limit/Coproduct.v 的头文件记录，而不是 Structure/Limit.v 意义上的 [Colimit]；这里也没有提供两者之间的翻译。
*)

Definition power_of_limit {C : Category} {J : Type} (b : C)
  (L : Limit (DiscreteCat_Functor (fun _ : J => b))) : C :=
  iprod (fun _ : J => b) L.

Definition power_ev_of_limit {C : Category} {J : Type} (b : C)
  (L : Limit (DiscreteCat_Functor (fun _ : J => b))) (j : J) :
  power_of_limit b L ~> b :=
  iprod_proj (fun _ : J => b) L j.

Definition power_ump_of_limit {C : Category} {J : Type} (b : C)
  (L : Limit (DiscreteCat_Functor (fun _ : J => b)))
  (c : C) (pi : ∀ _ : J, c ~> b) :
  ∃! u : c ~> power_of_limit b L, ∀ j : J, power_ev_of_limit b L j ∘ u ≈ pi j :=
  iprod_ump (fun _ : J => b) L c pi.

Definition limit_is_power {C : Category} {J : Type} (b : C)
  (L : Limit (DiscreteCat_Functor (fun _ : J => b))) :
  IsPower b (power_of_limit b L) (power_ev_of_limit b L) :=
  limit_is_indexed_product (fun _ : J => b) L.

Definition copower_of_colimit {C : Category} {J : Type} (b : C)
  (L : Limit (@DiscreteCat_Functor J (C^op) (fun _ : J => b))) : C :=
  @power_of_limit (C^op) J b L.

Definition copower_inj_of_colimit {C : Category} {J : Type} (b : C)
  (L : Limit (@DiscreteCat_Functor J (C^op) (fun _ : J => b))) (j : J) :
  b ~> copower_of_colimit b L :=
  @power_ev_of_limit (C^op) J b L j.

Definition copower_ump_of_colimit {C : Category} {J : Type} (b : C)
  (L : Limit (@DiscreteCat_Functor J (C^op) (fun _ : J => b)))
  (c : C) (iota : ∀ _ : J, b ~> c) :
  ∃! u : copower_of_colimit b L ~> c,
    ∀ j : J, u ∘ copower_inj_of_colimit b L j ≈ iota j :=
  @power_ump_of_limit (C^op) J b L c iota.

Definition colimit_is_copower {C : Category} {J : Type} (b : C)
  (L : Limit (@DiscreteCat_Functor J (C^op) (fun _ : J => b))) :
  IsCopower b (copower_of_colimit b L) (copower_inj_of_colimit b L) :=
  @limit_is_power (C^op) J b L.

(** ** Notation, opt-in / ** 符号，选择加入 *)

Declare Scope power_scope.
Delimit Scope power_scope with power.

Notation "J ⋔ b" := (power J b)
  (at level 30, right associativity) : power_scope.
Notation "J · b" := (copower J b)
  (at level 30, right associativity) : power_scope.
