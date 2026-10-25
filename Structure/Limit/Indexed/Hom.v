Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Discrete.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.

Generalizable All Variables.

(* * * The hom-set form of the indexed product and coproduct / * * 指数积和余积的霍姆集形式 *)

(*
 nLab:      https://ncatlab.org/nlab/show/product
 nLab:      https://ncatlab.org/nlab/show/coproduct
 Wikipedia: https://en.wikipedia.org/wiki/Coproduct

 Sources, cited BY LOCATION; the descriptions are transcribed from the
 catalog entries of issue #320 rather than from the printed books:

 - Mac Lane, "Categories for the Working Mathematician", 2nd ed.
 (Springer GTM 5), section III.3, printed p. 64 (PDF p. 73), item
 [maclane:III.3:def2]: for a set X read as a discrete category, the
 X-fold coproduct of a family {a_x} is an object with injections
 through which every family of arrows out factors uniquely --
 "equivalently, a bijection C(⊔_x a_x, c) ≅ ∏_x C(a_x, c) natural in
 c".  It is that "equivalently" which this file supplies.
 - Riehl, "Category Theory in Context", 2nd ed., section 3.1, printed
 pp. 90-91 (PDF pp. 110-111), item [riehl:3.1:remark27], clauses (i)
 and (ii): morphisms out of an I-indexed coproduct correspond
 naturally and bijectively to I-indexed families,
 C(∐_i A_i, X) ≅ ∏_i C(A_i, X), the i-th component being restriction
 along the inclusion; dually C(X, ∏_j B_j) ≅ ∏_j C(X, B_j).
 Clause (iii), the (I × J)-matrix, is issue #336 and is NOT here.

 WHAT WAS ALREADY IN THE TREE, AND WHAT THIS FILE ADDS

 The two universal properties themselves are Structure/Limit/Product.v
 ([IsIndexedProduct], [iprod], [HasIndexedProducts]) and
 Structure/Limit/Coproduct.v (its definitional dual at [C^op]), and both
 are inhabited at [Sets] (Instance/Sets/Products.v).  What
 neither file states is the hom-set bijection: as of this commit,

 rg -n '≅\[Sets\]|@Isomorphism|hom_iso' \
 Structure/Limit/Product.v Structure/Limit/Coproduct.v

 returns nothing, and so does [rg -c 'Isomorphism'] over the same two
 files.  [iprod_desc] and [icoprod_desc] give UNIQUE EXISTENCE -- ∃! u,
 ∀ a, proj a ∘ u ≈ pi a -- with no naturality anywhere.  This file
 upgrades both to an [Isomorphism] in a functor category over [Sets],
 natural in the varying object, and relates each back to the pre-existing
 [∃!] accessor so the two presentations cannot drift.

 WHY A NEW FILE RATHER THAN AN EXTENSION IN PLACE

 Not taste: a cycle.  The right-hand side ∏_a C(c, f a) is the
 dependent-function setoid [Sets_iprod_obj], and the statement lives in
 [Sets]; but Instance/Sets/Products.v already Requires
 Structure/Limit/Product.v AND Structure/Limit/Coproduct.v, so neither of
 those two can Require it back.  Structure/Limit/Weighted.v is the
 in-tree precedent for a Structure/Limit/ file that Requires
 Instance/Sets and builds a [J ⟶ Sets] functor out of hom-setoids.

 WHICH DISCRETE-DIAGRAM SHAPE THIS IS STATED AGAINST -- NEITHER

 Structure/Limit/Coproduct.v's header records a real obstruction: its
 [icoprod] reads a [Limit] of the discrete diagram taken IN [C^op],
 namely [Limit (@DiscreteCat_Functor A (C^op) f)], and NOT a [Colimit] in
 the sense of Structure/Limit.v, which sets [Colimit F := Limit (F^op)]
 and so indexes over [(DiscreteCat A)^op]; the two categories are not
 identified, and no translation between them exists in the tree.

 This file states everything against the ELEMENTARY records
 [IsIndexedProduct] and [IsIndexedCoproduct], which mention no discrete
 diagram at all, so the question does not arise and no translation is
 needed or supplied.  That choice is not merely evasive -- it is what
 makes the result compose with every presentation the tree carries
 ACCESSORS for, and all four compositions are exhibited rather than
 asserted:

 [limit_hom_iso]             through [limit_is_indexed_product]
 [colimit_hom_iso]           through [colimit_is_indexed_coproduct]
 [indexed_product_hom_iso]   through [indexed_product_ump]   (the class)
 [indexed_coproduct_hom_iso] through [indexed_coproduct_ump] (the class)

 Read "every presentation the tree carries accessors for" strictly: it is
 NOT every expressible shape.  [Colimit (@DiscreteCat_Functor A C f)] --
 the form Structure/Limit.v defines, indexing over [(DiscreteCat A)^op]
 -- is formable and is a genuine in-tree presentation, and
 [colimit_hom_iso] does NOT accept it: a term of that type is rejected
 against the expected [Limit (@DiscreteCat_Functor A (C^op) f)].  That is
 the same non-identification recorded above and in NOT DELIVERED below, and
 it is the one shape these four compositions leave out of reach.  Nothing
 here narrows it; the translation remains open.

 THE COPRODUCT SIDE COSTS NOTHING, AND THAT IS THE POINT OF THE SYMMETRY

 Every coproduct-side constant is its product-side counterpart applied at
 [C^op], supplied by [:=] with no tactic and no obligation -- the
 discipline Structure/Limit/Coproduct.v already follows.  Two conversions
 make it work and both were measured outside the tree, then relied on
 here: [(C^op)^op = C] and [@Curried_CoHom (C^op) p = @Curried_Hom C p],
 each by [eq_refl].  (They are not landed as [Example]s, and the reason is
 NOT the [make todo] scan: that scan greps for a fixed list of
 proof-hole and TODO keywords, none of which a positive [eq_refl]
 contains, so landing them would cost nothing there.  They are guarded
 implicitly instead, by the coproduct section below typechecking at all.
 Do not quote that keyword list in a source file: one of its entries is
 also what the separate proof-hole gate counts, so quoting it raises that
 count and breaks the build.  Note too that the two gates use DIFFERENT
 patterns -- the Makefile's is word-bounded and lefthook's is not, so
 lefthook also counts that keyword as a substring of longer words.  Both
 were measured the hard way, in that order.)  The second holds because [Curried_CoHom D] IS
 [Curried_Hom D^op] by Definition (Functor/Hom.v).  So the two clauses
 of Riehl's Remark 3.1.27 are symmetric BY CONSTRUCTION here, not by a
 parallel development; [icoprod_hom_functor_is_op] records the reading.

 WHAT IS PROVED, AND AT WHICH STRENGTH

 For an arbitrary family [f : A → C] and an arbitrary candidate cone:

 [iprod_hom_functor f : C^op ⟶ Sets]   is  c ↦ ∏_a C(c, f a)
 [icoprod_hom_functor f : C ⟶ Sets]    is  c ↦ ∏_a C(f a, c)

 and [iprod_hom_transform f q proj] is the comparison natural
 transformation [Hom ─,q] ⟹ ∏_a [Hom ─,f a], u ↦ (proj a ∘ u)_a.  It is
 defined for ANY family [proj], with NO universal property assumed: its
 naturality is associativity and nothing else.  The content is therefore
 entirely in INVERTIBILITY, and that is delivered as a biconditional --

 [iprod_iff_hom_iso]   : IsIndexedProduct f q proj
 ↔ IsIsomorphism (iprod_hom_transform f q proj)
 [icoprod_iff_hom_iso] : the same at [C^op]

 -- whose two legs are [iprod_hom_iso] (which packages the isomorphism in
 [[C^op, Sets]] proper) and [iprod_of_hom_iso].  The [↔] is [Lib]'s
 Type-valued [iffT], and the pairing is transparent, so projecting it
 returns the named leg by conversion -- machine-checked by
 [iprod_iff_hom_iso_fst]/[_snd] and their coproduct duals, at Leibniz [=].

 STRICT-FIRST MEASUREMENT.  The following hold at Leibniz [=] by
 [eq_refl], and are recorded as [Example]s so the claims are
 machine-checked rather than inferred:

 - the forward leg of the isomorphism IS the comparison map, and the
 backward leg IS [iprod_hom_inverse] ([iprod_hom_iso_to],
 [iprod_hom_iso_from], and [icoprod_hom_iso_to]);
 - the backward leg's VALUE is the mediator named by the pre-existing
 [∃!] accessor -- [iprod_hom_iso_from_is_desc] and
 [icoprod_hom_iso_from_is_desc] are the "does not drift" guarantee at
 its strongest available form;
 - the forward leg computes to restriction along the projections
 ([iprod_hom_transform_computes]) and, on the coproduct side, to
 [u ∘ inj a] ([icoprod_hom_transform_computes]);
 - the right-hand side IS the tree's own indexed product read in [Sets]
 ([iprod_hom_functor_is_indexed_product] and its dual);
 - at [Sets] the backward leg computes to the tupling and case maps of
 Instance/Sets/Products.v ([Sets_iprod_hom_from_computes],
 [Sets_icoprod_hom_from_computes]), and the class-derived isomorphism
 is the SAME TERM as the one read straight off [Sets_IsIndexedProduct]
 ([Sets_iprod_hom_iso_is_class] and its dual).

 TWO STRICT ATTEMPTS WERE MADE AND REFUTED, both pinned as [Fail]
 probes in Test/ProbeIndexedHom.v with positive controls: the ROUND TRIP
 does not compute, neither at an abstract product nor at the concrete
 [Sets] one.  Recovering [u] from the family it restricts to is exactly
 the uniqueness clause of [iprod_desc], a [≈]-level fact.  At [Sets] the
 diagnosis is sharper and is itself pinned by a control: [SetoidMorphism]
 has primitive projections with eta, the [morphism] fields DO agree on the
 nose, and what differs is the [proper_morphism] certificate, which the
 tupling rebuilds as its own obligation.

 UNIVERSES, MEASURED IN THE CONSTRAINT BLOCKS

 Reproduce with [Set Printing Universes.] and [About].  Reading the
 binder alone gets this wrong; the constraint block is the authority.

 [iprod_hom_functor@{u u0 u1 u2 u3 u4}] takes [C : Category@{u3 u4 u4}]
 and [A : Type@{u}] with [u <= u2] and [u4 <= u2] -- the index universe
 and [C]'s hom universe are each bounded by the TARGET [Sets]' carrier
 universe [u2] and are unrelated to each other.  So the target functor
 alone tolerates an index strictly larger than [C]'s homs.

 The COMPARISON MAP does not, and the cause is worth knowing.  Its source
 is the hom-functor, whose objects ARE the hom-setoids of [C]; a
 [SetoidObject] carries its [Setoid] as a field, and neither record is
 cumulative here (measured: lifting a [Setoid@{a a}] to a [Setoid@{b b}]
 with [a < b] is rejected, and likewise for [SetoidObject]), so the [Sets]
 in which the comparison lives has its carrier universe forced EQUAL to
 [C]'s hom universe rather than merely above it -- an annotated variant
 declaring the two apart was attempted and reports "Cannot enforce
 uh = us because uh < us".  The index bound follows.  This is pinned in Test/ProbeIndexedHom.v
 as a formability negative with the exact message "Cannot enforce
 ua <= uh because uh < ua", against two controls showing that neither
 functor alone is what gets rejected.  In practice the bound costs
 nothing that cumulativity does not already give: an index at or below
 [C]'s hom universe lifts, and this is the same smallness side condition
 Instance/Sets/Products.v's header analyses at [Sets].

 The two LIMIT-shaped bridges carry [{A : Set}].  RECORDED CORRECTION to
 the analysis of that binder: an earlier revision said it "is a
 COMBINATION of two facts rather than one, which the probe file
 separates.  [Structure/Limit/Product.v]'s [iprod] is over
 [C : Category@{u Set Set}] -- [DiscreteCat]'s hom-setoid is strict
 equality -- with its own index universe FREE; the probe's controls show
 [Limit (DiscreteCat_Functor f)] and [iprod f L] are both formable over
 such a [C] at an index strictly above [Set].  Adding this file's bound at
 [C]'s hom universe, which is [Set] there, is what cuts the index to
 [Set]."  The donor half of that combination is GONE: [iprod] inherited
 its [Set] from Instance/Discrete.v's unannotated [DiscreteCat_Functor],
 annotated in place there in the PR "algebraic carriers are sets"
 (2026-09-17), and [iprod@{u u0 u1 u2 u3}] is now over
 [C : Category@{u1 u2 u2}].  Test/ProbeIndexedHom.v re-measured the two
 negatives in a copy of the whole file with its section's [C] declared at
 a hom universe strictly above [Set]: both still refuse, so the [{A : Set}]
 binder is THIS FILE'S bound alone and not a combination.  The section's
 [C] is left at the [Set] instance because that is the instance the
 binder is about; see that probe's header.  The class-shaped bridges [indexed_product_hom_iso] and
 [indexed_coproduct_hom_iso] carry no such pin, mentioning no discrete
 diagram.

 NON-VACUITY, IN BOTH DIRECTIONS

 The conditional is instantiated at the tree's only inhabitants:
 [Sets_iprod_hom_iso] and [Sets_icoprod_hom_iso] over
 Instance/Sets/Products.v, with both backward legs computing.  And the
 INVERTIBILITY hypothesis is proved not to be vacuous, which the
 instantiations alone would not show: [Sets_bad_not_iprod] and
 [Sets_bad_not_icoprod] exhibit a candidate cone in [Sets] -- the
 two-element setoid with the constantly-true map for its single
 projection -- whose comparison map is not invertible, and conclude
 through the biconditional's forward leg that it is not an indexed
 (co)product.  So [iprod_of_hom_iso]'s hypothesis genuinely selects.

 WHAT IS NOT DELIVERED

 No (I × J)-matrix form (Riehl clause (iii), issue #336).  No translation
 between [(DiscreteCat A)^op] and [DiscreteCat A]: the question is
 side-stepped rather than settled, exactly as before this file.  No
 naturality in the FAMILY [f] or in the index [A], only in the varying
 object.  No [Representable] instance for either functor, and no
 universal-element packaging.  Nothing is claimed about a category
 without the relevant (co)product: the comparison map exists there, but
 this file exhibits no such category.

 STATUS: axiom-free.  All 59 constants -- 47 named plus 12 [Program]
 obligations, enumerated by [Print Module] per the docs/AXIOMS.md
 methodology -- report "Closed under the global context"; the Makefile's
 [print-assumptions] target audits the headline ones.  Nothing here
 appeals to funext, choice, or UIP.  The concrete [Sets] witness of a
 small coproduct is issue #254's, in Instance/Sets/Products.v, and is not
 duplicated; issue #729 consumes Structure/Limit/Coproduct.v and is not
 affected by this file. 

 --------
 nLab:       https://ncatlab.org/nlab/show/product 
 nLab:       https://ncatlab.org/nlab/show/coproduct 
 维基百科:  https://en.wikipedia.org/wiki/Coproduct 

 来源，按位置引用；描述是从第 #320 期目录条目转录的，而不是从印刷书籍中：- Mac Lane，《为工作的数学家准备的范畴论》，第2版（Springer GTM 5），第三部分第3节，印刷版第64页（PDF第73页），条目 [maclane:III.3:def2]：对于一个集合 X，当作离散范畴来理解时，族 {a_x} 的 X 重余积是一个具有注射的对象，通过该注射，每个出射箭头族都可以唯一分解——“等价地，存在一个自然于 c 的双射 C(⊔_x a_x, c) ≅ ∏_x C(a_x, c)”。正是这个“等价地”是本文件提供的。- Riehl，《情境中的范畴论》，第2版，第3.1节，印刷版第90-91页（PDF页110-111)，条目 [riehl:3.1:remark27]，条款 (i) 和 (ii)：从 I 索引的余积出的态射自然且一一对应于 I 索引的族，C(∐_i A_i, X) ≅ ∏_i C(A_i, X)，第 i 个分量是沿包含的限制；对偶地，C(X, ∏_j B_j) ≅ ∏_j C(X, B_j)。条款 (iii)，(I × J) 矩阵，是第 336 号问题，这里没有涉及。

 树中已有的内容以及此文件新增的内容

 这两个极限性质本身是 Structure/Limit/Product.v（[IsIndexedProduct]，[iprod]，[HasIndexedProducts]）以及 Structure/Limit/Coproduct.v（其在 [C^op] 的定义性对偶），并且两者在 [Sets]（Instance/Sets/Products.v）都有实例化。 这两个文件都没有陈述的是同态集的双射：截至此提交,rg -n '≅\ [Sets\] |@Isomorphism|hom_iso' \
 Structure/Limit/Product.v Structure/Limit/Coproduct.v

 返回为空，[rg -c 'Isomorphism'] 在相同的两个文件上也是如此。[iprod_desc] 和 [icoprod_desc] 给出唯一存在性 -- ∃! u, ∀ a, proj a ∘ u ≈ pi a -- 但没有任何自然性。这个文件将两者在 [Sets] 上的函子范畴中升级为 [Isomorphism]，对变化的对象是自然的，并将每个与已有的 [∃!] 访问器关联起来，因此两种表达方式不会偏离。

 为什么要创建新文件而不是在原地扩展不尝试：一个循环。右侧 ∏_a C(c, f a) 是依赖函数集合 [Sets_iprod_obj]，而该语句存在于 [Sets]；但 Instance/Sets/Products.v 已经需要 Structure/Limit/Product.v 和 Structure/Limit/Coproduct.v，所以这两个都不能反过来要求它。Structure/Limit/Weighted.v 是 Structure/Limit/ 文件中需要 Instance/Sets 并从同态集合构建 [J ⟶ Sets]函子的一棵树内先例。

 针对哪种离散图形来陈述——都不是Structure/Limit/Coproduct.v 的头部记录了一个真实的阻碍：它的 [icoprod] 读取了一个在 [C^op] 中取的离散图 [Limit]，即 [Limit (@DiscreteCat_Functor A (C^op) f)]，而不是 Structure/Limit.v 意义下的 [Colimit]，后者设定了 [Colimit F := Limit (F^op)] 并因此在 [(DiscreteCat A)^op] 上建立索引；这两个范畴没有被认同，并且在树中不存在它们之间的转换。

 该文件将所有内容与 ELEMENTARY 记录 [IsIndexedProduct] 和 [IsIndexedCoproduct] 对立，这些记录根本没有提到离散图，因此问题并不存在，也不需要或提供任何转换。这个选择不仅仅是回避——它正是使结果能够与树中携带访问器的每个表示组合在一起的原因，并且四个组合都被展示出来而不是仅仅被声明：[limit_hom_iso] 通过 [limit_is_indexed_product] 
 [colimit_hom_iso] 通过 [colimit_is_indexed_coproduct] 
 [indexed_product_hom_iso] 通过 [indexed_product_ump] （该类）
 [indexed_coproduct_hom_iso] 通过 [indexed_coproduct_ump] （该类）

 严格地阅读“树所携带的所有呈现的访问器”：它并不是
 每一个可表达的形状。 [Colimit (@DiscreteCat_Functor A C f)] --
 Structure/Limit.v 定义的形式，对 [(DiscreteCat A)^op] 进行索引
 -- 是可形成的并且是一个真正的树内呈现，并且
 [colimit_hom_iso] 不接受它：该类型的项会在与预期 [Limit (@DiscreteCat_Functor A (C^op) f)] 对比时被拒绝。
 这与上面记录以及下面“未交付”中描述的非同一性相同，
 并且这是这四个组合无法触及的形状。这里没有任何东西缩小它；翻译仍然保持开放。

 余积这边不产生任何成本，这就是对称性的重点每个余积侧常数都是其积侧对应项在 [C^op] 上的应用，由 [:=] 提供，无策略且无义务——Structure/Limit/Coproduct.v 这个模块已经遵循了这一点。两次转换使其生效，这两次转换都是在树之外测量的，然后在此依赖：[(C^op)^op = C] 和 [@Curried_CoHom (C^op) p = @Curried_Hom C p]，每个由 [eq_refl] 提供。（它们未作为 [Example] 落地，原因不是 [make todo] 扫描：该扫描仅检索固定列表中的证明孔和 TODO 关键词，而积极的 [eq_refl] 不包含其中任何一个，因此在那儿落地毫无成本。它们反而由余积部分在类型检查时隐式保护。）不要在源文件中引用那个关键字列表：它其中的一条条目也是单独证明孔门的计数项，所以引用它会增加那个计数并破坏构建。还要注意，这两个门使用的是不同的模式——Makefile 的模式是词边界限定的，而 lefthook 的模式不是，因此 lefthook 还会将该关键字计为更长单词的子串。两者都是通过艰难的方式测量的，按此顺序。第二个成立，因为 [Curried_CoHom D] 根据定义（Functor/Hom.v）就是 [Curried_Hom D^op]。因此，Riehl 的 Remark 3.1.27 的两个条款在这里是通过构造对称的，而不是通过平行展开；[icoprod_hom_functor_is_op] 记录了该读取结果。

 被证明的内容及其强度

 对于任意族 [f : A → C] 和任意候选圆锥：

 [iprod_hom_functor f : C^op ⟶ Sets] 是 c ↦ ∏_a C(c, f a)
 [icoprod_hom_functor f : C ⟶ Sets] 是 c ↦ ∏_a C(f a, c)并且 [iprod_hom_transform f q proj] 是比较自然变换 [Hom ─,q] ⟹ ∏_a [Hom ─,f a]，u ↦ (proj a ∘ u)_a。它对于任何家族 [proj] 都定义，不假设任何泛性质：它的自然性仅是结合性而已。因此，其内容完全在于可逆性，并以双条件式给出——

 [iprod_iff_hom_iso]    : IsIndexedProduct f q proj
 ↔ IsIsomorphism (iprod_hom_transform f q proj)
 [icoprod_iff_hom_iso]  : 在 [C^op] 上相同-- 其两条腿是 [iprod_hom_iso]（在 [[C^op, Sets] 中正确封装同构）和 [iprod_of_hom_iso]。[↔] 是 [Lib] 的类型值 [iffT]，并且配对是透明的，因此投影它会通过转换返回命名的腿——由 [iprod_iff_hom_iso_fst] / [_snd] 及其余积对偶在 Leibniz [=] 上进行机器检查。

 严格优先测量。在 Leibniz [=] 上，由 [eq_refl] 保证如下情况，并记录为 [Example]，因此这些声明是经过机器检查的，而不是推断的：- 同构的前向分支就是比较映射，而后向分支就是 [iprod_hom_inverse]（[iprod_hom_iso_to]、[iprod_hom_iso_from] 和 [icoprod_hom_iso_to]）；
 - 后向分支的值是由预先存在的 [∃!] 访问器命名的中介器——[iprod_hom_iso_from_is_desc] 和 [icoprod_hom_iso_from_is_desc] 是其最强形式下的“不会漂移”保证；
 - 前向分支计算沿投影（[iprod_hom_transform_computes]）的限制，在余积（coproduct）侧计算为 [u ∘ inj a]（[icoprod_hom_transform_computes]）；
 - 右侧就是树自身的索引积，在 [Sets] 中读取（[iprod_hom_functor_is_indexed_product] 及其对偶）；
 - 在 [Sets] 处，后向分支计算为 Instance/Sets/Products.v 的成组及 case 映射（[Sets_iprod_hom_from_computes]、[Sets_icoprod_hom_from_computes]），并且类导出的同构与已读出的项相同。直接 d [Sets_IsIndexedProduct]
 （[Sets_iprod_hom_iso_is_class] 及其对偶）。进行了两次严格尝试并被否定，都被标记为 [Fail] 探针，在 Test/ProbeIndexedHom.v 中有阳性对照：循环操作无法计算，无论是在抽象积上还是在具体的 [Sets] 上。从它所限制的族中恢复 [u] 恰好是 [iprod_desc] 的唯一性条款，这是一个 [≈] 级别的事实。在 [Sets] 中，诊断更明确，并且由一个对照本身固定：[SetoidMorphism] 拥有带 eta 的原始投影，[morphism] 字段完全一致，区别在于 [proper_morphism] 证书，元组重建为其自身义务。

 宇宙，按约束块衡量

 使用 [Set Printing Universes.] 和 [About] 重现。仅读取绑定器会出错；约束块是权威。[iprod_hom_functor@{u u0 u1 u2 u3 u4}] 使用 [C : Category@{u3 u4 u4}] 和 [A : Type@{u}] 以及 [u <= u2] 和 [u4 <= u2] —— 索引宇宙和 [C] 的 Hom 宇宙各自由目标 [Sets] 的载体宇宙 [u2] 限定，并且彼此无关。因此，仅目标函子就允许一个严格大于 [C] 的 hom 的索引。比较映射不存在，其原因值得了解。它的来源是同态函子，其对象是 [C] 的同态集合；一个 [SetoidObject] 拥有其 [Setoid] 作为字段，并且在这里没有记录是累积的（测度：将一个 [Setoid@{a a}] 提升为 [Setoid@{b b}] 并附带 [a < b] 是被拒绝的，[SetoidObject] 同理），因此比较存在的 [Sets] 的承载宇宙被强制等于 [C] 的同态宇宙，而不仅仅是高于它——曾尝试过一个标注变体来声明两者不同，但报告“无法强制 uh = us 因为 uh < us”。索引界限如下。这被固定在 Test/ProbeIndexedHom.v 中，作为可形成性否定，其确切消息为“Cannot enforce ua <= uh because uh < ua”，针对两个控件显示单独的函子都不是被拒绝的原因。实际上，这个约束不会增加累积性已经提供的开销：在或低于 [C] 的同伦宇宙中的索引会提升，这与 Instance/Sets/Products.v 的标题分析在 [Sets] 时的相同小性边界条件相同。这两座 LIMIT 形桥承载 [{A : Set}]。对该粘合剂分析的记录更正：之前的修订说它“是两个事实的组合而不是一个，探测文件将其分开。[Structure/Limit/Product.v] 的 [iprod] 位于 [C : Category@{u Set Set}] 之上——[DiscreteCat] 的同类集是严格相等的——并具有其自身的索引宇宙 FREE；探针的控制显示 [Limit (DiscreteCat_Functor f)] 和 [iprod f L] 都可以在索引严格高于 [Set] 的 [C] 上形成。将此文件的边界添加到 [C] 的同态宇宙，该宇宙在 [Set] 中，是切割索引到 [Set] 的原因。该组合的捐赠半部分已经消失：[iprod] 从 Instance/Discrete.v 中未标注的 [DiscreteCat_Functor] 继承了其 [Set]，在 PR "代数载体是集合"（2026-09-17）中进行了现场标注，[iprod@{u u0 u1 u2 u3}] 现在位于 [C : Category@{u1 u2 u2}] 之上。Test/ProbeIndexedHom.v 在整个文件的副本中重新测量了两个负值，其部分的 [C] 被声明在严格高于 [Set] 的同态宇宙中：两个仍然拒绝，因此 [{A : Set}] 绑定器仅是本文件的边界，而不是组合。该部分的 [C] 保留在 [Set] 实例上，因为绑定器与该实例有关；请参见该探针的标题。[indexed_product_hom_iso] 和 [indexed_coproduct_hom_iso] 类形桥没有这样的销钉，也没有提到任何离散图。

 在两个方向上都非空

 该条件在树的唯一成员处实例化：[Sets_iprod_hom_iso] 和 [Sets_icoprod_hom_iso]，它们在 Instance/Sets/Products.v 上，其中两个后向腿都在计算。并且可逆性假设被证明不是空洞的，仅凭实例化无法显示这一点：[Sets_bad_not_iprod] 和 [Sets_bad_not_icoprod] 在 [Sets] 中展示了一个候选锥 —— 这是一个两元素集类，其单投影具有恒为真的映射 —— 其比较映射不可逆，并通过双条件的正向部分得出它不是索引的（共）积。因此 [iprod_of_hom_iso] 的假设是真正具有选择性的。

 未交付的内容是什么没有 (I × J)-矩阵形式（Riehl 条款 (iii)，问题 #336）。在 [(DiscreteCat A)^op] 和 [DiscreteCat A] 之间没有翻译：问题被回避而不是解决，就像在此文件之前一样。在 FAMILY [f] 或索引 [A] 中没有自然性，只有在变化的对象中才有。在任一函子中都没有 [Representable] 实例，也没有通用元素包装。关于没有相关 (co)积的范畴没有任何声明：比较映射存在于那里，但此文件没有展示这样的范畴。状态：无公理。所有 59 个常量——47 个已命名加上 12 个 [Program] 义务，按照 docs/AXIOMS.md 方法论由 [Print Module] 列出——报告“在全局上下文下封闭”；Makefile 的 [print-assumptions] 目标审核主要的那些。这里没有使用到 funext、choice 或 UIP。一个小型余积的具体 [Sets] 见证位于 Issue #254 的 Instance/Sets/Products.v 中，并未重复；Issue #729 使用 Structure/Limit/Coproduct.v 并不受该文件影响。
*)

#[local] Obligation Tactic := idtac.

(* * ** The indexed hom presheaf [c ↦ ∏ₐ C(c, f a)] / * ** 索引的同 Presheaf [c ↦ ∏ₐ C(c, f a)] *)

Definition iprod_hom_fam {C : Category} {A : Type} (f : A → C) (c : C) :
  A → obj[Sets] :=
  fun a => {| carrier := @hom C c (f a); is_setoid := @homset C c (f a) |}.

Program Definition iprod_hom_functor {C : Category} {A : Type} (f : A → C) :
  C^op ⟶ Sets := {|
  fobj := fun c => Sets_iprod_obj (iprod_hom_fam f c);
  fmap := fun c c' (h : c ~{C^op}~> c') =>
            {| morphism := fun fam => fun a : A => fam a ∘[C] h |}
|}.
Next Obligation.
  intros C A f c c' h fam fam' Hfam a; simpl in *; now rewrite (Hfam a).
Qed.
Next Obligation.
  intros C A f c c' h h' Hh fam a; simpl in *; now rewrite Hh.
Qed.
Next Obligation.
  intros C A f c fam a; simpl; apply id_right.
Qed.
Next Obligation.
  intros C A f x y z h k fam a; simpl; apply comp_assoc.
Qed.

(* * ** The comparison map: restriction along the projections / * ** 比较图：沿投影的限制 *)

Program Definition iprod_hom_transform {C : Category} {A : Type} (f : A → C)
  (q : C) (proj : ∀ a : A, q ~> f a) :
  @Transform (C^op) Sets (@Curried_CoHom C q) (iprod_hom_functor f) := {|
  transform := fun c => {| morphism := fun u => fun a : A => proj a ∘ u |}
|}.
Next Obligation.
  intros C A f q proj c u v Huv a; simpl in *; now rewrite Huv.
Qed.
Next Obligation.
  intros C A f q proj x y h u a; simpl; apply comp_assoc_sym.
Qed.
Next Obligation.
  intros C A f q proj x y h u a; simpl; apply comp_assoc.
Qed.

(* * ** The inverse, supplied by the universal property / * ** 逆，由泛性质提供 *)

Program Definition iprod_hom_inverse {C : Category} {A : Type} {f : A → C}
  {q : C} {proj : ∀ a : A, q ~> f a} (H : IsIndexedProduct f q proj) :
  @Transform (C^op) Sets (iprod_hom_functor f) (@Curried_CoHom C q) := {|
  transform := fun c => {| morphism := fun fam => unique_obj (iprod_desc H fam) |}
|}.
Next Obligation.
  intros C A f q proj H c fam fam' Hfam; simpl in *.
  symmetry.
  apply (uniqueness (iprod_desc H fam')).
  intros a.
  rewrite (unique_property (iprod_desc H fam) a).
  now rewrite (Hfam a).
Qed.
Next Obligation.
  intros C A f q proj H x y h fam; simpl in *.
  symmetry.
  apply (uniqueness (iprod_desc H (fun a => fam a ∘ h))).
  intros a.
  rewrite comp_assoc.
  now rewrite (unique_property (iprod_desc H fam) a).
Qed.
Next Obligation.
  intros C A f q proj H x y h fam; simpl in *.
  apply (uniqueness (iprod_desc H (fun a => fam a ∘ h))).
  intros a.
  rewrite comp_assoc.
  now rewrite (unique_property (iprod_desc H fam) a).
Qed.

Program Definition iprod_hom_iso {C : Category} {A : Type} {f : A → C}
  {q : C} {proj : ∀ a : A, q ~> f a} (H : IsIndexedProduct f q proj) :
  @Isomorphism ([C^op, Sets]) (@Curried_CoHom C q) (iprod_hom_functor f) := {|
  to   := iprod_hom_transform f q proj;
  from := iprod_hom_inverse H
|}.
Next Obligation.
  intros C A f q proj H c fam a; simpl.
  rewrite id_right.
  apply (unique_property (iprod_desc H fam) a).
Qed.
Next Obligation.
  intros C A f q proj H c u; simpl.
  rewrite id_right.
  apply (uniqueness (iprod_desc H (fun a => proj a ∘ u))).
  intros a; reflexivity.
Qed.

(* * ** The converse: an invertible comparison map is a universal property / * ** 反之：可逆比较映射是一个普遍性质 *)

Definition iprod_of_hom_iso {C : Category} {A : Type} {f : A → C}
  {q : C} {proj : ∀ a : A, q ~> f a}
  (I : @IsIsomorphism ([C^op, Sets]) (@Curried_CoHom C q)
                      (iprod_hom_functor f) (iprod_hom_transform f q proj)) :
  IsIndexedProduct f q proj.
Proof.
  apply (@Build_IsIndexedProduct C A f q proj).
  intros c pi.
  unshelve eapply Build_Unique.
  - exact (transform (@two_sided_inverse _ _ _ _ I) c pi).
  - intros a.
    pose proof (@is_right_inverse _ _ _ _ I c pi a) as Hr; simpl in Hr.
    now rewrite id_right in Hr.
  - intros v Hv.
    pose proof (@is_left_inverse _ _ _ _ I c v) as Hl; simpl in Hl.
    rewrite id_right in Hl.
    transitivity (transform (@two_sided_inverse _ _ _ _ I) c
                    (fun a => proj a ∘ v)).
    + apply (proper_morphism (transform (@two_sided_inverse _ _ _ _ I) c)).
      intros a; symmetry; exact (Hv a).
    + exact Hl.
Defined.

Definition iprod_hom_IsIsomorphism {C : Category} {A : Type} {f : A → C}
  {q : C} {proj : ∀ a : A, q ~> f a} (H : IsIndexedProduct f q proj) :
  @IsIsomorphism ([C^op, Sets]) (@Curried_CoHom C q) (iprod_hom_functor f)
                 (iprod_hom_transform f q proj).
Proof.
  exact (@Build_IsIsomorphism ([C^op, Sets])
           (@Curried_CoHom C q) (iprod_hom_functor f)
           (iprod_hom_transform f q proj) (iprod_hom_inverse H)
           (iso_to_from (iprod_hom_iso H)) (iso_from_to (iprod_hom_iso H))).
Defined.

Definition iprod_iff_hom_iso {C : Category} {A : Type} (f : A → C)
  (q : C) (proj : ∀ a : A, q ~> f a) :
  IsIndexedProduct f q proj ↔
  @IsIsomorphism ([C^op, Sets]) (@Curried_CoHom C q) (iprod_hom_functor f)
                 (iprod_hom_transform f q proj) :=
  (fun H => iprod_hom_IsIsomorphism H, fun I => iprod_of_hom_iso I).

(** ** Strict readings / ** 严格解读 *)

Example iprod_hom_transform_computes {C : Category} {A : Type} (f : A → C)
  (q : C) (proj : ∀ a : A, q ~> f a) (c : C) (u : c ~> q) :
  transform (iprod_hom_transform f q proj) c u = fun a : A => proj a ∘ u
  := eq_refl.

Example iprod_hom_iso_to {C : Category} {A : Type} {f : A → C}
  {q : C} {proj : ∀ a : A, q ~> f a} (H : IsIndexedProduct f q proj) :
  to (iprod_hom_iso H) = iprod_hom_transform f q proj := eq_refl.

Example iprod_hom_iso_from {C : Category} {A : Type} {f : A → C}
  {q : C} {proj : ∀ a : A, q ~> f a} (H : IsIndexedProduct f q proj) :
  from (iprod_hom_iso H) = iprod_hom_inverse H := eq_refl.

Example iprod_hom_iso_from_is_desc {C : Category} {A : Type} {f : A → C}
  {q : C} {proj : ∀ a : A, q ~> f a} (H : IsIndexedProduct f q proj)
  (c : C) (fam : ∀ a : A, c ~> f a) :
  transform (from (iprod_hom_iso H)) c fam = unique_obj (iprod_desc H fam)
  := eq_refl.

(* The biconditional's pairing is transparent, so projecting it returns the named leg by conversion rather than merely proving the same thing. / 双条件的配对是透明的，因此投影它会通过转换返回命名的分支，而不仅仅是证明相同的事情。 *)

Example iprod_iff_hom_iso_fst {C : Category} {A : Type} (f : A → C)
  (q : C) (proj : ∀ a : A, q ~> f a) :
  fst (iprod_iff_hom_iso f q proj)
  = fun H => @iprod_hom_IsIsomorphism C A f q proj H := eq_refl.

Example iprod_iff_hom_iso_snd {C : Category} {A : Type} (f : A → C)
  (q : C) (proj : ∀ a : A, q ~> f a) :
  snd (iprod_iff_hom_iso f q proj)
  = fun I => @iprod_of_hom_iso C A f q proj I := eq_refl.

(* * ** The coproduct side, by definition at [C^op] / * ** 共积的部分，根据定义在 [C^op] *)

(*
 Every constant in this section is its product counterpart applied at
 [C^op], supplied by [:=] with no tactic; [icoprod_hom_functor_is_op]
 records that reading by [eq_refl]. 

 --------
 本节中的每个常数都是其产品对应项在 [C^op] 上的应用，由 [:=] 提供，没有策略；[icoprod_hom_functor_is_op] 由 [eq_refl] 记录该读数。
*)

Definition icoprod_hom_fam {C : Category} {A : Type} (f : A → C) (c : C) :
  A → obj[Sets] :=
  @iprod_hom_fam (C^op) A f c.

Definition icoprod_hom_functor {C : Category} {A : Type} (f : A → C) :
  C ⟶ Sets :=
  @iprod_hom_functor (C^op) A f.

Definition icoprod_hom_transform {C : Category} {A : Type} (f : A → C)
  (p : C) (inj : ∀ a : A, f a ~> p) :
  @Transform C Sets (@Curried_Hom C p) (icoprod_hom_functor f) :=
  @iprod_hom_transform (C^op) A f p inj.

Definition icoprod_hom_inverse {C : Category} {A : Type} {f : A → C}
  {p : C} {inj : ∀ a : A, f a ~> p} (H : IsIndexedCoproduct f p inj) :
  @Transform C Sets (icoprod_hom_functor f) (@Curried_Hom C p) :=
  @iprod_hom_inverse (C^op) A f p inj H.

Definition icoprod_hom_iso {C : Category} {A : Type} {f : A → C}
  {p : C} {inj : ∀ a : A, f a ~> p} (H : IsIndexedCoproduct f p inj) :
  @Isomorphism ([C, Sets]) (@Curried_Hom C p) (icoprod_hom_functor f) :=
  @iprod_hom_iso (C^op) A f p inj H.

Definition icoprod_hom_IsIsomorphism {C : Category} {A : Type} {f : A → C}
  {p : C} {inj : ∀ a : A, f a ~> p} (H : IsIndexedCoproduct f p inj) :
  @IsIsomorphism ([C, Sets]) (@Curried_Hom C p) (icoprod_hom_functor f)
                 (icoprod_hom_transform f p inj) :=
  @iprod_hom_IsIsomorphism (C^op) A f p inj H.

Definition icoprod_of_hom_iso {C : Category} {A : Type} {f : A → C}
  {p : C} {inj : ∀ a : A, f a ~> p}
  (I : @IsIsomorphism ([C, Sets]) (@Curried_Hom C p) (icoprod_hom_functor f)
                      (icoprod_hom_transform f p inj)) :
  IsIndexedCoproduct f p inj :=
  @iprod_of_hom_iso (C^op) A f p inj I.

Definition icoprod_iff_hom_iso {C : Category} {A : Type} (f : A → C)
  (p : C) (inj : ∀ a : A, f a ~> p) :
  IsIndexedCoproduct f p inj ↔
  @IsIsomorphism ([C, Sets]) (@Curried_Hom C p) (icoprod_hom_functor f)
                 (icoprod_hom_transform f p inj) :=
  @iprod_iff_hom_iso (C^op) A f p inj.

Example icoprod_hom_transform_computes {C : Category} {A : Type} (f : A → C)
  (p : C) (inj : ∀ a : A, f a ~> p) (c : C) (u : p ~> c) :
  transform (icoprod_hom_transform f p inj) c u = fun a : A => u ∘ inj a
  := eq_refl.

Example icoprod_iff_hom_iso_fst {C : Category} {A : Type} (f : A → C)
  (p : C) (inj : ∀ a : A, f a ~> p) :
  fst (icoprod_iff_hom_iso f p inj)
  = fun H => @icoprod_hom_IsIsomorphism C A f p inj H := eq_refl.

Example icoprod_iff_hom_iso_snd {C : Category} {A : Type} (f : A → C)
  (p : C) (inj : ∀ a : A, f a ~> p) :
  snd (icoprod_iff_hom_iso f p inj)
  = fun I => @icoprod_of_hom_iso C A f p inj I := eq_refl.

Example icoprod_hom_iso_to {C : Category} {A : Type} {f : A → C}
  {p : C} {inj : ∀ a : A, f a ~> p} (H : IsIndexedCoproduct f p inj) :
  to (icoprod_hom_iso H) = icoprod_hom_transform f p inj := eq_refl.

Example icoprod_hom_iso_from_is_desc {C : Category} {A : Type} {f : A → C}
  {p : C} {inj : ∀ a : A, f a ~> p} (H : IsIndexedCoproduct f p inj)
  (c : C) (fam : ∀ a : A, f a ~> c) :
  transform (from (icoprod_hom_iso H)) c fam = unique_obj (icoprod_desc H fam)
  := eq_refl.

(* * ** The three presentations of an indexed (co)product all compose / * ** 一个索引的（协）积的三种表示都可以组合 *)

Definition limit_hom_iso {C : Category} {A : Set} (f : A → C)
  (L : Limit (DiscreteCat_Functor f)) :
  @Isomorphism ([C^op, Sets]) (@Curried_CoHom C (iprod f L))
               (iprod_hom_functor f) :=
  iprod_hom_iso (limit_is_indexed_product f L).

Definition colimit_hom_iso {C : Category} {A : Set} (f : A → C)
  (L : Limit (@DiscreteCat_Functor A (C^op) f)) :
  @Isomorphism ([C, Sets]) (@Curried_Hom C (icoprod f L))
               (icoprod_hom_functor f) :=
  icoprod_hom_iso (colimit_is_indexed_coproduct f L).

Definition indexed_product_hom_iso {C : Category}
  {HP : @HasIndexedProducts C} {A : Type} (f : A → C) :
  @Isomorphism ([C^op, Sets]) (@Curried_CoHom C (indexed_product f))
               (iprod_hom_functor f) :=
  iprod_hom_iso (indexed_product_ump f).

Definition indexed_coproduct_hom_iso {C : Category}
  {HC : @HasIndexedCoproducts C} {A : Type} (f : A → C) :
  @Isomorphism ([C, Sets]) (@Curried_Hom C (indexed_coproduct f))
               (icoprod_hom_functor f) :=
  icoprod_hom_iso (indexed_coproduct_ump f).

(* * ** The right-hand side is the tree's own indexed product, at [Sets] / * ** 右侧是树自身的索引产品，在 [Sets] *)

Example iprod_hom_functor_is_indexed_product {C : Category} {A : Type}
  (f : A → C) (c : C) :
  fobj[iprod_hom_functor f] c = indexed_product (iprod_hom_fam f c) := eq_refl.

Example icoprod_hom_functor_is_indexed_product {C : Category} {A : Type}
  (f : A → C) (c : C) :
  fobj[icoprod_hom_functor f] c = indexed_product (icoprod_hom_fam f c)
  := eq_refl.

Example icoprod_hom_functor_is_op {C : Category} {A : Type} (f : A → C) :
  icoprod_hom_functor f = @iprod_hom_functor (C^op) A f := eq_refl.

(* * ** Non-vacuity: the in-tree indexed (co)products of [Sets] / * ** 非空性： [Sets] 的树内索引（协）积 *)

Definition Sets_iprod_hom_iso {A : Type} (F : A → obj[Sets]) :
  @Isomorphism ([Sets^op, Sets]) (@Curried_CoHom Sets (Sets_iprod_obj F))
               (iprod_hom_functor F) :=
  iprod_hom_iso (Sets_IsIndexedProduct F).

Definition Sets_icoprod_hom_iso {A : Type} (F : A → obj[Sets]) :
  @Isomorphism ([Sets, Sets]) (@Curried_Hom Sets (Sets_icoprod_obj F))
               (icoprod_hom_functor F) :=
  icoprod_hom_iso (Sets_IsIndexedCoproduct F).

Example Sets_iprod_hom_from_computes {A : Type} (F : A → obj[Sets])
  (c : obj[Sets]) (fam : ∀ a : A, c ~{Sets}~> F a) :
  transform (from (Sets_iprod_hom_iso F)) c fam = Sets_iprod_tuple F c fam
  := eq_refl.

Example Sets_icoprod_hom_from_computes {A : Type} (F : A → obj[Sets])
  (c : obj[Sets]) (fam : ∀ a : A, F a ~{Sets}~> c) :
  transform (from (Sets_icoprod_hom_iso F)) c fam = Sets_icoprod_case F c fam
  := eq_refl.

(* * ** The invertibility hypothesis is not vacuous / * ** 可逆性假设并非空洞 *)

Definition Sets_const_true : Sets_bool ~{Sets}~> Sets_bool.
Proof.
  unshelve refine {| morphism := fun _ => true |}.
  all: intros x y Hxy; reflexivity.
Defined.

Definition Sets_bad_proj (a : poly_unit) :
  Sets_bool ~{Sets}~> (fun _ : poly_unit => Sets_bool) a := Sets_const_true.

Lemma Sets_bad_transform_not_iso :
  @IsIsomorphism ([Sets^op, Sets])
    (@Curried_CoHom Sets Sets_bool)
    (iprod_hom_functor (fun _ : poly_unit => Sets_bool))
    (iprod_hom_transform (fun _ : poly_unit => Sets_bool)
                         Sets_bool Sets_bad_proj) → False.
Proof.
  intros I.
  pose proof (@is_left_inverse _ _ _ _ I Sets_bool
                (@id Sets Sets_bool)) as H0.
  pose proof (@is_left_inverse _ _ _ _ I Sets_bool Sets_const_true) as H1.
  simpl in H0, H1.
  assert (Heq : transform (@two_sided_inverse _ _ _ _ I) Sets_bool
                  (fun _ : poly_unit => Sets_const_true ∘ @id Sets Sets_bool)
                ≈ transform (@two_sided_inverse _ _ _ _ I) Sets_bool
                  (fun _ : poly_unit => Sets_const_true ∘ Sets_const_true)).
  { apply (proper_morphism
             (transform (@two_sided_inverse _ _ _ _ I) Sets_bool)).
    intros a x; reflexivity. }
  specialize (Heq false).
  rewrite H0, H1 in Heq.
  simpl in Heq.
  discriminate Heq.
Qed.

Definition Sets_bad_not_iprod :
  IsIndexedProduct (fun _ : poly_unit => Sets_bool) Sets_bool Sets_bad_proj
  → False :=
  fun H => Sets_bad_transform_not_iso (fst (iprod_iff_hom_iso _ _ _) H).

Definition Sets_bad_inj (a : poly_unit) :
  (fun _ : poly_unit => Sets_bool) a ~{Sets}~> Sets_bool := Sets_const_true.

Lemma Sets_bad_transform_not_iso_co :
  @IsIsomorphism ([Sets, Sets])
    (@Curried_Hom Sets Sets_bool)
    (icoprod_hom_functor (fun _ : poly_unit => Sets_bool))
    (icoprod_hom_transform (fun _ : poly_unit => Sets_bool)
                           Sets_bool Sets_bad_inj) → False.
Proof.
  intros I.
  pose proof (@is_left_inverse _ _ _ _ I Sets_bool
                (@id Sets Sets_bool)) as H0.
  pose proof (@is_left_inverse _ _ _ _ I Sets_bool Sets_const_true) as H1.
  simpl in H0, H1.
  assert (Heq : transform (@two_sided_inverse _ _ _ _ I) Sets_bool
                  (fun _ : poly_unit => @id Sets Sets_bool ∘ Sets_const_true)
                ≈ transform (@two_sided_inverse _ _ _ _ I) Sets_bool
                  (fun _ : poly_unit => Sets_const_true ∘ Sets_const_true)).
  { apply (proper_morphism
             (transform (@two_sided_inverse _ _ _ _ I) Sets_bool)).
    intros a x; reflexivity. }
  specialize (Heq false).
  rewrite H0, H1 in Heq.
  simpl in Heq.
  discriminate Heq.
Qed.

Definition Sets_bad_not_icoprod :
  IsIndexedCoproduct (fun _ : poly_unit => Sets_bool) Sets_bool Sets_bad_inj
  → False :=
  fun H => Sets_bad_transform_not_iso_co (fst (icoprod_iff_hom_iso _ _ _) H).

(*
 The class-derived comparison and the one read straight off
 [Sets_IsIndexedProduct] are the SAME TERM, not merely isomorphic: the
 class projection reduces by iota to the field it was built from. 

 --------
 从类派生的比较和直接从 [Sets_IsIndexedProduct] 读取的比较是相同的项，而不仅仅是同构：类投影通过 iota 简化到它所构建的字段。
*)

Example Sets_iprod_hom_iso_is_class {A : Type} (F : A → obj[Sets]) :
  @indexed_product_hom_iso Sets Sets_HasIndexedProducts A F
  = Sets_iprod_hom_iso F := eq_refl.

Example Sets_icoprod_hom_iso_is_class {A : Type} (F : A → obj[Sets]) :
  @indexed_coproduct_hom_iso Sets Sets_HasIndexedCoproducts A F
  = Sets_icoprod_hom_iso F := eq_refl.
