(* * * Limits over a coproduct of shapes, and connected components / * * 关于形状的余积上的极限，以及连通分支 *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Equivalence.Bundled.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Construction.Coproduct.Indexed.
Require Import Category.Structure.Groupoid.Connected.
Require Import Category.Theory.Connected.Components.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.
Require Import Category.Instance.Coq.
Require Import Category.Structure.Limit.Initial.
(*
 PORTABILITY: the [Coq.Logic.] spelling, not [From Stdlib], for the
 reason Construction/Coproduct/Indexed.v records -- the [Stdlib]
 prefix does not exist on the 8.x line the tree still builds on. 

 --------
 可移植性：使用 [Coq.Logic.] 拼写，而不是 [From Stdlib]，原因是 Construction/Coproduct/Indexed.v 记录——[Stdlib] 前缀在 8.x 系列上不存在，但树仍然可以构建。
*)
Require Import Coq.Logic.Eqdep_dec.

Generalizable All Variables.

(*
 Book:      Mac Lane, “Categories for the Working Mathematician”,
 2nd ed., §IV.2 Exercise 7, printed p. 90 (maclane:IV.2:ex7)
 Book:      Riehl, “Category Theory in Context”, §3.6
 (riehl:3.6:construction-cat-coproducts)
 nLab:      https://ncatlab.org/nlab/show/connected+category
 nLab:      https://ncatlab.org/nlab/show/limit

 Mac Lane's exercise has three clauses and they are delivered as three
 theorems, with a fourth result -- the reindexing lemma clause (c)
 needs -- factored out because nothing in it is about components.

 (a) [coprod_IsALimit]: for [F : ∐_k J_k ⟶ C], a limit of each
 restriction [F ◯ inj k] plus an indexed product of those limit
 apexes gives a limit of [F], at that product.

 (b) [ComponentDecomposition] with [cd_compare], [cd_compare_Full],
 [cd_compare_ESO], [cd_compare_Faithful] and [cd_equivalence]:
 a category EQUIPPED WITH A DECOMPOSITION AS DATA, whose index
 satisfies [IdxUIP], is the coproduct of its connected
 components.  Mac Lane's own sentence quantifies over EVERY
 category; this one does not, and §3 and §4 below say why and
 at what cost.

 (c) [components_IsALimit]: a limit over any shape carrying a
 decomposition is a product of limits over connected shapes.

 [xfer_IsALimit]: a FULL, ESSENTIALLY SURJECTIVE functor of
 shapes transfers limits.  Faithfulness is not consumed.

 1. A PRIOR-ART CORRECTION.  The catalog issue states that “no
 connectedness predicate exists anywhere in the tree” and asks for
 the zig-zag relation and its reflexivity, symmetry and
 transitivity to be built.  That is FALSE, and was false before
 Theory/Connected/Components.v landed: Structure/Groupoid/
 Connected.v declares [Inductive ZigZag {C : Category}] and
 [Definition Connected (C : Category)] for an ARBITRARY category,
 together with [zigzag_trans], [zigzag_sym] and [hom_zigzag].
 Theory/Connected/Components.v REUSES them -- it Requires that
 module and declares neither -- and so does this
 file.  Nothing here redeclares a zig-zag.

 2. THE CENTRAL ABSENCE IS REAL, AND MEASURED BY CONSUMER RATHER THAN
 BY NAME.  Before this file [SigmaCat] had exactly three mentions
 in the tree -- its own module Construction/Coproduct/Indexed.v,
 Instance/Cat/Coproduct.v, and Test/ProbeCatCoproduct338.v -- and
 none of the three states any result about limits over a coproduct
 of shapes.  An earlier revision of this paragraph said “none of the
 three mentions a limit or a cone”, and the LIMIT half of that is
 FALSE: all three mention [Limit], 2, 11 and 2 times, in [Require]
 lines and in NOT-delivered prose (Instance/Cat/Coproduct.v is
 a numbered section headed “THE [Colimit] READING IS NOT
 DELIVERED”).  The CONE half stands -- zero hits in all three -- and
 the conclusion is unaffected, but the evidence as first stated was
 wrong.  The near-hit a
 name search does return, Structure/Limit/Coproduct.v's
 [colimit_is_indexed_coproduct], is a different statement: it
 reads a COLIMIT OVER A DISCRETE DIAGRAM as an indexed coproduct
 OF OBJECTS, and no coproduct of index CATEGORIES occurs in it.
 Per the issue's own QA correction the indexed coproduct is
 CONSUMED here and not rebuilt: [SigmaCat], [SigmaCat_inj],
 [SigmaCat_case], [ob_cast], [mor_cast], [IdxUIP] and
 [IdxUIP_pair] all come from the donor.

 3. THE OBSTRUCTION IN PART (b) IS REAL, AND IT IS PROVED HERE RATHER
 THAN ASSERTED.  Theory/Connected/Components.v's π₀ is a COARSER
 SETOID ON THE SAME CARRIER -- that file's own [pi0_carrier]
 records [carrier (pi0 C) = obj[C]] by [eq_refl] -- so it supplies
 no quotient TYPE to index a coproduct by.  Indexing [SigmaCat] by
 it yields ONE SUMMAND PER OBJECT, and at the walking arrow that
 is two summands where there is one component:
 [naive_pi0_sum_not_connected] proves the resulting category is
 not connected while [Two_Connected] proves [_2] is, and
 [no_ESO_into_naive_pi0_sum] turns that into the statement a
 consumer would want, that no essentially surjective functor
 [_2 ⟶ naive_pi0_sum] exists.  Read that at its strength: it
 refutes THAT index, and it is NOT a proof that the two categories
 are inequivalent, which would need connectedness carried backwards
 along a quasi-inverse -- not done here.

 The decomposition is therefore packaged as DATA, on the model of
 Theory/Skeleton.v's [Skeleton] record, which carries a chosen
 representative [skel_rep] together with a uniqueness field
 [skel_uniq].  [ComponentDecomposition] carries [cd_rep] (a chosen
 representative per index), [cd_part] (the index of an object),
 [cd_join] (a chain from the representative) and [cd_sep] (the
 uniqueness clause).  NO CHOICE PRINCIPLE IS CONSUMED and no
 unconditional decomposition is claimed: a category is not shown
 to HAVE a decomposition, and the two concrete ones below are
 built by hand.  Riehl's uniqueness clause is [cd_transfer] with
 [cd_transfer_round] -- the index type is determined up to a
 canonical bijection -- sharpened by [cd_transfer_part], which
 says the bijection is compatible with the two part-assignments,
 so two decompositions cut the category into the same pieces
 rather than merely having equinumerous index sets.

 4. WHERE THE ONE HYPOTHESIS IS SPENT, AND -- MORE INTERESTINGLY --
 WHERE IT IS NOT.  [cd_compare_ESO] and [cd_compare_Full] take NO
 hypothesis; [cd_compare_Faithful] takes the donor's own
 [IdxUIP (cd_index D)], spent in exactly one place, and
 [cd_equivalence] inherits it.  The hypothesis is NOT shown
 necessary: no countermodel is built and no forcing theorem in the
 style of Construction/Coproduct/Indexed.v's
 [sigma_inj_Full_forces_UIP] is proved.  It is discharged for any
 index with decidable equality by Hedberg ([UIP_dec]), which is
 what [poly_unit_IdxUIP] and [bool_IdxUIP] do for the two
 witnesses.

 PART (c) COSTS NO [IdxUIP] AT ALL, and that is the reason
 [xfer_IsALimit] is stated for a full, essentially surjective
 functor rather than for an equivalence: fullness supplies the
 preimage arrows, essential surjectivity the objects, and
 faithfulness is never used.  So the limit decomposition holds
 wherever the equivalence of categories does and also where it is
 not available.

 5. STRENGTHS, MEASURED STRICT-FIRST.  Holding at [eq_refl]:
 [summand_obj], [summand_map], [coprod_leg_at],
 [coprod_IsALimit_leg], [coprod_IsALimit_med],
 [coprod_IsALimit_iprod_leg], [restrict_cone_apex],
 [cd_compare_obj], [cd_compare_map], [cd_eso_obj_image],
 [Two_Decomposition_index], [component_diagram_obj],
 [component_diagram_map], [sigma_hom_eta], and the three [Coq]
 computations [CoqPair_leg_true], [CoqPair_leg_false] and
 [CoqPair_med_computes].  Settling for [≈]: the two
 projection-versus-restriction statements
 ([coprod_proj_is_restriction], [coprod_proj_via_iso]), which are
 equations between MEDIATORS and so cannot be definitional -- each
 is proved through the summand limit's own uniqueness clause --
 and [component_diagram_equiv], whose two DATA agreements are
 [eq_refl] and whose refutation at whole-record level is pinned as
 [component_diagram_strict].

 6. UNIVERSES, READ OFF BOTH THE BINDER AND THE CONSTRAINT BLOCK.
 [coprod_IsALimit@{...}] is over [J : I → Category@{u0 u1 u1}] and
 [C : Category@{u2 u3 u3}] with the single equation [u1 = u3] in
 its block: the SHAPES' hom-and-proof universe is identified with
 the AMBIENT's.  That is the donor [IsALimit]'s own shape and
 nothing here adds to it; BOTH object universes stay free, bounded
 and never identified, and NO [Set] appears.  [components_IsALimit]
 reads the same way ([J : Category@{u u0 u0}],
 [C : Category@{u1 u2 u2}], block equation [u0 = u2]), and
 [xfer_IsALimit] identifies THREE hom universes rather than two
 ([u0 = u2] and [u0 = u4]), the two shapes' and the ambient's,
 which is what stating [IsALimit] on both sides of a reindexing
 costs.

 TWO CONSTANTS PUT THE IDENTIFICATION ENTIRELY IN THE BINDER, WITH
 AN EMPTY OR EQUATION-FREE BLOCK, so a reader who checks only the
 block reports “no identification” and is wrong.
 [coprod_IsALimit_HasIndexedProducts] has NO equation in its block
 while its binder writes [Category@{u1 u7 u7}] and
 [Category@{u6 u7 u7}], reusing one level for four slots; and
 [ComponentDecomposition@{u u0 u1}] has a LITERALLY EMPTY block
 while its binder reads [Category@{u0 u1 u1} → Type@{...}].  The
 latter is [ZigZag]'s own shape, inherited; its INDEX universe [u]
 is free of the category's, which is what lets the index be as
 large as the object type.

 [coprod_IsALimit_iprod] IS THE PLACE TO READ THE FORMER [Set] PIN,
 AND THE PIN IS GONE.  An earlier revision of this paragraph said
 the pin “arrives” here and is “WIDER than the donor's binder alone
 suggests”, quoting [iprod] as declared over
 [C : Category@{_ Set Set}] and the corollary as reading
 [J : I → Category@{u0 Set Set}] and [C : Category@{u3 Set Set}];
 it added that the pin “is inherited, is not repaired, and is NOT
 claimed unavoidable”.  The first half was a correct reading of the
 tree of the time and the last clause was right: the pin was a
 universe-minimization artifact of Instance/Discrete.v's
 [DiscreteCat_Functor], reaching [iprod] through [Limit]'s
 identification of the shape's hom-and-proof universe with the
 ambient's.  That donor was annotated in place in the PR “algebraic
 carriers are sets” (2026-09-17), so no literal [Set] reaches this
 corollary any more.  The elementary [IsIndexedProduct] form is
 still stated first and the [iprod] reading is still a corollary --
 that ordering was never only about [Set] -- and Section
 [UniversePin] below now GUARDS the repair: the same two lines that
 used to refuse over homs strictly above [Set] are kept there as
 positive controls.

 7. NEGATIVES: TWO, BOTH CONVERSION.  An earlier revision of this item
 read “FOUR, OF TWO KINDS, KEPT LEXICALLY APART” and described two
 FORMABILITY negatives -- [iprod] and [coprod_IsALimit_iprod]
 rejected over a category whose homs are declared strictly above
 [Set], “each ending ”universe inconsistency: Cannot enforce
 Set = uh“” -- against three controls.  Those two are now ACCEPTED
 at those very levels and stand in Section [UniversePin] as
 controls beside the original three (item 6); the correction is
 recorded here rather than made silently.  What remains are the two
 CONVERSION negatives.  [sigma_obj_eta],
 which records that an object of a coproduct of categories is NOT
 convertible with the pair of its projections (this is why
 [coprod_leg] is a [match] with a return annotation; its control
 [sigma_hom_eta] shows only that [sigma_equiv] PROJECTS its
 arguments, NOT that morphisms have an eta rule -- measured, a
 morphism is rejected with the same `cannot unify “f” and
 “(`1 (f); `2 (f))”` as the object), and [component_diagram_strict],
 which records
 that [Compose] rebuilds its three law fields.  Each was stripped
 of its [Fail] once and its failure kind read off the whole error.

 WHAT IS NOT DELIVERED.  No dual: nothing here is stated for
 colimits, coproducts of shapes on the colimit side, or cocones.  No
 [Colimit]/[DiscreteCat_Functor] reading of part (a), and no bridge
 to Structure/Limit/Coproduct.v's [colimit_is_indexed_coproduct].  No
 converse to (a): it is not shown that a limit of [F] forces limits
 of the restrictions, nor that the product of the summand limits is
 the ONLY apex.  No preservation, reflection or creation statement,
 and no relation to [PreservesLimit]/[CreatesLimit].  No functoriality
 or naturality of [coprod_leg] or [cd_compare] in anything.  No proof
 that a category HAS a decomposition, hence no “every category is a
 coproduct of connected categories” as an unconditional theorem, and
 no statement relating [ComponentDecomposition] to [Pi0] as a functor.
 [IdxUIP] is not shown necessary for [cd_compare_Faithful].  Nothing
 relates the [cd_sum]s of two different decompositions: [cd_transfer]
 is a bijection of INDEX TYPES compatible with the part maps, and it
 is never lifted to a comparison functor or an equivalence between
 the two coproduct categories.  No constant of type [_ ≅[Cat] _] is
 built for [cd_compare] -- work item 3 words its ask “isomorphism of
 categories in the library's [≈]-based sense”, and what is delivered
 is [EquivalenceOfCategories], which is what [≅[Cat]] amounts to in
 this tree but is not that literal type.  Finally, the issue's own
 Verification block pins [Print Assumptions
 limit_over_coproduct_is_product] and [Print Assumptions
 category_is_coproduct_of_components]; NEITHER NAME EXISTS anywhere in
 the tree, and the corresponding results here are [coprod_IsALimit]
 and [cd_equivalence], both gated.  The
 converse of [xfer_IsALimit] (that a full ESO functor of shapes
 REFLECTS limits) is not proved, and neither is any cofinality
 statement.  No notation.  No concrete category is shown complete by
 these means.  The [Coq] witness of part (a) is at a two-element
 index with point shapes; no witness instantiates part (c) at a
 concrete ambient category with a concrete non-trivial component. 

 --------
 书籍：      Mac Lane，《Categories for the Working Mathematician》，第2版，第IV.2节 练习7，印刷页90 (maclane:IV.2:ex7)
 书籍：      Riehl，《Category Theory in Context》，第3.6节 (riehl:3.6:construction-cat-coproducts)
 nLab：       https://ncatlab.org/nlab/show/connected+category
 nLab：       https://ncatlab.org/nlab/show/limit

 Mac Lane的练习有三个条款，它们作为三个定理陈述，其中有第四个结果——重新索引引理条款(c)被提取出来，因为其中没有关于分量的内容。

 (a)  [coprod_IsALimit] ：对于[F : ∐_k J_k ⟶ C]，每个限制[F ◯ inj k]的极限加上这些极限顶点的指标积给出[F]的极限，在该积上。(b) [ComponentDecomposition] 与 [cd_compare]、[cd_compare_Full]、[cd_compare_ESO]、[cd_compare_Faithful] 和 [cd_equivalence]：
 一个带有分解为数据的类别，其索引满足 [IdxUIP]，是其连通分量的余积。Mac Lane 自己的句子量化于每个类别；这个则没有，下面的 §3 和 §4 说明了原因及代价。

 (c) [components_IsALimit]：任意带有分解的形状上的极限，是其连通形状上的极限的积。

 [xfer_IsALimit]：一个完整的、基本上满射的形状函子能转移极限。忠实性不被消耗。1. 先前艺术的更正。 该目录问题声明“在树中没有任何连通谓词存在”，并要求建立折线关系及其自反性、对称性和传递性。 那是不正确的，并且在 Theory/Connected/Components.v 引入之前就是错误的：Structure/Groupoid/Connected.v 为任意类别声明了 [Inductive ZigZag {C : Category}] 和 [Definition Connected (C : Category)]，以及 [zigzag_trans]、[zigzag_sym] 和 [hom_zigzag]。 Theory/Connected/Components.v 重用了它们——它需要该模块但不重新声明——本文件也是如此。 这里没有重新声明任何折线。2. 核心缺失是真实存在的，并且是通过使用者而不是名称来衡量的。在此文件 [SigmaCat] 之前，它在目录树中仅出现过三次——它自身的模块 Construction/Coproduct/Indexed.v、Instance/Cat/Coproduct.v 和 Test/ProbeCatCoproduct338.v——且这三次都没有陈述关于形状余积的极限的任何结果。该段落的早期版本曾说“这三次都没有提到极限或圆锥”，其中关于极限的部分是错误的：这三次都提到了 [Limit]，分别出现了 2 次、11 次和 2 次，在 [Require] 行以及未交付的文字中（Instance/Cat/Coproduct.v 是一个带编号的章节，其标题为“THE [Colimit] READING IS NOT DELIVERED”）。CONE 一半部分成立——在三个中全部为零命中——结论不受影响，但最初陈述的证据是错误的。近似匹配的名称搜索确实返回了 Structure/Limit/Coproduct.v 的 [colimit_is_indexed_coproduct]，这是一个不同的陈述：它将离散图上的余极限读作对象的索引余积，并且其中没有出现指数类别的余积。根据该问题自身的 QA 更正，索引余积在这里被消耗而不是重建：[SigmaCat]、[SigmaCat_inj]、[SigmaCat_case]、[ob_cast]、[mor_cast]、[IdxUIP] 和 [IdxUIP_pair] 都来自于捐赠者。3. 第(b)部分的障碍是真实存在的，并且在此得到证明而不是仅仅断言。Theory/Connected/Components.v 的 π₀ 是在相同载体上的一个更粗的集合等价类——该文件自身的 [pi0_carrier] 记录了 [carrier (pi0 C) = obj[C] ] 通过 [eq_refl] ——所以它没有提供一个商类型来对一个余积进行索引。用它索引 [SigmaCat] 会产生每个对象一个直和子对象，而在走动箭头处则是两个子对象而应该只有一个连通分量：[naive_pi0_sum_not_connected] 证明了结果范畴不是连通的，而 [Two_Connected] 证明了 [_2] 是连通的，[no_ESO_into_naive_pi0_sum] 将其转换为消费者想要的陈述，即不存在本质上满射的函子 [_2 ⟶ naive_pi0_sum]。从其本意来读：它否定了那个指数，并且它不是证明这两个范畴不等价的证据，那需要沿着准逆映射向后携带连通性——这里没有做到。因此，分解被打包为 DATA，其模式借鉴了 Theory/Skeleton.v 中的 [Skeleton] 记录，该记录携带一个选定的代表 [skel_rep] 以及一个唯一性字段 [skel_uniq]。[ComponentDecomposition] 携带 [cd_rep]（每个索引的选定代表）、[cd_part]（对象的索引）、[cd_join]（来自代表的链）以及 [cd_sep]（唯一性条款）。没有使用选择原理，也没有声称存在无条件的分解：没有显示一个范畴拥有分解，下面的两个具体分解都是手工构建的。Riehl 的唯一性条款是 [cd_transfer] 及 [cd_transfer_round] ——索引类型仅在一个规范双射下确定——通过 [cd_transfer_part] 得到加强，该条款说明该双射与两个部分赋值兼容，因此两个分解将类别切分为相同的部分，而不仅仅是具有等数量的索引集合。4. 在一个假设被使用的地方，——更有趣的是——在它没有被使用的地方。[cd_compare_ESO] 和 [cd_compare_Full] 不使用假设；[cd_compare_Faithful] 使用捐赠者自己的 [IdxUIP (cd_index D)] ，在恰好一个地方被使用，而 [cd_equivalence] 继承了它。假设没有被证明是必要的：没有构建反例模型，也没有证明像 Construction/Coproduct/Indexed.v 中那样的强制性定理（[sigma_inj_Full_forces_UIP]）。它可通过 Hedberg（[UIP_dec]）为任何具有可判定等式的索引被解除，这正是 [poly_unit_IdxUIP] 和 [bool_IdxUIP] 对两个见证者所做的事情。部分 (c) 完全不产生任何费用 [IdxUIP]，这就是为什么 [xfer_IsALimit] 针对的是一个满的、本质上满射的函子，而不是针对等价：满性提供了原像箭头，本质满射提供了对象，而忠实性从未被使用。因此，极限分解成立的地方，无论范畴等价是否存在，也都成立。5. 优势，严格优先衡量。持有 [eq_refl]：
 [summand_obj]，[summand_map]，[coprod_leg_at]，
 [coprod_IsALimit_leg]，[coprod_IsALimit_med]，
 [coprod_IsALimit_iprod_leg]，[restrict_cone_apex]，
 [cd_compare_obj]，[cd_compare_map]，[cd_eso_obj_image]，
 [Two_Decomposition_index]，[component_diagram_obj]，
 [component_diagram_map]，[sigma_hom_eta]，以及三个 [Coq]
 计算 [CoqPair_leg_true]，[CoqPair_leg_false] 和 [CoqPair_med_computes]。以 [≈] 定居：两个
 投影与限制的声明（[coprod_proj_is_restriction]，[coprod_proj_via_iso]），它们是中介者之间的方程，因此不能是定义性的——每个都通过求和项极限自身的唯一性条款证明——
 以及 [component_diagram_equiv]，其两个数据协议是 [eq_refl]，并且在整个记录层面的反驳被固定为 [component_diagram_strict]。6. 宇宙，同时读取绑定器和约束块。
 [coprod_IsALimit@{...}] 位于 [J : I → Category@{u0 u1 u1}] 之上，并且位于 [C : Category@{u2 u3 u3}] 上，它在其块中有单个方程 [u1 = u3]：形状的同态与证明宇宙被识别为环境的宇宙。也就是说，捐赠者 [IsALimit] 自身的形状，什么都没有增加；两个对象宇宙保持自由、有界且从未被识别，并且没有 [Set] 出现。[components_IsALimit] 的读取方式相同（[J : Category@{u u0 u0}]，[C : Category@{u1 u2 u2}]，块方程 [u0 = u2]），并且 [xfer_IsALimit] 识别三个同态宇宙而不是两个（[u0 = u2] 和 [u0 = u4]），分别是两个形状的和环境的，这就是在重索引的两边声明 [IsALimit] 的代价。两个常量将标识完全放在绑定器中，且使用了一个空块或无方程块，因此仅检查块的读者会报告“没有标识”，这是错误的。[coprod_IsALimit_HasIndexedProducts] 的块中没有方程，而它的绑定器写的是 [Category@{u1 u7 u7}] 和 [Category@{u6 u7 u7}]，为四个槽重用了一个级别；[ComponentDecomposition@{u u0 u1}] 具有字面上的空块，而它的绑定器显示为 [Category@{u0 u1 u1} → Type@{...}]。后者是 [ZigZag] 自身的形状，继承而来；其 INDEX 宇宙 [u] 不属于该类别，这正是允许索引与对象类型一样大的原因。[coprod_IsALimit_iprod] 是阅读前一个 [Set] 插销的地方，而插销已经不见了。该段的早期版本说插销“到达”这里，并且“比捐赠者的活页夹单独显示的要宽”，引用了 [iprod]，在 [C : Category@{_ Set Set}] 上宣布，并将推论读取为 [J : I → Category@{u0 Set Set}] 和 [C : Category@{u3 Set Set}]；它补充说插销“是继承的，不可修复，也不被认为是不可避免的”。前半部分正确阅读了当时的树结构，最后一句也正确：插销是 Instance/Discrete.v 的 [DiscreteCat_Functor] 的宇宙最小化产物，通过 [Limit] 对形状的 hom-and-proof 宇宙与环境宇宙的识别达到 [iprod]。该捐赠者在 PR “代数承载是集合”（2026-09-17）中已在原位标注，因此没有任何字面上的 [Set] 再能达到这个推论。基本的 [IsIndexedProduct] 形式仍然首先陈述，而 [iprod] 的解读仍然是一个推论——这种排序从未仅仅关于 [Set]——下面的 [UniversePin] 节现在保护了修复：以前严格拒绝超出 [Set] 的同态的同样两行现在保留在那里作为正控制。7. 否定项：两个，均为转换。该条目的早期版本写作“四个，两种类型，保持词汇上分开”，并描述了两个可形成性否定项——[iprod] 和 [coprod_IsALimit_iprod]——由于其同类项被宣布严格高于 [Set] 而被拒绝，“每个以‘宇宙不一致：无法强制设置 = uh’结束”——针对三个控制项。这两个现在在相同级别被接受，并在 [UniversePin] 节中作为控制项与原来的三个（第6项）并列；此处记录修正，而不是悄然更改。剩下的是两个转换否定项。[sigma_obj_eta]，记录了一个类别余积的对象**不能**与其投影对可转换（这就是为什么 [coprod_leg] 是一个带返回注释的 [match]；其控制 [sigma_hom_eta] 仅显示 [sigma_equiv] 投影其参数，而不是说明态射有 eta 规则——经过测量，如果态射被拒绝，会显示相同的 `cannot unify “f” and “( `1 (f); ` 2 (f))”` 错误，就像对象一样），以及 [component_diagram_strict]，记录了 [Compose] 重建其三个律域字段的情况。每个字段都曾被去掉一次 [Fail]，并且其失败类型从整个错误中读取。未实现的内容。没有二对偶：此处未说明余极限、余积在余极限一侧的形状或余锥。部分(a)没有[Colimit] / [DiscreteCat_Functor]的解读，也没有通向Structure/Limit/Coproduct.v中的[colimit_is_indexed_coproduct]的桥梁。没有(a)的逆命题：没有证明[F]的极限会强制其限制的极限，也没有证明各部分极限的积是唯一的顶点。没有保持、反射或创建的说明，也没有与[PreservesLimit] / [CreatesLimit]的关系。没有[coprod_leg]或[cd_compare]在任何事情上的函子性或自然性。没有证明某个范畴具有分解，因此没有“每个范畴都是连通范畴的余积”的无条件定理，也没有关于[ComponentDecomposition]与[Pi0]作为函子之间关系的说明。没有证明[IdxUIP]对[cd_compare_Faithful]是必要的。没有任何东西关联两个不同分解的 [cd_sum]：[cd_transfer] 是与部分映射兼容的索引类型的双射，并且它从未被提升为比较函子或两个余积范畴之间的等价。没有为 [cd_compare] 构建类型为 [_ ≅[Cat] _] 的常量——工作项 3 的问题是“库中的 [≈] 基于意义的范畴同构”，而实际交付的是 [EquivalenceOfCategories]，它相当于在这棵树中 [≅[Cat] ] 的含义，但不是那个字面类型。最后，该问题自身的验证块固定了 [打印假设 limit_over_coproduct_is_product] 和 [打印假设 category_is_coproduct_of_components]；在树中的任何地方都不存在这两个名称，对应结果是 [coprod_IsALimit] 和 [cd_equivalence]，均受限制。[xfer_IsALimit] 的逆命题（即一个完整的 ESO 函子在形状下反映极限）尚未被证明，任何上界性声明也同样没有被证明。没有符号。没有使用这些方法展示具体范畴是完备的。[Coq] 在第 (a) 部分的证据位于具有单点形状的两元素指标上；没有任何证据在具有具体非平凡分量的具体环境范畴中实例化第 (c) 部分。
*)

(* * ** Part (a): the limit over a coproduct of shapes / * ** 部分 (a)：在形状的余积上的极限 *)

Section CoproductLimit.

Context {I : Type}.
Context {J : I → Category}.
Context {C : Category}.
Context (F : SigmaCat J ⟶ C).

(* The restriction of [F] to the k-th summand. / [F] 在第 k 个加数上的限制。 *)
Definition summand (k : I) : J k ⟶ C := F ◯ SigmaCat_inj J k.

(*
 Its object and arrow actions are [F]'s at the injected argument, by
 conversion: the injection's own two actions are [(k; x)] and
 [(eq_refl; f)]. 

 --------
 它的对象和箭头动作是在注入参数上的 [F]，通过转换：注入自身的两个动作是 [(k; x)] 和 [(eq_refl; f)]。
*)
Example summand_obj (k : I) (x : J k) : summand k x = F (k; x) := eq_refl.

Example summand_map (k : I) (x y : J k) (f : x ~> y) :
  fmap[summand k] f = fmap[F] ((eq_refl; f) : (k; x) ~{SigmaCat J}~> (k; y))
  := eq_refl.

Context {L : I → C}.
Context (HL : ∀ k : I, IsALimit (summand k) (L k)).

Context {p : C}.
Context {proj : ∀ k : I, p ~> L k}.
Context (HP : IsIndexedProduct L p proj).

(*
 The candidate legs: descend into the k-th summand's limit, then take
 that limit's leg.  The [match] is forced -- [sigT] has no eta here, so
 [X] is not convertible with [(`1 X; `2 X)] and the return type must be
 given by the branch. 

 --------
 候选项的腿：下降到第 k 个求和项的极限，然后取该极限的腿。[match] 是强制的——[sigT] 在这里没有 eta，因此 [X] 不可与 [(`1 X; `2 X)] 转换，并且返回类型必须由分支给出。
*)
Definition coprod_leg (X : SigmaCat J) : p ~> F X :=
  match X as X0 return p ~> F X0 with
  | (k; x) => limit_leg (HL k) x ∘ proj k
  end.

Example coprod_leg_at (k : I) (x : J k) :
  coprod_leg (k; x) = limit_leg (HL k) x ∘ proj k := eq_refl.

Lemma coprod_leg_coherence {X Y : SigmaCat J} (f : X ~> Y) :
  fmap[F] f ∘ coprod_leg X ≈ coprod_leg Y.
Proof.
  destruct X as [i x], Y as [j y], f as [e f]; simpl in *.
  destruct e; simpl in *.
  rewrite comp_assoc.
  now rewrite (limit_leg_coherence (HL i) f).
Qed.

Definition coprod_acone : ACone p F :=
  @Build_ACone (SigmaCat J) C p F coprod_leg (@coprod_leg_coherence).

(* * *** Restricting a competing cone to one summand / * *** 将竞争锥限制到一个子和 *)

(*
 The legs of [N] at the objects of the k-th summand form a cone over
 [summand k].  The coherence proof is [N]'s own, at the injected
 morphism: no reshaping is needed, the two statements being
 convertible. 

 --------
 [N] 在第 k 个和项的对象上的腿形成了 [summand k] 上的一个锥。相干性证明是 [N] 自己的，在注入的态射上：不需要重新构造，这两个陈述是可转换的。
*)

Definition restrict_leg (N : Cone F) (k : I) (x : J k) :
  vertex_obj[N] ~> summand k x := cone_leg N (k; x).

Lemma restrict_coherence (N : Cone F) (k : I) {x y : J k} (f : x ~> y) :
  fmap[summand k] f ∘ restrict_leg N k x ≈ restrict_leg N k y.
Proof.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) (k; x) (k; y)
           ((eq_refl; f) : (k; x) ~{SigmaCat J}~> (k; y))).
Qed.

Definition restrict_cone (N : Cone F) (k : I) : Cone (summand k) :=
  @Build_Cone (J k) C (summand k) vertex_obj[N]
    (@Build_ACone (J k) C vertex_obj[N] (summand k)
       (restrict_leg N k) (fun x y f => restrict_coherence N k f)).

(* Its apex is [N]'s, on the nose. / 它的顶点正好是 [N] 的。 *)
Example restrict_cone_apex (N : Cone F) (k : I) :
  vertex_obj[restrict_cone N k] = vertex_obj[N] := eq_refl.

(** *** The mediating morphism / *** 中介态射 *)

(*
 Mediate summand by summand into the [L k], then tuple across the
 indexed product. 

 --------
 将每一项依次调解到 [L k] 中，然后在索引乘积上进行元组化。
*)

Definition coprod_med (N : Cone F) : vertex_obj[N] ~> p :=
  unique_obj (iprod_desc HP (fun k => limit_med (HL k) (restrict_cone N k))).

Lemma coprod_med_proj (N : Cone F) (k : I) :
  proj k ∘ coprod_med N ≈ limit_med (HL k) (restrict_cone N k).
Proof.
  exact (unique_property
           (iprod_desc HP (fun k => limit_med (HL k) (restrict_cone N k))) k).
Qed.

Lemma coprod_med_commutes (N : Cone F) (X : SigmaCat J) :
  coprod_leg X ∘ coprod_med N ≈ cone_leg N X.
Proof.
  destruct X as [k x]; simpl.
  rewrite <- comp_assoc.
  rewrite (coprod_med_proj N k).
  exact (limit_med_commutes (HL k) (restrict_cone N k) x).
Qed.

Lemma coprod_med_unique (N : Cone F) (v : vertex_obj[N] ~> p) :
  (∀ X : SigmaCat J, coprod_leg X ∘ v ≈ cone_leg N X) → coprod_med N ≈ v.
Proof.
  intro Hv.
  apply (uniqueness
           (iprod_desc HP (fun k => limit_med (HL k) (restrict_cone N k)))).
  intro k.
  symmetry.
  apply (limit_med_unique (HL k) (restrict_cone N k)).
  intro x.
  rewrite comp_assoc.
  exact (Hv (k; x)).
Qed.

(** *** The theorem / *** 定理 *)

(*
 Mac Lane §IV.2 Exercise 7, first clause: the limit of a diagram over a
 coproduct of shapes is the indexed product of the limits over the
 summands.  Stated at the ELEMENTARY level -- the hypothesis is
 [IsIndexedProduct], not a [Limit] of a discrete diagram -- so no
 universe is pinned; see the [iprod] corollary below. 

 --------
 Mac Lane §IV.2 练习 7，第一条：在形状的余积上的图的极限，是这些分图极限的指标积。以初等水平来表述——假设是 [IsIndexedProduct]，而不是一个离散图的 [Limit]——所以没有固定宇宙；参见下面的 [iprod] 推论。
*)

Definition coprod_IsALimit : IsALimit F p :=
  @Build_IsALimit (SigmaCat J) C F p coprod_acone
    (fun N => Build_Unique _ _ _ (coprod_med N)
                (coprod_med_commutes N) (coprod_med_unique N)).

(* Its legs ARE [coprod_leg], by conversion. / 它的腿经过转换是 [coprod_leg]。 *)
Example coprod_IsALimit_leg (X : SigmaCat J) :
  limit_leg coprod_IsALimit X = coprod_leg X := eq_refl.

(* ... and its mediator IS [coprod_med]. / ... 它的中介是 [coprod_med]。 *)
Example coprod_IsALimit_med (N : Cone F) :
  limit_med coprod_IsALimit N = coprod_med N := eq_refl.

Definition coprod_cone : Cone F :=
  @Build_Cone (SigmaCat J) C F p coprod_acone.

Definition coprod_IsLimitCone : IsLimitCone coprod_cone :=
  @ump_limit _ _ _ _ coprod_IsALimit.

Definition coprod_Limit : Limit F := isalimit_to_limit coprod_IsALimit.

(* * *** The projections are the restrictions along the injections / * *** 投影是沿注入的约束 *)

(*
 The plainest form: mediating the restriction of the assembled limit
 cone to the k-th summand returns the k-th projection.  This is what
 “the product projections agree with restriction along the injections”
 says at the assembled limit, and it is proved through the SUMMAND's
 own uniqueness clause rather than read off the definition. 

 --------
 最简单的形式：将组装极限锥的限制调解到第 k 个加数，会返回第 k 个投影。这就是“乘积投影与沿注入的限制一致”在组装极限处所表达的意思，并且它是通过加数自身的唯一性条款证明的，而不是从定义中直接得出的。
*)

Lemma coprod_proj_is_restriction (k : I) :
  limit_med (HL k) (restrict_cone coprod_cone k) ≈ proj k.
Proof.
  apply (limit_med_unique (HL k) (restrict_cone coprod_cone k)).
  intro x; reflexivity.
Qed.

(*
 The general form, at an ARBITRARY limit of [F].  Restricting that
 limit's cone to the k-th summand and mediating into [L k] returns the
 k-th projection conjugated by the comparison isomorphism.  Nothing
 here is definitional: the proof runs through the summand's uniqueness
 clause and the leg equations of [limit_unique_iso]. 

 --------
 一般形式，在 [F] 的任意极限处。将该极限的锥限制到第 k 个直和分量并中介到 [L k]，会返回由比较同构共轭的第 k 个投影。这里没有任何是定义性的：证明通过直和分量的唯一性条款以及 [limit_unique_iso] 的腿方程进行。
*)

Lemma coprod_proj_via_iso {c : C} (Hc : IsALimit F c) (k : I) :
  proj k ∘ to (limit_unique_iso Hc coprod_IsALimit)
    ≈ limit_med (HL k) (restrict_cone (alimit_cone Hc) k).
Proof.
  symmetry.
  apply (limit_med_unique (HL k) (restrict_cone (alimit_cone Hc) k)).
  intro x.
  rewrite comp_assoc.
  exact (fst (limit_unique_iso_legs Hc coprod_IsALimit) (k; x)).
Qed.

(* * *** Part (a) packaged as an isomorphism / * *** 部分（a）封装为同构 *)

(*
 Any apex carrying a limit of [F] is canonically isomorphic to the
 indexed product of the summand limits.  [limit_unique_iso] carries the
 leg equations, and [limit_unique_iso_unique] the uniqueness clause, so
 this is not a bare [≅]. 

 --------
 任何承载极限 [F] 的极点在范畴上同构于求和限的指标积。[limit_unique_iso] 承载腿方程，而 [limit_unique_iso_unique] 承载唯一性条款，因此这不是一个裸的 [≅]。
*)

Definition coprod_limit_iso {c : C} (Hc : IsALimit F c) : c ≅ p :=
  limit_unique_iso Hc coprod_IsALimit.

Definition coprod_limit_iso_legs {c : C} (Hc : IsALimit F c) :
  (∀ X : SigmaCat J,
     coprod_leg X ∘ to (coprod_limit_iso Hc) ≈ limit_leg Hc X) *
  (∀ X : SigmaCat J,
     limit_leg Hc X ∘ from (coprod_limit_iso Hc) ≈ coprod_leg X) :=
  limit_unique_iso_legs Hc coprod_IsALimit.

Theorem coprod_limit_iso_unique {c : C} (Hc : IsALimit F c)
  (h : c ~{C}~> p) :
  (∀ X : SigmaCat J, coprod_leg X ∘ h ≈ limit_leg Hc X) →
  h ≈ to (coprod_limit_iso Hc).
Proof. exact (limit_unique_iso_unique Hc coprod_IsALimit h). Qed.

End CoproductLimit.

Arguments summand {I J C} F k.
Arguments coprod_leg {I J C} F {L} HL {p proj} X.
Arguments coprod_IsALimit {I J C} F {L} HL {p proj} HP.

(** *** The bundled readings / *** 捆绑阅读材料 *)

(*
 Over a category with all indexed products the hypothesis [HP]
 disappears.  [HasIndexedProducts] is stated over [IsIndexedProduct],
 so this reading carries no [Set] pin either. 

 --------
 在包含所有已索引产品的类别上，假设 [HP] 消失了。[HasIndexedProducts] 在 [IsIndexedProduct] 上被提出，因此这个读数也没有 [Set] 针脚。
*)

Definition coprod_IsALimit_HasIndexedProducts {I : Type} {J : I → Category}
  {C : Category} (F : SigmaCat J ⟶ C) (HIP : HasIndexedProducts C)
  {L : I → C} (HL : ∀ k : I, IsALimit (summand F k) (L k)) :
  IsALimit F (indexed_product L) :=
  coprod_IsALimit F HL (indexed_product_ump L).

(*
 The [iprod] reading the issue's reviewer check asks for: the right-hand
 side is [Structure/Limit/Product.v]'s own product operator, not a
 bespoke one.  RECORDED CORRECTION: an earlier revision continued “IT
 INHERITS THAT DONOR'S UNIVERSE PIN -- [iprod] is defined over
 [Limit (DiscreteCat_Functor f)] and so is declared at
 [C : Category@{_ Set Set}], where [coprod_IsALimit] above leaves both
 levels free.”  The pin is gone: the donor was annotated in place at
 Instance/Discrete.v in the PR “algebraic carriers are sets”
 (2026-09-17), and [iprod@{u u0 u1 u2 u3}] is now declared over
 [C : Category@{u1 u2 u2}].  What it still inherits is [Limit]'s
 IDENTIFICATION of the discrete shape's hom-and-proof universe with the
 ambient's, where [coprod_IsALimit] above leaves the two apart; that,
 rather than a [Set] floor, is why the elementary form is stated first
 and this one is a corollary. 

 --------
 [iprod] 阅读该问题的审阅者检查要求：右侧是 [Structure/Limit/Product.v] 自己的积运算符，而不是定制的。已记录的更正：早期的修订继续说“它继承了该捐赠者的宇宙引脚——[iprod] 在 [Limit (DiscreteCat_Functor f)] 上定义，因此在 [C : Category@{_ Set Set}] 上声明，而上面的 [coprod_IsALimit] 使两个层级都自由。”引脚已消失：捐赠者已在 PR “代数载体是集合”（2026-09-17）中在 Instance/Discrete.v 原位标注，现在 [iprod@{u u0 u1 u2 u3}] 已在 [C : Category@{u1 u2 u2}] 上声明。它仍然继承的是 [Limit] 对离散形状的 hom-and-proof 宇宙与环境的一致性的 IDENTIFICATION，而上面的 [coprod_IsALimit] 保持两者分开；这恰恰是为什么基础形式先声明，而这个是推论，而不是 [Set] 的限制。
*)

Definition coprod_IsALimit_iprod {I : Type} {J : I → Category}
  {C : Category} (F : SigmaCat J ⟶ C)
  {L : I → C} (HL : ∀ k : I, IsALimit (summand F k) (L k))
  (P : Limit (DiscreteCat_Functor L)) : IsALimit F (iprod L P) :=
  coprod_IsALimit F HL (limit_is_indexed_product L P).

Definition coprod_Limit_iprod {I : Type} {J : I → Category}
  {C : Category} (F : SigmaCat J ⟶ C)
  {L : I → C} (HL : ∀ k : I, IsALimit (summand F k) (L k))
  (P : Limit (DiscreteCat_Functor L)) : Limit F :=
  isalimit_to_limit (coprod_IsALimit_iprod F HL P).

(*
 The [iprod] corollary's legs are the general ones at [iprod_proj], by
 conversion -- so the corollary is the theorem instantiated, not a
 parallel construction. 

 --------
 [iprod] 推论的推脚是 [iprod_proj] 的一般形式，通过转换得出——所以该推论是定理的实例化，而不是平行构造。
*)

Example coprod_IsALimit_iprod_leg {I : Type} {J : I → Category}
  {C : Category} (F : SigmaCat J ⟶ C)
  {L : I → C} (HL : ∀ k : I, IsALimit (summand F k) (L k))
  (P : Limit (DiscreteCat_Functor L)) (k : I) (x : J k) :
  limit_leg (coprod_IsALimit_iprod F HL P) (k; x)
    = limit_leg (HL k) x ∘ iprod_proj L P k := eq_refl.

(* * ** Part (b): the decomposition of a category into its components / * ** 部分 (b)：将一个类别分解成其组成部分 *)

(*
 A DECOMPOSITION OF [C] INTO CONNECTED COMPONENTS, PACKAGED AS DATA.
 The design follows Theory/Skeleton.v's [Skeleton] record exactly:
 an index type, a CHOSEN representative for each index, the assignment
 of an index to each object, a chain joining every object to its
 representative, and a uniqueness clause.  It is data and not a
 theorem, and the header says why: [Theory/Connected/Components.v]'s
 π₀ is a COARSER SETOID ON THE SAME CARRIER, so it supplies no
 quotient type to index a coproduct by. 

 --------
 将 [C] 分解为连通分量，以数据形式打包。
 设计严格遵循 Theory/Skeleton.v 中的 [Skeleton] 记录：一个索引类型，每个索引的 CHOSEN 代表，对每个对象的索引分配，将每个对象连接到其代表的链，以及唯一性条款。它是数据而不是定理，头部注明了原因：[Theory/Connected/Components.v] 的 π₀ 在相同载体上是一个更粗的集合等价类，因此它不能提供用来索引余积的商类型。
*)

Record ComponentDecomposition (C : Category) := {
  cd_index : Type;
  cd_rep   : cd_index → C;
  cd_part  : C → cd_index;
  cd_join  : ∀ x : C, ZigZag (cd_rep (cd_part x)) x;
  cd_sep   : ∀ (x : C) (k : cd_index), ZigZag (cd_rep k) x → cd_part x = k
}.

Arguments cd_index {_} _.
Arguments cd_rep {_} _.
Arguments cd_part {_} _.
Arguments cd_join {_} _.
Arguments cd_sep {_} _.

Section DecompositionTheory.

Context {C : Category}.
Variable D : ComponentDecomposition C.

(* Choosing a representative and reading off its index is the identity. / 选择一个代表并读出它的索引就是身份。 *)
Definition cd_part_rep (k : cd_index D) : cd_part D (cd_rep D k) = k :=
  cd_sep D (cd_rep D k) k (zz_nil _).

(* Joined objects lie in the same component. / 连接的对象位于同一组件中。 *)
Definition cd_part_zigzag {x y : C} (s : ZigZag x y) :
  cd_part D x = cd_part D y :=
  eq_sym (cd_sep D y (cd_part D x) (zigzag_trans (cd_join D x) s)).

(*
 ... and conversely, which is the other half of “the parts ARE the
 components”.  This direction consumes no [cd_sep]. 

 --------
 ... 相反，这正是“部分就是组成部分”的另一半。这种方向不消耗 [cd_sep]。
*)
Definition cd_conn {x y : C} (e : cd_part D x = cd_part D y) : ZigZag x y :=
  zigzag_trans
    (match e in _ = k return ZigZag x (cd_rep D k) with
     | eq_refl => zigzag_sym (cd_join D x)
     end)
    (cd_join D y).

(* * *** The summands, the coproduct, and the comparison functor / * *** 加数、余积和比较函子 *)

Definition cd_comp (k : cd_index D) : Category :=
  ConnectedComponent C (cd_rep D k).

Definition cd_sum : Category := SigmaCat cd_comp.

Definition cd_compare : cd_sum ⟶ C :=
  SigmaCat_case (fun k => Component_Incl C (cd_rep D k)).

(* Each summand is connected -- the donor's own theorem, instantiated. / 每一个加数都是相连的——捐赠者自己的定理，被实例化了。 *)
Definition cd_comp_Connected (k : cd_index D) : Connected (cd_comp k) :=
  Component_Connected C (cd_rep D k).

(* Both actions of the comparison are the evident projections, by conversion. / 比较的两个动作都是通过转换显而易见的投射。 *)
Example cd_compare_obj (k : cd_index D) (a : cd_comp k) :
  cd_compare (k; a) = `1 a := eq_refl.

Example cd_compare_map (k : cd_index D) (a b : cd_comp k) (f : a ~> b) :
  fmap[cd_compare] ((eq_refl; f) : (k; a) ~{cd_sum}~> (k; b)) = `1 f
  := eq_refl.

(* * *** The comparison is essentially surjective, with NO hypothesis / * *** 该比较本质上是满射的，没有任何假设 *)

(*
 It is more than essentially surjective: it is SPLIT SURJECTIVE ON
 OBJECTS, the chosen preimage's image being the object itself by
 conversion, so the witnessing isomorphism is [iso_id].  That is what
 makes the limit transfer of part (c) cheap. 

 --------
 它不仅仅是本质上满射：它在对象上是分裂满射，所选择的原像的像通过转换正好是对象本身，因此见证同构是 [iso_id]。这就是使第（c）部分的极限转移变得廉价的原因。
*)

Definition cd_eso_obj (y : C) : cd_sum :=
  (cd_part D y; ((y; cd_join D y) : cd_comp (cd_part D y))).

Example cd_eso_obj_image (y : C) : cd_compare (cd_eso_obj y) = y := eq_refl.

Definition cd_compare_ESO : EssentiallySurjective cd_compare :=
  @Build_EssentiallySurjective cd_sum C cd_compare cd_eso_obj
    (fun y => iso_id).

(* * *** The comparison is full, with NO hypothesis / * *** 比较是完整的，没有假设 *)

(*
 The index equality.  Both objects' membership witnesses pin their own
 index, and the arrow supplies a one-step chain between the carriers;
 [cd_sep] converts each into an index equation and [cd_part_zigzag]
 bridges them. 

 --------
 索引相等。两个对象的成员见证各自固定自己的索引，箭头在承载体之间提供一步链；[cd_sep] 将每个转换为索引方程，[cd_part_zigzag] 将它们连接起来。
*)

Definition cd_full_eq {X Y : cd_sum} (f : cd_compare X ~> cd_compare Y) :
  `1 X = `1 Y :=
  eq_trans (eq_sym (cd_sep D (`1 (`2 X)) (`1 X) (`2 (`2 X))))
    (eq_trans (cd_part_zigzag (hom_zigzag f))
              (cd_sep D (`1 (`2 Y)) (`1 Y) (`2 (`2 Y)))).

(* Given ANY index equality, the arrow lifts. The equality is a universally quantified variable here, which is exactly what makes [destruct e] available and every transport vanish. / 给定任意索引等式，箭头上升。这里的等式是一个全称量化变量，这正是使 [destruct e] 可用并且每个传输消失的原因。 *)

Lemma cd_full_step {X Y : cd_sum} (e : `1 X = `1 Y)
  (f : cd_compare X ~> cd_compare Y) :
  ∃ g : ob_cast cd_comp e (`2 X) ~> `2 Y,
    fmap[cd_compare] ((e; g) : X ~{cd_sum}~> Y) ≈ f.
Proof.
  destruct X as [k a], Y as [l b]; simpl in *.
  destruct e; simpl in *.
  destruct a as [x sx], b as [y sy]; simpl in *.
  exists (component_arr sx sy f).
  reflexivity.
Defined.

Definition cd_compare_Full : Functor.Full cd_compare := {|
  prefmap := fun X Y f =>
    ((cd_full_eq f; `1 (cd_full_step (cd_full_eq f) f)) : X ~{cd_sum}~> Y);
  fmap_sur := fun X Y f => `2 (cd_full_step (cd_full_eq f) f)
|}.

(* * *** Faithfulness, and the one hypothesis the file spends / * *** 忠诚，以及文件所花费的一个假设 *)

Lemma cd_faithful_step {X Y : cd_sum} (e1 e2 : `1 X = `1 Y) (p : e1 = e2)
  (g1 : ob_cast cd_comp e1 (`2 X) ~> `2 Y)
  (g2 : ob_cast cd_comp e2 (`2 X) ~> `2 Y) :
  fmap[cd_compare] ((e1; g1) : X ~{cd_sum}~> Y)
    ≈ fmap[cd_compare] ((e2; g2) : X ~{cd_sum}~> Y) →
  mor_cast cd_comp p g1 ≈ g2.
Proof.
  destruct X as [k a], Y as [l b]; simpl in *.
  destruct p; destruct e1; simpl in *.
  intro H; exact H.
Qed.

(*
 [IdxUIP] is the donor's own hypothesis (Construction/Coproduct/
 Indexed.v), and it is spent HERE AND NOWHERE ELSE in this file. 

 --------
 [IdxUIP] 是捐赠者自己的假设（Construction/Coproduct/Indexed.v），并且它仅在此处使用，在此文件的其他地方没有使用。
*)

Definition cd_compare_Faithful (U : IdxUIP (cd_index D)) :
  Functor.Faithful cd_compare :=
  @Build_Faithful cd_sum C cd_compare
    (fun (X Y : cd_sum) (f g : X ~{cd_sum}~> Y) H =>
       (IdxUIP_pair U (`1 f) (`1 g);
        cd_faithful_step (`1 f) (`1 g) (IdxUIP_pair U (`1 f) (`1 g))
          (`2 f) (`2 g) H)).

(*
 Riehl §3.6: a category IS the coproduct of its connected components.
 The strength is an EQUIVALENCE of categories, and the hypothesis is
 [IdxUIP] on the index -- see the header for what is and is not known
 about its necessity. 

 --------
 Riehl §3.6：一个范畴是其连通分量的余积。
 强度是范畴的一个等价，而假设是
 [IdxUIP] 在指数上——参见标题了解关于其必要性已知和未知的内容。
*)

Definition cd_equivalence (U : IdxUIP (cd_index D)) :
  EquivalenceOfCategories cd_compare :=
  @FF_ESO_Equivalence cd_sum C cd_compare
    cd_compare_Full (cd_compare_Faithful U) cd_compare_ESO.

(* The bundled reading, in the vocabulary Theory/Skeleton.v uses for the analogous statement about skeletons. / 在词汇 Theory/Skeleton.v 中捆绑的阅读，用于关于骨架的类似陈述。 *)

Definition cd_bundled_equivalence (U : IdxUIP (cd_index D)) : cd_sum ≃ C :=
  (cd_compare; cd_equivalence U).

End DecompositionTheory.

(* * ** Riehl's uniqueness clause for the decomposition / * ** Riehl 分解的独特性条款 *)

(*
 Transport an index of one decomposition to an index of another, by
 reading off the part of its chosen representative. 

 --------
 通过读取所选代表的部分，将一个分解的指标传输到另一个指标。
*)

Definition cd_transfer {C : Category} (D D' : ComponentDecomposition C)
  (k : cd_index D) : cd_index D' := cd_part D' (cd_rep D k).

(*
 The two transfers are mutually inverse, so the index type of a
 decomposition is determined up to a canonical bijection.  Only one
 direction is written: it is symmetric in [D] and [D'], so the other is
 the same statement with the arguments exchanged. 

 --------
 这两个变换是相互逆的，因此分解的指标类型可以通过一个典型的双射确定。只写出一个方向：它在 [D] 和 [D'] 中是对称的，因此另一个方向就是交换参数后的相同陈述。
*)

Lemma cd_transfer_round {C : Category} (D D' : ComponentDecomposition C)
  (k : cd_index D) : cd_transfer D' D (cd_transfer D D' k) = k.
Proof.
  unfold cd_transfer.
  transitivity (cd_part D (cd_rep D k)).
  - exact (cd_part_zigzag D (cd_join D' (cd_rep D k))).
  - exact (cd_part_rep D k).
Qed.

(*
 Sharper than a bare bijection: the transfer is COMPATIBLE with the two
 part-assignments, so the two decompositions cut [C] into the same
 pieces rather than merely having equinumerous index sets. 

 --------
 比裸双射更锋利：该转移与两个部分赋值兼容，因此这两个分解将 [C] 切成相同的部分，而不仅仅是具有等数的索引集合。
*)

Lemma cd_transfer_part {C : Category} (D D' : ComponentDecomposition C)
  (y : C) : cd_transfer D D' (cd_part D y) = cd_part D' y.
Proof. exact (cd_part_zigzag D' (cd_join D y)). Qed.

(* ... and it carries representatives to joined representatives. / ... 它将代表带到联合的代表那里。 *)

Definition cd_transfer_join {C : Category} (D D' : ComponentDecomposition C)
  (k : cd_index D) :
  ZigZag (cd_rep D' (cd_transfer D D' k)) (cd_rep D k) :=
  cd_join D' (cd_rep D k).

(* * ** Limits along a full, essentially surjective functor of shapes / * ** 沿着全的、本质上满射的形状函子取极限 *)

(*
 The reindexing step part (c) needs.  FAITHFULNESS IS NOT CONSUMED:
 fullness supplies the preimage arrows and essential surjectivity the
 objects, and that is all the argument uses.  So the decomposition
 theorem for limits costs no [IdxUIP], even though the equivalence of
 categories of part (b) does. 

 --------
 重索引步骤部分 (c) 需要。忠实性不被消耗：满性提供原像箭头，本质满性提供对象，这就是论证所使用的全部。因此，极限的分解定理不需要任何 [IdxUIP]，即使部分 (b) 的范畴等价确实需要。
*)

Section LimitAlongFullESO.

(*
 Section-local: the fullness and essential-surjectivity hypotheses are
 consumed only inside proofs, so the ambient default (which reads the
 statement alone) rejects them.  Scoped to this section so that the
 part (a) definitions do not pick up hypotheses they never use. 

 --------
 局部于章节：满性和本质上的上射假设仅在证明内部使用，因此环境默认（仅读取陈述）会拒绝它们。将其限定在本章节，以便(a)部分的定义不会拾取它们从未使用过的假设。
*)
Local Set Default Proof Using "All".

Context {K J C : Category}.
Context (Phi : K ⟶ J).
Context (PF : Functor.Full Phi).
Context (PE : EssentiallySurjective Phi).

#[local] Existing Instance PF.
#[local] Existing Instance PE.

Context (G : J ⟶ C).
Context {c : C}.
Context (H : IsALimit (G ◯ Phi) c).

Definition xfer_leg (y : J) : c ~> G y :=
  fmap[G] (to (eso_iso y)) ∘ limit_leg H (eso_obj y).

(*
 At an object in the image the conjugation is invisible: the leg is the
 one the given limit already has.  This is where fullness is spent the
 second time, and it is what makes the uniqueness clause go through. 

 --------
 在图像中的一个物体上，结合是不可见的：那条腿是给定限制已经有的那条腿。这是丰满第二次被消耗的地方，也是使唯一性条款成立的原因。
*)

Lemma xfer_leg_image (z : K) : xfer_leg (Phi z) ≈ limit_leg H z.
Proof.
  unfold xfer_leg.
  transitivity (fmap[G] (fmap[Phi] (prefmap (to (eso_iso (Phi z)))))
                  ∘ limit_leg H (eso_obj (Phi z))).
  - now rewrite (fmap_sur (to (eso_iso (Phi z)))).
  - exact (limit_leg_coherence H (prefmap (to (eso_iso (Phi z))))).
Qed.

Lemma xfer_coherence {y z : J} (f : y ~> z) :
  fmap[G] f ∘ xfer_leg y ≈ xfer_leg z.
Proof.
  unfold xfer_leg.
  pose (g := from (eso_iso z) ∘ f ∘ to (eso_iso y)).
  assert (Hg : f ∘ to (eso_iso y) ≈ to (eso_iso z) ∘ g).
  { unfold g; rewrite !comp_assoc, iso_to_from, id_left; reflexivity. }
  assert (Hleg : fmap[G] g ∘ limit_leg H (eso_obj y)
                   ≈ limit_leg H (eso_obj z)).
  { transitivity (fmap[G] (fmap[Phi] (prefmap g)) ∘ limit_leg H (eso_obj y)).
    - now rewrite (fmap_sur g).
    - exact (limit_leg_coherence H (prefmap g)). }
  rewrite comp_assoc, <- fmap_comp, Hg, fmap_comp, <- comp_assoc.
  now rewrite Hleg.
Qed.

Definition xfer_acone : ACone c G :=
  @Build_ACone J C c G xfer_leg (@xfer_coherence).

(*
 A cone over [G] restricts along [Phi] to a cone over [G ◯ Phi]; the
 coherence proof is the given cone's own, at the [Phi]-image arrow. 

 --------
 在  [G] 上的一个圆锥沿  [Phi] 限制为在  [G ◯ Phi] 上的一个圆锥；其一致性证明是给定圆锥自身在  [Phi] 映射箭头上的证明。
*)

Definition xfer_restrict (N : Cone G) : Cone (G ◯ Phi) :=
  @Build_Cone K C (G ◯ Phi) vertex_obj[N]
    (@Build_ACone K C vertex_obj[N] (G ◯ Phi)
       (fun z => cone_leg N (Phi z))
       (fun z w h => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N)
                       (Phi z) (Phi w) (fmap[Phi] h))).

(*
 Deliberately unascribed: writing the type as [vertex_obj[N] ~> c]
 would make the composite below carry a different (though convertible)
 object argument, and setoid rewriting matches syntactically. 

 --------
 故意未标注来源：将类型写为 [vertex_obj[N]  ~> c] 会使下面的复合使用不同的（但可转换的）对象参数，并且集合重写在语法上匹配。
*)
Definition xfer_med (N : Cone G) := limit_med H (xfer_restrict N).

Lemma xfer_med_commutes (N : Cone G) (y : J) :
  xfer_leg y ∘ xfer_med N ≈ cone_leg N y.
Proof.
  transitivity (fmap[G] (to (eso_iso y)) ∘ cone_leg N (Phi (eso_obj y))).
  - unfold xfer_leg, xfer_med.
    rewrite <- comp_assoc.
    apply compose_respects; [ reflexivity |].
    exact (limit_med_commutes H (xfer_restrict N) (eso_obj y)).
  - exact (@cone_coherence J C vertex_obj[N] G (@coneFrom J C G N)
             (Phi (eso_obj y)) y (to (eso_iso y))).
Qed.

Lemma xfer_med_unique (N : Cone G) (v : vertex_obj[N] ~> c) :
  (∀ y : J, xfer_leg y ∘ v ≈ cone_leg N y) → xfer_med N ≈ v.
Proof.
  intro Hv.
  apply (limit_med_unique H (xfer_restrict N)).
  intro z.
  rewrite <- (xfer_leg_image z).
  exact (Hv (Phi z)).
Qed.

Definition xfer_IsALimit : IsALimit G c :=
  @Build_IsALimit J C G c xfer_acone
    (fun N => Build_Unique _ _ _ (xfer_med N)
                (xfer_med_commutes N) (xfer_med_unique N)).

End LimitAlongFullESO.

(* * ** Part (c): every limit is a product of limits over connected shapes / * ** 第(c)部分：每个极限都是在连通形状上的极限的乘积 *)

Section ComponentLimit.

Context {J C : Category}.
Variable D : ComponentDecomposition J.
Variable F : J ⟶ C.

(* The diagram restricted to the k-th connected component. / 该图仅限于第 k 个连通分量。 *)
Definition component_diagram (k : cd_index D) : cd_comp D k ⟶ C :=
  F ◯ Component_Incl J (cd_rep D k).

(* It agrees with the k-th summand of the reindexed diagram on BOTH actions, by conversion... / 它在两个作用上都与重新索引图的第 k 项和一致，通过转换… *)

Example component_diagram_obj (k : cd_index D) (a : cd_comp D k) :
  component_diagram k a = summand (F ◯ cd_compare D) k a := eq_refl.

Example component_diagram_map (k : cd_index D) (a b : cd_comp D k)
  (f : a ~> b) :
  fmap[component_diagram k] f = fmap[summand (F ◯ cd_compare D) k] f
  := eq_refl.

(*
 ... but the two functor RECORDS are not identified: [Compose] rebuilds
 its three law fields, and they are distinct opaque terms.  Measured,
 not assumed. 

 --------
 ... 但是这两个函子 RECORDS 没有被识别：[Compose] 重建了它的三个法则字段，它们是不同的不可透明项。已测量，而非假设。
*)

Fail Example component_diagram_strict (k : cd_index D) :
  component_diagram k = summand (F ◯ cd_compare D) k := eq_refl.

(*
 So the comparison is made at [≈], with identity components -- which is
 all the two definitional agreements above leave to prove. 

 --------
 所以比较是在 [≈] 处进行的，具有恒等分量——这正是上述两个定义性约定剩下需要证明的内容。
*)

Definition component_diagram_equiv (k : cd_index D) :
  component_diagram k ≈ summand (F ◯ cd_compare D) k.
Proof.
  exists (fun _ => iso_id).
  intros x y f; simpl.
  rewrite id_left, id_right; reflexivity.
Defined.

(*
 Mac Lane §IV.2 Exercise 7, third clause.  Given a decomposition of the
 SHAPE, a limit over each connected component, and an indexed product
 of those limits, the diagram has a limit at that product.  NO [IdxUIP]
 is spent: the reindexing runs through [xfer_IsALimit], which consumes
 only fullness and essential surjectivity. 

 --------
 Mac Lane §IV.2 习题 7，第三条款。给定一个形状的分解、每个连通分量的极限，以及这些极限的指标积，该图在该积上有一个极限。没有 [IdxUIP] 被消耗：重新索引经过 [xfer_IsALimit]，仅消耗满性和本质满射性。
*)

Definition components_IsALimit {L : cd_index D → C}
  (HL : ∀ k : cd_index D, IsALimit (component_diagram k) (L k))
  {p : C} {proj : ∀ k : cd_index D, p ~> L k}
  (HP : IsIndexedProduct L p proj) : IsALimit F p :=
  xfer_IsALimit (cd_compare D) (cd_compare_Full D) (cd_compare_ESO D) F
    (coprod_IsALimit (F ◯ cd_compare D)
       (fun k => isalimit_transport (component_diagram_equiv k) (HL k)) HP).

Definition components_Limit {L : cd_index D → C}
  (HL : ∀ k : cd_index D, IsALimit (component_diagram k) (L k))
  {p : C} {proj : ∀ k : cd_index D, p ~> L k}
  (HP : IsIndexedProduct L p proj) : Limit F :=
  isalimit_to_limit (components_IsALimit HL HP).

(* The bundled reading over a category with all indexed products. / 针对包含所有已索引产品的类别的捆绑阅读。 *)

Definition components_IsALimit_HasIndexedProducts (HIP : HasIndexedProducts C)
  {L : cd_index D → C}
  (HL : ∀ k : cd_index D, IsALimit (component_diagram k) (L k)) :
  IsALimit F (indexed_product L) :=
  components_IsALimit HL (indexed_product_ump L).

End ComponentLimit.

(* * ** Non-vacuity, part 1: the connected (one-component) case / * ** 非空性，第一部分：连通（一元）情况 *)

(* The walking arrow is connected, though NOT by a single arrow in either direction -- there is no [TwoY ~> TwoX] -- so the zig-zag really is used. / 行走箭头是连接的，虽然没有用单一箭头在任一方向上连接——没有 [TwoY ~> TwoX] ——所以之字形的使用确实是必要的。 *)

Definition two_ZigZag (x y : _2) : ZigZag x y.
Proof.
  destruct x, y.
  - exact (zz_nil _).
  - exact (hom_zigzag (TwoXY : TwoX ~{_2}~> TwoY)).
  - exact (zigzag_sym (hom_zigzag (TwoXY : TwoX ~{_2}~> TwoY))).
  - exact (zz_nil _).
Defined.

Definition Two_Connected : Connected _2 := two_ZigZag.

Definition Two_Decomposition : ComponentDecomposition _2 :=
  @Build_ComponentDecomposition _2 poly_unit
    (fun _ => TwoX) (fun _ => ttt)
    (fun x => two_ZigZag TwoX x)
    (fun x k s => match k as k0 return ttt = k0 with ttt => eq_refl end).

(*
 Its index is a singleton -- the degenerate case, and it is labelled as
 such: what it exercises is that the machinery closes when there is one
 component, not that the decomposition is informative. 

 --------
 它的指标是单元素——退化情况，并被标记为此：它所体现的是当只有一个组件时机制会闭合，而不是分解是有信息量的。
*)

Example Two_Decomposition_index : cd_index Two_Decomposition = poly_unit
  := eq_refl.

(*
 [poly_unit_IdxUIP] is the DONOR's (Construction/Coproduct/Indexed.v),
 not a second copy. 

 --------
 [poly_unit_IdxUIP] 是捐赠者的（Construction/Coproduct/Indexed.v），不是第二份副本。
*)

Definition Two_cd_equivalence :
  EquivalenceOfCategories (cd_compare Two_Decomposition) :=
  cd_equivalence Two_Decomposition poly_unit_IdxUIP.

(*
 The one component is not itself trivial: it contains both objects of
 [_2], with the non-identity arrow between them. 

 --------
 这个组成部分本身并非微不足道：它包含 [_2] 的两个对象，以及它们之间的非单位箭头。
*)

Definition Two_component_TwoX : cd_comp Two_Decomposition ttt :=
  Component_obj _2 TwoX.

Definition Two_component_TwoY : cd_comp Two_Decomposition ttt :=
  existT _ TwoY (two_ZigZag TwoX TwoY).

Definition Two_component_arrow :
  Two_component_TwoX ~{cd_comp Two_Decomposition ttt}~> Two_component_TwoY :=
  @component_arr _2 TwoX TwoX TwoY (@zz_nil _2 TwoX)
    (two_ZigZag TwoX TwoY) TwoXY.

Lemma Two_component_objects_differ : TwoX <> TwoY.
Proof. discriminate. Qed.

(* * ** Non-vacuity, part 2: a shape with two components / * ** 非空性，第2部分：具有两个组成部分的形状 *)

(*
 Along a zig-zag in a coproduct of categories the index never moves:
 every step carries an index equality, and the chain composes them. 

 --------
 在类别的余积中的锯齿形路径上，指标从不移动：每一步都携带一个指标相等，链将它们组合起来。
*)

Fixpoint sigma_index_zigzag {I : Type} {Cs : I → Category}
  {X Y : SigmaCat Cs} (s : ZigZag X Y) : `1 X = `1 Y :=
  match s in ZigZag a b return `1 a = `1 b with
  | zz_nil _    => eq_refl
  | zz_fwd f s' => eq_trans (`1 f) (sigma_index_zigzag s')
  | zz_bwd f s' => eq_trans (eq_sym (`1 f)) (sigma_index_zigzag s')
  end.

(* Two disjoint copies of the walking arrow. / 两个不相交的行走箭头的副本。 *)

Definition TwoSum : Category := SigmaCat (fun _ : bool => _2).

Definition twosum_arr (X : TwoSum) : ((`1 X; TwoX) : TwoSum) ~> X :=
  (eq_refl; match `2 X as o return TwoX ~{_2}~> o with
            | TwoX => id
            | TwoY => TwoXY
            end).

Definition TwoSum_Decomposition : ComponentDecomposition TwoSum :=
  @Build_ComponentDecomposition TwoSum bool
    (fun k => ((k; TwoX) : TwoSum)) (fun X => `1 X)
    (fun X => hom_zigzag (twosum_arr X))
    (fun X k s => eq_sym (sigma_index_zigzag s)).

(* THE DECOMPOSITION IS NOT DEGENERATE, AND THIS IS PROVED RATHER THAN ASSERTED. The two summands are genuinely separated: no zig-zag joins a point of one to a point of the other. / 分解不是退化的，这已经被证明而不是断言。两个加数是真正分开的：没有之字形将一个的点连接到另一个的点。 *)

Theorem TwoSum_separated :
  ZigZag ((true; TwoX) : TwoSum) ((false; TwoX) : TwoSum) → False.
Proof. intro s; exact (Bool.diff_true_false (sigma_index_zigzag s)). Qed.

Corollary TwoSum_not_connected : Connected TwoSum → False.
Proof. intro K; exact (TwoSum_separated (K _ _)). Qed.

(*
 ... and neither summand is a point: each contains both objects of the
 walking arrow, which are distinct in [TwoSum]. 

 --------
 ... 并且两个加数都不是一个点：每个都包含步行箭头的两个对象，这些对象在 [TwoSum] 中是不同的。
*)

Definition twosum_snd (X : TwoSum) : bool :=
  match `2 X with TwoX => true | TwoY => false end.

Theorem TwoSum_component_objects_differ (k : bool) :
  ((k; TwoX) : TwoSum) <> (k; TwoY).
Proof.
  intro e.
  exact (Bool.diff_true_false (f_equal twosum_snd e)).
Qed.

Example TwoSum_component_TwoY (k : bool) : cd_comp TwoSum_Decomposition k :=
  (((k; TwoY) : TwoSum); hom_zigzag (twosum_arr (k; TwoY))).

Definition bool_IdxUIP : IdxUIP bool :=
  fun i p => UIP_dec Bool.bool_dec p eq_refl.

Definition TwoSum_cd_equivalence :
  EquivalenceOfCategories (cd_compare TwoSum_Decomposition) :=
  cd_equivalence TwoSum_Decomposition bool_IdxUIP.

(* * ** Why the index cannot simply be π₀ / * ** 为什么索引不能简单地是 π₀ *)

(*
 A coproduct of categories over an index with two distinct inhabited
 summands is never connected -- the index cannot move along a chain. 

 --------
 在具有两个不同非空项的索引上的范畴余积从不连通——索引不能沿着链移动。
*)

Definition SigmaCat_not_connected {I : Type} {Cs : I → Category}
  {i j : I} (Hij : i = j → False) (x : Cs i) (y : Cs j) :
  Connected (SigmaCat Cs) → False :=
  fun K => Hij (sigma_index_zigzag
                  (K ((i; x) : SigmaCat Cs) ((j; y) : SigmaCat Cs))).

(*
 [Theory/Connected/Components.v]'s π₀ COARSENS THE SETOID AND LEAVES THE
 CARRIER ALONE -- [pi0_carrier] there records [carrier (pi0 C) = obj[C]]
 by [eq_refl] -- so a coproduct indexed by it has ONE SUMMAND PER
 OBJECT.  At the walking arrow that gives two summands where there is
 one component, and the result is a category that is not connected
 although [_2] is.  This is why the decomposition record above carries
 a chosen representative as DATA. 

 --------
 [Theory/Connected/Components.v] 的 π₀ 粗化了集合体而保持承载物不变——[pi0_carrier] 在那里记录了 [carrier (pi0 C) = obj[C] ] 由 [eq_refl] ——所以一个以它为索引的余积在每个对象上有一个求和项。在给出一个组件只有一个元素的步进箭头那里会产生两个求和项，结果是一个不连通的范畴，尽管 [_2] 是连通的。这就是为什么上面的分解记录作为数据携带一个选定的代表。
*)

Definition naive_pi0_sum : Category :=
  SigmaCat (fun x : carrier (pi0 _2) => ConnectedComponent _2 x).

Definition naive_pi0_sum_not_connected : Connected naive_pi0_sum → False :=
  SigmaCat_not_connected Two_component_objects_differ
    (Component_obj _2 TwoX) (Component_obj _2 TwoY).

(*
 Consequently no functor out of [_2] hits it up to isomorphism: the
 naive index does not merely name the components badly, it names a
 category that no comparison from [_2] can cover. 

 --------
 因此，没有从 [_2] 出发的函子可以在同构意义上命中它：天真的指标不仅仅是把分量命名得不好，它命名了一个 [_2] 无法覆盖其比较的范畴。
*)

Definition no_ESO_into_naive_pi0_sum (F : _2 ⟶ naive_pi0_sum) :
  EssentiallySurjective F → False :=
  fun E => naive_pi0_sum_not_connected (eso_connected F E Two_Connected).

(* * ** Non-vacuity, part 3: part (a) computing in [Coq] / * ** 非空性，第3部分：第(a)部分 在 [Coq] 中计算 *)

(*
 The constant functor out of the point.  Named [coq_point] rather than
 [One_Const], which Theory/Shapes.v already takes for the DIFFERENT
 functor [C ⟶ [_1, C]]; that module is deliberately not required here,
 its identifications being pinned at [Category@{_ Set Set}]. 

 --------
 从点出的恒等函子。命名为 [coq_point]，而不是 [One_Const]，原因是 Theory/Shapes.v 已经将 [One_Const] 用于不同的函子 [C ⟶ [_1, C]；该模块在这里故意不被引用，其识别被固定在 [Category@{_ Set Set}]。
*)

Definition coq_point (T : Type) : _1 ⟶ Coq :=
  @Build_Functor _1 Coq (fun _ => T) (fun _ _ _ => Datatypes.id)
    (fun _ _ _ _ _ _ => eq_refl) (fun _ _ => eq_refl)
    (fun _ _ _ _ _ _ => eq_refl).

(*
 A diagram over the coproduct of two points, picking out [nat] and
 [bool].  It is built by the DONOR's case functor, so it carries no
 proof obligation of its own. 

 --------
 两个点的余积的示意图，选出 [nat] 和 [bool]。它由 DONOR 的 case 函子构建，因此自身不承担任何证明义务。
*)

Definition CoqPair : SigmaCat (fun _ : bool => _1) ⟶ Coq :=
  SigmaCat_case (fun k : bool => coq_point (if k then nat else bool)).

Definition coqpair_fam (k : bool) : Coq := if k then nat else bool.

Definition coqpair_obj : Coq := (nat * bool)%type.

Definition coqpair_proj (k : bool) : coqpair_obj ~{Coq}~> coqpair_fam k :=
  match k as k0 return coqpair_obj → coqpair_fam k0 with
  | true  => @fst nat bool
  | false => @snd nat bool
  end.

Definition coqpair_IsIndexedProduct :
  IsIndexedProduct coqpair_fam coqpair_obj coqpair_proj.
Proof.
  constructor; intros c pi.
  unshelve eapply Build_Unique.
  - exact (fun x => (pi true x, pi false x)).
  - intros [|] x; reflexivity.
  - intros v Hv x.
    pose proof (Hv true x) as H1; pose proof (Hv false x) as H2.
    simpl in H1, H2.
    destruct (v x); simpl in *; subst; reflexivity.
Defined.

(*
 Each summand's limit is the point's: the diagram restricted to a
 summand is a functor out of [_1], and [point_IsALimit] applies. 

 --------
 每个加数的极限就是该点的极限：限制在某个加数上的图是一个从 [_1] 出发的函子，并且适用 [point_IsALimit]。
*)

Definition coqpair_summand_limit (k : bool) :
  IsALimit (summand CoqPair k) (coqpair_fam k) :=
  point_IsALimit (summand CoqPair k).

Definition CoqPair_IsALimit : IsALimit CoqPair coqpair_obj :=
  coprod_IsALimit CoqPair coqpair_summand_limit coqpair_IsIndexedProduct.

(* The legs COMPUTE to the two projections. / 这些腿计算到两个投影。 *)

Example CoqPair_leg_true (x : nat * bool) :
  limit_leg CoqPair_IsALimit ((true; ttt) : SigmaCat (fun _ : bool => _1)) x
    = fst x := eq_refl.

Example CoqPair_leg_false (x : nat * bool) :
  limit_leg CoqPair_IsALimit ((false; ttt) : SigmaCat (fun _ : bool => _1)) x
    = snd x := eq_refl.

(* ... and so does the mediator, at a cone that is not a projection pair: [n] goes to [(n, n =? 0)]. / ... 调解者也是如此，在一个不是投影对的锥体上： [n] 变为 [(n, n =? 0)] 。 *)

Definition coq_test_leg (X : SigmaCat (fun _ : bool => _1)) :
  nat ~{Coq}~> CoqPair X :=
  match `1 X as k return nat → coqpair_fam k with
  | true  => fun n => n
  | false => fun n => Nat.eqb n 0
  end.

Lemma coq_test_coherence {X Y : SigmaCat (fun _ : bool => _1)} (f : X ~> Y) :
  fmap[CoqPair] f ∘ coq_test_leg X ≈ coq_test_leg Y.
Proof.
  destruct X as [k x], Y as [l y], f as [e m]; simpl in *.
  destruct e; simpl in *.
  destruct k; intro n; reflexivity.
Qed.

Definition coq_test_cone : Cone CoqPair :=
  @Build_Cone (SigmaCat (fun _ : bool => _1)) Coq CoqPair nat
    (@Build_ACone (SigmaCat (fun _ : bool => _1)) Coq nat CoqPair
       coq_test_leg (@coq_test_coherence)).

Example CoqPair_med_computes (n : nat) :
  limit_med CoqPair_IsALimit coq_test_cone n = (n, Nat.eqb n 0) := eq_refl.

(*
 The witness is not degenerate: the two summand limits are different
 objects, and the apex has at least two distinct elements. 

 --------
 见证者不是堕落的：两个求和项的极限是不同的对象，并且顶点至少有两个不同的元素。
*)

Lemma coqpair_fam_differ : coqpair_fam true <> coqpair_fam false.
Proof.
  intro e.
  assert (K : ∀ x y z : coqpair_fam false, x = y \/ y = z \/ x = z)
    by (simpl; intros [|] [|] [|]; auto).
  rewrite <- e in K.
  destruct (K 0%nat 1%nat 2%nat) as [H|[H|H]]; discriminate.
Qed.

Example CoqPair_apex_two_elements : (0%nat, true) <> (0%nat, false).
Proof. discriminate. Qed.

(** ** Measured boundaries, pinned / ** 测量好的边界，固定 *)

(*
 The universe placement of the [iprod] reading, GUARDED rather than
 merely measured.

 RECORDED CORRECTION.  An earlier revision stated this section as two
 NEGATIVES: over a category whose homs are declared strictly above
 [Set] the elementary statements elaborated and the two [iprod] ones
 were refused, and the section concluded that the pin was attributable
 to the donor [iprod].  The attribution was one step short.  [iprod]
 itself was never [Set]-pinned; it inherited the pin from
 [DiscreteCat_Functor], which was declared with bare binders and
 minimized to [DiscreteCat@{u Set Set}], and which [Limit] (unlike
 [Cone]) identifies with the AMBIENT hom-and-proof universe.

 In the PR “algebraic carriers are sets” (2026-09-17)
 [DiscreteCat_Functor] was annotated in place at Instance/Discrete.v,
 and both lines below are now ACCEPTED.  They are kept as positive
 controls at exactly the levels that used to refuse them, so this
 section now guards the repair rather than the pin: were the annotation
 ever dropped, these two would refuse again and this file would stop
 compiling. 

 --------
 [iprod] 读数的宇宙位置，受保护而不是仅仅测量。 记录修正。早期的修订将本节表述为两个否定：在一个其同态被严格声明在 [Set] 之上的类别中，对所阐述的基本陈述以及两个 [iprod] 的陈述被拒绝，本节得出结论该针归因于供体 [iprod]。归因还差一步。[iprod] 本身从未被 [Set] 针对；它继承了来自 [DiscreteCat_Functor] 的针，[DiscreteCat_Functor] 被声明为仅带绑定器并最小化至 [DiscreteCat@{u Set Set}]，而 [Limit]（不同于 [Cone]）与 AMBIENT hom-and-proof 宇宙同一。在 PR “代数载体是集合”（2026-09-17）中，[DiscreteCat_Functor] 已在 Instance/Discrete.v 中原地标注，并且下面的两行现在都被接受。它们被保留为正向控制，正好在以前会拒绝它们的级别上，因此这一部分现在保护的是修复而不是标记：如果标注被删除，这两行将再次被拒绝，并且这个文件将无法编译。
*)

Section UniversePin.

Universe uo uh.
Constraint Set < uh.

Context (Cu : Category@{uo uh uh}).
Context (Js : bool → Category@{uo uh uh}).

(* Controls: the elementary vocabulary is formable at these levels. / 控制：在这些级别上可以形成基础词汇。 *)

Check (fun (A : Type) (f : A → Cu) (p : Cu) (pr : ∀ a : A, p ~{Cu}~> f a) =>
         IsIndexedProduct f p pr).

Check (fun (F : SigmaCat Js ⟶ Cu) (p : Cu) => IsALimit F p).

Check (fun (F : SigmaCat Js ⟶ Cu) (L : bool → Cu)
           (HL : ∀ k : bool, IsALimit (summand F k) (L k))
           (p : Cu) (pr : ∀ k : bool, p ~{Cu}~> L k)
           (HP : IsIndexedProduct L p pr) => coprod_IsALimit F HL HP).

(* The donor's product operator IS formable here. / 这里可以形成供体的产物操作符。 *)

Check (fun (A : Type) (f : A → Cu)
           (P : Limit (DiscreteCat_Functor f)) => iprod f P).

(* ... and so, therefore, is the corollary stated over it. / ……因此，上面所陈述的推论也是如此。 *)

Check (fun (F : SigmaCat Js ⟶ Cu) (L : bool → Cu)
           (HL : ∀ k : bool, IsALimit (summand F k) (L k))
           (P : Limit (DiscreteCat_Functor L)) =>
         coprod_IsALimit_iprod F HL P).

End UniversePin.

(*
 The objects of a coproduct of categories have NO eta rule: [sigT] is
 not a primitive-projection record here, so an object is not
 convertible with the pair of its projections.  That is why
 [coprod_leg] above is written as a [match] with a return annotation
 rather than as a plain composite. 

 --------
 范畴的余积的对象没有η规则：[sigT]在这里不是原始投影记录，因此一个对象不能与其投影的对转换。这就是为什么上面的[coprod_leg]被写为带有返回注解的[match]，而不是作为普通的复合。
*)

Fail Example sigma_obj_eta (I : Type) (Cs : I → Category)
  (X : SigmaCat Cs) : X = ((`1 X; `2 X) : SigmaCat Cs) := eq_refl.

(*
 [sigma_equiv] and [sigma_case_map] PROJECT their morphism argument
 rather than requiring it to be a pair, which is why they need no
 return annotation.  The morphism itself is NO MORE eta-convertible
 than the object: measured, [f = ((`1 f; `2 f))] is rejected with
 `cannot unify “f” and “(`1 (f); `2 (f))”`, the same failure as the
 object negative above.  So this Example is not a contrast with that
 negative; it records the projection behaviour only. 

 --------
 [sigma_equiv] 和 [sigma_case_map] 投射它们的态射参数，而不是要求它是一个对，这就是它们不需要返回注解的原因。态射本身并不比对象更能进行 eta 转换：经过测量，[f = ((`1 f; `2 f))] 被 `cannot unify “f” and “(` 1 (f) 拒绝；`2 (f))”`，和上述对象否定的失败相同。因此，这个示例不是与那个否定的对比；它只记录投射行为。
*)

Example sigma_hom_eta (I : Type) (Cs : I → Category)
  {X Y : SigmaCat Cs} (f : X ~> Y) :
  sigma_equiv f ((`1 f; `2 f) : X ~{SigmaCat Cs}~> Y)
    = sigma_equiv f f := eq_refl.
