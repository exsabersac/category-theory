Require Import Coq.Vectors.Fin.
Require Import Coq.Logic.Eqdep_dec.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Bicartesian.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Biproduct.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.Semiadditive.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Limit.Product.Finite.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(*
 Every lemma below sits in a section whose hypotheses ([inj]/[proj],
 [HQ]/[HP], [dec]) frequently do not appear in the statement, so the file
 opts into the [Default Proof Using "All"] discipline of
 Theory/EckmannHilton.v rather than annotating each proof.  Definitions are
 unaffected: they abstract only the section variables they actually use, so
 e.g. [matrix_row] takes [HP] alone while [matrix_mor] takes both. 

 --------
 下面的每个引理都位于一个其假设（[inj] / [proj], [HQ] / [HP], [dec]）经常在陈述中未出现的部分中，因此该文件选择了Theory/EckmannHilton.v中的[Default Proof Using "All"]规范，而不是为每个证明做注解。定义不受影响：它们只抽象实际使用的节变量，例如[matrix_row]只使用[HP]，而[matrix_mor]则使用两者。
*)
#[local] Set Default Proof Using "All".

(*
   * * Matrices of morphisms between finite coproducts and products 

   --------
   * * 有限余积与积之间的态射矩阵
*)

(*
 nLab:      https://ncatlab.org/nlab/show/biproduct
 nLab:      https://ncatlab.org/nlab/show/matrix+calculus
 Wikipedia: https://en.wikipedia.org/wiki/Biproduct

 Mac Lane, CWM 2nd ed. §III.5 (pp. 73-74), records that a morphism out of
 an m-fold coproduct and into an n-fold product is *exactly* an m x n
 matrix of morphisms: the coproduct UMP splits it into m rows, the product
 UMP splits each row into n entries, and nothing else about it is free.
 With a zero object in play the identity matrix -- identities down the
 diagonal, zero morphisms elsewhere -- names a canonical comparison from
 the coproduct to the product, whose invertibility is what "the finite
 coproduct and the finite product coincide" means.  Riehl, CTiC 2nd ed.
 §3.1, states the same correspondence (Remark 3.1.27 clause (iii)) and uses
 it to define direct sums; her Exercise 3.1.ix is the small consequence
 that in the presence of a zero object the coproduct injections split.

 This file proves the correspondence over the *indexed* (co)product
 vocabulary of Structure/Limit/{Product,Coproduct}.v -- so the row and
 column index types are arbitrary, not merely finite -- and then reads it
 off at the n-ary folds [fin_coprod]/[fin_prod] and at the classes
 [HasFiniteCoproducts]/[HasFiniteProducts] of
 Structure/Limit/Product/Finite.v.

 ** What is proved

 (1) DETERMINATION AND CONSTRUCTION.  For a coproduct (q, inj) of a family
 [g : J -> C] and a product (p, proj) of a family [fam : K -> C],
 [mat_entry inj proj u j k := proj k ∘ u ∘ inj j] is the (j,k) entry of
 [u : q ~> p].  Then [matrix_ext] says two such morphisms agreeing in
 every entry are equal, [matrix_determined] packages that as a
 biconditional (Lib's [↔] is the Type-valued [iffT], so both legs are
 data), [matrix_mor] builds the morphism with prescribed
 entries, [matrix_entry] computes its entries back, and [matrix_ump]
 bundles both halves as the unique existence
 [∃! u, ∀ j k, mat_entry inj proj u j k ≈ e j k].
 [matrix_mor_entry] is the other round trip.  No finiteness, no
 decidability, no zero object, and no [Cartesian]/[Cocartesian]
 instance: the two universal properties are the entire input.

 (2) THE IDENTITY MATRIX.  Over a single family, a decidable index
 equality and a [ZeroObject], [kron] is the Kronecker delta
 (an identity on the diagonal, [zero_mor] off it -- the diagonal case
 is a transport [eq_rect] along the index equality, and the decider is
 what makes the two cases separable), and [can_matrix] is the induced
 comparison from the coproduct to the product.  [can_matrix_diag] and
 [can_matrix_off] read its entries; [can_matrix_unique] and
 [can_matrix_ump] say it is the only morphism with those entries.
 Specialized at the folds this is [fin_can] and at the classes
 [finite_can].  That this generalizes the binary [can_comparison] of
 Structure/Semiadditive.v is not asserted but *proved*:
 [binary_IsIndexedProduct] and [binary_IsIndexedCoproduct] exhibit the
 ordinary binary product and coproduct as indexed ones over
 [fin2fam x y], and [binary_can_is_can_comparison] shows the identity
 matrix there IS [can_comparison x y] -- at [≈]; the [eq_refl] reading
 is refuted and located below.  The four matrix-entry
 lemmas [exl_can_inl], [exr_can_inl], [exl_can_inr], [exr_can_inr]
 (Structure/Semiadditive.v) are exactly the four entries that
 proof consumes.

 (3) RIEHL EXERCISE 3.1.ix.  With a zero object the coproduct injections
 are split monic, hence monic, and this needs *no* [Cartesian]
 structure: [inl_Section] and [inr_Section] exhibit the retractions
 [id ▽ zero_mor] and [zero_mor ▽ id], whose defining equations are
 literally instances of [inl_merge] / [inr_merge]
 (Structure/Cocartesian.v), and [inl_Monic] / [inr_Monic]
 follow through [sections_are_monic] (Theory/Morphisms.v).
 [indexed_inj_Section] and [indexed_inj_Monic] are the n-ary form, the
 retraction being the cotuple of a column of the Kronecker delta --
 note the asymmetry, that the *binary* statement needs no decidable
 index equality (the two summands are distinguished syntactically)
 while the indexed one does, since without a decider [kron] cannot
 even be written.

 ** Prior art for (3), scoped

 The census is a search over the whole tree for the SHAPE "an equation
 whose left side composes something with [inl] and whose right side is
 [id]", plus a search for [Section]/[SplitMono]/[Monic] applied to a
 coproduct injection.  It returns three things, none of them this
 statement.  (i) Structure/Semiadditive.v's [exl_can_inl] is the only
 in-tree DERIVED retraction for a [Cocartesian] [inl]; it additionally
 assumes [Cartesian] and routes through [can_comparison].  (ii)
 Structure/Biproduct.v's [bi_exl_inl] is a FIELD of the [Biproduct]
 record -- assumed data about that record's own [bi_inl], not about
 [inl], and no [Cocartesian] structure is in sight.  (iii)
 Instance/Grp/Pushout.v proves the free-product injections of
 [Grp] split and are monic, but concretely and from a FACTORIZATION
 hypothesis ([am_inj1_Section_of_factor]) rather than from a zero object.
 Adjacent but not subsuming: Structure/Pushout/Split.v's
 [pushout_both_Monic] derives monic injections from split legs of a
 pushout, and a binary coproduct is a pushout over the initial object --
 but that identification is issue #862's and is not in tree, so the
 generic "zero object + binary coproducts ⟹ the injections split" is
 stated here for the first time.

 ** Without a zero object the injections need not be monic

 Structure/Cocartesian.v makes this point in prose, citing the nLab.
 It is RECORDED here and not proved: no in-tree category is exhibited
 whose coproduct injections fail to be monic, and no impossibility is
 claimed either.  What the file does establish is where the hypothesis is
 spent -- the retraction [id ▽ zero_mor] cannot be written without
 [zero_mor], and [zero_mor] cannot be written without a zero object.

 ** Riehl's abelian-category footnote is not pursued, and cannot be

 Riehl remarks that the identity matrix is invertible in any abelian
 category.  As this library is arranged that is not a theorem waiting to
 be proved but a statement with no content: Structure/Abelian.v
 carries [abelian_additive : Additive C] and Structure/Additive.v
 carries [additive_biproducts : HasBiproducts] as DATA, so an in-tree
 abelian category HAS biproducts by hypothesis and there is nothing left
 to derive.  The remark is therefore stated here and left alone.

 ** Strengths measured, strict first

 These are measurements, not expectations.  What HOLDS at [eq_refl]:

 - [mat_entry_unfold]: an entry IS [proj k ∘ u ∘ inj j], by definition.
 - [matrix_row_at_fold]: the j-th row of a matrix built over the product
 fold IS [fin_tuple n fs (gs j) (e j)] -- the fold's own tupling, on
 the nose.  This works because [fin_prod_ump] is [Defined] and
 [IsIndexedProduct] has primitive projections, so [unique_obj] of the
 descent datum reduces.
 - [matrix_mor_at_fold]: correspondingly the whole matrix morphism IS
 [fin_cotuple] of those rows.
 - [finite_matrix_is_fin_matrix] and [finite_can_is_fin_can]: at the
 instances [Cartesian_Terminal_HasFiniteProducts] and
 [Cocartesian_Initial_HasFiniteCoproducts] the class-level
 constructions ARE the fold-level ones.
 - [kron_off_computes]: at two closed, distinct [Fin.t 2] indices the
 Kronecker delta reduces to [zero_mor] over [Fin.eq_dec].
 - [coq_matrix_computes] and [coq_matrix_computes_right]: over [Coq] a
 2x2 matrix of successors sends [inl 3] to [(4, (4, tt))] and
 [inr (inl 7)] to [(8, (8, tt))].  ([Category.Instance.Coq] is
 required directly for these, and adds nothing to the dependency
 closure: Structure/Limit/Product/Finite.v already requires it for
 its own computing examples.)

 What is REFUTED at [eq_refl] (measured during development; pinned in the
 companion probe), each a genuine conversion failure reported as
 "cannot unify":

 - [kron fam Fin.eq_dec Fin.F1 Fin.F1 = id].  The failure is located
 precisely: the branch selection DOES reduce -- [Fin.eq_dec] applied to
 two closed indices exposes [Specif.left]/[Specif.right], which is why
 [kron_off_computes] above succeeds -- but the equality proof it
 returns is not [eq_refl], so the [eq_rect] transport in the diagonal
 branch is stuck.  This is a property of the DECIDER, not of [kron]:
 the sections are parametric in [dec], and a decider returning
 [eq_refl] on the diagonal would collapse it.  No such decider is
 built here.
 - [binary_can x y = can_comparison x y].  The two are proved equal at
 [≈] ([binary_can_is_can_comparison]) and are not convertible: the
 former is a cotuple of tuples produced by two descent data, the
 latter the hand-written [(id △ zero_mor) ▽ (zero_mor △ id)].

 ** Universes, read off the constraint blocks

 [mat_entry] is declared with explicit universe binders and its constraint
 block is [uh <= up] alone: the two index universes are free of the
 category's, and the category's hom and proof universes are kept APART.
 That annotation is load-bearing and the fact was measured, not assumed --
 written unannotated, [mat_entry] elaborates at [Category@{uo uh uh}] with
 an EMPTY constraint block, and a probe at a section declaring
 [Constraint uh < up] then rejects it while accepting bare [~>] and [∘]
 at that same setting, and accepting the SHIPPED, annotated [mat_entry]
 applied at those levels.  (An earlier draft of this sentence described
 that control as a re-derivation of the body under explicit binders; the
 probe applies the shipped constant instead.  The conclusion is the same
 either way, but the method described was not the method shipped.)
 So the identification was minimization, not
 content, and explicit binders lift it; the probes are pinned in the
 companion probe file.

 Everything downstream nevertheless identifies the category's hom and
 proof universes, and that is the DONORS' doing rather than this file's,
 measured on their own constraint blocks: [IsIndexedProduct@{u u0 u1 u2}]
 is stated over [Category@{u1 u2 u2}], [IsIndexedCoproduct] over
 [Category@{u2 u3 u3}], and [ZeroObject@{u u0}] over [Category@{u u0 u0}].
 Read that roster as EXHIBITING donors, not as exhausting them -- an
 earlier draft presented it as a full account and it is not.  At least
 two more identify the same levels: [Cartesian@{u u0}] is itself over
 [Category@{u u0 u0}] and is what identifies them across the binary half
 ([inl_Section], [inl_Monic], [binary_can]), and [fin2_colegs@{u u0}] is
 over [Category@{u u0 u0}] while using NONE of the three named above --
 its donors are Structure/Limit/Product/Finite.v's [fin2_legs] and
 [fin2fam] plus Construction/Opposite.v's [Opposite].  The claim that
 the identification is the DONORS' doing and not this file's survives
 unchanged; only the completeness of the list was wrong.
 No attempt is made to lift any of them.  Within that, the
 constraint blocks are
 BOUNDS and not identifications: [matrix_ext] carries seven [<=] relations
 and no equation, with the row and column index universes [u1], [u2]
 bounded above by the two records' universes and unrelated to each other;
 [kron]'s entire constraint block is [u0 <= eq_rect.u0] and
 [u1 <= eq_rect.u1], i.e. the transport's, and nothing else; and
 [inl_Monic]'s constraint block is EMPTY.

 ** Axioms

 62/62 constants report "Closed under the global context".  The count is
 the file's [def] plus [prf] glob entries, and it is exact rather than a
 floor: the file contains no [Program], no [Record]/[Class]/[Inductive]
 and no [Instance], so there are no obligation constants, constructors or
 instance names for a glob sweep to miss -- 24 [Definition] + 19
 [Theorem] + 10 [Lemma] + 8 [Example] + 1 [Corollary] = 62 independently.
 [UIP_dec] (Hedberg) is the only nontrivial stdlib import and is
 axiom-free.

 ** Relation to #320, which hosts the other two clauses

 Structure/Limit/Indexed/Hom.v delivers Riehl 3.1.27 clauses (i) and
 (ii) over the SAME arbitrary-index API, as NATURAL ISOMORPHISMS
 ([iprod_hom_iso], [icoprod_hom_iso]); its header points forward
 twice, saying clause (iii) "is issue #336 and is NOT here".  This
 file supplies clause (iii), so the back pointer belongs here and an
 earlier draft omitted it entirely.  Two honest notes rather than one
 convenient one.  First, clause (iii) is NOT derived from (i) and (ii)
 here; whether it follows by composing them is not investigated.
 Second, it lands one strength LOWER than its siblings: they are
 isomorphisms in a functor category, whereas this is [∃!] plus mutually
 inverse maps at [≈], with no [≅[Sets]] object anywhere.  #336's own
 body says an implementer "should read #320 before starting the
 arbitrary-index box"; that was done, and the two are related by
 citation only.

 ** Citations corrected against the issue

 Five of #336's own citations are stale and are silently corrected
 above; recording that so the correction is visible.  The issue
 points at the wrong place for [can_comparison] and [exl_can_inl] in
 Structure/Semiadditive.v, for [bi_exl_inl] in
 Structure/Biproduct.v, for [sections_are_monic] in
 Theory/Morphisms.v and for [additive_biproducts] in
 Structure/Additive.v.  Each was checked by reading the
 declaration.

 ** NOT delivered

 The general matrix composition formula -- that composing two matrices
 multiplies them, entry (j,l) of [v ∘ u] being the sum over k of
 (entry (k,l) of v) ∘ (entry (j,k) of u) -- is NOT proved here.  It is
 OWNED by issue #536, whose QA correction on #336 says to "cite it
 rather than re-proving", so it is cross-referenced and nothing below
 depends on it.

 THE SECOND DEFERRAL IS NOT THE SAME KIND, and an earlier draft of this
 header wrongly said "both are owned by issue #536".  #336's remaining
 Riehl box asks that the identity-matrix comparison BE AN ISOMORPHISM
 for finite index, with the direct sum [⊕] as the common value.  Only
 the OBJECT is #536's -- its QA correction says the object "is #536's
 first Work item; consume it" -- while the box's own text says "the
 n-ary case is genuine new work".  So that box is #336's OWN work,
 BLOCKED on #536's [⊕], and DEFERRED here; it is not owned elsewhere.
 #336 states that it "cannot close while [these boxes] are unproved",
 so this commit ADVANCES #336 rather than closing it: the other box of
 that pair, the arbitrary-index matrix determination, IS delivered
 above, and both of its halves are.  Also absent: no invertibility criterion
 for [can_matrix] and so no n-ary semiadditivity (the binary version is
 Structure/Semiadditive.v's [E] hypothesis); no functoriality of
 [matrix_mor] in the two families; no naturality; no transpose or duality
 statement relating the J-indexed and K-indexed sides; no concrete
 category with a zero object is instantiated IN THIS FILE, so
 [can_matrix], [fin_can], [finite_can] and the Exercise 3.1.ix results
 are conditionals here (the [Coq] examples witness only (1), [Coq]
 having no zero object -- its initial object is [False] and its terminal
 [unit], asserted rather than proved, though the tree proves the
 analogue twice at Instance/Top.v and for [Rng]).  READ THAT AS A
 CHOICE, NOT AN UNAVAILABILITY: an earlier draft of this paragraph
 explained the gap by the witness category alone, which misleads.  The
 tree carries SIX registered [ZeroObject] instances -- [Grp_Zero]
 (Instance/Grp.v), [Ab_Zero] (Instance/Ab.v), [CMon_Zero]
 (Instance/CMon/Biproduct.v), [RMod_Zero] (Instance/Mod.v),
 [Rel_Zero] (Instance/Rel/Dagger.v), [PointedSets_Zero]
 (Instance/Sets/Pointed.v) -- and [Ab] supplies BOTH hypotheses as
 exported instances, [Ab_Cocartesian] being Instance/Ab/Coproduct.v.
 The Exercise 3.1.ix witness is therefore two lines of pure
 instantiation, and it IS shipped, in Test/ProbeMatrix336.v.  It is kept
 out of THIS file for a measured reason: [Instance/Ab] is not in this
 file's dependency closure (0 of 19 modules), while
 Instance/Ab/Coproduct.v's own closure is 17, so importing it here would
 nearly double a [Structure/] file's footprint for two [Example]s.  What
 remains genuinely unwitnessed is the [can_matrix] family, which needs a
 zero object AND a decidable index AND both indexed structures; and
 nothing is said about when the comparison is an isomorphism in any
 particular category. 

 --------
 nLab：       https://ncatlab.org/nlab/show/biproduct
 nLab：       https://ncatlab.org/nlab/show/matrix+calculus
 维基百科：  https://en.wikipedia.org/wiki/BiproductMac Lane，《CWM》第2版 §III.5（第73-74页）记录到，从一个m重余积到一个n重积的态射*恰好*是一个m × n的态射矩阵：余积的UMP将其拆分成m行，积的UMP将每行拆分成n个条目，而且除此之外没有其他自由度。在存在零对象的情况下，单位矩阵——对角线上是恒等态射，其他位置为零态射——表示从余积到积的一个规范比较，其可逆性就是“有限余积与有限积重合”的含义。Riehl，《CTiC》第2版 §3.1，也说明了同样的对应关系（备注3.1.27 条款(iii)），并用它来定义直和；她的习题3.1.ix是一个小结论，即在存在零对象的情况下，余积的注入态射会拆分。此文件证明了 Structure/Limit/{Product,Coproduct}.v 中 *有索引* 的（协）积词汇的一致性——因此行和列的索引类型是任意的，而不仅仅是有限的——然后在 n 元折叠 [fin_coprod] / [fin_prod] 以及 Structure/Limit/Product/Finite.v 中的类 [HasFiniteCoproducts] / [HasFiniteProducts] 上读取它。

 ** 证明了什么(1) 决定性与构造。对于一族的余积 (q, inj) 以及一族的积 (p, proj)，[mat_entry inj proj u j k := proj k ∘ u ∘ inj j] 是 [u : q ~> p] 的 (j,k) 项。然后 [matrix_ext] 表明两个在每个项上都相同的态射是相等的，[matrix_determined] 将其打包为一个双条件（在 Lib 中，[↔] 是类型值的 [iffT]，因此两条支线都是数据），[matrix_mor] 构造具有指定项的态射，[matrix_entry] 重新计算其项，而 [matrix_ump] 将两部分绑定为唯一存在的 [∃! u, ∀ j k, mat_entry inj proj u j k ≈ e j k]。[matrix_mor_entry] 是另一个往返。没有有限性，没有可判定性，没有零对象，也没有 [Cartesian] / [Cocartesian] 实例：这两个泛性质就是整个输入。(2) 单位矩阵。对于单一族，可判定的索引相等和 [ZeroObject]、[kron] 是克罗内克δ（对角线上是恒等，[zero_mor] 在对角线之外——对角线情况是沿索引相等的传输[eq_rect]，判定器是使这两种情况可分的东西），并且 [can_matrix] 是从余积到积的诱导比较。[can_matrix_diag] 和 [can_matrix_off] 读取其条目；[can_matrix_unique] 和 [can_matrix_ump] 表示它是具有这些条目的唯一态射。在折叠处的特化是 [fin_can]，在类处是 [finite_can]。这一点将 Structure/Semiadditive.v 中的二元 [can_comparison] 泛化，并非只是断言，而是*证明*的：[binary_IsIndexedProduct] 和 [binary_IsIndexedCoproduct] 展示了作为 [fin2fam x y] 上的索引对象的普通二元积和余积，而 [binary_can_is_can_comparison] 显示了其处的恒等矩阵确实是 [can_comparison x y] ——在 [≈] 处；[eq_refl] 的读法已被驳斥，并列在下方。四个矩阵元素引理 [exl_can_inl]、[exr_can_inl]、[exl_can_inr]、[exr_can_inr]（Structure/Semiadditive.v）正是证明中使用的四个元素。(3) RIEHL 练习 3.1.ix. 对于零对象，余积注入是分裂单射，因此是单射，这*不需要* [Cartesian] 结构：[inl_Section] 和 [inr_Section] 展示了重tractions [id ▽ zero_mor] 和 [zero_mor ▽ id]，其定义方程实际上是 [inl_merge] / [inr_merge] (Structure/Cocartesian.v) 的实例，而 [inl_Monic] / [inr_Monic] 通过 [sections_are_monic] (Theory/Morphisms.v) 得出。[indexed_inj_Section] 和 [indexed_inj_Monic] 是 n 元形式，重traction 是克罗内克增量列的余元组——注意不对称性，*二元*陈述不需要可判定的索引相等（两个和式在语法上是区分的），而索引形式则需要，因为没有判定器 [kron] 甚至无法书写。** （3）的现有技术，已限定范围人口普查是对整棵树进行搜索，以查找形状为“一个方程，其左边由 [inl] 组成，右边为 [id]”，同时还要搜索应用于余积注入的 [Section] / [SplitMono] / [Monic]。它返回三个结果，这些结果都不是该语句。(i) Structure/Semiadditive.v 的 [exl_can_inl] 是对 [Cocartesian]  [inl] 在树内的唯一派生收缩；它还假设了 [Cartesian] 并经由 [can_comparison] 路由。(ii) Structure/Biproduct.v 的 [bi_exl_inl] 是 [Biproduct] 记录的一个字段——假设的是该记录自身 [bi_inl] 的数据，而不是 [inl]，并且没有看到任何 [Cocartesian] 结构。(iii)
 Instance/Grp/Pushout.v 证明了自由积的注入 [Grp] 可分裂且为单射，但这是具体证明，并且基于一个分解假设（[am_inj1_Section_of_factor]），而不是基于零对象。紧邻但不包含其中：Structure/Pushout/Split.v 的 [pushout_both_Monic] 从推出的分裂支派生出单射注入，而二元余积是初始对象上的推出——但这种识别是第 #862 号问题的内容，并未在树中，因此这里首次提出通用的“零对象 + 二元余积 ⟹ 注入可分裂”。

 ** 没有零对象时，注入不一定是单射Structure/Cocartesian.v 用散文阐述了这一点，并引用了 nLab。它在此被记录而未被证明：没有展示任何树内范畴的例子，其余积注入不是单射，也没有声称这不可能。该文件所确立的是假设的使用位置——重traction [id ▽ zero_mor] 无法在没有 [zero_mor] 的情况下写出，而 [zero_mor] 无法在没有零对象的情况下写出。

 ** Riehl 关于阿贝尔范畴的脚注未被展开，也无法展开Riehl 备注说，在任何阿贝尔范畴中，单位矩阵都是可逆的。由于这个库的安排，这不是一个待证明的定理，而是一个没有内容的陈述：Structure/Abelian.v 包含 [abelian_additive : Additive C]，Structure/Additive.v 包含 [additive_biproducts : HasBiproducts] 作为数据，因此一个树状的阿贝尔范畴根据假设具有二积（biproducts），没有什么需要推导的。因此，这个备注在此陈述后就不再讨论。

 ** 优势测量，严格优先

 这些是测量值，不是期望值。在 [eq_refl] 上成立的是：- [mat_entry_unfold]：根据定义，一个条目就是 [proj k ∘ u ∘ inj j]。- [matrix_row_at_fold]：在乘积上构建的矩阵的第 j 行就是 [fin_tuple n fs (gs j) (e j)] —— 就是该 fold 自身的配对，精确无误。这有效是因为 [fin_prod_ump] 是 [Defined]，并且 [IsIndexedProduct] 有原始投影，所以 [unique_obj] 的下降数据会简化。- [matrix_mor_at_fold]：相应地，整个矩阵态射就是这些行的 [fin_cotuple]。- [finite_matrix_is_fin_matrix] 和 [finite_can_is_fin_can]：在实例 [Cartesian_Terminal_HasFiniteProducts] 和 [Cocartesian_Initial_HasFiniteCoproducts] 处，类级构造就是 fold 级构造。- [kron_off_computes]：在两个闭合的、不同的 [Fin.t 2] 指数处，克罗内克 delta 会简化为 [zero_mor] 在 [Fin.eq_dec] 上。- [coq_matrix_computes] 和 [coq_matrix_computes_right]：在 [Coq] 上，一个 2x2 的后继矩阵会将 [inl 3] 送到 [(4, (4, tt))]，并且将 [inr (inl 7)] 送到 [(8, (8, tt))]。([Category.Instance.Coq] 直接是这些所必需的，并且对依赖闭包没有任何补充：Structure/Limit/Product/Finite.v 已经为其自身的计算示例而需要它。)

 在 [eq_refl] 处被驳回（开发过程中测量；固定在伴随探针中），每一个都是以“无法统一”报告的真实转换失败：- [kron fam Fin.eq_dec Fin.F1 Fin.F1 = id]。故障定位在：分支选择确实会减少——[Fin.eq_dec] 应用于两个闭合索引会暴露 [Specif.left] / [Specif.right]，这就是为什么上面的 [kron_off_computes] 成功——但它返回的等式证明不是 [eq_refl]，因此对角分支中的 [eq_rect] 传输被卡住。这是 DECIDER 的特性，而不是 [kron] 的特性：这些截面在 [dec] 上是参数化的，并且在对角线上返回 [eq_refl] 的决策器会导致它崩溃。这里没有构建这样的决策器。
 - [binary_can x y = can_comparison x y]。这两者在 [≈]（[binary_can_is_can_comparison]）处被证明相等，但不可互换：前者是由两个下降数据产生的元组的余元组，后者是手写的 [(id △ zero_mor) ▽ (zero_mor △ id)]。** 宇宙，读取约束块[mat_entry] 被声明为带有显式宇宙绑定器，其约束块仅为 [uh <= up]：两个索引宇宙不受类别的约束，并且类别的 hom 和 proof 宇宙保持分开。该注释是关键性的，并且该事实是经过测量的，而不是假定的——未加注释地写作时，[mat_entry] 会在 [Category@{uo uh uh}] 展开且约束块为空，并且在声明 [Constraint uh < up] 的部分进行探测时会拒绝它，同时接受在相同设置下的裸 [~>] 和 [∘]，并接受在这些层次应用的已发布带注释的 [mat_entry]。（本句的早期草稿将这种控制描述为在显式绑定器下对主体的重新推导；探测则应用已发布的常量。）结论无论哪种方式都是相同的，但描述的方法并不是实际交付的方法。 因此，识别的是最小化，而不是内容，并且显式绑定器会提升它；探针被固定在伴随的探针文件中。尽管如此，下游的所有内容仍然识别该类别的 hom 和证明宇宙，这是由捐赠者的行为决定的，而不是由此文件决定的，根据它们自己的约束块测量：[IsIndexedProduct@{u u0 u1 u2}] 定义在 [Category@{u1 u2 u2}] 上，[IsIndexedCoproduct] 定义在 [Category@{u2 u3 u3}] 上，[ZeroObject@{u u0}] 定义在 [Category@{u u0 u0}] 上。把该清单读作展示捐赠者，而不是穷尽它们——早期的草稿将其呈现为完整的说明，但并非如此。至少还有两个识别相同层级：[Cartesian@{u u0}] 本身定义在 [Category@{u u0 u0}] 上，并且它是通过二进制半部分（[inl_Section]、[inl_Monic]、[binary_can]）识别它们的；而 [fin2_colegs@{u u0}] 定义在 [Category@{u u0 u0}] 上，同时不使用上述三个已命名的——它的捐赠者是 Structure/Limit/Product/Finite.v 的 [fin2_legs] 和 [fin2fam] 以及 Construction/Opposite.v 的 [Opposite]。关于识别是捐赠者所为而不是这个文件的说法仍然保持不变；只有列表的完整性是错误的。没有试图去提升其中的任何一项。在此范围内，约束块是界限而不是识别：[matrix_ext] 包含七个 [<=] 关系而没有方程，其行和列索引集合 [u1]、[u2] 受两个记录集合的上界限制且彼此无关；[kron] 的整个约束块是 [u0 <= eq_rect.u0] 和 [u1 <= eq_rect.u1]，即运输的，并且没有其他；而 [inl_Monic] 的约束块是空的。

 ** 公理62/62 个常量报告“在全局上下文下关闭”。计数是文件的 [def] 加上 [prf] 全局条目，并且这是精确的而不是下限：文件中没有 [Program]，没有 [Record] / [Class] / [Inductive]，也没有 [Instance]，因此全局扫描不会遗漏任何义务常量、构造函数或实例名称——24 个 [Definition] + 19 个 [Theorem] + 10 个 [Lemma] + 8 个 [Example] + 1 个 [Corollary] = 62 个独立项。[UIP_dec]（Hedberg）是唯一的非平凡标准库导入，并且不含公理。

 ** 与 #320 的关系，该编号包含另外两个条款Structure/Limit/Indexed/Hom.v 根据相同的任意索引 API 提供了 Riehl 3.1.27 条款 (i) 和 (ii) 作为自然同构 ([iprod_hom_iso], [icoprod_hom_iso])；其头部向前指向两次，说明条款 (iii) “是问题 #336 并且不在这里”。该文件提供了条款 (iii)，所以回指应在这里，而早期的草稿完全省略了它。有两条诚实的注释，而不是一条方便的注释。首先，条款 (iii) 在这里并非由 (i) 和 (ii) 推导得出；是否可以通过组合它们得到也未被探讨。其次，它的强度比其同类低一档：它们是在函子范畴中的同构，而这个是 [∃!] 加上在 [≈] 上互为逆映射的映射，在任何地方都没有 [≅[Sets] 对象。#336 本身的正文指出，实施者“在开始任意索引盒之前应阅读 #320”；这一点已经完成，并且两者仅通过引用相互关联。

 ** 引用已根据问题修正

 #336 自身的五个引用已经过时，并在上文中静默修正；记录此信息以便修正可见。该问题在 Structure/Semiadditive.v 中指向 [can_comparison] 和 [exl_can_inl] 的位置错误，在 Structure/Biproduct.v 中指向 [bi_exl_inl] 的位置错误，在 Theory/Morphisms.v 中指向 [sections_are_monic] 的位置错误，在 Structure/Additive.v 中指向 [additive_biproducts] 的位置错误。每一个都通过阅读声明进行了检查。

 ** 未交付通用矩阵组合公式——将两个矩阵组合就是将它们相乘，[v ∘ u] 的 (j,l) 项是对 k 求和得到的 (v 的 (k,l) 项) ∘ (u 的 (j,k) 项) ——在这里没有证明。它属于问题 #536，其在 #336 的 QA 修正中说“引用它而不是重新证明”，因此这里做了交叉引用，下面的内容不依赖它。第二次延迟不是同一种类型，并且该标题的早期草稿错误地写成“两者都属于问题#536”。#336剩余的Riehl框要求对有限指数的恒等矩阵比较是一个同构，其公共值为直和[⊕]。只有对象是#536的——其QA修正表示对象“是#536的第一个工作项；使用它”——而框本身的文本则说“n元情况是全新的工作”。所以该框是#336自己的工作，受阻于#536的[⊕]，并被在这里延迟；它不属于其他地方。#336指出其“在[these boxes]未证实时无法关闭”，因此这次提交推进了#336而不是关闭它：该对中的另一个框——任意指数矩阵确定——已在上面交付，并且其两部分都已交付。同样缺失：没有 [can_matrix] 的可逆性判据，因此也没有 n 元半加法性（二元版本是在 Structure/Semiadditive.v 的 [E] 假设中）；ZW184WZZ 在两个族中的函子性质缺失；没有自然性；没有关于 J 指数和 K 指数两边的转置或对偶性陈述；在此文件中没有实例化带零对象的具体范畴，因此 [can_matrix]、[fin_can]、[finite_can] 和练习 3.1.ix 的结果在此处均为条件性的（[Coq] 的示例仅验证了 (1)，[Coq] 没有零对象——其初始对象为 [False]，终对象为 [unit]，这些是陈述而非证明，虽然树结构在 Instance/Top.v 中以及 [Rng] 的情况两次证明了类似结论）。把它看作一种选择，而不是不可用：这段话的早期草稿仅通过见证类别来解释差距，这是误导的。该树包含六个已注册的 [ZeroObject] 实例——[Grp_Zero]（Instance/Grp.v）、[Ab_Zero]（Instance/Ab.v）、[CMon_Zero]（Instance/CMon/Biproduct.v）、[RMod_Zero]（Instance/Mod.v）、[Rel_Zero]（Instance/Rel/Dagger.v）、[PointedSets_Zero]（Instance/Sets/Pointed.v）——而 [Ab] 提供了两个假设作为导出实例，[Ab_Cocartesian] 是 Instance/Ab/Coproduct.v。因此，练习 3.1.ix 的见证只是两行纯实例化，并且确实包含在 Test/ProbeMatrix336.v 中。它被保留在这个文件之外是有经过权衡的原因的：[Instance/Ab] 不在这个文件的依赖闭包中（19 个模块中的 0 个），而 Instance/Ab/Coproduct.v 自己的闭包是 17，所以在这里导入它会使一个 [Structure/] 文件的占用几乎翻倍，仅为了两个 [Example]。真正未被考虑的是 [can_matrix] 系列，它需要一个零对象、一个可判定的索引以及两种索引结构；并且没有说明在任何特定范畴中比较何时是同构。
*)

(** ** Entries *)

(*
 The (j,k) entry of a morphism out of a coproduct and into a product:
 restrict along the j-th injection, then project onto the k-th factor.
 Explicit universe binders keep the category's hom and proof universes
 apart; see the header. 

 --------
 从余积到积的态射的 (j,k) 元素：沿第 j 个注入进行限制，然后投影到第 k 个因子。显式的宇宙绑定器将类别的同态和证明宇宙区分开；参见标题。
*)
Definition mat_entry@{uo uh up uj uk} {C : Category@{uo uh up}}
  {J : Type@{uj}} {K : Type@{uk}} {g : J → C} {fam : K → C} {q p : C}
  (inj : ∀ j : J, g j ~> q) (proj : ∀ k : K, p ~> fam k)
  (u : q ~> p) (j : J) (k : K) : g j ~> fam k :=
  proj k ∘ u ∘ inj j.

Example mat_entry_unfold {C : Category} {J K : Type} {g : J → C}
  {fam : K → C} {q p : C} (inj : ∀ j : J, g j ~> q)
  (proj : ∀ k : K, p ~> fam k) (u : q ~> p) (j : J) (k : K) :
  mat_entry inj proj u j k = proj k ∘ u ∘ inj j := eq_refl.

(* * ** The m x n determination (Mac Lane §III.5) / * ** m x n 定义（Mac Lane §III.5） *)

Section Matrix.

Context {C : Category}.
Context {J K : Type}.
Context {g : J → C}.
Context {fam : K → C}.
Context {q : C}.
Context {inj : ∀ j : J, g j ~> q}.
Context {p : C}.
Context {proj : ∀ k : K, p ~> fam k}.
Context (HQ : IsIndexedCoproduct g q inj).
Context (HP : IsIndexedProduct fam p proj).

(*
 Two morphisms into the product agree when all their projections do: both
 factor the same family through the universal one. 

 --------
 当所有它们的投影都相同时，两个射影到积的态射是相同的：它们都将同一族通过通用的态射进行分解。
*)
Lemma iprod_ext {c : C} (a b : c ~> p) :
  (∀ k : K, proj k ∘ a ≈ proj k ∘ b) → a ≈ b.
Proof.
  intro H.
  pose proof (iprod_desc HP (fun k => proj k ∘ a)) as D.
  transitivity (unique_obj D).
  - symmetry.
    apply (uniqueness D).
    intro k; reflexivity.
  - apply (uniqueness D).
    intro k; symmetry; apply H.
Qed.

(* Dually for morphisms out of the coproduct. / 对于从余积出的态射的对偶情况。 *)
Lemma icoprod_ext {c : C} (a b : q ~> c) :
  (∀ j : J, a ∘ inj j ≈ b ∘ inj j) → a ≈ b.
Proof.
  intro H.
  pose proof (icoprod_desc HQ (fun j => a ∘ inj j)) as D.
  transitivity (unique_obj D).
  - symmetry.
    apply (uniqueness D).
    intro j; reflexivity.
  - apply (uniqueness D).
    intro j; symmetry; apply H.
Qed.

(*
 Mac Lane's determination: a morphism from the coproduct to the product is
 fixed by its m x n matrix of entries.  Restricting along the injections
 uses the coproduct UMP, projecting onto the factors the product UMP; the
 only other step is reassociation. 

 --------
 Mac Lane 的确定性：从余积到积的一个态射由其 m x n 的条目矩阵固定。在沿着注入的限制使用余积的 UMP，将积投影到各个因子使用积的 UMP；唯一的其他步骤是重新结合。
*)
Theorem matrix_ext (u v : q ~> p) :
  (∀ (j : J) (k : K),
     mat_entry inj proj u j k ≈ mat_entry inj proj v j k) → u ≈ v.
Proof.
  intro H.
  apply icoprod_ext; intro j.
  apply iprod_ext; intro k.
  rewrite !comp_assoc.
  exact (H j k).
Qed.

Corollary matrix_determined (u v : q ~> p) :
  u ≈ v ↔ (∀ (j : J) (k : K),
             mat_entry inj proj u j k ≈ mat_entry inj proj v j k).
Proof.
  split.
  - intros Huv j k.
    unfold mat_entry.
    now rewrite Huv.
  - apply matrix_ext.
Qed.

(*
 The j-th row of a prescribed matrix: the tuple of its entries. 

 --------
 规定矩阵的第j行：其元素的元组。
*)
Definition matrix_row (e : ∀ (j : J) (k : K), g j ~> fam k) (j : J) :
  g j ~> p := unique_obj (iprod_desc HP (e j)).

Lemma matrix_row_commutes (e : ∀ (j : J) (k : K), g j ~> fam k)
  (j : J) (k : K) : proj k ∘ matrix_row e j ≈ e j k.
Proof. exact (unique_property (iprod_desc HP (e j)) k). Qed.

(*
 The morphism with prescribed entries: the cotuple of the rows. 

 --------
 具有规定条目的态射：行的余元组。
*)
Definition matrix_mor (e : ∀ (j : J) (k : K), g j ~> fam k) : q ~> p :=
  unique_obj (icoprod_desc HQ (matrix_row e)).

Lemma matrix_mor_inj (e : ∀ (j : J) (k : K), g j ~> fam k) (j : J) :
  matrix_mor e ∘ inj j ≈ matrix_row e j.
Proof. exact (unique_property (icoprod_desc HQ (matrix_row e)) j). Qed.

Theorem matrix_entry (e : ∀ (j : J) (k : K), g j ~> fam k)
  (j : J) (k : K) : mat_entry inj proj (matrix_mor e) j k ≈ e j k.
Proof.
  unfold mat_entry.
  rewrite <- comp_assoc.
  rewrite matrix_mor_inj.
  apply matrix_row_commutes.
Qed.

(* The correspondence in one statement: matrices are morphisms. / 在一句话中的对应关系：矩阵是态射。 *)
Theorem matrix_ump (e : ∀ (j : J) (k : K), g j ~> fam k) :
  ∃! u : q ~> p, ∀ (j : J) (k : K), mat_entry inj proj u j k ≈ e j k.
Proof.
  unshelve eapply Build_Unique.
  - exact (matrix_mor e).
  - exact (matrix_entry e).
  - intros v Hv.
    apply matrix_ext; intros j k.
    rewrite matrix_entry.
    symmetry; apply Hv.
Defined.

(*
 The other round trip: reading a morphism's entries and rebuilding it
 returns it (up to ≈; see the header for what is refuted strictly). 

 --------
 另一次往返：读取态射的条目并重建它
 返回它（到≈为止；参见标题了解哪些被严格反驳）。
*)
Theorem matrix_mor_entry (u : q ~> p) :
  matrix_mor (mat_entry inj proj u) ≈ u.
Proof. apply matrix_ext; intros j k; apply matrix_entry. Qed.

End Matrix.

(** ** The Kronecker delta / ** 克罗内克 δ *)

Section KroneckerDelta.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context {A : Type}.
Context (fam : A → C).
Context (dec : ∀ a b : A, {a = b} + {a <> b}).

(*
 An identity on the diagonal, a zero morphism off it.  The diagonal branch
 must transport the identity along the index equality, which is why a
 decider is needed to write this down at all: [Specif.left] carries the
 proof [e : j = k] that [eq_rect] consumes. 

 --------
 对角线上是恒等映射，对角线外是零态射。对角分支必须沿着索引相等传递恒等映射，这就是为什么需要决定器来写下它：[Specif.left] 携带了证明 [e : j = k]，而 [eq_rect] 则使用了该证明。
*)
Definition kron (j k : A) : fam j ~> fam k :=
  match dec j k with
  | Specif.left e  => eq_rect j (fun k' : A => fam j ~> fam k') id k e
  | Specif.right _ => zero_mor
  end.

(*
 Uniqueness of identity proofs on a type with decidable equality is
 Hedberg's theorem, [UIP_dec], which is axiom-free. 

 --------
 在具有可判定等式的类型上，身份证明的唯一性是 Hedberg 定理，[UIP_dec]，它是无公理的。
*)
Lemma kron_diag (j : A) : kron j j ≈ id.
Proof.
  unfold kron.
  destruct (dec j j) as [e|ne].
  - now rewrite (UIP_dec dec e eq_refl).
  - now contradiction ne.
Qed.

Lemma kron_off (j k : A) : j <> k → kron j k ≈ zero_mor.
Proof.
  intro Hne.
  unfold kron.
  destruct (dec j k) as [e|ne].
  - contradiction.
  - reflexivity.
Qed.

End KroneckerDelta.

(*
 Off the diagonal the delta COMPUTES over [Fin.eq_dec] at closed indices:
 the decider exposes [Specif.right], and that branch carries no transport.
 The diagonal case does not; see the header. 

 --------
 在对角线之外，Δ 在闭合指标上计算 [Fin.eq_dec]：
 决策器显示 [Specif.right]，并且该分支没有传输。
 对角线情况没有；见标题。
*)
Example kron_off_computes {C : Category} `{Z : @ZeroObject C}
  (fam : Fin.t 2 → C) :
  kron fam Fin.eq_dec Fin.F1 (Fin.FS Fin.F1) = zero_mor := eq_refl.

(* * ** The identity matrix as the canonical comparison / * ** 身份矩阵作为标准比较 *)

Section IdentityMatrix.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context {A : Type}.
Context (fam : A → C).
Context (dec : ∀ a b : A, {a = b} + {a <> b}).
Context {q : C}.
Context {inj : ∀ a : A, fam a ~> q}.
Context {p : C}.
Context {proj : ∀ a : A, p ~> fam a}.
Context (HQ : IsIndexedCoproduct fam q inj).
Context (HP : IsIndexedProduct fam p proj).

Definition can_matrix : q ~> p := matrix_mor HQ HP (kron fam dec).

Theorem can_matrix_diag (j : A) : mat_entry inj proj can_matrix j j ≈ id.
Proof.
  unfold can_matrix.
  rewrite matrix_entry.
  apply kron_diag.
Qed.

Theorem can_matrix_off (j k : A) :
  j <> k → mat_entry inj proj can_matrix j k ≈ zero_mor.
Proof.
  intro Hne.
  unfold can_matrix.
  rewrite matrix_entry.
  now apply kron_off.
Qed.

(*
 The identity matrix determines the comparison: any morphism with those
 entries is it. 

 --------
 单位矩阵决定了比较：任何具有那些条目的态射都是它。
*)
Theorem can_matrix_unique (u : q ~> p) :
  (∀ j : A, mat_entry inj proj u j j ≈ id) →
  (∀ j k : A, j <> k → mat_entry inj proj u j k ≈ zero_mor) →
  u ≈ can_matrix.
Proof.
  intros Hd Ho.
  apply (matrix_ext HQ HP); intros j k.
  destruct (dec j k) as [e|ne].
  - destruct e.
    rewrite can_matrix_diag.
    apply Hd.
  - rewrite (can_matrix_off _ _ ne).
    now apply Ho.
Qed.

Theorem can_matrix_ump :
  ∃! u : q ~> p,
    (∀ j : A, mat_entry inj proj u j j ≈ id) *
    (∀ j k : A, j <> k → mat_entry inj proj u j k ≈ zero_mor).
Proof.
  unshelve eapply Build_Unique.
  - exact can_matrix.
  - exact (can_matrix_diag, can_matrix_off).
  - intros v [Hd Ho].
    symmetry.
    now apply can_matrix_unique.
Defined.

End IdentityMatrix.

(* * ** Riehl Exercise 3.1.ix, indexed form / * ** Riehl 练习 3.1.ix，索引形式 *)

Section IndexedInjections.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context {A : Type}.
Context (fam : A → C).
Context (dec : ∀ a b : A, {a = b} + {a <> b}).
Context {q : C}.
Context {inj : ∀ a : A, fam a ~> q}.
Context (HQ : IsIndexedCoproduct fam q inj).

(*
 The retraction of the j-th injection is the cotuple of the j-th COLUMN of
 the Kronecker delta.  Note that only the coproduct is used: no product,
 no [Cartesian], no [Terminal]. 

 --------
 第 j 次注射的收缩是 Kronecker δ 第 j 列的余元积。注意这里只使用余积：没有积，没有 [Cartesian]，也没有 [Terminal]。
*)
Definition inj_retract (j : A) : q ~> fam j :=
  unique_obj (icoprod_desc HQ (fun k => kron fam dec k j)).

Lemma inj_retract_commutes (j k : A) :
  inj_retract j ∘ inj k ≈ kron fam dec k j.
Proof.
  exact (unique_property
           (icoprod_desc HQ (fun k => kron fam dec k j)) k).
Qed.

Lemma inj_retract_id (j : A) : inj_retract j ∘ inj j ≈ id.
Proof.
  rewrite inj_retract_commutes.
  apply kron_diag.
Qed.

Definition indexed_inj_Section (j : A) : Section (inj j) :=
  {| section := inj_retract j; section_comp := inj_retract_id j |}.

Definition indexed_inj_SplitMono (j : A) : SplitMono (inj j) :=
  indexed_inj_Section j.

Definition indexed_inj_Monic (j : A) : Monic (inj j) :=
  sections_are_monic _ _ _ (indexed_inj_Section j).

End IndexedInjections.

(* * ** Riehl Exercise 3.1.ix, binary form / * ** Riehl 练习 3.1.ix，二进制形式 *)

Section CoproductInjections.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context `{CC : @Cocartesian C}.
Context (x y : C).

(*
 Minimal hypotheses: a zero object and binary coproducts.  There is no
 [Cartesian] instance in this section, and the defining equations are
 nothing but [inl_merge] and [inr_merge] read at [id] and [zero_mor].
 Unlike the indexed form above this needs no decidable index equality,
 the two summands being distinguished syntactically. 

 --------
 最小假设：一个零对象和二元余积。本节中没有 [Cartesian] 的实例，定义方程只是 [inl_merge] 和 [inr_merge] 在 [id] 和 [zero_mor] 处的读取。与上面的索引形式不同，这不需要可判定的索引相等，两个加数在语法上是可区分的。
*)
Definition inl_Section : Section (@inl C CC x y) :=
  {| section := id ▽ zero_mor; section_comp := inl_merge id zero_mor |}.

Definition inr_Section : Section (@inr C CC x y) :=
  {| section := zero_mor ▽ id; section_comp := inr_merge zero_mor id |}.

Definition inl_SplitMono : SplitMono (@inl C CC x y) := inl_Section.
Definition inr_SplitMono : SplitMono (@inr C CC x y) := inr_Section.

Definition inl_Monic : Monic (@inl C CC x y) :=
  sections_are_monic _ _ _ inl_Section.

Definition inr_Monic : Monic (@inr C CC x y) :=
  sections_are_monic _ _ _ inr_Section.

End CoproductInjections.

(* * ** The binary product and coproduct as indexed ones / * ** 二元乘积与余积作为索引乘积 *)

(*
 The dual of [fin2_legs]: a pair of morphisms INTO a common target,
 indexed over [Fin.t 2].  It is [fin2_legs] read in C^op, which is why the
 binary coproduct instance below is a one-line instantiation. 

 --------
 [fin2_legs] 的对偶：一对射到公共目标的态射，按 [Fin.t 2] 索引。在 C^op 中阅读为 [fin2_legs]，这就是为什么下面的二元余积实例是一行实例化。
*)
Definition fin2_colegs {C : Category} {a x y : C} (f : x ~> a) (g : y ~> a) :
  ∀ i : Fin.t 2, fin2fam x y i ~> a :=
  @fin2_legs (C^op) a x y f g.

Definition binary_IsIndexedProduct {C : Category}
  (CP : @Cartesian C) (x y : C) :
  IsIndexedProduct (fin2fam x y) (x × y)%object (fin2_legs exl exr).
Proof.
  apply Build_IsIndexedProduct.
  intros c pi.
  unshelve eapply Build_Unique.
  - exact (pi Fin.F1 △ pi (Fin.FS Fin.F1)).
  - intro i.
    pattern i; apply (Fin.caseS' i); simpl.
    + apply exl_fork.
    + intro j.
      pattern j; apply (Fin.caseS' j); simpl.
      * apply exr_fork.
      * intro k; apply (Fin.case0 (fun _ => _) k).
  - intros v Hv.
    symmetry.
    apply (snd (ump_products _ _ _)).
    split.
    + exact (Hv Fin.F1).
    + exact (Hv (Fin.FS Fin.F1)).
Defined.

Definition binary_IsIndexedCoproduct {C : Category}
  (CC : @Cocartesian C) (x y : C) :
  IsIndexedCoproduct (fin2fam x y) (x + y)%object (fin2_colegs inl inr) :=
  @binary_IsIndexedProduct (C^op) CC x y.

(*
   * ** The identity matrix at n = 2 IS Semiadditive's [can_comparison] 

   --------
   * ** 在 n = 2 时的单位矩阵是 Semiadditive 的 [can_comparison]
*)

Section BinaryComparison.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context `{CP : @Cartesian C}.
Context `{CC : @Cocartesian C}.
Context (x y : C).

Definition binary_can : (x + y)%object ~> (x × y)%object :=
  can_matrix (fin2fam x y) Fin.eq_dec
    (binary_IsIndexedCoproduct CC x y) (binary_IsIndexedProduct CP x y).

(*
 The two diagonal entries are [exl_can_inl] and [exr_can_inr]. 

 --------
 两个对角线上的条目是 [exl_can_inl] 和 [exr_can_inr]。
*)
Lemma binary_entry_diag (j : Fin.t 2) :
  mat_entry (fin2_colegs inl inr) (fin2_legs exl exr)
    (can_comparison x y) j j ≈ id.
Proof.
  pattern j; apply fin2fam_rect; unfold mat_entry; simpl.
  - apply exl_can_inl.
  - apply exr_can_inr.
Qed.

(*
 The two off-diagonal entries are [exr_can_inl] and [exl_can_inr]. 

 --------
 两个非对角线条目是 [exr_can_inl] 和 [exl_can_inr]。
*)
Lemma binary_entry_off (j k : Fin.t 2) :
  j <> k →
  mat_entry (fin2_colegs inl inr) (fin2_legs exl exr)
    (can_comparison x y) j k ≈ zero_mor.
Proof.
  revert k.
  pattern j; apply fin2fam_rect; intro k; pattern k; apply fin2fam_rect;
  intro Hne; unfold mat_entry; simpl.
  - now contradiction Hne.
  - apply exr_can_inl.
  - apply exl_can_inr.
  - now contradiction Hne.
Qed.

Theorem binary_can_is_can_comparison : can_comparison x y ≈ binary_can.
Proof.
  apply (can_matrix_unique (fin2fam x y) Fin.eq_dec
           (binary_IsIndexedCoproduct CC x y)
           (binary_IsIndexedProduct CP x y)).
  - exact binary_entry_diag.
  - exact binary_entry_off.
Qed.

End BinaryComparison.

(*
   * ** At the n-ary folds of Structure/Limit/Product/Finite.v 

   --------
   * ** 在 Structure/Limit/Product/Finite.v 的 n 元折叠处
*)

Section FiniteMatrix.

Context {C : Category}.
Context `{CP : @Cartesian C}.
Context `{T : @Terminal C}.
Context (CC : @Cocartesian C).
Context (I : @Initial C).

Definition fin_matrix {m n : nat} (gs : Fin.t m → C) (fs : Fin.t n → C)
  (e : ∀ (j : Fin.t m) (k : Fin.t n), gs j ~> fs k) :
  fin_coprod CC I m gs ~> fin_prod n fs :=
  matrix_mor (fin_IsIndexedCoproduct CC I m gs) (fin_IsIndexedProduct n fs) e.

Theorem fin_matrix_entry {m n : nat} (gs : Fin.t m → C) (fs : Fin.t n → C)
  (e : ∀ (j : Fin.t m) (k : Fin.t n), gs j ~> fs k)
  (j : Fin.t m) (k : Fin.t n) :
  mat_entry (fin_inj CC I m gs) (fin_proj n fs)
    (fin_matrix gs fs e) j k ≈ e j k.
Proof. apply matrix_entry. Qed.

Theorem fin_matrix_ext {m n : nat} (gs : Fin.t m → C) (fs : Fin.t n → C)
  (u v : fin_coprod CC I m gs ~> fin_prod n fs) :
  (∀ (j : Fin.t m) (k : Fin.t n),
     mat_entry (fin_inj CC I m gs) (fin_proj n fs) u j k
       ≈ mat_entry (fin_inj CC I m gs) (fin_proj n fs) v j k) → u ≈ v.
Proof.
  apply (matrix_ext (fin_IsIndexedCoproduct CC I m gs)
                    (fin_IsIndexedProduct n fs)).
Qed.

(*
 Strict: the rows and the whole matrix ARE the fold's own tupling and
 cotupling.  [fin_prod_ump] is [Defined] and [IsIndexedProduct] has
 primitive projections, so the descent datum reduces. 

 --------
 严格：行和整个矩阵本身就是折叠的成对化和共成对化。[fin_prod_ump] 是 [Defined]，而 [IsIndexedProduct] 有原始投影，所以下行数据简化了。
*)
Example matrix_row_at_fold {J : Type} {gs : J → C} {n : nat}
  (fs : Fin.t n → C) (e : ∀ (j : J) (k : Fin.t n), gs j ~> fs k) (j : J) :
  matrix_row (fin_IsIndexedProduct n fs) e j = fin_tuple n fs (gs j) (e j) :=
  eq_refl.

Example matrix_mor_at_fold {m n : nat} (gs : Fin.t m → C) (fs : Fin.t n → C)
  (e : ∀ (j : Fin.t m) (k : Fin.t n), gs j ~> fs k) :
  fin_matrix gs fs e
    = fin_cotuple CC I m gs (fin_prod n fs)
        (fun j => fin_tuple n fs (gs j) (e j)) := eq_refl.

End FiniteMatrix.

Section FiniteComparison.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context `{CP : @Cartesian C}.
Context `{T : @Terminal C}.
Context (CC : @Cocartesian C).
Context (I : @Initial C).

(*
 [T] and [I] are taken as separate hypotheses rather than read off [Z].
 That is not a stronger assumption -- [zero_terminal] and [zero_initial]
 inhabit them -- and it keeps the fold's chosen unit independent of the
 zero object used for [zero_mor]. 

 --------
 [T] 和 [I] 被视为独立的假设，而不是从 [Z] 中读取。这并不是一个更强的假设——[zero_terminal] 和 [zero_initial] 存在于它们中——并且它保持了该 fold 选择的单元与用于 [zero_mor] 的零对象的独立性。
*)
Definition fin_can {n : nat} (fs : Fin.t n → C) :
  fin_coprod CC I n fs ~> fin_prod n fs :=
  can_matrix fs Fin.eq_dec
    (fin_IsIndexedCoproduct CC I n fs) (fin_IsIndexedProduct n fs).

Theorem fin_can_diag {n : nat} (fs : Fin.t n → C) (j : Fin.t n) :
  mat_entry (fin_inj CC I n fs) (fin_proj n fs) (fin_can fs) j j ≈ id.
Proof. apply can_matrix_diag. Qed.

Theorem fin_can_off {n : nat} (fs : Fin.t n → C) (j k : Fin.t n) :
  j <> k →
  mat_entry (fin_inj CC I n fs) (fin_proj n fs) (fin_can fs) j k
    ≈ zero_mor.
Proof. apply can_matrix_off. Qed.

Theorem fin_can_unique {n : nat} (fs : Fin.t n → C)
  (u : fin_coprod CC I n fs ~> fin_prod n fs) :
  (∀ j : Fin.t n,
     mat_entry (fin_inj CC I n fs) (fin_proj n fs) u j j ≈ id) →
  (∀ j k : Fin.t n, j <> k →
     mat_entry (fin_inj CC I n fs) (fin_proj n fs) u j k ≈ zero_mor) →
  u ≈ fin_can fs.
Proof. apply can_matrix_unique. Qed.

End FiniteComparison.

(*
   * ** At the classes [HasFiniteCoproducts] / [HasFiniteProducts] 

   --------
   * ** 在课程 [HasFiniteCoproducts] / [HasFiniteProducts]
*)

Section FiniteClassMatrix.

Context {C : Category}.
Context {HFP : HasFiniteProducts C}.
Context {HFC : HasFiniteCoproducts C}.

Definition finite_matrix {m n : nat} (gs : Fin.t m → C) (fs : Fin.t n → C)
  (e : ∀ (j : Fin.t m) (k : Fin.t n), gs j ~> fs k) :
  finite_coproduct gs ~> finite_product fs :=
  matrix_mor (finite_coproduct_ump gs) (finite_product_ump fs) e.

Theorem finite_matrix_entry {m n : nat} (gs : Fin.t m → C)
  (fs : Fin.t n → C) (e : ∀ (j : Fin.t m) (k : Fin.t n), gs j ~> fs k)
  (j : Fin.t m) (k : Fin.t n) :
  mat_entry (finite_coproduct_inj gs) (finite_product_proj fs)
    (finite_matrix gs fs e) j k ≈ e j k.
Proof. apply matrix_entry. Qed.

Theorem finite_matrix_ext {m n : nat} (gs : Fin.t m → C)
  (fs : Fin.t n → C) (u v : finite_coproduct gs ~> finite_product fs) :
  (∀ (j : Fin.t m) (k : Fin.t n),
     mat_entry (finite_coproduct_inj gs) (finite_product_proj fs) u j k
       ≈ mat_entry (finite_coproduct_inj gs) (finite_product_proj fs)
           v j k) → u ≈ v.
Proof.
  apply (matrix_ext (finite_coproduct_ump gs) (finite_product_ump fs)).
Qed.

End FiniteClassMatrix.

Section FiniteClassComparison.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context {HFP : HasFiniteProducts C}.
Context {HFC : HasFiniteCoproducts C}.

Definition finite_can {n : nat} (fs : Fin.t n → C) :
  finite_coproduct fs ~> finite_product fs :=
  can_matrix fs Fin.eq_dec
    (finite_coproduct_ump fs) (finite_product_ump fs).

Theorem finite_can_diag {n : nat} (fs : Fin.t n → C) (j : Fin.t n) :
  mat_entry (finite_coproduct_inj fs) (finite_product_proj fs)
    (finite_can fs) j j ≈ id.
Proof. apply can_matrix_diag. Qed.

Theorem finite_can_off {n : nat} (fs : Fin.t n → C) (j k : Fin.t n) :
  j <> k →
  mat_entry (finite_coproduct_inj fs) (finite_product_proj fs)
    (finite_can fs) j k ≈ zero_mor.
Proof. apply can_matrix_off. Qed.

Theorem finite_can_unique {n : nat} (fs : Fin.t n → C)
  (u : finite_coproduct fs ~> finite_product fs) :
  (∀ j : Fin.t n,
     mat_entry (finite_coproduct_inj fs) (finite_product_proj fs) u j j
       ≈ id) →
  (∀ j k : Fin.t n, j <> k →
     mat_entry (finite_coproduct_inj fs) (finite_product_proj fs) u j k
       ≈ zero_mor) →
  u ≈ finite_can fs.
Proof. apply can_matrix_unique. Qed.

End FiniteClassComparison.

(*
 Strict: at the instances built from [Cartesian]+[Terminal] and
 [Cocartesian]+[Initial], the class-level constructions ARE the
 fold-level ones. 

 --------
 严格：在由 [Cartesian] + [Terminal] 和 [Cocartesian] + [Initial] 构建的实例中，类级构造就是折叠级构造。
*)
Example finite_matrix_is_fin_matrix {C : Category} (CP : @Cartesian C)
  (T : @Terminal C) (CC : @Cocartesian C) (I : @Initial C)
  {m n : nat} (gs : Fin.t m → C) (fs : Fin.t n → C)
  (e : ∀ (j : Fin.t m) (k : Fin.t n), gs j ~> fs k) :
  @finite_matrix C (Cartesian_Terminal_HasFiniteProducts CP T)
    (Cocartesian_Initial_HasFiniteCoproducts CC I) m n gs fs e
  = @fin_matrix C CP T CC I m n gs fs e := eq_refl.

Example finite_can_is_fin_can {C : Category} `{Z : @ZeroObject C}
  (CP : @Cartesian C) (T : @Terminal C) (CC : @Cocartesian C)
  (I : @Initial C) {n : nat} (fs : Fin.t n → C) :
  @finite_can C Z (Cartesian_Terminal_HasFiniteProducts CP T)
    (Cocartesian_Initial_HasFiniteCoproducts CC I) n fs
  = @fin_can C Z CP T CC I n fs := eq_refl.

(* * ** Non-vacuity: the matrix construction computes / * ** 非空性：矩阵构造计算 *)

(*
 [Coq] has finite products and coproducts but no zero object (its initial
 object is [False] and its terminal [unit]), so it witnesses the m x n
 determination and nothing about the identity matrix. 

 --------
 [Coq] 有有限的积和余积，但没有零对象（它的初始对象是 [False]，终对象是 [unit]），所以它证明了 m x n 的确定性，但与单位矩阵无关。
*)

Definition coq_succ_matrix :
  ∀ (j k : Fin.t 2), (fun _ : Fin.t 2 => nat : Coq) j
                       ~> (fun _ : Fin.t 2 => nat : Coq) k :=
  fun _ _ => fun x => S x.

Example coq_matrix_computes :
  fin_matrix Coq_Cocartesian Coq_Initial
    (fun _ : Fin.t 2 => nat : Coq) (fun _ : Fin.t 2 => nat : Coq)
    coq_succ_matrix (Datatypes.inl 3%nat) = (4%nat, (4%nat, tt)) := eq_refl.

Example coq_matrix_computes_right :
  fin_matrix Coq_Cocartesian Coq_Initial
    (fun _ : Fin.t 2 => nat : Coq) (fun _ : Fin.t 2 => nat : Coq)
    coq_succ_matrix (Datatypes.inr (Datatypes.inl 7%nat))
      = (8%nat, (8%nat, tt)) := eq_refl.
