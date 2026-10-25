Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Theory.Metacategory.General.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.

(* Sets and set-like categories. / 集合和类集合类型。 *)
Require Import Category.Instance.Coq.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Ens.
Require Import Category.Instance.EnsV.
Require Import Category.Instance.Rel.
Require Import Category.Instance.Rel.Dagger.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Skeleton.
Require Import Category.Instance.Sets.Pointed.
Require Import Category.Instance.Sets.Par.
Require Import Category.Instance.Coq.Par.

(* Algebraic categories. / 代数范畴 *)
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.FdVect.
Require Import Category.Instance.Field.
Require Import Category.Instance.Rep.
Require Import Category.Instance.Matr.

(* Order, shape and graph categories. / 序、形状和图表类别。 *)
Require Import Category.Instance.Proset.
Require Import Category.Instance.Pos.
Require Import Category.Instance.Cat.
Require Import Category.Instance.One.
Require Import Category.Instance.Zero.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.Terminal.
Require Import Category.Instance.Simplex.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Free.Quiver.Concrete.

(*
 SEGREGATED: the two entries below are the file's entire non-Closed
 axiom footprint, and they are required here only so that the roster
 is complete in one place.  Instance/Top and its satellites run
 through the standard library reals (Instance/Top/Interval.v), so
 every constant mentioning them carries stdlib axioms; see the AXIOMS
 paragraph of the header. 

 --------
 隔离：下面的两个条目是该文件的全部非封闭公理足迹，它们在这里出现只是为了使名单在一个地方完整。Instance/Top及其附属项通过标准库实数（Instance/Top/Interval.v）运行，因此每个提到它们的常量都带有标准库公理；请参见头部的公理段落。
*)
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Forgetful.
Require Import Category.Instance.Top.Homotopy.

(*
 SEGREGATED: Instance/Comp.v is a Leibniz-equality development that
 invokes [functional_extensionality] (the caveat Instance/Ab.v's
 header records).  It is REQUIRED WITHOUT IMPORT, both to keep that
 axiom off this file's other constants and because its record field
 names ([carrier], [eq], [map]) would shadow the library's; every
 reference below is fully qualified. 

 --------
 分离：Instance/Comp.v 是一个莱布尼茨等式开发，它调用了 [functional_extensionality]（注意 Instance/Ab.v 的头部记录）。它需要在没有导入的情况下使用，这既是为了将该公理从本文件的其他常量中隔离开，也因为其记录字段名称（[carrier]、[eq]、[map]）会遮蔽库中的同名字段；下面的每个引用都是完全限定的。
*)
Require Category.Instance.Comp.

Generalizable All Variables.

(*
   * * Roster: the standard large categories, in one place

   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §I.1
   (printed pp. 8-9), the metacategory examples, and §I.2 (printed
   pp. 10-12), the roll-call of large categories that the rest of the
   book quotes without further comment
   [maclane:I.1:construction2, maclane:I.2:construction12]; Awodey,
   "Category Theory", 2nd ed., §1.4, the category of structured sets
   and structure-preserving functions
   [awodey:1.4:construction-structured-sets]; Riehl, "Category Theory
   in Context", §1.1, Example 1.1.3's clause-by-clause list of large
   concrete categories and Example 1.1.4's list of categories whose
   objects are not sets [riehl:1.1:example3, riehl:1.1:example4].
   nLab: https://ncatlab.org/nlab/show/concrete+category
   Wikipedia: https://en.wikipedia.org/wiki/Category_(mathematics)

   WHAT THIS FILE IS.  An INDEX, not a construction, and the contract
   is meant literally: every entry of the four surveys listed above —
   Mac Lane's §I.1 metacategory examples and §I.2 roll-call, Awodey's
   §1.4 structured sets, Riehl's Examples 1.1.3 and 1.1.4, and Riehl's
   Example 1.6.15 initial/terminal survey — is EITHER exhibited here
   from the tree (the category, and its evident forgetful functor or
   initial/terminal instance where the tree packages one) OR listed in
   the OUT OF SCOPE section below with the reason it is absent.  There
   is no third case: an entry that appears in none of the sections
   below is an omission, not a silent judgement.  The value is the
   single point of reference — a reader who wants to know whether this
   library has "the category of rings", or what it calls it, or
   whether "the category of measurable spaces" exists, should need to
   open one file.  Nothing is re-proved here.  Two things are
   genuinely new: [Mon_Sets], the residual instantiation named in the
   section below, and — in the companion Instance/Field.v — the
   category of fields together with the determination of its
   monomorphisms and the absence of initial and terminal objects,
   which is the one roster entry that asks for mathematics rather
   than bookkeeping.

   HOW TO READ AN ENTRY.  Each entry is one or two [Example] lines
   naming the category at its declared type and, where the tree
   packages one, the functor down to [Sets] or to the neighbouring
   structure.  An [Example] that typechecks is the claim: this
   category exists, under this name, with this shape.  Where the tree
   packages no forgetful functor, that is said rather than patched —
   building one is the business of the file that owns the entry, not
   of an index.

   THE MAC LANE ROSTER (§I.2), entry by entry.  Set is [Sets] (setoids
   — see Instance/Sets.v on why the library's "sets" carry an
   equivalence rather than Leibniz equality) with [Coq] the strict
   variant and [Ens]/[EnsV] Mac Lane's own set-within-a-universe
   readings; Set_* is [PointedSets]; Ens_V is [EnsV]; Mon is
   [Mon_Sets] below (internal monoids in (Sets, ∏)) with [CMon] the
   commutative set-level variant; Grp is [Grp]; Ab is [Ab]; Rng is
   [Rng] with [CRng] its commutative full subcategory; R-Mod is
   [RMod R], Mod-R is [ModR R], and bimodules are the record
   [Bimodule]; Vct_K is [Vct_F] with [FdVect] the finite-dimensional
   refinement carrying chosen coordinates; Top is [Top]; Toph is
   [Toph]; Top_* is [Top_pointed] and Toph_* is [Toph_pointed]; Cat is
   [Cat] with [StrictCat] the strict-functor-equality variant;
   Preord/Pos are [Proset]/[Pos] (see the erratum below); Δ is
   [Simplex]; Matr_K is [Matr]; Rel is [Rel]; and the arrows-only
   metacategory of §I.1 is [Metacategory], with
   [Category_from_Metacategory] the passage back.

   A NAMING ERRATUM, recorded because it has misled before.
   Instance/Poset.v's [Poset] TAKES an [Antisymmetric] hypothesis and
   then DISCARDS it: its body is literally [Proset P].  So it turns
   ONE preorder into a thin category, the antisymmetry contributes
   nothing to the category produced, and it is not the category of
   posets under another name.  The category whose OBJECTS are posets
   is Instance/Pos.v's [Pos].  Riehl 1.1.3's "Poset" clause is [Pos];
   Mac Lane's "Preord" is Instance/Ord.v's [Ord] (#372), NOT [Proset],
   which is ONE preorder.  [Pos] and [Proset] are exhibited below, side
   by side; [Ord] is NOT exhibited here (it would add Instance/Ord.v to
   this file's closure and move its measured counts), which is disclosed.

   RIEHL 1.1.4, the non-concrete entries.  Clause (i), the matrix
   category Mat_R, is [Matr] (Instance/Matr.v).  Clause (ii), the
   delooping BG of a group or monoid, is Construction/Deloop.v's
   [Deloop] — cited, not required here, to keep this file's dependency
   cone to the roster proper.  Clause (vii), the category Measure of
   almost-everywhere classes of measurable maps, is out of scope; see
   below.

   OUT OF SCOPE, each with its reason.  These are disclosures, not
   apologies: the reason in every case is a missing piece of
   mathematics elsewhere in the tree, named so that a later issue can
   pick it up.

   - Compact Hausdorff spaces AS A ROSTER ENTRY WITH ITS FORGETFUL
   STORY.  The full subcategory itself EXISTS and is exhibited
   below ([CompactHausdorffSpaces], Instance/Top.v).  What stays
   out is the reason the books list it: the underlying-set functor
   with its left adjoint (the Stone-Čech compactification) and the
   ultrafilter-monad monadicity theorem.  The first is obstructed
   by the universe stratification Instance/Top/Forgetful.v proves
   out — Top's homs sit strictly above its points, so the
   forgetful functor lands in a HIGHER [Sets] and the packaged
   [Adjunction] record is unformable — and the second needs
   ultrafilters, which the tree has not got.  CORRECTION (#455): for
   the Stone–Čech adjoint the packaged record IS formable, its left
   adjoint's domain being that higher [Sets] itself, and it is
   refuted under informative excluded middle, with the objects of
   [CompHaus] at its hom universe by
   Instance/Top/StoneCech/Refutations.v's
   [StoneCech_adjunction_refuted_IEM] and with them above it by that
   file's [StoneCech_adjunction_refuted_IEM_above], each at the
   instances its COVERAGE records (the [Top] slot at the hom
   universe, the proof slot at the object universe, the Hausdorff
   proof's opens at the points' universe): the higher [Sets] contains
   a set the size of all the arrows of [CompHaus], at which, under
   that principle, no universal arrow exists.  #455's review measured
   the second refutation, which a draft of this correction denied.
   The universal arrows at finitely enumerable sets of points are
   Instance/Top/StoneCech.v's [StoneCech_finite].

   - Ringed spaces.  There is no sheaf-of-rings machinery over
   [Top]: Theory/Sheaf.v's [Sheaf] predicate is per-leg and, as
   Theory/Sheaf/Category.v's header discloses, vacuous beyond
   subsingleton fibres, so a structure sheaf could not be stated
   honestly.  Gated on the matching-family re-founding that ships
   with sheafification.

   - Man, smooth manifolds and smooth maps.  No differential
   structure of any kind exists in the tree — no charts, no
   atlases, no smoothness predicate — and Instance/Rng/Frac.v
   already descopes the Lie-algebra half of its own exercise for
   the same reason.

   - Meas, measurable spaces, and Measure, its quotient by
   almost-everywhere equality [riehl:1.1:example4].  σ-algebras
   and null sets are both absent.  Worth recording as a FUTURE
   TARGET rather than a permanent gap: Measure is a natural test
   of this library's setoid discipline, since a.e.-equality is
   exactly a hom-setoid coarser than pointwise equality, which is
   what [homset] is for, and Construction/Quotient.v already has
   the hom-congruence quotient the construction would use.

   - ℕ with the recursive functions as morphisms.  Computability
   theory is out of scope; nothing in the tree formalizes a model
   of computation.  (Instance/Lambda/ formalizes the simply-typed
   lambda calculus over de Bruijn syntax — the internal language
   of a cartesian closed category — which is a different subject:
   a term language with its own semantics, not the partial
   recursive functions.)

   - Chain complexes Ch_R and their chain maps.  There is no graded
   machinery — no ℤ-graded objects, no differentials, no
   homology — so the entry would have no content beyond a record
   declaration.  Riehl's §E.2 material is tracked separately.

   - Model_T, the category of models of a full first-order theory.
   What the tree has is the EQUATIONAL fragment: Instance/Comp.v's
   [Algs] for an operation signature, together with its equational
   refinement (see the segregated section below), and
   Theory/Lawvere/Model.v's [Models T C] for a Lawvere theory.
   Relation symbols, quantifiers and non-equational axioms are
   absent, so "the category of models of T" is delivered only for
   algebraic T.

   - SIMPLE GRAPHS (Riehl 1.1.3's graph clause, in the symmetric
   irreflexive reading).  What the tree has is QUIVERS — directed
   multigraphs with an edge TYPE between each ordered pair
   ([QuiverCategory], exhibited below).  Simple graphs, with a
   symmetric irreflexive relation and no parallel edges, are not
   constructed.  The clause is worth its own row rather than
   folding into the quiver one, because it is the clause with the
   interesting initial/terminal behaviour: the empty graph is
   initial, but there is NO terminal simple graph, since a
   terminal one would have to receive the one-vertex-with-a-loop
   graph and hence carry a loop, which irreflexivity forbids.
   With no simple graphs in tree, neither half is statable.

   - Awodey's TWO REAL-ANALYSIS ROSTER ENTRIES: ℝ with the
   continuous maps, and the open subsets of ℝ with the continuous
   maps between them.  The INGREDIENTS exist —
   Instance/Top/Presheaf.v builds the real line as a space
   ([R_Top], its metric topology carried by a ball structure) and
   the open subspaces ([OpenSub]) with their subspace topology
   identified — but neither roster CATEGORY is assembled: not the
   endomorphism monoid of ℝ read as a one-object category, and not
   the full subcategory of [Top] on the open subspaces of ℝ.
   Nothing downstream consumes either, which is why they were
   never built; both are short given the ingredients, and both
   would land in the reals-carrying group.

   - The DERIVATIVE as a functor — the assignment sending a smooth
   map to its Jacobian, which is the standard first example of a
   functor whose action on morphisms is the interesting part.
   Same root cause as Man: there is no differential structure in
   the tree, so neither the domain category nor the morphism
   action can be written down.

   - The determination of the monomorphisms of the category of
   fields, and the absence of initial and terminal objects there,
   are NOT here: they are Instance/Field.v, which owns the
   category and both theorems, and which discloses in its own
   header the exact constructive strength of each.  The entry
   points are cross-referenced in the initial/terminal section
   below.

   AXIOMS, measured per constant rather than sampled, and the
   measurement is FINER than the section headings would suggest.  The
   count is docs/AXIOMS.md's: everything the module declares, which
   for this file is 96 constants — 94 [Example]s, the two
   [Definition]s of the [Mon_Sets] section, and no [Program]
   obligations, since no declaration here generates any.  Of those 96,
   90 are "Closed under the global context".  The other six are these,
   and only these:

   - [roster_Toph], [roster_TophProj], [roster_Toph_pointed],
   [roster_Toph_pointed_Proj] carry BOTH stdlib axioms
   ([ClassicalDedekindReals.sig_forall_dec] and
   [FunctionalExtensionality.functional_extensionality_dep]);

   - [roster_Group_variety] and [roster_Group_variety_witness] carry
   [functional_extensionality_dep] alone.

   Two consequences are worth stating because they correct the obvious
   guess.  FIRST, [Top] is NOT a reals-carrying entry: [roster_Top],
   [roster_Top_Forget], [roster_Top_Discrete],
   [roster_Top_Indiscrete], [roster_HausdorffSpaces],
   [roster_CompactHausdorffSpaces] and [roster_Top_pointed] are all
   Closed.  The reals enter only with the HOMOTOPY relation, which
   needs the unit interval (Instance/Top/Interval.v) — so it is the
   quotient categories Toph and Toph_*, not the topology, that pay.
   SECOND, [roster_Algs] and [roster_GroupOp] are Closed as well:
   Instance/Comp.v's signature and category machinery is axiom-free,
   and [functional_extensionality] is spent only in [GroupEq]'s
   naturality proof, hence only by the two constants that mention the
   group VARIETY.  The body is ordered so that in each segregated
   section the Closed constants come first and the six exceptions come
   last, contiguously. 

   --------
   * * 名录：标准大范畴，一处集合

   Mac Lane，《为工作数学家准备的范畴论》，第二版，第 I.1 节（印刷页 8-9），元范畴示例，以及第 I.2 节（印刷页 10-12），大范畴点名，书中其余部分引用而不作进一步评论
   [maclane:I.1:construction2, maclane:I.2:construction12] ; Awodey，《范畴论》，第二版，第 1.4 节，结构集合及保持结构的函数的范畴
   [awodey:1.4:construction-structured-sets] ; Riehl，《范畴论在语境中》，第 1.1 节，示例 1.1.3 的逐条列出大具体范畴，以及示例 1.1.4 的对象非集合的范畴列表  [riehl:1.1:example3, riehl:1.1:example4] .
   nLab:  https://ncatlab.org/nlab/show/concrete+category 
   维基百科:  https://en.wikipedia.org/wiki/Category_(mathematics)这个文件是什么。它是一个索引，而不是构造，并且合同是字面上的：上面列出的四个概述的每一个条目——Mac Lane 的 §I.1 元类示例和 §I.2 点名表，Awodey 的 §1.4 结构化集合，Riehl 的示例 1.1.3 和 1.1.4，以及 Riehl 的示例 1.6.15 初/末端概述——要么在此展示（来自树状结构——类别及其明显的遗忘函子或初/末端实例，其中树状结构包含其中之一），要么在下面的“超出范围”部分列出并说明缺失的原因。没有第三种情况：出现在以下任何部分都未被列出的条目是遗漏，而不是默示的评判。价值在于它是唯一的参考点——一个想要知道这个库是否有“环的范畴”，或者它称呼它为什么，或者“可测空间的范畴”是否存在的读者，只需要打开一个文件。这里没有重新证明任何东西。有两样东西是真正新的：下面章节中命名的残余实例 [Mon_Sets]，以及在配套的 Instance/Field.v 中的域的范畴，以及其单射的确定和初始对象与终端对象的缺失，这是唯一一条需要数学而非簿记的清单项。如何阅读条目。每个条目由一到两行 [Example] 组成，标明其声明类型的类别，以及在树打包的情况下，其函子直到 [Sets] 或邻近结构。一个通过类型检查的 [Example] 就是声明：该类别存在，以此名称，具有此形状。如果树打包没有遗忘函子，则说明而不是修补——构建遗忘函子是拥有该条目的文件的工作，而不是索引的工作。MAC LANE 名单（§I.2），逐条列出。集合是 [Sets]（集合论——参见 Instance/Sets.v，了解为什么库中的“集合”携带的是等价关系而不是莱布尼茨等式），[Coq] 是严格变体，[Ens] / [EnsV] 是 Mac Lane 自己的宇宙内集合解释；Set_* 是 [PointedSets]；Ens_V 是 [EnsV]；Mon 是 [Mon_Sets]（在 (Sets, ∏) 中的内部幺半群），[CMon] 是可交换集合级变体；Grp 是 [Grp]；Ab 是 [Ab]；Rng 是 [Rng]，[CRng] 是其可交换完整子范畴；R-Mod 是 [RMod R]，Mod-R 是 [ModR R]，双模体是记录 [Bimodule]；Vct_K 是 [Vct_F]，[FdVect] 是具有选择坐标的有限维精炼；Top 是 [Top]；Toph 是 [Toph]；Top_* 是 [Top_pointed]，Toph_* 是 [Toph_pointed]；Cat 是 [Cat]，[StrictCat] 是严格-functore-等价 变体；
   Preord/Pos 是 [Proset] / [Pos]（参见下面的勘误表）；Δ 是 [Simplex]；Matr_K 是 [Matr]；Rel 是 [Rel]；而 §I.1 中的仅箭头元范畴是 [Metacategory]，ZWZ38WZZ 是返回的映射。一个命名错误，记录下来是因为它之前造成了误导。
   Instance/Poset.v 的 [Poset] 接受一个 [Antisymmetric] 假设，然后将其丢弃：它的主体字面上是 [Proset P]。因此它将一个 preorder 转换为一个细类别，反对称性对生成的类别没有什么贡献，它也不是在另一个名称下的偏序集合类别。对象为偏序集合的类别是 Instance/Pos.v 的 [Pos]。Riehl 1.1.3 的 “Poset” 条款是 [Pos]；Mac Lane 的 “Preord” 是 Instance/Ord.v 的 [Ord] （#372），而不是 [Proset]，它只是一个 preorder。[Pos] 和 [Proset] 在下方并排展示；[Ord] 此处未展示（它会将 Instance/Ord.v 添加到本文件的闭包并移动其测量计数），这一点已公开。RIEHL 1.1.4，非具体条目。条款 (i)，矩阵范畴 Mat_R，是 [Matr] (Instance/Matr.v)。条款 (ii)，群或幺半群的去环化 BG，是 Construction/Deloop.v 的 [Deloop] — 引用而非此处必需，为了保持此文件对目录的依赖锥的完整。条款 (vii)，几乎处处可测映射的可测类的范畴 Measure，不在范围内；见下文。

   不在范围内，每条理由各不相同。这些是披露，而非道歉：每种情况的理由是树中其他地方缺失的一段数学内容，以便后续问题可以接上。- 作为花名册条目及其遗忘故事的紧致豪斯多夫空间。该子范畴本身存在，并在下文中展示（[CompactHausdorffSpaces]，Instance/Top.v）。没有提及的是书中列出的原因：带有其左伴随（Stone-Čech 紧致化）的底集合函子以及超滤子单子幂等性定理。第一个被宇宙分层阻碍，Instance/Top/Forgetful.v 证明了——Top 的箭子严格高于其点，因此遗忘函子落入更高的 [Sets]，并且打包的 [Adjunction] 记录无法形成——而第二个需要超滤子，而树中没有。更正 (#455)：对于 Stone–Čech 伴随，打包记录是可构造的，其左伴域是更高的 [Sets] 本身，并且在信息排中律下它是被反驳的，其同对象宇宙中的对象 [CompHaus] 由 Instance/Top/StoneCech/Refutations.v 的 [StoneCech_adjunction_refuted_IEM] 反驳，并且在它之上的对象由该文件的 [StoneCech_adjunction_refuted_IEM_above] 表示，每个都位于其实例 COVERAGE 记录中（同宇宙的 [Top] 槽、对象宇宙的证明槽、Hausdorff 证明的开集在点宇宙）：更高的 [Sets] 包含一个其大小为 [CompHaus] 所有箭头大小的集合，在该原则下，没有普遍箭头存在。#455的评论测量了第二次反驳，而本次修正的草稿否认了这一点。在有限可枚举点集上的普遍箭头是 Instance/Top/StoneCech.v 的 [StoneCech_finite]。

   - 括号化空间。在 [Top] 上没有环层机械装置：Theory/Sheaf.v 的 [Sheaf] 谓词是按腿的，并且正如 Theory/Sheaf/Category.v 的标题所披露的那样，超出子单例纤维是空的，所以结构层不能如实陈述。受限于匹配族重建，该重建随层化而发布。- 流形和平滑映射。树中不存在任何类型的微分结构——没有图表，没有图册，没有平滑性谓词——而 Instance/Rng/Frac.v 因同样的原因已经取消了其自身练习中 Lie 代数部分的范围。

   - Meas，可测空间，以及 Measure，其按几乎处处相等的商 [riehl:1.1:example4]。σ-代数和零测集都不存在。值得记录为未来目标而不是永久缺失：Measure 是测试该库集合体纪律的自然对象，因为 a.e.-相等恰好是一种比逐点相等更粗的同态集合体，而这正是 [homset] 的用途，并且 Construction/Quotient.v 已经具有构造将使用的同态一致商。- ℕ 以递归函数作为态射。可计算性理论不在讨论范围内；树中的内容没有形式化计算模型。(Instance/Lambda/ 形式化了基于 de Bruijn 语法的简单类型 lambda 演算 —— 笛卡尔闭范畴的内部语言 —— 这是一个不同的主题：一个有自身语义的项语言，而不是部分递归函数。)

   - 链复形 Ch_R 及其链映射。没有分级机制 —— 没有 ℤ-分级对象，没有微分，没有同调 —— 因此该条目除了记录声明外没有其他内容。Riehl 的 §E.2 材料单独跟踪。- Model_T，全一阶理论模型的范畴。 树中所包含的是方程片段：Instance/Comp.v 的 [Algs] 用于操作符号，以及其方程精炼（见下文独立部分），以及 Theory/Lawvere/Model.v 的 [Models T C] 用于 Lawvere 理论。 关系符号、量词和非方程公理缺失，因此“模型 T 的范畴”只适用于代数 T。- 简单图（Riehl 1.1.3 的图子句，在对称不可反自关系的理解下）。树中存在的是有向多重图（QUIVERS）——在每个有序对之间具有边类型的图（[QuiverCategory]，如下所示）。简单图，具有对称不可反自关系且没有平行边，并未构造。该子句值得独立成行，而不是合并到有向图那一行中，因为它是具有有趣初始/终止行为的子句：空图是初始的，但没有终止的简单图，因为终止图必须接收带有自环的单顶点图，因此会带有自环，而不可反自性禁止自环。在树中没有简单图的情况下，两半都无法表述。- Awodey 的两个实分析名册条目：ℝ 及其连续映射，以及 ℝ 的开子集及其之间的连续映射。原料是存在的——Instance/Top/Presheaf.v 将实数线构建为一个空间（[R_Top]，它的度量拓扑由球结构携带）以及带有其子空间拓扑的开子空间（[OpenSub]）——但这两个名册类别都没有组装：既不是将 ℝ 读作单对象类别的自同态幺半群，也不是 ℝ 的开子空间上的 [Top] 的满子类别。下游没有任何部分使用它们，这就是为什么它们从未被构建；根据这些原料，它们都很短，并且它们都将属于携带实数的群。- 导数作为函子——将一个光滑映射分配给它的雅可比矩阵，这是一个函子最标准的第一个例子，其中对态射的作用才是有趣的部分。与 Man 的根本原因相同：树中没有微分结构，因此既无法写出定义域范畴，也无法写出态射的作用。

   - 关于域范畴中单射的确定，以及那里初对象和终对象的缺失，不在这里：它们在 Instance/Field.v 中，该文件拥有这个范畴和这两个定理，并在其头部揭示了每个定理的确切构造性强度。入口点在下面的初对象/终对象部分有交叉引用。公理，按常量而非抽样进行测量，并且测量比章节标题所示的更精细。计数来源于 docs/AXIOMS.md：模块声明的所有内容，对于此文件是 96 个常量——94 个 [Example]，[Mon_Sets] 部分的两个 [Definition]，没有 [Program] 义务，因为此处没有声明会生成任何义务。在这 96 个常量中，有 90 个是“在全局上下文下封闭”的。其余六个如下，仅限于这些：

   - [roster_Toph]、[roster_TophProj]、[roster_Toph_pointed]、[roster_Toph_pointed_Proj] 均携带标准库公理（[ClassicalDedekindReals.sig_forall_dec] 和 [FunctionalExtensionality.functional_extensionality_dep]）；

   - [roster_Group_variety] 和 [roster_Group_variety_witness] 仅携带 [functional_extensionality_dep]。有两个结果值得说明，因为它们纠正了显而易见的猜测。首先，[Top] 不是携带实数的条目：[roster_Top]、[roster_Top_Forget]、[roster_Top_Discrete]、[roster_Top_Indiscrete]、[roster_HausdorffSpaces]、[roster_CompactHausdorffSpaces] 和 [roster_Top_pointed] 都是封闭的。实数只通过同伦关系进入，该关系需要单位区间（Instance/Top/Interval.v）——因此实际上付出代价的是商范畴 Toph 和 Toph_*，而不是拓扑。其次，[roster_Algs] 和 [roster_GroupOp] 也是封闭的：Instance/Comp.v 的签名和范畴机制是无公理的，而 [functional_extensionality] 只在 [GroupEq] 的自然变换证明中使用，因此只有通过提到群 VARIETY 的两个常量。正文的顺序是这样安排的：在每个独立部分中，封闭常量排在前面，六个例外连续排在最后。
*)

(* * ** Sets and the set-like categories / * ** 集合与类集合 *)

(*
 Mac Lane's Set, in the library's two readings: setoids, and the
 strict category of Coq types with functions. 

 --------
 Mac Lane 的集合，在图书馆的两种阅读中：集合族，以及带函数的 Coq 类型的严格范畴。
*)
Example roster_Sets : Category := Sets.
Example roster_Coq : Category := Coq.

(*
 Mac Lane's Ens and Ens_V: sets carrying membership, and the sets
 within a universe V presented as codes with a decoding.  [EnsV] is
 Mac Lane's own device for making "the category of all sets" a
 legitimate object; [Spanned] is its general form. 

 --------
 麦克莱恩的 Ens 和 Ens_V：携带成员资格的集合，以及作为编码并带有解码的宇宙 V 中的集合。[EnsV] 是麦克莱恩自己用于使“所有集合的范畴”成为合法对象的装置；[Spanned] 是它的一般形式。
*)
Example roster_Ens : Category := Ens.
Example roster_EnsT (T : Type) : Category := EnsT T.
Example roster_EnsV {V : Type} (El : V → Type) : Category := EnsV El.
Example roster_EnsV_Incl {V : Type} (El : V → Type) : EnsV El ⟶ Coq :=
  EnsV_Incl El.

(* Finite sets, in both presentations: the skeletal one on [nat], and finite setoids carrying their counting, with the comparison. / 有限集合，在两种表述中：在 [nat] 上的骨架形式，以及携带其计数的有限集合类，并进行比较。 *)
Example roster_FinSet : Category := FinSet.
Example roster_Set_f : Category := Set_f.
Example roster_FinSet_Incl : FinSet ⟶ Set_f := FinSet_Incl.

(*
 Mac Lane's Set_*: pointed sets and basepoint-preserving maps.  The
 underlying-set functor is still not packaged in
 Instance/Sets/Pointed.v and is not built here, but it now EXISTS:
 [Pointed_Forget], Instance/Sets/Pointed/Free.v, built directly for
 Mac Lane III.1 Ex 3's basepoint row.  The coslice presentation
 ([Pointed_Coslice_iso], Instance/Sets/Pointed/Coslice.v) remains an
 alternative route and is not the one taken. 

 --------
 Mac Lane 的 Set_*：有尖点的集合和保持基点的映射。底层集合函子仍未在 Instance/Sets/Pointed.v 中打包，也未在此构建，但它现在存在：[Pointed_Forget]，Instance/Sets/Pointed/Free.v，直接为 Mac Lane 第 III.1 章习题 3 的基点行构建。余片表示（[Pointed_Coslice_iso]，Instance/Sets/Pointed/Coslice.v）仍然是另一种方法，并不是采用的方法。
*)
Example roster_PointedSets : Category := PointedSets.

(* Partial maps, in both readings: over setoids and over types. / 部分映射，在两种读取方式中：在等价集合上以及在类型上。 *)
Example roster_Part : Category := Part.
Example roster_Par : Category := Par.

(* Rel, with the wide embedding of functions as relations. Note the direction: [Relation_Functor] goes from [Coq], not from [Sets]. / Rel，随着函数作为关系的广泛嵌入。注意方向：[Relation_Functor] 是从 [Coq] 出发，而不是从 [Sets] 出发。 *)
Example roster_Rel : Category := Rel.
Example roster_Relation_Functor : Coq ⟶ Rel := Relation_Functor.

(* * ** The algebraic categories, with their forgetful functors / * ** 代数范畴及其遗忘函子 *)

(* Commutative monoids at the set level. / 集合层面的交换幺半群。 *)
Example roster_CMon : Category := CMon.
Example roster_CMon_Forget : CMon ⟶ Sets := CMon_Forget.

(* Groups and abelian groups. / 群和阿贝尔群。 *)
Example roster_Grp : Category := Grp.
Example roster_Grp_Forget : Grp ⟶ Sets := Grp_Forget.
Example roster_Ab : Category := Ab.
Example roster_Ab_Forget : Ab ⟶ Sets := Ab_Forget.

(*
 Rigs, and rings under Mac Lane's name, with the commutative full
 subcategory and both forgetful functors. 

 --------
 在麦克莱恩名下的环和环体，带有交换的全子范畴以及两个遗忘函子。
*)
Example roster_Rig : Category := Rig.
Example roster_Rig_Forget_CMon : Rig ⟶ CMon := Rig_Forget_CMon.
Example roster_Rng : Category := Rng.
Example roster_Rng_Forget : Rng ⟶ Sets := Rng_Forget.
Example roster_Rng_Forget_Ab : Rng ⟶ Ab := Rng_Forget_Ab.
Example roster_CRng : Category := CRng.

(*
 Modules on both sides, and the bimodule record that justifies the
 right-module definition. 

 --------
 两边的模以及证明右模定义的双模记录。
*)
Example roster_RMod (R : RingObject) : Category := RMod R.
Example roster_RMod_Forget (R : RingObject) : RMod R ⟶ Sets :=
  RMod_Forget R.
Example roster_RMod_Forget_Ab (R : RingObject) : RMod R ⟶ Ab :=
  RMod_Forget_Ab R.
Example roster_ModR (R : RingObject) : Category := ModR R.
Example roster_Bimodule (R S : RingObject) : Type := Bimodule R S.

(*
 Vector spaces over a field, and the finite-dimensional refinement
 whose objects carry chosen coordinates. 

 --------
 域上的向量空间，以及有限维的细化，其对象具有选定的坐标。
*)
Example roster_Vct_F (F : FieldObject) : Category := Vct_F F.
Example roster_FdVect (F : FieldObject) : Category := FdVect F.
Example roster_FdVect_Forget (F : FieldObject) : FdVect F ⟶ Vct_F F :=
  FdVect_Forget F.

(*
 Fields.  The category and the determination of its monomorphisms
 are Instance/Field.v's; only the entry is recorded here. 

 --------
 域。其类别及其单态射的确定在 Instance/Field.v 中；这里只记录条目。
*)
Example roster_Field : Category := Field.
Example roster_Field_Forget : Field ⟶ Sets := Field_Forget.
Example roster_Field_Rng : Field ⟶ Rng := Field_Rng.

(* Representations of a group over a ring. / 关于环上群的表示。 *)
Example roster_Rep (K : RingObject) (G : GrpObject) : Category :=
  Rep K G.

(* Matrices over a rig, with Awodey's ℕ-matrix and Mac Lane's integer instantiations. / 在幂半环上的矩阵，包括 Awodey 的 ℕ 矩阵和 Mac Lane 的整数实例化。 *)
Example roster_Matr (R : RigObject) : Category := Matr R.
Example roster_Matr_N : Category := Matr_N.
Example roster_Matr_Z : Category := Matr_Z.

(* * ** The Mon residual: internal monoids in (Sets, ∏) / * ** Mon 残差：在 (Sets, ∏) 中的内部幺半群 *)

(*
 Theory/Algebra/Monoid/Hom.v defines [Mon] inside a section over an
 arbitrary monoidal category, so Mac Lane's roster entry Mon — THE
 category of monoids — has existed in the tree only as a section
 variable waiting for its base.  Instantiating it at [Sets] with the
 cartesian monoidal structure of Instance/Sets.v supplies the entry
 and names it.  This is not a new construction: Theory/Algebra/Rig.v
 already lands in exactly this category ([Rig_Forget_Mon], the
 multiplicative half of a rig), which the third example below records
 by having that functor typecheck at the new name. 

 --------
 Theory/Algebra/Monoid/Hom.v 在一个任意的单元范畴上的一个部分中定义了 [Mon]，因此 Mac Lane 的名录条目 Mon — 单子范畴 — 在树中仅以等待其基的部分变量存在。在 Instance/Sets.v 的笛卡尔单元结构下将其实例化为 [Sets] 提供了条目并命名它。这不是一个新的构造：Theory/Algebra/Rig.v 已经正好落在这个范畴中（[Rig_Forget_Mon]，一个环的乘法半部分），如下第三个示例所记录，通过使该函子在新名称下类型检查。
*)
Definition Mon_Sets : Category := @Mon Sets Sets_Product_Monoidal.

Definition Mon_Sets_Forget : Mon_Sets ⟶ Sets :=
  @Mon_Forget Sets Sets_Product_Monoidal.

Example roster_Mon_Sets : Category := Mon_Sets.
Example roster_Mon_Sets_Forget : Mon_Sets ⟶ Sets := Mon_Sets_Forget.
Example roster_Rig_Forget_Mon : Rig ⟶ Mon_Sets := Rig_Forget_Mon.

(*
 One pointer, and no comparison is owed here.  An object of
 [Mon_Sets] is an INTERNAL monoid in (Sets, ∏) — not assumed
 commutative — whereas [CMonObject] is a set-level COMMUTATIVE monoid
 presented as a record.  The two are the two halves of a rig, and
 Theory/Algebra/Rig.v projects onto each: the multiplicative half by
 [Rig_Forget_Mon] into [Mon_Sets], the additive half by
 [Rig_Forget_CMon] into [CMon].  A full dictionary between the
 internal and the set-level presentations belongs to whichever issue
 wants it; the roster needs only that both entries exist. 

 --------
 一点说明，这里无需比较。[Mon_Sets] 的对象是在 (Sets, ∏) 中的内部幺半群——不假定为交换性的——而 [CMonObject] 是以记录形式呈现的集合层面的交换幺半群。二者构成了一个环的两个部分，并且 Theory/Algebra/Rig.v 对每一部分都有对应投影：乘法部分由 [Rig_Forget_Mon] 投影到 [Mon_Sets]， 加法部分由 [Rig_Forget_CMon] 投影到 [CMon]。内部表示与集合层面表示之间的完整词典属于需要它的任一话题；登记表只需要两者都存在即可。
*)

(* * ** Order categories, and the Poset/Proset erratum / * ** 顺序类别，以及偏序集/前序集勘误 *)

(*
 ONE preorder as a thin category (Mac Lane's Preord is [Ord]).  The
 witness is (ℕ, ≤). 

 --------
 作为薄范畴的一个前序（Mac Lane 的 Preord 是 [Ord]）。证据是 (ℕ, ≤)。
*)
Example roster_Proset {A : Type} {R : A → A → Prop}
  (P : RelationClasses.PreOrder R) : Category := Proset P.
Example roster_Proset_nat : Category := Proset PeanoNat.Nat.le_preorder.

(*
 The category whose OBJECTS are posets — Riehl 1.1.3's Poset clause.
 Instance/Poset.v's identically-spelled [Poset] is NOT this: it is
 [Proset] under another name, antisymmetry discarded.  See the
 erratum in the header. 

 --------
 其对象是偏序集的范畴 — Riehl 1.1.3 的 Poset 条款。
 Instance/Poset.v 中拼写相同的 [Poset] 不是这个：它是 
 另一个名字下的 [Proset]，舍弃了反对称性。见页眉的勘误。
*)
Example roster_Pos : Category := Pos.
Example roster_Pos_Forget : Pos ⟶ Sets := Pos_Forget.

(* * ** Categories of categories, shapes and graphs / * ** 类别的类别、形状和图表 *)

Example roster_Cat : Category := Cat.
Example roster_StrictCat : Category := StrictCat.

(*
 Graphs, in Riehl's sense: the category of quivers.  Its three
 candidate underlying-set functors are Construction/Free/Quiver/
 Concrete.v's, and which of them is faithful is the content there. 

 --------
 在 Riehl 的意义上，图：箭头图的范畴。它的三个候选底层集合函子是 Construction/Free/Quiver/Concrete.v 的，哪个是忠实的就是其中的内容。
*)
Example roster_QuiverCategory : Category := QuiverCategory.
Example roster_QuiverVertices : QuiverCategory ⟶ Sets := QuiverVertices.
Example roster_QuiverArrows : QuiverCategory ⟶ Sets := QuiverArrows.

(*
 The simplicial category Δ, with its wide inclusion into finite
 sets — faithful, and provably not full. 

 --------
 单纯形范畴 Δ 及其对有限集合的广义包含——忠实的，并且可证明不是满射的。
*)
Example roster_Simplex : Category := Simplex.
Example roster_Simplex_FinSet : Simplex ⟶ FinSet := Simplex_FinSet.

(*
 Mac Lane's §I.1 arrows-only presentation, and the passage from it
 back to a category. 

 --------
 Mac Lane 的 §I.1 仅箭头表示法，以及从中返回到一个范畴的过程。
*)
Example roster_Metacategory : Type := Metacategory.
Example roster_Category_from_Metacategory (M : Metacategory) : Category :=
  Category_from_Metacategory M.

(*
   * ** Initial and terminal objects across the roster

   Riehl, "Category Theory in Context", §1.6 Example 1.6.15 (printed
   p. 38) [riehl:1.6:example15]: the standard categories surveyed for
   their initial and terminal objects.  The entries are cited, not
   rebuilt — each is an instance already registered in the file that
   owns the category — and the two genuinely negative clauses are the
   interesting ones.

   THE PATTERN.  In the algebraic entries the two coincide: the
   trivial object is a ZERO object, which is what [ZeroObject] records
   and what makes the zero morphism available.  In [Sets] and [Cat]
   they differ (the empty set/category against the singleton).  In
   [Top] they differ AND there is provably no zero object.  In [Field]
   NEITHER exists.

   THE UNITAL-RING DISCRIMINATION.  ℤ is initial in [Rng] and the
   zero ring is terminal, both exhibited below.  What makes this the
   discriminating case in the books — that dropping the unit from the
   morphism notion changes the answer — IS now checkable: [Rg], the
   category of non-unital rings, is Instance/Rg.v, and there the zero
   rng is BOTH initial and terminal, since a rng homomorphism is not
   required to preserve 1.  So [Rg] has a zero object, and [Rng]
   does not -- the latter being
   Structure/Kernel/Universal/Examples.v's [Rng_no_zero_object].
   Instance/Rg.v's [Rng_Rg_zero_object_contrast] pairs the zero object
   with the sharper elementary fact that no unital homomorphism runs
   from the zero ring to Z, which is what forces terminal and initial
   apart here; this roster is not extended to [Rg] itself, which would
   pull Instance/Rg.v into a file that already carries most of the
   library.  The contrast is no longer prose. 

   --------
   * ** 名单中的初始对象和终端对象

   Riehl，《情境中的范畴论》，§1.6 示例 1.6.15（印刷第38页）  [riehl:1.6:example15]：对其初始对象和终端对象进行概述的标准范畴。条目被引用，而非重新构建——每个条目都是已在拥有该范畴的文件中注册的实例——真正的两个否定条款才是有趣的。

   模式。在代数条目中，这两者是一致的：平凡对象是零对象，这正是 [ZeroObject] 记录的，同时也使零态射可用。在 [Sets] 和 [Cat] 中，它们不同（空集/范畴与单元素集）。在 [Top] 中，它们不同并且可证明不存在零对象。在 [Field] 中，二者都不存在。单位环区分。ℤ 在 [Rng] 中是初对象，而零环是终对象，如下所示。使得这在书中成为区分性案例的原因——从态射概念中去掉单位会改变答案——现在可以验证：[Rg]，即非单位环的范畴，是 Instance/Rg.v 中的实例，其中零环同时是初对象和终对象，因为 rng 同态不要求保持 1。因此 [Rg] 有零对象，而 [Rng] 没有——后者是 Structure/Kernel/Universal/Examples.v 中的 [Rng_no_zero_object]。Instance/Rg.v 的 [Rng_Rg_zero_object_contrast] 将零对象与更精确的基本事实配对，即没有一个有单位元的同态从零环映射到 Z，这正是迫使这里的终对象和初对象区分的原因；这个列表并没有扩展到 [Rg] 本身，否则会将 Instance/Rg.v 拉入一个已经包含库大部分内容的文件中。对比不再是散文。
*)

(* Sets and the strict variant: the two differ. / 集合和严格变体：两者不同。 *)
Example roster_Sets_Terminal : @Terminal Sets := Sets_Terminal.
Example roster_Sets_Initial : @Initial Sets := Sets_Initial.
Example roster_Coq_Terminal : @Terminal Coq := Coq_Terminal.
Example roster_Coq_Initial : @Initial Coq := Coq_Initial.
Example roster_FinSet_Terminal : @Terminal FinSet := FinSet_Terminal.
Example roster_FinSet_Initial : @Initial FinSet := FinSet_Initial.

(*
 Pointed sets: the singleton is a genuine zero object, which is what
 distinguishes Set_* from Set. 

 --------
 有基点的集合：单元素集合是真正的零对象，这也是 Set_* 与 Set 区别所在。
*)
Example roster_PointedSets_Zero : ZeroObject PointedSets :=
  PointedSets_Zero.

(* The algebraic entries, where initial and terminal coincide. / 代数条目，其中起点和终点重合。 *)
Example roster_CMon_Zero : ZeroObject CMon := CMon_Zero.
Example roster_Grp_Zero : ZeroObject Grp := Grp_Zero.
Example roster_Ab_Zero : ZeroObject Ab := Ab_Zero.
Example roster_RMod_Zero (R : RingObject) : ZeroObject (RMod R) :=
  RMod_Zero R.

(*
 Rings: ℤ initial, the zero ring terminal — and they do NOT coincide,
 which is why no [ZeroObject Rng] is cited.  The non-unital contrast
 named in the disclosure above is proved in Instance/Rg.v
 ([Rg_Zero], [Rng_Rg_zero_object_contrast]). 

 --------
 环：ℤ 是初始的，零环是终极的——它们并不重合，这就是为什么没有引用 [ZeroObject Rng]。在上述披露中提到的无单位对比在 Instance/Rg.v 中得以证明（[Rg_Zero]，[Rng_Rg_zero_object_contrast]）。
*)
Example roster_Rng_Terminal : @Terminal Rng := Rng_Terminal_zero.
Example roster_Rng_Initial : @Initial Rng := Rng_Initial_Z.

(* Relations: a zero object, by self-duality. / 关系：一个零对象，由自对偶性。 *)
Example roster_Rel_Zero : ZeroObject Rel := Rel_Zero.

(* Categories of categories. / 类别的类别。 *)
Example roster_Cat_Terminal : @Terminal Cat := Cat_Terminal.
Example roster_Cat_Initial : @Initial Cat := Cat_Initial.
Example roster_StrictCat_Terminal : @Terminal StrictCat :=
  StrictCat_Terminal.

(*
 FIELDS HAVE NEITHER.  The two theorems are Instance/Field.v's; the
 separating pair is ℚ against F₂, characteristic 0 against
 characteristic 2, and both proofs are constructive.  The
 object-level readings there say it without choosing a candidate: no
 object of [Field] is initial and none is terminal. 

 --------
 域都没有。 这两个定理来自 Instance/Field.v； 区分的实例是一阶有理数 ℚ 对比 F₂，特征 0 对比特征 2，两个证明都是构造性的。 那里的对象级解读在不选择候选对象的情况下说明了这一点：没有 [Field] 的对象是初始对象，也没有是终对象。
*)
Example roster_Field_no_initial : @Initial Field → False :=
  Field_no_initial.
Example roster_Field_no_terminal : @Terminal Field → False :=
  Field_no_terminal.

(*
   * ** SEGREGATED SECTION 1: topological entries

   The topology itself is axiom-free; see the AXIOMS paragraph.  Every
   constant in the first half of this section is Closed, and the four
   at the end — the homotopy quotients, which need the unit
   interval — are where the standard library's reals axioms enter.
   The stratification note in the header explains why [Top_Forget]
   lands in a HIGHER [Sets] than the one the algebraic entries use,
   and why the adjunctions are transposition isomorphisms rather than
   packaged [Adjunction] records. 

   --------
   * ** 分隔部分 1：拓扑条目

   拓扑本身是无公理的；参见公理段落。本节前半部分的每个常量都是闭合的，而结尾的四个——同伦商，需要单位区间——是标准库实数公理介入的地方。标题中的分层注释解释了为什么 [Top_Forget] 位于比代数条目使用的那个更高的 [Sets]，以及为什么伴随是换位同构而不是打包的 [Adjunction] 记录。
*)

Example roster_Top : Category := Top.
Example roster_Top_Forget : Top ⟶ Sets := Top_Forget.
Example roster_Top_Discrete : Sets ⟶ Top := Top_Discrete.
Example roster_Top_Indiscrete : Sets ⟶ Top := Top_Indiscrete.

(*
 Top's initial and terminal objects differ, and — unlike every
 algebraic entry above — there is provably no zero object: the empty
 space and the point are not isomorphic, and Instance/Top.v proves
 the non-existence outright rather than leaving it to inspection. 

 --------
 Top 的初对象和终对象不同，并且——与上面每一个代数条目不同——可以证明不存在零对象：空空间和点不同构，Instance/Top.v 直接证明了其不存在，而不是留给检查。
*)
Example roster_Top_Terminal : @Terminal Top := Top_Terminal.
Example roster_Top_Initial : @Initial Top := Top_Initial.
Example roster_Top_no_zero : @ZeroObject Top → False := Top_no_zero_object.

(* The separation full subcategories. [CompactHausdorffSpaces] is the roster entry; its forgetful/monadicity story is disclosed out of scope in the header. / 分离完全子范畴。[CompactHausdorffSpaces] 是名册条目；它的遗忘/单子性故事在头部超出范围的地方被揭示。 *)
Example roster_HausdorffSpaces : Category := HausdorffSpaces.
Example roster_CompactHausdorffSpaces : Category :=
  CompactHausdorffSpaces.

(*
 Top_*: based spaces and based maps.  Still axiom-free — a basepoint
 costs nothing. 

 --------
 Top_*：基于空间和基于映射。仍然是无公理的——基点不花任何代价。
*)
Example roster_Top_pointed : Category := Top_pointed.

(*
 THE FOUR REALS-CARRYING CONSTANTS OF THIS FILE.  Toph and Toph_*:
 spaces and homotopy classes of maps, as hom-congruence quotients of
 [Top] and [Top_pointed], with their identity-on-objects
 projections.  The homotopies are parametrized by the unit interval
 of Instance/Top/Interval.v, which is built over the standard library
 reals; that is the whole of the dependency. 

 --------
 本文件的四个实数常量。Toph 和 Toph_*：映射的空间和同伦类，作为 [Top] 和 [Top_pointed] 的同构余商，并带有它们的对象恒等投影。同伦由 Instance/Top/Interval.v 的单位区间参数化，该区间是基于标准库实数构建的；这就是整个依赖项。
*)
Example roster_Toph : Category := Toph.
Example roster_TophProj : Top ⟶ Toph := TophProj.
Example roster_Toph_pointed : Category := Toph_pointed.
Example roster_Toph_pointed_Proj : Top_pointed ⟶ Toph_pointed :=
  Toph_pointed_Proj.

(*
   * ** SEGREGATED SECTION 2: universal algebra (functional
   extensionality)

   Instance/Comp.v is a Leibniz-equality development and invokes
   [functional_extensionality] (the caveat Instance/Ab.v's header
   records).  It does NOT invoke it everywhere: the signature and
   category machinery below is axiom-free, and the axiom is spent in
   [GroupEq]'s naturality proof alone, so only the last two constants
   of this file carry it.  References go through the module alias [UA]
   rather than an [Import], because that file's record fields
   ([carrier], [eq], [map]) would shadow the library's. 

   --------
   * ** 分隔部分 2：通用代数（函数外延性）

   Instance/Comp.v 是一个莱布尼茨等式开发，并调用了 [functional_extensionality]（Instance/Ab.v 的头记录中的注意事项）。它并没有在所有地方调用它：下面的签名和范畴机制是无公理的，并且该公理仅在 [GroupEq] 的自然性证明中使用，因此本文件只有最后两个常量携带它。引用通过模块别名 [UA] 进行，而不是 [Import]，因为该文件的记录字段（[carrier]、[eq]、[map]）会遮蔽库的字段。
*)

Module UA := Category.Instance.Comp.UniversalAlgebra.

(*
 The category of algebras for an operation signature — the equational
 fragment of Model_T.  Axiom-free. 

 --------
 运算符号的代数范畴——Model_T 的方程片段。无公理。
*)
Example roster_Algs (S : UA.OpSignature) : Category := @UA.Algs S.
Example roster_GroupOp : UA.OpSignature := UA.GroupOp.

(*
 THE TWO FUNEXT-CARRYING CONSTANTS OF THIS FILE.  The group variety,
 at the level Instance/Comp.v supplies it: a signature, its
 equations, and the TYPE of algebras satisfying them.  There is no
 category of [Group]s there — [Algs] is taken over an operation
 signature alone, with the equations imposed objectwise — so the
 variety is recorded here as the type it is, and the roster's
 "category of groups" entry is Instance/Grp.v's [Grp] above.  The
 witness is that file's ℤ/2 under exclusive or.

 SUPERSEDED IN PART by #440: Instance/Variety.v now forms the variety
 as a genuine category, [GroupVariety], with [GroupVariety_Bool] the
 same ℤ/2 witness as an OBJECT of it, and
 Instance/Variety/GroupComparison.v gives a full and faithful
 comparison with [Grp] (not an isomorphism — the carriers are Leibniz
 types where [Grp]'s are setoids).  The entry below is left at the TYPE
 it always named, and no [Require] is added here, so that this file's
 closure is unchanged; what is no longer true is the sentence "there is
 no category of [Group]s there", read as a claim about the tree rather
 than about Instance/Comp.v. 

 --------
 本文件的两个携带 FUNEXT 的常量。该群体多样性在 Instance/Comp.v 文件中提供：一个签名、它的方程以及满足这些方程的代数类型。那里没有 [Group] 的范畴——[Algs] 仅在操作签名上进行处理，对象顺序地施加方程——因此多样性在此记录为它本身的类型，而花名册的“群的范畴”条目则是 Instance/Grp.v 文件中的 [Grp]。证明对象是该文件下的 ℤ/2 及其异或操作。部分被 #440 取代：Instance/Variety.v 现在将该品类形成一个真正的类别，[GroupVariety]，而 [GroupVariety_Bool] 是其作为对象的相同 ℤ/2 证明，Instance/Variety/GroupComparison.v 提供了与 [Grp] 的完整且忠实的比较（不是同构——载体是莱布尼茨类型，而 [Grp] 是集合类）。如下条目仍保持其一直命名的类型，这里没有添加 [Require]，因此此文件的闭包未改变；不再成立的是句子“那里不存在 [Group] 的类别”，应理解为关于树的声明，而不是关于 Instance/Comp.v 的声明。
*)
Example roster_Group_variety : Type := UA.Group.
Example roster_Group_variety_witness : UA.Group := UA.Bool.
