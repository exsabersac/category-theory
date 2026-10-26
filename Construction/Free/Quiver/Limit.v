Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Theory.Diagram.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(* * * Cones and limits over a diagram of graph shape / * * 图形形状图的锥和极限 *)

(*
 Book:    Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 Springer GTM 5, 1998, Section III.4, printed p. 71
 Catalog: maclane:III.4:def8  (“diagram of graph shape and its limit”)
 maclane:III.4:remark6 (“graph-shaped limits reduce to functor
 limits via the free category”), both in
 doc/plan/books/maclane/inventory/III.json
 nLab:    https://ncatlab.org/nlab/show/cone
 nLab:    https://ncatlab.org/nlab/show/free+category

 CITED BY LOCATION; the printed text was not consulted.  Everything
 attributed to Mac Lane below paraphrases the CATALOG'S summaries, which
 are themselves paraphrases and not the book's wording.

 WHAT WAS ALREADY IN TREE, AND WHAT IS ADDED HERE.  A DIAGRAM OF GRAPH
 SHAPE -- a graph morphism D : G -> U C into the underlying graph of C --
 is Theory/Diagram.v's [Diagram G C := QuiverHomomorphism G
 (QuiverOfCat C)], and this file adds no second definition of it; nor does
 it reprove the FACTORIZATION half of remark 6, which is
 Construction/Free/Quiver.v's [UniversalArrowQuiverCat] (every D
 factors through the unit as a functor on the free category, uniquely up
 to [StrictCat]'s hom-equivalence) together with Theory/Diagram.v's
 [FunctorOfDiagram], its [DiagramOfFunctor] and the two round trips
 between them -- all cited, none restated.  What was missing is the rest
 of def 8: the CONE over a graph diagram and its LIMIT, and then remark
 6's clause that limits and limiting cones for the two presentations
 “correspond exactly”.

 THE ABSENCE, SCOPED TO WHAT WAS SEARCHED, AND MEASURED BEFORE THIS FILE
 EXISTED.  [grep -icE 'cone|limit'] returned 0 on
 Construction/Free/Quiver.v and on each of the five siblings that were
 then under Construction/Free/Quiver/ (Concrete.v, Constructions.v,
 Coproduct.v, Examples.v, Presented.v), and Theory/Diagram.v's three hits
 are all inside comments.  A shape search
 [rg -g '*.v' 'GraphCone|graph_cone|gvertex'] over the whole tree returned
 nothing.  The claim is scoped to those two searches: no cone over a
 quiver homomorphism was found anywhere by them.

 NO FUNCTORIALITY IS NEEDED, AND THIS FILE SHOWS EXACTLY WHERE THAT SHOWS
 UP.  Mac Lane's cone assigns to each NODE i of G an arrow mu_i : c -> D i,
 subject to one equation per graph EDGE h : i -> j, namely
 D h ∘ mu_i = mu_j; the catalog's own summary calls it “a natural
 transformation from the constant, using composition in C but not in the
 domain”.  A graph has no composition and no identities, so there is
 nothing further for the cone to respect.  In [AGraphCone] below that is
 the single field [gcone_coherence], quantified over [edges x y] -- ONE
 TRIANGLE PER EDGE.  Contrast [ACone] (Structure/Cone.v), whose
 [cone_coherence] is quantified over [x ~{J}~> y]; over a free category
 those morphisms are PATHS of every length, so a functor cone carries ONE
 TRIANGLE PER ARROW.  The two witnesses below make that gap concrete.

 THE CORRESPONDENCE, AND WHICH HALF COSTS ANYTHING.  Passing a functor cone
 DOWN to a graph cone ([AGraphCone_of_ACone]) is RESTRICTION to one-edge
 paths: instantiate the functor cone's coherence at [tlist_singleton e]
 (Lib/TList.v) and remove the one identity a singleton path contributes.
 Passing a graph cone UP ([ACone_of_AGraphCone]) is EXTENSION ALONG PATHS,
 and it is the file's only induction over a path: [gcone_dpath] proves
 [dpath D p ∘ mu_x ≈ mu_y] for a path of ARBITRARY length by induction on
 the [tlist], each step spending one instance of [gcone_coherence] and one
 [comp_assoc].

 STRENGTHS, MEASURED RATHER THAN GUESSED.

 (1) APEXES AND LEGS SURVIVE BOTH PASSAGES ON THE NOSE.  Pinned by the four
 [eq_refl] Examples [gcone_apex_fwd], [gcone_leg_fwd],
 [gcone_apex_bwd], [gcone_leg_bwd], and by the two round-trip Examples
 [gcone_round_graph] and [gcone_round_cone].  Neither passage touches
 the leg family; each rebuilds only the coherence field.

 (2) THE WHOLE-RECORD ROUND TRIPS ARE REFUTED AT [eq_refl].  All FOUR
 records involved ([AGraphCone], [GraphCone], [ACone], [Cone]) --
 an earlier draft wrote “both” -- have primitive projections with
 eta, so record equality reduces to
 field equality -- and the coherence fields do not converge, [≈] being
 [crelation]-valued here, so those fields are DATA and the rebuilt
 proof is a different term.  Measured for [AGraphCone_of_ACone
 (ACone_of_AGraphCone N)], for [ACone_of_AGraphCone
 (AGraphCone_of_ACone N)] and for [GraphCone_of_Cone
 (Cone_of_GraphCone N)].  A FOURTH, [Cone_of_GraphCone
 (GraphCone_of_Cone N)], is refuted the same way and was omitted from
 that list; it is covered obliquely by the [≈]-level
 [Cone_of_GraphCone_round].  This file ships no [Fail] probe, so all
 four are stated as measurements and pinned nowhere -- and
 Test/ProbeQuiverLimit332.v, which accompanies this issue, does not
 pin them either and says so.  What IS
 delivered is the [≈]-level [Cone_of_GraphCone_round], through
 Structure/Cone.v's [AConeEquiv], which compares legs only.

 (3) AT THE LIMIT LEVEL THE CORRESPONDENCE COSTS NOTHING.  [graph_limitcone]
 and [limitcone_graph_limit] are supplied by [:=] with NO TACTIC and no
 obligation: the two [∃!] statements are CONVERTIBLE, because apex and
 every leg agree on the nose and [obj[FreeOnQuiver G]] IS [nodes G].
 All the proof content of remark 6 sits in the cone-level passages, and
 none of it in the limit-level ones.

 (4) [dpath D p] IS NOT [fmap[FunctorOfDiagram D] p] AT A VARIABLE PATH.
 Measured, and the cause is that [dpath] (Theory/Diagram.v) is a
 [Fixpoint] while [InducedFunctor]'s arrow action
 (Construction/Free/Quiver.v) is elaborated as a [tlist'_rect], so
 the two are different terms; Theory/Diagram.v's [dpath_fmap]
 relates them at [≈], and that is what [ACone_of_AGraphCone] and
 [AGraphCone_of_ACone] both consume.  At a ONE-EDGE path they DO agree
 definitionally, pinned here as [dpath_singleton_is_fmap].

 NON-VACUITY: TWO WITNESSES MAKING TWO DIFFERENT POINTS, both over quivers
 that ALREADY EXIST in Theory/Diagram.v -- no new shape is drawn.

 (a) A REAL LIMIT.  Over [TriangleQuiver] (Theory/Diagram.v) -- three
 nodes with edges X->Y, Y->Z and X->Z -- take the diagram whose direct
 edge is LITERALLY the composite, [TriangleDiagram u v (v ∘ u)].  Then
 the apex [p] with legs [id], [u], [v ∘ u] is a graph cone
 ([TriangleGraphCone]) and [triangle_graph_limit] proves it a LIMITING
 one, over an ARBITRARY category and arbitrary [u] and [v]: the
 mediator out of a competing graph cone is that cone's own leg at
 [TrX], its three triangles are [id_left] together with the coherence
 instances at the edges X->Y and X->Z, and uniqueness is [id_left]
 again.  The coherence instance at Y->Z is never spent.

 (b) THE NO-FUNCTORIALITY POINT, EXHIBITED.  The triangle shape has TWO
 DISTINCT parallel arrows X->Z in its free category -- [tri_via_Y] of
 length two and [tri_direct] of length one, proved distinct by
 Theory/Diagram.v's [tri_via_Y_neq_direct], cited and not
 reproved.  READ THE TWO DIFFERENTLY, and an earlier draft of this
 paragraph did not: [tri_via_Y] is the GENUINE no-functoriality
 instance -- it is a composite, no cone field mentions it, and its
 triangle is reached only by the induction in [gcone_dpath].
 [tri_direct] is a SINGLETON path on an actual edge of the shape, so
 the cone's own [gcone_coherence] field at that edge IS its triangle,
 modulo the one [id_left] that [dpath] leaves on a one-edge path --
 which is exactly what paragraph (a) above spends at the X->Z edge,
 and what the limit proof spends.  The earlier draft said a graph
 cone “states a triangle for NEITHER of them”, which contradicts
 paragraph (a) and is false of [tri_direct].  Both
 [tri_gcone_at_via_Y] and [tri_gcone_at_direct] are nonetheless
 routed uniformly through [gcone_leg_dpath], hence [gcone_dpath];
 for [tri_direct] that route is not the cheapest one.  The walking
 loop (Theory/Diagram.v) sharpens this to the extreme case:
 [loop_gcone] builds a graph cone from the SINGLE
 equation [e ∘ psi ≈ psi], and [loop_gcone_every_path] then discharges
 the triangle at [loop_path n] for EVERY [n], those paths being
 pairwise distinct arrows of the free category
 ([loop_paths_distinct]).  One field, one triangle for each of
 infinitely many arrows.

 (c) COMPUTATION.  The triangle witness is instantiated in [Coq]
 (Instance/Coq.v) at [u := S] and [v := Nat.even]: the apex, the three
 legs, and the mediator out of a probe cone all reduce, pinned by
 [eq_refl] ([coq_tri_apex] through [coq_probe_Y]).

 WHAT IS NOT DELIVERED, scoped to this file.

 * No dual.  There is no graph cocone and no colimit of a graph diagram;
 nothing here is stated at [C^op].
 * No category of graph cones, hence no rendering of the limit as a
 terminal object, and no setoid on [AGraphCone] mirroring
 Structure/Cone.v's [AConeEquiv].  Consequently there is no
 essential-uniqueness statement for graph limits: no “any two limiting
 graph cones are canonically isomorphic”, with or without legs.
 * No preservation, reflection or creation of graph limits, and no
 analogue of Structure/Limit/Preservation.v's [PreservesLimit].
 * [graph_limit_IsALimit] is offered only as the apex-only READING of the
 cone-level statement.  It is the weaker of the two -- its legs are
 unconstrained -- and NO separation between them is proved here, so
 “strictly weaker” is not claimed.
 * Nothing connects to Theory/Diagram.v's [Commutative], which is
 never invoked below, and no commutativity theorem of that file is
 consumed.  The triangle witness does draw a commuting triangle -- its
 direct edge is the composite BY DEFINITION, and that choice is what
 makes the apex a limit -- but it is used as a definitional unfolding,
 never through the predicate.
 * The loop witness exhibits the no-functoriality point but NOT a limit:
 the limit of a loop diagram is the equalizer of [e] and [id], and no
 equalizer is constructed here.
 * The computing witnesses at the end of the file are the sole reason
 this module Requires Category.Instance.Coq, which pulls that file's
 own closure (Theory.Monad, Functor.Strong, Structure.BiCCC and so
 on) into this module's.  Nothing but the probe Requires this file,
 so the weight is contained; it is disclosed rather than split, and
 the precedent for splitting on exactly this ground is the
 Structure/Limit/Power.v / Power/Hom.v division.
 * No [GraphLimit] instance is produced for any category from a
 completeness hypothesis; there is no “C complete implies every graph
 diagram over C has a graph limit”.
 * No universe measurement is offered IN THIS FILE.  Nothing below
 claims which levels these constants identify or leave free.  Scope
 that precisely: the companion Test/ProbeQuiverLimit332.v DOES make
 one measurement, that [Diagram] identifies C's hom and proof
 universes (which is why [AGraphCone] displays them identified where
 the [ACone] it mirrors displays them apart).  That pin is the
 DONOR's -- Theory/Diagram.v opens its section with an
 unannotated [Context {C : Category}], so it is a minimization
 artifact of the kind Construction/Free/Quiver/Examples.v's header
 records, repairable upstream with explicit binders, and NOT
 inherent content of this development. 

 --------
 书籍：Mac Lane，《为工作的数学家准备的范畴论》，第2版，Springer GTM 5，1998年，第III.4节，印刷页71
 目录：maclane:III.4:def8（“图形形状及其极限的图示”）
 maclane:III.4:remark6（“图形形状的极限通过自由范畴归约为函子极限”），均在 doc/plan/books/maclane/inventory/III.json
 nLab: https://ncatlab.org/nlab/show/cone
 nLab: https://ncatlab.org/nlab/show/free+category

 引用来源位置；未查阅印刷文本。以下所有归因于Mac Lane的内容均为目录摘要的释义，而该目录摘要本身就是对书中原文的释义。树中已经存在的内容，以及在这里添加的内容。图的一个示意图
 形状——一个图同态 D : G -> U C 到 C 的基础图——
 是 Theory/Diagram.v 中的 [Diagram G C := QuiverHomomorphism G (QuiverOfCat C)]，本文件没有添加它的第二个定义；也没有重证明 remark 6 的分解部分，该部分是 Construction/Free/Quiver.v 中的 [UniversalArrowQuiverCat]（每个 D 都可以通过自由范畴上的单位作为函子唯一分解，直到 [StrictCat] 的同态等价）以及 Theory/Diagram.v 中的 [FunctorOfDiagram]，其 [DiagramOfFunctor] 以及它们之间的两个往返——均已引用，未重新陈述。缺失的是定义 8 的其余部分：图示意图上的 CONE 及其 LIMIT，然后是 remark 6 中的条款，即两个表示的极限与极限锥“完全对应”。不存在性，限定于所搜索的内容，并在此文件存在之前测量。[grep -icE 'cone|limit'] 在 Construction/Free/Quiver.v 以及当时位于 Construction/Free/Quiver/ 下的五个兄弟文件（Concrete.v、Constructions.v、Coproduct.v、Examples.v、Presented.v）上返回 0，而 Theory/Diagram.v 的三次命中都在注释内。一种形状搜索 [rg -g '*.v' 'GraphCone|graph_cone|gvertex'] 对整个树进行搜索也没有返回任何结果。该声明限定在这两次搜索：它们在任何地方都未找到关于 quiver 同态的圆锥。不需要函子性，这个文件准确地展示了这一点出现的位置。Mac Lane 的锥将图 G 的每个节点 i 分配给一条箭头 mu_i : c -> D i，并且对于图中的每条边 h : i -> j，必须满足一个方程，即 D h ∘ mu_i = mu_j；该目录自身的摘要称其为“从常量出发的自然变换，使用 C 中的组合但不在定义域中”。图没有组合也没有恒等，因此锥不需遵守其他任何规则。在下方的 [AGraphCone] 中，这是单个字段 [gcone_coherence]，量化于 [edges x y] —— 每条边一个三角形。对比 [ACone] (Structure/Cone.v)，其 [cone_coherence] 被量化于 [x ~{J}~> y]；在自由范畴上，这些态射是任意长度的路径，因此函子锥包含每条箭头一个三角形。下面的两个例子使这一差距具体化。对应关系，哪个成本的一半。将函子锥向下传递到图锥（[AGraphCone_of_ACone]）是对单边路径的限制：在[tlist_singleton e]（Lib/TList.v）处实例化函子锥的相干性，并去掉单路径贡献的一个恒等。将图锥向上传递（[ACone_of_AGraphCone]）是沿路径的扩展，这是文件中唯一的路径归纳：[gcone_dpath] 通过对[tlist]归纳，证明任意长度路径的[dpath D p ∘ mu_x ≈ mu_y]，每一步消耗一个[gcone_coherence]的实例和一个[comp_assoc]。 

 优势，通过测量而非猜测。(1) 顶端和腿部在鼻子的两个通道中都存活。由四个实例 [eq_refl]、[gcone_apex_fwd]、[gcone_leg_fwd]、[gcone_apex_bwd]、[gcone_leg_bwd] 固定，以及两个往返实例 [gcone_round_graph] 和 [gcone_round_cone] 固定。没有一个通道接触到腿部系列；每个通道只重建相干场。(2) 全纪录的往返在 [eq_refl] 被驳斥。涉及的所有四个记录（[AGraphCone]、[GraphCone]、[ACone]、[Cone]）——早期草稿写成了“both”——都有带η的原始投影，所以记录相等性归结为字段相等性——而一致性字段不收敛，这里 [≈] 的值为 [crelation]，因此这些字段是数据，并且重建的证明是一个不同的项。分别为 [AGraphCone_of_ACone (ACone_of_AGraphCone N)]、[ACone_of_AGraphCone (AGraphCone_of_ACone N)] 和 [GraphCone_of_Cone (Cone_of_GraphCone N)] 测量。第四个 [Cone_of_GraphCone (GraphCone_of_Cone N)] 以相同方式被驳斥，并被从列表中省略；它间接地被 [≈] 级别的 [Cone_of_GraphCone_round] 覆盖。该文件不附带 [Fail] 探针，因此所有四个都被标记为测量值，并且未固定在任何地方——随此问题附带的 Test/ProbeQuiverLimit332.v 也没有固定它们，并且明确说明了这一点。实际交付的是 [≈] 级别的 [Cone_of_GraphCone_round]，通过 Structure/Cone.v 的 [AConeEquiv]，只比较腿部。

 (3) 在极限级别，对应什么都不花费。[graph_limitcone] 和 [limitcone_graph_limit] 由 [:=] 提供，无策略且无义务：这两个 [∃!] 声明是可转换的，因为顶点和每条腿都在尖端上达成一致，并且 [obj[FreeOnQuiver G] 就是 [nodes G]。备注 6 的所有证明内容都位于圆锥级段落中，而不在极限级段落中。(4) [dpath D p] 不是 [fmap[FunctorOfDiagram D] ，在一个可变路径下测量，原因是 [dpath]（Theory/Diagram.v）是一个 [Fixpoint]，而 [InducedFunctor] 的箭头作用（Construction/Free/Quiver.v）被阐述为一个 [tlist'_rect] ，所以两者是不同的项；Theory/Diagram.v 的 [dpath_fmap] 在 [≈] 上将它们关联起来，这就是 [ACone_of_AGraphCone] 和 [AGraphCone_of_ACone] 都使用的。在单边路径上，它们在定义上确实一致，这里固定为 [dpath_singleton_is_fmap]。

 非空性：两个证据提出两个不同的点，都在 Theory/Diagram.v 中已存在的 quiver 上——没有绘制新的形状。(a) 一个真正的极限。在  [TriangleQuiver] 之上 (Theory/Diagram.v) —— 三个节点，边为 X->Y、Y->Z 和 X->Z —— 取直接边字面上等于复合的图 [TriangleDiagram u v (v ∘ u)]。然后顶点 [p]，边为 [id]、[u]、[v ∘ u]，是一个图锥 ([TriangleGraphCone])，而 [triangle_graph_limit] 证明它是一个极限图锥，在任意范畴及任意 [u] 和 [v] 上：竞争图锥出的中介是该锥在 [TrX] 的自身边，它的三个三角形是 [id_left] 以及在 X->Y 和 X->Z 边上的相干实例，唯一性再次是 [id_left]。在 Y->Z 上的相干实例从未被消耗。(b) 展示“无函子性”点。该三角形在其自由范畴中有两条不同的平行箭头 X->Z——长度为二的 [tri_via_Y] 和长度为一的 [tri_direct]，通过 Theory/Diagram.v 中的 [tri_via_Y_neq_direct] 证明它们不同，该证明被引用但未重新证明。以不同的方式阅读这两个箭头，而本段的早期草稿没有这样做：[tri_via_Y] 才是真正的无函子性实例——它是一个复合物，没有圆锥场提到它，并且它的三角形只能通过 [gcone_dpath] 中的归纳法到达。[tri_direct] 是形状实际边上的一个单例路径，因此锥体在该边上的 [gcone_coherence] 字段就是它的三角形，模去 [dpath] 在一条单边路径上留下的那一个 [id_left]——这正是上面(a)段落在 X->Z 边上所处理的，也是极限证明所处理的。早期草稿说图锥“对它们两者都不表示一个三角形”，这与(a)段落矛盾，而且对于 [tri_direct] 是错误的。尽管如此，[tri_gcone_at_via_Y] 和 [tri_gcone_at_direct] 都通过 [gcone_leg_dpath] 均匀路由，因此 [gcone_dpath]；对于 [tri_direct]，那条路径并不是最便宜的。步行循环（Theory/Diagram.v）将这一点锐化到了极端情况：
 [loop_gcone] 从单一方程 [e ∘ psi ≈ psi] 构建一个图锥，然后 [loop_gcone_every_path] 对每一个 [n] 在 [loop_path n] 释放三角形，这些路径是自由范畴（[loop_paths_distinct]）的两两不同箭头。每个箭头对应一个场和一个三角形，而箭头数量无限。

 (c) 计算。三角形见证在 [Coq]（Instance/Coq.v）的 [u := S] 和 [v := Nat.even] 中被实例化：顶点、三条边以及探针锥出的中介全部归约，由 [eq_refl]（从 [coq_tri_apex] 到 [coq_probe_Y]）固定。

 未交付的内容，限定于此文件。* 没有对偶。没有图的余锥，也没有图示的余极限；在  [C^op] 处没有说明。* 没有图锥的范畴，因此也没有将极限表示为终对象的方法，也没有在  [AGraphCone] 上的集合类比 Structure/Cone.v 的  [AConeEquiv] 。因此，没有图极限的本质唯一性声明：无论是否带腿，“任意两个极限图锥在范畴上都是典范同构”都不存在。* 没有图极限的保持性、反映性或生成性，也没有 Structure/Limit/Preservation.v 的  [PreservesLimit] 的对应物。*  [graph_limit_IsALimit] 仅作为锥级声明的顶点唯一解读提供。它是两者中较弱的：它的腿不受约束，并且这里没有证明它们之间的分离，因此不宣称“严格更弱”。* 没有任何内容连接到 Theory/Diagram.v 中的 [Commutative]，该内容在下面从未被调用，并且该文件的任何交换性定理都未被使用。三角形见证确实绘制了一个交换三角形——它的直接边根据定义是复合边，而正是这个选择使顶点成为极限——但它作为定义展开被使用，从未通过谓词使用。* 循环见证展示了非函子性点，但不是极限：循环图的极限是 [e] 和 [id] 的等化器，而这里没有构造任何等化器。* 文件末尾的计算见证是该模块仅需 Category.Instance.Coq 的唯一原因，这会将该文件自身的闭包（Theory.Monad、Functor.Strong、Structure.BiCCC 等）引入到该模块中。除了探针之外，只有它需要这个文件，因此重量是包含在内的；它是公开的，而不是分开的，并且在完全相同的理由上进行拆分的先例是 Structure/Limit/Power.v / Power/Hom.v 的划分。* 从完整性假设出发，不会为任何类别生成 [GraphLimit] 实例；不存在“C 完全意味着 C 上的每个图表都有图极限”。* 本文件中未提供任何宇宙测量。下面没有声明这些常数标识或留空的层级。精确定范围：配套的 Test/ProbeQuiverLimit332.v 确实进行了一次测量，[Diagram] 标识了 C 的同构和证明宇宙（这就是为什么 [AGraphCone] 在 [ACone] 镜像显示它们分开时显示它们已识别）。那个引脚是捐赠者的——Theory/Diagram.v 在其部分以未注释的 [Context {C : Category}] 开始，因此它是 Construction/Free/Quiver/Examples.v 的头部记录那种最小化的产物，可以通过显式绑定器在上游修复，并不是该开发固有的内容。
*)

(** ** Graph cones / ** 图形锥 *)

(*
 Mac Lane's def 8, apex parameterized: a leg at every NODE, and one
 triangle at every EDGE.  There is no clause for composites or identities,
 because the shape [G] has neither. 

 --------
 Mac Lane 的定义 8，顶点参数化：每个节点一个支腿，每条边一个三角形。对于复合或恒等没有条款，因为形状 [G] 都没有。
*)
Class AGraphCone {G : Quiver} {C : Category} (D : Diagram G C)
  (c : obj[C]) := {
  (*
 The leg at the node [x]: an arrow from the apex into the label of [x]. 

 --------
 节点 [x] 的腿：从顶点指向 [x] 标签的箭头。
*)
  gvertex_map (x : G) : c ~{C}~> D x;
  (*
 One triangle for each drawn edge, and no other condition. 

 --------
 每条绘制的边对应一个三角形，没有其他条件。
*)
  gcone_coherence {x y : G} (e : edges x y) :
    dedge D e ∘ gvertex_map x ≈ gvertex_map y
}.

(*
 The bundled form, mirroring Structure/Cone.v's [Cone]. 

 --------
 捆绑形式，镜像 Structure/Cone.v 的 [Cone]。
*)
Class GraphCone {G : Quiver} {C : Category} (D : Diagram G C) := {
  gvertex_obj : obj[C];                    (* the apex *)
  gconeFrom : AGraphCone D gvertex_obj     (* its legs, with coherence / 它的腿，有条理 *)
}.

Coercion gvertex_obj : GraphCone >-> obj.
#[export] Existing Instance gconeFrom.

Notation "gvertex_obj[ N ]" := (@gvertex_obj _ _ _ N)
  (at level 9, format "gvertex_obj[ N ]") : category_scope.

(*
 The leg of a bundled graph cone at a node, as a first-class function --
 the covariant accessor, mirroring Structure/Limit/Preservation.v's
 [cone_leg]. 

 --------
 在一个节点处捆绑图锥的腿，作为一级函数——协变访问器，镜像 Structure/Limit/Preservation.v 的 [cone_leg]。
*)
Definition gcone_leg {G : Quiver} {C : Category} {D : Diagram G C}
  (N : GraphCone D) (x : G) : gvertex_obj[N] ~{C}~> D x :=
  @gvertex_map G C D (@gvertex_obj G C D N) (@gconeFrom G C D N) x.

Section Bridge.

Context {G : Quiver}.
Context {C : Category}.
Context {D : Diagram G C}.

(** ** Extension along paths / ** 沿路径的扩展 *)

(*
 THE induction.  The coherence field speaks only of edges; this extends it
 to a path of arbitrary length, one [gcone_coherence] and one [comp_assoc]
 per step.  It is what makes a graph cone a cone over the free category,
 and it is the only place in this file where a path is inducted over. 

 --------
 归纳。相干场仅谈论边；这将其扩展到任意长度的路径，每步一个 [gcone_coherence] 和一个 [comp_assoc]。它使得图锥成为自由范畴上的锥，也是本文件中唯一对路径进行归纳的地方。
*)
Lemma gcone_dpath {c : obj[C]} (N : AGraphCone D c) {x y : G}
  (p : tlist edges x y) : dpath D p ∘ gvertex_map x ≈ gvertex_map y.
Proof.
  induction p as [ | i m e p IH ]; simpl.
  - now rewrite id_left.
  - rewrite <- comp_assoc, gcone_coherence.
    exact IH.
Qed.

(* The same statement read off a bundled cone. / 同样的声明从一个捆绑的圆锥上读出。 *)
Lemma gcone_leg_dpath (N : GraphCone D) {x y : G} (p : tlist edges x y) :
  dpath D p ∘ gcone_leg N x ≈ gcone_leg N y.
Proof. exact (gcone_dpath (@gconeFrom G C D N) p). Qed.

(*
   * ** The correspondence with cones over the extending functor 

   --------
   * ** 与延伸函子上的圆锥对应关系
*)

(*
 Up: a graph cone IS a cone over [FunctorOfDiagram D].  The legs are
 carried across unchanged; the work is [gcone_dpath], routed through
 Theory/Diagram.v's [dpath_fmap]. 

 --------
 向上：一个图锥是 [FunctorOfDiagram D] 上的一个锥。腿部保持不变；工作是 [gcone_dpath]，通过 Theory/Diagram.v 的 [dpath_fmap] 进行路由。
*)
Definition ACone_of_AGraphCone {c : obj[C]} (N : AGraphCone D c) :
  ACone c (FunctorOfDiagram D).
Proof.
  unshelve eapply Build_ACone.
  - exact (fun x => @gvertex_map G C D c N x).
  - intros x y p; simpl.
    rewrite <- (dpath_fmap D p).
    exact (gcone_dpath N p).
Defined.

(*
 Down: restriction to one-edge paths.  The singleton path denotes
 [id ∘ dedge D e], so exactly one [id_left] is removed. 

 --------
 下降：限制为单边路径。单节点路径表示 [id ∘ dedge D e]，因此恰好移除一个 [id_left]。
*)
Definition AGraphCone_of_ACone {c : obj[C]}
  (N : ACone c (FunctorOfDiagram D)) : AGraphCone D c.
Proof.
  unshelve eapply Build_AGraphCone.
  - exact (fun x => @vertex_map _ _ c (FunctorOfDiagram D) N x).
  - intros x y e.
    pose proof (@cone_coherence _ _ c _ N x y (tlist_singleton e)) as H.
    rewrite <- (dpath_fmap D (tlist_singleton e)) in H.
    simpl in H.
    now rewrite id_left in H.
Defined.

Definition Cone_of_GraphCone (N : GraphCone D) : Cone (FunctorOfDiagram D) :=
  {| vertex_obj := gvertex_obj[N]
   ; coneFrom  := ACone_of_AGraphCone (@gconeFrom G C D N) |}.

Definition GraphCone_of_Cone (N : Cone (FunctorOfDiagram D)) : GraphCone D :=
  {| gvertex_obj := @vertex_obj _ _ _ N
   ; gconeFrom   := AGraphCone_of_ACone (@coneFrom _ _ _ N) |}.

(* Apexes and legs cross both ways ON THE NOSE. / 顶点和腿在鼻子上交叉两边。 *)
Example gcone_apex_fwd (N : GraphCone D) :
  vertex_obj[Cone_of_GraphCone N] = gvertex_obj[N] := eq_refl.

Example gcone_leg_fwd (N : GraphCone D) (x : G) :
  cone_leg (Cone_of_GraphCone N) x = gcone_leg N x := eq_refl.

Example gcone_apex_bwd (N : Cone (FunctorOfDiagram D)) :
  gvertex_obj[GraphCone_of_Cone N] = vertex_obj[N] := eq_refl.

Example gcone_leg_bwd (N : Cone (FunctorOfDiagram D)) (x : G) :
  gcone_leg (GraphCone_of_Cone N) x = cone_leg N x := eq_refl.

(*
 ... and so do the legs of both round trips.  The whole RECORDS do not:
 see measurement (2) of the header. 

 --------
 ... 两个往返的航程腿也是如此。整个记录则没有：看到报头的测量值（2）。
*)
Example gcone_round_graph (N : GraphCone D) (x : G) :
  gcone_leg (GraphCone_of_Cone (Cone_of_GraphCone N)) x = gcone_leg N x
  := eq_refl.

Example gcone_round_cone (N : Cone (FunctorOfDiagram D)) (x : G) :
  cone_leg (Cone_of_GraphCone (GraphCone_of_Cone N)) x = cone_leg N x
  := eq_refl.

(*
 The cone-side round trip at the strength the library's cone setoid
 supports: legs only, [AConeEquiv] ignoring the coherence proof. 

 --------
 在图书馆的圆锥集合所支持的强度下，圆锥侧的往返：仅限腿，[AConeEquiv]，忽略相干性证明。
*)
Lemma Cone_of_GraphCone_round (N : Cone (FunctorOfDiagram D)) :
  @coneFrom _ _ _ (Cone_of_GraphCone (GraphCone_of_Cone N))
    ≈ @coneFrom _ _ _ N.
Proof. intro j; reflexivity. Qed.

(*
 Where [dpath] and the extending functor's [fmap] DO agree definitionally.
 At a variable path they do not; measurement (4) of the header. 

 --------
 当 [dpath] 与扩展函子 [fmap] 定义上相同时。在一个变量路径上它们不相同；标题的测量（4）。
*)
Example dpath_singleton_is_fmap {x y : G} (e : edges x y) :
  dpath D (tlist_singleton e) = fmap[FunctorOfDiagram D] (tlist_singleton e)
  := eq_refl.

(** ** Limits of a graph diagram / ** 图表的限制 *)

(*
 Def 8's “a limit for the diagram D is a universal such cone”, at CONE
 level: the factorization is required to commute with the legs OF N, which
 is what the apex-only reading cannot say.  This is the graph-shaped mirror
 of Structure/Limit/Preservation.v's [IsLimitCone]. 

 --------
 Def 8 的“图 D 的极限是这样的一个通用锥”，在锥层面：要求分解与 N 的各条腿交换，这是仅顶点读法无法说明的。这是 Structure/Limit/Preservation.v 中 [IsLimitCone] 的图形化镜像。
*)
Definition IsLimitGraphCone (N : GraphCone D) : Type :=
  ∀ M : GraphCone D, ∃! u : gvertex_obj[M] ~{C}~> gvertex_obj[N],
    ∀ x : G, gcone_leg N x ∘ u ≈ gcone_leg M x.

(*
 Remark 6's “limits and limiting cones correspond exactly”, both
 directions, each a term with no tactic: the two statements are
 convertible. 

 --------
 备注6中的“极限和限制锥完全对应”，两个方向，每个术语都没有技巧：这两个陈述是可互换的。
*)
Definition graph_limitcone (N : GraphCone D) (H : IsLimitGraphCone N) :
  IsLimitCone (Cone_of_GraphCone N) :=
  fun M => H (GraphCone_of_Cone M).

Definition limitcone_graph_limit (N : GraphCone D)
  (H : IsLimitCone (Cone_of_GraphCone N)) : IsLimitGraphCone N :=
  fun M => H (Cone_of_GraphCone M).

Definition graph_limit_iff_limitcone (N : GraphCone D) :
  IsLimitGraphCone N ↔ IsLimitCone (Cone_of_GraphCone N) :=
  (graph_limitcone N, limitcone_graph_limit N).

(*
 The same passage starting from an arbitrary limiting cone over the
 extending functor, rather than from one already in the image. 

 --------
 相同的段落从扩展函子上的任意限制锥开始，而不是从已在像中的一个开始。
*)
Definition graph_limit_of_limitcone (N : Cone (FunctorOfDiagram D))
  (H : IsLimitCone N) : IsLimitGraphCone (GraphCone_of_Cone N) :=
  fun M => H (Cone_of_GraphCone M).

(*
 The apex-only READING.  Weaker than the cone-level statement -- its legs
 are unconstrained -- and no separation between the two is proved here. 

 --------
 仅顶点的解读。比锥层声明弱——它的各条支柱没有约束——而且这里没有证明两者之间的分离。
*)
Definition graph_limit_IsALimit (N : GraphCone D) (H : IsLimitGraphCone N) :
  IsALimit (FunctorOfDiagram D) gvertex_obj[N] :=
  limitcone_isalimit (graph_limitcone N H).

(*
 The bundled limit of a graph diagram, mirroring Structure/Limit.v. 

 --------
 图表的捆绑极限，镜像 Structure/Limit.v。
*)
Class GraphLimit := {
  graph_limit_cone : GraphCone D;
  graph_ump_limits : IsLimitGraphCone graph_limit_cone
}.

Definition Limit_of_GraphLimit (L : GraphLimit) : Limit (FunctorOfDiagram D) :=
  limitcone_limit (Cone_of_GraphCone (@graph_limit_cone L))
    (graph_limitcone _ (@graph_ump_limits L)).

Definition GraphLimit_of_Limit (L : Limit (FunctorOfDiagram D)) : GraphLimit :=
  {| graph_limit_cone := GraphCone_of_Cone (@limit_cone _ _ _ L)
   ; graph_ump_limits := graph_limit_of_limitcone _ (limit_limitcone L) |}.

Example graph_limit_round (L : GraphLimit) (x : G) :
  gcone_leg (@graph_limit_cone (GraphLimit_of_Limit (Limit_of_GraphLimit L))) x
  = gcone_leg (@graph_limit_cone L) x := eq_refl.

(** ** The mediating morphism / ** 中介态射 *)

Definition graph_limit_med {N : GraphCone D} (H : IsLimitGraphCone N)
  (M : GraphCone D) : gvertex_obj[M] ~{C}~> gvertex_obj[N] :=
  unique_obj (H M).

Lemma graph_limit_med_commutes {N : GraphCone D} (H : IsLimitGraphCone N)
  (M : GraphCone D) (x : G) :
  gcone_leg N x ∘ graph_limit_med H M ≈ gcone_leg M x.
Proof. exact (unique_property (H M) x). Qed.

Lemma graph_limit_med_unique {N : GraphCone D} (H : IsLimitGraphCone N)
  (M : GraphCone D) (m : gvertex_obj[M] ~{C}~> gvertex_obj[N]) :
  (∀ x : G, gcone_leg N x ∘ m ≈ gcone_leg M x) → graph_limit_med H M ≈ m.
Proof. intro Hm; exact (uniqueness (H M) m Hm). Qed.

Lemma graph_limit_med_eq {N : GraphCone D} (H : IsLimitGraphCone N)
  (M : GraphCone D) (m m' : gvertex_obj[M] ~{C}~> gvertex_obj[N]) :
  (∀ x : G, gcone_leg N x ∘ m ≈ gcone_leg M x) →
  (∀ x : G, gcone_leg N x ∘ m' ≈ gcone_leg M x) → m ≈ m'.
Proof.
  intros Hm Hm'.
  transitivity (graph_limit_med H M).
  - symmetry; exact (graph_limit_med_unique H M m Hm).
  - exact (graph_limit_med_unique H M m' Hm').
Qed.

End Bridge.

Arguments GraphLimit {G C} D.

(*
   * ** Witness one: a limiting graph cone over the walking triangle 

   --------
   * ** 证人一：行走三角上的限制图锥
*)

(*
 The shape is Theory/Diagram.v's [TriangleQuiver]; the diagram is that
 file's [TriangleDiagram] with its direct edge taken to be LITERALLY the
 composite, so no commutation hypothesis is needed and none is used. 

 --------
 该形状是 Theory/Diagram.v 的 [TriangleQuiver]；该图是该文件的 [TriangleDiagram]，其直接边被字面上视为复合，因此不需要也没有使用交换假设。
*)
Section TriangleLimit.

Context {C : Category}.
Context {p q r : C} (u : p ~{C}~> q) (v : q ~{C}~> r).

Notation TriD := (TriangleDiagram u v (v ∘ u)).

Definition tri_lim_legs (i : TriNode) : p ~{C}~> TriD i :=
  match i as i0 return p ~{C}~> TriD i0 with
  | TrX => id
  | TrY => u
  | TrZ => v ∘ u
  end.

Definition tri_lim_acone : AGraphCone TriD p.
Proof.
  unshelve eapply Build_AGraphCone.
  - exact tri_lim_legs.
  - intros i j e.
    destruct i, j; simpl in e; try destruct e; simpl;
      rewrite ?id_right; reflexivity.
Defined.

Definition TriangleGraphCone : GraphCone TriD :=
  {| gvertex_obj := p ; gconeFrom := tri_lim_acone |}.

(*
 Every arrow into the apex induces a competing graph cone. 

 --------
 每一根射入顶点的箭头都会引起一个竞争图锥。
*)
Definition tri_gcone_of_arrow {c : obj[C]} (f : c ~{C}~> p) : GraphCone TriD.
Proof.
  unshelve eapply Build_GraphCone; [ exact c | ].
  unshelve eapply Build_AGraphCone.
  - exact (fun i => match i as i0 return c ~{C}~> TriD i0 with
                    | TrX => f
                    | TrY => u ∘ f
                    | TrZ => (v ∘ u) ∘ f
                    end).
  - intros i j e.
    destruct i, j; simpl in e; try destruct e; simpl;
      rewrite ?comp_assoc; reflexivity.
Defined.

(*
 The apex [p] is the limit, over an arbitrary category and arbitrary
 [u], [v].  The mediator is the competing cone's leg at [TrX]; the
 coherence instance at the edge Y->Z is never spent. 

 --------
 顶点 [p] 是在任意范畴和任意 [u]、[v] 下的极限。中介者是在 [TrX] 的竞争锥的腿；边 Y->Z 处的相干实例从未被使用。
*)
Theorem triangle_graph_limit : IsLimitGraphCone TriangleGraphCone.
Proof.
  intro M.
  unshelve eapply Build_Unique.
  - exact (gcone_leg M TrX).
  - intro i; destruct i; simpl.
    + apply id_left.
    + exact (@gcone_coherence _ _ _ _ (@gconeFrom _ _ _ M) TrX TrY tt).
    + exact (@gcone_coherence _ _ _ _ (@gconeFrom _ _ _ M) TrX TrZ tt).
  - intros m Hm.
    pose proof (Hm TrX) as H; simpl in H.
    rewrite id_left in H.
    now symmetry.
Defined.

Example tri_med_is_arrow {c : obj[C]} (f : c ~{C}~> p) :
  graph_limit_med triangle_graph_limit (tri_gcone_of_arrow f) = f := eq_refl.

(*
   * *** No functoriality: the triangles at the two parallel X->Z arrows 

   --------
   * *** 无函子性：两个平行 X->Z 箭头上的三角形
*)

(*
 [tri_via_Y] and [tri_direct] are DISTINCT morphisms of the free category
 (Theory/Diagram.v's [tri_via_Y_neq_direct]), and a graph cone states a
 triangle for neither.  Both are consequences of the edge conditions,
 through [gcone_dpath]. 

 --------
 [tri_via_Y] 和 [tri_direct] 是自由范畴（Theory/Diagram.v 的 [tri_via_Y_neq_direct]）的不同态射，一个图锥对它们都不形成三角形。这两者都是通过 [gcone_dpath] 的边条件的结果。
*)
Lemma tri_gcone_at_via_Y (M : GraphCone TriD) :
  dpath TriD tri_via_Y ∘ gcone_leg M TrX ≈ gcone_leg M TrZ.
Proof. exact (gcone_leg_dpath M tri_via_Y). Qed.

Lemma tri_gcone_at_direct (M : GraphCone TriD) :
  dpath TriD tri_direct ∘ gcone_leg M TrX ≈ gcone_leg M TrZ.
Proof. exact (gcone_leg_dpath M tri_direct). Qed.

End TriangleLimit.

Example tri_via_Y_len : tlist_length tri_via_Y = 2%nat := eq_refl.
Example tri_direct_len : tlist_length tri_direct = 1%nat := eq_refl.

(*
   * ** Witness two: the walking loop, one field against infinitely many
   arrows 

   --------
   * ** 证人二：步行环，一片田地对抗无限多的箭
*)

Fixpoint loop_path (n : nat) : tlist (@edges LoopQuiver) LpX LpX :=
  match n with
  | O   => tnil
  | S k => tcons LpX (tt : @edges LoopQuiver LpX LpX) (loop_path k)
  end.

Lemma loop_path_length (n : nat) : tlist_length (loop_path n) = n.
Proof.
  induction n as [ | k IH ]; simpl; [ reflexivity | ].
  apply f_equal; exact IH.
Qed.

(*
 The paths are pairwise distinct arrows of the free category, so the
 endo-hom at the single node is infinite. 

 --------
 这些路径是自由范畴中成对不同的箭头，因此单节点的自同态集是无限的。
*)
Lemma loop_paths_distinct (n m : nat) :
  (loop_path n ≈[FreeOnQuiver LoopQuiver] loop_path m) → n = m.
Proof.
  intro H.
  pose proof (tlist'_equiv_lengths LoopQuiver LpX LpX LpX
                (loop_path n) (loop_path m) eq_refl H) as Hl.
  now rewrite !loop_path_length in Hl.
Qed.

Section LoopCone.

Context {C : Category}.
Context {a : C} (e : a ~{C}~> a).

(*
 A graph cone over the loop diagram is EXACTLY an arrow [psi] with
 [e ∘ psi ≈ psi]: one datum, one equation. 

 --------
 环图上的图锥正好是带有箭头 [psi] 的图，[e ∘ psi ≈ psi]：一个数据，一个方程。
*)
Definition loop_gcone {c : obj[C]} (psi : c ~{C}~> a) (H : e ∘ psi ≈ psi) :
  GraphCone (LoopDiagram e).
Proof.
  unshelve eapply Build_GraphCone; [ exact c | ].
  unshelve eapply Build_AGraphCone.
  - exact (fun i => match i as i0 return c ~{C}~> LoopDiagram e i0 with
                    | LpX => psi
                    end).
  - intros i j w; destruct i, j; simpl; exact H.
Defined.

Example loop_gcone_leg {c : obj[C]} (psi : c ~{C}~> a) (H : e ∘ psi ≈ psi) :
  gcone_leg (loop_gcone psi H) LpX = psi := eq_refl.

Lemma loop_gcone_fix (N : GraphCone (LoopDiagram e)) :
  e ∘ gcone_leg N LpX ≈ gcone_leg N LpX.
Proof. exact (@gcone_coherence _ _ _ _ (@gconeFrom _ _ _ N) LpX LpX tt). Qed.

(*
 ... and that one equation discharges the triangle at EVERY path, hence at
 every arrow of the free category, by [gcone_dpath] alone. 

 --------
 ...并且那个方程在每一条路径上释放三角形，因此仅通过 [gcone_dpath]，在自由范畴的每一条箭头上也能释放三角形。
*)
Theorem loop_gcone_every_path (N : GraphCone (LoopDiagram e)) (n : nat) :
  dpath (LoopDiagram e) (loop_path n) ∘ gcone_leg N LpX ≈ gcone_leg N LpX.
Proof. exact (gcone_leg_dpath N (loop_path n)). Qed.

End LoopCone.

(*
   * ** Witness three: the triangle limit computing in [Coq] 

   --------
   * ** 证人三：在 [Coq] 中的三角形极限计算
*)

Definition coq_u : nat ~{Coq}~> nat := S.
Definition coq_v : nat ~{Coq}~> bool := Nat.even.

Definition CoqTriDiagram : Diagram TriangleQuiver Coq :=
  TriangleDiagram coq_u coq_v (coq_v ∘ coq_u).

Definition CoqTriCone : GraphCone CoqTriDiagram :=
  TriangleGraphCone coq_u coq_v.

Example coq_tri_apex : gvertex_obj[CoqTriCone] = nat := eq_refl.
Example coq_tri_X : gcone_leg CoqTriCone TrX 3%nat = 3%nat := eq_refl.
Example coq_tri_Y : gcone_leg CoqTriCone TrY 3%nat = 4%nat := eq_refl.
Example coq_tri_Z : gcone_leg CoqTriCone TrZ 3%nat = true := eq_refl.
Example coq_tri_Z' : gcone_leg CoqTriCone TrZ 4%nat = false := eq_refl.

Definition coq_probe : bool ~{Coq}~> nat := fun b => if b then 1%nat else 0%nat.

Definition CoqProbeCone : GraphCone CoqTriDiagram :=
  tri_gcone_of_arrow coq_u coq_v coq_probe.

Example coq_probe_med :
  graph_limit_med (triangle_graph_limit coq_u coq_v) CoqProbeCone = coq_probe
  := eq_refl.

Example coq_probe_med_true :
  graph_limit_med (triangle_graph_limit coq_u coq_v) CoqProbeCone true = 1%nat
  := eq_refl.

Example coq_probe_Z_t : gcone_leg CoqProbeCone TrZ true = true := eq_refl.
Example coq_probe_Z_f : gcone_leg CoqProbeCone TrZ false = false := eq_refl.
Example coq_probe_Y : gcone_leg CoqProbeCone TrY true = 2%nat := eq_refl.
