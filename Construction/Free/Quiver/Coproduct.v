Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Coproduct.
Require Import Category.Construction.Free.Quiver.

Generalizable All Variables.

(** * Coproducts of quivers / * 箭图的余积 *)

(*
 Mac Lane, "Categories for the Working Mathematician", 2nd ed., §III.3
 Exercise 4, printed p. 68 (PDF p. 77); catalog item [maclane:III.3:ex4],
 whose recorded statement summary is

 "Describe coproducts, showing that they exist, in the category of small
 categories Cat, the category of monoids Mon, and the category of
 graphs Grph."

 (doc/plan/books/maclane/inventory/III.json).  The exercise has three
 independent thirds and this file delivers exactly one of them, the Grph
 third: the coproduct of two quivers, its two injections, the copairing
 universal property, and — since the price turned out to be small — the
 [Cocartesian QuiverCategory] instance, which is what "showing that they
 exist" asks for.  The Cat third was already in tree as
 [Cat_Cocartesian] (Instance/Cat/Cocartesian.v) over
 Construction/Coproduct.v, and is cross-linked below rather than redone;
 the Mon third is not touched here.

 nLab: https://ncatlab.org/nlab/show/quiver
 nLab: https://ncatlab.org/nlab/show/coproduct

 Mac Lane's "graph" is what is now called a quiver or directed multigraph.
 Construction/Free/Quiver.v indexes edges directly by their endpoints
 ([edges X Y] is the set of arrows from X to Y), and that encoding is again
 what makes the construction cheap, exactly as it was for the opposite and
 the product in the sibling file Construction/Free/Quiver/Constructions.v:
 nodes are the tagged disjoint union, and the edge family is defined by
 cases on the two tags, with the two CROSS cases empty.  That last clause
 is the whole mathematical content of "disjoint" and is where an error
 would hide, so it is stated several ways: five artifacts in three
 kinds.  They all rest on the SAME definitional fact and so would
 break together rather than giving independent checks below — as two [eq_refl]
 equations naming [False], as two eliminators, and as a concrete
 uninhabitedness witness at the end of the file.

 THE RELATIONSHIP TO THE SIBLING FILE.  Constructions.v builds [QuiverOp]
 and [QuiverProd] for §II.7 Exercise 1; this file builds [QuiverCoprod] for
 §III.3 Exercise 4.  They are different exercises with different content —
 §II.7's asks that the constructions AGREE with the corresponding ones on
 categories along the forgetful functor, §III.3's asks for existence and a
 description — but they invite the same measurements, and where the two can
 be compared the coproduct comes out STRONGER in two places and WEAKER in
 one.  All three differences are recorded here because each is a fact about
 [sum] versus [prod] rather than about the two authors:

 (a) STRONGER: the [≈]-hypothesis form of uniqueness IS proved here.
 Constructions.v discloses that [QuiverPair_unique] takes LEIBNIZ
 equalities of the two composites as hypotheses, and that upgrading
 them would need respectfulness of [QuiverPair] in its arguments, which
 it does not prove.  [QuiverCopair_unique] below takes [≈] hypotheses,
 and [QuiverCopair_respects] IS the corresponding respectfulness.  The
 reason is structural.  A pairing's node action is [fun x => (F x,
 F' x)], so relating two pairings needs an equality of PAIRS built from
 two equalities, and then the transported edge is a pair transported
 along it; a copairing's node action is [fun x => match x with inl a =>
 F a | inr b => F' b end], so at each constructor the required equality
 IS the given one, with no assembly and no transport bookkeeping.

 (b) STRONGER: consequently the universal property is packaged as a class
 instance, [QuiverCategory_Cocartesian], where Constructions.v states
 in terms that "no claim is made that [QuiverProd] is the categorical
 product in [QuiverCategory]".  [Cocartesian C] is notation for
 [@Cartesian (C^op)] (Structure/Cocartesian.v), so the instance
 literally says that [QuiverCategory^op] is cartesian, with
 [product_obj := QuiverCoprod], [exl := QuiverInl], [exr := QuiverInr]
 and [fork := QuiverCopair]; its [ump_products] field, read in the
 opposite, is the copairing property in both directions.  The derived
 vocabulary of Structure/Cocartesian.v is pinned to the named constants
 by [eq_refl] ([Coprod_is_QuiverCoprod] and its three siblings) so that
 no reader has to take on trust which orientation was chosen.

 (c) WEAKER, and this is the one that matters: the analogue of §II.7's
 headline does NOT hold at [eq_refl].  Constructions.v gets
 [QuiverOfCat (C ∏ D) = QuiverProd …] at Leibniz equality of the whole
 [Quiver] record.  The coproduct statement is measured and REFUTED at
 that strength, and the two obstructions are located rather than
 guessed; see the next paragraph.

 PRESERVATION BY THE FORGETFUL FUNCTOR: WHAT IS AND IS NOT TRUE.  The
 question "does U : Cat -> Grph preserve coproducts" is not part of
 Exercise 4, but it is the obvious companion to §II.7 and it is answered
 here.  Measured, strict first:

 [QuiverOfCat_Coproduct_nodes] — the NODE TYPES agree by [eq_refl].

 [QuiverOfCat_Coproduct_edges_ll] and its three siblings — the EDGE SETS
 agree by [eq_refl] AT EVERY PAIR OF CONSTRUCTOR ARGUMENTS, in all four
 cases including the two cross cases where both sides are [False].

 The [edges] FIELDS, as functions of two variable nodes, are NOT
 convertible, and neither are the whole records.  Both failures were
 checked by machine and each is a genuine conversion failure ("cannot
 unify"), not an elaboration or scope error.  There are exactly two
 causes and they are independent:

 - Construction/Coproduct.v is a [Program Definition], and Program's
 pattern-matching compilation gives its [hom] field the
 equation-passing shape [match y as y' return (y' = y0 -> Type) with
 … end eq_refl] rather than a plain nested match.  Under binders that
 term is not convertible with the plain match used here, though at
 constructor arguments both iota-reduce to the same thing — which is
 precisely why the four pointwise statements above DO close.

 - its [homset] field is [{| equiv := …; setoid_equiv := … |}] whose
 second component is a [Qed]-opaque Program obligation (the tree runs
 [Unset Transparent Obligations], Lib/Tactics.v).  [Setoid] has
 primitive projections with eta, so conversion compares that field,
 and an opaque constant defeats it.  This is the same obstruction
 Constructions.v records in its edgeset/prod_setoid non-reuse
 note -- NOT, as an earlier draft said, the one it records for
 [Forgetful_preserves_fst]/[_snd], which that file blames on
 [fmap_respects] instead -- met
 here one level earlier: there it blocked an arrow-level statement,
 here it blocks the object-level one.

 Neither obstruction is a fact about coproducts of graphs; both are facts
 about how Construction/Coproduct.v happens to be elaborated.  No attempt
 is made to route around them by re-spelling [QuiverCoprod] to match
 Program's output, and no claim is made that [eq_refl] is unreachable in
 principle.  These two negatives are MEASURED but not GUARDED in this
 file: nothing here re-checks them on a later build, and pinning them
 would take a probe file, which THIS file does not create -- but the
 same commit does.  Test/ProbeCoproduct328.v pins both.  An earlier
 draft stopped at "does not create", leaving a reader with the
 wrong conclusion about the commit.

 What IS delivered instead is [QuiverOfCat_Coproduct_iso], an ISOMORPHISM
 in [QuiverCategory] between the underlying quiver of C ∐ D and the
 coproduct of the underlying quivers, whose two legs are the IDENTITY on
 nodes and the IDENTITY on edges in every case — they carry no data
 whatsoever, which is the precise sense in which the failure above is
 presentational.  Read the word "isomorphism" here at full strength: this
 is an isomorphism in [QuiverCategory], not an equivalence of anything.
 And it is compatible with the injections: [Forgetful_preserves_coprod_inl]
 and [_inr] show that it carries the underlying map of the inclusion
 functor C ⟶ C ∐ D to [QuiverInl], so what is preserved is the coproduct
 DIAGRAM and not merely an abstract object.  The two inclusion functors are
 built here as [CoproductInl] and [CoproductInr] because the tree has no
 named ones — Instance/Cat/Cocartesian.v supplies them only as anonymous
 inline records in the [exl]/[exr] fields of [Cat_Cocartesian], and naming
 them that way would cost a dependency on Instance/Cat, which this file
 does not take.

 THE UNIQUENESS CLAUSE IS WITNESSED, NOT ONLY STATED.  Constructions.v
 discloses that its uniqueness clause has no exhibited competitor: "no
 homomorphism into a product is exhibited that FAILS the two triangles, so
 the clause's discriminating power is disclosed rather than witnessed",
 and observes that doing so needs a concrete quiver with two distinct
 nodes.  The closing section here supplies exactly that on the coproduct
 side: [copair_swap_fails_left] exhibits a homomorphism out of a concrete
 coproduct which satisfies neither triangle, and refutes the first of them
 outright.  The witnesses are two small quivers — [LoopQ], one node with
 one loop, and [TwoQ], two nodes with two parallel edges between every
 ordered pair — and the concrete facts proved of them are that the two
 injections into [QuiverCoprod LoopQ LoopQ] are NOT equivalent (so the
 construction does not collapse the two summands -- SCOPE THAT TO THE
 INSTANCE: this file proves NO general non-degeneracy for the
 injections, containing no [Monic], [Section] or injectivity statement
 at all, an asymmetry with the Mon half of the same commit where the
 corresponding results hold for ARBITRARY factors), that the cross edge
 set
 is empty, and that the copairing of two homomorphisms that differ COMPUTES
 to the left one on the left summand and to the right one on the right, by
 [eq_refl] on both nodes and edges.  Nothing in that section is asserted:
 every negative EXCEPT [coprod_no_cross_edge] is obtained by
 projecting the node component -- that one is the identity on
 [False], since the cross edge set IS [False], so like its general
 siblings above it makes the fact quotable rather than proving
 anything of a
 hypothetical equivalence and discriminating on [Datatypes.inl] versus
 [Datatypes.inr], or on [false] versus [true].  Transports do of course
 occur in the TYPES of the edge-coherence obligations, that being the
 shape of [QuiverHomomorphismEquivalence]; what is claimed is that no
 PROOF in this file manipulates one — each such obligation is either the
 hypothesis read at the corresponding constructor, or eliminated from
 [False], or closed by [reflexivity] once the node equalities have become
 [eq_refl].  No UIP hypothesis and no decidability assumption appears
 anywhere.

 OTHER STRENGTH MEASUREMENTS, all taken rather than estimated.

 BOTH TRIANGLES hold at LEIBNIZ EQUALITY of the whole homomorphism
 record, [QuiverCopair_Inl] and [QuiverCopair_Inr] by [eq_refl] — the
 same outcome Constructions.v reports for its two projections, and for
 the same reason: [QuiverComp]'s respectfulness field is synthesised as
 the composite of the two given ones, and composing with the identity
 that [QuiverInl] carries leaves the copairing's own field, which then
 iota-reduces at each constructor.

 AN EARLIER DRAFT OF THIS HEADER CLAIMED A CONSTANT THAT DOES NOT
 EXIST, and it is recorded here as bad evidence rather than deleted.
 It read: "[QuiverCoswap_is_copair] is [eq_refl] ... recorded rather
 than asserted".  There is no such constant anywhere in the tree,
 and the body below says the opposite in terms: [QuiverCoswap] is
 TAKEN AS A DEFINITION ([QuiverCopair QuiverInr QuiverInl]), so
 there is nothing to record and no second candidate whose agreement
 would be worth measuring.  The phrase "recorded rather than
 asserted" is this file's own honesty vocabulary, which made the
 invented measurement read as a checked one.

 [QuiverCoswap_invol] is only [≈] — the [eq_refl] form was tried and
 rejected with a genuine conversion failure — and the cause is the same
 one the sibling reports, met from the other side.  There
 [QuiverSwap_invol] fails because surjective pairing is not definitional
 for the standard library's [prod]; here the node action of the
 twice-exchanged quiver is a match on a match, which does not reduce
 while the scrutinee is a variable, [sum] having no eta rule either.  In
 both cases it is the absence of a definitional eta rule for the
 standard library's own datatype, not anything about the construction.

 UNIVERSES, measured per constant and reported with causes.
 [coprod_edges@{o1 h1 p1 o2 h2 p2 o h p}] carries only [h1 <= h] and
 [h2 <= h] — every other level stays free, since [Type] is cumulative.
 [coprod_edgeset] and hence [QuiverCoprod] carry in addition

 h1 = h2 = h    and    p1 = p2 = p,

 identifying the two summands' edge and proof levels with the coproduct's.
 The cause is measured, not guessed: this construction REUSES the
 summand's edge setoid verbatim ([edgeset G a b] is handed back
 unchanged), and [Setoid] is not cumulative here — the bare term
 [fun (A : Type@{a}) (S : Setoid@{a a} A) => (S : Setoid@{b b} A)] with
 [a < b] is rejected, which was checked directly rather than taken from
 elsewhere.  This is a real difference from [QuiverProd], which BUILDS a
 fresh componentwise setoid ([edgeset_prod]) and can therefore keep the
 levels apart.  The three OBJECT levels remain free on both sides
 ([o1 <= o], [o2 <= o]), and [False_Setoid@{h p}] carries an EMPTY
 constraint clause.

 The HOMOMORPHISMS are less general than the quiver, exactly as
 Constructions.v reports for its own: [QuiverInl@{o h p}] and
 [QuiverInr@{o h p}] take BOTH summands at one instance and add [h <= p],
 while [QuiverCopair] does better, keeping the three object levels apart
 and inheriting only [h1 = h2] and [p1 = p2] from [QuiverCoprod].
 Everything stated through [@homset QuiverCategory] — [QuiverCopair_eta],
 [QuiverCopair_unique], [QuiverCopair_respects], [QuiverCoswap_invol], the
 [Cocartesian] instance and the whole preservation section — collapses all
 the quivers involved to a SINGLE [Quiver@{u u0 u0}] instance, hom and
 proof levels identified.  That is [QuiverCategory]'s own doing: it is one
 universe instance of [Category], so any statement quantified over its
 hom-setoid is a statement at that instance.  Finally
 [QuiverOfCat_Coproduct_iso] takes [C : Category@{u u0 u0}] and
 [D : Category@{u1 u2 u2}], keeping the two object levels apart but
 identifying each factor's hom and proof levels; the cause is the donor,
 Construction/Coproduct.v being declared
 [Category@{u u0 u0} -> Category@{u1 u2 u2} -> Category@{u3 u4 u4}], the
 same phenomenon Constructions.v attributes to [Opposite] and [Product].
 No attempt was made to recover more generality anywhere, and nothing in
 this file needs it.

 WHAT IS NOT BUILT.  [QuiverCoprod] is not packaged as a bifunctor and no
 action on pairs of homomorphisms is defined (the sibling likewise builds
 no bifunctor for [QuiverProd]); the nullary case — the empty quiver as an
 initial object of [QuiverCategory] — is not supplied, so [Cocartesian] is
 binary here and no [Initial QuiverCategory] instance is claimed;
 [Forgetful] is not shown to preserve coproducts as a general statement
 about a functor (the comparison is exhibited pointwise in C and D, and
 its naturality in C and D is not proved); the correspondence is not
 packaged as a bijection of hom-setoids in [Sets], though its content is
 present — the [ump_products] field of the instance together with
 [QuiverCopair_respects] is exactly what such a bijection would need, and
 only the packaging (and a dependency on Instance/Sets) is missing; the
 free-category functor's behaviour on coproducts is not addressed; and no
 relation is drawn to
 Theory/OGraph.v, whose ×_O multiplies over a FIXED node set and defines
 no coproduct at all, so nothing here bears on it and nothing there bears
 on this. 

 --------
 Mac Lane，《为工作中的数学家而设的范畴论》，第2版，§III.3 练习4，印刷版第68页（PDF第77页）；目录项[maclane:III.3:ex4]，其记录的陈述摘要为

 “描述余积，证明它们在小范畴 Cat、幺半群范畴 Mon 和图的范畴 Grph 中存在。”(doc/plan/books/maclane/inventory/III.json)。该练习分为三个独立的部分，这个文件正好提供其中的一部分，即 Grph 部分：两个量子图的余积，它的两个注入，余配对的普遍性质，以及——由于代价很小——[Cocartesian QuiverCategory] 实例，这就是“证明它们存在”的要求。Cat 部分已经在 tree 中作为 [Cat_Cocartesian]（Instance/Cat/Cocartesian.v）位于 Construction/Coproduct.v 上，并且在下面交叉链接，而不是重新制作；Mon 部分在此未涉及。

 nLab: https://ncatlab.org/nlab/show/quiver  
 nLab: https://ncatlab.org/nlab/show/coproductMac Lane 的“图”就是现在所说的箭簇或有向多重图。Construction/Free/Quiver.v 直接按端点索引边（[edges X Y] 是从 X 到 Y 的箭头集合），这种编码方式正是使得构造变得廉价的原因，就像在兄弟文件 Construction/Free/Quiver/Constructions.v 中的对偶和积一样：节点是带标签的不相交并集，边族通过对两个标签的情况定义，其中两个 CROSS 情况为空。最后这一条款就是“不相交”的全部数学内容，也是错误可能隐藏的地方，所以它以多种方式陈述：三种类型中有五个工件。它们都依赖于相同的定义性事实，因此会一起失效，而不是在下面给出独立的检查——就像两个命名为 [False] 的 [eq_refl] 方程，作为两个消元器，以及作为文件末尾的具体空值证明。与兄弟文件的关系。Constructions.v 为 §II.7 练习 1 构建了 [QuiverOp] 和 [QuiverProd]；该文件为 §III.3 练习 4 构建了 [QuiverCoprod]。它们是不同的练习，内容不同——§II.7 的要求构造与在忘记函子下的相应范畴上的构造一致，§III.3 的则要求存在性和描述——但它们涉及相同的测量，并且在可比较的地方，两者在两个点上积更强，而在一个点上积更弱。这里记录了所有三处差异，因为每一处都是关于 [sum] 与 [prod] 的事实，而不是关于两位作者的事实：(a) 更强：在这里证明了 [≈] 假设形式的唯一性。Constructions.v 公开了 [QuiverPair_unique] 以两个复合体的赖布尼茨等式作为假设，并且升级它们需要 [QuiverPair] 在其论证中的恭敬性，但它并未证明这一点。下面的 [QuiverCopair_unique] 采用 [≈] 假设，而 [QuiverCopair_respects] 就是相应的恭敬性。原因是结构性的。一个配对的节点作用是 [fun x => (F x, F' x)]，所以关联两个配对需要通过两个相等构建的 PAIRS 的相等，然后传输的边就是沿它传输的一个配对；一个共配对的节点作用是 [fun x => match x with inl a => F a | inr b => F' b end]，所以在每个构造子处所需的相等就是给定的那个相等，不需要组装也不需要传输记录。(b) 更强：因此普遍性质被打包为一个类实例，[QuiverCategory_Cocartesian]，其中 Constructions.v 以这样的术语说明“并未声称 [QuiverProd] 是 [QuiverCategory] 中的范畴积”。[Cocartesian C] 是 [@Cartesian (C^op)]（Structure/Cocartesian.v）的符号表示，因此该实例字面上表明 [QuiverCategory^op] 是笛卡尔的，具有 [product_obj := QuiverCoprod]、[exl := QuiverInl]、[exr := QuiverInr] 和 [fork := QuiverCopair]；其 [ump_products] 字段，反向读取时，是两个方向的共配对性质。Structure/Cocartesian.v 的派生词汇由 [eq_refl]（[Coprod_is_QuiverCoprod] 及其三个同类项）绑定到命名常量，因此没有读者需要完全依赖信任去判断选择了哪种取向。(c) 较弱，而且这才是关键：§II.7 标题的类比在 [eq_refl] 上不成立。Constructions.v 在整条记录的 Leibniz 相等性上得到 [QuiverOfCat (C ∏ D) = QuiverProd …]。coproduct 语句在该强度下被测量并被反驳，这两个障碍也被定位而不是猜测；见下一段。  

 被遗忘函子保持性：什么成立，什么不成立。问题“U : Cat -> Grph 是否保持 coproducts”不属于练习 4，但它是 §II.7 的明显附属问题，这里给出答案。首先严格测量：  

 [QuiverOfCat_Coproduct_nodes] —— 节点类型通过 [eq_refl] 一致。[QuiverOfCat_Coproduct_edges_ll] 及其三个兄弟——边集（EDGE SETS）
 在每一对构造函数参数上都与 [eq_refl] 一致，在所有四种情况下，包括两种交叉情况，其中双方都是 [False]。

 [edges] 字段，作为两个变量节点的函数，不可转换，整个记录也不可转换。两种失败都经过机器检查，每一种都是实际的转换失败（“无法统一”），而不是展开或作用域错误。原因正好有两个，并且它们是独立的：- Construction/Coproduct.v 是一个 [Program Definition]，并且程序的模式匹配编译赋予它的 [hom] 字段方程传递的形式 [match y as y' return (y' = y0 -> Type) with … end eq_refl]，而不是一个普通的嵌套匹配。在绑定器下，该项与这里使用的普通匹配不可转换，尽管在构造函数参数处两者都通过 iota 简化为相同的东西——这正是上述四个逐点语句能够关闭的原因。- 它的 [homset] 字段是 [{| equiv := …; setoid_equiv := … |}]，  
 其第二个组件是一个 [Qed] -不透明程序义务（树运行 [Unset Transparent Obligations]，Lib/Tactics.v）。  
 [Setoid] 有带有 eta 的原始投影，因此转换会比较该字段，而不透明常量会阻止它。  
 这与 Constructions.v 在其 edgeset/prod_setoid 非重用注释中记录的阻碍相同 —— 并非如早期草稿所述，它记录的是 [Forgetful_preserves_fst] / [_snd] 的情况，该文件将其归咎于 [fmap_respects] —— 在这里比之前提前一级：  
 那里它阻止了箭头级别的声明，这里它阻止了对象级别的声明。这两个阻碍都不是关于图的余积的事实；它们都是关于 Construction/Coproduct.v 如何被展开的事实。没有尝试通过重新拼写 [QuiverCoprod] 来匹配 Program 的输出来绕过它们，也没有声称 [eq_refl] 原则上是不可到达的。这两个否定在此文件中是被测量的，但并未被保护：这里没有在以后的构建中重新检查它们，而且将其固定需要一个探针文件，而此文件并未创建——但同一提交确实创建了。Test/ProbeCoproduct328.v 固定了两者。早期的草稿止步于“未创建”，使读者对该提交得出错误结论。实际交付的是 [QuiverOfCat_Coproduct_iso]，这是 [QuiverCategory] 中的一个同构，连接 C ∐ D 的底层箭图与底层箭图的余积，它的两条腿在每种情况下都是节点上的恒等映射和边上的恒等映射——它们完全不携带任何数据，这正是上述失败表现为表面上的原因。在此将“同构”一词以完全意义理解：这是在 [QuiverCategory] 中的同构，而不是任何事物的等价。而且它与注入兼容：[Forgetful_preserves_coprod_inl] 和 [_inr] 表明它将包含函子 C ⟶ C ∐ D 的底层映射带入 [QuiverInl]，因此被保留的是余积图而不仅仅是抽象对象。这里的两个包含函子分别构建为 [CoproductInl] 和 [CoproductInr]，因为该树没有命名的 —— Instance/Cat/Cocartesian.v 仅将它们作为匿名内联记录提供在 [Cat_Cocartesian] 的 [exl] / [exr] 字段中，而以那种方式命名它们将导致对 Instance/Cat 的依赖，而此文件并未依赖该文件。唯一性条款是被见证的，而不仅仅是陈述的。Constructions.v 透露它的唯一性条款没有展示的竞争者：“没有展示一个映射到积的同态失败于两个三角形，因此该条款的判别能力是被披露而不是被见证”，并指出这样做需要一个具有两个不同节点的具体箭图。此处的结尾部分正好在余积方面提供了这一点：[copair_swap_fails_left] 展示了一个从具体余积出的同态，它不满足任意一个三角形，并直接驳斥了第一个三角形。证据是两个小的箭袋——[LoopQ]，一个节点带有一个环，和[TwoQ]，每对有序节点之间有两条平行边的两个节点——并且关于它们被证明的具体事实是，两个注入到[QuiverCoprod LoopQ LoopQ]的映射**不等价**（所以该构造不会将两个直和分量合并——将其限定到该实例：这个文件没有证明注入的一般非退化性，不包含[Monic]、[Section]或任何关于单射性的陈述，这与同一提交的Mon一半形成了不对称，在那里对应结果对于任意因子成立），交叉边集合为空，并且两个同态的共配对在左侧分量上计算结果为左边同态，在右侧分量上计算结果为右边同态，由[eq_refl]在两个节点和边上实现。该部分没有任何内容被断言：
 除了 [coprod_no_cross_edge] 之外的每个负面结果都是通过
 投影节点组件获得的——那是 [False] 上的恒等函数，因为交叉边集是 [False]，所以像其上面的通用同类一样，它使该事实可引用，而不是证明任何假设的等价性，并且在 [Datatypes.inl] 与 [Datatypes.inr]，或在 [false] 与 [true] 之间进行区分。当然，传输确实发生在边一致性义务的类型中，这正是 [QuiverHomomorphismEquivalence] 的形状；所声称的是，这个文件中没有任何证明确实操作了其中一个——每个此类义务要么是对应构造函数处读取的假设，要么从 [False] 中消除，要么在节点等式变为 [eq_refl] 后由 [reflexivity] 关闭。没有 UIP 假设，也没有可判定性假设出现在任何地方。

 其他强度测量，都是实际测量而非估算。

 两个三角形在整个同态记录的莱布尼茨等式下都成立，[QuiverCopair_Inl] 和 [QuiverCopair_Inr] 通过 [eq_refl] — 这是 Constructions.v 对其两个投影报告的相同结果，原因相同：[QuiverComp] 的敬重性字段被合成为两个给定字段的组合，与 [QuiverInl] 携带的身份组合会保持共对的自身字段，然后在每个构造函数处进行 iota 化简。这个标题的早期草稿声称了一个不存在的常量，这里将其记录为不良证据而不是删除。它写道：“[QuiverCoswap_is_copair] 是 [eq_refl] ... 记录而非断言”。树中没有这样的常量，下面的正文从术语上说则相反：[QuiverCoswap] 被作为定义（[QuiverCopair QuiverInr QuiverInl]），所以没有什么可记录的，也没有第二个候选项其一致性值得测量。“记录而非断言”这个短语是该文件自己的诚实词汇，使得虚构的测量被读作已检查的测量。[QuiverCoswap_invol] 只是  [≈]  ——  [eq_refl] 形式曾被尝试过但因真正的转换失败而被拒绝 —— 原因与其兄弟报告的相同，是从另一侧遇到的。那里 [QuiverSwap_invol] 失败是因为满射配对对于标准库的 [prod] 并非定义性；在这里，双重交换 quiver 的节点操作是对一个匹配的匹配，在 scrutinee 是变量时不会简化，[sum] 也没有 eta 规则。在两种情况下，这都是标准库自身数据类型缺乏定义性 eta 规则，而与构造本身无关。宇宙，每个常数测量并报告其原因。
 [coprod_edges@{o1 h1 p1 o2 h2 p2 o h p}] 仅包含  [h1 <= h]  和
 [h2 <= h]  —— 每个其他级别保持空闲，因为  [Type]  是累积的。
 [coprod_edgeset]  因此  [QuiverCoprod]  还额外包含

 h1 = h2 = h    并且    p1 = p2 = p,识别两个求和项的边缘和证明级别与余积的边缘和证明级别。原因是经过测量的，而不是猜测的：这个构造原封不动地重用了求和项的边缘等价类（[edgeset G a b] 被返回而未更改），且 [Setoid] 在这里不是累积的——带有 [fun (A : Type@{a}) (S : Setoid@{a a} A) => (S : Setoid@{b b} A)] 与 [a < b] 的单独项被拒绝，这是直接检查的，而不是从其他地方获取的。这与 [QuiverProd] 真正不同，[QuiverProd] 构建了一个全新的按组件分类的等价类（[edgeset_prod]），因此可以保持级别分离。三个对象级别在两边保持自由（[o1 <= o]，[o2 <= o]），且 [False_Setoid@{h p}] 带有一个空的约束子句。同态比箭形图的概念要不那么一般，正如 Constructions.v 对其自身报告的那样：[QuiverInl@{o h p}] 和 [QuiverInr@{o h p}] 在一次实例中取得两个直和并添加 [h <= p]，而 [QuiverCopair] 做得更好，将三个对象级别分开，并且仅从 [QuiverCoprod] 中继承 [h1 = h2] 和 [p1 = p2]。通过 [@homset QuiverCategory] — [QuiverCopair_eta]、[QuiverCopair_unique]、[QuiverCopair_respects]、[QuiverCoswap_invol]、[Cocartesian] 实例以及整个保留部分所陈述的一切——将所有涉及的箭形图折叠为单一的 [Quiver@{u u0 u0}] 实例，识别了同态和证明级别。这就是 [QuiverCategory] 自身的行为：它是 [Category] 的一个宇宙实例，因此在其同态集合上量化的任何陈述都是该实例上的陈述。最后
 [QuiverOfCat_Coproduct_iso] 接受 [C : Category@{u u0 u0}] 和
 [D : Category@{u1 u2 u2}]，将两个对象层级分开，但
 确定每个因子的 hom 和 proof 层级；原因是捐赠者，
 Construction/Coproduct.v 被声明为
 [Category@{u u0 u0} -> Category@{u1 u2 u2} -> Category@{u3 u4 u4}]，
 同一现象 Constructions.v 归因于 [Opposite] 和 [Product]。没有在任何地方尝试恢复更一般性，并且这个文件中没有任何内容需要它。未建成的东西。[QuiverCoprod] 并未作为二函子打包，也未定义对同态对的作用（其同类也未为 [QuiverProd] 构建二函子）；零元情况——作为 [QuiverCategory] 初始对象的空箭簇——未提供，因此此处 [Cocartesian] 是二元的，且未声明 [Initial QuiverCategory] 实例；[Forgetful] 并未被证明作为函子在一般情况下保持余积（该比较仅在 C 和 D 中逐点展示，其在 C 和 D 中的自然性未被证明）；该对应关系未在 [Sets] 中作为同态集之间的双射打包，尽管内容存在——该实例的 [ump_products] 字段连同 [QuiverCopair_respects] 恰好是这种双射所需的，缺少的仅是打包（以及对 Instance/Sets 的依赖）；自由范畴函子或在余积上的行为没有被讨论；并且也没有与 Theory/OGraph.v 建立任何关系，后者的 ×_O 在一个固定的节点集上进行乘法，并且根本没有定义任何余积，所以这里的内容与它无关，那里内容也与此无关。
*)

(*
 SHADOWING GUARD.  Structure/Cocartesian.v defines [inl] and [inr] as the
 coproduct injections of an arbitrary cocartesian category, which shadow
 [Datatypes.inl] and [Datatypes.inr].  Every constructor of [sum] below is
 therefore written qualified, following Instance/Cat/Cocartesian.v and
 Construction/Free/Quiver/Constructions.v.

 [Open Scope category_scope] is DEFENSIVE here, not required, and that was
 measured rather than assumed: the file compiles unchanged with the line
 deleted.  The hazard it guards against is real in general — three scopes
 declare [_ ^op], and [QuiverCategory^op] occurs below in an argument
 position — but the competing notation is declared in Functor/Opposite.v
 , which also opens functor_scope and which this file does not
 import.  Theory/Functor.v opens functor_scope too but declares no
 [^op] in it, so nothing here shadows Construction/Opposite.v's. 

 --------
 影子守卫。Structure/Cocartesian.v 定义了 [inl] 和 [inr] 作为任意余笛卡尔范畴的余积注入，它们影射 [Datatypes.inl] 和 [Datatypes.inr]。因此，下面 [sum] 的每一个构造函数都用限定形式书写，遵循 Instance/Cat/Cocartesian.v 和 Construction/Free/Quiver/Constructions.v。[Open Scope category_scope] 在这里是防御性的，不是必需的，这是经过测量而不是假设的：删除该行后文件仍能编译。它所防护的风险在一般情况下是真实存在的——三个作用域声明了 [_ ^op]，并且 [QuiverCategory^op] 出现在下方的参数位置——但是竞争符号在 Functor/Opposite.v 中声明，该文件也打开了 functor_scope，而本文件并未导入它。Theory/Functor.v 也打开了 functor_scope，但未在其中声明 [^op]，因此这里不会遮蔽 Construction/Opposite.v 的内容。
*)
Local Open Scope category_scope.

Local Notation "Q ⇨ Q'" := (QuiverHomomorphism Q Q') (at level 40).
Local Existing Instance edgeset.

(** ** The empty edge setoid / ** 空边集合体 *)

(*
 The cross-summand edge sets are empty, and an empty type carries exactly
 one setoid.  All three [Equivalence] fields are written as explicit terms
 rather than discharged by a tactic or by [Program]: the tree runs
 [Unset Transparent Obligations] (Lib/Tactics.v) and [Setoid] has
 primitive projections with eta, so an obligation-built proof would be an
 opaque constant sitting inside [QuiverCoprod] and would defeat the
 [eq_refl] measurements below.  The spelling follows [edgeset_prod] of
 Construction/Free/Quiver/Constructions.v. 

 --------
 交叉加法项的边集是空的，而空类型恰好携带一个集合等价关系。所有三个  [Equivalence]  字段都是以显式项写出的，而不是通过策略或 [Program]  解决：该树运行 [Unset Transparent Obligations]  （Lib/Tactics.v），并且 [Setoid]  有带 eta 的原始投影，因此基于义务构建的证明将是一个位于 [QuiverCoprod] 内的不透明常数，并且会破坏下面的 [eq_refl]  测量。拼写遵循 Construction/Free/Quiver/Constructions.v 中的 [edgeset_prod]。
*)
Definition False_Setoid@{h p} : Setoid@{h p} False := {|
  equiv := fun f (_ : False) => match f return Type@{p} with end;
  setoid_equiv :=
    {| Equivalence_Reflexive := fun x : False => match x with end
     ; Equivalence_Symmetric := fun x : False => match x with end
     ; Equivalence_Transitive := fun x : False => match x with end |}
|}.

(** ** The coproduct quiver / ** 共积箭形图 *)

Section CoproductQuiver.

(*
 The edge family: an edge between two left nodes is a left edge, between
 two right nodes a right edge, and there are NO edges between a left node
 and a right node in either direction.  [False] is used for the two cross
 cases exactly as Construction/Coproduct.v uses it for the cross hom-sets
 of C ∐ D. 

 --------
 边族：两个左节点之间的边是左边，两个右节点之间的边是右边，并且左节点和右节点之间在任一方向上都没有边。[False] 用于两个交叉情况，正如 Construction/Coproduct.v 用它处理 C ∐ D 的交叉同态集一样。
*)
Definition coprod_edges@{o1 h1 p1 o2 h2 p2 o h p}
  (G : Quiver@{o1 h1 p1}) (H : Quiver@{o2 h2 p2})
  (x y : (@nodes G + @nodes H)%type) : Type@{h} :=
  match x with
  | Datatypes.inl a =>
      match y with
      | Datatypes.inl b => @edges G a b
      | Datatypes.inr _ => False
      end
  | Datatypes.inr a =>
      match y with
      | Datatypes.inl _ => False
      | Datatypes.inr b => @edges H a b
      end
  end.

(*
 The edge setoid, by the same case analysis.  Note that the summand's own
 setoid is handed back unchanged; see the header for the universe
 identification this forces and why it does not arise for the product. 

 --------
 通过相同的情况分析得到边集合。注意，加数自身的集合保持不变；参见头部的宇宙识别，这会导致这种情况，以及为什么它不会出现在乘积中。
*)
Definition coprod_edgeset@{o1 h1 p1 o2 h2 p2 o h p}
  (G : Quiver@{o1 h1 p1}) (H : Quiver@{o2 h2 p2})
  (x y : (@nodes G + @nodes H)%type)
  : Setoid@{h p} (coprod_edges@{o1 h1 p1 o2 h2 p2 o h p} G H x y) :=
  match x with
  | Datatypes.inl a =>
      match y with
      | Datatypes.inl b => @edgeset G a b
      | Datatypes.inr _ => False_Setoid
      end
  | Datatypes.inr a =>
      match y with
      | Datatypes.inl _ => False_Setoid
      | Datatypes.inr b => @edgeset H a b
      end
  end.

Definition QuiverCoprod@{o1 h1 p1 o2 h2 p2 o h p}
  (G : Quiver@{o1 h1 p1}) (H : Quiver@{o2 h2 p2}) : Quiver@{o h p} := {|
  nodes   := (@nodes G + @nodes H)%type;
  edges   := coprod_edges@{o1 h1 p1 o2 h2 p2 o h p} G H;
  edgeset := coprod_edgeset@{o1 h1 p1 o2 h2 p2 o h p} G H
|}.

(* What the fields unfold to, recorded rather than described. / 田野展开的景象，被记录而不是描述。 *)

Definition QuiverCoprod_nodes@{o1 h1 p1 o2 h2 p2 o h p}
  (G : Quiver@{o1 h1 p1}) (H : Quiver@{o2 h2 p2}) :
  @nodes (QuiverCoprod@{o1 h1 p1 o2 h2 p2 o h p} G H)
    = (@nodes G + @nodes H)%type := eq_refl.

Context {G H : Quiver}.

Definition QuiverCoprod_edges_ll (a b : @nodes G) :
  @edges (QuiverCoprod G H) (Datatypes.inl a) (Datatypes.inl b)
    = @edges G a b := eq_refl.

Definition QuiverCoprod_edges_rr (a b : @nodes H) :
  @edges (QuiverCoprod G H) (Datatypes.inr a) (Datatypes.inr b)
    = @edges H a b := eq_refl.

(*
 The two clauses that make the union DISJOINT, stated as equations. 

 --------
 使联合不相交的两个子句，表示为方程。
*)

Definition QuiverCoprod_edges_lr (a : @nodes G) (b : @nodes H) :
  @edges (QuiverCoprod G H) (Datatypes.inl a) (Datatypes.inr b)
    = False := eq_refl.

Definition QuiverCoprod_edges_rl (a : @nodes H) (b : @nodes G) :
  @edges (QuiverCoprod G H) (Datatypes.inr a) (Datatypes.inl b)
    = False := eq_refl.

(*
 …and again as eliminators, which is the form a consumer wants.  Both are
 the identity function: the edge set IS [False], so nothing is proved by
 these beyond making the fact quotable. 

 --------
 ……再次作为消除器，这是消费者想要的形式。两者都是恒等函数：边集就是[False]，因此这些除了让这个事实可以引用之外，并没有证明任何东西。
*)

Definition quiver_coprod_no_edge_lr (a : @nodes G) (b : @nodes H)
  (e : @edges (QuiverCoprod G H) (Datatypes.inl a) (Datatypes.inr b))
  : False := e.

Definition quiver_coprod_no_edge_rl (a : @nodes H) (b : @nodes G)
  (e : @edges (QuiverCoprod G H) (Datatypes.inr a) (Datatypes.inl b))
  : False := e.

(*
 Distinctness of the two families of nodes.  This one is not definitional
 and is not vacuous: it is what says the union is tagged. 

 --------
 这两类节点的区别。这不是定义性的，也不是空洞的：它说明了并集是有标记的。
*)
Definition quiver_coprod_nodes_disjoint (a : @nodes G) (b : @nodes H)
  (p : @eq (@nodes (QuiverCoprod G H))
         (Datatypes.inl a) (Datatypes.inr b)) : False.
Proof. discriminate p. Defined.

End CoproductQuiver.

(** ** The two injections / ** 两次注射 *)

Section Injections.

(*
 Both injections are the identity on edges: [edges (QuiverCoprod G H)
 (inl x) (inl y)] iota-reduces to [edges G x y], so no map is needed and
 respectfulness is the identity too. 

 --------
 两个注射在边上都是恒等映射: [edges (QuiverCoprod G H) (inl x) (inl y)] iota-归约为 [edges G x y]，所以不需要映射，并且保持性也是恒等映射。
*)

Definition QuiverInl@{o h p} {G H : Quiver@{o h p}} : G ⇨ QuiverCoprod G H :=
  Build_QuiverHomomorphism G (QuiverCoprod G H)
    Datatypes.inl
    (fun x y (e : @edges G x y) => e)
    (fun x y f g (e : f ≈ g) => e).

Definition QuiverInr@{o h p} {G H : Quiver@{o h p}} : H ⇨ QuiverCoprod G H :=
  Build_QuiverHomomorphism H (QuiverCoprod G H)
    Datatypes.inr
    (fun x y (e : @edges H x y) => e)
    (fun x y f g (e : f ≈ g) => e).

End Injections.

(** ** The copairing / ** 配对 *)

Section Copair.

Context {G H R : Quiver}.
Context (F : G ⇨ R) (F' : H ⇨ R).

Definition copair_nodes (x : @nodes (QuiverCoprod G H)) : @nodes R :=
  match x with
  | Datatypes.inl a => F a
  | Datatypes.inr b => F' b
  end.

Definition copair_edges (x y : @nodes (QuiverCoprod G H))
  : @edges (QuiverCoprod G H) x y
      -> @edges R (copair_nodes x) (copair_nodes y).
Proof.
  destruct x as [a|a], y as [b|b]; cbn.
  - exact (@fedgemap _ _ F a b).
  - exact (fun e => match e with end).
  - exact (fun e => match e with end).
  - exact (@fedgemap _ _ F' a b).
Defined.

Definition copair_edges_respects (x y : @nodes (QuiverCoprod G H))
  : Proper (equiv ==> equiv) (copair_edges x y).
Proof.
  destruct x as [a|a], y as [b|b]; cbn.
  - exact (@fedgemap_respects _ _ F a b).
  - intros e; exact (match e with end).
  - intros e; exact (match e with end).
  - exact (@fedgemap_respects _ _ F' a b).
Defined.

Definition QuiverCopair : QuiverCoprod G H ⇨ R :=
  Build_QuiverHomomorphism (QuiverCoprod G H) R
    copair_nodes copair_edges copair_edges_respects.

End Copair.

Arguments QuiverCopair {G H R} F F'.

(* * ** The universal property of the coproduct quiver / * ** 余积箭宿的泛性质 *)

Section CoproductUniversal.

Context {G H R : Quiver}.

(*
 BOTH TRIANGLES hold at LEIBNIZ EQUALITY of the whole homomorphism record,
 not merely up to [≈].  [QuiverComp] synthesises the composite's
 respectfulness field as the composite of the two given ones, and
 [QuiverInl] contributes the identity there, so what remains is the
 copairing's own field read at [inl], which iota-reduces to [F]'s. 

 --------
 两个三角形在莱布尼茨整体同态记录上成立，不仅仅是在 [≈] 下成立。[QuiverComp] 将复合体的尊重域综合为两个给定域的复合，而 [QuiverInl] 在那里贡献了恒等，因此剩下的是在 [inl] 读取的共对的自身域，它通过 iota 归约为 [F] 的域。
*)

Definition QuiverCopair_Inl (F : G ⇨ R) (F' : H ⇨ R) :
  @compose QuiverCategory G (QuiverCoprod G H) R (QuiverCopair F F')
    QuiverInl = F := eq_refl.

Definition QuiverCopair_Inr (F : G ⇨ R) (F' : H ⇨ R) :
  @compose QuiverCategory H (QuiverCoprod G H) R (QuiverCopair F F')
    QuiverInr = F' := eq_refl.

(*
 The eta law.  Unlike the product's, this one needs no surjectivity
 principle: at each constructor the node action of the rebuilt copairing
 is the original one on the nose, so every node equality is [eq_refl] and
 the transports in the edge coherence vanish. 

 --------
 η定律。与产品不同，这个定律不需要满射性原则：在每个构造器处，重建的余配对的节点动作完全等同于原来的动作，因此每个节点等式都是 [eq_refl]，并且边缘一致性中的传输消失。
*)
Definition QuiverCopair_eta (M : QuiverCoprod G H ⇨ R) :
  @equiv _ (@homset QuiverCategory (QuiverCoprod G H) R)
    M (QuiverCopair
         (@compose QuiverCategory G (QuiverCoprod G H) R M QuiverInl)
         (@compose QuiverCategory H (QuiverCoprod G H) R M QuiverInr)).
Proof.
  unshelve eexists.
  - intros [a|a]; reflexivity.
  - intros [a|a] [b|b] e; try (exact (match e with end)); cbn; reflexivity.
Defined.

(*
 Uniqueness, with hypotheses at [≈].  READ THE CONTRAST with
 [QuiverPair_unique] (Construction/Free/Quiver/Constructions.v), whose
 hypotheses are Leibniz equalities of the two composites: here the
 [≈]-form is available, because the node family of the hypothesis is
 consumed constructor by constructor rather than assembled into an
 equality of pairs.  The two edge-coherence obligations ARE the
 hypotheses' own, at the corresponding constructor. 

 --------
 唯一性，在假设 [≈] 中。对比阅读 [QuiverPair_unique]（Construction/Free/Quiver/Constructions.v），其假设是两个复合的莱布尼茨等式：这里可用 [≈] 形式，因为假设的节点族是逐个构造器消耗的，而不是组装成成对的等式。这两个边一致性义务是对应构造器上假设自身的义务。
*)
Definition QuiverCopair_unique (M : QuiverCoprod G H ⇨ R)
  (F : G ⇨ R) (F' : H ⇨ R)
  (p : @equiv _ (@homset QuiverCategory G R)
         (@compose QuiverCategory G (QuiverCoprod G H) R M QuiverInl) F)
  (q : @equiv _ (@homset QuiverCategory H R)
         (@compose QuiverCategory H (QuiverCoprod G H) R M QuiverInr) F') :
  @equiv _ (@homset QuiverCategory (QuiverCoprod G H) R)
    M (QuiverCopair F F').
Proof.
  destruct p as [pn pc], q as [qn qc].
  unshelve eexists.
  - intros [a|a]; [ exact (pn a) | exact (qn a) ].
  - intros [a|a] [b|b] e; try (exact (match e with end)).
    + exact (pc a b e).
    + exact (qc a b e).
Defined.

(*
 Respectfulness of the copairing in both arguments — the statement
 Constructions.v leaves open on the product side, and the reason
 uniqueness above can take [≈] hypotheses. 

 --------
 在两个论证中共同配对的尊重性——语句 Constructions.v 在乘积端保持开放，并且上述唯一性原因可以使用 [≈] 假设。
*)
Definition QuiverCopair_respects :
  Proper (@equiv _ (@homset QuiverCategory G R) ==>
          @equiv _ (@homset QuiverCategory H R) ==>
          @equiv _ (@homset QuiverCategory (QuiverCoprod G H) R))
         (@QuiverCopair G H R).
Proof.
  intros F1 F2 [pn pc] F1' F2' [qn qc].
  unshelve eexists.
  - intros [a|a]; [ exact (pn a) | exact (qn a) ].
  - intros [a|a] [b|b] e; try (exact (match e with end)).
    + exact (pc a b e).
    + exact (qc a b e).
Defined.

End CoproductUniversal.

(** ** Exchange of the two summands / ** 两个加数的交换 *)

(*
 The exchange of summands is DEFINED as the copairing of the two
 injections in the other order — the coproduct-side reading of
 [QuiverSwap_is_pair] (Construction/Free/Quiver/Constructions.v), taken as
 the definition rather than recorded afterwards, since there is no second
 candidate here whose agreement would be worth measuring. 

 --------
 和项的交换被定义为以另一顺序的两个注入的余配对——在余积方面读取 [QuiverSwap_is_pair]（Construction/Free/Quiver/Constructions.v），作为定义而非事后记录，因为这里没有第二个候选者，其一致性值得衡量。
*)
Definition QuiverCoswap {G H : Quiver} :
  QuiverCoprod G H ⇨ QuiverCoprod H G := QuiverCopair QuiverInr QuiverInl.

(*
 Only [≈], and for the dual of the sibling's reason.  There
 [QuiverSwap_invol] cannot be [eq_refl] because surjective pairing is not
 definitional for [prod]; here the node action of the twice-exchanged
 quiver is a match on a match, which does not reduce while the scrutinee
 is a variable — [sum] has no eta rule at all.  The [eq_refl] form was
 tried first and rejected. 

 --------
 只有 [≈]，并且出于兄弟原因的对偶。那里 [QuiverSwap_invol] 不能是 [eq_refl]，因为满射配对对于 [prod] 并不是定义性的；这里两次交换的箭形的节点操作是匹配的匹配，这在被检验者是变量时不会简化——[sum] 根本没有 eta 规则。[eq_refl] 形式最先尝试过，但被拒绝。
*)
Definition QuiverCoswap_invol {G H : Quiver} :
  @equiv _ (@homset QuiverCategory (QuiverCoprod G H) (QuiverCoprod G H))
    (@compose QuiverCategory (QuiverCoprod G H) (QuiverCoprod H G)
       (QuiverCoprod G H) (@QuiverCoswap H G) (@QuiverCoswap G H))
    (@id QuiverCategory (QuiverCoprod G H)).
Proof.
  unshelve eexists.
  - intros [a|a]; reflexivity.
  - intros [a|a] [b|b] e; try (exact (match e with end)); reflexivity.
Defined.

(* * ** QuiverCategory has binary coproducts / * ** QuiverCategory 有二元余积 *)

(*
 [Cocartesian C] is notation for [@Cartesian (C^op)]
 (Structure/Cocartesian.v), so this instance literally exhibits
 [QuiverCategory^op] as cartesian.  Read in the opposite, [exl]/[exr] are
 the two injections, [fork] is the copairing, [fork_respects] is
 [QuiverCopair_respects], and [ump_products] is

 M ≈ [F, F']  ↔  (M ∘ inl ≈ F) * (M ∘ inr ≈ F'),

 whose forward direction is [compose_respects] against the two triangles
 (which, being [eq_refl], need no rewriting step at all) and whose
 backward direction is [QuiverCopair_unique].

 The record is built by [refine] against [@Build_Cartesian
 (QuiverCategory^op)] rather than by the [{| … |}] syntax, deliberately:
 the anonymous record notation infers the class's implicit category from
 [product_obj]'s type, and since [obj[C^op]] is [obj[C]] definitionally it
 picks [QuiverCategory] rather than its opposite, after which [fork]'s
 remaining fields fail to typecheck with a misleading message. 

 --------
 [Cocartesian C] 是 [@Cartesian (C^op)] (Structure/Cocartesian.v) 的表示法，因此这个实例字面上展示了 [QuiverCategory^op] 为笛卡尔积。反过来看，[exl] / [exr] 是两个注入，[fork] 是共配对，[fork_respects] 是 [QuiverCopair_respects]，并且 [ump_products] 是

 M ≈ [F, F'] ↔ (M ∘ inl ≈ F) * (M ∘ inr ≈ F'),

 其正向方向是 [compose_respects] 对应两个三角形（它们为 [eq_refl]，完全不需要重写步骤），其反向方向是 [QuiverCopair_unique]。该记录是由 [refine] 针对 [@Build_Cartesian (QuiverCategory^op)] 构建的，而不是使用 [{| … |}] 语法，这是故意的：匿名记录表示法从 [product_obj] 的类型中推断出类的隐式类别，并且由于 [obj[C^op] ] 在定义上是 [obj[C] ]，它选择了 [QuiverCategory] 而不是它的对偶，然后 [fork] 的其余字段由于类型检查失败而显示出误导信息。
*)
#[export] Instance QuiverCategory_Cocartesian : @Cocartesian QuiverCategory.
Proof.
  unshelve refine (@Build_Cartesian (QuiverCategory^op)
                     QuiverCoprod
                     (fun _ _ _ F F' => QuiverCopair F F')
                     (fun _ _ => QuiverInl)
                     (fun _ _ => QuiverInr)
                     _ _).
  - intros x y z; exact QuiverCopair_respects.
  - simpl; intros x y z F F' M; split.
    + intro Heq; split.
      * exact (@compose_respects QuiverCategory _ _ _ _ _ Heq _ _
                 (reflexivity QuiverInl)).
      * exact (@compose_respects QuiverCategory _ _ _ _ _ Heq _ _
                 (reflexivity QuiverInr)).
    + intros [p q]; exact (QuiverCopair_unique M F F' p q).
Defined.

(*
 The derived vocabulary of Structure/Cocartesian.v, pinned to the named
 constants by [eq_refl] so that the orientation is fixed by computation
 rather than by prose. 

 --------
 Structure/Cocartesian.v 的派生词汇，由 [eq_refl] 固定到命名常量，以便方向由计算而不是由文字说明固定。
*)

Definition Coprod_is_QuiverCoprod (G H : Quiver) :
  @Coprod QuiverCategory QuiverCategory_Cocartesian G H
    = QuiverCoprod G H := eq_refl.

Definition cocartesian_inl_is_QuiverInl (G H : Quiver) :
  @Structure.Cocartesian.inl QuiverCategory QuiverCategory_Cocartesian G H
    = @QuiverInl G H := eq_refl.

Definition cocartesian_inr_is_QuiverInr (G H : Quiver) :
  @Structure.Cocartesian.inr QuiverCategory QuiverCategory_Cocartesian G H
    = @QuiverInr G H := eq_refl.

Definition merge_is_QuiverCopair {G H R : Quiver} (F : G ⇨ R) (F' : H ⇨ R) :
  @merge QuiverCategory QuiverCategory_Cocartesian R G H F F'
    = QuiverCopair F F' := eq_refl.

(* * ** Preservation by the forgetful functor / * ** 通过忘记函子保持 *)

Section Preservation.

Context (C D : Category).

(* Objects: the node types agree on the nose. / 对象：节点类型完全一致。 *)
Definition QuiverOfCat_Coproduct_nodes :
  @nodes (QuiverOfCat (C ∐ D))
    = @nodes (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D)) := eq_refl.

(*
 Edges: all four cases agree on the nose AT CONSTRUCTOR ARGUMENTS,
 including the two cross cases where both sides are [False].  As functions
 of two variable nodes the two [edges] fields are NOT convertible, and
 neither are the whole [Quiver] records; see the header for the two
 independent causes. 

 --------
 边缘：所有四种情况在构造函数参数上完全一致，包括两种交叉情况，其中两边都是 [False]。作为两个变量节点的函数，两个 [edges] 字段不可转换，整个 [Quiver] 记录也不可转换；有关两个独立原因，请参见头部。
*)

Definition QuiverOfCat_Coproduct_edges_ll (a b : obj[C]) :
  @edges (QuiverOfCat (C ∐ D)) (Datatypes.inl a) (Datatypes.inl b)
    = @edges (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D))
        (Datatypes.inl a) (Datatypes.inl b) := eq_refl.

Definition QuiverOfCat_Coproduct_edges_rr (a b : obj[D]) :
  @edges (QuiverOfCat (C ∐ D)) (Datatypes.inr a) (Datatypes.inr b)
    = @edges (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D))
        (Datatypes.inr a) (Datatypes.inr b) := eq_refl.

Definition QuiverOfCat_Coproduct_edges_lr (a : obj[C]) (b : obj[D]) :
  @edges (QuiverOfCat (C ∐ D)) (Datatypes.inl a) (Datatypes.inr b)
    = @edges (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D))
        (Datatypes.inl a) (Datatypes.inr b) := eq_refl.

Definition QuiverOfCat_Coproduct_edges_rl (a : obj[D]) (b : obj[C]) :
  @edges (QuiverOfCat (C ∐ D)) (Datatypes.inr a) (Datatypes.inl b)
    = @edges (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D))
        (Datatypes.inr a) (Datatypes.inl b) := eq_refl.

(*
 The comparison, in both directions.  Every branch is the identity: on
 nodes because the two node types are the same type, on edges because the
 four equations above are [eq_refl], and in the two cross cases because
 both sides are [False] (either branch would do; the identity is taken so
 that no case is special). 

 --------
 双向的比较。每个分支都是恒等：在节点上，因为两种节点类型是相同类型；在边上，因为上述四个方程是 [eq_refl]；而在两个交叉情况中，因为两边都是 [False]（任一分支都可以；取恒等是为了没有特殊情况）。
*)

Definition QuiverOfCat_Coproduct_to :
  QuiverOfCat (C ∐ D) ⇨ QuiverCoprod (QuiverOfCat C) (QuiverOfCat D).
Proof.
  unshelve eapply Build_QuiverHomomorphism.
  - exact Datatypes.id.
  - intros x y; destruct x as [a|a], y as [b|b];
      solve [ exact (fun e => e) | exact (fun e : False => match e with end) ].
  - intros x y; destruct x as [a|a], y as [b|b];
      solve [ exact (fun f g e => e)
            | exact (fun f : False => match f with end) ].
Defined.

Definition QuiverOfCat_Coproduct_from :
  QuiverCoprod (QuiverOfCat C) (QuiverOfCat D) ⇨ QuiverOfCat (C ∐ D).
Proof.
  unshelve eapply Build_QuiverHomomorphism.
  - exact Datatypes.id.
  - intros x y; destruct x as [a|a], y as [b|b];
      solve [ exact (fun e => e) | exact (fun e : False => match e with end) ].
  - intros x y; destruct x as [a|a], y as [b|b];
      solve [ exact (fun f g e => e)
            | exact (fun f : False => match f with end) ].
Defined.

Definition QuiverOfCat_Coproduct_iso :
  @Isomorphism QuiverCategory (QuiverOfCat (C ∐ D))
    (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D)).
Proof.
  unshelve eapply Build_Isomorphism.
  - exact QuiverOfCat_Coproduct_to.
  - exact QuiverOfCat_Coproduct_from.
  - unshelve eexists.
    + intros [a|a]; reflexivity.
    + intros [a|a] [b|b] e; try (exact (match e with end)); reflexivity.
  - unshelve eexists.
    + intros [a|a]; reflexivity.
    + intros [a|a] [b|b] e; try (exact (match e with end)); reflexivity.
Defined.

(*
 The two inclusion functors.  The tree has none by name:
 Instance/Cat/Cocartesian.v supplies them only as anonymous inline records
 in the [exl]/[exr] fields of [Cat_Cocartesian], and naming them from
 there would cost a dependency on Instance/Cat. 

 --------
 这两个包含函子。该树没有命名的：
 Instance/Cat/Cocartesian.v 仅将它们作为匿名内联记录提供
 在 [Cat_Cocartesian] 的 [exl] / [exr] 字段中，从那里为它们命名将导致对 Instance/Cat 的依赖。
*)

Definition CoproductInl : C ⟶ C ∐ D.
Proof.
  unshelve eapply Build_Functor.
  - exact Datatypes.inl.
  - intros x y f; exact f.
  - intros x y f g Hfg; exact Hfg.
  - intro x; reflexivity.
  - intros x y z f g; reflexivity.
Defined.

Definition CoproductInr : D ⟶ C ∐ D.
Proof.
  unshelve eapply Build_Functor.
  - exact Datatypes.inr.
  - intros x y f; exact f.
  - intros x y f g Hfg; exact Hfg.
  - intro x; reflexivity.
  - intros x y z f g; reflexivity.
Defined.

(*
 Compatibility with the injections: the comparison carries the underlying
 quiver map of each inclusion functor to the corresponding injection, so
 what is preserved is the coproduct DIAGRAM and not merely an object. 

 --------
 与单射的兼容性：比较将每个包含函子所对应的底层箭袋映射携带到相应的单射，因此被保留的是余积图，而不仅仅是一个对象。
*)

Definition Forgetful_preserves_coprod_inl :
  @equiv _ (@homset QuiverCategory (QuiverOfCat C)
              (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D)))
    (@compose QuiverCategory _ _ _ QuiverOfCat_Coproduct_to
       (QuiverHomomorphismOfFunctor _ _ CoproductInl))
    QuiverInl.
Proof.
  unshelve eexists.
  - intro a; reflexivity.
  - intros a b e; reflexivity.
Defined.

Definition Forgetful_preserves_coprod_inr :
  @equiv _ (@homset QuiverCategory (QuiverOfCat D)
              (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D)))
    (@compose QuiverCategory _ _ _ QuiverOfCat_Coproduct_to
       (QuiverHomomorphismOfFunctor _ _ CoproductInr))
    QuiverInr.
Proof.
  unshelve eexists.
  - intro a; reflexivity.
  - intros a b e; reflexivity.
Defined.

End Preservation.

(** ** Non-degeneracy / ** 非退化 *)

(*
 Two small quivers, and concrete facts about their coproduct.  [LoopQ] has
 one node carrying one loop; [TwoQ] has two nodes with two PARALLEL edges
 between every ordered pair, so a homomorphism into it has room to move
 both a node and an edge.  Both are built with
 [Build_Quiver_Standard_Eq], whose edge setoids are Leibniz equality.
 Measured rather than assumed: neither witness is pinned to [Set] — both
 are universe-polymorphic, [LoopQ@{u u0 u1} : Quiver@{u0 u1 u}] and
 [TwoQ@{u u0 u1} : Quiver@{u u0 u1}], each carrying only a bound on the
 proof level coming from the Leibniz setoid, since [poly_unit] is
 polymorphic and [bool : Set] is absorbed by cumulativity.  The usual
 concrete-witness price is therefore not paid here; what does confine the
 STATEMENTS below is [@homset QuiverCategory], as the header records. 

 --------
 两个小箭袋，以及关于它们的余积的具体事实。[LoopQ] 有一个携带一个环的节点；[TwoQ] 有两个节点，每个有序对之间有两条平行边，因此映射到它的同态在节点和边上都有调整空间。两者都是用 [Build_Quiver_Standard_Eq] 构建的，其边集合等价关系是莱布尼茨等式。经过测量而不是假设：没有见证被固定到 [Set]——两者都是宇宙多态的，[LoopQ@{u u0 u1} : Quiver@{u0 u1 u}] 和 [TwoQ@{u u0 u1} : Quiver@{u u0 u1}]，每个仅携带来自莱布尼茨集合等价关系的证明水平的约束，因为 [poly_unit] 是多态的，而 [bool : Set] 被累积性吸收。因此，这里并没有支付通常的具体见证代价；限定下面陈述的，是 [@homset QuiverCategory]，如标题所记录的。
*)

Definition LoopQ : Quiver :=
  Build_Quiver_Standard_Eq poly_unit (fun _ _ => poly_unit).

Definition TwoQ : Quiver :=
  Build_Quiver_Standard_Eq bool (fun _ _ => bool).

(*
 The loop is a genuine edge, and the cross edge sets of the coproduct are
 genuinely empty. 

 --------
 这个环是真正的边，而余积的交叉边集是真正空的。
*)

Definition loop_edge : @edges LoopQ ttt ttt := ttt.

Definition coprod_loop_edge_left :
  @edges (QuiverCoprod LoopQ LoopQ)
    (Datatypes.inl ttt) (Datatypes.inl ttt) := ttt.

Definition coprod_loop_edge_right :
  @edges (QuiverCoprod LoopQ LoopQ)
    (Datatypes.inr ttt) (Datatypes.inr ttt) := ttt.

Definition coprod_no_cross_edge
  (e : @edges (QuiverCoprod LoopQ LoopQ)
         (Datatypes.inl ttt) (Datatypes.inr ttt)) : False := e.

(*
 The two summands are not identified: the injections of [LoopQ] into
 [QuiverCoprod LoopQ LoopQ] are parallel homomorphisms, and they are not
 equivalent.  The proof consumes only the node component of a hypothetical
 equivalence, so no transport and no UIP hypothesis is involved. 

 --------
 这两个加数没有被识别：[LoopQ] 到 [QuiverCoprod LoopQ LoopQ] 的注入是平行同态，并且它们不等价。证明只使用了假设等价的节点分量，因此不涉及传输和 UIP 假设。
*)
Definition injections_not_equivalent
  (p : @equiv _ (@homset QuiverCategory LoopQ (QuiverCoprod LoopQ LoopQ))
         QuiverInl QuiverInr) : False.
Proof. destruct p as [pn _]; discriminate (pn ttt). Defined.

Section Witness.

(*
 Two homomorphisms out of [LoopQ] into [TwoQ] that differ on BOTH the node
 and the edge: one lands on [false] and sends the loop to [false], the
 other lands on [true] and sends the loop to [true]. 

 --------
 从  [LoopQ]  到  [TwoQ]  的两个同态，它们在节点和边上都有所不同：一个映射到  [false] 并将环映射到  [false]，另一个映射到  [true] 并将环映射到  [true]。
*)

Definition Ffalse : LoopQ ⇨ TwoQ :=
  Build_QuiverHomomorphism LoopQ TwoQ
    (fun _ => false) (fun _ _ _ => false) (fun _ _ _ _ _ => eq_refl).

Definition Ftrue : LoopQ ⇨ TwoQ :=
  Build_QuiverHomomorphism LoopQ TwoQ
    (fun _ => true) (fun _ _ _ => true) (fun _ _ _ _ _ => eq_refl).

(*
 The copairing COMPUTES, on nodes and on edges, and differently on the two
 summands: the same loop is carried to [false] from the left and to [true]
 from the right. 

 --------
 共配对在节点和边上计算，并且在两个加数上有所不同：相同的环从左边传递到 [false]，从右边传递到 [true]。
*)

Definition copair_node_left :
  @fnodes _ _ (QuiverCopair Ffalse Ftrue) (Datatypes.inl ttt)
    = false := eq_refl.

Definition copair_node_right :
  @fnodes _ _ (QuiverCopair Ffalse Ftrue) (Datatypes.inr ttt)
    = true := eq_refl.

Definition copair_edge_left :
  @fedgemap _ _ (QuiverCopair Ffalse Ftrue)
    (Datatypes.inl ttt) (Datatypes.inl ttt) ttt = false := eq_refl.

Definition copair_edge_right :
  @fedgemap _ _ (QuiverCopair Ffalse Ftrue)
    (Datatypes.inr ttt) (Datatypes.inr ttt) ttt = true := eq_refl.

(* The two given homomorphisms really are different. / 给定的两个同态确实不同。 *)
Definition Ffalse_neq_Ftrue
  (p : @equiv _ (@homset QuiverCategory LoopQ TwoQ) Ffalse Ftrue) : False.
Proof. destruct p as [pn _]; discriminate (pn ttt). Defined.

(* The copairing depends on the ORDER of its two arguments. / 协配取决于它两个参数的顺序。 *)
Definition copair_order_matters
  (p : @equiv _ (@homset QuiverCategory (QuiverCoprod LoopQ LoopQ) TwoQ)
         (QuiverCopair Ffalse Ftrue) (QuiverCopair Ftrue Ffalse)) : False.
Proof. destruct p as [pn _]; discriminate (pn (Datatypes.inl ttt)). Defined.

(*
 A COMPETITOR for the uniqueness clause: a homomorphism out of the
 coproduct which fails the first triangle.  Constructions.v discloses that
 its product-side uniqueness clause has no such witness; this is the
 coproduct-side supply.  The composite with [QuiverInl] is [Ftrue] by
 [QuiverCopair_Inl] — a Leibniz equation — so the goal reduces to
 [Ftrue ≈ Ffalse], which [Ffalse_neq_Ftrue] refutes. 

 --------
 唯一性条款的一个竞争者：一个从余积出的同态，它未能满足第一个三角形。Constructions.v 说明它的积侧唯一性条款没有这样的实例；这是余积侧的提供。与 [QuiverInl] 的复合是 [Ftrue] 由 [QuiverCopair_Inl] —— 一个莱布尼茨方程 —— 因此目标归结为 [Ftrue ≈ Ffalse]，而 [Ffalse_neq_Ftrue] 否定了它。
*)
Definition copair_swap_fails_left
  (p : @equiv _ (@homset QuiverCategory LoopQ TwoQ)
         (@compose QuiverCategory LoopQ (QuiverCoprod LoopQ LoopQ) TwoQ
            (QuiverCopair Ftrue Ffalse) QuiverInl)
         Ffalse) : False.
Proof. destruct p as [pn _]; discriminate (pn ttt). Defined.

Definition copair_swap_fails_right
  (p : @equiv _ (@homset QuiverCategory LoopQ TwoQ)
         (@compose QuiverCategory LoopQ (QuiverCoprod LoopQ LoopQ) TwoQ
            (QuiverCopair Ftrue Ffalse) QuiverInr)
         Ftrue) : False.
Proof. destruct p as [pn _]; discriminate (pn ttt). Defined.

End Witness.
