Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Open Scope category_scope.

(* * * Limits from products and equalizers / * * 来自产品和均衡器的限制 *)

(*
 Mac Lane, Categories for the Working Mathematician, 2nd ed., §V.2
 Theorems 1 and 2 and Corollary 2 (book p. 113), §V.4 Exercise 2 (book
 p. 118); Riehl, Category Theory in Context, 2nd ed., §3.2 Theorem 3.2.11,
 Remark 3.2.13, Exercise 3.2.ii and §3.5 Theorem 3.5.11; Awodey, Category
 Theory, §5.4 Proposition 5.23, Corollary 5.24 and Theorem 5.25.

 The central existence theorem for limits.  A category with products
 indexed by the objects of a shape J and by the arrows of J, and with
 equalizers, has a limit for every diagram F : J ⟶ C: the equalizer of
 the two canonical maps

 s, t : ∏_{x ∈ ob J} F x  ⇉  ∏_{f ∈ mor J} F (cod f),

 whose components at f are the projection at cod f and the diagram's
 action fmap[F] f after the projection at dom f (Riehl's Remark 3.2.13,
 the element-free description), with legs the object projections after
 the equalizing map.  Hence products plus equalizers give completeness,
 dually coproducts plus coequalizers give cocompleteness, and a functor
 preserving both primitives preserves every limit.

 WHAT IS BUILT, and at what strength.

 (A) [pe_iprod_ext]: two maps into an indexed product agreeing under
 every projection are equal — the uniqueness clause of [iprod_desc]
 as an extensionality principle.  Structure/Bicartesian/Matrix.v's
 [iprod_ext] states the same fact but drags an [IsIndexedCoproduct]
 in from its section; the four-line restatement is disclosed.

 (B) [ArrowIx J := {p : obj J * obj J & fst p ~> snd p}], Mac Lane's
 index ∏_{f ∈ mor J}, with [aix_dom]/[aix_cod]/[aix_arr] and
 [mk_arrow] (readbacks at [eq_refl]).  [Gen idx_arr f] is the
 inductive closure of an arbitrary family of arrows under identities,
 composition and [≈]; [Generates idx_arr] says the family reaches
 every arrow, and [ArrowIx_Generates] discharges it at the full
 index in one constructor.

 (C) Section [Core], ELEMENTARY: over any two [IsIndexedProduct]s, any
 [s t] satisfying the two component equations at a GENERATING
 family, and any [IsEqualizer s t E e], the cone [pe_cone] (apex E,
 legs [projP x ∘ e]) is limiting: [pe_limiting] is Theorem 1.  Cone
 coherence is ONE induction over [Gen] whose only case with content
 is the indexed arrow, closed by the two component equations and
 [fork_eq]; the mediator is [eq_desc] of the tupling of the
 competing cone, the tupling equalizes by [pe_iprod_ext] at Q
 through cone coherence, and uniqueness is the product's uniqueness
 clause followed by the equalizer's.  The section runs under
 [Set Default Proof Using “All”], so every constant of it takes the
 whole context in the order it is declared.

 (D) Section [FromClasses], over [HasIndexedProducts C] and
 [HasEqualizers C]: [pe_obj_product], [pe_arrow_product], [pe_s],
 [pe_t] (by [iprod_desc], Remark 3.2.13), [pe_equalizer], [pe_apex],
 [pe_incl], [pe_limit_cone], [pe_limit_limiting], and the pinned
 [limit_of_products_equalizer F : Limit F].  Theorem 2's explicit
 description is read back at [eq_refl]: the limit's apex IS
 [pe_apex] and its leg at x IS [pe_obj_proj x ∘ pe_incl].

 (E) Corollary 2: [Complete_from_products_equalizers] (pinned), and its
 dual [Cocomplete_from_coproducts_coequalizers] (pinned by Riehl's
 §3.5 checkbox) as the primal theorem at C^op through
 [HasEqualizers_op_of_HasCoequalizers]
 (Structure/Pullback/Reduction.v) and [Opposite_Functor], a [:=]
 with no tactic — [HasIndexedCoproducts C] IS [HasIndexedProducts
 (C^op)] (Structure/Limit/Coproduct.v, #254, which is why the
 issue's “add HasIndexedCoproducts” checkbox needs no work here) and
 [Colimit F] IS [Limit (F^op)].  The colimit-first ORIENTATION is
 therefore delivered as an instantiation, not as a second
 construction: nothing here builds a coequalizer of two coproducts
 covariantly.

 (F) §V.4 Exercise 2: [PreservesIndexedProducts G] and
 [PreservesEqualizers G] are NEW predicates (the image of a product
 with its projections is a product, the image of an equalizer an
 equalizer; measured absent tree-wide at the base commit), and
 [continuous_from_products_equalizers] (pinned) lands in
 Structure/Limit/Preservation.v's cone-level [ContinuousFunctor] —
 the §V.4 notion, since the apex-only class cannot carry the
 conclusion.  The route: the core in D at [G ◯ K] with the G-images
 ([pe_image_s]/[pe_image_t] by [fmap_comp]), transported along
 [pe_image_ConeIso] to [FCone G (pe_limit_cone …)] — an identity
 apex, the legs differing by ONE [fmap_comp] — and then along
 [FCone_iso] of [limitcone_iso] to an arbitrary limiting cone.

 (G) Riehl's Exercise 3.2.ii, generally: section [Refinement] indexes
 the arrow product by ANY generating family, [pe_gen_limiting] makes
 that equalizer limiting, and [pe_gen_restrict_iso] shows the
 restriction does not change the limit — a [ConeIso] to the full
 construction, by [limitcone_iso].  At the full index the refined
 construction IS the construction in apex and every leg (probe
 controls at [eq_refl]) but NOT as a record, the two cones citing
 different [Qed] component lemmas.  Section [Families]:
 [IsIdArrow], [fam_dom]/[fam_cod]/[fam_arr] (a family cut by a
 predicate on [ArrowIx]), [sub_Generates_of_dec] (a predicate
 containing every non-identity arrow generates, given a DECIDER
 [S (mk_arrow f) + IsIdArrow f]), [NonIdArrow] with
 [nonid_Generates] (the non-identity family generates as soon as
 being an identity is decidable), and [AtomicArrow] (non-identity,
 every factorization through two arrows has an identity factor).
 Section [Refined]: [pe_nonid_limiting] under a decider, and
 [pe_atomic_limiting] under the HYPOTHESIS [Generates (fam_arr
 AtomicArrow)] — which IS Riehl's factorization hypothesis, taken
 as a hypothesis and discharged for NO shape here.  Decidability of
 being an identity is not claimed for any shape in this file
 (Test/ProbeFromProducts416.v discharges it on the walking arrow).

 WHY THE CLASS AND NOT [iprod] — the issue's work item 4, DECLINED ON A
 MEASUREMENT.  It asks that the indexed products be routed through
 Instance/Discrete.v's discrete-diagram encoding “so the result composes
 with Structure/Limit/Product.v's existing API rather than introducing a
 rival one”.  The API consumed IS that file's: the class
 [HasIndexedProducts] with [indexed_product]/[indexed_product_proj]/
 [indexed_product_ump], and the elementary [IsIndexedProduct] with
 [iprod_desc]; nothing rival is declared.  What is NOT consumed is that
 file's [iprod]/[iprod_proj]/[iprod_ump].

 RECORDED CORRECTION TO THE REASON.  An earlier revision gave it as:
 “because [iprod@{u u0 u1}] binds [C : Category@{u1 Set Set}] — the
 ambient hom AND proof universes pinned to the literal [Set], through
 [DiscreteCat_Functor] and [Limit] (the #331/#339 measurement) — so a
 theorem routed through it would hold only for Set-homed categories,
 and would have excluded the classes [Complete] is quantified over.
 Pinned as the probe's N8: at a hom level declared strictly above
 [Set], the class, its product and
 [Complete_from_products_equalizers] are accepted while [iprod] is
 refused with [Cannot enforce Set = ch].”  That [Set] floor is GONE:
 [DiscreteCat_Functor] was annotated in place at Instance/Discrete.v
 in the PR “algebraic carriers are sets” (2026-09-17), and measured
 after it [iprod@{u u0 u1 u2 u3}] binds [C : Category@{u1 u2 u2}] with
 no literal [Set].  Probe N8 accordingly turned over and is now a
 positive CONTROL in Test/ProbeFromProducts416.v.  What remains true,
 and is the surviving reason for the choice, is that [iprod] is stated
 through [Limit], which identifies the discrete shape's hom and proof
 universes with the ambient's, where the elementary [IsIndexedProduct]
 imposes no such identification; routing this theorem through the
 elementary form keeps it free of it.

 UNIVERSES, off BOTH binder and block (all 91 constants).
 [limit_of_products_equalizer@{u u0 u1 u2 u3 u4 u5}] is over
 [C : Category@{u1 u2 u2}] and [J : Category@{u3 u4 u4}] — hom
 identified with proof in the BINDER, every constant here — with the
 block equations [u = u3] (the class's index universe IS J's object
 universe: the object product is indexed by [obj J]) and [u2 = u4]
 (shape hom = ambient hom, the limit vocabulary's: [Limit]/[IsLimitCone]
 are refused at a shape whose homs sit strictly below the ambient's
 while [Cone] is accepted, probe N7), C's OBJECT universe free.
 [Complete_from_products_equalizers@{u u0 u1}] over [C : Category@{u u0
 u0}] carries NO block equation — bounds only — and concludes
 [Complete@{u0 u0 u0 u}], the diagram category's objects and homs at
 C's hom level: the same smallness discipline as [Sets_Complete].
 [Cocomplete_from_coproducts_coequalizers] carries the strict [u0 < u]
 of [HasIndexedCoproducts]'s own declaration and no equation.
 [continuous_from_products_equalizers] binds C and D at ONE hom level
 ([Category@{u5 u8 u8}], [Category@{u4 u8 u8}]) with bounds only, as do
 [PreservesIndexedProducts] and [PreservesEqualizers]. [pe_cone] and
 [pe_limiting] bind [J : Category@{u u0 u0}], [C : Category@{u1 u0 u0}]
 — the shape's hom level identified with the ambient's IN THE BINDER,
 which is why probe N7's [pe_cone] refusal fires at the ambient
 argument with the same message as [Limit]'s and corroborates nothing
 about which donor forces it — with bounds only, and the family's index
 [I : Type@{u3}] free of any identification (bounded above by two
 auxiliary levels, [Generates]'s and [IsIndexedProduct]'s); [Gen]'s
 block is LITERALLY EMPTY; [Generates] and [ArrowIx] carry bounds only;
 [pe_gen_restrict_iso] adds [u = u5] (the family's index universe, the
 class supplying ONE index universe per instance).  The hom = proof
 identification has SIX donors each refused alone at [ch < cp] with
 the hom-set, the identity and an endofunctor accepted (probe N6):
 [HasIndexedProducts], [HasEqualizers], [IsIndexedProduct],
 [IsEqualizer], [Limit], [Complete]; none is introduced here and none
 is claimed unavoidable.  ZERO word-bounded [Set] in any binder or
 block; the only two [Set] tokens in the whole [About] dump are the
 motive sorts of the two auto-generated [_rec] eliminators.

 COUNTS.  91/91 constants closed under the global context with ZERO
 [Axioms:] lines — 86 [Print Module] entries (70 [Definition], 14
 [Parameter], 2 [Inductive]) plus the five constructors it lists only
 after a [:=]; all 91 in the [make print-assumptions] gate FULLY
 QUALIFIED.  Closure 38 modules excluding self: dropping
 Structure/Pullback/Reduction costs 9, Structure/Limit/Coproduct and
 Structure/Complete 1 each, every other [Require] 0.  Three [Defined]
 tokens against 14 [Qed], NONE load-bearing — each flipped alone to
 [Qed] leaves this file and the probe compiling — kept [Defined] by the
 data convention.  Five [:= eq_refl] readbacks.  Zero declaration
 collisions over the 91 names plus the probe's, AFTER seven renames
 before landing: [arrow_dom]/[arrow_cod] are Instance/Square.v's,
 [arrow_of] is Theory/Shapes.v's, [sub_dom] is Theory/Subobject.v's
 field, and [two_fam] is Structure/Pullback/Wide.v's.  [make todo]
 grows by 19, ALL in the probe (16 refutation commands + 3 prose
 lines), this file contributing ZERO — so the issue's “adds no new
 hits” box is NOT met as written and is disclosed here.

 Test/ProbeFromProducts416.v carries 16 refutation commands = 1
 instrument + 15 commands pinning EIGHT negatives of THREE kinds told
 apart by the error TEXT — 3 CONVERSION (N1–N3), 2 TYPING (N4–N5; N5's
 message carries a trailing [cannot unify] on the two hom FAMILIES —
 [hom[C]] against [hom[C^op]], the latter printed unfolded as
 [λ x y, y ~> x] — not on two inhabitants of one type), 3
 UNIVERSE (N6–N8, ten commands) — each stripped ONE AT A TIME in a copy
 of the whole file and compiled alone with its error read; guard
 coverage measured mechanically (40 identifiers inside a refutation
 command, 35 also outside, the five exceptions exhaustively the keyword,
 the three refuting [Example] names and the instrument's absent name);
 rename-simulated 7/7 over the target constants the negatives name,
 every break on a [Check] line.
 The probe also carries the [Sets] instantiation — a SECOND inhabitant
 of [@Complete Sets], not compared with [Sets_Complete] and built
 WITHOUT it: products from Instance/Sets/Products.v, equalizers from
 Instance/Sets/Pullback.v's pullbacks through
 [HasEqualizers_of_HasPullbacks_Terminal], and Instance/Sets/Complete.v
 measured absent from the probe's closure (an audit caught a draft
 that fed it Adjunction/GAFT/Sets.v's [Sets_HasEqualizers], which IS
 [Complete_HasEqualizers Sets_Complete]) — and the walking-arrow
 generating family: [_2] has three arrows and the one-index family at
 its non-identity arrow generates.

 PROSE REPOINTED in the same commit: Structure/Complete.v (the edit
 is line neutral, parts of that passage being cited elsewhere), whose
 closing sentence had called [iprod] “the products half of the
 reduction”; Structure/Equalizer.v, whose “Both arguments run in this
 library” was FALSE for the reduction until this file; and two
 passages of Structure/Limit.v (the E.1 LIBRARY-DEFECT: “uniqueness up
 to unique isomorphism” is Structure/Limit/Unique.v's, landed since
 the issue was filed, and the construction is this file's), both line
 neutral.  Structure/Topos.v, which the issue also names, cites the
 PULLBACK reduction (Structure/Pullback/Reduction.v) and not this one,
 so it is untouched; the drift in the issue's citations is recorded
 here.

 NOT DELIVERED.  No covariant coequalizer-of-coproducts construction
 (the dual is the primal at C^op); no finite-shape variant (Awodey's
 Proposition 5.23 is about FINITE diagrams, whose finiteness predicate
 is #417's, and Corollary 5.24's cardinality bookkeeping is replaced
 by universe polymorphism); no [Set] instantiation IN THIS FILE and no
 computing witness (the probe's [Sets] limit is an equalizer built as
 a pullback in Instance/Sets/Pullback.v's agreement sub-setoid over
 Instance/Sets/Products.v's dependent-function product, whose elements
 are not written down); no comparison of the [Sets] instantiation with
 [Sets_Complete]; no shape shown to satisfy the atomic factorization
 hypothesis and no decision procedure for identities; no converse
 (nothing says a complete category has products, that being
 Adjunction/GAFT.v's [Complete_HasEqualizers] for the equalizer half
 and absent for the product half); no naturality of any identification
 in F; nothing registered as an [Instance] — a chosen limit must not
 become globally resolvable. 

 --------
 Mac Lane，《工作数学家的范畴论》，第二版，第V.2节 定理1和2及推论2（书第113页），第V.4节 习题2（书第118页）；Riehl，《情境中的范畴论》，第二版，第3.2节 定理3.2.11，注释3.2.13，习题3.2.ii 和第3.5节 定理3.5.11；Awodey，《范畴论》，第5.4节 命题5.23，推论5.24 和定理5.25。

 极限的中心存在定理。一个范畴如果存在由一个形状J的对象及J的箭头所索引的积，且存在等化器，那么对于每个图 F : J ⟶ C，范畴都存在极限：即两个典型映射的等化器

 s, t : ∏_{x ∈ ob J} F x  ⇉  ∏_{f ∈ mor J} F (cod f)其在 f 的组成部分是 cod f 处的投影以及图的作用 fmap [F] 在 dom f 处投影后的复合（Riehl 的备注 3.2.13，无元素描述），边是经过等化映射后的对象投影。因此，积加上等化器给出完备性，对偶地，余积加上余等化器给出余完备性，而且保持两个原始操作的函子保持每个极限。

 构建的内容，以及其强度。

 (A) [pe_iprod_ext]：两个映射到一个索引积，如果在每个投影下相等，则它们相等——作为外延性原则的 [iprod_desc] 的唯一性条款。Structure/Bicartesian/Matrix.v 中的 [iprod_ext] 陈述了相同的事实，但从其分段中引入了一个 [IsIndexedCoproduct]；四行重述中有所揭示。(B)  [ArrowIx J := {p : obj J * obj J & fst p ~> snd p}]，Mac Lane 的索引 ∏_{f ∈ mor J}，具有 [aix_dom] / [aix_cod] / [aix_arr] 和 [mk_arrow]（在 [eq_refl] 的回读）。[Gen idx_arr f] 是一个任意箭头族在恒等、组合和 [≈] 下的归纳闭包；[Generates idx_arr] 表示该族覆盖每一个箭头，而 [ArrowIx_Generates] 在一个构造子中在完整索引上释放它。(C) [Core] 节，基础：在任意两个 [IsIndexedProduct] 上，任意满足生成族两个分量方程的 [s t]，以及任意 [IsEqualizer s t E e]，锥体 [pe_cone]（顶点 E，边 [projP x ∘ e]）是极限：[pe_limiting] 是定理 1。锥体一致性是对 [Gen] 的一次归纳，其唯一有内容的情况是带索引的箭头，由两个分量方程和 [fork_eq] 闭合；中介者是竞争锥的组合 [eq_desc]，通过锥体一致性在 Q 由 [pe_iprod_ext] 实现等值化，唯一性则是先是积的唯一性条款，然后是等值化器的条款。该节在 [Set Default Proof Using “All”] 下运行，因此其每个常量都按声明顺序取整个上下文。(D) [FromClasses]节，位于[HasIndexedProducts C]和[HasEqualizers C]之上：[pe_obj_product]、[pe_arrow_product]、[pe_s]、[pe_t]（由[iprod_desc]，备注3.2.13）、[pe_equalizer]、[pe_apex]、[pe_incl]、[pe_limit_cone]、[pe_limit_limiting]，以及固定的[limit_of_products_equalizer F : Limit F]。定理2的明确描述在[eq_refl]处回顾：极限的顶点是[pe_apex]，其在x处的边为[pe_obj_proj x ∘ pe_incl]。(E) 推论 2：[Complete_from_products_equalizers]（已固定），及其对偶 [Cocomplete_from_coproducts_coequalizers]（由 Riehl 的 §3.5 复选框固定）作为 C^op 上的原始定理通过 [HasEqualizers_op_of_HasCoequalizers]（Structure/Pullback/Reduction.v）和 [Opposite_Functor]，一个没有策略的 [:=] — [HasIndexedCoproducts C] 是 [HasIndexedProducts (C^op)]（Structure/Limit/Coproduct.v，#254，这也是为什么该问题的“添加 HasIndexedCoproducts”复选框在这里无需操作的原因）及 [Colimit F] 是 [Limit (F^op)]。因此，先取余极限的方向（colimit-first ORIENTATION）作为实例实现，而不是第二种构造：这里没有任何内容协变地构建两个直和的共等化。(F) §V.4 练习 2：[PreservesIndexedProducts G] 和 [PreservesEqualizers G] 是新的谓词（一个积及其投影的像是一个积，一个等化器的像是一个等化器；在基本提交处树范围内测量缺失），而 [continuous_from_products_equalizers]（固定）落入 Structure/Limit/Preservation.v 中的锥级 [ContinuousFunctor] — §V.4 的概念，因为仅顶点类无法承载结论。路线：在 D 中的核心 [G ◯ K] 与 G-像（[pe_image_s] / [pe_image_t] 通过 [fmap_comp]）沿 [pe_image_ConeIso] 运输到 [FCone G (pe_limit_cone …)] — 一个同一顶点，边沿由 ONE [fmap_comp] 区分 — 然后沿 [limitcone_iso] 的 [FCone_iso] 到一个任意的限制锥。(G) Riehl 的练习 3.2.ii，一般来说：章节 [Refinement] 通过任意生成族索引箭头积，[pe_gen_limiting] 使该等化器有限制，并且 [pe_gen_restrict_iso] 表明限制不会改变极限 —— một [ConeIso] 对完整构造的说明，由 [limitcone_iso] 给出。在完整索引下，细化构造就是 apex 中的构造，以及每条腿（在 [eq_refl] 的探针控制下），但不是作为记录，两个锥体引用不同的 [Qed] 组成引理。[Families] 节 ：
 [IsIdArrow]，[fam_dom] / [fam_cod] / [fam_arr]（由 [ArrowIx] 上的谓词切割的一个族），[sub_Generates_of_dec]（一个谓词，包含每个非恒等箭头生成的，在给定一个 DECIDER [S (mk_arrow f) + IsIdArrow f] 的情况下），[NonIdArrow] 与 [nonid_Generates]（非恒等族只要恒等性可判定就会生成），以及 [AtomicArrow]（非恒等，每个通过两个箭头的分解都具有一个恒等因子）。
 [Refined] 节：在一个判断器下的 [pe_nonid_limiting]，以及在假设 [Generates (fam_arr AtomicArrow)] 下的 [pe_atomic_limiting] —— 这就是 Riehl 的分解假设，作为假设而在此没有形状下被解除。关于文件中任何形状是否为同一性的可判定性，并未提出声明（Test/ProbeFromProducts416.v 在行走箭头上进行了处理）。

 为什么选择 CLASS 而不是 [iprod]——这是问题的工作项 4，在一次测量中被拒绝。它要求将索引产品通过 Instance/Discrete.v 的离散图编码路由“以便结果能够与 Structure/Limit/Product.v 的现有 API 组合，而不是引入一个竞争的 API”。所使用的 API 是该文件的：类 [HasIndexedProducts] 以及 [indexed_product] / [indexed_product_proj] / [indexed_product_ump] ，以及基本的 [IsIndexedProduct] 和 [iprod_desc]；未声明任何竞争接口。未使用的是该文件中的 [iprod] / [iprod_proj] / [iprod_ump]。对原因的已记录更正。之前的修订版本为：
 “因为 [iprod@{u u0 u1}] 绑定 [C : Category@{u1 Set Set}] —— 通过 [DiscreteCat_Functor] 和 [Limit]（#331/#339 测量），将环境 hom 和证明宇宙固定到字面 [Set] 上 —— 因此通过它路径的定理仅适用于Set-homed类别，并将排除 [Complete] 所量化的类。作为探针的 N8 固定：在严格高于 [Set] 的 hom 级别声明，该类、其积和 [Complete_from_products_equalizers] 被接受，而 [iprod] 被拒绝，并带有 [Cannot enforce Set = ch]。”
 那个 [Set] 的下限消失了：
 [DiscreteCat_Functor] 被在 PR“代数承载是集合”（2026-09-17）的 Instance/Discrete.v 中原地注释，并在其之后测量 [iprod@{u u0 u1 u2 u3}] 绑定 [C : Category@{u1 u2 u2}]，而没有字面 [Set]。探针 N8 因此被翻转，现在在 Test/ProbeFromProducts416.v 中成为一个阳性对照。仍然成立的，并且是选择的存续原因，是 [iprod] 通过 [Limit] 被陈述，它将离散形状的同构和证明宇宙与环境的宇宙进行对应，而基本的 [IsIndexedProduct] 并未进行这种对应；通过基本形式引导该定理可以保持它不受此限制。宇宙，绑定器和区块均关闭（所有91个常数）。[limit_of_products_equalizer@{u u0 u1 u2 u3 u4 u5}] 位于 [C : Category@{u1 u2 u2}] 和 [J : Category@{u3 u4 u4}] 之上——在绑定器中通过证明已识别同态，这里的每个常数——以及区块方程 [u = u3]（类的索引宇宙就是 J 的对象宇宙：对象积由 [obj J] 索引）和 [u2 = u4]（形状同态=环境同态，极限词汇：[Limit] / [IsLimitCone] 在一个其同态严格低于环境的形状上被拒绝，而 [Cone] 被接受，探针 N7），C 的对象宇宙自由。[Complete_from_products_equalizers@{u u0 u1}] 在 [C : Category@{u u0 u0}] 上，没有承载区块方程——只有界限——并结束 [Complete@{u0 u0 u0 u}]，图表范畴的对象和同态在 C 的同态层级：与 [Sets_Complete] 相同的小型化规则。[Cocomplete_from_coproducts_coequalizers] 承载了 [u0 < u] 的严格 [HasIndexedCoproducts] 自我声明且无方程。[continuous_from_products_equalizers] 在一个同质层级 ([Category@{u5 u8 u8}], [Category@{u4 u8 u8}]) 上绑定 C 和 D，仅有界限，[PreservesIndexedProducts] 和 [PreservesEqualizers] 也是如此。[pe_cone] 和 [pe_limiting] 结合 [J : Category@{u u0 u0}]、[C : Category@{u1 u0 u0}] — 该形态的同层次由绑定器中的环境识别，这就是为什么探针 N7 的 [pe_cone] 拒绝在环境参数上触发与 [Limit] 相同的信息，并且不能证实是哪一个捐赠者强制执行——仅有界限，并且家族索引 [I : Type@{u3}] 没有任何身份识别（上限由两个辅助层次 [Generates] 和 [IsIndexedProduct]）、[Gen] 的块是字面上的空的；[Generates] 和 [ArrowIx] 仅承载界限；[pe_gen_restrict_iso] 添加 [u = u5]（家族索引宇宙，每个实例提供一个索引宇宙的类）。同态 = 证明识别有六个捐赠者，每个在 [ch < cp] 处单独被拒绝，使用同态集、恒等式和一个接受的自函子（探针 N6）：[HasIndexedProducts], [HasEqualizers], [IsIndexedProduct], [IsEqualizer], [Limit], [Complete]；这里没有引入，也没有声称不可避免。在任何绑定器或块中，零个单词有限的 [Set]；在整个 [About] 转储中唯一的两个 [Set] 代币是两个自动生成 [_rec] 消除器的动机类型。计数。91/91 常量在全局上下文中闭合，零 [Axioms:] 行 — 86 [Print Module] 条目（70 [Definition]，14 [Parameter]，2 [Inductive]）加上它在 [:=] 之后列出的五个构造函数；所有91个都在 [make print-assumptions] 门中完全限定。闭合38个模块（不包括自身）：去掉 Structure/Pullback/Reduction 成本 9，Structure/Limit/Coproduct 和 Structure/Complete 各 1，其余 [Require] 都是 0。三 个 [Defined] 令牌对抗 14 个 [Qed]，没有负载承重 — 每个单独翻转到 [Qed] 都会使该文件和探测编译 — 由数据约定保留 [Defined]。五 个 [:= eq_refl] 读回。零声明碰撞
 在 91 个名称加探针的名称上，在七次重命名之后
 着陆前：[arrow_dom] / [arrow_cod] 是 Instance/Square.v 的，
 [arrow_of] 是 Theory/Shapes.v 的，[sub_dom] 是 Theory/Subobject.v 的字段，
 [two_fam] 是 Structure/Pullback/Wide.v 的。[make todo] 增加了 19 个，全部在探针里（16 个反驳命令 + 3 行散文），
 此文件贡献为零——所以问题的“未增加新命中”框未按原文满足，并在此披露。Test/ProbeFromProducts416.v 包含 16 条反驳命令 = 1 个仪器 + 15 条命令固定三类中的八个否定，通过错误文本加以区分 — 3 个转换（N1–N3）、2 个类型（N4–N5；N5 的消息在两个相同类型的 FAMILIES 上带有尾随 [cannot unify] — [hom[C] ] 对比 [hom[C^op] ]，后者打印展开为 [λ x y, y ~> x] — 不在一类型的两个成员上）、3 个宇宙（N6–N8，十条命令）— 每条命令在整个文件的副本中一次剥离，并单独编译以读取其错误；守护覆盖率通过机械方式测量（在反驳命令中有 40 个标识符，在外部还有 35 个，五个例外详尽说明关键字，三个用于反驳 [Example] 的名称及仪器缺失的名称）；对目标常量的否定名称进行 7/7 的重命名模拟，每次中断在一条 [Check] 生产线上。探针还携带 [Sets] 实例化——[@Complete Sets] 的第二个元素，未与 [Sets_Complete] 对比并且未包含它：来自 Instance/Sets/Products.v 的产品，来自 Instance/Sets/Pullback.v 的等化器通过 [HasEqualizers_of_HasPullbacks_Terminal] 的拉回，以及 Instance/Sets/Complete.v，在探针闭包中未测量（一次审计发现一个草稿，它提供了 Adjunction/GAFT/Sets.v 的 [Sets_HasEqualizers]，即 [Complete_HasEqualizers Sets_Complete]）——以及行箭生成族：[_2] 有三个箭头，其非恒等箭头上的单索引族可以生成。同一提交中在散文中重指向：Structure/Complete.v（编辑对行没有影响，该段的一部分在其他地方被引用），其结尾句子曾称 [iprod] 为“约减的产品一半”；Structure/Equalizer.v，其“在此库中两个参数都运行”在该文件之前对于约减是错误的；以及 Structure/Limit.v 的两段（E.1 库缺陷：“唯一性到唯一同构”是 Structure/Limit/Unique.v 的，自问题提交以来已到位，该构造在此文件中），两段对行没有影响。Structure/Topos.v，该问题也提到，引用了 PULLBACK 约减（Structure/Pullback/Reduction.v）而非本约减，因此未被更改；问题中引用的漂移在此记录。未送达。没有协变余等化子-余积构造（对偶在 C^op 中是基本的）；没有有限形状的变体（Awodey 的命题 5.23 关于有限图，其有限性谓词是 #417 的，并且推论 5.24 的基数记账被宇宙多态性所取代）；在此文件中没有 [Set] 实例化，也没有计算证人（探针的 [Sets] 极限是在 Instance/Sets/Pullback.v 的一致子集合上作为拉回构建的等化子，该子集合位于 Instance/Sets/Products.v 的依赖函数乘积上，其元素没有写出）；没有将 [Sets] 实例化与 [Sets_Complete] 进行比较；没有显示形状满足原子分解假设，也没有身份决策程序；没有逆向（没有说明一个完全范畴有积，这是 Adjunc 的内容）。tion/GAFT.v 的 [Complete_HasEqualizers] 用于均衡器部分，而在产品部分不存在；在 F 中没有任何识别的自然性；没有注册为 [Instance] —— 选定的限制不得成为全局可解析的。
*)

(* * ** Joint monicity of the projections of an indexed product / * ** 乘积索引投影的联合单调性 *)

(*
 Two maps into an indexed product that agree under every projection are
 equal — the uniqueness clause of [iprod_desc] read as an extensionality
 principle.  Structure/Bicartesian/Matrix.v's [iprod_ext] states the
 same fact but drags a coproduct hypothesis in from its section, and
 Instance/Fun/Terminal.v's [iprod_jointly_monic] sits far outside this
 closure; the four-line restatement is disclosed. 

 --------
 两个映射到一个索引积中，如果在每个投影下都相同，则它们相等——[iprod_desc] 的唯一性条款可以被理解为一个外延性原理。Structure/Bicartesian/Matrix.v 的 [iprod_ext] 陈述了同样的事实，但带入了它所在章节的一个余积假设，而 Instance/Fun/Terminal.v 的 [iprod_jointly_monic] 则远远超出了这一闭包；四行的重述被揭示出来。
*)

Lemma pe_iprod_ext {C : Category} {A : Type} {f : A → C} {p : C}
  {proj : ∀ a : A, p ~> f a} (H : IsIndexedProduct f p proj)
  {c : C} (u v : c ~> p) :
  (∀ a : A, proj a ∘ u ≈ proj a ∘ v) → u ≈ v.
Proof.
  intro Huv.
  pose (d := iprod_desc H (fun a => proj a ∘ v)).
  transitivity (unique_obj d).
  - symmetry; exact (uniqueness d u Huv).
  - exact (uniqueness d v (fun a => reflexivity _)).
Qed.

(** ** The arrow index of a shape / ** 形状的箭头索引 *)

Section ArrowIndex.

Context {J : Category}.

(*
 The arrows of [J] as one type: a pair of objects and an arrow between
 them.  This is the index of Mac Lane's second product, ∏_{f ∈ mor J}. 

 --------
 [J] 的箭头作为一种类型：一对对象以及它们之间的一个箭头。这是 Mac Lane 第二个积的指标，∏_{f ∈ mor J}。
*)

Definition ArrowIx : Type := { p : obj[J] * obj[J] & fst p ~{J}~> snd p }.

Definition aix_dom (a : ArrowIx) : J := fst (`1 a).
Definition aix_cod (a : ArrowIx) : J := snd (`1 a).
Definition aix_arr (a : ArrowIx) : aix_dom a ~{J}~> aix_cod a := `2 a.

Definition mk_arrow {x y : J} (f : x ~{J}~> y) : ArrowIx := ((x, y); f).

Example mk_arrow_dom {x y : J} (f : x ~> y) : aix_dom (mk_arrow f) = x :=
  eq_refl.
Example mk_arrow_cod {x y : J} (f : x ~> y) : aix_cod (mk_arrow f) = y :=
  eq_refl.
Example mk_arrow_of {x y : J} (f : x ~> y) : aix_arr (mk_arrow f) = f :=
  eq_refl.

End ArrowIndex.

(* * ** Arrows generated by an indexed family / * ** 由索引族生成的箭头 *)

Section Generated.

Context {J : Category}.
Context {I : Type} (idx_dom idx_cod : I → J)
  (idx_arr : ∀ i : I, idx_dom i ~{J}~> idx_cod i).

(*
 The arrows of [J] that the family [idx_arr] generates under identities,
 composition and [≈]: exactly the hypothesis under which the family may
 index the second product in place of ALL arrows (Riehl, Exercise
 3.2.ii). 

 --------
 在恒等映射、复合和  [≈] 下，家族  [idx_arr]  生成的 [J] 箭头：正是该假设下，家族可以在所有箭头的位置上索引第二个积（Riehl，练习 3.2.ii）。
*)

Inductive Gen : ∀ (x y : J), (x ~{J}~> y) → Type :=
  | gen_idx (i : I) : Gen (idx_dom i) (idx_cod i) (idx_arr i)
  | gen_id (x : J) : Gen x x id
  | gen_comp {x y z : J} (g : y ~{J}~> z) (f : x ~{J}~> y) :
      Gen y z g → Gen x y f → Gen x z (g ∘ f)
  | gen_equiv {x y : J} (f f' : x ~{J}~> y) :
      f ≈ f' → Gen x y f → Gen x y f'.

(* The family generates the whole of [J]. / 这个家族生成整个 [J]。 *)

Definition Generates : Type := ∀ (x y : J) (f : x ~{J}~> y), Gen x y f.

End Generated.

Arguments Gen {J I idx_dom idx_cod} idx_arr {x y} f.
Arguments gen_idx {J I idx_dom idx_cod idx_arr} i.
Arguments gen_id {J I idx_dom idx_cod idx_arr} x.
Arguments gen_comp {J I idx_dom idx_cod idx_arr x y z} g f _ _.
Arguments gen_equiv {J I idx_dom idx_cod idx_arr x y} f f' _ _.
Arguments Generates {J I idx_dom idx_cod} idx_arr.

(* The full arrow index generates: every arrow is itself indexed. / 完整箭头索引生成：每个箭头本身都是有索引的。 *)

Definition ArrowIx_Generates {J : Category} :
  Generates (@aix_arr J) :=
  fun x y f => gen_idx (mk_arrow f).

(* * ** The core: an equalizer of two maps between two products is limiting / * ** 核心：两个乘积之间两个映射的等化器是极限 *)

(*
 Everything here is elementary — stated against [IsIndexedProduct] and
 [IsEqualizer], with no class instance, no chosen product and no chosen
 equalizer — so that it applies verbatim to the IMAGE of the construction
 under a functor (§V.4 Exercise 2 below), and to any sub-family of arrows
 that generates (Riehl's refinement). 

 --------
 这里的一切都是基础的——针对 [IsIndexedProduct] 和 [IsEqualizer] 陈述，没有类实例，没有选定的积，也没有选定的均衡器——因此它可以逐字适用于在函子下构造的像（见 §V.4 练习 2），以及生成的任何箭头子族（Riehl 的改进）。
*)

Section Core.

#[local] Set Default Proof Using "All".

Context {J C : Category} (F : J ⟶ C).

(* The product over the objects of J. / J 的对象的乘积。 *)
Context {P : C} (projP : ∀ x : J, P ~> F x)
  (HP : IsIndexedProduct (fun x : J => F x) P projP).

(*
 The product over a generating family of arrows of J, at their
 codomains. 

 --------
 在 J 的生成箭头族上的乘积，在它们的余域上。
*)
Context {I : Type} {idx_dom idx_cod : I → J}
  {idx_arr : ∀ i : I, idx_dom i ~{J}~> idx_cod i}
  (Hgen : Generates idx_arr).
Context {Q : C} (projQ : ∀ i : I, Q ~> F (idx_cod i))
  (HQ : IsIndexedProduct (fun i : I => F (idx_cod i)) Q projQ).

(* The two canonical maps, given by their components: projection at the codomain, and the diagram's action after projection at the domain. / 这两个规范映射，由它们的分量给出：在陪域上的投影，以及在定义域上投影后的图的作用。 *)
Context (s t : P ~> Q)
  (Hs : ∀ i : I, projQ i ∘ s ≈ projP (idx_cod i))
  (Ht : ∀ i : I, projQ i ∘ t ≈ fmap[F] (idx_arr i) ∘ projP (idx_dom i)).

(* Their equalizer. / 他们的扳平者。 *)
Context {E : C} (e : E ~> P) (HE : IsEqualizer s t E e).

(*
 The candidate cone: apex the equalizer, legs the object projections
 composed with the equalizing map. 

 --------
 候选圆锥：顶点为均衡器，腿为对象投影，通过均衡映射组成。
*)

Definition pe_leg (x : J) : E ~> F x := projP x ∘ e.

Lemma pe_leg_coherence_gen {x y : J} (f : x ~{J}~> y)
  (G : Gen idx_arr f) : fmap[F] f ∘ pe_leg x ≈ pe_leg y.
Proof.
  induction G as [i | x | x y z g f Hg IHg Hf IHf | x y f f' Hff' Hf IH].
  - unfold pe_leg.
    rewrite comp_assoc, <- (Ht i), <- comp_assoc, <- (fork_eq HE),
      comp_assoc, (Hs i).
    reflexivity.
  - rewrite fmap_id, id_left; reflexivity.
  - rewrite fmap_comp, <- comp_assoc, IHf, IHg; reflexivity.
  - rewrite <- Hff'; exact IH.
Qed.

Lemma pe_leg_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[F] f ∘ pe_leg x ≈ pe_leg y.
Proof. exact (pe_leg_coherence_gen f (Hgen x y f)). Qed.

Definition pe_cone : Cone F :=
  @Build_Cone J C F E
    (@Build_ACone J C E F pe_leg (fun x y f => pe_leg_coherence f)).

(* A competing cone tuples into the object product ... / 一个竞争的锥体元组进入对象产品... *)

Definition pe_tuple (M : Cone F) : vertex_obj[M] ~> P :=
  unique_obj (iprod_desc HP (fun x => cone_leg M x)).

Lemma pe_tuple_proj (M : Cone F) (x : J) :
  projP x ∘ pe_tuple M ≈ cone_leg M x.
Proof. exact (unique_property (iprod_desc HP (fun x => cone_leg M x)) x). Qed.

(* ... and its tuple equalizes the two canonical maps, by cone coherence at each indexed arrow. / ... 它的元组通过在每个索引箭头处的锥一致性，使两个典范映射相等。 *)

Lemma pe_tuple_equalizes (M : Cone F) : s ∘ pe_tuple M ≈ t ∘ pe_tuple M.
Proof.
  apply (pe_iprod_ext HQ); intro i.
  rewrite comp_assoc, (Hs i), pe_tuple_proj.
  rewrite comp_assoc, (Ht i), <- comp_assoc, pe_tuple_proj.
  symmetry; apply cone_leg_coh.
Qed.

(* The mediator is the descent of the tuple through the equalizer. / 中介者是元组通过均衡器的下降。 *)

Definition pe_med (M : Cone F) : vertex_obj[M] ~> E :=
  unique_obj (eq_desc HE (pe_tuple M) (pe_tuple_equalizes M)).

Lemma pe_med_incl (M : Cone F) : e ∘ pe_med M ≈ pe_tuple M.
Proof.
  exact (unique_property (eq_desc HE (pe_tuple M) (pe_tuple_equalizes M))).
Qed.

Lemma pe_med_leg (M : Cone F) (x : J) : pe_leg x ∘ pe_med M ≈ cone_leg M x.
Proof.
  unfold pe_leg.
  rewrite <- comp_assoc, pe_med_incl.
  apply pe_tuple_proj.
Qed.

Lemma pe_med_unique (M : Cone F) (v : vertex_obj[M] ~> E)
  (Hv : ∀ x : J, pe_leg x ∘ v ≈ cone_leg M x) : pe_med M ≈ v.
Proof.
  apply (uniqueness (eq_desc HE (pe_tuple M) (pe_tuple_equalizes M))).
  symmetry.
  apply (uniqueness (iprod_desc HP (fun x => cone_leg M x))).
  intro x.
  rewrite comp_assoc.
  exact (Hv x).
Qed.

(* Mac Lane §V.2 Theorem 1: the cone is limiting. / Mac Lane §V.2 定理 1：该锥是极限的。 *)

Theorem pe_limiting : IsLimitCone pe_cone.
Proof.
  intro M.
  unshelve refine {| unique_obj := pe_med M |}.
  - exact (pe_med_leg M).
  - intros v Hv; exact (pe_med_unique M v Hv).
Defined.

End Core.

(* * ** The construction from chosen products and equalizers (Theorem 2) / * ** 从选定产品和均衡器的构造（定理2） *)

Section FromClasses.

Context {C : Category} (HP : HasIndexedProducts C).
Context {J : Category} (F : J ⟶ C).

Definition pe_obj_product : C := indexed_product (fun x : J => F x).

Definition pe_obj_proj (x : J) : pe_obj_product ~> F x :=
  indexed_product_proj (fun x : J => F x) x.

Definition pe_obj_product_ump :
  IsIndexedProduct (fun x : J => F x) pe_obj_product pe_obj_proj :=
  indexed_product_ump (fun x : J => F x).

Definition pe_arrow_product : C :=
  indexed_product (fun a : @ArrowIx J => F (aix_cod a)).

Definition pe_arrow_proj (a : ArrowIx) : pe_arrow_product ~> F (aix_cod a) :=
  indexed_product_proj (fun a : @ArrowIx J => F (aix_cod a)) a.

Definition pe_arrow_product_ump :
  IsIndexedProduct (fun a : @ArrowIx J => F (aix_cod a))
    pe_arrow_product pe_arrow_proj :=
  indexed_product_ump (fun a : @ArrowIx J => F (aix_cod a)).

(* Mac Lane's two maps, Riehl's Remark 3.2.13: defined by their components against the projections of the arrow product. / Mac Lane 的两个映射，Riehl 的注释 3.2.13：由它们的分量针对箭头积的投影定义。 *)

Definition pe_s : pe_obj_product ~> pe_arrow_product :=
  unique_obj (iprod_desc pe_arrow_product_ump
    (fun a : ArrowIx => pe_obj_proj (aix_cod a))).

Definition pe_t : pe_obj_product ~> pe_arrow_product :=
  unique_obj (iprod_desc pe_arrow_product_ump
    (fun a : ArrowIx => fmap[F] (aix_arr a) ∘ pe_obj_proj (aix_dom a))).

Lemma pe_s_proj (a : ArrowIx) :
  pe_arrow_proj a ∘ pe_s ≈ pe_obj_proj (aix_cod a).
Proof.
  exact (unique_property (iprod_desc pe_arrow_product_ump
    (fun a : ArrowIx => pe_obj_proj (aix_cod a))) a).
Qed.

Lemma pe_t_proj (a : ArrowIx) :
  pe_arrow_proj a ∘ pe_t ≈ fmap[F] (aix_arr a) ∘ pe_obj_proj (aix_dom a).
Proof.
  exact (unique_property (iprod_desc pe_arrow_product_ump
    (fun a : ArrowIx => fmap[F] (aix_arr a) ∘ pe_obj_proj (aix_dom a))) a).
Qed.

Context (HE : HasEqualizers C).

Definition pe_equalizer := @equalizer C HE _ _ pe_s pe_t.

Definition pe_apex : C := `1 pe_equalizer.
Definition pe_incl : pe_apex ~> pe_obj_product := `1 (`2 pe_equalizer).
Definition pe_incl_IsEqualizer : IsEqualizer pe_s pe_t pe_apex pe_incl :=
  `2 (`2 pe_equalizer).

Definition pe_limit_cone : Cone F :=
  pe_cone F pe_obj_proj pe_obj_product_ump ArrowIx_Generates
    pe_arrow_proj pe_arrow_product_ump pe_s pe_t pe_s_proj pe_t_proj
    pe_incl pe_incl_IsEqualizer.

Definition pe_limit_limiting : IsLimitCone pe_limit_cone :=
  pe_limiting F pe_obj_proj pe_obj_product_ump ArrowIx_Generates
    pe_arrow_proj pe_arrow_product_ump pe_s pe_t pe_s_proj pe_t_proj
    pe_incl pe_incl_IsEqualizer.

(* The pinned name. / 固定的名字。 *)

Definition limit_of_products_equalizer : Limit F :=
  limitcone_limit pe_limit_cone pe_limit_limiting.

(* Theorem 2's explicit description, read back on the nose. / 定理2的明确描述，原原本本地读回去。 *)

Example limit_of_products_equalizer_apex :
  vertex_obj[@limit_cone _ _ _ limit_of_products_equalizer] = pe_apex :=
  eq_refl.

Example limit_of_products_equalizer_leg (x : J) :
  cone_leg (@limit_cone _ _ _ limit_of_products_equalizer) x
    = pe_obj_proj x ∘ pe_incl :=
  eq_refl.

End FromClasses.

(* * ** Corollary 2: completeness, and its dual / * ** 推论 2：完备性及其对偶 *)

Definition Complete_from_products_equalizers {C : Category}
  (HP : HasIndexedProducts C) (HE : HasEqualizers C) : @Complete C :=
  fun J F => limit_of_products_equalizer HP F HE.

Definition Cocomplete_from_coproducts_coequalizers {C : Category}
  (HP : HasIndexedCoproducts C) (HE : HasCoequalizers C) : @Cocomplete C :=
  fun J F =>
    @Complete_from_products_equalizers (C^op) HP
      (HasEqualizers_op_of_HasCoequalizers HE) (J^op) (Opposite_Functor F).

(*
   * ** §V.4 Exercise 2: a functor preserving products and equalizers is
   continuous 

   --------
   * ** §V.4 练习 2：保持积和等化子的函子是连续的
*)

(*
 Cone-level preservation of indexed products and of equalizers: the
 image of a product with its projections is a product, the image of an
 equalizer is an equalizer.  Neither predicate existed in the tree. 

 --------
 已索引乘积和等化器的圆锥级保持：乘积及其投影的像是乘积，等化器的像是等化器。树中不存在任何谓词。
*)

Definition PreservesIndexedProducts {C D : Category} (G : C ⟶ D) : Type :=
  ∀ (A : Type) (f : A → C) (p : C) (proj : ∀ a : A, p ~> f a),
    IsIndexedProduct f p proj →
    IsIndexedProduct (fun a => G (f a)) (G p) (fun a => fmap[G] (proj a)).

Definition PreservesEqualizers {C D : Category} (G : C ⟶ D) : Type :=
  ∀ (x y : C) (f g : x ~> y) (q : C) (e : q ~> x),
    IsEqualizer f g q e →
    IsEqualizer (fmap[G] f) (fmap[G] g) (G q) (fmap[G] e).

Section Continuity.

Context {C D : Category} (HP : HasIndexedProducts C) (HE : HasEqualizers C).
Context (G : C ⟶ D) (GP : PreservesIndexedProducts G)
  (GE : PreservesEqualizers G).
Context {J : Category} (K : J ⟶ C).

(* The image of the construction is the construction in D, with the image maps satisfying the two component equations. / 构造的像是 D 中的构造，像映射满足两个分量方程。 *)

Lemma pe_image_s (a : ArrowIx) :
  fmap[G] (pe_arrow_proj HP K a) ∘ fmap[G] (pe_s HP K)
    ≈ fmap[G] (pe_obj_proj HP K (aix_cod a)).
Proof. rewrite <- fmap_comp, pe_s_proj; reflexivity. Qed.

Lemma pe_image_t (a : ArrowIx) :
  fmap[G] (pe_arrow_proj HP K a) ∘ fmap[G] (pe_t HP K)
    ≈ fmap[G ◯ K] (aix_arr a) ∘ fmap[G] (pe_obj_proj HP K (aix_dom a)).
Proof. rewrite <- fmap_comp, pe_t_proj, fmap_comp; reflexivity. Qed.

Definition pe_image_cone : Cone (G ◯ K) :=
  pe_cone (G ◯ K) (fun x => fmap[G] (pe_obj_proj HP K x))
    (GP _ _ _ _ (pe_obj_product_ump HP K)) ArrowIx_Generates
    (fun a => fmap[G] (pe_arrow_proj HP K a))
    (GP _ _ _ _ (pe_arrow_product_ump HP K))
    (fmap[G] (pe_s HP K)) (fmap[G] (pe_t HP K)) pe_image_s pe_image_t
    (fmap[G] (pe_incl HP K HE))
    (GE _ _ _ _ _ _ (pe_incl_IsEqualizer HP K HE)).

Definition pe_image_limiting : IsLimitCone pe_image_cone :=
  pe_limiting (G ◯ K) (fun x => fmap[G] (pe_obj_proj HP K x))
    (GP _ _ _ _ (pe_obj_product_ump HP K)) ArrowIx_Generates
    (fun a => fmap[G] (pe_arrow_proj HP K a))
    (GP _ _ _ _ (pe_arrow_product_ump HP K))
    (fmap[G] (pe_s HP K)) (fmap[G] (pe_t HP K)) pe_image_s pe_image_t
    (fmap[G] (pe_incl HP K HE))
    (GE _ _ _ _ _ _ (pe_incl_IsEqualizer HP K HE)).

(*
 The image cone and the image OF the constructed cone differ only by
 [fmap_comp] on the legs: same apex, identity comparison. 

 --------
 成像锥和所构造锥的图像仅在锥体的侧面上有所不同：相同的顶点，相同的比较。
*)

Definition pe_image_ConeIso :
  ConeIso pe_image_cone (FCone G (pe_limit_cone HP K HE)).
Proof.
  exists iso_id.
  intro x; simpl.
  rewrite id_right.
  change (fmap[G] (pe_obj_proj HP K x ∘ pe_incl HP K HE)
            ≈ fmap[G] (pe_obj_proj HP K x) ∘ fmap[G] (pe_incl HP K HE)).
  apply fmap_comp.
Defined.

Definition pe_image_limit_cone_limiting :
  IsLimitCone (FCone G (pe_limit_cone HP K HE)) :=
  limitcone_transport pe_image_ConeIso pe_image_limiting.

(* Any limiting cone is isomorphic to the constructed one; transport. / 任何极限锥都与构造的那个同构；传递。 *)

Definition pe_preserves : PreservesLimitCone K G :=
  fun N HN =>
    limitcone_transport
      (FCone_iso G (limitcone_iso (pe_limit_limiting HP K HE) HN))
      pe_image_limit_cone_limiting.

End Continuity.

Definition continuous_from_products_equalizers {C D : Category}
  (HP : HasIndexedProducts C) (HE : HasEqualizers C)
  (G : C ⟶ D) (GP : PreservesIndexedProducts G) (GE : PreservesEqualizers G) :
  ContinuousFunctor G :=
  fun J K => pe_preserves HP HE G GP GE K.

(* * ** Riehl's refinement: any generating family of arrows will do / * ** Riehl的改进：任何生成箭头的族都可以 *)

Section Refinement.

Context {C : Category} (HP : HasIndexedProducts C) (HE : HasEqualizers C).
Context {J : Category} (F : J ⟶ C).
Context {I : Type} {idx_dom idx_cod : I → J}
  {idx_arr : ∀ i : I, idx_dom i ~{J}~> idx_cod i}
  (Hgen : Generates idx_arr).

Definition pe_gen_product : C := indexed_product (fun i : I => F (idx_cod i)).

Definition pe_gen_proj (i : I) : pe_gen_product ~> F (idx_cod i) :=
  indexed_product_proj (fun i : I => F (idx_cod i)) i.

Definition pe_gen_product_ump :
  IsIndexedProduct (fun i : I => F (idx_cod i)) pe_gen_product pe_gen_proj :=
  indexed_product_ump (fun i : I => F (idx_cod i)).

Definition pe_gen_s : pe_obj_product HP F ~> pe_gen_product :=
  unique_obj (iprod_desc pe_gen_product_ump
    (fun i : I => pe_obj_proj HP F (idx_cod i))).

Definition pe_gen_t : pe_obj_product HP F ~> pe_gen_product :=
  unique_obj (iprod_desc pe_gen_product_ump
    (fun i : I => fmap[F] (idx_arr i) ∘ pe_obj_proj HP F (idx_dom i))).

Lemma pe_gen_s_proj (i : I) :
  pe_gen_proj i ∘ pe_gen_s ≈ pe_obj_proj HP F (idx_cod i).
Proof.
  exact (unique_property (iprod_desc pe_gen_product_ump
    (fun i : I => pe_obj_proj HP F (idx_cod i))) i).
Qed.

Lemma pe_gen_t_proj (i : I) :
  pe_gen_proj i ∘ pe_gen_t
    ≈ fmap[F] (idx_arr i) ∘ pe_obj_proj HP F (idx_dom i).
Proof.
  exact (unique_property (iprod_desc pe_gen_product_ump
    (fun i : I => fmap[F] (idx_arr i) ∘ pe_obj_proj HP F (idx_dom i))) i).
Qed.

Definition pe_gen_equalizer := @equalizer C HE _ _ pe_gen_s pe_gen_t.

Definition pe_gen_apex : C := `1 pe_gen_equalizer.
Definition pe_gen_incl : pe_gen_apex ~> pe_obj_product HP F :=
  `1 (`2 pe_gen_equalizer).

Definition pe_gen_cone : Cone F :=
  pe_cone F (pe_obj_proj HP F) (pe_obj_product_ump HP F) Hgen
    pe_gen_proj pe_gen_product_ump pe_gen_s pe_gen_t
    pe_gen_s_proj pe_gen_t_proj pe_gen_incl (`2 (`2 pe_gen_equalizer)).

(* The equalizer over the generating family is limiting too ... / 生成族上的均衡器也正在限制... *)

Definition pe_gen_limiting : IsLimitCone pe_gen_cone :=
  pe_limiting F (pe_obj_proj HP F) (pe_obj_product_ump HP F) Hgen
    pe_gen_proj pe_gen_product_ump pe_gen_s pe_gen_t
    pe_gen_s_proj pe_gen_t_proj pe_gen_incl (`2 (`2 pe_gen_equalizer)).

(* ... hence canonically isomorphic, as a cone, to the full construction: restricting the index does not change the limit. / ... 因此从概范意义上作为一个锥体同构于完整的构造：限制指标不会改变极限。 *)

Definition pe_gen_restrict_iso : ConeIso pe_gen_cone (pe_limit_cone HP F HE) :=
  limitcone_iso pe_gen_limiting (pe_limit_limiting HP F HE).

End Refinement.

(* * ** The non-identity and the atomic families / * ** 非同一性与原子族 *)

Section Families.

Context {J : Category}.

(* An arrow that is an identity up to [≈]. / 一个箭头，其在 [≈] 上是恒等的。 *)

Inductive IsIdArrow : ∀ (x y : J), (x ~{J}~> y) → Type :=
  | is_id_arrow (x : J) (f : x ~{J}~> x) : f ≈ id → IsIdArrow x x f.

(* A family of arrows given by a predicate on the arrow index. / 由箭头索引的谓词给出的一族箭头。 *)

Definition fam_dom (S : @ArrowIx J → Type) (a : { a : ArrowIx & S a }) : J :=
  aix_dom (`1 a).
Definition fam_cod (S : @ArrowIx J → Type) (a : { a : ArrowIx & S a }) : J :=
  aix_cod (`1 a).
Definition fam_arr (S : @ArrowIx J → Type) (a : { a : ArrowIx & S a }) :
  fam_dom S a ~{J}~> fam_cod S a := aix_arr (`1 a).

(*
 A predicate that contains every arrow that is not an identity generates:
 the decider is the hypothesis, and it is exactly what “non-identity”
 costs constructively. 

 --------
 一个谓词包含每个非同一箭头会生成：判定器是假设，它正是“非同一”在构造上所花费的。
*)

Definition sub_Generates_of_dec (S : @ArrowIx J → Type)
  (dec : ∀ (x y : J) (f : x ~{J}~> y), S (mk_arrow f) + IsIdArrow x y f) :
  Generates (fam_arr S).
Proof.
  intros x y f.
  destruct (dec x y f) as [HS | Hid].
  - exact (gen_idx (idx_arr := fam_arr S) (mk_arrow f; HS)).
  - destruct Hid as [x f Hf].
    exact (gen_equiv id f (symmetry Hf) (gen_id x)).
Defined.

(*
 The non-identity arrows (Riehl, Exercise 3.2.ii, first clause).  The
 family generates as soon as being an identity is DECIDABLE, and the
 decider is the whole cost: nothing here decides it for any shape. 

 --------
 非同一箭头（Riehl，练习3.2.ii，第一条款）。只要是否是同一箭头是可判定的，该族就会生成，而判定器就是全部的代价：这里没有任何东西为任何形状判定它。
*)

Definition NonIdArrow (a : @ArrowIx J) : Type :=
  IsIdArrow (aix_dom a) (aix_cod a) (aix_arr a) → False.

Definition nonid_Generates
  (dec : ∀ (x y : J) (f : x ~{J}~> y),
     IsIdArrow x y f + (IsIdArrow x y f → False)) :
  Generates (fam_arr NonIdArrow) :=
  sub_Generates_of_dec NonIdArrow
    (fun x y f => match dec x y f with
                  | inl Hid => inr Hid
                  | inr Hn => inl Hn
                  end).

(*
 The atomic arrows (second clause): non-identities with no factorization
 through two non-identities.  Whether they generate is Riehl's
 factorization hypothesis, and it is taken as a HYPOTHESIS here — a
 [Generates (fam_arr AtomicArrow)] — with no shape shown to satisfy it. 

 --------
 原子箭头（第二条款）：没有通过两个非同一性的分解的非同一性。它们是否生成是Riehl的分解假设，在这里被作为一个假设——一个[Generates (fam_arr AtomicArrow)]——没有显示有形状满足它。
*)

Definition AtomicArrow (a : @ArrowIx J) : Type :=
  NonIdArrow a *
  (∀ (z : J) (g : z ~{J}~> aix_cod a) (h : aix_dom a ~{J}~> z),
     aix_arr a ≈ g ∘ h →
     IsIdArrow z (aix_cod a) g + IsIdArrow (aix_dom a) z h).

End Families.

(* * ** The refined presentations, read off the general one / * ** 精炼的演示，从一般的演示中读出 *)

Section Refined.

Context {C : Category} (HP : HasIndexedProducts C) (HE : HasEqualizers C).
Context {J : Category} (F : J ⟶ C).

(* Over the non-identity arrows, given a decider. / 在非恒等箭头上，给定一个决策器。 *)

Definition pe_nonid_limiting
  (dec : ∀ (x y : J) (f : x ~{J}~> y),
     IsIdArrow x y f + (IsIdArrow x y f → False)) :
  IsLimitCone (pe_gen_cone HP HE F (nonid_Generates dec)) :=
  pe_gen_limiting HP HE F (nonid_Generates dec).

(* Over the atomic arrows, given that they generate. / 关于原子箭，鉴于它们会产生。 *)

Definition pe_atomic_limiting (Hatom : Generates (fam_arr AtomicArrow)) :
  IsLimitCone (pe_gen_cone HP HE F Hatom) :=
  pe_gen_limiting HP HE F Hatom.

End Refined.
