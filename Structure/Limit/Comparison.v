Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Structure.Terminal.
Require Import Category.Functor.Structure.Cartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Span.
Require Import Category.Adjunction.Continuity.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Roof.

Generalizable All Variables.

(* * * The canonical comparison arrow for limits of composites / * * 复合极限的典型比较箭头 *)

(*
 Mac Lane §V.2 Exercise 4 and §V.4 Exercise 5 (book pp. 114, 118;
 maclane:V.2:ex4, maclane:V.4:ex5); Riehl §3.4's opening construction,
 Lemma 3.4.3 and Exercise 3.4.i, and §4.6 Exercise 4.6.iii
 (riehl:3.4:construction-canonical-comparison, riehl:3.4:lem3,
 riehl:3.4:exi, riehl:4.6:exiii).
 nLab: https://ncatlab.org/nlab/show/preserved+limit

 BACKGROUND.  For H : C ⟶ D and a cone N over F : J ⟶ C, applying H to
 the legs gives a cone over H ◯ F (Preservation.v's [FCone]); when H ◯ F
 has a limit cone M, the unique factorisation of that image cone through
 M is the canonical comparison κ : H (vertex N) ~> vertex M, determined
 by the leg equations cone_leg M x ∘ κ ≈ fmap[H] (cone_leg N x) together
 with uniqueness (Riehl §3.4; Awodey §5.5).  H preserves the limit N
 exactly when κ is an isomorphism (Riehl Lemma 3.4.3; Mac Lane V.4
 Exercise 5).  Mac Lane V.2 Exercise 4 adds a change of index category:
 for W : J' ⟶ J the image cone, restricted along W, factors through a
 limit of (H ◯ F) ◯ W.  The shape-specific classes [CartesianFunctor]
 (Functor/Structure/Cartesian.v) and [TerminalFunctor]
 (Functor/Structure/Terminal.v) postulate the invertible comparison as
 a FIELD ([fobj_prod_iso], [fobj_one_iso]); the last two sections prove
 each class equivalent to invertibility of the general comparison at the
 two-element discrete and the empty shape, so the functor-structure
 hierarchy and the limit-preservation hierarchy meet.

 STALE PREMISES, RE-MEASURED (the issue's "Current state" predates #427,
 986c7b35):
 - "the comparison is never named; there is no biconditional": since
 #427, Structure/Limit/Preservation.v carries [cone_comparison],
 its leg equations and uniqueness, the biconditional in both
 directions ([LimitCone_comparison_iso], [comparison_iso_LimitCone],
 [PreservesLimitCone_of_comparison],
 [comparison_iso_of_PreservesLimitCone]), [limit_comparison] —
 the issue's pinned name lives THERE, not here — and
 [cocone_comparison], the colimit MORPHISM without its biconditional.
 - "[fmap_cone] at Theory/Equivalence/Limit.v": no longer exists; it
 merged into [FCone] (Structure/Limit/Creation.v records the
 merge).  Construction/Comma/Limit.v ([image_leg],
 [image_acone]) still exist as measured.
 - "F ∘ Δc = Δ (F c) is not stated": stated componentwise in
 Structure/Limit/Constant.v — [const_image_fobj] at [eq_refl],
 the strict arrow form refused there, and [const_image_fmap_equiv]
 at ≈.
 - "no colimit comparison morphism": [cocone_comparison] exists; the
 colimit BICONDITIONAL did not, and is delivered here.
 - True gaps, all delivered here: reindexing along W; the W-general
 comparison; the converse of Structure/Limit/Product.v's
 [limit_is_indexed_product] (Functor/Hom/Limit.v records its
 absence); the bridge from [CartesianFunctor] and [TerminalFunctor] to
 [PreservesLimitCone].

 WHAT IS DELIVERED (57 constants, every one closed under the global
 context).
 (1) REINDEXING.  [cone_reindex W N : Cone (F ◯ W)] — same apex, legs
 at [W j'], coherence read off N at [fmap[W] f]; apex and legs read
 back at [eq_refl].  Functoriality along [Id] and along a composite
 at [eq_refl], apex- and leg-wise ([cone_reindex_id_*],
 [cone_reindex_comp_*]); NOT as an equation of cones, because
 [Cone ((F ◯ W) ◯ V)] and [Cone (F ◯ (W ◯ V))] are distinct record
 types (probe N1; Preservation.v [cone_assoc] repackages).  The
 diagram half of reindexing is Theory/Kan/Extension.v's
 [Induced := (− ◯ W)]; nothing new is needed for it.  No
 interaction with [IsLimitCone] is claimed: a limit cone restricted
 along W need not be limiting.
 (2) THE W-GENERAL COMPARISON (Mac Lane V.2 Exercise 4).
 [reindex_comparison W H N HM : H (vertex N) ~> vertex M] for
 [M : Cone ((H ◯ F) ◯ W)] limiting, as [cone_comparison H
 (cone_reindex W N) (islimitcone_assoc HM)]; its leg equations
 ([reindex_comparison_commutes]), uniqueness
 ([reindex_comparison_unique]), and invertibility ⇔ limit-ness of
 [FCone H (cone_reindex W N)] ([reindex_comparison_iso],
 [reindex_comparison_iso_LimitCone]).  At [W = Id] the cone
 [cone_reindex Id N] has type [Cone (F ◯ Id)], not [Cone F], so no
 [eq_refl] identification with [cone_comparison] is claimed; the
 legs agree at [eq_refl] ([cone_reindex_id_leg]).
 (3) THE BICONDITIONAL, BUNDLED.  [preserves_iff_comparison_iso F HM :
 PreservesLimitCone K F ↔ ∀ N, IsLimitCone N → IsIsomorphism
 (cone_comparison F N HM)] (the Type-valued ↔), from Preservation.v's
 two directions.  [PreservesLimitCone_of_cone]: preserving ONE
 limit cone is preserving them all ([limitcone_iso], [FCone_iso],
 [limitcone_transport]); [PreservesLimitCone_of_comparison_iso].
 (4) THE COLIMIT BICONDITIONAL (Riehl 3.4.i).  [colimitcocone_iso],
 [cocone_comparison_commutes], [cocone_comparison_unique],
 [ColimitCocone_comparison_iso], [comparison_iso_ColimitCocone],
 [PreservesColimitCocone_of_comparison],
 [comparison_iso_of_PreservesColimitCocone],
 [preserves_colimit_iff_comparison_iso] — built in the cocone
 vocabulary line for line after Preservation.v, NOT by
 instantiating the limit block at [F^op]: [FCocone F N] is a cone
 over [(F ◯ K)^op] and [FCone F^op N] one over [F^op ◯ K^op], two
 distinct record types (probe N5 reads the clause "cannot unify");
 the op route exists after Preservation.v's [cone_op_comp]
 repackaging (probe control) but would speak of a repackaged cone,
 not of [FCocone].  CORRECTION (#477): the colimit side now also
 has (3)'s [PreservesLimitCone_of_cone], as
 [PreservesColimitCocone_of_cocone] after the CoComparison
 section, over Preservation.v's [FCocone_iso]; the counts and
 censuses of this header are of the 57, and COUNTS AND CONVENTIONS
 records the 58th.
 (5) RIEHL'S WHISKERING IDENTITY at functor level:
 [const_image_iso : F ◯ Δ[J](c) ≈ Δ[J](F c)] in [Functor_Setoid],
 every component [iso_id] ([const_image_iso_component] at
 [eq_refl]); precedent Adjunction/Diagonal/Connected.v.
 (6) RIEHL'S WARM-UP: [pullback_comparison H F N HM] at [Cospan C]
 (Structure/Span.v; [Roof] is universe-free), [eq_refl] to
 [cone_comparison] ([pullback_comparison_is]).
 (7) RAPL RESTATED: [rapl_comparison_iso A G HM N HN] — the comparison
 of a right adjoint is invertible, from Adjunction/Continuity.v's
 [right_adjoint_PreservesLimitCone] (the restatement Riehl 4.6.iii
 asks for).
 (8) DISCRETE SHAPES.  [DiscreteCat_Functor'] is Instance/Discrete.v's
 functor with its universes annotated (see UNIVERSES).  For ANY
 [G : DiscreteCat A ⟶ C] — so also for image diagrams [F ◯ G] —
 [discrete_cone c pi] packages a family of legs as a cone
 ([discrete_cone_leg] at [eq_refl]), and a cone is limiting iff its
 legs form an [IsIndexedProduct]:
 [discrete_IsLimitCone_of_IsIndexedProduct] and
 [discrete_IsIndexedProduct_of_IsLimitCone], the latter the converse
 [limit_is_indexed_product] never had.
 (9) BINARY PRODUCTS (issue item 4).  [binary_proj] and
 [IsIndexedProduct_binary f : IsIndexedProduct f (f true × f false)
 (binary_proj f)] for any [f : bool → C]; [binary_cone f] and
 [binary_image_cone f], the product cones of C and of D over the
 image diagram, both limiting;
 [binary_comparison f : F (f true × f false) ~> F (f true) × F (f false)]
 as [cone_comparison] at them, with [binary_comparison_exl],
 [binary_comparison_exr] and [binary_comparison_fork :
 binary_comparison f ≈ fmap exl △ fmap exr] — the class's
 [prod_out], computed rather than postulated.
 [cartesian_functor_iff_comparison_iso : CartesianFunctor F ↔
 ∀ x y, IsIsomorphism (binary_comparison (binary_fam x y))] and the
 headline [cartesian_functor_iff_preserves_binary_products :
 CartesianFunctor F ↔ ∀ x y, PreservesLimitCone
 (DiscreteCat_Functor' (binary_fam x y)) F].
 (10) THE TERMINAL OBJECT (issue item 4).  [nullary_proj] and
 [IsIndexedProduct_nullary f : IsIndexedProduct f 1 (nullary_proj f)]
 for any [f : False → C]; [nullary_cone f], [nullary_image_cone f];
 [terminal_comparison f : F 1 ~> 1], which is [one]
 ([terminal_comparison_one]).  Functor/Structure/Terminal.v records
 [fobj_one_iso : 1 ≅ F 1] with [to : 1 ~> F 1], so the comparison is
 its [from] (probe N4); [terminal_functor_iff_comparison_iso] and
 [terminal_functor_iff_preserves_terminal : TerminalFunctor F ↔
 PreservesLimitCone (DiscreteCat_Functor' nullary_fam) F].

 UNIVERSES (measured by [About] under [Set Printing Universes] on all
 57 constants).
 - No word-bounded [Set] in any block.  Ambient categories elaborate as
 [C : Category@{u u0 u0}], [D : Category@{u1 u0 u0}] with ONE shared
 hom level: Preservation.v's [IsLimitCone] identifies the shape's hom
 and proof levels with the ambient's, and [Compose] types its three
 categories at one hom level.  [const_image_iso] carries the equation
 [u0 = u3] (J's hom level is C's, through [Functor_Setoid]); the
 discrete bridge carries [h = p], [h = uh], [h = up], the same
 identification with the shape's levels named.  Nineteen blocks —
 [DiscreteCat_Functor'] and the eighteen constants built over it —
 carry the stdlib caps [JMeq], [EqdepFacts] and [eq_rect_r] of this
 file's ONE [Program Definition], [DiscreteCat_Functor'] itself (an
 earlier revision of this paragraph attributed them to
 Structure/Cartesian.v, whose [Cartesian], [fork] and [exl] carry
 none, as do [binary_proj] and [IsIndexedProduct_binary] here).
 Fifty of the 57 blocks carry one strict bound, in every case a hom
 or proof level below the auxiliary universe of a [Program]-generated
 constant: [Compose@{u u0 u1 u2 u3}]'s own [u3 < u2] (Theory/Functor.v:
 259) wherever a composite functor appears, and [DiscreteCat_Functor']'s
 own [up < u] in the discrete sections; the seven elementary constants
 ([binary_fam], [binary_proj], [IsIndexedProduct_binary], their
 nullary twins and [discrete_IsLimitCone_of_IsIndexedProduct]) carry
 none.  An earlier revision read the bound [u0 < u5] as placing [bool]
 and [False] below the shape's object level; it does not — they sit at
 [Set] with no printed constraint.
 - WHY A LOCAL ANNOTATED FUNCTOR -- AND WHY IT IS NOW ONLY AN ALIAS.
 An earlier revision of this item read: "The unannotated
 [DiscreteCat_Functor] instantiates [DiscreteCat@{u Set Set}]
 (Functor/Hom/Limit.v; Test/ProbeHomLimit331.v pins
 [IsLimitCone] over its cones), so [cone_comparison] at it is refused
 above [Set] (probe N2, and N3 through Product.v's [family_cone]).
 [DiscreteCat_Functor'@{o h p uo uh up +}] has the same actions with
 the shape's levels free.  Instance/Discrete.v is NOT edited here:
 annotating the donor upstream is the lift
 Functor/Hom/Limit.v already names, but it flips
 Test/ProbeHomLimit331.v's pin and reworks that essay, and whether to
 do it is put to John in the PR rather than settled by this file."
 The question was settled: the donor WAS annotated upstream, in the
 PR "algebraic carriers are sets" (2026-09-17), at
 Instance/Discrete.v and with the same binder list.  Probes N2 and
 N3 turned over and are positive controls; Test/ProbeHomLimit331.v's
 pin flipped as predicted and that file's essay was reworked.  The
 local [DiscreteCat_Functor'] is therefore a transparent ALIAS now,
 kept for the reason given above its declaration rather than for a
 difference in signature.

 COUNTS AND CONVENTIONS.
 - 57 constants — 45 [def] and 12 [prf] in the [.glob] — all "Closed
 under the global context", zero [Axioms:] lines, all gated fully
 qualified in the Makefile's print-assumptions target.
 CORRECTION (#477): 58 since #477 added
 [PreservesColimitCocone_of_cocone], a term with no proof script,
 so 46 [def] and 12 [prf]; it is closed under the global context
 and gated fully qualified in #477's block of that target.  Its
 binders are written out, one hom level for the shape and the
 ambient as Structure/Limit/Absolute.v writes them, and its [About]
 block carries no [Set] and no equation, one strict bound
 ([Compose]'s, through [FCocone]) and the stdlib caps of
 [Projections], as [PreservesLimitCone_of_cone]'s does.  The
 [Defined] and [Qed] counts below are unchanged, and so is the
 closure: #477 adds no [Require] here.
 - Six [Defined]-terminated proofs.  Two are load-bearing by flipping
 each alone to [Qed]: [const_image_iso] (its component readback at
 [eq_refl] stops) and [discrete_cone] ([discrete_cone_leg] stops).
 Four flip freely and are kept [Defined] by the data convention —
 [comparison_iso_ColimitCocone],
 [discrete_IsLimitCone_of_IsIndexedProduct], [IsIndexedProduct_binary]
 and [IsIndexedProduct_nullary] produce [∃!]-data consumed downstream.
 Twelve [Qed].
 - Closure 37 files excluding self (transitive [Require]s through
 .Makefile.coq.d): Functor/Diagonal.v costs 6 at the margin,
 Adjunction/Continuity.v 2, Functor/Structure/Terminal.v,
 Functor/Structure/Cartesian.v, Structure/Limit/Product.v and
 Structure/Span.v 1 each, the other fourteen [Require]s 0.
 - Near-namesakes elsewhere, untouched: Instance/Fun/Terminal.v
 defines the same family as [bool_fam] (hence [binary_fam] here),
 Structure/Limit/Finite.v an [empty_cone] over [EmptyDiagram]
 (hence [nullary_cone] here), Instance/Proset/Order.v a
 [pair_cone], and Structure/Limit/Product.v's [family_cone], the
 same construction as [discrete_cone] specialised to
 [DiscreteCat_Functor f] — the closest existing constant, left as it is.
 - Test/ProbeComparison419.v mirrors the [Require] list and carries 6
 refutation commands (1 instrument + 5 negatives of three kinds: one
 conversion, two universe, two typing — N2/N3 and N5 are told from the
 rest by their universe and unification clauses, while N1 and N4 share
 the bare has-type shape and differ in the types named), each stripped
 one at a time in a copy of the whole file; readbacks at [eq_refl];
 guard coverage 35 tokens inside / 31 outside with four exhaustive
 exceptions; rename-simulated 5/5 with every first break on a positive
 line.  [make todo] grows by those 6 lines only (2196 → 2202), so the
 issue's "adds no new hits" box is not met as written; it is disclosed
 rather than met by moving the negatives out of the build.

 NOT DELIVERED.
 - Reindexing functoriality as an equation of CONES, or of the
 comparisons at the two bracketings: the record types differ; only
 apex and leg equations are stated.
 - Any [IsLimitCone] statement about [cone_reindex] alone (false in
 general), the comparison as a natural transformation in the diagram
 variable, and the Kan-extension reading of [lim (F ◯ W)] as a right
 Kan extension — none attempted.
 - The strict ([=]) arrow form of the whiskering identity: refused and
 pinned in Structure/Limit/Constant.v, not repeated here.
 - The bridges at the tree's [Two_Discrete] and [0] shapes
 (Structure/Limit/Cartesian.v [Cartesian_Limit] and
 Structure/Limit/Terminal.v [Terminal_Limit], both [Qed] and at
 [Limit] level): the bridges here are at the annotated [DiscreteCat
 bool] and [DiscreteCat False], and no passage between the shapes is
 built.
 - [PreservesProductCones] of Structure/Limit/Preservation/Shapes.v — a
 tracked file that is NOT in [_CoqProject] and is never compiled by
 [make] — is neither registered nor restated here (surfaced in the
 PR for John, not settled).
 - The operative half of Riehl's whiskering checkbox — building the
 IMAGE CONE by whiskering rather than by hand — is not delivered:
 [const_image_iso] is stated and read back but consumed by nothing
 here, and Preservation.v's [FCone] stays hand-built; the
 cone-as-transformation presentation of
 Structure/Cone/Natural/Transformation.v is where such a rebuild would
 live.
 - No edit to Instance/Discrete.v, Functor/Hom/Limit.v or
 Test/ProbeHomLimit331.v; the [bool_fam] of Instance/Fun/Terminal.v
 is left in place. 

 --------
 Mac Lane §V.2 练习 4 和 §V.4 练习 5（书页 114, 118；maclane:V.2:ex4, maclane:V.4:ex5）；Riehl §3.4 的开头构造，引理 3.4.3 和练习 3.4.i，以及 §4.6 练习 4.6.iii（riehl:3.4:construction-canonical-comparison, riehl:3.4:lem3, riehl:3.4:exi, riehl:4.6:exiii）。nLab: https://ncatlab.org/nlab/show/preserved+limit背景。对于 H : C ⟶ D 和 F : J ⟶ C 上的一个锥 N，将 H 应用于锥的各条腿会得到 H ◯ F 上的一个锥（Preservation.v 的 [FCone]）；当 H ◯ F 有一个极限锥 M 时，这个图像锥通过 M 的唯一分解就是典范的比较箭头 κ : H (N 的顶点) ~> M 的顶点，由腿方程 cone_leg M x ∘ κ ≈ fmap [H] (cone_leg N x) 以及唯一性决定（Riehl §3.4；Awodey §5.5）。H 恰好在 N 的极限情况下保持极限，当且仅当 κ 是一个同构（Riehl 引理 3.4.3；Mac Lane V.4 习题 5）。Mac Lane V.2 习题 4 加入了指标范畴的变化：对于 W : J' ⟶ J，沿 W 限制的图像锥通过 (H ◯ F) ◯ W 的一个极限进行分解。形状特定的类 [CartesianFunctor]（Functor/Structure/Cartesian.v）和 [TerminalFunctor]（Functor/Structure/Terminal.v）将可逆比较作为一个字段（[fobj_prod_iso], [fobj_one_iso]）假设；最后两节证明每个类等价于在两元素离散形状和空形状下的一般比较的可逆性，因此函子结构层次和极限保持层次汇合。陈旧的前提，重新测量（该问题的“当前状态”早于 #427, 986c7b35）:
 - “比较从未命名；没有双条件”：自 #427 以来，Structure/Limit/Preservation.v 包含 [cone_comparison]、其腿方程和唯一性、双条件在两个方向（[LimitCone_comparison_iso], [comparison_iso_LimitCone], [PreservesLimitCone_of_comparison], [comparison_iso_of_PreservesLimitCone]）、[limit_comparison] — 问题固定的名称在那儿，而不是这里 — 以及 [cocone_comparison]，无其双条件的余极限态射。 
 - “[fmap_cone] 在 Theory/Equivalence/Limit.v”：已不存在；它已合并到 [FCone]（Structure/Limit/Creation.v 记录了此合并）。Construction/Comma/Limit.v（[image_leg], [image_acone]）仍然存在并已测量。- “F ∘ Δc = Δ(F c) 未被陈述”：在 Structure/Limit/Constant.v 中按分量陈述 — [const_image_fobj] 在 [eq_refl]，那里拒绝了严格箭头形式，以及 [const_image_fmap_equiv] 在 ≈ 处。- “没有余极限比较态射”：[cocone_comparison] 存在；余极限 BICONDITIONAL 不存在，并在此提供。- 真正的缺口，均在此提供：沿 W 的重索引；W 一般的比较；Structure/Limit/Product.v 的 [limit_is_indexed_product] 的逆（Functor/Hom/Limit.v 记录了它的缺失）；从 [CartesianFunctor] 和 [TerminalFunctor] 到 [PreservesLimitCone] 的桥。交付内容是什么（57 个常量，每个在全局上下文下封闭）。(1) 重索引。[cone_reindex W N : Cone (F ◯ W)] — 同顶点，腿位于 [W j']，在 [fmap[W] 处从 N 读出一致性；顶点和腿在 [eq_refl] 处读回。沿 [Id] 和沿 [eq_refl] 的复合的函子性，顶点和腿分别处理（[cone_reindex_id_*], [cone_reindex_comp_*]）；不是锥体方程，因为 [Cone ((F ◯ W) ◯ V)] 和 [Cone (F ◯ (W ◯ V))] 是不同的记录类型（探针 N1；Preservation.v [cone_assoc] 重新打包）。重索引的图表部分是 Theory/Kan/Extension.v 的 [Induced := (− ◯ W)]；不需要新的内容。未声称与 [IsLimitCone] 有交互：沿 W 限制的极限锥不必是极限锥。(2) W-一般比较（Mac Lane V.2 练习 4）。[reindex_comparison W H N HM : H (vertex N) ~> vertex M] 对于 [M : Cone ((H ◯ F) ◯ W)] 的极限，如 [cone_comparison H (cone_reindex W N) (islimitcone_assoc HM)]；它的锥腿方程 ([reindex_comparison_commutes])、唯一性 ([reindex_comparison_unique]) 以及可逆性 ⇔ [FCone H (cone_reindex W N)] 的极限性 ([reindex_comparison_iso], [reindex_comparison_iso_LimitCone])。在 [W = Id]，锥 [cone_reindex Id N] 的类型是 [Cone (F ◯ Id)]，而不是 [Cone F]，所以不声称与 [cone_comparison] 存在 [eq_refl] 的对应；锥腿在 [eq_refl] ([cone_reindex_id_leg]) 上一致。(3) 双条件陈述，捆绑。[preserves_iff_comparison_iso F HM : PreservesLimitCone K F ↔ ∀ N, IsLimitCone N → IsIsomorphism (cone_comparison F N HM)]（类型值的 ↔），来自 Preservation.v 的两个方向。[PreservesLimitCone_of_cone]：保留一个极限锥就等于保留它们全部（[limitcone_iso]、[FCone_iso]、[limitcone_transport]）；[PreservesLimitCone_of_comparison_iso]。（4）共极限双条件（Riehl 3.4.i）。[colimitcocone_iso]、[cocone_comparison_commutes]、[cocone_comparison_unique]、[ColimitCocone_comparison_iso]、[comparison_iso_ColimitCocone]、[PreservesColimitCocone_of_comparison]、[comparison_iso_of_PreservesColimitCocone]、[preserves_colimit_iff_comparison_iso] — 在Preservation.v之后逐行在余锥词汇中内建，而不是通过在[F^op]实例化极限块：[FCocone F N]是[(F ◯ K)^op]上的一个锥，[FCone F^op N]是[F^op ◯ K^op]上的一个锥，两种不同的记录类型（探针N5读取条款“无法统一”）；在Preservation.v的[cone_op_comp]重新打包之后，op路径存在（探针控制），但会指代重新打包的锥，而不是[FCocone]。更正 (#477)：colimit 端现在也有 (3) 的 [PreservesLimitCone_of_cone]，作为 [PreservesColimitCocone_of_cocone] 在 CoComparison 部分之后，在 Preservation.v 的 [FCocone_iso] 上；此标题的计数和普查为 57，COUNTS AND CONVENTIONS 记录第 58 个。(5) RIEHL 的 WHISKERING 恒等式在函子层面：[const_image_iso : F ◯ Δ[J] (c) ≈ Δ [J] (F c)] 在 [Functor_Setoid] 中，每个分量 [iso_id]（[const_image_iso_component] 在 [eq_refl] 上）；前例见 Adjunction/Diagonal/Connected.v。(6) RIEHL 的热身：[pullback_comparison H F N HM] 在 [Cospan C]（Structure/Span.v；[Roof] 是无宇宙的），[eq_refl] 到 [cone_comparison]（[pullback_comparison_is]）。(7) RAPL 重述：[rapl_comparison_iso A G HM N HN] — 右伴随的比较是可逆的，来自 Adjunction/Continuity.v 的 [right_adjoint_PreservesLimitCone]（Riehl 4.6.iii 的重述要求）。(8) 离散形状。[DiscreteCat_Functor'] 是 Instance/Discrete.v 的函子，并标注了其宇宙（见 UNIVERSES）。对于任意 [G : DiscreteCat A ⟶ C] — 所以也对于像图 [F ◯ G] — [discrete_cone c pi] 将一族边作为一个圆锥打包（[discrete_cone_leg] 在 [eq_refl] 处），一个圆锥当且仅当其边形成一个 [IsIndexedProduct] 才是极限圆锥：[discrete_IsLimitCone_of_IsIndexedProduct] 和 [discrete_IsIndexedProduct_of_IsLimitCone]，后者是相反的 [limit_is_indexed_product] 从未拥有。(9) 二元积（问题项 4）。[binary_proj] 和 
 [IsIndexedProduct_binary f : 对于任意 [f : bool → C], [binary_cone f] 和 [binary_image_cone f], IsIndexedProduct f (f true × f false) (binary_proj f)]；C 和 D 在映射图上的乘积锥，均为极限；
 [binary_comparison f : F (f true × f false) ~> F (f true) × F (f false)] 
 作为 [cone_comparison] 在它们上，带有 [binary_comparison_exl], [binary_comparison_exr] 和 [binary_comparison_fork : binary_comparison f ≈ fmap exl △ fmap exr] — 该类的 [prod_out], 计算得到而非假设。[cartesian_functor_iff_comparison_iso : CartesianFunctor F ↔ ∀ x y, IsIsomorphism (binary_comparison (binary_fam x y))] 和标题 [cartesian_functor_iff_preserves_binary_products : CartesianFunctor F ↔ ∀ x y, PreservesLimitCone (DiscreteCat_Functor' (binary_fam x y)) F]。(10) 终端对象（问题条目 4）。[nullary_proj] 和 [IsIndexedProduct_nullary f : IsIndexedProduct f 1 (nullary_proj f)] 对于任何 [f : False → C]；[nullary_cone f]，[nullary_image_cone f]；[terminal_comparison f : F 1 ~> 1]，其为 [one]（[terminal_comparison_one]）。Functor/Structure/Terminal.v 记录了 [fobj_one_iso : 1 ≅ F 1] 与 [to : 1 ~> F 1]，因此比较是它的 [from]（探针 N4）；[terminal_functor_iff_comparison_iso] 和 [terminal_functor_iff_preserves_terminal : TerminalFunctor F ↔ PreservesLimitCone (DiscreteCat_Functor' nullary_fam) F]。宇宙（由 [About] 在 [Set Printing Universes] 下对所有 57 个常量进行测量）。- 在任何块中都没有以单词为界的 [Set]。环境类别阐述为 [C : Category@{u u0 u0}]、[D : Category@{u1 u0 u0}]，具有一个共享的同态层级：Preservation.v 的 [IsLimitCone] 确定形状的同态和证明层级与环境的一致，并且 [Compose] 在一个同态层级上为其三个类别类型化。[const_image_iso] 承载方程 [u0 = u3]（J 的同态层级是 C 的，通过 [Functor_Setoid]）；离散桥承载 [h = p]、[h = uh]、[h = up]，与命名的形状层级相同的识别。十九个模块——
 [DiscreteCat_Functor'] 以及其上构建的十八个常量——
 承载了本文件的 ONE  [Program Definition], [DiscreteCat_Functor'] 本身（该段落早期的修订版本将它们归于 Structure/Cartesian.v，其 [Cartesian], [fork] 和 [exl] 不承载任何内容，这里 [binary_proj] 和 [IsIndexedProduct_binary] 也是如此）
 的 stdlib 上限 [JMeq], [EqdepFacts] 和 [eq_rect_r]。57个块中的50个块带有一个严格的界限，在每种情况下，这个界限都是在辅助宇宙下的同态或证明层次，对[Program]生成的常量：[Compose@{u u0 u1 u2 u3}]自己的[u3 < u2]（Theory/Functor.v: 259）来说，每当出现复合函子时，在离散部分则为[DiscreteCat_Functor']自己的[up < u]；七个基本常量（[binary_fam]、[binary_proj]、[IsIndexedProduct_binary]，它们的零元双子以及[discrete_IsLimitCone_of_IsIndexedProduct]）没有界限。早期的修订将界限[u0 < u5]解释为将[bool]和[False]置于形状的对象层次之下；实际上并非如此——它们位于[Set]，没有显示任何约束。- 为什么是局部注释函子——以及为什么它现在只是一个别名。该条目的早期版本写道：“未经注释的 [DiscreteCat_Functor] 实例化了 [DiscreteCat@{u Set Set}]（Functor/Hom/Limit.v；Test/ProbeHomLimit331.v 通过其锥映射 [IsLimitCone]），因此 [cone_comparison] 在其上被拒绝于 [Set]（探针 N2，以及通过 Product.v 的 [family_cone] 的 N3）。[DiscreteCat_Functor'@{o h p uo uh up +}] 对形状的各级自由具有相同的作用。”Instance/Discrete.v 在这里没有被编辑：注释上游的捐赠者是提升，Functor/Hom/Limit.v 已经命名，但它翻转了，Test/ProbeHomLimit331.v 的引脚并重新编写了那篇文章，而是否执行则在 PR 中交给 John，而不是由此文件决定。问题已经解决：捐赠者确实在上游被注释，在 PR “algebraic carriers are sets”（2026-09-17）中，在 Instance/Discrete.v 中，并且使用相同的绑定器列表。探针 N2 和 N3 被翻转并作为阳性对照；Test/ProbeHomLimit331.v 的引脚按预测翻转，并且该文件的文章被重新编写。因此，本地 [DiscreteCat_Functor'] 现在是一个透明别名，保留的原因如其声明上方所述，而不是由于签名的差异。计数与约定。- 57 个常量——45 个 [def] 和 12 个 [prf] 在 [.glob] 中——均“在全局上下文下闭合”，零 [Axioms:] 行，全部在 Makefile 的 print-assumptions 目标中完全限定。修正 (#477)：由于 #477 添加了 [PreservesColimitCocone_of_cocone]（一个没有证明脚本的项），因此为 58 个，其中 46 个 [def] 和 12 个 [prf]；它在全局上下文下闭合，并在 #477 的目标块中完全限定。其绑定器已写出，形状的一个同源等级以及像 Structure/Limit/Absolute.v 所写的环境中一样，并且其 [About] 块不包含 [Set] 也没有方程，只有一个严格界限（[Compose] 的，通过 [FCocone]）以及 [Projections] 的 stdlib 上限，正如 [PreservesLimitCone_of_cone] 的一样。[Defined] 和 [Qed] 的计数保持不变，闭合也是如此：#477 在这里没有添加 [Require]。——六个 [Defined] 终止的证明。两个通过单独翻转到 [Qed] 承重：[const_image_iso]（其组件回读在 [eq_refl] 停止）和 [discrete_cone]（[discrete_cone_leg] 停止）。四个可以自由翻转，并且按照数据约定保持 [Defined]——[comparison_iso_ColimitCocone]、[discrete_IsLimitCone_of_IsIndexedProduct]、[IsIndexedProduct_binary] 和 [IsIndexedProduct_nullary] 生成 [∃!] 数据在下游被消耗。十二个 [Qed]。- 闭包 37 个文件（不包括自身）（传递 [Require] 通过 .Makefile.coq.d）：Functor/Diagonal.v 在边际成本为 6，Adjunction/Continuity.v 为 2，Functor/Structure/Terminal.v、Functor/Structure/Cartesian.v、Structure/Limit/Product.v 和 Structure/Span.v 每个为 1，其他十四个 [Require] 为 0。 - 其他地方的近似同名，未修改：Instance/Fun/Terminal.v 定义了与 [bool_fam] 相同的族（因此此处为 [binary_fam]），Structure/Limit/Finite.v 是 [empty_cone] 在 [EmptyDiagram] 上的扩展（因此此处为 [nullary_cone]），Instance/Proset/Order.v 为 [pair_cone]，Structure/Limit/Product.v 的 [family_cone]，与 [discrete_cone] 相同的构造，专门应用于 [DiscreteCat_Functor f] —— 最接近的现存常量，保持原样。- Test/ProbeComparison419.v 镜像 [Require] 列表，并包含 6 条反驳命令（1 条工具命令 + 5 条三种类型的否定命令：1 条转换，2 条全域，2 条类型——N2/N3 和 N5 可通过它们的全域和归一化条款与其他区分，而 N1 和 N4 共享纯 has-type 形状并在类型名称上不同），每次在整个文件的副本中移除一条；在 [eq_refl] 上进行回读；在四个穷尽例外下，守护覆盖范围内部 35 个标记 / 外部 31 个标记；重命名模拟 5/5，每个正面行上的第一次中断。[make todo] 仅通过那 6 行增加（2196 → 2202），因此按原文所述，问题的“未增加新命中”框未满足；通过将否定命令移出构建而是被披露，而不是满足。未交付。- 将函子性重指数化为 CONES 的方程，或作为两个括号比较的方程：记录类型不同；只给出了顶点和边的方程。- 关于 [IsLimitCone] 的任何 [cone_reindex] 声明（通常是错误的），作为图变量中的自然变换的比较，以及将 [lim (F ◯ W)] 理解为右 Kan 延拓——均未尝试。- 鞭状恒等式的严格 ([=]) 箭头形式：在 Structure/Limit/Constant.v 中被拒绝并固定，此处不再重复。- 树的  [Two_Discrete] 和  [0] 形状处的桥梁（Structure/Limit/Cartesian.v  [Cartesian_Limit] 和 Structure/Limit/Terminal.v  [Terminal_Limit]，两个都是 [Qed] 并且在 [Limit] 级别）：这里的桥梁位于标注的 [DiscreteCat bool] 和 [DiscreteCat False] 处，并且在这些形状之间没有建立通道。- Structure/Limit/Preservation/Shapes.v 的 [PreservesProductCones] — 一个跟踪文件，不在 [_CoqProject] 中，也从未被 [make] 编译 — 在此既未注册也未重申（在 John 的 PR 中出现，但尚未解决）。- Riehl的 whiskering 复选框的可操作部分——通过 whiskering 而不是手工构建 IMAGE CONE——没有实现：
 [const_image_iso] 已声明并回读，但在此未被使用，
 Preservation.v 的 [FCone] 仍然是手工构建的；
 Structure/Cone/Natural/Transformation.v 中的锥体作为变换的表示是该重建将存在的地方。
 - 对 Instance/Discrete.v、Functor/Hom/Limit.v 或 Test/ProbeHomLimit331.v 没有任何修改；
 Instance/Fun/Terminal.v 的 [bool_fam] 保持不变。
*)

(* * ** Reindexing a cone along a functor between shapes / * ** 沿着形状之间的函子重新索引锥 *)

Section Reindex.

Context {J' J C : Category} (W : J' ⟶ J) {F : J ⟶ C}.

(*
 Restricting a cone over [F] along [W]: the same apex, the legs at the
 objects [W j'], the coherence read off [N]'s at the arrows [fmap[W] f]. 

 --------
 沿着  [W] 限制 [F] 上的圆锥：相同的顶点，位于对象 [W j'] 的边，在箭头 [fmap[W] f] 上读出的 [N] 的相干性。
*)
Definition cone_reindex (N : Cone F) : Cone (F ◯ W) :=
  @Build_Cone J' C (F ◯ W) (vertex_obj[N])
    (@Build_ACone J' C (vertex_obj[N]) (F ◯ W)
       (fun j' => cone_leg N (W j'))
       (fun x y f =>
          @cone_coherence J C (vertex_obj[N]) F (@coneFrom _ _ _ N)
            (W x) (W y) (fmap[W] f))).

Example cone_reindex_apex (N : Cone F) :
  vertex_obj[cone_reindex N] = vertex_obj[N] := eq_refl.

Example cone_reindex_leg (N : Cone F) (j' : J') :
  cone_leg (cone_reindex N) j' = cone_leg N (W j') := eq_refl.

End Reindex.

(*
 Functoriality in the shape functor, at the level where the types allow an
 equation: apex and legs.  [Cone ((F ◯ W) ◯ V)] and [Cone (F ◯ (W ◯ V))]
 are distinct record types (the probe pins the refusal), so there is no
 equation of CONES to state; [cone_assoc] of Preservation.v repackages one
 into the other. 

 --------
 在形状函子中的函子性，在类型允许方程的层面上：顶点和边。[Cone ((F ◯ W) ◯ V)] 和 [Cone (F ◯ (W ◯ V))] 是不同的记录类型（探针标记了拒绝），所以没有 CONES 的方程可以陈述；Preservation.v 的 [cone_assoc] 将一个重新封装为另一个。
*)

Example cone_reindex_id_apex {J C : Category} {F : J ⟶ C} (N : Cone F) :
  vertex_obj[cone_reindex Id[J] N] = vertex_obj[N] := eq_refl.

Example cone_reindex_id_leg {J C : Category} {F : J ⟶ C} (N : Cone F) (j : J) :
  cone_leg (cone_reindex Id[J] N) j = cone_leg N j := eq_refl.

Example cone_reindex_comp_apex {J'' J' J C : Category} (W : J' ⟶ J) (V : J'' ⟶ J')
  {F : J ⟶ C} (N : Cone F) :
  vertex_obj[cone_reindex V (cone_reindex W N)] = vertex_obj[cone_reindex (W ◯ V) N]
  := eq_refl.

Example cone_reindex_comp_leg {J'' J' J C : Category} (W : J' ⟶ J) (V : J'' ⟶ J')
  {F : J ⟶ C} (N : Cone F) (j : J'') :
  cone_leg (cone_reindex V (cone_reindex W N)) j = cone_leg (cone_reindex (W ◯ V) N) j
  := eq_refl.

(* * ** The comparison with a change of shape: H (Lim F) ~> Lim ((H ◯ F) ◯ W) / * ** 与形状变化的比较：H (Lim F) ~> Lim ((H ◯ F) ◯ W) *)

Section ReindexComparison.

Context {J' J C D : Category} (W : J' ⟶ J) {F : J ⟶ C} (H : C ⟶ D).

(*
 Mac Lane's V.2 Exercise 4 arrow: the image under [H] of a cone over [F],
 restricted along [W], mediated into a limit cone of [(H ◯ F) ◯ W].  The
 limit cone is taken at the bracketing [(H ◯ F) ◯ W] so that [W = Id]
 reads as the plain comparison; [islimitcone_assoc] moves it to
 [H ◯ (F ◯ W)], which is where the image of the reindexed cone lives. 

 --------
 Mac Lane 的第 V.2 章练习 4 箭头：一个在 [H] 下的锥体图像，该锥体位于 [F] 上，沿着 [W] 受限，并中介到 [(H ◯ F) ◯ W] 的极限锥中。极限锥取在括号 [(H ◯ F) ◯ W] 处，以便 [W = Id] 读作普通比较；[islimitcone_assoc] 将其移动到 [H ◯ (F ◯ W)]，这就是重新索引锥的图像所在的位置。
*)
Definition reindex_comparison (N : Cone F)
  {M : Cone ((H ◯ F) ◯ W)} (HM : IsLimitCone M) :
  H (vertex_obj[N]) ~{D}~> vertex_obj[M] :=
  cone_comparison H (cone_reindex W N) (islimitcone_assoc HM).

Lemma reindex_comparison_commutes (N : Cone F)
  {M : Cone ((H ◯ F) ◯ W)} (HM : IsLimitCone M) (j' : J') :
  cone_leg M j' ∘ reindex_comparison N HM ≈ fmap[H] (cone_leg N (W j')).
Proof.
  exact (cone_comparison_commutes H (cone_reindex W N) (islimitcone_assoc HM) j').
Qed.

Lemma reindex_comparison_unique (N : Cone F)
  {M : Cone ((H ◯ F) ◯ W)} (HM : IsLimitCone M)
  (v : H (vertex_obj[N]) ~{D}~> vertex_obj[M]) :
  (∀ j' : J', cone_leg M j' ∘ v ≈ fmap[H] (cone_leg N (W j'))) →
  reindex_comparison N HM ≈ v.
Proof.
  intro Hv.
  exact (cone_comparison_unique H (cone_reindex W N) (islimitcone_assoc HM) v Hv).
Qed.

(* Invertibility is exactly limit-ness of the image of the reindexed cone, both ways. / 可逆性恰好是重索引圆锥的像的极限性，两种方向都是如此。 *)
Definition reindex_comparison_iso (N : Cone F)
  {M : Cone ((H ◯ F) ◯ W)} (HM : IsLimitCone M)
  (HN : IsLimitCone (FCone H (cone_reindex W N))) :
  IsIsomorphism (reindex_comparison N HM) :=
  LimitCone_comparison_iso H (cone_reindex W N) (islimitcone_assoc HM) HN.

Definition reindex_comparison_iso_LimitCone (N : Cone F)
  {M : Cone ((H ◯ F) ◯ W)} (HM : IsLimitCone M)
  (Hi : IsIsomorphism (reindex_comparison N HM)) :
  IsLimitCone (FCone H (cone_reindex W N)) :=
  comparison_iso_LimitCone H (cone_reindex W N) (islimitcone_assoc HM) Hi.

End ReindexComparison.

(* * ** The biconditional, bundled; one limit cone suffices / * ** 双条件，捆绑；一个极限锥足够 *)

Section LimitBundle.

Context {J C D : Category} {K : J ⟶ C} (F : C ⟶ D).

(* Riehl's Lemma 3.4.3 and Mac Lane's V.4 Exercise 5 as one statement: the two directions are Preservation.v's [comparison_iso_of_PreservesLimitCone] and [PreservesLimitCone_of_comparison]. / 将 Riehl 的引理 3.4.3 和 Mac Lane 的 V.4 练习 5 作为一个陈述：两个方向是 Preservation.v 的 [comparison_iso_of_PreservesLimitCone] 和 [PreservesLimitCone_of_comparison]。 *)
Definition preserves_iff_comparison_iso {M : Cone (F ◯ K)} (HM : IsLimitCone M) :
  PreservesLimitCone K F ↔
  (∀ N : Cone K, IsLimitCone N → IsIsomorphism (cone_comparison F N HM)) :=
  (fun P => comparison_iso_of_PreservesLimitCone F P HM,
   PreservesLimitCone_of_comparison F HM).

(*
 Preserving ONE limit cone of [K] is preserving them all: any other is
 isomorphic to it by [limitcone_iso], the image of that isomorphism is a
 cone isomorphism by [FCone_iso], and limit-ness transports along it. 

 --------
 保留 [K] 的一个极限锥就是保留它们全部：任何其他的锥通过 [limitcone_iso] 与它同构，该同构的像通过 [FCone_iso] 是一个锥同构，并且极限性质沿其传递。
*)
Definition PreservesLimitCone_of_cone (N0 : Cone K) (HN0 : IsLimitCone N0)
  (H0 : IsLimitCone (FCone F N0)) : PreservesLimitCone K F :=
  fun N HN => limitcone_transport (FCone_iso F (limitcone_iso HN0 HN)) H0.

Definition PreservesLimitCone_of_comparison_iso (N0 : Cone K) (HN0 : IsLimitCone N0)
  {M : Cone (F ◯ K)} (HM : IsLimitCone M)
  (Hi : IsIsomorphism (cone_comparison F N0 HM)) : PreservesLimitCone K F :=
  PreservesLimitCone_of_cone N0 HN0 (comparison_iso_LimitCone F N0 HM Hi).

End LimitBundle.

(* * ** The colimit comparison and its biconditional / * ** 共极限比较及其双条件 *)

Section CoComparison.

Context {J C D : Category} {K : J ⟶ C} (F : C ⟶ D).

(*
 Built directly in the cocone vocabulary ([cocone_inj], [FCocone],
 [cocone_comparison]) and not by instantiating the limit block at [F^op]:
 [FCocone F N] is a cone over [(F ◯ K)^op] while [FCone F^op N] is one
 over [F^op ◯ K^op], two distinct record types (Preservation.v
 repackages between them with [cone_op_comp]).  Every proof below is the
 mirror image of Preservation.v, one line for one line. 

 --------
 直接在 cocone 词汇表中构建（[cocone_inj]、[FCocone]、[cocone_comparison]），而不是通过在 [F^op] 实例化极限块：[FCocone F N] 是 [(F ◯ K)^op] 上的一个锥，而 [FCone F^op N] 是 [F^op ◯ K^op] 上的一个锥，它们是两个不同的记录类型（Preservation.v 在它们之间用 [cone_op_comp] 重新打包）。下面的每个证明都是 Preservation.v 的镜像，一行对应一行。
*)

Definition colimitcocone_iso {N M : Cocone K}
  (HN : IsColimitCocone N) (HM : IsColimitCocone M) : ConeIso N M :=
  limitcone_iso HN HM.

Lemma cocone_comparison_commutes (N : Cocone K) {M : Cocone (F ◯ K)}
  (HM : IsColimitCocone M) (x : J) :
  cocone_comparison F N HM ∘ cocone_inj M x ≈ fmap[F] (cocone_inj N x).
Proof.
  exact (unique_property (HM (FCocone F N)) x).
Qed.

Lemma cocone_comparison_unique (N : Cocone K) {M : Cocone (F ◯ K)}
  (HM : IsColimitCocone M) (v : vertex_obj[M] ~{D}~> F (vertex_obj[N])) :
  (∀ x : J, v ∘ cocone_inj M x ≈ fmap[F] (cocone_inj N x)) →
  cocone_comparison F N HM ≈ v.
Proof.
  intro Hv. exact (uniqueness (HM (FCocone F N)) v Hv).
Qed.

Definition ColimitCocone_comparison_iso (N : Cocone K) {M : Cocone (F ◯ K)}
  (HM : IsColimitCocone M) (HN : IsColimitCocone (FCocone F N)) :
  IsIsomorphism (cocone_comparison F N HM) :=
  @Build_IsIsomorphism D (vertex_obj[M]) (F (vertex_obj[N]))
    (cocone_comparison F N HM)
    (from `1 (limitcone_iso HN HM))
    (iso_from_to `1 (limitcone_iso HN HM))
    (iso_to_from `1 (limitcone_iso HN HM)).

Definition comparison_iso_ColimitCocone (N : Cocone K) {M : Cocone (F ◯ K)}
  (HM : IsColimitCocone M) (Hi : IsIsomorphism (cocone_comparison F N HM)) :
  IsColimitCocone (FCocone F N).
Proof.
  assert (ci : ConeIso (FCocone F N) M).
  { unshelve eexists.
    - (* the comparison, read as an isomorphism of [D^op]: its two inverse laws swap roles under [^op] / 这个比较，可以被视作 [D^op] 的一个同构：其两个逆律在 [^op] 下互换角色 *)
      exact (@Build_Isomorphism (D^op) (F (vertex_obj[N])) (vertex_obj[M])
               (cocone_comparison F N HM)
               (@two_sided_inverse D _ _ _ Hi)
               (@is_left_inverse D _ _ _ Hi)
               (@is_right_inverse D _ _ _ Hi)).
    - intro x; exact (cocone_comparison_commutes N HM x). }
  exact (limitcone_transport (ConeIso_sym ci) HM).
Defined.

Definition PreservesColimitCocone_of_comparison {M : Cocone (F ◯ K)}
  (HM : IsColimitCocone M)
  (H : ∀ N : Cocone K, IsColimitCocone N → IsIsomorphism (cocone_comparison F N HM)) :
  PreservesColimitCocone K F :=
  fun N HN => comparison_iso_ColimitCocone N HM (H N HN).

Definition comparison_iso_of_PreservesColimitCocone
  (P : PreservesColimitCocone K F) {M : Cocone (F ◯ K)} (HM : IsColimitCocone M)
  (N : Cocone K) (HN : IsColimitCocone N) :
  IsIsomorphism (cocone_comparison F N HM) :=
  ColimitCocone_comparison_iso N HM (P N HN).

(* Riehl's Exercise 3.4.i: the dual of Lemma 3.4.3. / Riehl 的练习 3.4.i：引理 3.4.3 的对偶。 *)
Definition preserves_colimit_iff_comparison_iso {M : Cocone (F ◯ K)}
  (HM : IsColimitCocone M) :
  PreservesColimitCocone K F ↔
  (∀ N : Cocone K, IsColimitCocone N → IsIsomorphism (cocone_comparison F N HM)) :=
  (fun P => comparison_iso_of_PreservesColimitCocone P HM,
   PreservesColimitCocone_of_comparison HM).

End CoComparison.

(*
 The cocone twin of [PreservesLimitCone_of_cone]: preserving ONE
 colimiting cocone of [K] is preserving them all, through
 [colimitcocone_iso] above and Preservation.v's [FCocone_iso].  Added by
 #477, the tree having had no cocone twin, for
 Structure/Limit/Absolute.v's [AbsoluteColimitCocone_preserves], with
 that file's binders. 

 --------
 [PreservesLimitCone_of_cone] 的余锥双胞胎：保持 [K] 的单余锥极限就是保持它们全部，通过上面的 [colimitcocone_iso] 和 Preservation.v 的 [FCocone_iso]。由 #477 添加，因为树之前没有余锥双胞胎，用于 Structure/Limit/Absolute.v 的 [AbsoluteColimitCocone_preserves]，以及该文件的绑定器。
*)

Definition PreservesColimitCocone_of_cocone@{jo co ch do +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}}
  {D : Category@{do ch ch}} {K : J ⟶ C} (F : C ⟶ D)
  (N0 : Cocone K) (HN0 : IsColimitCocone N0)
  (H0 : IsColimitCocone (FCocone F N0)) : PreservesColimitCocone K F :=
  fun N HN =>
    limitcone_transport (FCocone_iso F (colimitcocone_iso HN0 HN)) H0.

(* * ** Riehl's whiskering identity F ∘ Δc = Δ(Fc), at functor level / * ** Riehl 的胡须同一性 F ∘ Δc = Δ(Fc)，在函子层面 *)

Section Whisker.

Context {J C D : Category} (F : C ⟶ D) (c : C).

(*
 The two functors agree on objects by [eq_refl] and on arrows up to
 [fmap_id] (Structure/Limit/Constant.v records both facts
 componentwise, the strict arrow form being refused there); as objects
 of the functor category they are isomorphic with identity components. 

 --------
 这两个函子在对象上通过 [eq_refl] 一致，并且在箭头上至多通过 [fmap_id]（一方面 Structure/Limit/Constant.v 分别记录了这两个事实，严格箭头形式在那里被拒绝）；作为函子范畴的对象，它们是同构的，并且同构的分量是恒等的。
*)
Definition const_image_iso :
  @equiv _ (@Functor_Setoid J D) (F ◯ Δ[J](c)) (Δ[J](F c)).
Proof.
  exists (fun x => iso_id).
  intros x y f; simpl.
  rewrite fmap_id. cat.
Defined.

Example const_image_iso_component (x : J) :
  to (`1 const_image_iso x) = id[F c] := eq_refl.

End Whisker.

(* * ** Riehl's warm-up: the pullback comparison F (X ×_Z Y) ~> F X ×_{F Z} F Y / * ** Riehl 的热身：拉回比较 F (X ×_Z Y) ~> F X ×_{F Z} F Y *)

Section PullbackWarmup.

Context {C D : Category} (H : C ⟶ D) (F : Cospan C).

Definition pullback_comparison (N : Cone F) {M : Cone (H ◯ F)}
  (HM : IsLimitCone M) : H (vertex_obj[N]) ~{D}~> vertex_obj[M] :=
  cone_comparison H N HM.

Example pullback_comparison_is (N : Cone F) {M : Cone (H ◯ F)}
  (HM : IsLimitCone M) :
  pullback_comparison N HM = cone_comparison H N HM := eq_refl.

End PullbackWarmup.

(* * ** RAPL restated: the comparison of a right adjoint is invertible / * ** RAPL 重申：右伴随的比较是可逆的 *)

Section RAPLRestated.

Context {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U)
        {J : Category} (G : J ⟶ C).

Definition rapl_comparison_iso {M : Cone (U ◯ G)} (HM : IsLimitCone M)
  (N : Cone G) (HN : IsLimitCone N) :
  IsIsomorphism (cone_comparison U N HM) :=
  comparison_iso_of_PreservesLimitCone U
    (right_adjoint_PreservesLimitCone A G) HM N HN.

End RAPLRestated.

(* * ** Discrete shapes: a cone is limiting iff its legs are an indexed product / * ** 离散形状：当且仅当它的边是一个索引积时，锥体才是有限的 *)

(*
 An annotated discrete-diagram functor.
 RECORDED CORRECTION.  An earlier revision declared this as a second
 [Program Definition] with the same actions as Instance/Discrete.v's
 [DiscreteCat_Functor], because that one was declared with bare binders and
 so minimized to [DiscreteCat@{u Set Set}], pinning any [IsLimitCone] over
 its cones to hom level [Set] (Functor/Hom/Limit.v; the probe pins
 the comparison's refusal).  In the PR "algebraic carriers are sets"
 (2026-09-17) the SAME binders were put on [DiscreteCat_Functor] itself, so
 the two now have identical measured signatures:

 DiscreteCat_Functor@{o h p uo uh up u} :
 ∀ {A : Type@{o}} {C : Category@{uo uh up}},
 (A → obj) → Functor@{o h p uo uh up}

 This is therefore no longer a separate construction but a transparent
 alias, kept because eleven files and three probes name it and because the
 name marks, at each use site, the places where the shape's hom and proof
 levels must stay free and be identified with the ambient's by
 [IsLimitCone].  The binders are repeated on the alias deliberately: an
 unannotated [:=] alias of an annotated constant over a bare
 [(C : Category)] minimizes back to [Category@{u u u}]. 

 --------
 一个带注释的离散图函子。
 已记录更正。早期的修订将其声明为一个第二个 [Program Definition]，其操作与 Instance/Discrete.v 的 [DiscreteCat_Functor] 相同，因为那个被声明为裸绑定器，因此被最小化为 [DiscreteCat@{u Set Set}]，将其圆锥上的任何 [IsLimitCone] 固定为同态层级 [Set]（Functor/Hom/Limit.v；探针固定了比较的拒绝）。在 PR "代数载体是集合"（2026-09-17）中，相同的绑定器被放在 [DiscreteCat_Functor] 本身上，因此现在这两个具有相同的测量签名：

 DiscreteCat_Functor@{o h p uo uh up u} :
 ∀ {A : Type@{o}} {C : Category@{uo uh up}},
 (A → obj) → Functor@{o h p uo uh up}因此，这不再是一个独立的结构，而是一个透明的别名，之所以保留，是因为有十一份文件和三个探针使用了它，而且这个名称在每个使用位置都标记了形状的 hom 和 proof 级别必须保持自由，并通过 [IsLimitCone] 与环境的对应标识。别名上重复出现绑定器是有意为之：未注释的 [:=] 别名对于注释过的常量在裸 [(C : Category)] 上会最小化回到 [Category@{u u u}]。
*)
Definition DiscreteCat_Functor'@{o h p uo uh up +}
  {A : Type@{o}} {C : Category@{uo uh up}} (f : A → C) :
  DiscreteCat@{o h p} A ⟶ C := @DiscreteCat_Functor A C f.

Section DiscreteBridge.

Universe o h p uo uh up.

Context {A : Type@{o}} {C : Category@{uo uh up}} (G : DiscreteCat@{o h p} A ⟶ C).

(*
 Any family of legs is a cone over a discrete diagram: coherence has only
 the identity arrows to check. 

 --------
 任何腿族都是离散图上的一个圆锥：一致性只需要检查恒等箭头。
*)
Definition discrete_cone (c : C) (pi : ∀ a : A, c ~> G a) : Cone G.
Proof.
  unshelve refine (@Build_Cone (DiscreteCat A) C G c
                     (@Build_ACone (DiscreteCat A) C c G pi _)).
  intros x y e; destruct e.
  change (@eq_refl A x) with (@id (DiscreteCat A) x).
  rewrite fmap_id.
  apply id_left.
Defined.

Example discrete_cone_leg (c : C) (pi : ∀ a : A, c ~> G a) (a : A) :
  cone_leg (discrete_cone c pi) a = pi a := eq_refl.

(*
 The two readings of "product" coincide, for ANY functor out of a discrete
 shape — in particular for image diagrams [F ◯ G]. 

 --------
 “积”的两种读法是一致的，对于任何从离散形状出的函子——特别是对于像图 [F ◯ G] 这样的图像图。
*)
Definition discrete_IsLimitCone_of_IsIndexedProduct (N : Cone G)
  (HP : IsIndexedProduct (fobj[G]) (vertex_obj[N]) (cone_leg N)) :
  IsLimitCone N.
Proof.
  intro M.
  destruct (iprod_desc HP (cone_leg M)) as [u Hu Huniq].
  exists u.
  - exact Hu.
  - exact Huniq.
Defined.

(* The converse Structure/Limit/Product.v's [limit_is_indexed_product] never had (Functor/Hom/Limit.v records the absence). / The converse Structure/Limit/Product.v 的 [limit_is_indexed_product] 从未出现过（Functor/Hom/Limit.v 记录了其不存在）。 *)
Definition discrete_IsIndexedProduct_of_IsLimitCone (N : Cone G)
  (HN : IsLimitCone N) :
  IsIndexedProduct (fobj[G]) (vertex_obj[N]) (cone_leg N) :=
  {| iprod_desc := fun c pi => HN (discrete_cone c pi) |}.

End DiscreteBridge.

(* * ** Binary products: [CartesianFunctor] is invertibility of the comparison / * ** 二元积：[CartesianFunctor] 是比较的可逆性 *)

Section BinaryProducts.

Context {C : Category} `{@Cartesian C}.

(*
 A two-element family and its product's projections, as an indexed
 product over [bool]. 

 --------
 一个由两个元素组成的族及其积的投影，作为 [bool] 上的一个索引积。
*)
Definition binary_proj (f : bool → C) (b : bool) : f true × f false ~> f b :=
  match b return (f true × f false ~> f b) with
  | true => exl
  | false => exr
  end.

Definition IsIndexedProduct_binary (f : bool → C) :
  IsIndexedProduct f (f true × f false) (binary_proj f).
Proof.
  constructor; intros c pi.
  exists (pi true △ pi false).
  - intros [|]; simpl.
    + apply exl_fork.
    + apply exr_fork.
  - intros v Hv.
    symmetry.
    apply (snd (ump_products _ _ _)).
    split.
    + exact (Hv true).
    + exact (Hv false).
Defined.

Definition binary_fam (x y : C) : bool → C := fun b => if b then x else y.

End BinaryProducts.

Section CartesianBridge.

Context {C D : Category} (F : C ⟶ D) `{@Cartesian C} `{@Cartesian D}.

(* the product cone of [C] over the discrete two-object diagram of [f] / [f] 的离散两对象图上的 [C] 的乘积锥 *)
Definition binary_cone (f : bool → C) : Cone (DiscreteCat_Functor' f) :=
  discrete_cone (DiscreteCat_Functor' f) (f true × f false) (binary_proj f).

Definition binary_cone_IsLimitCone (f : bool → C) : IsLimitCone (binary_cone f) :=
  discrete_IsLimitCone_of_IsIndexedProduct _ (binary_cone f)
    (IsIndexedProduct_binary f).

(* the product cone of [D] over the IMAGE diagram [F ◯ DiscreteCat_Functor' f] / 在 IMAGE 图 [F ◯ DiscreteCat_Functor' f] 上的 [D] 的积锥 *)
Definition binary_image_cone (f : bool → C) : Cone (F ◯ DiscreteCat_Functor' f) :=
  discrete_cone (F ◯ DiscreteCat_Functor' f) (F (f true) × F (f false))
    (binary_proj (fun b => F (f b))).

Definition binary_image_cone_IsLimitCone (f : bool → C) :
  IsLimitCone (binary_image_cone f) :=
  discrete_IsLimitCone_of_IsIndexedProduct _ (binary_image_cone f)
    (IsIndexedProduct_binary (fun b => F (f b))).

(* The comparison F (x × y) ~> F x × F y, as the general [cone_comparison] at the two product cones. / 作为两个积锥的一般 [cone_comparison]，比较 F (x × y) ~> F x × F y。 *)
Definition binary_comparison (f : bool → C) :
  F (f true × f false) ~{D}~> F (f true) × F (f false) :=
  cone_comparison F (binary_cone f) (binary_image_cone_IsLimitCone f).

Lemma binary_comparison_exl (f : bool → C) :
  exl ∘ binary_comparison f ≈ fmap[F] exl.
Proof.
  exact (cone_comparison_commutes F (binary_cone f)
           (binary_image_cone_IsLimitCone f) true).
Qed.

Lemma binary_comparison_exr (f : bool → C) :
  exr ∘ binary_comparison f ≈ fmap[F] exr.
Proof.
  exact (cone_comparison_commutes F (binary_cone f)
           (binary_image_cone_IsLimitCone f) false).
Qed.

(* It is the pairing of the images of the projections — the forward map [prod_out] of Functor/Structure/Cartesian.v's class, computed rather than postulated. / 它是投影图像的配对——Functor/Structure/Cartesian.v 类的前向映射 [prod_out]，计算得到的而非假设的。 *)
Lemma binary_comparison_fork (f : bool → C) :
  binary_comparison f ≈ fmap[F] exl △ fmap[F] exr.
Proof.
  apply (snd (ump_products _ _ _)).
  split.
  - apply binary_comparison_exl.
  - apply binary_comparison_exr.
Qed.

Theorem cartesian_functor_iff_comparison_iso :
  @CartesianFunctor C D F _ _ ↔
  (∀ x y : C, IsIsomorphism (binary_comparison (binary_fam x y))).
Proof.
  split.
  - intros HF x y.
    unshelve refine {| two_sided_inverse := from (@fobj_prod_iso _ _ F _ _ HF x y) |}.
    + rewrite binary_comparison_fork.
      rewrite fmap_exl, fmap_exr; simpl.
      rewrite fork_comp.
      rewrite fork_exl_exr.
      rewrite id_left.
      apply iso_to_from.
    + rewrite binary_comparison_fork.
      rewrite fmap_exl, fmap_exr; simpl.
      rewrite fork_comp.
      rewrite fork_exl_exr.
      rewrite id_left.
      apply iso_from_to.
  - intros Hi.
    unshelve refine {| fobj_prod_iso := fun x y => IsIsoToIso _ (Hi x y) |}.
    + intros x y; simpl. symmetry. apply (binary_comparison_exl (binary_fam x y)).
    + intros x y; simpl. symmetry. apply (binary_comparison_exr (binary_fam x y)).
    + intros x y z f g; simpl.
      rewrite <- (id_left (fmap[F] (f △ g))).
      rewrite <- (is_left_inverse (IsIsomorphism := Hi y z)).
      rewrite <- comp_assoc.
      apply compose_respects; [reflexivity |].
      apply (snd (ump_products _ _ _)).
      split.
      * rewrite comp_assoc.
        rewrite (binary_comparison_exl (binary_fam y z)).
        rewrite <- fmap_comp.
        now rewrite exl_fork.
      * rewrite comp_assoc.
        rewrite (binary_comparison_exr (binary_fam y z)).
        rewrite <- fmap_comp.
        now rewrite exr_fork.
Qed.

(*
 The issue's headline: a cartesian functor is exactly a functor preserving
 the limit cones of the two-object discrete diagrams. 

 --------
 问题的标题：笛卡尔函子正是一个保持两个对象的离散图的极限锥的函子。
*)
Theorem cartesian_functor_iff_preserves_binary_products :
  @CartesianFunctor C D F _ _ ↔
  (∀ x y : C, PreservesLimitCone (DiscreteCat_Functor' (binary_fam x y)) F).
Proof.
  split.
  - intros HF x y.
    exact (PreservesLimitCone_of_comparison_iso F (binary_cone _)
             (binary_cone_IsLimitCone _) (binary_image_cone_IsLimitCone _)
             (fst cartesian_functor_iff_comparison_iso HF x y)).
  - intros P.
    apply (snd cartesian_functor_iff_comparison_iso).
    intros x y.
    exact (comparison_iso_of_PreservesLimitCone F (P x y)
             (binary_image_cone_IsLimitCone _) (binary_cone _)
             (binary_cone_IsLimitCone _)).
Qed.

End CartesianBridge.

(* * ** The terminal object: [TerminalFunctor] is invertibility of the comparison / * ** 终对象：[TerminalFunctor] 是比较的可逆性 *)

Section NullaryProducts.

Context {C : Category} `{@Terminal C}.

Definition nullary_proj (f : False → C) (a : False) : terminal_obj ~> f a :=
  match a with end.

Definition IsIndexedProduct_nullary (f : False → C) :
  IsIndexedProduct f terminal_obj (nullary_proj f).
Proof.
  constructor; intros c pi.
  exists one.
  - intros [].
  - intros v _; apply one_unique.
Defined.

Definition nullary_fam : False → C := fun a => match a with end.

End NullaryProducts.

Section TerminalBridge.

Context {C D : Category} (F : C ⟶ D) `{@Terminal C} `{@Terminal D}.

Definition nullary_cone (f : False → C) : Cone (DiscreteCat_Functor' f) :=
  discrete_cone (DiscreteCat_Functor' f) terminal_obj (nullary_proj f).

Definition nullary_cone_IsLimitCone (f : False → C) : IsLimitCone (nullary_cone f) :=
  discrete_IsLimitCone_of_IsIndexedProduct _ (nullary_cone f)
    (IsIndexedProduct_nullary f).

Definition nullary_image_cone (f : False → C) :
  Cone (F ◯ DiscreteCat_Functor' f) :=
  discrete_cone (F ◯ DiscreteCat_Functor' f) terminal_obj
    (nullary_proj (fun a => F (f a))).

Definition nullary_image_cone_IsLimitCone (f : False → C) :
  IsLimitCone (nullary_image_cone f) :=
  discrete_IsLimitCone_of_IsIndexedProduct _ (nullary_image_cone f)
    (IsIndexedProduct_nullary (fun a => F (f a))).

(* The comparison F 1 ~> 1: the unique map into the terminal object. / 比较 F 1 ~> 1：到终端对象的唯一映射。 *)
Definition terminal_comparison (f : False → C) :
  F terminal_obj ~{D}~> terminal_obj :=
  cone_comparison F (nullary_cone f) (nullary_image_cone_IsLimitCone f).

Lemma terminal_comparison_one (f : False → C) : terminal_comparison f ≈ one.
Proof. apply one_unique. Qed.

(* Functor/Structure/Terminal.v records [fobj_one_iso : 1 ≅ F 1] with [to : 1 ~> F 1]; the comparison is therefore its [from]. / Functor/Structure/Terminal.v 记录了 [fobj_one_iso : 1 ≅ F 1] 与 [to : 1 ~> F 1] 的比较，因此它是其 [from]。 *)
Theorem terminal_functor_iff_comparison_iso :
  @TerminalFunctor C D F _ _ ↔ IsIsomorphism (terminal_comparison nullary_fam).
Proof.
  split.
  - intros HF.
    unshelve refine {| two_sided_inverse := to (@fobj_one_iso _ _ F _ _ HF) |}.
    + apply one_unique.
    + rewrite terminal_comparison_one.
      rewrite <- (one_unique (from (@fobj_one_iso _ _ F _ _ HF)) one).
      apply iso_to_from.
  - intros Hi.
    unshelve refine {| fobj_one_iso := iso_sym (IsIsoToIso _ Hi) |}.
    intros X; simpl.
    rewrite <- (id_left (fmap[F] one)).
    rewrite <- (is_left_inverse (IsIsomorphism := Hi)).
    rewrite <- comp_assoc.
    apply compose_respects; [reflexivity |].
    apply one_unique.
Qed.

Theorem terminal_functor_iff_preserves_terminal :
  @TerminalFunctor C D F _ _ ↔
  PreservesLimitCone (DiscreteCat_Functor' nullary_fam) F.
Proof.
  split.
  - intros HF.
    exact (PreservesLimitCone_of_comparison_iso F (nullary_cone _)
             (nullary_cone_IsLimitCone _) (nullary_image_cone_IsLimitCone _)
             (fst terminal_functor_iff_comparison_iso HF)).
  - intros P.
    apply (snd terminal_functor_iff_comparison_iso).
    exact (comparison_iso_of_PreservesLimitCone F P
             (nullary_image_cone_IsLimitCone _) (nullary_cone _)
             (nullary_cone_IsLimitCone _)).
Qed.

End TerminalBridge.
