Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.Continuity.
Require Import Category.Theory.Equivalence.Limit.

Generalizable All Variables.

(* * * Limits in a full reflective subcategory / * * 完全反射子范畴中的极限 *)

(*
 Book: Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 Springer GTM 5, §IV.3, Exercise 7, printed p. 92, read from the page
 image:

 “7. If A is a full and reflective subcategory of B, prove that every
 functor S : J -> A with a limit in B has a limit in A.”

 Book: Riehl, “Category Theory in Context”, Dover 2016, §4.6,
 Proposition 4.6.14, printed p. 171, read from the page image:

 “If D <-> C is a reflective subcategory, then:
 (i) The inclusion D <-> C creates all limits.”

 That proposition has a second clause, on colimits in D formed by
 applying the reflector to the colimit in C.  Its exact wording is not
 transcribed here: one of its words matches the case-insensitive pattern
 this repository's [make todo] target scans for, so quoting it in a
 source comment would add a spurious hit.  The clause itself is scoped
 out below; see the paragraph on issue #434.

 Book: Riehl, ibid., §5.6, Corollary 5.6.6, printed p. 211, read from
 the page image:

 “The inclusion of a reflective subcategory creates all limits.  In
 particular, a reflective subcategory of a complete category is
 complete.”

 Its proof there reads, in full: “Proposition 5.3.3 proves that the
 inclusion of a reflective subcategory is monadic.  By Theorem 5.6.5(i),
 it follows that this inclusion creates all limits that exist in the
 codomain.”

 So Mac Lane asks for INHERITANCE (a limit downstairs yields a limit
 upstairs) and Riehl sharpens the same fact to CREATION, which is
 strictly more: creation also pins the lift, identifies its image with
 the given cone, and reflects limit-ness.  Both readings are delivered,
 the second as the record and the first as a one-line consequence of it.

 DELIVERED, by exact name:

 [reflective_CreatesLimit K : CreatesLimit K (Incl C S)]
 -- Riehl 4.6.14(i)/5.6.6 at one shape and one diagram.

 [reflective_CreatesLimitsOfShape J], [reflective_CreatesAllLimits]
 -- the shape-quantified and fully quantified forms.

 [reflective_inherits_limits (L : Limit (Incl C S ◯ K)) : Limit K]
 -- Mac Lane §IV.3 Exercise 7 verbatim: a limit of the diagram read
 in the ambient category yields a limit of the diagram itself.

 [reflective_Complete : @Complete C -> @Complete (Sub C S)]
 -- Riehl's “in particular”.

 [reflective_Incl_PreservesLimitCone K : PreservesLimitCone K (Incl C S)]
 -- the inclusion preserves the limits the subcategory already has,
 with NO completeness hypothesis, because it is a right adjoint.

 Everything is stated in the CONE-LEVEL vocabulary of
 Structure/Limit/Preservation.v ([IsLimitCone], [ConeIso],
 [PreservesLimitCone]); the apex-only [PreservesLimit] is known in this
 library to be insufficient for these purposes (the argument is at
 Construction/Comma/Limit.v, and Preservation.v records
 that only one direction of the bridge holds).

 ** The route, and what is reused rather than re-derived

 Write I := Incl C S and let R be the reflection, so that
 [reflective_adj R : reflector R ⊣ I].

 (1) THE LIFT is [rapl_transposed_cone] (Adjunction/Continuity.v)
 instantiated at this adjunction.  That constant sits inside a
 section whose [Context (L : Limit G)] it never consumes, so -- as
 [About] reports at commit 35511442 -- its discharged type takes NO
 limit argument:

 rapl_transposed_cone : ∀ {C D} {F U}, F ⊣ U →
 ∀ {J} (G : J ⟶ C), Cone (U ◯ G) → Cone G

 Its apex is [F (vertex_obj[N])], here [reflector R vertex_obj[N]],
 and its legs are the inverse transposes of the given legs.  Both
 readbacks hold at [eq_refl] ([reflective_lift_apex],
 [reflective_lift_leg]), so no cone is rebuilt by hand.

 (2) THE COMPARISON ISOMORPHISM [I (reflector R L) ≅ L], for a LIMITING
 cone N with apex L, is the only place with proof content.  Its
 forward leg is the limit mediator [unique_obj (HN (FCone I (lift)))]
 and its backward leg is the unit of the reflection; the [ConeIso]
 leg condition is that mediator's own [unique_property], on the nose
 ([reflective_compare_leg] closes by [exact]).  The two inverse laws
 cost different things, and it is worth naming which is which:

 [reflective_compare_unit] (to ∘ η ≈ id) spends the UNIQUENESS
 clause of the limit N at the competing cone N itself: both
 [to ∘ η] and [id] mediate N through N, so they agree.  The
 computation that [to ∘ η] mediates is one associativity, the leg
 condition, [to_adj_unit] read backwards, and [from_adj_comp_law].

 [reflective_unit_compare] (η ∘ to ≈ id) spends FULLNESS.  This
 is one of exactly two places this file consumes it; the other is
 the reflection lemma of (3), which needs I full as well as
 faithful.  It is the only place it is spent BY HAND -- (3) hands
 it straight to a donor.  Fullness of I is
 [Full_Implies_Full_Functor C S (reflective_full R)]; its
 [prefmap] lifts η ∘ to to an arrow g of the subcategory, and then
 ⌊g⌋ ≈ fmap[I] g ∘ η ≈ η ∘ (to ∘ η) ≈ η ≈ ⌊id⌋ by the previous
 law, so g ≈ id by injectivity of ⌊-⌋ and η ∘ to ≈ fmap[I] id.

 Injectivity of ⌊-⌋ is [reflective_to_adj_inj], four tactic lines
 from [to_adj_comp_law] and [from_adj_respects].  The tree does carry
 this fact already, as [adj_to_inj] (Adjunction/Additive.v), but
 that file is not in this one's dependency closure and requiring it
 would drag the whole Ab-enrichment layer behind every consumer of
 reflective limits; restating it locally costs four tactic lines.

 [reflective_counit_iso] (Construction/Reflective.v) does NOT
 shorten this, and the reason is structural rather than one of
 opacity: that lemma is about an object OF THE SUBCATEGORY, whereas
 L here is an arbitrary object of C, so it does not apply.  (It is
 also closed with [Qed] while producing data, so nothing reduces
 through it; that is a second, independent obstruction, pinned in
 Test/ProbeReflectiveLimit373.v.)

 (3) REFLECTION is [ff_reflect_ump] (Theory/Equivalence/Limit.v,
 with [ff_reflects_limit]) applied to the fullness and
 faithfulness of I, in exactly the packaging
 Theory/Equivalence/Creation.v uses for an equivalence: the leg
 side condition is [fun x => reflexivity _] because [FCone]'s legs
 ARE the image legs ([FCone_leg], Preservation.v).  Faithfulness
 is [Incl_Faithful] (Construction/Subcategory.v), which holds for
 every subcategory whatsoever.

 Nothing in (1)-(3) is a re-derivation: the lift, the reflection lemma,
 the creation class and all its consequences are consumed by name.  What
 is NEW here is the comparison isomorphism of (2) and the assembly.

 ** Prior art, and three claims of issue #373 that are stale

 Measured in this file's worktree, whose base is commit 35511442, by
 the searches named:

 - The issue's donor line numbers have drifted.  [ff_reflects_limit]
 and [equivalence_creates_limits] are both in
 Theory/Equivalence/Limit.v and
 [right_adjoint_preserves_limits] is in Adjunction/Continuity.v,
 none of them where the issue -- or, for the last, an appended note --
 places it.  Every donor cited in this header was re-grepped at that
 commit.

 - The issue's first appended note says the tree has no general
 limit-creation predicate and that a reusable class is the real
 deliverable.  That premise is false: Structure/Limit/Creation.v
 declares [Class CreatesLimit] with the derived
 [creates_limiting], [creates_lift_unique],
 [creates_reflects_limits], [creates_limit_lift],
 [creation_preserves_limit], [CreatesLimitsOfShape],
 [CreatesAllLimits], [creates_limits_Complete],
 [creates_limits_continuous], [CreatesLimit_compose] and the
 strict variant [StrictlyCreatesLimit].  Six files outside the
 declaring one already consume it (rg -l 'CreatesLimit\b' at 35511442
 returns seven: Structure/Limit/Creation itself,
 Structure/Limit/Constant, Structure/Limit/Components,
 Monad/Eilenberg/Moore/Limit, Construction/Comma/Creation,
 Functor/Hom/Limit, Theory/Equivalence/Creation).  This file CONSUMES
 that class and builds no lookalike.  The note's DEMAND -- creation,
 not merely inheritance -- is right, and is what is delivered.

 - The absence claims that do hold: the four reflective and localization
 files (Construction/Reflective.v, 115 lines;
 Construction/Reflective/Idempotent.v, 467;
 Construction/Localization.v, 290;
 Construction/Localization/Universal.v, 203) contain zero occurrences
 of [Limit] or [Complete]; Construction/Subcategory.v contains zero
 occurrences of [Limit], [Cone] or [Complete]; and
 rg -n 'reflective_inherits|inherits_limit|Reflective_Complete|
 reflective_complete' over '*.v' returns nothing.

 ** Riehl's monadic route, measured and not taken

 Riehl reaches 5.6.6 through monadicity, and the tree has most of the
 pieces: Construction/Reflective/Idempotent.v gives
 [Reflective_IdempotentMonad R] for the monad [Incl C S ◯ reflector R],
 Monad/Eilenberg/Moore/Limit.v gives [em_strict_lift] and the strict
 creation for [EM_Forget], Theory/Equivalence/Creation.v transports
 creation across an equivalence, and [CreatesLimit_compose] composes.
 The step that is missing is the join: Idempotent.v's
 [Idempotent_EM_Equivalence] is an equivalence for
 [Sub C MLocal_Subcategory] -- the full subcategory of objects at which
 the unit is invertible -- and NOT for the given S, and no equivalence
 [Sub C S ≃ Sub C MLocal_Subcategory] exists in tree, nor any transport
 of [CreatesLimit] along an equivalence of functors (both searched, zero
 hits).  Building that bridge is a separate piece of work; the direct
 route above needs none of it, so it is the route taken and Riehl's is
 cited rather than followed.  CORRECTION (#370): the join exists now for
 the given S, without [Sub C MLocal_Subcategory]:
 Construction/Reflective/Monadic.v's [Reflective_EM_Equivalence] proves
 Monad/Comparison.v's comparison functor of the reflection itself,
 [Sub C S ⟶ EilenbergMoore], an equivalence.  No [CreatesLimit] is
 transported along it, and this file's route is unchanged.

 ** The colimit half

 Clause (ii) of Proposition 4.6.14 -- colimits in the subcategory,
 obtained by applying the reflector -- is NOT proved here.  It is #434's
 (“MacLane V.5: A full reflective subcategory of a cocomplete category is
 cocomplete”), Construction/Reflective/Colimit.v: [reflective_colimit] and
 [reflective_Cocomplete], from [lapc_is_acolimit]
 (Adjunction/Continuity.v) and Theory/Equivalence/Colimit.v's transport
 along the counit
 isomorphism whiskered into a diagram isomorphism; no creation is claimed.

 ** Strengths, strict first

 At [eq_refl]: the lift's apex and its legs; the comparison's forward
 leg IS the limit mediator and its backward leg IS the unit; the created
 [Limit]'s cone IS the lift and its apex IS the reflector applied to the
 apex downstairs.  Six [eq_refl] Examples in all.

 At [≈] only: the two routes
 to [PreservesLimitCone K I] -- [creation_preserves_limit] applied to
 this creation record, and [right_adjoint_PreservesLimitCone] applied to
 the reflection adjunction -- are NOT convertible, neither as terms nor
 at their produced mediators (both refuted at [eq_refl] and pinned in
 the probe).  They do agree on the mediator up to [≈]
 ([reflective_two_routes_agree]), and the argument is one uniqueness
 appeal, not a computation: the mediators are unique, so any two of them
 coincide.  Read from the two definitions, they are visibly different
 terms of one type -- [creation_preserves_limit]
 (Structure/Limit/Creation.v) transports limit-ness along a
 composite cone isomorphism assembled from [limitcone_iso],
 [FCone_iso] and [ConeIso_sym], while
 [right_adjoint_PreservesLimitCone] (Adjunction/Continuity.v) is
 [rapl_ump] at the cone repackaged as a [Limit].  That is a reading of
 the two sources, not an isolating experiment, and no single step is
 named as THE cause.

 ** Universes

 Measured with [About] under [Set Printing Universes] on all 24
 constants of this file.  Every one is over [C : Category@{u u0 u0}] --
 hom identified with proof -- and that identification sits in the
 BINDER, not in any constraint block: reading the blocks alone would
 report none of it.  It is inherited rather than introduced, and
 [Subcategory] alone already forces it -- [Subcategory@{u u0 u1 u2}]
 takes a [Category@{u u0 u0}] and has an EMPTY constraint block -- which
 the probe pins by rejecting [Subcategory Cu] at a category whose proof
 universe is declared strictly above its hom universe, with that
 category's own hom-set, identity and hom-setoid accepted at those very
 levels.

 The shape-indexed constants additionally bind [J : Category@{u7 u8 u8}]
 and carry, in the block, the equations [u0 = u2], [u0 = u8] and
 [u0 = u10]: C's hom-and-proof level, J's hom-and-proof level, the
 subcategory's [shom] universe and the target hom level of K all
 collapse to one.  The two further equations are [u4 = u11] and
 [u5 = u9], and each relates a level of [Reflective] to a level of
 [Sub] (read off the printed type, where [K] lands in
 [Sub@{u u0 u1 u2 u9 u10 u11} C S]): [u4] is [Reflective]'s second
 universe and [u11] is [Sub]'s seventh, the auxiliary level [Sub]
 declares strictly above C's hom level and which [Incl] carries as its
 sixth -- both are fresh levels, with [u0 < u4] and [u0 < u11] in the
 block; [u5] is [Reflective]'s third universe, one of the two levels
 its record sort [Type@{max(u3,u5)}] is at, and [u9] is the object
 universe of [Sub C S], its fifth and [Incl]'s fifth.  The J-with-C
 collapse is a DIFFERENT axis from the first, it is the cone
 vocabulary's, and it too is inherited: with J's hom level declared
 strictly below C's, [Cone F] is accepted while [cone_leg] and
 [IsLimitCone] are each rejected alone (“Cannot enforce vh = jh”).
 [Functor] is NOT among them: [Ju ⟶ Cu] elaborates at those levels,
 and neither is [vertex_obj].  Nor are those two the only donors:
 [IsALimit], [Limit], [ConeIso] and [FCone] are each rejected alone at
 the same levels with the same message -- measured out of tree, NOT
 pinned, so the two the probe pins are a sample of the family and not
 an enumeration.  These are the same donor family
 Structure/Limit/Initial.v's header records for a RELATED
 collapse -- there the axis is the shape's own hom against its own
 proof, and [IsALimit] is a third donor there as it is here.  All three
 formability rejections and their controls are in the probe.

 No binder and no constraint block of any of the 24 constants contains
 [Set]: measured as zero occurrences of that token anywhere in the
 [About] output for all 24.  None of these identifications is claimed
 unavoidable.

 ** Not delivered

 - STRICT creation.  [StrictlyCreatesLimit] (Creation.v) is built on
 [StrictLift], whose [slift_eq] field demands
 [F (vertex_obj[slift_cone]) = vertex_obj[N]] at LEIBNIZ equality of
 objects of C.  The lift here has apex [I (reflector R L)], which is
 isomorphic to L but not equal to it -- that isomorphism is the whole
 content of (2) -- so the strict record is not reachable by this
 construction and is not attempted.  The probe pins the well-typed
 ascription that would assert it.
 - The colimit half, as above.
 - Any bridge to Idempotent.v's Eilenberg-Moore equivalence, as above.
 - Naturality of the comparison isomorphism in K, or in the cone.
 - Preservation or creation of limits by the REFLECTOR (it is a left
 adjoint; nothing here says anything about it).
 - Uniqueness of the created limit beyond what [creates_lift_unique]
 already gives generically.
 - A non-degenerate witness.  The probe's is at the empty shape (so no
 leg condition is exercised; [IsLimitCone] at shape [0] is
 terminality) and at an object already in the subcategory (the
 terminal group is torsion-free, so the reflection is inert up to
 isomorphism); it shows the assembly runs end to end and reduces,
 nothing more.
 - Nothing is registered as an [Instance].  [CreatesLimit] IS a [Class]
 (Creation.v), so [reflective_CreatesLimit] could be registered;
 it deliberately is not, since it would make instance resolution
 search for a [Reflective] structure on every subcategory it meets.
 [reflective_incl_adj] is likewise a plain [Definition], not an
 instance of [Adjunction]. 

 --------
 书籍：Mac Lane，《为工作中的数学家准备的范畴论》，第2版，Springer GTM 5，§IV.3，练习7，第92页，从页面图像读取：

 “7. 若 A 是 B 的一个满且反射的子范畴，证明每个在 B 中有极限的函子 S : J -> A 在 A 中也有极限。”

 书籍：Riehl，《范畴论在语境中》，Dover 2016，§4.6，命题4.6.14，第171页，从页面图像读取：

 “如果 D <-> C 是一个反射子范畴，则：
 (i) 包含函子 D <-> C 构造所有极限。”该命题有一个第二条款，关于在 D 中的余极限，是通过将反射器应用于 C 中的余极限形成的。其确切措辞未在此处转录：其中的一个词与本仓库的 [make todo] 目标扫描的大小写不敏感模式匹配，因此在源码注释中引用它会产生伪命中。该条款本身在下方被标出范围；参见第 #434 号问题的段落。

 书籍：Riehl，同上，第§5.6节，推论5.6.6，第211页印刷版，从页面图像阅读：

 “反射子范畴的包含产生所有极限。特别地，一个完备范畴的反射子范畴是完备的。”它的证明全文如下：“命题 5.3.3 证明了反射子范畴的包含是单范畴的。根据定理 5.6.5(i)，由此可得，该包含产生了在其余域中存在的所有极限。”

 因此 Mac Lane 所说的是继承（下面的极限产生上面的极限），而 Riehl 将相同的事实精确化为产生，这严格来说更强：产生还确定了提升，识别其像与给定的锥形，并反映极限性。两种解读都有给出，第二种作为记录，第一种作为一句话的推论。

 确切名称给出如下：

 [reflective_CreatesLimit K : CreatesLimit K (Incl C S)]  
 -- Riehl 4.6.14(i)/5.6.6 在一种形状和一张图中。

 [reflective_CreatesLimitsOfShape J] ， [reflective_CreatesAllLimits]  
 -- 形状量化形式和完全量化形式。[reflective_inherits_limits (L : Limit (Incl C S ◯ K)) : Limit K] 
 -- Mac Lane §IV.3 练习 7 原文: 在环境范畴中读出的图的极限产生该图本身的极限。

 [reflective_Complete : @Complete C -> @Complete (Sub C S)] 
 -- Riehl 的“特别是”。

 [reflective_Incl_PreservesLimitCone K : PreservesLimitCone K (Incl C S)] 
 -- 包含保持子范畴已经具有的极限，无需完全性假设，因为它是右伴随。

 所有内容都是用 Structure/Limit/Preservation.v 的 CONE-LEVEL 词汇表述的 ([IsLimitCone], [ConeIso], [PreservesLimitCone]); 仅顶点的 [PreservesLimit] 在这个库中已知不足以用于这些目的（该论证在 Construction/Comma/Limit.v 中，Preservation.v 记录了桥只能保持一个方向）。

 ** 路径，以及重用而不是重新推导的内容写 I := Incl C S 并设 R 为反射，使得
 [reflective_adj R : reflector R ⊣ I] 。

 (1) 提升是 [rapl_transposed_cone]（Adjunction/Continuity.v）
 在该伴随下实例化。该常量位于一个 
 [Context (L : Limit G)] 永远不使用的截面内，因此——正如 
 [About] 在提交 35511442 中报告的——其释放的类型不接受任何极限参数：

 rapl_transposed_cone : ∀ {C D} {F U}, F ⊣ U →
 ∀ {J} (G : J ⟶ C), Cone (U ◯ G) → Cone G

 它的顶点是 [F (vertex_obj[N] )]，这里 [reflector R vertex_obj[N] ]，
 其腿是所给腿的逆转置。两个回读在 [eq_refl]（[reflective_lift_apex]，
 [reflective_lift_leg]）处成立，因此不会手动重建锥体。(2) 比较同构 [I (reflector R L) ≅ L]，对于一个顶点为 L 的极限锥 N，是唯一包含证明内容的地方。它的前向腿是极限中介 [unique_obj (HN (FCone I (lift)))]，后向腿是反射的单位；[ConeIso] 腿条件是中介自身的 [unique_property]，恰好（[reflective_compare_leg] 由 [exact] 封闭）。两个逆律花费不同的东西，值得指出哪一个是哪一个：

 [reflective_compare_unit]（到 ∘ η ≈ id）使用了竞争锥 N 本身在极限 N 的唯一性条款：[to ∘ η] 和 [id] 都通过 N 调解 N，因此它们一致。[to ∘ η] 所调解的计算是一个结合律、腿条件 [to_adj_unit] 倒读，以及 [from_adj_comp_law]。[reflective_unit_compare]（η ∘ to ≈ id）消耗 FULLNESS。这是该文件消耗它的两个地方之一；另一个是(3)的反射引理，它需要 I 既 full 又 faithful。这是唯一一个手动消耗的地方——(3) 直接将其交给一个捐赠者。I 的 fullness 是 [Full_Implies_Full_Functor C S (reflective_full R)]；它的 [prefmap] 将 η ∘ to 提升为子范畴的箭头 g，然后 ⌊g⌋ ≈ fmap [I] g ∘ η ≈ η ∘ (to ∘ η) ≈ η ≈ ⌊id⌋ 根据之前的定律，所以由 ⌊-⌋ 的单射性和 η ∘ to ≈ fmap [I] id 可得 g ≈ id。⌊-⌋ 的单射性是 [reflective_to_adj_inj]，需要四行战术代码从 [to_adj_comp_law] 和 [from_adj_respects]。这个事实树已经包含了这个事实，见 [adj_to_inj] (Adjunction/Additive.v)，但那个文件不在这个文件的依赖闭包中，引用它会将整个 Ab-强化层拖入每个反射极限的使用者中；在本地重新表述它只需要四行战术代码。[reflective_counit_iso]（Construction/Reflective.v）不会缩短这个，原因是结构性的，而不是不透明性的问题：该引理是关于子类别的一个对象，而这里的 L 是 C 的一个任意对象，所以它不适用。（它在产生数据的同时也被 [Qed] 关闭，因此没有任何通过它简化；这是第二个独立的阻碍，在 Test/ProbeReflectiveLimit373.v 中被固定。）(3) 反射是 [ff_reflect_ump]（Theory/Equivalence/Limit.v，配合 [ff_reflects_limit]）应用于 I 的充足性和忠实性，正好使用 Theory/Equivalence/Creation.v 中等价所用的打包方式：支腿侧条件是 [fun x => reflexivity _]，因为 [FCone] 的腿就是像腿（[FCone_leg]，Preservation.v）。忠实性是 [Incl_Faithful]（Construction/Subcategory.v），适用于任何子范畴。

 (1)-(3) 中没有任何内容是重新推导：提升、反射引理、创建类及其所有后果都是按名称使用的。这里的新内容是 (2) 的比较同构和组装。

 ** 先前工作，以及问题 #373 的三个陈旧声明

 在基于提交 35511442 的此文件工作区中，通过被命名的搜索测量：- 问题的捐赠者行号已经偏移。[ff_reflects_limit] 和 [equivalence_creates_limits] 都在 Theory/Equivalence/Limit.v 中，而 [right_adjoint_preserves_limits] 在 Adjunction/Continuity.v 中，它们都不在问题所在的位置——或者对于最后一个，是附加注释的位置。此头文件中引用的每个捐赠者在那个提交时都重新进行了 grep 检查。- 问题的第一个附加注释指出，该树没有通用的限制创建谓词，并且可复用的类才是真正的交付内容。这个前提是错误的：Structure/Limit/Creation.v 声明了 [Class CreatesLimit]，并派生出 [creates_limiting]、[creates_lift_unique]、[creates_reflects_limits]、[creates_limit_lift]、[creation_preserves_limit]、[CreatesLimitsOfShape]、[CreatesAllLimits]、[creates_limits_Complete]、[creates_limits_continuous]、[CreatesLimit_compose] 以及严格变体 [StrictlyCreatesLimit]。在声明该类的文件之外已有六个文件使用了它（在 35511442 上运行 rg -l 'CreatesLimit' 返回七个：Structure/Limit/Creation 本身、Structure/Limit/Constant、Structure/Limit/Components、Monad/Eilenberg/Moore/Limit、Construction/Comma/Creation、Functor/Hom/Limit、Theory/Equivalence/Creation）。该文件使用了该类，并未构建相似物。该说明的要求——创造，而不仅仅是继承——是正确的，并且这正是所提供的。

 - 有效的缺失声明：四个反射和本地化文件（Construction/Reflective.v，115行；
 Construction/Reflective/Idempotent.v，467行；
 Construction/Localization.v，290行；
 Construction/Localization/Universal.v，203行）中没有出现 [Limit] 或 [Complete]；
 Construction/Subcategory.v 中没有出现 [Limit]、[Cone] 或 [Complete]；
 并且在 '*.v' 文件中运行 rg -n 'reflective_inherits|inherits_limit|Reflective_Complete|reflective_complete' 不返回任何结果。

 ** Riehl 的单子路径，经过衡量但未采用Riehl 通过幺半性达到了 5.6.6，并且该树包含大部分部分：Construction/Reflective/Idempotent.v 为幺半 [Incl C S ◯ reflector R] 给出 [Reflective_IdempotentMonad R]，Monad/Eilenberg/Moore/Limit.v 给出 [em_strict_lift] 以及 [EM_Forget] 的严格创建，Theory/Equivalence/Creation.v 可以在等价之间传输创建，ZWZ73WZZ 可以组合。缺少的步骤是连接：Idempotent.v 的 [Idempotent_EM_Equivalence] 是 [Sub C MLocal_Subcategory] ——单元可逆对象的完全子范畴——的等价，而不是给定 S 的等价，并且在树中不存在 [Sub C S ≃ Sub C MLocal_Subcategory] 的等价，也不存在沿函子等价传输 [CreatesLimit]（均搜索过，零结果）。建造那座桥是一项独立的工作；上方的直接路线不需要它，所以采用了这条路线，并引用了Riehl的工作而非遵循它。更正（#370）：对于给定的S，现在存在该连接，不依赖[Sub C MLocal_Subcategory]：
 Construction/Reflective/Monadic.v中的[Reflective_EM_Equivalence]证明了Monad/Comparison.v中反射本身的比较函子[Sub C S ⟶ EilenbergMoore]是等价的。没有[CreatesLimit]沿其传输，并且该文件的路线保持不变。

 ** 余极半部分命题 4.6.14 的条款 (ii) —— 在通过反射子得到的子范畴中的余极限 —— 在此未被证明。这是 #434（“MacLane V.5: 完全反射子范畴在余完备范畴中是余完备的”），Construction/Reflective/Colimit.v: [reflective_colimit] 和 [reflective_Cocomplete]，来自 [lapc_is_acolimit]（Adjunction/Continuity.v）以及 Theory/Equivalence/Colimit.v 中沿余单元同构传输形成的图同构；未声称任何生成。  ** 强度，先为严格 在 [eq_refl]：提升的顶点及其边；比较的前向边是极限中介，其后向边是单位；生成的 [Limit] 的圆锥是提升，其顶点是应用到底层顶点的反射子。总共有六个 [eq_refl] 示例。仅在 [≈]：到 [PreservesLimitCone K I] 的两条路径——[creation_preserves_limit] 应用于此创建记录，和 [right_adjoint_PreservesLimitCone] 应用于反射伴随——不可转换，无论是作为项还是在它们产生的中介上（在 [eq_refl] 上都被反驳并在探针中固定）。它们在中介上在 [≈]（[reflective_two_routes_agree]）之前是一致的，并且这个论点是一个唯一性诉求，而不是计算：中介是唯一的，因此其中任何两个重合。从这两个定义来看，它们显然是同一类型的不同项——[creation_preserves_limit]（Structure/Limit/Creation.v）沿从 [limitcone_iso]、[FCone_iso] 和 [ConeIso_sym] 组合的复合锥同构来传输极限性，而 [right_adjoint_PreservesLimitCone]（Adjunction/Continuity.v）是在锥上重新包装为 [Limit] 的 [rapl_ump]。那是对两个来源的解读，而不是孤立的实验，并且没有任何单一步骤被称为唯一的原因。

 ** 宇宙

 在该文件的所有 24 个常量下，用 [About] 在 [Set Printing Universes] 下进行测量。每一个都超过 [C : Category@{u u0 u0}] —— 使用同态证明确定 —— 并且该确定存在于 BINDER 中，而不在任何约束块中：仅读取这些块将报告不到它的任何内容。它是继承的而非引入的，而单独 [Subcategory] 已经强制执行它 —— [Subcategory@{u u0 u1 u2}] 接受一个 [Category@{u u0 u0}] 并且有一个空的约束块 —— 探针针脚通过在其证明宇宙严格高于其同态宇宙的类别中拒绝 [Subcategory Cu] 来完成，其中该类别的自身同态集、恒等和同态等价类在这些层次被接受。形状索引常数还绑定 [J : Category@{u7 u8 u8}]，并在该块中包含方程 [u0 = u2]、[u0 = u8] 和 [u0 = u10]：C 的同态与证明级别、J 的同态与证明级别、子范畴的 [shom] 宇宙以及 K 的目标同态级别全部合并为一个。另外两个方程是 [u4 = u11] 和 [u5 = u9]，每个方程将 [Reflective] 的一个层级与 [Sub] 的一个层级关联起来（从印刷类型中读取，[K] 位于 [Sub@{u u0 u1 u2 u9 u10 u11} C S] 中）：[u4] 是 [Reflective] 的第二宇宙，[u11] 是 [Sub] 的第七层，辅助层 [Sub] 明确声明在 C 的同类层之上，而 [Incl] 将其作为第六层——两者都是新层级，[u0 < u4] 和 [u0 < u11] 在该块中；[u5] 是 [Reflective] 的第三宇宙，是它的记录类型 [Type@{max(u3,u5)}] 所在的两个层级之一，而 [u9] 是 [Sub C S] 的对象宇宙，它的第五层也是 [Incl] 的第五层。J与C的塌缩是与第一个不同的轴，它属于圆锥词汇的，而且它也是继承的：当J的hom级别被严格声明在C之下时，[Cone F] 被接受，而 [cone_leg] 和 [IsLimitCone] 各自单独被拒绝（“无法强制 vh = jh”）。[Functor] 不在其中：[Ju ⟶ Cu] 在那些级别进行详细说明，[vertex_obj] 也不在其中。这两个也不是唯一的捐赠者：[IsALimit]、[Limit]、[ConeIso] 和 [FCone] 在相同级别以相同的信息被单独拒绝——在树之外测量，而不是固定，因此探针固定的两个是该家族的抽样，而不是枚举。这些是相同的捐赠者家族结构/限制/Initial.v 的头记录，用于相关的折叠——在那里轴是形状自身的 hom 与其自身的证明，而 [IsALimit] 在那里和这里一样是第三个捐赠者。所有三个可形成性拒绝及其控制都在探针中。

 24 个常量中的任何一个都没有包含 [Set] 的粘合剂和约束块：在所有 24 个的 [About] 输出中，该标记的出现次数被测量为零。这些识别中没有一个被声称是不可避免的。

 ** 未交付- 严格创建。[StrictlyCreatesLimit]（Creation.v）建立在 [StrictLift] 上，其 [slift_eq] 字段要求 [F (vertex_obj[slift_cone] ）= 在 C 对象的 LEIBNIZ 等式下的 vertex_obj [N] ]。这里的提升有顶点 [I (reflector R L)]，它与 L 同构但不等于它——这种同构就是（2）的全部内容——因此通过此构造无法到达严格记录，也未尝试。探针固定了将会断言它的良型标注。- 上述余极限部分。- 到 Idempotent.v 的 Eilenberg-Moore 等价的桥，如上所述。- 比较同构在 K 中或在圆锥中具有自然性。- REFLECTOR 对极限的保持或创建（它是左陪伴；此处没有任何内容说明其行为）。- 所创建的极限的唯一性超出了 [creates_lift_unique] 已经通常提供的范围。- 一个非退化的见证。探针位于空形状（因此没有执行任何阶条件； [IsLimitCone] 在形状 [0] 是终端的）并且位于子类别中已存在的对象（终端群是无挠的，所以反射在同构意义下是惰性的）；它展示了组装是从头到尾进行并简化的，仅此而已。- 没有任何内容被注册为 [Instance]。[CreatesLimit] 是一个 [Class]（Creation.v），所以 [reflective_CreatesLimit] 可以被注册；它故意没有被注册，因为这会使实例解析在遇到的每个子类别上寻找 [Reflective] 结构。[reflective_incl_adj] 同样只是一个普通的 [Definition]，而不是 [Adjunction] 的实例。
*)

Section ReflectiveLimits.

Context {C : Category}.
Context {S : Subcategory C}.
Context (R : Reflective S).

Notation I := (Incl C S).

(*
 The reflection adjunction, under a short name.  Deliberately NOT an
 [Instance]: the transpose notations below name it explicitly. 

 --------
 反射伴随作用，用一个简短的名字。 故意不是一个 [Instance]：下面的转置符号明确地给它命名。
*)

Definition reflective_incl_adj : reflector R ⊣ I := reflective_adj R.

Notation "⌊ f ⌋" := (to   (@adj _ _ _ _ reflective_incl_adj _ _) f).
Notation "⌈ f ⌉" := (from (@adj _ _ _ _ reflective_incl_adj _ _) f).

(*
 Fullness of the inclusion, in the [Functor.Full] form the reflection
 lemma consumes.  [Construction.Subcategory.Full] (a property of the
 subcategory) and [Theory.Functor.Full] (a structure on a functor) are
 different notions sharing a short name, and both modules are imported
 here, so the result type is written [Functor.Full] qualified. 

 --------
 包括的充满性，在 [Functor.Full] 形式下，反射引理消耗。[Construction.Subcategory.Full]（子范畴的一个性质）和 [Theory.Functor.Full]（函子上的一个结构）是不同的概念，但共享一个简称，并且这里导入了两个模块，所以结果类型以 [Functor.Full] 限定的形式书写。
*)

Definition reflective_Incl_Full : Functor.Full I :=
  Full_Implies_Full_Functor C S (reflective_full R).

(*
 Injectivity of the forward transpose.  [adj_to_inj]
 (Adjunction/Additive.v) is the same fact, in a module outside this
 file's closure. 

 --------
 前向转置的单射性。[adj_to_inj]（Adjunction/Additive.v）是同一个事实，在此文件闭包之外的一个模中。
*)

Lemma reflective_to_adj_inj {x : C} {y : Sub C S}
  (f g : reflector R x ~{Sub C S}~> y) : ⌊f⌋ ≈ ⌊g⌋ → f ≈ g.
Proof.
  intro Hfg.
  rewrite <- (@to_adj_comp_law _ _ _ _ reflective_incl_adj _ _ f).
  rewrite <- (@to_adj_comp_law _ _ _ _ reflective_incl_adj _ _ g).
  now apply (@from_adj_respects _ _ _ _ reflective_incl_adj).
Qed.

Section Shape.

Context {J : Category}.
Context (K : J ⟶ Sub C S).

(** ** The lift *)

(*
 A cone over the diagram read in C, transposed across the reflection.
 Its apex is the reflector applied to the apex downstairs. 

 --------
 一个锥体位于用 C 读取的图表上，横跨反射进行了转置。它的顶点是施加在楼下顶点的反射器。
*)

Definition reflective_lift (N : Cone (I ◯ K)) : Cone K :=
  rapl_transposed_cone reflective_incl_adj K N.

Example reflective_lift_apex (N : Cone (I ◯ K)) :
  vertex_obj[reflective_lift N] = reflector R vertex_obj[N] := eq_refl.

Example reflective_lift_leg (N : Cone (I ◯ K)) (x : J) :
  cone_leg (reflective_lift N) x = ⌈ cone_leg N x ⌉ := eq_refl.

(** ** The comparison isomorphism / ** 比较同构 *)

Section Compare.

Context (N : Cone (I ◯ K)).
Context (HN : IsLimitCone N).

(*
 The mediator of the image of the lift through the limiting cone N. 

 --------
 通过限制锥 N 提升图像的中介。
*)

Definition reflective_compare :
  I (reflector R vertex_obj[N]) ~{C}~> vertex_obj[N] :=
  unique_obj (HN (FCone I (reflective_lift N))).

Lemma reflective_compare_leg (x : J) :
  cone_leg N x ∘ reflective_compare ≈ fmap[I] ⌈ cone_leg N x ⌉.
Proof.
  exact (unique_property (HN (FCone I (reflective_lift N))) x).
Qed.

(* One inverse law, by the uniqueness clause of the limit N. / 根据极限 N 的唯一性条款，一个逆律。 *)

Lemma reflective_compare_unit :
  reflective_compare
    ∘ @unit _ _ (reflector R) I reflective_incl_adj vertex_obj[N]
    ≈ id[vertex_obj[N]].
Proof.
  pose proof (uniqueness (HN N)) as Hu.
  transitivity (unique_obj (HN N)).
  - symmetry.
    apply Hu.
    intro x.
    rewrite comp_assoc.
    rewrite reflective_compare_leg.
    rewrite <- (@to_adj_unit _ _ _ _ reflective_incl_adj _ _
                  (⌈ cone_leg N x ⌉)).
    apply (@from_adj_comp_law _ _ _ _ reflective_incl_adj).
  - apply Hu.
    intro x.
    apply id_right.
Qed.

(*
 The other inverse law, by fullness.  This is the one place fullness
 is spent BY HAND; the reflection lemma below spends it too, by handing
 it to [ff_reflect_ump]. 

 --------
 另一个逆律，通过充实。这是充实被手动使用的唯一地方；下面的反射引理也会使用它，通过将其交给[ff_reflect_ump]。
*)

Lemma reflective_unit_compare :
  @unit _ _ (reflector R) I reflective_incl_adj vertex_obj[N]
    ∘ reflective_compare
    ≈ id[I (reflector R vertex_obj[N])].
Proof.
  pose (g := @prefmap _ _ I reflective_Incl_Full
               (reflector R vertex_obj[N]) (reflector R vertex_obj[N])
               (@unit _ _ (reflector R) I reflective_incl_adj
                  vertex_obj[N] ∘ reflective_compare)).
  assert (Hg : fmap[I] g
                 ≈ @unit _ _ (reflector R) I reflective_incl_adj
                     vertex_obj[N] ∘ reflective_compare)
    by exact (@fmap_sur _ _ I reflective_Incl_Full _ _ _).
  assert (Hid : g ≈ id).
  { apply reflective_to_adj_inj.
    rewrite (@to_adj_unit _ _ _ _ reflective_incl_adj _ _ g).
    rewrite Hg.
    rewrite <- comp_assoc.
    rewrite reflective_compare_unit.
    rewrite id_right.
    symmetry.
    rewrite (@to_adj_unit _ _ _ _ reflective_incl_adj _ _ id).
    rewrite fmap_id.
    now rewrite id_left. }
  rewrite <- Hg, Hid.
  apply fmap_id.
Qed.

Definition reflective_cone_iso :
  ConeIso (FCone I (reflective_lift N)) N :=
  ({| to          := reflective_compare
    ; from        := @unit _ _ (reflector R) I reflective_incl_adj
                       vertex_obj[N]
    ; iso_to_from := reflective_compare_unit
    ; iso_from_to := reflective_unit_compare |}
   ; reflective_compare_leg).

Example reflective_cone_iso_to :
  to `1 reflective_cone_iso = reflective_compare := eq_refl.

Example reflective_cone_iso_from :
  from `1 reflective_cone_iso
    = @unit _ _ (reflector R) I reflective_incl_adj vertex_obj[N]
  := eq_refl.

End Compare.

(** ** Reflection / ** 反思 *)

(*
 Full and faithful functors reflect limiting cones.  The packaging is
 the one at Theory/Equivalence/Creation.v.  (That file's own comment
 cites [ff_reflect_ump] at a line of Theory/Equivalence/Limit.v that no
 longer holds it; a defect in an untouched file, recorded here
 and not edited.)

 CORRECTION (#481): the body wrote out [@ff_reflect_ump (Sub C S) C I
 reflective_Incl_Full (Incl_Faithful C S) J K M (limitcone_isalimit H)
 (fun x => reflexivity _)], which is Theory/Equivalence/Limit.v's
 [ff_ReflectsLimitCone] at the inclusion's fullness and faithfulness:
 the two read back as one at [eq_refl] (measured).  The body now calls
 that constant, eta-expanded, and the [About] blocks of this file's 24
 constants are unchanged (compared by script against the earlier
 body). 

 --------
 完全且忠实的函子会反映极限锥。打包形式是 Theory/Equivalence/Creation.v 中的那个。（该文件自身的注释引用了 Theory/Equivalence/Limit.v 中的一行 [ff_reflect_ump]，但该行已不再包含它；这是一个未修改文件中的缺陷，这里记录下来但未编辑。）

 更正 (#481)：正文展开写出了 [@ff_reflect_ump (Sub C S) C I reflective_Incl_Full (Incl_Faithful C S) J K M (limitcone_isalimit H) (fun x => reflexivity _)]，这是 Theory/Equivalence/Limit.v 中 [ff_ReflectsLimitCone] 在包含的完全性和忠实性处的内容：两者读回时在 [eq_refl] 处合并为一个（已测量）。正文现在调用该常量，进行了 eta 展开，并且该文件 24 个常量中的 [About] 块保持不变（通过脚本与之前的正文比较）。
*)

Definition reflective_ReflectsLimitCone : ReflectsLimitCone K I :=
  fun M H =>
    @ff_ReflectsLimitCone (Sub C S) C I reflective_Incl_Full
      (Incl_Faithful C S) J K M H.

(*
   * ** Riehl 4.6.14(i) / 5.6.6, at one diagram 

   --------
   * ** Riehl 4.6.14(i) / 5.6.6，在同一个图表中
*)

(*
 Note that the lift ignores the limiting hypothesis: it is defined for
 every cone downstairs. 

 --------
 注意，提升忽略了限制性假设：它对于楼下的每一个锥体都有定义。
*)

Definition reflective_CreatesLimit : CreatesLimit K I :=
  {| creates_lift      := fun N _ => reflective_lift N
   ; creates_lift_over := fun N HN => reflective_cone_iso N HN
   ; creates_reflect   := reflective_ReflectsLimitCone |}.

(** ** Mac Lane §IV.3 Exercise 7 / ** 马克·莱恩 §IV.3 练习 7 *)

Definition reflective_inherits_limits (L : Limit (Incl C S ◯ K)) : Limit K :=
  creates_limit_lift reflective_CreatesLimit L.

Example reflective_inherits_limits_cone (L : Limit (Incl C S ◯ K)) :
  @limit_cone _ _ _ (reflective_inherits_limits L)
    = reflective_lift (@limit_cone _ _ _ L) := eq_refl.

Example reflective_inherits_limits_apex (L : Limit (Incl C S ◯ K)) :
  vertex_obj[@limit_cone _ _ _ (reflective_inherits_limits L)]
    = reflector R vertex_obj[@limit_cone _ _ _ L] := eq_refl.

(*
   * ** The inclusion preserves limits, with no completeness hypothesis 

   --------
   * ** 包含保留了限制，没有完整性假设
*)

Definition reflective_Incl_PreservesLimitCone : PreservesLimitCone K I :=
  right_adjoint_PreservesLimitCone reflective_incl_adj K.

(*
 The creation route and the right-adjoint route to the same statement
 agree on mediators up to [≈], by uniqueness of the mediator, and are
 not convertible (pinned in the probe). 

 --------
 相同语句的创建路线和右伴随路线在调解器上达成一致，直到 [≈]，由于调解器的唯一性，并且不可转换（固定在探针中）。
*)

Lemma reflective_two_routes_agree (L : Limit (I ◯ K))
  (M : Cone K) (HM : IsLimitCone M) (P : Cone (I ◯ K)) :
  unique_obj (creation_preserves_limit reflective_CreatesLimit L M HM P)
    ≈ unique_obj (reflective_Incl_PreservesLimitCone M HM P).
Proof using All.
  apply (uniqueness
           (creation_preserves_limit reflective_CreatesLimit L M HM P)).
  exact (unique_property (reflective_Incl_PreservesLimitCone M HM P)).
Qed.

End Shape.

(* * ** The quantified forms, and Riehl's “in particular” / * ** 定量形式，以及赖尔特别提到的部分 *)

Definition reflective_CreatesLimitsOfShape (J : Category) :
  CreatesLimitsOfShape J I := fun K => reflective_CreatesLimit K.

Definition reflective_CreatesAllLimits : CreatesAllLimits I :=
  fun J K => reflective_CreatesLimit K.

Definition reflective_Complete (HC : @Complete C) : @Complete (Sub C S) :=
  creates_limits_Complete I HC reflective_CreatesAllLimits.

Definition reflective_Incl_continuous (HC : @Complete C) :
  ∀ (J : Category) (K : J ⟶ Sub C S), PreservesLimitCone K I :=
  creates_limits_continuous I HC reflective_CreatesAllLimits.

End ReflectiveLimits.
