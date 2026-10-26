(* * * Limits and colimits of a constant diagram / * * 常量图的极限与余极限 *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Fun.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Cone.Const.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Structure.Limit.Components.
Require Import Category.Structure.Groupoid.Connected.
Require Import Category.Theory.Connected.Components.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Instance.Zero.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Instance.Coq.
Require Import Category.Structure.Limit.Absolute.

(*
 NOTATION GUARD, and it is REQUIRED here rather than defensive.  Three
 scopes declare [_ ^op] -- category, functor and adjunction -- and
 Category.Functor.Opposite opens [functor_scope], so after the Require
 block above a BINDER [{x y : J^op}] parses [J] as a functor and fails
 with “The term J has type Category while it is expected to have type
 ?C ⟶ ?D”, naming neither culprit.  Measured: deleting the line below
 breaks this file at its first opposite-category binder.  Contrast
 Theory/Universal/Arrow/Dual.v, whose own guard is DEFENSIVE because
 every [C^op] there sits in an argument or ascription position, which
 [Bind Scope category_scope with Category] already rescues. 

 --------
 NOTATION GUARD，并且在这里是必需的，而不是防御性的。三个作用域声明 [_ ^op] —— 类别、函子和伴随 —— 并且 Category.Functor.Opposite 打开了 [functor_scope]，因此在上面的 Require 块之后，一个 BINDER [{x y : J^op}] 将 [J] 解析为函子并失败，提示“术语 J 的类型为 Category，而预期类型为 ?C ⟶ ?D”，未指明任何罪魁祸首。测量：删除下面的这一行会在第一个对偶类别绑定器处使此文件出错。对比 Theory/Universal/Arrow/Dual.v，其自身的守护是防御性的，因为那里的每个 [C^op] 都出现在参数或类型标注的位置，而 [Bind Scope category_scope with Category] 已经救援了。
*)
Open Scope category_scope.

Generalizable All Variables.

(*
 Book:      Mac Lane, “Categories for the Working Mathematician”,
 2nd ed., §IV.2 Exercise 8, printed p. 90 (maclane:IV.2:ex8)
 nLab:      https://ncatlab.org/nlab/show/connected+category
 nLab:      https://ncatlab.org/nlab/show/constant+functor
 nLab:      https://ncatlab.org/nlab/show/diagonal+functor
 nLab:      https://ncatlab.org/nlab/show/limit
 nLab:      https://ncatlab.org/nlab/show/absolute+colimit

 Mac Lane's exercise says that if J is connected then the limit of the
 constant diagram Δ[J](c) is c itself, and dually for the colimit; so
 over a connected shape the diagonal functor is fully faithful and the
 unit of Δ ⊣ lim is an isomorphism at every object.  The four
 deliverables are

 (a) [const_IsALimit] / [const_IsAColimit] (with the cone-level
 [const_IsLimitCone] / [const_IsColimitCocone] and the bundled
 [const_Limit] / [const_Colimit]): the identity cone on c is a
 limiting cone over Δ[J](c), and the identity cocone is a
 colimiting cocone;

 (b) [const_unit_iso] / [const_counit_iso]: the unit of
 Δ[J] ⊣ [LimitFunctor] is invertible at every object, and dually
 the counit of [ColimitFunctor] ⊣ Δ[J] -- with
 [const_unit_is_med] recording that the unit IS the mediating
 map rather than merely equalling it;

 (c) [Diagonal_Full] and [Diagonal_Faithful]: the diagonal functor
 is full over a connected shape and faithful over an inhabited
 one -- the SPLIT is the point, and §4 below proves both halves
 sharp;

 (d) [const_AbsoluteLimit] / [const_AbsoluteColimit]: these limits
 are ABSOLUTE, preserved by EVERY functor out of C.

 1. A PRIOR-ART CORRECTION, ON TWO COUNTS, BOTH MEASURED.  The catalog
 issue's “Current state” section is FALSE twice over.

 FIRST, it states that no connectedness predicate exists in the
 tree and asks for the zig-zag relation to be built from scratch.
 Structure/Groupoid/Connected.v has declared [Inductive ZigZag
 {C : Category}] and [Definition Connected (C : Category)]
 for an ARBITRARY category since it was written, together
 with [zigzag_trans], [zigzag_sym], [hom_zigzag] and
 [Two_Discrete_not_connected]; Theory/Connected/Components.v
 adds [ConnectedNonempty], [Zero_Connected],
 [Zero_not_ConnectedNonempty] and [connected_readings_differ].
 All of them are CONSUMED here.  Nothing in this file
 redeclares a zig-zag, a connectedness predicate, or any of their
 closure properties, and [leg_zigzag] below is an induction OVER the
 donor's inductive type, not a second copy of it.

 SECOND, it states that there is no Δ ⊣ lim adjunction to take the
 unit of.  Adjunction/Diagonal/Limit.v supplies
 [Diagonal_Limit_Adjunction : Δ[J] ⊣ LimitFunctor] and
 [Colimit_Diagonal_Adjunction : ColimitFunctor ⊣ Δ[J]],
 together with [HasLimitsOfShape], [LimitFunctor],
 [lim_obj], [lim_leg], [lim_med], [lim_transpose_to] and the whole
 covariant colimit mirror.  Part (b) below is stated against those
 constants and builds no adjunction of its own.

 What IS absent, and is what this file supplies, was confirmed by a
 SHAPE sweep rather than a name sweep: no statement anywhere in the
 tree computes the limit or colimit of a CONSTANT diagram.  The two
 near-hits a name search returns are about a constant WEIGHT, not a
 constant diagram -- Structure/Limit/Weighted.v's [conical_weighted]
 has weight Δ[J](terminal_obj) with the DIAGRAM arbitrary, which is
 a different statement -- and Instance/One/Diagonal.v's
 [Diagonal_Unique] is a FACTORISATION (Δ[J](d) ≈ Δ(d) ◯ one)
 carrying no connectedness hypothesis and computing no limit.
 Separately, [Full (@Diagonal ...)], [Faithful (@Diagonal ...)],
 [AbsoluteLimit], [AbsoluteColimit] and the string “absolute limit”
 each had ZERO occurrences tree-wide.  (d) is genuinely new
 VOCABULARY -- [AbsoluteLimit] and [AbsoluteColimit] are introduced
 here.  (c) is not: [Full] and [Faithful] are pre-existing
 (Theory/Functor.v), so what the zero-occurrence
 measurement shows there is a new INSTANTIATION at [Diagonal], not
 a new notion.  Prior art on absoluteness is prose in TWO files,
 not one: Structure/Coequalizer/Split.v and
 Construction/Karoubi.v (“Splitting an idempotent is an
 absolute colimit”).

 READ (d)'s NOVELTY NARROWLY, THOUGH: the CONCEPT is prior art.
 Structure/Coequalizer/Split.v is headed “Split coequalizers are
 absolute”, cites Paré 1971 and the nLab in prose, and proves
 [functor_preserves_split] together with
 [split_coequalizer_preserved].  What it does NOT do is declare a
 predicate -- its absoluteness is a property of one construction,
 stated by transporting its equational data through [fmap] -- so
 there was nothing to instantiate here and nothing here subsumes it.
 The two are related only by the shared word; §“WHAT IS NOT
 DELIVERED” records that no bridge is built.

 2. INHABITEDNESS IS LOAD-BEARING, AND THAT IS PROVED RATHER THAN
 ARGUED.  The in-tree [Connected] is the bare “any two objects are
 joined” clause with NO inhabitedness, and [Zero_Connected] shows
 the empty category satisfies it vacuously.  Over the empty shape a
 cone is a BARE APEX -- no legs, no coherence -- so the universal
 property collapses to terminality, which
 [zero_const_limit_IsTerminalObj] and [IsTerminalObj_zero_const_limit]
 prove in both directions.  Consequently
 [const_limit_not_from_bare_connected] refutes the bare-[Connected]
 reading outright: at J := [_0] and C := [_2] the object [TwoX] is
 not terminal ([TwoX_not_terminal], through [Instance/Two.v]'s own
 [TwoHom_Y_X_absurd]), so the conclusion is FALSE there while the
 hypothesis holds.

 The hypothesis is therefore [ConnectedNonempty J], and it goes in
 the statement.  #352 already separates the two readings at the
 empty shape; what is new here is that the separation BITES for
 constant limits.  A reader who wants the bare-[Connected] form
 should read [zero_const_limit_IsTerminalObj] as the missing case.

 3. WHERE EACH HYPOTHESIS IS SPENT.  [cn_obj K] and [cn_zigzag K] are
 spent at DIFFERENT points and neither substitutes for the other:
 [cn_obj K] NAMES the mediator ([limit_med (const_IsALimit K) N =
 cone_leg N (cn_obj K)], on the nose), while [cn_zigzag K] proves
 that this choice satisfies the triangle at EVERY other object.
 That is the precise sense in which connectedness alone does not
 suffice and a point alone does not either -- and both halves are
 refuted, in §4.

 The zig-zag content is factored out of the cone vocabulary
 entirely: [leg_zigzag] takes a BARE family [leg : ∀ x : J, n ~> c]
 that is constant along single arrows and concludes it is constant
 along zig-zags.  Its three cases are [zz_nil] (reflexivity alone),
 [zz_fwd] (the hypothesis at [f], then the induction hypothesis) and
 [zz_bwd] (THE SAME hypothesis at SWAPPED arguments, rewritten
 backwards) -- so the two non-trivial constructors consume one and
 the same input and there is no asymmetry to manage.  It serves the
 cone side, the cocone side, the two absolute statements and
 [Diagonal_Full], five consumers in all.

 THE COLIMIT HALF NEEDS NO [Connected (J^op)], WHICH IS FORTUNATE
 SINCE THE TREE CARRIES NO TRANSPORT OF CONNECTEDNESS TO THE
 OPPOSITE (measured: no [zigzag_op] and no [Connected_op] anywhere).
 [Connected] is declared for an ARBITRARY category, so
 [Connected (J^op)] is perfectly statable and would follow from a
 three-case induction swapping [zz_fwd] and [zz_bwd]; what is
 absent is that transport, not the statement.  [obj[J^op]] IS [obj[J]], so
 [leg_zigzag] is instantiated at the shape [J] with AMBIENT [C^op];
 the explicit [@leg_zigzag J (C^op) ...] is required, since left to
 inference the index type of [cone_leg N] makes Coq pick [J^op] and
 then the step hypothesis demands [J^op] arrows.

 4. THE TWO HALVES OF (c) ARE SEPARATED BY COMPILED COUNTEREXAMPLES.
 [Diagonal_Faithful] takes only an OBJECT of J; [Diagonal_Full]
 takes the whole of [ConnectedNonempty].  Sharpness is PARTIAL and
 the gap is named: what is refuted is the POINT for faithfulness
 and the CONNECTEDNESS half for fullness.  Nothing refutes fullness
 over a point-less shape, so the point half of [ConnectedNonempty]
 is NOT shown necessary for [Diagonal_Full].  The two
 refutations: [Diagonal_Zero_not_Faithful] refutes
 faithfulness over the
 empty shape (where [_0, Coq] has singleton hom-sets, so [id] and
 [negb] collapse), and [Diagonal_Two_Discrete_not_Full] refutes
 fullness over the inhabited but DISCONNECTED [Two_Discrete] --
 the transformation [td_split], which is [id] at one object and
 [negb] at the other, is natural there and is the image of no
 morphism.  That refutation fires against [Full]'s [prefmap] and
 [fmap_sur] directly, and [Full] demands no functoriality of
 [prefmap], so it refutes the WEAKEST reading of fullness.

 [Diagonal_Full] is delivered twice -- directly, and
 [Diagonal_Full_via_limit] through part (a)'s mediator -- and the
 two pick THE SAME preimage, recorded at [eq_refl] by
 [Diagonal_Full_routes_agree].  So the limit route is not a detour
 to a different chosen section; it is the direct one.  The two
 [Full] RECORDS are not compared, their [fmap_sur] proofs being
 distinct opaque terms.

 5. WHAT THE [Two_Discrete] REFUTATION DOES AND DOES NOT SAY.
 [two_discrete_const_not_limit] refutes that [bool], WITH ANY LEG
 FAMILY WHATSOEVER, is a limit of the constant [bool]-diagram of
 two-object discrete shape in [Coq] -- the quantification over legs
 sits inside [IsALimit], so this is the strong form.  It does NOT
 say the limit fails to exist: [td_const_IsALimit_product] builds
 it, and it is c × c.  Nor does it hold at every object:
 [td_const_IsALimit_at_unit] shows the disconnected conclusion is
 still TRUE at a terminal c, so the witness must be an object with
 c ≇ c × c, and no THIN ambient can host one (in a thin category
 c × c ≅ c always).  That is why the witness is [Coq] and the
 refutation is a pigeonhole: surjectivity of ⟨φX, φY⟩ onto
 bool × bool from bool.

 6. STRENGTHS, MEASURED STRICT-FIRST.  Every readback below names its
 subject.  Holding at [eq_refl]: [const_fobj] and [const_fmap] (the
 constant diagram's arrow action IS [id[c]], which is why every
 coherence obligation in this file closes by [id_left] rather than
 by a chase); [const_apex_strict], [const_cone_leg_strict],
 [const_leg_strict] and [const_med_strict] (the mediator IS the
 competing cone's leg at [cn_obj K]); the three colimit mirrors
 [const_cocone_inj_strict], [const_coinj_strict],
 [const_comed_strict]; [const_unit_is_transpose] and
 [const_unit_is_med] (the unit of Δ ⊣ lim IS the mediating map, not
 merely ≈ it) with [const_counit_is_transpose] dually;
 [const_two_cones_same_legs]; [const_absolute_leg_strict] and
 [const_absolute_coinj_strict]; [const_image_fobj];
 [Diagonal_Full_routes_agree]; and the non-vacuity pair
 [two_const_leg_strict], [two_const_med_strict].

 SETTLING FOR ≈, with the cause diagnosed rather than guessed --
 TWO of them, [const_unit_is_limit_unique_to] and
 [const_image_fmap_equiv].  The first:  Its strict form is
 REFUTED and pinned, and [const_two_cones_same_legs] is the
 DIAGNOSING control -- the two competing cones have the same legs
 at [eq_refl] and differ only in their [cone_coherence] proof
 terms, and [ump_limits] of an abstract [HasLimitsOfShape] reduces
 on nothing, so no conversion is available.  Also at ≈:
 [const_image_fmap_equiv], whose strict form is likewise refuted --
 [fmap[F ◯ Δ[J](c)] f] is [fmap[F] id[c]] where [fmap[Δ[J](F c)] f]
 is [id[F c]], and only [fmap_id] relates them.

 7. NEGATIVES: FIVE, OF TWO KINDS, KEPT LEXICALLY APART -- three
 CONVERSION in the body and two FORMABILITY in the closing
 [UniverseProbe] section -- each stripped once and its failure read
 off the WHOLE error message rather than the tail.

 CONVERSION.  [op_diag_strict] records that [Δ[J](c)^op] is NOT
 [Δ[J^op](c)], with [op_diag_fobj] and [op_diag_fmap] as controls
 showing BOTH DATA fields agree at [eq_refl], so the difference is
 confined to the three rebuilt law fields.  That is not a curiosity:
 [ACone n G] is not convertible for non-convertible [G], so the
 colimit half CANNOT be obtained by instantiating the limit half at
 [C^op] and [J^op], and it is built directly instead.
 [const_image_fmap] and [const_unit_is_limit_unique_to_strict] are
 the other two, both discussed in §6.

 FORMABILITY.  With the shape's hom universe declared strictly below
 both its own proof universe and the ambient's hom universe,
 [Diagonal] and [IsALimit] are each rejected ALONE and on DIFFERENT
 equations -- “Cannot enforce jh = ch” and “Cannot enforce jp = jh”
 respectively -- against four controls accepted at those very levels
 ([obj], a hom type, [ACone] and [Cone]).  So §8's “two independent
 donors” is guarded, not merely measured.

 Every constant named inside a [Fail] is also named by a succeeding
 command, so a rename breaks this file loudly rather than turning a
 guard vacuously green: [Opposite_Functor], [Diagonal], [fobj] and
 [fmap] by the two [op_diag_*] controls; [Diagonal] and [◯] again by
 [const_image_fobj] and [const_image_fmap_equiv]; and [const_unit],
 [limit_unique_to], [const_IsALimit] and [lim_alimit] by
 [const_unit_is_transpose] and [const_unit_is_limit_unique_to].

 8. UNIVERSES, READ OFF BOTH THE BINDER AND THE CONSTRAINT BLOCK.
 [const_IsALimit@{u u0 u1 u2 u3 u4 u5}] is over
 [J : Category@{u u0 u0}] and [C : Category@{u1 u2 u2}] with the
 single equation [u0 = u2] in its block -- the SHAPE's hom-and-proof
 universe identified with the AMBIENT's -- while BOTH OBJECT
 UNIVERSES STAY FREE, bounded and never identified, and no [Set]
 appears anywhere in the general results.  Note that hom = proof in
 each category is expressed by REUSING one level in the BINDER with
 nothing in the block saying so, which is the reading trap this tree
 records repeatedly.

 [AbsoluteLimit] IS THIS FILE'S SHARPEST INSTANCE OF THAT TRAP: its
 constraint block contains NO equation at all, while its binder reads
 [J : Category@{u1 u5 u5}] and [C : Category@{u3 u5 u5}] -- one level
 reused for four slots.  A reader who checks only the block reports
 “no identification” and is wrong.

 EVERY CROSS-CATEGORY IDENTIFICATION IS INHERITED -- read that
 precisely, because ONE identification IS added here and an earlier
 revision of this paragraph denied it (see the end of this item).
 The inherited ones are measured at the DONORS' OWN SIGNATURES
 rather than inferred:
 [IsALimit@{u u0 u1 u2}] is itself declared over
 [J : Category@{u0 u1 u1}] and [C : Category@{u2 u1 u1}], and
 [Diagonal@{u u0 u1 u2 u3 u4}] over [C : Category@{u3 u4 u4}] and
 [J : Category@{u2 u4 u4}], both carrying the identification in the
 binder with no equation in the block; [ACone@{u0 u1 u2 u3 u4 u5}]
 keeps all six levels apart and is innocent.  §7's two formability
 negatives guard exactly this.  [leg_zigzag@{u u0 u1 u2}], the
 reusable core, has a LITERALLY EMPTY constraint BLOCK -- but its
 BINDER reads [C : Category@{u u2 u2}], and THAT identification is
 NOT inherited: it is this file's own minimization artifact from
 the unannotated [Context {J C : Category}], demonstrated by an
 isolating experiment -- the identical statement and proof compile
 inside a section declaring [Constraint ch < cp] over
 [Cu : Category@{co ch cp}], with a hom type accepted at those
 levels as the control.  The J-side IS inherited ([ZigZag@{u u0}]
 is declared over [Category@{u u0 u0}]).  So reading the empty
 block alone gets it wrong here, exactly as this item warns two
 paragraphs above; explicit binders would lift it and none of it
 is claimed unavoidable.

 9. AXIOMS AND COUNTS.  89/89 constants closed under the global
 context, counted by [Print Module] on the compiled module so the two
 [Program] obligations of [td_split] are included; the file declares
 no [Record], [Class] or [Inductive], so there is no unlisted
 [Build_*] constructor, and the three [Fail]ed names declare nothing.
 Read the GRADE: that is a ONE-TIME measurement of all 89, not a
 standing gate.  CORRECTION (#477): 91 by the same count since #477
 added [AbsoluteLimitCone_apex] and [AbsoluteColimitCocone_apex] to
 part (d), both closed under the global context and gated fully
 qualified in #477's block of the print-assumptions target; for
 them this file requires Structure/Limit/Absolute.v.

 10. TWO ENGINEERING FINDINGS, both recorded where they bite.  First,
 the notation guard at the head of this file is REQUIRED rather than
 defensive -- see the comment there.  Second,
 Category.Theory.Adjunction exports [unit], so the singleton probe
 object of the [Two_Discrete] refutation is spelled with Lib's
 [poly_unit]/[ttt]: written [(unit : Coq)] the ascription resolves to
 the adjunction unit and fails with a type error naming neither
 culprit.

 WHAT IS NOT DELIVERED.  The issue's own Verification block pins
 [Print Assumptions connected_limit_of_constant]; THAT NAME EXISTS
 NOWHERE IN THE TREE (measured), the delivered name being
 [const_IsALimit].  And only the FORWARD direction of item 2's
 “exactly when” is proved: nothing forces [ConnectedNonempty J] from
 invertibility of the unit.  The GENERAL (non-connected) case is NOT
 built: nothing here composes with Structure/Limit/Components.v's
 [ComponentDecomposition] / [components_IsALimit] to compute the limit
 of a constant diagram over an arbitrary shape as a product of copies
 of c indexed by π₀, and no bridge exhibits the connected case as the
 one-component instance of that file's results.
 [td_const_IsALimit_product] is the two-object discrete case done by
 hand, not an instance of anything.  No converse: it is NOT shown that
 [∀ c, IsALimit Δ[J](c) c] forces [ConnectedNonempty J], so the
 counterexamples establish one direction only.  No separation between
 the cone-level and apex-only readings, so neither is called strictly
 weaker.  Nothing is stated in [StrictCat], and no [_ ≅[Cat] _]
 constant is built.  [Diagonal] is not shown to be an EQUIVALENCE
 under any hypothesis, no [FullyFaithful] record is assembled, and no
 essential-surjectivity clause is attempted.  No absolute-limit theory
 beyond the two definitions and their two witnesses: nothing relates
 [AbsoluteLimit] to [PreservesLimit], [PreservesLimitCone],
 [ContinuousFunctor] or [CreatesLimit], no cone-level absoluteness is
 defined, split coequalizers are not related to it although
 Structure/Coequalizer/Split.v has an absoluteness notion of its own,
 and no absolute limit OTHER than the constant one is exhibited.
 CORRECTION (#477): accurate when written (#356, PR #1229); since #477
 Structure/Limit/Absolute.v defines absoluteness at cone level and
 relates it to [PreservesLimitCone] ([AbsoluteLimitCone_preserves] and
 its converse), part (d) below maps it into [AbsoluteLimit] and
 [AbsoluteColimit] ([AbsoluteLimitCone_apex],
 [AbsoluteColimitCocone_apex]), and Structure/Coequalizer/Absolute.v
 carries split coequalizers into it
 ([split_cofork_AbsoluteColimitCocone]), an absolute colimit other
 than the constant one, which reaches this file's [AbsoluteColimit]
 through [AbsoluteColimitCocone_apex] (Test/ProbeAbsolute477.v, C21).
 The clause asks for an absolute LIMIT: that side is reached through
 Structure/Limit/Absolute.v's [AbsoluteColimitCocone_op], a split
 fork of C^op giving an absolute limit cone in C itself, C^op^op being
 C by conversion (the probe's C48; not declared as a constant).  This
 file's constant witnesses are not restated at cone level, and nothing
 relates [AbsoluteLimit] itself to [PreservesLimit],
 [ContinuousFunctor] or [CreatesLimit].  No
 functoriality or naturality of [const_unit] in c, so part (b) is a
 FAMILY of isomorphisms and is not packaged as a natural isomorphism
 [Id ≅ LimitFunctor ◯ Δ].  No uniqueness statement for the limiting
 cone beyond what [Structure/Limit/Unique.v] already gives.  Nothing
 about cofinality or final functors.  No notation.  No concrete
 category is shown complete by these means, and the only non-vacuity
 witness is the walking arrow. 

 --------
 书籍：      Mac Lane，《Categories for the Working Mathematician》，第二版，§IV.2 练习题 8，印刷页 90 (maclane:IV.2:ex8)
 nLab:       https://ncatlab.org/nlab/show/connected+category 
 nLab:       https://ncatlab.org/nlab/show/constant+functor 
 nLab:       https://ncatlab.org/nlab/show/diagonal+functor 
 nLab:       https://ncatlab.org/nlab/show/limit 
 nLab:       https://ncatlab.org/nlab/show/absolute+colimit 

 Mac Lane 的练习题说明，如果 J 是连通的，那么常量图 Δ [J] (c) 的极限就是 c 本身，而余极限也类似；因此在连通的图形上，对角函子是全忠的，并且 Δ ⊣ lim 单位在每个对象上都是同构。四个交付项是

 (a)  [const_IsALimit]  /  [const_IsAColimit]  (在锥层面上
 [const_IsLimitCone]  /  [const_IsColimitCocone]  和打包的
 [const_Limit]  /  [const_Colimit] ): c 的恒等锥是 Δ [J] (c) 的极限锥，恒等余锥是余极限锥;(b) [const_unit_iso] / [const_counit_iso]：Δ [J] ⊣ [LimitFunctor] 的单位在每个对象处都是可逆的，相对地，[ColimitFunctor] ⊣ Δ [J] 的余单位也是如此——[const_unit_is_med] 记录了单位确实是中介映射，而不仅仅是等于它；

 (c) [Diagonal_Full] 和 [Diagonal_Faithful]：对一个连通形状，对角函子是满的，对非空形状是忠实的——SPLIT 是该点，下面第4节证明了两个部分都是精确的；

 (d) [const_AbsoluteLimit] / [const_AbsoluteColimit]：这些极限是绝对的，由 C 的每一个函子保留。

 1. 先前技术的修正，从两个方面进行，均已测量。该目录问题的“当前状态”部分两次都是错误的。首先，它说明在树中不存在连通性谓词，并要求从零开始建立之字形关系。Structure/Groupoid/Connected.v 已经声明了 [Inductive ZigZag {C : Category}] 和 [Definition Connected (C : Category)]，用于任意类别，自其编写以来，还有 [zigzag_trans]、[zigzag_sym]、[hom_zigzag] 和 [Two_Discrete_not_connected]；Theory/Connected/Components.v 添加了 [ConnectedNonempty]、[Zero_Connected]、[Zero_not_ConnectedNonempty] 和 [connected_readings_differ]。它们在此处全部被使用。此文件中没有重新声明之字形、连通性谓词或它们的任何闭包性质，并且下面的 [leg_zigzag] 是对捐赠者的归纳类型进行的归纳，而不是它的第二个副本。其次，它指出不存在 Δ ⊣ lim 的伴随关系以取其单位。Adjunction/Diagonal/Limit.v 提供了 [Diagonal_Limit_Adjunction : Δ[J] ⊣ LimitFunctor] 和 [Colimit_Diagonal_Adjunction : ColimitFunctor ⊣ Δ[J] ]，以及 [HasLimitsOfShape]、[LimitFunctor]、[lim_obj]、[lim_leg]、[lim_med]、[lim_transpose_to] 以及整个协变余极限镜像。下面的部分 (b) 是针对这些常数陈述的，并且没有构建自己的伴随关系。什么是缺失的，也是这个文件提供的，已经通过 SHAPE 搜索而不是名称搜索得到确认：树中的任何语句都没有计算常量图的极限或余极限。名称搜索返回的两个接近匹配的是关于一个常量权重，而不是常量图——Structure/Limit/Weighted.v 的 [conical_weighted] 有权重 Δ [J]（终对象），而 DIAGRAM 是任意的，这是一个不同的语句——而 Instance/One/Diagonal.v 的 [Diagonal_Unique] 是一个分解（Δ [J] (d) ≈ Δ(d) ◯ one），没有涉及连通性假设，也不计算极限。另一些，[Full (@Diagonal ...)]、[Faithful (@Diagonal ...)]、[AbsoluteLimit]、[AbsoluteColimit] 以及字符串“absolute limit”，在整个树中都没有出现过。(d) 真正是新的
 词汇——[AbsoluteLimit] 和 [AbsoluteColimit] 在此处被引入。(c) 不是：[Full] 和 [Faithful] 是已有的（Theory/Functor.v），所以零出现次数的测量显示在 [Diagonal] 有一个新的实例化，而不是一个新的概念。关于绝对性的现有技术是两个文件中的散文，而不是一个：Structure/Coequalizer/Split.v 和 Construction/Karoubi.v（“拆分幂等元是一个绝对余极限”）。狭义上阅读(d)的新颖性：这个概念属于现有技术。
 Structure/Coequalizer/Split.v 的标题是“分裂余等子是绝对的”，在正文中引用了 Paré 1971 和 nLab，并证明了 [functor_preserves_split] 与 [split_coequalizer_preserved] 。它没有做的是声明一个谓词——它的绝对性是一个构造的属性，通过 [fmap] 传递其方程数据来说明——所以这里没有什么可以实例化，也没有什么可以被包含。两者仅通过共享的词语相关；§“未交付的内容”记录了没有建立桥梁。2. 居住性是承重的，这一点是被证明的，而不是被论证的。树中的 [Connected] 是没有居住性的单纯“任意两个对象被连接”子句，而 [Zero_Connected] 显示空范畴在形式上满足它。在空形状上，一个锥体是一个裸露的顶点——没有腿，没有一致性——所以普遍性质坍缩为终点性，[zero_const_limit_IsTerminalObj] 和 [IsTerminalObj_zero_const_limit] 双向证明了这一点。因此，[const_limit_not_from_bare_connected] 完全否定了裸露 [Connected] 的解读：在 J := [_0] 和 C := [_2] 的情况下，对象 [TwoX] 不是终点（[TwoX_not_terminal]，通过 [Instance/Two.v] 自身的 [TwoHom_Y_X_absurd]），所以结论在那里是错误的，而假设成立。因此假设是 [ConnectedNonempty J]，并且它出现在陈述中。#352 已经在空形处将两种读法分开；这里的新内容是分离在常量极限下也是适用的。想要获取纯 [Connected] 形式的读者，应当将 [zero_const_limit_IsTerminalObj] 视为缺失的情况。

 3. 每个假设的使用地点。[cn_obj K] 和 [cn_zigzag K] 在不同点被使用，且彼此不可替代：[cn_obj K] 指明了中介者（[limit_med (const_IsALimit K) N = cone_leg N (cn_obj K)]，直接指明），而 [cn_zigzag K] 证明了这个选择在每个其他对象上都满足三角形条件。正是在这种精确意义上，仅有连通性是不够的，仅有一个点也不够——这两部分在第4节中都被驳斥。锯齿形内容完全从锥体词汇中提取出来：[leg_zigzag] 采用一个单箭头上恒定的 BARE 系列 [leg : ∀ x : J, n ~> c]，并得出它在锯齿形上也是恒定的。它的三种情况是 [zz_nil]（仅反身性）、[zz_fwd]（在 [f] 的假设，然后是归纳假设）和 [zz_bwd]（相同假设在交换参数下，向后重写）——因此两个非平凡构造器消耗同一个输入，并且没有需要处理的不对称性。它服务于锥体侧、余锥体侧、两个绝对陈述以及 [Diagonal_Full]，总共有五个使用者。THE COLIMIT 的一半不需要 [Connected (J^op)]，这很幸运，因为树没有将连通性传输到对面（测量结果：任何地方都没有 [zigzag_op] 和 [Connected_op]）。 [Connected] 被声明为任意范畴，因此 [Connected (J^op)] 完全可以表述，并且可以通过三情况归纳互换 [zz_fwd] 和 [zz_bwd] 得出；缺少的只是这种传输，而不是陈述。 [obj[J^op] 是 [obj[J]，所以 [leg_zigzag] 在形状 [J] 上用环境 [C^op] 实例化；需要明确的 [@leg_zigzag J (C^op) ...]，因为如果交给推理，[cone_leg N] 的索引类型会让 Coq 选择 [J^op]，然后步骤假设要求 [J^op] 箭头。4. （c）的两半由已编写的反例分开。[Diagonal_Faithful] 只接受 J 的一个对象；[Diagonal_Full] 接受整个 [ConnectedNonempty]。尖锐性是部分的，间隙被命名：被反驳的是忠实度的点，以及完整性的连通性那一半。在没有点的形状上没有任何东西可以反驳完整性，因此 [ConnectedNonempty] 的点半部分对于 [Diagonal_Full] 并非必要。两个反驳：[Diagonal_Zero_not_Faithful] 反驳了空形上的忠实性（其中 [_0, Coq] 具有单元素 Hom 集，因此 [id] 和 [negb] 崩溃），而 [Diagonal_Two_Discrete_not_Full] 反驳了在有元素但不连通的 [Two_Discrete] 上的充实性——变换 [td_split] 在一个对象上是 [id]，在另一个对象上是 [negb]，在那里是自然的，并且不是任何态射的像。该反驳直接针对 [Full] 的 [prefmap] 和 [fmap_sur] 发起，而 [Full] 不要求 [prefmap] 的函子性，因此它反驳了充实性的最弱理解。[Diagonal_Full] 被传送两次——一次直接传送，另一次通过部分 (a) 的中介传送 [Diagonal_Full_via_limit]——并且两者选择了相同的前镜像，该前镜像由 [Diagonal_Full_routes_agree] 记录在 [eq_refl]。因此，极限路径不是绕道到不同选择的部分；它是直接路径。这两个 [Full] 记录没有被比较，它们的 [fmap_sur] 证明是不同的不透明项。5. [Two_Discrete] 反驳所说和未说的内容。
 [two_discrete_const_not_limit] 反驳说 [bool]，无论有任何腿的族，都是 [bool] 常数二维离散图在 [Coq] 中的极限——腿的量化位于 [IsALimit] 内，因此这是强形式。它并没有说极限不存在：[td_const_IsALimit_product] 构建了它，并且它是 c × c。它也不在每个对象上成立：[td_const_IsALimit_at_unit] 表明断开的结论在终端 c 上仍然成立，因此证据必须是一个对象，其 c ≇ c × c，并且没有薄环境能够容纳它（在薄范畴中，c × c ≅ c 总是成立）。这就是为什么证据是 [Coq]，而反驳是鸽笼原理：从 bool 出发到 bool × bool 的 ⟨φX, φY⟩ 的满射性。6. 优势，严格优先测量。如下每个回读都标明其主题。在 [eq_refl]、[const_fobj] 和 [const_fmap] 上保持：常量图的箭头作用是 [id[c]，这就是为什么该文件中的每个相干性义务都是通过 [id_left] 而不是通过追赶来结束的；[const_apex_strict]、[const_cone_leg_strict]、[const_leg_strict] 和 [const_med_strict]（调解者是 [cn_obj K] 上竞争锥的支）；三个余极镜 [const_cocone_inj_strict]、[const_coinj_strict]、[const_comed_strict]；[const_unit_is_transpose] 和 [const_unit_is_med]（Δ ⊣ lim 的单元是调解映射，而不仅仅是 ≈）以及 [const_counit_is_transpose] 的对偶；[const_two_cones_same_legs]；[const_absolute_leg_strict] 和 [const_absolute_coinj_strict]；[const_image_fobj]；[Diagonal_Full_routes_agree]；以及非空对 [two_const_leg_strict]、[two_const_med_strict]。满足于≈，原因已被诊断而非猜测——
 两个原因，[const_unit_is_limit_unique_to] 和 [const_image_fmap_equiv]。第一个：它的严格形式已被驳斥并固定，而 [const_two_cones_same_legs] 是诊断控制——两个相互竞争的锥体在 [eq_refl] 处的腿相同，仅在 [cone_coherence] 证明项上有所不同，而 [ump_limits] 的抽象 [HasLimitsOfShape] 归约为零，因此无法进行转换。同样在≈处：[const_image_fmap_equiv]，其严格形式同样被驳斥——[fmap[F ◯ Δ[J] (c)] f] 是 [fmap[F] id [c]]，其中 [fmap[Δ[J] (F c)] f] 是 [id[F c]]，且仅有 [fmap_id] 关联它们。7. 否定：五个，其中两种类型，词汇上保持分开——三个在正文中的转换，以及两个在结尾中的可形成性 [UniverseProbe] 部分——每一个都剥离一次，并且其失败信息从完整的错误消息中读取，而不是从尾部。

 转换。[op_diag_strict] 记录 [Δ[J] (c)^op] 不是 [Δ[J^op] (c)]，[op_diag_fobj] 和 [op_diag_fmap] 作为对照显示两个数据字段在 [eq_refl] 上一致，因此差异仅限于三个重建的法律字段。这不是巧合：[ACone n G] 对于不可转换的 [G] 不是可转换的，因此 colimit 的一半不能通过在 [C^op] 和 [J^op] 上实例化 limit 的一半来获得，而是直接构建。[const_image_fmap] 和 [const_unit_is_limit_unique_to_strict] 是另外两个，都在 §6 中讨论。可塑性。由于形状的 hom 宇宙被严格声明在其自身的证明宇宙和环境的 hom 宇宙之下，[Diagonal] 和 [IsALimit] 在各自不同的方程上单独被拒绝——分别是“无法强制 jh = ch”和“无法强制 jp = jh”——而四个在这些水平上被接受的控制（[obj]，一个 hom 类型，[ACone] 和 [Cone]）却被接受。因此，第8节的“两个独立供体”得到了保护，而不仅仅是测量。每个在 [Fail] 中命名的常量也会被后续命令命名，因此重命名会明显破坏此文件，而不是使一个保护显得无效地通过：[Opposite_Functor]、[Diagonal]、[fobj] 和 [fmap] 由两个 [op_diag_*] 控制；[Diagonal] 和 [◯] 再次由 [const_image_fobj] 和 [const_image_fmap_equiv] 控制；还有 [const_unit]、[limit_unique_to]、[const_IsALimit] 和 [lim_alimit] 由 [const_unit_is_transpose] 和 [const_unit_is_limit_unique_to] 控制。8. 宇宙，同时查看绑定器和约束块。
 [const_IsALimit@{u u0 u1 u2 u3 u4 u5}] 位于
 [J : Category@{u u0 u0}] 和 [C : Category@{u1 u2 u2}] 之上，其块中有单一方程 [u0 = u2] —— SHAPE 的同态与证明宇宙与 AMBIENT 的宇宙相对应 —— 而两个对象宇宙保持自由，有界且从未被对应识别，并且在一般结果中没有出现 [Set]。注意，每个范畴中的 hom = proof 是通过在绑定器中复用一个层次来表达的，而块中没有任何说明，这是该树反复记录的阅读陷阱。[AbsoluteLimit]  是否这是该陷阱的最尖锐实例：其约束块根本不包含任何方程，而其绑定器读取 [J : Category@{u1 u5 u5}] 和 [C : Category@{u3 u5 u5}] —— 一个层级被用于四个槽。仅检查该块的读者会报告“无识别”，这是错误的。每一个跨类别的识别都是继承的——准确地阅读这句话，因为这里添加了一个识别，而本段早期的修订版本否认了这一点（见本条目的结尾）。继承的识别是以捐赠者自身的签名来衡量的，而不是推断得出：
 [IsALimit@{u u0 u1 u2}] 本身被声明覆盖 [J : Category@{u0 u1 u1}] 和 [C : Category@{u2 u1 u1}]，
 而 [Diagonal@{u u0 u1 u2 u3 u4}] 覆盖 [C : Category@{u3 u4 u4}] 和 [J : Category@{u2 u4 u4}]，它们都在活页夹中携带识别，但区块中没有等式；
 [ACone@{u0 u1 u2 u3 u4 u5}] 保持六个层次的独立，是无辜的。第7条的两个可成形性否定正好保护了这一点。[leg_zigzag@{u u0 u1 u2}]，可重用核心，具有一个字面上为空的约束块——但它的绑定器读取的是 [C : Category@{u u2 u2}]，而该标识并不是继承来的：它是这个文件自身从未标注的 [Context {J C : Category}] 中的最小化产物，通过一个隔离实验得到证明——相同的陈述和证明在声明 [Constraint ch < cp] 在 [Cu : Category@{co ch cp}] 上的部分中也可以编译，其中在那些层次上接受一个同伦类型作为对照。J 侧是继承的（[ZigZag@{u u0}] 声明在 [Category@{u u0 u0}] 上）。所以仅阅读空块在这里会出错，正如前面两个段落的警告所示；显式绑定器可以纠正它，而且没有人声称这是不可避免的。9. 公理与计数。89/89 常量在全局上下文下闭合，由已编译模块上的 [Print Module] 计数，因此 [td_split] 的两个 [Program] 义务都包括在内；该文件未声明 [Record]、[Class] 或 [Inductive]，因此不存在未列出的 [Build_*] 构造函数，并且三个 [Fail] 出现的名称未声明任何内容。阅读等级（GRADE）：这是对所有 89 个的一次性测量，而不是持续门控。更正 (#477)：按相同计数为 91，因为 #477 将 [AbsoluteLimitCone_apex] 和 [AbsoluteColimitCocone_apex] 添加到 (d) 部分，这两个在全局上下文下都是闭合的，并且在 #477 的 print-assumptions 目标块中完全限定；对于它们，本文件需要 Structure/Limit/Absolute.v。10. 两个工程发现，都记录在它们发生的地方。首先，此文件开头的符号保护是必需的，而不是防御性的——见那里的注释。其次，Category.Theory.Adjunction 导出 [unit]，因此 [Two_Discrete] 反驳的单例探针对象通过 Lib 的 [poly_unit] / [ttt] 拼写：以 [(unit : Coq)] 写入时，类型说明解析到伴随单元并因类型错误失败，而该错误未指向任何责任方。未交付的内容。该问题自身的验证模块引脚 [Print Assumptions connected_limit_of_constant]；该名称在树中（测量的）不存在，交付的名称为 [const_IsALimit]。并且仅证明了第2项“确切何时”的正向方向：没有任何东西强制从单元的可逆性中得出 [ConnectedNonempty J]。一般（非连通）情况尚未构建：这里没有任何东西与 Structure/Limit/Components.v 中的 [ComponentDecomposition] / [components_IsALimit] 组合，以计算任意形状上常量图的极限，作为由 π₀ 索引的 c 的副本的乘积，并且没有桥接将连通情况表现为该文件结果的一组件实例。[td_const_IsALimit_product] 是通过手工完成的两个对象离散情况，而不是任何实例的结果。没有逆向：没有显示 [∀ c, IsALimit Δ[J] (c) c] 强制 [ConnectedNonempty J]，因此反例只建立了一个方向。锥级和仅顶点的解读之间没有分离，因此没有一个被称为严格更弱。在 [StrictCat] 中没有说明任何内容，也没有建立 [_ ≅[Cat] _] 常量。未显示 [Diagonal] 在任何假设下是等价的，没有组装 [FullyFaithful] 记录，也没有尝试基本满射性条款。无绝对极限理论
 超出这两个定义及其两个见证：没有任何事物将
 [AbsoluteLimit] 与 [PreservesLimit]、[PreservesLimitCone]、
 [ContinuousFunctor] 或 [CreatesLimit] 关联，未定义锥层级的绝对性，
 分裂余等化器与其无关，尽管 Structure/Coequalizer/Split.v 本身具有绝对性概念，
 并且未显示除常量之外的任何绝对极限。修正 (#477)：在编写时准确 (#356, PR #1229)；自 #477 起，Structure/Limit/Absolute.v 在圆锥层定义了绝对性，并将其与 [PreservesLimitCone]（[AbsoluteLimitCone_preserves] 及其逆）相关联，下文部分 (d) 将其映射到 [AbsoluteLimit] 和 [AbsoluteColimit]（[AbsoluteLimitCone_apex]，[AbsoluteColimitCocone_apex]），而 Structure/Coequalizer/Absolute.v 将分裂的等化器映射到其中（[split_cofork_AbsoluteColimitCocone]），这是一个非恒定的绝对余极限，通过 [AbsoluteColimitCocone_apex] 到达该文件的 [AbsoluteColimit]（Test/ProbeAbsolute477.v，C21）。该条款要求一个绝对极限：这一端通过 Structure/Limit/Absolute.v 的 [AbsoluteColimitCocone_op] 达到，这是 C^op 的一个分裂分叉，在 C 自身中给出了一个绝对极限圆锥，C^op^op 通过变换即为 C（探针的 C48；未声明为常量）。这个文件的常量见证在锥体层级没有重新陈述，也没有任何内容将 [AbsoluteLimit] 本身与 [PreservesLimit]、[ContinuousFunctor] 或 [CreatesLimit] 联系起来。[const_unit] 在 c 中没有函子性或自然性，因此部分 (b) 是一族同构，并未打包为自然同构 [Id ≅ LimitFunctor ◯ Δ]。对于极限锥的唯一性声明，仅限于 [Structure/Limit/Unique.v] 已经提供的内容。没有关于共终性或终函子的说明。没有符号表示。没有通过这些方式展示任何具体范畴是完备的，唯一非空的见证是行箭头 (walking arrow)。
*)

(*
   * ** The constant diagram, and the zig-zag closure that drives the file 

   --------
   * ** 恒定的图表，以及驱动文件的之字形闭合
*)

(*
 The arrow action of a constant diagram is [id] ON THE NOSE, not merely
 ≈ it (Functor/Diagonal.v).  Everything below rests on this: each
 coherence triangle of a cone over Δ[J](c) reads [id ∘ ψx ≈ ψy], so one
 [id_left] collapses it to [ψx ≈ ψy], so no diagram chase occurs in
 any cone-coherence triangle.  Read that scope: the two retraction
 lemmas [const_unit_retraction] and [const_counit_retraction] DO
 chase, each running [comp_assoc] plus a leg-agreement rewrite and a
 section rewrite, and two obligations close with [cat]. 

 --------
 一个常量图的箭头作用是 [id] ，精准对应，而不仅仅是 ≈ 它 (Functor/Diagonal.v)。 一切都建立在此基础上： Δ [J] (c) 上圆锥的每个相干三角形读取为 [id ∘ ψx ≈ ψy] ，因此一个 [id_left] 将其折叠为 [ψx ≈ ψy] ，所以在任何圆锥相干三角形中都不会发生图表追踪。 阅读该范围：两个重traction 引理 [const_unit_retraction] 和 [const_counit_retraction] 会进行追踪，每个运行 [comp_assoc] 加上腿一致性重写和截面重写，两个义务用 [cat] 关闭。
*)

Example const_fobj {J C : Category} (c : C) (x : J) :
  fobj[Δ[J](c)] x = c := eq_refl.

Example const_fmap {J C : Category} (c : C) {x y : J} (f : x ~{J}~> y) :
  fmap[Δ[J](c)] f = id[c] := eq_refl.

(*
 The reusable core, stated for a BARE leg family rather than for a cone:
 a family constant along every single arrow is constant along every
 zig-zag.  [zz_nil] needs reflexivity alone; [zz_fwd] and [zz_bwd]
 consume ONE AND THE SAME hypothesis [H], differing only in the order of
 its arguments and the direction of the rewrite. 

 --------
 可重复使用的核心，是针对裸腿族而不是锥体声明的：
 一个沿每条箭头都恒定的族常数，在每条曲折线路上也恒定。[zz_nil] 仅需自反性；[zz_fwd] 和 [zz_bwd] 消耗相同的假设 [H]，仅在其参数顺序和重写方向上有所不同。
*)

Lemma leg_zigzag {J C : Category} {n c : C} (leg : ∀ x : J, n ~{C}~> c)
  (H : ∀ (x y : J) (f : x ~{J}~> y), leg x ≈ leg y)
  {x y : J} (s : ZigZag x y) : leg x ≈ leg y.
Proof.
  induction s as [w|x' y' z' f s' IH|x' y' z' f s' IH].
  - reflexivity.
  - now rewrite (H _ _ f).
  - now rewrite <- (H _ _ f).
Qed.

(*
   * ** Part (a), the limit: the identity cone on c is limiting 

   --------
   * ** 第 (a) 部分，极限：c 上的恒等圆锥是极限
*)

Section ConstantLimit.

Context {J C : Category}.
Context (c : C).

(*
 No [Program], and no obligation: the coherence field is literally
 [id_left (id[c])]. 

 --------
 没有 [Program]，也没有义务：相干场字面上是 [id_left (id[c] )]。
*)

Definition const_acone : ACone c Δ[J](c) :=
  @Build_ACone J C c Δ[J](c) (fun _ => id[c]) (fun _ _ _ => id_left (id[c])).

Definition const_cone : Cone Δ[J](c) :=
  {| vertex_obj := c ; coneFrom := const_acone |}.

(*
 The single mathematical step: a cone over a constant diagram has legs
 that agree along every arrow of the shape. 

 --------
 单一数学步骤：一个常量图上的锥体在该形状的每一条箭头上都有一致的腿。
*)

Lemma const_cone_step (N : Cone Δ[J](c)) {x y : J} (f : x ~{J}~> y) :
  cone_leg N x ≈ cone_leg N y.
Proof.
  pose proof (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f) as Hc.
  unfold cone_leg. rewrite <- Hc. now rewrite id_left.
Qed.

Definition const_cone_zigzag (N : Cone Δ[J](c)) {x y : J} (s : ZigZag x y) :
  cone_leg N x ≈ cone_leg N y :=
  leg_zigzag (cone_leg N) (@const_cone_step N) s.

(*
 [cn_obj K] NAMES the mediator; [cn_zigzag K] proves that naming
 satisfies the triangle at every other object.  Neither substitutes for
 the other -- §4 of the header refutes each hypothesis without the
 other. 

 --------
 [cn_obj K] 命名了中介者；[cn_zigzag K] 证明命名在每个其他对象上满足三角形。两者互不替代——标题的第 §4 节在没有另一者的情况下驳斥了每个假设。
*)

Definition const_IsALimit (K : ConnectedNonempty J) : IsALimit Δ[J](c) c.
Proof.
  unshelve econstructor.
  - exact const_acone.
  - intro N. unshelve econstructor.
    + exact (cone_leg N (cn_obj K)).
    + intro x. simpl. rewrite id_left.
      exact (const_cone_zigzag N (cn_zigzag K (cn_obj K) x)).
    + intros v Hv. specialize (Hv (cn_obj K)). simpl in Hv.
      rewrite id_left in Hv. symmetry. exact Hv.
Defined.

(*
 The cone-level and bundled readings cost nothing: Preservation.v's four
 conversions are proof-free, so both are [:=] with no tactic. 

 --------
 锥形级别和捆绑读数是免费的：Preservation.v 的四个转换是不需要证明的，因此两者都是 [:=]，没有策略。
*)

Definition const_IsLimitCone (K : ConnectedNonempty J) :
  IsLimitCone const_cone := @ump_limit _ _ _ _ (const_IsALimit K).

Definition const_Limit (K : ConnectedNonempty J) : Limit Δ[J](c) :=
  @Build_Limit J C Δ[J](c) const_cone
    (@ump_limit _ _ _ _ (const_IsALimit K)).

Example const_apex_strict : vertex_obj[const_cone] = c := eq_refl.

Example const_cone_leg_strict (x : J) : cone_leg const_cone x = id[c]
  := eq_refl.

Example const_leg_strict (K : ConnectedNonempty J) (x : J) :
  limit_leg (const_IsALimit K) x = id[c] := eq_refl.

Example const_med_strict (K : ConnectedNonempty J) (N : Cone Δ[J](c)) :
  limit_med (const_IsALimit K) N = cone_leg N (cn_obj K) := eq_refl.

End ConstantLimit.

(*
   * ** Part (a), the colimit: built directly, not by op-instantiation 

   --------
   * ** （a 部分），余极限：直接构建，而不是通过对偶实例化
*)

Section ConstantColimit.

Context {J C : Category}.
Context (c : C).

(*
 NEGATIVE 1 (conversion), with its two controls.  [Δ[J](c)^op] and
 [Δ[J^op](c)] agree in BOTH data fields at [eq_refl] and differ only in
 the three rebuilt law fields -- and since [ACone n G] is not
 convertible for non-convertible [G], that is exactly what stops the
 colimit half from being the limit half instantiated at [C^op], [J^op]. 

 --------
 NEGATIVE 1（转换），以及它的两个控制。[Δ[J] (c)^op] 和 [Δ[J^op] (c)] 在 [eq_refl] 的两个数据字段上完全相同，仅在三个重建的法则字段上有所不同——并且由于 [ACone n G] 对不可转换的 [G] 不可转换，这正是阻止余极半是以 [C^op]、[J^op] 实例化的极限半的原因。
*)

Example op_diag_fobj (x : J) :
  fobj[Opposite_Functor Δ[J](c)] x = fobj[@Diagonal (C^op) (J^op) c] x
  := eq_refl.

Example op_diag_fmap {x y : J^op} (f : x ~{J^op}~> y) :
  fmap[Opposite_Functor Δ[J](c)] f = fmap[@Diagonal (C^op) (J^op) c] f
  := eq_refl.

Fail Example op_diag_strict :
  Opposite_Functor Δ[J](c) = @Diagonal (C^op) (J^op) c := eq_refl.

Definition const_acocone :
  @ACone (J^op) (C^op) c (Opposite_Functor Δ[J](c)) :=
  @Build_ACone (J^op) (C^op) c (Opposite_Functor Δ[J](c))
    (fun _ => id[c]) (fun _ _ _ => id_left (id[c])).

Definition const_cocone : Cocone Δ[J](c) :=
  @Build_Cone (J^op) (C^op) (Opposite_Functor Δ[J](c)) c const_acocone.

Lemma const_cocone_step (N : Cocone Δ[J](c)) {x y : J} (f : x ~{J}~> y) :
  cone_leg N x ≈ cone_leg N y.
Proof.
  pose proof (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) y x f) as Hc.
  unfold cone_leg. rewrite <- Hc. symmetry. now rewrite id_left.
Qed.

(*
 [obj[J^op]] IS [obj[J]], so [leg_zigzag] applies at the shape [J] with
 ambient [C^op] and NO [Connected (J^op)] is needed -- which is
 fortunate, the tree having neither [zigzag_op] nor [Connected_op].
 The explicit arguments are REQUIRED: left to inference the index type
 of [cone_leg N] makes Coq pick [J^op]. 

 --------
 [obj[J^op] ] 是 [obj[J] ]，所以 [leg_zigzag] 适用于形状 [J]，周围环境为 [C^op]，并且不需要 [Connected (J^op)] —— 这是幸运的，因为该树既没有 [zigzag_op] 也没有 [Connected_op]。显式参数是必须的：通过推断 [cone_leg N] 的索引类型，Coq 会选择 [J^op]。
*)

Definition const_cocone_zigzag (N : Cocone Δ[J](c)) {x y : J}
  (s : ZigZag x y) : cone_leg N x ≈ cone_leg N y :=
  @leg_zigzag J (C^op) vertex_obj[N] c (cone_leg N)
    (@const_cocone_step N) x y s.

Definition const_IsAColimit (K : ConnectedNonempty J) : IsAColimit Δ[J](c) c.
Proof.
  unshelve econstructor.
  - exact const_acocone.
  - intro N. unshelve econstructor.
    + exact (cone_leg N (cn_obj K)).
    + intro x. simpl. rewrite id_right.
      exact (const_cocone_zigzag N (cn_zigzag K (cn_obj K) x)).
    + intros v Hv. specialize (Hv (cn_obj K)). simpl in Hv.
      rewrite id_right in Hv. symmetry. exact Hv.
Defined.

Definition const_IsColimitCocone (K : ConnectedNonempty J) :
  IsColimitCocone const_cocone := @ump_limit _ _ _ _ (const_IsAColimit K).

Definition const_Colimit (K : ConnectedNonempty J) : Colimit Δ[J](c) :=
  @Build_Limit (J^op) (C^op) (Opposite_Functor Δ[J](c)) const_cocone
    (@ump_limit _ _ _ _ (const_IsAColimit K)).

Example const_cocone_inj_strict (x : J) : cocone_inj const_cocone x = id[c]
  := eq_refl.

Example const_coinj_strict (K : ConnectedNonempty J) (x : J) :
  colimit_inj (const_IsAColimit K) x = id[c] := eq_refl.

Example const_comed_strict (K : ConnectedNonempty J) (N : Cocone Δ[J](c)) :
  colimit_med (const_IsAColimit K) N = cocone_inj N (cn_obj K) := eq_refl.

End ConstantColimit.

(* * ** Part (d): these limits are absolute / * ** 第(d)部分：这些限制是绝对的 *)

(*
 “Absolute limit” had ZERO occurrences tree-wide, so the notion is
 introduced here: a limit is absolute when EVERY functor out of the
 ambient category preserves it.  Stated at the apex-pinned level, which
 is what part (a) delivers; no cone-level variant is defined.

 CORRECTION (#477): accurate when written; the cone-level variant is
 now Structure/Limit/Absolute.v's [AbsoluteLimitCone] and
 [AbsoluteColimitCocone], and [AbsoluteLimitCone_apex] and
 [AbsoluteColimitCocone_apex], below the two predicates, map it into
 them, typed by their names (Test/ProbeAbsolute477.v, C8 and C9).  The
 converse is not proved and no separation is attempted. 

 --------
 “绝对极限”在整个树中出现次数为零，因此这里引入了这一概念：当来自环境范畴的每一个函子都保持它时，该极限就是绝对的。在顶点固定水平上陈述，即(a)部分所提供的内容；没有定义锥级别的变体。

 修正 (#477)：在书写时是准确的；锥级别的变体现在是 Structure/Limit/Absolute.v 中的 [AbsoluteLimitCone] 和 [AbsoluteColimitCocone]，以及 [AbsoluteLimitCone_apex] 和 [AbsoluteColimitCocone_apex]，在两个谓词之下，将其映射到它们中，由它们的名字标记类型（Test/ProbeAbsolute477.v，C8 和 C9）。其逆命题未被证明，也没有尝试分离。
*)

Definition AbsoluteLimit {J C : Category} (G : J ⟶ C) (c : C) : Type :=
  ∀ (D : Category) (F : C ⟶ D), IsALimit (F ◯ G) (F c).

Definition AbsoluteColimit {J C : Category} (G : J ⟶ C) (c : C) : Type :=
  ∀ (D : Category) (F : C ⟶ D), IsAColimit (F ◯ G) (F c).

(*
 The cone-level predicates of Structure/Limit/Absolute.v (#477), read at
 the apex: an absolute limit cone makes its apex an [AbsoluteLimit] of
 the same diagram, and dually.  The legs are forgotten, so no converse
 is claimed.  Placed here, in the file that owns the apex-only notion,
 so that they are typed by its names; this file requires
 Structure/Limit/Absolute.v for them. 

 --------
 Structure/Limit/Absolute.v (#477) 的锥级谓词，在顶点读取：一个绝对极限锥使其顶点成为同一图的 [AbsoluteLimit]，反之亦然。腿被忽略，因此不声称存在逆命题。放在这里，在拥有仅顶点概念的文件中，这样它们就可以通过其名称进行类型化；该文件为它们需要 Structure/Limit/Absolute.v。
*)

Definition AbsoluteLimitCone_apex@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cone K} (A : AbsoluteLimitCone N) : AbsoluteLimit K vertex_obj[N] :=
  fun D F => limitcone_isalimit (A D F).

Definition AbsoluteColimitCocone_apex@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cocone K} (A : AbsoluteColimitCocone N) :
  AbsoluteColimit K vertex_obj[N] :=
  fun D F => colimitcocone_isacolimit (A D F).

Section Absolute.

Context {J C : Category}.
Context (c : C).

(*
 NEGATIVE 2 (conversion), with its control.  The image of a constant
 diagram agrees with the constant diagram on OBJECTS at [eq_refl] but
 not on ARROWS: [fmap[F ◯ Δ[J](c)] f] is [fmap[F] id[c]] where
 [fmap[Δ[J](F c)] f] is [id[F c]].  So absoluteness is not read off by
 rewriting the composite into a constant diagram; the proof repeats the
 argument with one [fmap_id] inserted. 

 --------
 NEGATIVE 2（转换），以及它的控制。恒定图像在对象 [eq_refl] 上与恒定图一致，但在箭头上不一致：[fmap[F ◯ Δ[J] (c)] f] 是 [fmap[F] id [c]]，其中 [fmap[Δ[J] (F c)] f] 是 [id[F c]]。因此，绝对性不能通过将复合重写为恒定图来得出；证明重复了插入一个 [fmap_id] 的论证。
*)

Example const_image_fobj {D : Category} (F : C ⟶ D) (x : J) :
  fobj[F ◯ Δ[J](c)] x = fobj[Δ[J](F c)] x := eq_refl.

Fail Example const_image_fmap {D : Category} (F : C ⟶ D)
  {x y : J} (f : x ~{J}~> y) :
  fmap[F ◯ Δ[J](c)] f = fmap[Δ[J](F c)] f := eq_refl.

Lemma const_image_fmap_equiv {D : Category} (F : C ⟶ D)
  {x y : J} (f : x ~{J}~> y) :
  fmap[F ◯ Δ[J](c)] f ≈ fmap[Δ[J](F c)] f.
Proof. simpl. apply fmap_id. Qed.

Definition const_AbsoluteLimit (K : ConnectedNonempty J) :
  AbsoluteLimit Δ[J](c) c.
Proof.
  intros D F.
  unshelve econstructor.
  - unshelve econstructor.
    + intro x. exact (id[F c]).
    + intros x y f. simpl. rewrite fmap_id. now rewrite id_left.
  - intro N.
    assert (Hstep : ∀ (x y : J) (f : x ~{J}~> y),
              cone_leg N x ≈ cone_leg N y).
    { intros x y f.
      pose proof (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f) as Hc.
      unfold cone_leg. rewrite <- Hc. simpl.
      rewrite fmap_id. now rewrite id_left. }
    unshelve econstructor.
    + exact (cone_leg N (cn_obj K)).
    + intro x. simpl. rewrite id_left.
      exact (@leg_zigzag J D vertex_obj[N] (F c) (cone_leg N)
               Hstep _ _ (cn_zigzag K (cn_obj K) x)).
    + intros v Hv. specialize (Hv (cn_obj K)). simpl in Hv.
      rewrite id_left in Hv. symmetry. exact Hv.
Defined.

Definition const_AbsoluteColimit (K : ConnectedNonempty J) :
  AbsoluteColimit Δ[J](c) c.
Proof.
  intros D F.
  unshelve econstructor.
  - unshelve econstructor.
    + intro x. exact (id[F c]).
    + intros x y f. simpl. rewrite fmap_id. now rewrite id_left.
  - intro N.
    assert (Hstep : ∀ (x y : J) (f : x ~{J}~> y),
              @cone_leg (J^op) (D^op) _ N x ≈ @cone_leg (J^op) (D^op) _ N y).
    { intros x y f.
      pose proof (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) y x f) as Hc.
      unfold cone_leg. rewrite <- Hc. simpl.
      rewrite fmap_id. now rewrite id_right. }
    unshelve econstructor.
    + exact (@cone_leg (J^op) (D^op) _ N (cn_obj K)).
    + intro x. simpl. rewrite id_right.
      exact (@leg_zigzag J (D^op) vertex_obj[N] (F c)
               (@cone_leg (J^op) (D^op) _ N) Hstep _ _
               (cn_zigzag K (cn_obj K) x)).
    + intros v Hv. specialize (Hv (cn_obj K)). simpl in Hv.
      rewrite id_right in Hv. symmetry. exact Hv.
Defined.

Example const_absolute_leg_strict (K : ConnectedNonempty J)
  {D : Category} (F : C ⟶ D) (x : J) :
  limit_leg (const_AbsoluteLimit K D F) x = id[F c] := eq_refl.

Example const_absolute_coinj_strict (K : ConnectedNonempty J)
  {D : Category} (F : C ⟶ D) (x : J) :
  colimit_inj (const_AbsoluteColimit K D F) x = id[F c] := eq_refl.

End Absolute.

(*
   * ** Part (b): the unit of Δ ⊣ lim is the mediating map, and invertible 

   --------
   * ** （b部分）：Δ ⊣ lim 的单位是中介映射，并且是可逆的
*)

Section LimitUnit.

Context {J C : Category}.
Context (L : HasLimitsOfShape J C).
Context (K : ConnectedNonempty J).
Context (c : C).

Definition const_unit : c ~{C}~> lim_obj L Δ[J](c) :=
  @unit ([J, C]) C (@Diagonal C J) (LimitFunctor L)
        (Diagonal_Limit_Adjunction L) c.

(*
 Both identifications are [eq_refl]: the unit IS the transpose of the
 identity, and IS the mediator out of the transposed cone. 

 --------
 两种标识都是 [eq_refl]：该单位是单位矩阵的转置，并且是转置锥的媒介。
*)

Example const_unit_is_transpose :
  const_unit = lim_transpose_to L (@id ([J, C]) Δ[J](c)) := eq_refl.

Example const_unit_is_med :
  const_unit = lim_med L (lim_transpose_cone (@id ([J, C]) Δ[J](c)))
  := eq_refl.

Lemma lim_leg_const_agree (x y : J) :
  lim_leg L Δ[J](c) x ≈ lim_leg L Δ[J](c) y.
Proof using J C L K c.
  exact (@const_cone_zigzag J C c (@limit_cone J C Δ[J](c) (L Δ[J](c)))
           x y (cn_zigzag K x y)).
Qed.

(*
 The section direction spends NO connectedness -- it is the transpose's
 own commutation law.  The zig-zag is spent exactly once, in the
 retraction, through the same [const_cone_zigzag] part (a) uses. 

 --------
 该部分方向不消耗连通性——它是转置自身的换位法则。之字形恰好使用一次，即在缩回时，通过同样的 [const_cone_zigzag] 部分（a）所使用的部分。
*)

Lemma const_unit_section :
  lim_leg L Δ[J](c) (cn_obj K) ∘ const_unit ≈ id[c].
Proof.
  unfold const_unit.
  exact (lim_transpose_to_commutes L (@id ([J, C]) Δ[J](c)) (cn_obj K)).
Qed.

Lemma const_unit_retraction :
  const_unit ∘ lim_leg L Δ[J](c) (cn_obj K) ≈ id.
Proof.
  apply (lim_med_eq L (@limit_cone J C Δ[J](c) (L Δ[J](c)))); intro j.
  - transitivity (lim_leg L Δ[J](c) (cn_obj K)).
    + rewrite comp_assoc, (lim_leg_const_agree j (cn_obj K)).
      rewrite const_unit_section. now rewrite id_left.
    + exact (lim_leg_const_agree (cn_obj K) j).
  - now rewrite id_right.
Qed.

Definition const_unit_IsIsomorphism : IsIsomorphism const_unit :=
  {| two_sided_inverse := lim_leg L Δ[J](c) (cn_obj K)
   ; is_right_inverse  := const_unit_retraction
   ; is_left_inverse   := const_unit_section |}.

Definition const_unit_iso : c ≅ lim_obj L Δ[J](c) :=
  {| to := const_unit ; from := lim_leg L Δ[J](c) (cn_obj K)
   ; iso_to_from := const_unit_retraction
   ; iso_from_to := const_unit_section |}.

(*
 NEGATIVE 3 (conversion), with its DIAGNOSING control.  The unit is the
 canonical comparison of the two limits, but only at ≈: the two
 competing cones have the same legs at [eq_refl] and differ only in
 their [cone_coherence] proof terms, and [ump_limits] of an abstract
 [HasLimitsOfShape] reduces on nothing. 

 --------
 NEGATIVE 3（转换），带有其诊断控制。该单元是两个极限的规范比较，但仅在≈时：两个竞争锥在[eq_refl]处具有相同的边，仅在其[cone_coherence]证明项中有所不同，而[ump_limits]的一个抽象[HasLimitsOfShape]在任何情况下都不简化。
*)

Fail Example const_unit_is_limit_unique_to_strict :
  const_unit = @limit_unique_to J C Δ[J](c) c (lim_obj L Δ[J](c))
                 (@const_IsALimit J C c K) (lim_alimit L Δ[J](c)) := eq_refl.

Example const_two_cones_same_legs (j : J) :
  cone_leg (lim_transpose_cone (@id ([J, C]) Δ[J](c))) j
    = cone_leg (alimit_cone (@const_IsALimit J C c K)) j := eq_refl.

Lemma const_unit_is_limit_unique_to :
  const_unit ≈ @limit_unique_to J C Δ[J](c) c (lim_obj L Δ[J](c))
                 (@const_IsALimit J C c K) (lim_alimit L Δ[J](c)).
Proof.
  symmetry.
  apply (lim_med_unique L (alimit_cone (@const_IsALimit J C c K))).
  intro j. unfold const_unit.
  exact (lim_transpose_to_commutes L (@id ([J, C]) Δ[J](c)) j).
Qed.

End LimitUnit.

(*
   * ** Part (b), dually: the counit of colim ⊣ Δ is invertible 

   --------
   * ** 部分 (b)，对偶地：colim ⊣ Δ 的余单位是可逆的
*)

Section ColimitCounit.

Context {J C : Category}.
Context (M : HasColimitsOfShape J C).
Context (K : ConnectedNonempty J).
Context (c : C).

Definition const_counit : colim_obj M Δ[J](c) ~{C}~> c :=
  @counit C ([J, C]) (ColimitFunctor M) (@Diagonal C J)
          (Colimit_Diagonal_Adjunction M) c.

Example const_counit_is_transpose :
  const_counit = colim_transpose_from M (@id ([J, C]) Δ[J](c)) := eq_refl.

Lemma colim_inj_const_agree (x y : J) :
  colim_inj M Δ[J](c) x ≈ colim_inj M Δ[J](c) y.
Proof using J C M K c.
  exact (@const_cocone_zigzag J C c
           (@limit_cone (J^op) (C^op) _ (M Δ[J](c))) x y (cn_zigzag K x y)).
Qed.

Lemma const_counit_section :
  const_counit ∘ colim_inj M Δ[J](c) (cn_obj K) ≈ id[c].
Proof.
  unfold const_counit.
  exact (colim_transpose_from_commutes M (@id ([J, C]) Δ[J](c)) (cn_obj K)).
Qed.

Lemma const_counit_retraction :
  colim_inj M Δ[J](c) (cn_obj K) ∘ const_counit ≈ id.
Proof.
  apply (colim_med_eq M (@limit_cone (J^op) (C^op) _ (M Δ[J](c)))); intro j.
  - transitivity (colim_inj M Δ[J](c) (cn_obj K)).
    + rewrite <- comp_assoc, (colim_inj_const_agree j (cn_obj K)).
      rewrite const_counit_section. now rewrite id_right.
    + exact (colim_inj_const_agree (cn_obj K) j).
  - now rewrite id_left.
Qed.

Definition const_counit_IsIsomorphism : IsIsomorphism const_counit :=
  {| two_sided_inverse := colim_inj M Δ[J](c) (cn_obj K)
   ; is_right_inverse  := const_counit_section
   ; is_left_inverse   := const_counit_retraction |}.

Definition const_counit_iso : colim_obj M Δ[J](c) ≅ c :=
  {| to := const_counit ; from := colim_inj M Δ[J](c) (cn_obj K)
   ; iso_to_from := const_counit_section
   ; iso_from_to := const_counit_retraction |}.

End ColimitCounit.

(*
   * ** Part (c): the diagonal is faithful on a point, full on a zig-zag 

   --------
   * ** 部分 (c)：对一点上是忠实的，对之字形上是满射的
*)

Section DiagonalFullyFaithful.

Context {J C : Category}.

(*
 Faithfulness costs only an OBJECT of J: two transformations agreeing
 everywhere agree at [j0], and their components at [j0] ARE the two
 morphisms. 

 --------
 忠实性只需一个 J 的对象：两个在每处都一致的变换在 [j0] 处一致，它们的分量在 [j0] 处是这两个态射。
*)

Definition Diagonal_Faithful (j0 : J) : Faithful (@Diagonal C J).
Proof. construct. exact (X j0). Defined.

(*
 Naturality between two constant functors reads [id ∘ τx ≈ τy ∘ id], so
 the components agree along every arrow -- the transformation-level twin
 of [const_cone_step]. 

 --------
 两个恒定函子之间的自然性表示为 [id ∘ τx ≈ τy ∘ id]，因此组件在每条箭头上都一致 —— 是 [const_cone_step] 的变换级双胞。
*)

Lemma const_transform_step {x y : C} (t : Δ[J](x) ⟹ Δ[J](y))
  {p q : J} (f : p ~{J}~> q) : transform[t] p ≈ transform[t] q.
Proof.
  pose proof (naturality[t] p q f) as Hn. simpl in Hn.
  rewrite id_left, id_right in Hn. exact Hn.
Qed.

Definition const_transform_zigzag {x y : C} (t : Δ[J](x) ⟹ Δ[J](y))
  {p q : J} (s : ZigZag p q) : transform[t] p ≈ transform[t] q :=
  leg_zigzag (fun j => transform[t] j) (@const_transform_step x y t) s.

Definition Diagonal_Full (K : ConnectedNonempty J) : Full (@Diagonal C J).
Proof.
  unshelve econstructor.
  - intros x y t. exact (transform[t] (cn_obj K)).
  - intros x y t j. simpl.
    exact (const_transform_zigzag t (cn_zigzag K (cn_obj K) j)).
Defined.

(*
 The same fullness read off part (a)'s mediator instead, through
 Structure/Cone/Const.v's [Cone_Natural_Transform]. 

 --------
 同样的丰度反而从部分 (a) 的中介读取，通过 Structure/Cone/Const.v 的 [Cone_Natural_Transform]。
*)

Definition Diagonal_Full_via_limit (K : ConnectedNonempty J) :
  Full (@Diagonal C J).
Proof.
  unshelve econstructor.
  - intros x y t.
    exact (limit_med (@const_IsALimit J C y K)
             {| vertex_obj := x
              ; coneFrom := fst (Cone_Natural_Transform Δ[J](y) x) t |}).
  - intros x y t j. simpl.
    pose proof (limit_med_commutes (@const_IsALimit J C y K)
      {| vertex_obj := x
       ; coneFrom := fst (Cone_Natural_Transform Δ[J](y) x) t |} j) as Hm.
    simpl in Hm. rewrite id_left in Hm. exact Hm.
Defined.

(*
 The two routes pick THE SAME preimage, on the nose -- so the limit
 route is not a detour to a different chosen section.  The two [Full]
 RECORDS are not compared; their [fmap_sur] proofs are distinct opaque
 terms. 

 --------
 这两条路径选择了完全相同的原像——所以极限路径并不是前往不同选定截面的绕行。这两个 [Full] 记录没有被比较；它们的 [fmap_sur] 证明是不同的不透明项。
*)

Example Diagonal_Full_routes_agree (K : ConnectedNonempty J) (x y : C)
  (t : Δ[J](x) ⟹ Δ[J](y)) :
  @prefmap _ _ _ (Diagonal_Full_via_limit K) x y t
    = @prefmap _ _ _ (Diagonal_Full K) x y t := eq_refl.

End DiagonalFullyFaithful.

(*
   * ** Inhabitedness is necessary: the empty shape computes a terminal
   object, not c 

   --------
   * ** 居住性是必要的：空形状计算的是终端对象，而不是 c
*)

Definition zero_ACone {C : Category} (c n : C) : ACone n Δ[_0](c) :=
  @Build_ACone _0 C n Δ[_0](c)
    (fun x => match x with end) (fun x _ _ => match x with end).

Definition zero_Cone {C : Category} (c n : C) : Cone Δ[_0](c) :=
  {| vertex_obj := n ; coneFrom := zero_ACone c n |}.

(*
 Over [_0] a cone is a BARE APEX, so the universal property IS
 terminality -- proved in both directions. 

 --------
 在 [_0] 上，锥体是一个裸顶点，因此其泛性质是终端性——在两个方向上都已证明。
*)

Theorem zero_const_limit_IsTerminalObj {C : Category} {c : C} :
  IsALimit Δ[_0](c) c → IsTerminalObj c.
Proof.
  intros H d.
  destruct (@ump_limit _ _ _ _ H (zero_Cone c d)) as [u _ Hu].
  unshelve econstructor.
  - exact u.
  - exact I.
  - intros v _. apply Hu. intro x. destruct x.
Defined.

Theorem IsTerminalObj_zero_const_limit {C : Category} {c : C} :
  IsTerminalObj c → IsALimit Δ[_0](c) c.
Proof.
  intro T.
  unshelve econstructor.
  - exact (zero_ACone c c).
  - intro N. unshelve econstructor.
    + exact (unique_obj (T vertex_obj[N])).
    + intro x. destruct x.
    + intros v _. apply (uniqueness (T vertex_obj[N])). exact I.
Defined.

Theorem TwoX_not_terminal : IsTerminalObj (TwoX : _2) → False.
Proof.
  intro T. exact (TwoHom_Y_X_absurd (unique_obj (T (TwoY : _2)))).
Qed.

Theorem zero_const_limit_needs_inhabited :
  IsALimit Δ[_0]((TwoX : _2)) (TwoX : _2) → False.
Proof.
  intro H. exact (TwoX_not_terminal (zero_const_limit_IsTerminalObj H)).
Qed.

(*
 The bare in-tree [Connected] reading of part (a) is FALSE. 

 --------
 部分 (a) 的裸树 [Connected] 读取为 FALSE。
*)

Theorem const_limit_not_from_bare_connected :
  (∀ (J C : Category) (c : C), Connected J → IsALimit Δ[J](c) c) → False.
Proof.
  intro H.
  exact (zero_const_limit_needs_inhabited
           (H _0 _2 (TwoX : _2) Zero_Connected)).
Qed.

Theorem Diagonal_Zero_not_Faithful : Faithful (@Diagonal Coq _0) → False.
Proof.
  intro F.
  assert (Hn : @id Coq bool ≈ negb).
  { apply (@fmap_inj _ _ _ F). intro x. destruct x. }
  exact (Bool.diff_true_false (Hn true)).
Qed.

(*
   * ** Connectedness is necessary: a two-object discrete shape 

   --------
   * ** 连接性是必要的：一个两对象的离散形状
*)

Definition td_ACone {C : Category} {c d : C} (p q : d ~{C}~> c) :
  ACone d Δ[Two_Discrete](c).
Proof.
  unshelve econstructor.
  - intro x. destruct x; [ exact p | exact q ].
  - intros x y f. destruct f; simpl; cat.
Defined.

Definition td_Cone {C : Category} {c d : C} (p q : d ~{C}~> c) :
  Cone Δ[Two_Discrete](c) :=
  {| vertex_obj := d ; coneFrom := td_ACone p q |}.

Section TwoDiscreteRefutation.

Context (H : IsALimit Δ[Two_Discrete]((bool : Coq)) (bool : Coq)).

Definition tdX : bool → bool := limit_leg H TwoDX.
Definition tdY : bool → bool := limit_leg H TwoDY.

(*
 The EXISTENCE half of the universal property alone, at apex [unit] with
 constant legs, makes ⟨tdX, tdY⟩ : bool → bool × bool surjective. 

 --------
 仅宇宙属性的存在部分，在顶点 [unit] 且带有恒定边的情况下，使 ⟨tdX, tdY⟩ : bool → bool × bool 成为满射。
*)

(*
 [Theory/Adjunction.v] exports [unit], so the singleton probe object is
 spelled with Lib's [poly_unit]/[ttt] rather than the stdlib [unit]/[tt];
 otherwise the ascription [(unit : Coq)] resolves to the adjunction unit
 and fails with a type error naming neither culprit. 

 --------
 [Theory/Adjunction.v] 导出 [unit]，因此单例探针对象是用 Lib 的 [poly_unit] / [ttt] 拼写的，而不是用 stdlib 的 [unit] / [tt]；否则，归属 [(unit : Coq)] 会解析为伴随单元，并以一个不指明具体原因的类型错误失败。
*)

Lemma td_surj (a b : bool) : { z : bool & (tdX z = a) * (tdY z = b) }.
Proof using H.
  destruct (@ump_limit _ _ _ _ H
              (@td_Cone Coq (bool : Coq) (poly_unit : Coq)
                 (fun _ => a) (fun _ => b))) as [u Hu _].
  exists (u ttt).
  exact (Hu TwoDX ttt, Hu TwoDY ttt).
Defined.

(*
 [False] mentions no section variable, so the [Proof using] is explicit;
 the Theory/Category/Monoid.v precedent. 

 --------
 [False] 没有提到任何节变量，所以 [Proof using] 是明确的；Theory/Category/Monoid.v 的先例。
*)

Theorem td_const_not_limit : False.
Proof using H.
  destruct (td_surj true  true)  as [z1 [Ha1 Hb1]].
  destruct (td_surj true  false) as [z2 [Ha2 Hb2]].
  destruct (td_surj false true)  as [z3 [Ha3 Hb3]].
  destruct z1, z2, z3; congruence.
Qed.

End TwoDiscreteRefutation.

Definition two_discrete_const_not_limit :
  IsALimit Δ[Two_Discrete]((bool : Coq)) (bool : Coq) → False :=
  td_const_not_limit.

Theorem const_limit_not_from_point_alone :
  (∀ (J C : Category) (c : C), J → IsALimit Δ[J](c) c) → False.
Proof.
  intro H.
  exact (two_discrete_const_not_limit
           (H Two_Discrete Coq (bool : Coq) TwoDX)).
Qed.

(*
 What the disconnected shape computes INSTEAD: the binary product.  So
 what is refuted is quantitative, not existence. 

 --------
 断开形状计算的相反结果：二进制乘积。所以被反驳的是量的方面，而不是存在。
*)

Definition td_const_IsALimit_product {C : Category} `{@Cartesian C} (c : C) :
  IsALimit Δ[Two_Discrete](c) (c × c).
Proof.
  unshelve econstructor.
  - exact (td_ACone exl exr).
  - intro N. unshelve econstructor.
    + exact (cone_leg N TwoDX △ cone_leg N TwoDY).
    + intro x. destruct x; simpl; cat.
    + intros v Hv. symmetry.
      apply (snd (ump_products _ _ v)).
      split; [ exact (Hv TwoDX) | exact (Hv TwoDY) ].
Defined.

Lemma punit_irrel (a b : poly_unit) : a = b.
Proof. destruct a, b; reflexivity. Qed.

(*
 ... and at a terminal object the disconnected conclusion still HOLDS, so
 the refutation genuinely needs an object with c ≇ c × c.  No thin
 ambient can host one, which is why the witness above is [Coq]. 

 --------
 ... 在一个终端对象上，不连通的结论仍然成立，所以反驳确实需要一个满足 c ≇ c × c 的对象。没有薄的环境可以容纳这样的对象，这就是上面提到的见证者是 [Coq] 的原因。
*)

Definition td_const_IsALimit_at_unit :
  IsALimit Δ[Two_Discrete]((poly_unit : Coq)) (poly_unit : Coq).
Proof.
  unshelve econstructor.
  - exact (td_ACone (fun _ => ttt) (fun _ => ttt)).
  - intro N. unshelve econstructor.
    + exact (fun _ => ttt).
    + intros x y. apply punit_irrel.
    + intros v _ y. apply punit_irrel.
Defined.

(*
 Fullness fails over an inhabited but disconnected shape.  The witness is
 natural and is the image of no morphism; the refutation fires against
 [Full]'s [prefmap]/[fmap_sur], which demand no functoriality of
 [prefmap], so it refutes the WEAKEST reading of fullness. 

 --------
 丰满作用于一个有人居住但断开的形状上。见证是自然的，并且不是任何态射的映像；反驳指向 [Full] 的 [prefmap] / [fmap_sur] ，它们不要求 [prefmap] 的函子性，因此它反驳了丰满的最弱理解。
*)

Program Definition td_split :
  Δ[Two_Discrete]((bool : Coq)) ⟹ Δ[Two_Discrete]((bool : Coq)) := {|
  transform := fun j => match j with
                        | TwoDX => @id Coq bool
                        | TwoDY => negb
                        end
|}.
Next Obligation. destruct f; reflexivity. Qed.
Next Obligation. destruct f; reflexivity. Qed.

Theorem Diagonal_Two_Discrete_not_Full :
  Full (@Diagonal Coq Two_Discrete) → False.
Proof.
  intro F.
  pose proof (@fmap_sur _ _ _ F (bool : Coq) (bool : Coq) td_split) as Hs.
  pose proof (Hs TwoDX true) as H1.
  pose proof (Hs TwoDY true) as H2.
  simpl in H1, H2. congruence.
Qed.

(* * ** Non-vacuity: the walking arrow / * ** 非空性：行走的箭 *)

(*
 [Two_Connected] is Structure/Limit/Components.v, consumed rather
 than rebuilt. 

 --------
 [Two_Connected] 是 Structure/Limit/Components.v，被使用而不是重建。
*)

Definition two_ConnectedNonempty : ConnectedNonempty _2 :=
  Build_ConnectedNonempty (TwoX : _2) Two_Connected.

Definition two_const_IsALimit {C : Category} (c : C) :
  IsALimit Δ[_2](c) c := @const_IsALimit _2 C c two_ConnectedNonempty.

Definition two_const_IsAColimit {C : Category} (c : C) :
  IsAColimit Δ[_2](c) c := @const_IsAColimit _2 C c two_ConnectedNonempty.

Definition two_const_AbsoluteLimit {C : Category} (c : C) :
  AbsoluteLimit Δ[_2](c) c :=
  @const_AbsoluteLimit _2 C c two_ConnectedNonempty.

(*
 The shape is not degenerate: two distinct objects, a crossing arrow, and
 provably NO arrow back -- so the zig-zag, not a single arrow, is what
 joins [TwoY] to [TwoX]. 

 --------
 这个形状不是退化的：两个不同的对象，一个交叉箭头，并且可以证明没有箭头回去——因此连接 [TwoY] 到 [TwoX] 的是之字形，而不是单个箭头。
*)

Theorem two_objects_distinct : (TwoX : _2) = TwoY → False.
Proof. discriminate. Qed.

Definition two_crossing_arrow : TwoX ~{_2}~> TwoY := TwoXY.

Theorem two_no_arrow_back : (TwoY ~{_2}~> TwoX) → False.
Proof. intro f. inversion f. Qed.

Example two_const_leg_strict {C : Category} (c : C) (x : _2) :
  limit_leg (two_const_IsALimit c) x = id[c] := eq_refl.

Example two_const_med_strict {C : Category} (c : C) (N : Cone Δ[_2](c)) :
  limit_med (two_const_IsALimit c) N = cone_leg N TwoX := eq_refl.

(*
   * ** Universe probe: the two identifications are the DONORS' 

   --------
   * ** 宇宙探测器：两个身份都是捐赠者的
*)

(*
 Section-local [Universes]/[Constraint] declarations do not leak past
 [End] -- the Instance/Fun/Group.v precedent, re-measured for this file
 out of tree by importing it into a scratch module that declares its own
 levels strictly apart and having that module elaborate -- so the guard
 for §8 of the header lives here rather than in a separate probe file.

 NEGATIVES 4 AND 5 (formability), with four controls.  With the shape's
 hom universe declared strictly BELOW both its own proof universe and
 the ambient's hom universe, [obj], a hom-type, [ACone] and [Cone] all
 elaborate -- so the cone vocabulary is INNOCENT -- while [Diagonal] and
 [IsALimit] are each rejected ALONE, and on DIFFERENT equations:
 [Diagonal] fails with “Cannot enforce jh = ch” (its codomain [Fun]
 identifies source and target hom levels) and [IsALimit] with “Cannot
 enforce jp = jh”.  So the [u0 = u2] carried by [const_IsALimit] has two
 genuinely independent donors, neither introduced here. 

 --------
 部分本地 [Universes] / [Constraint] 声明不会泄漏到 [End] 之外——根据 Instance/Fun/Group.v 的先例重新测量，用于此文件，通过将其导入到一个声明自己等级严格分开的临时模块中，并让该模块展开——因此标题 §8 的保护就在这里，而不是在单独的探针文件中。消极情况 4 和 5（可形成性），有四个控制。形状的 hom 宇宙被严格声明在其自身证明宇宙和环境的 hom 宇宙之下，[obj] 是一个 hom 类型，[ACone] 和 [Cone] 都被详细展开——因此圆锥词汇是无害的——而 [Diagonal] 和 [IsALimit] 各自单独被拒绝，并且在不同的方程上：[Diagonal] 失败，提示“无法强制 jh = ch”（其余域 [Fun] 识别源和目标的 hom 等级），[IsALimit] 失败，提示“无法强制 jp = jh”。因此，由 [const_IsALimit] 携带的 [u0 = u2] 有两个真正独立的供体，这里都没有引入。
*)

Section UniverseProbe.

Universes jo jh jp co ch cp.
Constraint jh < jp.
Constraint jh < ch.

Context (Ju : Category@{jo jh jp}) (Cu : Category@{co ch cp}) (x : Cu).

Check (obj[Ju]).
Check (∀ a b : Ju, a ~{Ju}~> b).
Check (@ACone Ju Cu x).
Check (@Cone Ju Cu).

Fail Check (@Diagonal Cu Ju).
Fail Check (@IsALimit Ju Cu).

End UniverseProbe.
