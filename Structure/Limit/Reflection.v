Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.CokernelPair.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Coequalizer.
Require Import Category.Instance.Parallel.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

Generalizable All Variables.

(* * * Reflection of limits, colimits and coequalizers / * * 极限、余极限与共同等化子的反射 *)

(*
 Book:   Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 Springer GTM 5, 1998, §VI.7 “Beck's Theorem”: the Definition
 of reflecting colimits, printed p. 154 (PDF p. 163) —
 maclane:VI.7:def2; Exercise 1, p. 154 (PDF p. 163) —
 maclane:VI.7:ex1; Exercise 3, p. 155 (PDF p. 164) —
 maclane:VI.7:ex3
 Book:   Riehl, “Category Theory in Context”, 2nd ed., §3.4:
 Definition 3.4.1 (ii), printed p. 104 (PDF p. 124) —
 riehl:3.4:def1; Lemma 3.4.5, p. 105 (PDF p. 125) —
 riehl:3.4:lem5; Exercise 3.4.iii, p. 108 (PDF p. 128) —
 riehl:3.4:exiii
 nLab:   https://ncatlab.org/nlab/show/reflected+limit
 nLab:   https://ncatlab.org/nlab/show/conservative+functor

 WHAT THE BOOKS SAY, read from the page images.  Mac Lane, p. 154:
 “Definition.  A functor G : A → X reflects colimits of T : J → A when
 every cone λ : T →· a from T to a ∈ A for which Gλ : GT →· Ga is a
 colimiting cone in X is already a colimiting cone in A.  In
 particular, G reflects coequalizers when every fork in A which becomes
 a coequalizer in X is already a coequalizer in A.  Similarly, G
 reflects isomorphisms when, for all arrows t of A, Gt an isomorphism
 implies t an isomorphism.”  The exercises open “(Throughout,
 ”coequalizers“ means ”coequalizers of parallel pairs“.)”; “1. If G
 creates coequalizers, prove that it also reflects coequalizers.”; and
 p. 155, “3. (Alternative hypothesis for Exercise 2.)  If A has all
 coequalizers, G preserves all coequalizers, and G reflects
 isomorphisms, prove that G reflects all coequalizers.”  Riehl, p. 104:
 F “reflects limits of K if every cone over K, whose image under F is a
 limit cone for the diagram FK, is a limit cone over K”, and “More
 commonly, we speak of a functor that preserves, reflects, or creates
 limits of a class of diagrams, for instance of a particular shape or
 size.  Definition 3.4.1 dualizes ...”; p. 105, Lemma 3.4.5: “Any full
 and faithful functor reflects any limits and colimits that are present
 in its codomain.”; p. 108, Exercise 3.4.iii: “Prove that F : C → D
 creates limits for a particular class of diagrams if both of the
 following hold: (i) C has those limits and F preserves them.  (ii)
 F : C → D reflects isomorphisms.”

 ALREADY IN THE TREE.  Mac Lane's definition, per diagram and at cone
 level, is Structure/Limit/Preservation.v's [ReflectsColimitCocone K F]
 (PR #1087, merged 2026-08-14, for #427): a cocone N over K whose image
 cocone [FCocone F N], the injections of N under F, is colimiting is
 itself colimiting (the probe reads it off, C1).  Riehl's 3.4.1 (ii) is
 [ReflectsLimitCone K F] beside it (PR #1083, merged 2026-08-13, for
 #406; moved there by #1087), and reflection of isomorphisms is the
 class [ReflectsIsos].  On the limit side creation gives reflection by
 Structure/Limit/Creation.v's [creates_reflects_limits] (#1083).  The
 transports [Full_op] and [Faithful_op] that the colimit half of
 Riehl's 3.4.5 needs are Functor/Opposite.v's (PR #1108, merged
 2026-08-15, for #266).  The name [ReflectsLimit], which Creation.v
 left unused for this issue, stays unused: [ReflectsLimitCone] is that
 predicate, and a second name would be a duplicate.

 WHAT IS HERE.
 - Reflection over a shape, over a class of shapes, over a class of
 diagrams and over every diagram, shaped like Preservation.v's
 [PreservesLimitConesOfShape] and [PreservesLimitConesOver] and
 Creation.v's [CreatesAllLimits]: [ReflectsLimitConesOfShape],
 [ReflectsLimitConesOver], [ReflectsLimitConesOfClass],
 [ReflectsAllLimits], and the colimit twins
 [ReflectsColimitCoconesOfShape], [ReflectsColimitCoconesOver],
 [ReflectsColimitCoconesOfClass], [ReflectsAllColimits].  The
 issue's [ReflectsLimits] and [ReflectsColimits] are the [All]
 forms, named like [CreatesAllLimits].  [ReflectsAllLimits_Over]
 and its twin descend from every diagram to any class of shapes.
 A class of shapes is a predicate on categories, so
 Structure/Limit/Finite.v's [FiniteCategory] is Riehl's “all
 finite shapes” (the probe, C11 and C12).  A class of diagrams,
 Riehl's own quantifier, is a predicate on the diagrams K : J ⟶ C
 of every shape J, and a class of shapes S is the class of all
 diagrams of those shapes, [fun J _ => S J]:
 [ReflectsLimitConesOver_OfClass] and
 [ReflectsLimitConesOfClass_Over] take the form over S to the form
 over [fun J _ => S J] and back, each the other's inverse at
 [eq_refl] (C23, C24), and so do their colimit twins (C25, C26).
 - [ReflectsIsos_op]: the opposite of a conservative functor is
 conservative, an isomorphism of C^op being one of C with its two
 laws exchanged (Theory/Morphisms/CokernelPair.v's
 [IsIsomorphism_of_op] and [op_IsIsomorphism_of]).
 - Creation gives reflection on the colimit side:
 [creates_reflects_colimits] is the reflection field of
 [CreatesColimit K F], which is [CreatesLimit] of [K^op] along
 [F^op], with the image cocone over (F ◯ K)^op read over
 F^op ◯ K^op by Preservation.v's [islimitcone_op_comp] (C2, at
 [eq_refl]); [creates_reflects_all_limits] and
 [creates_reflects_all_colimits] quantify.
 - Mac Lane's creation, read literally (§V.1, p. 112):
 [MacLaneCreatesLimit K F] lifts every limiting cone N over F ◯ K
 to a strict lift (Creation.v's [StrictLift]: the image apex equal
 to N's, the image legs N's up to ≈ along that equality) that is
 limiting and equal to every other strict lift of N, the apex by
 [=] and the legs by ≈ along it.  It gives reflection by Mac Lane's
 own argument ([maclane_creates_reflects]): a cone upstairs whose
 image is limiting is a strict lift of that image (Creation.v's
 [self_lift]), so it is the lift, which is limiting.  So it maps
 into the tree's creation ([maclane_CreatesLimit], its reflection
 field that theorem), it holds of the identity
 ([id_maclane_creates]), and [MacLaneCreatesColimit] is its colimit
 side, by the opposite.  In the iso-invariant reading of the same
 clauses, a lift that is limiting and unique up to cone
 isomorphism gives reflection in one line
 ([iso_unique_lift_reflects]); Creation.v's [creates_limiting] and
 [creates_lift_unique] derive those two clauses back from the
 reflection field and the lift's comparison, so for a lift with its
 comparison the field and the two clauses are interderivable.
 - A conservative functor reflects the limits it preserves:
 [conservative_reflects_limit] takes a limiting cone L over K
 whose image is limiting.  For a cone M whose image is limiting,
 the mediator u from M into L has F u commuting with the image
 legs, so F u is the comparison of two limiting image cones and
 invertible ([limitcone_iso]); F reflects that, and M is limiting
 by transport along the cone isomorphism u
 ([limitcone_transport]).  [preserves_conservative_reflects_limit]
 is the book's form (a limit of K, and F preserving it), with its
 forms over a shape, over a class of shapes and over a class of
 diagrams ([preserves_conservative_reflects_limits_of_class]; the
 form over a class of shapes S is the one over [fun J _ => S J],
 through [ReflectsLimitConesOfClass_Over], at [eq_refl], C27), and
 the colimit side goes by the opposite
 ([conservative_reflects_colimit] and its four forms; C28).  This
 is the reflection half of Riehl's 3.4.iii and, at the walking
 parallel pair, Mac Lane's Exercise 3.
 - Riehl's Exercise 3.4.iii: [preserves_conservative_creates_limit]
 is a [CreatesLimit K F] whose lift of every limiting cone
 downstairs is the given limit upstairs ([eq_refl], C4), whose
 comparison is [limitcone_iso] of two limiting cones over F ◯ K,
 and whose reflection is the theorem above.  For a class of
 diagrams, as the exercise states it,
 [preserves_conservative_creates_limits_of_class]: if C has the
 limits of the diagrams of the class, F preserves them and F
 reflects isomorphisms, F creates them.  For a class of shapes S,
 [preserves_conservative_creates_limits_over], consuming
 Preservation.v's [PreservesLimitConesOver]; it is the form over
 [fun J _ => S J], pointwise at [eq_refl] (C29).  On the
 colimit side, [preserves_conservative_creates_colimit] per
 diagram and [preserves_conservative_creates_colimits_of_class]
 for a class of diagrams.
 - Coequalizers.  [ReflectsCoequalizers F] is Mac Lane's “in
 particular” over the tree's elementary [IsCoequalizer]
 (Structure/Coequalizer.v): a fork e ∘ f ≈ e ∘ g in C whose image
 is a coequalizer in D is a coequalizer in C.
 [PreservesCoequalizers F] is the dual of Structure/Limit/
 FromProducts.v's [PreservesEqualizers]; [CreatesCoequalizers F]
 is Creation.v's [CreatesColimit] at every diagram of
 parallel-pair shape, a cocone-level predicate and not an
 elementary one.  The elementary and cone-level readings
 agree both ways ([ReflectsCoequalizers_ReflectsColimitCocones]
 and its converse, [PreservesCoequalizers_PreservesColimitCocones]
 and its converse), through Structure/Coequalizer.v's conversions
 at a diagram of parallel-pair shape (#477) and the converse for a
 given cocone added there by this issue
 ([parallel_cocone_coequalizer_colimit]): an image cocone is a
 cocone over F ◯ K, whose pair and whose injection over ParY are
 the images of K's, by conversion.  The two converses use their
 hypothesis only at the diagrams [APair f g], so they are stated
 per parallel pair
 ([ReflectsColimitCocones_ReflectsCoequalizers_of_pairs],
 [PreservesColimitCocones_PreservesCoequalizers_of_pairs]), the
 forms over every diagram of parallel-pair shape being their
 restrictions.
 - Exercise 1, per parallel pair as the book states it (its
 “coequalizers” are “coequalizers of parallel pairs”):
 [creates_reflects_coequalizers_of_pairs], from the tree's creation
 at every [APair f g], and [maclane_creates_reflects_coequalizers],
 from Mac Lane's, by his argument; [creates_reflects_coequalizers],
 from [CreatesCoequalizers], is the first at the restriction of its
 hypothesis (C17, at [eq_refl]).  Exercise 3:
 [conservative_reflects_coequalizers], from [HasCoequalizers C],
 [PreservesCoequalizers F] and [ReflectsIsos F]; it IS the
 cone-level theorem at the walking parallel pair, read back
 through the bridges (C5, at [eq_refl]), its colimits chosen by
 Coequalizer.v's [HasCoequalizers_HasColimitsOfShape].
 - Riehl's Lemma 3.4.5 is in Theory/Equivalence/Limit.v, beside the
 limit half [ff_reflects_limit] that it completes:
 [ff_reflects_colimit] in that apex-pinned form, and
 [ff_ReflectsLimitCone] and [ff_ReflectsColimitCocone] at cone
 level, which give [ReflectsAllLimits] and [ReflectsAllColimits]
 of every full and faithful functor (C8, C9).

 EXERCISE 1, UNDER BOTH READINGS OF CREATION.  Mac Lane's creation
 (the unnumbered Definition of §V.1, p. 112) asks for exactly one lift
 of each limiting cone, and with it Exercise 1 is immediate: a cone
 upstairs whose image is limiting is a lift of that image, hence the
 unique lift, which is limiting.  Creation.v's [CreatesLimit] does not
 carry that uniqueness as a field (its UNIQUENESS OF THE LIFT; the
 on-the-nose clause is refuted for [EM_Forget] at the identity monad
 on [Sets], #467) and carries reflection instead, so under the tree's
 creation Exercise 1 is that field read through the bridge
 ([creates_reflects_coequalizers_of_pairs]).  A field must hold of
 every creation the tree builds; a hypothesis need not, so
 [MacLaneCreatesLimit] states the book's clauses as a predicate on a
 functor, and [maclane_creates_reflects_coequalizers] is Exercise 1
 under it, by the book's argument through Creation.v's [self_lift].
 Both are per parallel pair.  The constants of Mac Lane's reading sit
 here and not in Creation.v: they consume only names Creation.v
 exports, their one consumer is this file's Exercise 1, and Creation.v
 stays as it was.

 EXERCISE 3'S CONSERVATIVITY IS NEEDED.  Instance/One.v's [Erase Sets],
 the functor from [Sets] to the point, preserves coequalizers, every
 fork in the point being a coequalizer, and [Sets] has them
 (Instance/Sets/Coequalizer.v's [Sets_HasCoequalizers]).  It does not
 reflect them: on the two-element setoid the fork of the identity,
 twice, with the map ! onto the singleton becomes a coequalizer in the
 point and is none in [Sets].  So by Exercise 3 it is not conservative
 (the probe, C13 to C16).  The three hypotheses do hold together, at
 the identity on [Sets], which Exercise 3 then shows reflects
 coequalizers (C22).

 THE OPPOSITE.  [ReflectsLimitCone (K^op) (F^op)] is not
 [ReflectsColimitCocone K F]: the probe's R1 is refused at conversion,
 under its import list with “(cannot unify ”Cone (F^op ◯ K^op)“ and
 ”Cone (F ◯ K)^op“)”, the two functors being distinct records
 (Preservation.v); so every colimit statement here reads its image
 cocone through [islimitcone_op_comp], and C3 converts in one line.

 STRENGTHS.  At [eq_refl], restated in the probe: Mac Lane's
 definition as [ReflectsColimitCocone] (C1), Exercise 1 at cone level
 as the creation's field (C2), the lift of 3.4.iii (C4), Exercise 3 as
 the cone-level theorem (C5), [ff_ReflectsLimitCone] as
 [ff_reflect_ump] (C10), Exercise 1 over every diagram of
 parallel-pair shape as the per-pair theorem at the restriction of its
 hypothesis (C17), the maps between the forms over a class of shapes
 and over a class of diagrams as each other's inverses (C23 to C26),
 and the conservative reflection and Riehl's 3.4.iii over a class of
 shapes as their forms over a class of diagrams (C27 to C29).  The
 universal properties hold at the categories' own ≈.  Every new
 constant is transparent, a term or closed [Defined]; the one [Qed] of
 this issue is the probe's C15.

 UNIVERSES, read off [About] for every name on Rocq 9.1.1.  No block
 carries an equation, and none mentions [Set].  The cone-level names
 bind J, C and D at one hom level, as the in-tree predicates they
 state already do ([ReflectsLimitCone], [ReflectsColimitCocone] and
 [CreatesLimit] each bind all three at one hom level), and so does
 [MacLaneCreatesLimit], stated over [Cone] and [StrictLift];
 [ReflectsIsos_op] binds C and D at the one hom level of [ReflectsIsos],
 and the full and faithful names at the one hom level of [Full].
 [ReflectsCoequalizers] and [PreservesCoequalizers] are
 [@{co ch do dh u}] with ch <= dh, [Functor]'s own bound (h1 <= h2):
 their binders are written out, and the probe accepts both with ch < dh
 strict (C6, C7), while [ReflectsIsos] is refused there (R2,
 “Cannot enforce dh = ch because ch < dh”).  So Exercises 1 and 3 hold
 at C's hom level, and the tie is a minimization artifact, twice over.
 First, the classes of their hypotheses leave their binders to Rocq,
 which identifies the two hom levels: [ReflectsIsos] with its binders
 written out is accepted with ch < dh (C18, C19) and is the class at
 one level (C20), and [Full] and [Faithful], each refused there, are
 each accepted with their binders written out (measured in a scratch
 file, not pinned).  Second, and independently, the route through the
 cone level ties them: [ReflectsColimitCocone], [CreatesColimit] and
 [MacLaneCreatesColimit] at a pair, and [PreservesColimitCoconesOfShape]
 at [Parallel], are each refused with ch < dh, with R2's message, and
 with the annotated [ReflectsIsos] Exercise 3 by this route is refused
 there at its first cone-level step (measured in a scratch file, not
 pinned).  The cone vocabulary is on #1363's list of such carriers.
 Lifting Exercise 3 above C's hom level would take [ReflectsIsos]
 annotated together with #1363's carriers, or a direct elementary
 proof over the annotated class; lifting Exercise 1 would take #1363's
 carriers, creation being cone-level.  Caps: [Projections] on the
 twenty-seven names whose terms reach Preservation.v's
 [limitcone_transport], whose own block carries them, as do the blocks
 of the cone-isomorphism lemmas before it ([coneiso_from],
 [ConeIso_sym]); and [False_rect] on the eight whose terms reach
 Instance/Parallel.v's [APair], whose own block carries it.  Two first
 drafts were rejected by measurement:
 [conservative_reflects_limit] stated in a Section carried four
 equations from the Section's [Context] (u0 = u2, u0 = u4, u2 = u4,
 u6 = u8), none at top level; and a converse bridge through
 Coequalizer.v's [is_coequalizer_cocone_ump], read as an
 [IsColimitCocone] of the cofork cocone, bounded the walking pair's
 object level by C's hom level (po <= ch, carried by that ascription
 alone, measured), where [parallel_coequalizer_colimit] leaves it
 free.  On Coq 8.19.2 and 8.20.1 ([About] in source overlays of the
 dependency closure of this issue's changed files, with the probe and
 a scratch file, 105 files each) every name binds as many levels, at
 the same type, under the same constraints apart from standard-library
 caps; the two versions agree with each other; and the caps differ
 from 9.1.1's on 56 of the 59 names ([eq], [sigT], [Specif] and
 [Logic] universes there), none of it an equation.  Only the printing
 of 8.19.2 differs: in five names it shows the implicit binders that
 follow an arrow in parentheses.  No explicit universe instance of a
 new constant is written.

 CLOSURE.  The [Require]s load 35 [Category] modules, this one
 included ([Print Libraries]); Theory/Morphisms/CokernelPair.v, which
 only [ReflectsIsos_op] uses, accounts for 7 of them.  The shared route
 is taken at that cost.

 STALE PREMISES, dated from gh.  Issue #481 (filed 2026-07-23; the
 three Riehl sections appended 2026-07-31) says that only the
 isomorphism case of reflection is first-class, “reflects colimits”
 existing only as the unfolded conclusion of theorems about full and
 faithful functors and equivalences; that creation implies reflection
 only for isomorphisms, from U-split creation; that a search for
 “CreatesLimit|ReflectsLimit” returns nothing; and that
 Functor/Opposite.v mentions neither [Full] nor [Faithful].  Each was
 accurate when written and is stale since PR #1083 (merged 2026-08-13:
 [CreatesLimit], [ReflectsLimitCone] and [creates_reflects_limits],
 which also gives the reflection of colimits read in the opposite
 category), PR #1087 (merged 2026-08-14: [ReflectsColimitCocone]) or
 PR #1108 (merged 2026-08-15: [Full_op], [Faithful_op] and their
 converses).  Its line citations are replaced by names here.  The
 quantified predicates, Exercise 3, Riehl's 3.4.iii, the elementary
 coequalizer predicates and [ff_reflects_colimit] were absent until
 this change: a sweep of the tree's .v and .glob files for the 59
 names (instrumented: [IsLimitCone] found, a made-up name not) finds
 them only in this file, the probe, the declarations and prose this
 change adds to Structure/Coequalizer.v and Theory/Equivalence/Limit.v,
 the three proof bodies it routes through [ff_ReflectsLimitCone] with
 their CORRECTION notes, and Adjunction/Continuity/Equalizer.v, whose
 sentence that no [PreservesCoequalizers] exists carries a CORRECTION
 (#481) in place, which names the bridge
 [PreservesColimitCocones_PreservesCoequalizers].

 DUPLICATES, UNIFIED AND KEPT.  Three constants of the tree wrote out
 [ff_ReflectsLimitCone]'s term at their own functors, and each reads
 back as it at [eq_refl] (measured): Theory/Equivalence/Creation.v's
 [equivalence_ReflectsLimitCone], Construction/Subcategory/Creation.v's
 [sub_ReflectsLimitCone] and Construction/Reflective/Limit.v's
 [reflective_ReflectsLimitCone].  Each body now calls it, eta-expanded,
 with a CORRECTION (#481) in place, and the [About] blocks of all 38
 constants of the three files are unchanged (compared by script).  Two
 others state special cases of new constants and are not convertible
 with them, their readbacks at [eq_refl] being refused (“cannot
 unify”, measured): Structure/Coequalizer/Absolute.v's
 [image_coequalizer_colimit], against
 [parallel_cocone_coequalizer_colimit] at [T ◯ APair f g], and
 Theory/Equivalence/Limit.v's [equivalence_reflects_colimits], against
 [ff_reflects_colimit], its fullness and faithfulness of F^op being
 those of the opposite equivalence and not [Full_op] and [Faithful_op]
 of F's.  Re-routing either would change its term, so both are kept as
 they are, for the maintainer to decide.

 NOT DELIVERED.  A functor other than the identity that creates in
 Mac Lane's literal sense: the on-the-nose uniqueness is refuted for
 [EM_Forget] at the identity monad on [Sets] (#467), and
 [id_maclane_creates] at the opposite diagram is a creation along
 [Id[C^op]], which Rocq does not accept where one along [Id[C]^op] is
 expected, so it gives no instance of
 [maclane_creates_reflects_coequalizers] (measured).  Creation
 transported along an isomorphism of diagrams, which would give the
 hypothesis of [creates_reflects_coequalizers] from that of its
 per-pair form.  Reflection relative to a class of pairs in the
 elementary form (at cocone level it is [ReflectsColimitCoconesOfClass]
 at a class of diagrams of parallel-pair shape), which the section's
 Exercises 5 and 6 use, Beck's U-split pairs among them
 (Monad/Monadicity/Beck.v's [CreatesUSplitCoequalizers] yields
 [creates_split_reflects_isos] and not the reflection of the
 coequalizers of U-split pairs).  A [PreservesColimitCoconesOver]
 beside Preservation.v's limit-side [PreservesLimitConesOver]: the
 colimit form of reflection over a class of shapes takes its
 preservation shape by shape, and 3.4.iii on the colimit side has no
 form over a class of shapes of its own, being stated per diagram and
 over a class of diagrams.  A witness of Exercise 3's conclusion at a
 functor that is neither an equivalence nor full and faithful; the
 probe shows its conservativity hypothesis is needed (C13 to C16), not
 the other two.  The elementary Exercises at a target hom level above
 C's (UNIVERSES). 

 --------
 书籍： Mac Lane，《为工作中的数学家准备的范畴论》，第2版，Springer GTM 5, 1998, §VI.7 “Beck 定理”：反射余极限的定义，印刷页154（PDF页163） — maclane:VI.7:def2；练习1，页154（PDF页163） — maclane:VI.7:ex1；练习3，页155（PDF页164） — maclane:VI.7:ex3
 书籍： Riehl，《上下文中的范畴论》，第2版，§3.4：定义3.4.1 (ii)，印刷页104（PDF页124） — riehl:3.4:def1；引理3.4.5，页105（PDF页125） — riehl:3.4:lem5；练习3.4.iii，页108（PDF页128） — riehl:3.4:exiii
 nLab: https://ncatlab.org/nlab/show/reflected+limit
 nLab: https://ncatlab.org/nlab/show/conservative+functor书中所述，阅读页图像。Mac Lane，第154页：
 “定义。当对于每个锥 λ : T →· a，从 T 到 a ∈ A，如果 Gλ : GT →· Ga 是 X 中的余极限锥，则 λ 已经是 A 中的余极限锥时，函子 G : A → X 反映 T : J → A 的余极限。特别地，当 A 中的每个分叉在 X 中成为等化器时，它已经是 A 中的等化器，则 G 反映等化器。类似地，当对于 A 中的所有箭头 t，如果 Gt 是同构，则 t 也是同构时，G 反映同构。”练习部分开头说明“（始终，“等化器”指“平行对的等化器”）”；“1. 如果 G 生成等化器，证明它也反映等化器。”；第155页，“3。”（练习 2 的替代假设。）如果 A 具有所有的等化子，G 保留所有的等化子，并且 G 能反映同构，证明 G 能反映所有等化子。Riehl，第 104 页：F “反映 K 的极限，如果每个 K 上的锥，其在 F 下的像是图 FK 的极限锥，则该锥是 K 上的极限锥”，以及“更常见的是，我们谈论一个函子保留、反映或创建一类图的极限，例如特定形状或大小的图。定义 3.4.1 进行对偶化……”；第 105 页，引理 3.4.5：“任何完全且忠实的函子都能反映其伴随域中存在的任何极限和余极限。”；第 108 页，练习 3.4.iii：“证明 F : C → D 为某一类特定的图创建极限，如果以下两条成立：(i) C 拥有这些极限且 F 保留它们。”(ii)
 F : C → D 反映同构。已经在树中。按照 Mac Lane 的定义，根据图表和锥层面，见 Structure/Limit/Preservation.v 的 [ReflectsColimitCocone K F]（PR #1087，于 2026-08-14 合并，用于 #427）：K 上的一个余锥 N，其在 F 下的像余锥 [FCocone F N]，即 N 的注入，是共极限的，也自身是共极限（探针读取它，C1）。Riehl 的 3.4.1 (ii) 在旁边是 [ReflectsLimitCone K F]（PR #1083，于 2026-08-13 合并，用于 #406；由 #1087 移动到那里），同构的反射是类 [ReflectsIsos]。在极限方面，创建给出 Structure/Limit/Creation.v 的 [creates_reflects_limits] (#1083) 的反射。Riehl 3.4.5 的共极限部分所需的传输 [Full_op] 和 [Faithful_op] 都在 Functor/Opposite.v 中（PR #1108，于 2026-08-15 合并，用于 #266）。名称 [ReflectsLimit]，Creation.v 在此问题中未使用，仍然未使用：[ReflectsLimitCone] 是该谓词，第二个名称将会是重复的。这里是什么。——对一个形状、一类形状、一类图表以及每个图表进行反思，这些图表的形状像 Preservation.v 的 [PreservesLimitConesOfShape] 和 [PreservesLimitConesOver]，以及 Creation.v 的 [CreatesAllLimits]、[ReflectsLimitConesOfShape]、[ReflectsLimitConesOver]、[ReflectsLimitConesOfClass]、[ReflectsAllLimits]，以及余极限的双胞胎 [ReflectsColimitCoconesOfShape]、[ReflectsColimitCoconesOver]、[ReflectsColimitCoconesOfClass]、[ReflectsAllColimits]。该问题的 [ReflectsLimits] 和 [ReflectsColimits] 是 [All] 形式，被命名为 [CreatesAllLimits]。[ReflectsAllLimits_Over] 及其双胞胎从每个图表传递到任何一类形状。一类形状是对范畴的谓词，因此 Structure/Limit/Finite.v 的 [FiniteCategory] 是 Riehl 的“所有有限形状”（探针，C11 和 C12）。一类图表，Riehl 自己的量词，是对每种形状 J 的图表 K : J ⟶ C 的谓词，而一类形状 S 是这些形状的所有图表的类，[fun J _ => S J] ：[ReflectsLimitConesOver_OfClass] 和 [ReflectsLimitConesOfClass_Over] 以 S 上的形式到 [fun J _ => S J] 上的形式并返回，它们在 [eq_refl] 处互为逆 (C23, C24)，它们的余极限双也如此 (C25, C26)。- [ReflectsIsos_op] ：保守函子（conservative functor）的对偶（opposite）是保守的，C^op 的同构是 C 的同构，其两条定律互换 (Theory/Morphisms/CokernelPair.v 的 [IsIsomorphism_of_op] 和 [op_IsIsomorphism_of])。- 创建在余极限方面给出反射：
 [creates_reflects_colimits] 是 [CreatesColimit K F] 的反射域，即沿 [F^op] 的 [K^op] 的 [CreatesLimit] ，通过 Preservation.v 的 [islimitcone_op_comp] 读取 (F ◯ K)^op 在 F^op ◯ K^op 上的像余圆锥，于 [eq_refl] 处；[creates_reflects_all_limits] 和 [creates_reflects_all_colimits] 进行量化。- Mac Lane 的创建，逐字读取（§V.1，第112页）：
 [MacLaneCreatesLimit K F] 将 F ◯ K 上的每一个极限圆锥 N 提升为严格提升（Creation.v 的 [StrictLift]：像顶点等于 N 的顶点，像腿在该等式下近似于 N 的腿），该提升是极限的，并等于 N 的每一个其他严格提升，顶点由 [=] 决定，腿由 ≈ 沿其决定。根据 Mac Lane 自己的论证（[maclane_creates_reflects]）它给出了反射：楼上的一个圆锥，其像是极限，是该像的严格提升（Creation.v 的 [self_lift]），所以它就是提升，是极限。因此它映射到树的创造中（[maclane_CreatesLimit]，其反射场定理），它适用于恒等映射（[id_maclane_creates]），并且 [MacLaneCreatesColimit] 是它的余极限方面，通过对偶。在相同条款的同构不变解读中，一个极限且唯一的提升（至圆锥同构）在一行中给出了反射（[iso_unique_lift_reflects]）；Creation.v 的 [creates_limiting] 和 [creates_lift_unique] 从反射场和提升的比较中得出这两个条款，因此对于一个带比较的提升，场和这两个条款可以相互推出。- 一个保守函子反映它所保持的极限：
 [conservative_reflects_limit]  将一个关于 K 的极限锥 L 映射，其像是极限。对于一个其像是极限的锥 M，从 M 到 L 的中介态 u 使得 F u 与像的各个腿交换，因此 F u 是两个极限像锥的比较，并且可逆 ([limitcone_iso])；F 反映了这一点，并且沿着锥同构 u 传输，M 是极限 ([limitcone_transport])。[preserves_conservative_reflects_limit] 是书中的形式（K 的一个极限，F 保持它），以及它在某一形状上、某一形状类上和某一图类上的形式 ([preserves_conservative_reflects_limits_of_class]；形状类 S 上的形式是  [fun J _ => S J] 上的形式，通过 [ReflectsLimitConesOfClass_Over]，在 [eq_refl]，C27)，而余极限边则按照相反方式进行 ([conservative_reflects_colimit] 及其四种形式；C28)。这是 Riehl 的 3.4.iii 的反射部分，在行走平行对下，是 Mac Lane 的练习 3。——Riehl 的练习 3.4.iii：[preserves_conservative_creates_limit] 是一个 [CreatesLimit K F]，其每个底下极限锥的提升都是上面的给定极限（[eq_refl]，C4），其比较是 ZZ W68WZZ 的两个 F ◯ K 上极限锥的比较，其反射是上面的定理。对于一类图，如练习所述，[preserves_conservative_creates_limits_of_class]：如果 C 拥有该类图的极限，F 保持它们并且 F 反映同构，则 F 创建它们。对于一类形状 S，[preserves_conservative_creates_limits_over]，使用 Preservation.v 的 [PreservesLimitConesOver]；它是 [fun J _ => S J] 上的形式，在 [eq_refl] 处逐点（C29）。在余极限方面，[preserves_conservative_creates_colimit] 对每个图而言，[preserves_conservative_creates_colimits_of_class] 针对一类图。—等化器。[ReflectsCoequalizers F] 是 Mac Lane 的“特别地”关于树的基本 [IsCoequalizer] （Structure/Coequalizer.v）：在 C 中一个分叉 e ∘ f ≈ e ∘ g，其像在 D 中是等化器，则在 C 中也是等化器。[PreservesCoequalizers F] 是 Structure/Limit/FromProducts.v 的 [PreservesEqualizers] 的对偶；[CreatesCoequalizers F] 是 Creation.v 中 [CreatesColimit]，在每个平行对形状的图上，是一个余锥层谓词，而非基本谓词。小学和锥级读数在两个方向上都一致（[ReflectsCoequalizers_ReflectsColimitCocones]及其逆，[PreservesCoequalizers_PreservesColimitCocones]及其逆），通过Structure/Coequalizer.v在平行对形状图#477的转换，以及通过这个问题在其中添加的给定余锥的逆（[parallel_cocone_coequalizer_colimit]）：象余锥是F ◯ K上的余锥，其对和在ParY上的注入是通过转换得到的K的象。两个逆仅在图[APair f g]处使用它们的假设，因此它们按平行对表述（[ReflectsColimitCocones_ReflectsCoequalizers_of_pairs]，[PreservesColimitCocones_PreservesCoequalizers_of_pairs]），在每个平行对形状图上的形式是它们的限制。- 练习1，按书中所述每组平行对（它的“共同等化器”是“平行对的共同等化器”）：
 [creates_reflects_coequalizers_of_pairs]，从树的创建时
 在每个 [APair f g] 和 [maclane_creates_reflects_coequalizers]，
 根据 Mac Lane 的论证；ZW91WZZ，
 从 [CreatesCoequalizers]，是在其假设的限制下的第一个（C17，在 [eq_refl]）。练习3：
 [conservative_reflects_coequalizers]，从 [HasCoequalizers C]，
 [PreservesCoequalizers F] 和 [ReflectsIsos F]；它是
 在移动平行对处的锥级定理，通过桥梁回读（C5，在 [eq_refl]），其余极由 Coequalizer.v 的 [HasCoequalizers_HasColimitsOfShape] 选择。- Riehl 的引理 3.4.5 在 Theory/Equivalence/Limit.v 中，位于它完成的极限部分 [ff_reflects_limit] 旁边：[ff_reflects_colimit] 在那个顶点固定的形式下，以及在锥层次的 [ff_ReflectsLimitCone] 和 [ff_ReflectsColimitCocone]，这给出了每个全忠实函子 (C8, C9) 的 [ReflectsAllLimits] 和 [ReflectsAllColimits]。练习 1，在创造的两种理解下。Mac Lane 的创造（第 V.1 节无编号定义，第 112 页）要求每个极限锥恰好升起一次，因此练习 1 很直接：楼上的一个锥，其像是极限锥，即是该像的升起，因此是唯一的升起，而它是极限的。Creation.v 的 [CreatesLimit] 并没有作为字段承载该唯一性（它的升起唯一性；对于 [EM_Forget] 在 [Sets] 上的恒等 monad，精确条款被驳斥，#467），而是承载了反射性，因此在树的创造下，练习 1 就是通过桥（[creates_reflects_coequalizers_of_pairs]）读取该字段。一个域必须包含树所构建的每一个创造；假设则不必如此，所以 [MacLaneCreatesLimit] 将书中的条款作为函子上的谓词陈述，而 [maclane_creates_reflects_coequalizers] 是其下的练习 1，按照书中通过 Creation.v 的 [self_lift] 的论证。两者都是按平行对排列。Mac Lane 阅读的常量位于此处，而不在 Creation.v：它们只消耗 Creation.v 导出的名称，它们的唯一消费者是此文件的练习 1，而 Creation.v 保持原样。练习 3 的保守性是必要的。Instance/One.v 中的 [Erase Sets]，从 [Sets] 到点的函子，保持余等化器，每个在点中的叉都是一个余等化器，并且 [Sets] 有它们（Instance/Sets/Coequalizer.v 中的 [Sets_HasCoequalizers]）。它不反映它们：在两个元素的等价集合上，恒等映射的叉，两次，与映射 ! 到单元素集，在点中成为一个余等化器，而在 [Sets] 中则不是。所以根据练习 3，它不是保守的（探针，从 C13 到 C16）。这三个假设在 [Sets] 上的恒等映射同时成立，练习 3 随后显示它反映余等化器（C22）。相反。[ReflectsLimitCone (K^op) (F^op)] 不是 [ReflectsColimitCocone K F]：探针的 R1 在转换时被拒绝，在其导入列表中显示“(无法统一 'Cone (F^op ◯ K^op)' 和 'Cone (F ◯ K)^op')”，这两个函子是不同的记录 (Preservation.v)；因此此处的每个余极限语句都通过 [islimitcone_op_comp] 读取其像余圆锥，并且 C3 在一行中转换。优势。在 [eq_refl] 中，在探针中重述：Mac Lane 的定义作为 [ReflectsColimitCocone]（C1），圆锥层次的练习 1 作为创造的场（C2），3.4.iii 的提升（C4），练习 3 作为圆锥层次定理（C5），[ff_ReflectsLimitCone] 作为 [ff_reflect_ump]（C10），每个平行对形状图上的练习 1 作为其假设限制下的每对定理（C17），形状类和图类之间的形式映射作为彼此的逆（C23 到 C26），以及保守反射和 Riehl 的 3.4.iii 在形状类上的形式作为它们在图类上的形式（C27 到 C29）。普遍性质在类别自身 ≈ 上成立。每个新常数都是透明的，一个项或闭合 [Defined]；本期的唯一 [Qed] 是探针的 C15。宇宙，对 Rocq 9.1.1 上的每个名字读取 [About]。没有块包含方程，也没有提到 [Set]。锥形层级的名字在一个同伦层级上绑定 J、C 和 D，就像它们所陈述的树内谓词已经做的那样（[ReflectsLimitCone]、[ReflectsColimitCocone] 和 [CreatesLimit] 都在一个同伦层级上绑定三者），[MacLaneCreatesLimit] 也同样如此，它是在 [Cone] 和 [StrictLift] 上声明的；[ReflectsIsos_op] 在 [ReflectsIsos] 的同伦层级上绑定 C 和 D，而在 [Full] 的同伦层级上绑定完整且忠实的名字。[ReflectsCoequalizers] 和 [PreservesCoequalizers] 是 [@{co ch do dh u}] 且 ch <= dh，[Functor] 自身绑定（h1 <= h2）：它们的绑定器被写出，探针接受 ch < dh 严格（C6，C7），而 [ReflectsIsos] 在那里被拒绝（R2，“无法强制 dh = ch 因为 ch < dh”）。因此，练习1和3在C的同伦层次上成立，而平局是一个最小化工件，有两方面含义。首先，它们假设的类将它们的绑定器留给Rocq，这确定了两个同伦层次：[ReflectsIsos]及其写出的绑定器在ch < dh（C18, C19）情况下被接受，并且在一个层次上的类为C20，而[Full]和[Faithful]，每个在此处被拒绝，每个在写出它们的绑定器后被接受（在临时文件中测量，而非固定）。第二，并且是独立的，通过锥层的路径使它们绑定：[ReflectsColimitCocone], [CreatesColimit]和[MacLaneCreatesColimit]作为一对，[PreservesColimitCoconesOfShape]在[Parallel]上，每个在ch < dh的情况下被拒绝，带有R2的消息，以及带注释的[ReflectsIsos]。通过这条路径，练习3在其第一个锥层步骤处被拒绝（在临时文件中测量，而非固定）。锥体词汇在 #1363 的此类承载者列表中。将上文中的练习 3 提升到 C 的同质水平需要 [ReflectsIsos] 与 #1363 的承载者一同注释，或在注释后的类上作直接的基础证明；提升练习 1 则需要 #1363 的承载者，创建仍处于锥体级别。Caps：[Projections] 在二十七个其项到达 Preservation.v 的 [limitcone_transport] 的名称上，其自身块承载它们，锥体同构引理之前的块也承载它们（[coneiso_from]，[ConeIso_sym]）；以及 [False_rect] 在八个其项到达 Instance/Parallel.v 的 [APair] 的名称上，其自身块承载它。两个初稿因测量而被拒绝：[conservative_reflects_limit] 在某一节中列出了四个来自该节的方程 [Context]（u0 = u2，u0 = u4，u2 = u4，u6 = u8），没有任何在顶层；并且通过 Coequalizer.v 的 [is_coequalizer_cocone_ump] 构成逆桥，作为共叉锥的 [IsColimitCocone] 读取，将步游对象的级别由 C 的同态级别限制（po <= ch，仅由该归属携带，已测量），而 [parallel_coequalizer_colimit] 将其保持自由。在 Coq 8.19.2 和 8.20.1（在该问题更改文件的依赖闭包的源覆盖中使用 [About]，并使用探针和一个临时文件，每个 105 个文件）中，每个名称在相同类型下，在相同约束下（标准库 caps 除外）绑定同样的层级；两个版本彼此一致；而 caps 在 59 个名称中的 56 个与 9.1.1 的不同（那里是 [eq]、[sigT]、[Specif] 和 [Logic] 宇宙），其中没有任何一个是方程。只有 8.19.2 的打印方式不同：在五个名称中，它以括号显示箭头之后的隐式绑定变量。没有新常量的显式宇宙实例被写入。闭包。[Require] 载入 35 个 [Category] 模块，包括这个 ([Print Libraries])；Theory/Morphisms/CokernelPair.v，仅被 [ReflectsIsos_op] 使用，占其中 7 个。共享路径以该成本被采用。陈旧前提，摘自 gh. 第 481 期（归档于 2026-07-23；三部分 Riehl 章节附加于 2026-07-31）指出，只有反射的同构情况属于一等，‘反映余极限’仅存在于关于全忠实函子和等价的定理展开结论中；创建仅对同构意味着反射，这是由 U-分裂创建得出；搜索“CreatesLimit|ReflectsLimit”没有结果；并且 Functor/Opposite.v 中既未提及 [Full]，也未提及 [Faithful]。每条在撰写时都是准确的，自 PR #1083（于 2026-08-13 合并：[CreatesLimit]、[ReflectsLimitCone] 和 [creates_reflects_limits]，这也给出了在相反范畴中读取的余极限的反射）、PR #1087（于 2026-08-14 合并：[ReflectsColimitCocone]）或 PR #1108（于 2026-08-15 合并：[Full_op]、[Faithful_op] 及其对偶）之后就已过时。其行引用在此处已被名称取代。量化谓词、练习 3、Riehl 的 3.4.iii、基本等化器谓词和 [ff_reflects_colimit] 在此更改之前都不存在：对树的 .v 和 .glob 文件中 59 个名称进行扫描（已插入工具：[IsLimitCone] 找到，虚构名称未找到）只在此文件、探针、声明以及此更改添加到 Structure/Coequalizer.v 和 Theory/Equivalence/Limit.v 的文章中找到它们，通过 [ff_ReflectsLimitCone] 路由的三个证明主体及其 CORRECTION 注释，以及 Adjunction/Continuity/Equalizer.v，其中关于不存在 [PreservesCoequalizers] 的句子携带了 CORRECTION (#481) 替代，并命名了桥 [PreservesColimitCocones_PreservesCoequalizers]。重复项，统一且保留。树的三个常量在它们各自的函子上写出了 [ff_ReflectsLimitCone] 的项，并且每个都在 [eq_refl]（已测量）中读取：Theory/Equivalence/Creation.v 的 [equivalence_ReflectsLimitCone]，Construction/Subcategory/Creation.v 的 [sub_ReflectsLimitCone] 和 Construction/Reflective/Limit.v 的 [reflective_ReflectsLimitCone]。每个主体现在都调用它，进行了 eta 展开，并且应用了修正 (#481)，三个文件的所有 38 个常量的 [About] 块保持不变（通过脚本比较）。另外两个陈述了新常数的特殊情况，并且不能与它们互换，它们在 [eq_refl] 的读取被拒绝（“不能统一”，已测量）：Structure/Coequalizer/Absolute.v 的 [image_coequalizer_colimit] ，对比 [parallel_cocone_coequalizer_colimit] 于 [T ◯ APair f g]，以及 Theory/Equivalence/Limit.v 的 [equivalence_reflects_colimits] ，对比 [ff_reflects_colimit]，它的 F^op 的完全性和忠实性是对偶等价的，而不是 F 的 [Full_op] 和 [Faithful_op]。重新路由任一项都会改变其项，因此两者保持原状，由维护者决定。未交付。一个除了恒等函子之外的函子，它在Mac Lane字面意义上创建：对于[EM_Forget]，在[Sets]上的恒等幺半群中瞬时唯一性被否定；而[id_maclane_creates]在对立图上沿[Id[C^op]进行创建，Rocq不接受这一点，而期望沿[Id[C] ^op进行，因此它没有给出[maclane_creates_reflects_coequalizers]（已测量）的实例。沿图的同构传递创建，这会从其成对形式的假设得到[creates_reflects_coequalizers]的假设。相对于一类成对对象的反射，在初等形式中（在余锥层次上是 [ReflectsColimitCoconesOfClass]，在一类平行对形状的图中），本节的练习 5 和 6 使用了它，其中包括 Beck 的 U-分割对（Monad/Monadicity/Beck.v 的 [CreatesUSplitCoequalizers] 产生 [creates_split_reflects_isos]，而不是 U-分割对的余等化子的反射）。在 Preservation.v 的极限侧旁边是一个 [PreservesColimitCoconesOver]：在一类形状上的反射的余极限形式按形状逐个获取其保持形式，而余极限侧的 3.4.iii 没有属于自身的一类形状的形式，它是针对每个图和一类图陈述的。在一个既不是等值也不是满且忠实的函子上，观察练习3的结论；探针显示需要其保守性假设（C13到C16），而不是另外两个。在高于C的目标同层次（宇宙）上的初等练习。
*)

(* * ** Reflection over a shape, a class of shapes or diagrams, and all / * ** 对一个形状、一类形状或图表以及所有的反射 *)

Definition ReflectsLimitConesOfShape (J : Category) {C D : Category}
  (F : C ⟶ D) : Type := ∀ K : J ⟶ C, ReflectsLimitCone K F.

Definition ReflectsLimitConesOver {C D : Category} (S : Category → Type)
  (F : C ⟶ D) : Type :=
  ∀ J : Category, S J → ∀ K : J ⟶ C, ReflectsLimitCone K F.

(*
 Over a class of diagrams, Riehl's own quantifier: a predicate on the
 diagrams K of every shape J.  A class of shapes S is the class of all
 diagrams of those shapes, [fun J _ => S J], and the two forms agree up
 to the order of their arguments, by the two maps below, each the
 other's inverse at [eq_refl] (the probe, C23 and C24). 

 --------
 在一类图上，Riehl 自己的量词：对每种形状 J 的图 K 的谓词。形状类 S 是那些形状的所有图的类，[fun J _ => S J]，并且这两种形式在参数顺序上是一致的，通过下面的两个映射，每个映射在 [eq_refl] 上都是对方的逆（探针，C23 和 C24）。
*)

Definition ReflectsLimitConesOfClass {C D : Category}
  (S : ∀ J : Category, (J ⟶ C) → Type) (F : C ⟶ D) : Type :=
  ∀ (J : Category) (K : J ⟶ C), S J K → ReflectsLimitCone K F.

Definition ReflectsLimitConesOver_OfClass {C D : Category}
  {S : Category → Type} {F : C ⟶ D} (H : ReflectsLimitConesOver S F) :
  ReflectsLimitConesOfClass (fun J _ => S J) F :=
  fun J K HJ => H J HJ K.

Definition ReflectsLimitConesOfClass_Over {C D : Category}
  {S : Category → Type} {F : C ⟶ D}
  (H : ReflectsLimitConesOfClass (fun J _ => S J) F) :
  ReflectsLimitConesOver S F :=
  fun J HJ K => H J K HJ.

Definition ReflectsAllLimits {C D : Category} (F : C ⟶ D) : Type :=
  ∀ (J : Category) (K : J ⟶ C), ReflectsLimitCone K F.

Definition ReflectsAllLimits_Over {C D : Category} {S : Category → Type}
  {F : C ⟶ D} (H : ReflectsAllLimits F) : ReflectsLimitConesOver S F :=
  fun J _ K => H J K.

Definition ReflectsColimitCoconesOfShape (J : Category) {C D : Category}
  (F : C ⟶ D) : Type := ∀ K : J ⟶ C, ReflectsColimitCocone K F.

Definition ReflectsColimitCoconesOver {C D : Category}
  (S : Category → Type) (F : C ⟶ D) : Type :=
  ∀ J : Category, S J → ∀ K : J ⟶ C, ReflectsColimitCocone K F.

Definition ReflectsColimitCoconesOfClass {C D : Category}
  (S : ∀ J : Category, (J ⟶ C) → Type) (F : C ⟶ D) : Type :=
  ∀ (J : Category) (K : J ⟶ C), S J K → ReflectsColimitCocone K F.

Definition ReflectsColimitCoconesOver_OfClass {C D : Category}
  {S : Category → Type} {F : C ⟶ D} (H : ReflectsColimitCoconesOver S F) :
  ReflectsColimitCoconesOfClass (fun J _ => S J) F :=
  fun J K HJ => H J HJ K.

Definition ReflectsColimitCoconesOfClass_Over {C D : Category}
  {S : Category → Type} {F : C ⟶ D}
  (H : ReflectsColimitCoconesOfClass (fun J _ => S J) F) :
  ReflectsColimitCoconesOver S F :=
  fun J HJ K => H J K HJ.

Definition ReflectsAllColimits {C D : Category} (F : C ⟶ D) : Type :=
  ∀ (J : Category) (K : J ⟶ C), ReflectsColimitCocone K F.

Definition ReflectsAllColimits_Over {C D : Category} {S : Category → Type}
  {F : C ⟶ D} (H : ReflectsAllColimits F) : ReflectsColimitCoconesOver S F :=
  fun J _ K => H J K.

(* * ** A conservative functor's opposite is conservative / * ** 保守函子的对偶是保守的 *)

(*
 An isomorphism of C^op is one of C with its two laws exchanged;
 Theory/Morphisms/CokernelPair.v's [IsIsomorphism_of_op] and
 [op_IsIsomorphism_of] read it across, in D and in C. 

 --------
 C^op 的同构是 C 的同构，其两个律交换；
 Theory/Morphisms/CokernelPair.v 中的 [IsIsomorphism_of_op] 和
 [op_IsIsomorphism_of] 在 D 和 C 中对照阅读。
*)

Definition ReflectsIsos_op {C D : Category} {F : C ⟶ D}
  (R : ReflectsIsos F) : ReflectsIsos (F^op) :=
  @Build_ReflectsIsos (C^op) (D^op) (F^op)
    (fun x y f I =>
       @op_IsIsomorphism_of C x y f
         (@reflects_iso C D F R y x f (IsIsomorphism_of_op (fmap[F] f) I))).

(* * ** Creation gives reflection: the colimit side / * ** 创造提供反思：余极的方面 *)

(*
 The colimit twin of Structure/Limit/Creation.v's
 [creates_reflects_limits].  [CreatesColimit K F] is [CreatesLimit] of
 [K^op] along [F^op], whose reflection field asks for the image cone over
 [F^op ◯ K^op]; Structure/Limit/Preservation.v's [islimitcone_op_comp]
 reaches it from the image cocone over [(F ◯ K)^op]. 

 --------
 Structure/Limit/Creation.v 的 [creates_reflects_limits] 的余极限双胞胎。[CreatesColimit K F] 是沿着 [F^op] 的 [K^op] 的 [CreatesLimit]，其反射域要求 [F^op ◯ K^op] 上的像锥；Structure/Limit/Preservation.v 的 [islimitcone_op_comp] 从 [(F ◯ K)^op] 上的像余锥达到它。
*)

Definition creates_reflects_colimits {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (CR : CreatesColimit K F) :
  ReflectsColimitCocone K F :=
  fun N H =>
    @creates_reflect (J^op) (C^op) (D^op) (K^op) (F^op) CR N
      (islimitcone_op_comp H).

Definition creates_reflects_all_limits {C D : Category} {F : C ⟶ D}
  (CR : CreatesAllLimits F) : ReflectsAllLimits F :=
  fun J K => creates_reflects_limits (CR J K).

Definition creates_reflects_all_colimits {C D : Category} {F : C ⟶ D}
  (CR : CreatesAllColimits F) : ReflectsAllColimits F :=
  fun J K => creates_reflects_colimits (CR J K).

(* * ** Mac Lane's creation, read literally / * ** 麦克莱恩的创作，按字面理解 *)

(*
 Mac Lane §V.1, the unnumbered Definition on p. 112: F creates the
 limit of K when every limiting cone N over F ◯ K has exactly one lift,
 an apex a with F a equal to N's apex and legs whose images are N's, and
 that lift is limiting.  The lift is Creation.v's [StrictLift] (the
 apex by [=], the legs by ≈ along it), and “exactly one” is equality
 with every other strict lift of N, the apex by [=] and the legs by ≈
 along it.  Creation.v declines that uniqueness as a FIELD of
 [CreatesLimit] (its UNIQUENESS OF THE LIFT); as a hypothesis it is
 what Mac Lane's Exercise 1 assumes. 

 --------
 Mac Lane §V.1，第112页未编号定义：当每个关于 F ◯ K 的极限定锥 N 都有且只有一个提升时，F 创建了 K 的极限，该提升有一个顶点 a，使得 F a 等于 N 的顶点，并且其边的象为 N 的边，并且该提升是极限的。该提升是 Creation.v 的 [StrictLift]（通过 [=] 得到顶点，通过 ≈ 沿它得到边），而“只有一个”是指与 N 的每个其他严格提升相等，顶点通过 [=]，边通过 ≈ 沿它得到。Creation.v 把该唯一性作为 [CreatesLimit] 的一个 FIELD（其提升的唯一性）；作为假设，它就是 Mac Lane 的练习1所假定的内容。
*)

Record MacLaneCreatesLimit {J C D : Category} (K : J ⟶ C) (F : C ⟶ D) := {
  mlc_lift (N : Cone (F ◯ K)) (HN : IsLimitCone N) : StrictLift K F N;
  mlc_limiting (N : Cone (F ◯ K)) (HN : IsLimitCone N) :
    IsLimitCone (slift_cone (mlc_lift N HN));
  mlc_unique (N : Cone (F ◯ K)) (HN : IsLimitCone N) (L : StrictLift K F N) :
    { p : vertex_obj[slift_cone L] = vertex_obj[slift_cone (mlc_lift N HN)]
    & ∀ x : J, cone_leg (slift_cone (mlc_lift N HN)) x ∘ to (obj_eq_iso p)
                 ≈ cone_leg (slift_cone L) x }
}.

Arguments mlc_lift {J C D K F} _ _ _.
Arguments mlc_limiting {J C D K F} _ _ _.
Arguments mlc_unique {J C D K F} _ _ _ _.

(*
 Reflection by Mac Lane's argument: a cone M upstairs whose image is
 limiting is a strict lift of that image (Creation.v's [self_lift]), so
 it is the lift, which is limiting.  The cone isomorphism is built with
 [exact], not as a pair term, which Coq 8.19 and 8.20 check by
 unification. 

 --------
 根据 Mac Lane 的论证的反思：楼上的一个圆锥 M，其像是极限，是该像的严格提升（Creation.v 的 [self_lift]），因此它就是极限的提升。圆锥同构是用 [exact] 构建的，而不是作为一对项，Coq 8.19 和 8.20 通过统一检查它。
*)

Definition maclane_creates_reflects {J C D : Category} {K : J ⟶ C}
  {F : C ⟶ D} (CR : MacLaneCreatesLimit K F) : ReflectsLimitCone K F.
Proof.
  intros M HM.
  refine (limitcone_transport (ConeIso_sym _)
            (mlc_limiting CR (FCone F M) HM)).
  unshelve eexists.
  - exact (obj_eq_iso (`1 (mlc_unique CR (FCone F M) HM (self_lift M)))).
  - exact (`2 (mlc_unique CR (FCone F M) HM (self_lift M))).
Defined.

(*
 So Mac Lane's creation is one of the tree's, whose reflection field is
 the theorem above. 

 --------
 所以 Mac Lane 的创造是树之一，其反射场是上面的定理。
*)

Definition maclane_CreatesLimit {J C D : Category} {K : J ⟶ C}
  {F : C ⟶ D} (CR : MacLaneCreatesLimit K F) : CreatesLimit K F.
Proof.
  unshelve refine
    {| creates_lift := fun N HN => slift_cone (mlc_lift CR N HN);
       creates_reflect := maclane_creates_reflects CR |}.
  intros N HN.
  exists (slift_iso (mlc_lift CR N HN)).
  intro x.
  exact (slift_iso_legs (mlc_lift CR N HN) x).
Defined.

(*
 The same two clauses in the iso-invariant reading, a lift that is
 limiting and unique up to cone isomorphism, give reflection in one
 line; Creation.v's [creates_limiting] and [creates_lift_unique] derive
 them back from the reflection field and the lift's comparison. 

 --------
 在等变阅读中相同的两个子句，一个限制性的升起并且在圆锥同构下是唯一的，在一行中给出反射；Creation.v 的 [creates_limiting] 和 [creates_lift_unique] 从反射域和升起的比较中将它们导回。
*)

Definition iso_unique_lift_reflects {J C D : Category} {K : J ⟶ C}
  {F : C ⟶ D}
  (lift : ∀ N : Cone (F ◯ K), IsLimitCone N → Cone K)
  (lift_limiting : ∀ N HN, IsLimitCone (lift N HN))
  (lift_unique : ∀ N HN (M : Cone K), ConeIso (FCone F M) N →
                   ConeIso M (lift N HN)) :
  ReflectsLimitCone K F :=
  fun M HM =>
    limitcone_transport (ConeIso_sym (lift_unique _ HM M (ConeIso_id _)))
      (lift_limiting _ HM).

(*
 The identity creates every limit in Mac Lane's sense: the lift of N is
 N itself, read over K, and a strict lift of N has N's apex. 

 --------
 恒等映射在 Mac Lane 的意义上创造了每一个极限：N 的提升是 N 本身，在 K 上进行读取，N 的严格提升具有 N 的顶点。
*)

Definition id_maclane_creates {J C : Category} (K : J ⟶ C) :
  MacLaneCreatesLimit K Id[C].
Proof.
  unshelve econstructor.
  - intros N HN.
    unshelve econstructor.
    + exact (@Build_Cone J C K vertex_obj[N]
               (@Build_ACone J C vertex_obj[N] K (fun x => cone_leg N x)
                  (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N)
                                  x y f))).
    + reflexivity.
    + intro x; reflexivity.
  - intros N HN; simpl.
    intro M.
    exact (HN (@Build_Cone J C (Id ◯ K) vertex_obj[M]
                 (@Build_ACone J C vertex_obj[M] (Id ◯ K)
                    (fun x => cone_leg M x)
                    (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ M)
                                    x y f)))).
  - intros N HN L; simpl.
    exists (slift_eq L).
    intro x.
    pose proof (slift_legs L x) as HL.
    destruct L as [L p HLs]; simpl in *.
    destruct N as [n acN]; simpl in *.
    destruct p; simpl in *.
    rewrite id_right.
    symmetry; exact HL.
Defined.

(* The colimit side, by the opposite, as Creation.v's [CreatesColimit]. / 通过对偶，余极限一边，如 Creation.v 的 [CreatesColimit]。 *)

Definition MacLaneCreatesColimit {J C D : Category} (K : J ⟶ C)
  (F : C ⟶ D) : Type := MacLaneCreatesLimit (K^op) (F^op).

(* * ** A conservative functor reflects the limits it preserves / * ** 保守函子反映它所保持的极限 *)

(*
 Let M be a cone over K whose image is limiting, and u its mediator
 into L.  F u commutes with the image legs, so it is the comparison
 between the two limiting image cones, an isomorphism; F reflects it,
 so u is a cone isomorphism from M to L, and M is limiting. 

 --------
 设 M 是 K 上的一个圆锥，其像是极限的，u 是其到 L 的中介。F u 与像的射线交换，因此它是两个极限像圆锥之间的比较，是一个同构；F 能反映它，所以 u 是从 M 到 L 的一个圆锥同构，并且 M 是极限的。
*)

Definition conservative_reflects_limit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (R : ReflectsIsos F)
  (L : Cone K) (HL : IsLimitCone L) (HFL : IsLimitCone (FCone F L)) :
  ReflectsLimitCone K F.
Proof.
  intros M HFM.
  pose (u := unique_obj (HL M)).
  assert (Hu : ∀ x : J, cone_leg L x ∘ u ≈ cone_leg M x)
    by exact (unique_property (HL M)).
  pose (i := limitcone_iso HFM HFL).
  assert (HFu : fmap[F] u ≈ to `1 i).
  { symmetry.
    apply (uniqueness (HFL (FCone F M))).
    intro x.
    change (fmap[F] (cone_leg L x) ∘ fmap[F] u ≈ fmap[F] (cone_leg M x)).
    rewrite <- fmap_comp.
    apply fmap_respects.
    exact (Hu x). }
  assert (IFu : IsIsomorphism (fmap[F] u)).
  { unshelve refine {| two_sided_inverse := from `1 i |}.
    - rewrite HFu.
      exact (iso_to_from `1 i).
    - rewrite HFu.
      exact (iso_from_to `1 i). }
  assert (ci : ConeIso M L).
  { exists (IsIsoToIso u (@reflects_iso C D F R _ _ u IFu)).
    exact Hu. }
  exact (limitcone_transport (ConeIso_sym ci) HL).
Defined.

Definition preserves_conservative_reflects_limit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (L : Limit K) (P : PreservesLimitCone K F)
  (R : ReflectsIsos F) : ReflectsLimitCone K F :=
  conservative_reflects_limit R (@limit_cone _ _ _ L) (limit_limitcone L)
    (P (@limit_cone _ _ _ L) (limit_limitcone L)).

Definition preserves_conservative_reflects_limits_of_shape (J : Category)
  {C D : Category} {F : C ⟶ D} (HL : ∀ K : J ⟶ C, Limit K)
  (P : PreservesLimitConesOfShape J F) (R : ReflectsIsos F) :
  ReflectsLimitConesOfShape J F :=
  fun K => preserves_conservative_reflects_limit (HL K) (P K) R.

Definition preserves_conservative_reflects_limits_over {C D : Category}
  (S : Category → Type) {F : C ⟶ D}
  (HL : ∀ J : Category, S J → ∀ K : J ⟶ C, Limit K)
  (P : PreservesLimitConesOver S F) (R : ReflectsIsos F) :
  ReflectsLimitConesOver S F :=
  fun J HJ K =>
    preserves_conservative_reflects_limit (HL J HJ K) (P J HJ K) R.

Definition preserves_conservative_reflects_limits_of_class {C D : Category}
  (S : ∀ J : Category, (J ⟶ C) → Type) {F : C ⟶ D}
  (HL : ∀ (J : Category) (K : J ⟶ C), S J K → Limit K)
  (P : ∀ (J : Category) (K : J ⟶ C), S J K → PreservesLimitCone K F)
  (R : ReflectsIsos F) : ReflectsLimitConesOfClass S F :=
  fun J K HS =>
    preserves_conservative_reflects_limit (HL J K HS) (P J K HS) R.

(* The colimit side, by op: [F^op] is conservative ([ReflectsIsos_op]), and both image cocones are read as image cones over [F^op ◯ K^op]. / 通过 op: [F^op] 的余极端是保守的 ([ReflectsIsos_op])，并且两个像余锥被读取为在 [F^op ◯ K^op] 上的像锥。 *)

Definition conservative_reflects_colimit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (R : ReflectsIsos F)
  (L : Cocone K) (HL : IsColimitCocone L)
  (HFL : IsColimitCocone (FCocone F L)) : ReflectsColimitCocone K F :=
  fun N HFN =>
    @conservative_reflects_limit (J^op) (C^op) (D^op) (K^op) (F^op)
      (ReflectsIsos_op R) L HL (islimitcone_op_comp HFL) N
      (islimitcone_op_comp HFN).

Definition preserves_conservative_reflects_colimit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (L : Colimit K) (P : PreservesColimitCocone K F)
  (R : ReflectsIsos F) : ReflectsColimitCocone K F :=
  conservative_reflects_colimit R (@limit_cone _ _ _ L)
    (colimit_colimitcocone L)
    (P (@limit_cone _ _ _ L) (colimit_colimitcocone L)).

Definition preserves_conservative_reflects_colimits_of_shape (J : Category)
  {C D : Category} {F : C ⟶ D} (HL : ∀ K : J ⟶ C, Colimit K)
  (P : PreservesColimitCoconesOfShape J F) (R : ReflectsIsos F) :
  ReflectsColimitCoconesOfShape J F :=
  fun K => preserves_conservative_reflects_colimit (HL K) (P K) R.

Definition preserves_conservative_reflects_colimits_over {C D : Category}
  (S : Category → Type) {F : C ⟶ D}
  (HL : ∀ J : Category, S J → ∀ K : J ⟶ C, Colimit K)
  (P : ∀ J : Category, S J → PreservesColimitCoconesOfShape J F)
  (R : ReflectsIsos F) : ReflectsColimitCoconesOver S F :=
  fun J HJ K =>
    preserves_conservative_reflects_colimit (HL J HJ K) (P J HJ K) R.

Definition preserves_conservative_reflects_colimits_of_class {C D : Category}
  (S : ∀ J : Category, (J ⟶ C) → Type) {F : C ⟶ D}
  (HL : ∀ (J : Category) (K : J ⟶ C), S J K → Colimit K)
  (P : ∀ (J : Category) (K : J ⟶ C), S J K → PreservesColimitCocone K F)
  (R : ReflectsIsos F) : ReflectsColimitCoconesOfClass S F :=
  fun J K HS =>
    preserves_conservative_reflects_colimit (HL J K HS) (P J K HS) R.

(* * ** Riehl Exercise 3.4.iii: preservation and conservativity create / * ** Riehl 练习 3.4.iii：保留性与守恒性创建 *)

(*
 The lift of every limiting cone downstairs is the given limit upstairs,
 whose image is limiting by preservation and so isomorphic, as a cone,
 to any limiting cone downstairs; reflection is the theorem above. 

 --------
 楼下每一个限制锥的提升就是楼上给定的极限，其像通过保留而是限制的，因此作为一个锥与楼下的任何限制锥同构；反射是上述定理。
*)

Definition preserves_conservative_creates_limit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (L : Limit K) (P : PreservesLimitCone K F)
  (R : ReflectsIsos F) : CreatesLimit K F :=
  @Build_CreatesLimit J C D K F
    (fun N HN => @limit_cone _ _ _ L)
    (fun N HN =>
       limitcone_iso (P (@limit_cone _ _ _ L) (limit_limitcone L)) HN)
    (preserves_conservative_reflects_limit L P R).

Definition preserves_conservative_creates_limits_over {C D : Category}
  (S : Category → Type) {F : C ⟶ D}
  (HL : ∀ J : Category, S J → ∀ K : J ⟶ C, Limit K)
  (P : PreservesLimitConesOver S F) (R : ReflectsIsos F) :
  ∀ J : Category, S J → CreatesLimitsOfShape J F :=
  fun J HJ K =>
    preserves_conservative_creates_limit (HL J HJ K) (P J HJ K) R.

(* For a class of diagrams, as the exercise states it; the form over a class of shapes S above is this one at [fun J _ => S J], pointwise at [eq_refl] (the probe, C29). / 对于一类图表，正如练习中所说的；在上述形状类 S 上的形式是 [fun J _ => S J] 处的这个，在 [eq_refl] 处逐点（探针，C29）。 *)

Definition preserves_conservative_creates_limits_of_class {C D : Category}
  (S : ∀ J : Category, (J ⟶ C) → Type) {F : C ⟶ D}
  (HL : ∀ (J : Category) (K : J ⟶ C), S J K → Limit K)
  (P : ∀ (J : Category) (K : J ⟶ C), S J K → PreservesLimitCone K F)
  (R : ReflectsIsos F) :
  ∀ (J : Category) (K : J ⟶ C), S J K → CreatesLimit K F :=
  fun J K HS =>
    preserves_conservative_creates_limit (HL J K HS) (P J K HS) R.

Definition preserves_conservative_creates_colimit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (L : Colimit K) (P : PreservesColimitCocone K F)
  (R : ReflectsIsos F) : CreatesColimit K F :=
  @preserves_conservative_creates_limit (J^op) (C^op) (D^op) (K^op) (F^op)
    L (fun N HN => islimitcone_op_comp (P N HN)) (ReflectsIsos_op R).

Definition preserves_conservative_creates_colimits_of_class {C D : Category}
  (S : ∀ J : Category, (J ⟶ C) → Type) {F : C ⟶ D}
  (HL : ∀ (J : Category) (K : J ⟶ C), S J K → Colimit K)
  (P : ∀ (J : Category) (K : J ⟶ C), S J K → PreservesColimitCocone K F)
  (R : ReflectsIsos F) :
  ∀ (J : Category) (K : J ⟶ C), S J K → CreatesColimit K F :=
  fun J K HS =>
    preserves_conservative_creates_colimit (HL J K HS) (P J K HS) R.

(* * ** Coequalizers: Mac Lane's “in particular” and Exercises 1 and 3 / * ** 共等化子：Mac Lane 的“特别是”和练习 1 与 3 *)

(*
 Mac Lane's reflection of coequalizers, over the tree's elementary
 [IsCoequalizer]: a fork in C (e ∘ f ≈ e ∘ g) whose image is a
 coequalizer in D is a coequalizer in C. 

 --------
 Mac Lane 对上同等化子的反射，关于树的基本 [IsCoequalizer]：C 中的一个叉（e ∘ f ≈ e ∘ g），其像在 D 中是一个上同等化子，在 C 中也是一个上同等化子。
*)

Definition ReflectsCoequalizers@{co ch do dh +}
  {C : Category@{co ch ch}} {D : Category@{do dh dh}} (F : C ⟶ D) : Type :=
  ∀ (x y : C) (f g : x ~{C}~> y) (q : C) (e : y ~{C}~> q),
    e ∘ f ≈ e ∘ g →
    IsCoequalizer (fmap[F] f) (fmap[F] g) (F q) (fmap[F] e) →
    IsCoequalizer f g q e.

(*
 Preservation in the same form: the dual of Structure/Limit/
 FromProducts.v's [PreservesEqualizers], and Monad/Monadicity/Crude.v's
 [PreservesReflexiveCoequalizers] without its reflexivity hypothesis.
 The binders of both predicates are written out: left to Rocq,
 minimization identified D's hom level with C's (measured), and the
 probe accepts both with D's strictly above (C6, C7). 

 --------
 以相同形式的保持：Structure/Limit/FromProducts.v 中的 [PreservesEqualizers] 的对偶，以及 Monad/Monadicity/Crude.v 中的 [PreservesReflexiveCoequalizers]（不包含其自反性假设）。两个谓词的绑定器都已写出：左到 Rocq，最小化将 D 的同伦层级与 C 的（已测量）相对应，并且探针同时接受两者，D 的层级严格高于（C6，C7）。
*)

Definition PreservesCoequalizers@{co ch do dh +}
  {C : Category@{co ch ch}} {D : Category@{do dh dh}} (F : C ⟶ D) : Type :=
  ∀ (x y : C) (f g : x ~{C}~> y) (q : C) (e : y ~{C}~> q),
    IsCoequalizer f g q e →
    IsCoequalizer (fmap[F] f) (fmap[F] g) (F q) (fmap[F] e).

(*
 Creation of coequalizers: Structure/Limit/Creation.v's creation of the
 colimit of every diagram of parallel-pair shape. 

 --------
 共轭化子的创建：Structure/Limit/Creation.v 中每个平行对形状图的余极限的创建。
*)

Definition CreatesCoequalizers {C D : Category} (F : C ⟶ D) : Type :=
  ∀ K : Parallel ⟶ C, CreatesColimit K F.

(*
 The elementary and the cocone-level readings agree, both ways, through
 Structure/Coequalizer.v's conversions at a diagram of parallel-pair
 shape: an image cocone is a cocone over [F ◯ K], whose pair is the
 image pair and whose injection over [ParY] is the image injection, by
 conversion. 

 --------
 初等读法和余锥层读法一致，通过 Structure/Coequalizer.v 在平行对图形上的转换：像余锥是 [F ◯ K] 上的一个余锥，其对是像对，其在 [ParY] 上的注入是通过转换的像注入。
*)

Definition ReflectsCoequalizers_ReflectsColimitCocones {C D : Category}
  {F : C ⟶ D} (R : ReflectsCoequalizers F) :
  ReflectsColimitCoconesOfShape Parallel F.
Proof.
  intros K N H.
  apply (parallel_cocone_coequalizer_colimit K N).
  apply R.
  - (* N coforks the pair: both composites are its injection over ParX / N 分叉这对：两个复合体都是它在 ParX 上的注入 *)
    transitivity (cocone_inj N ParX).
    + exact (cocone_inj_coherence N
               ((true; ParOne) : ParX ~{Parallel}~> ParY)).
    + symmetry.
      exact (cocone_inj_coherence N
               ((false; ParTwo) : ParX ~{Parallel}~> ParY)).
  - exact (parallel_colimit_coequalizer (F ◯ K) (FCocone F N) H).
Defined.

(*
 The two bridges from the cocone level to the elementary predicates use
 their hypothesis only at the diagrams [APair f g], so they are stated
 per parallel pair, and their forms over every diagram of parallel-pair
 shape are the restrictions. 

 --------
 从 cocone 层到基本谓词的两座桥仅在图 [APair f g] 上使用它们的假设，因此它们是按平行对陈述的，并且它们在每个平行对形状的图上的形式都是这些限制。
*)

Definition ReflectsColimitCocones_ReflectsCoequalizers_of_pairs
  {C D : Category} {F : C ⟶ D}
  (R : ∀ (x y : C) (f g : x ~> y), ReflectsColimitCocone (APair f g) F) :
  ReflectsCoequalizers F :=
  fun x y f g q e H E =>
    parallel_colimit_coequalizer (APair f g) (cofork_cocone f g e H)
      (R x y f g (cofork_cocone f g e H)
         (parallel_cocone_coequalizer_colimit (F ◯ APair f g)
            (FCocone F (cofork_cocone f g e H)) E)).

Definition ReflectsColimitCocones_ReflectsCoequalizers {C D : Category}
  {F : C ⟶ D} (R : ReflectsColimitCoconesOfShape Parallel F) :
  ReflectsCoequalizers F :=
  ReflectsColimitCocones_ReflectsCoequalizers_of_pairs
    (fun x y f g => R (APair f g)).

Definition PreservesCoequalizers_PreservesColimitCocones {C D : Category}
  {F : C ⟶ D} (P : PreservesCoequalizers F) :
  PreservesColimitCoconesOfShape Parallel F :=
  fun K N HN =>
    parallel_cocone_coequalizer_colimit (F ◯ K) (FCocone F N)
      (P _ _ _ _ _ _ (parallel_colimit_coequalizer K N HN)).

Definition PreservesColimitCocones_PreservesCoequalizers_of_pairs
  {C D : Category} {F : C ⟶ D}
  (P : ∀ (x y : C) (f g : x ~> y), PreservesColimitCocone (APair f g) F) :
  PreservesCoequalizers F :=
  fun x y f g q e E =>
    parallel_colimit_coequalizer (F ◯ APair f g)
      (FCocone F (parallel_cofork_cocone (APair f g) e (cofork E)))
      (P x y f g (parallel_cofork_cocone (APair f g) e (cofork E))
         (parallel_coequalizer_colimit (APair f g) E)).

Definition PreservesColimitCocones_PreservesCoequalizers {C D : Category}
  {F : C ⟶ D} (P : PreservesColimitCoconesOfShape Parallel F) :
  PreservesCoequalizers F :=
  PreservesColimitCocones_PreservesCoequalizers_of_pairs
    (fun x y f g => P (APair f g)).

(* Mac Lane §VI.7 Exercise 1, per parallel pair, as the book states it: under the tree's creation, where reflection is a field ... / 麦克·莱恩 §VI.7 练习 1，按照书中的平行对：在树的创造之下，反射是一种领域... *)

Definition creates_reflects_coequalizers_of_pairs {C D : Category}
  {F : C ⟶ D}
  (CR : ∀ (x y : C) (f g : x ~> y), CreatesColimit (APair f g) F) :
  ReflectsCoequalizers F :=
  ReflectsColimitCocones_ReflectsCoequalizers_of_pairs
    (fun x y f g => creates_reflects_colimits (CR x y f g)).

(* ... and under Mac Lane's own, by his argument. / ...并且根据麦克雷恩自己的论证。 *)

Definition maclane_creates_reflects_coequalizers {C D : Category}
  {F : C ⟶ D}
  (CR : ∀ (x y : C) (f g : x ~> y), MacLaneCreatesColimit (APair f g) F) :
  ReflectsCoequalizers F :=
  ReflectsColimitCocones_ReflectsCoequalizers_of_pairs
    (fun x y f g N H =>
       maclane_creates_reflects (CR x y f g) N (islimitcone_op_comp H)).

(* Over every diagram of parallel-pair shape, by restriction (C17). / 通过限制 (C17)，在每个平行对形状的图表上。 *)

Definition creates_reflects_coequalizers {C D : Category} {F : C ⟶ D}
  (CR : CreatesCoequalizers F) : ReflectsCoequalizers F :=
  creates_reflects_coequalizers_of_pairs (fun x y f g => CR (APair f g)).

(* Mac Lane §VI.7 Exercise 3. / 麦克莱恩 §VI.7 练习 3。 *)

Definition conservative_reflects_coequalizers {C D : Category}
  {F : C ⟶ D} (HC : HasCoequalizers C) (P : PreservesCoequalizers F)
  (R : ReflectsIsos F) : ReflectsCoequalizers F :=
  ReflectsColimitCocones_ReflectsCoequalizers
    (preserves_conservative_reflects_colimits_of_shape Parallel
       (HasCoequalizers_HasColimitsOfShape HC)
       (PreservesCoequalizers_PreservesColimitCocones P) R).
