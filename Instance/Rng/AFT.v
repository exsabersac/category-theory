Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.GAFT.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Instance.Ab.Free.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Limit.
Require Import Category.Instance.Rng.Free.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

(* * * The free ring functors, read through the adjoint functor theorem / * * 自由环函子，通过伴随函子定理来阅读 *)

(*
 nLab: https://ncatlab.org/nlab/show/adjoint+functor+theorem
 nLab: https://ncatlab.org/nlab/show/free+ring
 nLab: https://ncatlab.org/nlab/show/created+limit
 Mac Lane: Categories for the Working Mathematician, 2nd ed. (GTM 5),
 §V.6 Exercise 2, book p. 125 (PDF p. 134); the theorem it
 invokes is §V.6 Theorem 2, book p. 123, as Adjunction/GAFT.v
 reads it
 Awodey:   Category Theory, 1st ed., §9.9 Exercise 9, printed p. 264
 (PDF p. 273)
 Fong & Spivak: Seven Sketches in Compositionality (CUP, 2019),
 §3.4.2 Example 3.74 clause 1, printed p. 104 (PDF p. 116)

 Mac Lane's Exercise 2 asks that Freyd's theorem be run at the forgetful
 functors of rings -- [Rng ⟶ Sets] and [Rng ⟶ Ab] -- and that its output
 be compared with the free ring and the tensor/monoid ring built by hand.
 Both halves are here, and so is the disclosure of what each one is worth.

 ** READ THIS BEFORE READING ANYTHING ELSE: NOTHING HERE IS CIRCULAR ANY
 MORE, AND THE CIRCULAR READINGS ARE KEPT BESIDE THE NEW ONES

 [Rng_Forget_Ab_continuous] IS NOT CIRCULAR.  It is derived from
 [Rng_Forget_continuous] (Instance/Rng/Limit.v) and
 [Ab_Forget_reflects_limits] (Instance/Ab/Limit.v) through the
 factorization below, and neither of those mentions an adjunction: the
 first comes from strict creation over [Sets_Complete], the second from
 strict creation of limits of abelian groups.  Nothing in its term
 mentions [FreeRngAb], [FreeAb] or any free object.

 CORRECTION, PR "algebraic carriers are sets" (2026-09-17).  This block
 used to read "ONE RESULT HERE IS NEW, TWO ARE CIRCULAR" and continued:

 "THE TWO GAFT APPLICATIONS ARE CIRCULAR, AND SAYING SO IS THE POINT.
 Freyd's third hypothesis is a solution set, and the two fed to it
 below -- [Rng_Forget_Ab_solution_set_from_adjunction] and
 [Rng_Forget_solution_set_from_adjunction] -- are
 [solution_set_of_adjunction] (Adjunction/GAFT.v) applied to
 [free_rng_ab_adjunction] (Instance/Rng/Free.v) and to the
 retyping of [free_ring_via_ab_adjunction]: the singleton
 family at the unit of THE VERY ADJUNCTION EACH APPLICATION IS MEANT
 TO PRODUCE.  So [free_rng_ab_via_GAFT] and [free_ring_via_GAFT] are
 genuine applications of a genuine theorem and are worthless as
 existence proofs -- strip Instance/Rng/Free.v and nothing in those
 two lines survives."

 That description is now TRUE OF TWO DIFFERENT CONSTANTS and FALSE of
 [free_rng_ab_via_GAFT] and [free_ring_via_GAFT].  The two circular
 solution sets are kept, under the names they always had, and the two
 circular GAFT applications built from them are kept under the new names
 [free_rng_ab_via_GAFT_from_adjunction] and
 [free_ring_via_GAFT_from_adjunction].  Every sentence of the quoted
 paragraph applies to those four and to nothing else.

 WHAT THE TWO HEADLINE CONSTANTS NOW CONSUME is
 [Rng_Forget_Ab_solution_set_prop] and [Rng_Forget_solution_set_prop]:
 the quotients of the FREE-RING TERM MODEL ([FRTerm],
 Instance/Rng/Free.v) by [Prop]-valued congruences, covered by the
 kernel congruence of an evaluation.  Strip Instance/Rng/Free.v's
 ADJUNCTIONS and both still stand.  Strip its TERM MODEL and they do not
 -- which is a dependence on a CONSTRUCTION, not on the conclusion, and
 is the same dependence every solution-set argument has.

 THE EXCEPTION, STATED HERE SO IT IS NOT DISCOVERED LATER.  The five
 [_mon] clauses -- the comparison with the monoid-ring route -- are
 stated about [free_ring_via_GAFT_from_adjunction], the CIRCULAR
 constant, and not about the new one.  [free_ring_via_mon] is itself
 pinned at [Set] and the non-circular application carries
 [Set < carrier], so the two cannot be compared; the measurement and the
 refusal are recorded at the clause itself.  The [_ab] comparisons are
 about the new constant and are unaffected.

 The disclosure this file used to make is still made by
 Adjunction/GAFT/Sets.v about its own instance; Instance/Grp/FreeAFT.v
 moved with this one.

 ** WHY THE CONTINUITY RESULT IS THE ONE WORTH HAVING

 Instance/Rng/Limit.v's NOT-DELIVERED block explains why no
 CREATION result for [Rng_Forget_Ab] is proved there, and the reason is
 structural rather than a matter of effort.  The cone-mediator method
 that works over [Sets] does not transpose to [Ab]: multiplication would
 need a cone whose apex is a direct sum with leg [(a, b) ↦ leg a · leg b],
 and that map is BILINEAR, not additive, so it is not a morphism of [Ab]
 and there is no cone to take a mediator of; the multiplicative unit is
 worse, since [Ab]'s initial object is a ZERO object (Instance/Ab.v)
 and the only canonical maps out of it send everything to zero, so
 none of them selects [1].  NOTHING BELOW REPAIRS THAT.  No creation
 result for [Rng_Forget_Ab] is proved here either, and the bilinearity
 obstruction stands exactly where that block leaves it.

 What the composite route gets is the CONTINUITY anyway, by going around
 the obstruction rather than through it.  Given a limiting cone [N] over
 a diagram [K] in [Rng]:

 - [Rng_Forget_continuous] makes [FCone Rng_Forget N] limiting in
 [Sets] -- that is creation over [Sets], where the mediator method
 does work, because a set carries no additivity constraint at all;
 - by the factorization, that cone IS [FCone Ab_Forget (FCone
 Rng_Forget_Ab N)] -- same apex, same legs, same coherence proof,
 only a different diagram record (see the next paragraph);
 - [Ab_Forget_reflects_limits], which is
 [ReflectsLimitCone K Ab_Forget], then makes [FCone Rng_Forget_Ab N]
 limiting in [Ab].

 So the multiplicative structure never has to be built over [Ab]: it is
 built over [Sets], where it is legal, and the conclusion is imported
 back into [Ab] by reflection.  Creation is strictly more than this and
 is still missing.

 AND THE CONTRAST WITH RAPL IS THE WHOLE REASON THE ROUTE MATTERS HERE.
 Adjunction/Continuity.v's [right_adjoint_Continuous] would give
 [ContinuousFunctor Rng_Forget_Ab] in one line from
 [free_rng_ab_adjunction], since [FreeRngAb ⊣ Rng_Forget_Ab].  That term
 would be CIRCULAR in exactly the sense above: fed to GAFT it would
 presuppose the adjunction GAFT is being asked to produce, and the
 application would establish nothing.  Instance/Ab/Limit.v states
 the same contrast for its own two continuity constants -- the RAPL-built
 [Ab_Forget_Continuous] (Instance/Ab/FreeNotContinuous.v) against the
 creation-built [Ab_Forget_creates_continuous] -- and this file is the
 first consumer for which the distinction actually bites.

 ** THE FACTORIZATION IS DEFINITIONAL ON DATA AND NOT ON RECORDS

 [rng_forget_factors_obj] and [rng_forget_factors_map] are [eq_refl]:
 [fobj[Rng_Forget] R] and [fmap[Rng_Forget] f] are convertible with
 [fobj[Ab_Forget ◯ Rng_Forget_Ab] R] and [fmap[Ab_Forget ◯
 Rng_Forget_Ab] f].  Both sides reduce to [rig_setoid R] and [rig_map f]
 (Instance/Rng.v is where those two functors are written, and it
 already records both object readbacks).

 THE FUNCTOR RECORDS ARE NOT CONVERTIBLE, and pretending otherwise would
 have made this file two lines shorter and wrong.  [Rng_Forget] is a
 [Program Definition] whose three functor laws are discharged by [Qed]
 obligations; [Ab_Forget ◯ Rng_Forget_Ab] is a [Compose] record whose
 laws are [Compose]'s generic proofs.  Those proof fields do not reduce
 to each other, so [Cone (Rng_Forget ◯ K)] and
 [Cone (Ab_Forget ◯ (Rng_Forget_Ab ◯ K))] are DIFFERENT TYPES and no
 [exact] crosses between them.  What IS convertible is every component a
 cone is built from -- apex, legs, and the coherence statement, which
 mentions the diagram only through [fmap] -- so [rng_ab_recone] and
 [rng_sets_recone] rebuild the record field for field, reusing the SAME
 coherence proof term.  Each is four lines and neither needs a tactic.

 ** THE TYPE TRAP GAFT SETS, MEASURED HERE AND NOT INHERITED AS A RUMOUR

 [ContinuousFunctor] does not ascribe where GAFT asks for
 [PreservesImageLimit].  Measured in this worktree, Rocq 9.1.1, feeding
 [GAFT Rng_Forget Rng_Complete Rng_Forget_continuous sols] is refused,
 with this STABLE head:

 The term "Rng_Forget_continuous" has type "ContinuousFunctor
 Rng_Forget" while it is expected to have type
 "Limit.PreservesImageLimit"

 The trailing [cannot unify ...] clause is deliberately NOT quoted here,
 because it is IMPORT-SENSITIVE: it is rendered with whatever module
 short-names are in scope, so the same refusal prints
 [cannot unify "Limit.Limit K" and "Cone.Cone K"] under one import list
 and [cannot unify "Cone.Cone (F ◯ K)" and "IsLimitCone N"] under
 another (measured at [Ab], four import lists, in
 Test/ProbeAlgLimit443.v's section E).  An earlier revision of this
 paragraph quoted one of them as though it were the text; two independent
 measurements of this same refusal then appeared to contradict each other
 when neither was wrong.  Only the head is quoted now.

 The refusal itself is the same one Instance/Ab/Limit.v records at
 [Ab_Forget] and Test/ProbeGrpFreeAFT442.v's N6 records at [Grp_Forget],
 here at [Rng].  The bridge [Continuous_PreservesImageLimit]
 (Construction/Comma/Creation.v) is load-bearing and stands in both
 GAFT terms below.

 ** THE ISSUE'S "CURRENT STATE" IS STALE IN SIX PLACES

 It says: "The ring cases are entirely absent: [Rng] and [Ab] do not
 exist (#257, #256), so neither the ring-side forgetful functors nor
 their free objects exist, and no [SolutionSet] instance is ever built
 for a forgetful functor of this kind."  Each clause, checked against a
 green build on 2026-09-13:

 1. "[Rng] ... [does] not exist" -- [Rng], Instance/Rng.v.
 2. "[Ab] [does] not exist" -- [Ab], Instance/Ab.v.
 3. "neither the ring-side forgetful functors ... exist" --
 [Rng_Forget_Ab] and [Rng_Forget], both Instance/Rng.v.
 4. "nor their free objects exist" -- [FreeRngAb],
 [free_ring_via_ab] and [free_ring_via_mon], all
 Instance/Rng/Free.v; with the adjunctions
 [free_rng_ab_adjunction], [free_ring_via_ab_adjunction] and
 [free_ring_via_mon_adjunction] beside them.
 5. "no [SolutionSet] instance is ever built for a forgetful functor of
 this kind" -- [Grp_Forget_solution_set_from_adjunction],
 Instance/Grp/FreeAFT.v, at [Grp_Forget : Grp ⟶ Sets], which is
 a forgetful functor of exactly this kind.
 6. The Awodey section's "the adjoint functor theorem's only in-tree
 application is a diagonal/product toy example" -- [free_group_via_GAFT],
 Instance/Grp/FreeAFT.v, and [GAFT_at_Sets_Id],
 Adjunction/GAFT/Sets.v, which feeds GAFT [Sets_Id_SolutionSet].
 Sweeping [grep -rnw GAFT] over all [.v] files outside
 [Adjunction/GAFT*], those two are the only applications of the theorem
 in tree; everything else is prose or a probe.  (CORRECTION, #450:
 that sweep is dated.  This file itself applies [GAFT] in four
 constants -- [free_rng_ab_via_GAFT] and [free_ring_via_GAFT], and
 their circular readings [free_rng_ab_via_GAFT_from_adjunction] and
 [free_ring_via_GAFT_from_adjunction] -- and since #450
 Instance/Grp/Colimit.v and Instance/Rng/Colimit.v apply it at the
 diagonal functor of every shape with homs at the carrier universe
 and objects at or below it, and Instance/Variety/Colimit.v at the
 diagonal and at the forgetful functor of the setoid variety.)

 None of the six is established here -- each was in tree before this file
 was started, which is the whole difficulty, exactly as at [Grp].  What
 is NOT stale is the issue's requirement.

 ** THE ONE ABSENCE THAT WAS REAL, AND THE FINDING THAT IT WAS ONLY
 NOMINAL

 Before this file, [grep -rnP '⊣\s*Rng_Forget(?![A-Za-z0-9_])'] over all
 [.v] files returned NOTHING: no adjunction in tree had the literal
 [Rng_Forget : Rng ⟶ Sets] as its right adjoint.  Instance/Rng/Limit.v
 records the same measurement and draws the correct conclusion
 for its own purposes, that [right_adjoint_Continuous] does not reach
 [Rng_Forget].

 THAT ABSENCE IS NOMINAL, NOT STRUCTURAL, and the measurement above is
 what made it look otherwise.  Instance/Rng/Free.v's
 [free_ring_via_ab_adjunction] has right adjoint [RngUnderlyingAb], which
 is DEFINED as [Ab_Forget ◯ Rng_Forget_Ab] -- the very composite
 the factorization identifies with [Rng_Forget] on data.  Every field of
 [Adjunction] (Theory/Adjunction.v) mentions the right adjoint
 only through [U y] and [fmap[U] f], so the five field TYPES are
 convertible and the record can be copied across field by field.  That
 is [free_ring_via_ab_adjunction_set] below, and the trick is not
 invented here: Instance/Rng/Free.v's
 [free_ring_via_mon_adjunction_ab] is the same copy, between the same two
 presentations of the same underlying-set functor, with the reason
 spelled out there.

 So the second GAFT application IS buildable, and an earlier reading of
 this issue that concluded it was not -- on the strength of the [grep]
 alone -- was wrong.  The [grep] is a measurement of NAMES; the question
 is one of TYPES.

 ** THE TWO HIDDEN CHECKBOXES IN THE ISSUE BODY

 (A) Awodey §9.9 Exercise 9 asks to "Build a solution set for a forgetful
 functor out of an algebraic category and derive the free construction
 from the adjoint functor theorem, so the theorem has a genuine
 application in the tree."  ADDRESSED, at two functors, IN BOTH READINGS.

 CORRECTION, PR "algebraic carriers are sets" (2026-09-17): this clause
 read "ADDRESSED, at two functors, and with the circularity disclosed:
 the solution sets below are not Mac Lane's, and the derivation is
 therefore an application of the theorem and not an independent
 construction.  Awodey's exercise is satisfied in its literal reading --
 the theorem has a genuine application -- and NOT in the reading a reader
 might want, where the free ring is OBTAINED from the theorem."  The
 reading the reader wanted is now delivered: the solution sets are STILL
 not Mac Lane's (they are congruence quotients of a term model, not
 subrings cut down by a cardinality bound), but they are built without
 the adjunction, so the free ring IS obtained from the theorem.
 Instance/Grp/FreeAFT.v moved with this file.

 (B) Fong & Spivak §3.4.2 Example 3.74 clause 1 asks to "Deliver the
 conclusion as [Adjunction] witnesses rather than only as universal
 arrows, so the 'free is left adjoint to forgetful' slogan is a statement
 in the library".  Its supporting sentence, "Today Instance/CMon.v
 supplies a forgetful functor with no free functor and no adjunction
 beside it, and no other algebraic category exists in tree", is EXACT in
 its first half and stale in its second.  [CMon_Forget] is still at
 Instance/CMon.v with no [FreeCMon] and, measured,
 [grep -rnP '⊣\s*CMon_Forget(?![A-Za-z0-9_])'] over all [.v] files returns
 nothing.  But five other algebraic categories carry the slogan already:
 [free_group_adjunction] (Instance/Grp/Free.v),
 [free_ab_adjunction] (Instance/Ab/Free.v),
 [free_mon_sets_adjunction] (Instance/Mon/Free.v),
 [free_module_adjunction] (Instance/Mod/Free.v) and
 [free_rng_ab_adjunction] (Instance/Rng/Free.v).  What this file adds
 that was genuinely missing is the slogan AT THE LITERAL UNDERLYING-SET
 FUNCTOR OF RINGS:
 [free_ring_via_ab_adjunction_set : free_ring_via_ab ⊣ Rng_Forget]
 is the first inhabitant in tree of a type of that shape, by the
 measurement two paragraphs up.  [Instance/CMon.v]'s own gap is NOT
 closed here; no free commutative monoid is built.
 CORRECTION (#471): that gap is closed by Instance/CMon/Free.v, whose
 [FreeCMon_adj] is an adjunction of FreeCMon with CMon_Forget, so
 "still … with no [FreeCMon]" held until #471.  Its declaration names
 the right adjoint through a local notation, and the literal grep above
 matches only two comment lines of that file.

 ** THE COMPARISON CLAUSES ARE AT [≈] AND CANNOT BE ANYTHING ELSE

 The issue asks that each "compare with the usual construction" clause be
 "a proved isomorphism of the AFT-produced adjoint with the explicit free
 object".  [GAFT] (Adjunction/GAFT.v) ends in [Qed], so its output
 does not reduce and no component of it can be named.  Measured:

 Example nr1 : `1 free_ring_via_GAFT = free_ring_via_ab := eq_refl.

 is refused with "The term "eq_refl" has type "`1 (free_ring_via_GAFT) =
 `1 (free_ring_via_GAFT)" while it is expected to have type "`1
 (free_ring_via_GAFT) = free_ring_via_ab" (cannot unify "`1
 (free_ring_via_GAFT)" and "free_ring_via_ab")".  So NO [eq_refl] is
 claimed anywhere about a GAFT output, and the three comparisons below
 are at [≈], by [left_adjoints_agree] (Instance/Rng/Free.v) -- left
 adjoints to a fixed functor are isomorphic.  That donor is [Defined],
 so the comparison morphism has a name ([adj_left_compare]) and the
 unit clause ([adj_left_compare_unit]) is available; Mac Lane's
 exercise asks for both.  Theory/Adjunction.v's [left_adjoint_iso]
 inhabits the same types and is recorded beside each comparison so the
 claim is machine-checked twice.

 ** WHAT IS DELIVERED

 1. The factorization, at [eq_refl] on objects and on morphisms.
 2. [Rng_Forget_Ab_continuous : ContinuousFunctor Rng_Forget_Ab], and its
 apex-only consequence [Rng_Forget_Ab_PreservesAllLimits] -- the
 genuinely new, non-circular result, derived without an ADJUNCTION and
 without RAPL — though emphatically not without creation, since both of
 its inputs are creation results (Instance/Rng/Limit.v's
 [creates_limits_continuous ...] and Instance/Ab/Limit.v's
 [creates_reflects_limits ...]); what it avoids is a creation argument
 FOR [Rng_Forget_Ab] ITSELF, which is the one that stops.  Without
 an adjunction and without RAPL.
 3. [Rng_Forget_Ab_reflects_limits : ReflectsLimitCone K Rng_Forget_Ab],
 the same composite read in the other direction, also adjunction-free.
 4. [free_ring_via_ab_adjunction_set : free_ring_via_ab ⊣ Rng_Forget],
 the retyping, which is the Seven Sketches clause and the third GAFT
 hypothesis at [Rng_Forget] in one.
 5. FOUR solution sets (an earlier revision said two): the two
 NON-CIRCULAR ones built from [Prop] congruences on the free-ring term
 model, [Rng_Forget_Ab_solution_set_prop] and
 [Rng_Forget_solution_set_prop], which the two headline GAFT
 applications [free_rng_ab_via_GAFT] and [free_ring_via_GAFT] consume;
 and the two circular ones, kept under the names that say so, which
 [free_rng_ab_via_GAFT_from_adjunction] and
 [free_ring_via_GAFT_from_adjunction] consume.
 6. Three comparison clauses at [≈], each with its named comparison
 morphism and its unit equation: against [FreeRngAb], against
 [free_ring_via_ab] and against [free_ring_via_mon].  THE FIRST TWO
 are about the non-circular constants; the THIRD is about
 [free_ring_via_GAFT_from_adjunction], for the measured universe
 reason recorded at the clause.

 Items 1-4 do not depend on the AFT applications at all, and none of them
 is circular.

 ** NOT DELIVERED

 (1) NO CREATION RESULT FOR [Rng_Forget_Ab], and no repair of the
 bilinearity obstruction Instance/Rng/Limit.v records.
 Continuity is strictly less than creation and nothing here compares the
 two as propositions.  (2) NO [Complete Ab]-based route: [Ab_Complete]
 (Instance/Ab/Limit.v) exists and is not used, because GAFT is run at
 [Rng_Forget_Ab] and so wants [Complete Rng], not [Complete Ab].
 (3) NO SOLUTION SET OF MAC LANE'S OWN SHAPE.  CORRECTION, PR "algebraic
 carriers are sets" (2026-09-17): this clause read "NO NON-CIRCULAR
 SOLUTION SET", and that is false -- there are two, above.  What is still
 true, and is what the clause went on to say, is that MAC LANE'S OWN
 family is not built: the subrings generated by the image of a set, cut
 down by a cardinality bound, need a generated-subring API that does not
 exist over [RingObject].  The analogous gap at [Grp] is filed as #1309
 together with the universe-minimization artifact of
 Instance/Discrete.v's [DiscreteCat_Functor] -- the second of which
 has since been repaired -- and the [Rng] case would still meet the
 first.  Nothing here attempts it.  What is delivered instead is a
 congruence-quotient family, which is a different argument for the same
 conclusion.  (Instance/Mod/TensorAFT.v section 10 shows the two
 arguments meet at [RMod R], Mac Lane's family being SMALL UP TO
 ISOMORPHISM with the congruences as its small index; no such bridge is
 built here.)  (4) THE GRAPH HALF OF THE ISSUE IS NOT TOUCHED.
 Producing the left adjoint to the categories-to-graphs forgetful
 functor via GAFT and comparing it with Construction/Free/Quiver.v's
 [FreeForgetfulAdjunction] -- the location the issue body gives for
 that constant is stale, measured -- would need [Complete StrictCat]
 and continuity of that forgetful functor; the only
 completeness in tree is Instance/Cat/Limit.v's [StrictCat_Complete],
 which is CONDITIONAL on [∀ C, ObjUIP C] and [DepFunext] and so would
 carry those hypotheses into every constant downstream, and
 [grep -rnE 'ContinuousFunctor (Forgetful|Quiver)'] returns nothing.
 (5) NO MONADICITY and no comparison functor, so nothing here says [Rng]
 is an Eilenberg-Moore category; Riehl §5.6 Example 5.6.8 remains an
 observation, as Instance/Rng/Limit.v already records.
 (6) NO [Test/Probe] FILE accompanies this one.  The [eq_refl] readbacks
 below are guarded only by being [Example]s in this file, and the two
 refusals quoted in the header -- the [ContinuousFunctor]/
 [PreservesImageLimit] ascription and the non-reducing GAFT output -- are
 measured here but pinned nowhere.  That is a gap, not a claim.
 (7) NOTHING is registered as an [Instance]; the file declares none.

 ** STATUS: axiom-free

 Counting [def]+[prf] heads in the [.glob] file, this file declares
 THIRTY-FOUR constants and NO [Program] obligations -- it uses no
 [Program] at all, so the trap of obligations that no source-level
 reading sees does not arise here.  [Print Assumptions] reports "Closed
 under the global context" for all thirty-four, read back by name:
 [rng_forget_factors_obj], [rng_forget_factors_map],
 [rng_underlying_ab_is_forget_obj], [rng_underlying_ab_is_forget_map],
 [rng_ab_recone], [rng_sets_recone], [rng_ab_image_limit],
 [rng_ab_limit_cone], [rng_ab_reflect], [Rng_Forget_Ab_continuous],
 [Rng_Forget_Ab_PreservesAllLimits], [Rng_Forget_Ab_reflects_limits],
 [free_ring_via_ab_adjunction_set], [free_ring_via_mon_adjunction_set],
 [free_ring_via_ab_adjunction_set_transpose],
 [Rng_Forget_Ab_solution_set_from_adjunction],
 [Rng_Forget_solution_set_from_adjunction], [free_rng_ab_via_GAFT],
 [free_ring_via_GAFT], the three [_agrees] comparisons, their three
 [_via_left_adjoint_iso] cross-checks, the three [_comparison]
 morphisms, the three [_comparison_is_component] readbacks and the three
 [_unit] clauses.  That is a readback of this file's own constants, not
 a directory-wide certification, and nothing here is registered with
 [make print-assumptions].

 EIGHT of the thirty-four are [eq_refl] Examples: the four factorization
 readbacks, the transpose readback and the three
 [_comparison_is_component] readbacks.  No [eq_refl] is claimed about a
 GAFT output anywhere.

 This file contributes ZERO hits to [make todo]. 

 --------
 nLab：https://ncatlab.org/nlab/show/adjoint+functor+theorem
 nLab：https://ncatlab.org/nlab/show/free+ring
 nLab：https://ncatlab.org/nlab/show/created+limit
 Mac Lane：《为工作中的数学家准备的范畴论》，第2版（GTM 5），
 §V.6 练习题 2，书籍第125页（PDF 第134页）；它所引用的定理是
 §V.6 定理 2，书籍第123页，如Adjunction/GAFT.v所述
 Awodey：《范畴论》，第1版，§9.9 练习题 9，印刷版第264页（PDF 第273页）
 Fong & Spivak：《组合性中的七个例子》（剑桥大学出版社，2019），
 §3.4.2 示例 3.74 第1条，印刷版第104页（PDF 第116页）

 Mac Lane 的练习题 2 要求在环的遗忘函子——[Rng ⟶ Sets] 和 [Rng ⟶ Ab]——上运行 Freyd 定理，并将其输出与手工构建的自由环和张量/幺半环进行比较。两部分都在这里，以及每一个的价值披露。** 在阅读其他内容之前请先阅读此内容：这里没有任何内容是循环的，循环的内容已保存在新的旁边。

 [Rng_Forget_Ab_continuous] 不是循环的。它来源于
 [Rng_Forget_continuous]（Instance/Rng/Limit.v）和
 [Ab_Forget_reflects_limits]（Instance/Ab/Limit.v），通过下面的
 分解得到，并且它们都没有提到伴随：第一个来自 [Sets_Complete] 上的严格创建，第二个来自阿贝尔群极限的严格创建。它的项中没有提到 [FreeRngAb]、[FreeAb] 或任何自由对象。

 更正，PR “代数承载体是集合”（2026-09-17）。该块过去写着“这里有一个结果是新的，两个是循环的”，并继续：“两个 GAFT 应用是循环的，说出这一点就是重点。
 Freyd 的第三个假设是一个解集，下面提供给它的两个解集——[Rng_Forget_Ab_solution_set_from_adjunction] 和
 [Rng_Forget_solution_set_from_adjunction]——是
 [solution_set_of_adjunction]（Adjunction/GAFT.v）应用于
 [free_rng_ab_adjunction]（Instance/Rng/Free.v）以及对 [free_ring_via_ab_adjunction] 的重新类型化：单元素族在每个应用所要生成的真正伴随单元处。因此 [free_rng_ab_via_GAFT] 和 [free_ring_via_GAFT] 是真正定理的真实应用，并且作为存在性证明毫无价值——去掉 Instance/Rng/Free.v，这两行中没有任何内容能存活。”这个描述现在对两个不同的常量为真，而对 [free_rng_ab_via_GAFT] 和 [free_ring_via_GAFT] 为假。这两个圆形解集合保持原来的名称，用它们构建的两个圆形 GAFT 应用保持在新名称 [free_rng_ab_via_GAFT_from_adjunction] 和 [free_ring_via_GAFT_from_adjunction] 下。引用段落中的每句话都适用于这四个常量，而不适用于其他任何东西。现在两个标题常量所消耗的是 [Rng_Forget_Ab_solution_set_prop] 和 [Rng_Forget_solution_set_prop]：它们是 FREE-RING TERM MODEL（[FRTerm]，Instance/Rng/Free.v）除以 [Prop] 值同余的商，被一个求值的核同余所覆盖。去掉 Instance/Rng/Free.v 的 ADJUNCTIONS，两个仍然存在。去掉它的 TERM MODEL，它们就不存在了——这是对一个 CONSTRUCTION 的依赖，而不是对结论的依赖，并且是每个解集论证都有的相同依赖。例外情况，在此陈述以免以后被发现。这五个 [_mon] 条款——与幺半环路径的比较——是关于 [free_ring_via_GAFT_from_adjunction]，即 CIRCULAR 常数，而不是关于新的常数。[free_ring_via_mon] 本身固定在 [Set]，并且非循环应用带有 [Set < carrier]，所以两者无法比较；测量和拒绝记录在条款本身。[_ab] 的比较是关于新的常数，并且不受影响。

 此文件曾经进行的信息披露仍由 Adjunction/GAFT/Sets.v 关于其自身实例进行；Instance/Grp/FreeAFT.v 随本文件一起移动。

 ** 为什么连续性结果是值得拥有的Instance/Rng/Limit.v 的 NOT-DELIVERED 块解释了为什么在那里没有为 [Rng_Forget_Ab] 证明 CREATION 结果，其原因是结构性的，而不是努力的问题。在 [Sets] 上有效的锥中介方法无法转移到 [Ab]：乘法需要一个顶点为与 [(a, b) ↦ leg a · leg b] 的直和的锥，而该映射是 BILINEAR 的，而非加法的，因此它不是 [Ab] 的态射，也没有锥可以取其中介；乘法单位更糟，因为 [Ab] 的初始对象是零对象（Instance/Ab.v），且从它出去的唯一规范映射将一切都映射为零，因此没有一个选择 [1]。没有什么可以修复这个问题。这里也没有为 [Rng_Forget_Ab] 证明 CREATION 结果，并且双线性阻碍正好停留在该块留下的位置。复合路由所得到的无论如何是连续性，通过绕过障碍而不是穿过它。给定在 [Rng] 中对图表 [K] 的限制锥 [N]：

 - [Rng_Forget_continuous] 使 [FCone Rng_Forget N] 在 [Sets] 中受限 —— 即在 [Sets] 上的生成，其中中介方法确实有效，因为集合根本不受加法性约束；
 - 通过分解，该锥是 [FCone Ab_Forget (FCone Rng_Forget_Ab N)] —— 相同的顶点，相同的边，相同的一致性证明，仅仅不同的图表记录（见下段）；
 - [Ab_Forget_reflects_limits]，即 [ReflectsLimitCone K Ab_Forget]，然后使 [FCone Rng_Forget_Ab N] 在 [Ab] 中受限。因此，乘法结构永远不必建立在  [Ab] 上：它建立在  [Sets] 上，在那里是合法的，并且结论通过反射导回到  [Ab] 中。创造远不止于此，并且仍然缺失。与 RAPL 的对比正是这里路线重要的全部原因。
 Adjunction/Continuity.v 的 [right_adjoint_Continuous] 会在一行中从 [free_rng_ab_adjunction] 得到 [ContinuousFunctor Rng_Forget_Ab]，因为 [FreeRngAb ⊣ Rng_Forget_Ab]。这个项在完全上述意义上是循环的：将其输入 GAFT，它将预设 GAFT 被要求产生的附加，而应用不会建立任何东西。Instance/Ab/Limit.v 对它自己的两个连续性常数也陈述了相同的对比——RAPL 构建的 [Ab_Forget_Continuous]（Instance/Ab/FreeNotContinuous.v）与创建构建的 [Ab_Forget_creates_continuous]——而这个文件是第一个真正受此区别影响的使用者。

 ** 因式分解是基于数据的定义，而不是基于记录的定义[rng_forget_factors_obj] 和 [rng_forget_factors_map] 是 [eq_refl]：[fobj[Rng_Forget] R] 和 [fmap[Rng_Forget] f] 可以与 [fobj[Ab_Forget ◯ Rng_Forget_Ab] R] 和 [fmap[Ab_Forget ◯ Rng_Forget_Ab] f] 互换。两边都化简为 [rig_setoid R] 和 [rig_map f]（Instance/Rng.v 是写有这两个函子的地方，并且它已经记录了两个对象的回读）。函子记录不可转换，并且假装可以转换只会让这个文件少两行而且是错误的。[Rng_Forget] 是一个 [Program Definition]，其三个函子定律由 [Qed] 义务完成；[Ab_Forget ◯ Rng_Forget_Ab] 是一个 [Compose] 记录，其定律是 [Compose] 的泛型证明。那些证明字段不会相互归约，因此 [Cone (Rng_Forget ◯ K)] 和 [Cone (Ab_Forget ◯ (Rng_Forget_Ab ◯ K))] 是不同类型，并且没有 [exact] 跨越它们。可转换的是锥体构建的每个组件——顶点、边以及提到图表的相干性声明，只通过 [fmap] 来提及——因此 [rng_ab_recone] 和 [rng_sets_recone] 重建记录字段，重复使用相同的相干性证明项。每个都四行，并且都不需要策略。** 类型陷阱 GAFT 设置，这里测量，而不是作为谣言继承

 [ContinuousFunctor] 不归因于 GAFT 要求的位置
 [PreservesImageLimit] 。在此工作树中测量，Rocq 9.1.1，输入
 [GAFT Rng_Forget Rng_Complete Rng_Forget_continuous sols] 被拒绝，
 使用此 STABLE 头：

 术语 “Rng_Forget_continuous”的类型是 “ContinuousFunctor
 Rng_Forget”，而期望的类型是
 “Limit.PreservesImageLimit”这里故意没有引用尾部的 [cannot unify ...] 条款，因为它依赖于导入：它会根据当前作用域中的模块短名进行呈现，因此同一拒绝在一个导入列表下显示为 [cannot unify "Limit.Limit K" and "Cone.Cone K"]，而在另一个导入列表下显示为 [cannot unify "Cone.Cone (F ◯ K)" and "IsLimitCone N"]（在 Test/ProbeAlgLimit443.v 的 E 部分中测量为 [Ab]，共四个导入列表）。本段的早期修订版曾引用其中之一，好像它就是文本本身；对同一拒绝的两次独立测量随后看起来互相矛盾，但其实都没有错误。现在仅引用了开头部分。拒绝本身与 Instance/Ab/Limit.v 在 [Ab_Forget] 上记录的相同，以及 Test/ProbeGrpFreeAFT442.v 的 N6 在 [Grp_Forget] 上记录的相同，这里是在 [Rng] 上。桥 [Continuous_PreservesImageLimit]（Construction/Comma/Creation.v）是承重的，并且在下面的两个 GAFT 项中都存在。

 ** 该问题的“当前状态”在六处都是过时的

 它表示：“环形情况完全不存在：[Rng] 和 [Ab] 不存在 (#257, #256)，因此既不存在环侧遗忘函子，也不存在它们的自由对象，并且从未为这种类型的遗忘函子构建过 [SolutionSet] 实例。”每个条款均已在 2026-09-13 的绿色构建中进行核对：1. “[Rng] ... [does] 不存在” -- [Rng], Instance/Rng.v。 2. “[Ab] [does] 不存在” -- [Ab], Instance/Ab.v。 3. “两者的环边遗忘函子都不存在” -- [Rng_Forget_Ab] 和 [Rng_Forget], 都在 Instance/Rng.v。 4. “它们的自由对象也不存在” -- [FreeRngAb], [free_ring_via_ab] 和 [free_ring_via_mon], 全部在 Instance/Rng/Free.v；以及对应的伴随 [free_rng_ab_adjunction], [free_ring_via_ab_adjunction] 和 [free_ring_via_mon_adjunction]。 5. “没有任何 [SolutionSet] 实例会为这种类型的遗忘函子建立” -- [Grp_Forget_solution_set_from_adjunction], Instance/Grp/FreeAFT.v, 在 [Grp_Forget : Grp ⟶ Sets]，它正是这种类型的遗忘函子。 6.Awodey 部分的“伴随函子定理在树中的唯一应用是对角/乘积玩具示例”——[free_group_via_GAFT]，Instance/Grp/FreeAFT.v，以及 [GAFT_at_Sets_Id]，Adjunction/GAFT/Sets.v，它支撑 GAFT [Sets_Id_SolutionSet]。在所有 [.v] 文件（位于 [Adjunction/GAFT*] 之外）中进行 [grep -rnw GAFT] 扫描，这两个是定理在树中的唯一应用；其他所有内容都是散文或探查。（更正，#450：该扫描有日期。）这个文件本身在四个常量中应用了 [GAFT] —— [free_rng_ab_via_GAFT] 和 [free_ring_via_GAFT]，以及它们的循环读取 [free_rng_ab_via_GAFT_from_adjunction] 和 [free_ring_via_GAFT_from_adjunction] —— 并且自 #450 以来，Instance/Grp/Colimit.v 和 Instance/Rng/Colimit.v 在每个带有载体宇宙中的态射且对象在其下的形状的对角函子上应用它，Instance/Variety/Colimit.v 在集合等价类代数的对角函子和忘记函子上也应用了它。 

 六者中没有一个是在这里建立的——每一个在开始这个文件之前就在树中，这正是整个困难点，完全如 [Grp] 所示。没有过时的是问题的要求。

 ** 唯一真实缺失的，以及发现它只是名义上的在此文件之前，[grep -rnP '⊣\s*Rng_Forget(?![A-Za-z0-9_])'] 在所有 [.v] 文件中返回了 NOTHING：树中的没有一个附加物将字面值 [Rng_Forget : Rng ⟶ Sets] 作为其右附加物。Instance/Rng/Limit.v 记录了同样的测量结果，并为其自身目的得出了正确的结论，即 [right_adjoint_Continuous] 不会达到 [Rng_Forget]。该缺失是名义上的，而非结构性的，上述测量使其看起来有所不同。Instance/Rng/Free.v 的 [free_ring_via_ab_adjunction] 有右伴随 [RngUnderlyingAb]，其被定义为 [Ab_Forget ◯ Rng_Forget_Ab]——正是分解在数据上识别为 [Rng_Forget] 的复合。[Adjunction] (Theory/Adjunction.v) 的每个字段仅通过 [U y] 和 [fmap[U] f] 提到右伴随，因此这五个字段类型是可转换的，记录可以逐字段复制。这就是下面的 [free_ring_via_ab_adjunction_set]，这个技巧不是这里发明的：Instance/Rng/Free.v 的 [free_ring_via_mon_adjunction_ab] 是相同的复制，在相同两个相同基础集函子表示之间，理由在那里已经说明。所以第二个 GAFT 应用程序是可构建的，而早先关于此问题的解读得出的结论是它不可构建——仅基于 [grep]——这是错误的。[grep] 是对 NAMES 的测量；问题在于 TYPES。

 ** 问题正文中的两个隐藏复选框

 (A) Awodey §9.9 练习 9 要求“从代数范畴构建忘记函子的一组解，并从伴随函子定理推导自由构造，使得该定理在树中的应用是真正的。” 已经在两个函子上解决，在两种解读中都已处理。更正，PR “代数载体是集合”（2026-09-17）：本条款读作“在两个函子上解决，并揭示了循环性：下面的解集不是麦克莱恩的，因此推导是定理的应用而非独立构造。Awodey 的练习在其字面理解下得以满足——定理确实有应用——而非读者可能希望的理解，即自由环是由定理获得的。”读者想要的理解现在已交付：解集仍然不是麦克莱恩的（它们是项模型的合同商，而不是由基数上界截断的子环），但它们是在没有伴随的情况下构建的，所以自由环确实是由定理获得的。Instance/Grp/FreeAFT.v 已随此文件一起移动。(B) Fong & Spivak §3.4.2 示例 3.74 条款 1 要求“将结论作为 [Adjunction] 见证者交付，而不仅仅作为通用箭头，因此‘自由是遗忘的左伴随’的口号是在库中的陈述”。其支持句，“今天 Instance/CMon.v 提供了一个没有自由函子且没有伴随的遗忘函子，并且在树中不存在其他代数范畴”，前半部分是准确的，后半部分是陈旧的。[CMon_Forget] 仍然在 Instance/CMon.v，没有 [FreeCMon]，并且，测量来看，[grep -rnP '⊣\s*CMon_Forget(?![A-Za-z0-9_]）在所有 [.v] 文件中返回为空。但是另外五个代数范畴已经有了这个口号：
 [free_group_adjunction]  (Instance/Grp/Free.v)，
 [free_ab_adjunction]  (Instance/Ab/Free.v)，
 [free_mon_sets_adjunction]  (Instance/Mon/Free.v)，
 [free_module_adjunction]  (Instance/Mod/Free.v) 和
 [free_rng_ab_adjunction]  (Instance/Rng/Free.v)。这个文件真正补充了缺失的是环的字面底层集合函子上的口号：
 [free_ring_via_ab_adjunction_set : free_ring_via_ab ⊣ Rng_Forget] 
 根据上面两段的测量，这是这种形状类型树中的第一个元素。[Instance/CMon.v] 自身的空缺在这里并没有被填补；没有构建自由交换幺半群。修正 (#471)：这个空缺已由 Instance/CMon/Free.v 填补，其 [FreeCMon_adj] 是 FreeCMon 与 CMon_Forget 的伴随，因此“仍然……没有 [FreeCMon]” 的说法一直有效直到 #471。它的声明通过本地符号命名右伴随，上面字面上的 grep 只匹配该文件的两行注释。

 ** 比较子句位于 [≈]，不能是其他任何地方

 该问题要求每个“与通常构造比较”子句是“AFT 生成的伴随与显式自由对象的已证明同构”。[GAFT]（Adjunction/GAFT.v）结束于 [Qed]，因此其输出不会化简，并且其任何组成部分都无法命名。测量得出：

 示例 nr1：`1 free_ring_via_GAFT = free_ring_via_ab := eq_refl.被拒绝，提示“术语"eq_refl"的类型是`1 (free_ring_via_GAFT) = `1 (free_ring_via_GAFT)" while it is expected to have type "` 1 (free_ring_via_GAFT) = free_ring_via_ab"（无法统一"`1 (free_ring_via_GAFT)"和"free_ring_via_ab"）。因此没有在任何地方声称关于GAFT输出的 [eq_refl]，并且下面三次比较都在 [≈]，由 [left_adjoints_agree] （Instance/Rng/Free.v）进行——固定函子的左伴随是同构的。该提供者是 [Defined]，因此比较态射有一个名称（[adj_left_compare]），且单位条款（[adj_left_compare_unit]）是可用的；Mac Lane 的练习要求两者。Theory/Adjunction.v 的 [left_adjoint_iso] 属于相同类型，并且被记录在每个比较旁边，因此该声明由机器检查了两次。

 ** 已交付内容是什么1. 在对象和态射上的因式分解，见 [eq_refl]。 2. [Rng_Forget_Ab_continuous : ContinuousFunctor Rng_Forget_Ab]，以及其仅顶点的推论 [Rng_Forget_Ab_PreservesAllLimits] —— 真正新的、非循环的结果，在没有伴随（ADJUNCTION）和没有 RAPL 的情况下得出——尽管绝对不是没有创建，因为它的两个输入都是创建结果（Instance/Rng/Limit.v 的 [creates_limits_continuous ...] 和 Instance/Ab/Limit.v 的 [creates_reflects_limits ...]）；它避免的是对 [Rng_Forget_Ab] 本身的创建论证，这是导致停止的那个。没有伴随，也没有 RAPL。 3. [Rng_Forget_Ab_reflects_limits : ReflectsLimitCone K Rng_Forget_Ab]，同一复合在另一个方向的读法，也无需伴随。 4. [free_ring_via_ab_adjunction_set : free_ring_via_ab ⊣ Rng_Forget]，重新类型化，即 Seven Sketches 条款和在 [Rng_Forget] 的第三个 GAFT 假设合二为一。 5.四组解集（早期版本说是两组）：两组非循环的由自由环项模型上的 [Prop] 合同式构建的 [Rng_Forget_Ab_solution_set_prop] 和 [Rng_Forget_solution_set_prop]，被两个主要的 GAFT 应用 [free_rng_ab_via_GAFT] 和 [free_ring_via_GAFT] 使用；还有两组循环的，保留了名称中表示循环的命名，被 [free_rng_ab_via_GAFT_from_adjunction] 和 [free_ring_via_GAFT_from_adjunction] 使用。6. 在 [≈] 有三个比较子句，每个子句都有其命名的比较同态及其单位方程：针对 [FreeRngAb]、针对 [free_ring_via_ab] 和针对 [free_ring_via_mon]。前两者关于非循环常数；第三个关于 [free_ring_via_GAFT_from_adjunction]，原因是子句中记录的测量宇宙的原因。

 条目 1-4 完全不依赖于 AFT 应用，且它们都不是循环的。**未送达(1) [Rng_Forget_Ab] 没有创建结果，并且没有修复双线性障碍 Instance/Rng/Limit.v 记录。连续性严格小于创建，这里没有任何东西将两者作为命题进行比较。 (2) 没有基于 [Complete Ab] 的路线：[Ab_Complete] (Instance/Ab/Limit.v) 存在但未被使用，因为 GAFT 在 [Rng_Forget_Ab] 运行，因此需要 [Complete Rng]，而不是 [Complete Ab]。 (3) 没有麦克莱恩自身形状的解集。更正，PR “代数承载是集合”(2026-09-17)：该条款写为“没有非循环解集”，这是错误的——上方有两个。仍然正确的是，该条款接着说，麦克莱恩自身的族没有构建：由一个集合的像生成的子环，受到基数约束，需要一个在 [RingObject] 上不存在的生成子环 API。在 [Grp] 的类似间隙被归档为 #1309，同时包含了 Instance/Discrete.v 的 [DiscreteCat_Functor] 的宇宙最小化工件——后者之后已被修复——而 [Rng] 的情况仍然满足前者。这里没有尝试解决它。相反，提供的是一个合同商-商族，这是同一结论的不同论证。（Instance/Mod/TensorAFT.v 第 10 节显示两个论证在 [RMod R] 汇合，Mac Lane 的族在同构意义下是小的，合同商作为其小指数；这里没有建立这样的桥梁。） (4) 该问题的图形部分未涉及。通过 GAFT 构造类别到图的遗忘函子（forgetful functor）的左伴随，并将其与 Construction/Free/Quiver.v 中的 [FreeForgetfulAdjunction] 比较——问题正文给出的该常量位置已经过时、已测量——需要 [Complete StrictCat] 以及该遗忘函子的连续性；树中的唯一完备性存在于 Instance/Cat/Limit.v 的 [StrictCat_Complete] ，这依赖于 [∀ C, ObjUIP C] 和 [DepFunext]，因此会把这些假设传递到下游的每个常量，并且 [grep -rnE 'ContinuousFunctor (Forgetful|Quiver)'] 不返回任何内容。 (5) 没有单子性（MONADICITY）和没有比较函子，因此这里没有任何东西表明 [Rng] 是 Eilenberg-Moore 范畴；Riehl §5.6 例 5.6.8 仍然只是一个观察，如 Instance/Rng/Limit.v 已经记录的。 (6) 没有与此文件配套的 [Test/Probe] 文件。下面的 [eq_refl] 回读仅通过在此文件中成为 [Example] 来保护，而标题中引用的两个拒绝 —— [ContinuousFunctor] / [PreservesImageLimit] 指定和非还原 GAFT 输出 —— 在此进行测量但未固定在任何地方。那是一个缺口，而不是声明。(7) 没有任何内容被注册为 [Instance]；文件未声明任何。 

 ** 状态：无公理在 [.glob] 文件中统计 [def] + [prf] 头部，该文件声明了三十四个常量且没有 [Program] 义务——它完全没有使用 [Program]，因此源级别阅读中看不到的义务陷阱并未在这里出现。[Print Assumptions] 对所有三十四个常量报告“在全局上下文下关闭”，可通过名称回读：[rng_forget_factors_obj]、[rng_forget_factors_map]、[rng_underlying_ab_is_forget_obj]、[rng_underlying_ab_is_forget_map]、[rng_ab_recone]、[rng_sets_recone]、[rng_ab_image_limit]、[rng_ab_limit_cone]、[rng_ab_reflect]、[Rng_Forget_Ab_continuous]、[Rng_Forget_Ab_PreservesAllLimits]、[Rng_Forget_Ab_reflects_limits]、[free_ring_via_ab_adjunction_set]、[free_ring_via_mon_adjunction_set]、[free_ring_via_ab_adjunction_set_transpose]、[Rng_Forget_Ab_solution_set_from_adjunction]、[Rng_Forget_solution_set_from_adjunction]、[free_rng_ab_via_GAFT]、[free_ring_via_GAFT]、三个 [_agrees] 比较、它们的三个 [_via_left_adjoint_iso] 交叉检查、三个 [_comparison] 同态映射、三个 [_comparison_is_component] 回读以及三个 [_unit] 条款。这是对该文件自身常量的回读，而不是目录范围的认证，并且这里没有任何内容注册到 [make print-assumptions]。

 三十四个中有八个是 [eq_refl] 示例：四个分解回读、转置回读以及三个 [_comparison_is_component] 回读。关于 GAFT 输出没有声明任何 [eq_refl]。

 该文件对 [make todo] 没有贡献任何命中。
*)

(* * * The factorization of [Rng_Forget] through [Ab] / * * 通过 [Ab] 对 [Rng_Forget] 的因式分解 *)

(*
 On data these two functors are the same term.  The records are not
 convertible -- see the header -- which is why the two recones below
 exist at all. 

 --------
 在数据上，这两个函子是相同的术语。记录不可转换——见标题——这就是下面存在这两个重构的原因。
*)

Example rng_forget_factors_obj (R : Rng) :
  fobj[Rng_Forget] R = fobj[Ab_Forget ◯ Rng_Forget_Ab] R := eq_refl.

Example rng_forget_factors_map (R S : Rng) (f : R ~{Rng}~> S) :
  fmap[Rng_Forget] f = fmap[Ab_Forget ◯ Rng_Forget_Ab] f := eq_refl.

(*
 [RngUnderlyingAb] (Instance/Rng/Free.v) IS that composite, so the
 same two readbacks hold against it.  These are what make the retyping of
 [free_ring_via_ab_adjunction] typecheck. 

 --------
 [RngUnderlyingAb] (Instance/Rng/Free.v) 是那个复合类型，因此相同的两个读回在它上面也成立。这些正是使 [free_ring_via_ab_adjunction] 的重类型检查通过的原因。
*)

Example rng_underlying_ab_is_forget_obj (R : Rng) :
  fobj[RngUnderlyingAb] R = fobj[Rng_Forget] R := eq_refl.

Example rng_underlying_ab_is_forget_map (R S : Rng) (f : R ~{Rng}~> S) :
  fmap[RngUnderlyingAb] f = fmap[Rng_Forget] f := eq_refl.

(*
   * * Continuity of [Rng_Forget_Ab], without a creation argument FOR IT,
   and without RAPL 

   --------
   * * [Rng_Forget_Ab] 的连续性，没有为它提供创建参数，也没有 RAPL
*)

Section RngAbContinuity.

Context {J : Category}.
Context (K : J ⟶ Rng).

(*
 A cone over [Ab_Forget ◯ (Rng_Forget_Ab ◯ K)] rebuilt as a cone over
 [Rng_Forget ◯ K].  Apex, legs and coherence proof are reused verbatim;
 only the diagram record changes, and every type the fields inhabit is
 convertible by the factorization above. 

 --------
 一个以 [Ab_Forget ◯ (Rng_Forget_Ab ◯ K)] 为底的圆锥被重建为以 [Rng_Forget ◯ K] 为底的圆锥。顶点、侧棱和一致性证明完全照搬；只有图表记录发生变化，并且每个字段所处的类型都可以通过上述因式分解进行转换。
*)
Definition rng_ab_recone (M : Cone (Ab_Forget ◯ (Rng_Forget_Ab ◯ K)))
  : Cone (Rng_Forget ◯ K) :=
  @Build_Cone J Sets (Rng_Forget ◯ K) vertex_obj[M]
    (@Build_ACone J Sets vertex_obj[M] (Rng_Forget ◯ K)
       (fun j => cone_leg M j)
       (fun x y f => @cone_coherence J Sets _ _ (@coneFrom _ _ _ M) x y f)).

(* The other direction, needed for the reflection clause. / 另一方向，需要用于反射条款。 *)
Definition rng_sets_recone (M : Cone (Rng_Forget ◯ K))
  : Cone (Ab_Forget ◯ (Rng_Forget_Ab ◯ K)) :=
  @Build_Cone J Sets (Ab_Forget ◯ (Rng_Forget_Ab ◯ K)) vertex_obj[M]
    (@Build_ACone J Sets vertex_obj[M] (Ab_Forget ◯ (Rng_Forget_Ab ◯ K))
       (fun j => cone_leg M j)
       (fun x y f => @cone_coherence J Sets _ _ (@coneFrom _ _ _ M) x y f)).

(*
 Step one: the image of a limiting cone of rings under [Ab_Forget ◯
 Rng_Forget_Ab] is limiting, because that composite's image cone IS
 [Rng_Forget]'s, and [Rng_Forget] is continuous.  Every cone the goal
 quantifies over is re-presented by [rng_ab_recone]; no tactic is
 involved. 

 --------
 第一步：在 [Ab_Forget ◯ Rng_Forget_Ab] 下，环的极限锥的像是极限的，因为该复合的像锥确实是 [Rng_Forget] 的，而 [Rng_Forget] 是连续的。目标量化的每一个锥都由 [rng_ab_recone] 重新表示；这不涉及任何策略。
*)
Definition rng_ab_image_limit (N : Cone K) (HN : IsLimitCone N) :
  IsLimitCone (FCone Ab_Forget (FCone Rng_Forget_Ab N)) :=
  fun M => Rng_Forget_continuous J K N HN (rng_ab_recone M).

(*
 Step two: [Ab_Forget] reflects limit cones, so the [Ab]-level cone is
 limiting.  This is where the bilinearity obstruction is bypassed -- the
 ring multiplication on the apex is never built over [Ab]. 

 --------
 步骤二：[Ab_Forget] 反映了限制锥，因此 [Ab] 级别的锥是限制性的。这就是双线性阻塞被绕过的地方——顶点上的环乘法从未在 [Ab] 上构建。
*)
Definition rng_ab_limit_cone (N : Cone K) (HN : IsLimitCone N) :
  IsLimitCone (FCone Rng_Forget_Ab N) :=
  Ab_Forget_reflects_limits (Rng_Forget_Ab ◯ K) (FCone Rng_Forget_Ab N)
    (rng_ab_image_limit N HN).

(*
 The same composite read backwards: [Ab_Forget] is continuous by
 creation ([Ab_Forget_creates_continuous], Instance/Ab/Limit.v, which
 presupposes no adjunction either), and [Rng_Forget] reflects. 

 --------
 相同的复合体倒过来读：[Ab_Forget] 是通过创建连续的（[Ab_Forget_creates_continuous]，Instance/Ab/Limit.v，它也不假设任何附加），而 [Rng_Forget] 则是反射的。
*)
Definition rng_ab_reflect (N : Cone K)
  (HN : IsLimitCone (FCone Rng_Forget_Ab N)) : IsLimitCone N :=
  Rng_Forget_reflects_limits K N
    (fun M =>
       Ab_Forget_creates_continuous J (Rng_Forget_Ab ◯ K)
         (FCone Rng_Forget_Ab N) HN (rng_sets_recone M)).

End RngAbContinuity.

(** The headline non-circular result. / 主要非循环结果。 *)
Definition Rng_Forget_Ab_continuous : ContinuousFunctor Rng_Forget_Ab :=
  fun J K N HN => rng_ab_limit_cone K N HN.

Definition Rng_Forget_Ab_PreservesAllLimits :
  PreservesAllLimits Rng_Forget_Ab :=
  Continuous_PreservesAllLimits Rng_Forget_Ab_continuous.

Definition Rng_Forget_Ab_reflects_limits {J : Category} (K : J ⟶ Rng) :
  ReflectsLimitCone K Rng_Forget_Ab :=
  fun N HN => rng_ab_reflect K N HN.

(* * * The underlying-set adjunction, retyped onto [Rng_Forget] / * * 底层集合伴随，重新类型化到 [Rng_Forget] *)

(*
 Instance/Rng/Free.v states the composite adjunction against
 [RngUnderlyingAb].  Every field of [Adjunction] mentions the right
 adjoint only through [U y] and [fmap[U] f], and the two readbacks above
 say those agree definitionally, so the five field types are convertible
 and the record copies across.  This is Instance/Rng/Free.v's own
 manoeuvre at the other pair of presentations.

 This is the first inhabitant in tree of [_ ⊣ Rng_Forget]: see the header
 for the measurement, and for why its absence was nominal. 

 --------
 Instance/Rng/Free.v 陈述了相对于 [RngUnderlyingAb] 的复合伴随。[Adjunction] 的每一个域仅通过 [U y] 和 [fmap[U] f] 提及右伴随，上面的两个读回说明它们在定义上是相符的，因此五个字段类型是可转换的，并且记录可以复制过来。这是 Instance/Rng/Free.v 在另一对表示上的操作手法。

 这是 [_ ⊣ Rng_Forget] 树中的第一个元素：见标题了解测量，以及为什么它的缺失是名义上的。
*)

Definition free_ring_via_ab_adjunction_set : free_ring_via_ab ⊣ Rng_Forget :=
  @Build_Adjunction Rng Sets free_ring_via_ab Rng_Forget
    (@adj _ _ _ _ free_ring_via_ab_adjunction)
    (@to_adj_nat_l _ _ _ _ free_ring_via_ab_adjunction)
    (@to_adj_nat_r _ _ _ _ free_ring_via_ab_adjunction)
    (@from_adj_nat_l _ _ _ _ free_ring_via_ab_adjunction)
    (@from_adj_nat_r _ _ _ _ free_ring_via_ab_adjunction).

(*
 The monoid route retyped the same way, so that the comparison below can
 be made against BOTH explicit constructions rather than only one. 

 --------
 幺半群路径以相同的方式重新输入，以便下面的比较可以针对两种显式构造而不是仅针对一种进行。
*)
Definition free_ring_via_mon_adjunction_set : free_ring_via_mon ⊣ Rng_Forget :=
  @Build_Adjunction Rng Sets free_ring_via_mon Rng_Forget
    (@adj _ _ _ _ free_ring_via_mon_adjunction_ab)
    (@to_adj_nat_l _ _ _ _ free_ring_via_mon_adjunction_ab)
    (@to_adj_nat_r _ _ _ _ free_ring_via_mon_adjunction_ab)
    (@from_adj_nat_l _ _ _ _ free_ring_via_mon_adjunction_ab)
    (@from_adj_nat_r _ _ _ _ free_ring_via_mon_adjunction_ab).

(* The retyping is inert on the transpose, hence on the unit. / 在转置上重新输入是惰性的，因此在单位上也是如此。 *)
Example free_ring_via_ab_adjunction_set_transpose (X : Sets) (R : Rng)
  (f : free_ring_via_ab X ~{Rng}~> R) :
  to (@adj _ _ _ _ free_ring_via_ab_adjunction_set X R) f
    = to (@adj _ _ _ _ free_ring_via_ab_adjunction X R) f := eq_refl.

(* * * [Prop] congruences on the free-ring terms / * * [Prop] 自由环项上的同余 *)

(*
 THE NON-CIRCULAR SOLUTION SETS.

 A solution set for [Rng_Forget_Ab] at [A] must be a family of rings, at
 the universe the theorem demands, through which every homomorphism out
 of [A] factors.  The family used here is the QUOTIENTS OF THE FREE-RING
 TERM MODEL by [Prop]-valued congruences: [FRTerm A]
 (Instance/Rng/Free.v) with its relation [fr_eq], which is already a
 [Prop] inductive since the PR "algebraic carriers are sets"
 (2026-09-17).

 WHY THE INDEX IS THE RIGHT SIZE.  Every field of [IsRngCongruence] is a
 [Prop], so the record is a [Prop] and the sigma over it lands at the
 carrier universe rather than one above it.  Structure/Complete.v's SIZE
 NOTE, item 1, is the authority and is not restated; item 2(b) is why the
 index universe has to be the carrier universe in the first place.  The
 same device serves Instance/Mod/TensorAFT.v (section 3A) and
 Instance/Grp/FreeAFT.v.

 NO [PropEquiv] HYPOTHESIS ANYWHERE BELOW: [rig_prop] is a field of
 [RigObject] and [cmon_prop] a field of [CMonObject], both with
 [#[export] Existing Instance], so the kernel congruence of an evaluation
 is available at every ring with no side condition. 

 --------
 非循环解集。

 [Rng_Forget_Ab] 在 [A] 的解集必须是一个环族，在宇宙中定理要求，通过这个环族，每一个从 [A] 出发的同态都可以分解。这里使用的族是由 [Prop] 值的合同数构成的自由环项模型的商：[FRTerm A]（Instance/Rng/Free.v）及其关系 [fr_eq]，这已经是一个 [Prop] 归纳结构，因为 PR "代数承载体是集合"（2026-09-17）。为什么索引是合适的大小。[IsRngCongruence] 的每个字段都是 [Prop]，因此记录是 [Prop]，并且对它的求和作用在承载宇宙上，而不是其之上。Structure/Complete.v 的 SIZE 注释，第 1 项是权威且不再重复；第 2(b) 项说明了索引宇宙为什么必须首先是承载宇宙。同样的方法也适用于 Instance/Mod/TensorAFT.v（第 3A 节）和 Instance/Grp/FreeAFT.v。

 以下任何地方都没有 [PropEquiv] 假设：[rig_prop] 是 [RigObject] 的一个字段，[cmon_prop] 是 [CMonObject] 的一个字段，两者都有 [#[export] 的现有实例，因此评估的核同余在每个环上都是可用的，无需附加条件。
*)

Section RngCongruence.

Context (A : AbObject).

Record IsRngCongruence (Rq : FRTerm A → FRTerm A → Prop) : Prop := {
  rc_refl  : ∀ s, Rq s s;
  rc_sym   : ∀ s t, Rq s t → Rq t s;
  rc_trans : ∀ s t u, Rq s t → Rq t u → Rq s u;
  rc_gen   : ∀ s t, fr_eq s t → Rq s t;
  rc_plus  : ∀ s s' t t', Rq s s' → Rq t t' →
               Rq (@fr_plus A s t) (@fr_plus A s' t');
  rc_neg   : ∀ s s', Rq s s' → Rq (@fr_neg A s) (@fr_neg A s');
  rc_mul   : ∀ s s' t t', Rq s s' → Rq t t' →
               Rq (@fr_mul A s t) (@fr_mul A s' t')
}.

Definition RngCongIdx : Type :=
  { Rq : FRTerm A → FRTerm A → Prop & IsRngCongruence Rq }.

(*
 NAMED for [PropEquiv_of_relation]'s sake: written inline, its setoid
 argument is found by resolution, which picks the AMBIENT term setoid
 rather than the quotient's, and both implications are then refused. 

 --------
 为了[PropEquiv_of_relation]的缘故而命名：以内联方式编写，其集合论参数通过解析找到，该解析选择的是环境项的集合论而不是商的集合论，然后两个蕴含都被拒绝。
*)
Definition QRng_Setoid (Rq : FRTerm A → FRTerm A → Prop)
  (H : IsRngCongruence Rq) : Setoid (FRTerm A) :=
  {| equiv := Rq
   ; setoid_equiv :=
       {| Equivalence_Reflexive  := rc_refl  Rq H
        ; Equivalence_Symmetric  := rc_sym   Rq H
        ; Equivalence_Transitive := rc_trans Rq H |} |}.

(* The quotient ring, at the SAME [Rng] instance. Every law is the term model's own law passed through [rc_gen]. / 商环，在同一 [Rng] 实例中。每条定律都是通过 [rc_gen] 的模型自身定律。 *)
Definition QRng (Rq : FRTerm A → FRTerm A → Prop) (H : IsRngCongruence Rq)
  : RingObject :=
  {| ring_rig := {|
       rig_setoid :=
         {| carrier := FRTerm A
          ; is_setoid := QRng_Setoid Rq H |};
       rig_zero := @fr_zero A;
       rig_add  := @fr_plus A;
       rig_one  := @fr_one A;
       rig_mul  := @fr_mul A;
       rig_add_respects := fun _ _ Hs _ _ Ht => rc_plus Rq H _ _ _ _ Hs Ht;
       rig_mul_respects := fun _ _ Hs _ _ Ht => rc_mul Rq H _ _ _ _ Hs Ht;
       rig_add_assoc := fun s t u => rc_gen Rq H _ _ (fre_add_assoc s t u);
       rig_add_comm := fun s t => rc_gen Rq H _ _ (fre_add_comm s t);
       rig_add_zero_l := fun s => rc_gen Rq H _ _ (fre_add_zero_l s);
       rig_mul_assoc := fun s t u => rc_gen Rq H _ _ (fre_mul_assoc s t u);
       rig_mul_one_l := fun s => rc_gen Rq H _ _ (fre_mul_one_l s);
       rig_mul_one_r := fun s => rc_gen Rq H _ _ (fre_mul_one_r s);
       rig_distr_l := fun s t u => rc_gen Rq H _ _ (fre_distr_l s t u);
       rig_distr_r := fun s t u => rc_gen Rq H _ _ (fre_distr_r s t u);
       rig_mul_zero_l := fun s => rc_gen Rq H _ _ (fr_mul_zero_l A s);
       rig_mul_zero_r := fun s => rc_gen Rq H _ _ (fr_mul_zero_r A s);
       rig_prop := @PropEquiv_of_relation _ (QRng_Setoid Rq H) Rq
                     (fun _ _ h => h) (fun _ _ h => h)
     |};
     ring_neg := @fr_neg A;
     ring_neg_respects := fun _ _ Hs => rc_neg Rq H _ _ Hs;
     ring_neg_l := fun s => rc_gen Rq H _ _ (fre_neg_l s)
  |}.

(* The canonical insertion of [A] into the quotient. / [A] 在商中的规范插入。 *)
Definition QRng_insert (Rq : FRTerm A → FRTerm A → Prop)
  (H : IsRngCongruence Rq) : A ~{Ab}~> Rng_Forget_Ab (QRng Rq H).
Proof.
  unshelve refine {| cmon_map := _ |}.
  - unshelve refine {| morphism := @fr_gen A |}.
    intros a b Hab; exact (rc_gen Rq H _ _ (fre_gen Hab)).
  - exact (rc_gen Rq H _ _ (@fre_gen_zero A)).
  - intros a b; exact (rc_gen Rq H _ _ (fre_gen_plus a b)).
Defined.

End RngCongruence.

Arguments IsRngCongruence {A} Rq.
Arguments RngCongIdx A.
Arguments QRng_Setoid {A} Rq H.
Arguments QRng {A} Rq H.
Arguments QRng_insert {A} Rq H.

(* THE KERNEL CONGRUENCE of a ring-valued extension, and the covering. / 环值扩张的核合同以及覆盖。 *)

Section RngKernel.

Context (A : AbObject).
Context (R : RingObject).
Context (h : A ~{Ab}~> Rng_Forget_Ab R).

Definition rng_ker : FRTerm A → FRTerm A → Prop :=
  fun s t => @pequiv _ _ (rig_prop R) (fr_eval h s) (fr_eval h t).

Lemma rng_ker_is_cong : IsRngCongruence rng_ker.
Proof.
  unfold rng_ker.
  constructor.
  - intro s; apply (@pequiv_from _ _ (rig_prop R)); reflexivity.
  - intros s t Hst; apply (@pequiv_from _ _ (rig_prop R)); symmetry;
      exact (@pequiv_to _ _ (rig_prop R) _ _ Hst).
  - intros s t u H1 H2; apply (@pequiv_from _ _ (rig_prop R)).
    transitivity (fr_eval h t);
      [ exact (@pequiv_to _ _ (rig_prop R) _ _ H1)
      | exact (@pequiv_to _ _ (rig_prop R) _ _ H2) ].
  (*
 [fr_eval_respects] takes [R] EXPLICITLY (Instance/Rng/Free.v)
 while [fr_eval] takes both implicitly. 

 --------
 [fr_eval_respects] 明确地采用 [R]（实例/范围/Free.v），而 [fr_eval] 则同时隐式采用两者。
*)
  - intros s t Hst; apply (@pequiv_from _ _ (rig_prop R));
      exact (fr_eval_respects R h s t Hst).
  - intros s s' t t' H1 H2; apply (@pequiv_from _ _ (rig_prop R)); simpl.
    exact (rig_add_respects R _ _ (@pequiv_to _ _ (rig_prop R) _ _ H1)
                              _ _ (@pequiv_to _ _ (rig_prop R) _ _ H2)).
  - intros s s' H1; apply (@pequiv_from _ _ (rig_prop R)); simpl.
    exact (ring_neg_respects R _ _ (@pequiv_to _ _ (rig_prop R) _ _ H1)).
  - intros s s' t t' H1 H2; apply (@pequiv_from _ _ (rig_prop R)); simpl.
    exact (rig_mul_respects R _ _ (@pequiv_to _ _ (rig_prop R) _ _ H1)
                              _ _ (@pequiv_to _ _ (rig_prop R) _ _ H2)).
Qed.

Definition rng_ker_idx : RngCongIdx A := existT _ rng_ker rng_ker_is_cong.

(* The mediator out of the quotient: respectfulness IS [pequiv_to]. / 商之外的调解者：尊重是 [pequiv_to]。 *)
Program Definition rng_ker_med : QRng rng_ker rng_ker_is_cong ~{Rng}~> R := {|
  rig_map := {| morphism := fr_eval h |}
|}.
Solve All Obligations with
  (first [ (intros s t Hst; exact (@pequiv_to _ _ (rig_prop R) _ _ Hst))
         | (intros; simpl; reflexivity) ]).

(* The covering equation, on the nose. / 遮盖方程，恰到好处。 *)
Example rng_ker_factors (a : carrier (cmon_setoid A)) :
  rig_map rng_ker_med (cmon_map (QRng_insert rng_ker rng_ker_is_cong) a)
  = cmon_map h a
  := eq_refl.

End RngKernel.

Arguments rng_ker {A R} h.
Arguments rng_ker_is_cong {A R} h.
Arguments rng_ker_idx {A R} h.
Arguments rng_ker_med {A R} h.

(* NAMED so that both record fields elaborate [QRng] at ONE universe instance; written inline they mint two and the record is refused. / 命名以便两个记录字段在一个宇宙实例中详细说明 [QRng]；内联写入时，它们会生成两个，记录被拒绝。 *)
Definition QRngOf {A : Ab} (i : RngCongIdx A) : obj[Rng] :=
  QRng (`1 i) (`2 i).

Definition QRngInsertOf {A : Ab} (i : RngCongIdx A)
  : A ~{Ab}~> Rng_Forget_Ab (QRngOf i) := QRng_insert (`1 i) (`2 i).

Definition Rng_Forget_Ab_solution_set_prop (A : Ab) :
  SolutionSet Rng_Forget_Ab A.
Proof.
  unshelve refine (@Build_SolutionSet Rng Ab Rng_Forget_Ab A
                     (RngCongIdx A) QRngOf QRngInsertOf _).
  intros c h.
  exists (rng_ker_idx h), (rng_ker_med h).
  intro a; simpl; reflexivity.
Defined.

(*
 THE [Rng_Forget] HALF, TAKEN DIRECTLY AND NOT AS A COMPOSITE.

 The free ring on a SET is the free ring on the free abelian group on it
 ([free_ring_via_ab := FreeRngAb ◯ FreeAb], Instance/Rng/Free.v), so
 the SAME congruence index over [FreeAbObject X] and the SAME quotients
 serve; only the covering changes, by one transposition through
 [free_ab_extend].  Cost over the [Ab] case: three lines and no new
 vocabulary.

 THE COMPOSITE ROUTE WAS MEASURED AND NOT TAKEN.  Composing through
 Adjunction/Compose.v would need a GAFT application for [Ab_Forget] as
 well -- a fourth term model and a fourth congruence class -- or else
 would lean on the already-in-tree [free_ab_adjunction], which would make
 the result an adjunction-COMPOSITION rather than a GAFT application and
 leave [free_ring_via_GAFT] naming a theorem it did not prove.

 ONE TRAP: [free_ab_extend h] will not elaborate against an open [?A0]
 ([h : X ~> Rng_Forget c] and [X ~> Ab_Forget ?A0] are convertible but
 not unifiable), so the target is given explicitly. 

 --------
 [Rng_Forget] 的一半，直接取而不是作为合成。

 在一个集合上的自由环是该集合上的自由阿贝尔群的自由环（[free_ring_via_ab := FreeRngAb ◯ FreeAb]，Instance/Rng/Free.v），所以在 [FreeAbObject X] 上相同的同余指数和相同的商环都适用；唯一改变的是覆盖，通过 [free_ab_extend] 的一次换位。相对于 [Ab] 的情况，代价：三行代码，没有新增词汇。

 合成路线已测量但未采用。通过 Adjunction/Compose.v 进行合成将需要对 [Ab_Forget] 也进行 GAFT 应用——即第四项模型和第四个同余类——否则就必须依赖已经在树中的 [free_ab_adjunction]，这将使结果成为一个伴随-合成，而不是 GAFT 应用，并且会让 [free_ring_via_GAFT] 命名一个它并未证明的定理。一个陷阱：[free_ab_extend h] 不会对一个开放的 [?A0] 进行详细说明（[h : X ~> Rng_Forget c] 和 [X ~> Ab_Forget ?A0] 可以转换但不能统一），因此目标是明确给出的。
*)

Definition Rng_Forget_solution_set_prop (X : Sets) :
  SolutionSet Rng_Forget X.
Proof.
  unshelve refine (@Build_SolutionSet Rng Sets Rng_Forget X
                     (RngCongIdx (FreeAbObject X)) QRngOf
                     (fun i => fmap[Ab_Forget] (QRngInsertOf i)
                                 ∘ free_ab_unit X) _).
  intros c h.
  exists (rng_ker_idx (@free_ab_extend X (Rng_Forget_Ab c) h)),
         (rng_ker_med (@free_ab_extend X (Rng_Forget_Ab c) h)).
  intro a; simpl.
  reflexivity.
Defined.

(* * * The two solution sets, and the two GAFT applications / * * 两个解集，以及两个 GAFT 应用 *)

(*
 THE CIRCULAR DISCHARGES, KEPT FOR COMPARISON; REMOVAL CANDIDATES FOR
 JOHN.  Each is named so that the circularity is visible at every use
 site rather than buried in a term: the family is the singleton at the
 unit of the adjunction the theorem is being asked to produce.

 CORRECTION, PR "algebraic carriers are sets" (2026-09-17): these two are
 no longer what the GAFT applications below consume.  They are kept
 because removing working code is John's call, because the naming
 convention they establish is what makes the circularity legible, and
 because they are the honest comparison -- two different solution sets
 for one functor, one read off the answer and one not. 

 --------
 循环的排放，保留用于比较；约翰的移除候选。每个名称都使循环性在每个使用位置可见，而不是隐藏在某个术语中：该族是附加单位上的单例，定理正是要求生成的。

 更正，PR“代数载体是集合”（2026-09-17）：这两个不再是下文 GAFT 应用所使用的。保留它们是因为移除工作代码由约翰决定，因为它们确立的命名规范使循环性可读，并且因为它们是诚实的比较——一个函子有两个不同的解集，一个从答案中读取，另一个则没有。
*)

Definition Rng_Forget_Ab_solution_set_from_adjunction (A : Ab) :
  SolutionSet Rng_Forget_Ab A :=
  solution_set_of_adjunction free_rng_ab_adjunction A.

Definition Rng_Forget_solution_set_from_adjunction (X : Sets) :
  SolutionSet Rng_Forget X :=
  solution_set_of_adjunction free_ring_via_ab_adjunction_set X.

(*
 Mac Lane §V.6 Exercise 2, first half: the tensor/monoid ring on an
 abelian group.  [Continuous_PreservesImageLimit] is load-bearing -- see
 the header's measurement of what happens without it.

 NON-CIRCULAR since the PR "algebraic carriers are sets": the solution
 set is [Rng_Forget_Ab_solution_set_prop], built from the free-ring term
 model and its [Prop] congruences.  Strip Instance/Rng/Free.v's
 ADJUNCTIONS and this still stands; strip its TERM MODEL and it does
 not, which is the honest statement of what it depends on. 

 --------
 Mac Lane §V.6 练习 2，上半部分：在阿贝尔群上的张量/单子环。[Continuous_PreservesImageLimit] 承重——参见标题中关于没有它会发生什么的测量。

 非循环，因为 PR “代数载体是集合”：解集是 [Rng_Forget_Ab_solution_set_prop]，由自由环项模型及其 [Prop] 同余构建。去掉 Instance/Rng/Free.v 的 ADJUNCTIONS，这仍然成立；去掉它的 TERM MODEL，则不成立，这是对其依赖关系的真实描述。
*)
Definition free_rng_ab_via_GAFT : ∃ F : Ab ⟶ Rng, F ⊣ Rng_Forget_Ab :=
  GAFT Rng_Forget_Ab Rng_Complete
       (Continuous_PreservesImageLimit Rng_Forget_Ab_continuous)
       Rng_Forget_Ab_solution_set_prop.

(* Second half: the free ring on a set, likewise non-circular. / 下半部分：集合上的自由环，同样是非循环的。 *)
Definition free_ring_via_GAFT : ∃ F : Sets ⟶ Rng, F ⊣ Rng_Forget :=
  GAFT Rng_Forget Rng_Complete
       (Continuous_PreservesImageLimit Rng_Forget_continuous)
       Rng_Forget_solution_set_prop.

(* The circular readings, kept under names that say so. / 循环读数，以说明其用途的名称保存。 *)
Definition free_rng_ab_via_GAFT_from_adjunction :
  ∃ F : Ab ⟶ Rng, F ⊣ Rng_Forget_Ab :=
  GAFT Rng_Forget_Ab Rng_Complete
       (Continuous_PreservesImageLimit Rng_Forget_Ab_continuous)
       Rng_Forget_Ab_solution_set_from_adjunction.

Definition free_ring_via_GAFT_from_adjunction :
  ∃ F : Sets ⟶ Rng, F ⊣ Rng_Forget :=
  GAFT Rng_Forget Rng_Complete
       (Continuous_PreservesImageLimit Rng_Forget_continuous)
       Rng_Forget_solution_set_from_adjunction.

(** * The comparison clauses, at [≈] / * 比较从句，在 [≈] *)

(*
 [GAFT] is [Qed], so its output does not reduce and no [eq_refl] is
 available; the header quotes the refusal.  What IS available is the
 uniqueness of left adjoints, and [left_adjoints_agree]
 (Instance/Rng/Free.v) is [Defined], so the comparison morphism has a
 name and the unit clause can be stated. 

 --------
 [GAFT] 是 [Qed]，因此其输出不会减少，也没有 [eq_refl] 可用；标题引用了拒绝。可用的是左伴随的唯一性，而 [left_adjoints_agree] (Instance/Rng/Free.v) 是 [Defined]，因此比较态射有一个名称，并且可以陈述单元子句。
*)

Definition free_rng_ab_via_GAFT_agrees : `1 free_rng_ab_via_GAFT ≈ FreeRngAb :=
  left_adjoints_agree (`2 free_rng_ab_via_GAFT) free_rng_ab_adjunction.

Definition free_ring_via_GAFT_agrees :
  `1 free_ring_via_GAFT ≈ free_ring_via_ab :=
  left_adjoints_agree (`2 free_ring_via_GAFT) free_ring_via_ab_adjunction_set.

(*
 RECORDED STATEMENT CHANGE, PR "algebraic carriers are sets"
 (2026-09-17), AND THE MEASURED REASON.  This clause and the four other
 [_mon] ones below used to be stated about [free_ring_via_GAFT] and are
 now stated about [free_ring_via_GAFT_from_adjunction], the circular
 reading.  Nothing is lost -- the same theorem, "left adjoints to
 [Rng_Forget] agree", is still in tree against the monoid-ring route --
 but the WITNESS is a different constant and that must be said.

 THE OBSTRUCTION IS [free_ring_via_mon]'S OWN [Set] PIN, not the new
 solution set's fault and not repairable from this file.  Measured,
 [About] under [Set Printing Universes]:

 free_ring_via_mon@{u u0 … u7} : Functor@{u Set Set u …}
 free_ring_via_ab@{u u0 … u8}  : Functor@{u u1 u1 u0 …}

 -- the monoid route pins the hom AND proof universes of [Sets] to
 [Set], where the abelian-group route leaves them free.  The
 non-circular [free_ring_via_GAFT] carries the [Set < carrier] side
 condition of the [Prop] index (see the solution-set section above), so
 the two cannot be compared, and the attempt is refused with

 The term "free_ring_via_mon" has type "Sets@{Set u} ⟶ Rng@{u Set}"
 while it is expected to have type "Sets@{u0 u1} ⟶ Rng@{u1 u0}"
 (universe inconsistency: Cannot enforce Set = u0 because Set < u0)

 (generated universe names replaced positionally; everything else
 verbatim).  [free_ring_via_GAFT_agrees] above, against
 [free_ring_via_ab], is unaffected and IS about the non-circular
 constant.  Widening [free_ring_via_mon] would be a change to
 Instance/Rng/Free.v and belongs to its own commit, exactly as the
 widening of Adjunction/SpanningArrow.v did. 

 --------
 已记录声明更改，PR “代数载体是集合”（2026-09-17），及其测量原因。该条款和下面的另外四个 [_mon] 条款曾经适用于 [free_ring_via_GAFT]，现在适用于 [free_ring_via_GAFT_from_adjunction]，即循环读取。没有任何内容丢失——同一个定理，“[Rng_Forget] 的左伴随一致”，仍然沿着单子环路径成立——但见证（WITNESS）是不同的常数，这必须说明。

 阻碍是 [free_ring_via_mon] 自身的 [Set] 引脚，而不是新解集的错误，也无法通过此文件修复。测量结果如下，[About] 在 [Set Printing Universes] 下：

 free_ring_via_mon@{u u0 … u7} : Functor@{u Set Set u …}
 free_ring_via_ab@{u u0 … u8} : Functor@{u u1 u1 u0 …}-- 单元半群路径将  [Sets] 的同态 AND 证明宇固定到 [Set]，而阿贝尔群路径则保持它们自由。  
 非循环的 [free_ring_via_GAFT] 承载了 [Set < carrier] 的 [Prop] 指数的附加条件（参见上面的解集部分），因此两者无法比较，并且尝试被拒绝，显示：

 术语 "free_ring_via_mon" 的类型为 "Sets@{Set u} ⟶ Rng@{u Set}"，
 而期望的类型为 "Sets@{u0 u1} ⟶ Rng@{u1 u0}"
 （宇不一致：无法强制 Set = u0 因为 Set < u0）(生成的宇宙名称按位置替换；其他一切逐字照搬)。[free_ring_via_GAFT_agrees] 在上方，对抗 [free_ring_via_ab]，不受影响，并且确实与非循环常数有关。扩展 [free_ring_via_mon] 将是对 Instance/Rng/Free.v 的更改，并属于它自己的提交，正如扩展 Adjunction/SpanningArrow.v 所做的那样。
*)
Definition free_ring_via_GAFT_agrees_mon :
  `1 free_ring_via_GAFT_from_adjunction ≈ free_ring_via_mon :=
  left_adjoints_agree (`2 free_ring_via_GAFT_from_adjunction)
    free_ring_via_mon_adjunction_set.

(*
 Theory/Adjunction.v's [left_adjoint_iso] inhabits the same three
 types.  The two terms are NOT identified -- that theorem is [Qed], so no
 component of it reduces and none can be named, which is exactly why the
 transparent donor is used above. 

 --------
 Theory/Adjunction.v 的 [left_adjoint_iso] 属于相同的三种类型。这两个项没有被识别——那个定理是 [Qed]，所以它的任何部分都不能化简，也无法命名，这正是上面使用透明提供者的原因。
*)

Example free_rng_ab_via_GAFT_agrees_via_left_adjoint_iso :
  `1 free_rng_ab_via_GAFT ≈ FreeRngAb :=
  left_adjoint_iso Rng_Forget_Ab _ FreeRngAb (`2 free_rng_ab_via_GAFT)
    free_rng_ab_adjunction.

Example free_ring_via_GAFT_agrees_via_left_adjoint_iso :
  `1 free_ring_via_GAFT ≈ free_ring_via_ab :=
  left_adjoint_iso Rng_Forget _ free_ring_via_ab (`2 free_ring_via_GAFT)
    free_ring_via_ab_adjunction_set.

Example free_ring_via_GAFT_agrees_mon_via_left_adjoint_iso :
  `1 free_ring_via_GAFT_from_adjunction ≈ free_ring_via_mon :=
  left_adjoint_iso Rng_Forget _ free_ring_via_mon
    (`2 free_ring_via_GAFT_from_adjunction)
    free_ring_via_mon_adjunction_set.

(* * ** The comparison morphisms, named / * ** 比较态射，命名为 *)

Definition free_rng_ab_via_GAFT_comparison (A : Ab)
  : `1 free_rng_ab_via_GAFT A ~{Rng}~> FreeRngAb A :=
  adj_left_compare (`2 free_rng_ab_via_GAFT) free_rng_ab_adjunction A.

Definition free_ring_via_GAFT_comparison (X : Sets)
  : `1 free_ring_via_GAFT X ~{Rng}~> free_ring_via_ab X :=
  adj_left_compare (`2 free_ring_via_GAFT) free_ring_via_ab_adjunction_set X.

Definition free_ring_via_GAFT_comparison_mon (X : Sets)
  : `1 free_ring_via_GAFT_from_adjunction X ~{Rng}~> free_ring_via_mon X :=
  adj_left_compare (`2 free_ring_via_GAFT_from_adjunction)
    free_ring_via_mon_adjunction_set X.

(*
 [left_adjoints_agree] is [Defined], so each comparison IS the component
 of the corresponding natural isomorphism, by [eq_refl] and not by an
 argument. 

 --------
 [left_adjoints_agree] 是 [Defined]，因此每个比较都是相应自然同构的组成部分，由 [eq_refl] 决定，而不是通过论证。
*)

Example free_rng_ab_via_GAFT_comparison_is_component (A : Ab) :
  to (projT1 free_rng_ab_via_GAFT_agrees A)
    = free_rng_ab_via_GAFT_comparison A := eq_refl.

Example free_ring_via_GAFT_comparison_is_component (X : Sets) :
  to (projT1 free_ring_via_GAFT_agrees X)
    = free_ring_via_GAFT_comparison X := eq_refl.

Example free_ring_via_GAFT_comparison_mon_is_component (X : Sets) :
  to (projT1 free_ring_via_GAFT_agrees_mon X)
    = free_ring_via_GAFT_comparison_mon X := eq_refl.

(*
   * ** The unit clauses

   Mac Lane's exercise asks for the comparison to be compatible with the
   universal arrows, not merely for an isomorphism to exist.  Composing
   the comparison with the AFT-produced unit gives the explicit
   construction's own unit -- the ring-expression insertion on one side,
   the word insertion on the other. 

   --------
   * ** 单位子句

   Mac Lane 的练习要求比较与全箭兼容，而不仅仅是存在同构。将比较与 AFT 生成的单位复合，会得到显式构造本身的单位——一边是环表达式插入，另一边是单词插入。
*)

Theorem free_rng_ab_via_GAFT_unit (A : Ab) :
  fmap[Rng_Forget_Ab] (free_rng_ab_via_GAFT_comparison A)
    ∘ @Category.Theory.Adjunction.unit _ _ _ _ (`2 free_rng_ab_via_GAFT) A
    ≈ @Category.Theory.Adjunction.unit _ _ _ _ free_rng_ab_adjunction A.
Proof.
  exact (adj_left_compare_unit (`2 free_rng_ab_via_GAFT)
           free_rng_ab_adjunction A).
Qed.

Theorem free_ring_via_GAFT_unit (X : Sets) :
  fmap[Rng_Forget] (free_ring_via_GAFT_comparison X)
    ∘ @Category.Theory.Adjunction.unit _ _ _ _ (`2 free_ring_via_GAFT) X
    ≈ @Category.Theory.Adjunction.unit _ _ _ _
        free_ring_via_ab_adjunction_set X.
Proof.
  exact (adj_left_compare_unit (`2 free_ring_via_GAFT)
           free_ring_via_ab_adjunction_set X).
Qed.

Theorem free_ring_via_GAFT_unit_mon (X : Sets) :
  fmap[Rng_Forget] (free_ring_via_GAFT_comparison_mon X)
    ∘ @Category.Theory.Adjunction.unit _ _ _ _
        (`2 free_ring_via_GAFT_from_adjunction) X
    ≈ @Category.Theory.Adjunction.unit _ _ _ _
        free_ring_via_mon_adjunction_set X.
Proof.
  exact (adj_left_compare_unit (`2 free_ring_via_GAFT_from_adjunction)
           free_ring_via_mon_adjunction_set X).
Qed.
