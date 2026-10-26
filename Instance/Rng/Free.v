Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Adjunction.Compose.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Ab.Free.
Require Import Category.Instance.Mon.Free.
Require Import Category.Instance.Rng.MonoidRing.
Require Import Category.Instance.Rng.Algebras.Associative.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(*
   * * The free ring on an abelian group, and Mac Lane's §IV.8 Exercise 2:
   the free-ring adjunction as a composite in TWO ways

   nLab:      https://ncatlab.org/nlab/show/tensor+algebra
   nLab:      https://ncatlab.org/nlab/show/free+object
   nLab:      https://ncatlab.org/nlab/show/composition+of+adjoints
   Wikipedia: https://en.wikipedia.org/wiki/Tensor_algebra
   Wikipedia: https://en.wikipedia.org/wiki/Monoid_ring
   Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,
   GTM 5, §IV.8, Exercise 2, printed p. 104 -- maclane:IV.8:ex2
   Book: Mac Lane, ibid., §IV.8, Theorem 1 (adjoints compose) --
   the theorem the exercise is an exercise ON

   WHAT THE EXERCISE ASKS.  The free ring on a SET can be reached two
   ways.  Either take the free abelian group on the set and then the free
   ring on that abelian group (the tensor algebra), or take the free
   monoid on the set and then the monoid ring over ℤ.  Each leg is a left
   adjoint, so each composite is a left adjoint by Mac Lane's Theorem 1,
   and since left adjoints of one right adjoint are unique up to natural
   isomorphism, the two composites agree.  The delivered artifacts are
   [free_ring_via_ab], [free_ring_via_mon] and
   [free_ring_composites_agree], the last being a NATURAL ISOMORPHISM of
   the two functors -- [≈] at [Sets ⟶ Rng] IS [Functor_Setoid], i.e. a
   family of isomorphisms together with the coherence square -- and NOT
   an object-level equality, together with the unit statement
   [free_ring_composites_agree_unit].

   THE ISSUE'S “CURRENT STATE” IS BADLY STALE, AND THIS FILE SAYS SO
   RATHER THAN REPEATING IT.  #400 says “none of the three categories
   exists” and “not one of the six functors the exercise needs is
   defined”.  That is false: [Grp] (Instance/Grp.v), [Ab]
   (Instance/Ab.v) and [Rng] (Instance/Rng.v, a [Definition]
   aliasing [Ring]) all exist, with [Ab_Forget] (Instance/Ab.v),
   [Rng_Forget_Ab] (Instance/Rng.v), [Mon_Forget]
   (Theory/Algebra/Monoid/Hom.v) and [Rng_Forget_Mon]
   (Instance/Rng/MonoidRing.v) among them, and the monoid ring
   exists WITH its adjunction ([MonoidRingFunctor],
   [zmring_adjunction], Instance/Rng/MonoidRing.v).  The
   issue's own QA correction supersedes its work items 1-2 (“consume the
   free monoid, do not rebuild”), and that instruction was blocked by a
   CATEGORY MISMATCH: the in-tree free monoid of Instance/Coq/Monoid/Free.v
   is at [MonCoq := @Mon Coq Coq_Monoidal] while the monoid
   ring's right adjoint lands in [@Mon Sets Sets_Product_Monoidal], and
   no bridge between the two exists.  Instance/Mon/Free.v was written for
   this issue precisely to close that gap, and Instance/Ab/Free.v
   supplies the other leg; NEITHER is rebuilt here, both are consumed by
   name.

   WHAT IS GENUINELY NEW HERE is therefore exactly one construction --
   [FreeRngAbObject], [FreeRngAb : Ab ⟶ Rng] and
   [free_rng_ab_adjunction : FreeRngAb ⊣ Rng_Forget_Ab] -- plus the two
   composites and their comparison.
   CORRECTION (#474): #474 adds a second packaging of the same
   adjunction, [free_rng_ab_adjunction_hom] (THE HOM-SET FORM (#474),
   below), and no further construction.

   WHY GENERATORS AND RELATIONS, NOT ⊕ₙ A^⊗ⁿ.  The classical carrier of
   the tensor algebra is the direct sum of the tensor powers, and that
   presentation is unavailable in tree: it needs countable direct sums of
   abelian groups, i.e. [HasIndexedCoproducts Ab], which is not built --
   Instance/Ab/Coproduct.v says so in terms, and the only instances of
   that class anywhere are at [Sets] and at [Cat].  The carrier here is
   instead an inductive of formal ring expressions [FRTerm] with an
   inductive congruence [fr_eq], following Instance/Rng/MonoidRing.v,
   Instance/Vect/TensorAlgebra.v, Instance/Rng/Polynomial.v and
   Instance/Ab/Tensor.v.  The design is copied and the debt is
   acknowledged; no code is shared with any of them.
   CORRECTION (#474): the direct sum of the tensor powers of ONE
   abelian group is built by Instance/Ab/TensorPower.v
   ([TW_is_tensor_coproduct], an [IsIndexedCoproduct] of that family
   in Ab, the tensor powers being Structure/Monoidal/Hypergraph/
   Spider.v's [tpower] at [Ab_Monoidal]), with no general
   [HasIndexedCoproducts Ab], which is still not built; and
   Instance/Rng/FreeMonad/Words.v proves the abelian group of
   [FreeRngAbObject A] isomorphic to it ([T_TW_iso]), the forward map
   being [free_rng_ab_extend] of the insertion of one-letter words.

   THE PRESENTATION CARRIES NO REDUNDANCY, AND THAT IS MEASURED.
   [fr_eq] has SEVENTEEN constructors: four congruence clauses (one per
   former, the generator clause saturating under A's own [≈]), the four
   abelian-group laws, the three multiplicative-monoid laws, the two
   distributive laws, the two clauses making the insertion of A a
   homomorphism of abelian groups, and symmetry and transitivity.
   Reflexivity is DERIVED ([fr_refl]), keeping the induction principle
   one case shorter everywhere it is consumed.  [RigObject] has twelve
   law fields and only TEN of them are constructors: the two annihilation
   clauses [rig_mul_zero_l] and [rig_mul_zero_r] are THEOREMS
   ([fr_mul_zero_l], [fr_mul_zero_r]), derived from distributivity and
   additive inverses through the one-line [fr_idem_zero].  So the record
   is not a zero-obligation literal, unlike Instance/Ab/Free.v's; two
   fields are paid for, deliberately, to keep the generating set
   irredundant.  Since the PR “algebraic carriers are sets” (2026-09-17)
   the record carries a THIRTEENTH field, [rig_prop], which is neither a
   law nor a constructor: it is [fr_eq] read as its own [Prop] mirror,
   both implications being the identity, and it costs no obligation
   either.

   STRENGTHS, MEASURED STRICT-FIRST.  The mediator is a [Fixpoint] on
   formal expressions, so a great deal is definitional:

   - [eq_refl]: the carrier of the free ring seen through
   [Ab_Forget ◯ Rng_Forget_Ab] IS [FRTerm] and its [≈] IS [fr_eq]
   ([free_rng_ab_carrier_is_FRTerm], [free_rng_ab_equiv_is_fr_eq]);
   the insertion IS the generator former
   ([free_rng_ab_insert_is_gen]); the extension agrees with the given
   homomorphism on generators and preserves 0, 1, +, · AND negation
   definitionally ([free_rng_ab_extend_generators] and the five
   siblings, recorded at Leibniz [=] on the TARGET's carrier -- the
   convertibility exception the house style sanctions -- so the claim
   is machine-checked rather than inferred from which branch of the
   obligation tactic fired); the free functor's object part
   ([FreeRngAb_obj]); the universal arrow IS the insertion
   ([free_rng_ab_arrow_is_insert]); the UNIT is the insertion and
   hence the one-generator expression ([free_rng_ab_unit_is_insert]);
   both composites' object actions ([free_ring_via_ab_obj],
   [free_ring_via_mon_obj]); the abelian route's transpose is the
   pasted transpose ([free_ring_via_ab_transpose]); the retyping of
   the monoid route is inert on transpose and unit
   ([retype_adj_agrees], [retype_unit_agrees]); and the two
   underlying-set functors agree on objects AND on arrows
   ([rng_underlying_fobj_agree], [rng_underlying_fmap_agree]).
   - [≈] only, with the cause DIAGNOSED and DISCRIMINATED: the COUNIT.
   It is [unique_obj (ump_universal_arrows …)] and
   [ump_universal_arrows] (Theory/Universal/Arrow.v) is [Qed]-opaque,
   so nothing reduces through it; [free_rng_ab_counit_evaluates] is
   what does hold.  The blame is on that one constant and not on the
   route, and the discriminating control is in the same file: the
   UNIT comes out of the SAME [AdjunctionFromUniversalArrows] and
   DOES reduce ([free_rng_ab_unit_is_insert], [eq_refl]).  Both are
   pinned -- the negative as [rng_counit_computes].
   CORRECTION (#474): that diagnosis names one of two causes.  Two
   [Qed] constants block the counit: [ump_universal_arrows] and
   this file's own [free_rng_ab_universal], the proof of the
   factorization that [free_rng_ab_universal_arrow] hands to
   [universal_arrow_from_UMP] and from which the counit is read.
   Measured three times, each in a copy of a closure rebuilt
   after the change: by #474's scout, in a 92-file closure, on its
   nine route-A refutations; by its build, in the probe's 111-file
   closure, on the thirty-one refutations Test/ProbeFreeRing474.v
   then had; and after its review, in the 112-file closure, on the
   thirty-two it has now.  With either constant alone turned
   [Defined], [rng_counit_computes] and
   [rng_fmap_generator_computes] are still refused, and so are the
   scout's nine and every refutation of the probe; with both turned
   [Defined], those two negatives hold, and so do the scout's nine
   and twelve of the probe's (R2, R3, R5 to R13 and R26), the ones
   that read this counit or the free functor's action on arrows.
   Neither constant is turned [Defined] here:
   [ump_universal_arrows] is shared by many developments, several
   of which pin its opacity in probes, and issue #1353 tracks it.
   #474 adds instead the same adjunction in hom-set form,
   [free_rng_ab_adjunction_hom] below, whose counit IS the
   evaluation by conversion ([free_rng_ab_hom_counit]).
   - [≈] only: the action of [FreeRngAb] on an arrow.
   [LeftAdjointFunctorFromUniversalArrows] defines [fmap] by
   universal factorization rather than by a formula, so
   [free_rng_ab_fmap_generators] is a theorem; the strict form is
   pinned as [rng_fmap_generator_computes].
   CORRECTION (#474): [≈] on this tree; the strict form holds once
   both [Qed] layers of the previous item are turned [Defined],
   where [rng_fmap_generator_computes] is no longer refused.

   THE TWO RIGHT ADJOINTS, AND WHY NO TRANSPORT LEMMA WAS NEEDED.  Write
   [RngUnderlyingAb := Ab_Forget ◯ Rng_Forget_Ab] and
   [RngUnderlyingMon := Mon_Forget ◯ Rng_Forget_Mon], both [Rng ⟶ Sets].
   Four facts, measured:

   (i)   [fobj[RngUnderlyingAb] R = fobj[RngUnderlyingMon] R] by
   [eq_refl];
   (ii)  [fmap[RngUnderlyingAb] f = fmap[RngUnderlyingMon] f] by
   [eq_refl];
   (iii) [RngUnderlyingAb = RngUnderlyingMon] is REFUTED at [eq_refl] --
   [Functor] has primitive projections with eta, so record
   equality is field equality, and the three LAW fields are
   [Compose]'s obligations at different arguments;
   (iv)  consequently the composed monoid-route adjunction cannot be
   ASCRIBED against [RngUnderlyingAb] ([rng_mon_route_ascribed],
   refuted), the [Adjunction] type mentioning the whole functor
   record.

   From (iv) one expects to need a lemma transporting an adjunction along
   a natural isomorphism of its right adjoint.  NONE IS NEEDED, and that
   is the file's cheapest finding: every one of [Adjunction]'s five
   fields mentions the right adjoint ONLY through [U y] (an object) and
   [fmap[U] f] (a morphism), and by (i) and (ii) those are definitionally
   equal, so the five field TYPES are convertible even though the two
   functor records are not.  [free_ring_via_mon_adjunction_ab] is
   therefore literal field copying through [@Build_Adjunction], with no
   tactic, no isomorphism and no coherence obligation -- and
   [retype_adj_agrees] and [retype_unit_agrees] record by [eq_refl] that
   the operation is inert.

   THE COMPARISON IS BUILT TRANSPARENTLY, AND GENERALLY.  Section
   [LeftAdjointComparison] proves, for ANY two left adjoints of one right
   adjoint, that [⌈η'⌉] and [⌈η⌉] are mutually inverse and natural, so
   [left_adjoints_agree] inhabits [F ≈ F'] with NAMED components, and it
   is [Defined], so [free_ring_comparison_is_agree_component] records by
   [eq_refl] that [free_ring_comparison] IS the component of
   [free_ring_composites_agree] -- not merely an isomorphism with the
   same endpoints.  Theory/Adjunction.v's [left_adjoint_iso]
   proves the same TYPE -- [free_ring_composites_agree_via_left_adjoint_iso]
   feeds it the same two adjunctions, so that much is machine-checked --
   but it is [Qed], so no component of it reduces and none can be named,
   which is why the transparent version exists:
   [free_ring_composites_agree_unit] is a statement ABOUT
   [free_ring_comparison], and could not have been tied to an opaque
   isomorphism at all.  The two terms are NOT identified, and no such
   identification is claimed.  Two small general lemmas were needed on
   the way and are stated here rather than upstream: [to_adj_injective],
   and
   [unit_natural] -- naturality of the unit along an ARBITRARY morphism
   of D, which Theory/Adjunction.v's [unit_comp] does not give, that
   one stating naturality only along a morphism [x ~> U y].

   UNIVERSES: THE TWO ROUTES DO NOT HAVE THE SAME REACH, AND THE
   ASYMMETRY IS THE DONOR'S.  Read off the constraint blocks:
   [RngUnderlyingAb@{u u0} : Functor@{u u0 u0 u u0 u0}] leaves the
   carrier universe [u0] FREE (only [u0 < u], which is [Ab]'s own
   stratification), and so do [FreeRngAb], [free_rng_ab_adjunction] and
   [free_ring_via_ab].  The monoid route does not:
   [RngUnderlyingMon] and [free_ring_via_mon] are
   [Functor@{u Set Set u Set Set}] -- hom and proof universes pinned at
   [Set].  The pin is located exactly and is NOT this file's:
   [Rig_Forget_Mon] (Theory/Algebra/Rig.v) has source [Rig@{u Set}],
   and [Rng_Forget_Mon] is [Rig_Forget_Mon ◯ Ring_Forget_Rig].  Both are
   rejected under a declared [Constraint Set < uh] while [Rng_Forget_Ab]
   and [Rig_Forget_CMon] elaborate there.  Read that guard precisely:
   the negatives fire on the donor's literal [Set] meeting a RIGID
   declared level -- deleting the [Constraint] leaves them failing with
   the identical message, so it is INERT for them -- and what it buys is
   the positive controls' “strictly above [Set]”.  The attribution is
   guarded
   and not merely asserted.  CONSEQUENCE, stated plainly: since the
   comparison needs both routes at ONE [Rng],
   [free_ring_composites_agree] instantiates the abelian route at [Set]
   and inherits the pin, so the EXERCISE is a statement about rings whose
   carriers live in [Set] even though the abelian half of it is not.  The
   pin is not repaired here and is NOT claimed unavoidable.

   NON-DEGENERACY, PROVED RATHER THAN GESTURED AT.  No induction over
   [fr_eq] can yield a negative -- every constructor concludes an
   equation -- so each refutation maps OUT into a concrete ring.  In
   general: no generator is the unit and 0 is not 1
   ([free_rng_ab_gen_not_one], [free_rng_ab_zero_not_one]), for EVERY
   abelian group, by the constant-zero probe into any ring with 1 ≉ 0.
   Concretely over ℤ: the insertion is INJECTIVE
   ([int_free_rng_gen_injective]), so ℤ genuinely embeds.  And the free
   ring on the free abelian group of rank two is NOT COMMUTATIVE
   ([free_rng_ab_not_commutative]), by mapping the two generators to the
   non-commuting matrix units of [UT2]
   (Instance/Rng/Algebras/Associative.v, the FIRST closed
   non-commutative [RingObject] in tree; [Lam2],
   Instance/Vect/TensorAlgebra.v, is a second, so “only” would be
   false); both products COMPUTE, so the
   separation is [discriminate] on closed data.  That witness is not
   beside the exercise: [rng_two_gens_is_via_ab] records by [eq_refl]
   that the ring probed IS [free_ring_via_ab AbTwoGens].  Finally
   [rng_routes_convertible] is refuted, so the two composites are
   not convertible, so the isomorphism is not between a thing
   and itself.

   MEASURED BOUNDARIES.  Seven [Fail]s of TWO KINDS, kept lexically
   apart: five CONVERSION (the two functor records, the ascription, the
   two routes' objects, the counit, the arrow action) and two FORMABILITY
   (the [Set] pin, at each of [Rng_Forget_Mon] and [Rig_Forget_Mon]),
   plus a separate instrument check.  Each was stripped once and its
   failure kind read off the message.  Every constant named in a [Fail]
   is also named in a command that must SUCCEED -- four positive [Check]s
   were added for exactly that reason -- so a rename breaks this file
   instead of turning a negative vacuously green.

   THE HOM-SET FORM (#474).  Two packagings of the one adjunction
   [FreeRngAb ⊣ Rng_Forget_Ab] are kept.  [free_rng_ab_adjunction],
   from the universal arrows, is the one the composites below,
   Instance/Rng/AFT.v and Test/ProbeFreeRing400.v consume, and it is
   unchanged.  [free_rng_ab_adjunction_hom] is Theory/Adjunction.v's
   [Build_Adjunction'] applied to the natural bijection
   [free_rng_ab_hom_iso], with the same left adjoint [FreeRngAb], the
   same right adjoint and the same insertion: its unit and its forward
   transpose ARE those of [free_rng_ab_adjunction] at [eq_refl]
   ([free_rng_ab_hom_unit], [free_rng_ab_hom_to]), and its inverse
   transpose is the extension [free_rng_ab_extend], so its counit is
   the evaluation of the identity at [eq_refl]
   ([free_rng_ab_hom_counit]), where the other counit is that
   evaluation at `≈` here ([free_rng_ab_counit_evaluates]; at
   [eq_refl] once both [Qed] layers of STRENGTHS are transparent,
   #1353).  It exists for the tensor-algebra monad T of Mac Lane's
   §VI.4 Exercise 4 (Instance/Rng/FreeMonad.v), whose multiplication
   U ε F and comparison functor then compute, and it is not only a way
   around that opacity: it is the literal reading of the exercise's
   “adjunction ⟨F, G, φ⟩”, Mac Lane's adjunctions being given by
   their natural bijection φ (§IV.1), and [free_rng_ab_hom_iso] is that
   φ.  It is not a second free ring and not a second free functor: the
   action on arrows is still [FreeRngAb]'s, the relabelling of
   generators at `≈` here ([free_rng_ab_fmap_generators]; at [eq_refl]
   once both layers are transparent, #1353).  The two adjunctions are
   refused equal at [eq_refl], and so are their inverse transposes and
   their counits at a variable expression (Test/ProbeFreeRing474.v, R1
   to R3).  Its universes: [free_rng_ab_hom_iso] and
   [free_rng_ab_adjunction_hom] bind @{u p}, [Ab]'s and [Rng]'s own,
   and the four further levels of [FreeRngAb], with no [Set] but the
   strict lower bound [Set < u]; the adjunction is pinned to
   [Adjunction@{u p p u p p p p u p u}], so that the phantom level of
   [Build_Adjunction'] is not left free (an unpinned version binds it,
   unconstrained, measured by [About]).  Issue #1353 records the exit:
   once [ump_universal_arrows] and [free_rng_ab_universal] are
   transparent, one record is kept and T is rebased on it.

   116/116 constants closed under the global context, the count taken
   over the source declarations and the constructors UNION what
   [Print Module] lists (which adds the eliminators and the six [Program]
   obligations, ALL SIX of which are reachable only by fully qualified
   name).

   AN EARLIER REVISION of this sentence read 118/118.  Since the PR
   “algebraic carriers are sets” (2026-09-17) [fr_eq] is a [Prop]
   inductive, and Coq generates only [fr_eq_ind] and [fr_eq_sind] for it,
   not [_rec] and [_rect]: measured by grepping the output of
   [Print Module Free] for [fr_eq_*], which returns exactly those two.
   Those two vanished names are the whole of the difference.  The “closed
   under the global context” reading was NOT re-run for all 116 at this
   revision; what was re-measured is the eliminator count.

   CORRECTION (#474): #474 adds six constants, [fr_eval_pointwise],
   [free_rng_ab_hom_iso], [free_rng_ab_adjunction_hom] and the three
   [eq_refl] readbacks [free_rng_ab_hom_counit], [free_rng_ab_hom_unit]
   and [free_rng_ab_hom_to], each “Closed under the global context”
   and named in #474's print-assumptions block; the 116 above are
   unchanged.  The refusals about the hom-set form are pinned in
   Test/ProbeFreeRing474.v, which restates the three readbacks (C1 to
   C3) and names the six constants in its guard.

   NOT DELIVERED, scoped:
   - no normal form for [fr_eq], hence no coefficient uniqueness, no
   decision procedure and no basis; nothing is claimed about when two
   formal expressions are equal beyond what the probes above settle;
   - no grading and no identification of [FreeRngAbObject A] with
   ⊕ₙ A^⊗ⁿ, and no comparison with Instance/Vect/TensorAlgebra.v's
   [TensorAlg] (that one is the tensor algebra of a MODULE over a
   base ring, built on a different generating structure; no map
   either way is built and none is claimed);
   CORRECTION (#474): the identification is now
   Instance/Rng/FreeMonad/Words.v's [T_TW_iso], an isomorphism in
   Ab (its forward map is a ring map, [tw_to_rng]) with ⊕ₙ A^⊗ⁿ as
   Instance/Ab/TensorPower.v's coproduct of the tensor powers; there
   is still no grading on [FreeRngAbObject A] itself, and the
   comparison with [TensorAlg] needs Ab ≅ RMod ℤ (issue #1356);
   - no commutative variant, so no free commutative ring and no
   relation to Instance/Rng/Polynomial.v's ℤ[x] -- in particular it
   is NOT claimed that [FreeRngAbObject ab_int] is ℤ[x];
   - the comparison is between the two COMPOSITES only: no comparison
   of [FreeRngAb ◯ FreeAb] with [MonoidRingFunctor] leg by leg, and
   no claim that either intermediate category is determined;
   - no [Set]-pin repair for [Rig_Forget_Mon], and no restatement of
   the monoid route at a free carrier universe;
   - no counit-level companion to [free_ring_composites_agree_unit];
   - [to_adj_injective] and [unit_natural] are stated here and NOT
   upstreamed to Theory/Adjunction.v. 

   --------
   * * 阿贝尔群上的自由环，以及 Mac Lane 第四章 §IV.8 练习 2：
   自由环伴随作为两种方式的复合

   nLab:       https://ncatlab.org/nlab/show/tensor+algebra 
   nLab:       https://ncatlab.org/nlab/show/free+object 
   nLab:       https://ncatlab.org/nlab/show/composition+of+adjoints 
   Wikipedia:  https://en.wikipedia.org/wiki/Tensor_algebra 
   Wikipedia:  https://en.wikipedia.org/wiki/Monoid_ring 
   书籍: Mac Lane，《为工作数学家准备的范畴论》，第二版，
   GTM 5，第 IV.8 节，练习 2，印刷页 104 -- maclane:IV.8:ex2
   书籍: Mac Lane，同上，第 IV.8 节，定理 1（伴随可组合） --
   该定理是该练习所依据的定理练习的要求。集合上的自由环可以通过两种方式得到。可以先取集合上的自由阿贝尔群，然后在该阿贝尔群上取自由环（张量代数），或者先取集合上的自由幺半群，然后在ℤ上取幺半群环。每一步都是左伴随，因此根据Mac Lane的定理1，每个复合也是左伴随，而且由于一个右伴随的左伴随在自然同构下是唯一的，所以两个复合是相同的。所给出的成果为 [free_ring_via_ab]、[free_ring_via_mon] 和 [free_ring_composites_agree]，最后一个是两个函子之间的自然同构——在[Sets ⟶ Rng]处的[≈]等于[Functor_Setoid]，即一族同构及其一致性方格——而不是对象层面的相等，同时还有单元陈述 [free_ring_composites_agree_unit]。该问题的“当前状态”已经非常陈旧，这个文件也说明了这一点，而不是重复说。#400 说“这三类都不存在”以及“练习需要的六个函子没有一个被定义”。这是错误的：[Grp]（Instance/Grp.v）、[Ab]（Instance/Ab.v）和[Rng]（Instance/Rng.v，一个[Definition]别名[Ring]）都存在，其中有[Ab_Forget]（Instance/Ab.v）、[Rng_Forget_Ab]（Instance/Rng.v）、[Mon_Forget]（Theory/Algebra/Monoid/Hom.v）和[Rng_Forget_Mon]（Instance/Rng/MonoidRing.v），并且这个幺半环存在且带有它的伴随（[MonoidRingFunctor]、[zmring_adjunction]、Instance/Rng/MonoidRing.v）。该问题自身的 QA 修正优先于其工作项 1-2（“使用自由单子，不要重建”），但该指令被类别不匹配阻止：Instance/Coq/Monoid/Free.v 中的树内自由单子位于 [MonCoq := @Mon Coq Coq_Monoidal]，而单子环的右伴随落在 [@Mon Sets Sets_Product_Monoidal]，并且两者之间不存在桥接。Instance/Mon/Free.v 正是为了解决此问题而编写，以弥合该差距，而 Instance/Ab/Free.v 提供了另一端；这里两者都没有被重建，都只是被按名称使用。真正新的东西正好是一个构造——
   [FreeRngAbObject]、[FreeRngAb : Ab ⟶ Rng] 和
   [free_rng_ab_adjunction : FreeRngAb ⊣ Rng_Forget_Ab]——加上两个复合体及它们的比较。
   修正 (#474)：#474 添加了相同连接的第二种包装，[free_rng_ab_adjunction_hom]（下面的同构集形式 (#474)），没有进一步的构造。为什么使用生成元和关系，而不是 ⊕ₙ A^⊗ⁿ。张量代数的经典承载对象是张量幂的直和，而在树结构中无法使用这种表示：它需要可数个阿贝尔群的直和，即 [HasIndexedCoproducts Ab]，而该结构尚未构建——Instance/Ab/Coproduct.v 以术语形式说明，而且该类的唯一实例仅存在于 [Sets] 和 [Cat]。这里的承载对象改为形式环表达式的归纳 [FRTerm]，并采用归纳同余 [fr_eq]，参考了 Instance/Rng/MonoidRing.v、Instance/Vect/TensorAlgebra.v、Instance/Rng/Polynomial.v 和 Instance/Ab/Tensor.v。设计是借鉴的，并已注明出处；与它们没有任何代码共享。更正 (#474)：一个阿贝尔群的张量幂的直和是由 Instance/Ab/TensorPower.v 构建的（[TW_is_tensor_coproduct]，这是该系列在 Ab 中的一个 [IsIndexedCoproduct]，张量幂是 Structure/Monoidal/Hypergraph/Spider.v 中的 [tpower] 在 [Ab_Monoidal] 处），没有一般的 [HasIndexedCoproducts Ab]，目前仍未构建；并且 Instance/Rng/FreeMonad/Words.v 证明 [FreeRngAbObject A] 的阿贝尔群与其同构（[T_TW_iso]），正向映射是插入单字母词的 [free_rng_ab_extend]。该演示没有冗余，这是经过衡量的。[fr_eq] 有十七个构造函数：四个合同子句（每个前者一个，由生成子句在 A 自身的 [≈] 下饱和）、四条阿贝尔群定律、三条乘法幺半群定律、两条分配律、两条使 A 的插入成为阿贝尔群同态的子句，以及对称性和传递性。自反性是推导出来的（[fr_refl]），保持归纳原理在使用的每个地方少一个案例。[RigObject] 有十二个定律域，其中只有十个是构造函数：两个消去子句 [rig_mul_zero_l] 和 [rig_mul_zero_r] 是定理（[fr_mul_zero_l]，[fr_mul_zero_r]），通过唯一一行的 [fr_idem_zero] 从分配律和加法逆元中推导出来。所以这个记录并不是一个零义务字面值，不像 Instance/Ab/Free.v 的；两个字段是有偿的，这是故意为之，用于保持生成集的非冗余性。自从 PR “代数承载体是集合”（2026-09-17）以来，这个记录携带了第十三个字段 [rig_prop]，它既不是定律也不是构造器：它是 [fr_eq]，被视为其自身的 [Prop] 镜像，这两个含义都是恒等的，而且它也不需要任何义务。

   优势，严格优先衡量。仲裁者是形式表达上的 [Fixpoint]，因此有大量是定义性的：- [eq_refl]：通过[Ab_Forget ◯ Rng_Forget_Ab]看到的自由环的载体是[FRTerm]，其[≈]是[fr_eq]（[free_rng_ab_carrier_is_FRTerm], [free_rng_ab_equiv_is_fr_eq]）；插入是前生成元（[free_rng_ab_insert_is_gen]）；扩展在生成元上与给定同态一致并按定义保持0、1、+、·以及取负（[free_rng_ab_extend_generators]及其五个兄弟，在目标的载体上记录于莱布尼茨[=] —— 可转换性例外由内部风格允许 —— 因此该声明是机器检查的，而不是从责任策略触发的分支推断的）；自由函子对象部分（[FreeRngAb_obj]）；通用箭头是插入（[free_rng_ab_arrow_is_insert]）；单位是插入，因此是一生成元表达式（[free_rng_ab_unit_is_insert]）；两个复合体的对象动作（[free_ring_via_ab_obj]，[free_ring_via_mon_obj]）；阿贝尔路径的转置是粘贴的转置（[free_ring_via_ab_transpose]）；幺半群路径的重类型在转置和单位上是惰性的（[retype_adj_agrees]，[retype_unit_agrees]）；并且两个底层集合函子在对象和箭头上都一致（[rng_underlying_fobj_agree]，[rng_underlying_fmap_agree]）。-  仅 [≈]，有因被诊断并区分：共单位。它是 [unique_obj (ump_universal_arrows …)] 且 [ump_universal_arrows]（理论/通用/箭头.v）是 [Qed]——不透明的，因此没有任何东西能通过它简化；[free_rng_ab_counit_evaluates] 才是有效的。责任在于那个常量，而不在于路径，区分控制也在同一个文件中：该单位来自相同的 [AdjunctionFromUniversalArrows]，并且可以简化（[free_rng_ab_unit_is_insert]，[eq_refl]）。两者都被固定——负值为 [rng_counit_computes]。更正 (#474)：该诊断指出了两个原因中的一个。有两个 [Qed] 常量阻止共单位：[ump_universal_arrows]，以及此文件自身的 [free_rng_ab_universal]，这是 [free_rng_ab_universal_arrow] 交给 [universal_arrow_from_UMP] 并从中读取共单位的因式分解证明。在每次复制关闭后测量三次：在#474的侦察中，在一个92文件的关闭上，对其九个A路线的反驳进行测量；在其构建中，在探针的111文件关闭上，对Test/ProbeFreeRing474.v然后拥有的三十一条反驳进行测量；以及在其复查后，在112文件的关闭上，对其现在拥有的三十二条反驳进行测量。仅将任一常量置为[Defined]、[rng_counit_computes]和[rng_fmap_generator_computes]仍被拒绝，侦察的九个反驳和探针的每一个反驳也一样；将两者都置为[Defined]，这两个否定仍然成立，侦察的九个反驳以及探针的十二个反驳（R2、R3、R5至R13和R26）也同样如此，这些反驳是那些读取该副单位或自由函子在箭头上的作用的反驳。这里没有开启任何常量 [Defined]：
   [ump_universal_arrows] 被许多开发共享，其中几个在探针中固定其不透明度，并且问题 #1353 跟踪它。#474 改为在 hom-set 形式中添加相同的附加项，
   下面的 [free_rng_ab_adjunction_hom]，其余单位确实是通过转换的评估 ([free_rng_ab_hom_counit])。- [≈] 仅：[FreeRngAb] 对箭头的作用。[LeftAdjointFunctorFromUniversalArrows] 通过通用分解而不是公式定义 [fmap]，因此 [free_rng_ab_fmap_generators] 是一个定理；严格形式被固定为 [rng_fmap_generator_computes]。更正 (#474)：在此树上 [≈]；一旦前一项的两个 [Qed] 层被开启 [Defined]，严格形式就成立，其中 [rng_fmap_generator_computes] 不再被拒绝。两个右伴随，以及为什么不需要传输引理。写下
   [RngUnderlyingAb := Ab_Forget ◯ Rng_Forget_Ab] 和
   [RngUnderlyingMon := Mon_Forget ◯ Rng_Forget_Mon]，都是 [Rng ⟶ Sets]。
   四个测量的事实：

   (i)    [fobj[RngUnderlyingAb] R = fobj [RngUnderlyingMon] R] 通过
   [eq_refl];
   (ii)   [fmap[RngUnderlyingAb] f = fmap [RngUnderlyingMon] f] 通过
   [eq_refl];
   (iii)  [RngUnderlyingAb = RngUnderlyingMon] 在 [eq_refl] 被驳斥--
   [Functor] 具有带 eta 的原始投影，因此记录相等是字段相等，并且三个 LAW 字段是
   [Compose] 在不同参数下的义务;
   (iv)  因此，组合的单子路径伴随不能被
   归因于 [RngUnderlyingAb] ([rng_mon_route_ascribed], 被驳斥)，[Adjunction] 类型涉及整个函子记录。从 (iv) 可以预期需要一个引理来沿其右伴随的自然同构传递伴随。但实际上不需要，这正是该文件最廉价的发现：[Adjunction] 的五个字段中的每一个都仅通过 [U y]（一个对象）和 [fmap[U] f]（一个态射）提到右伴随，并且根据 (i) 和 (ii) 它们在定义上是相等的，因此这五个字段的类型是可转换的，尽管这两个函子记录不是。因此，[free_ring_via_mon_adjunction_ab] 只是通过 [@Build_Adjunction] 进行字面字段复制，没有策略、没有同构，也没有相干义务——并且 [retype_adj_agrees] 和 [retype_unit_agrees] 通过 [eq_refl] 记录该操作是惰性的。比较是透明地建立的，并且是一般性的。[LeftAdjointComparison] 证明了，对于一个右伴随的任意两个左伴随，[⌈η'⌉] 和 [⌈η⌉] 互为逆且自然，因此 [left_adjoints_agree] 存在于 [F ≈ F'] 中，并具有命名的分量，并且它是 [Defined]，因此 [free_ring_comparison_is_agree_component] 通过 [eq_refl] 记录 [free_ring_comparison] 是 [free_ring_composites_agree] 的分量——不仅仅是具有相同端点的同构。Theory/Adjunction.v 的 [left_adjoint_iso] 证明了相同的类型——[free_ring_composites_agree_via_left_adjoint_iso] 给它提供了相同的两个伴随，所以这些在机器中是已检查的——但它是 [Qed]，因此其中没有任何分量可以化简，也没有任何分量可以被命名，这就是透明版本存在的原因：[free_ring_composites_agree_unit] 是关于 [free_ring_comparison] 的陈述，并且根本不可能与不透明的同构联系在一起。这两个术语没有被识别，也没有声称进行过这样的识别。在过程中需要两个小的通用引理，这里给出它们而不是在上游给出：[to_adj_injective]，以及[unit_natural]——单位沿着D的任意态射的自然性，而Theory/Adjunction.v中的[unit_comp]并没有给出这一点，后者仅陈述沿着一个态射[x ~> U y]的自然性。宇宙：两条路线的覆盖范围不同，这种不对称性属于捐赠者。读取约束块：
   [RngUnderlyingAb@{u u0} : Functor@{u u0 u0 u u0 u0}] 让承载宇宙 [u0] 保持自由（只有 [u0 < u]，即 [Ab] 自身的分层），[FreeRngAb]、[free_rng_ab_adjunction] 和 [free_ring_via_ab] 也同样如此。幺半群路径则不然：
   [RngUnderlyingMon] 和 [free_ring_via_mon] 是 [Functor@{u Set Set u Set Set}] —— 同构和证明宇宙被固定在 [Set]。固定点位置是精确的，并且不是本文件的：
   [Rig_Forget_Mon] （Theory/Algebra/Rig.v）的来源是 [Rig@{u Set}]，[Rng_Forget_Mon] 是 [Rig_Forget_Mon ◯ Ring_Forget_Rig]。在声明的 [Constraint Set < uh] 下，两者都被拒绝，而 [Rng_Forget_Ab] 和 [Rig_Forget_CMon] 在那里展开。仔细阅读那段警告：
   负面在捐赠者的字面 [Set] 上触发 RIGID 声明的水平——删除 [Constraint] 会导致它们以相同的消息失败，因此对它们是无效的——而它所获得的是正对照的“严格高于 [Set]”。归属是受保护的，而不仅仅是声称。结果，直白地说：由于比较需要两个路径在一个 [Rng] 上，同时 [free_ring_composites_agree] 在 [Set] 上实例化阿贝尔路径并继承该 pin，因此该练习是关于其载体存在于 [Set] 的环的说明，即使其阿贝尔部分不是如此。这里 pin 并未修复，也不被声称为不可避免。非退化性，经过证明而非仅仅提示。对 [fr_eq] 的任何归纳都不能得出负数——每个构造子都能得出一个方程——因此每个反证都将 OUT 映射到一个具体的环中。一般来说：没有生成元是单位元，并且 0 ≠ 1（[free_rng_ab_gen_not_one]，[free_rng_ab_zero_not_one]），对于每个阿贝尔群，通过对任何 1 ≠ 0 的环进行常数零探测。具体到 ℤ：这个插入是单射的（[int_free_rng_gen_injective]），因此 ℤ 确实可以嵌入。自由阿贝尔群秩为二的自由环不是交换的（[free_rng_ab_not_commutative]），通过将两个生成元映射到[UT2]的非交换矩阵单位（Instance/Rng/Algebras/Associative.v，树中第一个封闭的非交换[RingObject]；Instance/Vect/TensorAlgebra.v中的[Lam2]是第二个，所以“唯一”是错误的）；两个乘积都可以计算，所以在封闭数据上的分离是[discriminate]。这个证明并不是附带练习：[rng_two_gens_is_via_ab]由[eq_refl]记录表明被探测的环确实是[free_ring_via_ab AbTwoGens]。最后[rng_routes_convertible]被反驳，所以这两个复合体不可互换，因此同构不是一个事物自身之间的。测量边界。七个 [Fail] 类型的两种，保持词汇上分开：五个转换（两个函子记录、指定、两条路径的对象、余单位、箭头操作）和两个可形成性（[Set] 销，在 [Rng_Forget_Mon] 和 [Rig_Forget_Mon] 各处），加上一个单独的工具检查。每个都被剥离一次，并从消息中读取其失败类型。[Fail] 中命名的每一个常量也在必须成功的命令中被命名——正是因为这个原因添加了四个正 [Check]——所以重命名会破坏这个文件，而不是让一个负值变得毫无意义的绿色。HOM-SET 形式 (#474)。保留了一个伴随的两种打包形式 [FreeRngAb ⊣ Rng_Forget_Ab]。[free_rng_ab_adjunction] 来自通用箭头，是下面复合体中使用的一个，Instance/Rng/AFT.v 和 Test/ProbeFreeRing400.v 会使用它，并且它保持不变。[free_rng_ab_adjunction_hom] 是 Theory/Adjunction.v 中的 [Build_Adjunction'] 应用于自然双射 [free_rng_ab_hom_iso]，具有相同的左伴随 [FreeRngAb]、相同的右伴随和相同的插入：它的单位及其前向转置是 [free_rng_ab_adjunction] 在 [eq_refl]（[free_rng_ab_hom_unit], [free_rng_ab_hom_to]）的单位及前向转置，其逆转置是扩展 [free_rng_ab_extend]，因此它的余单位是对 [eq_refl]（[free_rng_ab_hom_counit]）处恒等的求值，而另一个余单位是在此处对 `≈`（[free_rng_ab_counit_evaluates]；在 [eq_refl] 一旦 STRENGTHS 的两个 [Qed] 层透明时，#1353）的求值。它存在于 Mac Lane 的 §VI.4 习题 4（Instance/Rng/FreeMonad.v）的张量代数单子 T 中，其乘法 U ε F 和比较函子随后进行计算，它不仅仅是一种绕过该不透明性的方式：它是习题“挨附 ⟨F, G, φ⟩”的字面阅读，Mac Lane 的挨附由它们的自然双射 φ (§IV.1) 给出，而 [free_rng_ab_hom_iso] 就是那个 φ。它不是第二个自由环，也不是第二个自由函子：箭头上的作用仍然是 [FreeRngAb] 的作用，这里在 `≈` 上重新标记生成元（[free_rng_ab_fmap_generators]；在 [eq_refl] 当两层都透明时，＃1353）。两个挨附在 [eq_refl] 被拒绝为相等，它们的逆转置以及在变量表达式上的余单位也是如此（Test/ProbeFreeRing474.v，R1 到 R3）。它的宇宙：[free_rng_ab_hom_iso] 和 [free_rng_ab_adjunction_hom] 绑定 @{u p}，[Ab] 和 [Rng] 自身绑定，还有 [FreeRngAb] 的四个更高层次，没有 [Set]，但有严格下界 [Set < u]；附加操作固定在 [Adjunction@{u p p u p p p p u p u}] 上，因此 [Build_Adjunction'] 的幽灵层不会被释放（未固定的版本会绑定它，不受约束，由 [About] 测量）。问题 #1353 记录了退出：一旦 [ump_universal_arrows] 和 [free_rng_ab_universal] 变为透明，记录保留一条，并以此为基础重置 T。

   在全局上下文下闭合的 116/116 个常量，计数取自源声明和构造函数 UNION [Print Module] 列出的内容（这增加了消元器和六个 [Program] 义务，这六个义务仅通过完全限定名称才能到达）。这句话的早期修订版本为 118/118。由于 PR “代数载体是集合”（2026-09-17） [fr_eq] 是 [Prop] 归纳的，而 Coq 只为它生成 [fr_eq_ind] 和 [fr_eq_sind]，而不是 [_rec] 和 [_rect]：通过在 [Print Module Free] 的输出中搜索 [fr_eq_*]，可以精确返回这两个。那两个消失的名称就是全部差异。“在全局上下文下闭合”的版本在此次修订中并未对所有 116 项重新运行；重新测量的是消去器的数量。更正 (#474)：#474 添加了六个常量，[fr_eval_pointwise]、[free_rng_ab_hom_iso]、[free_rng_ab_adjunction_hom] 以及三个 [eq_refl] 读回 [free_rng_ab_hom_counit]、[free_rng_ab_hom_unit] 和 [free_rng_ab_hom_to]，每个都“在全局上下文下封闭”，并在 #474 的打印假设块中命名；上述 116 个保持不变。关于同态集合形式的拒绝被固定在 Test/ProbeFreeRing474.v 中，其中重述了三个读回（C1 到 C3）并在其保护中命名了六个常量。未交付，范围包括：
   - [fr_eq] 没有标准形式，因此没有系数唯一性，没有判定程序，也没有基；对于两个形式表达式何时相等，只能依赖上面探讨的内容；
   - [FreeRngAbObject A] 没有分级，也没有与 ⊕ₙ A^⊗ⁿ 的识别，也没有与 Instance/Vect/TensorAlgebra.v 的 [TensorAlg] 进行比较（那个是基于不同生成结构的模块上的张量代数；没有建立任何映射，也未声称有任何映射）；
   修正 (#474)：该识别现在是 Instance/Rng/FreeMonad/Words.v 的 [T_TW_iso]，在 Ab 中是同构（其正向映射是环映射 [tw_to_rng]），并且与 ⊕ₙ A^⊗ⁿ 作为 Instance/Ab/TensorPower.v 的张量幂余积相对应；[FreeRngAbObject A] 本身仍然没有分级，并且与 [TensorAlg] 的比较需要 Ab ≅ RMod ℤ（问题 #1356）；
   - 没有交换变体，因此没有自由交换环，也与 Instance/Rng/Polynomial.v 的 ℤ [x] 无关 —— 特别是并不声称 [FreeRngAbObject ab_int] 是 ℤ [x]；
   - 比较仅限于两个复合对象：没有逐步比较 [FreeRngAb ◯ FreeAb] 与 [MonoidRingFunctor]，也没有声称任一中间范畴是已确定的；
   - [Rig_Forget_Mon] 不存在 [Set] 的 pin 修复，也没有在自由载体宇宙中重述幺半群路线；
   - 没有 [free_ring_composites_agree_unit] 的 counit 级伴随对象；
   - [to_adj_injective] 和 [unit_natural] 在这里被陈述，并且没有上游至 Theory/Adjunction.v。
*)

#[local] Obligation Tactic := idtac.

(* * ** Formal ring expressions over an abelian group / * ** 阿贝尔群上的形式环表达式 *)

Section FreeRingOnAb.

Context (A : AbObject).

Inductive FRTerm : Type :=
  | fr_gen  : carrier (cmon_setoid A) → FRTerm
  | fr_zero : FRTerm
  | fr_one  : FRTerm
  | fr_plus : FRTerm → FRTerm → FRTerm
  | fr_neg  : FRTerm → FRTerm
  | fr_mul  : FRTerm → FRTerm → FRTerm.

(*
 AN EARLIER REVISION of this inductive landed in [Type].  Since the PR
 “algebraic carriers are sets” (2026-09-17) it lands in [Prop], because
 [RigObject] carries a [rig_prop : PropEquiv (is_setoid rig_setoid)] field
 and the `≈` of [FreeRngAbObject] IS [fr_eq]: the relation must BE a [Prop]
 for that field to be the identity pair of implications.  The cost is one
 elimination — [fr_eval_respects] below goes through [pequiv_to] at the
 target ring — and nothing else in the file changes: the non-degeneracy
 theorems conclude in [False] or in an [eq] of integers, both already
 [Prop].  Test/ProbeTermModelPropRng.v pins the refusal of the old
 script. 

 --------
 这个诱导的早期修订版本出现在 [Type]。由于 PR“代数承载体是集合”（2026-09-17），它出现在 [Prop]，因为 [RigObject] 承载一个 [rig_prop : PropEquiv (is_setoid rig_setoid)] 域，并且 [FreeRngAbObject] 的 `≈` 是 [fr_eq]：为了让该域成为蕴含的恒等对，该关系必须是 [Prop]。代价是一次消去——下面的 [fr_eval_respects] 在目标环上通过 [pequiv_to]——文件中的其他内容没有变化：非退化定理在 [False] 或整数的 [eq] 中结束，这两者都已是 [Prop]。Test/ProbeTermModelPropRng.v 固定了旧脚本的拒绝。
*)
Inductive fr_eq : FRTerm → FRTerm → Prop :=
  (* congruence for each former, saturating under A's own [≈] / 每个前者的全等，在 A 自身的 [≈] 下饱和 *)
  | fre_gen {a b : carrier (cmon_setoid A)} :
      a ≈ b → fr_eq (fr_gen a) (fr_gen b)
  | fre_plus {s s' t t'} :
      fr_eq s s' → fr_eq t t' → fr_eq (fr_plus s t) (fr_plus s' t')
  | fre_neg {s s'} : fr_eq s s' → fr_eq (fr_neg s) (fr_neg s')
  | fre_mul {s s' t t'} :
      fr_eq s s' → fr_eq t t' → fr_eq (fr_mul s t) (fr_mul s' t')

  (* (0, +, -) is an abelian group / (0, +, -) 是一个阿贝尔群 *)
  | fre_add_assoc (s t u : FRTerm) :
      fr_eq (fr_plus (fr_plus s t) u) (fr_plus s (fr_plus t u))
  | fre_add_comm (s t : FRTerm) : fr_eq (fr_plus s t) (fr_plus t s)
  | fre_add_zero_l (s : FRTerm) : fr_eq (fr_plus fr_zero s) s
  | fre_neg_l (s : FRTerm) : fr_eq (fr_plus (fr_neg s) s) fr_zero

  (* (1, ·) is a monoid -- NOT assumed commutative / (1, ·) 是一个幺半群 —— 不假设交换性 *)
  | fre_mul_assoc (s t u : FRTerm) :
      fr_eq (fr_mul (fr_mul s t) u) (fr_mul s (fr_mul t u))
  | fre_mul_one_l (s : FRTerm) : fr_eq (fr_mul fr_one s) s
  | fre_mul_one_r (s : FRTerm) : fr_eq (fr_mul s fr_one) s

  (* · distributes over + on both sides / · 在两边分配 + *)
  | fre_distr_l (s t u : FRTerm) :
      fr_eq (fr_mul s (fr_plus t u)) (fr_plus (fr_mul s t) (fr_mul s u))
  | fre_distr_r (s t u : FRTerm) :
      fr_eq (fr_mul (fr_plus s t) u) (fr_plus (fr_mul s u) (fr_mul t u))

  (* the insertion of A is a homomorphism of abelian groups / A 的插入是阿贝尔群的同态 *)
  | fre_gen_zero : fr_eq (fr_gen (cmon_zero A)) fr_zero
  | fre_gen_plus (a b : carrier (cmon_setoid A)) :
      fr_eq (fr_gen (cmon_plus A a b)) (fr_plus (fr_gen a) (fr_gen b))

  | fre_sym {s t} : fr_eq s t → fr_eq t s
  | fre_trans {s t u} : fr_eq s t → fr_eq t u → fr_eq s u.

Lemma fr_refl (s : FRTerm) : fr_eq s s.
Proof.
  induction s.
  - exact (fre_gen (reflexivity _)).
  - exact (fre_trans (fre_sym (fre_add_zero_l fr_zero))
                     (fre_add_zero_l fr_zero)).
  - exact (fre_trans (fre_sym (fre_mul_one_l fr_one))
                     (fre_mul_one_l fr_one)).
  - exact (fre_plus IHs1 IHs2).
  - exact (fre_neg IHs).
  - exact (fre_mul IHs1 IHs2).
Qed.

Lemma fr_eq_Equivalence : Equivalence fr_eq.
Proof.
  constructor.
  - exact fr_refl.
  - exact (fun s t => fre_sym).
  - exact (fun s t u => fre_trans).
Qed.

Definition fr_Setoid : Setoid FRTerm := {|
  equiv        := fr_eq;
  setoid_equiv := fr_eq_Equivalence
|}.

(*
   * ** The two annihilation clauses are THEOREMS, not constructors

   [RigObject] has twelve law fields; seventeen constructors above meet
   ten of them.  The remaining two -- [rig_mul_zero_l] and
   [rig_mul_zero_r] -- are derivable in the presence of additive
   inverses, so they are NOT among the constructors and the presentation
   is by a generating set that carries no redundancy.  The derivation is
   the usual one: an element equal to its own double is zero. 

   --------
   * ** 这两个消去条款是定理，不是构造子

   [RigObject] 有十二个规律域；上面十七个构造子满足其中十个。剩下的两个——[rig_mul_zero_l] 和 [rig_mul_zero_r]——在存在加法逆元的情况下是可导出的，因此它们不属于构造子范围，该表示是由不包含冗余的生成集合给出的。推导方法是常规的：一个元素如果等于它自身的两倍，则该元素为零。
*)

Lemma fr_idem_zero (s : FRTerm) :
  fr_eq s (fr_plus s s) → fr_eq s fr_zero.
Proof.
  intro H.
  refine (fre_sym _).
  refine (fre_trans (fre_sym (fre_neg_l s)) _).
  refine (fre_trans (fre_plus (fr_refl (fr_neg s)) H) _).
  refine (fre_trans (fre_sym (fre_add_assoc (fr_neg s) s s)) _).
  refine (fre_trans (fre_plus (fre_neg_l s) (fr_refl s)) _).
  exact (fre_add_zero_l s).
Qed.

Lemma fr_mul_zero_l (s : FRTerm) : fr_eq (fr_mul fr_zero s) fr_zero.
Proof.
  apply fr_idem_zero.
  refine (fre_trans _ (fre_distr_r fr_zero fr_zero s)).
  exact (fre_sym (fre_mul (fre_add_zero_l fr_zero) (fr_refl s))).
Qed.

Lemma fr_mul_zero_r (s : FRTerm) : fr_eq (fr_mul s fr_zero) fr_zero.
Proof.
  apply fr_idem_zero.
  refine (fre_trans _ (fre_distr_l s fr_zero fr_zero)).
  exact (fre_sym (fre_mul (fr_refl s) (fre_add_zero_l fr_zero))).
Qed.

(* * ** The free ring on the abelian group A / * ** 阿贝尔群 A 上的自由环 *)

Definition FreeRngAbObject : RingObject := {|
  ring_rig := {|
    rig_setoid := {| carrier := FRTerm; is_setoid := fr_Setoid |};
    rig_zero := fr_zero;
    rig_add := fr_plus;
    rig_one := fr_one;
    rig_mul := fr_mul;
    rig_add_respects := fun _ _ Hs _ _ Ht => fre_plus Hs Ht;
    rig_mul_respects := fun _ _ Hs _ _ Ht => fre_mul Hs Ht;
    rig_add_assoc := fre_add_assoc;
    rig_add_comm := fre_add_comm;
    rig_add_zero_l := fre_add_zero_l;
    rig_mul_assoc := fre_mul_assoc;
    rig_mul_one_l := fre_mul_one_l;
    rig_mul_one_r := fre_mul_one_r;
    rig_distr_l := fre_distr_l;
    rig_distr_r := fre_distr_r;
    rig_mul_zero_l := fr_mul_zero_l;
    rig_mul_zero_r := fr_mul_zero_r;
    (*
 [fr_eq] IS a [Prop]-valued relation, so it is its own [Prop] mirror
 and both implications are the identity. 

 --------
 [fr_eq] 是一个 [Prop] 值的关系，因此它是其自身的 [Prop] 镜像，并且两个蕴涵都是恒等映射。
*)
    rig_prop := @PropEquiv_of_relation _ fr_Setoid fr_eq
                  (fun _ _ h => h) (fun _ _ h => h)
  |};
  ring_neg := fr_neg;
  ring_neg_respects := fun _ _ Hs => fre_neg Hs;
  ring_neg_l := fre_neg_l
|}.

(*
 The carrier of the free ring, seen through BOTH forgetful routes, IS
 the type of formal ring expressions, and its [≈] IS the quotienting
 relation.  These are equations between TYPES -- the convertibility
 exception the house style sanctions. 

 --------
 自由环的载体，通过两条遗忘路径看到，正是形式环表达式的类型，其 [≈] 是商关系。这些是类型之间的方程——可转换性异常是系统风格允许的。
*)
Example free_rng_ab_carrier_is_FRTerm :
  carrier (Ab_Forget (Rng_Forget_Ab FreeRngAbObject)) = FRTerm := eq_refl.

(*
 The corresponding reading through the MONOID route is deliberately NOT
 stated here.  [Rng_Forget_Mon] is instantiable only at
 [RingObject@{Set Set _}] (the pin is [Rig_Forget_Mon]'s,
 Theory/Algebra/Rig.v), and a section variable's universes are fixed
 by everything stated in the section, so writing that Example here would
 confine the WHOLE free-ring construction to [Set]-sized abelian groups.
 It is stated instead in the §IV.8 section below, where the monoid route
 already carries the pin. 

 --------
 通过 MONOID 路径的相应读取特意没有在此说明。[Rng_Forget_Mon] 只能在 [RingObject@{Set Set _}] 上实例化（引脚属于 [Rig_Forget_Mon]，位于 Theory/Algebra/Rig.v），并且节变量的宇宙由节中声明的所有内容固定，因此在此处编写该示例会将整个自由环构造限制在 [Set] 大小的阿贝尔群中。相反，它在下面的 §IV.8 节中说明，此处单元路径已经携带了引脚。
*)

Example free_rng_ab_equiv_is_fr_eq (s t : FRTerm) :
  (@equiv _ (is_setoid (rig_setoid FreeRngAbObject)) s t) = fr_eq s t
  := eq_refl.

(*
   * ** The insertion of the abelian group

   A group element becomes the corresponding generator.  This is a
   morphism of [Ab], not merely of [Sets]: [fre_gen_zero] and
   [fre_gen_plus] are exactly the two [CMonHom] laws, so the insertion
   costs no proof at all. 

   --------
   * ** 阿贝尔群的插入

   群元素变为相应的生成元。这是  [Ab] 的一个态射，而不仅仅是 [Sets] 的：[fre_gen_zero] 和 [fre_gen_plus] 恰好是两个 [CMonHom] 定律，因此插入完全不需要证明。
*)

Definition free_rng_ab_insert : A ~{Ab}~> Rng_Forget_Ab FreeRngAbObject.
Proof.
  unshelve refine {| cmon_map := _ |}.
  - unshelve refine {| morphism := fr_gen |}.
    intros a b H; exact (fre_gen H).
  - exact fre_gen_zero.
  - exact fre_gen_plus.
Defined.

Example free_rng_ab_insert_is_gen (a : carrier (cmon_setoid A)) :
  cmon_map free_rng_ab_insert a = fr_gen a := eq_refl.

(* * ** The ring extension of a homomorphism on generators / * ** 同态在生成元上的环扩展 *)

Section Extension.

Context (R : RingObject).
Context (h : A ~{Ab}~> Rng_Forget_Ab R).

Fixpoint fr_eval (t : FRTerm) : carrier (rig_setoid R) :=
  match t with
  | fr_gen a    => cmon_map h a
  | fr_zero     => rig_zero R
  | fr_one      => rig_one R
  | fr_plus s t => rig_add R (fr_eval s) (fr_eval t)
  | fr_neg s    => ring_neg R (fr_eval s)
  | fr_mul s t  => rig_mul R (fr_eval s) (fr_eval t)
  end.

(*
 One induction over the relation: seventeen cases, one per constructor.
 Ten are met by the corresponding law of the target ring; four are
 congruence for a former; TWO are the two [CMonHom] laws of [h] -- which
 is the only place the hypothesis that [h] is a group homomorphism
 rather than a bare function is spent -- and the last two are the target
 setoid's symmetry and transitivity.

 AN EARLIER REVISION of this proof inducted on [fr_eq] straight into the
 [Type]-valued goal `≈`.  Since the PR “algebraic carriers are sets”
 (2026-09-17) [fr_eq] is a [Prop] inductive and eliminates only into
 [Prop], so the script opens with [apply pequiv_to] at the TARGET ring's
 own [rig_prop] and each branch returns to `≈` with [pequiv_from].  The
 seventeen cases are unchanged; the induction hypotheses are now
 [pequiv]-valued, so the branches that consume one spend [pequiv_to] on
 it.  No hypothesis is added. 

 --------
 对该关系进行一次归纳：十七种情况，每个构造子各一例。十种由目标环的相应定律满足；四种是前者的合同性；两种是 [h] 的两个 [CMonHom] 定律——这是唯一使用 [h] 是群同态而不仅仅是普通函数这一假设的地方——最后两种是目标集合等价关系的对称性和传递性。这个证明的早期修订版本直接在 [fr_eq] 上引入到 [Type] 值的目标 `≈`。由于 PR “代数载体是集合”（2026-09-17） [fr_eq] 是一个 [Prop] 归纳，并且只消除到 [Prop]，因此脚本以 TARGET 环的自身 [rig_prop] 中的 [apply pequiv_to] 开始，并且每个分支都带着 [pequiv_from] 返回到 `≈`。十七个情况保持不变；归纳假设现在是 [pequiv] 值，因此消耗一个的分支会在其上花费 [pequiv_to]。没有添加假设。
*)
Lemma fr_eval_respects (s t : FRTerm) : fr_eq s t → fr_eval s ≈ fr_eval t.
Proof.
  intro He.
  apply pequiv_to.
  induction He as
    [ a b Hab
    | s s' t t' _ IHs _ IHt
    | s s' _ IHs
    | s s' t t' _ IHs _ IHt
    | s t u | s t | s | s
    | s t u | s | s
    | s t u | s t u
    | | a b
    | s t _ IHst
    | s t u _ IHst _ IHtu ]; simpl.
  - apply pequiv_from; exact (proper_morphism (cmon_map h) _ _ Hab).
  - apply pequiv_from.
    exact (rig_add_respects R _ _ (pequiv_to _ _ IHs)
                              _ _ (pequiv_to _ _ IHt)).
  - apply pequiv_from.
    exact (ring_neg_respects R _ _ (pequiv_to _ _ IHs)).
  - apply pequiv_from.
    exact (rig_mul_respects R _ _ (pequiv_to _ _ IHs)
                              _ _ (pequiv_to _ _ IHt)).
  - apply pequiv_from; exact (rig_add_assoc R _ _ _).
  - apply pequiv_from; exact (rig_add_comm R _ _).
  - apply pequiv_from; exact (rig_add_zero_l R _).
  - apply pequiv_from; exact (ring_neg_l R _).
  - apply pequiv_from; exact (rig_mul_assoc R _ _ _).
  - apply pequiv_from; exact (rig_mul_one_l R _).
  - apply pequiv_from; exact (rig_mul_one_r R _).
  - apply pequiv_from; exact (rig_distr_l R _ _ _).
  - apply pequiv_from; exact (rig_distr_r R _ _ _).
  - apply pequiv_from; exact (cmon_map_zero h).
  - apply pequiv_from; exact (cmon_map_plus h a b).
  - exact (symmetry IHst).
  - exact (transitivity IHst IHtu).
Qed.

(*
 The extension, as a morphism of [Rng].  Five obligations:
 respectfulness of the fold, and preservation of 0, +, 1 and ·.
 Preservation of NEGATION is not among them -- in [Rng] it is the
 derived [RigHom_neg] rather than a field -- yet it holds for THIS
 homomorphism definitionally all the same, the fixpoint having a clause
 for [fr_neg].  The last four obligations are [reflexivity], the
 fixpoint's clauses BEING those four equations.  One uniform body is
 used so the proof does not depend on the order [Program] emits the
 obligations in. 

 --------
 这个扩展，作为  [Rng] 的一个态射。有五个义务：
 尊重折叠，并保持 0、+、1 和 ·。
 保持取反不在其中——在  [Rng] 中，它是派生出来的  [RigHom_neg] 而不是一个域——然而对于此同态，它在定义上仍然成立，定点包含  [fr_neg] 的一条条款。最后四个义务是  [reflexivity]，定点的条款就是这四个方程。使用一个统一的主体，因此证明不依赖于  [Program] 发出义务的顺序。
*)
Program Definition free_rng_ab_extend : FreeRngAbObject ~{Rng}~> R := {|
  rig_map := {| morphism := fr_eval |}
|}.
Next Obligation.
  first [ (intros s t He; exact (fr_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (fr_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (fr_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (fr_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (fr_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.

Example free_rng_ab_extend_generators (a : carrier (cmon_setoid A)) :
  rig_map free_rng_ab_extend (fr_gen a) = cmon_map h a := eq_refl.

Example free_rng_ab_extend_zero :
  rig_map free_rng_ab_extend fr_zero = rig_zero R := eq_refl.

Example free_rng_ab_extend_one :
  rig_map free_rng_ab_extend fr_one = rig_one R := eq_refl.

Example free_rng_ab_extend_plus (s t : FRTerm) :
  rig_map free_rng_ab_extend (fr_plus s t)
    = rig_add R (rig_map free_rng_ab_extend s)
                (rig_map free_rng_ab_extend t) := eq_refl.

Example free_rng_ab_extend_mul (s t : FRTerm) :
  rig_map free_rng_ab_extend (fr_mul s t)
    = rig_mul R (rig_map free_rng_ab_extend s)
                (rig_map free_rng_ab_extend t) := eq_refl.

Example free_rng_ab_extend_neg (s : FRTerm) :
  rig_map free_rng_ab_extend (fr_neg s)
    = ring_neg R (rig_map free_rng_ab_extend s) := eq_refl.

(*
   * *** Uniqueness

   Any ring homomorphism out of the free ring agreeing with [h] on the
   generators IS the extension.  Six cases, one per former: the generator
   case is the agreement hypothesis, four are homomorphism laws of the
   competitor, and the [fr_neg] case is [RigHom_neg] -- a THEOREM of
   Theory/Algebra/Rig.v rather than a field, which is exactly the place
   that derivation earns its keep, mirroring [ab_map_neg]'s role in
   Instance/Ab/Free.v. 

   --------
   * *** 唯一性

   从自由环出来的任何环同态，如果在生成元上与 [h] 一致，那么它就是这个扩展。六种情况，每种对应一个前者：生成元情况对应一致性假设，四种情况是竞争者的同态法则，而 [fr_neg] 情况则是 [RigHom_neg] —— 这是 Theory/Algebra/Rig.v 中的一个定理，而非域，这正是导出发挥作用的地方，类似于 [ab_map_neg] 在 Instance/Ab/Free.v 中的作用。
*)
Lemma free_rng_ab_extend_unique (g : FreeRngAbObject ~{Rng}~> R)
  (Hg : ∀ a : carrier (cmon_setoid A),
          rig_map g (fr_gen a) ≈ cmon_map h a) (t : FRTerm) :
  rig_map g t ≈ fr_eval t.
Proof.
  induction t as [ a | | | t1 IHt1 t2 IHt2 | t IHt | t1 IHt1 t2 IHt2 ];
    simpl.
  - exact (Hg a).
  - exact (rig_map_zero g).
  - exact (rig_map_one g).
  - refine (transitivity (rig_map_add g t1 t2) _).
    exact (rig_add_respects R _ _ IHt1 _ _ IHt2).
  - refine (transitivity (RigHom_neg FreeRngAbObject R g t) _).
    exact (ring_neg_respects R _ _ IHt).
  - refine (transitivity (rig_map_mul g t1 t2) _).
    exact (rig_mul_respects R _ _ IHt1 _ _ IHt2).
Qed.

End Extension.

Arguments fr_eval {R} h t.
Arguments free_rng_ab_extend {R} h.

(*
   * ** The universal property, in the shape [universal_arrow_from_UMP]
   consumes 

   --------
   * ** 通用性质，在形状 [universal_arrow_from_UMP] 中消耗
*)
Theorem free_rng_ab_universal :
  ∀ (R : RingObject) (h : A ~{Ab}~> Rng_Forget_Ab R),
    ∃! g : FreeRngAbObject ~{Rng}~> R,
      h ≈ fmap[Rng_Forget_Ab] g ∘ free_rng_ab_insert.
Proof.
  intros R h.
  unshelve eexists.
  - exact (free_rng_ab_extend h).
  - intro a; simpl; reflexivity.
  - intros g Hg t; simpl.
    symmetry; apply (free_rng_ab_extend_unique R h g).
    intro a; symmetry; exact (Hg a).
Qed.

End FreeRingOnAb.

Arguments fr_gen {A} a.
Arguments fr_zero {A}.
Arguments fr_one {A}.
Arguments fr_plus {A} s t.
Arguments fr_neg {A} s.
Arguments fr_mul {A} s t.
Arguments fr_eq {A} s t.
Arguments fr_refl {A} s.
Arguments fre_gen {A a b} _.
Arguments fre_plus {A s s' t t'} _ _.
Arguments fre_neg {A s s'} _.
Arguments fre_mul {A s s' t t'} _ _.
Arguments fre_add_assoc {A} s t u.
Arguments fre_add_comm {A} s t.
Arguments fre_add_zero_l {A} s.
Arguments fre_neg_l {A} s.
Arguments fre_mul_assoc {A} s t u.
Arguments fre_mul_one_l {A} s.
Arguments fre_mul_one_r {A} s.
Arguments fre_distr_l {A} s t u.
Arguments fre_distr_r {A} s t u.
Arguments fre_gen_zero {A}.
Arguments fre_gen_plus {A} a b.
Arguments fre_sym {A s t} _.
Arguments fre_trans {A s t u} _ _.
Arguments fr_eval {A R} h t.
Arguments free_rng_ab_extend {A R} h.
Arguments fr_eval_respects {A} R h s t _.
Arguments free_rng_ab_extend_unique {A} R h g _ t.

(* * ** The universal arrow, the free functor and the adjunction / * ** 普遍箭头、自由函子与伴随 *)

Definition free_rng_ab_universal_arrow (A : Ab)
  : UniversalArrow A Rng_Forget_Ab :=
  universal_arrow_from_UMP A Rng_Forget_Ab (FreeRngAbObject A)
    (free_rng_ab_insert A) (free_rng_ab_universal A).

Program Definition free_rng_ab_AUniversalArrow (A : Ab)
  : AUniversalArrow A Rng_Forget_Ab (FreeRngAbObject A) := {|
  universal_arrow := free_rng_ab_insert A
|}.
Next Obligation.
  intros A R h.
  unshelve eexists.
  - exact (free_rng_ab_extend h).
  - intro a; simpl; reflexivity.
  - intros g Hg t; simpl.
    symmetry; apply (free_rng_ab_extend_unique R h g).
    intro a; exact (Hg a).
Qed.

Definition FreeRngAb : Ab ⟶ Rng :=
  LeftAdjointFunctorFromUniversalArrows Rng_Forget_Ab
    free_rng_ab_universal_arrow.

Definition free_rng_ab_adjunction : FreeRngAb ⊣ Rng_Forget_Ab :=
  AdjunctionFromUniversalArrows Rng_Forget_Ab free_rng_ab_universal_arrow.

Example FreeRngAb_obj (A : Ab) : FreeRngAb A = FreeRngAbObject A := eq_refl.

Example free_rng_ab_arrow_is_insert (A : Ab) :
  @arrow _ _ A Rng_Forget_Ab (free_rng_ab_universal_arrow A)
    = free_rng_ab_insert A := eq_refl.

Definition free_rng_ab_unit (A : Ab)
  : A ~{Ab}~> Rng_Forget_Ab (FreeRngAb A) :=
  @Category.Theory.Adjunction.unit _ _ _ _ free_rng_ab_adjunction A.

Example free_rng_ab_unit_is_insert (A : Ab)
  (a : carrier (cmon_setoid A)) :
  cmon_map (free_rng_ab_unit A) a = fr_gen a := eq_refl.

Definition free_rng_ab_counit (R : Rng)
  : FreeRngAb (Rng_Forget_Ab R) ~{Rng}~> R :=
  @Category.Theory.Adjunction.counit _ _ _ _ free_rng_ab_adjunction R.

Lemma free_rng_ab_counit_generator (R : Rng)
  (a : carrier (rig_setoid R)) :
  rig_map (free_rng_ab_counit R) (@fr_gen (Rng_Forget_Ab R) a) ≈ a.
Proof.
  exact (@to_adj_counit _ _ _ _ free_rng_ab_adjunction R a).
Qed.

Theorem free_rng_ab_counit_evaluates (R : Rng)
  (t : FRTerm (Rng_Forget_Ab R)) :
  rig_map (free_rng_ab_counit R) t
    ≈ fr_eval (@id Ab (Rng_Forget_Ab R)) t.
Proof.
  apply (free_rng_ab_extend_unique R (@id Ab (Rng_Forget_Ab R))
           (free_rng_ab_counit R)).
  intro a; exact (free_rng_ab_counit_generator R a).
Qed.

Lemma free_rng_ab_fmap_generators {A B : Ab} (u : A ~{Ab}~> B)
  (a : carrier (cmon_setoid A)) :
  rig_map (fmap[FreeRngAb] u) (fr_gen a) ≈ fr_gen (cmon_map u a).
Proof.
  symmetry.
  exact (unique_property
           (ump_universal_arrows (free_rng_ab_universal_arrow A)
              (@arrow _ _ B Rng_Forget_Ab
                 (free_rng_ab_universal_arrow B) ∘ u)) a).
Qed.

(*
   * ** The same adjunction in hom-set form (#474)

   A second packaging of [FreeRngAb ⊣ Rng_Forget_Ab], with the SAME left
   adjoint [FreeRngAb] and the same insertion: Theory/Adjunction.v's
   hom-set constructor [Build_Adjunction'] applied to the natural
   bijection [free_rng_ab_hom_iso], whose forward transpose is the one of
   [free_rng_ab_adjunction] (g ↦ U g ∘ insert) and whose inverse
   transpose is the extension [free_rng_ab_extend].  Its counit is then
   the evaluation of the identity by conversion ([free_rng_ab_hom_counit]),
   where the counit of [free_rng_ab_adjunction] is that evaluation up to
   `≈` here ([free_rng_ab_counit_evaluates]; at [eq_refl] once both
   [Qed] layers of the header's STRENGTHS are transparent, #1353).  The
   bijection is Mac Lane's φ of the exercise's “adjunction ⟨F, G, φ⟩”
   (§IV.1), so this is also the literal reading of the book.
   Instance/Rng/FreeMonad.v builds the tensor-algebra monad T of Mac
   Lane's §VI.4 Exercise 4 on it.  No second free ring and no second free
   functor: the action on arrows is still [FreeRngAb]'s, the relabelling
   of generators at `≈` here ([free_rng_ab_fmap_generators]; at
   [eq_refl] once both layers are transparent, #1353). 

   --------
   * ** 同样的伴随在同态集形式 (#474)[FreeRngAb ⊣ Rng_Forget_Ab] 的第二次封装，具有相同的左伴随 [FreeRngAb] 和相同的插入：Theory/Adjunction.v 中的同态集构造器 [Build_Adjunction'] 应用于自然双射 [free_rng_ab_hom_iso]，其正变换是 [free_rng_ab_adjunction] 的正变换（g ↦ U g ∘ insert），其逆变换是扩展 [free_rng_ab_extend]。其余单位随后为通过转换评估身份（[free_rng_ab_hom_counit]），其中 [free_rng_ab_adjunction] 的余单位是此处至 `≈` 的评估（[free_rng_ab_counit_evaluates]；在 [eq_refl] 处，一旦标头的两个 [Qed] 层的 STRENGTHS 都变为透明，#1353）。该双射是 Mac Lane 的 φ 出自练习“伴随 ⟨F, G, φ⟩”（§IV.1），因此这也是该书的字面读取。Instance/Rng/FreeMonad.v 构建 Mac Lane §VI.4 练习 4 上的张量代数幺半群 T。没有第二个自由环也没有第二个自由函子：箭头上的作用仍然是 [FreeRngAb] 的，在 `≈` 这里对生成元的重新标记（[free_rng_ab_fmap_generators]；在 [eq_refl] 当两层都透明时，#1353）。
*)

(* The evaluation respects pointwise-`≈` homomorphisms. / 该评估尊重逐点 `≈` 同态。 *)
Lemma fr_eval_pointwise@{u p +} {A : Ab@{u p}} {R : Rng@{u p}}
  (h h' : A ~{Ab@{u p}}~> Rng_Forget_Ab R) (H : h ≈ h') (t : FRTerm A) :
  fr_eval h t ≈ fr_eval h' t.
Proof.
  induction t as [ a | | | t1 IH1 t2 IH2 | t IH | t1 IH1 t2 IH2 ]; simpl.
  - exact (H a).
  - reflexivity.
  - reflexivity.
  - exact (rig_add_respects R _ _ IH1 _ _ IH2).
  - exact (ring_neg_respects R _ _ IH).
  - exact (rig_mul_respects R _ _ IH1 _ _ IH2).
Qed.

(* The natural bijection Rng(F A, R) ≅ Ab(A, U R): forward g ↦ U g ∘ insert, backward the extension. / 自然双射 Rng(F A, R) ≅ Ab(A, U R)：正向 g ↦ U g ∘ insert，反向为扩展。 *)
Definition free_rng_ab_hom_iso@{u p +} (A : Ab@{u p}) (R : Rng@{u p}) :
  @Isomorphism Sets@{p u}
    {| carrier := @hom Rng@{u p} (FreeRngAb A) R
     ; is_setoid := @homset Rng@{u p} (FreeRngAb A) R |}
    {| carrier := @hom Ab@{u p} A (Rng_Forget_Ab R)
     ; is_setoid := @homset Ab@{u p} A (Rng_Forget_Ab R) |}.
Proof.
  unshelve refine
    (@Build_Isomorphism Sets
       {| carrier := @hom Rng (FreeRngAb A) R
        ; is_setoid := @homset Rng (FreeRngAb A) R |}
       {| carrier := @hom Ab A (Rng_Forget_Ab R)
        ; is_setoid := @homset Ab A (Rng_Forget_Ab R) |}
       (@Build_SetoidMorphism
          (@hom Rng (FreeRngAb A) R) (@homset Rng (FreeRngAb A) R)
          (@hom Ab A (Rng_Forget_Ab R)) (@homset Ab A (Rng_Forget_Ab R))
          (fun g => fmap[Rng_Forget_Ab] g ∘[Ab] free_rng_ab_insert A) _)
       (@Build_SetoidMorphism
          (@hom Ab A (Rng_Forget_Ab R)) (@homset Ab A (Rng_Forget_Ab R))
          (@hom Rng (FreeRngAb A) R) (@homset Rng (FreeRngAb A) R)
          (fun h => free_rng_ab_extend h) _) _ _).
  - intros g g' H a. exact (H (fr_gen a)).
  - intros h h' H t. exact (fr_eval_pointwise h h' H t).
  - intros h a. reflexivity.
  - intros g t. simpl. symmetry.
    apply (free_rng_ab_extend_unique R _ g). intro a. reflexivity.
Defined.

Definition free_rng_ab_adjunction_hom@{u p +} :
  @Adjunction@{u p p u p p p p u p u} Rng@{u p} Ab@{u p}
    FreeRngAb Rng_Forget_Ab.
Proof.
  unshelve refine
    (@Build_Adjunction' Rng Ab FreeRngAb Rng_Forget_Ab
       free_rng_ab_hom_iso _ _).
  - intros A B R f g a. simpl.
    apply (proper_morphism (rig_map f)).
    exact (free_rng_ab_fmap_generators g a).
  - intros A R R' f g a. reflexivity.
Defined.

(* Its counit is the evaluation of the identity, by conversion. / 它的余单位是通过转换对恒等式的评估。 *)
Example free_rng_ab_hom_counit@{u p +} (R : Rng@{u p})
  (t : FRTerm (Rng_Forget_Ab R)) :
  rig_map (@counit _ _ _ _ free_rng_ab_adjunction_hom R) t
    = fr_eval (@id Ab@{u p} (Rng_Forget_Ab R)) t := eq_refl.

(* Its unit and its forward transpose ARE those of [free_rng_ab_adjunction]. / 它的单位和它的前向转置是 [free_rng_ab_adjunction] 的。 *)
Example free_rng_ab_hom_unit@{u p +} (A : Ab@{u p}) :
  @Category.Theory.Adjunction.unit _ _ _ _ free_rng_ab_adjunction_hom A
    = @Category.Theory.Adjunction.unit _ _ _ _ free_rng_ab_adjunction A
  := eq_refl.

Example free_rng_ab_hom_to@{u p +} (A : Ab@{u p}) (R : Rng@{u p})
  (g : FreeRngAb A ~{Rng@{u p}}~> R) :
  to (@adj _ _ _ _ free_rng_ab_adjunction_hom A R) g
    = to (@adj _ _ _ _ free_rng_ab_adjunction A R) g := eq_refl.

(*
   * * Two left adjoints of one right adjoint

   A general comparison, built transparently so that its components are
   available to the unit statement below.  Theory/Adjunction.v's
   [left_adjoint_iso] proves the same [F ≈ F'] but is [Qed], so nothing
   reduces through it and no component of it can be named. 

   --------
   * * 一个右伴随的两个左伴随

   一个通用比较，构建得很透明，以便其组件可用于下面的单位语句。Theory/Adjunction.v 的 [left_adjoint_iso] 证明了相同的 [F ≈ F']，但却是 [Qed]，所以没有通过它的约简，并且它的任何组件都无法命名。
*)

Section LeftAdjointComparison.

Context {C D : Category}.
Context {U : C ⟶ D}.

(*
 The forward transpose of an adjunction is injective, being one leg of
 an isomorphism of hom-setoids. 

 --------
 伴随的前向转置是单射，因为它是同态集合同构的一个部分。
*)
Lemma to_adj_injective {F : D ⟶ C} (AF : F ⊣ U) {x : D} {y : C}
  (f g : F x ~> y) :
  to (@adj _ _ _ _ AF x y) f ≈ to (@adj _ _ _ _ AF x y) g → f ≈ g.
Proof.
  intro H.
  refine (transitivity
            (symmetry (@to_adj_comp_law _ _ _ _ AF x y f)) _).
  refine (transitivity _ (@to_adj_comp_law _ _ _ _ AF x y g)).
  exact (@from_adj_respects _ _ _ _ AF x y _ _ H).
Qed.

(*
 Naturality of the unit along an ARBITRARY morphism of D.  The in-tree
 [unit_comp] (Theory/Adjunction.v) states naturality only along a
 morphism [x ~> U y], which is a different statement. 

 --------
 单位沿着 D 的任意态射的自然性。in-tree [unit_comp]（Theory/Adjunction.v）仅说明沿着态射 [x ~> U y] 的自然性，这是一个不同的陈述。
*)
Lemma unit_natural {F : D ⟶ C} (AF : F ⊣ U) {x y : D} (u : x ~> y) :
  @Category.Theory.Adjunction.unit _ _ _ _ AF y ∘ u
    ≈ fmap[U] (fmap[F] u)
        ∘ @Category.Theory.Adjunction.unit _ _ _ _ AF x.
Proof.
  unfold Category.Theory.Adjunction.unit.
  rewrite <- (@to_adj_nat_l _ _ _ _ AF x y (F y) id u).
  rewrite <- (@to_adj_nat_r _ _ _ _ AF x (F x) (F y) (fmap[F] u) id).
  rewrite id_left, id_right.
  reflexivity.
Qed.

(*
 The comparison: transpose the OTHER adjunction's unit back through this
 one.  Everything below is stated with both adjunctions as explicit
 arguments, so each lemma is available at the swapped instantiation too
 -- which is what makes one round-trip argument serve for both. 

 --------
 比较：将另一个伴随的单位通过这个伴随转置回去。下面的一切都是以两个伴随作为明确参数来陈述的，所以每个引理在交换实例化时也可用——这就是使一个往返论证可以同时适用于两者的原因。
*)
Definition adj_left_compare {F F' : D ⟶ C}
  (AF : F ⊣ U) (AF' : F' ⊣ U) (x : D)
  : F x ~> F' x :=
  from (@adj _ _ _ _ AF x (F' x))
       (@Category.Theory.Adjunction.unit _ _ _ _ AF' x).

(*
 The comparison is compatible with the units.  This is the statement
 Mac Lane's exercise asks for beside the isomorphism of functors, and
 it is two lines: [to_adj_unit] turns [fmap[U] h ∘ η] into [⌊h⌋], and
 the comparison was DEFINED as [⌈η'⌉]. 

 --------
 这个比较与单位是兼容的。这就是陈述：麦克莱恩的练习要求在函子同构之外，它有两行：[to_adj_unit] 将 [fmap[U] h ∘ η] 转换为 [⌊h⌋]，而比较定义为 [⌈η'⌉]。
*)
Theorem adj_left_compare_unit {F F' : D ⟶ C}
  (AF : F ⊣ U) (AF' : F' ⊣ U) (x : D) :
  fmap[U] (adj_left_compare AF AF' x)
    ∘ @Category.Theory.Adjunction.unit _ _ _ _ AF x
    ≈ @Category.Theory.Adjunction.unit _ _ _ _ AF' x.
Proof.
  refine (transitivity
            (symmetry (@to_adj_unit _ _ _ _ AF x (F' x)
                         (adj_left_compare AF AF' x))) _).
  exact (@from_adj_comp_law _ _ _ _ AF x (F' x) _).
Qed.

(*
 One round-trip argument; the other round trip is this lemma at the
 swapped pair. 

 --------
 一个往返论证；另一个往返论证是在交换对上的这个引理。
*)
Lemma adj_left_compare_round {F F' : D ⟶ C}
  (AF : F ⊣ U) (AF' : F' ⊣ U) (x : D) :
  adj_left_compare AF' AF x ∘ adj_left_compare AF AF' x ≈ id[F x].
Proof.
  apply (to_adj_injective AF).
  refine (transitivity
            (@to_adj_nat_r _ _ _ _ AF x (F' x) (F x)
               (adj_left_compare AF' AF x)
               (adj_left_compare AF AF' x)) _).
  refine (transitivity
            (compose_respects _ _ (reflexivity _) _ _
               (@from_adj_comp_law _ _ _ _ AF x (F' x) _)) _).
  (* [unit] IS [⌊id⌋] by definition, so the last step is [reflexivity]. / 根据定义，[unit] 是 [⌊id⌋]，所以最后一步是 [reflexivity]。 *)
  exact (adj_left_compare_unit AF' AF x).
Qed.

Definition adj_left_compare_iso {F F' : D ⟶ C}
  (AF : F ⊣ U) (AF' : F' ⊣ U) (x : D)
  : F x ≅ F' x := {|
  to := adj_left_compare AF AF' x;
  from := adj_left_compare AF' AF x;
  iso_to_from := adj_left_compare_round AF' AF x;
  iso_from_to := adj_left_compare_round AF AF' x
|}.

Lemma adj_left_compare_natural {F F' : D ⟶ C} (AF : F ⊣ U) (AF' : F' ⊣ U)
  {x y : D} (u : x ~> y) :
  adj_left_compare AF AF' y ∘ fmap[F] u
    ≈ fmap[F'] u ∘ adj_left_compare AF AF' x.
Proof.
  apply (to_adj_injective AF).
  refine (transitivity
            (@to_adj_nat_l _ _ _ _ AF x y (F' y)
               (adj_left_compare AF AF' y) u) _).
  refine (transitivity
            (compose_respects _ _
               (@from_adj_comp_law _ _ _ _ AF y (F' y) _)
               _ _ (reflexivity u)) _).
  refine (transitivity (unit_natural AF' u) _).
  symmetry.
  refine (transitivity
            (@to_adj_nat_r _ _ _ _ AF x (F' x) (F' y)
               (fmap[F'] u) (adj_left_compare AF AF' x)) _).
  exact (compose_respects _ _ (reflexivity _) _ _
           (@from_adj_comp_law _ _ _ _ AF x (F' x) _)).
Qed.

(*
 The two left adjoints are naturally isomorphic, with the comparison
 above as the family.  This is [Functor_Setoid]'s [≈] unfolded, so it
 is the same statement Theory/Adjunction.v's [left_adjoint_iso] proves
 -- built transparently here so that its components have names. 

 --------
 这两个左伴随是自然同构的，上述比较即为该族。这是 [Functor_Setoid] 的 [≈] 展开，因此它与 Theory/Adjunction.v 的 [left_adjoint_iso] 所证明的语句相同——在这里透明地构建，以便其组件有名字。
*)
Definition left_adjoints_agree {F F' : D ⟶ C}
  (AF : F ⊣ U) (AF' : F' ⊣ U) : F ≈ F'.
Proof.
  exists (adj_left_compare_iso AF AF').
  intros x y u; simpl.
  rewrite <- comp_assoc.
  rewrite <- adj_left_compare_natural.
  rewrite comp_assoc.
  rewrite adj_left_compare_round.
  rewrite id_left.
  reflexivity.
Defined.

End LeftAdjointComparison.

(* * * Mac Lane §IV.8 Exercise 2: the free ring in two ways / * * Mac Lane §IV.8 练习 2：两种方式的自由环 *)

Definition RngUnderlyingAb : Rng ⟶ Sets := Ab_Forget ◯ Rng_Forget_Ab.
Definition RngUnderlyingMon : Rng ⟶ Sets := Mon_Forget ◯ Rng_Forget_Mon.

Example rng_underlying_fobj_agree (R : Rng) :
  fobj[RngUnderlyingAb] R = fobj[RngUnderlyingMon] R := eq_refl.

Example rng_underlying_fmap_agree (R S : Rng) (f : R ~> S) :
  fmap[RngUnderlyingAb] f = fmap[RngUnderlyingMon] f := eq_refl.

(* * ** Route one: sets ⟶ abelian groups ⟶ rings / * ** 路线一：集合 ⟶ 阿贝尔群 ⟶ 环 *)

Definition free_ring_via_ab : Sets ⟶ Rng := FreeRngAb ◯ FreeAb.

Definition free_ring_via_ab_adjunction
  : free_ring_via_ab ⊣ RngUnderlyingAb :=
  Adjunction_Compose free_ab_adjunction free_rng_ab_adjunction.

(* * ** Route two: sets ⟶ monoids ⟶ rings / * ** 路线二：集合 ⟶ 幺半群 ⟶ 环 *)

Definition free_ring_via_mon : Sets ⟶ Rng :=
  MonoidRingFunctor ◯ FreeMonSets.

Definition free_ring_via_mon_adjunction
  : free_ring_via_mon ⊣ RngUnderlyingMon :=
  Adjunction_Compose free_mon_sets_adjunction zmring_adjunction.

(*
 Retyping the monoid route against the ABELIAN route's right adjoint is
 pure field copying: every field of [Adjunction] mentions the right
 adjoint only through [U y] and [fmap[U] f], and those agree
 definitionally, so the five field TYPES are convertible even though the
 two functor RECORDS are not. 

 --------
 针对阿贝尔路线的右伴随重打单子路线只是纯字段复制：[Adjunction] 的每个字段都仅通过 [U y] 和 [fmap[U] f] 提到右伴随，并且它们在定义上是一致的，因此五个字段的类型是可转换的，即使这两个函子记录不可转换。
*)
Definition free_ring_via_mon_adjunction_ab
  : free_ring_via_mon ⊣ RngUnderlyingAb :=
  @Build_Adjunction Rng Sets free_ring_via_mon RngUnderlyingAb
    (@adj _ _ _ _ free_ring_via_mon_adjunction)
    (@to_adj_nat_l _ _ _ _ free_ring_via_mon_adjunction)
    (@to_adj_nat_r _ _ _ _ free_ring_via_mon_adjunction)
    (@from_adj_nat_l _ _ _ _ free_ring_via_mon_adjunction)
    (@from_adj_nat_r _ _ _ _ free_ring_via_mon_adjunction).

(** ** The two composites agree / ** 两个复合体一致 *)

Definition free_ring_composites_agree : free_ring_via_ab ≈ free_ring_via_mon
  := left_adjoints_agree free_ring_via_ab_adjunction
       free_ring_via_mon_adjunction_ab.

(*
 Theory/Adjunction.v's [left_adjoint_iso] inhabits the SAME type -- the
 two adjunctions are fed to it here so the claim is machine-checked
 rather than asserted.  The two terms are NOT identified: that theorem
 is [Qed], so no component of it reduces and none can be named, which
 is exactly why the transparent version above was built. 

 --------
 Theory/Adjunction.v 的 [left_adjoint_iso] 属于相同的类型——这里将两个陪集传递给它，因此该断言是由机器检查的而不是直接声明的。这两个项没有被识别：那个定理是 [Qed]，因此它的任何组成部分都不会被化简，也无法命名，这正是上面构建透明版本的原因。
*)
Example free_ring_composites_agree_via_left_adjoint_iso :
  free_ring_via_ab ≈ free_ring_via_mon :=
  left_adjoint_iso RngUnderlyingAb free_ring_via_ab free_ring_via_mon
    free_ring_via_ab_adjunction free_ring_via_mon_adjunction_ab.

Definition free_ring_comparison (X : Sets)
  : free_ring_via_ab X ~{Rng}~> free_ring_via_mon X :=
  adj_left_compare free_ring_via_ab_adjunction
    free_ring_via_mon_adjunction_ab X.

(*
 [left_adjoints_agree] is [Defined], so its isomorphism family reduces
 and the comparison named here IS the component of the natural
 isomorphism -- by [eq_refl], not by an argument.  This is what
 [left_adjoint_iso] could not have given. 

 --------
 [left_adjoints_agree] 是 [Defined]，因此它的同构族减少了，而这里提到的比较是自然同构的组成部分——由 [eq_refl] 给出，而不是通过论证。这是 [left_adjoint_iso] 无法提供的。
*)
Example free_ring_comparison_is_agree_component (X : Sets) :
  to (projT1 free_ring_composites_agree X) = free_ring_comparison X
  := eq_refl.

Theorem free_ring_composites_agree_unit (X : Sets) :
  fmap[RngUnderlyingAb] (free_ring_comparison X)
    ∘ @Category.Theory.Adjunction.unit _ _ _ _
        free_ring_via_ab_adjunction X
    ≈ @Category.Theory.Adjunction.unit _ _ _ _
        free_ring_via_mon_adjunction_ab X.
Proof.
  exact (adj_left_compare_unit free_ring_via_ab_adjunction
           free_ring_via_mon_adjunction_ab X).
Qed.

(*
   * ** Readings of the two composites

   The two routes produce visibly different rings on the same generating
   setoid -- formal ring expressions over a free abelian group on one
   side, ℤ-linear combinations of words on the other -- and both object
   actions reduce.  This is a difference of TERMS; the two rings are
   provably isomorphic, and no inequality is proved anywhere.
   That they are nevertheless isomorphic is the exercise. 

   --------
   * ** 两个复合的读数

   这两条路线在同一个生成集合上生成明显不同的环——一边是在自由阿贝尔群上的形式环表达式，另一边是词的 ℤ 线性组合——并且两者的对象作用都会简化。这是项的差异；这两个环可以被证明是同构的，并且在任何地方都没有证明不等式。
   尽管如此，它们依然是同构的，这是一个练习题。
*)

Example free_ring_via_ab_obj (X : Sets) :
  free_ring_via_ab X = FreeRngAbObject (FreeAbObject X) := eq_refl.

Example free_ring_via_mon_obj (X : Sets) :
  free_ring_via_mon X = ZMonRing (FreeMonSetsObject X) := eq_refl.

(*
 The retyping is inert on the unit: the two adjunctions have the SAME
 forward transpose, hence the same unit, on the nose. 

 --------
 重新输入在单位上是惰性的：这两个伴随具有相同的前向转置，因此在单位上完全相同。
*)
Example retype_adj_agrees (X : Sets) (R : Rng)
  (f : free_ring_via_mon X ~{Rng}~> R) :
  to (@adj _ _ _ _ free_ring_via_mon_adjunction_ab X R) f
    = to (@adj _ _ _ _ free_ring_via_mon_adjunction X R) f := eq_refl.

Example retype_unit_agrees (X : Sets) :
  @Category.Theory.Adjunction.unit _ _ _ _
      free_ring_via_mon_adjunction_ab X
    = @Category.Theory.Adjunction.unit _ _ _ _
        free_ring_via_mon_adjunction X := eq_refl.

(*
   * * Non-degeneracy

   Nothing below is obtained by induction on [fr_eq]: every constructor
   of that relation concludes an equation, so no induction over it can
   produce a negative.  Each refutation maps OUT of the free ring into a
   concrete ring and reads the answer off there. 

   --------
   * * 非退化性

   下面的内容不是通过对 [fr_eq] 的归纳得到的：该关系的每个构造子都会得出一个方程，因此对它进行归纳无法产生负数。每个反证都将自由环映射到具体环中，并在那里读取答案。
*)

Section NonDegeneracy.

(* The hypotheses appear only in proofs, so they must be named for the section to discharge them as explicit arguments -- the Theory/EckmannHilton.v idiom. / 假设只出现在证明中，因此必须为这一节命名它们，以便将它们作为显式参数释放——Theory/EckmannHilton.v 的惯用法。 *)
Local Set Default Proof Using "All".

Context (A : AbObject).
Context (R : RingObject).
Context (Hne : rig_one R ≈ rig_zero R → False).

(*
 The constant-zero map is a homomorphism of abelian groups, hence a
 legitimate probe.  Under it every generator dies and the unit does
 not, which is what separates a generator from a scalar. 

 --------
 常零映射是阿贝尔群的同态，因此是一个合法的探针。在它之下，每个生成元消失，而单位元不消失，这就是生成元与标量的区别所在。
*)
Definition fr_zero_probe : A ~{Ab}~> Rng_Forget_Ab R.
Proof.
  unshelve refine {| cmon_map := _ |}.
  - unshelve refine {| morphism := fun _ => rig_zero R |}.
    intros a b Hab; reflexivity.
  - simpl; reflexivity.
  - intros a b; simpl; symmetry; exact (rig_add_zero_l R (rig_zero R)).
Defined.

(* The free ring is not the zero ring. / 自由环不是零环。 *)
Theorem free_rng_ab_zero_not_one : fr_eq (@fr_zero A) fr_one → False.
Proof.
  intro He.
  apply Hne; symmetry.
  exact (fr_eval_respects R fr_zero_probe _ _ He).
Qed.

(*
 No generator is the unit -- the insertion of A does not meet the
 scalars.  True of EVERY generator of EVERY abelian group. 

 --------
 没有生成元是单位——A 的插入不满足标量。每个阿贝尔群的每个生成元都是如此。
*)
Theorem free_rng_ab_gen_not_one (a : carrier (cmon_setoid A)) :
  fr_eq (fr_gen a) (@fr_one A) → False.
Proof.
  intro He.
  apply Hne; symmetry.
  exact (fr_eval_respects R fr_zero_probe _ _ He).
Qed.

End NonDegeneracy.

Arguments fr_zero_probe A {R}.
Arguments free_rng_ab_zero_not_one A {R} Hne _.
Arguments free_rng_ab_gen_not_one A {R} Hne a _.

(* * ** The integers embed in the free ring on the integers / * ** 整数嵌入在整数上的自由环中 *)

Lemma int_one_not_zero : rig_one Int_Ring ≈ rig_zero Int_Ring → False.
Proof. intro H; compute in H; discriminate H. Qed.

(*
 [Rng_Forget_Ab Int_Ring] IS Instance/Ab/Free.v's [ab_int], so the
 identity of [Ab] is already a probe and no new homomorphism is
 needed. 

 --------
 [Rng_Forget_Ab Int_Ring]  IS Instance/Ab/Free.v's  [ab_int] , so the
 identity of  [Ab]  is already a probe and no new homomorphism is
 needed.
*)
Definition rng_int_probe : ab_int ~{Ab}~> Rng_Forget_Ab Int_Ring :=
  @id Ab ab_int.

Theorem int_free_rng_gen_injective (m n : Z) :
  fr_eq (@fr_gen ab_int m) (@fr_gen ab_int n) → m = n.
Proof. exact (fr_eval_respects Int_Ring rng_int_probe _ _). Qed.

Theorem int_free_rng_gens_distinct :
  fr_eq (@fr_gen ab_int 2%Z) (@fr_gen ab_int 3%Z) → False.
Proof. intro H; discriminate (int_free_rng_gen_injective _ _ H). Qed.

Theorem int_free_rng_gen_not_one :
  fr_eq (@fr_gen ab_int 1%Z) fr_one → False.
Proof.
  exact (free_rng_ab_gen_not_one ab_int int_one_not_zero 1%Z).
Qed.

(*
   * ** The free ring on a free abelian group of rank two is NOT
   commutative

   The probe is the upper-triangular 2×2 integer matrices of
   Instance/Rng/Algebras/Associative.v -- the FIRST closed
   non-commutative [RingObject] in tree, [Lam2] being a second -- and
   the two generators go to its two non-commuting matrix units.  Both
   products COMPUTE, so the separation
   is [discriminate] on closed data. 

   --------
   * ** 自由阿贝尔群秩为二的自由环 **不是**交换的

   探针是 Instance/Rng/Algebras/Associative.v 中的上三角 2×2 整数矩阵 —— 树中的第一个闭合非交换 [RingObject]，[Lam2] 是第二个 —— 两个生成元映射到其两个不交换的矩阵单位。两个乘积都可以计算，所以分离在闭合数据上是 [discriminate]。
*)

Definition ut2_two_probe : AbTwoGens ~{Sets}~> Ab_Forget (Rng_Forget_Ab UT2).
Proof.
  unshelve refine {|
    morphism := fun b : carrier AbTwoGens =>
                  if b then ut2_e11 else ut2_e12
  |}.
  all: intros x y H; simpl in H; subst y; reflexivity.
Defined.

Definition rng_ut2_probe
  : FreeAbObject AbTwoGens ~{Ab}~> Rng_Forget_Ab UT2 :=
  free_ab_extend ut2_two_probe.

Definition rng_two_gens : AbObject := FreeAbObject AbTwoGens.

Definition rng_gx : FRTerm rng_two_gens :=
  @fr_gen rng_two_gens (@fa_gen AbTwoGens true).
Definition rng_gy : FRTerm rng_two_gens :=
  @fr_gen rng_two_gens (@fa_gen AbTwoGens false).

Example rng_gxgy_computes :
  rig_map (free_rng_ab_extend rng_ut2_probe) (fr_mul rng_gx rng_gy)
    = ut2_e12 := eq_refl.

Example rng_gygx_computes :
  rig_map (free_rng_ab_extend rng_ut2_probe) (fr_mul rng_gy rng_gx)
    = ut2_zero := eq_refl.

Theorem free_rng_ab_not_commutative :
  fr_eq (fr_mul rng_gx rng_gy) (fr_mul rng_gy rng_gx) → False.
Proof.
  intro He.
  pose proof (fr_eval_respects UT2 rng_ut2_probe _ _ He) as H.
  compute in H; discriminate H.
Qed.

Theorem free_rng_ab_two_gens_distinct : fr_eq rng_gx rng_gy → False.
Proof.
  intro He.
  pose proof (fr_eval_respects UT2 rng_ut2_probe _ _ He) as H.
  compute in H; discriminate H.
Qed.

(*
 The object just probed IS the ab-route free ring on the two-element
 setoid, so the witness exercises the composite of the exercise and not
 a construction beside it. 

 --------
 该对象刚刚探测的是双元集合上的ab-路线自由环，因此证人执行的是练习的复合，而不是旁边的构造。
*)
Example rng_two_gens_is_via_ab :
  FreeRngAbObject rng_two_gens = free_ring_via_ab AbTwoGens := eq_refl.

(*
   * ** The two-step transpose of the abelian route

   [Adjunction_Compose]'s transposes are the pasted transposes
   definitionally, so restricting a ring homomorphism out of the
   ab-route free ring to the generating SET is: restrict to the free
   abelian group, then restrict to the generators. 

   --------
   * ** 阿贝尔路径的两步转置

   [Adjunction_Compose] 的转置在定义上就是粘贴的转置，因此将一个环同态从阿贝尔路径自由环限制到生成集合，就是：先限制到自由阿贝尔群，然后再限制到生成元。
*)
Example free_ring_via_ab_transpose (X : Sets) (R : Rng)
  (f : free_ring_via_ab X ~{Rng}~> R) :
  to (@adj _ _ _ _ free_ring_via_ab_adjunction X R) f
    = to (@adj _ _ _ _ free_ab_adjunction X (Rng_Forget_Ab R))
        (to (@adj _ _ _ _ free_rng_ab_adjunction (FreeAb X) R) f)
  := eq_refl.

(*
   * * Measured boundaries

   Each [Fail] below was stripped once and its failure KIND read off the
   message; the two kinds are kept apart.  Every constant named in a
   [Fail] is also named in a command that must SUCCEED, so a rename
   breaks the file loudly instead of turning a negative vacuously
   green. 

   --------
   * * 测量边界

   下面的每个 [Fail] 都被剥离过一次，并从消息中读取它的失败类型；两种类型被分开保存。每个在 [Fail] 中命名的常量也会在一个必须成功的命令中被命名，因此重命名会明显破坏文件，而不是使一个负值虚假的变为绿色。
*)

(** ** CONVERSION negatives / ** 转换负面 *)

(*
 The two underlying-set functors agree on objects and on arrows -- both
 recorded above by [eq_refl] -- but they are NOT the same functor: the
 law fields are [Compose]'s obligations at different arguments.  Error:
 “cannot unify RngUnderlyingAb and RngUnderlyingMon”. 

 --------
 这两个基础集合函子在对象和箭头上是一致的——上面都由 [eq_refl] 记录——但它们不是同一个函子：律场是 [Compose] 在不同参数下的义务。错误：“无法统一 RngUnderlyingAb 和 RngUnderlyingMon”。
*)
Fail Example rng_underlying_records_agree :
  RngUnderlyingAb = RngUnderlyingMon := eq_refl.

(*
 Consequently the composed monoid-route adjunction cannot simply be
 ASCRIBED against the abelian route's right adjoint: [Adjunction]'s type
 mentions the whole functor record.  What DOES work is copying the five
 fields across ([free_ring_via_mon_adjunction_ab]), because each field
 type mentions the right adjoint only through [U y] and [fmap[U] f]. 

 --------
 因此，组合的幺半群-路线伴随不能简单地归因于阿贝尔路线的右伴随：[Adjunction] 的类型提到了整个函子记录。真正可行的方法是将五个字段复制过去（[free_ring_via_mon_adjunction_ab]），因为每个字段类型仅通过 [U y] 和 [fmap[U] f 提到右伴随。
*)
Fail Definition rng_mon_route_ascribed
  : free_ring_via_mon ⊣ RngUnderlyingAb :=
  Adjunction_Compose free_mon_sets_adjunction zmring_adjunction.

(*
 The two composites are non-convertible terms denoting isomorphic
 rings on the same
 generating setoid, so [free_ring_composites_agree] is not an
 isomorphism between a thing and itself. 

 --------
 这两个复合体是不可转换的项，表示在相同生成集上同构的环，所以 [free_ring_composites_agree] 不是一个事物与自身之间的同构。
*)
Fail Example rng_routes_convertible :
  free_ring_via_ab AbTwoGens = free_ring_via_mon AbTwoGens := eq_refl.

(*
 The UNIT computes ([free_rng_ab_unit_is_insert], above, is [eq_refl]);
 the COUNIT does not.  It is [unique_obj (ump_universal_arrows …)] and
 [ump_universal_arrows] (Theory/Universal/Arrow.v) is [Qed]-opaque, so
 nothing reduces through it -- [free_rng_ab_counit_generator] states the
 [≈] that does hold.  The discriminating control is the unit: it runs
 through the SAME [AdjunctionFromUniversalArrows] and DOES reduce, so
 the cause is that one constant's opacity and not the route as such.
 CORRECTION (#474): one of two; this file's own [free_rng_ab_universal]
 is the other (the header's STRENGTHS), and the counit of the hom-set
 form [free_rng_ab_adjunction_hom] is the evaluation at [eq_refl]
 ([free_rng_ab_hom_counit]). 

 --------
 UNIT 计算 (上文的 [free_rng_ab_unit_is_insert] 是 [eq_refl] ); COUNIT 则不计算。它是 [unique_obj (ump_universal_arrows …)] 和 [ump_universal_arrows] （Theory/Universal/Arrow.v）是 [Qed] - 不透明的，所以没有东西能通过它化简 —— [free_rng_ab_counit_generator] 陈述了 [≈] 是成立的。区分控制的是单位：它通过相同的 [AdjunctionFromUniversalArrows] 并且确实能化简，所以原因在于某个常数的不透明性，而不是路径本身。修正 (#474)：两个中的一个；这个文件自身的 [free_rng_ab_universal] 是另一个（标题的 STRENGTHS），而同构集形式的余单位 [free_rng_ab_adjunction_hom] 是在 [eq_refl] 的求值（[free_rng_ab_hom_counit]）。
*)
Fail Example rng_counit_computes (R : Rng) (a : carrier (rig_setoid R)) :
  rig_map (free_rng_ab_counit R) (@fr_gen (Rng_Forget_Ab R) a) = a
  := eq_refl.

(*
 Likewise the free functor's action on an arrow is defined by universal
 factorization rather than by a formula, so relabelling generators is
 the theorem [free_rng_ab_fmap_generators] and not a computation. 

 --------
 同样，自由函子在箭头上的作用是由泛化分解定义的，而不是由公式定义的，因此重新标记生成元是定理 [free_rng_ab_fmap_generators]，而不是计算。
*)
Fail Example rng_fmap_generator_computes {A B : Ab} (u : A ~{Ab}~> B)
  (a : carrier (cmon_setoid A)) :
  rig_map (fmap[FreeRngAb] u) (fr_gen a) = fr_gen (cmon_map u a)
  := eq_refl.

(*
   * ** FORMABILITY negatives: the monoid route is pinned at [Set]

   [Rig_Forget_Mon] (Theory/Algebra/Rig.v) has source [Rig@{u Set}]:
   the rig's hom-and-proof universe is literally [Set].  [Rng_Forget_Mon]
   is [Rig_Forget_Mon ◯ Ring_Forget_Rig] and inherits it, so the whole
   monoid route -- and hence the comparison, which needs both routes at
   ONE [Rng] -- is confined to rings whose carriers live in [Set].  The
   abelian route is not: [RngUnderlyingAb@{u u0}] leaves [u0] free.  The
   pin is the DONOR's and is not repaired here; it is not claimed
   unavoidable.  Error in both cases: “Cannot enforce Set = uh”. 

   --------
   * ** 可形成性缺点：幺半群路径固定在 [Set] 

   [Rig_Forget_Mon] （理论/代数/半环.v）有源代码 [Rig@{u Set}] ：半环的同态和证明宇宙实际上是 [Set] 。 [Rng_Forget_Mon] 是 [Rig_Forget_Mon ◯ Ring_Forget_Rig] 并继承它，因此整个幺半群路径——因此比较也需要在同一个 [Rng] 上的两个路径——受限于载体存在于 [Set] 的环。阿贝尔路径则不受限制：[RngUnderlyingAb@{u u0}] 使 [u0] 保持自由。固定点属于 DONOR 并未在此修复；也不声称这是不可避免的。两种情况下的错误：“无法强制执行 Set = uh”。
*)

(* Positive controls naming the two constants the negatives below name, so that renaming either breaks this file instead of turning a [Fail] vacuously green. Unconstrained, these elaborate. / 正向控制命名这两个常数，下面的否定命名，因此重命名其中任何一个都会破坏此文件，而不是让 [Fail] 虚假地变绿。没有约束，这些是详细的。 *)
Check (Rng_Forget_Mon : Rng ⟶ MonSets).
Check (Rig_Forget_Mon : Rig ⟶ MonSets).

Section MonRouteSetPin.

Universe uo uh.
Constraint Set < uh.

(*
 Positive controls: the abelian route's two forgetful functors DO
 elaborate at a ring whose homs live strictly above [Set]. 

 --------
 阳性对照：阿贝尔路的两个遗忘函子确实在一个其同态严格高于 [Set] 的环上展开。
*)
Check (Rng_Forget_Ab : Rng@{uo uh} ⟶ Ab).
Check (Rig_Forget_CMon : Rig@{uo uh} ⟶ CMon).

Fail Check (Rng_Forget_Mon : Rng@{uo uh} ⟶ MonSets).
Fail Check (Rig_Forget_Mon : Rig@{uo uh} ⟶ MonSets).

End MonRouteSetPin.

(* * ** Instrument check A [Fail] that must fail for a reason having nothing to do with this file, so that a broken [Fail] mechanism would be visible. / * ** 仪器检查 一个必须因与此文件无关的原因失败的 [Fail]，这样一个损坏的 [Fail] 机制就会显现出来。 *)
Fail Example rng_instrument_check : (0%Z = 1%Z) := eq_refl.
