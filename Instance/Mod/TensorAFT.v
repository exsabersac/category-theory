Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Universal.Element.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Construction.Elements.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.GAFT.Resize.
Require Import Category.Adjunction.SpanningArrow.
Require Import Category.Adjunction.Representability.Sets.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Instance.Ab.DirectedColimit.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Quotient.
Require Import Category.Instance.Mod.Tensor.
Require Import Category.Instance.Mod.Bimodule.
Require Import Category.Instance.Mod.Limit.
Require Import Category.Instance.Mod.Spanning.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   * * The tensor product of modules from the adjoint functor theorem

   nLab:      https://ncatlab.org/nlab/show/adjoint+functor+theorem
   nLab:      https://ncatlab.org/nlab/show/tensor+product+of+modules
   nLab:      https://ncatlab.org/nlab/show/representable+functor
   nLab:      https://ncatlab.org/nlab/show/solution+set+condition
   Wikipedia: https://en.wikipedia.org/wiki/Tensor_product_of_modules
   Riehl:     Category Theory in Context, §4.6 and §5.6

   Mac Lane, “Categories for the Working Mathematician”, 2nd ed. (GTM 5),
   §V.7, book p. 128 (PDF p. 137), is the source: the unnumbered
   construction of the tensor product from the adjoint functor theorem
   (catalog id `maclane:V.7:construction1`) and Exercise 3 (catalog id
   `maclane:V.7:ex3`).  CITED BY LOCATION AND BY THE IN-TREE CATALOG
   (doc/plan/books/maclane/inventory/V.json); the printed text was not
   consulted and no sentence of it is reproduced here.  Instance/Mod/
   Spanning.v quotes the two catalog summaries in full and is not repeated.

   Mac Lane's argument has three premises and a conclusion.  The premises
   are that K-Mod is small-complete, that Bilin(A,B;-) : K-Mod -> Set is
   continuous, and that the bilinear maps which SPAN their target form a
   solution set.  The conclusion is that Bilin(A,B;-) is representable, so
   that a universal bilinear map A x B -> A (x) B exists without any
   construction by generators and relations.

   THIS FILE DELIVERS THE THREE PREMISES AND THE CONCLUSION
   UNCONDITIONALLY, and says exactly what that costs.  Two of the premises
   are discharged the obvious way: [RMod_Complete] (Instance/Mod/Limit.v,
   imported) and [Bilin_PreservesImageLimit] below.  The third is BUILT
   here twice over.

   CORRECTION, PR “algebraic carriers are sets” (2026-09-17).  Until this
   commit the paragraph above ended “THIS FILE DELIVERS THE THREE PREMISES
   AND THE CONCLUSION AS A CONDITIONAL”, and this one read: “What does NOT
   go through is FEEDING it to the theorem: the index of an
   [ElementSolutionSet] that [representability_theorem] will accept must
   live at the ring's CARRIER universe, which that theorem also pins to
   [Set], while Mac Lane's index is a sigma over the OBJECTS of [RMod R],
   one universe up. ... So [tensor_via_AFT] takes its solution set as a
   hypothesis, and the same for Exercise 3.”  THREE of those clauses are
   now false and one is still true.

   STILL TRUE: [tensor_esols_direct] -- Mac Lane's COVERING FAMILY, WITH
   NO SMALLNESS, indexed by the spanning bilinear maps out of V x V' -- is
   a sigma over the OBJECTS of [RMod R] and is STILL refused by the
   theorem, as NEGATIVE 1 of Test/ProbeModTensorAFT449.v pins.

   FALSE NOW: (i) the [Set], which went with the annotation of
   [DiscreteCat_Functor] in this same PR; (ii) that no solution set at the
   carrier universe exists -- section 3A builds one, [tensor_esols_prop],
   indexed by the [Prop]-valued CONGRUENCES on the term module, and it is
   accepted; (iii) that [tensor_via_AFT] takes a hypothesis -- it does
   not, and neither does [bal_tensor_via_AFT].  The conditionals are kept
   under the names [tensor_via_AFT_of_esols] and
   [bal_tensor_via_AFT_of_esols], statement for statement, so nothing is
   lost.

   THE COST, stated once and pinned: one new side condition,
   [Set < carrier] at [RMod R], the sort of [Prop] reaching the index
   universe.  Section 3A measures it and NEGATIVE 8 of the probe pins it
   with the conditional form as its control.

   AND MAC LANE'S OWN ARGUMENT IS NOT ABANDONED.  Section 10 proves his
   §V.7 Lemma 2 at [RMod R] -- the spanning family IS small up to
   isomorphism, the small index being the same congruences -- and feeds
   the resizing to the theorem as [tensor_via_AFT_maclane], a second route
   to the same statement through p. 128's argument rather than through the
   kernel congruence directly.

   ** 1. WHAT IS DELIVERED, IN NINE STEPS, AND AT WHAT STRENGTH

   (1) ELEMENTS OF A LIMITING CONE IN [Sets].  [slim_family_cone],
   [slim_elem], [slim_elem_leg] and [slim_ext]: a compatible family of
   elements is a cone out of the singleton, its mediator evaluated at [ttt]
   is the element it names, and the legs of a limiting cone are jointly
   monic on elements.  The last is not reproved -- it is
   Instance/Ab/Limit.v's [absets_limit_ext], which this file consumes
   rather than copying, exactly as Instance/Mod/Limit.v does.  These four
   are the whole element calculus, and BOTH continuity proofs below are
   stated against them.

   (2) MAC LANE'S COVERING FAMILY, WITH NO SMALLNESS, UNCONDITIONALLY.
   [tensor_esols_direct : ElementSolutionSet (Bilin V V')] is his p. 128
   argument: given an arbitrary bilinear beta : V x V' -> C, corestrict it
   to the submodule generated by its image
   (Instance/Mod/Spanning.v's [rbl_gen_corestrict]), observe that the
   corestriction SPANS ([rbl_corestrict_spanning], by induction on the
   generation witness -- the one new lemma the step needs), and cover beta
   by the submodule inclusion.  The index is
   [SpanningArrowsOutOf (Bilin V V') SetsOne] at [eq_refl], the SAME index
   as the conditional [tensor_esols] of Instance/Mod/Spanning.v's section 7
   -- [tensor_esols_same_index] pins that, with the wide-pullback
   hypothesis passed EXPLICITLY, since the exported instance
   [RMod_HasWidePullbacks] would be found by resolution and then refused at
   the application.  Mac Lane's Lemma 2 route (wide intersections of
   subobjects, Instance/Mod/Spanning.v) and his p. 128 route (corestrict to
   the generated submodule, here) therefore agree on the nose about WHAT
   the solution set is indexed by, and differ only in what they assume.
   CORRECTION, PR “algebraic carriers are sets” (2026-09-17).  This step
   read: “NOTHING BELOW CONSUMES [tensor_esols_direct]: the theorem will
   not accept it, for the universe reason of section 2, so the only
   solution set ever fed to [tensor_via_AFT] in tree is the CIRCULAR
   [tensor_esols_from_tensor] of step (5).  [tensor_esols_direct]'s only
   consumers are its own three [eq_refl] readbacks and
   [tensor_esols_same_index].”  The first clause is still true -- the
   theorem still will not accept THIS family -- and the rest is false.
   [tensor_esols_direct] is now the SUBJECT of section 10:
   [tensor_spanning_SmallUpToIso] proves it small up to isomorphism and
   [tensor_esols_resized] resizes it into a family the theorem does
   accept.  And the solution set fed to the AFT by default is
   [tensor_esols_prop] of section 3A, not the circular one.

   NO SMALLNESS HERE, and that is now a statement about THIS constant
   rather than about the file.  [esol_index] is a bare [Type], so Mac
   Lane's cardinality bound (“such a C consists of all finite sums”) is
   not part of what the record asks for and this step supplies none.
   Section 10 supplies the SMALLNESS separately, as [SmallUpToIso]
   (Adjunction/GAFT/Resize.v), which is the shape Mac Lane's Lemma 2
   actually proves -- representatives up to isomorphism, not a cardinality
   bound.

   (3) CONTINUITY OF [Bilin V V'], UNCONDITIONALLY AND NOT VIA THE TENSOR.
   [Bilin_continuous : ContinuousFunctor (Bilin V V')] is proved
   ELEMENTWISE against an arbitrary limiting cone: the underlying cone of
   sets is limiting by Instance/Mod/Limit.v's
   [RMod_Forget_creates_continuous] (creation from [Sets_Complete], no
   adjunction presupposed), a bilinear map into the apex is exactly a
   compatible family of bilinear maps into the [K j], and the five laws
   come from joint monicity plus the law in each [K j].  No transport is
   needed and none is used: the argument never mentions the CHOSEN limit,
   so Structure/Limit/Preservation.v's [limitcone_transport] and
   [FCone_iso] -- which would have carried the statement from the created
   limit to an arbitrary one -- are available but not consumed.

   THE CIRCULAR ROUTE IS NAMED AND NOT USED.
   [preserves_image_of_representable (tensor_repr_of_UE V V')]
   (Adjunction/Representability/Sets.v) inhabits the same type in one
   line, and is CIRCULAR: it derives the theorem's hypothesis from the very
   tensor the theorem is meant to construct.  That is the circularity
   Instance/Ab/Limit.v warns against and Instance/Grp/FreeAFT.v
   discloses for its own solution set.  It is checked as a positive
   control in the probe, and NEGATIVE 6 there pins that the delivered term
   is a different one.

   (4) [Bilin_PreservesImageLimit] is [Continuous_PreservesImageLimit
   Bilin_continuous] (Construction/Comma/Creation.v).  That bridge is
   LOAD-BEARING and cannot be skipped: a [ContinuousFunctor] does not
   ascribe where the theorem asks for [PreservesImageLimit], the refusal
   being “cannot unify \”Limit.Limit K\“ and \”Cone.Cone K\“”, quoted at
   Instance/Ab/Limit.v.

   (5) THE CONSTRUCTION.  [tensor_via_AFT_of_esols V V' E : Representable
   (Bilin V V')] is [representability_theorem] at [RMod_Complete R],
   [Bilin_PreservesImageLimit V V'] and a solution set [E].  It is stated
   at TOP LEVEL, outside any [Section], for the reason
   Adjunction/Representability/Sets.v gives.
   [tensor_esols_from_tensor] -- index [unit], object [TensorMod V V'],
   element [tensor_gen] -- inhabits the hypothesis and is CIRCULAR, named
   so that the circularity is visible at every use site, exactly as
   Instance/Grp/FreeAFT.v's [Grp_Forget_solution_set_from_adjunction]
   is.  Its only role is to show the conditional is not vacuous;
   [tensor_via_AFT_from_tensor] is that instantiation.
   (CORRECTION, this PR: an earlier revision of this step wrote the
   conditional as [tensor_via_AFT V V' E].  Since the unconditional
   solution set landed, [tensor_via_AFT V V'] takes NO solution set --
   it is [tensor_via_AFT_of_esols V V' (tensor_esols_prop V V')] -- and
   the [E]-taking form is the [_of_esols] one.  The
   definition site carries the same correction.)

   (6) THE COMPARISON, AT `≅` AND NOT AT [eq_refl].  [tensor_AFT_iso] is
   [repr_unique_iso] (Functor/Representable.v) against
   [tensor_repr_of_UE], the representation read off Instance/Mod/Tensor.v's
   [tensor_UniversalElement] through the DIRECT route
   [Representable_of_UniversalElement] (Theory/Universal/Element.v;
   the header says why the Yoneda-composed route is the
   wrong one at a category whose objects sit above its homs).  The
   uniqueness clause is [tensor_AFT_iso_universal]
   ([repr_unique_iso_universal], Functor/Representable.v -- named with
   its file, since an unqualified citation would read as Element.v's), and
   the two [eq_refl] legs are
   [repr_of_ue_obj] (Theory/Universal/Element.v) and
   [tensor_UniversalElement_obj]
   (Instance/Mod/Tensor.v), read back here as
   [tensor_repr_of_UE_obj].  THE OBJECT COMPARISON IS `≅`, NOT [eq_refl]:
   the adjoint functor theorem builds its object as a limit inside the
   comma category and [TensorMod] is a quotient of formal terms.
   NEGATIVE 5 of the probe pins that.

   (7) AND THE COMPARISON CARRIES THE UNIVERSAL ELEMENT.
   [tensor_AFT_iso_carries_elem] says the AFT's universal bilinear map,
   transported along [tensor_AFT_iso] itself, IS [tensor_gen] at `≈`; the
   proof is naturality of the representation followed by
   [repr_induced_compatible] at the identity, and nothing about the
   solution set enters.  [tensor_AFT_elem_iso] is the element-level
   comparison ([universal_element_iso], Theory/Universal/Element.v),
   [tensor_AFT_elem_unique] its uniqueness clause
   ([universal_element_unique]), and [tensor_AFT_isos_agree] proves
   the two comparisons are the same isomorphism at `≈`.  That theorem and
   its [bal_] twin are the only two of the nine [E]-taking constants whose
   STATEMENT this PR changed, and only by the forced rename of their
   right-hand side to [tensor_AFT_iso_of_esols] / [bal_AFT_iso_of_esols];
   both sites carry the note.

   (8) EXERCISE 3: THE BALANCED TENSOR.  The balanced tensor of a right and
   a left module over a possibly non-commutative ring already exists
   (Instance/Mod/Bimodule.v's [BalTensor], landing in [Ab]); what did
   not exist is the FUNCTOR it represents.  [BalBiadd N M : Ab ⟶ Sets] is
   it -- object part [BalBiadditive N M A] with the pointwise setoid,
   arrow part postcomposition, on the pattern of Instance/Mod/
   Tensor.v -- together with [bal_universal_element :
   AUniversalElement (BalBiadd N M) (BalTensor N M)] built from [bal_med]
   and [bal_med_unique], whose object and element read back at [eq_refl].
   [BalBiadd_continuous] is the continuity, elementwise over [Ab]'s created
   limits ([Ab_Forget_creates_continuous], Instance/Ab/Limit.v) through
   the SAME four lemmas of step (1); [bal_tensor_via_AFT_of_esols N M E]
   is the construction over [Ab_Complete], and [bal_tensor_via_AFT N M]
   takes no solution set (an earlier revision of this step wrote
   [bal_tensor_via_AFT N M E], the arity it had before the
   unconditional solution set landed in this PR); [bal_AFT_iso] and
   [bal_AFT_iso_carries_elem] are the comparison with [BalTensor] and its
   element clause, and [bal_AFT_isos_agree] identifies the two.

   (9) EXERCISE 3'S SOLUTION SET, UNCONDITIONALLY.  [bal_esols_direct] is
   Mac Lane's argument over [Ab], and it needed four pieces of [Ab]
   vocabulary that were not in tree: [ABGenSub] (Instance/Mod/Spanning.v's
   [ABGen] has exactly the five fields of Instance/Ab/DirectedColimit.v:
   273's [AbSubgroup], so this is repackaging with no obligation),
   [AbImageSub] (the image of a homomorphism as a subgroup, the [Ab]
   counterpart of Instance/Mod/Quotient.v's [ImageSubmod]), [ab_split]
   (a bijective homomorphism splits) and [abg_subobj] (a subgroup as a
   [SubObj Ab], through [ab_injective_monic]).
   [bal_spanning_to_spanning] is then the [Ab] form of Instance/Mod/
   Spanning.v's [rbilinear_spanning_to_spanning], and
   [bal_gen_corestrict]/[bal_corestrict_spanning] the [Ab] form of the
   corestriction of step (2).

   ** 2. THE UNIVERSE WALL, MEASURED -- A HISTORY SECTION AND ONE LIVE
   CLAIM

   READ THIS SECTION AS THE RECORD OF A WALL THAT WAS ROUTED AROUND, not
   as a live limitation of the file.  Exactly one claim in it is still
   live: [tensor_esols_direct], the OBJECT-indexed family, is still
   refused by [representability_theorem].  Everything the section says
   about that refusal stands.  What it used to conclude from it -- that no
   unconditional construction was possible -- was corrected in the PR
   “algebraic carriers are sets” (2026-09-17) and is marked below.

   The chain.  The solution set's INDEX universe is also the SHAPE
   universe of the [Complete] the theorem is handed, and [RMod_Complete]
   puts that at the ring's carrier universe.  The current signature of
   [representability_theorem] is carried by
   Adjunction/Representability/Sets.v and is CITED rather than
   re-quoted here: an earlier revision of this comment quoted it as

   representability_theorem@{u u0 … u9} :
   ∀ {C : Category@{u8 Set Set}} (K : C ⟶ Sets@{Set u9}),
   Complete@{u7 u7 Set u8} → … ElementSolutionSet@{u8 Set u9 u7} K
   → Representable@{u u8 u9 u8 Set} K

   with FOUR literal [Set]s, every one of them a universe-minimization
   artifact of Instance/Discrete.v's then-unannotated
   [DiscreteCat_Functor], repaired in the same PR.  The quote is stale;
   the ARITHMETIC it illustrated is not, and Structure/Complete.v's SIZE
   NOTE, item 2, is the authority for it.

   Mac Lane's index is [SpanningArrowsOutOf (Bilin V V') SetsOne], a sigma
   over [obj[RMod R]], and [RModObject] is a record over a [SetoidObject],
   so its objects sit STRICTLY ABOVE its carriers.  The two cannot meet,
   and

   Definition n1 {R : RingObject} (V V' : RModObject R) :
   Representable (Bilin V V') :=
   representability_theorem (Bilin V V') (RMod_Complete R)
   (Bilin_PreservesImageLimit V V') (tensor_esols_direct V V').

   is refused.  THE REFUSAL IS NOT RE-QUOTED HERE.
   Test/ProbeModTensorAFT449.v's NEGATIVE 1 carries the re-measured,
   [Set]-free text with its own recorded correction, and is the single
   place it is maintained; an earlier revision of this comment quoted the
   pre-repair form, with “Cannot enforce Set = u_obj' because
   Set < u_obj'”, and that message no longer occurs.

   The spanning-arrow route is refused for a related reason seen from the
   other side:

   @GAFT_from_spanning (RMod R) Sets (Bilin V V') HWP
   (Bilin_PreservesWidePullbacks V V') (RMod_Complete R)
   (Bilin_PreservesImageLimit V V')

   is refused, and that refusal has MOVED TWICE.  An earlier revision of
   this comment quoted it at the completeness argument, “The term
   \”RMod_Complete R\“ has type \”Complete@{Set Set Set u}\“ …”; it then
   moved to the ambient category argument when [DiscreteCat_Functor] was
   annotated, and moved again when this PR widened
   Adjunction/SpanningArrow.v's [Section GAFTFromSpanning] off [Set].  It
   now reads, with the generated universe names replaced by readable ones
   positionally and everything else verbatim,

   The term “RMod R” has type “Category@{u_obj u_hom u_hom}”
   while it is expected to have type “Category@{u_obj' u_hom' u_hom'}”
   (universe inconsistency: Cannot enforce u_hom = u_hom' because
   u_hom < u_obj <= u_hom')

   -- the widened theorem wants objects at or below homs, and [RMod R] has
   homs strictly below objects.  So NO ADJUNCTION is delivered here, only
   a representation; see NOT DELIVERED (2), which is unchanged.  Exercise
   3 meets the index refusal at [Ab] ([bal_esols_direct] into
   [bal_tensor_via_AFT_of_esols]).  All three are NEGATIVES 1, 2 and 3 of
   Test/ProbeModTensorAFT449.v, each stripped and re-run in a copy of the
   whole probe so the refusal kind could be read rather than guessed.

   A WALL OF THE SAME FAMILY AS #1309, MEASURED NOT TO BE LIFTED BY IT.
   Instance/Grp/FreeAFT.v measures a wall of this family at [Grp]
   -- Mac Lane's literal index [Subgroup Gfix] refused there too -- and
   attributes the [Set] to a universe-MINIMIZATION artifact of
   Instance/Discrete.v's [DiscreteCat_Functor], which carries no universe
   binders; it reports the repair as three annotated lines filed as #1309
   (CORRECTION: it said “eleven recorded boundaries”; its own measurement
   paragraph finds TWENTY-TWO in FIFTEEN), and that the index IS accepted.
   THE REPAIR WAS APPLIED AND MEASURED; IT DOES NOT LIFT THIS WALL.
   With only the #1309 edit
   ([Program Definition DiscreteCat_Functor@{o h p co ch cp +} ...])
   applied in a full copy of the worktree and the tree rebuilt, the
   literal [Set] vanishes from the refusal but the refusal remains, now
   as the identification of the index universe with the ring's carrier
   universe: the [n1] quoted above then reports “The term
   \”tensor_esols_direct V V'\“ has type \”ElementSolutionSet@{u_a u_b
   u_c u_a} ...\“ while it is expected to have type
   \”ElementSolutionSet@{u_d u_b u_e u_b} ...\“ (universe inconsistency:
   Cannot enforce u_d = u_b because u_b < u_d)”, with NO [Set] anywhere
   in the message, and the [Ab] refusal of Exercise 3 likewise (“Cannot
   enforce u_f = u_g because u_g < u_f”).  The structural reason survives
   the repair: [Sets_Complete@{u u0} : Complete@{u u u u0}] fixes the
   shape universe at the carrier universe, while the index is a sigma
   over objects and [Submodule W : Type@{u}] with [carrier < u] puts any
   subobject-shaped index strictly above the carrier.  Three further
   repair attempts -- an explicitly annotated [ElementSolutionSet] with
   [Constraint Set < iu], a fully named [@representability_theorem], and
   the same with [RMod_Complete] replaced by an abstract
   [comp : @Complete (RMod R)] -- are each refused too, the last showing
   the identification is not [RMod_Complete]'s.

   AND THE WALL WAS NOT LIFTED; IT WAS ROUTED AROUND.  CORRECTION, PR
   “algebraic carriers are sets” (2026-09-17).  The paragraph above used
   to end: “Nothing here claims the wall is unavoidable.  What is claimed
   is that until it moves -- and landing #1309 alone is measured NOT to
   move it -- an AFT construction of the tensor product at [RMod R] is
   either conditional on a solution set at the ring's carrier universe, or
   circular.  This file delivers both readings and labels each.”  That was
   the headline sentence of the file and it is FALSE.  The wall has not
   moved: every refusal recorded above still stands, verbatim in substance,
   and the structural reason still holds of any index shaped as a sigma
   over objects or as a [Type]-valued congruence.  What changed is that an
   index of a THIRD shape was built -- the [Prop]-valued congruences on
   the term module (section 3A) -- and [Prop] is carrier-sized
   (Structure/Complete.v's SIZE NOTE, item 1).  A solution set at that
   index is accepted, so the construction is UNCONDITIONAL and
   NON-CIRCULAR, at an arbitrary ring, at the cost of the one side
   condition [Set < carrier].  Section 10 then shows the two readings were
   never as far apart as this section suggested: Mac Lane's OWN family IS
   small up to isomorphism, with the congruences as its small index.

   ** 3. MEASURED

   RE-MEASURED after the PR “algebraic carriers are sets” (2026-09-17);
   an earlier revision read 111 constants (78 heads, 33 obligations) and
   the criteria below are unchanged, only the counts.

   161 constants: 121 [.glob] declaration heads (94 [def], 27 [prf]) plus
   40 [Program] obligations, which appear in NEITHER the [.glob] heads NOR
   [Search inside].  The heads were counted with
   [awk '/^(def|prf) /{print $4}' Instance/Mod/TensorAFT.glob | sort -u];
   the obligations with
   [strings Instance/Mod/TensorAFT.vo | grep -o
   '[A-Za-z0-9_]*_obligation_[0-9]*' | sed 's/^[0-9]*//' | sort -u] -- the
   junk digit prefix STRIPPED, not dropped, most appearing in the census
   only prefixed ([5BalBiadd_obligation_1], [6Bilin_med_obligation_1] and
   the rest).  ALL 161 report “Closed under the global context”, with zero
   [Axioms:] lines, run through a generated scratch file of
   [Print Assumptions Category.Instance.Mod.TensorAFT.<name>] -- the
   obligations answer only to the qualified name.

   Counted BY TOKEN over the whole file with the criterion
   [grep -o 'Qed\.'] and [grep -o 'Defined\.'] -- the trailing period is
   what keeps the words used in this comment out of the count -- the
   numbers are 54 proof terminators of the first kind and FIFTEEN of the
   second (an earlier revision read 50 and EIGHT).

   WHICH OF THE FIFTEEN ARE LOAD-BEARING: SIX, each shown so by making it
   opaque in a copy of the WHOLE file and naming what stops.

   The two the earlier revision named are unchanged: [tensor_esols_direct]
   (then [tensor_esols_direct_index] and its two siblings stop, their
   [eq_refl] having the wrong type) and [bal_esols_direct] (then
   [bal_esols_direct_index] and its two siblings stop).

   Of the SEVEN added by this PR, FOUR are load-bearing, measured by
   flipping each one individually and recompiling the file and then
   Test/ProbeModTensorAFT449.v:
   [ker_iso]                     -- THE FILE stops: section 10's arrow
   clause needs its [to] component
   convertible.
   [tensor_esols_prop]           -- the PROBE stops ([p449_prop_obj],
   [p449_prop_elem]).
   [bal_esols_prop]              -- the PROBE stops
   ([p449_bal_prop_obj]).
   [tensor_spanning_SmallUpToIso] -- the PROBE stops
   ([p449_maclane_small_index]).
   The other three added here -- [QMod_gen_spanning], [mgen_preimage] and
   [ker_med_surjective] -- were flipped individually and BOTH file and
   probe still compile; their transparency is a choice, kept so the
   covering data stays computable.

   The five older non-load-bearing ones -- [rbl_corestrict_spanning],
   [tensor_esols_from_tensor], [bal_esols_from_tensor],
   [bal_restrict_image], [bal_spanning_to_spanning] and
   [bal_corestrict_spanning] -- are as the earlier revision recorded them
   and were not re-flipped in this PR.  (That list names six; the earlier
   revision's arithmetic “the other six” counted them against eight
   terminators and is left as written, since the names are what a reader
   needs.)

   UNIVERSES ([About] under [Set Printing Universes], all 161).
   RE-MEASURED, and the previous paragraph is withdrawn in full.  It read:
   “EXACTLY 21 of the 111 carry a word-bounded [Set], and they are
   precisely the two AFT applications and everything downstream of them”,
   and it quoted [tensor_via_AFT@{…} : ∀ {R : RingObject@{Set u8 u8}} …],
   [tensor_AFT_iso@{…} : ∀ {R : RingObject@{Set Set Set}} …] and
   [bal_tensor_via_AFT@{…} : ∀ {X : RingObject@{Set u5 u5}} …] as its
   headlines, with a paragraph attributing the [RingObject@{Set Set Set}]
   pin by isolation.  ALL OF IT IS STALE: every one of those [Set]s was
   the universe-minimization artifact of Instance/Discrete.v's
   [DiscreteCat_Functor], repaired in the PR “algebraic carriers are
   sets”.

   Measured now, with the criterion “a word-bounded [Set] appearing as a
   universe ARGUMENT inside an [@{…}] list in the printed type”:
   ZERO of the 161.  The command was an [About] of every name, generated
   from the [.glob] heads and the obligation census above, with
   [grep -E '@\{[^}]*\bSet\b'] over the output -- no hits, against 144
   lines that do print [RingObject@{…}], which is the instrument control.

   A DIFFERENT criterion, and the one that now matters: “a [Set < …] line
   in the CONSTRAINT block”.  Of the 133 names that print a universe list
   at all, 100 carry one.  These are bounds, not pins -- [Set < u] only
   says [u] is above [Set], which Lib.v's
   [Unset Universe Minimization ToSet] makes the default -- and the one
   that is a genuine SIDE CONDITION rather than noise is section 3A's
   [Set < carrier] on the unconditional constants.  Headlines:

   tensor_via_AFT@{u u0 u1 u2 …} :
   ∀ {R : RingObject@{u10 u2 u11}} (V V' : obj[RMod … R]),
   Representable@{u u0 u1 u0 u2} (Bilin … V V')
   ( * … Set < u2 / u2 < u0 / u2 < u1 … * )      <-- u2 IS the carrier

   tensor_via_AFT_of_esols@{… u2 …} :
   ∀ {R : RingObject@{u13 u2 u14}} … ElementSolutionSet@{u0 u2 u1 u2}
   (Bilin … V V') → Representable@{u u0 u1 u0 u2} (Bilin … V V')
   ( * … Set < u0 / Set < u11 / u2 < u0 / u2 < u1 / u2 < u11 … * )
   <-- NO bound on u2

   CongIdx@{u u0 u1 u2 u3 u4} : ∀ {R : RingObject@{u u0 u1}},
   obj[RMod@{u2 u3 u u1 u0} R] → obj[RMod@{u2 u3 u u1 u0} R] → Type@{u4}
   ( * … u0 <= u4 … * )          <-- the index may be taken AT the carrier

   THE ASYMMETRY AT [Ab], measured and not explained.  The same comparison
   for Exercise 3 shows [bal_tensor_via_AFT]'s block gaining exactly ONE
   line over [bal_tensor_via_AFT_of_esols]'s -- [Set < Projections.u0], a
   bound on a stdlib constant -- and NO new bound on the ring's carrier
   slot.  So the [Ab] half pays nothing the conditional was not already
   paying, while the [RMod R] half pays [Set < carrier].  Why the two
   differ is not established here.

   [Require] discipline: THIRTY-ONE imports (an earlier revision read 28;
   the PR “algebraic carriers are sets” added Category.Lib.Setoid.
   Propositional for [PropEquiv], and Category.Adjunction.GAFT together
   with Category.Adjunction.GAFT.Resize for section 10's [SolutionSet] and
   [SmallUpToIso]).  The earlier revision's closure figure of 169 files,
   and its record that four imports the first draft carried were droppable
   -- Category.Theory.Morphisms, Category.Structure.Limit,
   Category.Structure.Complete and Category.Adjunction.GAFT -- stand as
   written, except that the LAST of those four is now back, and is now
   load-bearing.  The closure was NOT recomputed in this PR and the figure
   169 should be read as the earlier measurement, not as current.

   Zero DECLARATION-HEAD COLLISIONS was measured for the earlier 111
   names by scanning every other [.glob] file in the landed tree for a
   [def]/[prf]/[ind]/[constr]/[scheme]/[inst] head equal to one of them,
   the file list produced by [find] and fed through [xargs] so that no
   [.gitignore] traversal rule can apply (ugrep honours [.gitignore] on
   traversal and returns nothing for names that exist).  THE SCAN WAS NOT
   RE-RUN for the 50 names this PR adds; a later reader should not cite
   the zero as covering them.

   [make todo] gains hits only from Test/ProbeModTensorAFT449.v, which now
   carries EIGHT guarded commands (seven before this PR) and NINE
   case-insensitive hits, the ninth being one prose mention of the guard's
   name; this file contributes none, measured by running the Makefile's
   own [MISSING] pattern over it.

   ** 4. NOT DELIVERED

   (1) WITHDRAWN.  This clause read “NO UNCONDITIONAL REPRESENTATION.
   [tensor_via_AFT] and [bal_tensor_via_AFT] take a solution set as a
   hypothesis, for the measured universe reason of section 2.  The only
   in-tree inhabitants of that hypothesis are the two CIRCULAR ones,
   [tensor_esols_from_tensor] and [bal_esols_from_tensor], read off the
   tensor products the theorem is meant to construct.  So what is
   demonstrated is that the machinery applies and that its output agrees
   with the explicit construction -- NOT that the tensor product exists
   independently of the explicit construction.  Instance/Grp/FreeAFT.v is
   in exactly this position and says so.”  The PR “algebraic carriers are
   sets” (2026-09-17) makes every sentence of it false, at both [RMod R]
   and [Ab], and Instance/Grp/FreeAFT.v moved with it.  WHAT IS DELIVERED
   IN ITS PLACE: [tensor_via_AFT] and [bal_tensor_via_AFT] take nothing
   beyond the ring and the modules; the tensor product of modules EXISTS
   by the adjoint functor theorem independently of the explicit
   construction, and [tensor_AFT_iso] then compares the two.  The
   circular constants are kept as remarks and are removal candidates.

   (1') THE SIDE CONDITION THAT REPLACES IT, so that this list is not
   shorter than it should be: the unconditional constants at [RMod R]
   carry [Set < carrier].  Section 3A states it, section 3 measures it
   against the conditional forms, and NEGATIVE 8 of the probe pins it.

   (2) NO ADJUNCTION.  [GAFT] and [GAFT_from_spanning] produce a left
   adjoint; both are refused at [RMod R] (section 2), so nothing here is a
   functor [Sets ⟶ RMod R] and no [⊣] appears below.  UNCHANGED by this
   PR and re-measured under the widening of
   Adjunction/SpanningArrow.v's [Section GAFTFromSpanning]: the refusal
   survives, with a new message, quoted in section 2.  Section 10's
   discharge of Mac Lane's Lemma 2 does NOT change this -- what Lemma 2
   supplies is the SMALLNESS premise, not [GAFT_from_spanning]'s wide
   pullbacks.  The tensor's parametrized adjunctions already in tree
   (Instance/Mod/Closed.v's [RMod_SymMonClosed],
   Instance/Mod/Bimodule.v) are untouched and unrelated.

   (3) NO CARDINALITY BOUND, and a correction.  This clause read “NO
   SMALLNESS, hence no cardinality bound: [esol_index] is a bare [Type],
   as Adjunction/SpanningArrow.v says of itself.”  The premise is
   still true of [esol_index] and of [tensor_esols_direct], and the
   conclusion no longer follows for the file: section 10 proves the
   spanning family SMALL UP TO ISOMORPHISM ([SmallUpToIso],
   Adjunction/GAFT/Resize.v), which is what Mac Lane's Lemma 2 actually
   asserts.  What is still not delivered is a CARDINALITY bound -- “such a
   C consists of all finite sums” -- which nothing here supplies and which
   [SmallUpToIso] does not imply.

   (4) NO [eq_refl] OBJECT COMPARISON, only `≅` with a uniqueness clause
   (probe NEGATIVE 5).

   (5) HALF WITHDRAWN.  This clause read “NO CONCRETE WITNESS.  Nothing
   below instantiates [R] at a named ring, so nothing exhibits the AFT
   object at [Int_Ring] or anywhere else”.  THAT HALF IS FALSE: nothing in
   THIS FILE instantiates [R], but Test/ProbeModTensorAFT449.v's
   [Section UnconditionalPayoff] now does, at [Int_Ring], at [Q_Ring] and
   at [Ring_op Int_Ring], for both the direct and the Mac Lane routes and
   for Exercise 3 -- which was impossible while the construction took a
   solution set it had no honest inhabitant for.  THE OTHER HALF STANDS:
   the tree still has no non-commutative ring at all
   (Instance/Mod/Tensor.v records that gap), so Exercise 3's
   non-commutative reading stays uninstantiated here as elsewhere, the
   opposite ring of a commutative one being commutative.

   (6) NOTHING ABOUT THE BASE-CHANGE CLAUSE of Exercise 3.  Instance/Mod/
   Spanning.v's [bal_change] and [bal_change_surjective] are that clause
   and are not extended here; the kernel of the comparison is still not
   described.

   (7) WITHDRAWN AS TO ITS FIRST CLAUSE.  It read “NO REPAIR OF THE
   UNIVERSE ARTIFACT.  Instance/Discrete.v is not touched, and #1309 stays
   open”.  The annotation landed in the PR “algebraic carriers are sets”
   (2026-09-17) and every [Set] this file used to quote went with it.  The
   SECOND clause stands and was the point of recording it: landing #1309
   did not lift this file's wall, as section 2 measures, and the wall was
   routed around by a different index rather than moved.

   (8) NOTHING IS REGISTERED AS AN [Instance] -- a representation and a
   solution set must not become globally resolvable.  The constants ARE
   registered in the Makefile's [make print-assumptions] gate block, one
   [Print Assumptions Category.Instance.Mod.TensorAFT.<name>] line each,
   so the axiom-free report of section 3 is re-run by that target rather
   than only by the scratch file it was first measured with.  (An earlier
   revision said “All 111 constants”; the count is now 161, and the gate
   block was extended in the same PR.)

   (9) NO UNIQUENESS FOR THE RESIZING.  [SmallUpToIso] is data, not a
   property (Adjunction/GAFT/Resize.v's header says so), so section 10
   chooses ONE small family of representatives and nothing here says a
   different choice gives the same [tensor_via_AFT_maclane].  The AFT's
   output is determined only up to isomorphism in any case, and
   [tensor_AFT_iso] is where that is made explicit. 

   --------
   * * 来自伴随函子定理的模的张量积

   nLab:       https://ncatlab.org/nlab/show/adjoint+functor+theorem 
   nLab:       https://ncatlab.org/nlab/show/tensor+product+of+modules 
   nLab:       https://ncatlab.org/nlab/show/representable+functor 
   nLab:       https://ncatlab.org/nlab/show/solution+set+condition 
   Wikipedia:  https://en.wikipedia.org/wiki/Tensor_product_of_modules 
   Riehl:     《分类理论上下文》，§4.6 和 §5.6

   Mac Lane，《为工作数学家准备的范畴论》，第2版（GTM 5），
   §V.7，书籍第128页（PDF第137页），是来源：未编号
   的构造来自伴随函子定理的张量积（目录ID  `maclane:V.7:construction1` ）和练习3（目录ID
   `maclane:V.7:ex3`）。被引用的地点及树内目录
   (doc/plan/books/maclane/inventory/V.json)；印刷文本未被查阅，文中没有句子被复现。实例/模块/
   Spanning.v 完整引用了两个目录摘要，并未重复。麦克·莱恩的论证有三个前提和一个结论。前提是：K-Mod 是小完备的；Bilin(A,B;-) : K-Mod -> Set 是连续的；以及那些张成（SPAN）其目标的双线性映射形成一个解集合。结论是 Bilin(A,B;-) 是可表示的，因此存在一个通用的双线性映射 A x B -> A (x) B，而无需通过生成元和关系来构造。

   该文件无条件地提供了三个前提和结论，并精确说明了其代价。两个前提以显而易见的方式被解除：[RMod_Complete]（Instance/Mod/Limit.v，已导入）和下面的 [Bilin_PreservesImageLimit]。第三个前提在此处被构造了两次。更正，PR “代数载体是集合”（2026-09-17）。直到这个提交之前，上面的段落以“本文件以条件形式提供三个前提和结论”结尾，并且这一段写道：“不成立的是将其输入定理：[ElementSolutionSet] 的索引 [representability_theorem] 必须存在于环的载体宇宙中，而该定理也将其固定在 [Set] 上，而 Mac Lane 的索引是 [RMod R] 对象的 sigma，再往上一层宇宙……所以 [tensor_via_AFT] 将其解集作为假设，练习 3 也是如此。”其中三个条款现在是假的，一个仍然是真的。仍然成立：[tensor_esols_direct] -- Mac Lane 的覆盖族，没有小性，由从 V x V' 出发的生成双线性映射索引 -- 是 [RMod R] 对象上的 sigma，并且仍然被定理拒绝，正如 Test/ProbeModTensorAFT449.v 的负 1 所指示的那样。

   现在错误：(i) [Set]，它随同这个 PR 中 [DiscreteCat_Functor] 的注释出现；(ii) 不存在承载宇宙中的任何解集 -- 第 3A 节构建了一个 [tensor_esols_prop]，由 [Prop] 值的同余在项模上索引，并且它被接受；(iii) [tensor_via_AFT] 采用了假设 -- 事实上没有，[bal_tensor_via_AFT] 也没有。条件语句被保留在 [tensor_via_AFT_of_esols] 和 [bal_tensor_via_AFT_of_esols] 名称下，逐条陈述，因此不会丢失任何内容。成本，一次性陈述并固定：一个新的附加条件，[Set < carrier] 在 [RMod R] 处，这种 [Prop] 达到索引宇宙。第3A节对其进行测量，探针的负8将其以条件形式作为控制固定。

   并且麦克莱恩自己的论证并未放弃。第10节证明了他在 [RMod R] 的 §V.7 引理2——生成族在同构下是小的，小索引是相同的同余——并将调整大小传递给定理作为 [tensor_via_AFT_maclane]，这是通过第128页的论证而不是直接通过核同余得到同一结论的第二条途径。

   ** 1. 以九个步骤交付的内容，以及其强度(1) [Sets]、[slim_family_cone]、[slim_elem]、[slim_elem_leg] 和 [slim_ext] 中限制锥的元素：一个兼容的元素族是从单例出的锥，其在 [ttt] 处评估的中介是它所命名的元素，限制锥的各条腿在元素上是联合单的。最后一点没有重新证明——它是 Instance/Ab/Limit.v 的 [absets_limit_ext]，本文件使用它而不是复制，就像 Instance/Mod/Limit.v 所做的那样。这四个构成了完整的元素演算，并且下面的两个连续性证明都是以它们为基础陈述的。(2) 麦克莱恩的覆盖族，无小性，无条件。[tensor_esols_direct : ElementSolutionSet (Bilin V V')] 是他在第128页的论证：给定任意双线性 β : V x V' -> C，将其限制到其像生成的子模上（Instance/Mod/Spanning.v 的 [rbl_gen_corestrict]），注意这个限制生成 SPANS（[rbl_corestrict_spanning]，通过生成证据的归纳——这一步需要的唯一新引理），并通过子模包含覆盖 β。索引为 [SpanningArrowsOutOf (Bilin V V') SetsOne] 在 [eq_refl]，与 Instance/Mod/Spanning.v 第7节的条件 [tensor_esols] 的索引相同——[tensor_esols_same_index] 固定了这一点，并且宽拉回假设明确传递，因为导出的实例 [RMod_HasWidePullbacks] 将通过解析找到，然后在应用时被拒绝。Mac Lane 的引理 2 路线（子对象的广泛交集，Instance/Mod/Spanning.v）和他第 128 页的路线（限制到生成的子模，这里）因此在解决集合按什么索引上完全一致，只是在假设上有所不同。更正，PR “代数载体是集合”（2026-09-17）。这一步读作：“下面没有任何东西消耗 [tensor_esols_direct]：定理不会接受它，因为第 2 节的宇宙原因，所以在树中唯一一次送给 [tensor_via_AFT] 的解集是步骤（5）的循环 [tensor_esols_from_tensor]。[tensor_esols_direct] 的唯一使用者是它自己的三个 [eq_refl] 读取值和 [tensor_esols_same_index]。”第一条仍然为真——定理仍然不会接受这个族——其余的是错误的。[tensor_esols_direct] 现在是第10节的主题：
   [tensor_spanning_SmallUpToIso] 证明它在同构下是小的，
   [tensor_esols_resized]  将其调整为定理可接受的一个族。并且默认提供给 AFT 的解集合是第3A节的 [tensor_esols_prop] ，而不是循环的那个。

   这里没有小性，这现在是关于这个常数的陈述，而不是关于文件的。[esol_index] 是一个裸 [Type]，因此 Mac Lane 的基数界限（“这样的 C 由所有有限和组成”）不是记录所要求的内容，这一步也没有提供。第10节单独提供了小性，作为 [SmallUpToIso] (Adjunction/GAFT/Resize.v)，这是 Mac Lane 的引理2 实际证明的形式——同构下的代表，而不是基数界限。(3) [Bilin V V'] 的连续性，无条件且不经过张量。  
   [Bilin_continuous : ContinuousFunctor (Bilin V V')] 针对任意极限锥在元素级上被证明：一系列集合的基础锥是由 Instance/Mod/Limit.v 的 [RMod_Forget_creates_continuous]（从 [Sets_Complete] 创建，无需假定伴随）所限制的，映射到顶点的双线性映射正好是一系列兼容的映射到 [K j] 的双线性映射，并且五条定律来自联合单性加上每个 [K j] 中的定律。不需要也没有使用迁移：论证中从未提到所选极限，因此 Structure/Limit/Preservation.v 的 [limitcone_transport] 和 [FCone_iso]——可以将从创建的极限到任意极限的陈述传递——是可用的但未被使用。循环路径被命名但未使用。
   [preserves_image_of_representable (tensor_repr_of_UE V V')]
   (Adjunction/Representability/Sets.v) 在一行中居于同一类型，并且是循环的：它从定理要构造的张量中推导出了定理的假设。这就是 Instance/Ab/Limit.v 所警告的循环性，以及 Instance/Grp/FreeAFT.v 为其自身解集所揭示的循环性。它在探针中作为正控制被检查，而那里的 NEGATIVE 6 表明所提供的项是不同的项。(4) [Bilin_PreservesImageLimit] 是 [Continuous_PreservesImageLimit Bilin_continuous]（Construction/Comma/Creation.v）。那座桥是承重的，不能跳过：[ContinuousFunctor] 并没有在定理要求 [PreservesImageLimit] 的地方赋值，拒绝的原因是 “cannot unify \“Limit.Limit K\” and \“Cone.Cone K\””，引自 Instance/Ab/Limit.v。(5) 构造。[tensor_via_AFT_of_esols V V' E : 可表示的(Bilin V V')] 在 [representability_theorem] 处，[RMod_Complete R] 处，[Bilin_PreservesImageLimit V V'] 处以及解集 [E] 处。它在顶层（TOP LEVEL）声明，位于任何 [Section] 之外，原因是 Adjunction/Representability/Sets.v 所指出的。[tensor_esols_from_tensor] -- 索引 [unit]，对象 [TensorMod V V']，元素 [tensor_gen] -- 位于假设中并且是循环的，命名如此以便在每个使用处都能看到循环性，正如 Instance/Grp/FreeAFT.v 的 [Grp_Forget_solution_set_from_adjunction] 一样。它的唯一作用是展示条件不是空的；[tensor_via_AFT_from_tensor] 就是该实例化。（更正，这次 PR：该步骤的早期版本将条件写作 [tensor_via_AFT V V' E]。）自从无条件解集落定以来，[tensor_via_AFT V V'] 不接受解集——它是 [tensor_via_AFT_of_esols V V' (tensor_esols_prop V V')]——而 [E] 接受形式是 [_of_esols]。定义位置也进行了相同的更正。(6) 比较在 `≅`，而不是在 [eq_refl]。[tensor_AFT_iso] 是 [repr_unique_iso]（Functor/Representable.v）与 [tensor_repr_of_UE] 的比较，通过 DIRECT 路径从 Instance/Mod/Tensor.v 的 [tensor_UniversalElement] 读取表示法 [Representable_of_UniversalElement]（Theory/Universal/Element.v；标题说明为什么 Yoneda 组合路径在其对象位于同态之上的范畴中是错误的）。唯一性条款是 [tensor_AFT_iso_universal]（[repr_unique_iso_universal], Functor/Representable.v —— 用其文件命名，因为未经限定的引用会被理解为 Element.v 的），两个 [eq_refl] 分支是 [repr_of_ue_obj]（Theory/Universal/Element.v）和 [tensor_UniversalElement_obj]（Instance/Mod/Tensor.v），在这里读回为 [tensor_repr_of_UE_obj]。对象比较是 `≅`，而不是 [eq_refl]：伴随函子定理将其对象构建为逗号范畴内的极限，而 [TensorMod] 是形式项的商。探针针脚的负五表明了这一点。(7) 并且该比较包含了通用元素。 [tensor_AFT_iso_carries_elem] 表示 AFT 的通用双线性映射，沿着 [tensor_AFT_iso] 本身传输，等于 [tensor_gen] 在 `≈`；证明是表示的自然性，随后在恒等映射处使用 [repr_induced_compatible]，而解集的内容并未涉及。 [tensor_AFT_elem_iso] 是元素级的比较（[universal_element_iso]，Theory/Universal/Element.v），[tensor_AFT_elem_unique] 是其唯一性条款（[universal_element_unique]），[tensor_AFT_isos_agree] 证明这两个比较在 `≈` 是相同的同构。 该定理及其 [bal_] 的对应定理，是九个参与 [E] 的常数中唯一两个其陈述被此 PR 改动的定理，并且仅是通过强制重命名其右侧至 [tensor_AFT_iso_of_esols] / [bal_AFT_iso_of_esols]；两个位置都有备注。(8) 练习 3：平衡张量。一个右模和一个左模在可能非交换环上的平衡张量已经存在（Instance/Mod/Bimodule.v 的 [BalTensor]，落在 [Ab] 中）；尚不存在的是它所表示的函子。[BalBiadd N M : Ab ⟶ Sets] 就是它——对象部分为 [BalBiadditive N M A]，使用逐点集合类，箭头部分为后合成，遵循 Instance/Mod/Tensor.v 的模式——以及 [bal_universal_element：AUniversalElement (BalBiadd N M) (BalTensor N M)]，由 [bal_med] 和 [bal_med_unique] 构建，其对象和元素在 [eq_refl] 中被读回。[BalBiadd_continuous] 是沿 [Ab] 创建的极限（[Ab_Forget_creates_continuous]，Instance/Ab/Limit.v）逐元素的连续性，通过步骤（1）的相同四个引理；[bal_tensor_via_AFT_of_esols N M E] 是在 [Ab_Complete] 上的构造，而 [bal_tensor_via_AFT N M] 不获取任何解集（此步骤的早期修订版本写作 [bal_tensor_via_AFT N M E]，它在无条件解集进入此 PR 之前的元数）；[bal_AFT_iso] 和 [bal_AFT_iso_carries_elem] 是与 [BalTensor] 及其元素子句的比较，而 [bal_AFT_isos_agree] 确定了这两者。(9) 练习 3 的解集，无条件。[bal_esols_direct] 是 Mac Lane 对 [Ab] 的论证，它需要四个 [Ab] 词汇，这些词汇不在树中：[ABGenSub]（Instance/Mod/Spanning.v 的 [ABGen] 恰好有 Instance/Ab/DirectedColimit.v 的五个字段：273 的 [AbSubgroup]，因此这是重新打包，没有义务）、[AbImageSub]（同态的像作为子群，[Ab] 是 Instance/Mod/Quotient.v 的 [ImageSubmod] 的对应）、[ab_split]（双射同态可以拆分）和 [abg_subobj]（通过 [ab_injective_monic] 将子群作为 [SubObj Ab]）。然后 [bal_spanning_to_spanning] 是 Instance/Mod/Spanning.v 的 [rbilinear_spanning_to_spanning] 的 [Ab] 形式，而 [bal_gen_corestrict] / [bal_corestrict_spanning] 是步骤 (2) 的余限制的 [Ab] 形式。** 2. 宇宙墙，测量——历史部分和一个有效声明

   请将本节作为一个被规避的墙的记录来阅读，而不是作为文件的实时限制。该节中恰好有一个声明仍然有效：[tensor_esols_direct]，按对象索引的系列，仍然被 [representability_theorem] 拒绝。关于该拒绝的所有描述仍然有效。过去从中得出的结论——无法进行无条件构造——已在 PR “代数承载体是集合”（2026-09-17）中得到纠正，并在下文标明。链。解集的索引宇宙也是 [Complete] 定理所处理的形状宇宙，而 [RMod_Complete] 将其放在环的承载宇宙中。[representability_theorem] 的当前签名由 Adjunction/Representability/Sets.v 承载，并在此被引用而非重新引用：该注释的早期版本曾将其引用为

   representability_theorem@{u u0 … u9} :
   ∀ {C : Category@{u8 Set Set}} (K : C ⟶ Sets@{Set u9}),
   Complete@{u7 u7 Set u8} → … ElementSolutionSet@{u8 Set u9 u7} K
   → Representable@{u u8 u9 u8 Set} K有四个字面上的 [Set]，每一个都是 Instance/Discrete.v 当时未注释的 [DiscreteCat_Functor] 的宇宙最小化工件，在同一个 PR 中修复。引用已经过时；它所展示的算术并没有过时，而 Structure/Complete.v 中的尺寸注释，第 2 项，是其权威依据。

   Mac Lane 的索引是 [SpanningArrowsOutOf (Bilin V V') SetsOne]，一个关于 [obj[RMod R] 的 sigma，而 [RModObject] 是关于 [SetoidObject] 的记录，因此它的对象严格高于其载体。这两者不可能相遇，并且

   定义 n1 {R : 环对象} (V V' : RModObject R) ：
   可表示性 (Bilin V V') :=
   representability_theorem (Bilin V V') (RMod_Complete R)
   (Bilin_PreservesImageLimit V V') (tensor_esols_direct V V')。被拒绝。此处未重新引用拒绝的内容。
   测试/ProbeModTensorAFT449.v 的 NEGATIVE 1 包含重新测量的、[Set] 自由文本及其自身记录的更正，并且这是唯一保存该文本的地方；该评论的早期版本引用了修复前的形式，内容为“Cannot enforce Set = u_obj' because Set < u_obj'”，但该消息现在不再出现。

   跨箭头路径被拒绝的原因与从另一侧看到的相关原因有关：

   @GAFT_from_spanning (RMod R) Sets (Bilin V V') HWP
   (Bilin_PreservesWidePullbacks V V') (RMod_Complete R)
   (Bilin_PreservesImageLimit V V')被拒绝了，并且这种拒绝已经移动了两次。之前的评论版本在完整性论证中引用了它，“术语 \“RMod_Complete R\” 的类型是 \“Complete@{Set Set Set u}\” …”；然后，当 [DiscreteCat_Functor] 被注释时，它被移到了环境范畴论证中，并在此 PR 扩展 Adjunction/SpanningArrow.v 的 [Section GAFTFromSpanning] 从 [Set] 时再次移动。它现在的内容是，在位置上用可读名称替换生成的宇宙名称，其余部分完全照原文，

   术语 “RMod R” 的类型是 “Category@{u_obj u_hom u_hom}”
   而期望的类型是 “Category@{u_obj' u_hom' u_hom'}”
   （宇宙不一致：无法强制 u_hom = u_hom'，因为
   u_hom < u_obj <= u_hom'）-- 扩展的定理希望对象位于或低于态射，而 [RMod R] 的态射严格低于对象。因此这里没有提供伴随，只提供一个表示；见未提供（2），此处保持不变。练习 3 在 [Ab]（[bal_esols_direct] 到 [bal_tensor_via_AFT_of_esols]）遇到了索引拒绝。全部三个都是 Test/ProbeModTensorAFT449.v 的负例 1、2 和 3，每个都在整个探针的副本中被剥离并重新运行，以便可以读取拒绝类型，而不是猜测。与#1309属于同一家族的一面墙，经测量不能被其提升。Instance/Grp/FreeAFT.v 在 [Grp] 测量了该家族的一面墙
   -- Mac Lane 的字面索引 [Subgroup Gfix] 在那里也被拒绝 -- 并将 [Set] 属性归因于 Instance/Discrete.v 的 [DiscreteCat_Functor] 的一个宇宙最小化工件，它没有携带任何宇宙绑定；它报告的修复是作为 #1309 提交的三条带注释的行（修正：它说的是“记录的边界有十一条”；它自己的测量段落发现了十五行中有二十二条），并且该索引被接受。修复已经应用并测量；它不能提升这面墙。仅应用 #1309 编辑
   ([Program Definition DiscreteCat_Functor@{o h p co ch cp +} ...])
   在工作树的完整副本中并重建树后，
   字面上的 [Set] 从拒绝中消失，但拒绝仍然存在，现在
   作为索引宇宙与环的承载宇宙的同一性：上文引用的 [n1] 然后报告“术语
   \“tensor_esols_direct V V'\” 的类型为 \“ElementSolutionSet@{u_a u_b u_c u_a} ...\”，而预计的类型为
   \“ElementSolutionSet@{u_d u_b u_e u_b} ...\”（宇宙不一致：不能强制 u_d = u_b，因为 u_b < u_d）”，消息中没有 [Set]，且锻炼 3 的 [Ab] 拒绝也是如此（“不能强制 u_f = u_g，因为 u_g < u_f”）。结构原因在修复后仍然存在：[Sets_Complete@{u u0} : Complete@{u u u u0}] 在承载宇宙中固定形状宇宙，而索引是对象上的一个 sigma，并且 [Submodule W : Type@{u}] 与 [carrier < u] 将任何子对象形状的索引严格置于承载之上。还有三次进一步的修复尝试——一个带有明确注释的 [ElementSolutionSet] 及 [Constraint Set < iu]、一个完全命名的 [@representability_theorem]，以及将 [RMod_Complete] 替换为抽象 [comp : @Complete (RMod R)] 后的相同尝试——每次都被拒绝，最后显示出该识别不是 [RMod_Complete] 的。而这堵墙并未被移开；它是被绕过的。更正，PR“代数载体是集合”（2026-09-17）。上面段落的结尾曾是：“这里没有人声称墙是无法避免的。所声称的是，在它移动之前——单独着陆 #1309 被测定为不会移动它——在 [RMod R] 上张量积的 AFT 构造要么依赖于环载体宇宙中的解集，要么是循环的。此文件提供了两种解读并对每种解读进行了标注。” 那是文件的标题句，而它是错误的。这堵墙没有移动：上述记录的每一次拒绝仍然有效，本质上逐字保留，并且任何以对象为索引或以 [Type] 值的合同形态的索引的结构性原因仍然成立。变化在于建立了第三种形状的索引——项模上的 [Prop] 值同余（第 3A 节）——并且 [Prop] 是承载大小的（Structure/Complete.v 的 SIZE NOTE，第 1 项）。在该索引处接受一个解集，因此构造是无条件的且非循环的，在任意环上成立，代价是单边条件 [Set < carrier]。第 10 节随后表明，两种解读从未像本节所示那样相差甚远：Mac Lane 自己的族在同构意义下是小的，以同余作为其小索引。

   ** 3. 测量过的

   在 PR“代数承载是集合”（2026-09-17）之后重新测量；早期版本列出 111 个常量（78 个首项，33 个义务），下面的标准保持不变，仅计数有所不同。161 个常量：121 个 [.glob] 声明头（94 个 [def]，27 个 [prf]）加上 40 个 [Program] 义务，它们既不出现在 [.glob] 头中，也不出现在 [Search inside] 中。头通过 [awk '/^(def|prf) /{print $4}' Instance/Mod/TensorAFT.glob | sort -u] 计算；义务通过 [strings Instance/Mod/TensorAFT.vo | grep -o ' [A-Za-z0-9_] *_obligation_ [0-9] *' | sed 's/^ [0-9] *//' | sort -u] —— 清除了冗余的数字前缀，但未删除，大多数只在普查中以带前缀的形式出现（[5BalBiadd_obligation_1]、[6Bilin_med_obligation_1] 及其余部分）。所有 161 个都报告“在全局上下文下关闭”，并且 [Axioms:] 行数为零，通过生成的 [Print Assumptions Category.Instance.Mod.TensorAFT.<name>] 临时文件运行 —— 义务仅对限定名称响应。在整个文件中按照令牌计数，标准为 [grep -o 'Qed\.'] 和 [grep -o 'Defined\.'] —— 末尾的句点是使此评论中使用的单词不计入统计的原因 —— 数字分别是第一类的 54 个证明终结符和第二类的 15 个（早期版本为 50 和 8）。

   哪 15 个是承重的：6 个，每一个通过在整个文件的副本中使其不透明并命名停止方式来显示。

   早期版本命名的两个保持不变：[tensor_esols_direct]（当时是 [tensor_esols_direct_index] 及其两个兄弟停止，它们的 [eq_refl] 类型错误）和 [bal_esols_direct]（当时为 [bal_esols_direct_index] 及其两个兄弟停止）。在这个 PR 中新增的七个中，有四个是承重的，通过单独翻转每一个并重新编译文件，然后测试/ProbeModTensorAFT449.v 来测量：
   [ker_iso]                      -- 文件停止：第10节的箭头条款需要它的 [to] 组件可转换。
   [tensor_esols_prop]            -- 探针停止（[p449_prop_obj]，[p449_prop_elem]）。
   [bal_esols_prop]               -- 探针停止（[p449_bal_prop_obj]）。
   [tensor_spanning_SmallUpToIso]  -- 探针停止（[p449_maclane_small_index]）。这里另外添加的三个——[QMod_gen_spanning]、[mgen_preimage] 和 [ker_med_surjective]——已单独翻转，并且文件和探针仍然可以编译；它们的透明性是可选的，保持透明以便覆盖数据仍然可计算。

   五个较旧的非承重项——[rbl_corestrict_spanning]、[tensor_esols_from_tensor]、[bal_esols_from_tensor]、[bal_restrict_image]、[bal_spanning_to_spanning] 和 [bal_corestrict_spanning]——按照早期版本记录的内容，没有在本次 PR 中重新翻转。（该列表列出六个；早期版本的算术“其他六个”是将它们与八个终端器进行对比计数，保持原样，因为名称正是读者所需的。）宇宙（[About] 在 [Set Printing Universes] 下，共 161 个）。
   重新测量，前一段已全部撤回。其内容为：
   “在 111 个中恰好有 21 个带有字词界限的 [Set]，它们正是两个 AFT 应用及其下游的所有内容”，
   并引用了 [tensor_via_AFT@{…} : ∀ {R : RingObject@{Set u8 u8}} …]、
   [tensor_AFT_iso@{…} : ∀ {R : RingObject@{Set Set Set}} …] 和
   [bal_tensor_via_AFT@{…} : ∀ {X : RingObject@{Set u5 u5}} …] 作为其标题，并附有一段将 [RingObject@{Set Set Set}] 引脚归因于隔离的说明。所有内容均已过时：每一个 [Set] 都是 Instance/Discrete.v 的 [DiscreteCat_Functor] 的宇宙最小化产物，在 PR “代数载体是集合” 中已修复。现在测量，根据标准“在打印类型中作为 [@{…}] 列表中的宇宙 ARGUMENT 出现的以单词为界的 [Set]”：在 161 个中为零。该命令是从 [.glob] 头和上述义务清单中生成的每个名称的 [About]，输出上使用 [grep -E '@\{[^}] *\bSet\b'] ——没有命中，而打印 [RingObject@{…}] 的有 144 行，这是仪器控制。不同的标准，现在重要的标准：在 CONSTRAINT 块中的一行 “[Set < …]”。在 133 个会打印宇宙列表的名称中，有 100 个包含这一行。这些是界限，而不是引脚——[Set < u] 仅表示 [u] 在 [Set] 之上，Lib.v 的 [Unset Universe Minimization ToSet] 使其成为默认值——而真正作为 SIDE CONDITION（副条件）而非噪声的是第 3A 节中关于无条件常数的 [Set < carrier]。标题：

   tensor_via_AFT@{u u0 u1 u2 …} :
   ∀ {R : RingObject@{u10 u2 u11}} (V V' : obj [RMod … R] ),
   Representable@{u u0 u1 u0 u2} (Bilin … V V')
   ( * … Set < u2 / u2 < u0 / u2 < u1 … * )      <-- u2 是载体tensor_via_AFT_of_esols@{… u2 …} ：
   ∀ {R : RingObject@{u13 u2 u14}} … ElementSolutionSet@{u0 u2 u1 u2}
   (Bilin … V V') → Representable@{u u0 u1 u0 u2} (Bilin … V V')
   ( * … Set < u0 / Set < u11 / u2 < u0 / u2 < u1 / u2 < u11 … *）
   <-- u2 没有上界

   CongIdx@{u u0 u1 u2 u3 u4} ：∀ {R : RingObject@{u u0 u1}},
   obj [RMod@{u2 u3 u u1 u0} R]  → obj [RMod@{u2 u3 u u1 u0} R]  → Type@{u4}
   ( * … u0 <= u4 … * )          <-- 索引可在承载对象上取在 [Ab] 处的不对称性，已测量但未解释。对练习 3 的相同比较显示 [bal_tensor_via_AFT] 的块相对于 [bal_tensor_via_AFT_of_esols] 的块恰好多出一行 —— [Set < Projections.u0]，是 stdlib 常量的一个界限 —— 并且对环的承载槽没有新的界限。因此，[Ab] 那一半没有支付条件原本未支付的部分，而 [RMod R] 那一半支付了 [Set < carrier] 。为什么两者不同，这里没有说明。[Require] 学科：三十一个导入（较早的版本是28；PR“代数载体是集合”添加了 Category.Lib.Setoid。对于 [PropEquiv] 是命题性的，以及 Category.Adjunction.GAFT 以及 Category.Adjunction.GAFT.Resize 用于第10节的 [SolutionSet] 和 [SmallUpToIso]）。早期版本的闭包数为169个文件，并且记录了初稿中四个可删除的导入——Category.Theory.Morphisms、Category.Structure.Limit、Category.Structure.Complete 和 Category.Adjunction.GAFT——保持原样，除了这四个中的最后一个现在已经恢复，而且现在是承重的。此 PR 中闭包未重新计算，数字169应理解为早期测量值，而非当前值。之前的111个名字通过扫描已着陆树中每隔一个的[.glob]文件来测量零DECLARATION-HEAD冲突，以查找[def] / [prf] / [ind] / [constr] / [scheme] / [inst]头是否等于其中之一，由[find]生成文件列表并通过[xargs]处理，以确保没有[.gitignore]遍历规则可以应用（ugrep在遍历时尊重[.gitignore]，并对存在的名字返回空）。对于此PR添加的50个名字，扫描未重新运行；后来的读者不应引用零冲突涵盖这些名字。[make todo] 只从 Test/ProbeModTensorAFT449.v 获得命中，该文件现在包含八个受保护命令（在此 PR 之前为七个）和九个不区分大小写的命中，第九个是对保护名称的一次散文提及；通过运行 Makefile 自己的 [MISSING] 模式对其进行测量，该文件没有贡献。

   ** 4. 未交付(1) 已撤回。本条款内容为：“无无条件表示。[tensor_via_AFT] 和 [bal_tensor_via_AFT] 将一个解集作为假设，基于第2节的测量宇宙原因。该假设中树内的唯一成员是两个循环成员 [tensor_esols_from_tensor] 和 [bal_esols_from_tensor]，它们从张量积中读取定理要构造的对象。因此，所证明的是该机制可用，并且其输出与显式构造一致——而不是张量积独立于显式构造存在。Instance/Grp/FreeAFT.v 正处于这种情况，并明确说明了这一点。” PR“代数载体是集合”（2026-09-17）使其每句话在 [RMod R] 和 [Ab] 上都不成立，并且 Instance/Grp/FreeAFT.v 随之移动。交付的内容
   代替它的是：[tensor_via_AFT] 和 [bal_tensor_via_AFT] 不超出环和模的范围；模的张量积通过伴随函子定理存在，与显式构造无关，而 [tensor_AFT_iso] 则比较两者。
   圆周常数作为备注保留，并可以被移除。

   (1') 替代它的附加条件，以确保此列表不短于其应有长度：无条件常数在 [RMod R] 处承载 [Set < carrier]。第 3A 节说明了它，第 3 节将其与条件形式进行比较，而探针的负 8 针对此进行了标定。(2) 无伴随。[GAFT] 和 [GAFT_from_spanning] 产生一个左伴随；在 [RMod R]（第2节）都被拒绝，因此这里没有任何是函子 [Sets ⟶ RMod R]，并且下面没有出现 [⊣]。此 PR 没有改变，并且在 Adjunction/SpanningArrow.v 的 [Section GAFTFromSpanning] 扩展下重新测量：拒绝依然存在，并伴有一个新消息，引用在第2节。第10节对 Mac Lane 引理2的解除并不改变这一点——引理2提供的是小性前提，而不是 [GAFT_from_spanning] 的广泛 pullbacks。树中已经存在的张量参数化伴随（Instance/Mod/Closed.v 的 [RMod_SymMonClosed]，Instance/Mod/Bimodule.v）保持不变且无关。(3) 无基数界限，以及一个更正。 本条款写道“无小性，因此无基数界限：[esol_index] 是一个裸 [Type]，正如 Adjunction/SpanningArrow.v 自述。” 前提仍然适用于 [esol_index] 和 [tensor_esols_direct]，但结论不再适用于该文件：第10节证明了跨越族在同构下很小（[SmallUpToIso]，Adjunction/GAFT/Resize.v），这正是 Mac Lane 引理2 实际断言的内容。仍未提供的是基数界限——“这样的 C 包含所有有限和”——这里没有提供，也不由 [SmallUpToIso] 蕴含。

   (4) 没有 [eq_refl] 对象比较，仅有带唯一性条款的 `≅`（探针 NEGATIVE 5）。(5) 部分撤回。该条款写道“没有具体的证人。下文没有在命名环上实例化 [R]，因此没有任何地方在 [Int_Ring] 或其他地方展示 AFT 对象”。这部分是假的：本文件中没有实例化 [R]，但 Test/ProbeModTensorAFT449.v 的 [Section UnconditionalPayoff] 现在在 [Int_Ring]、[Q_Ring] 和 [Ring_op Int_Ring] 中实例化了，对于直接路径和 Mac Lane 路径以及练习3——在构造时其解集中没有真实元素，这是不可能的。另一部分仍然成立：树中仍然完全没有非交换环（Instance/Mod/Tensor.v 记录了这个空白），所以练习3的非交换解释在这里和其他地方都保持未实例化状态，一个交换环的对环仍然是交换的。(6) 关于练习3的基本变换条款没有任何内容。Instance/Mod/Spanning.v 的 [bal_change] 和 [bal_change_surjective] 就是该条款，这里没有扩展；比较的核心仍未被描述。

   (7) 关于其第一条款已撤回。它的原文是“不可修复宇宙工件。Instance/Discrete.v 未被触及，#1309 保持开放状态”。该注释出现在 PR “代数承载体是集合” (2026-09-17) 中，并且此文件中引用的每个 [Set] 都随之处理。第二条款仍然有效，并且这是记录它的重点：应用 #1309 并没有解除此文件的障碍，如第2节所述，并且该障碍是通过不同的索引绕过的，而不是移动的。(8) 没有任何内容被注册为 [Instance] —— 表示和解集不能变得全局可解析。这些常量已在 Makefile 的 [make print-assumptions] 门块中注册，每行一个 [Print Assumptions Category.Instance.Mod.TensorAFT.<name>]，因此第 3 节中无公理报告是由该目标重新运行的，而不仅仅是由最初测量时的临时文件运行。（早期版本写道“所有 111 个常量”；现在数量为 161，并且在同一个 PR 中扩展了门块。）(9) 调整大小没有唯一性。[SmallUpToIso] 是数据，不是属性（Adjunction/GAFT/Resize.v 的标题说明了这一点），所以第 10 节选择了一个小的代表族，这里没有说明不同的选择会给出相同的 [tensor_via_AFT_maclane]。无论如何，AFT 的输出仅在同构意义下确定，[tensor_AFT_iso] 在那里明确说明了这一点。
*)

(* * ** 1. Elements of a limiting cone in [Sets] / * ** 1. [Sets] 中极限锥的元素 *)

Section SetsLimitElements.

Context {J : Category}.
Context {G : J ⟶ Sets}.
Context {N : Cone G}.
Context (HN : IsLimitCone N).

(* A compatible family of elements is a cone out of the singleton. / 一族兼容的元素是从单子对象出来的圆锥。 *)
Definition slim_family_cone (b : ∀ x : J, carrier (G x))
  (Hb : ∀ (x y : J) (f : x ~{J}~> y), fmap[G] f (b x) ≈ b y) : Cone G :=
  @Build_Cone J Sets G SetsOne
    (@Build_ACone J Sets SetsOne G (fun x => global_element (b x))
       (fun x y f _ => Hb x y f)).

Definition slim_elem (b : ∀ x : J, carrier (G x))
  (Hb : ∀ (x y : J) (f : x ~{J}~> y), fmap[G] f (b x) ≈ b y) :
  carrier (vertex_obj[N]) :=
  unique_obj (HN (slim_family_cone b Hb)) ttt.

Lemma slim_elem_leg (b : ∀ x : J, carrier (G x))
  (Hb : ∀ (x y : J) (f : x ~{J}~> y), fmap[G] f (b x) ≈ b y) (x : J) :
  cone_leg N x (slim_elem b Hb) ≈ b x.
Proof using All.
  exact (unique_property (HN (slim_family_cone b Hb)) x ttt).
Qed.

Lemma slim_ext (u v : carrier (vertex_obj[N]))
  (H : ∀ x : J, cone_leg N x u ≈ cone_leg N x v) : u ≈ v.
Proof using All. exact (absets_limit_ext (limitcone_isalimit HN) u v H). Qed.

End SetsLimitElements.

(* * ** 2. Mac Lane's direct solution set for [Bilin V V'] / * ** 2. Mac Lane 对 [Bilin V V'] 的直接解集 *)

Section DirectSolutionSet.

Context {R : RingObject}.
Context (V V' : RModObject R).

(* The corestriction of a bilinear map to the submodule generated by its image spans that submodule, by induction on the generation witness. / 双线性映射限制到其像生成的子模会生成该子模，这是通过对生成见证的归纳法得到的。 *)
Lemma rbl_corestrict_spanning {W : RModObject R} (β : RBilinear V V' W) :
  RBilinearSpanning (rbl_gen_corestrict β).
Proof using.
  intros [a D].
  induction D as [a Ha|a b Hab D IH| |a b D1 IH1 D2 IH2|r a D IH].
  - refine (mgen_base (rbl_image (rbl_gen_corestrict β)) _ _).
    destruct Ha as [v [w Hvw]].
    exists v, w; exact Hvw.
  - refine (mgen_resp (rbl_image (rbl_gen_corestrict β)) _ _ _ IH).
    exact Hab.
  - refine (mgen_resp (rbl_image (rbl_gen_corestrict β)) _ _ _
              (mgen_zero (rbl_image (rbl_gen_corestrict β)))).
    reflexivity.
  - refine (mgen_resp (rbl_image (rbl_gen_corestrict β)) _ _ _
              (mgen_plus (rbl_image (rbl_gen_corestrict β)) _ _ IH1 IH2)).
    reflexivity.
  - refine (mgen_resp (rbl_image (rbl_gen_corestrict β)) _ _ _
              (mgen_smul (rbl_image (rbl_gen_corestrict β)) r _ IH)).
    reflexivity.
Defined.

Definition tensor_esols_direct : ElementSolutionSet (Bilin V V').
Proof using.
  unshelve refine
    {| esol_index := SpanningArrowsOutOf (Bilin V V') SetsOne
     ; esol_obj := fun i => `1 i
     ; esol_elem := fun i => `1 (`2 i) ttt |}.
  intros c β.
  unshelve eexists.
  - refine (existT _ (SubmoduleMod (SubGenMod (rbl_image β))) _).
    refine (existT _ (global_element
                        (X := Bilin V V' (SubmoduleMod
                                (SubGenMod (rbl_image β))))
                        (rbl_gen_corestrict β)) _).
    exact (rbilinear_spanning_to_spanning (rbl_gen_corestrict β)
             (rbl_corestrict_spanning β)).
  - exists (smod_incl (SubGenMod (rbl_image β))).
    intros v w; reflexivity.
Defined.

Example tensor_esols_direct_index :
  esol_index tensor_esols_direct = SpanningArrowsOutOf (Bilin V V') SetsOne
  := eq_refl.

Example tensor_esols_direct_obj (i : SpanningArrowsOutOf (Bilin V V') SetsOne) :
  esol_obj tensor_esols_direct i = `1 i := eq_refl.

Example tensor_esols_direct_elem
  (i : SpanningArrowsOutOf (Bilin V V') SetsOne) :
  esol_elem tensor_esols_direct i = `1 (`2 i) ttt := eq_refl.

(* The conditional solution set of Instance/Mod/Spanning.v and the unconditional one above are indexed by the SAME type, on the nose. / Instance/Mod/Spanning.v 的条件解集和上面的无条件解集由完全相同的类型索引。 *)
Example tensor_esols_same_index
  (HWP : @HasWidePullbacks (RMod R)) :
  esol_index (@tensor_esols R V V' HWP) = esol_index tensor_esols_direct
  := eq_refl.

End DirectSolutionSet.

(** ** 3. [Bilin V V'] is continuous / ** 3. [Bilin V V'] 是连续的 *)

Section BilinContinuity.

Context {R : RingObject}.
Context (V V' : RModObject R).

Section AtALimitingCone.

Context {J : Category}.
Context {K : J ⟶ RMod R}.
Context {N : Cone K}.
Context (HN : IsLimitCone N).

(* The underlying cone of SETS is limiting, by Instance/Mod/Limit.v's creation result -- the only input from the module side. / SETS 的底层圆锥是限制性的，由 Instance/Mod/Limit.v 的创建结果——模块端的唯一输入。 *)
Definition bilin_sets_limit : IsLimitCone (FCone (RMod_Forget R) N) :=
  RMod_Forget_creates_continuous R J K N HN.

(*
 Joint monicity of the legs on ELEMENTS, in the spelling the module laws
 below present their goals in.  [slim_ext] states the same thing with
 [cone_leg (FCone (RMod_Forget R) N) x]; the two are convertible, and
 only this spelling is rewritable against [cmon_map_plus]. 

 --------
 在 ELEMENTS 上腿的联合单一性，在拼写模块法则中，下面展示了它们的目标。[slim_ext] 与 [cone_leg (FCone (RMod_Forget R) N) x] 陈述了相同的内容；两者是可互换的，并且只有这种拼写可以针对 [cmon_map_plus] 进行重写。
*)
Lemma bilin_lim_ext (u v : carrier (cmon_setoid vertex_obj[N]))
  (H : ∀ x : J, cmon_map (rm_hom (cone_leg N x)) u
                  ≈ cmon_map (rm_hom (cone_leg N x)) v) : u ≈ v.
Proof using All. exact (slim_ext bilin_sets_limit u v H). Qed.

Section AtACone.

Context (Q : Cone (Bilin V V' ◯ K)).

Lemma bilin_family_compat (q : carrier (vertex_obj[Q]))
  (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V'))
  (x y : J) (f : x ~{J}~> y) :
  fmap[RMod_Forget R ◯ K] f (rbl_map (cone_leg Q x q) v w)
    ≈ rbl_map (cone_leg Q y q) v w.
Proof using All.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ Q) x y f q v w).
Qed.

Definition bilin_med_elem (q : carrier (vertex_obj[Q]))
  (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  carrier (cmon_setoid vertex_obj[N]) :=
  slim_elem bilin_sets_limit (fun x => rbl_map (cone_leg Q x q) v w)
    (fun x y f => bilin_family_compat q v w x y f).

Lemma bilin_med_elem_leg (q : carrier (vertex_obj[Q]))
  (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) (x : J) :
  cmon_map (rm_hom (cone_leg N x)) (bilin_med_elem q v w)
    ≈ rbl_map (cone_leg Q x q) v w.
Proof using All.
  exact (slim_elem_leg bilin_sets_limit
           (fun x => rbl_map (cone_leg Q x q) v w)
           (fun x y f => bilin_family_compat q v w x y f) x).
Qed.

Program Definition Bilin_med (q : carrier (vertex_obj[Q])) :
  RBilinear V V' vertex_obj[N] := {|
  rbl_map := bilin_med_elem q
|}.
Next Obligation.
  intros q v v' Hv w w' Hw.
  apply bilin_lim_ext; intro x.
  rewrite !bilin_med_elem_leg.
  now rewrite Hv, Hw.
Qed.
Next Obligation.
  intros q v v' w.
  apply bilin_lim_ext; intro x.
  rewrite bilin_med_elem_leg.
  rewrite (cmon_map_plus (rm_hom (cone_leg N x))).
  rewrite !bilin_med_elem_leg.
  apply rbl_add_l.
Qed.
Next Obligation.
  intros q v w w'.
  apply bilin_lim_ext; intro x.
  rewrite bilin_med_elem_leg.
  rewrite (cmon_map_plus (rm_hom (cone_leg N x))).
  rewrite !bilin_med_elem_leg.
  apply rbl_add_r.
Qed.
Next Obligation.
  intros q r v w.
  apply bilin_lim_ext; intro x.
  rewrite bilin_med_elem_leg.
  rewrite (rm_map_smul (cone_leg N x)).
  rewrite !bilin_med_elem_leg.
  apply rbl_smul_l.
Qed.
Next Obligation.
  intros q r v w.
  apply bilin_lim_ext; intro x.
  rewrite bilin_med_elem_leg.
  rewrite (rm_map_smul (cone_leg N x)).
  rewrite !bilin_med_elem_leg.
  apply rbl_smul_r.
Qed.

Program Definition Bilin_cone_med :
  vertex_obj[Q] ~{Sets}~> vertex_obj[FCone (Bilin V V') N] :=
  {| morphism := Bilin_med |}.
Next Obligation.
  intros q q' Hq v w.
  change (bilin_med_elem q v w ≈ bilin_med_elem q' v w).
  apply bilin_lim_ext; intro x.
  rewrite !bilin_med_elem_leg.
  exact (proper_morphism (cone_leg Q x) q q' Hq v w).
Qed.

End AtACone.

Theorem Bilin_preserves_cone : IsLimitCone (FCone (Bilin V V') N).
Proof using All.
  intro Q.
  unshelve refine {| unique_obj := Bilin_cone_med Q |}.
  - intros x q v w.
    exact (bilin_med_elem_leg Q q v w x).
  - intros u Hu q v w.
    apply bilin_lim_ext; intro x.
    rewrite (bilin_med_elem_leg Q q v w x).
    symmetry; exact (Hu x q v w).
Qed.

End AtALimitingCone.

Definition Bilin_continuous : ContinuousFunctor (Bilin V V') :=
  fun J K N HN => Bilin_preserves_cone HN.

Definition Bilin_PreservesImageLimit :
  @PreservesImageLimit (RMod R) Sets (Bilin V V') :=
  Continuous_PreservesImageLimit Bilin_continuous.

End BilinContinuity.

(* * ** 3A. [Prop] congruences on the term module: a solution set AT the carrier universe / * ** 3A. [Prop] 关于项模的同余：在承载宇宙上的解集 *)

(*
 THE REPAIR OF THE WALL OF SECTION 2 OF THE HEADER, AND WHY IT WORKS.

 Mac Lane's index is a sigma over the OBJECTS of [RMod R], which sit
 strictly above its carriers; the theorem wants the index AT the carrier
 universe (Structure/Complete.v's SIZE NOTE, item 2(b), is the authority
 and is not restated).  What is built here is a DIFFERENT index for the
 same job: the [Prop]-valued congruences on the term module [MTerm V V'].

 Every field of [IsCongruence] is a [Prop], so the record is a [Prop] and
 the sigma over it lands at the carrier universe -- item 1 of the SIZE
 NOTE, read forwards rather than as an obstruction.  Measured, [About]
 under [Set Printing Universes]:

 CongIdx@{u u0 u1 u2 u3 u4} :
 ∀ {R : RingObject@{u u0 u1}},
 obj[RMod@{u2 u3 u u1 u0} R] → obj[RMod@{u2 u3 u u1 u0} R] → Type@{u4}
 ( * … Set < u2 / Set < u4 / u0 < u2 / u0 < u3 / u <= u2 / u0 <= u4 /
 u1 <= u * )

 [u0] is the ring's carrier universe and [RMod]'s hom universe; the ONLY
 bound on the index [u4] is [u0 <= u4], so [u4 := u0] is expressible and
 the theorem accepts the family.  Contrast [tensor_esols_direct], measured
 in the same run: its index gives [ElementSolutionSet@{u12 u0 u16 u12}]
 with [u0 < u12] -- strictly above.  That single inequality is the whole
 wall and the whole repair.  The wall is not LIFTED; it is ROUTED AROUND.

 THE ONE NEW SIDE CONDITION, stated here and not smoothed over:
 [Set < carrier].  [Set+1] is the sort of [Prop], and identifying the
 index universe with the ring's carrier universe therefore forces the
 carrier strictly above [Set].  The conditional [tensor_via_AFT_of_esols]
 below carries [Set < u0] and [Set < u11]; it does NOT carry [Set < u2],
 the ring's carrier slot, and the unconditional form does.  In practice
 it costs nothing -- Lib.v's [Unset Universe Minimization ToSet] keeps
 carrier universes off [Set] -- but it is a real side condition, and it is
 pinned as a probe in Test/ProbeModTensorAFT449.v beside the positive
 control of its [Section SetPin].

 [obj[RMod R]], NOT [RModObject R], in the section context: the quotient
 must land at the SAME [RMod] universe instance as the ambient modules or
 the two elaborations of [QMod] in [esol_obj] and [esol_elem] disagree. 

 --------
 第2节标题部分的墙体修复，以及它为什么有效。

 Mac Lane的指标是对[RMod R]对象的σ求和，这些对象严格位于其承载集合之上；定理需要在承载类型的宇宙上求指标（Structure/Complete.v的SIZE NOTE，第2(b)项，是权威来源，并未重新陈述）。这里构建的是为了同一任务的不同指标：[MTerm V V']项模块上取值于[Prop]的同余类。

 [IsCongruence]的每个字段都是[Prop]，因此该记录是[Prop]，并且其上的σ求和落在承载类型宇宙上——SIZE NOTE的第1项，应正向理解而非作为障碍。测量后，[About]在[Set Printing Universes]下:CongIdx@{u u0 u1 u2 u3 u4} ：
 对于所有 {R : RingObject@{u u0 u1}},
 obj [RMod@{u2 u3 u u1 u0} R] → obj [RMod@{u2 u3 u u1 u0} R] → Type@{u4}
 ( * … Set < u2 / Set < u4 / u0 < u2 / u0 < u3 / u <= u2 / u0 <= u4 /
 u1 <= u * )

 [u0] 是环的承载宇宙，[RMod] 是它的同态宇宙；索引 [u4] 的唯一
 限制是 [u0 <= u4]，因此 [u4 := u0] 是可表达的，定理接受该族。对比 [tensor_esols_direct]，在相同运行中测量：它的索引得到 [ElementSolutionSet@{u12 u0 u16 u12}] 与 [u0 < u12] ——严格更高。这个单一的不等式构成了整个
 障碍和整个修复。这个障碍没有被提升；它是绕行的。唯一的新附加条件，在此声明而未被掩饰：
 [Set < carrier]。[Set+1] 是 [Prop] 的一种，并且将指标宇宙与环的载体宇宙对应起来因此迫使载体严格高于 [Set]。下面的条件 [tensor_via_AFT_of_esols] 承载 [Set < u0] 和 [Set < u11]；它不承载 [Set < u2]，即环的载体插槽，而无条件形式则承载。在实践中，它不产生任何成本——Lib.v 的 [Unset Universe Minimization ToSet] 保持载体宇宙远离 [Set]——但它是真实的附加条件，并且作为探针固定在 Test/ProbeModTensorAFT449.v 中，位于其 [Section SetPin] 的阳性控制旁边。在章节上下文中使用 [obj[RMod R] ]，而不是 [RModObject R] ：商必须落在与环境模块相同的 [RMod] 宇宙实例中，否则 [esol_obj] 和 [esol_elem] 中对 [QMod] 的两次具体化将会不一致。
*)

Section CongruenceIndex.

Context {R : RingObject}.
Context (V V' : obj[RMod R]).

(*
 A [Prop]-valued congruence on the term module.  [cg_gen] says the
 congruence contains the term model's own relation, so a quotient by it
 is a quotient OF the term model; the remaining four clauses say the
 module operations descend. 

 --------
 [Prop]-值同余在项模上。[cg_gen] 表示同余包含项模型自身的关系，因此通过它的商是项模型的商；其余四条说明模运算可以降到商上。
*)
Record IsCongruence (Rq : MTerm V V' → MTerm V V' → Prop) : Prop := {
  cg_refl  : ∀ s, Rq s s;
  cg_sym   : ∀ s t, Rq s t → Rq t s;
  cg_trans : ∀ s t u, Rq s t → Rq t u → Rq s u;
  cg_gen   : ∀ s t, mt_eq s t → Rq s t;
  cg_plus  : ∀ s s' t t', Rq s s' → Rq t t' →
               Rq (mt_plus s t) (mt_plus s' t');
  cg_neg   : ∀ s s', Rq s s' → Rq (mt_neg s) (mt_neg s');
  cg_smul  : ∀ (r : carrier (rig_setoid (ring_rig R))) s s',
               Rq s s' → Rq (mt_smul r s) (mt_smul r s')
}.

Definition CongIdx : Type :=
  { Rq : MTerm V V' → MTerm V V' → Prop & IsCongruence Rq }.

End CongruenceIndex.

Arguments IsCongruence {R} V V' Rq.
Arguments CongIdx {R} V V'.

Section QuotientModule.

Context {R : RingObject}.
Context (V V' : obj[RMod R]).

Lemma QMod_smul_respects (Rq : MTerm V V' → MTerm V V' → Prop)
  (HRq : IsCongruence V V' Rq) :
  Proper (equiv ==> Rq ==> Rq) (@mt_smul R V V').
Proof.
  intros r r' Hr s s' Hs.
  refine (cg_trans _ _ Rq HRq _ (@mt_smul R V V' r s') _ _ _).
  - exact (cg_smul _ _ Rq HRq r _ _ Hs).
  - exact (cg_gen _ _ Rq HRq _ _ (mte_smul Hr (mt_refl s'))).
Qed.

(*
 THE QUOTIENT SETOID IS NAMED, and that is load-bearing.  Written inline,
 [PropEquiv_of_relation]'s setoid argument is found by resolution, which
 picks the AMBIENT [mt_Setoid] rather than the quotient's, and both
 implications are then refused (“The term ”h“ has type ”Rq f f0“ while it
 is expected to have type ”f ≈ f0“”).  Instance/Mod/Tensor.v gives
 [mt_Setoid] by name for the same reason. 

 --------
 商集等价类被命名了，这是关键的。内联书写时，[PropEquiv_of_relation] 的等价类参数是通过解析找到的，它选择了周围的 [mt_Setoid] 而不是商的，而两种推论随后都被拒绝（“项 'h' 的类型是 'Rq f f0'，而期望的类型是 'f ≈ f0'”）。Instance/Mod/Tensor.v 也是出于同样的原因通过名称给出 [mt_Setoid]。
*)
Definition QMod_Setoid (Rq : MTerm V V' → MTerm V V' → Prop)
  (HRq : IsCongruence V V' Rq) : Setoid (MTerm V V') :=
  {| equiv := Rq
   ; setoid_equiv :=
       {| Equivalence_Reflexive  := cg_refl  _ _ Rq HRq
        ; Equivalence_Symmetric  := cg_sym   _ _ Rq HRq
        ; Equivalence_Transitive := cg_trans _ _ Rq HRq |} |}.

(*
 The quotient module: the term module's carrier and operations with the
 congruence as its `≈`.  Every law is the term model's own law passed
 through [cg_gen], and [cmon_prop] is the congruence being its own [Prop]
 mirror -- the quotient's `≈` IS a [Prop] relation by construction. 

 --------
 商模：项模的载体及运算与同余作为它的 `≈`。每条定律都是项模型自身的定律通过 [cg_gen]，而 [cmon_prop] 是同余作为其自身 [Prop] 的镜像——商的 `≈` 从构造上是 [Prop] 关系。
*)
Definition QMod (Rq : MTerm V V' → MTerm V V' → Prop)
  (HRq : IsCongruence V V' Rq) : obj[RMod R] :=
  {| rm_ab := {|
       ab_cmon := {|
         cmon_setoid :=
           {| carrier := MTerm V V'
            ; is_setoid := QMod_Setoid Rq HRq |};
         cmon_zero := @mt_zero R V V';
         cmon_plus := @mt_plus R V V';
         cmon_plus_respects := fun _ _ Hs _ _ Ht => cg_plus _ _ Rq HRq _ _ _ _ Hs Ht;
         cmon_plus_assoc := fun s t u => cg_gen _ _ Rq HRq _ _ (mte_assoc s t u);
         cmon_plus_comm  := fun s t => cg_gen _ _ Rq HRq _ _ (mte_comm s t);
         cmon_plus_zero_l := fun s => cg_gen _ _ Rq HRq _ _ (mte_zero_l s);
         cmon_prop := @PropEquiv_of_relation _ (QMod_Setoid Rq HRq) Rq
                        (fun _ _ h => h) (fun _ _ h => h)
       |};
       ab_neg := @mt_neg R V V';
       ab_neg_respects := fun _ _ Hs => cg_neg _ _ Rq HRq _ _ Hs;
       ab_neg_left := fun s => cg_gen _ _ Rq HRq _ _ (mte_neg_l s)
     |};
     rm_smul := @mt_smul R V V';
     rm_smul_respects := QMod_smul_respects Rq HRq;
     rm_smul_distr_l := fun r s t => cg_gen _ _ Rq HRq _ _ (mte_smul_distr_l r s t);
     rm_smul_distr_r := fun r s t => cg_gen _ _ Rq HRq _ _ (mte_smul_distr_r r s t);
     rm_smul_assoc := fun r s t => cg_gen _ _ Rq HRq _ _ (mte_smul_assoc r s t);
     rm_smul_one := fun s => cg_gen _ _ Rq HRq _ _ (mte_smul_one s)
  |}.

(* The canonical bilinear map into the quotient is the generator former. / 到商的典型双线性映射是生成元形式。 *)
Definition QMod_gen (Rq : MTerm V V' → MTerm V V' → Prop)
  (HRq : IsCongruence V V' Rq) : RBilinear V V' (QMod Rq HRq) :=
  @Build_RBilinear R V V' (QMod Rq HRq) (@mt_gen R V V')
    (fun _ _ Hv _ _ Hw => cg_gen _ _ Rq HRq _ _ (mte_gen Hv Hw))
    (fun v v' w => cg_gen _ _ Rq HRq _ _ (mte_add_l v v' w))
    (fun v w w' => cg_gen _ _ Rq HRq _ _ (mte_add_r v w w'))
    (fun r v w => cg_gen _ _ Rq HRq _ _ (mte_sym (mte_act_l r v w)))
    (fun r v w => cg_gen _ _ Rq HRq _ _ (mte_sym (mte_act_r r v w))).

(*
 THE ELEMENTARY TENSORS SPAN EVERY QUOTIENT.  This is Instance/Mod/
 Spanning.v's [tensor_gen_spanning] verbatim, five cases with
 [mt_neg] discharged by [smod_neg]: the carrier is the same [MTerm] and
 [rbl_map (QMod_gen …)] is [mt_gen], so nothing about the congruence
 enters the induction.  Section 10 consumes it. 

 --------
 基本张量跨越每一个商。本句是 Instance/Mod/Spanning.v 中 [tensor_gen_spanning] 的逐字内容，五种情况由 [smod_neg] 释放 [mt_neg]：载体相同为 [MTerm]，并且 [rbl_map (QMod_gen …)] 是 [mt_gen]，因此没有关于同余的信息进入归纳。第 10 节消耗它。
*)
Theorem QMod_gen_spanning (Rq : MTerm V V' → MTerm V V' → Prop)
  (HRq : IsCongruence V V' Rq) : RBilinearSpanning (QMod_gen Rq HRq).
Proof.
  intro t; induction t.
  - refine (mgen_base (rbl_image (QMod_gen Rq HRq)) _ _).
    exists c, c0; reflexivity.
  - exact (mgen_zero (rbl_image (QMod_gen Rq HRq))).
  - exact (mgen_plus (rbl_image (QMod_gen Rq HRq)) _ _ IHt1 IHt2).
  - exact (smod_neg (SubGenMod (rbl_image (QMod_gen Rq HRq))) _ IHt).
  - exact (mgen_smul (rbl_image (QMod_gen Rq HRq)) _ _ IHt).
Defined.

End QuotientModule.

Arguments QMod {R V V'} Rq HRq.
Arguments QMod_gen {R V V'} Rq HRq.
Arguments QMod_gen_spanning {R V V'} Rq HRq.

(*
 THE KERNEL CONGRUENCE OF A BILINEAR MAP, AND THE COVERING.

 There is NO [PropEquiv] hypothesis anywhere below, and that single fact
 is what turns the conditional of section 4 into a theorem: since the PR
 “algebraic carriers are sets” (2026-09-17) [cmon_prop] is a FIELD of
 [CMonObject] with [#[export] Existing Instance], so every [RModObject]
 carries the [Prop] mirror of its own `≈`. 

 --------
 双线性映射的核同余与覆盖。

 以下任何地方都没有 [PropEquiv] 假设，而这一单一事实使第 4 节的条件成为定理：由于 PR“代数承载体是集合”（2026-09-17）[cmon_prop] 是 [CMonObject] 的一个体，且 [#[export] 存在实例，因此每个 [RModObject] 都承载它自身 `≈` 的 [Prop] 镜像。
*)

Section KernelCongruence.

Context {R : RingObject}.
Context (V V' : obj[RMod R]).
Context {W : obj[RMod R]}.
Context (beta : RBilinear V V' W).

Definition ker_cong : MTerm V V' → MTerm V V' → Prop :=
  fun x y => @pequiv _ _ (cmon_prop W)
               (tensor_med_fun beta x) (tensor_med_fun beta y).

Lemma ker_cong_is_cong : IsCongruence V V' ker_cong.
Proof.
  unfold ker_cong.
  constructor.
  - intro s; apply (@pequiv_from _ _ (cmon_prop W)); reflexivity.
  - intros s t H; apply (@pequiv_from _ _ (cmon_prop W)); symmetry;
      exact (@pequiv_to _ _ (cmon_prop W) _ _ H).
  - intros s t u H1 H2; apply (@pequiv_from _ _ (cmon_prop W)).
    transitivity (tensor_med_fun beta t);
      [ exact (@pequiv_to _ _ (cmon_prop W) _ _ H1)
      | exact (@pequiv_to _ _ (cmon_prop W) _ _ H2) ].
  - intros s t H; apply (@pequiv_from _ _ (cmon_prop W));
      exact (tensor_med_respects beta s t H).
  - intros s s' t t' H1 H2; apply (@pequiv_from _ _ (cmon_prop W)); simpl.
    exact (cmon_plus_respects W _ _ (@pequiv_to _ _ (cmon_prop W) _ _ H1)
                                _ _ (@pequiv_to _ _ (cmon_prop W) _ _ H2)).
  - intros s s' H; apply (@pequiv_from _ _ (cmon_prop W)); simpl.
    exact (ab_neg_respects W _ _ (@pequiv_to _ _ (cmon_prop W) _ _ H)).
  - intros r s s' H; apply (@pequiv_from _ _ (cmon_prop W)); simpl.
    exact (rm_smul_respects W _ _ (reflexivity r) _ _
             (@pequiv_to _ _ (cmon_prop W) _ _ H)).
Qed.

Definition ker_idx : CongIdx V V' := existT _ ker_cong ker_cong_is_cong.

(* The mediator out of the quotient. Respectfulness IS [pequiv_to]; the other four obligations are [reflexivity], the mediator being the term model's own fold. / 调解者不在商中。尊重是 [pequiv_to]；其他四项义务是 [reflexivity]，调解者是术语模型自身的折叠。 *)
Program Definition ker_med : QMod ker_cong ker_cong_is_cong ~{RMod R}~> W := {|
  rm_hom := {| cmon_map := {| morphism := tensor_med_fun beta |} |}
|}.
Solve All Obligations with
  (first [ (intros s t H; exact (@pequiv_to _ _ (cmon_prop W) _ _ H))
         | (intros; simpl; reflexivity) ]).

(* The covering equation, on the nose. / 遮盖方程，恰到好处。 *)
Example ker_factors (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  cmon_map (rm_hom ker_med)
    (rbl_map (QMod_gen ker_cong ker_cong_is_cong) v w)
  = rbl_map beta v w
  := eq_refl.

(* THE MEDIATOR IS INJECTIVE BY CONSTRUCTION: the congruence IS the kernel pair of the evaluation, so injectivity is [pequiv_from] and nothing else. / 仲裁者通过构造是单射的：同余是评估的核对，因此单射性是[pequiv_from]，仅此而已。 *)
Lemma ker_med_injective : RModInjective ker_med.
Proof.
  intros x y H; exact (@pequiv_from _ _ (cmon_prop W) _ _ H).
Qed.

(* AND SURJECTIVE WHEN [beta] SPANS: the generation derivation is READ as a term of the term module, one case per constructor of [MGen]. / 当 [beta] 跨越时是满射的：生成导出被读取为项模的一个项，对于 [MGen] 的每个构造函数都是一个情况。 *)
Definition mgen_preimage (a : carrier (cmon_setoid W))
  (D : MGen (rbl_image beta) a)
  : { t : MTerm V V' & tensor_med_fun beta t ≈ a }.
Proof.
  induction D as [a Ha|a b Hab D IH| |a b D1 IH1 D2 IH2|r a D IH].
  - exact (existT _ (@mt_gen R V V' (`1 Ha) (`1 (`2 Ha))) (`2 (`2 Ha))).
  - exact (existT _ (`1 IH) (transitivity (`2 IH) Hab)).
  - refine (existT _ (@mt_zero R V V') _); simpl; reflexivity.
  - exact (existT _ (@mt_plus R V V' (`1 IH1) (`1 IH2))
             (cmon_plus_respects W _ _ (`2 IH1) _ _ (`2 IH2))).
  - exact (existT _ (@mt_smul R V V' r (`1 IH))
             (rm_smul_respects W _ _ (reflexivity r) _ _ (`2 IH))).
Defined.

Lemma ker_med_surjective (Hsp : RBilinearSpanning beta) :
  RModSurjective ker_med.
Proof.
  intro b; exact (mgen_preimage b (Hsp b)).
Defined.

(*
 ...and therefore an ISOMORPHISM of [RMod R], through
 Instance/Mod/Spanning.v's [rmod_split].  This is the content of Mac
 Lane's Lemma 2 at [RMod R]: every spanning codomain is (isomorphic to) a
 quotient of ONE fixed object, the term module. 

 --------
 ...因此是  [RMod R] 的一个同构，通过 Instance/Mod/Spanning.v 的  [rmod_split] 。这是 Mac Lane 的引理 2 在  [RMod R] 的内容：每个生成的陪域都是（同构于）一个固定对象的商，这个固定对象是项模。
*)
Definition ker_iso (Hsp : RBilinearSpanning beta) :
  QMod ker_cong ker_cong_is_cong ≅ W.
Proof.
  unshelve refine {| to := ker_med
                   ; from := rmod_split ker_med ker_med_injective
                               (ker_med_surjective Hsp) |}.
  - exact (rmod_split_commutes ker_med ker_med_injective
             (ker_med_surjective Hsp)).
  - intro t; simpl.
    apply ker_med_injective.
    exact (`2 (ker_med_surjective Hsp (tensor_med_fun beta t))).
Defined.

End KernelCongruence.

Arguments ker_cong {R V V' W} beta.
Arguments ker_cong_is_cong {R V V' W} beta.
Arguments ker_idx {R V V' W} beta.
Arguments ker_med {R V V' W} beta.
Arguments ker_iso {R V V' W} beta Hsp.

(*
 THE OBJECT AND ELEMENT PARTS ARE NAMED, and that too is load-bearing.
 Written inline, [esol_obj] and [esol_elem] each mint their OWN universe
 instance of [QMod] and the record is refused, “RBilinear … (QMod@{a…} …)”
 against “carrier (fobj[?K] (QMod@{b…} …))”.  Naming them forces one. 

 --------
 对象和元素部件都有命名，而且它们也是承重的。
 以行内方式书写时，[esol_obj] 和 [esol_elem] 各自铸造它们自己对 [QMod] 的宇宙实例，并且记录被拒绝，“RBilinear … (QMod@{a…} …)” 针对 “carrier (fobj [?K] (QMod@{b…} …))”。命名它们会强制执行某种操作。
*)
Definition QModOf {R : RingObject} {V V' : obj[RMod R]}
  (i : CongIdx V V') : obj[RMod R] := QMod (`1 i) (`2 i).

Definition QModGenOf {R : RingObject} {V V' : obj[RMod R]}
  (i : CongIdx V V') : RBilinear V V' (QModOf i) := QMod_gen (`1 i) (`2 i).

(*
 THE SOLUTION SET, AT THE CARRIER UNIVERSE.  The [{| … |}] form leaves the
 functor [?K] open and is refused even with the two parts named; the
 explicit [@Build_ElementSolutionSet (RMod R) (Bilin V V')] is required. 

 --------
 解集，在载体宇宙中。[{| … |}] 形式保留了函子 [?K] 的开放状态，即使两个部分都已命名也会被拒绝；需要显式的 [@Build_ElementSolutionSet (RMod R) (Bilin V V')]。
*)
Definition tensor_esols_prop {R : RingObject} (V V' : obj[RMod R]) :
  ElementSolutionSet (Bilin V V').
Proof.
  unshelve refine (@Build_ElementSolutionSet (RMod R) (Bilin V V')
                     (CongIdx V V') QModOf QModGenOf _).
  intros c beta.
  exists (ker_idx beta), (ker_med beta).
  intros v w; simpl; reflexivity.
Defined.

(* * ** 4. Mac Lane's Construction 1: the tensor product from the AFT / * ** 4. Mac Lane 的构造1：来自 AFT 的张量积 *)

(*
 Stated at TOP LEVEL, outside any [Section], for the reason
 Adjunction/Representability/Sets.v gives: the comma-initial step
 pins the hom AND proof universes of both categories to [Set], and inside
 a section that has already elaborated a category with those levels apart
 the ascription is refused.  The pin is measured in the header.

 ALL THREE of Mac Lane's premises are now discharged here outright --
 [RMod_Complete] (“K-Mod is small-complete”), [Bilin_PreservesImageLimit]
 (“Bilin(A,B;-) is continuous”) and [tensor_esols_prop] of section 3A (the
 solution set).  CORRECTION, PR “algebraic carriers are sets”
 (2026-09-17): until this commit the third stayed a hypothesis and this
 comment said so.  [tensor_esols_direct] -- Mac Lane's OWN family, indexed
 by a sigma over the objects of [RMod R] -- is still refused by the
 theorem, and that refusal is NEGATIVE 1 of the probe and is unchanged;
 what changed is that a DIFFERENT solution set for the same functor, at
 the carrier universe, is now in tree.  Section 10 closes the circle by
 proving Mac Lane's own family small up to isomorphism and feeding the
 resizing.

 THE CONDITIONAL IS NOT LOST.  [tensor_via_AFT_of_esols] is the old
 [tensor_via_AFT], statement for statement; the unconditional
 [tensor_via_AFT] is that constant at [tensor_esols_prop]. 

 --------
 在顶层声明，在任何 [Section] 之外，原因是 Adjunction/Representability/Sets.v 给出：以逗号开头的步骤将两个范畴的 Hom 和证明宇宙钉定在 [Set] 上，并且在已经展开了具有这些层次的范畴的章节内，赋值被拒绝。这个钉定在头部进行测量。马克·莱恩的三个前提现在在这里完全解除——
 [RMod_Complete]（“K-模是小完全”）、[Bilin_PreservesImageLimit]（“Bilin(A,B;-) 是连续的”）以及第 3A 节的 [tensor_esols_prop]（解集）。更正，PR “代数承载体是集合”（2026-09-17）：在此提交之前，第三个仍然是一个假设，并且这个评论如此说明。[tensor_esols_direct]——马克·莱恩自己的族，由 [RMod R] 对象上的一个 σ 索引——仍然被定理拒绝，并且这种拒绝在探针中是负一且未改变；改变的是，现在在承载体宇宙中，对于相同函子有一个不同的解集在树中。第 10 节通过证明马克·莱恩自己的族在同构下是小的并进行重新调整，从而闭合循环。条件句并未丢失。[tensor_via_AFT_of_esols] 是旧的 [tensor_via_AFT]，逐条语句；无条件的 [tensor_via_AFT] 是那个在 [tensor_esols_prop] 的常量。
*)

Definition tensor_via_AFT_of_esols {R : RingObject} (V V' : RModObject R)
  (E : ElementSolutionSet (Bilin V V')) : Representable (Bilin V V') :=
  representability_theorem (Bilin V V') (RMod_Complete R)
    (Bilin_PreservesImageLimit V V') E.

(* THE HEADLINE, at an ARBITRARY ring, with no hypothesis and no [Set]. / 标题，在任意的铃声下，没有假设，也没有 [Set]。 *)
Definition tensor_via_AFT {R : RingObject} (V V' : obj[RMod R]) :
  Representable (Bilin V V') :=
  tensor_via_AFT_of_esols V V' (tensor_esols_prop V V').

(*
 THE CIRCULAR DISCHARGE, KEPT FOR COMPARISON; A REMOVAL CANDIDATE FOR
 JOHN.  A solution set at the universe the theorem demands, obtained from
 the tensor product the theorem is meant to construct.  CIRCULAR, and
 named so that the circularity is visible at every use site -- exactly
 Instance/Grp/FreeAFT.v's [Grp_Forget_solution_set_from_adjunction], which
 existed for the same reason and is disclosed the same way.

 CORRECTION, PR “algebraic carriers are sets” (2026-09-17): its stated
 role was “to show the conditional above is not vacuous”, and that role is
 GONE -- [tensor_esols_prop] discharges the hypothesis non-circularly.  It
 is kept, not deleted, because NEGATIVE 6 of
 Test/ProbeModTensorAFT449.v and [tensor_via_AFT_from_tensor] are
 statements ABOUT it, and because removing working code is John's call and
 not this commit's.  What it now is, is the comparison: the two solution
 sets are different terms for the same functor, and the probe pins that. 

 --------
 循环放电，保留用于比较；约翰的移除候选。一个在宇宙中设置的解集，是定理所要求的，从定理旨在构造的张量积中获得的。循环的，并以此命名以便在每个使用点都能看到循环性——正是 Instance/Grp/FreeAFT.v 的 [Grp_Forget_solution_set_from_adjunction]，其存在原因相同，并以相同方式披露。更正，PR “代数载体是集合”（2026-09-17）：其声明的作用是“显示上面的条件不是空的”，而这一作用已经消失——[tensor_esols_prop] 非循环地解除假设。它被保留，而不是删除，因为 Test/ProbeModTensorAFT449.v 的 NEGATIVE 6 和 [tensor_via_AFT_from_tensor] 是关于它的陈述，并且删除工作代码是 John 的决定，而不是本次提交的。它现在的作用是比较：两个解集是同一个函子不同的项，并且探针固定了这一点。
*)
Definition tensor_esols_from_tensor {R : RingObject} (V V' : RModObject R) :
  ElementSolutionSet (Bilin V V').
Proof.
  unshelve refine (@Build_ElementSolutionSet (RMod R) (Bilin V V')
                     unit (fun _ => TensorMod V V')
                     (fun _ => @tensor_gen R V V') _).
  intros c β.
  refine (existT _ tt _).
  refine (existT _ (tensor_factor β) _).
  intros v w; exact (tensor_factor_commutes β v w).
Defined.

Definition tensor_via_AFT_from_tensor {R : RingObject} (V V' : RModObject R) :
  Representable (Bilin V V') :=
  tensor_via_AFT_of_esols V V' (tensor_esols_from_tensor V V').

(* * ** 5. The comparison with [TensorMod] / * ** 5. 与 [TensorMod] 的比较 *)

Definition tensor_repr_of_UE {R : RingObject} (V V' : RModObject R) :
  Representable (Bilin V V') :=
  Representable_of_UniversalElement (tensor_UniversalElement V V').

Example tensor_repr_of_UE_obj {R : RingObject} (V V' : RModObject R) :
  @repr_obj (RMod R) (Bilin V V') (tensor_repr_of_UE V V') = TensorMod V V'
  := eq_refl.

(*
 The object comparison is `≅`, NOT [eq_refl]: the AFT builds its object
 as a limit inside the comma category, [TensorMod] is a quotient of
 formal terms.  The statement holds for EVERY solution set, so nothing
 here depends on which one is supplied -- which is why the conditional
 form is kept beside the unconditional one rather than replaced by it. 

 --------
 对象比较是 `≅`，而不是 [eq_refl]：AFT 将其对象构建为逗号范畴内的极限，[TensorMod] 是形式项的商。该陈述适用于每一个解集，因此这里没有依赖于提供哪一个解集——这就是为什么条件形式会保留在无条件形式旁边，而不是被其替代。
*)
Definition tensor_AFT_iso_of_esols {R : RingObject} (V V' : RModObject R)
  (E : ElementSolutionSet (Bilin V V')) :
  @repr_obj (RMod R) (Bilin V V') (tensor_via_AFT_of_esols V V' E)
    ≅ TensorMod V V' :=
  repr_unique_iso (tensor_repr_of_UE V V')
    (tensor_via_AFT_of_esols V V' E).

Definition tensor_AFT_iso {R : RingObject} (V V' : obj[RMod R]) :
  @repr_obj (RMod R) (Bilin V V') (tensor_via_AFT V V')
    ≅ TensorMod V V' :=
  tensor_AFT_iso_of_esols V V' (tensor_esols_prop V V').

Definition tensor_AFT_iso_universal_of_esols {R : RingObject}
  (V V' : RModObject R) (E : ElementSolutionSet (Bilin V V')) :=
  repr_unique_iso_universal (tensor_repr_of_UE V V')
    (tensor_via_AFT_of_esols V V' E).

Definition tensor_AFT_iso_universal {R : RingObject} (V V' : obj[RMod R]) :=
  tensor_AFT_iso_universal_of_esols V V' (tensor_esols_prop V V').

Definition tensor_AFT_ue_of_esols {R : RingObject} (V V' : RModObject R)
  (E : ElementSolutionSet (Bilin V V')) : UniversalElement (Bilin V V') :=
  UniversalElement_of_Representable (tensor_via_AFT_of_esols V V' E).

Definition tensor_AFT_ue {R : RingObject} (V V' : obj[RMod R]) :
  UniversalElement (Bilin V V') :=
  tensor_AFT_ue_of_esols V V' (tensor_esols_prop V V').

(*
 The issue's verification name.  [module_tensor_universal V V'] is the
 universal element the adjoint functor theorem produces -- an alias of
 [tensor_AFT_ue], so that the name the issue asks to audit resolves to
 the delivered constant.

 CORRECTION, PR “algebraic carriers are sets” (2026-09-17): this comment
 read “it inherits the conditional shape and the [Set] pin of
 [tensor_via_AFT]”.  Both clauses are now false of the name as it stands.
 The conditional shape is [module_tensor_universal_of_esols], which is the
 old constant statement for statement; the [Set] pin went with the
 annotation of [DiscreteCat_Functor] in the same PR.  What the
 unconditional form DOES carry is the new [Set < carrier] side condition
 of section 3A. 

 --------
 该问题的验证名称。[module_tensor_universal V V'] 是伴随函子定理产生的通用元素——[tensor_AFT_ue] 的别名，因此该问题要求审核的名称解析到交付的常量。

 更正，PR “代数载体是集合”（2026-09-17）：这条评论写的是“它继承了条件形状和 [Set] 的 [tensor_via_AFT] 引脚”。就目前而言，这两条都是假的。条件形状是 [module_tensor_universal_of_esols]，这是旧常量按语句对应的声明；[Set] 引脚随同 [DiscreteCat_Functor] 在同一 PR 中的注释。无条件形式确实携带的是第 3A 节的新 [Set < carrier] 侧条件。
*)
Definition module_tensor_universal_of_esols {R : RingObject}
  (V V' : RModObject R) (E : ElementSolutionSet (Bilin V V')) :
  UniversalElement (Bilin V V') :=
  tensor_AFT_ue_of_esols V V' E.

Definition module_tensor_universal {R : RingObject} (V V' : obj[RMod R]) :
  UniversalElement (Bilin V V') :=
  tensor_AFT_ue V V'.

Definition tensor_AFT_elem_iso {R : RingObject} (V V' : RModObject R)
  (E : ElementSolutionSet (Bilin V V')) :
  @ue_obj (RMod R) (Bilin V V') (tensor_AFT_ue_of_esols V V' E) ≅ TensorMod V V' :=
  universal_element_iso
    (AUniversalElement_of_UniversalElement (tensor_AFT_ue_of_esols V V' E))
    (tensor_universal_element V V').

Theorem tensor_AFT_elem_commutes {R : RingObject} (V V' : RModObject R)
  (E : ElementSolutionSet (Bilin V V')) :
  fmap[Bilin V V'] (to (tensor_AFT_elem_iso V V' E))
    (@ue_elem (RMod R) (Bilin V V') (tensor_AFT_ue_of_esols V V' E))
    ≈ @tensor_gen R V V'.
Proof.
  exact (ue_med_commutes
           (AUniversalElement_of_UniversalElement (tensor_AFT_ue_of_esols V V' E))
           (tensor_universal_element V V')).
Qed.

Definition tensor_AFT_elem_unique {R : RingObject} (V V' : RModObject R)
  (E : ElementSolutionSet (Bilin V V')) :=
  universal_element_unique
    (AUniversalElement_of_UniversalElement (tensor_AFT_ue_of_esols V V' E))
    (tensor_universal_element V V').

(*
 The two comparisons agree, and the AFT's universal bilinear map carried
 along the REPRESENTATION-level isomorphism is [tensor_gen] itself.  The
 argument is naturality of the representation followed by
 [repr_induced_compatible] at the identity; nothing about the solution set
 enters. 

 --------
 这两个比较是一致的，并且 AFT 的通用双线性映射沿着表示层同构携带的正是 [tensor_gen] 本身。该论点是表示的自然性，随后在恒等映射处使用 [repr_induced_compatible]；解集的任何内容都没有进入。
*)
Theorem tensor_AFT_iso_carries_elem {R : RingObject} (V V' : RModObject R)
  (E : ElementSolutionSet (Bilin V V')) :
  fmap[Bilin V V'] (to (tensor_AFT_iso_of_esols V V' E))
    (@ue_elem (RMod R) (Bilin V V') (tensor_AFT_ue_of_esols V V' E))
    ≈ @tensor_gen R V V'.
Proof.
  pose proof (repr_compatible_at
    (repr_induced_compatible (tensor_repr_of_UE V V')
       (tensor_via_AFT_of_esols V V' E) nat_id) (TensorMod V V') id) as HC.
  pose proof (@naturality _ _ _ _
      (to (@represented _ _ (tensor_via_AFT_of_esols V V' E)))
      (@repr_obj _ _ (tensor_via_AFT_of_esols V V' E)) (TensorMod V V')
      (to (tensor_AFT_iso_of_esols V V' E)) (@id (RMod R) _)) as HN.
  transitivity (transform[to (@represented _ _ (tensor_via_AFT_of_esols V V' E))]
                  (TensorMod V V')
                  (@compose (RMod R) _ _ _ (to (tensor_AFT_iso_of_esols V V' E))
                     (@id (RMod R) _))).
  - exact HN.
  - transitivity (transform[to (@represented _ _ (tensor_via_AFT_of_esols V V' E))]
                    (TensorMod V V')
                    (@compose (RMod R) _ _ _ (@id (RMod R) _)
                       (to (tensor_AFT_iso_of_esols V V' E)))).
    + apply proper_morphism.
      rewrite id_left, id_right; reflexivity.
    + rewrite HC.
      exact (@fmap_id _ _ (Bilin V V') (TensorMod V V') (@tensor_gen R V V')).
Qed.

(*
 STATEMENT CHANGE, recorded (the PR “algebraic carriers are sets”,
 2026-09-17).  The right-hand side of this equation read
 [tensor_AFT_iso V V' E] before that PR.  It is the ONE forced rename:
 [tensor_AFT_iso] no longer takes a solution set, and the [E]-taking
 isomorphism is [tensor_AFT_iso_of_esols], which is the old
 [tensor_AFT_iso] verbatim.  Nothing else about the theorem moved -- same
 name, same binders, same proof -- and the same note applies to
 [bal_AFT_isos_agree].  An earlier report said the nine
 [E]-taking constants kept “their exact statements”; these two did not,
 and the correction is recorded here rather than in that report. 

 --------
 声明更改，已记录（PR “代数载体是集合”，2026-09-17）。在该PR之前，这个等式的右边写作 [tensor_AFT_iso V V' E]。它是唯一被强制重命名的：[tensor_AFT_iso] 不再取解集，而取 [E] 的同构是 [tensor_AFT_iso_of_esols]，它就是旧的 [tensor_AFT_iso] 原样。定理的其他部分没有移动——名字相同，绑定器相同，证明相同——相同的说明也适用于 [bal_AFT_isos_agree]。早期报告说九个 [E] 取常量保持“它们的确切陈述”；而这两个没有，这里的更正记录在此，而不是在该报告中。
*)
Theorem tensor_AFT_isos_agree {R : RingObject} (V V' : RModObject R)
  (E : ElementSolutionSet (Bilin V V')) :
  tensor_AFT_elem_iso V V' E ≈ tensor_AFT_iso_of_esols V V' E.
Proof.
  exact (universal_element_iso_unique
           (AUniversalElement_of_UniversalElement (tensor_AFT_ue_of_esols V V' E))
           (tensor_universal_element V V')
           (tensor_AFT_iso_of_esols V V' E)
           (tensor_AFT_iso_carries_elem V V' E)).
Qed.

(* * ** 6. Exercise 3: the balanced-biadditive functor [Ab ⟶ Sets] / * ** 6. 练习 3：平衡双加性函子 [Ab ⟶ Sets] *)

Section BalBiaddFunctor.

Context {X : RingObject}.
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).

Program Definition BalBiadditive_Setoid (A : AbObject) :
  Setoid (BalBiadditive N M A) := {|
  equiv := fun β γ => ∀ n m, bal_map β n m ≈ bal_map γ n m
|}.
Next Obligation.
  intros A.
  constructor.
  - intros β n m; reflexivity.
  - intros β γ Hβγ n m; symmetry; apply Hβγ.
  - intros β γ δ H1 H2 n m.
    transitivity (bal_map γ n m); [ apply H1 | apply H2 ].
Qed.

Definition BalBiadd_obj (A : AbObject) : SetoidObject := {|
  carrier   := BalBiadditive N M A;
  is_setoid := BalBiadditive_Setoid A
|}.

Program Definition BalBiadd_post {A B : AbObject} (f : A ~{Ab}~> B)
  (β : BalBiadditive N M A) : BalBiadditive N M B := {|
  bal_map := fun n m => cmon_map f (bal_map β n m)
|}.
Next Obligation.
  intros A B f β n n' Hn m m' Hm; simpl.
  exact (proper_morphism (cmon_map f) _ _ (bal_respects β _ _ Hn _ _ Hm)).
Qed.
Next Obligation.
  intros A B f β n n' m; simpl.
  rewrite (bal_add_l β n n' m).
  apply (cmon_map_plus f).
Qed.
Next Obligation.
  intros A B f β n m m'; simpl.
  rewrite (bal_add_r β n m m').
  apply (cmon_map_plus f).
Qed.
Next Obligation.
  intros A B f β x n m; simpl.
  now rewrite (bal_balance β x n m).
Qed.

Program Definition BalBiadd : Ab ⟶ Sets := {|
  fobj := BalBiadd_obj;
  fmap := fun A B f => {| morphism := BalBiadd_post f |}
|}.
Next Obligation.
  intros A B f β γ Hβγ n m; simpl.
  exact (proper_morphism (cmon_map f) _ _ (Hβγ n m)).
Qed.
Next Obligation.
  intros A B f g Hfg β n m; simpl.
  exact (Hfg (bal_map β n m)).
Qed.
Next Obligation. intros A β n m; simpl; reflexivity. Qed.
Next Obligation. intros A B C f g β n m; simpl; reflexivity. Qed.

(*
 The universal element the explicit construction already supplies, in the
 form the comparison below consumes. 

 --------
 通用元素由显式构造已经提供，以比较下面所使用的形式。
*)
Program Definition bal_universal_element :
  AUniversalElement BalBiadd (BalTensor N M) := {|
  aue_elem      := @bal_gen X N M;
  aue_universal := fun A β => {| unique_obj := bal_med β |}
|}.
Next Obligation. intros A β n m; simpl; reflexivity. Qed.
Next Obligation.
  intros A β k Hk.
  symmetry.
  exact (bal_med_unique β k Hk).
Qed.

Definition bal_UniversalElement : UniversalElement BalBiadd :=
  UniversalElement_of_AUniversalElement bal_universal_element.

Example bal_UniversalElement_obj :
  @ue_obj Ab BalBiadd bal_UniversalElement = BalTensor N M := eq_refl.

Example bal_UniversalElement_elem :
  @ue_elem Ab BalBiadd bal_UniversalElement = @bal_gen X N M := eq_refl.

End BalBiaddFunctor.

Arguments BalBiadditive_Setoid {X} N M A.
Arguments BalBiadd_obj {X} N M A.
Arguments BalBiadd_post {X} N M {A B} f β.
Arguments BalBiadd {X} N M.
Arguments bal_universal_element {X} N M.
Arguments bal_UniversalElement {X} N M.

(* * ** 7. Exercise 3: [BalBiadd N M] is continuous / * ** 7. 练习 3：[BalBiadd N M] 是连续的 *)

Section BalContinuity.

Context {X : RingObject}.
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).

Section AtALimitingCone.

Context {J : Category}.
Context {K : J ⟶ Ab}.
Context {L : Cone K}.
Context (HL : IsLimitCone L).

Definition bal_sets_limit : IsLimitCone (FCone Ab_Forget L) :=
  Ab_Forget_creates_continuous J K L HL.

Lemma bal_lim_ext (u v : carrier (cmon_setoid vertex_obj[L]))
  (H : ∀ x : J, cmon_map (cone_leg L x) u ≈ cmon_map (cone_leg L x) v) :
  u ≈ v.
Proof using All. exact (slim_ext bal_sets_limit u v H). Qed.

Section AtACone.

Context (Q : Cone (BalBiadd N M ◯ K)).

Lemma bal_family_compat (q : carrier (vertex_obj[Q]))
  (n : carrier (cmon_setoid (rm_ab N))) (m : carrier (cmon_setoid (rm_ab M)))
  (x y : J) (f : x ~{J}~> y) :
  fmap[Ab_Forget ◯ K] f (bal_map (cone_leg Q x q) n m)
    ≈ bal_map (cone_leg Q y q) n m.
Proof using All.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ Q) x y f q n m).
Qed.

Definition bal_med_elem (q : carrier (vertex_obj[Q]))
  (n : carrier (cmon_setoid (rm_ab N)))
  (m : carrier (cmon_setoid (rm_ab M))) :
  carrier (cmon_setoid vertex_obj[L]) :=
  slim_elem bal_sets_limit (fun x => bal_map (cone_leg Q x q) n m)
    (fun x y f => bal_family_compat q n m x y f).

Lemma bal_med_elem_leg (q : carrier (vertex_obj[Q]))
  (n : carrier (cmon_setoid (rm_ab N)))
  (m : carrier (cmon_setoid (rm_ab M))) (x : J) :
  cmon_map (cone_leg L x) (bal_med_elem q n m)
    ≈ bal_map (cone_leg Q x q) n m.
Proof using All.
  exact (slim_elem_leg bal_sets_limit
           (fun x => bal_map (cone_leg Q x q) n m)
           (fun x y f => bal_family_compat q n m x y f) x).
Qed.

Program Definition BalBiadd_med (q : carrier (vertex_obj[Q])) :
  BalBiadditive N M vertex_obj[L] := {|
  bal_map := bal_med_elem q
|}.
Next Obligation.
  intros q n n' Hn m m' Hm.
  apply bal_lim_ext; intro x.
  rewrite !bal_med_elem_leg.
  exact (bal_respects (cone_leg Q x q) _ _ Hn _ _ Hm).
Qed.
Next Obligation.
  intros q n n' m.
  apply bal_lim_ext; intro x.
  rewrite bal_med_elem_leg.
  rewrite (cmon_map_plus (cone_leg L x)).
  rewrite !bal_med_elem_leg.
  apply bal_add_l.
Qed.
Next Obligation.
  intros q n m m'.
  apply bal_lim_ext; intro x.
  rewrite bal_med_elem_leg.
  rewrite (cmon_map_plus (cone_leg L x)).
  rewrite !bal_med_elem_leg.
  apply bal_add_r.
Qed.
Next Obligation.
  intros q r n m.
  apply bal_lim_ext; intro x.
  rewrite !bal_med_elem_leg.
  apply bal_balance.
Qed.

Program Definition BalBiadd_cone_med :
  vertex_obj[Q] ~{Sets}~> vertex_obj[FCone (BalBiadd N M) L] :=
  {| morphism := BalBiadd_med |}.
Next Obligation.
  intros q q' Hq n m.
  change (bal_med_elem q n m ≈ bal_med_elem q' n m).
  apply bal_lim_ext; intro x.
  rewrite !bal_med_elem_leg.
  exact (proper_morphism (cone_leg Q x) q q' Hq n m).
Qed.

End AtACone.

Theorem BalBiadd_preserves_cone : IsLimitCone (FCone (BalBiadd N M) L).
Proof using All.
  intro Q.
  unshelve refine {| unique_obj := BalBiadd_cone_med Q |}.
  - intros x q n m.
    exact (bal_med_elem_leg Q q n m x).
  - intros u Hu q n m.
    apply bal_lim_ext; intro x.
    rewrite (bal_med_elem_leg Q q n m x).
    symmetry; exact (Hu x q n m).
Qed.

End AtALimitingCone.

Definition BalBiadd_continuous : ContinuousFunctor (BalBiadd N M) :=
  fun J K L HL => BalBiadd_preserves_cone HL.

Definition BalBiadd_PreservesImageLimit :
  @PreservesImageLimit Ab Sets (BalBiadd N M) :=
  Continuous_PreservesImageLimit BalBiadd_continuous.

End BalContinuity.

(* * ** 7A. Exercise 3's congruence index: [Prop] congruences on [bsum] / * ** 7A. 练习 3 的同余指数： [Prop] 关于 [bsum] 的同余式 *)

(*
 Section 3A over [Ab], one clause shorter: the balanced tensor is an
 abelian group, not a module, so there is no scalar congruence clause.
 Everything else transposes: the term type is Instance/Mod/Bimodule.v's
 [bsum] (whose relation [bs_eq] is already a [Prop] inductive), the
 quotient is an [AbObject] with the congruence as its `≈` and its own
 [Prop] mirror as [cmon_prop], and the covering is the kernel congruence
 of [bal_med_fun].

 WHAT DOES NOT TRANSPOSE, and is stated here rather than discovered
 later: section 10's Lemma-2 theorem is about [RMod R] only.  The [Ab]
 spanning vocabulary of section 9 ([ABGenSub], [AbImageSub], [ab_split],
 [abg_subobj]) has no counterpart of [mgen_preimage], so nothing below
 claims [bal_esols_direct] is small up to isomorphism.  Exercise 3 gets
 the unconditional representation and NOT the book-faithful second
 route. 

 --------
 第3A节 在[Ab]上，比原条款短一条：平衡张量是一个阿贝尔群，而不是模，因此没有标量同余条款。其他内容保持不变：项类型是Instance/Mod/Bimodule.v的[bsum]（其关系[bs_eq]已经是[Prop]的归纳），商是一个[AbObject]，其同余作为其`≈`，并且其自身的[Prop]镜像为[cmon_prop]，覆盖是[bal_med_fun]的核同余。什么是不转置的，并且在此处说明而不是稍后发现：第10节的引理-2定理仅关于 [RMod R]。第9节的 [Ab] 跨越词汇表（[ABGenSub]，[AbImageSub]，[ab_split]，[abg_subobj]）没有 [mgen_preimage] 的对应，因此下面没有任何内容声称 [bal_esols_direct] 在同构意义下是小的。练习3得到的是无条件表示，而不是书中忠实的第二种途径。
*)

Section BalCongruenceIndex.

Context {X : RingObject}.
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).

Record IsBalCongruence (Rq : bsum N M → bsum N M → Prop) : Prop := {
  bc_refl  : ∀ s, Rq s s;
  bc_sym   : ∀ s t, Rq s t → Rq t s;
  bc_trans : ∀ s t u, Rq s t → Rq t u → Rq s u;
  bc_gen   : ∀ s t, bs_eq s t → Rq s t;
  bc_plus  : ∀ s s' t t', Rq s s' → Rq t t' →
               Rq (bs_plus s t) (bs_plus s' t');
  bc_neg   : ∀ s s', Rq s s' → Rq (bs_neg s) (bs_neg s')
}.

Definition BalCongIdx : Type :=
  { Rq : bsum N M → bsum N M → Prop & IsBalCongruence Rq }.

End BalCongruenceIndex.

Arguments IsBalCongruence {X} N M Rq.
Arguments BalCongIdx {X} N M.

Section BalQuotient.

Context {X : RingObject}.
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).

(* NAMED, for the reason section 3A's [QMod_Setoid] is named. / 被命名，原因是第 3A 节的 [QMod_Setoid] 被命名。 *)
Definition QBal_Setoid (Rq : bsum N M → bsum N M → Prop)
  (H : IsBalCongruence N M Rq) : Setoid (bsum N M) :=
  {| equiv := Rq
   ; setoid_equiv :=
       {| Equivalence_Reflexive  := bc_refl  _ _ Rq H
        ; Equivalence_Symmetric  := bc_sym   _ _ Rq H
        ; Equivalence_Transitive := bc_trans _ _ Rq H |} |}.

Definition QBal (Rq : bsum N M → bsum N M → Prop)
  (H : IsBalCongruence N M Rq) : obj[Ab] :=
  {| ab_cmon := {|
       cmon_setoid :=
         {| carrier := bsum N M ; is_setoid := QBal_Setoid Rq H |};
       cmon_zero := @bs_zero X N M;
       cmon_plus := @bs_plus X N M;
       cmon_plus_respects := fun _ _ Hs _ _ Ht => bc_plus _ _ Rq H _ _ _ _ Hs Ht;
       cmon_plus_assoc := fun s t u => bc_gen _ _ Rq H _ _ (be_assoc s t u);
       cmon_plus_comm  := fun s t => bc_gen _ _ Rq H _ _ (be_comm s t);
       cmon_plus_zero_l := fun s => bc_gen _ _ Rq H _ _ (be_zero_l s);
       cmon_prop := @PropEquiv_of_relation _ (QBal_Setoid Rq H) Rq
                      (fun _ _ h => h) (fun _ _ h => h)
     |};
     ab_neg := @bs_neg X N M;
     ab_neg_respects := fun _ _ Hs => bc_neg _ _ Rq H _ _ Hs;
     ab_neg_left := fun s => bc_gen _ _ Rq H _ _ (be_neg_l s)
  |}.

(* The canonical balanced map into the quotient is the generator former. / 到商的典型平衡映射是生成器前体。 *)
Definition QBal_gen (Rq : bsum N M → bsum N M → Prop)
  (H : IsBalCongruence N M Rq) : BalBiadditive N M (QBal Rq H) :=
  @Build_BalBiadditive X N M (QBal Rq H) (@bs_gen X N M)
    (fun _ _ Hn _ _ Hm => bc_gen _ _ Rq H _ _ (be_gen Hn Hm))
    (fun n n' m => bc_gen _ _ Rq H _ _ (be_add_l n n' m))
    (fun n m m' => bc_gen _ _ Rq H _ _ (be_add_r n m m'))
    (fun x n m => bc_gen _ _ Rq H _ _ (be_balance x n m)).

End BalQuotient.

Arguments QBal_Setoid {X N M} Rq H.
Arguments QBal {X N M} Rq H.
Arguments QBal_gen {X N M} Rq H.

Section BalKernelCongruence.

Context {X : RingObject}.
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).
Context {A : AbObject}.
Context (beta : BalBiadditive N M A).

(*
 NO [PropEquiv] hypothesis: [cmon_prop] is a field of [CMonObject] and
 [AbObject] is a record over one. 

 --------
 NO  [PropEquiv] 假设：[cmon_prop] 是 [CMonObject] 的一个域，并且 [AbObject] 是在一上面的一个记录。
*)
Definition bal_ker_cong : bsum N M → bsum N M → Prop :=
  fun s t => @pequiv _ _ (cmon_prop A)
               (bal_med_fun beta s) (bal_med_fun beta t).

Lemma bal_ker_is_cong : IsBalCongruence N M bal_ker_cong.
Proof.
  unfold bal_ker_cong.
  constructor.
  - intro s; apply (@pequiv_from _ _ (cmon_prop A)); reflexivity.
  - intros s t H; apply (@pequiv_from _ _ (cmon_prop A)); symmetry;
      exact (@pequiv_to _ _ (cmon_prop A) _ _ H).
  - intros s t u H1 H2; apply (@pequiv_from _ _ (cmon_prop A)).
    transitivity (bal_med_fun beta t);
      [ exact (@pequiv_to _ _ (cmon_prop A) _ _ H1)
      | exact (@pequiv_to _ _ (cmon_prop A) _ _ H2) ].
  - intros s t H; apply (@pequiv_from _ _ (cmon_prop A));
      exact (bal_med_respects N M beta s t H).
  - intros s s' t t' H1 H2; apply (@pequiv_from _ _ (cmon_prop A)); simpl.
    exact (cmon_plus_respects A _ _ (@pequiv_to _ _ (cmon_prop A) _ _ H1)
                                _ _ (@pequiv_to _ _ (cmon_prop A) _ _ H2)).
  - intros s s' H; apply (@pequiv_from _ _ (cmon_prop A)); simpl.
    exact (ab_neg_respects A _ _ (@pequiv_to _ _ (cmon_prop A) _ _ H)).
Qed.

Definition bal_ker_idx : BalCongIdx N M :=
  existT _ bal_ker_cong bal_ker_is_cong.

(*
 The mediator out of the quotient.  Respectfulness IS [pequiv_to]; the
 two monoid laws are [reflexivity], the mediator being [bal_med_fun]. 

 --------
 仲裁者来自商。尊重就是 [pequiv_to]；两个幺半群定律是 [reflexivity]，仲裁者是 [bal_med_fun]。
*)
Program Definition bal_ker_med :
  QBal bal_ker_cong bal_ker_is_cong ~{Ab}~> A := {|
  cmon_map := {| morphism := bal_med_fun beta |}
|}.
Solve All Obligations with
  (first [ (intros s t H; exact (@pequiv_to _ _ (cmon_prop A) _ _ H))
         | (intros; simpl; reflexivity) ]).

(* The covering equation, on the nose. / 遮盖方程，恰到好处。 *)
Example bal_ker_factors (n : carrier (cmon_setoid (rm_ab N)))
  (m : carrier (cmon_setoid (rm_ab M))) :
  cmon_map bal_ker_med (bal_map (QBal_gen bal_ker_cong bal_ker_is_cong) n m)
  = bal_map beta n m
  := eq_refl.

End BalKernelCongruence.

Arguments bal_ker_cong {X N M A} beta.
Arguments bal_ker_is_cong {X N M A} beta.
Arguments bal_ker_idx {X N M A} beta.
Arguments bal_ker_med {X N M A} beta.

(* NAMED, so that the two record fields elaborate [QBal] at ONE universe instance -- section 3A's [QModOf] trap, at [Ab]. / 已命名，以便这两个记录字段在一个宇宙实例中详细说明 [QBal] —— 第 3A 节的 [QModOf] 陷阱，在 [Ab] 。 *)
Definition QBalOf {X : RingObject} {N : RModObject (Ring_op X)}
  {M : RModObject X} (i : BalCongIdx N M) : obj[Ab] := QBal (`1 i) (`2 i).

Definition QBalGenOf {X : RingObject} {N : RModObject (Ring_op X)}
  {M : RModObject X} (i : BalCongIdx N M) : BalBiadditive N M (QBalOf i) :=
  QBal_gen (`1 i) (`2 i).

Definition bal_esols_prop {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) : ElementSolutionSet (BalBiadd N M).
Proof.
  unshelve refine (@Build_ElementSolutionSet Ab (BalBiadd N M)
                     (BalCongIdx N M) QBalOf QBalGenOf _).
  intros A beta.
  exists (bal_ker_idx beta), (bal_ker_med beta).
  intros n m; simpl; reflexivity.
Defined.

(* * ** 8. Exercise 3: the balanced tensor from the AFT, and the comparison / * ** 8. 练习3：来自AFT的平衡张量及其比较 *)

(*
 Top level again, for the same [Set] pin.

 CORRECTION, PR “algebraic carriers are sets” (2026-09-17): the
 conditional is now named [bal_tensor_via_AFT_of_esols] and
 [bal_tensor_via_AFT] is unconditional, at [bal_esols_prop] of section
 7A.  No statement was weakened: the conditional is the old constant
 statement for statement. 

 --------
 顶层再次出现，对于同一个 [Set] 引脚。

 更正，PR “代数载体是集合”（2026-09-17）：条件现在被命名为 [bal_tensor_via_AFT_of_esols]，[bal_tensor_via_AFT] 是无条件的，在第 7A 节的 [bal_esols_prop]。没有任何陈述被削弱：条件是陈述的旧常量陈述。
*)

Definition bal_tensor_via_AFT_of_esols {X : RingObject}
  (N : RModObject (Ring_op X)) (M : RModObject X)
  (E : ElementSolutionSet (BalBiadd N M)) :
  Representable (BalBiadd N M) :=
  representability_theorem (BalBiadd N M) Ab_Complete
    (BalBiadd_PreservesImageLimit N M) E.

Definition bal_tensor_via_AFT {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) : Representable (BalBiadd N M) :=
  bal_tensor_via_AFT_of_esols N M (bal_esols_prop N M).

(*
 THE CIRCULAR DISCHARGE, KEPT FOR COMPARISON; A REMOVAL CANDIDATE FOR
 JOHN.  Circular as at [RMod R]: a solution set at the universe the
 theorem demands, read off the balanced tensor the theorem is meant to
 build.  CORRECTION, PR “algebraic carriers are sets” (2026-09-17): its
 stated role, “to show the conditional above is not vacuous”, is gone --
 [bal_esols_prop] discharges the hypothesis non-circularly.  Kept, not
 deleted, on the same footing as [tensor_esols_from_tensor]. 

 --------
 循环释放，保留用于比较；约翰的一个移除候选项。 截至 [RMod R] 的循环：一个在宇宙中由定理要求的解集，从定理旨在构建的平衡张量中读取。 修正，PR “代数载体是集合”（2026-09-17）：其声明的角色，“展示上述条件不是空洞的”，已经消失——[bal_esols_prop] 非循环地释放假设。 保留，未删除，与 [tensor_esols_from_tensor] 处于同等地位。
*)
Definition bal_esols_from_tensor {X : RingObject}
  (N : RModObject (Ring_op X)) (M : RModObject X) :
  ElementSolutionSet (BalBiadd N M).
Proof.
  unshelve refine (@Build_ElementSolutionSet Ab (BalBiadd N M)
                     unit (fun _ => BalTensor N M)
                     (fun _ => @bal_gen X N M) _).
  intros A β.
  refine (existT _ tt _).
  refine (existT _ (bal_med β) _).
  intros n m; reflexivity.
Defined.

Definition bal_tensor_via_AFT_from_tensor {X : RingObject}
  (N : RModObject (Ring_op X)) (M : RModObject X) :
  Representable (BalBiadd N M) :=
  bal_tensor_via_AFT_of_esols N M (bal_esols_from_tensor N M).

Definition bal_repr_of_UE {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) : Representable (BalBiadd N M) :=
  Representable_of_UniversalElement (bal_UniversalElement N M).

Example bal_repr_of_UE_obj {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) :
  @repr_obj Ab (BalBiadd N M) (bal_repr_of_UE N M) = BalTensor N M := eq_refl.

Definition bal_AFT_iso_of_esols {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) (E : ElementSolutionSet (BalBiadd N M)) :
  @repr_obj Ab (BalBiadd N M) (bal_tensor_via_AFT_of_esols N M E)
    ≅ BalTensor N M :=
  repr_unique_iso (bal_repr_of_UE N M)
    (bal_tensor_via_AFT_of_esols N M E).

Definition bal_AFT_iso {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) :
  @repr_obj Ab (BalBiadd N M) (bal_tensor_via_AFT N M) ≅ BalTensor N M :=
  bal_AFT_iso_of_esols N M (bal_esols_prop N M).

Definition bal_AFT_iso_universal_of_esols {X : RingObject}
  (N : RModObject (Ring_op X)) (M : RModObject X)
  (E : ElementSolutionSet (BalBiadd N M)) :=
  repr_unique_iso_universal (bal_repr_of_UE N M)
    (bal_tensor_via_AFT_of_esols N M E).

Definition bal_AFT_iso_universal {X : RingObject}
  (N : RModObject (Ring_op X)) (M : RModObject X) :=
  bal_AFT_iso_universal_of_esols N M (bal_esols_prop N M).

Definition bal_AFT_ue_of_esols {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) (E : ElementSolutionSet (BalBiadd N M)) :
  UniversalElement (BalBiadd N M) :=
  UniversalElement_of_Representable (bal_tensor_via_AFT_of_esols N M E).

Definition bal_AFT_ue {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) : UniversalElement (BalBiadd N M) :=
  bal_AFT_ue_of_esols N M (bal_esols_prop N M).

Definition bal_AFT_elem_iso {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) (E : ElementSolutionSet (BalBiadd N M)) :
  @ue_obj Ab (BalBiadd N M) (bal_AFT_ue_of_esols N M E) ≅ BalTensor N M :=
  universal_element_iso
    (AUniversalElement_of_UniversalElement (bal_AFT_ue_of_esols N M E))
    (bal_universal_element N M).

Theorem bal_AFT_elem_commutes {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) (E : ElementSolutionSet (BalBiadd N M)) :
  fmap[BalBiadd N M] (to (bal_AFT_elem_iso N M E))
    (@ue_elem Ab (BalBiadd N M) (bal_AFT_ue_of_esols N M E))
    ≈ @bal_gen X N M.
Proof.
  exact (ue_med_commutes
           (AUniversalElement_of_UniversalElement (bal_AFT_ue_of_esols N M E))
           (bal_universal_element N M)).
Qed.

Theorem bal_AFT_iso_carries_elem {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) (E : ElementSolutionSet (BalBiadd N M)) :
  fmap[BalBiadd N M] (to (bal_AFT_iso_of_esols N M E))
    (@ue_elem Ab (BalBiadd N M) (bal_AFT_ue_of_esols N M E))
    ≈ @bal_gen X N M.
Proof.
  pose proof (repr_compatible_at
    (repr_induced_compatible (bal_repr_of_UE N M)
       (bal_tensor_via_AFT_of_esols N M E) nat_id) (BalTensor N M) id) as HC.
  pose proof (@naturality _ _ _ _
      (to (@represented _ _ (bal_tensor_via_AFT_of_esols N M E)))
      (@repr_obj _ _ (bal_tensor_via_AFT_of_esols N M E)) (BalTensor N M)
      (to (bal_AFT_iso_of_esols N M E)) (@id Ab _)) as HN.
  transitivity (transform[to (@represented _ _ (bal_tensor_via_AFT_of_esols N M E))]
                  (BalTensor N M)
                  (@compose Ab _ _ _ (to (bal_AFT_iso_of_esols N M E)) (@id Ab _))).
  - exact HN.
  - transitivity (transform[to (@represented _ _ (bal_tensor_via_AFT_of_esols N M E))]
                    (BalTensor N M)
                    (@compose Ab _ _ _ (@id Ab _) (to (bal_AFT_iso_of_esols N M E)))).
    + apply proper_morphism.
      rewrite id_left, id_right; reflexivity.
    + rewrite HC.
      exact (@fmap_id _ _ (BalBiadd N M) (BalTensor N M) (@bal_gen X N M)).
Qed.

(*
 STATEMENT CHANGE, recorded: the right-hand side read [bal_AFT_iso N M E]
 before the PR “algebraic carriers are sets” (2026-09-17).  The note at
 [tensor_AFT_isos_agree] above gives the reason; this is its twin. 

 --------
 声明更改，记录：在 PR “代数载体是集合” (2026-09-17) 之前，右侧显示为 [bal_AFT_iso N M E]。上面 [tensor_AFT_isos_agree] 的注释给出了原因；这是它的对应项。
*)
Theorem bal_AFT_isos_agree {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) (E : ElementSolutionSet (BalBiadd N M)) :
  bal_AFT_elem_iso N M E ≈ bal_AFT_iso_of_esols N M E.
Proof.
  exact (universal_element_iso_unique
           (AUniversalElement_of_UniversalElement (bal_AFT_ue_of_esols N M E))
           (bal_universal_element N M)
           (bal_AFT_iso_of_esols N M E)
           (bal_AFT_iso_carries_elem N M E)).
Qed.

Definition bal_AFT_elem_unique {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) (E : ElementSolutionSet (BalBiadd N M)) :=
  universal_element_unique
    (AUniversalElement_of_UniversalElement (bal_AFT_ue_of_esols N M E))
    (bal_universal_element N M).

(* * ** 9. Exercise 3: Mac Lane's direct solution set over [Ab] / * ** 9. 练习 3：Mac Lane 在 [Ab] 上的直接解集 *)

Section AbGeneratedSub.

Context {A : AbObject}.
Context (P : carrier (cmon_setoid A) → Type).

(*
 Instance/Mod/Spanning.v's [ABGen] has exactly the five fields of
 Instance/Ab/DirectedColimit.v's [AbSubgroup]; this is the
 repackaging, with no proof obligation. 

 --------
 Instance/Mod/Spanning.v 的 [ABGen] 恰好具有 Instance/Ab/DirectedColimit.v 的 [AbSubgroup] 的五个字段；这是重新打包，没有任何证明义务。
*)
Definition ABGenSub : AbSubgroup A :=
  @Build_AbSubgroup A (ABGen P) (abgen_resp P) (abgen_zero P)
    (abgen_plus P) (abgen_neg P).

End AbGeneratedSub.

(* The image of a homomorphism of abelian groups, as a subgroup -- the [Ab] counterpart of Instance/Mod/Quotient.v's [ImageSubmod]. / 作为子群的阿贝尔群同态的像——Instance/Mod/Quotient.v 中 [ImageSubmod] 的 [Ab] 对应物。 *)
Program Definition AbImageSub {A B : AbObject} (f : A ~{Ab}~> B) :
  AbSubgroup B := {|
  absub_mem := fun b => { a : carrier (cmon_setoid A) & cmon_map f a ≈ b }
|}.
Next Obligation.
  intros A B f a b Hab [x Hx].
  exists x; rewrite Hx; exact Hab.
Qed.
Next Obligation.
  intros A B f.
  exists (cmon_zero A); apply cmon_map_zero.
Qed.
Next Obligation.
  intros A B f a b [x Hx] [y Hy].
  exists (cmon_plus A x y).
  rewrite (cmon_map_plus f); now rewrite Hx, Hy.
Qed.
Next Obligation.
  intros A B f a [x Hx].
  exists (ab_neg A x).
  rewrite (ab_map_neg f); now rewrite Hx.
Qed.

(*
 A bijective homomorphism of abelian groups splits.  The section is not
 canonical -- it picks the preimage the surjectivity datum carries -- and
 each law is injectivity applied to the witness equation. 

 --------
 阿贝尔群的双射同态可分裂。该截面不是规范的 —— 它选择了满射数据携带的原像 —— 并且每个定律都是将单射性应用于见证方程。
*)
Program Definition ab_split {A B : AbObject} (f : A ~{Ab}~> B)
  (Hi : AbInjective f) (Hs : AbSurjective f) : B ~{Ab}~> A := {|
  cmon_map := {| morphism := fun b => `1 (Hs b) |}
|}.
Next Obligation.
  intros A B f Hi Hs a b Hab.
  apply Hi; rewrite (`2 (Hs a)), (`2 (Hs b)); exact Hab.
Qed.
Next Obligation.
  intros A B f Hi Hs; simpl.
  apply Hi; rewrite (`2 (Hs (cmon_zero B))).
  symmetry; exact (cmon_map_zero f).
Qed.
Next Obligation.
  intros A B f Hi Hs a b; simpl.
  apply Hi.
  rewrite (cmon_map_plus f).
  rewrite (`2 (Hs (cmon_plus B a b))), (`2 (Hs a)), (`2 (Hs b)).
  reflexivity.
Qed.

Lemma ab_split_commutes {A B : AbObject} (f : A ~{Ab}~> B)
  (Hi : AbInjective f) (Hs : AbSurjective f) :
  @compose Ab _ _ _ f (ab_split f Hi Hs) ≈ @id Ab B.
Proof. intro b; exact (`2 (Hs b)). Qed.

(*
 A subgroup as a subobject of [Ab]: the inclusion is injective on the
 nose, hence monic. 

 --------
 作为  [Ab] 的子对象的子群：包含映射在本质上是单射的，因此是单态的。
*)
Definition abg_subobj {A : AbObject} (S : AbSubgroup A) : @SubObj Ab A :=
  @Build_SubObj Ab A (AbSubgroupAb S) (absub_incl S)
    (ab_injective_monic (absub_incl S) (fun _ _ H => H)).

Section BalSpanningBridge.

Context {X : RingObject}.
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).
Context {A : AbObject}.
Context (β : BalBiadditive N M A).

Definition bal_restrict_image (m : @SubObj Ab A)
  (β' : BalBiadditive N M (sub_dom m))
  (Hβ : ∀ n mm, cmon_map (sub_mono m) (bal_map β' n mm) ≈ bal_map β n mm)
  (a : carrier (cmon_setoid A)) (Ha : bal_image N M β a) :
  absub_mem (AbImageSub (sub_mono m)) a.
Proof using All.
  destruct Ha as [n [mm Hnm]].
  exists (bal_map β' n mm).
  rewrite (Hβ n mm); exact Hnm.
Defined.

(*
 Elementwise spanning implies Mac Lane's categorical form, over [Ab].
 Same argument as Instance/Mod/Spanning.v's
 [rbilinear_spanning_to_spanning], with [ABGen] for [MGen] and
 [AbImageSub] for [ImageSubmod]. 

 --------
 逐元素的生成意味着在  [Ab] 上的 Mac Lane 范畴形式。
 与 Instance/Mod/Spanning.v 中的 [rbilinear_spanning_to_spanning] 的论证相同，
 将 [ABGen] 用于 [MGen]，
 将 [AbImageSub] 用于 [ImageSubmod]。
*)
Theorem bal_spanning_to_spanning (H : BalSpanning N M β) :
  Spanning (BalBiadd N M) (global_element (X := BalBiadd N M A) β).
Proof using All.
  intros m [k Hk].
  pose (β' := k ttt).
  assert (Hβ : ∀ n mm, cmon_map (sub_mono m) (bal_map β' n mm)
                         ≈ bal_map β n mm) by exact (Hk ttt).
  assert (Hs : AbSurjective (sub_mono m)).
  { intro x.
    exact (abgen_least (bal_image N M β)
             (absub_mem (AbImageSub (sub_mono m)))
             (absub_resp (AbImageSub (sub_mono m)))
             (absub_zero (AbImageSub (sub_mono m)))
             (absub_plus (AbImageSub (sub_mono m)))
             (absub_neg (AbImageSub (sub_mono m)))
             (bal_restrict_image m β' Hβ) x (H x)). }
  assert (Hi : AbInjective (sub_mono m)) by
    exact (ab_monic_injective (sub_mono m) (sub_is_monic m)).
  exists (ab_split (sub_mono m) Hi Hs).
  exact (ab_split_commutes (sub_mono m) Hi Hs).
Defined.

(* The corestriction of β to the subgroup generated by its image. / β 在其像所生成子群上的余限制。 *)
Program Definition bal_gen_corestrict :
  BalBiadditive N M (AbSubgroupAb (ABGenSub (bal_image N M β))) := {|
  bal_map := fun n mm =>
    existT _ (bal_map β n mm)
      (abgen_base (bal_image N M β) (bal_map β n mm)
         (existT _ n (existT _ mm (reflexivity _))))
|}.
Next Obligation.
  intros n n' Hn m m' Hm; simpl.
  exact (bal_respects β _ _ Hn _ _ Hm).
Qed.
Next Obligation. intros n n' m; simpl; apply bal_add_l. Qed.
Next Obligation. intros n m m'; simpl; apply bal_add_r. Qed.
Next Obligation. intros x n m; simpl; apply bal_balance. Qed.

Lemma bal_corestrict_spanning : BalSpanning N M bal_gen_corestrict.
Proof using All.
  intros [a D].
  induction D as [a Ha|a b Hab D IH| |a b D1 IH1 D2 IH2|a D IH].
  - refine (abgen_base (bal_image N M bal_gen_corestrict) _ _).
    destruct Ha as [n [mm Hnm]].
    exists n, mm; exact Hnm.
  - refine (abgen_resp (bal_image N M bal_gen_corestrict) _ _ _ IH).
    exact Hab.
  - refine (abgen_resp (bal_image N M bal_gen_corestrict) _ _ _
              (abgen_zero (bal_image N M bal_gen_corestrict))).
    reflexivity.
  - refine (abgen_resp (bal_image N M bal_gen_corestrict) _ _ _
              (abgen_plus (bal_image N M bal_gen_corestrict) _ _ IH1 IH2)).
    reflexivity.
  - refine (abgen_resp (bal_image N M bal_gen_corestrict) _ _ _
              (abgen_neg (bal_image N M bal_gen_corestrict) _ IH)).
    reflexivity.
Defined.

End BalSpanningBridge.

Definition bal_esols_direct {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) : ElementSolutionSet (BalBiadd N M).
Proof.
  unshelve refine (@Build_ElementSolutionSet Ab (BalBiadd N M)
                     (SpanningArrowsOutOf (BalBiadd N M) SetsOne)
                     (fun i => `1 i) (fun i => `1 (`2 i) ttt) _).
  intros A β.
  unshelve eexists.
  - refine (existT _ (AbSubgroupAb (ABGenSub (bal_image N M β))) _).
    refine (existT _ (global_element
                        (X := BalBiadd N M
                                (AbSubgroupAb (ABGenSub (bal_image N M β))))
                        (bal_gen_corestrict N M β)) _).
    exact (bal_spanning_to_spanning N M (bal_gen_corestrict N M β)
             (bal_corestrict_spanning N M β)).
  - exists (absub_incl (ABGenSub (bal_image N M β))).
    intros n m; reflexivity.
Defined.

Example bal_esols_direct_index {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) :
  esol_index (bal_esols_direct N M)
    = SpanningArrowsOutOf (BalBiadd N M) SetsOne := eq_refl.

Example bal_esols_direct_obj {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) (i : SpanningArrowsOutOf (BalBiadd N M) SetsOne) :
  esol_obj (bal_esols_direct N M) i = `1 i := eq_refl.

Example bal_esols_direct_elem {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) (i : SpanningArrowsOutOf (BalBiadd N M) SetsOne) :
  esol_elem (bal_esols_direct N M) i = `1 (`2 i) ttt := eq_refl.

(* * ** 10. MAC LANE §V.7 LEMMA 2 AS A THEOREM AT [RMod R] / * ** 10. MAC LANE §V.7 引理 2 作为 [RMod R] 的定理 *)

(*
 WHAT THIS SECTION DISCHARGES, AND WHAT IT DOES NOT.

 Mac Lane's Lemma 2 (book p. 128, catalog id `maclane:V.7:lem2`) is the
 step that turns his covering family into a SET: the spanning codomains
 are quotients of one fixed object, so a small family of representatives
 UP TO ISOMORPHISM suffices.  Section 2's [tensor_esols_direct] is the
 covering family and section 3A gives the fixed object -- the term module
 -- together with the quotients.  Putting the two together proves the
 lemma at [RMod R], as [SmallUpToIso] of Adjunction/GAFT/Resize.v, and
 feeding the resizing to [representability_theorem] gives a SECOND,
 book-faithful route to the same representation.

 SCOPE, because “Lemma 2 is discharged” is easy to over-read.  What is
 discharged is the SMALLNESS premise.  It is NOT
 [GAFT_from_spanning]'s hypotheses, which are [HasWidePullbacks A] and
 [PreservesWidePullbacks G]; the first is still universe-refused at
 [RMod R] (Instance/Mod/Spanning.v), and the widening of
 Adjunction/SpanningArrow.v's [Section GAFTFromSpanning] in this same PR
 does not reach it either (that file's header measures the surviving
 refusal).  [GAFT_from_spanning] is not reachable at [RMod R] by this
 work, and NOT DELIVERED (2) of the header stands.

 THE THREE PIECES.

 (1) [si_to] is [cong_spanning_arrow]: every congruence quotient, with
 its canonical bilinear map, IS a spanning arrow.  The spanning proof is
 [QMod_gen_spanning] of section 3A.

 (2) [si_rep] is the interesting half.  At a spanning arrow [(W; (g; sp))]
 with [β := g ttt], the representative is [ker_idx β], and [ker_med β] is
 an ISOMORPHISM -- injective because the congruence IS the kernel pair,
 surjective because [β] spans.

 (3) The arrow clause is [reflexivity] after destructing the singleton.

 ONE TRAP, worth the line.  [sp : Spanning (Bilin V V') g] is NOT
 [Spanning (Bilin V V') (global_element (g ttt))]: eta on the singleton
 is not definitional.  The transport is Adjunction/SpanningArrow.v's
 [spanning_respects], with [g ≈ global_element (g ttt)] proved by
 destructing the singleton. 

 --------
 本节说明的内容及未说明的内容。

 Mac Lane 的引理 2（书中第 128 页，目录 ID `maclane:V.7:lem2`）是将他的覆盖族转化为集合的步骤：跨越的余域是一个固定对象的商，因此一小批代表（至同构）就足够了。第 2 节的 [tensor_esols_direct] 是覆盖族，第 3A 节给出了固定对象——项模——以及商。将两者结合起来在 [RMod R] 处证明了该引理，作为 Adjunction/GAFT/Resize.v 中的 [SmallUpToIso]，并将调整大小应用于 [representability_theorem]，提供了第二条与书籍一致的相同表示路径。范围，因为“引理 2 已被取消”容易被误读。被取消的是 SMALLNESS 前提。它并不是 [GAFT_from_spanning] 的假设，后者是 [HasWidePullbacks A] 和 [PreservesWidePullbacks G]；前者在 [RMod R]（Instance/Mod/Spanning.v）仍然被宇宙拒绝，并且在同一个 PR 中对 Adjunction/SpanningArrow.v 的 [Section GAFTFromSpanning] 的扩展也没有达到它（该文件的头部衡量了存活的拒绝）。[GAFT_from_spanning] 在 [RMod R] 处无法被这项工作触及，并且头部的 NOT DELIVERED (2) 仍然有效。

 三部分内容。

 (1) [si_to] 是 [cong_spanning_arrow]：每个同余商，以及其典型的双线性映射，都是一个跨度箭头。跨度证明是第 3A 节的 [QMod_gen_spanning]。(2)  [si_rep] 是有趣的一半。在一个支撑箭头 [(W; (g; sp))] 与 [β := g ttt] 中，代表是 [ker_idx β]，而 [ker_med β] 是一个同构——注入因为合同是核对，满射因为 [β] 支撑。

 (3) 箭头条款是在解析单例之后的 [reflexivity]。

 一个陷阱，值得一行。[sp : Spanning (Bilin V V') g] 不是 [Spanning (Bilin V V') (global_element (g ttt))]：单例上的 eta 不是定义性的。传输是 Adjunction/SpanningArrow.v 的 [spanning_respects]，[g ≈ global_element (g ttt)] 通过解析单例来证明。
*)

Definition cong_spanning_arrow {R : RingObject} {V V' : obj[RMod R]}
  (i : CongIdx V V') : SpanningArrowsOutOf (Bilin V V') SetsOne :=
  existT _ (QModOf i)
    (existT _ (global_element (X := Bilin V V' (QModOf i)) (QModGenOf i))
       (rbilinear_spanning_to_spanning (QModGenOf i)
          (QMod_gen_spanning (`1 i) (`2 i)))).

Theorem tensor_spanning_SmallUpToIso {R : RingObject} (V V' : obj[RMod R]) :
  SmallUpToIso (sols_of_esols (Bilin V V') (tensor_esols_direct V V')).
Proof.
  unshelve refine (@Build_SmallUpToIso (RMod R) Sets (Bilin V V') SetsOne
                     (sols_of_esols (Bilin V V') (tensor_esols_direct V V'))
                     (CongIdx V V') cong_spanning_arrow _).
  intro i.
  destruct i as [W [g sp]].
  pose (beta := g ttt).
  assert (Hg : g ≈ global_element (X := Bilin V V' W) beta).
  { intro u; destruct u; intros v w; reflexivity. }
  assert (Hsp : RBilinearSpanning beta).
  { exact (spanning_to_rbilinear_spanning beta
             (spanning_respects (Bilin V V') g
                (global_element (X := Bilin V V' W) beta) Hg sp)). }
  exists (ker_idx beta).
  unshelve eexists.
  - exact (ker_iso beta Hsp).
  - intro u; destruct u; simpl; intros v w; reflexivity.
Defined.

(* Mac Lane's OWN family, resized by his own Lemma 2. / 麦克·莱恩自己的家族，由他自己的引理 2 调整大小。 *)
Definition tensor_esols_resized {R : RingObject} (V V' : obj[RMod R]) :
  ElementSolutionSet (Bilin V V') :=
  esols_of_sols (Bilin V V')
    (resize_up_to_iso (sols_of_esols (Bilin V V') (tensor_esols_direct V V'))
       (tensor_spanning_SmallUpToIso V V')).

(*
 ...and fed to the theorem.  Same signature as [tensor_via_AFT], reached
 by a different argument: p. 128's covering family plus Lemma 2, rather
 than the kernel congruence of an arbitrary bilinear map directly. 

 --------
 ...并输入到定理中。与 [tensor_via_AFT] 相同的签名，通过不同的论证得到：第128页的覆盖族加上引理2，而不是直接使用任意双线性映射的核同余。
*)
Definition tensor_via_AFT_maclane {R : RingObject} (V V' : obj[RMod R]) :
  Representable (Bilin V V') :=
  tensor_via_AFT_of_esols V V' (tensor_esols_resized V V').
