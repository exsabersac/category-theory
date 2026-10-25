Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Comma.Special.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Functor.Construction.Product.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Morphisms.
Require Import Category.Instance.One.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Limit.Power.
Require Import Category.Structure.Limit.Power.Hom.
Require Import Category.Structure.Limit.Weighted.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Adjunction.Parameter.

Generalizable All Variables.

(* * * The copower is left adjoint to the power / * * 余幂是幂的左伴随 *)

(*
 nLab:      https://ncatlab.org/nlab/show/copower
 nLab:      https://ncatlab.org/nlab/show/power
 nLab:      https://ncatlab.org/nlab/show/adjoint+functor

 Sources, cited BY LOCATION, both read off the RENDERED page (the printed
 page number and the PDF page number differ by a constant +9, verified):

 - Mac Lane, "Categories for the Working Mathematician", 2nd ed.
 (Springer GTM 5), section IV.2, exercise 12, printed p. 90
 (PDF p. 99), item [maclane:IV.2:ex12], VERBATIM:

 "12. If X is a set and C a category with powers and copowers,
 prove that the copower  c ↦ X · c  is left adjoint to the power
 c ↦ c^X."

 That is the theorem this file exists for, and
 [Copower_Power_Adjunction] is its name.

 - Mac Lane, same book, section IV.7, exercise 1, printed p. 102
 (PDF p. 111), item [maclane:IV.7:ex1], VERBATIM AS PRINTED:

 "1. Interpret the definition  C(X · a, c) ≅ Set(X, C(c, a))  of
 copowers X · a in C as an adjunction with parameter a."

 See the misprint disclosure below.  Nothing in THIS section of the
 file discharges Ex 1; the quote is carried because the variance
 argument settles what the parameter half must say.

 ★ THE PRINTED FORM OF §IV.7 Ex 1 HAS THE VARIANCE WRONG.  It is a
 MISPRINT, not an OCR artifact: the page was read at 400 dpi and the
 [pdftotext] layer agrees, printing "Set (X, C(c, a))".  The reason it
 cannot be what is meant is a variance count and not a matter of taste:

 LHS  C(X·a, c)        is COVARIANT     in c
 RHS  Set(X, C(a,c))   is COVARIANT     in c   <- consistent
 RHS  Set(X, C(c,a))   is CONTRAVARIANT in c   <- as printed

 A covariant and a contravariant functor of [c] cannot be naturally
 isomorphic in [c].  Mathematically a map OUT of the X-fold copower of [a]
 is an X-indexed FAMILY of maps [a → c], which is [Set(X, C(a,c))].  The
 correct form is therefore [C(X · a, c) ≅ Set(X, C(a,c))], and that is
 what Structure/Limit/Power/Hom.v's [copower_hom_iso] already proves --
 [copower_hom_functor J b] is [c ↦ ∏_J C(b,c)], covariant, exactly as the
 variance count requires.  The printed form is disclosed here rather than
 reproduced, and rather than silently "fixed".

 ★ THE ISSUE AND THE BOOK PARAMETRIZE DIFFERENT VARIABLES.  Ex 12 above
 fixes the SET X and varies the object; Ex 1 fixes nothing and asks for the
 bifunctor [(X, a) ↦ X · a] read as an adjunction with parameter [a], whose
 assembled right adjoint is the HOM-FUNCTOR.  The issue's own item 4 asks
 instead for the INDEX SET as the parameter -- the variable its item 3
 (= Ex 12) holds FIXED.  Both readings are true and neither implies the
 other; this section delivers Ex 12, at a fixed [J].

 PRIOR ART -- THE ISSUE'S "Current state" IS STALE, AND HERE IS THE
 CRITERION.

 THE CRITERION, stated once and used for every count below: "any
 whole-word occurrence in any [.v] file OTHER THAN THIS ONE, comments
 included", reproduced by

 rg -l -w -e '<token>' -g '*.v' \
 -g '!Structure/Limit/Power/Adjunction.v' .

 Issue #366 says: "Absent.  Searches for [copower], [cotensor] and
 [tensoring] return nothing."  That is FALSE for [copower], which AT THE
 BASE COMMIT (every count in this paragraph is taken there, before this
 file and its probe existed) occurs in
 THREE files -- Structure/Limit/Power.v (361 lines),
 Structure/Limit/Power/Hom.v (548) and Test/ProbePower.v -- all delivered
 by issue #321, and the module path the issue "suggests",
 Structure/Limit/Power.v, is ALREADY TAKEN by it.  What IS absent is the
 FUNCTOR: [Power_Functor], [Copower_Functor], [power_fmap] and
 [copower_fmap] each return ZERO files, so functoriality in the object
 variable is genuinely new.  The instrument discriminates: [power] itself
 returns 42 files and [Monoid] 91.  (At HEAD, excluding only this file,
 the probe adds one to each of [copower] and [power] and one to three of
 the four functor names; the collision sweep below therefore excludes the
 probe as well.)

 Accordingly a QA correction on the issue supersedes its first three work
 items with "consume, do not rebuild", and this file consumes: #321's
 [power], [copower], [power_ev], [copower_inj], [power_ump], [copower_ump],
 [power_desc], [copower_desc], and -- for the adjunction proper -- its two
 already-proved characterizing bijections [power_hom_iso_at] and
 [copower_hom_iso_at].  Nothing below re-derives a universal property.

 WHY THIS IS A NEW FILE AND NOT AN EXTENSION -- MEASURED, NOT PREFERRED

 Structure/Limit/Power.v CANNOT host the adjunction: it would be a
 DEPENDENCY CYCLE, not merely a cost.  Structure/Limit/Power/Hom.v Requires
 Structure/Limit/Power.vo (visible in .Makefile.coq.d at the
 [Structure/Limit/Power/Hom.vo :] rule), so Power.v cannot Require Power/Hom.v
 back, and the two [_at] bijections this file composes live in Power/Hom.v.

 Structure/Limit/Power/Hom.v COULD have hosted it -- Theory/Adjunction is a
 MARGINAL cost of exactly ONE module there -- but that would place
 Theory/Adjunction behind that file's one existing consumer,
 Test/ProbePower.v (measured: it is the only [.v] file in the tree that
 Requires Power/Hom), and would mix the characterizing-isomorphism layer
 with the adjunction layer.  The margin is also not stable for the rest of
 #366: Adjunction/Parameter.v, which the parameter half wants, is a marginal
 FORTY-SIX on that same base.  A sibling costs no existing file anything,
 since nothing Requires it.

 Closures, measured as transitive in-project [.vo] dependencies EXCLUDING
 the file itself, over .Makefile.coq.d: Structure/Limit/Power/Hom.v is 36
 and this file is 38, the two added modules being Power/Hom.v itself and
 Theory/Adjunction.v.  Adjunction/GAFT.v is 42 and is untouched.

 WHAT IS DELIVERED HERE

 [Power_Functor J : C ⟶ C], the endofunctor [b ↦ J ⋔ b], with all three
 functor laws PROVED from [power_desc]'s uniqueness clause -- the issue's
 item 2, which had no prior art of any kind.

 [Copower_Functor J : C ⟶ C] costs NOTHING, and that is the one place the
 op-trick in #321's design pays in full.  [copower] is DEFINITIONALLY
 [@power (C^op)], so [Copower_Functor J := Opposite_Functor
 (@Power_Functor (C^op) HC J)] needs no obligation, no tactic and no proof
 text: Functor/Opposite.v's [Opposite_Functor] is a plain [Definition] that
 passes all three law fields through unchanged.  Four [eq_refl] readbacks
 pin what that buys -- the object action IS [copower J b], the arrow action
 IS the op-power's [power_fmap], the double opposite returns the op-power
 functor ON THE NOSE, and the arrow action IS the mediator [copower_desc]
 produces.

 TWO REFUTATIONS, MEASURED STRICT-FIRST, WITH THEIR VERBATIM ERRORS, SO A
 PROBE CAN PIN THEM.  Both were compiled alone with the other stripped.

 (1) CONVERSION.  A hand-built DIRECT copower functor -- object action
 [b ↦ copower J b], arrow action the [copower_desc] mediator, three
 obligations -- agrees with [Copower_Functor J] on BOTH data fields at
 [eq_refl], and the WHOLE RECORD is refused:

 The term "eq_refl" has type
 "Copower_Functor_direct = Copower_Functor_direct"
 while it is expected to have type
 "Copower_Functor_direct = Copower_Functor J"
 (cannot unify "Copower_Functor_direct" and "Copower_Functor J").

 The two data fields agreeing is what says nothing is LOST by taking the
 cheap route; the record differing is the three [Program]-rebuilt law
 fields, as everywhere else in this tree.

 (2) TYPING, and it is a DIFFERENT KIND, told apart by the error text
 rather than by a label.  Stated with BOTH sides' implicits written out,
 [@Copower_Functor C HC J = @Power_Functor (C^op) HC J := eq_refl] is
 refused at the STATEMENT, before any [eq_refl] is examined, the two
 constants not sharing a type ([C ⟶ C] against [C^op ⟶ C^op]); the
 error carries no "cannot unify" clause:

 The term "Power_Functor J" has type "C^op ⟶ C^op"
 while it is expected to have type "C ⟶ C".

 That spelling matters.  Written [Copower_Functor J = @Power_Functor
 (C^op) HC J], with the left side's category IMPLICIT, the statement
 ELABORATES -- the elaborator re-solves that category as [C^op], leaving
 the coproduct instance an unresolved evar -- and the error fires at
 [eq_refl] instead, which is negative 3's fact at [C^op] and not a type
 mismatch at all; a first draft of this paragraph quoted exactly that
 error, and the probe's negative 2 records the episode.  The same
 equation at [C] ([Copower_Functor J = Power_Functor J]) is negative 3,
 and it is CONVERSION: both sides share [C ⟶ C] and the error ends in
 [cannot unify "Copower_Functor J" and "Power_Functor J"].

 So [Copower_Functor J] is [Opposite_Functor] OF the op-power functor and
 is NOT that functor; what holds on the nose is the double opposite,
 [copower_functor_double_op] below.

 [Copower_Power_Adjunction J : Copower_Functor J ⊣ Power_Functor J] is
 Ex 12.  Its hom-set isomorphism is the COMPOSITE of #321's two bijections
 rather than a fresh derivation from the universal properties, which is
 what "consume, do not rebuild" means here and is the issue's stated
 reviewer check that the file does not fork the API.  The composite is
 well-founded because the two bijections share their right-hand side ON THE
 NOSE: [copower_hom_iso_at (copower_ump J b) c] and
 [power_hom_iso_at (power_ump J c) b] both land at the [Sets]-power
 [J ⋔ C(b,c)], written [cp_middle b c] below, so they compose with no
 comparison map inserted and [cp_adj_iso] is a [:=] with no tactic.  Only
 the two naturality clauses of [Build_Adjunction'] are proved, each in a
 handful of lines through [cp_to_uniq].

 That shared landing is not asserted: [cp_copower_at_middle] and
 [cp_power_at_middle] supply the two DONORS AS TERMS at a type naming
 [cp_middle b c], so each typechecks only if that donor's target is
 [cp_middle b c] up to delta.  An [X = X] tautology would have said nothing
 here and is deliberately not what is written.  The ascriptions are also
 not vacuous through a coercion: at the SWAPPED middle [cp_middle c b] the
 copower one is refused, and the error prints the donor's real target,

 The term "copower_hom_iso_at (copower_ump J b) c" has type
 "… ≅ (J ⋔ {| carrier := b ~{ C }~> c; is_setoid := homset b c |})%power"
 while it is expected to have type "… ≅ cp_middle J c b".

 which is a plain typing mismatch -- no "cannot unify", no universe clause.

 UNIVERSES, MEASURED OFF BOTH THE BINDER AND THE BLOCK

 Reproduce with [Set Printing Universes.] and [About]; reading either alone
 gets this wrong, in both directions, and it does so here.

 Every constant is over [C : Category@{u u0 u0}] -- hom identified with
 proof by REUSING the level variable in the BINDER, with no equation in any
 block saying so.  That identification is inherited: it is [Category]'s own
 shape at every donor, and nothing here adds to it.

 [Power_Functor@{u u0 u1 u2 u3 u4 u5}] and
 [Copower_Functor@{u u0 u1 u2 u3 u4 u5 u6}] have blocks of BOUNDS ONLY --
 NO equation anywhere -- and the INDEX stays free of [C]'s hom universe:
 [Power_Functor]'s index [Type@{u3}] carries only [u3 <= u1] and
 [u3 <= u2], both against the class's own levels.  So §A is universe-free
 in the sense that matters.

 [cp_adj_iso] and [Copower_Power_Adjunction] carry FOUR equations,
 [u0 = u1], [u0 = u2], [u0 = u4] and [u0 = u5], identifying [C]'s
 hom-and-proof level with all four index slots of [HasIndexedProducts]
 and [HasIndexedCoproducts], plus the bound [u6 <= u0] on the index.
 Read as a boundary a consumer meets: at an index universe strictly
 ABOVE [C]'s hom-and-proof level, [Power_Functor], [Copower_Functor]
 and [power_fmap] are ACCEPTED while [Copower_Power_Adjunction] is
 REFUSED ("Cannot enforce ji <= ..."), pinned as probe negative 14 with
 those three as its controls.

 ★ THOSE FOUR ARE NOT CREATED BY COMPOSING, AND THE ISOLATING EXPERIMENT
 SAYS SO.  Applying [copower_hom_iso_at] to [copower_ump J b] ALONE already
 carries [u0 = u4] and [u0 = u5]; applying [power_hom_iso_at] to
 [power_ump J c] ALONE already carries [u0 = u1] and [u0 = u2]; the
 composite carries exactly their union and nothing further.  Measured by
 defining four constants -- one per donor applied alone, one pairing them
 without composing, one composing them -- and reading all four blocks.

 The CAUSE is a binder, not a block, which is why the naive measurement
 misses it: the bare donor reads
 [copower_hom_iso_at@{u u0 u1 u2 u3} : ∀ {C : Category@{u3 u u}}
 {J : Type@{u}} …] -- hom, proof AND INDEX all at the ONE level [u] -- while
 its block contains no equation at all.  Applying it at a [copower_ump]
 drawn from the CLASS, whose index slots are separate levels, turns that
 binder identification into the block equations above.  This is #321's own
 recorded [iprod_hom_iso] propagation, now localized: it is per-donor, and
 it is already present before any composition.  It is NOT claimed
 unavoidable.

 NO word-bounded [Set] occurs in the binder or the block of ANY of the
 seven constants measured ([power_fmap], [Power_Functor], [Copower_Functor],
 [power_functor_ev], [copower_functor_inj], [cp_adj_iso],
 [Copower_Power_Adjunction]).  RECORDED CORRECTION: an earlier revision
 continued "That is strictly better than the limit-shaped route:
 [power_of_limit@{u u0 u1}] reads [∀ {C : Category@{u1 Set Set}} …],
 pinning [C]'s hom AND proof to the literal [Set] in its binder.  Going
 through the CLASS ([power]/[power_ev]/[power_ump]) rather than through
 [Limit (DiscreteCat_Functor …)] avoids that pin entirely."  The
 comparison no longer holds, because the pin is gone:
 [DiscreteCat_Functor] was annotated in place at Instance/Discrete.v
 in the PR "algebraic carriers are sets" (2026-09-17), and the
 limit-shaped route now carries no literal [Set] either
 (Structure/Limit/Power.v's own universe note records the measurement).
 The class route is still preferred, but for the identification the
 limit-shaped route carries rather than for a [Set] floor: [Limit] ties
 the discrete shape's hom and proof universes to the ambient's, and the
 class imposes no such tie.

 AN ENGINEERING FINDING, RECORDED BECAUSE IT COST A COMPILE

 [rewrite] does not match a goal that DISPLAYS the pattern it is given.
 The second naturality clause of [Build_Adjunction'] presents the composite
 [fmap[Copower_Functor J] g ∘ copower_inj J x j], and under
 [Set Printing All] its implicit object arguments are MIXED: the middle
 object elaborates as [copower J x] while the codomain elaborates as
 [fobj[Copower_Functor J] y].  A lemma stated naively gets [copower J y] in
 both positions and a lemma stated with the injection ascribed to
 [b ~> fobj[Copower_Functor J] b] gets [fobj[…] x] in both, so BOTH are
 rejected with "Found no subterm matching", the second one printing an
 ascription the elaborator had already erased.  The repair is not a third
 spelling but to stop rewriting: [apply compose_respects] followed by
 [symmetry; exact (copower_functor_inj J g j)] closes it by CONVERSION,
 which does not care how the objects are spelled.  Same family as the
 [star_fmap_mor] finding recorded for Construction/Slice/Pullback.v.

 THE ONE [Defined] IS LOAD-BEARING, MEASURED BY FLIPPING IT.
 [Copower_Power_Adjunction] closed with [Qed] instead breaks
 [cp_adj_readback] outright:

 The term "eq_refl" has type
 "adj[Copower_Power_Adjunction] = adj[Copower_Power_Adjunction]"
 while it is expected to have type
 "adj[Copower_Power_Adjunction] = cp_adj_iso b c"
 (cannot unify "adj[Copower_Power_Adjunction]" and "cp_adj_iso b c").

 AS THE FILE NOW STANDS THERE ARE SEVEN [Defined]s AND SIXTY-ONE [Qed]s,
 counted over proof terminators in the code body, and EXACTLY THREE of the
 seven are load-bearing -- measured by flipping each ALONE to [Qed] and
 recompiling: [Copower_Power_Adjunction] (above), [cp_pa_adj] and
 [ex1_pa_adj], each of which an [eq_refl] readback or a mate computation
 reduces through.  The other four -- [power_of_weighted],
 [copower_of_weighted], [One_iprod_ump] and [One_icoprod_ump] -- compile as
 [Qed] with everything else intact and are [Defined] by the convention that
 a constant producing DATA stays transparent.  All THREE load-bearing ones
 are PINNED in the probe by an opaque [Qed]-closed clone whose readback is
 refuted (negatives 5, 12 and 13), so the flipping measurement is guarded;
 the four that are not load-bearing stay measured only, "flipping this
 changes nothing" being a counterfactual no refutation command can
 express.

 STATUS OF §A-§B ALONE, AS FIRST LANDED: axiom-free, 25/25 constants
 reporting "Closed under the global context", each queried by fully
 qualified name.  (The whole-file figure is 147/147; see the COST section
 below.)  The criterion for 25 is
 every [Definition] and [Parameter] head of
 [Print Module Category.Structure.Limit.Power.Adjunction] on its
 whitespace-flattened output -- that command wraps its module head across
 three lines, so a line-anchored sweep of it needs flattening first -- which
 is 22 source-declared heads plus the THREE [Program] obligations of
 [Power_Functor], invisible to a [.glob] sweep (the [.glob] carries exactly
 22 [def]/[prf] entries).  The file declares no [Record], [Class] or
 [Inductive], so there is no unlisted [Build_*].  ([Print Module] renders an
 opaque constant as [Parameter]; the eight so shown here are the three
 obligations and five ordinary [Qed] lemmas, not axioms, which is what the
 audit above checks.)  All 25 names are free under the criterion stated in
 the prior-art paragraph -- ZERO collisions across all 25, swept one name
 at a time.  All 25 are registered in the Makefile's
 [print-assumptions] gate, FULLY QUALIFIED: the three [Program] obligations
 are NOT reachable by their bare names in that target's single shared scope
 (measured -- the gate stops with "The reference
 Power_Functor_obligation_1 was not found in the current environment"), so
 the whole block is qualified rather than only the three, following the
 [Powerset.Universal] precedent already in that file.

 [make todo] grew, FOR §A-§B AS FIRST LANDED, by exactly ONE line, and it
 was PROSE: the engineering paragraph above used an ordinary English verb
 that the target's case-insensitive pattern matches on its first
 alternative.  That verb has since been replaced, so this file now
 contributes ZERO hits: it carries no probe command and no ticket marker
 of any kind, and the paragraph you are reading is written so as not to
 add one.
 ────────────────────────────────────────────────────────────────────────

 C. THE WEIGHTED-LIMIT COMPARISON, AND THAT IT IS AN AGREEMENT

 Structure/Limit/Weighted.v presents a limit by a WEIGHT.  The power is the
 weighted limit over the TERMINAL SHAPE [_1] whose WEIGHT picks out the
 index SET and whose DIAGRAM is constant at [b].  [conical_weighted]
 (Weighted.v) is NOT this theorem and is not cited as though it were:
 it is the CONSTANT weight over an ARBITRARY shape, i.e. weighted ⇒
 ordinary limit, which is the conical case and says nothing about powers.

 BOTH DIRECTIONS ARE PROVED, which is what makes this an agreement of the
 two presentations rather than one inhabitant of a class.
 [power_WeightedLimit] puts the CHOSEN power in the class, and
 [power_of_weighted] runs the other way: for an ARBITRARY weighted limit of
 that weight and that diagram, [wlim_obj] IS a power, with [wpow_ev] --
 the identity transported back across [wlim_iso] -- as its evaluations.
 The converse assumes NOTHING about the ambient category, not even that it
 has powers.  [copower_of_weighted] is the dual, and [WeightedColimit] is
 the class it consumes.  The whole of [wlim_natural] is spent in exactly
 one lemma per side ([wpow_from_is_precompose], [wcop_from_is_postcompose]).

 THE COPOWER HALF IS BUILT DIRECTLY OVER [1^op] AND IS NOT AN
 OP-INSTANTIATION, AND BOTH REASONS ARE PINNED.  A colimit weight is
 contravariant on the shape, so [WeightedColimit W F] puts [W] over [J^op];
 [Opposite _1 = _1] is refuted at [eq_refl] (CONVERSION), and
 [Opposite_Functor (copower_diagram b) = @power_diagram (C^op) b] is
 refuted too (TYPING -- the error reports the SHAPES, [1 ⟶ C^op] against
 [1^op ⟶ C^op]).  So the power half cannot simply be read at [C^op]: this
 is where #321's op-trick, which makes §A's copower functor entirely free,
 does not carry.

 THE WEIGHT IS DISCRETE, AND THAT IS FORCED RATHER THAN CONVENIENT: the
 evaluations of a power are indexed by ELEMENTS, so the backward leg's
 respectfulness would have to derive [ev j ≈ ev j'] from [j ≈ j'].
 [index_setoid J] therefore uses [eq_Setoid], and both [wpow_cone] and
 [wcop_cocone] get respectfulness for free from that.

 THE ROUND TRIP RETURNS THE CHOSEN DATA WITH ONE IDENTITY RESIDUE PER SIDE,
 EXHIBITED RATHER THAN DESCRIBED.  [wrt_ev_residue] and [wrt_inj_residue]
 close at [eq_refl] on [power_ev J b j ∘ id] and [id ∘ copower_inj J b j];
 the strict forms are refuted and pinned, and [wrt_ev_equiv]/[wrt_inj_equiv]
 are the [≈] statements, one [id_right] and one [id_left].

 ★ AND THE TWO DIRECTIONS COST DIFFERENT UNIVERSES, WHICH IS THE
 INTERESTING MEASUREMENT HERE.  [power_WeightedLimit] carries the block
 equation [u0 = u3] -- [C]'s hom-and-proof level IDENTIFIED with the INDEX
 universe -- and [copower_WeightedColimit] carries [u0 = u4]; but
 [power_of_weighted] and [copower_of_weighted] carry NO EQUATION AT ALL,
 their index universe merely BOUNDED.  Where the identification enters is
 LOCALIZED by probe rather than attributed: under [Constraint ch < ji],
 [power], [power_ev], [Power_Functor], [index_setoid], [power_weight],
 [power_diagram] and even [HomDiagram cu (power_diagram bu)] are ALL
 accepted, and [WeightedLimit (power_weight Ju) (power_diagram bu)] is
 refused -- so it is putting the weight and the hom-diagram into ONE [Sets]
 that forces it, not the weight and not the diagram.  It is NOT claimed
 unavoidable, and it is inherent to a [Sets]-weighted formulation with a
 bare-[Type] weight rather than to anything #321 does.

 ────────────────────────────────────────────────────────────────────────

 D0. THE COPOWER BIFUNCTOR, WHICH BOTH PARAMETER READINGS SHARE

 [Copower_Bifunctor : C ∏ Coq ⟶ C] makes [(b, J) ↦ J · b] functorial in
 both arguments at once.  §D fixes the OBJECT and varies the index; §E
 fixes the INDEX and varies the object.  They are two parametrizations of
 this ONE bifunctor, differing only in which slot of
 [ParametrizedAdjunction]'s [X ∏ P ⟶ A] the parameter occupies, and §D
 reaches its own by [Copower_Bifunctor ◯ Swap] rather than by building a
 second bifunctor.

 ★ THE INDEX CATEGORY IS [Coq], AND THAT IS FORCED, NOT PREFERRED.  The
 copower injections are indexed by ELEMENTS, so [fmap_respects] must derive
 [copower_inj (f j) ≈ copower_inj (f' j)] from [f ≈ f'], which needs
 [f j = f' j] at LEIBNIZ equality.  [Coq]'s hom-setoid is pointwise
 Leibniz and supplies it.  [Sets]' does not, and the probe carries an
 AXIOM-FREE COUNTERMODEL -- [sets_index_respects_absurd], over a
 two-element setoid whose [≈] is the total relation -- refuting
 [SetsIndexRespects], the [fmap_respects] obligation of the CANONICAL
 arrow action (the copower mediator of the injections, which is what any
 arrow action commuting with the injections must be).  Read it at that
 scope: THAT action over [Sets] is refuted outright rather than merely
 recorded as a proof that does not go through; no other arrow action with
 the same object action is investigated, and none is claimed refuted.
 #321's own Power/Hom.v anticipates the same
 fact for its bijections -- its header records that the index of
 [HasIndexedCoproducts] is a bare [Type], and that no claim is made about
 a coarser setoid on the index -- and this is that fact, refuted.

 ────────────────────────────────────────────────────────────────────────

 D1. MAC LANE §IV.7 EXERCISE 1, UNRESTRICTED

 [Copower_Bifunctor_Iso J : CopLeft J ≅ CopRight J] in
 [[C^op ∏ C, Sets]] is the exercise's displayed isomorphism -- in its
 CORRECTED form [C(J · a, c) ≅ Set(J, C(a,c))], per the variance argument
 above -- upgraded from a family of bijections to an isomorphism of
 BIFUNCTORS, which is what "natural in the parameter a" asks for.  It takes
 no hypothesis beyond [HasIndexedCoproducts].

 The right-hand side is pleasing and is not a coincidence:
 [CopRight J] is [@Power_Functor Sets Sets_HasIndexedProducts J ◯ Hom C],
 so Mac Lane's [Set(J, −)] is §A's OWN power functor read at [Sets], and
 the whole right-hand side is that functor applied to the hom-bifunctor.
 Both object actions read back at [eq_refl].

 The pointwise-invertible transformation is upgraded through #369's
 [componentwise_iso] rather than by building the inverse transformation and
 its naturality by hand.  That donor costs a MARGINAL 10 modules (measured
 by dropping the [Require]: 111 → 101); it is taken because building the
 inverse by hand would fork exactly the general lemma that file exists to
 supply.

 ────────────────────────────────────────────────────────────────────────

 D2. THE SAME EXERCISE PACKAGED, AND THE PUNCHLINE

 [Copower_Object_ParametrizedAdjunction : ParametrizedAdjunction
 Ex1_Bifunctor] is #396's record at the object parameter, and #396's
 Theorem 3 then assembles the right adjoints into
 [MacLane_Ex1_hom_bifunctor : C^op ∏ C ⟶ Coq] -- WHICH IS THE HOM-FUNCTOR,
 which is the point of the exercise.  That identification is delivered at
 two strengths and neither is asserted: [ex1_hom_bifunctor_obj] closes at
 [eq_refl] on the OBJECT action, [fobj (a,c) = (a ~{C}~> c)], and
 [ex1_hom_bifunctor_fmap] gives the ARROW action POINTWISE as
 [g ↦ k ∘ g ∘ unop h], through [ex1_param_mate_precomp], which reads the
 parameter mate off [conj_mate]'s own component formula rather than
 recomputing conjugacy.

 THE PACKAGING NEEDS A HYPOTHESIS AND IT IS AN EXPLICIT ARGUMENT.  The
 right adjoint [C(a,−)] must land in the SAME index category the copower
 is indexed by, and there the two demands pull against each other: the
 copower wants LEIBNIZ equality on the index (D0), the hom-functor wants
 [C]'s own [≈].  [HomAllStrict C] is exactly where they coincide.

 ★ IT IS NOT A NEW HYPOTHESIS AND IS NOT REDECLARED.
 Construction/Comma/Special.v already carries [HomStrict], at a FIXED
 pair of objects, for its own [Full] criterion; that name is CONSUMED here
 and quantified over all objects ([HomAllStrict C := ∀ x y, HomStrict x y])
 at a marginal cost of 4 modules.  The collision was found by sweeping this
 file's own declared names, and consuming the donor is what resolves it:
 redeclaring [HomStrict] would have put two different predicates under one
 name in the [print-assumptions] target's single shared scope.  That donor
 also supplies [Blur_HomStrict_absurd], a compiled category where the
 per-hom-set form is refutable, which is the boundary of the hypothesis.

 ★ AND THE HYPOTHESIS IS INHABITED IN TREE, WHICH IS BETTER THAN THE
 OBVIOUS GUESS.  [_1]'s hom-setoid IS [Morphism_equality] (Instance/One.v),
 so [One_HomAllStrict] is the identity implication, and [_1] has all
 indexed products and coproducts trivially ([One_HasIndexedProducts] and
 [One_HasIndexedCoproducts] are three-line record literals over an
 eight-line universal property apiece, every step [one_hom_eq]) -- so
 [One_Ex1_ParametrizedAdjunction] is a genuine in-tree model.  Read it at
 its strength: it exercises the HYPOTHESES and the assembly, not the
 conclusion, everything in [1] collapsing to [ttt].  No non-degenerate
 model is exhibited and none is claimed.

 ────────────────────────────────────────────────────────────────────────

 E. THE ISSUE'S OWN ITEM 4: THE INDEX SET AS THE PARAMETER

 Here the parameter slot holds the INDEX and the varying argument is the
 object.  The right adjoints ARE §A's power functors ON THE NOSE --
 [pa_right Copower_ParametrizedAdjunction J = Power_Functor J] by
 [eq_refl] -- while the partial functors agree with §A's copower functors
 on BOTH ACTIONS at [eq_refl] ([copower_bifunctor_partial_obj],
 [copower_bifunctor_partial_fmap]) but not as RECORDS, which is the next
 paragraph.  Also [pa_adj]'s own hom-set isomorphism IS §B's [cp_adj_iso] by
 [eq_refl] ([pa_adj_iso_is_cp_adj_iso]) -- so §E does not fork §B's
 bijection.  #396's Theorem 3 then assembles
 [Power_Bifunctor : Coq^op ∏ C ⟶ C], contravariant in the index, with
 [fobj (J, b) = power J b] at [eq_refl].

 ★ THE §B ISOMORPHISM ASCRIBES AT THE PARTIAL FUNCTOR; THE §B ADJUNCTION
 DOES NOT, AND THE ERROR SAYS WHY.  [fobj[Partial_l Copower_Bifunctor J] b]
 and [fobj[Copower_Functor J] b] agree at [eq_refl], so [cp_adj_iso J b c]
 ascribes at the partial functor's type with nothing inserted; but
 [Adjunction] is indexed by the functor RECORD rather than by its two
 actions, so [Copower_Power_Adjunction J] is REFUSED there, the error
 naming the offending field:

 (cannot unify "λ (x y : obj[C^op^op]) (f g : x ~{ C^op^op }~> y),
 fmap_respects y x f g"
 and "Partial.Partial_l_obligation_1 C Coq C Copower_Bifunctor J").

 Both facts are pinned.  [cp_pa_adj] therefore rebuilds the record -- but
 over the SAME isomorphism and the same two uniqueness lemmas, so no
 universal property is re-derived.

 THE CONJUGACY IS CONSUMED, NOT RECOMPUTED.  [copower_reindex h] is #396's
 [param_transform] and [power_reindex h] is its [pa_param_mate], which
 [power_reindex_is_conj_mate] records at [eq_refl] as #394's [conj_mate];
 [power_reindex_conjugate] is [pa_natural_p] ascribed at #394's
 [Conjugate], the ascription being the whole proof because
 [pa_square_is_Conjugate] identifies the two on the nose; and
 [power_reindex_universal] is [pa_param_mate_universal], so the mate is the
 UNIQUE conjugate and not merely one.  Functoriality in the index is
 [pa_param_mate_id]/[pa_param_mate_comp] and [param_transform_id]/[_comp],
 cited by name.  What is proved here rather than cited is the elementary
 reading of each: [copower_reindex_inj] and [power_reindex_ev]
 ([ev_{j'} ∘ τ_b ≈ ev_{h j'}]), the second from the mate's component
 formula plus [cp_pa_counit_inj].

 ★ §D AND §E ARE DIFFERENT STATEMENTS AND NEITHER DISCHARGES THE OTHER.
 Mac Lane's Ex 1 varies the OBJECT; the issue's item 4 varies the INDEX,
 which is the variable its own item 3 (= §IV.2 Ex 12, §B above) holds
 FIXED.  Both are true and both are here, labelled.

 ────────────────────────────────────────────────────────────────────────

 UNIVERSES OF §C-§E, MEASURED OFF BOTH BINDER AND BLOCK

 All eighteen measured constants are over [C : Category@{u u0 u0}] -- hom
 identified with proof by REUSING the level variable in the BINDER, with no
 block equation saying so -- and NO word-bounded [Set] occurs in the binder
 or the block of ANY of them.  The block equations are:

 [power_WeightedLimit]                    u0 = u3        (index)
 [copower_WeightedColimit]                u0 = u4        (index)
 [power_of_weighted]                      none
 [copower_of_weighted]                    none
 [Copower_Bifunctor], [CopLeft], [CopRight], [HomCoq],
 [copower_reindex]                      none
 [Copower_Bifunctor_Iso]                  u0 = u2, u0 = u3
 [Copower_Object_ParametrizedAdjunction], [ex1_pa_adj],
 [MacLane_Ex1_hom_bifunctor]            none
 [Copower_ParametrizedAdjunction], [Power_Bifunctor], [cp_pa_adj],
 [power_reindex], [power_reindex_conjugate]
 u0 = u1, u0 = u2,
 u0 = u4, u0 = u5

 ★ SO THE OBJECT-PARAMETRIZED READING IS UNIVERSE-FREER THAN THE
 INDEX-PARAMETRIZED ONE, AND THE REASON IS WHICH BIJECTION EACH USES.  §D2
 builds its hom-set bijection DIRECTLY from the copower's universal
 property, in [Coq], and carries no equation at all; §E composes #321's two
 [_at] bijections and inherits exactly the four equations localized in the
 §B paragraph above.  §D1 sits between them at two, which is CONSISTENT
 with only the COPRODUCT class being involved there -- but that is an
 attribution, not an isolation: no experiment removes one donor and shows
 one equation vanish.  None of this is claimed unavoidable.

 ────────────────────────────────────────────────────────────────────────

 COST, AND WHAT IT BUYS

 Closure 111 modules (transitive in-project [.vo] dependencies over
 [.Makefile.coq.d], EXCLUDING the file itself), up from the 38 of §A-§B.
 Measured by DROPPING each [Require] one at a time: of the twelve added
 for §C-§E, [Adjunction/Parameter] 28, [Instance/Coq] 13,
 [Instance/Fun/Morphisms] 10, [Construction/Comma/Special] 4,
 [Structure/Limit/Weighted] 1, and the other SEVEN ZERO apiece; of the
 §A-§B [Require]s, [Structure/Limit/Power/Hom] costs 2.  Those marginals
 do not add to 111 - 38 and are not meant to: a drop-one marginal ignores
 what the survivors share.  Nothing in the tree Requires this file, so
 none of that lands on an existing consumer.

 147/147 CONSTANTS CLOSED UNDER THE GLOBAL CONTEXT, each queried by fully
 qualified name, ZERO [Axioms:] lines.  The criterion for 147 is every
 [Definition] and [Parameter] head of
 [Print Module Category.Structure.Limit.Power.Adjunction] on its
 WHITESPACE-FLATTENED output (the command wraps its module head): 86
 [Definition] plus 61 [Parameter].  The [.glob] carries 110 (86 [def] + 24
 [prf]), so THIRTY-SEVEN of the 61 opaque constants are [Program]
 obligations that no source or [.glob] sweep sees, and 147 - 110 = 37
 checks that.  The file declares no [Record], [Class] or [Inductive], so
 there is no unlisted [Build_*].  All 147 are in the [print-assumptions]
 gate, FULLY QUALIFIED, which took block 5 of that target from 25.5 to
 38.9 KiB, measured on the raw text with its [@{]/[}] delimiters (the
 largest block in the file is 73.6).

 ZERO COLLISIONS across all 147 names, swept ONE NAME AT A TIME under the
 criterion of the prior-art paragraph WIDENED to exclude this file's own
 probe as well (which names 27 of them as controls, by design):

 rg -l -w -e '<token>' -g '*.v' \
 -g '!Structure/Limit/Power/Adjunction.v' \
 -g '!Test/ProbeCopower366.v' .

 instrument-checked at [power] = 42 files and [Monoid] = 91, both under
 that same exclusion (unexcluded, [Monoid] is 92, this file mentioning
 it).  TWO REAL
 COLLISIONS were found before landing and BOTH were resolved by consuming
 the donor rather than by renaming: [HomStrict] and [One_HomStrict] are
 Construction/Comma/Special.v.

 Test/ProbeCopower366.v mirrors this file's full [Require] list and carries
 FIFTEEN refutation commands = 1 instrument check + 14 negatives of THREE
 KINDS told apart by the error TEXT: 9 CONVERSION (each ends "cannot unify"
 between two terms of one type), 3 TYPING (a plain "has type ... expected",
 with NO "cannot unify" and no universe clause), 2 FORMABILITY (each ends
 in a universe clause).  Each was stripped ONE AT A TIME, compiled ALONE,
 and produced exactly one [Error] whose whole text was read.  NEGATIVES 2
 AND 3 ARE THE SAME EQUATION AT TWO SPELLINGS AND COME OUT AS DIFFERENT
 KINDS -- with BOTH sides' implicits written out, [@Copower_Functor C HC J]
 against [@Power_Functor (C^op) HC J] is refused at the STATEMENT, the
 two constants not sharing a type and the error carrying no "cannot
 unify";
 against [Power_Functor J] at [C] they do share one and there is -- which
 is why a negative's kind is read off its error and never guessed from its
 statement.  A FALSE GUARD WAS CAUGHT THERE AND IS RECORDED IN THE PROBE:
 negative 2 as first written, [Copower_Functor J = @Power_Functor (C^op)
 HC J], left the left side's category IMPLICIT, and the elaborator
 re-solved it as [C^op] (leaving its coproduct instance an unresolved
 evar) so that the two sides DID share a type; the error then fired at
 [eq_refl], refuting negative 3's fact restated at [C^op] and not the type
 mismatch the comment claimed.  The tell is general: a negative whose
 claimed reason is "the two sides do not share a type" but whose error
 fires at [eq_refl] elaborated its statement and is measuring something
 else -- the [obj[?C]] family Test/ProbeFiniteProducts335.v records.
 Negatives 12 and 13 pin the two further load-bearing [Defined]s
 ([cp_pa_adj], [ex1_pa_adj]) by the opaque-clone technique negative 5 uses
 for [Copower_Power_Adjunction]; negative 14 pins the index-universe
 boundary recorded in the §B universe paragraph.  Every constant a
 negative names also appears outside every refutation; the only tokens
 confined to one are the refuted commands' own names, which never enter
 the environment, and the instrument's deliberately absent one.
 Rename-simulated 15/15 -- the thirteen target constants the negatives
 name plus the two reached only through their clones -- with each rename
 applied to THIS FILE ONLY (a whole-tree rename is a no-op by
 construction), every break landing on a [Check] control line and none
 inside a refutation.

 [make todo] grows by 29, ALL of them in the probe (its 15 refutation
 commands and 14 prose lines matching that target's pattern); this file
 contributes NOTHING, the one prose line §A-§B first carried having been
 reworded.

 ────────────────────────────────────────────────────────────────────────

 NOT DELIVERED

 - No [Set]-indexed reading of anything: the index category is [Coq]
 throughout, and the CANONICAL arrow action over [Sets] is REFUTED
 (probe §H) rather than deferred; no other arrow action over [Sets] is
 investigated.  Whether some full subcategory of [Sets] on discrete
 setoids would serve is not investigated either; no such subcategory
 exists in tree.
 - No NON-DEGENERATE model of [HomAllStrict].  [_1] is the only witness and
 it collapses everything; in particular nothing here exhibits a category
 with genuinely many arrows satisfying it, and no impossibility is
 claimed either.
 - §D1 and §D2 are NOT RELATED to each other.  Nothing states that
 [Copower_Bifunctor_Iso] is the [Sets]-valued shadow of
 [MacLane_Ex1_hom_bifunctor], and the two land in different categories
 ([Sets] against [Coq]), so a comparison would need a functor between
 them that is not built.
 - No naturality of the §C comparison in [J] or in [b], and no uniqueness
 for [wlim_obj] (the class has none), so §C is an agreement of the two
 presentations at fixed data and not an equivalence of structures.
 - No [WeightedLimit] statement for the general indexed product, only for
 the constant family that a power is.
 - No 2-categorical reading, nothing about [Adjunction/Map.v]'s maps of
 adjunctions, and no relation between §E's conjugate pairs and
 [Instance/Adj.v]'s category of adjunctions.
 - Nothing is registered as an [Instance]: [One_HasIndexedProducts] and
 [One_HasIndexedCoproducts] are plain [Definition]s deliberately, so that
 resolution is not offered a degenerate model of either class.
 - No concrete witness at a named category for §B, §D1 or §E; the only
 concrete instantiation anywhere in the file is [_1] for §D2. 

 --------
 nLab:       https://ncatlab.org/nlab/show/copower 
 nLab:       https://ncatlab.org/nlab/show/power 
 nLab:       https://ncatlab.org/nlab/show/adjoint+functor 

 来源，按位置引用，均从渲染页面读取（印刷页码和 PDF 页码相差恒定 +9，经验证）：

 - Mac Lane，《Working Mathematician 的范畴》，第 2 版
 （Springer GTM 5），第 IV.2 节，第 12 题，印刷页 90
 （PDF 页 99），条目 [maclane:IV.2:ex12]，逐字原文：

 “12. 如果 X 是一个集合且 C 是一个具有幂和余幂的范畴，
 证明余幂 c ↦ X · c 是幂 c ↦ c^X 的左伴随。”

 这就是本文件存在的定理，而
 [Copower_Power_Adjunction] 是它的名称。

 - Mac Lane，同书，第 IV.7 节，第 1 题，印刷页 102
 （PDF 页 111），条目 [maclane:IV.7:ex1]，逐字按印刷原文：1. 将 C(X · a, c) ≅ Set(X, C(c, a)) 这个关于 C 中 copowers X · a 的定义理解为带参数 a 的伴随。 

 请参见下面的印刷错误说明。在本节文件中没有内容能够完成习题 1；引用它是因为方差论证决定了参数部分必须指出的内容。

 ★ §IV.7 第 1 题的印刷版本方差是错误的。这是印刷错误，而非 OCR 故障：页面以 400 dpi 读取，[pdftotext] 层确认，打印为“Set(X, C(c, a))”。这不可能是正确含义的原因是方差计算问题，而不是偏好问题：

 左边  C(X·a, c)       在 c 上是协变的
 右边  Set(X, C(a, c))  在 c 上是协变的   <- 一致
 右边  Set(X, C(c, a))  在 c 上是逆变的  <- 如印刷所示[c] 的协变函子和逆变函子在 [c] 中不能自然同构。数学上，[a] 的 X 重共幂的映射 OUT 是 [a → c] 的 X 索引族映射，也就是 [Set(X, C(a,c))]。因此正确的形式是 [C(X · a, c) ≅ Set(X, C(a,c))]，而这正是 Structure/Limit/Power/Hom.v 的 [copower_hom_iso] 已经证明的——[copower_hom_functor J b] 是 [c ↦ ∏_J C(b,c)]，协变的，恰如方差计数所要求的。打印形式在这里公开，而不是复印，也不是默默“修正”。★ 该期刊和书籍对不同的变量进行参数化。上面的示例 12 固定了集合 X 并改变对象；示例 1 不固定任何内容，并要求求双函子 [(X, a) ↦ X · a]，可读作带参数 [a] 的伴随关系，其组装的右伴随是 HOM-函子。该期刊自身的第 4 项则要求将索引集合作为参数——它的第 3 项（= 示例 12）保持固定。两种解读都是正确的，且互不蕴涵；本节提供固定 [J] 的示例 12。

 前人工作——该期刊的“当前状态”已过时，这里给出标准。

 标准，仅陈述一次，并用于下面的每一个计数：“在任何 [.v] 文件中（除了本文件，包含注释）出现的任何完整单词”，如下重现rg -l -w -e '<token>' -g '*.v' \
 -g '!Structure/Limit/Power/Adjunction.v' .问题 #366 说：“缺失。搜索 [copower]、[cotensor] 和 [tensoring] 没有结果。” 对 [copower] 来说这是错误的，它在基础提交（本段中的每个计数都取自此处，在这个文件及其探针存在之前）中出现在三个文件中——Structure/Limit/Power.v（361 行）、Structure/Limit/Power/Hom.v（548 行）和 Test/ProbePower.v —— 都由问题 #321 提供，并且该问题“建议”的模块路径 Structure/Limit/Power.v 已经被它使用。真正缺失的是函子：[Power_Functor]、[Copower_Functor]、[power_fmap] 和 [copower_fmap] 每个都返回零文件，因此对象变量中的函子性确实是新的。该工具会区分：[power] 本身返回 42 个文件，[Monoid] 返回 91 个文件。(在 HEAD，排除只有这个文件，探针会把 [copower] 和 [power] 各加一，并在四个函子名称中加一个到三个；因此下面的碰撞扫描也排除了该探针。)

 因此，对该问题的 QA 修正用“消耗，不重建”取代了前三个工作项，而这个文件消耗了：#321 的 [power]、[copower]、[power_ev]、[copower_inj]、[power_ump]、[copower_ump]、[power_desc]、[copower_desc]，以及——为了恰当的陪集——其两个已证明的表征双射 [power_hom_iso_at] 和 [copower_hom_iso_at]。下面没有重新推导任何普遍性质。

 为什么这是一个新文件而不是扩展——经过衡量，而不是优选Structure/Limit/Power.v 不能承载附加：这将是一个依赖循环，而不仅仅是一个成本。Structure/Limit/Power/Hom.v 需要 Structure/Limit/Power.vo（在 .Makefile.coq.d 的 [Structure/Limit/Power/Hom.vo :] 规则中可见），因此 Power.v 不能再依赖 Power/Hom.v，而这个文件组合的两个 [_at] 双射存在于 Power/Hom.v 中。Structure/Limit/Power/Hom.v 本可以承载它——Theory/Adjunction 在那里正好是一个模块的边际成本——但那会把 Theory/Adjunction 放在该文件唯一的现有使用者 Test/ProbePower.v 之后（测量结果：它是代码树中唯一需要 Power/Hom 的 [.v] 文件），并且会将表征同构层与伴随层混合。对于 #366 的其余部分也没有稳定的边际：Adjunction/Parameter.v，其参数半部分需要，在同一基础上是边际的四十六。一个同级文件不会让任何现有文件多出负担，因为没有任何文件需要它。闭包，按传递的项目内 [.vo] 依赖计算，不包括文件本身，在 .Makefile.coq.d: Structure/Limit/Power/Hom.v 上为 36，而该文件为 38，新增的两个模块分别是 Power/Hom.v 本身和 Theory/Adjunction.v。Adjunction/GAFT.v 为 42，未做修改。

 这里交付的内容

 [Power_Functor J : C ⟶ C]，即自函子 [b ↦ J ⋔ b]，所有三个函子律均由 [power_desc] 的唯一性条款证明——这是该问题的第 2 项，以前没有任何相关先例。[Copower_Functor J : C ⟶ C] 不花费任何东西，而这正是 #321 设计中的 op-trick 完全发挥作用的地方。[copower] 从定义上就是 [@power (C^op)]，所以 [Copower_Functor J := Opposite_Functor (@Power_Functor (C^op) HC J)] 不需要任何义务、策略或证明文本：Functor/Opposite.v 的 [Opposite_Functor] 是一个普通的 [Definition]，它将所有三个规律字段保持不变。四个 [eq_refl] 的回读显示了它带来的好处——对象操作是 [copower J b]，箭头操作是 op-power 的 [power_fmap]，双重对立精确返回了 op-power functor，箭头操作是 [copower_desc] 生成的中介。  

 两个反证，按严格优先顺序测量，附带原文错误，以便探针可以识别它们。两者都单独编译，其他部分已剥离。(1) 转换。一个手工构建的直接共幂函子 —— 对象作用 [b ↦ copower J b]，箭头作用 [copower_desc] 中介器，三个义务 —— 在 [eq_refl] 的两个数据字段上与 [Copower_Functor J] 一致，但整个记录被拒绝：

 术语“eq_refl”的类型是
 “Copower_Functor_direct = Copower_Functor_direct”，
 而期望的类型是
 “Copower_Functor_direct = Copower_Functor J”
 （无法统一“Copower_Functor_direct”和“Copower_Functor J”）。

 两个数据字段一致说明采取简便方法并没有丢失任何内容；记录不同的是三个 [Program] 重建的法则字段，就像此树的其他地方一样。(2) 类型检查，并且它是另一种类型，通过错误文本而不是标签来区分。 将双方的隐式参数都写出来时，[@Copower_Functor C HC J = @Power_Functor (C^op) HC J := eq_refl] 在语句处被拒绝，在检查任何 [eq_refl] 之前，这两个常量不共享类型（[C ⟶ C] 对 [C^op ⟶ C^op]）；错误不包含“无法统一”条款：

 “Power_Functor J”项的类型是“C^op ⟶ C^op”，而预期的类型是“C ⟶ C”。拼写很重要。写作 [Copower_Functor J = @Power_Functor (C^op) HC J] 时，左侧的范畴是隐含的，这个声明进行了详细说明——详述器重新解析该范畴为 [C^op] ，留下了余积实例为未解决的 evar —— 而错误在 [eq_refl] 处触发，它是负三在 [C^op] 的事实，而根本不是类型不匹配；这段的初稿正是引用了该错误，探针的负二记录了这个事件。同样的等式在 [C] （[Copower_Functor J = Power_Functor J]）处是负三，并且它是转换的：两边共享 [C ⟶ C]，错误最终出现在 [cannot unify "Copower_Functor J" and "Power_Functor J"] 。

 因此 [Copower_Functor J] 是 op-power 函子上的 [Opposite_Functor]，并不是该函子；准确成立的是双重对偶，即下方的 [copower_functor_double_op]。[Copower_Power_Adjunction J : Copower_Functor J ⊣ Power_Functor J] 是 Ex 12。它的同态集同构是 #321 的两个双射的复合，而不是从泛性质新推导出的，这里“使用，不重建”的意思就是如此，也是本问题中审查者提出的检查文件没有分叉 API 的问题。这个复合是有良好基础的，因为两个双射在右侧完全相同：[copower_hom_iso_at (copower_ump J b) c] 和 [power_hom_iso_at (power_ump J c) b] 都映射到 [Sets] 次方的 [J ⋔ C(b,c)]，下面写作 [cp_middle b c]，因此它们可以无比较映射地复合，而且 [cp_adj_iso] 是一个没有策略的 [:=]。只有 [Build_Adjunction'] 的两个自然性条款被证明，每个条款通过 [cp_to_uniq] 用几行完成。该共享着陆未被断言：[cp_copower_at_middle] 和 [cp_power_at_middle] 在类型命名 [cp_middle b c] 下提供两个捐赠者作为项，因此只有当该捐赠者的目标在 delta 内为 [cp_middle b c] 时，每个才会类型检查。[X = X] 的同义反复在此不会说任何东西，并且故意未被写出。通过强制转换，这些指派也不是空的：在 SWAPPED 中间 [cp_middle c b]，copower 一个被拒绝，错误会打印捐赠者的实际目标。  

 术语“copower_hom_iso_at (copower_ump J b) c”的类型为  
 “… ≅ (J ⋔ {| carrier := b ~{ C }~> c; is_setoid := homset b c |})%power”，  
 而预期类型为 “… ≅ cp_middle J c b”。  

 这是一个明显的类型不匹配——没有“无法统一”，也没有宇宙条款。  

 宇宙，基于绑定器和区块两者测量。用 [Set Printing Universes.] 和 [About] 重现；单独读取任意一个都会出错，无论方向如何，这里也是如此。

 每个常量都是在 [C : Category@{u u0 u0}] 上——同构通过在 BINDER 中重复使用级别变量来证明，在任何块中都没有方程表明如此。这种同一性是继承的：它是 [Category] 在每个捐赠者处自身的形状，这里没有任何内容会增加它。

 [Power_Functor@{u u0 u1 u2 u3 u4 u5}] 和 [Copower_Functor@{u u0 u1 u2 u3 u4 u5 u6}] 只有 BOUNDS 块——
 没有任何方程——索引保持不受 [C] 的同构宇宙约束：
 [Power_Functor] 的索引 [Type@{u3}] 只携带 [u3 <= u1] 和 [u3 <= u2]，两者都与类自身的级别相对。因此 §A 在重要意义上是无宇宙的。[cp_adj_iso] 和 [Copower_Power_Adjunction] 载有四个方程，[u0 = u1]、[u0 = u2]、[u0 = u4] 和 [u0 = u5]，标识 [C] 的同质与证明等级与 [HasIndexedProducts] 和 [HasIndexedCoproducts] 的所有四个索引槽，以及索引上的约束 [u6 <= u0]。作为边界读取消费者所遇到的情况：在严格高于 [C] 的同质与证明等级的索引宇宙中，[Power_Functor]、[Copower_Functor] 和 [power_fmap] 被接受，而 [Copower_Power_Adjunction] 被拒绝（“无法强制 ji <= ...”），作为探针负 14 固定，同时将那三者作为其控制对象。★ 那四个不是通过组合创造的，孤立实验也说明了这一点。仅将 [copower_hom_iso_at] 应用于 [copower_ump J b] 就已经包含了 [u0 = u4] 和 [u0 = u5]；仅将 [power_hom_iso_at] 应用于 [power_ump J c] 就已经包含了 [u0 = u1] 和 [u0 = u2]；组合体恰好包含它们的并集而没有额外的内容。通过定义四个常数来测量——每个捐赠者单独应用一个，一个不组合地配对它们，一个组合它们——并读取所有四个块。原因是一个绑定器，而不是一个块，这就是为什么简单测量会遗漏它：裸露的 donor 显示为
 [copower_hom_iso_at@{u u0 u1 u2 u3} : ∀ {C : Category@{u3 u u}}
 {J : Type@{u}} …] -- hom、证明 AND 索引都在同一个层级 [u] -- 而它的块根本不包含任何方程。将它应用于来自 CLASS 的 [copower_ump]，其索引槽在不同层级，会将该绑定器识别转换为上面的块方程。这是 #321 自身记录的 [iprod_hom_iso] 传播，现在是局部化的：它是按 donor 的，并且在任何组合之前已经存在。它并不被认为是不可避免的。在所测量的七个常数（[power_fmap]、[Power_Functor]、[Copower_Functor]、[power_functor_ev]、[copower_functor_inj]、[cp_adj_iso]、[Copower_Power_Adjunction]）的粘结剂或块中，没有出现以单词为界的[Set]。记录的更正：之前的修订继续写道“这严格优于极限形路线：[power_of_limit@{u u0 u1}]读取[∀ {C : Category@{u1 Set Set}} …]，将[C]的同源和证明固定在其粘结剂中的文字[Set]上。”通过 CLASS（[power] / [power_ev] / [power_ump]）而不是通过 [Limit (DiscreteCat_Functor …)] 可以完全避免该引脚。比较不再成立，因为引脚已经不存在：[DiscreteCat_Functor] 已在 PR“代数承载是集合”（2026-09-17）中在 Instance/Discrete.v 中就地注释，而极限形路线现在也不再携带字面上的 [Set]（Structure/Limit/Power.v 自身的宇宙注释记录了测量）。类路线仍然是首选，但用于识别时，极限形路线携带的内容而不是 [Set] 底板：[Limit] 将离散形状的 hom 和证明宇宙绑定到环境的宇宙，而类不施加这样的绑定。

 一项工程发现，因为花费了编译成本而被记录。[rewrite] 与显示其所给模式的目标不匹配。[Build_Adjunction'] 的第二自然性条款呈现复合 [fmap[Copower_Functor J] g ∘ copower_inj J x j]，并且在 [Set Printing All] 下，其隐式对象参数是混合的：中间对象展开为 [copower J x]，而余域展开为 [fobj[Copower_Functor J] y]。一个天真陈述的引理在两个位置都会得到 [copower J y]，而一个将注入指定给 [b ~> fobj[Copower_Functor J] b] 的引理在两个位置都会得到 [fobj[…] x]，因此两者都被“未找到匹配的子项”拒绝，第二个打印了展开器已经删除的注释。解决方法不是第三种写法，而是停止重写：[apply compose_respects] 后跟 [symmetry; exact (copower_functor_inj J g j)]，通过 CONVERSION 完成，它不关心对象是如何拼写的。与记录在 Construction/Slice/Pullback.v 中的 [star_fmap_mor] 属于同一家族。

 [Defined] 是承重的，通过翻转它来测量。
 [Copower_Power_Adjunction] 用 [Qed] 关闭，但却直接破坏了 [cp_adj_readback] ：

 术语 “eq_refl” 的类型是
 "adj [Copower_Power_Adjunction] = adj [Copower_Power_Adjunction]"
 而它被期望的类型是
 "adj [Copower_Power_Adjunction] = cp_adj_iso b c"
 （无法统一 "adj [Copower_Power_Adjunction]" 和 "cp_adj_iso b c"）。根据当前文件的情况，在代码主体中经过证明的终结点计数，有七个 [Defined] 和六十一 [Qed]，其中正好有三个是承重的——通过将每个单独的 [Qed] 翻转并重新编译来测量：[Copower_Power_Adjunction]（如上）、[cp_pa_adj] 和 [ex1_pa_adj]，每一个都能通过 [eq_refl] 读取回或伴随计算简化。其他四个——[power_of_weighted]、[copower_of_weighted]、[One_iprod_ump] 和 [One_icoprod_ump]——在保持其他所有内容不变的情况下编译为 [Qed]，并根据生成数据的常量保持透明的惯例被视为 [Defined]。所有三个承重的都被一个不透明的 [Qed] 闭合克隆 PINNED 在探针中，其回读被否定（负值 5、12 和 13），因此翻转测量是受保护的；四个不承重的保持仅测量，“翻转这个什么也不会改变”是一个反事实的否认命令无法表达的。§A-§B 单独的状态，首次加载时：无公理，25/25 常量，报告“在全局上下文下封闭”，每个均通过全限定名查询。（整个文件的数字是 147/147；见下文 COST 部分。）25 的标准是每个 [Definition] 和 [Parameter] 的头在 [Print Module Category.Structure.Limit.Power.Adjunction] 的空白平铺输出中——该命令将其模块头跨三行包装，因此首先需要对其进行按行锚定的扫描——其中包含 22 个源声明的头加上 [Power_Functor] 的三项 [Program] 义务，这对 [.glob] 扫描是不可见的（[.glob] 恰好包含 22 个 [def] / [prf] 条目）。该文件未声明 [Record]、[Class] 或 [Inductive]，因此不存在未列出的 [Build_*]。（[Print Module] 将一个不透明常量呈现为 [Parameter]；这里显示的八个是三个义务和五个普通的 [Qed] 引理，而不是公理，这正是上面的审核所检查的内容。）根据前述专利段落中提出的标准，所有25个名称都是自由的——在所有25个名称中，一个一个检查，没有任何冲突。所有25个名称都在 Makefile 的 [print-assumptions] 门中注册，完全限定：这三个 [Program] 义务在该目标的单一共享作用域中无法通过其裸名称访问（测量结果——该门提示“在当前环境中未找到引用 Power_Functor_obligation_1”），因此整个代码块被限定，而不仅仅是三个，遵循该文件中已经存在的 [Powerset.Universal] 先例。[make todo] 增长了，按 §A-§B 作为首次着陆，正好增加了一行，而且它是散文：上面的工程段落使用了一个普通的英语动词，目标的不区分大小写的模式在其第一个替代项上匹配该动词。自那以后，该动词已被替换，因此该文件现在贡献的命中为零：它不包含任何探测命令，也不包含任何类型的工单标记，而且你正在阅读的段落是以不增加任何命令的方式编写的。
 ────────────────────────────────────────────────────────────────────────

 C. 加权限制比较，以及它是一个协议Structure/Limit/Weighted.v 提出了由一个权重（WEIGHT）决定的极限。幂是对终端形状 [_1] 的加权极限，其中权重选择索引集合（SET），且图形（DIAGRAM）在 [b] 处恒定。[conical_weighted]（Weighted.v）不是这个定理，也没有被引用为该定理：它是对任意形状的常数权重，即加权极限 ⇒ 普通极限，这是圆锥情形，并不涉及幂。两个方向都已经证明，这正是使其成为两个表示之间的对应，而不是一个类的成员。[power_WeightedLimit] 将所选择的幂放入类中，而 [power_of_weighted] 则走相反的方向：对于该权重和该图的任意加权极限，[wlim_obj] 是一个幂，其评估为 [wpow_ev] ——跨 [wlim_iso] 传回的恒等映射。反之则不对环境范畴假设任何条件，甚至不假设它具有幂。[copower_of_weighted] 是对偶，而 [WeightedColimit] 是其所消耗的类。整个 [wlim_natural] 完全花费在每一边的恰好一个引理中（[wpow_from_is_precompose]，[wcop_from_is_postcompose]）。共幂的一半直接构建在 [1^op] 之上，并且不是一个操作实例化，两者的原因都已固定。余极限权重在形状上是逆变的，所以 [WeightedColimit W F] 将 [W] 放置在 [J^op] 之上；[Opposite _1 = _1] 在 [eq_refl] 被反驳（转换），并且 [Opposite_Functor (copower_diagram b) = @power_diagram (C^op) b] 也被反驳（类型——错误报告了形状，[1 ⟶ C^op] 对比 [1^op ⟶ C^op]）。因此，共幂的一半不能简单地在 [C^op] 处读取：这是 #321 的操作技巧使 §A 的共幂函子完全自由的地方不起作用。权重是离散的，这是被强制的而非方便的：幂的评估是由元素索引的，因此后退腿的尊敬性必须从 [j ≈ j'] 推导出 [ev j ≈ ev j']。[index_setoid J] 因此使用 [eq_Setoid]，并且 [wpow_cone] 和 [wcop_cocone] 都从中获得了免费的尊敬性。

 往返行程返回所选择的数据，每边都有一个身份残差，以展示而非描述的方式。[wrt_ev_residue] 和 [wrt_inj_residue] 在 [power_ev J b j ∘ id] 和 [id ∘ copower_inj J b j] 的 [eq_refl] 处关闭；严格形式被证伪和固定，[wrt_ev_equiv] / [wrt_inj_equiv] 是 [≈] 声明，一个是 [id_right]，另一个是 [id_left]。★ 两个方向的代价是不同的宇宙，这是这里有趣的测量。[power_WeightedLimit] 携带块方程 [u0 = u3] -- [C] 的同论证水平与索引宇宙相对应 -- 而 [copower_WeightedColimit] 携带 [u0 = u4]；但 [power_of_weighted] 和 [copower_of_weighted] 根本不携带任何方程，它们的索引宇宙只是被界定。识别的位置是由探测器而非归因来定位的：在 [Constraint ch < ji]、[power]、[power_ev]、[Power_Functor]、[index_setoid]、[power_weight]、[power_diagram] 甚至 [HomDiagram cu (power_diagram bu)] 下都被接受，而 [WeightedLimit (power_weight Ju) (power_diagram bu)] 被拒绝 —— 因此，是把权重和同论图放入一个 [Sets] 才迫使它成立，而不是权重，也不是图。这并不是声称不可避免的，它是 [Sets] 加权公式固有的特性，具有裸 [Type] 权重，而不是任何 #321 所造成的。

 ────────────────────────────────────────────────────────────────────────

 D0. COPWER 双函子，这是两个参数读取共享的内容

 [Copower_Bifunctor : C ∏ Coq ⟶ C] 使 [(b, J) ↦ J · b] 在两个参数上同时保持函子性。§D 固定对象并改变索引；§E 固定索引并改变对象。它们是这个单一双函子的两种参数化方式，仅在 [ParametrizedAdjunction] 的 [X ∏ P ⟶ A] 的哪一个槽位放置参数上有所不同，§D 通过 [Copower_Bifunctor ◯ Swap] 达到其自身的目的，而不是通过构建第二个双函子。★ 索引类别是 [Coq]，这是强制的，而不是首选。共幂注入是按元素（ELEMENTS）索引的，因此 [fmap_respects] 必须从 [f ≈ f'] 推导出 [copower_inj (f j) ≈ copower_inj (f' j)]，而 [f ≈ f'] 需要在 LEIBNIZ 相等下使用 [f j = f' j]。[Coq] 的同态集是逐点 Leibniz，并且提供它。[Sets] 不提供，探针携带一个无公理的反模型——[sets_index_respects_absurd]，作用于一个二元素同态集合，其 [≈] 是全集关系——以反驳 [SetsIndexRespects]，这个是 CANONICAL 箭头作用的 [fmap_respects] 义务（注入的共幂中介，也是任何与注入交换的箭头作用必须满足的）。在那个范围内阅读它：对于 [Sets] 的那个动作被完全驳回，而不仅仅是记录为一个不能通过的证明；没有对同一对象动作的其他箭头动作进行调查，也没有声称其被驳回。#321 自身的 Power/Hom.v 预料到了它的双射的同一事实——它的标题记录了 [HasIndexedCoproducts] 的索引是一个裸 [Type]，并且没有对索引上的较粗集同类提出任何主张——这就是那个被驳回的事实。

 ────────────────────────────────────────────────────────────────────────

 D1. MAC LANE §IV.7 练习 1，无限制[Copower_Bifunctor_Iso J : CopLeft J ≅ CopRight J] 在 [[C^op ∏ C, Sets] ] 是该练习显示的同构——在其修正形式 [C(J · a, c) ≅ Set(J, C(a,c))] 中，根据上述方差论证——从一族双射升级为 BIFUNCTORS 的同构，这就是“在参数 a 上自然”所要求的。它不需要除 [HasIndexedCoproducts] 以外的任何假设。

 右边的形式很令人满意，这并非巧合：
 [CopRight J] 是 [@Power_Functor Sets Sets_HasIndexedProducts J ◯ Hom C]，
 所以 Mac Lane 的 [Set(J, −)] 是 §A 自己的幂函子在 [Sets] 处的读取，并且整个右边是该函子应用于 hom-bifunctor。两者的对象作用在 [eq_refl] 处读取。逐点可逆变换是通过#369的[componentwise_iso]升级的，而不是通过手工构建逆变换及其自然性。该供体仅花费边际的10个模块（通过移除[Require] : 111 → 101来衡量）；之所以使用它，是因为手工构建逆变换会正好复刻那个文件已存在以提供的一般引理。

 ────────────────────────────────────────────────────────────────────────

 D2. 相同的练习打包，以及重点[Copower_Object_ParametrizedAdjunction : ParametrizedAdjunction Ex1_Bifunctor] 是 #396 在对象参数处的记录，而 #396 的定理 3 然后将右伴随组装成 [MacLane_Ex1_hom_bifunctor : C^op ∏ C ⟶ Coq] —— 这就是 HOM-函子，这是这个练习的重点。该识别是在两个强度下实现的，但都没有被断言：[ex1_hom_bifunctor_obj] 在对象作用上闭合于 [eq_refl]，[fobj (a,c) = (a ~{C}~> c)]，而 [ex1_hom_bifunctor_fmap] 给出了箭头作用的逐点形式 [g ↦ k ∘ g ∘ unop h]，通过 [ex1_param_mate_precomp]，该公式从 [conj_mate] 自身的分量公式中读取参数伴随，而不是重新计算共轭。包装需要一个假设，并且它是一个明确的论证。右伴随 [C(a,−)] 必须落在协幂所索引的相同索引类别中，在那里这两个要求相互冲突：协幂希望索引上具有莱布尼茨等式（D0），Hom 函子希望 [C] 拥有自身的 [≈]。[HomAllStrict C] 正是它们一致的地方。★ 这不是一个新的假设，也没有重新声明。
 Construction/Comma/Special.v 已经携带 [HomStrict]，固定
 对象对，用于其自身的 [Full] 标准；该名称在此被使用
 并在所有对象上进行量化（[HomAllStrict C := ∀ x y, HomStrict x y]），边际成本为 4 个模块。 通过扫描该文件自有声明的名称发现了冲突，而使用该来源名称是解决冲突的方法：重新声明 [HomStrict] 会在 [print-assumptions] 目标的单一共享范围内将两个不同的谓词放在同一个名称下。 该来源还提供了 [Blur_HomStrict_absurd]，一个已编译的类别，其中每个同族集合形式都是可反驳的，这是该假设的边界。★ 并且假设被包含在树中，这比明显的猜测更好。[_1] 的 hom-setoid 是 [Morphism_equality]（Instance/One.v），因此 [One_HomAllStrict] 是身份蕴含，并且 [_1] 拥有所有索引积和余积（[One_HasIndexedProducts] 和 [One_HasIndexedCoproducts] 分别是每个八行通用性质的三行记录字面量，每一步 [one_hom_eq]）——因此 [One_Ex1_ParametrizedAdjunction] 是一个真正的树内模型。按其强度阅读它：它运用了假设和组合，而不是结论，[1] 中的一切都塌缩为 [ttt]。没有展示非退化模型，也没有声称存在非退化模型。 

 ────────────────────────────────────────────────────────────────────────

 E. 问题自身的第 4 项：将索引集作为参数这里参数槽保存索引，而可变参数是对象。右伴随正好是§A的幂函子——[pa_right Copower_ParametrizedAdjunction J = Power_Functor J]通过[eq_refl]——而部分函子在[eq_refl]（[copower_bifunctor_partial_obj]，[copower_bifunctor_partial_fmap]）的两个作用上与§A的共幂函子一致，但作为记录则不一致，这是下一段的内容。此外，[pa_adj]自身的霍姆集合同构正是§B的[cp_adj_iso]通过[eq_refl]（[pa_adj_iso_is_cp_adj_iso]）——因此§E没有干扰§B的对应。#396定理3随后组装了[Power_Bifunctor : Coq^op ∏ C ⟶ C]，在索引上是逆变的，并在[eq_refl]处对应[fobj (J, b) = power J b]。★ §B 同构在部分函子上赋值；§B 伴随关系没有赋值，并且错误说明了原因。[fobj[Partial_l Copower_Bifunctor J] b] 和 [fobj[Copower_Functor J] b] 在 [eq_refl] 上一致，因此 [cp_adj_iso J b c] 在部分函子的类型上赋值，没有插入任何内容；但是 [Adjunction] 是由函子 RECORD 索引，而不是由其两个作用索引，因此 [Copower_Power_Adjunction J] 在那里被拒绝，错误指明了有问题的字段：

 (无法统一 "λ (x y : obj [C^op^op] ) (f g : x ~{ C^op^op }~> y),
 fmap_respects y x f g"
 和 "Partial.Partial_l_obligation_1 C Coq C Copower_Bifunctor J").

 两个事实都被固定。因此 [cp_pa_adj] 重建记录 —— 但仍然基于相同的同构和相同的两个唯一性引理，所以没有重新推导出任何泛性质。共轭是被消耗的，而不是重新计算的。 [copower_reindex h] 是 #396 的 [param_transform] 和 [power_reindex h] 是它的 [pa_param_mate]，[power_reindex_is_conj_mate] 在 [eq_refl] 处记录为 #394 的 [conj_mate]；[power_reindex_conjugate] 是 [pa_natural_p] 被归属于 #394 的 [Conjugate]，这种归属本身就是完整的证明，因为 [pa_square_is_Conjugate] 精确地识别了两者；并且 [power_reindex_universal] 是 [pa_param_mate_universal]，因此配偶是唯一的共轭，而不仅仅是其中之一。指标上的函子性是 [pa_param_mate_id] / [pa_param_mate_comp] 和 [param_transform_id] / [_comp]，按名称引用。在这里被证明而非引用的是它们各自的基本解读：[copower_reindex_inj] 和 [power_reindex_ev] ([ev_{j'} ∘ τ_b ≈ ev_{h j'}])，第二个来自配偶的分量公式加上 [cp_pa_counit_inj]。★ §D 和 §E 是不同的陈述，且彼此不抵消。
 Mac Lane 的例 1 改变了 OBJECT；问题中的第 4 项改变了 INDEX，
 这是其自身第 3 项 (= §IV.2 例 12, §B 上文) 固定的变量。两者都是真的，并且都在此处标注。

 ────────────────────────────────────────────────────────────────────────

 §C-§E 的宇宙，同时以 BINDER 和 BLOCK 测量

 所有十八个测量常数都位于 [C : Category@{u u0 u0}] 上——通过在 BINDER 中重用水平变量进行证明而同源识别，没有区块方程说明这一点——并且在它们中的任何一个的绑定器或区块中都不存在以单词界定的 [Set]。区块方程为：[power_WeightedLimit]                     u0 = u3        (索引)
 [copower_WeightedColimit]                 u0 = u4        (索引)
 [power_of_weighted]                       无
 [copower_of_weighted]                     无
 [Copower_Bifunctor] ,  [CopLeft] ,  [CopRight] ,  [HomCoq] ,
 [copower_reindex]                       无
 [Copower_Bifunctor_Iso]                   u0 = u2, u0 = u3
 [Copower_Object_ParametrizedAdjunction] ,  [ex1_pa_adj] ,
 [MacLane_Ex1_hom_bifunctor]             无
 [Copower_ParametrizedAdjunction] ,  [Power_Bifunctor] ,  [cp_pa_adj] ,
 [power_reindex] ,  [power_reindex_conjugate] 
 u0 = u1, u0 = u2,
 u0 = u4, u0 = u5★ 所以，参数化对象的阅读比参数化指标的阅读对宇宙的依赖更少，原因在于它们各自使用的双射。§D2 直接从共幂的普遍性质在 [Coq] 中构建其同态集双射，并且完全不携带任何方程；§E 组合了 #321 的两个 [_at] 双射，并且正好继承了上文 §B 段落中局部的四个方程。§D1 位于它们之间的两个层面，这仅与所涉及的余积类一致——但这是一种归因，而不是孤立：没有任何实验移除一个供体并显示某个方程消失。这些都不被声称是不可避免的。

 ───────────────────────────────────────────────────────────────

 成本，以及它带来的收益闭包 111 个模块（项目内传递依赖 [.vo] 超过 [.Makefile.coq.d]，但不包括文件本身），比 §A-§B 的 38 个增加了很多。通过逐个 DROPPING 每个 [Require] 测量：在 §C-§E 新增的 12 个中，[Adjunction/Parameter] 为 28，[Instance/Coq] 为 13，[Instance/Fun/Morphisms] 为 10，[Construction/Comma/Special] 为 4，[Structure/Limit/Weighted] 为 1，其余七个为零；在 §A-§B 的 [Require] 中，[Structure/Limit/Power/Hom] 成本为 2。这些边际值加起来并不等于 111 - 38，也不意味着要等于：逐个删除边际值忽略了剩余部分共享的内容。树中没有任何内容需要此文件，因此这些都不会影响现有的使用者。在全局上下文中，147/147 常量已关闭，每个都通过完全限定名查询，零行 [Axioms:]。147 的标准是每个 [Definition] 和 [Parameter] 在其 WHITESPACE-FLATTENED 输出中的 [Print Module Category.Structure.Limit.Power.Adjunction] 头（该命令封装其模块头）：86 个 [Definition] 加上 61 个 [Parameter]。[.glob] 包含 110 个（86 个 [def] + 24 个 [prf]），因此 61 个不透明常量中的三十七个是 [Program] 义务，没有源代码或 [.glob] 扫描可以看到，并且 147 - 110 = 37 个检查。该文件未声明 [Record]、[Class] 或 [Inductive]，因此没有未列出的 [Build_*]。所有 147 个都在 [print-assumptions] 闸门中，完全合格，该闸门将该目标的第 5 块从 25.5 提升到 38.9 KiB，测量的是带有 [@{] / [}] 分隔符的原始文本（文件中最大的块是 73.6）。

 在所有 147 个名称中零碰撞，在先前技术段落的标准下逐一扫描每个名称，并扩展该标准以排除该文件自身的探测（该探测按设计将其中 27 个作为控制）：

 rg -l -w -e '<token>' -g '*.v' \
 -g '!Structure/Limit/Power/Adjunction.v' \
 -g '!Test/ProbeCopower366.v' .仪器检查在 [power] = 42 个文件 和 [Monoid] = 91 个文件，两者都在相同的排除范围内（未排除，[Monoid] 是 92，这个文件提到了它）。在着陆前发现了两个真实的冲突，并且两者都是通过使用捐赠者而不是重命名来解决的：[HomStrict] 和 [One_HomStrict] 是 Construction/Comma/Special.v。Test/ProbeCopower366.v 反映了该文件的完整 [Require] 列表，并携带了十五条反驳命令 = 1 个工具检查 + 14 条三种类型的否定命令，这些类型由错误文本区分开：9 条转换错误（每条以“cannot unify between two terms of one type”结尾），3 条类型错误（仅为“has type ... expected”，没有“cannot unify”且没有宇宙子句），2 条可形成性错误（每条以宇宙子句结尾）。每条命令都是单独移除、单独编译，并且生成了正好一条 [Error]，其完整文本被读取。负数 2 和 3 是在两种拼写下相同的方程，但结果为不同的类型——当双方的隐式都写出来时，[@Copower_Functor C HC J] 与 [@Power_Functor (C^op) HC J] 在语句处被拒绝，两个常量类型不一致且错误信息中没有“无法统一”；而在 [Power_Functor J] 对 [C]，它们共享一个类型，因此——这就是为什么负数的类型是通过其错误信息读出的，而不是从其语句猜测的。在那里捕获了一个错误的守卫，并记录在探测中：
 首次书写为负 2，[Copower_Functor J = @Power_Functor (C^op) HC J]，将左侧的类别留为隐式，且展开器重新解析为 [C^op]（将其余乘积实例留作未解析的 evar），以便两边确实共享类型；然后错误在 [eq_refl] 触发，驳斥了在 [C^op] 重新陈述的负 3 的事实，而不是评论中声称的类型不匹配。一般迹象是：一个负面，其声称的原因是“双方不共享类型”，但其错误在 [eq_refl] 处触发，展开了它的陈述并测量了别的东西——[obj[?C] 家族 Test/ProbeFiniteProducts335.v 记录了此情况。负号 12 和 13 通过不透明克隆技术固定了两个进一步的承载 [Defined]（[cp_pa_adj]、[ex1_pa_adj]），负号 5 用于 [Copower_Power_Adjunction]；负号 14 固定了 §B 宇宙段中记录的索引宇宙边界。每个负号命名的常量也出现在每个反驳之外；唯一限制在一个负号中的标记是被反驳命令自身的名称，这些名称从不进入环境，以及仪器故意缺失的名称。重命名模拟 15/15——负号命名的十三个目标常量加上仅通过其克隆达到的两个——每个重命名仅应用于本文件（整个树的重命名在构造上是无操作），每次中断都落在 [Check] 控制线，而不在反驳内部。[make todo] 增长了 29，全部在探针中（它的 15 条反驳命令和 14 行散文与该目标的模式匹配）；这个文件没有任何贡献，其中最初携带的散文行 §A-§B 已被改写。

 ────────────────────────────────────────────────────────────────────────

 未交付- 没有对任何事物进行 [Set] 索引读取：索引类别在整个过程中都是 [Coq]，并且在 [Sets] 上的规范箭头作用是被反驳的（探针 §H），而不是延迟的；没有对 [Sets] 上的其他箭头作用进行研究。是否某些离散集合上的 [Sets] 的完整子类别会起作用也没有被研究；树中不存在这样的子类别。- 没有 [HomAllStrict] 的非退化模型。[_1] 是唯一的见证，它会使一切都崩溃；特别是，这里没有任何东西展示了一个真正具有许多箭头满足它的类别，而且也没有声称其不可能。- §D1 和 §D2 彼此没有关联。没有任何说明表明
 [Copower_Bifunctor_Iso] 是 [MacLane_Ex1_hom_bifunctor] 的 [Sets] 值影子，并且两者属于不同类别
 ([Sets] 对 [Coq])，所以比较它们需要一个未建立的函子。- 在 [J] 或 [b] 中没有 §C 比较的自然性，也没有 [wlim_obj] 的唯一性（该类没有），因此 §C 是对固定数据下两个表示的约定，而不是结构的等价。- 对于一般的索引积没有 [WeightedLimit] 声明，仅对作为幂的常量族有。- 没有 2-范畴的解读，没有关于 [Adjunction/Map.v] 的伴随映射的内容，也没有 §E 的共轭对与 [Instance/Adj.v] 的伴随类之间的关系。- 没有任何内容注册为 [Instance]：[One_HasIndexedProducts] 和 [One_HasIndexedCoproducts] 故意作为普通 [Definition]，因此解析不会提供任一类的退化模型。- 在 §B、§D1 或 §E 的命名分类中没有具体实例；文件中唯一的具体实例化是 §D2 的 [_1]。
*)

#[local] Obligation Tactic := idtac.

(*
   * ** The power as an endofunctor of [C]

   The arrow action is the mediator [power_desc] produces for the family
   [j ↦ g ∘ ev j], and every functor law is one appeal to that mediator's
   uniqueness clause followed by a computation with [power_fmap_ev]. 

   --------
   * ** 作为 [C] 的端函子（endofunctor）的幂  

   箭头作用是 [power_desc] 为族 [j ↦ g ∘ ev j] 所产生的中介器，每个函子定律都是对该中介器的唯一性条款的一次引用，随后进行 [power_fmap_ev] 的计算。
*)

Section PowerFunctor.

Context {C : Category}.
Context {HP : @HasIndexedProducts C}.
Context (J : Type).

Definition power_fmap {b b' : C} (g : b ~> b') : power J b ~> power J b' :=
  unique_obj (power_desc (power_ump J b')
                (fun j : J => g ∘ power_ev J b j)).

(* The characterizing equation of the arrow action: it commutes with the evaluations. This is the mediator's [unique_property], nothing more. / 箭头作用的特征方程：它与评估可交换。这是中介者的 [unique_property]，仅此而已。 *)
Lemma power_fmap_ev {b b' : C} (g : b ~> b') (j : J) :
  power_ev J b' j ∘ power_fmap g ≈ g ∘ power_ev J b j.
Proof. exact (unique_property (power_desc (power_ump J b') _) j). Qed.

Program Definition Power_Functor : C ⟶ C := {|
  fobj := fun b => power J b;
  fmap := fun b b' g => power_fmap g
|}.
Next Obligation.
  intros b b' g g' Hg.
  apply (uniqueness (power_desc (power_ump J b') _)).
  intros j; rewrite power_fmap_ev; now rewrite Hg.
Qed.
Next Obligation.
  intros b.
  apply (uniqueness (power_desc (power_ump J b) _)).
  intros j; rewrite id_left; apply id_right.
Qed.
Next Obligation.
  intros x y z f g.
  apply (uniqueness (power_desc (power_ump J z) _)).
  intros j.
  rewrite comp_assoc, power_fmap_ev.
  rewrite <- !comp_assoc; now rewrite power_fmap_ev.
Qed.

Example power_functor_obj (b : C) :
  fobj[Power_Functor] b = power J b := eq_refl.

Example power_functor_fmap {b b' : C} (g : b ~> b') :
  fmap[Power_Functor] g = power_fmap g := eq_refl.

(*
 [power_fmap_ev] restated through [fmap], which is the spelling the
 adjunction's naturality goals present. 

 --------
 [power_fmap_ev] 通过 [fmap] 重述，这是结合的自然性目标所呈现的拼写。
*)
Lemma power_functor_ev {b b' : C} (g : b ~> b') (j : J) :
  power_ev J b' j ∘ fmap[Power_Functor] g ≈ g ∘ power_ev J b j.
Proof. exact (power_fmap_ev g j). Qed.

End PowerFunctor.

Arguments power_fmap {C HP} J {b b'} g.
Arguments Power_Functor {C HP} J.
Arguments power_functor_ev {C HP} J {b b'} g j.

(*
   * ** The copower as an endofunctor, for free

   [copower J b] is [@power (C^op) HC J b] DEFINITIONALLY (#321), so the
   copower functor is the op-power functor read back through
   [Opposite_Functor].  That is a plain [Definition] with no obligation and
   no tactic; the four [Example]s below record by [eq_refl] exactly what it
   costs, namely nothing. 

   --------
   * ** 作为一个端函子（endofunctor）的余冪（copower），是免费的

   [copower J b] 在定义上是 [@power (C^op) HC J b] (#321)，所以
   余冪函子是通过 [Opposite_Functor] 读回的对冪（op-power）函子。
   这就是一个普通的 [Definition]，没有任何义务和策略；下面的四个 [Example] 通过 [eq_refl] 精确记录了它的代价，也就是没有任何代价。
*)

Section CopowerFunctor.

Context {C : Category}.
Context {HC : @HasIndexedCoproducts C}.
Context (J : Type).

Definition Copower_Functor : C ⟶ C :=
  Opposite_Functor (@Power_Functor (C^op) HC J).

Example copower_functor_obj (b : C) :
  fobj[Copower_Functor] b = copower J b := eq_refl.

Example copower_functor_fmap {b b' : C} (g : b ~> b') :
  fmap[Copower_Functor] g = @power_fmap (C^op) HC J b' b g := eq_refl.

(*
 The double opposite returns the op-power functor ON THE NOSE, which is
 what makes [C ⟶ C] the right type rather than [(C^op)^op ⟶ (C^op)^op]. 

 --------
 双重对立精确地返回了幂对偶函子，这正是使 [C ⟶ C] 成为正确类型而不是 [(C^op)^op ⟶ (C^op)^op] 的原因。
*)
Example copower_functor_double_op :
  Opposite_Functor Copower_Functor = @Power_Functor (C^op) HC J := eq_refl.

(* And the arrow action IS the mediator [copower_desc] produces, read covariantly: no [^op] appears in this statement. / 箭头作用确实是中介者 [copower_desc] 产生的，协变地读取：在此声明中没有 [^op] 出现。 *)
Example copower_functor_desc {b b' : C} (g : b ~> b') :
  fmap[Copower_Functor] g
  = unique_obj (copower_desc (copower_ump J b)
                  (fun j : J => copower_inj J b' j ∘ g)) := eq_refl.

Lemma copower_functor_inj {b b' : C} (g : b ~> b') (j : J) :
  fmap[Copower_Functor] g ∘ copower_inj J b j
  ≈ copower_inj J b' j ∘ g.
Proof. exact (@power_fmap_ev (C^op) HC J b' b g j). Qed.

End CopowerFunctor.

Arguments Copower_Functor {C HC} J.
Arguments copower_functor_inj {C HC} J {b b'} g j.

(*
   * ** Mac Lane §IV.2 Exercise 12

   The hom-set isomorphism is the composite of #321's two bijections.  The
   two land at the SAME [Sets]-power -- [copower_hom_iso_at] at
   [J ⋔ C(b,c)] read from the copower side, [power_hom_iso_at] at the same
   object read from the power side -- so no comparison map is needed and
   [cp_adj_iso] is supplied by [:=]. 

   --------
   * ** Mac Lane §IV.2 练习 12

   同态集同构是 #321 的两个双射的合成。两个同态集最终落在相同的 [Sets] 幂上 —— 从余幂侧读作 [copower_hom_iso_at] 于 [J ⋔ C(b,c)]，从幂侧读作 [power_hom_iso_at] 于同一对象 —— 因此不需要比较映射，而 [cp_adj_iso] 由 [:=] 提供。
*)

Section CopowerPowerAdjunction.

Context {C : Category}.
Context {HP : @HasIndexedProducts C}.
Context {HC : @HasIndexedCoproducts C}.
Context (J : Type).

(*
 The shared right-hand side of the two bijections: the [Sets]-power of the
 hom-setoid [C(b,c)] by [J].  Naming it lets each donor be ASCRIBED at a
 type mentioning it, which is what says they meet ON THE NOSE. 

 --------
 两个双射的共享右边：通过 [J] 对同态集族 [C(b,c)] 的 [Sets] 次幂。为它命名可以让每个捐赠者在提到它的类型上被归属，这就是它们精确匹配的意思。
*)
Definition cp_middle (b c : C) : Sets :=
  @power Sets Sets_HasIndexedProducts J
    {| carrier := @hom C b c ; is_setoid := @homset C b c |}.

(*
 Each donor lands at [cp_middle b c] with no comparison map inserted --
 these are the two donors supplied AS TERMS at that ascribed type, so a
 change to either target breaks them.  A tautology [X = X] would say
 nothing here, and is deliberately not what is written. 

 --------
 每个供体在 [cp_middle b c] 降落时没有插入比较地图——这些是作为该指定类型的条款提供的两个供体，因此对任一目标的更改都会破坏它们。一个重言式 [X = X] 在这里什么也不会说，并且故意不是所写内容。
*)
Example cp_copower_at_middle (b c : C) :
  @Isomorphism Sets
    {| carrier := @hom C (copower J b) c
     ; is_setoid := @homset C (copower J b) c |} (cp_middle b c) :=
  copower_hom_iso_at (@copower_ump C HC J b) c.

Example cp_power_at_middle (b c : C) :
  @Isomorphism Sets
    {| carrier := @hom C b (power J c)
     ; is_setoid := @homset C b (power J c) |} (cp_middle b c) :=
  power_hom_iso_at (@power_ump C HP J c) b.

Definition cp_adj_iso (b c : C) :
  @Isomorphism Sets
    {| carrier := @hom C (fobj[Copower_Functor J] b) c
     ; is_setoid := @homset C (fobj[Copower_Functor J] b) c |}
    {| carrier := @hom C b (fobj[Power_Functor J] c)
     ; is_setoid := @homset C b (fobj[Power_Functor J] c) |} :=
  iso_compose (iso_sym (power_hom_iso_at (@power_ump C HP J c) b))
              (copower_hom_iso_at (@copower_ump C HC J b) c).

(*
 The forward transpose of [u] is the unique arrow whose [j]-th evaluation
 is [u] precomposed with the [j]-th injection -- Mac Lane's correct
 [C(X · a, c) ≅ Set(X, C(a,c))], read at one pair of objects. 

 --------
 [u] 的前向转置是唯一的箭头，其 [j] 次评估是 [u] 与 [j] 次注射的复合——Mac Lane 的正确 [C(X · a, c) ≅ Set(X, C(a,c))]，在一对对象上阅读。
*)
Lemma cp_to_char (b c : C) (u : copower J b ~> c) (j : J) :
  power_ev J c j ∘ to (cp_adj_iso b c) u ≈ u ∘ copower_inj J b j.
Proof. exact (unique_property (power_desc (power_ump J c) _) j). Qed.

Lemma cp_to_uniq {b c : C} (u : copower J b ~> c) (v : b ~> power J c) :
  (∀ j : J, power_ev J c j ∘ v ≈ u ∘ copower_inj J b j) →
  to (cp_adj_iso b c) u ≈ v.
Proof.
  intros H.
  exact (uniqueness (power_desc (power_ump J c)
           (fun j : J => u ∘ copower_inj J b j)) v H).
Qed.

(* Mac Lane §IV.2 Ex 12: the copower is left adjoint to the power. / Mac Lane §IV.2 练习 12：余幂是幂的左伴随。 *)
Definition Copower_Power_Adjunction : Copower_Functor J ⊣ Power_Functor J.
Proof.
  unshelve eapply (Build_Adjunction' cp_adj_iso).
  - intros x y z f g.
    apply cp_to_uniq; intros j.
    rewrite comp_assoc, cp_to_char.
    rewrite <- !comp_assoc.
    apply compose_respects; [ reflexivity |].
    symmetry; exact (copower_functor_inj J g j).
  - intros x y z f g.
    apply cp_to_uniq; intros j.
    rewrite comp_assoc.
    rewrite (power_functor_ev J f j).
    rewrite <- !comp_assoc; now rewrite (cp_to_char x y g j).
Defined.

(*
 The adjunction's own hom-set isomorphism IS the composite, and both its
 legs are the mediators of the two universal properties, on the nose. 

 --------
 伴随自身的同集同构就是复合映射，并且它的两条边都是两个泛性质的调解器，完全如此。
*)
Example cp_adj_readback (b c : C) :
  @adj C C (Copower_Functor J) (Power_Functor J) Copower_Power_Adjunction b c
  = cp_adj_iso b c := eq_refl.

Example cp_to_readback (b c : C) (u : copower J b ~> c) :
  to (cp_adj_iso b c) u
  = unique_obj (power_desc (power_ump J c)
                  (fun j : J => u ∘ copower_inj J b j)) := eq_refl.

Example cp_from_readback (b c : C) (v : b ~> power J c) :
  from (cp_adj_iso b c) v
  = unique_obj (copower_desc (copower_ump J b)
                  (fun j : J => power_ev J c j ∘ v)) := eq_refl.

End CopowerPowerAdjunction.

Arguments cp_adj_iso {C HP HC} J b c.
Arguments Copower_Power_Adjunction {C HP HC} J.

(*
   * ** C. The weighted-limit presentation, and that it agrees

   Mac Lane's §III.4 power is an indexed product; Structure/Limit/Weighted.v
   presents limits by a WEIGHT.  The power is the weighted limit over the
   TERMINAL SHAPE [1] whose weight picks out the index SET and whose diagram
   is constant at [b].  Both directions are proved: [power_WeightedLimit]
   inhabits the class at the chosen power, and [power_of_weighted] shows
   that ANY weighted limit for that weight and diagram IS a power.  Dually
   for the copower and [WeightedColimit]. 

   --------
   * ** C. 加权极限的表示，以及它与

   Mac Lane §III.4中幂的对应关系是一个索引积；Structure/Limit/Weighted.v
   通过一个权重呈现极限。该幂是终端形状 [1] 上的加权极限，其权重选取索引集合，其图是常数 [b]。两个方向都得到了证明：[power_WeightedLimit] 属于所选幂的类，而 [power_of_weighted] 显示对于该权重和图的任意加权极限都是一个幂。对余幂和 [WeightedColimit] 同理。
*)

Section WeightedPower.

Context {C : Category}.
Context {HP : @HasIndexedProducts C}.
Context (J : Type).
Context (b : C).

(*
 The weight picks out [J] as a DISCRETE setoid.  Discreteness is what the
 backward leg's respectfulness needs: evaluations are indexed by ELEMENTS,
 so a coarser index setoid would demand [ev j ≈ ev j'] from [j ≈ j']. 

 --------
 权重将 [J]  选作一个离散集类。离散性是后腿的尊重所需要的：评估是按元素索引的，因此更粗的索引集类将要求从 [j ≈ j'] 到 [ev j ≈ ev j'] 。
*)
Definition index_setoid : Sets :=
  {| carrier := J ; is_setoid := eq_Setoid J |}.

Definition power_weight : _1 ⟶ Sets := Δ[_1]( index_setoid ).

Definition power_diagram : _1 ⟶ C := Δ[_1]( b ).

Definition wpow_to_fn (c : C)
  (a : power_weight ⟹ HomDiagram c power_diagram) : c ~> power J b :=
  unique_obj (power_desc (power_ump J b) (fun j : J => a ttt j)).

Program Definition wpow_to (c : C) :
  SetoidMorphism ([[[_1,Sets]]](power_weight, HomDiagram c power_diagram))
    {| carrier := c ~{C}~> power J b
     ; is_setoid := @homset C c (power J b) |} :=
  {| morphism := wpow_to_fn c |}.
Next Obligation.
  intros c a a' Heq; unfold wpow_to_fn.
  apply (uniqueness (power_desc (power_ump J b) (fun j : J => a ttt j))).
  intro j.
  transitivity ((fun j0 : J => a' ttt j0) j).
  - exact (unique_property
             (power_desc (power_ump J b) (fun j0 : J => a' ttt j0)) j).
  - simpl; symmetry; exact (Heq ttt j).
Qed.

Program Definition wpow_from (c : C) :
  SetoidMorphism
    {| carrier := c ~{C}~> power J b
     ; is_setoid := @homset C c (power J b) |}
    ([[[_1,Sets]]](power_weight, HomDiagram c power_diagram)) :=
  {| morphism := fun u =>
       {| transform := fun _ =>
            {| morphism := fun j => power_ev J b j ∘ u |} |}
   |}.
Next Obligation. intros c u i x y Hxy; simpl in Hxy; subst; reflexivity. Qed.
Next Obligation. intros c u x y f j; simpl; now rewrite id_left. Qed.
Next Obligation. intros c u x y f j; simpl; now rewrite id_left. Qed.
Next Obligation. intros c u u' Heq x j; simpl; now rewrite Heq. Qed.

Program Definition wpow_iso (c : C) :
  @Isomorphism Sets ([[[_1,Sets]]](power_weight, HomDiagram c power_diagram))
    {| carrier := c ~{C}~> power J b
     ; is_setoid := @homset C c (power J b) |} :=
  {| to := wpow_to c ; from := wpow_from c |}.
Next Obligation.
  intros c u; simpl; unfold wpow_to_fn.
  apply (uniqueness (power_desc (power_ump J b)
                       (fun j : J => power_ev J b j ∘ u))).
  intro j; reflexivity.
Qed.
Next Obligation.
  intros c a x j; destruct x; simpl; unfold wpow_to_fn.
  exact (unique_property
           (power_desc (power_ump J b) (fun j0 : J => a ttt j0)) j).
Qed.

Program Definition power_WeightedLimit :
  WeightedLimit power_weight power_diagram := {|
  wlim_obj := power J b ;
  wlim_iso := wpow_iso
|}.
Next Obligation.
  intros c c' h a; simpl; unfold wpow_to_fn.
  apply (uniqueness (power_desc (power_ump J b)
            (fun j : J => (a ttt j) ∘ h))).
  intro j.
  rewrite comp_assoc.
  apply compose_respects; [| reflexivity ].
  exact (unique_property
           (power_desc (power_ump J b) (fun j0 : J => a ttt j0)) j).
Qed.

Example power_weighted_obj : wlim_obj power_WeightedLimit = power J b
  := eq_refl.

End WeightedPower.

Arguments power_diagram {C} b.

Section WeightedCopower.

Context {C : Category}.
Context {HC : @HasIndexedCoproducts C}.
Context (J : Type).
Context (b : C).

(*
 The colimit weight is contravariant on the shape, so it lives over
 [1^op].  That shape is NOT [1] -- refuted at [eq_refl] and pinned -- which
 is why this half is built directly rather than instantiated at [C^op]. 

 --------
 余极限权重在形上是逆变的，所以它存在于 [1^op] 上。该形状不是 [1] —— 在 [eq_refl] 处已被驳斥并固定 —— 这就是为什么这一半是直接构建的，而不是在 [C^op] 处实例化的。
*)
Definition copower_weight : (Opposite _1) ⟶ Sets :=
  @Diagonal Sets (Opposite _1) (index_setoid J).

Definition copower_diagram : _1 ⟶ C := @Diagonal C _1 b.

Definition wcop_to_fn (c : C)
  (a : copower_weight
         ⟹ HomDiagram (C:=C^op) c (Opposite_Functor copower_diagram)) :
  copower J b ~{C}~> c :=
  unique_obj (copower_desc (copower_ump J b) (fun j : J => a ttt j)).

Program Definition wcop_to (c : C) :
  SetoidMorphism
    ([[[Opposite _1,Sets]]](copower_weight,
       HomDiagram (C:=C^op) c (Opposite_Functor copower_diagram)))
    {| carrier := c ~{C^op}~> copower J b
     ; is_setoid := @homset (C^op) c (copower J b) |} :=
  {| morphism := wcop_to_fn c |}.
Next Obligation.
  intros c a a' Heq; unfold wcop_to_fn.
  apply (uniqueness (copower_desc (copower_ump J b) (fun j : J => a ttt j))).
  intro j.
  transitivity ((fun j0 : J => a' ttt j0) j).
  - exact (unique_property
             (copower_desc (copower_ump J b) (fun j0 : J => a' ttt j0)) j).
  - simpl; symmetry; exact (Heq ttt j).
Qed.

Program Definition wcop_from (c : C) :
  SetoidMorphism
    {| carrier := c ~{C^op}~> copower J b
     ; is_setoid := @homset (C^op) c (copower J b) |}
    ([[[Opposite _1,Sets]]](copower_weight,
       HomDiagram (C:=C^op) c (Opposite_Functor copower_diagram))) :=
  {| morphism := fun u =>
       {| transform := fun _ =>
            {| morphism := fun j => u ∘[C] copower_inj J b j |} |}
   |}.
Next Obligation. intros c u i x y Hxy; simpl in Hxy; subst; reflexivity. Qed.
Next Obligation. intros c u x y f j; simpl; now rewrite id_right. Qed.
Next Obligation. intros c u x y f j; simpl; now rewrite id_right. Qed.
Next Obligation. intros c u u' Heq x j; simpl; now rewrite Heq. Qed.

Program Definition wcop_iso (c : C) :
  @Isomorphism Sets
    ([[[Opposite _1,Sets]]](copower_weight,
       HomDiagram (C:=C^op) c (Opposite_Functor copower_diagram)))
    {| carrier := c ~{C^op}~> copower J b
     ; is_setoid := @homset (C^op) c (copower J b) |} :=
  {| to := wcop_to c ; from := wcop_from c |}.
Next Obligation.
  intros c u; simpl; unfold wcop_to_fn.
  apply (uniqueness (copower_desc (copower_ump J b)
                       (fun j : J => u ∘[C] copower_inj J b j))).
  intro j; reflexivity.
Qed.
Next Obligation.
  intros c a x j; destruct x; simpl; unfold wcop_to_fn.
  exact (unique_property
           (copower_desc (copower_ump J b) (fun j0 : J => a ttt j0)) j).
Qed.

Program Definition copower_WeightedColimit :
  WeightedColimit copower_weight copower_diagram := {|
  wlim_obj := copower J b ;
  wlim_iso := wcop_iso
|}.
Next Obligation.
  intros c c' h a; simpl; unfold wcop_to_fn.
  apply (uniqueness (copower_desc (copower_ump J b)
            (fun j : J => h ∘[C] (a ttt j)))).
  intro j.
  rewrite <- comp_assoc.
  apply compose_respects; [ reflexivity |].
  exact (unique_property
           (copower_desc (copower_ump J b) (fun j0 : J => a ttt j0)) j).
Qed.

Example copower_weighted_obj :
  wlim_obj copower_WeightedColimit = copower J b := eq_refl.

End WeightedCopower.

Arguments copower_diagram {C} b.

(*
   * ** C'. The converses: a weighted limit for that data IS a power

   This is what turns §C from "the chosen power inhabits the class" into an
   agreement of the two presentations, which is the issue's stated reviewer
   check.  Nothing here assumes the ambient category has powers at all. 

   --------
   * ** C'。逆命题：对于该数据的加权极限 IS 一个幂

   这就是将 §C 从“所选幂位于该类中”转变为两种呈现的一致性的原因，这也是本期审稿人核查中所述的问题。这里没有假设背景范畴中存在幂。
*)

Section WeightedPowerConverse.

Context {C : Category}.
Context (J : Type).
Context (b : C).
Context (WL : WeightedLimit (power_weight J) (power_diagram b)).

(*
 A family read as a weighted cone.  Respectfulness is free because
 [index_setoid J] is DISCRETE; naturality is [id_left] twice. 

 --------
 一个家族被读作一个加权圆锥。尊重是免费的，因为 [index_setoid J] 是离散的；自然性是 [id_left] 两次。
*)
Program Definition wpow_cone (c : C) (pi : ∀ _ : J, c ~> b) :
  power_weight J ⟹ HomDiagram c (power_diagram b) := {|
  transform := fun _ => {| morphism := pi |}
|}.
Next Obligation. intros c pi i x y Hxy; simpl in Hxy; subst; reflexivity. Qed.
Next Obligation. intros c pi x y f j; simpl; now rewrite id_left. Qed.
Next Obligation. intros c pi x y f j; simpl; now rewrite id_left. Qed.

(* The generic element: transport the identity back across [wlim_iso]. / 通用元素：将身份传回 [wlim_iso]。 *)
Definition wpow_ev (j : J) : wlim_obj WL ~> b :=
  from (wlim_iso WL (wlim_obj WL)) id ttt j.

(* The only place [wlim_natural] is spent: the inverse transpose of [u] is the generic element precomposed with [u]. / [wlim_natural] 被消耗的唯一地方：[u] 的逆转置是与 [u] 预组合的通用元素。 *)
Lemma wpow_from_is_precompose (c : C) (u : c ~> wlim_obj WL) (j : J) :
  from (wlim_iso WL c) u ttt j ≈ wpow_ev j ∘ u.
Proof.
  unfold wpow_ev.
  set (al := from (wlim_iso WL (wlim_obj WL)) id).
  set (uc := nat_compose (HomDiagram_precompose u (power_diagram b)) al).
  assert (Hnat : to (wlim_iso WL c) uc ≈ u).
  { unfold uc; rewrite (wlim_natural WL (wlim_obj WL) c u al).
    assert (Ht : to (wlim_iso WL (wlim_obj WL)) al ≈ id).
    { unfold al; exact (iso_to_from (wlim_iso WL (wlim_obj WL)) id). }
    rewrite Ht; apply id_left. }
  assert (Hb : from (wlim_iso WL c) (to (wlim_iso WL c) uc)
                 ≈ from (wlim_iso WL c) u).
  { apply proper_morphism; exact Hnat. }
  transitivity (from (wlim_iso WL c) (to (wlim_iso WL c) uc) ttt j).
  - symmetry; exact (Hb ttt j).
  - exact (iso_from_to (wlim_iso WL c) uc ttt j).
Qed.

Definition power_of_weighted : IsPower b (wlim_obj WL) wpow_ev.
Proof.
  apply Build_IsPower; intros c pi.
  exists (to (wlim_iso WL c) (wpow_cone c pi)).
  - intro j.
    rewrite <- (wpow_from_is_precompose c _ j).
    exact (iso_from_to (wlim_iso WL c) (wpow_cone c pi) ttt j).
  - intros v Hv.
    rewrite <- (iso_to_from (wlim_iso WL c) v).
    apply proper_morphism.
    intros x j; destruct x; simpl.
    rewrite (wpow_from_is_precompose c v j).
    symmetry; exact (Hv j).
Defined.

End WeightedPowerConverse.

Section WeightedCopowerConverse.

Context {C : Category}.
Context (J : Type).
Context (b : C).
Context (WL : WeightedColimit (copower_weight J) (copower_diagram b)).

Program Definition wcop_cocone (c : C) (iota : ∀ _ : J, b ~{C}~> c) :
  copower_weight J
    ⟹ HomDiagram (C:=C^op) c (Opposite_Functor (copower_diagram b)) := {|
  transform := fun _ => {| morphism := iota |}
|}.
Next Obligation.
  intros c iota i x y Hxy; simpl in Hxy; subst; reflexivity.
Qed.
Next Obligation. intros c iota x y f j; simpl; now rewrite id_right. Qed.
Next Obligation. intros c iota x y f j; simpl; now rewrite id_right. Qed.

Definition wcop_inj (j : J) : b ~{C}~> wlim_obj WL :=
  from (wlim_iso WL (wlim_obj WL)) id ttt j.

Lemma wcop_from_is_postcompose (c : C) (u : wlim_obj WL ~{C}~> c)
  (j : J) : from (wlim_iso WL c) u ttt j ≈ u ∘[C] wcop_inj j.
Proof.
  unfold wcop_inj.
  set (al := from (wlim_iso WL (wlim_obj WL)) id).
  set (uc := nat_compose
               (HomDiagram_precompose (C:=C^op) u
                  (Opposite_Functor (copower_diagram b))) al).
  assert (Hnat : to (wlim_iso WL c) uc ≈ u).
  { unfold uc; rewrite (wlim_natural WL (wlim_obj WL) c u al).
    assert (Ht : to (wlim_iso WL (wlim_obj WL)) al ≈ id).
    { unfold al; exact (iso_to_from (wlim_iso WL (wlim_obj WL)) id). }
    rewrite Ht; cat. }
  assert (Hb : from (wlim_iso WL c) (to (wlim_iso WL c) uc)
                 ≈ from (wlim_iso WL c) u).
  { apply proper_morphism; exact Hnat. }
  transitivity (from (wlim_iso WL c) (to (wlim_iso WL c) uc) ttt j).
  - symmetry; exact (Hb ttt j).
  - exact (iso_from_to (wlim_iso WL c) uc ttt j).
Qed.

Definition copower_of_weighted : IsCopower b (wlim_obj WL) wcop_inj.
Proof.
  apply Build_IsCopower; intros c iota.
  exists (to (wlim_iso WL c) (wcop_cocone c iota)).
  - intro j.
    rewrite <- (wcop_from_is_postcompose c _ j).
    exact (iso_from_to (wlim_iso WL c) (wcop_cocone c iota) ttt j).
  - intros v Hv.
    rewrite <- (iso_to_from (wlim_iso WL c) v).
    apply proper_morphism.
    intros x j; destruct x; simpl.
    rewrite (wcop_from_is_postcompose c v j).
    symmetry; exact (Hv j).
Defined.

End WeightedCopowerConverse.

(*
 The round trip returns the chosen data with ONE identity residue on each
 side, exhibited here rather than described. 

 --------
 往返返回所选数据，每一侧都有一个身份残基，这里展示而不是描述。
*)

Section WeightedRoundTrip.

Context {C : Category}.
Context {HP : @HasIndexedProducts C}.
Context {HC : @HasIndexedCoproducts C}.
Context (J : Type).
Context (b : C).

Definition wrt_ev (j : J) : power J b ~{C}~> b :=
  wpow_ev J b (power_WeightedLimit J b) j.

Example wrt_ev_residue (j : J) : wrt_ev j = power_ev J b j ∘[C] id
  := eq_refl.

Lemma wrt_ev_equiv (j : J) : wrt_ev j ≈ power_ev J b j.
Proof. exact (@id_right C _ _ (power_ev J b j)). Qed.

Definition wrt_inj (j : J) : b ~{C}~> copower J b :=
  wcop_inj J b (copower_WeightedColimit J b) j.

Example wrt_inj_residue (j : J) : wrt_inj j = id ∘[C] copower_inj J b j
  := eq_refl.

Lemma wrt_inj_equiv (j : J) : wrt_inj j ≈ copower_inj J b j.
Proof. exact (@id_left C _ _ (copower_inj J b j)). Qed.

End WeightedRoundTrip.

(*
   * ** D0. The copower BIFUNCTOR, which BOTH parameter readings share

   [(b, J) ↦ J · b] is functorial in both arguments at once.  §D fixes the
   OBJECT and varies the index (Mac Lane's Ex 1 reads the object as the
   parameter); §E fixes the index and varies the object.  They are two
   parametrizations of this ONE bifunctor, and neither implies the other.

   The index category is [Coq], not [Sets], and that is FORCED: the copower
   injections are indexed by ELEMENTS, so [fmap_respects] demands
   [f j = f' j] at LEIBNIZ equality from [f ≈ f'].  [Coq]'s hom-setoid is
   pointwise Leibniz and supplies it; [Sets]' does not, and the probe
   carries an axiom-free countermodel refuting the CANONICAL arrow action
   over [Sets] -- the copower mediator of the injections -- outright rather
   than merely recording that the obvious proof does not go through.  No
   other arrow action over [Sets] is claimed refuted. 

   --------
   * ** D0. 共幂双函子，两个参数读法都共有的

   [(b, J) ↦ J · b] 在两个参数上都是函子的。§D 固定对象并改变指标（Mac Lane 的例 1 将对象视为参数）；§E 固定指标并改变对象。它们是这个唯一双函子的两种参数化方式，且彼此不蕴含。索引类别是 [Coq]，而不是 [Sets]，而且这是强制性的：余幂注入是由元素索引的，所以 [fmap_respects] 在 LEIBNIZ 等式下要求 [f j = f' j] 来自 [f ≈ f']。[Coq] 的同态集是逐点 Leibniz 并提供它；[Sets] 则不提供，并且探针带来了无公理的反模型，从而直接反驳了 [Sets] 上的规范箭头作用——也就是注入的余幂调解器——而不仅仅是记录明显的证明无法进行。没有声称其他在 [Sets] 上的箭头作用被反驳。
*)

Section CopowerBifunctor.

Context {C : Category}.
Context {HC : @HasIndexedCoproducts C}.

Definition cop_bifun_fmap (p q : C * Type)
  (gf : (fst p ~{C}~> fst q) * (snd p ~{Coq}~> snd q)) :
  copower (snd p) (fst p) ~> copower (snd q) (fst q) :=
  unique_obj (copower_desc (copower_ump (snd p) (fst p))
    (fun j : snd p =>
       copower_inj (snd q) (fst q) (snd gf j) ∘ fst gf)).

Lemma cop_bifun_inj (p q : C * Type)
  (gf : (fst p ~{C}~> fst q) * (snd p ~{Coq}~> snd q)) (j : snd p) :
  cop_bifun_fmap p q gf ∘ copower_inj (snd p) (fst p) j
    ≈ copower_inj (snd q) (fst q) (snd gf j) ∘ fst gf.
Proof.
  exact (unique_property (copower_desc (copower_ump (snd p) (fst p)) _) j).
Qed.

Program Definition Copower_Bifunctor : C ∏ Coq ⟶ C := {|
  fobj := fun p => copower (snd p) (fst p) ;
  fmap := fun p q gf => cop_bifun_fmap p q gf
|}.
Next Obligation.
  intros p q gf gf' [Hg Hf].
  apply (uniqueness (copower_desc (copower_ump (snd p) (fst p)) _)).
  intros j; rewrite cop_bifun_inj.
  destruct gf as [g f], gf' as [g' f']; simpl in *.
  rewrite Hg; now rewrite (Hf j).
Qed.
Next Obligation.
  intros p.
  apply (uniqueness (copower_desc (copower_ump (snd p) (fst p)) _)).
  intros j; simpl; now rewrite id_left, id_right.
Qed.
Next Obligation.
  intros p q r gf hk.
  apply (uniqueness (copower_desc (copower_ump (snd p) (fst p)) _)).
  intros j.
  rewrite <- comp_assoc, cop_bifun_inj.
  rewrite comp_assoc, cop_bifun_inj.
  now rewrite <- !comp_assoc.
Qed.

Example copower_bifunctor_obj (J : Type) (b : C) :
  fobj[Copower_Bifunctor] (b, J) = copower J b := eq_refl.

Example copower_bifunctor_partial_obj (J : Type) (b : C) :
  fobj[Partial_l Copower_Bifunctor J] b = fobj[Copower_Functor J] b
  := eq_refl.

Example copower_bifunctor_partial_fmap (J : Type) {b b' : C} (g : b ~> b') :
  fmap[Partial_l Copower_Bifunctor J] g = fmap[Copower_Functor J] g
  := eq_refl.

End CopowerBifunctor.

Arguments Copower_Bifunctor {C HC}.

(*
   * ** D1. Mac Lane §IV.7 Exercise 1, UNRESTRICTED

   The displayed isomorphism of the exercise, in its CORRECTED form
   [C(J · a, c) ≅ Set(J, C(a,c))], upgraded from a family of bijections to
   an isomorphism of BIFUNCTORS on [C^op ∏ C] -- which is what "natural in
   the parameter a" asks for.  No hypothesis beyond [HasIndexedCoproducts].

   The right-hand side is [Power_Functor] AT [Sets] composed with the
   hom-bifunctor: Mac Lane's [Set(J, −)] is §A's own power functor. 

   --------
   * ** D1. Mac Lane §IV.7 练习 1，无限制

   显示的同构在练习中的修正形式  
   [C(J · a, c) ≅ Set(J, C(a,c))]，从一族双射升级为  
   [C^op ∏ C] 上的双函子同构——这就是“在参数 a 下自然”所要求的。除了 [HasIndexedCoproducts] 外，无需假设。

   右侧是 [Power_Functor] 在 [Sets] 上与 Hom-双函子组成的：Mac Lane 的 [Set(J, −)] 就是 §A 自身的幂函子。
*)

Section ObjectParameterUnrestricted.

Context {C : Category}.
Context {HC : @HasIndexedCoproducts C}.
Context (J : Type).

Definition CopLeft : C^op ∏ C ⟶ Sets :=
  Hom C ◯ ((Opposite_Functor (Copower_Functor J)) ∏⟶ Id[C]).

Definition CopRight : C^op ∏ C ⟶ Sets :=
  @Power_Functor Sets Sets_HasIndexedProducts J ◯ Hom C.

Example copleft_obj (a c : C) :
  fobj[CopLeft] (a, c)
  = {| carrier := @hom C (copower J a) c
     ; is_setoid := @homset C (copower J a) c |} := eq_refl.

Example copright_obj (a c : C) :
  fobj[CopRight] (a, c)
  = @power Sets Sets_HasIndexedProducts J
      {| carrier := @hom C a c ; is_setoid := @homset C a c |} := eq_refl.

Program Definition cop_nat : CopLeft ⟹ CopRight := {|
  transform := fun p =>
    to (copower_hom_iso_at (@copower_ump C HC J (fst p)) (snd p))
|}.
Next Obligation.
  intros [a c] [a' c'] [h k] u j; simpl in *.
  rewrite <- !comp_assoc.
  now rewrite (@power_fmap_ev (C^op) HC J a a' h j).
Qed.
Next Obligation.
  intros [a c] [a' c'] [h k] u j; simpl in *.
  rewrite <- !comp_assoc.
  now rewrite (@power_fmap_ev (C^op) HC J a a' h j).
Qed.

Definition cop_nat_pointwise (p : C^op ∏ C) :
  IsIsomorphism (transform[cop_nat] p) :=
  @Build_IsIsomorphism Sets _ _ _
    (from (copower_hom_iso_at (@copower_ump C HC J (fst p)) (snd p)))
    (iso_to_from (copower_hom_iso_at (@copower_ump C HC J (fst p)) (snd p)))
    (iso_from_to (copower_hom_iso_at (@copower_ump C HC J (fst p)) (snd p))).

Definition Copower_Bifunctor_Iso :
  @Isomorphism ([C^op ∏ C, Sets]) CopLeft CopRight :=
  @IsIsoToIso ([C^op ∏ C, Sets]) _ _ cop_nat
    (componentwise_iso cop_nat cop_nat_pointwise).

End ObjectParameterUnrestricted.

Arguments CopLeft {C HC} J.
Arguments CopRight {C} J.
Arguments Copower_Bifunctor_Iso {C HC} J.

(*
   * ** D2. Mac Lane §IV.7 Exercise 1, PACKAGED as an adjunction with a
   parameter -- and the punchline, that the assembled right adjoint IS the
   hom-functor

   The packaging needs the right adjoint [C(a,−)] to land in the SAME index
   category the copower is indexed by, and there the two demands pull
   against each other: the copower wants LEIBNIZ equality on the index, the
   hom-functor wants [C]'s own [≈].  [HomAllStrict C] is exactly the
   hypothesis under which they coincide, and it is disclosed as an explicit
   argument rather than hidden.  It is inhabited in tree -- degenerately,
   by the terminal category, whose hom-setoid IS [Morphism_equality]. 

   --------
   * ** D2. Mac Lane §IV.7 练习 1，封装为带参数的伴随关系 -- 以及重点是，组装好的右伴随确实就是 Hom 函子。

   封装需要右伴随 [C(a,−)] 落在与copower索引相同的范畴上，在这里这两个要求相互冲突：copower 希望索引上是 LEIBNIZ 相等，而 Hom 函子希望 [C] 拥有自己的 [≈]。[HomAllStrict C] 正是它们一致的假设，并且它以显式参数形式展现，而非隐藏。在树中是可居住的——退化地，由终范畴给出，其 Hom-集确实是 [Morphism_equality]。
*)

(*
 [Construction/Comma/Special.v] already declares this hypothesis at a
 FIXED pair of objects, for exactly this reason (its [Full] criterion for
 the discrete-hom comparison), so it is CONSUMED here and quantified over
 all objects rather than redeclared.  Its [Blur_HomStrict_absurd] is a
 compiled witness of a category where the per-hom-set form is refutable. 

 --------
 [Construction/Comma/Special.v] 已经在一对固定对象上声明了这个假设，正是出于这个原因（它用于离散同态比较的 [Full] 标准），所以它在这里被使用，并对所有对象进行量化，而不是重新声明。它的 [Blur_HomStrict_absurd] 是一个编译过的证据，属于一个类别，其中每个 Hom 集的形式是可驳的。
*)
Definition HomAllStrict (C : Category) : Type :=
  ∀ x y : C, @HomStrict C x y.

Section ObjectParameterPackaged.

Context {C : Category}.
Context {HC : @HasIndexedCoproducts C}.
Context (HS : HomAllStrict C).

Program Definition HomCoq (a : C) : C ⟶ Coq := {|
  fobj := fun c => @hom C a c ;
  fmap := fun c c' (k : c ~> c') => fun h : a ~> c => k ∘ h
|}.
Next Obligation. intros a c c' k k' Hk h; now rewrite (HS _ _ _ _ Hk). Qed.
Next Obligation. intros a c h; apply HS; apply id_left. Qed.
Next Obligation.
  intros a x y z k k' h; apply HS; simpl; symmetry; apply comp_assoc.
Qed.

(* The SAME bifunctor as §D0, with its two arguments exchanged so that the OBJECT sits in the parameter slot [P] of [ParametrizedAdjunction]. / 与§D0相同的双函子，其两个参数交换位置，使得对象位于[ParametrizedAdjunction]的参数槽[P]中。 *)
Definition Ex1_Bifunctor : Coq ∏ C ⟶ C := Copower_Bifunctor ◯ Swap.

Example ex1_bifunctor_obj (J : Type) (a : C) :
  fobj[Ex1_Bifunctor] (J, a) = copower J a := eq_refl.

Example ex1_partial_obj (a : C) (J : Type) :
  fobj[Partial_l Ex1_Bifunctor a] J = copower J a := eq_refl.

Lemma ex1_partial_inj (a : C) {J J' : Type} (h : J ~{Coq}~> J') (j : J) :
  fmap[Partial_l Ex1_Bifunctor a] h ∘ copower_inj J a j
    ≈ copower_inj J' a (h j) ∘ id.
Proof.
  unfold Partial_l, Ex1_Bifunctor; simpl; unfold bimap; simpl.
  exact (cop_bifun_inj (a, J) (a, J') (id, h) j).
Qed.

Program Definition ex1_adj_iso (a : C) (J : Type) (c : C) :
  @Isomorphism Sets
    {| carrier := @hom C (fobj[Partial_l Ex1_Bifunctor a] J) c
     ; is_setoid := @homset C (fobj[Partial_l Ex1_Bifunctor a] J) c |}
    {| carrier := @hom Coq J (fobj[HomCoq a] c)
     ; is_setoid := @homset Coq J (fobj[HomCoq a] c) |} :=
  {| to   := {| morphism := fun u => fun j : J => u ∘ copower_inj J a j |}
   ; from := {| morphism := fun fam : J → (a ~> c) =>
                  unique_obj (copower_desc (copower_ump J a) fam) |} |}.
Next Obligation. intros a J c u u' Hu j; apply HS; now rewrite Hu. Qed.
Next Obligation.
  intros a J c fam fam' Hfam.
  apply (uniqueness (copower_desc (copower_ump J a) fam)).
  intros j.
  rewrite (unique_property (copower_desc (copower_ump J a) fam') j).
  now rewrite (Hfam j).
Qed.
Next Obligation.
  intros a J c fam j; simpl.
  apply HS.
  exact (unique_property (copower_desc (copower_ump J a) fam) j).
Qed.
Next Obligation.
  intros a J c u; simpl.
  apply (uniqueness (copower_desc (copower_ump J a)
                       (fun j : J => u ∘ copower_inj J a j))).
  intros j; reflexivity.
Qed.

Example ex1_to_char (a : C) (J : Type) (c : C)
  (u : copower J a ~> c) (j : J) :
  to (ex1_adj_iso a J c) u j = u ∘ copower_inj J a j := eq_refl.

Definition ex1_pa_adj (a : C) : Partial_l Ex1_Bifunctor a ⊣ HomCoq a.
Proof.
  unshelve eapply (@Build_Adjunction' C Coq (Partial_l Ex1_Bifunctor a)
                     (HomCoq a) (ex1_adj_iso a)).
  - intros x y z f g j; simpl.
    apply HS.
    rewrite <- comp_assoc.
    rewrite (ex1_partial_inj a g j).
    now rewrite id_right.
  - intros x y z f g j; simpl.
    apply HS; symmetry; apply comp_assoc.
Defined.

Definition Copower_Object_ParametrizedAdjunction :
  ParametrizedAdjunction Ex1_Bifunctor := {|
  pa_right := HomCoq ;
  pa_adj   := ex1_pa_adj
|}.

(*
 ★ THE PUNCHLINE.  #396's Theorem 3 assembles the right adjoints into a
 bifunctor contravariant in the parameter, and that bifunctor IS the
 hom-functor of [C] -- on objects definitionally, on arrows pointwise. 

 --------
 ★ 笑点。#396 定理 3 将右伴随函子组装成一个在参数上反变的双函子，而这个双函子就是 [C] 的同构函子 —— 在对象上是定义上的，在箭头上是按点定义的。
*)
Definition MacLane_Ex1_hom_bifunctor : C^op ∏ C ⟶ Coq :=
  @parametrized_right_adjoint_bifunctor Coq C C Ex1_Bifunctor
    Copower_Object_ParametrizedAdjunction.

Example ex1_hom_bifunctor_obj (a c : C) :
  fobj[MacLane_Ex1_hom_bifunctor] (a, c) = (a ~{C}~> c) := eq_refl.

Example ex1_pa_right_is_HomCoq (a : C) :
  pa_right Copower_Object_ParametrizedAdjunction a = HomCoq a := eq_refl.

Lemma ex1_counit_inj (a c : C) (g : a ~> c) :
  @counit C Coq (Partial_l Ex1_Bifunctor a) (HomCoq a) (ex1_pa_adj a) c
    ∘ copower_inj (a ~> c) a g ≈ g.
Proof.
  exact (unique_property
           (copower_desc (copower_ump (a ~> c) a) (fun i : a ~> c => i)) g).
Qed.

(*
 The parameter mate is PRECOMPOSITION -- read off [conj_mate]'s own
 component formula, not recomputed. 

 --------
 参数 mate 是 PRECOMPOSITION —— 读取 [conj_mate] 自己的组件公式，而不是重新计算。
*)
Lemma ex1_param_mate_precomp {a a' : C} (h : a' ~> a) (c : C)
  (g : a ~> c) :
  pa_param_mate Copower_Object_ParametrizedAdjunction h c g = g ∘ h.
Proof.
  unfold pa_param_mate, conj_mate; simpl.
  apply HS.
  rewrite <- comp_assoc.
  rewrite (cop_bifun_inj (a', (a ~> c)) (a, (a ~> c)) (h, id) g).
  simpl.
  rewrite comp_assoc.
  apply compose_respects; [ apply ex1_counit_inj | reflexivity ].
Qed.

Lemma ex1_hom_bifunctor_fmap {a a' c c' : C}
  (h : a ~{C^op}~> a') (k : c ~> c') (g : a ~> c) :
  fmap[MacLane_Ex1_hom_bifunctor] ((h, k) : (a, c) ~{C^op ∏ C}~> (a', c'))
    g = k ∘ g ∘ unop h.
Proof.
  etransitivity.
  { apply (f_equal (fun x : a' ~> c => k ∘ x)).
    exact (ex1_param_mate_precomp (unop h) c g). }
  apply HS; apply comp_assoc.
Qed.

End ObjectParameterPackaged.

Arguments HomCoq {C} HS a.
Arguments Ex1_Bifunctor {C HC}.

(*
 ** [HomAllStrict] is inhabited in tree, degenerately

 [_1]'s hom-setoid IS [Morphism_equality] (Instance/One.v), so
 [HomAllStrict _1] is the identity implication -- which is also the donor's
 own [One_HomStrict] (Construction/Comma/Special.v), there at the
 single object pair.  The witness exercises the
 HYPOTHESES and the assembly, not the conclusion: everything in [1]
 collapses to [ttt]. 

 --------
 **  [HomAllStrict]  在树中被占据，退化地

 [_1] 的同态集合是  [Morphism_equality]  (Instance/One.v)，因此
 [HomAllStrict _1]  是恒等蕴涵 —— 这也是捐赠者自身的
 [One_HomStrict]  (Construction/Comma/Special.v)，在单对象对处。 见证者行使
 假设和组合，而非结论：[1] 中的所有内容都塌缩为 [ttt] 。
*)

Definition One_HomAllStrict : HomAllStrict _1 := fun _ _ _ _ H => H.

Lemma one_hom_eq {x y : _1} (f g : x ~{_1}~> y) : f = g.
Proof. destruct f, g; reflexivity. Qed.

Definition One_iprod_ump {A : Type} (f : A → _1) :
  IsIndexedProduct f ttt (fun _ => ttt).
Proof.
  constructor; intros c pi.
  exists ttt.
  - intros a; apply one_hom_eq.
  - intros v Hv; apply one_hom_eq.
Defined.

Definition One_icoprod_ump {A : Type} (f : A → _1) :
  @IsIndexedCoproduct _1 A f ttt (fun _ => ttt).
Proof.
  constructor; intros c pi.
  exists ttt.
  - intros a; apply one_hom_eq.
  - intros v Hv; apply one_hom_eq.
Defined.

Definition One_HasIndexedProducts : @HasIndexedProducts _1 :=
  @Build_HasIndexedProducts _1 (fun A f => ttt) (fun A f a => ttt)
    (@One_iprod_ump).

Definition One_HasIndexedCoproducts : @HasIndexedCoproducts _1 :=
  @Build_HasIndexedCoproducts _1 (fun A f => ttt) (fun A f a => ttt)
    (@One_icoprod_ump).

Definition One_Ex1_ParametrizedAdjunction :
  ParametrizedAdjunction (@Ex1_Bifunctor _1 One_HasIndexedCoproducts) :=
  @Copower_Object_ParametrizedAdjunction _1 One_HasIndexedCoproducts
    One_HomAllStrict.

(*
   * ** E. The issue's own item 4: the INDEX SET as the parameter

   Here the parameter slot of [ParametrizedAdjunction] holds the index and
   the varying argument is the object, so the partial functors ARE §A's
   copower functors and the right adjoints ARE §A's power functors.  A
   function between index sets induces a transformation of copower functors
   whose CONJUGATE is the induced transformation of power functors, and
   that conjugacy is #396's [pa_natural_p] consumed, not recomputed. 

   --------
   * ** E. 该问题自身的第4项：作为参数的索引集合

   在这里，[ParametrizedAdjunction] 的参数槽包含索引，而可变参数是对象，因此部分函子是 §A 的余幂函子，右伴函子是 §A 的幂函子。索引集合之间的函数会引起余幂函子的变换，其共轭是幂函子的诱导变换，并且该共轭是 #396 的 [pa_natural_p] 已消费的，而不是重新计算的。
*)

Section IndexParameter.

Context {C : Category}.
Context {HP : @HasIndexedProducts C}.
Context {HC : @HasIndexedCoproducts C}.

(*
 The §B isomorphism ASCRIBES at the partial functor (both [fobj]s reduce
 to [copower J b]); the §B ADJUNCTION does not, because [Adjunction] is
 indexed by the functor RECORD.  Both facts are pinned in the probe. 

 --------
 §B 同构归因于部分函子（两个 [fobj] 都简化为 [copower J b]）；§B 伴随没有归因，因为 [Adjunction] 是由函子 RECORD 索引的。这两个事实都固定在探针中。
*)
Definition cp_pa_iso (J : Type) (b c : C) :
  @Isomorphism Sets
    {| carrier := @hom C (fobj[Partial_l Copower_Bifunctor J] b) c
     ; is_setoid := @homset C (fobj[Partial_l Copower_Bifunctor J] b) c |}
    {| carrier := @hom C b (fobj[Power_Functor J] c)
     ; is_setoid := @homset C b (fobj[Power_Functor J] c) |} :=
  cp_adj_iso J b c.

Lemma cp_partial_inj (J : Type) {b b' : C} (g : b ~> b') (j : J) :
  fmap[Partial_l Copower_Bifunctor J] g ∘ copower_inj J b j
    ≈ copower_inj J b' j ∘ g.
Proof.
  unfold Partial_l; simpl; unfold bimap; simpl.
  now rewrite (cop_bifun_inj (b, J) (b', J) (g, id) j).
Qed.

(* [cp_to_char] restated in the spelling these goals present: [rewrite] is syntactic and will not see through the [cp_pa_iso] delta. / [cp_to_char] 用拼写重新表述这些目标：[rewrite] 是句法上的，无法看穿 [cp_pa_iso] 的差异。 *)
Lemma cp_pa_char (J : Type) (b c : C) (u : copower J b ~> c) (j : J) :
  power_ev J c j ∘ to (cp_pa_iso J b c) u ≈ u ∘ copower_inj J b j.
Proof. exact (cp_to_char J b c u j). Qed.

Definition cp_pa_adj (J : Type) :
  Partial_l Copower_Bifunctor J ⊣ Power_Functor J.
Proof.
  unshelve eapply (Build_Adjunction' (cp_pa_iso J)).
  - intros x y z f g.
    apply cp_to_uniq; intros j.
    rewrite comp_assoc, cp_pa_char.
    rewrite <- !comp_assoc.
    apply compose_respects; [ reflexivity |].
    symmetry; exact (cp_partial_inj J g j).
  - intros x y z f g.
    apply cp_to_uniq; intros j.
    rewrite comp_assoc.
    rewrite (power_functor_ev J f j).
    rewrite <- !comp_assoc; now rewrite (cp_pa_char J x y g j).
Defined.

Definition Copower_ParametrizedAdjunction :
  ParametrizedAdjunction Copower_Bifunctor := {|
  pa_right := fun J : Coq => Power_Functor J;
  pa_adj   := cp_pa_adj
|}.

Definition Power_Bifunctor : Coq^op ∏ C ⟶ C :=
  @parametrized_right_adjoint_bifunctor C Coq C Copower_Bifunctor
    Copower_ParametrizedAdjunction.

Example power_bifunctor_obj (J : Type) (b : C) :
  fobj[Power_Bifunctor] (J, b) = power J b := eq_refl.

Example pa_right_is_power_functor (J : Type) :
  pa_right Copower_ParametrizedAdjunction J = Power_Functor J := eq_refl.

(*
 The parametrized adjunction's own hom-set isomorphism at each index IS
 §B's, on the nose -- so §E does not fork §B's bijection. 

 --------
 在每个索引处，参数化伴随的自身同态集合同构正是 §B 的同构——因此 §E 不会干扰 §B 的双射。
*)
Example pa_adj_iso_is_cp_adj_iso (J : Type) (b c : C) :
  @adj C C (Partial_l Copower_Bifunctor J) (Power_Functor J)
    (pa_adj Copower_ParametrizedAdjunction J) b c
  = cp_adj_iso J b c := eq_refl.

End IndexParameter.

Arguments cp_pa_adj {C HP HC} J.
Arguments Copower_ParametrizedAdjunction {C HP HC}.
Arguments Power_Bifunctor {C HP HC}.

Section IndexReindexing.

Context {C : Category}.
Context {HP : @HasIndexedProducts C}.
Context {HC : @HasIndexedCoproducts C}.

Notation PA := (@Copower_ParametrizedAdjunction C HP HC).
Notation CB := (@Copower_Bifunctor C HC).

(* Reindexing the COPOWER, covariantly in the index set. / 对 COPOWER 进行重索引，在索引集中协变地进行。 *)
Definition copower_reindex {J J' : Type} (h : J ~{Coq}~> J') :
  Partial_l CB J ⟹ Partial_l CB J' := param_transform CB h.

Lemma copower_reindex_inj {J J' : Type} (h : J ~{Coq}~> J') (b : C) (j : J) :
  copower_reindex h b ∘ copower_inj J b j ≈ copower_inj J' b (h j) ∘ id.
Proof. exact (cop_bifun_inj (b, J) (b, J') (id, h) j). Qed.

(* Reindexing the POWER, CONTRAVARIANTLY: #396's conjugate mate, consumed. / 以逆变方式重新索引 POWER：#396 的共轭搭档，已消耗。 *)
Definition power_reindex {J J' : Type} (h : J' ~{Coq}~> J) :
  Power_Functor J ⟹ Power_Functor J' := pa_param_mate PA h.

Example power_reindex_is_conj_mate {J J' : Type} (h : J' ~{Coq}~> J) :
  power_reindex h
    = conj_mate (pa_adj PA J) (pa_adj PA J') (param_transform CB h) := eq_refl.

(*
 The counit of the parametrized adjunction at the index [J], read through
 the copower injections: it IS the evaluation, with one identity residue. 

 --------
 在索引 [J] 处参数化伴随的余单位，通过余幂注入读取：它就是求值，只带有一个恒等的残差。
*)
Lemma cp_pa_counit_inj (J : Type) (b : C) (j : J) :
  @counit C C (Partial_l CB J) (Power_Functor J) (pa_adj PA J) b
    ∘ copower_inj J (power J b) j ≈ power_ev J b j.
Proof.
  etransitivity.
  - exact (unique_property
             (copower_desc (copower_ump J (power J b))
                (fun i : J => power_ev J b i ∘ id)) j).
  - apply id_right.
Qed.

(* The contravariant reindexing of powers is evaluation at [h j']. / 幂的逆变重索引是在 [h j'] 上的评估。 *)
Lemma power_reindex_ev {J J' : Type} (h : J' ~{Coq}~> J) (b : C) (j' : J') :
  power_ev J' b j' ∘ power_reindex h b ≈ power_ev J b (h j').
Proof.
  unfold power_reindex, pa_param_mate, conj_mate; simpl.
  etransitivity.
  { exact (unique_property (power_desc (power_ump J' b) _) j'). }
  rewrite <- comp_assoc.
  rewrite (copower_reindex_inj h (power J b) j').
  rewrite id_right.
  apply cp_pa_counit_inj.
Qed.

(*
 ★ THE CONJUGACY, CONSUMED.  [pa_natural_p] is #396's theorem and
 [pa_square_is_Conjugate] says the square IS #394's [Conjugate] on the
 nose, so the ascription below is the whole proof. 

 --------
 ★ 共轭，已消耗。[pa_natural_p] 是 #396 的定理，而 [pa_square_is_Conjugate] 说平方就是 #394 的 [Conjugate]，完全正确，所以下面的归属就是整个证明。
*)
Definition power_reindex_conjugate {J J' : Type} (h : J' ~{Coq}~> J) :
  Conjugate (pa_adj PA J) (pa_adj PA J')
            (copower_reindex h) (power_reindex h) :=
  pa_natural_p PA h.

(* And it is the UNIQUE such transformation. / 而且这是唯一的这种变换。 *)
Definition power_reindex_universal {J J' : Type} (h : J' ~{Coq}~> J) :
  ∃! tau : Power_Functor J ⟹ Power_Functor J',
    Conjugate (pa_adj PA J) (pa_adj PA J') (copower_reindex h) tau :=
  pa_param_mate_universal PA h.

Corollary power_reindex_id (J : Type) : power_reindex (@id Coq J) ≈ nat_id.
Proof. exact (pa_param_mate_id PA). Qed.

Corollary power_reindex_comp {J J' J'' : Type}
  (h : J' ~{Coq}~> J) (h' : J'' ~{Coq}~> J') :
  power_reindex (h ∘ h') ≈ power_reindex h' ∙ power_reindex h.
Proof. exact (pa_param_mate_comp PA h h'). Qed.

Corollary copower_reindex_id (J : Type) :
  copower_reindex (@id Coq J) ≈ nat_id.
Proof. exact (param_transform_id CB). Qed.

Corollary copower_reindex_comp {J J' J'' : Type}
  (h : J ~{Coq}~> J') (h' : J' ~{Coq}~> J'') :
  copower_reindex (h' ∘ h) ≈ copower_reindex h' ∙ copower_reindex h.
Proof. exact (param_transform_comp CB h h'). Qed.

End IndexReindexing.
