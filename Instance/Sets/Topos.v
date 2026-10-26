Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.Topos.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Sets.Classifier.OneLevel.

Open Scope category_scope.

(* * * The category of setoids is an elementary topos / * * 集合等价类的范畴是一个初等拓扑 *)

(*
 Book:      Mac Lane, Categories for the Working Mathematician, 2nd
 ed., §IV.10, printed p. 107 (PDF p. 116)
 ([maclane:IV.10:remark1]).  Verbatim, from the rendered
 page:

 “The category Sets of all (small) sets is a topos and so
 is the category Sets^{C^op} of all set-valued
 contravariant functors on a small category C.”

 Book:      Mac Lane, ibid., Appendix “Foundations”, §App.1, printed
 pp. 289-290 (PDF pp. 295-296) ([maclane:App.1:remark1]).
 Verbatim, from the rendered pages.  His axioms 8 and 9,
 printed p. 289:

 “An elementary topos is a category with a certain
 additional structure: terminal object, pullbacks,
 truth, a subobject classifier, and power objects (sets
 of subsets).”

 “8. Truth.  There is an object Ω (the object of truth
 values) and a monomorphism t : 1 → Ω called truth; to
 any monomorphism m : a → b, there is a unique arrow
 ψ : b → Ω such that the following square is a
 pullback:”                                          (2)

 “9. Power objects.  To each object b, there is an
 associated object P b and an arrow ε_b : b × P b → Ω
 such that for every arrow f : b × a → Ω there is a
 unique arrow g : a → P b for which the following
 diagram commutes:”                                  (3)

 and the four witnesses, printed p. 290:

 “To understand these axioms, we observe how they apply
 to the usual category of all sets.  There, any set with
 just one element can serve as a terminal object 1,
 because each set a has a unique function a → 1 to 1.
 For two sets a and b, the pullback of two arrows
 a → 1 ← b is then the usual set-theoretic product, with
 its projections to the given factors a and b.”

 “For truth values, take the object Ω to be any set 2
 consisting of two objects, 1 and 0, while the
 monomorphism t : 1 → 2 is just the usual inclusion of 1
 in 2.  Then a monomorphism m : a → b, as in Axiom 8, is
 a subset a of b.  This subset has a well-known
 characteristic function ψ : b → 2 with ψ(y) = 1 or 0
 according as the element of y of b is or is not in the
 subset a.  This produces the pullback (2) above.”

 “Axiom 9 describes P b, the set of all subsets s of b,
 often called the ”power set“ P b.  Indeed, one can then
 set ε_b(x, s) = 0 if the element x of b is in the
 subset s and equal to 1 otherwise.  This does give a
 pullback, as in (3) above.”

 “These axioms for a topos then hold for the category of
 sets.”

 nLab:      https://ncatlab.org/nlab/show/topos
 Wikipedia: https://en.wikipedia.org/wiki/Topos

 TWO NOTES ON THE PRINTED PAGE, BOTH LEFT AS THEY STAND.

 First, “according as the element of y of b is or is not in the subset
 a” is the book's own wording, transcribed verbatim; the sense is
 plainly “the element y of b”.

 Second, and this one matters for the reading of clause (d): THE PAGE
 IS INTERNALLY INCONSISTENT ABOUT WHICH TRUTH VALUE MEANS MEMBERSHIP.
 Two sentences apart it says “ψ(y) = 1 or 0 according as the element
 of y of b is or is not in the subset a” and “ε_b(x, s) = 0 if the
 element x of b is in the subset s and equal to 1 otherwise” -- 1 for
 membership under ψ, 0 for membership under ε_b, on one page.  The
 issue's paraphrase silently corrects the second to “ε_b(x, s) = 1 iff
 x ∈ s”.  BOTH SENTENCES ARE QUOTED ABOVE AND NEITHER IS RESOLVED
 HERE.  Nothing below depends on the choice: the naming of the truth
 value is a convention, and this tree's convention is recorded, with
 its own measurements, in Instance/Sets/Classifier/OneLevel.v and
 Instance/Fun/Classifier.v.  What IS delivered is the classifying
 rule in the form those two files prove it -- section (C)'s
 [app1_char_rule_U] and [app1_char_rule_dec], which say that the
 characteristic map takes the value [truth] exactly on the image.

 WHAT IS DELIVERED.  THREE inhabitants of
 [ElementaryTopos Sets@{o so}], each CONDITIONAL on one hypothesis.
 Read the three apart carefully: [Sets_Topos_IEM] IS [Sets_Topos] at
 [eq_refl] (the table below writes it as the [:=] it is), so it shares
 BOTH its truth object and its power object and differs only in the
 hypothesis it takes; [Sets_Topos_dec] is the one that differs in
 both, and in its reach:

 Sets_Topos     (U : Untruncate@{o})   Ω = Powerset_Omega
 Sets_Topos_dec (D : DecImage@{o so})  Ω = BoolSetoid   -- Mac Lane's 2
 Sets_Topos_IEM (E : IEM@{o})          := Sets_Topos (untruncate_of_IEM E)

 together with Mac Lane's four App.1 witnesses at each measured
 strength, in sections (B)-(E).  All three bundles are plain
 [Definition]s, all three are Closed under the global context, and
 there is no obligation and no tactic in any of them.

 THE ROUTE IS PURE ASSEMBLY: five fields, five pre-existing donors,
 NOTHING re-proved.

 topos_terminal    Instance/Sets.v's [Sets_Terminal]
 topos_cartesian   Instance/Sets/Cartesian.v's [Sets_Cartesian]
 topos_pullbacks   Instance/Sets/Pullback.v's [Sets_HasPullbacks]
 topos_closed      Instance/Sets/Cartesian/Closed.v's [Sets_Closed]
 topos_classifier  Instance/Sets/Classifier/OneLevel.v's
 [Sets_Classifier] (with [Sets_Classifier_dec]
 on the decidable route)

 Instance/FinSet/Topos.v is NOT offered as a witness for anything
 here, and is not required by this file: the issue's reviewer check
 asks for exactly that, and its sibling Instance/Fun/Topos.v says the
 same on the presheaf side.

 WHY PLAIN [Definition]s AND NOT [Instance]s.  Instance/FinSet/Topos.v
 gives the reason and it is followed: the five [topos_*] projections
 are [#[export] Existing Instance]s, so registering a bundle would
 give typeclass search a second, convergent path to each component.
 MEASURED, at [Sets], in both directions: (i) the five projections ARE
 in the instance database, so FinSet's reason genuinely applies here
 -- [Print HintDb typeclass_instances] lists [simple apply
 @topos_terminal], [@topos_cartesian], [@topos_pullbacks],
 [@topos_closed] and [@topos_classifier]; and (ii) the harm is not
 observable today, because with the bundle registered globally all
 four unconditional components still resolve to the DIRECT instances
 and [@SubobjectClassifier Sets Sets_Terminal] still does not resolve,
 [Untruncate] being a [Definition] and not a [Class], so the
 [topos_classifier] path ends in an unresolvable metavariable.  Both
 readings are stated because either alone would mislead.  NOT
 MEASURED: whether the extra path costs search time.

 UNIVERSES, MEASURED OFF BOTH THE BINDER AND THE CONSTRAINT BLOCK.

 Sets_Topos@{o so} :
 Untruncate@{o} → ElementaryTopos@{so so o} Sets@{o so}
 block: Set < o, o < so, plus stdlib bounds.

 Sets_Topos_IEM@{o so} : IEM@{o} → ElementaryTopos@{so so o} Sets@{o so}
 block: the same.

 Sets_Topos_dec@{o so} :
 DecImage@{o so} → ElementaryTopos@{so so o} Sets@{o so}
 block: o < so, plus stdlib bounds -- and NO [Set] at all.

 pullback_over_one_is_product@{o so} :
 ∀ a b : obj[Sets@{o so}], pbone@{o so} a b ≅ a × b
 block: o < so, plus stdlib bounds.

 Read four things off that.

 (1) NOT ONE CONSTRAINT IN ANY BLOCK OF THIS FILE IS AN EQUATION.
 Every entry is [<] or [<=].  That is worth stating because it was NOT
 free for section (B): written inside a [Section] with
 [Context (a b : Sets)], the same pullback development elaborates at
 [pullback_over_one_is_product@{u u0 u1 u2}] with TWO block equations
 ([u = u1] and [u0 = u2]) identifying the two objects' [Sets] with
 each other.  The annotated top-level form shipped below carries none.
 So here the annotation buys more than presentation -- it is what
 keeps the file equation-free -- unlike the bundles, where an
 unannotated body gives the same reading up to renaming.

 (2) NOTHING IS PINNED TO [Set].  [Set < o] is a strict LOWER bound
 and it is on the [Untruncate]/[IEM] route only, arriving from
 [Prop : Type@{Set+1}] through [Powerset_Omega].

 (3) THE TWO ROUTES DIFFER IN REACH, AND THAT IS THE POINT OF SHIPPING
 BOTH.  In a section declaring [Set < su], [Sets@{Set su}] is a
 category, its four unconditional donors are all accepted at
 [@{su Set}], and [Sets_Topos_dec@{Set su}] is ACCEPTED -- while
 [Sets_Classifier@{Set su}] and [Sets_Topos@{Set su}] are each refused
 with “Cannot enforce Set < Set because Set = Set”.  So the decidable
 route reaches the [Sets] whose carrier universe is the literal [Set]
 and the truncation route does not.  Both refusals and the seven
 controls are pinned in Test/ProbeToposInstances404.v.  This
 corroborates at the TOPOS level what
 Instance/Sets/Classifier/OneLevel.v states at the classifier level.

 (4) THE CLASS'S OWN TWO COROLLARIES DO NOT BOTH REACH THIS TOPOS.
 [Pow] does; [relations_iso] does NOT, and neither does
 [classifier_classifies].  Both carry the bound [u <= u0] over
 [C : Category@{u u0 u0}] -- objects at or below homs -- while
 [Sets@{o so} : Category@{so o o}] has o < so, and
 [relations_iso] is built as [iso_compose exp_iso
 (classifier_classifies (a × b))], so it inherits the refusal.  Both
 are pinned in the probe, with [Pow] at this topos as the accepted
 control.  So this is a genuine [ElementaryTopos] at which one of
 Structure/Topos.v's own two derived constants is not statable, and
 docs/INHABITATION.md's row for those two constants keeps its
 FinSet-only witness column for exactly that reason.

 WHAT EACH CONSTANT CONSUMES.  Most of the file is assembly or
 conversion; only section (B) proves anything.

 Sets_Topos, _dec, _IEM   the five donors above; no tactic.
 app1_terminal_singleton  one [destruct] on [poly_unit].
 pbone_sq                 the terminal object's uniqueness, spent
 NOT through [one_unique] but by a double
 [destruct] -- see the gotcha below.
 pbone_from_prod          [ump_pullbacks] of [Sets_HasPullbacks],
 nothing else.
 pullback_over_one_is_product
 its FROM-TO law is the [unique_property]
 of that same mediator, read at a point;
 its TO-FROM law is [reflexivity] at a
 point.  Neither inverse law is left to the
 obligation tactic; both are written out.
 pbone_to_exl/_to_exr     [reflexivity] at a point -- the fork's two
 projections reduce.
 pbone_from_fst/_from_snd the two halves of [unique_property].
 app1_truth_monic         [truth_monic] (Structure/SubobjectClassifier.v),
 which is derived there, applied.
 app1_char_rule_U/_dec    [sets_classifier_char_iff] and
 [sets_classifier_dec_char_iff]
 (OneLevel.v), applied verbatim at
 the topos-level classifier; [:=] with no
 tactic.
 app1_classifying_square  [char_pullback], re-exposed at the bundle.
 app1_classifying_unique  [char_unique], re-exposed at the bundle.
 every Example            conversion alone.

 ONE BUILDER GOTCHA, RECORDED BECAUSE IT COSTS TIME.  The square
 [pbone_sq : one ∘ exl ≈ one ∘ exr] cannot be supplied as
 [one_unique _ _]: the elaborator will not unify [@homset Sets]
 against [@SetoidMorphism_Setoid], and [apply one_unique] does not
 match the unfolded pointwise goal either.  What works is to go
 pointwise and [destruct] both composites, whose values inhabit
 [poly_unit].

 STRICT VERSUS [≈], MEASURED STRICT FIRST.

 TWENTY-TWO identifications hold at [eq_refl] and are shipped as
 [Example]s, and that is the whole count of [eq_refl] STATEMENTS
 below this header (the token occurs in this header several times
 more): the
 five field readbacks plus the decidable route's classifier; the
 terminal carrier and the terminal object itself; the chosen pullback
 of [a → 1 ← b] IS the section-(B) one; the mediator out of the
 product REDUCES to [sets_pb_med] (which is why
 Instance/Sets/Pullback.v's [Sets_IsPullback] being [Defined] matters
 here); Ω and [truth] on BOTH routes, with the decidable Ω's carrier
 [poly_bool]; the two [char] readbacks; the power object and its
 carrier on both routes; and membership as application on both routes.

 THE STRONGEST OF THOSE, and it is stronger than the brief expected:

 @Pow Sets (Sets_Topos U) b = Powerset_Prop_obj b   by [eq_refl]

 Mac Lane's “P b, the set of all subsets s of b” is DEFINITIONAL here,
 not an isomorphism.  The reason is that two files build the same
 record: Instance/Sets/Powerset.v's [Powerset_Prop_obj X] packages
 [SetoidMorphism X Powerset_Prop_truth] with [SetoidMorphism_Setoid],
 Instance/Sets/Cartesian/Closed.v's [exponent_obj x y] packages
 [SetoidMorphism x y] with the same, and
 Instance/Sets/Powerset/Universal.v defines [Powerset_Omega] to BE
 [Powerset_Prop_truth].  So Ω^b and the power set are one term.

 ON THE DECIDABLE ROUTE THE POWER OBJECT IS THE **DECIDABLE** POWER
 SET, and that is measured both ways: its carrier IS
 [SetoidMorphism b BoolSetoid] at [eq_refl], and
 [@Pow Sets (Sets_Topos_dec D) b = Powerset_Prop_obj b] is REFUSED at
 [eq_refl] (a CONVERSION refusal, pinned in the probe).  NOT BUILT: no
 isomorphism between the two power objects, under [IEM] or otherwise,
 and no isomorphism between [BoolSetoid] and [Powerset_Omega].

 EVALUATION IS APPLICATION on both routes, at [eq_refl] -- with an
 ARGUMENT-ORDER DISCLOSURE, and with the reach of the two Examples
 stated exactly.  Mac Lane's ε_b : b × P b → Ω takes the ELEMENT
 first, ε_b(x, s); this tree's [eval : y^x × x ~> y] takes the SUBSET
 first, so the Examples read [eval (s, x) = s x].  That is a
 difference of convention, not of mathematics, and it is stated
 rather than silently normalised.  READ THEIR STRENGTH NARROWLY: the
 equation holds at an ARBITRARY second object of [Sets] -- it is a
 [Sets_Closed] fact, not a topos fact -- so the two Examples are one
 and the same fact at the two routes' Ω, and what their TYPES pin
 (that [carrier (Pow b)] reduces to the exponential's) is already
 pinned by [app1_pow_carrier] and [app1_pow_dec_carrier].  In
 particular the word MEMBERSHIP would be an over-read: nothing here
 relates [s x] to [sets_in_image], to [char] or to the classifying
 rule, and no such statement is made.

 FOUR IDENTIFICATIONS COME OUT AT [≈] AND NOT AT [eq_refl], all in
 section (B), and their cause is structural rather than incidental:
 Instance/Sets/Pullback.v makes the apex a SIGMA carrying the
 agreement witness,

 sets_pb_carrier := { p : carrier x * carrier y
 & equiv (f (fst p)) (g (snd p)) },

 so it is not the product carrier and its first projection is not
 [exl].  Hence Mac Lane's “the pullback of two arrows a → 1 ← b is
 then the usual set-theoretic product, with its projections to the
 given factors” is delivered as an ISOMORPHISM CARRYING ITS FOUR LEG
 EQUATIONS -- [pbone_to_exl], [pbone_to_exr], [pbone_from_fst],
 [pbone_from_snd] -- and not as a bare [≅].  FOUR strict forms are
 REFUSED and pinned in the probe: [pbone = a × b] and
 [carrier pbone = carrier (a × b)] and
 [exl ∘ pbone_to_prod = pbone_fst] are CONVERSION refusals, and
 [pbone_fst = exl] is a TYPING one -- a plain has-type mismatch with
 no “cannot unify” and no universe clause, because the two morphisms
 do not even share a source.

 THE OBSTRUCTION, ARGUED FOR THE RECORD, since the issue's Definition
 of Done asks for an instance OR an argued obstruction, its work item
 1 anticipates a verdict that no one-level instance exists, and the
 honest verdict is NEITHER of those two branches: a one-level instance
 DOES exist, conditionally.

 WHICH OF MAC LANE'S CLAUSES IS CONDITIONAL: exactly one, his Axiom
 8 “Truth” -- the subobject classifier -- and hence the §IV.9
 construction-1 clause.  Measured three ways: [Sets_Terminal],
 [Sets_Cartesian], [Sets_HasPullbacks] and [Sets_Closed] are
 argument-free [#[export]] instances, all four resolve by typeclass
 search, and all four are Closed; each of [Sets_Classifier],
 [Sets_Classifier_dec] and [Sets_Classifier_IEM] takes exactly one
 hypothesis.  So his Axioms 6 (terminal object), 7 (pullbacks, hence
 products) and 9 (power objects, here the exponential by Ω) are
 UNCONDITIONAL at [Sets]; only Axiom 8 is not.

 WHAT THE HYPOTHESES ARE, verbatim from
 Instance/Sets/Classifier/OneLevel.v and
 Instance/Sets/Powerset.v:

 Definition Untruncate@{o} :=
 ∀ P : Type@{o}, Powerset_squash@{o} P -> P.
 Definition DecImage@{o so} :=
 ∀ (u x : SetoidObject@{o o}) (m : u ~{Sets@{o so}}~> x),
 @Monic Sets@{o so} u x m →
 ∀ b : carrier x,
 sets_in_image@{o} m b + (sets_in_image@{o} m b -> False).
 Definition IEM@{o} := ∀ P : Type@{o}, P + (P -> False).
 Definition Powerset_squash@{o} (A : Type@{o}) : Prop :=
 ∀ Q : Prop, (A → Q) → Q.

 WHERE THE HYPOTHESIS IS SPENT: exactly once.  In
 OneLevel.v's [small_of_untruncate] the argument [U] occurs
 on two lines, the binder and one use
 ([exact (U P (proj2 Hp I))]), inside the obligation which by the
 field order of [Record SmallClassifierExt] is [sce_elim].

 WHY IT IS NEEDED AT ALL: [≈] in this library is [Type@{o}]-valued,
 so the characteristic predicate [λ b, ∃ a, m a ≈ b] is
 [Type@{o}]-valued, and truncating it with the impredicative
 [Powerset_squash] is what puts it at the carrier's own level.
 Inverting that truncation is exactly [Untruncate].  The naive
 elimination [fun P h => h P (fun p => p)] is refused with “Cannot
 enforce o <= Prop”, against the [Prop]-valued instantiation
 [powerset_squash_prop_inert] as the accepted control; that pair is
 already Test/ProbeClassifier402.v and its control, and is CITED
 here rather than duplicated.

 NO IMPOSSIBILITY IS PROVED, AND THE PREMISE HAS NO IN-TREE
 INHABITANT, measured with TWO sweeps whose criteria are stated
 because the counts move with them.  (i) Declaration heads that
 MENTION one of the three at the first colon -- overwhelmingly
 binders -- number 36 outside this change's three files.  (ii)
 Declarations whose CONCLUSION is one of the three (the type
 preceded by an arrow, or followed by [:=] or a period) number FIVE:
 [untruncate_of_IEM], [DecImage_of_IEM], [IEM_of_DecImage] and
 [DecImage_iff_IEM]'s packaged pair, every one a PASSAGE between the
 hypotheses and not an inhabitant, and one refutation command,
 Test/ProbeFunClassifier403.v, which never enters the
 environment.
 Instance/Sets/Classifier/OneLevel.v's three-part disclosure applies
 verbatim here: (i) no unconditional axiom-free instance is built,
 (ii) no impossibility theorem is proved, (iii) an out-of-tree
 scratch development builds the classifier on exactly [classic] and
 [constructive_indefinite_description], so an in-tree impossibility
 theorem would refute a classically valid statement.  PART (iii) IS
 A HEADER CLAIM OF THAT FILE, quoted here and NOT re-run.
 Instance/Sets/Classifier.v additionally records, as folklore
 and explicitly not as an in-tree theorem, that no small classifier
 can exist over predicative [Type].

 PRIOR ART, AND THE ISSUE'S “CURRENT STATE”, EACH RE-MEASURED WITH ITS
 CRITERION AT THE BASE COMMIT.

 TRUE AT THE BASE COMMIT: “no [ElementaryTopos Sets]”, and “the
 only [ElementaryTopos] inhabitant anywhere is
 Instance/FinSet/Topos.v”.  CRITERION, stated so that it produces
 the numbers below: declaration heads whose type MENTIONS
 [ElementaryTopos] after a colon -- which therefore also catches the
 two that take one as a HYPOTHESIS -- swept comment-stripped ACROSS
 LINE BREAKS.  A line-anchored pattern such as
 [rg -n ':\s*ElementaryTopos' -g '*.v'] is NOT sound for this claim:
 it misses every head whose type wraps, which is all three bundles
 of THIS file.  Under the sound criterion the base commit returns
 three heads, two of them Structure/Topos.v's [Pow] and its
 [relations_iso] taking one as a hypothesis, so [FinSet_Topos] is
 the sole INHABITANT; the shipped tree returns ten.

 FALSE: “There is no [HasPullbacks Sets]” --
 Instance/Sets/Pullback.v's [#[export] Instance
 Sets_HasPullbacks], landed by #333, which the issue itself lists as
 a dependency.  FALSE: “no [SubobjectClassifier Sets]” -- three
 conditional ones in OneLevel.v, plus its engine.  FALSE FOR TWO
 OF THREE: “a tree-wide search finds exactly
 one instance of each of those three classes, all for FinSet” --
 true of [ElementaryTopos]; false of [SubobjectClassifier]
 (FinSet's, OneLevel.v's three, and four for functor categories at
 Instance/Fun/Classifier.v) and false of
 [HasPullbacks] (FinSet's, [Sets_HasPullbacks],
 Instance/Cat/Pullback.v's [StrictCat_HasPullbacks],
 Instance/Fun/Pullback.v's [Fun_HasPullbacks], plus generic
 conditionals).

 STALE AS A CITATION: “The setoid half is blocked by a documented
 and deliberate universe obstruction (Instance/Sets/Classifier.v)”.
 That file's header now records the OPPOSITE -- that the
 conditional one-level instance exists -- and the obstruction
 paragraph proper is now the section headed “WHY ONE LEVEL DOES NOT
 SUFFICE UNCONDITIONALLY”.

 LOCATION DRIFT in four of the issue's citations: the places it
 gives for [Sets_Terminal] in Instance/Sets.v and for
 [sets_char_pullback], [sets_char_unique] and
 [sets_char_subobject] in Instance/Sets/Classifier.v are all
 stale, the last three by the same amount and in the same
 direction.  CORRECT as cited: Instance/Sets/Cartesian.v,
 Instance/Sets/Cartesian/Closed.v and Instance/FinSet/Topos.v.

 A SECOND-INHABITANT NOTE, because it makes another file's header
 stale.  Through Structure/Topos/Colimits.v this bundle yields an
 initial object, a binary coproduct, coequalizers, pushouts and
 equalizers for [Sets]; unlike the presheaf side, where all five
 would be firsts, at [Sets] all five are SECOND inhabitants --
 Instance/Sets.v, Instance/Sets/Cocartesian.v,
 Instance/Sets/Coequalizer.v, Instance/Sets/Pushout.v and
 Adjunction/GAFT/Sets.v already have them.  That last file's
 header CALLED itself “the tree's only inhabitant of that class” and
 is corrected in this same change to “the only such LIBRARY-file
 inhabitant” -- which the derived one does NOT falsify, since it
 lives in Test/ProbeToposInstances404.v and is therefore not a
 library-file inhabitant, as that file's own appended note says.  The
 four colimit legs and the equalizer leg are ASCRIBED at the
 existing instances' own types in Test/ProbeToposInstances404.v, so
 the types are checked to line up;
 NO AGREEMENT PROOF IS BUILT, deliberately, and none is claimed.
 They live in the probe because requiring
 Structure/Topos/{Monadic,Colimits}.v takes this file's closure from
 74 to 101.

 WHAT IS NOT DELIVERED -- read this as the scope of the file.

 * No unconditional topos and no impossibility theorem (see the
 obstruction above).

 * No [classifier_classifies] and no [relations_iso] at any bundle
 here: both are refused, both refusals are pinned, and neither is
 repaired.  So this file adds NO witness to
 docs/INHABITATION.md's row for those two constants.

 * No comparison between the three bundles: no isomorphism of their
 truth objects, no isomorphism of their power objects, and no
 statement that they agree under [IEM].

 * No agreement proof between the derived colimits and the existing
 [Sets] instances (types only), and no [Complete]/[Cocomplete]
 statement derived from the topos structure.

 * No naturality anywhere, and no functoriality of any of the App.1
 witnesses in [a] or [b].

 * Nothing about slices, Lawvere-Tierney topologies, the internal
 logic or Giraud's theorem.

 * No relation to Instance/Fun/Topos.v's [Presheaf_Topos]: no
 functor between the two categories is built.

 * Nothing is registered as an [Instance]; all three bundles are
 plain [Definition]s, deliberately.

 * This file contributes NO lines to [make todo].  Its probe does,
 as every probe in this tree does, and that is disclosed rather
 than hidden. 

 --------
 书籍：      Mac Lane，《为工作的数学家准备的范畴论》，第2版，§IV.10，印刷页 107（PDF 页 116）（[maclane:IV.10:remark1]）。逐字摘录自呈现的页面：

 “所有（小）集合的范畴 Sets 是一个拓扑斯，同样所有集合值的函子范畴 Sets^{C^op} 对于一个小范畴 C 的逆变函子也是一个拓扑斯。”

 书籍：      Mac Lane，同上，引申附录“基础”，§App.1，印刷页 289-290（PDF 页 295-296）（[maclane:App.1:remark1]）。逐字摘录自呈现的页面。他的公理 8 和 9，印刷页 289：一个初等拓扑是一个具有某种额外结构的范畴：终对象、拉回、真值、子对象分类器，以及幂对象（子集的集合）。

 8. 真值。存在一个对象 Ω（真值对象）和一个单射 t : 1 → Ω，称为真值；对于任何单射 m : a → b，存在唯一的箭头 ψ : b → Ω，使得下列方格是一个拉回：“9. 动力对象。对于每个对象b，都有一个
 关联对象 P b 和一个箭头 ε_b ： b × P b → Ω
 使得对于每个箭头 f ： b ×一个→ Ω 都存在
 唯一箭头 G ： a → P b 满足以下条件
 图交换：“（3）

 以及四位证人，第290页印刷：为了理解这些公理，我们观察它们如何应用于通常的所有集合的范畴。在那里，任何只有一个元素的集合都可以作为终对象 1，因为每个集合 a 都有一个唯一的函数 a → 1 指向 1。对于两个集合 a 和 b，两个箭头 a → 1 ← b 的拉回（pullback）就是通常的集合论意义上的笛卡尔积，并带有指向给定因子 a 和 b 的投影。对于真值，取对象 Ω 为任意包含两个对象 1 和 0 的集合 2，而单态射 t : 1 → 2 只是 1 在 2 中的通常包含。然后如公理 8 所示的单态射 m : a → b，就是 b 的一个子集 a。这个子集有一个众所周知的特征函数 ψ : b → 2，使得 ψ(y) = 1 或 0，取决于 b 中的元素 y 是否在子集 a 中。这产生了上述的拉回（2）。“公理9描述了P b，即b的所有子集s的集合，通常称为‘幂集’P b。事实上，可以定义ε_b(x, s) = 0，如果b的元素x在子集s中，否则等于1。这样确实给出了一个如上(3)中的拉回。

 这些对顶点范畴的公理随后在集合范畴中成立。

 印刷页上的两个注释，均保持原样。

 首先，“根据b的元素y是否在子集a中”是书中自己用的措辞，逐字转录；其含义显然是“b的元素y”。其次，这一点对于理解条款(d)很重要：这一页在成员资格对应的真值方面内部不一致。相隔两句话，它说“ψ(y) = 1 或 0，取决于 y 的元素 b 是否属于子集 a”和“ε_b(x, s) = 0，如果 b 的元素 x 属于子集 s，否则等于 1”——在同一页上，ψ 下的成员资格为 1，ε_b 下的成员资格为 0。问题的意译悄悄地将第二句话改为“ε_b(x, s) = 1 当且仅当 x ∈ s”。上面引用了两句话，这里没有解决。下面内容不依赖于选择：真值的命名是惯例，这棵树的惯例及其测量记录在 Instance/Sets/Classifier/OneLevel.v 和 Instance/Fun/Classifier.v 中。所交付的是分类规则，这两个文件以其形式证明了这一点——第(C)节的 [app1_char_rule_U] 和 [app1_char_rule_dec]，它们表明特征映射在像上正好取值 [truth]。

 所交付的内容：[ElementaryTopos Sets@{o so}] 的三位成员，每位都依赖于一个假设。仔细区分这三位：[Sets_Topos_IEM] 在 [eq_refl] 处是 [Sets_Topos]（下表将其写为它的 [:=]），因此它共享它的真实对象和幂对象，仅在其采用的假设上有所不同；[Sets_Topos_dec] 则在两者及其作用范围上都有不同：

 Sets_Topos     (U : Untruncate@{o})   Ω = Powerset_Omega
 Sets_Topos_dec (D : DecImage@{o so})  Ω = BoolSetoid   -- Mac Lane 的 2
 Sets_Topos_IEM (E : IEM@{o})          := Sets_Topos (untruncate_of_IEM E)连同 Mac Lane 在每个测量强度下的四个 App.1 证人，在（B）到（E）部分。三个捆绑包都是普通的 [Definition]，三个都是在全局上下文下封闭的，而且其中没有任何义务或策略。

 路径是纯装配：五个字段，五个预先存在的捐赠者，没有重新证明的内容。

 topos_terminal    Instance/Sets.v 的 [Sets_Terminal]
 topos_cartesian   Instance/Sets/Cartesian.v 的 [Sets_Cartesian]
 topos_pullbacks   Instance/Sets/Pullback.v 的 [Sets_HasPullbacks]
 topos_closed      Instance/Sets/Cartesian/Closed.v 的 [Sets_Closed]
 topos_classifier  Instance/Sets/Classifier/OneLevel.v 的 [Sets_Classifier]（与 [Sets_Classifier_dec] 在可判定路径上）Instance/FinSet/Topos.v 在这里并未作为任何事物的证明提供，也不是此文件所要求的：问题的审查者检查正是要求这一点，而其兄弟文件 Instance/Fun/Topos.v 在预层面上也有同样的说明。为什么是普通的 [Definition] 而不是 [Instance]。在 Instance/FinSet/Topos.v 中给出了原因，并且紧随其后：五个 [topos_*] 投影是 [#[export] 已存在的实例，因此注册一个 bundle 会给类型类搜索提供另一条收敛到每个组件的路径。在 [Sets] 处测量的，双向：(i) 五个投影存在于实例数据库中，因此 FinSet 的理由在这里确实适用 -- [Print HintDb typeclass_instances] 列出了 [simple apply @topos_terminal]，[@topos_cartesian]，[@topos_pullbacks]，[@topos_closed] 和 [@topos_classifier]；(ii) 目前无法观察到损害，因为在全局注册该 bundle 后，所有四个无条件组件仍解析为 DIRECT 实例，并且 [@SubobjectClassifier Sets Sets_Terminal] 仍未解析，[Untruncate] 是 [Definition] 而不是 [Class]，因此 [topos_classifier] 路径以无法解析的元变量结束。两种读法都已说明，因为单独说明任何一种都会产生误导。未测量：额外路径是否增加搜索时间。 

 宇宙，测量于绑定器和约束块两端。Sets_Topos@{o so} ：
 Untruncate@{o} → ElementaryTopos@{so so o} Sets@{o so}
 块：Set < o, o < so，加上标准库界限。

 Sets_Topos_IEM@{o so} ： IEM@{o} → ElementaryTopos@{so so o} Sets@{o so}
 块：相同。

 Sets_Topos_dec@{o so} ：
 DecImage@{o so} → ElementaryTopos@{so so o} Sets@{o so}
 块：o < so，加上标准库界限 —— 并且完全没有 [Set]。

 pullback_over_one_is_product@{o so} ：
 ∀ a b : obj [Sets@{o so}] , pbone@{o so} a b ≅ a × b
 块：o < so，加上标准库界限。

 读出这四个东西。(1) 在此文件的任何块中没有一个约束是方程。每个条目都是 [<] 或 [<=]。这值得说明，因为在部分 (B) 中它不是自由的：写在 [Section] 内，并且 [Context (a b : Sets)]，同样的拉回展开在 [pullback_over_one_is_product@{u u0 u1 u2}] 中用两个块方程（[u = u1] 和 [u0 = u2]）将两个对象的 [Sets] 相互识别。下面提供的带注释的顶层形式没有任何方程。因此，这里的注释带来的不仅是展示效果——它是保持文件无方程的原因——与捆绑不同，未经注释的主体经过重命名仍可获得相同的解读。

 (2) 没有任何内容固定在 [Set] 上。[Set < o] 是一个严格的下界，并且它只在 [Untruncate] / [IEM] 路径上，从 [Prop : Type@{Set+1}] 通过 [Powerset_Omega] 到达。(3) 这两条路径在到达范围上不同，这也是运送两者的意义所在。在一节中声明 [Set < su]，[Sets@{Set su}] 是一个类别，它的四个无条件给予者都在 [@{su Set}] 被接受，而 [Sets_Topos_dec@{Set su}] 被接受——而 [Sets_Classifier@{Set su}] 和 [Sets_Topos@{Set su}] 各自被拒绝，提示“无法执行 Set < Set，因为 Set = Set”。因此，可判定路径到达 [Sets]，其载体宇宙是字面 [Set]，而截断路径则不到达。拒绝情况和七个控制都固定在 Test/ProbeToposInstances404.v 中。这在 TOPOS 层面上证实了 Instance/Sets/Classifier/OneLevel.v 在分类器层面的说明。(4) 这个类自身的两个推论都未必适用于这个拓扑。
 [Pow] 可以； [relations_iso] 不行，[classifier_classifies] 也不行。两者都将界定的 [u <= u0] 作用于 [C : Category@{u u0 u0}] —— 对象处于或低于 homs —— 而 [Sets@{o so} : Category@{so o o}] 有 o < so，[relations_iso] 构建为 [iso_compose exp_iso (classifier_classifies (a × b))]，因此它继承了这种拒绝。两者都在探针中固定，[Pow] 在这个拓扑中作为被接受的控制。因此，这确实是一个 [ElementaryTopos]，其上 Structure/Topos.v 自身的两个派生常量之一无法被声明，而 docs/INHABITATION.md 对那两个常量的行正因为这个原因保持了仅限 FinSet 的见证列。

 每个常量消耗的内容。文件的大部分是汇编或转换；只有（B）节证明了任何东西。Sets_Topos, _dec, _IEM   上述五个捐赠者；没有策略。app1_terminal_singleton  一个  [destruct]  在  [poly_unit] 上。pbone_sq                 终端对象的唯一性，已经使用
 不是通过  [one_unique]  而是通过双重
 [destruct]  -- 见下面的陷阱。pbone_from_prod           [ump_pullbacks]  来自  [Sets_HasPullbacks] ,
 没有其他。pullback_over_one_is_product
 它的 FROM-TO 法则是 该同一中介的  [unique_property] ，在某一点读取；
 它的 TO-FROM 法则是 [reflexivity] ，在某一点。没有一个逆法则留给
 义务策略；两者都已写出。pbone_to_exl/_to_exr      [reflexivity]  在一个点 -- 叉的两个投影减少。 pbone_from_fst/_from_snd [unique_property] 的两半部分。 app1_truth_monic          [truth_monic]  (Structure/SubobjectClassifier.v)，在那儿导出的，已应用。 app1_char_rule_U/_dec     [sets_classifier_char_iff] 和 [sets_classifier_dec_char_iff] (OneLevel.v)，在拓扑层级分类器上逐字应用； [:=] 没有策略。 app1_classifying_square   [char_pullback] ，在捆绑处重新暴露。 app1_classifying_unique   [char_unique] ，在捆绑处重新暴露。 每个示例            仅转换。一个构建器问题，被记录下来因为它很耗时间。方块 [pbone_sq : one ∘ exl ≈ one ∘ exr] 不能作为 [one_unique _ _] 提供：展开器不会统一 [@homset Sets] 与 [@SetoidMorphism_Setoid]，而 [apply one_unique] 也不匹配展开后的逐点目标。可行的方法是逐点进行，并将 [destruct] 应用于两个组合，其值属于 [poly_unit]。

 严格与 [≈]，先测量严格。在 [eq_refl] 上共有二十二个标识，并作为 [Example] 发送，这就是本标题下 [eq_refl] 声明的全部数量（该标记在本标题中出现多次）：
 五个字段回读加上可判定路线的分类器；终端承载器和终端对象本身；所选择的 [a → 1 ← b] 拉回是 (B) 部分的；来自乘积的中介归约到 [sets_pb_med]（这就是为什么 Instance/Sets/Pullback.v 中 [Sets_IsPullback] 是 [Defined] 在这里很重要）；Ω 和 [truth] 出现在两条路线中，并且可判定 Ω 的承载器为 [poly_bool]；两个 [char] 回读；在两条路线上的幂对象及其承载器；以及两条路线上的作为应用的成员关系。

 其中最强的，而且它比预期的简略形式更强：@Pow 集合 (Sets_Topos U) b = Powerset_Prop_obj b   由 [eq_refl] 

 Mac Lane 的“P b，b 的所有子集 s 的集合”在这里是定义性的，
 而不是同构。原因是两个文件构建了相同的记录：
 Instance/Sets/Powerset.v 的 [Powerset_Prop_obj X] 打包了
 [SetoidMorphism X Powerset_Prop_truth] 与 [SetoidMorphism_Setoid]，
 Instance/Sets/Cartesian/Closed.v 的 [exponent_obj x y] 打包了
 [SetoidMorphism x y] 与相同的，
 并且 Instance/Sets/Powerset/Universal.v 定义了 [Powerset_Omega] 为
 [Powerset_Prop_truth]。 所以 Ω^b 和幂集是同一项。在可判定路径上，幂对象是**可判定**幂集，并且它的测量是双向的：它的载体在 [eq_refl] 是 [SetoidMorphism b BoolSetoid]，并且 [@Pow Sets (Sets_Topos_dec D) b = Powerset_Prop_obj b] 在 [eq_refl] 被拒绝（转换拒绝，被固定在探测中）。未构建：在 [IEM] 或其他情况下，两个幂对象之间没有同构，并且 [BoolSetoid] 和 [Powerset_Omega] 之间也没有同构。评估在两条路径上都是应用，在 [eq_refl] —— 带有参数顺序公开，并且精确说明了两个示例的适用范围。Mac Lane 的 ε_b : b × P b → Ω 先取元素，ε_b(x, s)；而这个树的 [eval : y^x × x ~> y] 先取子集，所以示例读作 [eval (s, x) = s x]。这是约定上的差异，而非数学上的差异，并且已明确表述，而不是默默归一化。狭义地理解它们的强度：该方程在 [Sets] 的任意第二个对象上成立 —— 这是 [Sets_Closed] 事实，而非拓扑事实 —— 因此两个示例在两条路径的 Ω 上是同一事实，而它们的类型所限定的（即 [carrier (Pow b)] 归约为指数的）已经被 [app1_pow_carrier] 和 [app1_pow_dec_carrier] 所限定。特别是“MEMBERSHIP”这个词会被理解过度：这里没有任何内容将 [s x] 与 [sets_in_image]、[char] 或分类规则联系起来，也没有做出这样的说明。

 四个标识出现在 [≈]，而不是 [eq_refl]，全都在（B）部分，它们的原因是结构性的而非偶然的：
 Instance/Sets/Pullback.v 使顶点成为携带协议证据的 SIGMA，

 sets_pb_carrier := { p : carrier x * carrier y
 & equiv (f (fst p)) (g (snd p)) },所以它不是积对象，并且它的第一个投影不是 [exl]。因此，Mac Lane 的“两个箭头 a → 1 ← b 的拉回就是通常的集合论积，其投影到给定因子的映射”被实现为携带其四条腿等式的同构——[pbone_to_exl]、[pbone_to_exr]、[pbone_from_fst]、[pbone_from_snd]——而不是作为一个单独的 [≅]。四种严格形式被拒绝并固定在探针中：[pbone = a × b]、[carrier pbone = carrier (a × b)] 和 [exl ∘ pbone_to_prod = pbone_fst] 是转换拒绝，而 [pbone_fst = exl] 是类型拒绝——一个普通的类型不匹配，没有“无法统一”提示，也没有宇宙子句，因为这两个态射甚至没有共同的源。阻碍，在记录中提出争论，由于问题的完成定义要求一个实例或一个有争论的阻碍，它的工作项1预期的判决是不存在单级实例，而诚实的判决既不属于这两个分支：单级实例在特定条件下确实存在。麦克莱恩的哪一个条款是有条件的：恰好一个，他的公理 8 “真理”——子对象分类器——因此还有 §IV.9 构造-1 条款。通过三种方式测量：[Sets_Terminal]、[Sets_Cartesian]、[Sets_HasPullbacks] 和 [Sets_Closed] 是无参数的 [#[export] 实例，四者都通过类型类搜索解决，并且四者都是封闭的；[Sets_Classifier]、[Sets_Classifier_dec] 和 [Sets_Classifier_IEM] 每个都恰好接受一个假设。所以他的公理 6（终对象）、7（拉回，因此是积）和 9（幂对象，这里是 Ω 指数）在 [Sets] 上是无条件的；只有公理 8 不是。

 假设内容是什么，逐字摘自 Instance/Sets/Classifier/OneLevel.v 和 Instance/Sets/Powerset.v：Definition Untruncate@{o} :=
 ∀ P : Type@{o}, Powerset_squash@{o} P -> P.
 Definition DecImage@{o so} :=
 ∀ (u x : SetoidObject@{o o}) (m : u ~{Sets@{o so}}~> x),
 @Monic Sets@{o so} u x m →
 ∀ b : carrier x,
 sets_in_image@{o} m b + (sets_in_image@{o} m b -> False).
 Definition IEM@{o} := ∀ P : Type@{o}, P + (P -> False).
 Definition Powerset_squash@{o} (A : Type@{o}) : Prop :=
 ∀ Q : Prop, (A → Q) → Q.

 假设已用完的位置：恰好使用一次。在
 OneLevel.v 的 [small_of_untruncate] 文件中，参数 [U] 在两行中出现，
 分别是在绑定器和一个使用位置 ([exact (U P (proj2 Hp I))])，在义务中，
 按照 [Record SmallClassifierExt] 的字段顺序，位置是 [sce_elim]。为什么它根本需要：在此库中，[≈] 是 [Type@{o}] 值，因此特征谓词 [λ b, ∃ a, m a ≈ b] 是 [Type@{o}] 值，并且用反演 [Powerset_squash] 截断它会将其放在承载者自身的级别上。反转该截断正是 [Untruncate]。天真的消去 [fun P h => h P (fun p => p)] 被拒绝，提示“无法强制 o <= Prop”，针对作为接受控制的 [Prop] 值实例 [powerset_squash_prop_inert]；该对已经是 Test/ProbeClassifier402.v 及其控制，并且在此引用，而不是重复。没有任何不可能性被证明，并且前提没有树内居民，使用两个扫描进行测量，其标准已说明，因为计数会随它们变化。(i) 声明头在第一个冒号处提到三个之一——绝大多数是绑定器——在此次更改的三个文件之外的数量为36。(ii) 其结论为三者之一的声明（类型前有箭头，或后跟 [:=] 或句号）数量为五个：[untruncate_of_IEM]、[DecImage_of_IEM]、[IEM_of_DecImage] 和 [DecImage_iff_IEM] 的成对封装，每一个都是假设之间的通道而不是居民，还有一个反驳命令 Test/ProbeFunClassifier403.v，它从未进入环境。Instance/Sets/Classifier/OneLevel.v 的三部分披露在此逐字适用：(i) 未构建任何无条件无公理的实例，(ii) 未证明任何不可能性定理，(iii) 一个树外的临时开发在 [classic] 和 [constructive_indefinite_description] 上构建了分类器，因此树内的不可能性定理会否定一个经典有效的陈述。（iii 部分是该文件的标题声明，此处引用但未重新运行。）Instance/Sets/Classifier.v 另外记录了作为民间传说，明确不是树内定理，即在层次 [Type] 上不存在小型分类器。

 先前工作，以及该问题的“当前状态”，均以其标准在基本提交中重新衡量。在基础提交中为真：“no [ElementaryTopos Sets]”，并且“唯一的 [ElementaryTopos] 居民存在于 Instance/FinSet/Topos.v 中”。标准（CRITERION）表述如下，以便生成以下数字：类型在冒号后提及 [ElementaryTopos] 的声明头——因此也会捕获两个将其作为假设的——在跨行的注释去除后扫描。像 [rg -n ':\s*ElementaryTopos' -g '*.v'] 这样的行锚定模式对于此声明并不可靠：它会遗漏类型换行的所有头部，这正好是此文件的三个包。在可靠标准下，基础提交返回三个头部，其中两个是 Structure/Topos.v 的 [Pow] 及其将其作为假设的 [relations_iso]，所以 [FinSet_Topos] 是唯一的居民；而发布的树返回十个。错误：“没有 [HasPullbacks Sets]” -- Instance/Sets/Pullback.v 的 [#[export] 实例 Sets_HasPullbacks，由 #333 引入，而问题本身将其列为依赖项。错误：“没有 [SubobjectClassifier Sets]” -- OneLevel.v 中有三个条件实例，加上它的引擎。三者中两者为假：“一次树状搜索恰好找到每个这三类中的一个实例，全部属于 FinSet” -- 对 [ElementaryTopos] 为真；对 [SubobjectClassifier] 为假（FinSet 的、OneLevel.v 的三个，以及 Instance/Fun/Classifier.v 中函子类别的四个）且对 [HasPullbacks] 为假（FinSet 的，[Sets_HasPullbacks]，Instance/Cat/Pullback.v 的 [StrictCat_HasPullbacks]，Instance/Fun/Pullback.v 的 [Fun_HasPullbacks]，外加通用条件）。像引用一样陈旧：“集合论一半被记录在案并故意的宇宙障碍阻挡（Instance/Sets/Classifier.v）”。该文件的头部现在记录了相反的情况——条件的一层实例存在——而障碍段落本身现在在标题为“为什么一层不足以无条件适用”的章节中。

 四个问题引用中的位置漂移：它在 Instance/Sets.v 中给出的 [Sets_Terminal] 的位置，以及在 Instance/Sets/Classifier.v 中的 [sets_char_pullback]、[sets_char_unique] 和 [sets_char_subobject] 的位置都已陈旧，后三个的位置改变幅度相同且方向一致。引用正确的文件：Instance/Sets/Cartesian.v、Instance/Sets/Cartesian/Closed.v 和 Instance/FinSet/Topos.v。一个 SECOND-INHABITANT 注释，因为它会使另一个文件的头部过时。通过 Structure/Topos/Colimits.v 这个模块产生一个初始对象、二元余积、余等化器、推挤和等化器用于 [Sets]；与预层面不同，在预层面中这五个都是首次，在 [Sets] 中这五个都是 SECOND inhabitants —— Instance/Sets.v、Instance/Sets/Cocartesian.v、Instance/Sets/Coequalizer.v、Instance/Sets/Pushout.v 和 Adjunction/GAFT/Sets.v 已经拥有它们。最后一个文件的头部称自己为“该类中树的唯一居住者”，并在同一次更改中被修改为“唯一的此类库文件居住者”——派生文件并未否定这一点，因为它存在于 Test/ProbeToposInstances404.v 中，因此不是库文件居住者，正如该文件附加的说明所述。四个余积腿和等化子腿被归属到 Test/ProbeToposInstances404.v 中现有实例的自身类型，因此类型检查是一致的；刻意没有构建任何一致性证明，也没有声称有。这些文件存在于探针中，因为引用 Structure/Topos/{Monadic,Colimits}.v 会使该文件的闭包从 74 增至 101。

 未交付的内容——将其理解为文件的范围。* 没有无条件的拓扑，也没有不可能性定理（参见上述障碍）。

 * 在任何束上都没有 [classifier_classifies] 和 [relations_iso]：两者都被拒绝，两者的拒绝都有记录，而且没有修复。因此，此文件没有为 docs/INHABITATION.md 中这两个常量的行添加任何证据。

 * 三个束之间没有比较：没有它们的真对象同构，没有它们的幂对象同构，也没有声明它们在 [IEM] 下是一致的。

 * 派生余极限与现有 [Sets] 实例（仅类型）之间没有一致性证明，也没有基于拓扑结构派生的 [Complete] / [Cocomplete] 声明。

 * 任何地方都没有自然性，也没有任何 App.1 证据在 [a] 或 [b] 中的函子性。* 关于切片、Lawvere-Tierney拓扑、内部结构，都没有相关内容
 逻辑或吉罗定理。

 * 与 Instance/Fun/Topos.v 的 [Presheaf_Topos] 无关 ：无
 两个范畴之间的函子被构建。

 * 没有任何东西被登记为[Instance];这三个丛都是
 就是故意[Definition] S。

 * 此文件对[make todo]没有任何线条。它的探针会，
 正如本树中的每个探针一样，这一点被揭示为
 而不是隐藏。
*)

(** ** (A) The three bundles / **（A）三捆 *)

Definition Sets_Topos@{o so} (U : Untruncate@{o}) :
  ElementaryTopos@{so so o} Sets@{o so} :=
  {| topos_terminal   := Sets_Terminal@{so o}
   ; topos_cartesian  := Sets_Cartesian@{so o}
   ; topos_pullbacks  := Sets_HasPullbacks@{so o}
   ; topos_closed     := Sets_Closed@{so o}
   ; topos_classifier := Sets_Classifier@{o so} U |}.

Definition Sets_Topos_dec@{o so} (D : DecImage@{o so}) :
  ElementaryTopos@{so so o} Sets@{o so} :=
  {| topos_terminal   := Sets_Terminal@{so o}
   ; topos_cartesian  := Sets_Cartesian@{so o}
   ; topos_pullbacks  := Sets_HasPullbacks@{so o}
   ; topos_closed     := Sets_Closed@{so o}
   ; topos_classifier := Sets_Classifier_dec@{o so} D |}.

Definition Sets_Topos_IEM@{o so} (E : IEM@{o}) :
  ElementaryTopos@{so so o} Sets@{o so} :=
  Sets_Topos@{o so} (untruncate_of_IEM@{o} E).

Example sets_topos_terminal (U : Untruncate) :
  @topos_terminal Sets (Sets_Topos U) = Sets_Terminal := eq_refl.
Example sets_topos_cartesian (U : Untruncate) :
  @topos_cartesian Sets (Sets_Topos U) = Sets_Cartesian := eq_refl.
Example sets_topos_pullbacks (U : Untruncate) :
  @topos_pullbacks Sets (Sets_Topos U) = Sets_HasPullbacks := eq_refl.
Example sets_topos_closed (U : Untruncate) :
  @topos_closed Sets (Sets_Topos U) = Sets_Closed := eq_refl.
Example sets_topos_classifier (U : Untruncate) :
  @topos_classifier Sets (Sets_Topos U) = Sets_Classifier U := eq_refl.
Example sets_topos_dec_classifier (D : DecImage) :
  @topos_classifier Sets (Sets_Topos_dec D) = Sets_Classifier_dec D := eq_refl.

(*
   * ** (B) App.1 clause (a): the terminal object is a one-element set,
   and clause (b): the pullback of [a → 1 ← b] is [a × b] 

   --------
   * **（B）附录1条款(a)：终对象是一个单元素集合，
   条款(b)：[a → 1 ← b]的拉回是[a × b]
*)

Example app1_terminal_carrier (U : Untruncate) :
  carrier (@terminal_obj Sets (@topos_terminal Sets (Sets_Topos U)))
  = poly_unit := eq_refl.

Example app1_terminal_is_donor (U : Untruncate) :
  @terminal_obj Sets (@topos_terminal Sets (Sets_Topos U))
  = @terminal_obj Sets Sets_Terminal := eq_refl.

(* “any set with just one element can serve as a terminal object 1” / 任何只有一个元素的集合都可以作为终端对象1 *)
Lemma app1_terminal_singleton
  (t : carrier (@terminal_obj Sets Sets_Terminal)) : t = ttt.
Proof. destruct t; reflexivity. Qed.

(* The pullback of the unique arrows into 1. Stated at top level with explicit binders rather than inside a Section: see universe reading (1) in the header. / 唯一箭头到 1 的回拉。在顶层使用显式绑定器陈述，而不是在某个 Section 内：参见标题中的宇宙读法 (1)。 *)
Definition PBONE@{o so} (a b : obj[Sets@{o so}]) :=
  @pullback Sets@{o so} Sets_HasPullbacks@{so o} a b
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o}) one one.

Definition pbone@{o so} (a b : obj[Sets@{o so}]) : obj[Sets@{o so}] :=
  Pull _ _ (PBONE@{o so} a b).

Definition pbone_fst@{o so} (a b : obj[Sets@{o so}]) :
  pbone@{o so} a b ~{Sets@{o so}}~> a := pullback_fst _ _ (PBONE@{o so} a b).

Definition pbone_snd@{o so} (a b : obj[Sets@{o so}]) :
  pbone@{o so} a b ~{Sets@{o so}}~> b := pullback_snd _ _ (PBONE@{o so} a b).

Definition pbone_to_prod@{o so} (a b : obj[Sets@{o so}]) :
  pbone@{o so} a b ~{Sets@{o so}}~> a × b :=
  pbone_fst@{o so} a b △ pbone_snd@{o so} a b.

(* [one_unique] does not apply here; see the gotcha in the header. / [one_unique] 在这里不适用；请参阅标题中的陷阱。 *)
Definition pbone_sq@{o so} (a b : obj[Sets@{o so}]) :
  one ∘ exl ≈ one ∘ (exr : a × b ~{Sets@{o so}}~> b).
Proof.
  intro p; destruct ((one[a] ∘ exl) p);
    destruct ((one[b] ∘ (exr : a × b ~{Sets@{o so}}~> b)) p); reflexivity.
Defined.

Definition pbone_from_prod@{o so} (a b : obj[Sets@{o so}]) :
  a × b ~{Sets@{o so}}~> pbone@{o so} a b :=
  unique_obj (ump_pullbacks _ _ (PBONE@{o so} a b) (a × b) exl exr
                (pbone_sq@{o so} a b)).

Definition pullback_over_one_is_product@{o so} (a b : obj[Sets@{o so}]) :
  pbone@{o so} a b ≅ a × b.
Proof.
  unshelve refine {| to := pbone_to_prod@{o so} a b
                   ; from := pbone_from_prod@{o so} a b |}.
  - destruct (unique_property
                (ump_pullbacks _ _ (PBONE@{o so} a b) (a × b) exl exr
                   (pbone_sq@{o so} a b))) as [H1 H2].
    intro p; split; [ exact (H1 p) | exact (H2 p) ].
  - intro p; split; reflexivity.
Defined.

(*
 “with its projections to the given factors a and b”: the four leg
 equations, at the setoid relation. 

 --------
 “以其对给定因子 a 和 b 的投影”：四条支腿方程，在集合等价关系下。
*)
Lemma pbone_to_exl (a b : obj[Sets]) :
  exl ∘ pbone_to_prod a b ≈ pbone_fst a b.
Proof. intro p; reflexivity. Qed.

Lemma pbone_to_exr (a b : obj[Sets]) :
  exr ∘ pbone_to_prod a b ≈ pbone_snd a b.
Proof. intro p; reflexivity. Qed.

Lemma pbone_from_fst (a b : obj[Sets]) :
  pbone_fst a b ∘ pbone_from_prod a b ≈ exl.
Proof.
  exact (fst (unique_property
                (ump_pullbacks _ _ (PBONE a b) (a × b) exl exr
                   (pbone_sq a b)))).
Qed.

Lemma pbone_from_snd (a b : obj[Sets]) :
  pbone_snd a b ∘ pbone_from_prod a b ≈ exr.
Proof.
  exact (snd (unique_property
                (ump_pullbacks _ _ (PBONE a b) (a × b) exl exr
                   (pbone_sq a b)))).
Qed.

(*
 The mediator REDUCES: Instance/Sets/Pullback.v's [Sets_IsPullback] is
 [Defined], so the pullback's universal property computes. 

 --------
 中介者减少：Instance/Sets/Pullback.v 的 [Sets_IsPullback] 是 [Defined]，因此拉回的泛性质可以计算。
*)
Example pbone_from_computes (a b : obj[Sets]) :
  pbone_from_prod a b = sets_pb_med one one exl exr (pbone_sq a b) := eq_refl.

(* and the topos's own chosen pullback over 1 is that one / 而拓扑的自身选择的在 1 上的回拉就是那个 1 *)
Example app1_pullback_is_topos_pullback (U : Untruncate) (a b : obj[Sets]) :
  @pullback Sets (@topos_pullbacks Sets (Sets_Topos U)) a b
    (@terminal_obj Sets (@topos_terminal Sets (Sets_Topos U))) one one
  = PBONE a b := eq_refl.

(* * ** (C) App.1 clause (c): Ω, truth, and the classifying rule / * **（C）附录1 条款（c）：Ω、真理及分类规则 *)

(*
 Mac Lane's “any set 2 consisting of two objects, 1 and 0”, on the
 decidable route. 

 --------
 麦克·莱恩的“任何由两个对象 1 和 0 组成的集合 2”，在可判定路径上。
*)
Example app1_omega_dec (D : DecImage) :
  @Ω Sets _ (@topos_classifier Sets (Sets_Topos_dec D)) = BoolSetoid
  := eq_refl.
Example app1_omega_dec_carrier (D : DecImage) :
  carrier (@Ω Sets _ (@topos_classifier Sets (Sets_Topos_dec D)))
  = poly_bool := eq_refl.
Example app1_truth_dec (D : DecImage) :
  @truth Sets _ (@topos_classifier Sets (Sets_Topos_dec D)) ttt = ptrue
  := eq_refl.

(* and the truncation route's own truth-value object / 以及截断路线自身的真值对象 *)
Example app1_omega_U (U : Untruncate) :
  @Ω Sets _ (@topos_classifier Sets (Sets_Topos U)) = Powerset_Omega
  := eq_refl.
Example app1_truth_U (U : Untruncate) :
  @truth Sets _ (@topos_classifier Sets (Sets_Topos U)) ttt
  = Powerset_truth_point := eq_refl.

(* “the monomorphism t : 1 → 2”: monic for free, from the derived [truth_monic] of Structure/SubobjectClassifier.v. / “单射 t : 1 → 2”：天然单射，来自 Structure/SubobjectClassifier.v 的导出 [truth_monic]。 *)
Definition app1_truth_monic (U : Untruncate) :
  @Monic Sets _ _ (@truth Sets _ (@topos_classifier Sets (Sets_Topos U)))
  := @truth_monic Sets _ _.

(* “This subset has a well-known characteristic function ψ : b → 2”: the classifying rule, applied verbatim at the topos-level classifier on both routes. / 该子集具有一个众所周知的特征函数 ψ : b → 2：在拓扑层分类器上按原样应用的分类规则，对两条路径都适用。 *)
Definition app1_char_rule_dec@{o so} (D : DecImage@{o so})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) (b : carrier x) :
  (@char Sets@{o so} _
     (@topos_classifier Sets@{o so} (Sets_Topos_dec@{o so} D)) u x m M b
     ≈ @truth Sets@{o so} _
         (@topos_classifier Sets@{o so} (Sets_Topos_dec@{o so} D)) ttt)
    ↔ sets_in_image@{o} m b
  := sets_classifier_dec_char_iff@{o so} D m M b.

Definition app1_char_rule_U@{o so} (U : Untruncate@{o})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) (b : carrier x) :
  (@char Sets@{o so} _
     (@topos_classifier Sets@{o so} (Sets_Topos@{o so} U)) u x m M b
     ≈ @truth Sets@{o so} _
         (@topos_classifier Sets@{o so} (Sets_Topos@{o so} U)) ttt)
    ↔ sets_in_image@{o} m b
  := sets_classifier_char_iff@{o so} U m M b.

Example app1_char_dec_strict@{o so} (D : DecImage@{o so})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) :
  @char Sets@{o so} _
    (@topos_classifier Sets@{o so} (Sets_Topos_dec@{o so} D)) u x m M
  = char_of_dec@{o so} m M (D u x m M) := eq_refl.

Example app1_char_U_strict@{o so} (U : Untruncate@{o})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) (b : carrier x) :
  @char Sets@{o so} _
    (@topos_classifier Sets@{o so} (Sets_Topos@{o so} U)) u x m M b
  = Powerset_squash@{o} (sets_in_image@{o} m b) := eq_refl.

(* “such that the following square is a pullback” -- display (2) and its uniqueness clause are the class's own two fields, re-exposed at the bundle so that they can be quoted at a topos. / “使得下列方格是一个拉回图”——显示 (2) 及其唯一性条款是该类自身的两个字段，在丛上重新暴露，以便它们可以在拓扑中被引用。 *)
Definition app1_classifying_square@{o so} (U : Untruncate@{o})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) :=
  @char_pullback Sets@{o so} _
    (@topos_classifier Sets@{o so} (Sets_Topos@{o so} U)) u x m M.

Definition app1_classifying_unique@{o so} (U : Untruncate@{o})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) :=
  @char_unique Sets@{o so} _
    (@topos_classifier Sets@{o so} (Sets_Topos@{o so} U)) u x m M.

(* * ** (D) App.1 clause (d): P b IS the power set of b / * **（D）附录1 条款（d）：P b 是 b 的幂集 *)

(*
 Mac Lane's “P b, the set of all subsets s of b” -- definitional, not
 an isomorphism.  See the header for why the two records coincide. 

 --------
 Mac Lane 的“P b，b 的所有子集 s 的集合”——定义性的，而不是同构的。参见标题了解为何这两个记录一致。
*)
Example app1_pow_is_powerset (U : Untruncate) (b : obj[Sets]) :
  @Pow Sets (Sets_Topos U) b = Powerset_Prop_obj b := eq_refl.

Example app1_pow_carrier (U : Untruncate) (b : obj[Sets]) :
  carrier (@Pow Sets (Sets_Topos U) b)
  = SetoidMorphism b Powerset_Prop_truth := eq_refl.

(* On the decidable route it is the DECIDABLE power set instead. / 在可判定路径上，它是可判定幂集。 *)
Example app1_pow_dec_carrier (D : DecImage) (b : obj[Sets]) :
  carrier (@Pow Sets (Sets_Topos_dec D) b) = SetoidMorphism b BoolSetoid
  := eq_refl.

(* Membership: Mac Lane's ε_b is function application. MIND THE ARGUMENT ORDER -- he writes ε_b(x, s) with the element first, and this tree's [eval : y^x × x ~> y] takes the subset first. / 成员资格：Mac Lane 的 ε_b 是函数应用。注意参数顺序——他写作 ε_b(x, s) 时先写元素，而这个树的 [eval : y^x × x ~> y] 则先写子集。 *)
Example app1_eval_is_application (U : Untruncate) (b : obj[Sets])
  (s : carrier (@Pow Sets (Sets_Topos U) b)) (x : carrier b) :
  @eval Sets Sets_Cartesian Sets_Closed b
        (@Ω Sets _ (@topos_classifier Sets (Sets_Topos U))) (s, x) = s x
  := eq_refl.

Example app1_eval_dec_is_application (D : DecImage) (b : obj[Sets])
  (s : carrier (@Pow Sets (Sets_Topos_dec D) b)) (x : carrier b) :
  @eval Sets Sets_Cartesian Sets_Closed b
        (@Ω Sets _ (@topos_classifier Sets (Sets_Topos_dec D))) (s, x) = s x
  := eq_refl.
