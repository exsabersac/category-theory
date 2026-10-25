Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Theory.Sieve.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.SubobjectClassifier.Natural.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Terminal.
Require Import Category.Instance.Fun.Morphisms.
Require Import Category.Instance.Fun.Pullback.
Require Import Category.Instance.Two.
Require Import Category.Instance.FinSet.

Generalizable All Variables.

Set Default Proof Using "All".

(* * * The subobject classifier of a set-valued functor category / * * 集值函子范畴的子对象分类器 *)

(*
 Mac Lane, CWM 2nd ed., §IV.9 construction 2 and remark 1, book
 pp. 105-106 ([maclane:IV.9:construction2], [maclane:IV.9:remark1]).
 Verbatim, from the rendered pages:

 "For example, take C to be the category of functions f : X → Y.
 Here, a monomorphism g ↣ f is a function g : S → T between a pair
 of subsets S ⊂ X and T ⊂ Y such that g(s) = f(s) for all s ∈ S.
 ...  In this case, there are three types of elements of X: those x
 in S, those x not in S but with g x in T, and, finally, those x not
 in S with g x not in T.  We may then define a characteristic
 function with three values by setting

 ψ_S x = 0  if x ∈ S ,
 ψ_S x = 1  if x ∉ S but f x ∈ T ,
 ψ_S x = 2  if f x ∉ T (and hence, x ∉ S) .

 Again this prescription provides a pullback ... of objects X → Y
 and j : {0,1,2} → {0, 1} in the category of functions, where the
 function j on the right is given by j0 = 0, j1 = 0, j2 = 2.  Thus,
 in this case, the inclusion j on the right is a subobject
 classifier for the category of functions."

 "There are many other examples of subobject classifiers.  First,
 recall that the arrow category 2 is the category with only two
 objects 0 and 1 and only one non-identity arrow a : 0 → 1.  Thus,
 an ordinary function f is the same thing as a functor 2 → Sets.
 Hence, we have constructed above the subobject classifier for the
 functor category Sets^2.  For any category C, there is a subobject
 classifier (find it!) for the functor category Sets^C."

 THE PRINTED PAGE CARRIES A MISPRINT, and it is recorded rather than
 silently corrected: the text says "j : {0,1,2} → {0, 1}" while the
 diagram's lower-right corner is "{0,2}" and the formula in the same
 sentence is "j0 = 0, j1 = 0, j2 = 2".  The diagram and the formula
 agree with each other, so the codomain of j is the two-element set
 {0, 2} and the text's "{0, 1}" is the misprint.  The mathematics
 below follows the diagram and the formula.

 Awodey, *Category Theory* (1st ed., Carnegie Mellon pre-print,
 September 2005), §8.8, printed pp. 210-211, inside the proof of
 Proposition 8.17 ([awodey:8.8:def-sieve],
 [awodey:8.8:construction-omega-sieves]).  Verbatim:

 "To that end, for any category C we define a sieve on an object C
 to be any set S of arrows f : · → C (with arbitrary domain) that
 is closed under precomposition ...  Then let:

 Ω(C) = {S ⊆ C_1 | S is a sieve on C}

 and given h : D → C let:  h* : Ω(C) → Ω(D)  be defined by:
 h*(S) = {g : · → D | h ∘ g ∈ S}.

 This clearly defines a presheaf Ω : C^op → Sets, with a
 distinguished point, t : 1 → Ω, namely, at each C, the "total
 sieve": t_C = {f : · → C}."

 "We claim that t : 1 → Ω so defined is a subobject classifier for
 Sets^{C^op}.  Indeed, given any object E and subobject U ↣ E,
 define u : E → Ω at any object C ∈ C by:

 u_C(e) = {f : D → C | f*(e) ∈ U(D) ↣ E(D)}

 for any e ∈ E(C).  That is, u_C(e) is the sieve of arrows into C
 that take e ∈ E(C) back into the subobject U.

 The reader should verify that this specification does indeed
 determine a unique classifying morphism for U ↣ E.  □"

 Mac Lane's Sets^C is the COVARIANT functor category [C, Sets] and
 Awodey's Ω is for PRESHEAVES [C^op, Sets].  The two are one family
 with C replaced by C^op, and here that replacement costs nothing:
 [(D^op)^op = D] holds by [eq_refl] in this tree, so the covariant
 reading [Fun_Classifier_cov] is [Fun_Classifier] at [D^op] supplied
 by [:=] with no tactic and no transport.

 WHAT IS DELIVERED, AND AT WHICH STRENGTH.  A genuine
 [@SubobjectClassifier ([C^op, Sets]) (Functor_Category_Terminal
 Sets_Terminal)] for an ARBITRARY category C — at the universe levels
 the presheaf category itself forces, see UNIVERSES below —
 CONDITIONALLY on #402's [Untruncate@{o}], in two universe readings:

 [Fun_Classifier      : Untruncate -> SubobjectClassifier] at the
 minimized reading of the presheaf category, with
 Ω := [Sieve_Presheaf C] (Theory/Sieve.v) and
 truth := [sieve_truth C], both read back by [eq_refl], and the
 characteristic map read back as [char_nat] likewise;

 [Fun_Classifier_small : ... -> SubobjectClassifier] at a reading
 that places the presheaf category's OBJECTS at or below its
 HOMS, which is what Structure/SubobjectClassifier.v's
 [classifier_classifies] demands — see WORK ITEM 2 below.

 [Fun_Classifier_IEM] is the first at #402's [untruncate_of_IEM], and
 [Fun_Classifier_cov] the covariant reading.  Neither is registered as
 an [Instance]: the hypothesis must not become globally resolvable,
 and neither must a chosen classifier.

 THE PER-CONSTANT HYPOTHESIS LEDGER, MEASURED AT THE SIGNATURES.  The
 three class obligations cost three different things, and this is the
 file's sharpest fact.

 [char_nat], [char_square]   NO hypothesis at all.  They are section
 constants of Section Char, whose Context is C, E, U and theta and
 nothing else, so no [Monic] and no [Untruncate] occurs in either
 type.  The classifying square commutes for an ARBITRARY natural
 transformation, monic or not.

 [presheaf_char_unique]      NO hypothesis either — neither [Monic]
 nor [Untruncate].  Section Unique's Context is C, E, U, theta, h and the
 [IsPullback] the caller supplies.  Awodey's "the reader should verify
 ... a UNIQUE classifying morphism", which the issue flags as real work,
 is the CHEAP half here.  What pays for it is the sieve read as a
 SUBPRESHEAF: [h_sub_char] feeds the pullback's own universal property
 [sieve_subpresheaf d S], the presheaf of the arrows into d that lie in
 the sieve, together with its cone [sieve_cone] into E, and the witness
 comes OUT of the mediator as a genuine element, so no truncation is
 eliminated anywhere in it.  The Awodey §8.8 "standalone, exported Sieve
 as a subobject of the representable" checkbox is the further step
 [sieve_incl] / [sieve_incl_Monic] / [sieve_subobject], that subpresheaf
 embedded in [Curried_CoHom C d]; the three form a chain ending in
 [sieve_subobject], and NOTHING outside the chain consumes any of them —
 measured by deleting all three and recompiling the file, which succeeds
 — so the checkbox is delivered as a standalone reading of Awodey's
 clause, and the uniqueness clause consumes only the subpresheaf and its
 cone.

 [presheaf_char_pullback]    needs BOTH.  [Monic theta] is turned
 into pointwise injectivity by #369's
 [presheaf_monic_iff_injective] (Instance/Fun/Morphisms.v) — this
 is the issue's reviewer check, "the monos used are the pointwise
 ones, which requires the pointwise mono characterisation" — and
 that injectivity, named [theta_inj] here, is spent at THREE
 SITES on the way to [presheaf_char_pullback] — the mediator
 [char_med]'s respectfulness obligation, its naturality (two
 obligations, [Transform] carrying both [naturality] and
 [naturality_sym]), and the uniqueness clause of
 [presheaf_char_pullback] itself — which is FOUR uses; a fifth
 is section (I)'s [small_pb], which rebuilds only that last
 clause.  [Untruncate] is spent EXACTLY ONCE, in [med_img],
 where the commuting hypothesis at f := id gives a squashed image
 membership and the mediator must produce an ELEMENT — the token
 [UT] is eliminated at exactly one line of the file.

 WHETHER [Untruncate] IS NECESSARY IS NOT SETTLED.  It SUFFICES; no
 impossibility is proved, and no weaker hypothesis was searched for.
 What IS measured is that the naive elimination
 [fun P h => h P (fun p => p)] is refused with "Cannot enforce
 o <= Prop" — #402's wall, at the same level o — with
 [powerset_squash_prop_inert] as the accepted control, both pinned in
 Test/ProbeFunClassifier403.v.  No [DecImage]-shaped variant is built.

 THE DISCLOSURE, IN THREE PARTS, following #402's.  (i) NO
 unconditional axiom-free instance is built here.  (ii) NO
 impossibility theorem is proved here.  (iii) An in-tree impossibility
 proof is out of reach in a precise sense: a scratch development
 compiled against this worktree builds [Fun_Classifier
 (untruncate_of_IEM IEM_classical)] out of Coq's own classical axioms
 and [Print Assumptions] reports EXACTLY [constructive_indefinite_
 description] and [classic] (Coq.Logic.ClassicalEpsilon), so an
 in-tree impossibility theorem would refute a classically valid
 statement.  That is an ARGUMENT, not a theorem: nothing below proves
 it, and the classical instance is deliberately not shipped.

 THE TRUTH-VALUE CONVENTION, AND THE DICTIONARY.  Every subobject
 classifier puts ITS truth value on the subobject — that is what the
 classifying pullback square says — so a "convention" here can only be
 the NAME the truth value carries.  Mac Lane names his 0 (§IV.9
 construction 1, book p. 105: ψ_S x = 0 if x ∈ S, with 0 the value
 "truth"); Seven Sketches names it [true]; Instance/FinSet/Classifier.v
 names it [fin_true], which is [Fin.F1], the FIRST element of [Fin.t 2] —
 so read as a numeral it is Mac Lane's 0, and the "swap 0 ↔ 1" that
 Instance/Sets/Classifier/OneLevel.v records is between the two books'
 NAMES, not between elements of any in-tree Ω; and OneLevel.v's two
 instances name theirs [Powerset_truth_point] and [ptrue], with no
 numeral at all.  Here Ω(c) is a set of SIEVES and the truth point is the
 total sieve: an element of the subobject has the total characteristic
 sieve ([char_square], no hypothesis), and the converse is the pullback
 clause, where [Untruncate] is spent.  There is no numeral in Ω(c) and
 nothing to swap.

 The numeral enters only at the arrow shape, through section (G)'s
 codes [twoX_code : Sieve TwoX → Fin.t 3] and
 [twoY_code : Sieve TwoY → Fin.t 2], and there the dictionary

 total sieve on TwoX  ↔  0        {TwoXY}  ↔  1        ∅  ↔  2
 total sieve on TwoY  ↔  0                            ∅  ↔  2

 is FORCED rather than chosen, by two facts.  The page puts 0 ON the
 subset and an element of the subobject has the total characteristic
 sieve, so the total sieve is 0 — the same [Fin.F1] that [fin_true] is,
 so numeral for numeral this file, Instance/FinSet/Classifier.v and the
 page agree.  Then [jmap := fmap[Sieve_Presheaf (_2^op)] TwoXY] carries
 total ↦ total, mid ↦ total, empty ↦ empty ([j_total], [j_mid],
 [j_empty]), so it IDENTIFIES the first two and SEPARATES the first from
 the third ([j_identifies], [j_separates]) — Mac Lane's j0 = 0, j1 = 0,
 j2 = 2 with codomain {0, 2}, whose fibres are {0, 1} and {2}; with total
 already at 0 that leaves {TwoXY} at 1 and ∅ at 2 on TwoX, and total at 0
 and ∅ at 2 on TwoY.  The three sieves on TwoX are pairwise ≉-distinct
 ([twoX_total_neq_mid], [twoX_mid_neq_empty], [twoX_total_neq_empty]),
 the two on TwoY likewise.  The identification with his EXPLICIT
 three-element object is [mac_dictionary]: under #402's [IEM] the codes
 satisfy [twoY_code (jmap S) = macj (twoX_code S)] for EVERY sieve S,
 where [macj] is Mac Lane's j written out and computing at all three
 arguments.  So the arrow-shape specialisation is PROVED, not asserted,
 which is the issue's other reviewer check.  The counts themselves —
 "exactly three sieves on TwoX" — are constructively unavailable (a sieve
 on TwoX is a pair of [Prop]s under mutual implication, so counting them
 is as strong as two-valuedness of [Prop]), and are delivered under [IEM]
 as [twoX_three_sieves] and [twoY_two_sieves].  This is the SAME
 conditionality as the general instance, for the same reason.

 WORK ITEM 2 ("subfunctors correspond to natural families of sieves,
 which is the content of the classification"), and the exact status of
 [classifier_classifies].  The sentence "classifier_classifies is not
 statable for presheaf categories" would be FALSE; the precise one is
 this.  The theorem carries the BOUND [u <= u0] over
 [C : Category@{u u0 u0}] — objects at or below homs — which is what
 #402 records as unsatisfiable at [Sets].  At a presheaf category it IS
 satisfiable, and three things are measured.  (a) The theorem is
 FORMABLE at an ABSTRACT classifier of [[C^op, Sets]] (a probe
 control).  (b) It is NOT applicable to [Fun_Classifier], whose own
 elaboration minimizes the presheaf category's hom universe below its
 object universe: the refusal is of the shape "Cannot enforce o = …
 because o < … <= … <= …", pinned.  (c) A HAND-ANNOTATED redefinition DOES
 escape it, and that is section (I): under declared universes with
 [so <= OO] and [OO <= HH], [PShSmall := [Cs^op, Sets@{o so}] :
 Category@{OO HH HH}] carries [Fun_Classifier_small], and
 [fun_classifier_classifies] is [classifier_classifies] applied to it
 over [Fun_HasPullbacks Sets_HasPullbacks] — an isomorphism in [Sets]
 between the subobjects of a presheaf and the maps into Ω.  That IS
 work item 2, in the form the issue calls "the content of the
 classification"; and its NATURAL upgrade comes with it, since
 Structure/SubobjectClassifier/Natural.v's [Sub_classifier_natural]
 carries the same bound — [fun_sub_classifier_natural] and
 [fun_Sub_Representable] are that theorem and its representability
 corollary applied.  The re-annotation is NOT free: [small_pb] reuses the
 already-built pieces, but the uniqueness clause has to be RESTATED
 ([small_char_sub_h], [small_h_sub_char], [small_unique]), because
 [presheaf_char_unique] takes an [IsPullback] and the two universe
 readings of that argument are not interconvertible — measured:
 supplying section (I)'s [IsPullback] to [presheaf_char_unique] is
 refused with a universe inconsistency at that argument, the field where
 the two readings visibly differ being [ump], which quantifies over the
 ambient category's objects and hom-types.  The two
 ROUND TRIPS of Structure/SubobjectClassifier.v are delivered for the
 minimized reading as well ([fun_char_roundtrip],
 [fun_pullback_roundtrip]), both [:=] of that file's own constants,
 both NAMING [Fun_HasPullbacks Sets_HasPullbacks] explicitly in their
 statements — it is a plain [Definition], not an [Instance], so nothing
 resolves it silently.

 WHY THREE FILES.  Theory/Sieve.v is LEAN (closure 16, a subset of
 both Theory/Sheaf.v's 18 and Construction/Localization.v's 23, so
 either could reuse it later at zero module cost; neither is rewired
 here).  Instance/Fun/Pullback.v is a general [C, D] result with no
 [Sets] in it at all.  This file is the [Sets]-valued assembly, and it
 is where [Functor/Hom.v]'s [Curried_CoHom] and
 Instance/Fun/Morphisms.v's mono characterisation enter, neither of
 which is in the lean closure.

 UNIVERSES, measured off BOTH binder and block over all 115 constants.
 [Fun_Classifier@{u u0 u1}] is over [C : Category@{u1 u u}] with
 [Untruncate@{u}] — C's hom universe, C's proof universe and [Sets]' CARRIER
 universe are all the single level [u], and that identification sits ENTIRELY
 IN THE BINDER: its constraint block carries NO equation at all, only bounds
 ([Set < u], [u < u0], [u1 <= u] and stdlib bounds), and
 [Fun_Classifier_small@{co o so OO HH u u0}] carries none either (its block
 adds no equation to the four declared constraints of section (I), [Set < o],
 [o < so], [so <= OO] and [OO <= HH]; the rest are bounds — eight relating the
 declared levels to each other and to the constant's own [u], and the stdlib
 ones).  Reading the block alone reports no identification and is wrong.
 TWENTY of the 115 do carry a block equation, and it is a different one.
 FOURTEEN — Section Char's [Efmap_resp], [Efmap_comp], [Efmap_id],
 [theta_natural], [in_image], [char_sieve], [char_at], [char_nat],
 [char_square] and their five [Program] obligations — carry [u1 = u2],
 identifying the [Sets] universes of the two presheaves E and U: that section
 binds E and U on SEPARATE Context lines, so each gets its own [Sets]
 instance, and [Context (theta : U ⟹ E)] — a transformation lives between
 functors into ONE [Sets] — equates them, an equation handed to every constant
 of the section by discharge, [Efmap_resp] included though its own type never
 mentions U or theta; the same body in a section binding E and U on separate
 lines but no theta carries no equation (measured out of tree, not pinned).
 WHERE the identification lands is decided by the binding shape and not by
 theta: Section Pullback has the same [theta] in its Context but binds
 [{E U : C^op ⟶ Sets}] on ONE line, so its constants share the level in the
 BINDER and carry no block equation at all, [presheaf_char_pullback] included.
 THREE — Section Unique's [char_sub_h], [h_sub_char] and
 [presheaf_char_unique] — also bind [{E U}] on one line, and their [u1 = u2]
 is a DIFFERENT identification under the same spelling: [u2] there is a
 universe [Sieve_Presheaf] brings in through
 [Context (h : E ⟹ Sieve_Presheaf C)], which BOUNDS it ([u0 < u2]) without
 identifying it, and the equation is the [IsPullback] Context [HP]'s — the
 same Context without [HP] carries no equation and with it carries this one
 (measured out of tree, not pinned; that [HP] places E, U and
 [Sieve_Presheaf C] as objects of ONE functor category is an explanation, not
 the measurement).  The other THREE are section (I)'s [small_char_sub_h],
 [small_h_sub_char] and [small_unique], which carry [so = u0] (and [so = u])
 from the declared constraints.  [Sieve_Presheaf] and [SieveObj] carry none,
 and neither does anything in Instance/Fun/Pullback.v except [Fun]'s own
 [u0 = u2], which SEVENTEEN of that file's 24 do carry.  SIXTY-THREE of the
 115 carry a word-bounded [Set], always as the strict LOWER bound [Set < _]
 and never as an equation.  The two BINDER identifications are the presheaf
 category's, not this file's, and each is guarded by a probe negative with
 controls accepted at the very same levels: [ch = cp] has TWO INDEPENDENT
 donors, [Opposite] and [Fun] (the second refused with no [^op] in the command
 at all), while [@Functor Cu Cu] and [@Functor Cu Sets] are ACCEPTED, so
 [Functor] is not a donor; and [ch = o] is [Fun]'s in BOTH variances, with
 [Cv^op], [Cv^op ⟶ Sets] and [Cv ⟶ Sets] accepted as controls.  C's OBJECT
 universe is only BOUNDED ([u1 <= u]), which is Awodey's "for any SMALL
 category C" and is where smallness lands.  The strict lower bound [Set < u]
 enters with the [Prop]-valued membership itself ([Prop : Type@{Set+1}]) — it
 is already [SieveObj]'s in Theory/Sieve.v, upstream of any [Powerset_squash]
 — and is a BOUND, never a pin, but it excludes exactly the C whose hom
 universe is the literal [Set].  TWENTY-ONE constants carry [Set] in a BINDER
 and every one of them is section (G)'s — most as [Sieve@{_ Set}], the rest
 through [_2] or [FinSet] — inherited from Instance/Two.v's
 [TwoHom : TwoObj → TwoObj → Set] and not introduced here; the other thirty of
 section (G)'s fifty-one heads carry [Set] only as the block bound above.

 THE ISSUE'S "Current state" IS STALE ON FOUR COUNTS, each measured.  It says
 [ls Instance/Fun/] "contains only [Cartesian.v]"; at the base commit that
 directory has SEVEN satellites (Cartesian, Terminal, Closed, Morphisms,
 Discrete, Group, Action).  It says there is "not even a [Terminal] instance
 for a functor category"; that is #339's [Functor_Category_Terminal], and
 Instance/Fun/Terminal.v even carries the specialised [Two_Sets_Terminal].  It
 says the pointwise mono characterisation is missing; that is #369's
 [presheaf_monic_iff_injective].  And it says the only [SubobjectClassifier]
 instance in the tree is Instance/FinSet/Classifier.v's; #402 added two
 conditional ones for [Sets].  What IS genuinely absent, and is what these
 three files supply, is any sieve at all (at the base commit
 [rg -in 'sieve' -g '*.v'] returns two prose lines, one in Theory/Sheaf.v and
 one in Construction/Localization.v; without the [-g] the doc/plan coverage
 records add 143 more), any classifier for a functor category, and any
 pullback instance for a functor category.

 COUNTS, WITH THEIR CRITERIA.  Constants closed under the global
 context: 115/115 with zero [Axioms:] lines, counted as the entries
 [Print Module] emits at five-space indent (which include the
 [Program] obligations, invisible to the [.glob]); this file declares
 no record, so there is no unlisted [Build_*].  Every one is queried
 FULLY QUALIFIED, and all 115 are in the [print-assumptions] gate,
 which carries 161 names for the three files together.  [Defined]
 tokens: 7, of which FOUR are load-bearing — measured by flipping each
 ALONE to [Qed] and compiling the result alone: [sieve_sub_map],
 [sieve_subpresheaf], [sieve_incl] and [sieve_cone] all stop the file,
 while [med_img], [presheaf_char_pullback] and [small_pb] compile as
 [Qed] and are kept [Defined] only because they produce data.
 Statements closed by [:= eq_refl]: 14.  Transitive
 in-project closure excluding this file: 105 modules, with drop-one
 marginals Instance/Fun/Terminal 29, Instance/Sets/Classifier/OneLevel
 14, and Theory/Sieve, Structure/SubobjectClassifier/Natural,
 Instance/Fun/Morphisms and Instance/Fun/Pullback 1 each; EVERY other
 Require costs 0, Instance/FinSet included, which is why [MacOmega] can
 live here rather than in the probe.  The 14 for
 OneLevel is what identity with #402's hypothesis costs, and it is paid
 deliberately: restating
 [Untruncate] locally would fork the hypothesis, which is the whole
 point of consuming it.  This file contributes ZERO [make todo] hits;
 its probe carries the refutation commands.

 NOT DELIVERED.  No unconditional axiom-free instance and no impossibility
 theorem (the three-part disclosure above).  No proof that [Untruncate] is
 necessary, and no [DecImage] variant.  No
 [@SubobjectClassifier ([_2, FinSet]) _] instance: [MacOmega] is built and
 computes, but the instance would need the shape-[_2] converse of the mono
 characterisation and a three-way characteristic map, neither of which is
 built.  No bijection between the sieves on TwoX and [Fin.t 3] without [IEM] —
 [twoX_code] is defined only from it.  No converse for [Fun_IsPullback]
 (Instance/Fun/Pullback.v's own NOT DELIVERED).  No pushouts, equalizers or
 completeness for [C, D].  No [ElementaryTopos] for any presheaf category and
 no exponentials: Instance/Fun/Closed.v refutes the inheritance of cartesian
 closure in general, and its positive half is not attempted here.  NATURALITY
 IS DELIVERED, but only at the second reading: [Sub_classifier_natural] is
 MEASURED to be formable at an abstract classifier of [[C^op, Sets]] and
 refused at [Fun_Classifier] — the same pair as [classifier_classifies] —
 while at [Fun_Classifier_small] it applies, and is shipped as
 [fun_sub_classifier_natural] with [fun_Sub_Representable] beside it.  So
 there is NO naturality statement for [Fun_Classifier] itself.  No
 Grothendieck topology, no coverage and no sheaf reading; Theory/Sheaf.v and
 Construction/Localization.v are NOT rewired, only pointed at this file in
 prose.  No comparison of [Sieve_Presheaf] at a poset with a lower-set
 construction.  No passage from a subobject of the representable BACK to a
 sieve: [sieve_subobject] runs one way only, so Awodey's "as a subobject of
 the representable" is delivered as an embedding of sieves and not as an
 identification of the two notions — and nothing outside the chain
 [sieve_incl] / [sieve_incl_Monic] / [sieve_subobject] consumes it, the
 uniqueness clause taking the subpresheaf and its cone instead (the ledger
 above).  No comparison of [Fun_Classifier] with [Fun_Classifier_small] at any
 strength: they are two universe readings of one construction, and no equation
 relates them.  Nothing at all is registered as an [Instance] in this file:
 the setoid [sieve_sub_obj] needs is an inline record literal, and the only
 registered instance of the three files is Theory/Sieve.v's [Sieve_Setoid]. 

 --------
 Mac Lane, CWM 第2版，§IV.9 构造 2 和备注 1，书本第 105-106 页（[maclane:IV.9:construction2]，[maclane:IV.9:remark1]）。
 逐字，从渲染的页面：

 “例如，取 C 为函数 f : X → Y 的范畴。
 在这里，一个单态射 g ↣ f 是一个函数 g : S → T，作用于一对子集 S ⊂ X 和 T ⊂ Y，使得对所有 s ∈ S，有 g(s) = f(s)。
 ... 在这种情况下，X 有三种类型的元素：那些在 S 中的 x；那些不在 S 中但 g(x) ∈ T 的 x；最后，那些不在 S 且 g(x) 不在 T 的 x。我们可以通过如下定义构造一个三值特征函数

 ψ_S x = 0  如果 x ∈ S ，
 ψ_S x = 1  如果 x ∉ S 但 f(x) ∈ T ，
 ψ_S x = 2  如果 f(x) ∉ T（因此，x ∉ S）。”再次，这个规定提供了一个拉回 ... 对象 X → Y 和 j : {0,1,2} → {0, 1} 在函数范畴中的映射，其中右边的函数 j 定义为 j0 = 0, j1 = 0, j2 = 2。因此，在这种情况下，右边的包含映射 j 是函数范畴的子对象分类器。

 还有许多其他子对象分类器的例子。首先，回想一下箭头范畴 2，它是一个只有两个对象 0 和 1 并且只有一个非恒等箭头 a : 0 → 1 的范畴。因此，一个普通函数 f 与一个函子 2 → 集合 是同一个东西。因此，我们在上面构造了函子范畴 Sets^2 的子对象分类器。对于任意范畴 C，对于函子范畴 Sets^C，也存在一个子对象分类器（去找到它！）。印刷页有一个印刷错误，它被记录下来而不是默默地更正：文本写着“j : {0,1,2} → {0, 1}”，而图的右下角是“{0,2}”，同一句话中的公式是“j0 = 0, j1 = 0, j2 = 2”。图和公式相互一致，因此 j 的陪域是双元素集合 {0, 2}，而文本中的“{0, 1}”是印刷错误。下面的数学内容遵循图和公式。

 Awodey, *Category Theory*（第1版，卡内基梅隆预印本，2005年9月），§8.8，第210-211页，在命题 8.17 的证明中（[awodey:8.8:def-sieve], [awodey:8.8:construction-omega-sieves]）。逐字原文:为此，对于任意范畴 C，我们在对象 C 上定义筛子为任意箭头集合 S，它由 f : · → C（域任意）组成，并且在前复合下封闭……然后令：

 Ω(C) = {S ⊆ C_1 | S 是 C 上的筛子}

 并且给定 h : D → C，令 h* : Ω(C) → Ω(D) 定义为：
 h*(S) = {g : · → D | h ∘ g ∈ S}。

 这显然定义了一个预层 Ω : C^op → Sets，并且有一个特殊点 t : 1 → Ω，即在每个 C 处的“全筛子”：t_C = {f : · → C}。

 我们声称这样定义的 t : 1 → Ω 是 Sets^{C^op} 的子对象分类器。事实上，给定任意对象 E 和子对象 U ↣ E，在 C ∈ C 的任意对象处定义 u : E → Ω 为：

 u_C(e) = {f : D → C | f*(e) ∈ U(D) ↣ E(D)}对于任何 e ∈ E(C)。也就是说，u_C(e) 是箭头流入 C 的筛子，这些箭头将 e ∈ E(C) 映回子对象 U。

 读者应验证该规范确实确定了 U ↣ E 的唯一分类态射。□

 Mac Lane 的 Sets^C 是协变函子范畴 [C, Sets]，而 Awodey 的 Ω 是用于余屢 [C^op, Sets]。这两者是一族关系，区别在于 C 被替换为 C^op，在这里这种替换没有任何代价：[(D^op)^op = D] 在此树上通过 [eq_refl] 成立，因此协变读法 [Fun_Classifier_cov] 在 [D^op] 由 [:=] 提供，无需策略也无需传递。交付的内容及其强度。一个真正的 [@SubobjectClassifier ([C^op, Sets] ) (Functor_Category_Terminal Sets_Terminal)] 对于任意范畴 C — 在预层范畴自身强制的宇宙层次上，见下文的 UNIVERSES — 条件于 #402 的 [Untruncate@{o}]，在两种宇宙解释下：

 [Fun_Classifier      : Untruncate -> SubobjectClassifier] 在预层范畴的最小化解释下，其中 Ω := [Sieve_Presheaf C] (Theory/Sieve.v) 并且 truth := [sieve_truth C]，两者都由 [eq_refl] 读取回来，并且特征映射同样由 [char_nat] 读取回来；

 [Fun_Classifier_small : ... -> SubobjectClassifier] 在一种解释下，将预层范畴的对象放置在其 HOMS 的同级或以下，这正是 Structure/SubobjectClassifier.v 的 [classifier_classifies] 所要求的 — 见下文的工作项 2。[Fun_Classifier_IEM] 是 #402 的 [untruncate_of_IEM] 的第一个，而 [Fun_Classifier_cov] 是协变读数。两者都未注册为 [Instance]：假设不能变得全局可解，也不能选择分类器。

 每常量假设账本，在签名下测量。三个类的义务成本各不相同，这是该文件最尖锐的事实。

 [char_nat]，[char_square] 根本没有假设。它们是 Char 节的节常量，其上下文为 C、E、U 和 θ，除此之外没有其他，因此在任一类型中都没有 [Monic] 和 [Untruncate]。分类方阵对于任意自然变换都是可交换的，无论是否单映。[presheaf_char_unique]       没有假设 — 既不是  [Monic] 也不是  [Untruncate] 。Section Unique 的上下文是 C、E、U、theta、h 和调用者提供的 [IsPullback] 。Awodey 的“读者应该验证……一个独特的分类态射”，这个问题标记为真正的工作，是这里的便宜部分。真正起作用的是被当作子预层读取的筛子：[h_sub_char] 提供拉回自身的普遍性质 [sieve_subpresheaf d S]，以及位于筛子中的到 d 的箭头的预层，再加上它的 E 中的锥 [sieve_cone]，见证来自中介作为真实元素，因此其中任何地方都没有消除截断。Awodey §8.8“作为可表示对象的子对象的独立导出的Sieve”复选框是进一步步骤 [sieve_incl] / [sieve_incl_Monic] / [sieve_subobject]，这个子预层嵌入在 [Curried_CoHom C d] 中；三者形成一个以 [sieve_subobject] 结束的链，并且链外没有任何东西使用它们——通过删除这三者并重新编译文件来衡量，结果成功——因此该复选框作为 Awodey 条款的独立解读提供，而唯一性条款仅使用子预层及其圆锥。[presheaf_char_pullback] 需要两者。[Monic theta] 被转换为逐点单射性，通过 #369 的 [presheaf_monic_iff_injective] （Instance/Fun/Morphisms.v）——这是该问题的审查员检查，“使用的单态是逐点单态，需要逐点单态的表征”——而这个单射性，在此处命名为 [theta_inj]，在通向 [presheaf_char_pullback] 的过程中被使用在三个地方——调解器 [char_med] 的尊重义务，其自然性（两个义务，[Transform] 承担了 [naturality] 和 [naturality_sym]）、以及 [presheaf_char_pullback] 本身的唯一性条款——总计为四次使用；第五次是第 (I) 节的 [small_pb]，只重建最后那个条款。[Untruncate] 恰好使用了一次，在 [med_img] 中，
 通信假设在 f := id 时给出一个压缩的图像成员资格，并且中介者必须产生一个元素 —— 令牌 [UT] 在文件的恰好一行被消除。

 是否需要 [Untruncate] 尚未确定。它是充分的；没有证明不可能性，也没有寻找更弱的假设。真正被测量的是天真的消除 [fun P h => h P (fun p => p)] 被拒绝，并显示“无法强制 o <= Prop” —— #402 的限制，在同一级别 o —— 以 [powerset_squash_prop_inert] 作为接受的控制，两者都固定在 Test/ProbeFunClassifier403.v 中。没有构建任何 [DecImage] 形状的变体。披露分为三部分，紧随#402之后。(i) 此处未构建任何无条件无公理的实例。(ii) 此处未证明任何不可能性定理。(iii) 树内不可能性证明在精确定义的意义上是无法实现的：一个针对此工作树编译的临时开发项目构建了 [Fun_Classifier (untruncate_of_IEM IEM_classical)]，该构建基于 Coq 自身的经典公理，而 [Print Assumptions] 精确地报告了 [constructive_indefinite_description] 和 [classic] (Coq.Logic.ClassicalEpsilon)，因此树内的不可能性定理将反驳一个在经典意义下有效的命题。那是一个论证，而不是定理：以下内容没有证明它，并且经典实例是故意不提供的。真值约定与字典。每一个子对象分类器都将其真值放在子对象上——这正是分类拉回图所说的——所以这里的“约定”只能是该真值所携带的名称。Mac Lane 给他的 0 命名（§IV.9 构造 1, 书页 105：ψ_S x = 0 如果 x ∈ S，其中 0 是“真”的值）；《七个素描》给它命名为 [true]；Instance/FinSet/Classifier.v 给它命名为 [fin_true]，它是 [Fin.F1]，即 [Fin.t 2] 的第一个元素——所以作为数字读取时，它是 Mac Lane 的 0，而 Instance/Sets/Classifier/OneLevel.v 中记录的“交换 0 ↔ 1”是在两本书的名称之间，而不是 Ω 树中任何元素之间；OneLevel.v 的两个实例分别将它们命名为 [Powerset_truth_point] 和 [ptrue]，根本没有数字。这里 Ω(c) 是一组筛子，而真理点是总筛：子对象的一个元素具有总特征筛（[char_square]，无假设），而反之是拉回子句，其中 [Untruncate] 已经使用。Ω(c) 中没有数字，也没有可以交换的东西。

 数字只出现在箭头形态，通过部分 (G) 的代码 [twoX_code : Sieve TwoX → Fin.t 3] 和 [twoY_code : Sieve TwoY → Fin.t 2]，在那里字典是：

 TwoX 上的总筛 ↔ 0        {TwoXY} ↔ 1        ∅ ↔ 2
 TwoY 上的总筛 ↔ 0                            ∅ ↔ 2由两个事实决定，而非选择。该页面将 0 放在子集上，并且子对象的一个元素具有总特征筛子，因此总筛子为 0——与 [fin_true] 相同的 [Fin.F1]，因此在数字上，这个文件 Instance/FinSet/Classifier.v 与页面一致。然后 [jmap := fmap[Sieve_Presheaf (_2^op)] TwoXY] 映射 total ↦ total, mid ↦ total, empty ↦ empty ([j_total], [j_mid], [j_empty])，因此它 IDENTIFIES 前两个并区分第一个与第三个 ([j_identifies], [j_separates])——Mac Lane 的 j0 = 0, j1 = 0, j2 = 2，其余域为 {0, 2}，其纤维分别为 {0, 1} 和 {2}；在 total 已经为 0 时，TwoX 上 {TwoXY} 为 1，∅ 为 2，TwoY 上 total 为 0，∅ 为 2。TwoX 上的三个筛子两两 ≉-不同 ([twoX_total_neq_mid], [twoX_mid_neq_empty], [twoX_total_neq_empty])，TwoY 上的两个筛子同样如此。他对其明确的三元素对象的认同是 [mac_dictionary]：在 #402 的 [IEM] 下，这些代码对每一个筛子 S 满足 [twoY_code (jmap S) = macj (twoX_code S)]，其中 [macj] 是完整写出的 Mac Lane 的 j 并在三个参数上进行计算。因此，箭头形状的特化是被证明的，而不是被声明的，这是该问题的另一位审稿人需要检查的地方。计数本身——“TwoX 上恰好有三个筛子”——在构造上是不可用的（TwoX 上的筛子是相互蕴涵下的 [Prop] 对，因此对它们进行计数相当于 [Prop] 的二值性），并且在 [IEM] 下被作为 [twoX_three_sieves] 和 [twoY_two_sieves] 提供。这与一般实例的条件性是相同的，原因相同。工作项目 2（“子函子对应于筛子的自然族，这是分类的内容”），以及 [classifier_classifies] 的确切状态。句子“classifier_classifies 不适用于预上层范畴”将是错误的；准确说法是这个。该定理将 BOUND [u <= u0] 传递到 [C : Category@{u u0 u0}]——位于或低于同态的对象——这就是 #402 记录为在 [Sets] 处不可满足的原因。在预上层范畴中它是可满足的，并且测量了三件事。(a) 该定理在 [[C^op, Sets] 的抽象分类器上是可形成的（一个探针控制）。(b) 它不适用于 [Fun_Classifier]，其自身展开将预上层范畴的同态宇宙最小化到低于其对象宇宙：拒绝的形式是“无法强制 o = … 因为 o < … <= … <= …”，已固定。(c) 手动注释的重新定义确实能够绕过它，这就是第（I）节：在声明的宇宙下使用 [so <= OO] 和 [OO <= HH]，[PShSmall := [Cs^op, Sets@{o so}]：Category@{OO HH HH}] 携带 [Fun_Classifier_small]，并且 [fun_classifier_classifies] 是 [classifier_classifies] 在 [Fun_HasPullbacks Sets_HasPullbacks] 上应用的——这是在 [Sets] 中预层对象的子对象与到 Ω 的映射之间的同构。这正是工作项 2，以问题中称为“分类内容”的形式；其自然的升级随之而来，因为 Structure/SubobjectClassifier/Natural.v 的 [Sub_classifier_natural] 携带相同的界限——[fun_sub_classifier_natural] 和 [fun_Sub_Representable] 是该定理及其可表示性推论的应用。重新注释并不是免费的：[small_pb] 重用了已构建的部分，但必须重新声明唯一性条款（[small_char_sub_h]、[small_h_sub_char]、[small_unique]），因为 [presheaf_char_unique] 需要一个 [IsPullback] 并且该参数的两个宇宙读数不可互换——具体来说：在该参数上将部分 (I) 的 [IsPullback] 提供给 [presheaf_char_unique] 会因为宇宙不一致而被拒绝，该参数的两个读数明显不同的字段是 [ump]，它对环境类别的对象和同型进行量化。Structure/SubobjectClassifier.v 的两个往返在最小化读取下也被提供（[fun_char_roundtrip]，[fun_pullback_roundtrip]），该文件自身常量的 [:=] 都包括在内，它们在各自的语句中都明确命名 [Fun_HasPullbacks Sets_HasPullbacks] —— 这是一个普通的 [Definition]，而不是 [Instance]，因此不会被静默解析。

 为什么有三个文件。Theory/Sieve.v 是 LEAN（闭包16，是 Theory/Sheaf.v 的18和 Construction/Localization.v 的23 的子集，因此之后任意一个文件都可以零模块成本地重用它；这里都没有重新连接）。Instance/Fun/Pullback.v 是一个一般的 [C, D] 结果，完全没有 [Sets]。在这个文件中是 [Sets] 值的汇编，它也是 [Functor/Hom.v] 的 [Curried_CoHom] 和 Instance/Fun/Morphisms.v 的单态特征进入的地方，这些都不在精简闭包中。宇宙，通过对绑定器和区块的所有 115 个常量进行测量。[Fun_Classifier@{u u0 u1}] 位于 [C : Category@{u1 u u}] 之上，并且 [Untruncate@{u}]——C 的同宇宙、C 的证明宇宙以及 [Sets] 的承载者宇宙都是单层的 [u]，并且该识别完全位于绑定器中：其约束区块根本不包含方程，只有边界（[Set < u]、[u < u0]、[u1 <= u] 以及标准库边界），而 [Fun_Classifier_small@{co o so OO HH u u0}] 也没有承载（其区块没有向第 (I) 节声明的四个约束 [Set < o]、[o < so]、[so <= OO] 和 [OO <= HH] 添加任何方程；其余是边界——八个将所声明的层彼此关联以及与常量自身的 [u] 关联，还有标准库的边界）。单独读取区块不会报告识别，这是错误的。在这115个中，有二十个确实包含一个块方程，而且它是不同的。十四个——Section Char 的 [Efmap_resp]、[Efmap_comp]、[Efmap_id]、[theta_natural]、[in_image]、[char_sieve]、[char_at]、[char_nat]、[char_square] 及它们的五个 [Program] 义务——包含 [u1 = u2]，用于识别两个预层 E 和 U 的 [Sets] 宇宙：该 section 在单独的上下文行上绑定 E 和 U，因此每个都有自己的 [Sets] 实例，而 [Context (theta : U ⟹ E)]——一个位于函子之间的变换到一个 [Sets]——将它们等同，这是通过释放赋予 section 的每个常数的一个方程，[Efmap_resp] 包含在内，尽管它自己的类型从未提到 U 或 theta；在一个在单独行上绑定 E 和 U 的 section 中，相同的主体但没有 theta 不包含任何方程（从树外测量，而非固定）。标识位置由绑定形状决定，而不是由 theta 决定：部分回撤在其上下文中有相同的 [theta]，但在一行上绑定 [{E U : C^op ⟶ Sets}]，因此其常量在 BINDER 中共享等级，并且完全不包含块方程，包括 [presheaf_char_pullback]。三——Section Unique 的 [char_sub_h]、[h_sub_char] 和 [presheaf_char_unique]——也在一行上绑定 [{E U}]，它们的 [u1 = u2] 在相同拼写下是一个不同的标识：[u2] 那里有一个宇宙 [Sieve_Presheaf] 通过 [Context (h : E ⟹ Sieve_Presheaf C)] 引入，它限制了它（[u0 < u2]）而不识别它，并且方程是 [IsPullback] Context [HP] 的——相同的 Context 不带 [HP] 没有方程，带上它则有这个方程（从树中测量，而不是固定；[HP] 将 E、U 和 [Sieve_Presheaf C] 作为一个函子范畴的对象是一个解释，而不是测量）。其他三个是 section (I) 的 [small_char_sub_h]、[small_h_sub_char] 和 [small_unique]，它们携带来自已声明约束的 [so = u0]（和 [so = u]）。[Sieve_Presheaf] 和 [SieveObj] 都不携带任何东西，Instance/Fun/Pullback.v 中也没有任何东西携带，除了 [Fun] 自己的 [u0 = u2]，而该文件的 24 个中有 17 个携带。115 个中有 63 个携带带有单词边界的 [Set]，总是作为严格的下界 [Set < _]，而从不作为方程。两个 BINDER 的标识是预层范畴的，而不是该文件的，并且每个都由带有探针负号的保护控制，控制在相同的级别被接受：[ch = cp] 有两个独立的捐赠者，[Opposite] 和 [Fun]（第二个在命令中完全没有 [^op] 而被拒绝），而 [@Functor Cu Cu] 和 [@Functor Cu Sets] 被接受，所以 [Functor] 不是捐赠者；并且 [ch = o] 在两种变异中都是 [Fun] 的，其中 [Cv^op]、[Cv^op ⟶ Sets] 和 [Cv ⟶ Sets] 被接受为控制。C 的 OBJECT 宇宙只是有界的 ([u1 <= u])，这是 Awodey 所说的“对于任何小范畴 C”，也是小性的归宿。严格下界 [Set < u] 是通过 [Prop] 值的成员资格本身 ([Prop : Type@{Set+1}]) 引入的——它已经是 Theory/Sieve.v 中的 [SieveObj]，在任何 [Powerset_squash] 之前——并且它是一个边界，从不固定，但它精确排除了那些同构宇宙是字面上 [Set] 的 C。二十一条常量在绑定器中携带 [Set]，并且每一个属于 section (G)——大多数作为 [Sieve@{_ Set}]，其余通过 [_2] 或 [FinSet]——继承自 Instance/Two.v 的 [TwoHom : TwoObj → TwoObj → Set]，而不是在此引入；section (G) 的五十一个头中的其余三十个仅以上述块边界形式携带 [Set]。该问题的“当前状态”在四个方面是陈旧的，每一项都有衡量依据。它指出 [ls Instance/Fun/] “仅包含 [Cartesian.v]”；但在基础提交中，该目录下有七个卫星（Cartesian、Terminal、Closed、Morphisms、Discrete、Group、Action）。它说“甚至没有 [Terminal] 的函子范畴实例”；那是 #339 的 [Functor_Category_Terminal]，Instance/Fun/Terminal.v 甚至包含了专门化的 [Two_Sets_Terminal]。它说缺少逐点单射的表征；那是 #369 的 [presheaf_monic_iff_injective]。并且它说树中唯一的 [SubobjectClassifier] 实例是在 Instance/FinSet/Classifier.v；#402 为 [Sets] 添加了两个条件实例。真正缺失的，而这三个文件提供的，完全是缺少任何筛子（在基础提交 [rg -in 'sieve' -g '*.v'] 上返回两行散文，一行在 Theory/Sheaf.v 中，一行在 Construction/Localization.v 中；如果没有 [-g]，doc/plan 覆盖记录会增加 143 行），任何函子范畴的分类器，以及任何函子范畴的拉回实例。计数及其标准。在全局上下文中关闭的常量：115/115，零行 [Axioms:]，计为条目 [Print Module]，在五个空格缩进处发出（其中包括 [Program]，对 [.glob] 是不可见的义务）；该文件未声明任何记录，因此没有未列出的 [Build_*]。每个都以完全限定方式查询，并且所有 115 个都在 [print-assumptions] 门中，该门为三个文件一起携带 161 个名称。[Defined] 令牌：7 个，其中四个是承重的——通过将每个单独翻转为 [Qed] 并单独编译结果来测量：[sieve_sub_map]、[sieve_subpresheaf]、[sieve_incl] 和 [sieve_cone] 都会停止文件，而 [med_img]、[presheaf_char_pullback] 和 [small_pb] 编译为 [Qed]，仅因为它们生成数据而保留 [Defined]。由 [:= eq_refl] 关闭的语句：14 个。及物
 项目内闭包（不包括此文件）：105 个模块，包含单项边际
 Instance/Fun/Terminal 29，Instance/Sets/Classifier/OneLevel
 14，以及 Theory/Sieve, Structure/SubobjectClassifier/Natural,
 Instance/Fun/Morphisms 和 Instance/Fun/Pullback 每个 1；其他所有
 Require 成本为 0，包括 Instance/FinSet，这就是 [MacOmega] 可以
 在这里而不是在探针中存在的原因。OneLevel 的 14
 是与 #402 假设的身份成本，并且是故意支付的：重新声明
 [Untruncate] 在本地会分叉假设，这正是消耗它的意义所在。此文件贡献了零 [make todo] 命中;
 其探针包含反驳命令。未交付。没有无条件无公理的实例，也没有不可能定理（上述三部分披露）。没有证明 [Untruncate] 是必需的，也没有 [DecImage] 变体。没有 [@SubobjectClassifier ([_2, FinSet]） _] 实例：[MacOmega] 已构建并计算，但该实例需要形状 [_2] 的单一表征的逆和一个三向特性映射，而这两者都未构建。TwoX 上的筛与 [Fin.t 3] 之间没有双射，没有 [IEM] —— [twoX_code] 仅由它定义。[Fun_IsPullback] 没有逆（Instance/Fun/Pullback.v 自己的未交付）。[C, D] 没有推挤、等值化器或完备性。对于任何预层范畴都没有 [ElementaryTopos]，也没有指数：Instance/Fun/Closed.v 否定了笛卡尔闭包的继承，并且其正面部分在这里没有尝试。自然性是实现的，但仅在第二次阅读时：[Sub_classifier_natural] 被测量为可以在 [[C^op, Sets] 的抽象分类器上形成，但在 [Fun_Classifier] 被拒绝——与 [classifier_classifies] 是同一对——而在 [Fun_Classifier_small] 上它适用，并作为 [fun_sub_classifier_natural] 与 [fun_Sub_Representable] 一起发布。因此，[Fun_Classifier] 本身没有自然性声明。没有 Grothendieck 拓扑，没有覆盖，也没有层的阅读；Theory/Sheaf.v 和 Construction/Localization.v 没有重新连接，只在本文中以文字形式被指出。没有在具有下界集合构造的偏序集上比较 [Sieve_Presheaf]。从可表示对象的子对象回到筛子的任何通路：[sieve_subobject] 仅单向运行，因此 Awodey 的“作为可表示对象的子对象”被呈现为筛子的嵌入，而不是将两者概念识别为相同——在 [sieve_incl] / [sieve_incl_Monic] / [sieve_subobject] 链之外没有任何东西使用它，唯一性条款取而代之的是子预层及其锥（如上账本所示）。没有在任何强度上比较 [Fun_Classifier] 与 [Fun_Classifier_small]：它们是同一构造的两个宇宙读取，并没有方程式将它们联系起来。在此文件中，没有任何东西被注册为 [Instance]：所需的集合体 [sieve_sub_obj] 是内联记录字面量，三文件唯一注册的实例是 Theory/Sieve.v 中的 [Sieve_Setoid]。
*)

#[local] Obligation Tactic := idtac.

(* ---------------- (A) the truth transformation ---------------- / ---------------- (A) 真理变换 ---------------- *)

Program Definition sieve_truth (C : Category) :
  @terminal_obj ([C^op, Sets]) (Functor_Category_Terminal Sets_Terminal)
    ⟹ Sieve_Presheaf C := {|
  transform := fun c => {| morphism := fun _ => @total_sieve C c |}
|}.
Next Obligation.
  intros C c; unfold Proper, respectful; intros u v _ d g; simpl.
  split; auto.
Qed.
Next Obligation. intros C x y f u d k; simpl; split; auto. Qed.
Next Obligation. intros C x y f u d k; simpl; split; auto. Qed.

Example sieve_truth_at (C : Category) (c : C)
  (u : carrier (fobj[@terminal_obj ([C^op, Sets])
                       (Functor_Category_Terminal Sets_Terminal)] c)) :
  transform[sieve_truth C] c u = @total_sieve C c := eq_refl.

(* ---------------- (B) the characteristic transformation ------- / ---------------- (B) 特征变换 ------- *)

Section Char.

Context {C : Category}.
Context {E : C^op ⟶ Sets}.
Context {U : C^op ⟶ Sets}.
Context (theta : U ⟹ E).

Definition Efmap_resp {c d : C} (f g : d ~{C}~> c) (Hfg : f ≈ g)
      (e : carrier (fobj[E] c)) : fmap[E] f e ≈ fmap[E] g e
  := @fmap_respects (C^op) Sets E c d f g Hfg e.

Definition Efmap_comp {c d d' : C} (f : d ~{C}~> c) (g : d' ~{C}~> d)
      (x : carrier (fobj[E] c)) :
  fmap[E] (f ∘ g) x ≈ fmap[E] g (fmap[E] f x)
  := @fmap_comp (C^op) Sets E c d d' g f x.

Definition Efmap_id {c : C} (x : carrier (fobj[E] c)) :
  fmap[E] (@id C c) x ≈ x
  := @fmap_id (C^op) Sets E c x.

Definition theta_natural {c d : C} (f : d ~{C}~> c)
    (x : carrier (fobj[U] c)) :
  fmap[E] f (transform[theta] c x) ≈ transform[theta] d (fmap[U] f x)
  := @naturality (C^op) Sets U E theta c d f x.

Definition in_image (d : C) (y : carrier (fobj[E] d)) : Type :=
  ∃ x : carrier (fobj[U] d), transform[theta] d x ≈ y.

Program Definition char_sieve (c : C) (e : carrier (fobj[E] c)) :
  @Sieve C c := {|
  sieve_mem := fun d (f : d ~{C}~> c) =>
                 Powerset_squash (in_image d (fmap[E] f e))
|}.
Next Obligation.
  intros c e d f g Hfg Hmem Q k.
  apply Hmem; intros [x Hx]; apply k; exists x.
  transitivity (fmap[E] f e); [ exact Hx | exact (Efmap_resp f g Hfg e) ].
Qed.
Next Obligation.
  intros c e d d' f g Hmem Q k.
  apply Hmem; intros [x Hx]; apply k.
  exists (fmap[U] g x).
  transitivity (fmap[E] g (transform[theta] d x)).
  - symmetry; exact (theta_natural g x).
  - transitivity (fmap[E] g (fmap[E] f e)).
    + exact (proper_morphism (fmap[E] g) _ _ Hx).
    + symmetry; exact (Efmap_comp f g e).
Qed.

Program Definition char_at (c : C) :
  fobj[E] c ~{Sets}~> @SieveObj C c := {|
  morphism := char_sieve c
|}.
Next Obligation.
  intros c.
  unfold Proper, respectful; intros e e' Hee' d f; simpl.
  split; intros Hmem Q k; apply Hmem; intros [x Hx]; apply k; exists x.
  - transitivity (fmap[E] f e); [ exact Hx | ].
    exact (proper_morphism (fmap[E] f) _ _ Hee').
  - transitivity (fmap[E] f e'); [ exact Hx | ].
    symmetry; exact (proper_morphism (fmap[E] f) _ _ Hee').
Qed.

Program Definition char_nat : E ⟹ Sieve_Presheaf C := {|
  transform := char_at
|}.
Next Obligation.
  intros x y h e d g; simpl.
  pose proof (@Efmap_comp x y d h g e) as Hc.
  split; intros Hmem Q k; apply Hmem; intros [a Ha]; apply k; exists a;
    rewrite Ha; [ exact Hc | symmetry; exact Hc ].
Qed.
Next Obligation.
  intros x y h e d g; simpl.
  pose proof (@Efmap_comp x y d h g e) as Hc.
  split; intros Hmem Q k; apply Hmem; intros [a Ha]; apply k; exists a;
    rewrite Ha; [ symmetry; exact Hc | exact Hc ].
Qed.

(* the square commutes, with no hypothesis at all / 这个平方是交换的，完全没有假设 *)
Theorem char_square :
  char_nat ∘[[C^op, Sets]] theta
    ≈ sieve_truth C ∘[[C^op, Sets]]
        @one ([C^op, Sets]) (Functor_Category_Terminal Sets_Terminal) U.
Proof.
  intros c x d f; simpl.
  split; intro Hm; [ exact I | ].
  intros Q k; apply k.
  exists (fmap[U] f x).
  symmetry; exact (theta_natural f x).
Qed.

End Char.

(* ---------------- (C) a sieve as a subobject of y(c) ---------- / ---------------- (C) 作为 y(c) 的子对象的筛子 ---------- *)

Section SieveSub.

Context {C : Category}.

Lemma sieve_sub_eq (c : C) (S : Sieve c) (k : C) :
  Equivalence (fun u v : { g : k ~{C}~> c & sieve_mem S g } =>
                 projT1 u ≈ projT1 v).
Proof.
  constructor; repeat intro.
  - reflexivity.
  - now symmetry.
  - etransitivity; eassumption.
Qed.

Definition sieve_sub_obj (c : C) (S : Sieve c) (k : C) : SetoidObject :=
  {| carrier := { g : k ~{C}~> c & sieve_mem S g }
   ; is_setoid := {| equiv := fun u v => projT1 u ≈ projT1 v
                   ; setoid_equiv := sieve_sub_eq c S k |} |}.

Definition sieve_sub_map (c : C) (S : Sieve c) (k j : C) (h : j ~{C}~> k) :
  sieve_sub_obj c S k ~{Sets}~> sieve_sub_obj c S j.
Proof.
  unshelve refine {| morphism := fun u => existT _ (projT1 u ∘ h) _ |}.
  - exact (sieve_closed S (projT1 u) h (projT2 u)).
  - intros u v Huv; simpl in *. now rewrite Huv.
Defined.

Definition sieve_subpresheaf (c : C) (S : Sieve c) : C^op ⟶ Sets.
Proof.
  unshelve refine (@Build_Functor (C^op) Sets (sieve_sub_obj c S)
                     (fun k j (h : k ~{C^op}~> j) => sieve_sub_map c S k j h)
                     _ _ _).
  - intros k j h1 h2 Hh u; simpl. now rewrite Hh.
  - intros k u; simpl. apply id_right.
  - intros k j l h1 h2 u; simpl. apply comp_assoc.
Defined.

Definition sieve_incl (c : C) (S : Sieve c) :
  sieve_subpresheaf c S ~{[C^op, Sets]}~> Curried_CoHom C c.
Proof.
  unshelve refine (@Build_Transform' (C^op) Sets (sieve_subpresheaf c S)
                     (Curried_CoHom C c) (fun k => _) _).
  - unshelve refine {| morphism := fun u => projT1 u |}.
    intros u v Huv; exact Huv.
  - intros k j h u; simpl. reflexivity.
Defined.

Definition sieve_incl_Monic (c : C) (S : Sieve c) :
  @Monic ([C^op, Sets]) _ _ (sieve_incl c S) :=
  snd (presheaf_monic_iff_injective (sieve_incl c S))
      (fun k a b Hab => Hab).

Definition sieve_subobject (c : C) (S : Sieve c) :
  @SubObj ([C^op, Sets]) (Curried_CoHom C c) :=
  @Build_SubObj ([C^op, Sets]) (Curried_CoHom C c)
    (sieve_subpresheaf c S) (sieve_incl c S) (sieve_incl_Monic c S).

(* the cone into E determined by an element of E c / 由 E c 中的一个元素确定的 E 中的锥体 *)
Definition sieve_cone {E : C^op ⟶ Sets} (c : C) (e : carrier (fobj[E] c))
  (S : Sieve c) : sieve_subpresheaf c S ~{[C^op, Sets]}~> E.
Proof.
  unshelve refine (@Build_Transform' (C^op) Sets (sieve_subpresheaf c S) E
                     (fun k => _) _).
  - unshelve refine {| morphism := fun u => fmap[E] (projT1 u) e |}.
    intros u v Huv; simpl in *.
    exact (@fmap_respects _ _ E c k (projT1 u) (projT1 v) Huv e).
  - intros k j h u; simpl. symmetry.
    exact (@fmap_comp _ _ E c k j h (projT1 u) e).
Defined.

End SieveSub.

(* ---------------- (D) uniqueness of the classifying map ------- / ----------------（D）分类映射的唯一性------- *)

Section Unique.

Context {C : Category}.
Context {E U : C^op ⟶ Sets}.
Context (theta : U ⟹ E).
Context (h : E ⟹ Sieve_Presheaf C).
Context (HP : @IsPullback ([C^op, Sets]) E
                (@terminal_obj _ (Functor_Category_Terminal Sets_Terminal))
                (Sieve_Presheaf C) h (sieve_truth C) U theta
                (@one _ (Functor_Category_Terminal Sets_Terminal) U)).

Lemma char_sub_h (c : C) (e : carrier (fobj[E] c)) (d : C) (f : d ~{C}~> c) :
  sieve_mem (char_sieve theta c e) f -> sieve_mem (transform[h] c e) f.
Proof.
  intro Hf. apply Hf. intros [x Hx].
  pose proof (is_pullback_commutes HP d x) as Hc; simpl in Hc.
  assert (Hid : sieve_mem (transform[h] d (fmap[E] f e)) (@id C d)).
  { assert (Heq : transform[h] d (transform[theta] d x)
                    ≈ transform[h] d (fmap[E] f e))
      by (apply proper_morphism; exact Hx).
    apply (proj1 (Heq d (@id C d))).
    exact (proj2 (Hc d (@id C d)) I). }
  pose proof (@naturality _ _ _ _ h c d f e) as Hn; simpl in Hn.
  pose proof (proj2 (Hn d (@id C d)) Hid) as Hm2; simpl in Hm2.
  eapply sieve_respects; [ | exact Hm2 ]. apply id_right.
Qed.

Lemma h_sub_char (c : C) (e : carrier (fobj[E] c)) (d : C) (f : d ~{C}~> c) :
  sieve_mem (transform[h] c e) f -> sieve_mem (char_sieve theta c e) f.
Proof.
  intro Hf.
  set (ed := fmap[E] f e).
  set (S := transform[h] d ed).
  assert (HidS : sieve_mem S (@id C d)).
  { unfold S, ed.
    pose proof (@naturality _ _ _ _ h c d f e) as Hn; simpl in Hn.
    apply (proj1 (Hn d (@id C d))). simpl.
    eapply sieve_respects; [ | exact Hf ]. symmetry. apply id_right. }
  set (q1 := @sieve_cone C E d ed S).
  assert (Hcone : ∀ (k : C) (u : carrier (sieve_sub_obj d S k)),
            sieve_equiv (transform[h] k (transform[q1] k u)) (total_sieve k)).
  { intros k u j g. split; intro; [ exact I | ].
    unfold q1, sieve_cone; simpl.
    pose proof (@naturality _ _ _ _ h d k (projT1 u) ed) as Hn; simpl in Hn.
    apply (proj1 (Hn j g)). simpl.
    exact (sieve_closed S (projT1 u) g (projT2 u)). }
  assert (Hsq : h ∘[[C^op, Sets]] q1
                  ≈ sieve_truth C ∘[[C^op, Sets]]
                      @one ([C^op, Sets])
                        (Functor_Category_Terminal Sets_Terminal)
                        (sieve_subpresheaf d S))
    by (intros k u j g; exact (Hcone k u j g)).
  pose proof (is_pullback_ump HP (sieve_subpresheaf d S) q1
                (@one _ (Functor_Category_Terminal Sets_Terminal) _) Hsq)
    as UM.
  destruct (unique_property UM) as [Hu1 Hu2].
  intros P kk. apply kk.
  exists (transform[unique_obj UM] d (existT _ (@id C d) HidS)).
  pose proof (Hu1 d (existT _ (@id C d) HidS)) as Hval; simpl in Hval.
  rewrite Hval. exact (@fmap_id _ _ E d ed).
Qed.

Theorem presheaf_char_unique : h ≈ char_nat theta.
Proof.
  intros c e d f; split; [ apply h_sub_char | apply char_sub_h ].
Qed.

End Unique.

(* ---------------- (E) the classifying square is a pullback ---- / ----------------（E）分类方格是一个拉回---- *)

Section Pullback.

Context {C : Category}.
Context (UT : Untruncate).
Context {E U : C^op ⟶ Sets}.
Context (theta : U ⟹ E).
Context (M : @Monic ([C^op, Sets]) U E theta).

Definition theta_inj : ∀ (c : C^op) (a b : carrier (fobj[U] c)),
    transform[theta] c a ≈ transform[theta] c b -> a ≈ b
  := fst (presheaf_monic_iff_injective theta) M.

Definition med_img {Q : C^op ⟶ Sets} (q1 : Q ⟹ E)
  (Hq : ∀ (c : C) (z : carrier (fobj[Q] c)),
          sieve_mem (char_sieve theta c (transform[q1] c z)) (@id C c))
  (c : C) (z : carrier (fobj[Q] c)) : in_image theta c (transform[q1] c z).
Proof.
  pose proof (UT _ (Hq c z)) as Hx.
  destruct Hx as [x Hx].
  exists x.
  transitivity (fmap[E] (@id C c) (transform[q1] c z)); [ exact Hx | ].
  exact (Efmap_id (E:=E) (transform[q1] c z)).
Defined.

Definition med_elt {Q : C^op ⟶ Sets} (q1 : Q ⟹ E)
  (Hq : ∀ (c : C) (z : carrier (fobj[Q] c)),
          sieve_mem (char_sieve theta c (transform[q1] c z)) (@id C c))
  (c : C) (z : carrier (fobj[Q] c)) : carrier (fobj[U] c) :=
  projT1 (med_img q1 Hq c z).

Definition med_spec {Q : C^op ⟶ Sets} (q1 : Q ⟹ E)
  (Hq : ∀ (c : C) (z : carrier (fobj[Q] c)),
          sieve_mem (char_sieve theta c (transform[q1] c z)) (@id C c))
  (c : C) (z : carrier (fobj[Q] c)) :
  transform[theta] c (med_elt q1 Hq c z) ≈ transform[q1] c z :=
  projT2 (med_img q1 Hq c z).

Program Definition char_med {Q : C^op ⟶ Sets} (q1 : Q ⟹ E)
  (Hq : ∀ (c : C) (z : carrier (fobj[Q] c)),
          sieve_mem (char_sieve theta c (transform[q1] c z)) (@id C c)) :
  Q ⟹ U := {|
  transform := fun c => {| morphism := fun z => med_elt q1 Hq c z |}
|}.
Next Obligation.
  intros Q q1 Hq c.
  unfold Proper, respectful; intros z z' Hzz'.
  apply (theta_inj c).
  transitivity (transform[q1] c z); [ exact (med_spec q1 Hq c z) | ].
  transitivity (transform[q1] c z').
  - exact (proper_morphism (transform[q1] c) _ _ Hzz').
  - symmetry; exact (med_spec q1 Hq c z').
Qed.
Next Obligation.
  intros Q q1 Hq x y f z; simpl.
  apply (theta_inj y).
  transitivity (fmap[E] f (transform[theta] x (med_elt q1 Hq x z))).
  - symmetry; exact (theta_natural theta f (med_elt q1 Hq x z)).
  - transitivity (fmap[E] f (transform[q1] x z)).
    + exact (proper_morphism (fmap[E] f) _ _ (med_spec q1 Hq x z)).
    + transitivity (transform[q1] y (fmap[Q] f z)).
      * exact (@naturality (C^op) Sets Q E q1 x y f z).
      * symmetry; exact (med_spec q1 Hq y (fmap[Q] f z)).
Qed.
Next Obligation.
  intros Q q1 Hq x y f z; simpl.
  symmetry.
  apply (theta_inj y).
  transitivity (fmap[E] f (transform[theta] x (med_elt q1 Hq x z))).
  - symmetry; exact (theta_natural theta f (med_elt q1 Hq x z)).
  - transitivity (fmap[E] f (transform[q1] x z)).
    + exact (proper_morphism (fmap[E] f) _ _ (med_spec q1 Hq x z)).
    + transitivity (transform[q1] y (fmap[Q] f z)).
      * exact (@naturality (C^op) Sets Q E q1 x y f z).
      * symmetry; exact (med_spec q1 Hq y (fmap[Q] f z)).
Qed.

Definition presheaf_char_pullback :
  @IsPullback ([C^op, Sets]) E
    (@terminal_obj _ (Functor_Category_Terminal Sets_Terminal))
    (Sieve_Presheaf C) (char_nat theta) (sieve_truth C) U theta
    (@one _ (Functor_Category_Terminal Sets_Terminal) U).
Proof.
  constructor.
  - exact (char_square theta).
  - intros Q q1 q2 Hcomm.
    assert (Hq : ∀ (c : C) (z : carrier (fobj[Q] c)),
               sieve_mem (char_sieve theta c (transform[q1] c z)) (@id C c)).
    { intros c z. exact (proj2 (Hcomm c z c (@id C c)) I). }
    unshelve refine {| unique_obj := char_med q1 Hq |}.
    + split.
      * intros c z; simpl. exact (med_spec q1 Hq c z).
      * intros c z; simpl. destruct (transform[q2] c z); reflexivity.
    + intros v [Hv1 Hv2] c z; simpl.
      apply (theta_inj c).
      transitivity (transform[q1] c z); [ exact (med_spec q1 Hq c z) | ].
      symmetry; exact (Hv1 c z).
Defined.

End Pullback.

(* ---------------- (F) the classifier ---------------- / ----------------（F）分类词 ---------------- *)

Definition Fun_Classifier {C : Category} (UT : Untruncate) :
  @SubobjectClassifier ([C^op, Sets])
    (Functor_Category_Terminal Sets_Terminal) :=
  @Build_SubobjectClassifier ([C^op, Sets])
    (Functor_Category_Terminal Sets_Terminal)
    (Sieve_Presheaf C)
    (sieve_truth C)
    (fun U E theta M => char_nat theta)
    (fun U E theta M => presheaf_char_pullback UT theta M)
    (fun U E theta M h HP => presheaf_char_unique theta h HP).

Definition Fun_Classifier_IEM {C : Category} (Em : IEM) :
  @SubobjectClassifier ([C^op, Sets])
    (Functor_Category_Terminal Sets_Terminal) :=
  Fun_Classifier (untruncate_of_IEM Em).

Definition Fun_Classifier_cov {D : Category} (UT : Untruncate) :
  @SubobjectClassifier ([D, Sets])
    (Functor_Category_Terminal Sets_Terminal) :=
  @Fun_Classifier (D^op) UT.

Example fun_classifier_omega {C : Category} (UT : Untruncate) :
  @Ω ([C^op, Sets]) _ (Fun_Classifier UT) = Sieve_Presheaf C := eq_refl.
Example fun_classifier_truth {C : Category} (UT : Untruncate) :
  @truth ([C^op, Sets]) _ (Fun_Classifier UT) = sieve_truth C := eq_refl.
Example fun_classifier_char {C : Category} (UT : Untruncate)
  {U E : C^op ⟶ Sets} (theta : U ⟹ E) (M : @Monic ([C^op, Sets]) U E theta) :
  @char ([C^op, Sets]) _ (Fun_Classifier UT) U E theta M = char_nat theta
  := eq_refl.

(* ---------------- (G) the arrow shape ---------------- / ---------------- (G) 箭头形 ---------------- *)

Example op_op_two : (_2^op)^op = _2 := eq_refl.
Check (Sieve_Presheaf (_2^op) : _2 ⟶ Sets).

Definition twoX_pred (P Q : Prop) :
  ∀ (d : _2^op), (d ~{_2^op}~> TwoX) → Prop :=
  fun d => match d with TwoX => fun _ => P | TwoY => fun _ => Q end.

Program Definition twoX_sieve (P Q : Prop) (H : P -> Q) :
  @Sieve (_2^op) TwoX := {| sieve_mem := twoX_pred P Q |}.
Next Obligation. intros P Q H d f g Hfg Hmem; destruct d; exact Hmem. Qed.
Next Obligation.
  intros P Q H d e f g Hmem.
  destruct d, e; simpl in *;
    try solve [ destruct (TwoHom_Y_X_absurd f) ];
    try solve [ destruct (TwoHom_Y_X_absurd g) ];
    auto.
Qed.

Definition twoX_total : @Sieve (_2^op) TwoX :=
  twoX_sieve True True (fun x => x).
Definition twoX_mid : @Sieve (_2^op) TwoX :=
  twoX_sieve False True (fun x => match x return True with end).
Definition twoX_empty : @Sieve (_2^op) TwoX :=
  twoX_sieve False False (fun x => x).

Definition twoY_pred (R : Prop) :
  ∀ (d : _2^op), (d ~{_2^op}~> TwoY) → Prop :=
  fun d => match d with TwoY => fun _ => R | TwoX => fun _ => True end.

Program Definition twoY_sieve (R : Prop) : @Sieve (_2^op) TwoY :=
  {| sieve_mem := twoY_pred R |}.
Next Obligation. intros R d f g Hfg Hmem; destruct d; exact Hmem. Qed.
Next Obligation.
  intros R d e f g Hmem.
  destruct d, e; simpl in *;
    try solve [ destruct (TwoHom_Y_X_absurd f) ];
    try solve [ destruct (TwoHom_Y_X_absurd g) ];
    auto.
Qed.

Definition twoY_total : @Sieve (_2^op) TwoY := twoY_sieve True.
Definition twoY_empty : @Sieve (_2^op) TwoY := twoY_sieve False.

Theorem twoX_total_neq_mid : twoX_total ≈ twoX_mid -> False.
Proof. intro H. exact (proj1 (H TwoX TwoIdX) I). Qed.
Theorem twoX_mid_neq_empty : twoX_mid ≈ twoX_empty -> False.
Proof. intro H. exact (proj1 (H TwoY TwoXY) I). Qed.
Theorem twoX_total_neq_empty : twoX_total ≈ twoX_empty -> False.
Proof. intro H. exact (proj1 (H TwoX TwoIdX) I). Qed.
Theorem twoY_total_neq_empty : twoY_total ≈ twoY_empty -> False.
Proof. intro H. exact (proj1 (H TwoY TwoIdY) I). Qed.

Theorem twoX_sieve_normal (S : @Sieve (_2^op) TwoX) :
  S ≈ twoX_sieve (sieve_mem S TwoIdX) (sieve_mem S TwoXY)
        (fun p => sieve_closed S TwoIdX TwoXY p).
Proof.
  intros d f; destruct d;
    [ pose proof (TwoHom_inv TwoX TwoX f) as Hf
    | pose proof (TwoHom_inv TwoX TwoY f) as Hf ];
    simpl in Hf; subst; simpl; split; auto.
Qed.

Theorem twoY_sieve_normal (S : @Sieve (_2^op) TwoY) :
  S ≈ twoY_sieve (sieve_mem S TwoIdY).
Proof.
  intros d f; destruct d;
    [ destruct (TwoHom_Y_X_absurd f)
    | pose proof (TwoHom_inv TwoY TwoY f) as Hf ];
    simpl in *; subst; simpl; split; auto.
Qed.

Definition jmap :
  @SieveObj (_2^op) TwoX ~{Sets}~> @SieveObj (_2^op) TwoY :=
  @fmap (_2^op^op) Sets (Sieve_Presheaf (_2^op)) TwoX TwoY TwoXY.

Theorem j_total : jmap twoX_total ≈ twoY_total.
Proof.
  intros d f; destruct d;
    [ destruct (TwoHom_Y_X_absurd f) | ]; simpl; split; auto.
Qed.
Theorem j_mid : jmap twoX_mid ≈ twoY_total.
Proof.
  intros d f; destruct d;
    [ destruct (TwoHom_Y_X_absurd f) | ]; simpl; split; auto.
Qed.
Theorem j_empty : jmap twoX_empty ≈ twoY_empty.
Proof.
  intros d f; destruct d;
    [ destruct (TwoHom_Y_X_absurd f) | ]; simpl; split; auto.
Qed.

Theorem j_identifies : jmap twoX_total ≈ jmap twoX_mid.
Proof. transitivity twoY_total; [ apply j_total | symmetry; apply j_mid ]. Qed.

Theorem j_separates : jmap twoX_total ≈ jmap twoX_empty -> False.
Proof.
  intro H. apply twoY_total_neq_empty.
  transitivity (jmap twoX_total); [ symmetry; apply j_total | ].
  transitivity (jmap twoX_empty); [ exact H | apply j_empty ].
Qed.

Theorem twoX_sieve_ext (P Q : Prop) (H : P -> Q) (P' Q' : Prop) (H' : P' -> Q')
        (HP : P <-> P') (HQ : Q <-> Q') :
  twoX_sieve P Q H ≈ twoX_sieve P' Q' H'.
Proof. intros d f; destruct d; simpl; assumption. Qed.

Theorem twoY_sieve_ext (R R' : Prop) (HR : R <-> R') :
  twoY_sieve R ≈ twoY_sieve R'.
Proof. intros d f; destruct d; simpl; [ split; auto | assumption ]. Qed.

Theorem twoX_three_sieves (Em : IEM) (S : @Sieve (_2^op) TwoX) :
  (S ≈ twoX_total) + (S ≈ twoX_mid) + (S ≈ twoX_empty).
Proof.
  pose proof (twoX_sieve_normal S) as HN.
  destruct (Em (sieve_mem S TwoIdX)) as [Hp | Hp].
  - left; left. rewrite HN. apply twoX_sieve_ext.
    + split; [ exact (fun _ => I) | exact (fun _ => Hp) ].
    + split; [ exact (fun _ => I)
             | exact (fun _ => sieve_closed S TwoIdX TwoXY Hp) ].
  - destruct (Em (sieve_mem S TwoXY)) as [Hq | Hq].
    + left; right. rewrite HN. apply twoX_sieve_ext.
      * split; [ exact Hp | intro C0; destruct C0 ].
      * split; [ exact (fun _ => I) | exact (fun _ => Hq) ].
    + right. rewrite HN. apply twoX_sieve_ext.
      * split; [ exact Hp | intro C0; destruct C0 ].
      * split; [ exact Hq | intro C0; destruct C0 ].
Qed.

Theorem twoY_two_sieves (Em : IEM) (S : @Sieve (_2^op) TwoY) :
  (S ≈ twoY_total) + (S ≈ twoY_empty).
Proof.
  pose proof (twoY_sieve_normal S) as HN.
  destruct (Em (sieve_mem S TwoIdY)) as [Hp | Hp].
  - left. rewrite HN. apply twoY_sieve_ext.
    split; [ exact (fun _ => I) | exact (fun _ => Hp) ].
  - right. rewrite HN. apply twoY_sieve_ext.
    split; [ exact Hp | intro C0; destruct C0 ].
Qed.

Theorem total_is_twoX_total : @total_sieve (_2^op) TwoX ≈ twoX_total.
Proof. intros d f; destruct d; split; intro; exact I. Qed.

Theorem total_is_twoY_total : @total_sieve (_2^op) TwoY ≈ twoY_total.
Proof. intros d f; destruct d; split; intro; exact I. Qed.

(* --- Mac Lane's explicit j : {0,1,2} -> {0,2} --- / --- 马克·莱恩的显式 j : {0,1,2} -> {0,2} --- *)

Definition macj : Fin.t 3 -> Fin.t 2 :=
  fun k => match k with
           | Fin.F1 => Fin.F1
           | Fin.FS k' => match k' with
                          | Fin.F1 => Fin.F1
                          | Fin.FS _ => Fin.FS Fin.F1
                          end
           end.

Example macj_0 : macj Fin.F1 = Fin.F1 := eq_refl.
Example macj_1 : macj (Fin.FS Fin.F1) = Fin.F1 := eq_refl.
Example macj_2 : macj (Fin.FS (Fin.FS Fin.F1)) = Fin.FS Fin.F1 := eq_refl.

Definition twoX_code (Em : IEM) (S : @Sieve (_2^op) TwoX) : Fin.t 3 :=
  match Em (sieve_mem S TwoIdX) with
  | inl _ => Fin.F1
  | inr _ => match Em (sieve_mem S TwoXY) with
             | inl _ => Fin.FS Fin.F1
             | inr _ => Fin.FS (Fin.FS Fin.F1)
             end
  end.

Definition twoY_code (Em : IEM) (S : @Sieve (_2^op) TwoY) : Fin.t 2 :=
  match Em (sieve_mem S TwoIdY) with
  | inl _ => Fin.F1
  | inr _ => Fin.FS Fin.F1
  end.

Lemma twoX_code_total (Em : IEM) : twoX_code Em twoX_total = Fin.F1.
Proof.
  unfold twoX_code; destruct (Em (sieve_mem twoX_total TwoIdX)) as [|N];
    [ reflexivity | destruct (N I) ].
Qed.

Lemma twoX_code_mid (Em : IEM) : twoX_code Em twoX_mid = Fin.FS Fin.F1.
Proof.
  unfold twoX_code; destruct (Em (sieve_mem twoX_mid TwoIdX)) as [Hp|N];
    [ destruct Hp | ].
  destruct (Em (sieve_mem twoX_mid TwoXY)) as [|N2];
    [ reflexivity | destruct (N2 I) ].
Qed.

Lemma twoX_code_empty (Em : IEM) :
  twoX_code Em twoX_empty = Fin.FS (Fin.FS Fin.F1).
Proof.
  unfold twoX_code; destruct (Em (sieve_mem twoX_empty TwoIdX)) as [Hp|N];
    [ destruct Hp | ].
  destruct (Em (sieve_mem twoX_empty TwoXY)) as [Hq|];
    [ destruct Hq | reflexivity ].
Qed.

Lemma twoY_code_total (Em : IEM) : twoY_code Em twoY_total = Fin.F1.
Proof.
  unfold twoY_code; destruct (Em (sieve_mem twoY_total TwoIdY)) as [|N];
    [ reflexivity | destruct (N I) ].
Qed.

Lemma twoY_code_empty (Em : IEM) : twoY_code Em twoY_empty = Fin.FS Fin.F1.
Proof.
  unfold twoY_code; destruct (Em (sieve_mem twoY_empty TwoIdY)) as [Hp|];
    [ destruct Hp | reflexivity ].
Qed.

Example two_op_XY_IdY : (TwoXY ∘[_2^op] TwoIdY) = TwoXY := eq_refl.

Lemma jmap_mem_IdY (S : @Sieve (_2^op) TwoX) :
  sieve_mem (jmap S) TwoIdY <-> sieve_mem S TwoXY.
Proof. unfold jmap; simpl; split; intro H; exact H. Qed.

(*
 Mac Lane's j AS AN OBJECT of [_2, FinSet]: the three-element object
 {0,1,2} at TwoX, the two-element object {0,2} at TwoY, and [macj]
 between them.  [Instance/FinSet] costs this file ZERO extra modules
 (measured), so the explicit construction lives here beside the sieve
 one it is being identified with. 

 --------
 麦克莱恩的 j 作为 [_2, FinSet] 的一个对象：TwoX 上的三元素对象 {0,1,2}，TwoY 上的二元素对象 {0,2}，以及它们之间的 [macj]。[Instance/FinSet] 不额外占用这个文件的任何模块（已测量），所以这个显式构造就放在这里，与它所被识别的筛子构造并列。
*)

Definition macO (o : TwoObj) : nat := match o with TwoX => 3 | TwoY => 2 end.

Definition macF (x y : TwoObj) (f : TwoHom x y) :
  Fin.t (macO x) -> Fin.t (macO y) :=
  match f with
  | TwoIdX => fun k => k
  | TwoIdY => fun k => k
  | TwoXY  => macj
  end.

Lemma macF_respects (a b : TwoObj) :
  Proper (@equiv _ (@homset _2 a b)
            ==> @equiv _ (@homset FinSet (macO a) (macO b))) (macF a b).
Proof.
  intros f g Hfg; simpl in Hfg.
  assert (Heq : f = g) by exact Hfg.
  rewrite Heq; intro k; reflexivity.
Qed.

Lemma macF_id (a : TwoObj) : macF a a (@id _2 a) ≈ @id FinSet (macO a).
Proof. destruct a; intro k; reflexivity. Qed.

Lemma macF_comp (a b c : TwoObj) (f : b ~{_2}~> c) (g : a ~{_2}~> b) :
  macF a c (f ∘[_2] g) ≈ macF b c f ∘[FinSet] macF a b g.
Proof.
  destruct a, b, c;
    try solve [ destruct (TwoHom_Y_X_absurd g) ];
    try solve [ destruct (TwoHom_Y_X_absurd f) ];
    pose proof (TwoHom_inv _ _ f) as Hf;
    pose proof (TwoHom_inv _ _ g) as Hg;
    simpl in Hf, Hg; subst; intro k; reflexivity.
Qed.

Definition MacOmega : _2 ⟶ FinSet :=
  @Build_Functor _2 FinSet macO macF macF_respects macF_id macF_comp.

Example macOmega_X : fobj[MacOmega] TwoX = 3%nat := eq_refl.
Example macOmega_Y : fobj[MacOmega] TwoY = 2%nat := eq_refl.
Example macOmega_fmap : fmap[MacOmega] TwoXY = macj := eq_refl.

(*
 THE IDENTIFICATION.  Under informative excluded middle the sieves on
 TwoX are coded by [Fin.t 3] and those on TwoY by [Fin.t 2], and the
 sieve presheaf's action along the one non-identity arrow IS Mac
 Lane's j — that is, [MacOmega]'s own arrow action, by the [eq_refl]
 above.  So his explicit three-element construction is the general
 sieve answer read through the dictionary, proved rather than
 asserted. 

 --------
 身份识别。在信息排除中间原则下，TwoX 上的筛子编码为 [Fin.t 3]，而 TwoY 上的筛子编码为 [Fin.t 2]，筛子预层沿唯一非恒等箭头的作用是 Mac Lane 的 j —— 即通过上面的 [eq_refl]，[MacOmega] 自己的箭头作用。因此，他明确的三元素构造是通过词典读取的一般筛子答案，得到的是证明而非声称的结果。
*)
Theorem mac_dictionary (Em : IEM) (S : @Sieve (_2^op) TwoX) :
  twoY_code Em (jmap S) = macj (twoX_code Em S).
Proof.
  unfold twoY_code, twoX_code.
  destruct (Em (sieve_mem (jmap S) TwoIdY)) as [Hj | Nj];
  destruct (Em (sieve_mem S TwoIdX)) as [Hx | Nx].
  - reflexivity.
  - destruct (Em (sieve_mem S TwoXY)) as [Hy | Ny]; [ reflexivity | ].
    destruct (Ny (proj1 (jmap_mem_IdY S) Hj)).
  - destruct (Nj (proj2 (jmap_mem_IdY S)
                   (sieve_closed S TwoIdX TwoXY Hx))).
  - destruct (Em (sieve_mem S TwoXY)) as [Hy | Ny].
    + destruct (Nj (proj2 (jmap_mem_IdY S) Hy)).
    + reflexivity.
Qed.

(* ---------------- (H) the two round trips ---------------- / ----------------（H）两次往返---------------- *)

Definition fun_truth_subobject {C : Category} (UT : Untruncate) :
  @SubObj ([C^op, Sets])
    (@Ω ([C^op, Sets]) (Functor_Category_Terminal Sets_Terminal)
       (Fun_Classifier UT)) :=
  @truth_subobject ([C^op, Sets]) (Functor_Category_Terminal Sets_Terminal)
    (Fun_Classifier UT).

Definition fun_char_roundtrip {C : Category} (UT : Untruncate)
  {x : C^op ⟶ Sets}
  (h : x ~{[C^op, Sets]}~> @Ω ([C^op, Sets])
                              (Functor_Category_Terminal Sets_Terminal)
                              (Fun_Classifier UT)) :
  @char ([C^op, Sets]) (Functor_Category_Terminal Sets_Terminal)
    (Fun_Classifier UT) _ _
    (sub_mono (@sub_reindex ([C^op, Sets])
                 (Fun_HasPullbacks Sets_HasPullbacks) _ x h
                 (fun_truth_subobject UT)))
    (sub_is_monic (@sub_reindex ([C^op, Sets])
                 (Fun_HasPullbacks Sets_HasPullbacks) _ x h
                 (fun_truth_subobject UT)))
    ≈ h
  := @classifier_char_roundtrip ([C^op, Sets])
       (Functor_Category_Terminal Sets_Terminal)
       (Fun_HasPullbacks Sets_HasPullbacks) (Fun_Classifier UT) x h.

Definition fun_pullback_roundtrip {C : Category} (UT : Untruncate)
  {x : C^op ⟶ Sets} (s : @SubObj ([C^op, Sets]) x) :
  @sub_reindex ([C^op, Sets]) (Fun_HasPullbacks Sets_HasPullbacks) _ x
    (@char ([C^op, Sets]) (Functor_Category_Terminal Sets_Terminal)
       (Fun_Classifier UT) _ _ (sub_mono s) (sub_is_monic s))
    (fun_truth_subobject UT)
    ≈ s
  := @classifier_pullback_roundtrip ([C^op, Sets])
       (Functor_Category_Terminal Sets_Terminal)
       (Fun_HasPullbacks Sets_HasPullbacks) (Fun_Classifier UT) x s.

(* ------------------------------------------------------------------ *)
(* * ** (I) The classification theorem, at objects <= homs / * **（我）分类定理，在对象 <= Hom *)

Section Small.
Universes co o so OO HH.
Constraint Set < o.
Constraint o < so.
Constraint so <= OO.
Constraint OO <= HH.
Context (Cs : Category@{co o o}).
Context (UTs : Untruncate@{o}).
Definition PShSmall : Category@{OO HH HH} := [Cs^op, Sets@{o so}].
Definition PShSmall_Terminal : @Terminal PShSmall :=
  @Functor_Category_Terminal (Cs^op) Sets@{o so} Sets_Terminal.

Definition small_pb (U E : obj[PShSmall]) (theta : U ~{PShSmall}~> E)
  (M : @Monic PShSmall U E theta) :
  @IsPullback PShSmall E (@terminal_obj PShSmall PShSmall_Terminal)
    (Sieve_Presheaf Cs) (char_nat theta) (sieve_truth Cs) U theta
    (@one PShSmall PShSmall_Terminal U).
Proof using Cs UTs.
  constructor.
  - exact (char_square theta).
  - intros Q q1 q2 Hcomm.
    assert (Hq : ∀ (c : Cs) (z : carrier (fobj[Q] c)),
               sieve_mem (char_sieve theta c (transform[q1] c z)) (@id Cs c)).
    { intros c z. exact (proj2 (Hcomm c z c (@id Cs c)) I). }
    unshelve refine {| unique_obj := char_med UTs theta M q1 Hq |}.
    + split.
      * intros c z; simpl. exact (med_spec UTs theta M q1 Hq c z).
      * intros c z; simpl. destruct (transform[q2] c z); reflexivity.
    + intros v [Hv1 Hv2] c z; simpl.
      apply (theta_inj theta M c).
      transitivity (transform[q1] c z);
        [ exact (med_spec UTs theta M q1 Hq c z) | ].
      symmetry; exact (Hv1 c z).
Defined.

Section SmallUnique.
Context (U E : obj[PShSmall]) (theta : U ~{PShSmall}~> E).
Context (h : E ~{PShSmall}~> Sieve_Presheaf Cs).
Context (HP : @IsPullback PShSmall E (@terminal_obj PShSmall PShSmall_Terminal)
                (Sieve_Presheaf Cs) h (sieve_truth Cs) U theta
                (@one PShSmall PShSmall_Terminal U)).

Lemma small_char_sub_h (c : Cs) (e : carrier (fobj[E] c)) (d : Cs)
  (f : d ~{Cs}~> c) :
  sieve_mem (char_sieve theta c e) f -> sieve_mem (transform[h] c e) f.
Proof using All.
  intro Hf. apply Hf. intros [x Hx].
  pose proof (is_pullback_commutes HP d x) as Hc; simpl in Hc.
  assert (Hid : sieve_mem (transform[h] d (fmap[E] f e)) (@id Cs d)).
  { assert (Heq : transform[h] d (transform[theta] d x)
                    ≈ transform[h] d (fmap[E] f e))
      by (apply proper_morphism; exact Hx).
    apply (proj1 (Heq d (@id Cs d))).
    exact (proj2 (Hc d (@id Cs d)) I). }
  pose proof (@naturality _ _ _ _ h c d f e) as Hn; simpl in Hn.
  pose proof (proj2 (Hn d (@id Cs d)) Hid) as Hm2; simpl in Hm2.
  eapply sieve_respects; [ | exact Hm2 ]. apply id_right.
Qed.

Lemma small_h_sub_char (c : Cs) (e : carrier (fobj[E] c)) (d : Cs)
  (f : d ~{Cs}~> c) :
  sieve_mem (transform[h] c e) f -> sieve_mem (char_sieve theta c e) f.
Proof using All.
  intro Hf.
  set (ed := fmap[E] f e).
  set (S := transform[h] d ed).
  assert (HidS : sieve_mem S (@id Cs d)).
  { unfold S, ed.
    pose proof (@naturality _ _ _ _ h c d f e) as Hn; simpl in Hn.
    apply (proj1 (Hn d (@id Cs d))). simpl.
    eapply sieve_respects; [ | exact Hf ]. symmetry. apply id_right. }
  set (q1 := @sieve_cone Cs E d ed S).
  assert (Hcone : ∀ (k : Cs) (u : carrier (sieve_sub_obj d S k)),
            sieve_equiv (transform[h] k (transform[q1] k u)) (total_sieve k)).
  { intros k u j g. split; intro; [ exact I | ].
    unfold q1, sieve_cone; simpl.
    pose proof (@naturality _ _ _ _ h d k (projT1 u) ed) as Hn; simpl in Hn.
    apply (proj1 (Hn j g)). simpl.
    exact (sieve_closed S (projT1 u) g (projT2 u)). }
  assert (Hsq : h ∘[PShSmall] q1
                  ≈ sieve_truth Cs ∘[PShSmall]
                      @one PShSmall PShSmall_Terminal (sieve_subpresheaf d S))
    by (intros k u j g; exact (Hcone k u j g)).
  pose proof (is_pullback_ump HP (sieve_subpresheaf d S) q1
                (@one PShSmall PShSmall_Terminal _) Hsq) as UM.
  destruct (unique_property UM) as [Hu1 Hu2].
  intros P kk. apply kk.
  exists (transform[unique_obj UM] d (existT _ (@id Cs d) HidS)).
  pose proof (Hu1 d (existT _ (@id Cs d) HidS)) as Hval; simpl in Hval.
  rewrite Hval. exact (@fmap_id _ _ E d ed).
Qed.

Theorem small_unique : h ≈ char_nat theta.
Proof using All.
  intros c e d f; split; [ apply small_h_sub_char | apply small_char_sub_h ].
Qed.

End SmallUnique.

Definition Fun_Classifier_small :
  @SubobjectClassifier PShSmall PShSmall_Terminal :=
  @Build_SubobjectClassifier PShSmall PShSmall_Terminal
    (Sieve_Presheaf Cs)
    (sieve_truth Cs)
    (fun U E theta M => char_nat theta)
    (fun U E theta M => small_pb U E theta M)
    (fun U E theta M h HP => small_unique U E theta h HP).

Example fun_classifier_small_omega :
  @Ω PShSmall PShSmall_Terminal Fun_Classifier_small = Sieve_Presheaf Cs
  := eq_refl.
Example fun_classifier_small_truth :
  @truth PShSmall PShSmall_Terminal Fun_Classifier_small = sieve_truth Cs
  := eq_refl.

(*
 WORK ITEM 2, in the form the issue calls "the content of the
 classification": the subobjects of a presheaf x correspond to the
 maps x ⟹ Ω, as an isomorphism of setoids in [Sets].  This is
 Structure/SubobjectClassifier.v's own theorem applied, over
 Instance/Fun/Pullback.v's [Fun_HasPullbacks Sets_HasPullbacks], which
 is a plain [Definition] and so is named here rather than resolved. 

 --------
 工作项 2，在问题所称的“分类内容”的形式中：预层 x 的子对象对应于映射 x ⟹ Ω，作为 [Sets] 中的集合族同构。这是 Structure/SubobjectClassifier.v 自身的定理的应用，作用于 Instance/Fun/Pullback.v 的 [Fun_HasPullbacks Sets_HasPullbacks]，它是一个普通的 [Definition]，因此在此命名而非解析。
*)
Definition fun_classifier_classifies (x : obj[PShSmall]) :
  @Isomorphism Sets
    {| carrier := @SubObj PShSmall x |}
    {| carrier := x ~{PShSmall}~> @Ω PShSmall PShSmall_Terminal
                                    Fun_Classifier_small |} :=
  @classifier_classifies PShSmall PShSmall_Terminal
    (Fun_HasPullbacks Sets_HasPullbacks) Fun_Classifier_small x.

(*
 Awodey's naturality clause, which is strictly stronger than the
 object-wise bijection: the subobject presheaf of the presheaf category
 IS the presheaf represented by Ω.  Structure/SubobjectClassifier/
 Natural.v's theorem applied; it too carries the [u <= u0] bound, so it
 is available here and refused at [Fun_Classifier], the same pair as
 [classifier_classifies]. 

 --------
 Awodey 的自然性条款，它严格强于按对象的一一对应：预层范畴的子对象预层确实就是由 Ω 表示的预层。Structure/SubobjectClassifier/Natural.v 的定理已应用；它也具有 [u <= u0] 的界限，因此在此可用，而在 [Fun_Classifier] 被拒绝，与 [classifier_classifies] 相同的一对。
*)
Definition fun_sub_classifier_natural :
  @Isomorphism ([(PShSmall^op), Sets])
    (@Sub PShSmall (Fun_HasPullbacks Sets_HasPullbacks))
    (@Curried_CoHom PShSmall
       (@Ω PShSmall PShSmall_Terminal Fun_Classifier_small)) :=
  @Sub_classifier_natural PShSmall PShSmall_Terminal
    (Fun_HasPullbacks Sets_HasPullbacks) Fun_Classifier_small.

Definition fun_Sub_Representable :
  Representable (@Sub PShSmall (Fun_HasPullbacks Sets_HasPullbacks)) :=
  @Sub_Representable PShSmall PShSmall_Terminal
    (Fun_HasPullbacks Sets_HasPullbacks) Fun_Classifier_small.

End Small.
