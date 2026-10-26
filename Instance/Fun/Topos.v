Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Sieve.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.Topos.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Terminal.
Require Import Category.Instance.Fun.Cartesian.
Require Import Category.Instance.Fun.Pullback.
Require Import Category.Instance.Fun.Exponential.
Require Import Category.Instance.Fun.Classifier.

Open Scope category_scope.

(* * * Presheaf categories are elementary toposes / * * 预层范畴是初等拓扑 *)

(*
 Book:      Mac Lane, Categories for the Working Mathematician, 2nd
 ed., §IV.10, printed p. 107 (PDF p. 116)
 ([maclane:IV.10:remark1]).  Verbatim, from the rendered
 page:

 “The category Sets of all (small) sets is a topos and so
 is the category Sets^{C^op} of all set-valued
 contravariant functors on a small category C.  Such a
 functor F : C^op → Sets is also called a presheaf.”

 Book:      Awodey, Category Theory (1st ed., Carnegie Mellon
 pre-print, September 2005), §8.8 “Topoi”, Definition 8.16
 and Proposition 8.17, printed pp. 210-211 (PDF pp.
 219-220) ([awodey:8.8:prop17]).  Verbatim:

 “Definition 8.16.  A topos is a category E such that:
 1. E has all finite limits,
 2. E has a subobject classifier,
 3. E has all exponentials.”

 “Proposition 8.17.  For any small category C, the
 category of diagrams Sets^{C^op} is a topos.”

 “Proof.  Since we already know that Sets^{C^op} has all
 limits, and we know that it has exponentials by the
 foregoing section, we just need to find a subobject
 classifier.  To that end, for any category C we define
 a sieve on an object C to be any set S of arrows
 f : · → C (with arbitrary domain) that is closed under
 precomposition, i.e. if f : D → C is in S then so is
 f ∘ g : E → D → C for every g : E → D (think of a
 sieve as a generalization of a ”lower set“ in a
 poset).”

 Book:      Fong & Spivak, Seven Sketches in Compositionality, §7.3,
 printed pp. 231-232 (PDF pp. 243-244)
 ([7sketches:7.3:remark-presheaf-topos]).  Verbatim:

 “In general, we can think of any small category C as a
 site; the corresponding topos is the category of
 functors C^op → Set.^5  Such functors are called
 presheaves on C.”

 “Did you notice that we just introduced a huge class of
 toposes?  For any category C, we said there is a topos
 of presheaves on it.”

 and, from the closing paragraph of the §7.2 “Review” on
 the facing page (printed p. 231), which is where this
 sentence actually sits:

 “Such toposes are called presheaf toposes and are
 fundamental, but we will focus on sheaf toposes,
 because our topos of behavior types will be a sheaf
 topos.”

 and its footnote 5, which is this issue's appended
 checkbox, verbatim:

 “5 The category of functors C → Set is also a topos: use
 C^op as the defining site.”

 nLab:      https://ncatlab.org/nlab/show/presheaf+topos
 nLab:      https://ncatlab.org/nlab/show/topos
 Wikipedia: https://en.wikipedia.org/wiki/Topos

 WHAT IS DELIVERED.  [Presheaf_Topos C UT], an inhabitant of
 Structure/Topos.v's [ElementaryTopos ([C^op, Sets])] for an ARBITRARY
 category C -- at the universe levels measured below, which is where
 Awodey's word “small” lands -- CONDITIONAL on one hypothesis, #402's
 [Untruncate], which is the classifier field's and nothing else's.
 [Presheaf_Topos_IEM] is the same bundle under informative excluded
 middle.  Seven Sketches' footnote 5 is [Copresheaf_Topos], an
 [ElementaryTopos ([C, Sets])] supplied by [:=] at the opposite
 category with no tactic and no transport, since [(C^op)^op = C] holds
 by [eq_refl] in this tree -- recorded here as [psh_op_invol].

 THE ROUTE IS PURE ASSEMBLY: five fields, five pre-existing donors,
 NOTHING re-proved, no obligation raised and no tactic anywhere in the
 four bundles.

 topos_terminal    Instance/Fun/Terminal.v's [Functor_Category_Terminal]
 topos_cartesian   Instance/Fun/Cartesian.v's [Functor_Category_Cartesian]
 topos_pullbacks   Instance/Fun/Pullback.v's [Fun_HasPullbacks]
 topos_closed      Instance/Fun/Exponential.v's [Functor_Category_Closed]
 topos_classifier  Instance/Fun/Classifier.v's [Fun_Classifier]

 The three structural fields and the closed field fit WITHOUT a
 comparison because the record literal supplies the very terms the
 later fields were stated over: [Functor_Category_Closed]'s cartesian
 index IS the [topos_cartesian] written here, and [Fun_Classifier]'s
 terminal index IS the [topos_terminal] written here.  All five read
 back at [eq_refl] in section (B).

 THE ISSUE'S REVIEWER CHECK -- “the presheaf exponential is proved,
 not postulated” -- is met twice over: [psh_topos_exponent] records at
 [eq_refl] that the bundle's [exponent_obj] IS Awodey's display-(8.5)
 presheaf [PshExp], and [Print Assumptions] reports “Closed under the
 global context” for [Functor_Category_Closed] itself.  Its second
 check -- “the FinSet topos is not silently offered as the witness for
 either of Mac Lane's two claims” -- is met by construction:
 Instance/FinSet/Topos.v is neither required by this file nor cited as
 a witness for anything here, and the [Instance/Sets/Topos.v] sibling
 says the same on its own side.

 WHY A PLAIN [Definition] AND NOT AN [Instance].  Instance/FinSet/Topos.v
 gives the reason and it is followed here: the five [topos_*]
 projections are [#[export] Existing Instance]s, and the component
 structures are registered directly, so registering the bundle too
 would give typeclass search two convergent resolution paths for each
 component.  MEASURED, and the measurement differs from FinSet's
 situation: registering [Presheaf_Topos] is INERT today, because
 [Untruncate] is a plain [Definition] and not a [Class], so the
 bundle's premise can never be discharged by search and the second
 path is a dead end -- with the bundle registered, [@Terminal]
 still resolves to the direct instance and [@HasPullbacks] does not
 resolve at all.  The precedent is followed anyway, and it is
 future-proof against anyone registering an [Untruncate].  A separate
 measurement: THREE of the five components DO resolve on their own, to
 exactly the terms written here, so the record could carry three
 underscores; writing the terms out is what makes section (B)'s
 readbacks statable and stable.

 UNIVERSES, MEASURED OFF BOTH THE BINDER AND THE CONSTRAINT BLOCK.

 Presheaf_Topos@{o h so} :
 ∀ C : Category@{o h h},
 Untruncate@{h} → ElementaryTopos@{so so h} ([C^op, Sets@{h so}])
 block: Set < h, h < so, o <= h, o <= so, plus stdlib bounds.

 Copresheaf_Topos@{o h so},  Presheaf_Topos_IEM@{o h so} and
 Copresheaf_Topos_IEM@{o h so}: character-for-character the same
 block, with [IEM@{h}] in place of [Untruncate@{h}] for the last two.

 Read five things off that.

 (1) NOT ONE CONSTRAINT BLOCK IN THIS FILE CONTAINS AN EQUATION --
 not in these four, and not in any of the twenty readbacks below.
 Every entry is [<] or [<=].  The readbacks reach that only because
 their [Section] [Context] is annotated; see the note at section (B).

 (2) C's hom and proof universes are identified IN THE BINDER
 ([Category@{o h h}], by reusing the level variable) with no equation
 in the block saying so -- the binder/block trap.  That identification
 is inherited from the donors, not introduced here.

 (3) C's OBJECT universe is BOUNDED above by its hom universe
 ([o <= h]), never identified.  That bound IS Awodey's “for any small
 category C”, and it has EXACTLY TWO DONORS, EACH SUFFICIENT ALONE:
 [Functor_Category_Closed] and [Fun_Classifier].  Measured in a
 section declaring C's objects STRICTLY ABOVE its homs: the terminal,
 cartesian and pullback donors are all ACCEPTED there, and the
 exponential and the classifier are each refused alone.  Both refusals
 and the three controls are pinned in Test/ProbeToposInstances404.v.
 Instance/Fun/Exponential.v's own universes paragraph attributes the
 bound to [Transform]'s result type and declines to call it
 unavoidable; it is not claimed unavoidable here either.

 (4) [Set] appears ONLY as the strict LOWER bound [Set < h], which is
 [Prop : Type@{Set+1}] arriving through the truncation inside
 [Fun_Classifier].  NOTHING is pinned to [Set].  The bound is not
 inert: it excludes exactly the C whose hom universe is the literal
 [Set], and [_2] is such a C, which is why the probe's non-vacuity
 section (F) uses [_1], [Ordinal 2], [Parallel] and [Roof] and not
 [_2].  The probe
 pins that refusal with [Functor_Category_Closed _2] ACCEPTED as the
 discriminating control, so the exclusion is attributed to
 [Fun_Classifier] and not to the exponential.

 (5) THE ANNOTATION BUYS PRESENTATION, NOT STRENGTH, FOR THE BUNDLE,
 and that is measured rather than assumed.  The same four bodies with
 NO annotation at all elaborate at [∀ C : Category@{u1 u u}] with
 [u1 <= u] -- the same reading up to renaming, the annotated block's
 extra [o <= so] following from [o <= h < so] -- and no trailing [+]
 is needed.  Read that narrowly, because the #718 minimization lesson
 DOES fire one level down: an unannotated standalone alias of
 [Functor_Category_Closed] minimizes to [Category@{u0 u0 u0}], object,
 hom AND proof identified, strictly narrower than its donor.  No such
 alias is shipped here; the collapse is Instance/Fun/Exponential.v's
 own measurement, pinned in Test/ProbePresheafExp718.v, and is cited
 rather than duplicated.  The bundle escapes it because
 [Fun_Classifier] already fixes the reading -- which is also why the
 UNANNOTATED [Copresheaf_Topos] does not collapse: its body applies
 [Presheaf_Topos], whose binder has already fixed it.

 WHAT EACH CONSTANT CONSUMES.  Every constant in this file is either a
 record literal of five in-tree terms, a [:=] of another constant in
 this file, or an [Example ... := eq_refl].  There is no tactic, no
 [Program], no obligation and no [Qed] anywhere below.  So the ledger
 is short:

 Presheaf_Topos        the five donors named above, and nothing else.
 Presheaf_Topos_IEM    [Presheaf_Topos] and [untruncate_of_IEM].
 Copresheaf_Topos      [Presheaf_Topos] at [C^op]; the conversion
 [(C^op)^op = C], which is definitional here.
 Copresheaf_Topos_IEM  [Copresheaf_Topos] and [untruncate_of_IEM].
 sections (B), (C)     conversion alone.

 STRICT VERSUS [≈], MEASURED STRICT FIRST.  Every identification in
 this file is [eq_refl], and NO equation is proved here at [≈] -- which
 is not a boast but a consequence of the file being an assembly: the
 morphism equations live in the five donors, and each was proved there
 with the [≈] discipline.  Read that exactly: a [≈] DOES occur inside
 one statement, the truncated proposition of [psh_char_is_awodey_sieve],
 but it is part of the sieve membership being read back and not an
 equation this file proves.  TWENTY [eq_refl] STATEMENTS are
 shipped, and that is their whole count below this header -- the
 token itself occurs once more down there, in a comment, and several
 times in this header:
 [psh_op_invol]; the five field readbacks; [exponent_obj] IS [PshExp];
 Ω IS [Sieve_Presheaf C]; [truth] IS [sieve_truth C]; [Pow] IS
 [PshExp P (Sieve_Presheaf C)] (the power object of a presheaf IS its
 exponential by Ω, which is Structure/Topos.v's [Pow] unfolded);
 [topos_terminal] IS Instance/Fun/Exponential.v's [presheaf_terminal];
 the chosen pullback IS [Fun_Pullback Sets_HasPullbacks]; the
 covariant bundle's closed and classifier fields ARE the tree's own
 [Functor_Category_Closed_cov] and [Fun_Classifier_cov], so the
 covariant reading is not a parallel construction; the THREE
 whole-bundle readbacks, which say something strictly stronger than
 those two field ones -- the covariant and contravariant bundles are
 the SAME TERM at opposite categories, in both directions, and the
 [IEM] pair with them; and section (C)'s three Awodey displays.

 ONE SPELLING NOTE, BECAUSE IT COST A REFUSAL.  Two readbacks need
 their types written out or elaboration stalls on an evar.  The
 pullback readback needs the CATEGORY ([a : F ~{[C^op, Sets]}~> H]);
 with a bare [F ~> H] the elaborator reports that F has type
 [C^op ⟶ Sets] where an [obj[?Category]] was expected.  And the
 restriction readback of section (C) needs its arrow ASCRIBED into
 [C^op] ([(h : c ~{C^op}~> d)]); written instead through the
 [morphism] coercion, as [morphism (fmap[Sieve_Presheaf C] h) S], the
 coercion is left an evar [?s] and [eq_refl] does not close.  Both the
 refusal and the accepted spelling are pinned in the probe, the
 accepted one as the discriminating control.

 THE SMALL READING IS BLOCKED, AND AT THE CLOSED FIELD -- NOT AT THE
 CLASSIFIER.  Instance/Fun/Classifier.v's [Section Small] lifts the
 presheaf category's hom universe above its object universe, giving
 [PShSmall Cs : Category@{OO HH HH}] with [Fun_Classifier_small] at
 that reading, which is what makes [classifier_classifies] apply there
 ([fun_classifier_classifies]).  FOUR of the five topos fields fit
 [PShSmall Cs] -- [PShSmall_Terminal], the pointwise cartesian
 structure, [Fun_HasPullbacks Sets_HasPullbacks] and
 [Fun_Classifier_small] are all accepted -- and the exponential does
 not:

 The term “Functor_Category_Closed Cs” has type
 “@Closed ([Cs^op, Sets])
 (Functor_Category_Cartesian Cs^op Sets Sets_Cartesian)”
 while it is expected to have type
 “@Closed (PShSmall Cs)
 (Functor_Category_Cartesian Cs^op Sets Sets_Cartesian)”
 (universe inconsistency: Cannot enforce o = small1.97 because
 o < so <= small1.96 <= small1.97).

 The obstruction sits at [presheaf_exp_iso], which is an isomorphism
 of hom-setoids in [Sets@{o so}]: at the lifted reading those
 hom-setoids are objects of a LARGER [Sets], so the exponential's
 category index -- unlike the functor category itself, whose hom
 universe is free to move up -- is invariant.  CONSEQUENCE: there is
 no [Presheaf_Topos_small], hence no topos here at which
 [classifier_classifies] applies.  What stands in for it is
 [fun_classifier_classifies], already in tree over
 [Fun_Classifier_small] and [Fun_HasPullbacks Sets_HasPullbacks]
 without a topos bundle; it is CITED and not re-derived.  NOTHING IS
 CLAIMED IMPOSSIBLE: only that the naive lift and the naive rebuild
 are both refused, with the error above.  Whether a [Setoid_Lift]-
 mediated exponential at the lifted [Sets] would work is NOT MEASURED,
 and repairing it would be work in Instance/Fun/Exponential.v rather
 than in a topos file.

 THE OBSTRUCTION, ARGUED FOR THE RECORD, since the issue's Definition
 of Done asks for an instance OR an argued obstruction and the honest
 verdict is neither of its two branches.

 WHICH CLAUSE IS CONDITIONAL: exactly one, the classifier -- Mac
 Lane's Axiom 8 “Truth” of §App.1 and his §IV.9 construction 1.  The
 terminal object, the pointwise products, the pointwise pullbacks
 and the exponentials are UNCONDITIONAL at [C^op, Sets]: all four
 donors are argument-free apart from C, and each is Closed under the
 global context.  So “presheaf categories are cartesian closed with
 finite limits” is unconditional in this tree; only the topos is
 conditional.

 WHAT THE HYPOTHESIS IS, verbatim from
 Instance/Sets/Classifier/OneLevel.v and
 Instance/Sets/Powerset.v:

 Definition Untruncate@{o} :=
 ∀ P : Type@{o}, Powerset_squash@{o} P -> P.
 Definition Powerset_squash@{o} (A : Type@{o}) : Prop :=
 ∀ Q : Prop, (A → Q) → Q.

 WHERE IT IS SPENT: Instance/Fun/Classifier.v records that
 [Untruncate] is spent EXACTLY ONCE in that file, in [med_img], and
 that whether it is NECESSARY is not settled there.  It is not
 settled here either.

 WHY IT IS NEEDED AT ALL: [≈] in this library is [Type@{o}]-valued,
 so a sieve's membership predicate has to be truncated into [Prop]
 to sit at the carrier's own level, and inverting that truncation is
 exactly what [Untruncate] is.  The naive elimination
 [fun P h => h P (fun p => p)] is refused with “Cannot enforce
 o <= Prop”; that refusal is already
 Test/ProbeClassifier402.v and is CITED, not duplicated here.

 NO IMPOSSIBILITY IS PROVED, and there is NO IN-TREE INHABITANT of
 the premise: a sweep of the declarations whose CONCLUSION is
 [Untruncate], [IEM] or [DecImage] returns five, of which four are
 PASSAGES between the hypotheses ([untruncate_of_IEM],
 [DecImage_of_IEM], [IEM_of_DecImage] and [DecImage_iff_IEM]) and
 one is a refutation command that never enters the environment
 (Test/ProbeFunClassifier403.v).
 Instance/Sets/Classifier/OneLevel.v's three-part
 disclosure applies verbatim, including its part (iii), that an
 out-of-tree scratch development builds the classifier on exactly
 [classic] and [constructive_indefinite_description] so an in-tree
 impossibility theorem would refute a classically valid statement.
 THAT PART IS A HEADER CLAIM OF THAT FILE, quoted here and NOT
 re-run.

 AND THERE IS NO [DecImage] VARIANT FOR PRESHEAVES.  At [Sets] there
 is one ([Sets_Classifier_dec]), which is why the sibling
 Instance/Sets/Topos.v ships three bundles and this file two;
 Instance/Fun/Classifier.v records, in two places, that no such
 presheaf variant is built.

 NON-VACUITY, and its limit.  A non-vacuity section is deliberately
 absent from this file: the four shape witnesses live in the probe, because
 naming them costs [Instance/One], [Instance/Ordinal],
 [Instance/Parallel] and [Instance/Roof] and none of the four is in
 this file's closure.  The probe carries [Presheaf_Topos] at [_1], at
 [Ordinal 2], at [Parallel] and at [Roof], with three [eq_refl]
 Examples over them.  NOTHING COMPUTES TO A NUMERAL, and that is
 structural rather than an omission: a sieve's membership is
 [Prop]-valued and truncated (Theory/Sieve.v records that the
 [Prop] choice is forced, a [Type@{o}]-valued sieve type sitting one
 universe too high), so Ω carries no decidable code and there is no
 analogue of Instance/FinSet/Topos.v's [Pow 2 = 4].  What holds are
 the definitional readbacks of sections (B) and (C).

 NO CONFLICT WITH Instance/Fun/Closed.v.  That file's
 [fun_not_cartesian_closed] refutes cartesian closure of
 [[Omega, FinSet]] -- a FinSet-valued functor category, not a
 [Sets]-valued presheaf category -- and its Awodey counterexample
 concerns the OBJECTWISE formula, not the display-(8.5) one.  The two
 do not collide, and this file changes nothing there.

 PRIOR ART, AND THE ISSUE'S “CURRENT STATE”, EACH RE-MEASURED WITH ITS
 CRITERION AT THE BASE COMMIT.

 TRUE STILL AT THE BASE COMMIT: “the only [ElementaryTopos]
 inhabitant anywhere is Instance/FinSet/Topos.v”.  CRITERION, and
 it must be stated so that it produces the numbers beside it:
 declaration heads whose type MENTIONS [ElementaryTopos] after a
 colon -- so it also catches the two that take one as a HYPOTHESIS
 -- swept comment-stripped ACROSS LINE BREAKS, since a head whose
 type wraps is invisible to a line-anchored pattern:
 [rg -n ':\s*ElementaryTopos' -g '*.v'] is exactly such a pattern and
 misses all three bundles of Instance/Sets/Topos.v, whose [:] and
 class name sit on different lines.  Under the sound criterion the
 base commit returns three heads, two of them Structure/Topos.v's
 [Pow] and its [relations_iso] taking one as a hypothesis, leaving
 [FinSet_Topos] as the sole INHABITANT; the shipped tree returns ten,
 the seven new bundles included.  ALSO TRUE: “[ElementaryTopos]
 carries pullbacks explicitly ... the assembly must supply pullbacks
 directly” -- Structure/Topos.v does, and this file supplies
 them.

 STALE, in six places.  “For presheaves ... no terminal object, no
 exponentials, no pullbacks, no classifier” -- all four now exist,
 at Instance/Fun/Terminal.v, Instance/Fun/Exponential.v,
 Instance/Fun/Pullback.v and Instance/Fun/Classifier.v, and
 all four are consumed here.  “Instance/Fun/Cartesian.v is the
 only structural instance on any functor category” -- it is not.
 “[ls Instance/Fun/] contains Cartesian.v and nothing else” --
 [ls Instance/Fun/*.v | wc -l] returns 10 before this file.  “sieve
 occurs only twice in the tree, both prose” -- [rg -li 'sieve'
 -g '*.v'] returns 6 files, one of which, Theory/Sieve.v, is a
 258-line module DECLARING the notion.  “no [HasPullbacks] for a
 functor category (the only instance in the tree is
 Instance/FinSet/Classifier.v)” -- [Fun_HasPullbacks] is
 Instance/Fun/Pullback.v.  And the Awodey section's “the
 classifier by #403, and the cartesian-closure component by the
 Awodey §8.7 issue” -- both have landed, and are what this file
 assembles.

 A FIRST, MEASURED BY THREE SWEEPS RATHER THAN BY NAME.  Through
 Structure/Topos/Colimits.v, this bundle yields an initial object, a
 binary coproduct, coequalizers, pushouts and equalizers for
 [C^op, Sets], and each would be the FIRST inhabitant of its class
 at any functor category in this tree.  Criterion, all three run at
 the base commit: (i) a name sweep for [Fun_Initial],
 [Fun_Cocartesian], [Fun_HasCoequalizers], [Fun_HasPushouts],
 [Fun_HasEqualizers], [Functor_Category_Initial] and
 [Functor_Category_Cocartesian] returns nothing; (ii) a shape sweep
 for any of [Initial], [Cocartesian], [HasCoequalizers],
 [HasPushouts], [HasEqualizers] applied to a bracketed functor
 category returns nothing, with [@Cartesian ([] returning five CODE
 lines as the instrument (a sixth hit is prose); (iii) every
 declaration head of those five classes tree-wide was read, and not
 one is at a functor category.
 The five are exhibited in the probe rather than here, because
 requiring Structure/Topos/{Monadic,Colimits}.v takes this file's
 closure from 108 to 133.  They are CONDITIONAL on [Untruncate],
 like the bundle, and no construction of their own is offered.

 WHAT IS NOT DELIVERED -- read this as the scope of the file.

 * No unconditional presheaf topos, and no impossibility theorem
 (see the obstruction above).  [Untruncate] has no axiom-free
 in-tree inhabitant.

 * No [Presheaf_Topos_small], hence no [classifier_classifies],
 [relations_iso] or [Sub_classifier_natural] AT a topos here: all
 three are refused at [Presheaf_Topos], and the probe pins the
 three refusals.  [fun_classifier_classifies] is the standalone
 result that stands in for the first.

 * No comparison of [Presheaf_Topos] with Instance/Sets/Topos.v's
 [Sets_Topos]: no functor between the two categories is built and
 nothing relates their truth objects or their power objects.

 * No sheaf reading.  Theory/Sheaf.v is not touched; the trivial
 coverage and the equivalence with sheaves on a trivial site
 belong to the Seven Sketches §7.4 item and are not attempted.

 * No slice topos, no Lawvere-Tierney topology, no internal logic,
 and nothing about Giraud's theorem.

 * Nothing about the Yoneda embedding, representables, or density,
 and no naturality of any identification in C.

 * Nothing computes: see the non-vacuity paragraph.

 * Nothing is registered as an [Instance]; all four bundles are
 plain [Definition]s, deliberately.

 * This file contributes NO lines to [make todo].  Its probe does,
 as every probe in this tree does, and that is disclosed rather
 than hidden. 

 --------
 书籍：      Mac Lane，《为工作数学家而写的范畴论》，第二版，§IV.10，第107页（PDF第116页）（[maclane:IV.10:remark1]）。照字面翻译，自渲染页面：

 “所有（小）集合的范畴 Sets 是一个拓扑类，因此
 所有集合值的协变对偶函子在小范畴 C 上构成的范畴 Sets^{C^op} 也是一个拓扑类。这样的
 函子 F : C^op → Sets 也称为预层。”

 书籍：      Awodey，《范畴论》（第一版，卡内基梅隆大学预印本，2005年9月），§8.8 “拓扑类”，定义 8.16
 和命题 8.17，第210-211页（PDF第219-220页）（[awodey:8.8:prop17]）。照字面翻译：定义 8.16. 拓扑是一个范畴 E，使得：
 1. E 具有所有有限极限，
 2. E 具有子对象分类器，
 3. E 具有所有指数对象。

 命题 8.17. 对于任意小范畴 C，图示范畴 Sets^{C^op} 是一个拓扑。证明。由于我们已经知道 Sets^{C^op} 拥有所有极限，并且根据前面一节我们知道它具有指数对象，我们只需要找到一个子对象分类器。为此，对于任何范畴 C，我们定义对象 C 上的筛子（sieve）为任意箭头集合 S，其中每个箭头 f : · → C（定义域任意）都在集合中，并且该集合在前合成下闭合，即如果 f : D → C 属于 S，那么对于每个 g : E → D，复合箭头 f ∘ g : E → D → C 也属于 S（将筛子看作是偏序集合中“下集”的推广）。一般来说，我们可以把任何小范畴C看作一个站点；对应的拓扑是范畴 C^op → Set 的函子范畴。这样的函子称为C上的前层。

 你注意到我们刚刚引入了一个巨大的拓扑类吗？对于任何范畴C，我们说在其上有一个前层拓扑。

 这样的拓扑称为前层拓扑，它们非常基础，但我们将关注于层拓扑，因为我们的行为类型拓扑将是一个层拓扑。以及其脚注5，即本期附加的复选框，逐字如下：

 “5 从 C 到 Set 的函子类别也是一个拓扑：使用 C^op 作为定义站点。”

 nLab: https://ncatlab.org/nlab/show/presheaf+topos
 nLab: https://ncatlab.org/nlab/show/topos
 Wikipedia: https://en.wikipedia.org/wiki/Topos交付的内容。[Presheaf_Topos C UT]，Structure/Topos.v 的 [ElementaryTopos ([C^op, Sets] 的居民，对于任意类别 C——在下面测量的宇宙层次上，这是 Awodey 所说的“小”的位置——在一个假设 #402 的条件下，[Untruncate]，这是分类器字段，仅此而已。[Presheaf_Topos_IEM] 是在信息排中律排除下的同一捆束。Seven Sketches 的脚注 5 是 [Copresheaf_Topos]，一个由 [:=] 在对立类别提供的 [ElementaryTopos ([C, Sets]，无策略亦无传输，因为 [(C^op)^op = C] 在此树中由 [eq_refl] 保持——此处记录为 [psh_op_invol]。

 路径是纯装配：五个字段，五个预先存在的供体，未重新证明，未提出义务，四个捆束中没有任何策略。topos_terminal    Instance/Fun/Terminal.v 的 [Functor_Category_Terminal]
 topos_cartesian   Instance/Fun/Cartesian.v 的 [Functor_Category_Cartesian]
 topos_pullbacks   Instance/Fun/Pullback.v 的 [Fun_HasPullbacks]
 topos_closed      Instance/Fun/Exponential.v 的 [Functor_Category_Closed]
 topos_classifier  Instance/Fun/Classifier.v 的 [Fun_Classifier]

 三个结构字段和闭合字段无需比较即可匹配，因为记录字面量提供了后续字段所述的确切项：[Functor_Category_Closed] 的 cartesian 索引就是此处写的 [topos_cartesian]，而 [Fun_Classifier] 的 terminal 索引就是此处写的 [topos_terminal]。所有五个都在第 (B) 节的 [eq_refl] 中读取。问题审阅者检查——“预层指数已被证明，而非假设”——已经得到两次满足：[psh_topos_exponent] 在 [eq_refl] 记录了该丛的 [exponent_obj] 是 Awodey 的显示-(8.5) 预层 [PshExp]，且 [Print Assumptions] 报告 [Functor_Category_Closed] 本身“在全局上下文下闭合”。其第二次检查——“FinSet 拓扑不是作为 Mac Lane 两个主张的见证被默默提供”——通过构造得到满足：Instance/FinSet/Topos.v 既不是此文件所需，也未被引用为此处任何事物的见证，而 [Instance/Sets/Topos.v] 的兄弟在其自身页面上也表示同样。为什么是一个普通的 [Definition] 而不是一个 [Instance]。《Instance/FinSet/Topos.v》给出了原因，这里沿用了该理由：五个 [topos_*] 投影是 [#[export] 已存在的实例，并且组件结构是直接注册的，因此如果同时注册该束，将会为每个组件的类型类搜索提供两条汇聚的解析路径。MEASURED，并且该度量与 FinSet 的情况不同：今天注册 [Presheaf_Topos] 是惰性的，因为 [Untruncate] 是一个普通的 [Definition] 而不是 [Class]，因此束的前提条件无法通过搜索解除，第二条路径是死路——即使束已注册，[@Terminal] 仍然解析为直接实例，而 [@HasPullbacks] 根本无法解析。无论如何，这一先例都被遵循，并且它对任何注册 [Untruncate] 的行为都有前瞻性保护。另一项测量：五个组件中的三个确实会自行解析，且恰好符合这里写下的条款，因此记录可以包含三个下划线；写出条款是使 (B) 节的回读可表述且稳定的原因。

 宇宙，同时以绑定器和约束块为量度。

 Presheaf_Topos@{o h so} :
 ∀ C : Category@{o h h},
 Untruncate@{h} → ElementaryTopos@{so so h} ( [C^op, Sets@{h so}] )
 block: Set < h, h < so, o <= h, o <= so, 加上标准库边界。

 Copresheaf_Topos@{o h so}, Presheaf_Topos_IEM@{o h so} 和 Copresheaf_Topos_IEM@{o h so}：逐字符完全相同的块，将最后两个的 [Untruncate@{h}] 替换为 [IEM@{h}]。读出五件事。 

 (1) 这个文件中没有一个约束块包含方程——
 无论是在这四个中，还是在下面二十个回读中都没有。
 每个条目都是 [<] 或 [<=]。回读达到这一点仅仅是因为它们的 [Section] [Context] 已被注释；见 (B) 节的说明。

 (2) C 的 hom 和 proof 宇宙在装订器中被识别（[Category@{o h h}]，通过重用级变量）且块中没有方程说明此点——这就是装订器/块陷阱。该识别是继承自捐赠者的，而非在此引入。(3) C 的对象宇宙在其 Hom 宇宙 ([o <= h]) 之上是有界的，从未被确认。这个界就是 Awodey 所说的“对于任何小范畴 C”，并且它恰好有两个捐赠者，每个独自就足够：[Functor_Category_Closed] 和 [Fun_Classifier]。在声明 C 的对象严格位于其 Hom 之上这一节中测量：终端对象、笛卡尔对象和拉回对象捐赠者都被接受，而指数对象和分类器各自单独被拒绝。拒绝的对象和三个控制对象都在 Test/ProbeToposInstances404.v 中固定。Instance/Fun/Exponential.v 自己的宇宙段把界归于 [Transform] 的结果类型，并拒绝称其为不可避免；这里也没有声称它是不可避免的。(4) [Set] 仅以严格下界 [Set < h] 的形式出现，该下界是通过 [Fun_Classifier] 内的截断到达的 [Prop : Type@{Set+1}]。没有任何东西被固定到 [Set]。该下界并非惰性：它恰好排除了同类宇宙为 [Set] 的 C，并且 [_2] 是这样的 C，这就是探针的非空部分 (F) 使用 [_1]、[Ordinal 2]、[Parallel] 和 [Roof] 而非 [_2] 的原因。探针通过 [Functor_Category_Closed _2] 接受该拒绝作为区分控制，因此排除归因于 [Fun_Classifier]，而不是指数。(5) 注释为捆绑包提供的是呈现，而不是强度，并且这是经过测量而非假设的。相同的四个主体在完全没有注释的情况下，在 [∀ C : Category@{u1 u u}] 处展开，并且在 [u1 <= u] 处——与重命名前的读取相同，带注释块的额外 [o <= so] 来源于 [o <= h < so] ——并且不需要后续的 [+]。狭义地理解这一点，因为 #718 最小化的教训确实会在下一层触发：[Functor_Category_Closed] 的未注释独立别名最小化为 [Category@{u0 u0 u0}]，对象、同态和证明确认，严格比其源更狭窄。这里没有传输这样的别名；折叠是 Instance/Fun/Exponential.v 自己的测量结果，在 Test/ProbePresheafExp718.v 中固定，并且是引用而非复制。该捆绑包逃脱了它，因为 [Fun_Classifier] 已经固定了读取 —— 这也是为什么未注释的 [Copresheaf_Topos] 不会倒塌的原因：它的主体应用了 [Presheaf_Topos]，其绑定器已经固定了它。

 每个常量的消耗。 本文件中的每个常量要么是五个内部树项的记录字面量，要么是本文件中另一个常量的 [:=]，或者是一个 [Example ... := eq_refl]。 下面没有任何策略、[Program]、义务或 [Qed]。 因此账目很简短：Presheaf_Topos        上述五个捐赠者，并且没有其他人。
 Presheaf_Topos_IEM     [Presheaf_Topos] 和 [untruncate_of_IEM]。
 Copresheaf_Topos       [Presheaf_Topos] 在 [C^op]；转换
 [(C^op)^op = C]，这里是定义性的。
 Copresheaf_Topos_IEM   [Copresheaf_Topos] 和 [untruncate_of_IEM]。
 sections (B), (C)     仅转换。严格与 [≈]，对严格进行优先测量。本文件中的每个标识都是 [eq_refl]，而且这里没有任何方程在 [≈] 中被证明——这不是夸耀，而是由于该文件是一个汇编文件的结果：态射方程存在于五个供体中，并且每个都在 [≈] 的纪律下被证明。准确地阅读：一个 [≈] 确实出现在一个陈述中，即 [psh_char_is_awodey_sieve] 的截断命题，但它是被回读的筛子成员的一部分，而不是本文件证明的方程。二十个 [eq_refl] 语句已被发送，这是此标题下它们的全部计数——该标记本身在下方的注释中再次出现，并在此标题中出现多次：
 [psh_op_invol]；五个字段的回读；[exponent_obj] 是 [PshExp]；
 Ω 是 [Sieve_Presheaf C]；[truth] 是 [sieve_truth C]；[Pow] 是 [PshExp P (Sieve_Presheaf C)]（一个预层的幂对象是它对 Ω 的指数，等于 Structure/Topos.v 的 [Pow] 展开）；
 [topos_terminal] 是 Instance/Fun/Exponential.v 的 [presheaf_terminal]；
 所选择的拉回是 [Fun_Pullback Sets_HasPullbacks]；协变丛的闭合和分类字段是树本身的 [Functor_Category_Closed_cov] 和 [Fun_Classifier_cov]，所以协变回读不是平行构造；三个完整丛回读，其含义严格强于那两个字段——协变和逆变体丛在相对范畴中是相同的术语，在两个方向上，与它们配对的 [IEM]；以及第 (C) 节的三个位 Awodey 显示器。一个拼写注意事项，因为它导致了拒绝。两个回读需要写出它们的类型，否则 elaborator 在一个 evar 上会停滞。回拉回读需要类别 ( [a : F ~{[C^op, Sets] }~> H ]); 使用一个裸 [F ~> H]，elaborator 报告 F 的类型为 [C^op ⟶ Sets]，而期望的是一个 [obj[?Category] ]。并且，第 (C) 节的限制性回读需要箭头 ASCRIBED 到 [C^op] ( [(h : c ~{C^op}~> d)] )；如果改为通过 [morphism] 强制转换写作 [morphism (fmap[Sieve_Presheaf C] h) S]，强制转换会被保留为一个 evar [?s]，而 [eq_refl] 无法关闭。拒绝的拼写和被接受的拼写都固定在探针中，被接受的作为区分控制。小的读数被阻塞，并且在封闭域处——而不是在分类器处。Instance/Fun/Classifier.v 的 [Section Small] 将 presheaf 范畴的同构宇宙提升到其对象宇宙之上，给出 [PShSmall Cs : Category@{OO HH HH}]，并在该读数处有 [Fun_Classifier_small]，这就是使 [classifier_classifies] 在那里应用的原因（[fun_classifier_classifies]）。五个 topoi 域中的四个适合 [PShSmall Cs]——[PShSmall_Terminal]，即逐点笛卡尔结构，[Fun_HasPullbacks Sets_HasPullbacks] 和 [Fun_Classifier_small] 全部被接受——而指数则不被接受。术语 “Functor_Category_Closed Cs”的类型是
 “@Closed ( [Cs^op, Sets] )
 (Functor_Category_Cartesian Cs^op Sets Sets_Cartesian)”
 而预期的类型是
 “@Closed (PShSmall Cs)
 (Functor_Category_Cartesian Cs^op Sets Sets_Cartesian)”
 （宇宙不一致：无法强制 o = small1.97 因为
 o < so <= small1.96 <= small1.97）。阻塞位于 [presheaf_exp_iso]，它是在 [Sets@{o so}] 中同态集合的同构：在提升后的读法中，这些同态集合是更大 [Sets] 的对象，所以指数的范畴指标——与函子范畴本身不同，其同态宇宙可以自由上升——是不变的。结果：不存在 [Presheaf_Topos_small]，因此在此处不存在 [classifier_classifies] 适用的拓扑。替代它的是 [fun_classifier_classifies]，已经存在于 [Fun_Classifier_small] 和 [Fun_HasPullbacks Sets_HasPullbacks] 的树上而没有拓扑簇；它被引用而不是重新导出。没有声明任何事情是不可能的：只是说明天真的提升和天真的重建都被拒绝，出现如上错误。是否由 [Setoid_Lift] 介导的在提升的 [Sets] 上的指数会起作用尚未测量，修复它的工作将是在 Instance/Fun/Exponential.v 中进行，而不是在 topos 文件中进行。

 记录中争论的阻碍，因为该问题的完成定义要求一个实例或一个争论的阻碍，而诚实的判决是它的两个分支都不是。哪个条款是有条件的：恰好一个，分类器 -- Mac Lane 的公理 8 “真理” (§App.1) 及其 §IV.9 构造 1。终对象、逐点积、逐点拉回和指数在 [C^op, Sets] 上是无条件的：除了 C 之外，所有四个供体都没有参数，并且每个都在全局上下文下封闭。因此，“预层范畴具有笛卡尔闭性并具有有限极限”在此树中是无条件的；只有拓扑（topos）是有条件的。

 假设是什么，逐字来自 Instance/Sets/Classifier/OneLevel.v 和 Instance/Sets/Powerset.v：

 定义 Untruncate@{o} :=
 ∀ P : Type@{o}, Powerset_squash@{o} P -> P.
 定义 Powerset_squash@{o} (A : Type@{o}) : Prop :=
 ∀ Q : Prop, (A → Q) → Q.花费地点：Instance/Fun/Classifier.v 记录了 [Untruncate] 在该文件中恰好使用一次，出现在 [med_img] 中，并且那里没有确定它是否是必要的。在这里也没有确定。

 为什么它需要：这个库中的 [≈] 是 [Type@{o}] 值，所以筛子的成员谓词必须被截断为 [Prop]，以便与承载类型自身层级一致，而反转该截断正是 [Untruncate] 的作用。天真的消除 [fun P h => h P (fun p => p)] 被拒绝，并提示“无法强制 o <= Prop”；这种拒绝已经出现在 Test/ProbeClassifier402.v 中，并且被引用，而不是在这里重复。没有不可能性被证明，并且前提中没有树内的居民：对声明的扫掠，其结论是 [Untruncate]、[IEM] 或 [DecImage]，共返回五条，其中四条是假设之间的通道（[untruncate_of_IEM]、[DecImage_of_IEM]、[IEM_of_DecImage] 和 [DecImage_iff_IEM]），一条是从未进入环境的反驳命令（Test/ProbeFunClassifier403.v）。Instance/Sets/Classifier/OneLevel.v 的三部分披露照原文适用，包括其第（三）部分，即树外的临时开发在 [classic] 和 [constructive_indefinite_description] 上构建分类器，因此树内的不可能性定理将驳斥一个经典有效的陈述。那部分是该文件的标题声明，在此引用，并未重新运行。并且没有用于预层的 [DecImage] 变体。在 [Sets] 有一个（[Sets_Classifier_dec]），这就是为什么 sibling Instance/Sets/Topos.v 提供三个捆绑包而这个文件提供两个；Instance/Fun/Classifier.v 在两个地方记录了没有构建这样的预层变体。非空性及其极限。本文件中故意省略了非空性部分：四个形状证人在探针中存在，因为命名它们需要 [Instance/One]、[Instance/Ordinal]、[Instance/Parallel] 和 [Instance/Roof]，而这四个都不在本文件的闭包中。探针在 [_1]、[Ordinal 2]、[Parallel] 和 [Roof] 处携带 [Presheaf_Topos]，并在其上有三个 [eq_refl] 示例。没有任何内容可以计算为数字，这是结构性的，而不是遗漏：筛子的成员是 [Prop] 值并被截断（Theory/Sieve.v 记录了 [Prop] 选择是强制的，[Type@{o}] 值的筛子类型位于比当前宇宙高一个的级别），因此 Ω 没有可判定的代码，并且没有 Instance/FinSet/Topos.v 中 [Pow 2 = 4] 的类似物。保持的是 (B) 和 (C) 节的定义性重述。

 与 Instance/Fun/Closed.v 没有冲突。该文件的 [fun_not_cartesian_closed] 反驳了 [[Omega, FinSet] 的笛卡尔闭性 —— 一个以 FinSet 为值的函子范畴，而不是 [Sets] 值的预层范畴 —— 且其 Awodey 反例涉及的是按对象的公式，而不是显示的 (8.5) 公式。这两者不冲突，该文件在这里没有任何改变。

 先前工作，以及该问题的“当前状态”，都用其在基础提交中的标准重新衡量。在基础提交中仍然为 TRUE：“唯一的 [ElementaryTopos] 居民在任何地方都是 Instance/FinSet/Topos.v”。标准，并且必须以这样的方式陈述，以便它在旁边产生数字：声明头的类型在冒号之后提到 [ElementaryTopos] —— 所以它也会捕获那些把它作为假设的两个 —— 去掉注释后跨行扫描，因为类型换行的头对行锚定模式是不可见的：[rg -n ':\s*ElementaryTopos' -g '*.v'] 正是这样的模式，并且漏掉了 Instance/Sets/Topos.v 的所有三个组合包，其 [:] 和类名位于不同行。在声学标准下，基础提交返回三个头，其中两个是 Structure/Topos.v 的 [Pow] 及其 [relations_iso]，将其中一个作为假设，剩下 [FinSet_Topos] 作为唯一的 INHABITANT；提供的树返回十个，包括七个新捆绑包。同样正确的是：“[ElementaryTopos] 明确处理拉回……组件必须直接提供拉回”——Structure/Topos.v 做到了，而这个文件也提供了它们。陈旧，在六个地方。“对于预层...没有终端对象，没有指数，没有拉回，没有分类器”——现在这四个都存在于 Instance/Fun/Terminal.v、Instance/Fun/Exponential.v、Instance/Fun/Pullback.v 和 Instance/Fun/Classifier.v，并且这四个在这里都被使用。“Instance/Fun/Cartesian.v 是任何函子范畴上唯一的结构实例”——事实并非如此。“[ls Instance/Fun/] 包含 Cartesian.v，别无他物”——[ls Instance/Fun/*.v | wc -l] 在此文件之前返回 10。“筛子在树中只出现两次，均为文字描述”——[rg -li 'sieve' -g '*.v'] 返回 6 个文件，其中一个 Theory/Sieve.v 是一个 258 行的模块，用于声明该概念。“对于函子范畴没有 [HasPullbacks]（树中唯一的实例是 Instance/FinSet/Classifier.v）”——[Fun_HasPullbacks] 是 Instance/Fun/Pullback.v。Awodey 部分的“由 #403 提出的分类器，以及 Awodey §8.7 问题中的笛卡尔闭包分量”——两者都已完成，并且就是这个文件所汇编的内容。第一个，不是按名称，而是通过三次扫描来衡量。通过 Structure/Topos/Colimits.v，这个集合产生一个初始对象、一个二元余积、余等化子、推出和等化子用于 [C^op, Sets]，并且在这棵树中的任何函子范畴中，每一个都会是其类的第一个成员。标准，全部三项在基础提交上运行：（i）对 [Fun_Initial]、[Fun_Cocartesian]、[Fun_HasCoequalizers]、[Fun_HasPushouts]、[Fun_HasEqualizers]、[Functor_Category_Initial] 和 [Functor_Category_Cocartesian] 进行名称扫描，返回为空；（ii）对 [Initial]、[Cocartesian]、[HasCoequalizers]、[HasPushouts]、[HasEqualizers] 应用于带括号的函子类别进行形状扫描，返回为空，其中 [@Cartesian ([] 返回五行 CODE 作为工具（第六个命中是散文）；（iii）树状结构中那五个类的每个声明头都已被读取，没有一个是在函子类别中。这五个在探针中展示，而不是在这里展示，因为要求 Structure/Topos/{Monadic,Colimits}.v 会将此文件的闭包从 108 增至 133。它们对 [Untruncate] 具有条件性，就像捆绑包一样，并且没有提供自己的构造。未交付的内容 -- 读取此内容作为文件的范围。

 * 没有无条件的预层拓扑，也没有不可能性定理（见上面的障碍）。[Untruncate] 没有无公理的树内居民。

 * 没有 [Presheaf_Topos_small]，因此也没有 [classifier_classifies]、[relations_iso] 或 [Sub_classifier_natural] 在此拓扑中：三者在 [Presheaf_Topos] 处都被拒绝，探针标记了这三次拒绝。[fun_classifier_classifies] 是独立的结果，代表第一个结果。

 * 没有将 [Presheaf_Topos] 与 Instance/Sets/Topos.v 的 [Sets_Topos] 进行比较：没有在两类之间建立函子，也没有任何内容将它们的真值对象或幂对象联系起来。* 不涉及层阅读。Theory/Sheaf.v 没有被改动；平凡覆盖以及与平凡站点上层的等价属于《七个素描》第7.4节的内容，不会尝试。

 * 不涉及切片拓扑、Lawvere-Tierney 拓扑、内部逻辑，也不涉及 Giraud 定理。

 * 不涉及 Yoneda 嵌入、表示物或密度，也不涉及 C 中任何同一性的自然性。

 * 不计算任何东西：参见非空段落。

 * 没有任何内容被注册为 [Instance]；四个丛都是普通的 [Definition]，这是有意为之。

 * 此文件没有向 [make todo] 贡献任何行。它的探针会贡献，就像此树中的每个探针都会那样，这是公开的而非隐藏的。
*)

(** ** (A) The four bundles / **（A）四捆 *)

(*
 [(C^op)^op = C] by conversion: what makes the covariant reading a
 [:=] rather than a transport. 

 --------
 通过转换：是什么使协变读取成为 [:=] 而不是传输。
*)
Example psh_op_invol (C : Category) : (C^op)^op = C := eq_refl.

Definition Presheaf_Topos@{o h so} (C : Category@{o h h})
  (UT : Untruncate@{h}) : ElementaryTopos ([C^op, Sets@{h so}]) := {|
  topos_terminal   := Functor_Category_Terminal Sets_Terminal;
  topos_cartesian  := Functor_Category_Cartesian (C^op) Sets Sets_Cartesian;
  topos_pullbacks  := Fun_HasPullbacks Sets_HasPullbacks;
  topos_closed     := Functor_Category_Closed C;
  topos_classifier := Fun_Classifier UT
|}.

Definition Presheaf_Topos_IEM@{o h so} (C : Category@{o h h})
  (Em : IEM@{h}) : ElementaryTopos ([C^op, Sets@{h so}]) :=
  Presheaf_Topos@{o h so} C (untruncate_of_IEM Em).

(*
 Seven Sketches §7.3 footnote 5: “The category of functors C → Set is
 also a topos: use C^op as the defining site.” 

 --------
 七个素描 §7.3 脚注 5：“函子 C → Set 的范畴也是一个拓扑：使用 C^op 作为定义站点。”
*)
Definition Copresheaf_Topos@{o h so} (C : Category@{o h h})
  (UT : Untruncate@{h}) : ElementaryTopos ([C, Sets@{h so}]) :=
  Presheaf_Topos@{o h so} (C^op) UT.

Definition Copresheaf_Topos_IEM@{o h so} (C : Category@{o h h})
  (Em : IEM@{h}) : ElementaryTopos ([C, Sets@{h so}]) :=
  Copresheaf_Topos@{o h so} C (untruncate_of_IEM Em).

(* * ** (B) The five fields, and the two derived objects, read back / * **（B）五个字段，以及两个派生对象，读取回 *)

Section Readback.

(*
 ANNOTATED DELIBERATELY.  Left bare, this [Context] fixes its own
 universes at discharge and every readback that USES it acquires the
 block equation [u0 = u1] -- sixteen of the nineteen below, the three
 exceptions being the whole-bundle readbacks, which bind their own [C]
 and [UT] and so never see this [Context] (measured on the bare
 variant).  The equation is the [Untruncate] universe identified with
 C's hom universe, which the bundles carry in their BINDER instead.
 The
 equation is sound but it would make reading (1) below true only of
 the four bundles' blocks; annotating moves it back into the binder
 and makes the file equation-free throughout.  Measured both ways. 

 --------
 刻意注释。裸露状态下，这个 [Context] 在放电时固定它自己的宇宙，并且每次使用它的回读都会获取方程块 [u0 = u1] —— 下面的十九个中有十六个，三个例外是完整捆绑的回读，它们绑定自己的 [C] 和 [UT]，因此从未看到这个 [Context]（在裸露变体上测量）。该方程是与 C 的同类宇宙对应的 [Untruncate] 宇宙，捆绑则在它们的 BINDER 中携带。该方程是可靠的，但它会使下面的（1）仅对四个捆绑块为真；注释后将其移回 BINDER，并使整个文件无方程。两种方式均已测量。
*)
Universes ro rh rso.
Context (C : Category@{ro rh rh}) (UT : Untruncate@{rh}).

Example psh_topos_terminal :
  @topos_terminal _ (Presheaf_Topos C UT)
  = @Functor_Category_Terminal (C^op) Sets Sets_Terminal := eq_refl.

Example psh_topos_cartesian :
  @topos_cartesian _ (Presheaf_Topos C UT)
  = @Functor_Category_Cartesian (C^op) Sets Sets_Cartesian := eq_refl.

Example psh_topos_pullbacks :
  @topos_pullbacks _ (Presheaf_Topos C UT)
  = @Fun_HasPullbacks (C^op) Sets Sets_HasPullbacks := eq_refl.

Example psh_topos_closed :
  @topos_closed _ (Presheaf_Topos C UT) = Functor_Category_Closed C
  := eq_refl.

Example psh_topos_classifier :
  @topos_classifier _ (Presheaf_Topos C UT) = Fun_Classifier UT := eq_refl.

(* The exponential IS Awodey's display-(8.5) presheaf. This is the issue's reviewer check that it is proved rather than postulated. / 指数是 Awodey 的 display-(8.5) 预层。这是审稿人检查的问题，确保它是被证明的，而不是被假定的。 *)
Example psh_topos_exponent (P Q : C^op ⟶ Sets) :
  @exponent_obj _ _ (@topos_closed _ (Presheaf_Topos C UT)) P Q
  = PshExp P Q := eq_refl.

(* Ω is Awodey's presheaf of sieves, and truth his total sieve. / Ω 是 Awodey 的筛子上预层，而 truth 是他的全集筛子。 *)
Example psh_topos_omega :
  @Ω ([C^op, Sets]) _ (@topos_classifier _ (Presheaf_Topos C UT))
  = Sieve_Presheaf C := eq_refl.

Example psh_topos_truth :
  @truth ([C^op, Sets]) _ (@topos_classifier _ (Presheaf_Topos C UT))
  = sieve_truth C := eq_refl.

(*
 Mac Lane's Axiom 9 object, unfolded: the power object of a presheaf
 is its exponential by Ω. 

 --------
 麦克·莱恩的公理9对象，展开：一个预层的幂对象是它通过 Ω 的指数。
*)
Example psh_topos_pow (P : C^op ⟶ Sets) :
  @Pow ([C^op, Sets]) (Presheaf_Topos C UT) P
  = PshExp P (Sieve_Presheaf C) := eq_refl.

(* The terminal presheaf is the one Instance/Fun/Exponential.v names. / 终端预层是 Instance/Fun/Exponential.v 所命名的那个。 *)
Example psh_terminal_is_donor :
  @topos_terminal _ (Presheaf_Topos C UT) = presheaf_terminal C := eq_refl.

(*
 The chosen pullback is the pointwise one.  The category must be
 written out in the two arrows, or elaboration stalls. 

 --------
 所选择的回拉是逐点回拉。类别必须用两个箭头写出，否则阐述将停滞。
*)
Example psh_pullback_is_donor (F G H : C^op ⟶ Sets)
  (a : F ~{[C^op, Sets]}~> H) (b : G ~{[C^op, Sets]}~> H) :
  @pullback ([C^op, Sets]) (@topos_pullbacks _ (Presheaf_Topos C UT))
    F G H a b
  = Fun_Pullback Sets_HasPullbacks a b := eq_refl.

(* The covariant reading is not a parallel construction: its closed and classifier fields ARE the tree's own covariant donors. / 协变读取不是平行结构：它的封闭和分类字段是树自身的协变供体。 *)
Example copsh_topos_closed :
  @topos_closed _ (Copresheaf_Topos C UT) = Functor_Category_Closed_cov C
  := eq_refl.

Example copsh_topos_classifier :
  @topos_classifier _ (Copresheaf_Topos C UT) = Fun_Classifier_cov UT
  := eq_refl.

(*
 STRONGER THAN THE TWO FIELD READBACKS ABOVE: the covariant reading and
 the contravariant one are the SAME TERM at opposite categories, as
 WHOLE bundles and in both directions, and the [IEM] pair with them.
 [(C^op)^op = C] by conversion is what makes all three [eq_refl]. 

 --------
 比上面两个场读回更强：协变读回和逆变读回在相对类别上是相同的项，无论作为整体捆绑还是在两个方向上，以及与它们配对的 [IEM]。通过转换的 [(C^op)^op = C] 是使所有三个 [eq_refl] 的原因。
*)
Example copsh_is_psh_at_op (C : Category) (UT : Untruncate) :
  Copresheaf_Topos C UT = Presheaf_Topos (C^op) UT := eq_refl.

Example psh_is_copsh_at_op (C : Category) (UT : Untruncate) :
  Copresheaf_Topos (C^op) UT = Presheaf_Topos C UT := eq_refl.

Example copsh_iem_is_psh_iem_at_op (C : Category) (Em : IEM) :
  Copresheaf_Topos_IEM C Em = Presheaf_Topos_IEM (C^op) Em := eq_refl.

(** ** (C) Awodey's three displays / **（C）Awodey 的三个展示 *)

(* “t : 1 → Ω, namely, at each C, the 'total sieve': t_C = {f : · → C}.” / t : 1 → Ω，即，在每个 C 处，“全筛”：t_C = {f : · → C}。 *)
Example psh_truth_is_total_sieve (c : C)
  (u : carrier (fobj[@terminal_obj ([C^op, Sets])
                       (@topos_terminal _ (Presheaf_Topos C UT))] c)) :
  transform[@truth ([C^op, Sets]) _
              (@topos_classifier _ (Presheaf_Topos C UT))] c u
  = @total_sieve C c := eq_refl.

(*
 “u_C(e) = {f : D → C | f*(e) ∈ U(D) ↣ E(D)}”, with the membership
 truncated by [Powerset_squash] -- which is what [Untruncate] inverts.
 The bound variables must be typed as Instance/Fun/Classifier.v types
 its own Example, or the [morphism] coercion is left an evar. 

 --------
 “u_C(e) = {f : D → C | f*(e) ∈ U(D) ↣ E(D)}”，其成员关系被 [Powerset_squash] 截断——而 [Untruncate] 则是对其进行反转的。  
 约束变量必须被类型化为 Instance/Fun/Classifier.v 类型  
 它自己的示例，或者 [morphism] 强制类型转换保留为一个 evar。
*)
Example psh_char_is_awodey_sieve (E U : C^op ⟶ Sets) (theta : U ⟹ E)
  (M : @Monic ([C^op, Sets]) U E theta) (c d : C)
  (e : carrier (fobj[E] c)) (f : d ~{C}~> c) :
  sieve_mem (transform[@char ([C^op, Sets]) _
                         (@topos_classifier _ (Presheaf_Topos C UT))
                         U E theta M] c e) f
  = Powerset_squash (∃ x : carrier (fobj[U] d),
                       transform[theta] d x ≈ fmap[E] f e) := eq_refl.

(* “and given h : D → C let h* : Ω(C) → Ω(D) be defined by: h*(S) = {g : · → D | h ∘ g ∈ S}.” The arrow must be ascribed into [C^op]; see the spelling note in the header. / “并且给定 h : D → C，令 h* : Ω(C) → Ω(D) 定义为： h*(S) = {g : · → D | h ∘ g ∈ S}。” 该箭头必须归入 [C^op]；参见标题中的拼写说明。 *)
Example psh_omega_is_restriction (c d : C) (h : d ~{C}~> c) (S : Sieve c) :
  fmap[@Ω ([C^op, Sets]) _ (@topos_classifier _ (Presheaf_Topos C UT))]
      (h : c ~{C^op}~> d) S
  = sieve_restrict h S := eq_refl.

End Readback.
