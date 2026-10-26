(* * * The indiscrete functor and the right half of Smythe's adjoint string / * * 不离散函子与Smythe伴随串的右半部分 *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Coq.
Require Import Category.Instance.StrictCat.
Require Import Category.Structure.Discrete.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Discrete.Reconstruct.
Require Import Category.Structure.Groupoid.Connected.
Require Import Category.Instance.Cat.Objects.

Generalizable All Variables.

(*
 Book:      Mac Lane, “Categories for the Working Mathematician”,
 Springer GTM 5, 2nd ed., §IV.2 Exercise 9, printed p. 90
 (maclane:IV.2:ex9), where the result is attributed to
 N. Smythe.
 nLab:      https://ncatlab.org/nlab/show/indiscrete+category
 nLab:      https://ncatlab.org/nlab/show/discrete+category
 nLab:      https://ncatlab.org/nlab/show/adjoint+string
 nLab:      https://ncatlab.org/nlab/show/adjoint+triple
 nLab:      https://ncatlab.org/nlab/show/strict+category
 Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

 Mac Lane's exercise asks for the adjoint string carried by the functor
 that sends a category to its set of objects:

 Components  ⊣  Discrete  ⊣  Objects  ⊣  Indiscrete

 Instance/Cat/Objects.v builds the objects functor, settles the two
 categories, and proves the MIDDLE adjunction.  This file builds the
 RIGHT-HAND wing on top of it: the indiscrete (codiscrete, chaotic)
 functor and [StrictCat_Objects ⊣ StrictCat_Indisc].  With the two
 together, three of Mac Lane's four terms are in place and the fourth
 is shown -- there, not here -- not to belong to this string at all
 (item II).

 Delivered here:

 (a) [indisc_lift]: the co-extension of a function [obj[C] → A] to a
 functor [C ⟶ Indiscrete A].  This is the exact mirror of
 Instance/Cat/Objects.v's [disc_ext], and like it, it is what
 the functor's arrow action is BUILT from rather than an extra
 construction: [obj[Indiscrete A]] IS [A] definitionally
 ([indisc_obj_carrier], §4), so [fmap[StrictCat_Indisc] f] is
 literally [indisc_lift f].

 (b) [StrictCat_Indisc : Coq ⟶ StrictCat], the indiscrete functor --
 the ARROW ACTION that the tree's [Indiscrete] object map has
 never had (item I).

 (c) [indisc_adj_iso], the hom-setoid isomorphism, and the packaged
 record [Objects_Indisc_Adjunction], of type
 [StrictCat_Objects ⊣ StrictCat_Indisc].  As on the left wing,
 no analogue arises of the universe wall that
 Instance/Top/Forgetful.v meets for the corresponding [Top]
 triple.  (An earlier revision added “what DOES arise here, and
 does not there, is a [Set] pin inherited from the donor”; that
 pin was removed on 2026-09-17 -- item V.)

 (d) [adjoint_string]: the two adjunctions packaged as one term, so
 that the string is a single artifact rather than two files that
 happen to compile.

 (e) [Indisc_Full] and [Indisc_Faithful]: the indiscrete functor is
 fully faithful, the categorical reading of the fact that the
 COUNIT of this adjunction is the identity function
 ([indisc_counit_is_id], §4) -- the mirror of Objects.v's
 [Disc_Full]/[Disc_Faithful] and of the left wing's unit.

 (f) [disc_indisc_not_iso] and [disc_indisc_not_eq]: the two adjoints
 of the objects functor genuinely differ, and not merely up to
 presentation -- [DiscreteCat bool] and [Indiscrete bool] are not
 isomorphic in [StrictCat].

 (g) [ind_to_disc_constant] and [no_identity_functor_ind_to_disc]:
 why the string stops here on the right, stated at the strength
 it is actually proved (item VII).

 I. A PRIOR-ART CORRECTION, INHERITED AND EXTENDED.

 The catalog issue states that the indiscrete half “has no
 construction at all -- searching for it finds only comments”.  That
 is FALSE, and Instance/Cat/Objects.v's item I already records it:
 Instance/Discrete/Reconstruct.v has declared
 [Indiscrete (A : Type) : Category], with [hom := fun _ _ => unit],
 [homset := Morphism_equality] and every category law discharged by
 the ambient obligation tactic, since it was written.  It is
 CONSUMED here and NOTHING REBUILDS IT -- [StrictCat_Indisc]'s
 [fobj] is that constant by name, and [indisc_obj] records the fact
 by [eq_refl].

 What this file supplies is the part that genuinely was missing, and
 Objects.v states it precisely: [Indiscrete] was an OBJECT MAP ONLY.
 Its three prior consumers -- Theory/Skeleton/Separation.v,
 Instance/Cat/Pullback.v (whose [IB := Indiscrete bool] drives
 [FibreProduct_not_Cat_pullback]) and Instance/Cat/Objects.v:§6
 (whose [SwapI] drives [objects_not_functorial_over_Cat]) -- all
 three use it on OBJECTS alone, and each of the latter two uses it
 for a REFUTATION turning on the same fact, that [Cat] cannot tell
 [true] from [false] there.  No arrow action, no functor and no
 adjunction for it existed anywhere.  Those are (a), (b), (c).

 Three further files match a name search and are NOT consumers, so
 that a later reader repeating the search is not misled:
 Instance/Top.v has an unrelated [Section Indiscrete] about the
 indiscrete TOPOLOGY, and Instance/Top/Forgetful.v and
 Instance/Cat/Components.v mention the word in prose only.

 A SECOND, SMALLER PIECE OF PRIOR ART IS DISCLOSED IN PLACE RATHER
 THAN DUPLICATED SILENTLY: §10's [ind_bool_iso] is
 Theory/Skeleton/Separation.v's [Indiscrete_iso] -- already
 general in both the type and the two points -- specialized at
 [bool].  That module is not required, for a measured reason: it
 would add TEN modules to this file's 49-module closure, among them
 [Instance/Fun.v], which is in neither this closure nor
 [Instance/Cat.v]'s.  The comment at that definition names the
 donor; nothing there is claimed new.

 II. THE DOMAIN IS INHERITED, AND THE CODOMAIN DECISION WAS ALREADY
 PROVED BINDING ON THIS WING.

 Instance/Cat/Objects.v settles both ends by refutation rather than
 by taste, and this file adds nothing to that argument and repeats
 none of it.  The source must be [StrictCat], because
 [objects_not_functorial_over_Cat] refutes the [fmap_respects]
 obligation that an objects functor owes over [Cat] WHEN ITS TARGET
 COMPARES OBJECT MAPS BY LEIBNIZ EQUALITY (an isomorphism-setoid
 objects functor on [Cat] does exist; see that file's §6).  The target
 must be [Coq], because [no_carrier_functor_Sets_StrictCat] refutes
 it for any pointed, injective, natural object map
 [obj[Sets] → obj[StrictCat]] -- and THAT THEOREM IS ALREADY
 INSTANTIATED AT THE INDISCRETE OBJECT MAP THERE, as
 [ind_carrier_not_Sets_functor].  So the right adjoint's codomain
 was fixed before this file existed, and the work of fixing it is
 not redone here.

 CONSEQUENCE FOR THE FOURTH ADJOINT, REPEATED BECAUSE IT IS WHAT
 “as far as it goes” IN §6 MEANS.  [Pi0] (Theory/Connected/
 Components.v) runs [Cat ⟶ Sets] and shares NEITHER end with
 [StrictCat_Objects : StrictCat ⟶ Coq]; by the source refutation it
 cannot be restricted and re-aimed, since there is no objects
 functor over [Cat] to be adjoint to.  So [adjoint_string] has two
 components and not three, and the leftmost adjunction is a
 separate statement over a different pair of categories.

 IT IS NOW A STATEMENT THAT EXISTS.  Instance/Cat/Components.v,
 landed alongside this file, delivers [Pi0 ⊣ Cat_Disc] with
 [Cat_Disc : Sets ⟶ Cat] -- confirming the separation by
 construction rather than by prediction, since its discrete functor
 is not [StrictCat_Disc] and could not be: the two run between
 different categories.  Mac Lane's four terms therefore exist in
 the tree as TWO strings of two, meeting nowhere, and
 [adjoint_string] packages only the pair that shares its
 categories.  NOTHING IN ANY OF THE THREE FILES PROVES that no
 [Coq]-valued π₀ exists; that question is left open in all of
 them.

 NAMING.  [StrictCat_Indisc] is the name Instance/Cat/Objects.v
 reserved for this functor, on the Instance/Top/Forgetful.v
 precedent (prefix = the structured category, whichever way the
 functor runs).  The obvious short names were unavailable there and
 remain so: [Indiscrete] is the category constructor of item I,
 [Discrete] is Structure/Discrete.v's predicate (required here,
 and used once, in [disc_indisc_not_eq]), and [Objects] is
 Solver/Expr.v's reification class.

 III. WHAT IS CONSUMED, AND WHAT IS BUILT.

 CONSUMED, not rebuilt: Instance/Discrete/Reconstruct.v's
 [Indiscrete] and [Indiscrete_bool_Discrete_absurd];
 Instance/Cat/Objects.v's [StrictCat_Objects], [StrictCat_Disc],
 [disc_ext], [Disc_Objects_Adjunction] and [indiscrete_hom_eq] --
 that last one is the little lemma “any two elements of [unit] are
 equal”, declared there for the [Cat] refutation and used here in
 every single obligation, so the two wings share their one piece of
 proof plumbing; Instance/Discrete.v's [DiscreteCat] and
 [DiscreteCat_Discrete]; Structure/Discrete.v's [Discrete];
 Instance/StrictCat.v's [StrictCat] with Theory/Functor.v's
 [Functor_StrictEq_Setoid]; Instance/Coq.v's [Coq];
 Theory/Functor.v's [Build_Functor], [Compose], [Id], [Full] and
 [Faithful]; Theory/Isomorphism.v's [Isomorphism] and
 [iso_to_from]; and Theory/Adjunction.v's [Adjunction],
 [Build_Adjunction'], [unit] and [counit].  Not one category,
 functor or adjunction lemma is re-proved, and no [Cat]-level or
 [Sets]-level refutation is restated.

 BUILT: (a)-(g) above.

 IV. STRENGTHS, MEASURED STRICT-FIRST -- AND THE TWO WINGS COME APART
 HERE, IN THE DIRECTION ONE WOULD NOT GUESS.

 SIXTEEN [Example]s close by [eq_refl].  Twelve of them are general
 readbacks, and the other four are §10's computing witnesses:
 the object action of [StrictCat_Indisc] and the object action of
 its arrow action ([indisc_obj], [indisc_map]); the fact that
 [obj[Indiscrete A]] IS [A] ([indisc_obj_carrier]), which is what
 makes (a) do double duty; both legs of the transposition
 ([adj_to_lifts], [adj_from_forgets]); one of the two round trips
 ([adj_from_to_ind], and note it is the WHOLE record, not merely a
 component); THE COUNIT IS THE IDENTITY FUNCTION ON THE NOSE
 ([indisc_counit_is_id]) and the unit is the identity on objects
 ([unit_obj]) and is [indisc_lift] of the identity as a WHOLE
 FUNCTOR ([unit_is_lift]); the object half of the remaining round
 trip ([rt_obj]); and, one level up, the object and arrow actions
 of [StrictCat_Objects ◯ StrictCat_Indisc] against [Id[Coq]]
 ([comp_obj], [comp_map], §10).

 Everything above is the exact mirror of Instance/Cat/Objects.v's
 §4, with [to] and [from] exchanged: there [to] forgets an arrow
 action and [from] extends, and the round trip that fails is
 [from ∘ to]; here [to] lifts and [from] forgets, and the round trip
 that fails is [to ∘ from].

 THE CAUSE OF THE FAILURE IS NOT THE MIRROR, AND THIS WING COMES
 OUT STRICTLY BETTER AT THE ARROW LEVEL.  On the left wing the
 residue is [fmap_id] and the arrow round trip is [≈]-ONLY.  Here
 it is not a coherence law at all: it is the absence of definitional
 ETA FOR [Datatypes.unit].  [fmap[F] h] inhabits [unit] and the
 round trip produces [tt], and Coq will not identify a variable of
 a one-constructor NON-record inductive with its constructor --
 pinned as [unit_has_no_eta] with [unit_eta_by_destruct] as the
 passing control immediately after.  Consequently
 [rt_map_leibniz] closes the arrow round trip at LEIBNIZ [=] with
 one [destruct], where the left wing reaches only [≈].

 READ THE WHOLE-RECORD NEGATIVE HONESTLY, THOUGH.  It has AT LEAST
 TWO independent causes and only one is isolated: besides the arrow
 field, the three law fields of the rebuilt functor are this file's
 own opaque obligations, and NO probe here separates them.  So
 “eta is the obstruction” is a claim about [rt_map_strict], which is
 pinned, and not about [adj_to_from_ind], which is also pinned but
 whose diagnosis is left incomplete.  The [≈] form is available as
 [adj_to_from_equiv], straight from [iso_to_from].

 The adjunction is packaged through [Build_Adjunction']
 (Theory/Adjunction.v) for the same measured reason as on the
 left wing, though the arithmetic differs: the smart constructor
 asks only for the two [to]-side naturality clauses, which here land
 in [StrictCat] rather than in [Coq] -- but both close with an
 [eq_refl] object family and one [indiscrete_hom_eq], because a
 strict functor equality between two functors into an indiscrete
 category has a coherence field valued in [unit].  The full
 constructor would have demanded the two [from]-side squares as
 well.

 Sharpness is proved rather than asserted, in two places.  §7 shows
 the two adjoints of [StrictCat_Objects] are not isomorphic in
 [StrictCat], so the string's two ends are genuinely different
 functors; and Instance/Cat/Objects.v:§9's [Objects_not_Faithful]
 already shows the middle functor genuinely forgets, so neither
 adjunction is an equivalence in disguise.

 V. UNIVERSES, MEASURED OFF BOTH THE BLOCK AND THE BINDER -- AND THE
 LITERAL THAT USED TO BE IN THE BINDER IS GONE.

 NO CONSTRAINT BLOCK IN THIS FILE CONTAINS A UNIVERSE EQUATION.
 Every entry of every block is a [<] or a [<=]; checked constant by
 constant, not sampled.  Measured now:

 Objects_Indisc_Adjunction@{u u0 u1} :
 StrictCat_Objects@{u u u1 u u1 u1}
 ⊣ StrictCat_Indisc@{u u1 u u1 u u1}        ( * u1 < u * )

 indisc_lift@{u u0 u1} : ∀ {C : Category@{u0 u1 u1}} {A : Type@{u}},
 (obj[C] → A) → Functor@{u0 u1 u1 u u1 u1}

 Indiscrete@{o h p} : Type@{o} → Category@{o h p}

 -- no literal [Set] anywhere, so the adjunction is a statement about
 categories at ANY hom-and-proof level.

 RECORDED CORRECTION, AND IT IS A CONCLUSION, NOT A NUMBER.  An
 earlier revision of this item said the opposite, in terms: “A reader
 who stops there concludes that the adjunction is universe-free, AND
 IS WRONG, because the restriction is spelled in the BINDER as the
 literal [Set]: [Objects_Indisc_Adjunction@{u u0 u1 u2 u3} :
 StrictCat_Objects@{u2 u0 u3 u u3 Set} ⊣ StrictCat_Indisc@{u2 u0 u
 u3}].  The sixth argument of [StrictCat_Objects] is the ambient
 [StrictCat]'s inner hom-and-proof level, and it is [Set] on the
 nose.  So THE ADJUNCTION IS A STATEMENT ABOUT CATEGORIES WHOSE HOM
 AND PROOF UNIVERSES ARE THE LITERAL [Set].”  It attributed the pin
 correctly -- “[Indiscrete@{u} : Type@{u} → Category@{u Set Set}]
 takes ONE universe binder where [Class Category] has three, so its
 hom and proof universes minimize to [Set]”, reaching the source
 through [indisc_lift@{u u0}] over [C : Category@{u0 Set Set}] --
 and it recorded the repair as measured out of tree and deliberately
 not made, because the edit belonged to
 Instance/Discrete/Reconstruct.v.  That edit HAS since been made:
 [Indiscrete] was annotated [@{o h p}] in the PR “algebraic carriers
 are sets” (2026-09-17), and [indisc_adj_iso] here was annotated with
 it, to keep a second minimization the literal had been masking from
 narrowing the theorem.  §8's three formability negatives -- the
 donor, [indisc_lift], [indisc_adj_iso], each formerly reporting
 “Cannot enforce Set = uh” -- are now positive CONTROLS at the same
 levels, and §8 carries a new section for objects declared strictly
 above homs.

 One clause of the old item is withdrawn outright rather than
 updated: it called the pin “a repairable donor defect of the
 [Build_Quiver_Standard_Eq] minimization family that
 Construction/Free/Quiver/Examples.v documents”.  That named the
 wrong family -- [About] put it on [Indiscrete]'s own single binder
 -- and repairing it needed nothing from that file.

 WHAT WAS NEVER PINNED IS THE OBJECT UNIVERSE, and that is still
 guarded ([IndiscreteObjectsFree], §8).  The class the file talks
 about is inhabited at every level now, not only at [Set], which is
 what §7 and §10 are about.

 Two inherited identifications are named rather than repaired, and
 neither is introduced here: [StrictCat] is declared at
 [Category@{u u0 u0}], identifying its OWN hom and proof universes,
 and [Coq]'s own block carries [u0 = u1] and [u0 = u2].  Those are
 claims about those two constants, not about the transitive
 closure, which was not swept.

 VI. AUDIT.  42 constants, ALL CLOSED UNDER THE GLOBAL CONTEXT
 ([Print Module] lists 42 and the file declares no [Record], [Class]
 or [Inductive], so there is no unlisted [Build_*]; each was queried
 by fully qualified name, which is what reaches the 10 [Program]
 obligations a [.glob] sweep cannot see; 32 names are declared in
 the source and 32 + 10 = 42).  ZERO of the 42 collides anywhere in
 the tree, by a sweep of this file's own declared names that allows
 attribute prefixes.  THAT SWEEP FOUND A LIVE COLLISION and it is
 recorded rather than quietly fixed: [counit_is_id] -- the mirror of
 Instance/Cat/Objects.v's [unit_is_id], and the obvious name --
 clashes with Instance/Cat/Components.v, which landed while
 this file was being written; §4's is renamed
 [indisc_counit_is_id].  The hazard is not cosmetic, since the
 [make print-assumptions] gate reads its targets by bare name in a
 single scope.  DISCLOSED IN THE SAME BREATH, AND NOT FIXED HERE
 BECAUSE NEITHER FILE IS THIS ONE: [Disc_Full], [Disc_Faithful] and
 [disc_adj_iso] are each declared BOTH in Instance/Cat/Objects.v
 and in Instance/Cat/Components.v, at different types over
 different categories.  FOUR [Fail] probes, all of ONE kind --
 CONVERSION, three in §4 and one in §10 -- each stripped once and
 its kind read off the whole error message, beside an instrument
 check and EIGHTEEN positive controls: twelve [Check]s in §8 (eight
 in [IndiscreteSetPin], two in the objects-free section, two in the
 objects-above-homs one) and six passing [Example]s standing beside
 the §4 and §10 negatives ([rt_obj], [rt_map_leibniz],
 [adj_to_from_equiv], [unit_eta_by_destruct], [comp_obj] and
 [comp_map]).

 RECORDED CORRECTION.  An earlier revision counted “SEVEN [Fail]
 probes ... four CONVERSION (three in §4, one in §10) and three
 FORMABILITY (all in §8)” and “THIRTEEN positive controls: seven
 [Check]s in §8 (five in the pinning section, two in the
 objects-free one)”.  The three FORMABILITY negatives turned over
 when [Indiscrete] was annotated in the PR “algebraic carriers are
 sets” (2026-09-17) and are now controls, and a third §8 section was
 added; that is the whole difference.  The same revision also said
 of the two section-local [Constraint] declarations, tested by
 DELETION, that “the one in [IndiscreteSetPin] is INERT” -- its
 three negatives still refusing byte-identically with the line
 removed, since what they fired on was the donor's literal [Set]
 meeting a rigid declared level.  There are
 no negatives in that section any more, so that measurement no
 longer applies and was NOT re-run; §8 records why the [Constraint]
 is kept.  The one in [IndiscreteObjectsFree] is unchanged and
 meaning-giving (its [Check]s pass either way, but without it the
 levels could collapse and would demonstrate nothing).  Neither is
 load-bearing in the sense of Instance/Cat/Objects.v's middle
 section, and this is recorded because a reader who assumes a
 [Constraint] does work would be wrong both times here.
 Rename-simulated 5/5 on an UNPADDED denominator -- the constants a
 NEGATIVE names, which are [Indiscrete] and [StrictCat_Objects]
 (renamed throughout, simulating a donor rename) and [indisc_lift],
 [StrictCat_Indisc] and [indisc_adj_iso] (renamed at the definition
 site only, since a whole-file rename of a file-local constant is a
 no-op and would score a false pass) -- every one of them breaking
 the file at a non-[Fail] line.

 VII. WHAT IS NOT DELIVERED.

 No [Components ⊣ StrictCat_Disc] and no [Coq]-valued π₀ -- the
 leftmost adjunction exists, in Instance/Cat/Components.v, but over
 [Cat] and [Sets], so it does not extend [adjoint_string] and is not
 cited as doing so.  Item II records why [Pi0] cannot join this
 string, and records equally that no impossibility is proved for a
 differently-built π₀.  So [adjoint_string] is a string of THREE
 functors, not Mac Lane's four, and it does not claim otherwise.

 NO PROOF THAT THE STRING STOPS ON THE RIGHT.  §9 proves the fact
 the expectation rests on -- every functor from an indiscrete
 category to a discrete one is CONSTANT ([ind_to_disc_constant]),
 so no such functor is the identity on [bool]
 ([no_identity_functor_ind_to_disc]).  That is NOT a refutation of
 [StrictCat_Indisc ⊣ StrictCat_Objects]: an adjunction supplies a
 hom-setoid isomorphism whose two legs are arbitrary setoid maps,
 and nothing here forces either leg to be [fobj], so the counting
 argument one would want does not follow from §9 alone.  No such
 refutation is attempted and none is claimed.

 No uniqueness statement for either adjoint; no naturality of
 [indisc_adj_iso] in [C] or [A] beyond the two clauses
 [Build_Adjunction'] consumes; no (co)monad on either side and hence
 nothing about idempotency; no statement that [StrictCat_Indisc] is
 a coreflective embedding (the tree's reflectivity vocabulary,
 Construction/Reflective.v, is stated over subcategories rather than
 over an arbitrary fully faithful right adjoint, and no bridge is
 built); no preservation, reflection or creation of limits, in
 particular nothing about [StrictCat_Objects] preserving them from
 both sides; no comparison of [StrictCat_Indisc] with
 Instance/Top/Forgetful.v's [Top_Indiscrete] beyond the remark in
 (c); no relation between this [Indiscrete] and Instance/Top.v's
 unrelated [Section Indiscrete] on the indiscrete TOPOLOGY; no
 annotated ([Set]-free) restatement of anything (SUPERSEDED: since
 the PR “algebraic carriers are sets”, 2026-09-17, [indisc_adj_iso]
 IS annotated and every constant here is [Set]-free, because the
 donor was; see item V); and no
 diagnosis of the whole-record negative beyond the one field
 isolated in item IV. 

 --------
 书籍： Mac Lane，《为在职数学家准备的范畴论（Categories for the Working Mathematician）》，Springer GTM 5，第2版，§IV.2 练习 9，第90页印刷版（maclane:IV.2:ex9），结果归因于 N. Smythe。
 nLab: https://ncatlab.org/nlab/show/indiscrete+category
 nLab: https://ncatlab.org/nlab/show/discrete+category
 nLab: https://ncatlab.org/nlab/show/adjoint+string
 nLab: https://ncatlab.org/nlab/show/adjoint+triple
 nLab: https://ncatlab.org/nlab/show/strict+category
 Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

 Mac Lane 的练习要求求出由将一个范畴映射到其对象集合的函子所携带的伴随串：

 Components ⊣ Discrete ⊣ Objects ⊣ IndiscreteInstance/Cat/Objects.v 构建了对象函子，确定了两个范畴，并证明了 MIDDLE 伴随。这个文件在其基础上构建了右侧翼：非离散（共离散、混乱）函子和 [StrictCat_Objects ⊣ StrictCat_Indisc]。结合这两者，Mac Lane 的四个项中有三个已经就位，第四个已显示——在那里，而不是在这里——根本不属于这个序列（项目 II）。

 这里提供：

 (a) [indisc_lift]：函数 [obj[C] → A] 的共扩展到函子 [C ⟶ Indiscrete A]。这与 Instance/Cat/Objects.v 的 [disc_ext] 完全相对应，并且像它一样，它是从中构建函子箭头作用的基本方式，而不是额外的构造：[obj[Indiscrete A]] 定义上是 [A]（[indisc_obj_carrier]，第4节），所以 [fmap[StrictCat_Indisc] f] 实际上是 [indisc_lift f]。(b) [StrictCat_Indisc : Coq ⟶ StrictCat]，不离散函子——树的 [Indiscrete] 对象映射从未具有的 ARROW ACTION（项 I）。

 (c) [indisc_adj_iso]，同态集合等价同构，以及类型为 [StrictCat_Objects ⊣ StrictCat_Indisc] 的封装记录 [Objects_Indisc_Adjunction]。如同左翼，没有类似于 Instance/Top/Forgetful.v 对应 [Top] 三元组遇到的宇宙墙的情况。（早期修订加入了“这里出现而那里没有出现的是来自捐赠者的 [Set] 插针”；该插针于 2026-09-17 被移除——项 V。）

 (d) [adjoint_string]：两个伴随关系封装为一个术语，使得该字符串是单个工件，而不是碰巧能编译的两个文件。(e) [Indisc_Full] 和 [Indisc_Faithful]：不离散函子是全忠的，这是从范畴角度阅读该伴随函子的余单元是恒等函数（[indisc_counit_is_id], §4）——相当于 Objects.v 的 [Disc_Full] / [Disc_Faithful] 以及左翼单元的镜像。

 (f) [disc_indisc_not_iso] 和 [disc_indisc_not_eq]：对象函子的两个伴随函子确实不同，而不仅仅是呈现上的差异——[DiscreteCat bool] 和 [Indiscrete bool] 在 [StrictCat] 中不是同构的。

 (g) [ind_to_disc_constant] 和 [no_identity_functor_ind_to_disc]：为什么右侧的字符串在此处停止，按其强度陈述时实际上已被证明（第VII项）。

 I. 先前技术的修正，继承并扩展。目录问题指出，不连续的一半“根本没有构造——搜索它只会找到注释”。这是错误的，Instance/Cat/Objects.v 的条目 I 已经记录了它：Instance/Discrete/Reconstruct.v 已经声明了 [Indiscrete (A : Type) : Category]，并且有 [hom := fun _ _ => unit]、[homset := Morphism_equality] 以及由环境义务策略解除的每一个范畴定律，自它编写以来。这在这里被消耗，并且没有任何东西重建它——[StrictCat_Indisc] 的 [fobj] 就是按名称的那个常数，而 [indisc_obj] 通过 [eq_refl] 记录了这个事实。这个文件提供的正是之前真正缺失的部分，而 Objects.v 精确地说明了这一点：[Indiscrete] 只是一个对象映射。它之前的三个使用者——Theory/Skeleton/Separation.v、Instance/Cat/Pullback.v（其中 [IB := Indiscrete bool] 驱动 [FibreProduct_not_Cat_pullback]）以及 Instance/Cat/Objects.v:§6（其中 [SwapI] 驱动 [objects_not_functorial_over_Cat]）——全部三个仅在对象上使用它，并且后两个中的每一个都将其用于基于同一事实的反驳，即 [Cat] 不能区分那里 [true] 和 [false]。不存在任何箭头作用、函子或伴随。它们就是 (a)、(b)、(c)。另外三个文件匹配名称搜索且不是消费者，因此以后重复搜索的读者不会被误导：
 Instance/Top.v 有一个关于非离散拓扑的无关 [Section Indiscrete]，
 而 Instance/Top/Forgetful.v 和 Instance/Cat/Components.v 仅在文章中提到该词。一个第二个、更小的现有技术片段是在原位披露的，而不是默默地复制：§10 的 [ind_bool_iso] 是 Theory/Skeleton/Separation.v 的 [Indiscrete_iso] ——在类型和两个点上已经是通用的——在 [bool] 处被专门化。这个模块不是必需的，有一个经过衡量的理由：它会给这个文件的 49 个模块闭包增加十个模块，其中包括 [Instance/Fun.v]，而它既不在这个闭包中，也不在 [Instance/Cat.v] 的闭包中。该定义处的注释标明了来源；那里什么都没有被宣称为新发明。

 II. 该域是继承的，而且余域决策已被证明对这一分支具有约束力。Instance/Cat/Objects.v 通过反驳而不是通过品味来解决两端问题，而这个文件对该论证没有任何添加，也没有重复其中的内容。源必须是 [StrictCat]，因为 [objects_not_functorial_over_Cat] 反驳了 [fmap_respects] 的义务，即对象函子在 [Cat] 上对其目标进行比较对象映射时应遵守的义务（在 [Cat] 上确实存在一个同构-等价类对象函子；见该文件的§6）。目标必须是 [Coq]，因为 [no_carrier_functor_Sets_StrictCat] 对任何有指点的、单射的、自然的对象映射 [obj[Sets] → obj [StrictCat] 都予以反驳 —— 并且该定理已经在那里的非离散对象映射上被实例化，作为 [ind_carrier_not_Sets_functor]。因此右伴随函子的余域在此文件存在之前就已固定，而固定它的工作在这里没有重新进行。对于第四个伴随的结果，重复是因为它正是§6中“就其本身而言”所意味着的。[Pi0]（理论/连通/分量.v）运行[Cat ⟶ Sets]，并且与[StrictCat_Objects : StrictCat ⟶ Coq]没有共享端点；根据源驳论，它不能被限制和重新指向，因为不存在可与[Cat]伴随的对象函子。因此[adjoint_string]有两个分量而不是三个，最左边的伴随是另一个关于不同类别对的独立陈述。它现在是一个已存在的陈述。Instance/Cat/Components.v 文件与此文件一起出现，提供了 [Pi0 ⊣ Cat_Disc] 和 [Cat_Disc : Sets ⟶ Cat] —— 通过构造而不是预测来确认分离，因为其离散函子不是 [StrictCat_Disc]，也不可能是：两者运行在不同的范畴之间。因此，Mac Lane 的四个项在树中以两个两项的形式存在，互不相交，而 [adjoint_string] 只打包共享其范畴的那一对。三个文件中的任何内容都不能证明不存在 [Coq] 值的 π₀；这个问题在它们中都仍然开放。命名。[StrictCat_Indisc] 是 Instance/Cat/Objects.v 中的 functor 保留名称，用于 Instance/Top/Forgetful.v 中的前例（前缀 = 结构化类别，无论 functor 如何运行）。显而易见的简短名称在那里不可用，并且仍然不可用：[Indiscrete] 是项目 I 的类别构造器，[Discrete] 是 Structure/Discrete.v 的谓词（此处需要，并且在 [disc_indisc_not_eq] 中使用了一次），[Objects] 是 Solver/Expr.v 的具现类。

 III. 消耗什么，以及构建什么。消耗，而不是重建：Instance/Discrete/Reconstruct.v 的 [Indiscrete] 和 [Indiscrete_bool_Discrete_absurd]；Instance/Cat/Objects.v 的 [StrictCat_Objects]、[StrictCat_Disc]、[disc_ext]、[Disc_Objects_Adjunction] 和 [indiscrete_hom_eq]——最后一个是小引理“[unit] 的任意两个元素相等”，在那里为 [Cat] 否定声明，并在此处每个命题中使用，因此两翼共享它们的一段证明管道；Instance/Discrete.v 的 [DiscreteCat] 和 [DiscreteCat_Discrete]；Structure/Discrete.v 的 [Discrete]；Instance/StrictCat.v 的 [StrictCat] 与 Theory/Functor.v 的 [Functor_StrictEq_Setoid]；Instance/Coq.v 的 [Coq]；Theory/Functor.v 的 [Build_Functor]、[Compose]、[Id]、[Full] 和 [Faithful]；Theory/Isomorphism.v 的 [Isomorphism] 和 [iso_to_from]；以及 Theory/Adjunction.v 的 [Adjunction]、[Build_Adjunction']、[unit]和[counit]。没有重新证明任何类别、函子或伴随引理，也没有重述 [Cat] 级或 [Sets] 级的反驳。

 已构建：（a）-（g）如上。

 四、优点，以严格优先方式测量 —— 在这里，两翼分开，方向出乎意料。十六 [Example] 接近 [eq_refl] 。其中十二个是通用回读，另外四个是§10的计算见证：[StrictCat_Indisc]的对象动作及其箭头动作（[indisc_obj]，[indisc_map]）；[obj[Indiscrete A]是[A]（[indisc_obj_carrier]），这正是使(a)双重作用的原因；换位的两个部分（[adj_to_lifts]，[adj_from_forgets]）；两次往返中的一个（[adj_from_to_ind]，注意这是整个记录，而不仅仅是一个组成部分）；伴随余单位是鼻子上的恒等函数（[indisc_counit_is_id]），单位是对象上的恒等（[unit_obj]），并且是整体函子恒等的[indisc_lift]（[unit_is_lift]）；剩余往返的对象部分（[rt_obj]）；以及再上一层，[StrictCat_Objects ◯ StrictCat_Indisc]对[Id[Coq]的对象和箭头动作。]([comp_obj]，[comp_map]，第10条)。以上所有内容完全对应于 Instance/Cat/Objects.v 的 §4，只是将 [to] 和 [from] 互换：在那里 [to] 忘记了一个箭头操作，而 [from] 扩展，失败的往返是 [from ∘ to]；这里 [to] 提升，而 [from] 忘记，失败的往返是 [to ∘ from]。失败的原因不是镜像，并且这只翼在箭头级别上出的严格更好。在左翼上，残余是 [fmap_id]，箭头往返是 [≈] - 仅此而已。在这里，它根本不是相干律：它是 [Datatypes.unit] 定义性 ETA 的缺失。[fmap[F] h] 居住在 [unit] 中，往返产生 [tt]，而 Coq 不会将单构造非记录归纳变量识别为其构造函数——被固定为 [unit_has_no_eta]，并且 [unit_eta_by_destruct] 作为之后立即控制传递。因此，[rt_map_leibniz] 在 LEIBNIZ [=] 上关闭箭头往返，其中有一个 [destruct]，而左翼只到达 [≈]。然而，请诚实地阅读整个记录的负面信息。它至少有两个独立的原因，而只有一个是孤立的：除了箭头字段之外，重建函子的三个法则字段是此文件自身的不透明义务，并且这里没有探测能将它们分开。所以“eta 是阻塞”是关于 [rt_map_strict] 的声明，它是固定的，而不是关于 [adj_to_from_ind] 的声明，后者也是固定的，但其诊断尚未完成。[≈] 形式可作为 [adj_to_from_equiv] 使用，直接来源于 [iso_to_from]。该伴随通过 [Build_Adjunction'] （Theory/Adjunction.v）打包，理由与左翼相同，尽管算术不同：智能构造器只要求两个 [to] 侧的自然性条款，这里落在 [StrictCat] 而不是 [Coq] ——但两者都以一个 [eq_refl] 对象族和一个 [indiscrete_hom_eq] 结尾，因为两个函子进入一个不可分类别之间的严格函子等式具有一个值域在 [unit] 中的相干性字段。完整构造器还会要求两个 [from] 侧的方格。锐度通过证明而非断言，在两个地方得以体现。§7显示 [StrictCat_Objects] 的两个伴随在 [StrictCat] 中并非同构，因此这个字符串的两端确实是不同的函子；而 Instance/Cat/Objects.v:§9 的 [Objects_not_Faithful] 已经表明中间的函子确实会遗忘，因此没有一个伴随是伪装的等价。  

 V. 宇宙，同时从块和绑定器进行测量——而原来在绑定器中的字面内容已经消失。  

 此文件中的任何约束块都不包含宇宙方程。每块的每一项都是 [<] 或 [<=]；逐个常量检查，而非抽样。当前测量值:Objects_Indisc_Adjunction@{u u0 u1} :
 StrictCat_Objects@{u u u1 u u1 u1}
 ⊣ StrictCat_Indisc@{u u1 u u1 u u1}        ( * u1 < u * )

 indisc_lift@{u u0 u1} : ∀ {C : Category@{u0 u1 u1}} {A : Type@{u}},
 (obj [C] → A) → Functor@{u0 u1 u1 u u1 u1}

 Indiscrete@{o h p} : Type@{o} → Category@{o h p}

 -- 在任何地方都没有字面上的 [Set]，因此该伴随关系关于任意同态和证明等级的范畴。已记录更正，这是一种结论，而不是一个数字。该条目的早期修订版在措辞上表示相反：“停在这里的读者会得出附加项是无界的结论，这是错误的，因为该限制在绑定器中被拼写为字面意义的 [Set] ：[Objects_Indisc_Adjunction@{u u0 u1 u2 u3} ：StrictCat_Objects@{u2 u0 u3 u u3 Set} ⊣ StrictCat_Indisc@{u2 u0 u u3}]。[StrictCat_Objects] 的第六个参数是环境 [StrictCat] 的内部同态和证明层级，并且它在精确上是 [Set]。”因此，该附加是关于其同态和证明宇宙是字面上的 [Set] 的类别的陈述。它正确地归因了引脚 ——“[Indiscrete@{u} : Type@{u} → Category@{u Set Set}] 仅取一个宇宙绑定，而 [Class Category] 有三个，因此其同态和证明宇宙最小化为 [Set]”，通过 [indisc_lift@{u u0}] 经过 [C : Category@{u0 Set Set}] 到达源 —— 并且它记录了修复为树外测量且故意未完成，因为该编辑属于 Instance/Discrete/Reconstruct.v。该编辑此后已完成：[Indiscrete] 在 PR “代数载体是集合”（2026-09-17）中被标注为 [@{o h p}]，并且此处的 [indisc_adj_iso] 也进行了标注，以保留字面上所掩盖的第二次最小化，从而不收窄定理。§8 的三个可形成性负项——捐赠者、[indisc_lift]、[indisc_adj_iso]，之前报告“无法强制执行 Set = uh”——现在在相同级别上都是正控制，并且 §8 增加了一个新部分，用于严格声明在 hom 之上的对象。

 旧条目的一个条款已被完全撤回，而不是更新：它称该销钉为“[Build_Quiver_Standard_Eq] 最小化家族的可修复捐赠者缺陷，Construction/Free/Quiver/Examples.v 已文档记录”。这命名了错误的家族——[About] 将它放在 [Indiscrete] 的单独绑定器上——而修复它根本不需要那个文件。从未固定的是对象宇宙，这仍然受到保护（[IndiscreteObjectsFree]，第8节）。文件中讨论的类现在在每一个层次上都有实例，而不仅仅是在[Set]，这正是第7节和第10节的内容。

 两个继承的标识被命名而不是修复，并且这里没有引入：[StrictCat] 在 [Category@{u u0 u0}] 处声明，确定其 OWN hom 和 proof 宇宙；而 [Coq] 自己的块包含 [u0 = u1] 和 [u0 = u2]。这些是关于这两个常量的断言，而不是关于传递闭包的断言，后者尚未被清理。VI. 审计。42 个常量，在全局上下文中全部封闭（[Print Module] 列出了 42 个，并且文件未声明 [Record]、[Class] 或 [Inductive]，所以没有未列出的 [Build_*]；每个都通过完全限定名进行查询，这正是达到 10 个 [Program] 义务时 [.glob] 扫描无法看到的；源文件中声明了 32 个名字，32 + 10 = 42）。在树中的任何地方，这 42 个名字都没有碰撞，通过对该文件自己声明的名字进行扫描，并允许属性前缀。该扫描发现了一个实时碰撞，并记录下来而不是悄悄修复：[counit_is_id] —— Instance/Cat/Objects.v 的 [unit_is_id] 的镜像，以及显而易见的名字 —— 与 Instance/Cat/Components.v 冲突，该文件在编写时已添加；第 §4 节的名称已重命名为 [indisc_counit_is_id]。这种危险不是表面上的，因为[make print-assumptions]门在单个作用域中通过裸名称读取其目标。同一时间披露，但在此未修复，因为这些文件都不是这个文件：[Disc_Full]、[Disc_Faithful]和[disc_adj_iso]分别在Instance/Cat/Objects.v和Instance/Cat/Components.v中声明，且在不同类别上具有不同类型。四个 [Fail] 探针，都是同一种——转换型，§4 中三个，§10 中一个——每个都剥离一次，并读取整个错误信息中的种类，旁边有一个仪器检查和十八个阳性对照：十二个 [Check] 在 §8（八个在 [IndiscreteSetPin] 中，两个在无对象部分，两个在对象在同源上方部分）以及六个通过的 [Example] 站在 §4 和 §10 阴性旁边（[rt_obj]、[rt_map_leibniz]、[adj_to_from_equiv]、[unit_eta_by_destruct]、[comp_obj] 和 [comp_map]）。已记录更正。早期的修订中统计了“七个 [Fail] 探针……四个转换（§4 中三个，§10 中一个）和三个可成形性（全部在 §8）”以及“十三个阳性对照：§8 中七个 [Check]（在插针部分五个，在无对象部分两个）”。当 [Indiscrete] 在 PR 中被注释为“代数载体是集合”（2026-09-17）时，三个可成形性阴性变为正对照，并且增加了第三个 §8 部分；这就是全部差异。同一修订还提到，对于通过删除测试的两个段落局部 [Constraint] 声明，“在 [IndiscreteSetPin] 中的那个是惰性的”——它的三个否定仍然以完全相同的方式拒绝响应，与删除该行时相同，因为它们触发的是捐赠者的字面 [Set] 与严格声明的级别相符。该段落中不再有否定项，因此该测量不再适用，也未重新进行；§8 记录了为什么保留 [Constraint]。在 [IndiscreteObjectsFree] 中的那个保持不变并具有意义（它的 [Check] 可以任意通过，但没有它，级别可能会崩溃，并且不会展示任何内容）。都不是  
 在 Instance/Cat/Objects.v 的中间部分意义上的承重，这一点被记录下来，因为假设 [Constraint] 能工作的人在这里两次都会错。重命名模拟在未填充的分母上 5/5——常量是负名，分别是 [Indiscrete] 和 [StrictCat_Objects]（在整个过程中重命名，模拟捐赠者重命名）以及 [indisc_lift]、[StrictCat_Indisc] 和 [indisc_adj_iso]（仅在定义位置重命名，因为对文件本地常量进行整个文件的重命名是无操作的，会产生错误通过）——每一个都会在非 [Fail] 行使文件出错。  

 VII. 未交付的内容。没有 [Components ⊣ StrictCat_Disc] 也没有 [Coq] -值的 π₀ -- 最左边的伴随存在于 Instance/Cat/Components.v 中，但在 [Cat] 和 [Sets] 上，所以它不能扩展 [adjoint_string]，也没有被引用为这样做。条目 II 记录了为什么 [Pi0] 无法加入该序列，并同样记录了对于一个不同构建的 π₀ 没有证明不可能性。因此 [adjoint_string] 是三个函子的序列，而不是 Mac Lane 的四个，并且它没有声称相反。没有证据表明该串在右侧停止。 §9 证明了期望所依据的事实——从无散列范畴到离散范畴的每个函子都是恒定的（[ind_to_disc_constant]），因此没有这样的函子在 [bool] 上是恒等的（[no_identity_functor_ind_to_disc]）。这并不是对 [StrictCat_Indisc ⊣ StrictCat_Objects] 的驳斥：一个伴随提供了一个同态集等价同构，它的两条边是任意的集合等价映射，这里没有任何东西强制任一边为 [fobj]，因此人们想要的计数论证并不能仅从 §9 推出。没有尝试这样的驳斥，也没有声称存在。两个伴随都没有唯一性声明；[indisc_adj_iso]在[C]或[A]中的自然性也没有超出[Build_Adjunction']所包含的两个分句；两边都没有（余）模范，因此关于幂等性也没有任何信息；没有声明[StrictCat_Indisc]是一个共反射嵌入（树的反射词汇，Construction/Reflective.v，是在子类别上声明的，而不是在任意完全忠实的右伴随上声明的，也没有建立桥梁）；没有极限的保持、反射或创造，尤其是关于[StrictCat_Objects]从两边保持它们没有说明；[StrictCat_Indisc]与Instance/Top/Forgetful.v的[Top_Indiscrete]的比较除了(c)中的备注外没有说明；这个[Indiscrete]与Instance/Top.v中在不离散拓扑上的无关[Section Indiscrete]之间没有关系。POLOGY；没有注释（[Set]-自由）的任何重述（已废止：自2026-09-17的PR“代数承载是集合”以来，[indisc_adj_iso] 已注释，并且这里的每个常量都是[Set]-自由的，因为捐赠者是；见V项）；并且除了在IV项中单独指出的字段外，没有对整个记录的消极情况进行诊断。
*)

(* * ** §1. The indiscrete co-extension / * ** §1. 非离散的共延伸 *)

(*
 A function [f : obj[C] → A] co-extends to a functor into the
 indiscrete category on [A]: an object goes to its image, and a
 morphism goes to the only morphism there is.  This is the exact
 mirror of Instance/Cat/Objects.v:§1's [disc_ext], and like it, all
 three functor laws are equations in [unit] and close by that file's
 own [indiscrete_hom_eq].

 Unlike [disc_ext] it carries NO universe binders.  RECORDED CORRECTION
 to the reason: an earlier revision said “the reason is not that it is
 better behaved but that there is nothing left to bind: [Indiscrete] has
 already fixed the target's hom and proof universes at [Set], and
 [Functor] then forces the SOURCE's to agree.  Item V and §8 measure
 that; it is the one place this wing is worse off than the left one.”
 [Indiscrete] fixes nothing since its annotation in the PR “algebraic
 carriers are sets” (2026-09-17), and measured now
 [indisc_lift@{u u0 u1}] is over [C : Category@{u0 u1 u1}] with the
 target at [Functor@{u0 u1 u1 u u1 u1}] -- free, and no worse off than
 the left wing.  The absence of binders here is therefore inherited
 freedom rather than a pin, and adding them was not attempted.

 A SECOND CORRECTION: the same revision added “A [Program Definition]
 cannot be annotated here in any case, since its obligations mint fresh
 universes.”  That is FALSE, and Instance/Discrete.v's annotated
 [Program Definition DiscreteCat_Functor@{o h p uo uh up +}] is the
 counterexample: a trailing [+] allows exactly the universes the
 obligations mint.  The [refine] is kept for the narrower reason that it
 mints none, again following the donor. 

 --------
 一个函数  [f : obj[C] → A] 可以扩展为一个函子进入  [A] 上的不离散范畴：一个对象映射到它的像，一个态射映射到唯一的态射。这正好是 Instance/Cat/Objects.v:§1 中  [disc_ext] 的镜像，并且像它一样，所有三个函子律都是  [unit] 中的方程，并且由该文件自身的  [indiscrete_hom_eq] 闭合。与 [disc_ext] 不同，它不携带任何宇宙绑定器。已记录更正: 原因的早期修订说“原因不是它表现得更好，而是没有剩下的东西可以绑定：[Indiscrete] 已经在 [Set] 固定了目标的 hom 和证明宇宙，然后 [Functor] 强制源的一致。项目 V 和 §8 测量了这一点；这是这一翼比左翼更差的唯一地方。”[Indiscrete] 没有固定任何东西，因为其在 PR 中的注释“代数载体是集合”（2026-09-17），现在测量 [indisc_lift@{u u0 u1}] 位于 [C : Category@{u0 u1 u1}] 上，目标在 [Functor@{u0 u1 u1 u u1 u1}] ——自由，并且不比左翼更差。因此这里绑定器的缺失是继承的自由而不是钉锁，也未尝试添加它们。第二次修正：同样的修订增加了“在任何情况下这里都不能注释 A [Program Definition]，因为它的义务会开创新的宇宙。”这是错误的，而 Instance/Discrete.v 中注释的 [Program Definition DiscreteCat_Functor@{o h p uo uh up +}] 就是反例：一个尾随的 [+] 刚好允许义务所开创的宇宙。保留 [refine] 的原因较狭窄，因为它没有开创新的宇宙，这同样遵循了原作者的做法。
*)
Definition indisc_lift {C : Category} {A : Type} (f : obj[C] -> A)
  : C ⟶ Indiscrete A.
Proof.
  unshelve refine (@Build_Functor C (Indiscrete A) f
                     (fun _ _ _ => tt) _ _ _).
  - intros x y f1 g1 H. apply indiscrete_hom_eq.
  - intros x. apply indiscrete_hom_eq.
  - intros x y z g1 h1. apply indiscrete_hom_eq.
Defined.

(** ** §2. The indiscrete functor / ** §2. 非离散函子 *)

(*
 [Indiscrete] on objects, and [indisc_lift] on arrows -- the arrow
 action is not a second construction, because [obj[Indiscrete A]] IS
 [A] ([indisc_obj_carrier], §4), so a [Coq]-morphism [A ~> B] already
 has the type [indisc_lift] wants.  §3's mirror on the left wing is
 Objects.v's [fmap := fun A B f => disc_ext f].

 ONE obligation remains, [fmap_respects]; [fmap_id] and [fmap_comp]
 are discharged by the ambient tactic, since a strict functor equality
 between two functors into an indiscrete category has an [eq_refl]
 object family and a coherence field valued in [unit]. 

 --------
 [Indiscrete] 在对象上，以及 [indisc_lift] 在箭头上——箭头操作不是第二种构造，因为 [obj[Indiscrete A] ] 是 [A] ([indisc_obj_carrier]，第4节)，所以一个 [Coq]-态射 [A ~> B] 已经具有 [indisc_lift] 所需的类型。第3节在左翼的镜像是 Objects.v 的 [fmap := fun A B f => disc_ext f]。

 一个义务仍然存在，[fmap_respects]；[fmap_id] 和 [fmap_comp] 已经由环境策略解决，因为两个函数到一个杂乱类别之间的严格函子等式具有一个 [eq_refl] 对象族和一个值在 [unit] 中的连贯场。
*)
Program Definition StrictCat_Indisc : Coq ⟶ StrictCat := {|
  fobj := Indiscrete;
  fmap := fun A B (f : A ~{Coq}~> B) => indisc_lift (C := Indiscrete A) f
|}.
Next Obligation.
  intros f g H. exists H. intros a b e. apply indiscrete_hom_eq.
Defined.

(** ** §3. The adjunction / ** §3. 附加 *)

(*
 The transposition, and the whole content is that a functor INTO an
 indiscrete category IS its object map: [to] co-extends and [from]
 forgets the arrow action.  On the left wing the two are exchanged --
 there [to] forgets and [from] extends -- which is why the round trip
 that survives on the nose is the other one (§4).

 Two obligations remain, that [to] respects [≈] and one round trip;
 the other round trip and [from]'s [Proper] certificate are discharged
 by the ambient tactic, which is already the strict/[≈] split §4
 measures. 

 --------
 换位，以及整体内容是，一个函子进入一个无差别范畴就是它的对象映射：[to] 扩展，而 [from] 忘记箭头作用。在左翼，两者交换——在那里 [to] 忘记，而 [from] 扩展——这就是为什么在原样上存活的完整往返是另一个 (§4)。

 剩下两个义务，即 [to] 尊重 [≈] 和一个完整往返；另一个完整往返以及 [from] 的 [Proper] 证书由环境策略解除，该策略已经是严格/[≈] 分裂 §4 测量。
*)
(*
 THE [StrictCat] INSTANCE IS WRITTEN OUT, AND THE LAST TWO BINDERS ARE
 THE POINT.  [StrictCat@{u u0 u1 co ch} : Category@{u u0 u0}] has the
 INNER category's object level [co] and hom-and-proof level [ch] as its
 fourth and fifth arguments, and nothing in this definition relates
 them.  Left implicit, universe minimization identifies them, and the
 adjunction then applies only to categories whose objects and homs sit
 at one level.  That was invisible while [Indiscrete] was pinned at
 [Category@{u Set Set}] -- [ch] was then the literal [Set] and [co] was
 free by construction -- and it became visible the moment [Indiscrete]
 was annotated (Instance/Discrete/Reconstruct.v, PR “algebraic
 carriers are sets”, 2026-09-17).  Naming the instance keeps both free,
 so §8's two sections can exhibit homs strictly above [Set] AND objects
 strictly above homs.  The trailing [+] allows the universes
 [Program]'s obligations mint. 

 --------
 [StrictCat] 实例已经被写出，最后两个绑定器是重点。[StrictCat@{u u0 u1 co ch} : Category@{u u0 u0}] 的第四和第五个参数分别是 INNER 类别的对象层级 [co] 和同态及证明层级 [ch]，这一定义中没有任何内容将它们关联。未明确指定时，宇宙最小化会识别它们，然后该附加操作只应用于对象和同态位于同一层级的类别。当 [Indiscrete] 被固定在 [Category@{u Set Set}] 时，这一点是不可见的——[ch] 那时是字面上的 [Set]，而 [co] 根据构造是自由的——当 [Indiscrete] 被注释时它就变得可见（Instance/Discrete/Reconstruct.v，PR “代数承载体是集合”，2026-09-17）。命名该实例会保持两者自由，因此第8节的两个部分可以展示严格高于 [Set] 的同态，以及严格高于同态的对象。尾随的 [+] 允许宇宙 [Program] 的义务铸造。
*)
Program Definition indisc_adj_iso@{u u0 u1 co ch +}
  (C : obj[StrictCat@{u u0 u1 co ch}]) (A : obj[Coq]) :
  @Isomorphism Sets
    {| carrier := @hom Coq (StrictCat_Objects C) A
     ; is_setoid := @homset Coq (StrictCat_Objects C) A |}
    {| carrier := @hom StrictCat C (StrictCat_Indisc A)
     ; is_setoid := @homset StrictCat C (StrictCat_Indisc A) |} := {|
  to   := {| morphism := fun (f : obj[C] -> A) => indisc_lift f |};
  from := {| morphism := fun (F : C ⟶ Indiscrete A) => fobj[F] |}
|}.
Next Obligation.
  intros f g H. exists H. intros a b e. apply indiscrete_hom_eq.
Defined.
Next Obligation.
  exists (fun _ => eq_refl). intros a b e. apply indiscrete_hom_eq.
Defined.

(*
 Mac Lane's right-hand adjunction.  Both naturality clauses close with
 an [eq_refl] object family and one [indiscrete_hom_eq], for the reason
 §2's comment gives.  [Build_Adjunction'] (Theory/Adjunction.v)
 asks only for the two [to]-side clauses; see item IV. 

 --------
 麦克莱恩的右手伴随。两个自然性条款都以一个 [eq_refl] 对象族和一个 [indiscrete_hom_eq] 结束，原因如 §2 的评论所示。[Build_Adjunction']（Theory/Adjunction.v）只要求两个 [to] 侧的条款；见项目 IV。
*)
Definition Objects_Indisc_Adjunction :
  StrictCat_Objects ⊣ StrictCat_Indisc.
Proof.
  unshelve eapply Build_Adjunction'.
  - exact indisc_adj_iso.
  - intros C D A f g. exists (fun _ => eq_refl).
    intros a b e. apply indiscrete_hom_eq.
  - intros C A B f g. exists (fun _ => eq_refl).
    intros a b e. apply indiscrete_hom_eq.
Defined.

(** ** §4. Strengths, strict first / ** §4. 优势，先严格 *)

Example indisc_obj (A : obj[Coq]) :
  fobj[StrictCat_Indisc] A = Indiscrete A := eq_refl.

Example indisc_obj_carrier (A : obj[Coq]) :
  obj[Indiscrete A] = A := eq_refl.

Example indisc_map (A B : obj[Coq]) (f : A ~{Coq}~> B) (x : A) :
  fobj[fmap[StrictCat_Indisc] f] x = f x := eq_refl.

Example adj_to_lifts (C : obj[StrictCat]) (A : obj[Coq])
  (f : StrictCat_Objects C ~{Coq}~> A) :
  to (indisc_adj_iso C A) f = indisc_lift f := eq_refl.

Example adj_from_forgets (C : obj[StrictCat]) (A : obj[Coq])
  (F : C ~{StrictCat}~> StrictCat_Indisc A) :
  from (indisc_adj_iso C A) F = fobj[F] := eq_refl.

Example adj_from_to_ind (C : obj[StrictCat]) (A : obj[Coq])
  (f : StrictCat_Objects C ~{Coq}~> A) :
  from (indisc_adj_iso C A) (to (indisc_adj_iso C A) f) = f := eq_refl.

Example indisc_counit_is_id (A : obj[Coq]) (a : A) :
  @counit _ _ _ _ Objects_Indisc_Adjunction A a = a := eq_refl.

Example unit_obj (C : obj[StrictCat]) (x : C) :
  fobj[@unit _ _ _ _ Objects_Indisc_Adjunction C] x = x := eq_refl.

Example unit_is_lift (C : obj[StrictCat]) :
  @unit _ _ _ _ Objects_Indisc_Adjunction C
    = indisc_lift (fun x : obj[C] => x) := eq_refl.

Fail Example adj_to_from_ind (C : obj[StrictCat]) (A : obj[Coq])
  (F : C ~{StrictCat}~> StrictCat_Indisc A) :
  to (indisc_adj_iso C A) (from (indisc_adj_iso C A) F) = F := eq_refl.

Example rt_obj (C : obj[StrictCat]) (A : obj[Coq])
  (F : C ~{StrictCat}~> StrictCat_Indisc A) (x : C) :
  fobj[to (indisc_adj_iso C A) (from (indisc_adj_iso C A) F)] x
    = fobj[F] x := eq_refl.

Fail Example rt_map_strict (C : obj[StrictCat]) (A : obj[Coq])
  (F : C ~{StrictCat}~> StrictCat_Indisc A) (x y : C) (h : x ~> y) :
  fmap[to (indisc_adj_iso C A) (from (indisc_adj_iso C A) F)] h
    = fmap[F] h := eq_refl.

Example rt_map_leibniz (C : obj[StrictCat]) (A : obj[Coq])
  (F : C ~{StrictCat}~> StrictCat_Indisc A) (x y : C) (h : x ~> y) :
  fmap[to (indisc_adj_iso C A) (from (indisc_adj_iso C A) F)] h
    = fmap[F] h.
Proof. apply indiscrete_hom_eq. Qed.

Example adj_to_from_equiv (C : obj[StrictCat]) (A : obj[Coq])
  (F : C ~{StrictCat}~> StrictCat_Indisc A) :
  to (indisc_adj_iso C A) (from (indisc_adj_iso C A) F) ≈ F.
Proof. exact (iso_to_from (indisc_adj_iso C A) F). Qed.

Fail Example unit_has_no_eta (u : Datatypes.unit) : u = tt := eq_refl.

Example unit_eta_by_destruct (u : Datatypes.unit) : u = tt.
Proof. now destruct u. Qed.

(* * ** §5. The indiscrete functor is fully faithful / * ** §5. 非离散函子是全忠的 *)

(*
 Which is what “the counit is the identity” (§4) says categorically.
 Faithfulness costs NOTHING -- injectivity of [fmap[StrictCat_Indisc]]
 is the first projection of a strict functor equality, and the ambient
 tactic finds it.  Fullness costs exactly the round trip of §4, taken
 at [≈]: the preimage of [G] is [fobj[G]], and [iso_to_from] says the
 co-extension of that is [G] again. 

 --------
 这正是“余单位是恒等”（§4）明确说明的内容。  
 忠实性不花任何代价——[fmap[StrictCat_Indisc] 的单射性是严格函子等式的第一个投影，而且环境策略可以找到它。  
 丰满性确切地花费了 §4 的往返路径，在 [≈] 处：[G] 的原像是 [fobj[G]，而 [iso_to_from] 表示其余扩仍然是 [G]。
*)
#[export] Program Instance Indisc_Faithful : Faithful StrictCat_Indisc.

#[export] Program Instance Indisc_Full : Full StrictCat_Indisc := {|
  prefmap := fun A B (G : StrictCat_Indisc A ~{StrictCat}~> StrictCat_Indisc B)
              => fobj[G]
|}.
Next Obligation.
  exact (iso_to_from (indisc_adj_iso (StrictCat_Indisc x) y) g).
Defined.

(* * ** §6. The adjoint string, as far as it goes / * ** §6. 伴随弦，尽可能地 *)

(*
 Three of Mac Lane's four functors, and the two adjunctions between
 them, as ONE term -- so that the string is an artifact rather than two
 files that happen to compile.  It has two components and not three,
 and item II says why: the fourth adjoint lives over a different pair
 of categories, and Instance/Cat/Components.v now proves it there.
 Nothing here claims Mac Lane's full string is in the tree. 

 --------
 Mac Lane 的四个函子中的三个，以及它们之间的两个伴随关系，作为一个整体术语——这样这个串就是一个整体，而不是碰巧可以编译的两个文件。它有两个组成部分，而不是三个，第二项说明了原因：第四个伴随函子位于另一对范畴上，而 Instance/Cat/Components.v 现在在那里证明了它。这里没有声明 Mac Lane 的完整串在树中。
*)
Definition adjoint_string :
  (StrictCat_Disc ⊣ StrictCat_Objects)
    * (StrictCat_Objects ⊣ StrictCat_Indisc) :=
  (Disc_Objects_Adjunction, Objects_Indisc_Adjunction).

(* * ** §7. The two adjoints of the objects functor genuinely differ / * ** §7. 对象函子的两个伴随函子确实不同 *)

(*
 The engine, one line: a morphism of a DISCRETE category is an
 equality proof, and an indiscrete category supplies a morphism
 between any two objects, so the image of [tt] IS the equation. 

 --------
 引擎，一行：离散范畴的一个态射就是一个等式证明，而非离散范畴在任意两个对象之间提供一个态射，因此  [tt] 的像就是这个方程。
*)
Lemma ind_to_disc_constant {A B : Type}
  (F : Indiscrete A ⟶ DiscreteCat B) (x y : A) : fobj[F] x = fobj[F] y.
Proof. exact (fmap[F] (tt : x ~{Indiscrete A}~> y)). Qed.

Theorem disc_indisc_not_iso :
  @Isomorphism StrictCat (DiscreteCat bool) (Indiscrete bool) -> False.
Proof.
  intro I.
  destruct (iso_to_from I) as [eo _]. simpl in eo.
  pose proof (f_equal (fobj[to I]) (ind_to_disc_constant (from I) true false))
    as H.
  rewrite (eo true), (eo false) in H.
  discriminate.
Qed.

Theorem disc_indisc_not_eq :
  StrictCat_Disc bool = StrictCat_Indisc bool -> False.
Proof.
  intro H.
  refine (Indiscrete_bool_Discrete_absurd _).
  exact (eq_rect _ Discrete (DiscreteCat_Discrete bool) _ H).
Qed.

(** ** §8. The universe boundary / ** §8. 宇宙边界 *)

(* Instrument check: [Fail] is live in this file. / 仪器检查：[Fail] 在此文件中处于活动状态。 *)
Fail Definition probe_instrument_live : Datatypes.unit := 0.

(*
 The former [Set] pin of [Indiscrete], and its propagation -- first into
 this file's own [indisc_lift], then into the adjunction.

 RECORDED CORRECTION.  An earlier revision stated this section as THREE
 NEGATIVES and read:

 “The [Set] pin of [Indiscrete], guarded rather than merely measured,
 and then tracked as it propagates -- first into this file's own
 [indisc_lift], then into the adjunction.

 READ THE [Constraint] CORRECTLY: IT IS INERT FOR ALL THREE
 NEGATIVES, AND THAT WAS MEASURED BY DELETION RATHER THAN ASSUMED.
 Removing the line leaves all three [Fail]s failing with
 byte-identical messages, because what they fire on is the donor's
 LITERAL [Set] meeting the RIGID declared level [uh], not a relation
 declared between them.”

 The three negatives were: [Indiscrete] refused at
 [Type@{uo} -> Category@{uo uh uh}]; [indisc_lift] refused over [C],
 with the gloss “NO annotation of [indisc_lift] can free it, because the
 pin reaches the SOURCE as well”; and [indisc_adj_iso] refused in
 consequence.

 ALL THREE ARE NOW ACCEPTED, and that gloss was the one thing measured
 wrongly.  No annotation of [indisc_lift] could free it, true -- but an
 annotation of [Indiscrete] could, and did: [Indiscrete@{o h p}]
 (Instance/Discrete/Reconstruct.v, PR “algebraic carriers are sets”,
 2026-09-17) is [Set]-free, so the bound [Functor] puts on the source's
 hom universe is now a bound by a free level rather than by the literal
 [Set], and the whole propagation chain travels.  All three commands are
 kept as positive controls at exactly the levels that used to refuse
 them, so dropping the annotation refuses them again and breaks this
 file.

 The first line is also a GUARD ON THE ARITY: written [Indiscrete@{uo}]
 before, it would now be a universe-instance-length error and a [Fail]
 on it would have passed vacuously.  It is written with all three
 levels.

 [Constraint Set < uh] is kept: what it buys is the CONTENT of the
 section, which is only interesting above [Set].  (Instance/Cat/
 Objects.v's §8 carries the parallel correction for its own [SetPin]
 section, and records beside it a [Constraint] that IS load-bearing on
 a negative that remains, so the distinction is not academic.) 

 --------
 前 [Set] 引脚的 [Indiscrete]，以及它的传播 —— 首先进入这个文件自身的 [indisc_lift]，然后进入附加部分。

 已记录的更正。早期的修订将这一部分描述为三个负数，并写道：

 “[Indiscrete] 的 [Set] 引脚，受保护而不仅仅是测量，然后跟踪它的传播 —— 首先进入这个文件自身的 [indisc_lift]，然后进入附加部分。

 正确读取 [Constraint]：它在所有三个负数中都是惰性的，并且这是通过删除测量的而非假定的。删除这一行会使三个 [Fail] 都以字节相同的消息失败，因为它们触发的是捐赠者的字面 [Set] 与刚性声明级别 [uh] 的匹配，而不是它们之间声明的关系。”三个否定是：[Indiscrete] 在 [Type@{uo} -> Category@{uo uh uh}] 被拒；[indisc_lift] 在 [C] 被拒，附注“[indisc_lift] 没有注释能将其释放，因为引脚也到达源”；以及 [indisc_adj_iso] 因此被拒。现在三者都被接受了，而那个注释是唯一一个测量错误的。没有对 [indisc_lift] 的注释可以解放它，确实如此——但是对 [Indiscrete] 的注释可以，并且确实解放了它：[Indiscrete@{o h p}]（Instance/Discrete/Reconstruct.v，PR“代数载体是集合”，2026-09-17）是 [Set] 自由的，所以 [Functor] 对源的 hom 宇的约束现在是由一个自由层次施加的，而不是由字面 [Set] 施加的，并且整个传播链能够传递。所有三个命令都被保留为正向控制，恰好在以前拒绝它们的层次，因此删除注释会再次拒绝它们，并破坏这个文件。第一行也是一个关于元数的保护：写作 [Indiscrete@{uo}] 以前，它现在将是一个宇宙实例长度错误，而在它上面的 [Fail] 将会无效地通过。它以三层级全部写出。

 [Constraint Set < uh] 被保留：它提供的是章节的内容，这只有在 [Set] 之上才有趣。（Instance/Cat/Objects.v 的 §8 为它自己的 [SetPin] 部分提供了相应的修正，并在旁边记录了一个 [Constraint]，它在仍然存在的负值上是承重的，所以这种区别并非纯理论。）
*)
Section IndiscreteSetPin.
  Universes uo uh.
  Constraint Set < uh.
  Context (C : Category@{uo uh uh}) (A : Type@{uo}).

  (* Controls: the ambient, the left wing, and the two shapes. / 控制：环境、左翼和两个形状。 *)
  Check (C : obj[StrictCat]).
  Check (fmap[StrictCat_Objects] (Id[C])).
  Check (@disc_ext@{uo uh uh uo}).
  Check (DiscreteCat@{uo uh uh} A).
  Check (@indisc_lift (DiscreteCat@{uo Set Set} A) A).

  (* 1: the donor reaches these levels. / 1：捐赠者达到这些水平。 *)
  Check (Indiscrete@{uo uh uh} : Type@{uo} -> Category@{uo uh uh}).

  (* 2: so does the lift built over it ... / 2: 由它建造的电梯也是如此... *)
  Check (@indisc_lift C A).

  (* 3: ... and so, therefore, does the adjunction. / 3: ……因此，伴随也如此。 *)
  Check (@indisc_adj_iso C A).
End IndiscreteSetPin.

(*
 The OBJECT universe is free of the hom universe, and stays so.

 RECORDED CORRECTION to what this section was FOR.  An earlier revision
 read: “What is NOT pinned: the OBJECT universe.  The restriction is
 exactly 'hom and proof universes are the literal [Set]', and objects
 may sit anywhere above it -- so the adjunction is a statement about a
 real class of categories rather than about [Set]-sized ones.”  There is
 no longer any [Set] restriction to soften: §8 above now exhibits the
 whole wing at homs strictly ABOVE [Set].  What this section measures
 instead is the independence that survived the repair, and it is kept
 because that independence was nearly LOST in it: with [Indiscrete]
 annotated, [indisc_adj_iso]'s implicit [StrictCat] instance minimized
 its inner object and hom levels TOGETHER, which no [Set] had been
 allowed to do while [ch] was the literal [Set].  Writing that instance
 out at §3 keeps them apart, and this section is the guard on that: the
 [Check]s below are refused if the binders at [indisc_adj_iso] are ever
 dropped.

 The [Constraint] here is neither inert nor load-bearing: the two
 [Check]s pass with or without it (measured by deletion), and what the
 declaration buys is the CONTENT of the controls -- without it [wo]
 could collapse to [Set] and the commands would demonstrate nothing.
 Stated so that a later reader does not delete it as redundant.

 The second section pushes the same point one step further and needs no
 [Set] at all: homs strictly above [Set] AND objects strictly above the
 homs, neither identified with the other. 

 --------
 OBJECT 宇宙不包含 hom 宇宙，并且保持如此。对本节内容目的的已记录更正。早期修订版写道：“未固定的内容：对象宇宙。限制正是‘hom 和 proof 宇宙是字面上的 [Set]’，对象可以位于其之上的任何位置——因此附加项是关于一类实际范畴的陈述，而不是关于 [Set] 尺寸的范畴。” 不再有任何 [Set] 限制需要放宽：上面的第8节现在展示了严格位于 [Set] 之上的整个翅膀。本节测量的不是其他，而是修复后依然存在的独立性，这种独立性得以保留，因为它几乎在修复中丧失：在标注了 [Indiscrete] 的情况下，[indisc_adj_iso] 的隐含 [StrictCat] 实例将其内部对象和层级一起最小化，而在 [ch] 作为字面 [Set] 时，没有任何 [Set] 被允许这样做。在第 §3 节中写出该实例可以将它们分开，而本节则是对此的保护：如果在 [indisc_adj_iso] 的绑定器被删除，下面的 [Check] 将被拒绝。这里的 [Constraint] 既不是惰性的，也不是承重的：两个 [Check] 无论有无它都能通过（通过删除来衡量），而声明所提供的是控件的内容——没有它 [wo] 可能会缩减为 [Set]，并且命令将无法显示任何东西。这样表述是为了让以后的读者不会将其删除为多余的。

 第二部分将同样的观点进一步推进一步，并且根本不需要 [Set]：homs 严格高于 [Set]，并且对象严格高于 homs，它们彼此不被识别为同一。
*)
Section IndiscreteObjectsFree.
  Universes wo.
  Constraint Set < wo.
  Context (C : Category@{wo Set Set}) (A : Type@{wo}).
  Check (@indisc_lift C A).
  Check (@indisc_adj_iso C A).
End IndiscreteObjectsFree.

Section IndiscreteObjectsAboveHoms.
  Universes vo vh.
  Constraint Set < vh.
  Constraint vh < vo.
  Context (C : Category@{vo vh vh}) (A : Type@{vo}).
  Check (@indisc_lift C A).
  Check (@indisc_adj_iso C A).
End IndiscreteObjectsAboveHoms.

(* * ** §9. Where the string stops on the right / * ** §9. 弦在右边停止的位置 *)

(*
 WHY one expects [StrictCat_Indisc ⊣ StrictCat_Objects] to fail, and
 NOT a proof that it does -- read the two apart, since only the first
 is established here.  §7's [ind_to_disc_constant] says every functor
 out of an indiscrete category into a discrete one is constant; so the
 identity map of [bool] is the object map of NO such functor, while it
 is of course one of four functions [bool → bool].  A counting
 argument from that to the non-existence of an adjunction would need
 the transposition's two legs to BE [fobj] and its inverse, and an
 [Adjunction] supplies only a pair of arbitrary setoid maps, so
 nothing here forces that.  No refutation is attempted and none is
 claimed; item VII repeats the caveat where a reader will meet it. 

 --------
 为什么有人期望 [StrictCat_Indisc ⊣ StrictCat_Objects] 会失败，而不是证明它会失败——将两者分开阅读，因为这里只建立了前者。§7 的 [ind_to_disc_constant] 表示从离散类别到一个离散类别的每个函子都是常数；所以 [bool] 的恒等映射不是任何这样的函子的对象映射，而它当然是四个函数 [bool → bool] 之一。从这个出发到伴随不存在的计数论证需要换位的两个腿是 [fobj] 及其逆，而 [Adjunction] 只提供了一对任意的集合同构映射，因此这里没有什么强制要求。没有进行反驳，也没有声称进行反驳；第 VII 项重复了读者将遇到的警告。
*)
Theorem no_identity_functor_ind_to_disc
  (F : Indiscrete bool ⟶ DiscreteCat bool)
  (H : forall b : bool, fobj[F] b = b) : False.
Proof.
  pose proof (ind_to_disc_constant F true false) as K.
  rewrite (H true), (H false) in K. discriminate.
Qed.

(** ** §10. Non-vacuity / ** §10. 非空性 *)

(*
 The composite [Objects ◯ Indisc] returns [Id[Coq]]'s DATA on the nose
 -- object action and arrow action both by [eq_refl] -- which is what
 “the counit is the identity” (§4) says one level up.  The whole record
 is REFUTED, and the cause is the usual one: [Compose] rebuilds
 [fmap_respects], [fmap_id] and [fmap_comp] as its own opaque proofs.
 So this is a CONVERSION negative about the law fields, with the two
 data fields as its passing controls. 

 --------
 复合体 [Objects ◯ Indisc] 精确返回 [Id[Coq] 的 DATA
 -- 对象操作和箭头操作均由 [eq_refl] 执行 -- 这正是“余单位是恒等” (§4) 在上一级所说的。整条记录被驳回，原因是通常的那种：[Compose] 将 [fmap_respects]、[fmap_id] 和 [fmap_comp] 重建为它自己的不透明证明。所以这是关于律字段的 CONVERSION 负性，其两个数据字段作为其传递控制。
*)
Example comp_obj (A : obj[Coq]) :
  fobj[StrictCat_Objects ◯ StrictCat_Indisc] A = A := eq_refl.

Example comp_map (A B : obj[Coq]) (f : A ~{Coq}~> B) (x : A) :
  fmap[StrictCat_Objects ◯ StrictCat_Indisc] f x = f x := eq_refl.

Fail Example comp_is_id :
  StrictCat_Objects ◯ StrictCat_Indisc = Id[Coq] := eq_refl.

(*
 [Indiscrete bool] is not degenerate in either direction: it has two
 provably DISTINCT objects, and they are nonetheless isomorphic, which
 is what “indiscrete” means and what [DiscreteCat bool] provably is
 not (§7).  So the witnesses below are not applied to a one-object
 category, and the adjunction is not being exercised at a shape where
 its content evaporates. 

 --------
 [Indiscrete bool] 在任一方向上都不是退化的：它有两个可证明不同的对象，尽管如此，它们仍然是同构的，这就是“不可离散”的意思，也是 [DiscreteCat bool] 可证明不是的情况 (§7)。所以下面的证据不是应用于只有一个对象的范畴，且这个伴随并没有在其内容消失的形状上被使用。
*)
Example ind_bool_objs_distinct : (true : Indiscrete bool) = false -> False.
Proof. discriminate. Qed.

(*
 PRIOR ART, disclosed rather than duplicated silently: this is
 Theory/Skeleton/Separation.v's [Indiscrete_iso] -- which is already
 general in the type and the two points -- specialized at [bool].  That
 module is NOT required, for a measured reason rather than taste:
 through [Theory/Skeleton.v] it would add TEN modules to this file's
 49-module closure ([Construction/Quotient.v],
 [Construction/Subcategory.v], [Instance/Fun.v], [Instance/One.v],
 [Instance/Two.v], the three [Theory/Equivalence*] files,
 [Theory/Skeleton.v] and [Theory/Skeleton/Separation.v] itself), and
 [Instance/Fun.v] in particular is in neither this closure nor
 [Instance/Cat.v]'s.  Nothing here is claimed new. 

 --------
 现有技术，公开而非默默复制：这是 Theory/Skeleton/Separation.v 的 [Indiscrete_iso]——它在类型和两个点上已经是一般性的——在 [bool] 上进行了专门化。该模块不是必需的，这是出于一个有根据的理由而非个人喜好：通过 [Theory/Skeleton.v]，它将为这个文件的 49 个模块闭包 添加十个模块（[Construction/Quotient.v]、[Construction/Subcategory.v]、[Instance/Fun.v]、[Instance/One.v]、[Instance/Two.v]、三个 [Theory/Equivalence*] 文件、[Theory/Skeleton.v] 以及 [Theory/Skeleton/Separation.v] 本身），而 [Instance/Fun.v] 尤其不在这个闭包中，也不在 [Instance/Cat.v] 的闭包中。这里没有任何内容被声明为新颖。
*)
(*
 Issue #357 work item 5 asks for two sanity checks.  The first --
 components of a discrete category are its objects -- is
 [pi0_counit_iso] in Instance/Cat/Components.v.  This is the second:
 the indiscrete category on a two-element set is CONNECTED.  It is
 pure instantiation of Structure/Groupoid/Connected.v's
 [arrow_connected] at the unique arrow, every hom of [Indiscrete]
 being [unit] -- so no zig-zag induction is performed here. 

 --------
 第357号问题工作项5要求进行两个合理性检查。第一个——离散范畴的组成部分是它的对象——在 Instance/Cat/Components.v 中是 [pi0_counit_iso]。第二个是：一个二元素集合上的不可分范畴是连通的。它是 Structure/Groupoid/Connected.v 中 [arrow_connected] 在唯一箭头上的纯实例化，每个 [Indiscrete] 的同态都是 [unit] ——因此这里没有执行之字形归纳。
*)

(*
 THE SHARED-MIDDLE READING COSTS NOTHING, AND THAT IS MEASURED.

 RECORDED CORRECTION.  An earlier revision read: “THE SHARED-MIDDLE
 READING COSTS A [Set] PIN, AND THAT IS MEASURED.  At its DEFAULT
 universe instance [adjoint_string] does NOT print with one
 [StrictCat_Objects]: the two occurrences elaborate at different
 instances, the second carrying a literal [Set].  So 'the two links
 share their middle term' is true only at a shared instance, and the
 shared instance pins an inner level to [Set] -- inherited from
 [Indiscrete], as §4 records.”  It then checked
 [adjoint_string@{b a Set a a b a Set}], an EIGHT-universe instance with
 two literal [Set]s.

 Half of that still holds and half does not.  At its default instance
 [adjoint_string] still elaborates its two [StrictCat_Objects]
 occurrences at DIFFERENT instances -- it is now
 [adjoint_string@{u u0 u1 u2 u3 u4}], six universes, the left link at
 [{u0 u1}] and the right at [{u3 u4}] with [u1 < u0] and [u4 < u3] --
 so the shared-middle reading is still a statement about a shared
 INSTANCE and not about the default one.  What is gone is the price:
 [Indiscrete] was annotated (Instance/Discrete/Reconstruct.v, PR
 “algebraic carriers are sets”, 2026-09-17), so no [Set] appears in the
 shared instance at all.  The check below identifies the two middles on
 the nose -- both print [StrictCat_Objects@{a a b a b b}] -- with the
 hom level [b] declared strictly ABOVE [Set] and the object level [a]
 strictly above [b].  Measured, not asserted. 

 --------
 共享中间读取不花费任何费用，并且这是可以衡量的。

 记录的更正。之前的修订稿写道：“共享中间读取花费一个 [Set] 引脚，并且这是可以衡量的。在其默认的宇宙实例 [adjoint_string] 中，不会打印带有一个 [StrictCat_Objects] 的内容：这两个出现点在不同实例中展开，第二个携带一个文字 [Set]。因此‘这两个链接共享它们的中间项’仅在共享实例中为真，并且共享实例将一个内部层级固定为 [Set]——继承自 [Indiscrete]，如第4节所记录。”然后它检查了 [adjoint_string@{b a Set a a b a Set}]，一个具有两个文字 [Set] 的八宇宙实例。这一半仍然成立，而另一半则不成立。在其默认实例中，[adjoint_string] 仍然展开其两个 [StrictCat_Objects] 出现在不同实例——现在它是 [adjoint_string@{u u0 u1 u2 u3 u4}] ，六个宇宙，左侧链接在 [{u0 u1}] ，右侧在 [{u3 u4}] 以及 [u1 < u0] 和 [u4 < u3] ——因此共享中间的读法仍然是关于共享的实例，而不是关于默认实例。消失的是代价：[Indiscrete] 已被注释（Instance/Discrete/Reconstruct.v，PR “代数承载体是集合”，2026-09-17），因此在共享实例中完全没有出现 [Set] 。下面的检查准确标识了两个中间——两者都打印 [StrictCat_Objects@{a a b a b b}] ——同态层级 [b] 被声明为严格高于 [Set] ，对象层级 [a] 严格高于 [b] 。这是测量值，而不是断言。
*)

Section SharedMiddle.
Universes a b c d.
Constraint Set < b.
Constraint b < a.
Check adjoint_string@{c a b d a b}.
End SharedMiddle.

Definition ind_bool_connected : Connected (Indiscrete bool) :=
  @arrow_connected (Indiscrete bool) (fun _ _ => tt).

Program Definition ind_bool_iso :
  @Isomorphism (Indiscrete bool) true false := {| to := tt; from := tt |}.

(*
 The transposition computes.  By [adj_to_lifts] the forward leg IS
 [indisc_lift], so these evaluate the adjunction's own [to] at a
 non-identity function. 

 --------
 换位进行计算。由 [adj_to_lifts] 得出前向支是 [indisc_lift]，因此这些在非恒等函数上计算了附加本身的 [to]。
*)
Example neg_lift_true :
  fobj[indisc_lift (C := DiscreteCat bool) negb] true = false := eq_refl.

Example neg_lift_false :
  fobj[indisc_lift (C := DiscreteCat bool) negb] false = true := eq_refl.

Example counit_bool (b : bool) :
  @counit _ _ _ _ Objects_Indisc_Adjunction bool b = b := eq_refl.

Example unit_disc_bool (b : bool) :
  fobj[@unit _ _ _ _ Objects_Indisc_Adjunction (DiscreteCat bool)] b = b
  := eq_refl.
