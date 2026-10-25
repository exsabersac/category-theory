Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Instance.One.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Cartesian.
Require Import Category.Instance.Fun.Terminal.

Open Scope category_scope.

Generalizable All Variables.

(* * * Exponentials of presheaves: [C^op, Sets] is cartesian closed / * * 预层的指数：[C^op, Sets] 是笛卡尔闭的 *)

(*
 Book:      Awodey, Category Theory (1st ed., Carnegie Mellon
 pre-print, September 2005), §8.7 "Exponentials in
 categories of diagrams", display (8.5) and Proposition
 8.13, printed p. 208, and Theorem 8.14, printed p. 209
 ([awodey:8.7:def-presheaf-exponential], [awodey:8.7:prop13],
 [awodey:8.7:thm14]).  Verbatim, from the rendered pages:

 "If we had such an exponential Q^P, we could compute its
 value at any object C ∈ C by Yoneda:

 Q^P(C) ≅ Hom(yC, Q^P)

 And if it's to be an exponential, then we must also
 have:

 Hom(yC, Q^P) ≅ Hom(yC × P, Q)

 But this latter set does exist.  Thus, we can just
 define:

 Q^P(C) = Hom(yC × P, Q)                      (8.5)

 with the action on h : C' → C being:

 Q^P(h) = Hom(yh × 1_P, Q)

 This is clearly a contravariant, set-valued functor on
 C.  Let us now check that it indeed gives an exponential
 of P and Q."

 "Proposition 8.13.  For any objects X, P, Q in Sets^{C^op},
 there is an isomorphism, natural in X,

 Hom(X, Q^P) ≅ Hom(X × P, Q)"

 "Theorem 8.14.  For any small category C, the category of
 diagrams Sets^{C^op} is cartesian closed."

 Book:      Riehl, Category Theory in Context, 2nd ed., §4.4,
 printed pp. 152-153 ([riehl:4.4:lem11]).  Verbatim:

 "Lemma 4.4.11.  For any small category C, the functor
 category Set^C is cartesian closed."

 "Proof.  Given functors F, G : C → Set our aim is to
 define a functor G^F : C → Set so that there is a
 natural bijection between sets of natural
 transformations

 (4.4.12)          {H × F ⇒ G} ≅ {H ⇒ G^F}

 for all functors H : C → Set.  To define the value of
 G^F on an object c, we define

 (4.4.13)   G^F(c) := {C(c, −) × F ⇒ G} ≅ {C(c, −) ⇒ G^F}

 so that the desired bijection can be given by the Yoneda
 lemma."

 "There is a formal reason why the natural bijection
 (4.4.12) follows from the special case (4.4.13) (see
 Exercise 6.5.iii) but this bijection can also be
 demonstrated directly by providing formulas for adjoint
 transposition."

 "Given α : H × F ⇒ G, its transpose is the natural
 transformation β : H ⇒ G^F defined for c ∈ C and x ∈
 Hc by declaring β_c(x) : C(c, −) × F ⇒ G to be the
 natural transformation whose component at d ∈ D is the
 function that takes f : c → d and z ∈ Fd to the element
 α_d((H f)x, z).  These operations can be seen to be
 natural in all of the variables mentioned and inverses."

 Book:      Riehl, ibid., §6.5 Exercise 6.5.iii, printed p. 248
 ([riehl:6.5:exiii]).  Verbatim:

 "Exercise 6.5.iii.  Use Theorem 6.5.7 to give a second
 proof of Lemma 4.4.11, showing that the desired natural
 isomorphism follows from the definition of the internal
 hom."

 nLab:      https://ncatlab.org/nlab/show/exponential+object
 nLab:      closed+monoidal+structure+on+presheaves (same site), which
 states exactly [X,Y](c) = Hom(y(c) × X, Y)
 Wikipedia: https://en.wikipedia.org/wiki/Cartesian_closed_category

 WHAT IS DELIVERED.  [Functor_Category_Closed C], an [#[export]
 Program Instance] of type

 @Closed ([C^op, Sets])
 (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian)

 for an ARBITRARY category C -- at the universe levels measured below,
 which is where Awodey's word "small" lands -- together with
 [presheaf_exp_iso], Proposition 8.13 as an isomorphism of hom-setoids
 in [Sets], and [to_exp_natural_X] / [from_exp_natural_X], its
 naturality in X in both directions.  The exponential object is the
 display-(8.5) formula and nothing else: [PshExp_obj P Q c] IS the
 hom-setoid of the presheaf category at the representable-times-P, and
 [exp_obj_is_display85] reads that back at [eq_refl].

 The terminal half is #339's and is NOT rebuilt: [presheaf_terminal] is
 [Functor_Category_Terminal Sets_Terminal] specialised to [C^op] and
 [Sets], with [presheaf_terminal_is_donor] reading that back at
 [eq_refl].  With [Functor_Category_Cartesian] for binary products,
 that is Theorem 8.14's first clause in this library's own vocabulary.

 Riehl's Set^C is the COVARIANT functor category and Awodey's
 Sets^{C^op} is the contravariant one; here the passage between them
 costs no proof, since [(C^op)^op = C] holds by [eq_refl] in this tree,
 so [Functor_Category_Closed_cov] is [Functor_Category_Closed] at the
 opposite category supplied by [:=] with no tactic and no transport.
 It is annotated like the instance, and measured to sit at the same
 universes ([∀ C : Category@{o h h}, Closed@{so h u}] with the same
 block); left unannotated it minimizes to [Category@{u0 u0 u0}] and is
 refused at the very C where the instance is accepted, so the
 covariant reading would otherwise have been delivered at a strictly
 narrower class of categories than the contravariant one.

 WHICH ROUTE WAS TAKEN, AND WHY IT IS NOT MERELY A MATTER OF TASTE.
 The DIRECT route: Riehl's explicit formulas for adjoint transposition,
 quoted above.  Nothing below requires Category.Functor.Hom.Yoneda or
 Category.Functor.Hom.Yoneda.Natural, and the Yoneda step of Riehl's
 proof -- her "the desired bijection can be given by the Yoneda lemma"
 -- is discharged in [to_from_exp] by the OUTER transformation's own
 [naturality] field plus one identity law.

 That choice has a MEASURED consequence.  [Yoneda_Lemma] and
 [yoneda_natural_pre] are declared over [Category@{u0 u0 u0}], object
 universe identified with hom and with proof, and at a C whose objects
 sit strictly BELOW its homs they are refused, while the display-(8.5)
 object, [PshExp], [presheaf_exp_iso] and [Functor_Category_Closed] are
 all accepted at that very C.  So a route through the Yoneda LEMMA
 would have narrowed the theorem from Awodey's hypothesis to a strictly
 stronger one.  Both halves of that measurement are pinned in
 Test/ProbePresheafExp718.v -- the two refusals against seven positive
 controls at those very levels.

 THE BOOK'S OWN ROUTE GOES THROUGH DENSITY, and it is not taken.
 Awodey proves Proposition 8.13 by writing X as a colimit of
 representables (his Proposition 8.10) and then commuting that colimit
 past [− × P] (his Lemma 8.12).  Proposition 8.10 IS in tree, in the
 presheaf orientation, as Theory/Density.v's [presheaf_density]; it is
 cited by path here and deliberately not required.  Lemma 8.12 is NOT
 in tree, and the two constants in
 Instance/Sets/Cartesian/Closed/Adjunction.v that look like it do not
 serve: [Sets_prod_preserves_colimits] is at [Sets] and not at a
 functor category, and [CCC_prod_preserves_colimits] takes a [Closed]
 structure as a HYPOTHESIS and derives colimit-preservation from the
 currying adjunction, so applying it at a presheaf category before this
 file exists would be circular.  That reading is off those two
 constants' TYPES and is not a compiled experiment.  Riehl's Exercise
 6.5.iii asks for exactly that density proof; it is recorded here as
 the alternative and is not delivered.

 UNIVERSES, MEASURED OFF BOTH THE BINDER AND THE CONSTRAINT BLOCK with
 [Set Printing Universes].

 Functor_Category_Closed@{o h so u} : ∀ C : Category@{o h h},
 Closed@{so h u}
 block: h < so, h < u, o <= h, o <= so, plus stdlib bounds.

 presheaf_exp_iso@{u u0 u1 u2} :
 ∀ {C : Category@{u u0 u0}} (X P Q : C^op ⟶ Sets@{u0 u1}), ...
 block: u0 < u1, u0 < u2, u <= u0, u <= u1, plus stdlib bounds.

 Read three things off that.

 (1) The OBJECT universe is FREE of the hom universe -- bounded above
 by it, never identified.  That bound (C's objects at or below the
 carrier universe of [Sets]) IS Awodey's "for any small category C",
 and it is NEW relative to the presheaf category itself, which carries
 only the hom identification.  Its mechanism is
 Theory/Natural/Transformation.v's [Transform], whose result type is
 [Type@{max(o1,p2)}]: a set of natural transformations is a family
 indexed by the OBJECTS of the source, so those objects must fit where
 the target's hom-sets live.  Construction/Elements/Kan.v's [KanNat]
 and [KanCone] carry the same bound with the same attribution and its
 header works the point out; the precedent is followed here, including
 its refusal to claim the bound unavoidable.  It is NOT claimed
 unavoidable here either, and no attempt is made to restate the
 theorem at a coarser level.

 (2) THE UNIVERSE ANNOTATIONS ARE LOAD-BEARING, and that is measured
 rather than assumed.  Written with NO annotation at all -- no binder
 list, [C : Category] bare and [Sets] bare -- the same body elaborates
 at [∀ C : Category@{u0 u0 u0}], object, hom AND proof identified, a
 minimization artifact, and is then refused at a C whose objects sit
 strictly below its homs, where the shipped instance is accepted.  The
 probe carries that clone and pins the refusal against the shipped
 instance.  Read the attribution narrowly, because it was measured one
 annotation at a time: with the binder [Category@{o h h}] on C kept
 and [Sets@{h so}] dropped, the object universe stays free ([o <= h],
 with [so] then unused); and with [Sets@{h so}] kept and C bare it
 stays free as well (a fresh level bounded by [h]).  So EITHER
 annotation alone blocks the collapse and it is their joint absence
 that produces it; neither is decorative, and the pair is kept so that
 the levels the instance is stated at carry names.  The trailing [+]
 is required, and the reason is the STATEMENT, not [Program]: without
 it the elaborator reports an unbound universe, and the TYPE alone --
 with no [Program] and no obligation -- is refused the same way, taking
 four further levels once [+] is supplied (measured).

 (3) HOM = PROOF in the binder is the donors' doing, not this file's.
 [Opposite] and [Fun] each refuse a C whose hom universe is declared
 strictly below its proof universe, with no reference to the other,
 while [@Functor C Sets] is ACCEPTED at those very levels -- so
 [Functor] is not a donor.  Both refusals and that control are pinned.

 One further reading, because it is easy to get backwards: [PshExp]
 taken ALONE lands in a possibly LARGER [Sets] than the one its
 arguments take values in (its binder reads [C^op ⟶ Sets@{u0 u1} →
 C^op ⟶ Sets@{u0 u1} → C^op ⟶ Sets@{u3 u2}] with [u0 <= u3]).  It is
 [presheaf_exp_iso]'s STATEMENT -- which forces the exponential to be
 an object of the same presheaf category -- that collapses [u3] to
 [u0], and with it produces the smallness bound.  No [Set] occurs in
 the binder or the block of any constant in this file.  The twelve
 constants of section F -- [one_exp_to], [one_from_comp],
 [one_exp_from], [one_exp_iso] and their obligations -- carry block
 EQUATIONS identifying the two [1^op]-presheaves' universe triples
 with each other ([u = u2], [u0 = u3], [u1 = u4]; the two
 [one_from_comp] constants the first two only), reported and not
 attributed; the other thirty-four constants carry none.

 WHAT EACH CONSTANT CONSUMES.  Each entry names the SUBSTANTIVE input;
 the structural step every equation in [Sets] takes -- [proper_morphism]
 of a [SetoidMorphism], to descend to the pair's two components -- is
 used throughout and is not repeated per entry.

 PshExp            fmap_respects: respectfulness of composition in C
 in its left argument, a rewrite with the
 hypothesis after unfolding [op]; fmap_comp:
 associativity in C.
 fmap_id is discharged by the file's default
 obligation tactic and is not written out.
 to_exp_inner      the component's respectfulness is fmap_respects of
 X; the naturality square is naturality of alpha
 followed by fmap_comp of X.
 to_exp            fmap_comp of X and nothing further -- in
 particular NO naturality of alpha and no lemma
 about [Curried_CoHom], the representable's action
 having already reduced away (see the [first] note
 below).
 from_exp          naturality of the INNER transformation, naturality
 of beta, and the identity laws.
 from_to_exp       exactly fmap_id of X.
 to_from_exp       exactly naturality of beta and one identity law.
 This is Riehl's Yoneda step.
 ump_exponents'    fmap_respects then fmap_id of the presheaf, to
 normalise [op id ∘ id] to [id].

 A MEASURED SPELLING NOTE.  Awodey's [y h × 1_P] is written with
 [first] rather than with [split _ id].  Both elaborate at the same
 printed type and the two are NOT convertible, which the probe pins;
 [first] is chosen because in the pointwise-cartesian presheaf category
 its identity factor leaves NO [fmap[P] id] residue, so the second
 component of the pair passes through untouched.  The probe carries
 that reduction as two [eq_refl] controls.  WHY it reduces was not
 isolated, and no claim is made about it.

 STRICT VERSUS [≈], MEASURED STRICT FIRST.  FIVE identifications are
 shipped as [Example ... := eq_refl], and that is the whole count of
 [eq_refl] statements in the file: the display-(8.5) object action;
 the class's [exponent_obj] IS [PshExp]; [curry'] IS [to_exp];
 [uncurry'] IS [from_exp]; and [presheaf_terminal] IS the #339 donor.
 A sixth fact is definitional although its statement is written with
 [≈], as every morphism equation here is: the FROM direction of
 naturality in X closes by [reflexivity], where the TO direction costs
 exactly one appeal to the naturality field of the transformation
 being precomposed, in its [naturality_sym] orientation.

 Exactly one identification comes out at [≈] and not at [eq_refl], and
 its cause is exhibited rather than guessed.  Riehl's counit formula
 ev_c(γ, y) = γ_c(id_c, y) is [eval_is_at_identity]; the [eq_refl] form
 is REFUTED and pinned as a conversion negative.  The reason is that
 [eval'] is [uncurry' id] and the identity of a functor category has
 component [fmap[−] id] rather than [id], so the value reduces to
 γ_c(op id ∘ id, y) and the residue is exactly one identity law,
 [id ∘ id ≈ id], an instance of [id_left] and of [id_right] alike.
 Repairing it would mean changing [nat_id], which is not on the table.

 NON-VACUITY, IN TWO DIRECTIONS.

 At C := 1 the construction recovers [Sets_Closed]'s exponential:
 [one_exp_iso] is an isomorphism in [Sets] between the value of
 [PshExp P Q] at the unique object and [Sets]' own exponential of the
 two values.  The backward leg needs a [match] on the object rather
 than a plain function, because [obj[1]] is [poly_unit], which has no
 eta here: written pointwise, the second projection of the pair
 elaborates at the wrong object and the definition is rejected.

 At C := _2 the conditional theorem of Instance/Fun/Closed.v becomes
 unconditional.  That file's Section AwodeyPointwise is stated for an
 arbitrary [@Closed ([_2^op, Sets]) CC], and its own header records
 that nothing in tree witnessed that hypothesis; this instance does,
 so [awodey_pointwise_not_exponential_unconditional] and
 [pq_point_distinct_unconditional] land there with no hypothesis
 outstanding.  DISCLOSE THE PIN: [_2] is declared with its homs at the
 literal [Set] and [Fun] identifies source and target hom universes,
 so that corollary is about presheaves valued in setoids whose carrier
 lives in [Set].  The pin is [_2]'s, is inherited, and is not
 introduced here.

 PRIOR ART, MEASURED BY SHAPE AS WELL AS BY NAME.  There was no
 [@Closed] structure on any functor category anywhere in this tree
 before this file.  READ THE CRITERION, because the count moves with
 it: sweeping the lines that ASSIGN [exponent_obj] (the two new files
 excluded) returns fifteen, of which two are prose inside comments and
 one, Instance/Comp.v's [Algs_Closed], is a whole instance inside a
 block comment, leaving twelve live assignments; two of those belong
 to other classes ([SymMonClosed] in Instance/Mod/Closed.v,
 [ClosedMonoidal] in Structure/Monoidal/Internal/Product.v), leaving
 ten live for the [Closed] class, and not one of the ten -- nor the
 dead eleventh -- is over a functor category.
 Instance/Cat/Cartesian/Closed.v's [Cat_Closed] is the different claim
 that the exponential OBJECT in [Cat] is a functor category.  Every
 occurrence of [@Closed] at a functor category was a HYPOTHESIS, in
 Instance/Fun/Closed.v, whose [ccc_point] family CONSUMES a closed
 structure and so could not have proved this.

 Two Transform-valued functors into [Sets] already existed, neither
 an exponential: Construction/Elements/Kan.v's [KanNat], a presheaf,
 and Functor/Hom/Yoneda/Natural.v's [YoNat], a bifunctor out of a
 product category, BOTH pure assemblies of
 [Curried_Hom] composites with zero obligations and all three functor
 laws INHERITED, as each file's own comment says.  This file follows
 neither: [PshExp_obj] packages the hom-setoid by hand through
 Instance/Fun.v's notation, and [PshExp] is a hand-built [Program Definition]
 over separate plain definitions of the object and arrow actions, and
 its [fmap_respects] and [fmap_comp] are discharged explicitly, which is
 what the contravariance in the object argument -- the place where the
 objectwise formula gives the wrong object -- deserves.

 THE ISSUE'S "CURRENT STATE" IS STALE ON THREE COUNTS, all re-measured.
 [ls Instance/Fun/] was nine [.v] files before this one, not
 [Cartesian.v] alone; there IS a [@Terminal (@Fun _ _)] instance,
 #339's [Functor_Category_Terminal], which is consumed here; and its
 list of ten [Closed] instances omits Instance/Theory/Lindenbaum.v's
 [Lind_Closed], whose type wraps onto a second line and so escapes a
 one-line sweep, while counting Instance/Comp.v's [Algs_Closed], which
 sits inside a block comment; and its "[exponent_obj :=] occurs at 11
 sites" is fifteen lines, twelve of them live.  A sharper claim
 survives in each case, and each is stated above.  Four of its cited
 donor line numbers have also drifted (Instance/Fun.v's two,
 Functor/Hom/Yoneda.v's and Theory/Sheaf.v's).

 A NAMING HAZARD, RECORDED BECAUSE THE GATE IS WHERE IT WOULD BITE.
 The [print-assumptions] target loads many modules into ONE scope, and
 it already loads Instance/Cat/Exponential.v, so the SHORT module name
 [Exponential] is shared between that file and this one.  That is legal
 -- the kernel paths differ -- but nothing here may be referenced as
 [Exponential.<name>], and every gate entry for this file is written
 fully qualified.

 WHAT IS NOT DELIVERED -- read this as the scope of the file.

 * No naturality in P or in Q.  [PshExp] is not exhibited as a
 bifunctor [([C^op, Sets])^op ∏ [C^op, Sets] ⟶ [C^op, Sets]], so
 Awodey's "natural in X" is the only naturality proved.

 * No Lemma 8.12 and no density proof.  Riehl's Exercise 6.5.iii is
 cited above and no artifact answers it.

 * No [ElementaryTopos] for a presheaf category.  This supplies the
 cartesian-closure component of that assembly, the classifier
 component being Instance/Fun/Classifier.v's; nothing here joins
 them.

 * Nothing about the Yoneda embedding preserving products and
 exponentials -- Awodey's Theorem 8.14 second clause, which is his
 §8.9 Exercise 4 and a separate catalog item.

 * No general target D in place of [Sets].  The positive theorem for
 a complete cartesian closed D is not attempted, and
 Instance/Fun/Closed.v's counterexample shows the hypothesis on D
 is not decorative.

 * No comparison with [Cat_Closed], and no statement relating the
 exponential built here to the exponential of [Cat].

 * Nothing is registered as an [Instance] except
 [Functor_Category_Closed].  [presheaf_terminal] and
 [Functor_Category_Closed_cov] are plain definitions.

 * This file contributes NO lines to [make todo].  Its probe does,
 as every probe in this tree does, and that is disclosed rather
 than hidden. 

 --------
 书籍：Awodey，《范畴论》（第一版，卡耐基梅隆预印本，2005年9月），第8.7节“图范畴中的指数对象”，显示 (8.5) 和命题 8.13，印刷页 208，以及定理 8.14，印刷页 209（[awodey:8.7:def-presheaf-exponential], [awodey:8.7:prop13], [awodey:8.7:thm14]）。逐字从渲染页面：

 "如果我们有这样的指数对象 Q^P，我们可以通过 Yoneda 引理计算它在任意对象 C ∈ C 上的值：

 Q^P(C) ≅ Hom(yC, Q^P)

 如果它要成为指数对象，那么我们还必须有：

 Hom(yC, Q^P) ≅ Hom(yC × P, Q)

 但是后者的集合确实存在。因此，我们可以直接定义：

 Q^P(C) = Hom(yC × P, Q)                      (8.5)"作用在 h 上的映射为：C' → C，具体为：

 Q^P(h) = Hom(yh × 1_P, Q)

 这显然是一个对 C 的反变、集合值函子。让我们现在检查它确实给出了 P 和 Q 的指数对象。

 命题 8.13. 对于 Sets^{C^op} 中的任意对象 X、P、Q，存在一个在 X 上自然的同构：

 Hom(X, Q^P) ≅ Hom(X × P, Q)

 定理 8.14. 对于任意小范畴 C，图范畴 Sets^{C^op} 是笛卡尔闭的。

 书籍：Riehl，《Category Theory in Context》，第二版，第 4.4 节，第 152-153 页（[riehl:4.4:lem11]）。原文逐字如下：

 引理 4.4.11. 对于任意小范畴 C，函子范畴 Set^C 是笛卡尔闭的。证明。给定函子 F, G : C → Set，我们的目标是定义一个函子 G^F : C → Set，使得存在自然双射在自然变换集合之间

 (4.4.12)          {H × F ⇒ G} ≅ {H ⇒ G^F}

 对于所有函子 H : C → Set。为了定义 G^F 在对象 c 上的值，我们定义

 (4.4.13)   G^F(c) := {C(c, −) × F ⇒ G} ≅ {C(c, −) ⇒ G^F}

 这样所需的双射可以由 Yoneda 引理给出。存在一个正式的理由说明，自然双射(4.4.12)如何由特例(4.4.13)推导而来（见练习6.5.iii），但这个双射也可以通过提供伴随转置的公式直接证明。

 给定 α : H × F ⇒ G，其转置是自然变换 β : H ⇒ G^F，对于 c ∈ C 和 x ∈ Hc，定义 β_c(x) : C(c, −) × F ⇒ G 为自然变换，其在 d ∈ D 处的分量是函数，该函数将 f : c → d 和 z ∈ Fd 映射到元素 α_d((H f)x, z)。这些操作在所提到的所有变量中都是自然的，并且彼此互为逆。书籍：Riehl，同上，第6.5节，练习6.5.iii，第248页打印版
 ([riehl:6.5:exiii])。原文：

 "练习6.5.iii。使用定理6.5.7给引理4.4.11提供第二种证明，表明所需的自然同构来自内部Hom的定义。"

 nLab: https://ncatlab.org/nlab/show/exponential+object
 nLab: presheaves上的闭单结构（相同站点），其确切陈述为[X,Y] (c) = Hom(y(c) × X, Y)
 Wikipedia: https://en.wikipedia.org/wiki/Cartesian_closed_category

 已交付内容：[Functor_Category_Closed C]，一个[#[export]
 程序实例，类型为

 @Closed ([C^op, Sets])
 (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian)对于任意类别 C——在以下测量的宇宙层次下，这正是 Awodey 所说的“small”所在——连同 [presheaf_exp_iso]，在 [Sets] 中作为同态集体的同构的命题 8.13，以及 [to_exp_natural_X] / [from_exp_natural_X]，其在 X 方向上的自然性。指数对象是显示的 (8.5) 公式，仅此而已：ZW15WZZ 是在代表-乘-P 的预束范畴中的同态集体，ZW16WZZ 在 [eq_refl] 上读回它。

 终端部分是 #339 的，并且没有重建：ZW18WZZ 是 [Functor_Category_Terminal Sets_Terminal] 专门化到 [C^op] 和 [Sets]，并且 [presheaf_terminal_is_donor] 在 [eq_refl] 上读回它。对于二元积使用 [Functor_Category_Cartesian]，这就是本库词汇下定理 8.14 的第一条款。Riehl 的 Set^C 是协变函子范畴，而 Awodey 的 Sets^{C^op} 是反变函子范畴；在这里它们之间的转换不需要证明，因为在这个树中 [(C^op)^op = C] 通过 [eq_refl] 成立，所以在对偶范畴中 [Functor_Category_Closed_cov] 就是 [Functor_Category_Closed]，它由 [:=] 提供，无需策略也无需传递。它像实例一样被注释，并测量以位于相同的宇宙中（[∀ C : Category@{o h h}, Closed@{so h u}] 与相同的区块）；如果未加注释，它会最小化为 [Category@{u0 u0 u0}]，并在实例被接受的那个 C 被拒绝，因此协变解释本来会在严格比反变范畴更窄的类别类中给出。采取了哪条路线，以及为什么这不仅仅是个人喜好的问题。
 直接路线：Riehl 对伴随转置的明确公式，如上所引。下面的内容不需要 Category.Functor.Hom.Yoneda 或 Category.Functor.Hom.Yoneda.Natural，并且 Riehl 证明中的 Yoneda 步骤——她的“所需的双射可以由 Yoneda 引理给出”——在 [to_from_exp] 中已经由 OUTER 变换自身的 [naturality] 字段加上一条恒等律完成。这个选择有一个有度量的后果。[Yoneda_Lemma] 和 [yoneda_natural_pre] 在 [Category@{u0 u0 u0}] 上被声明，对象宇宙与 hom 及其证明相关，并且在一个对象严格低于其 hom 的 C 中，它们被拒绝，而显示-(8.5) 对象 [PshExp]、[presheaf_exp_iso] 和 [Functor_Category_Closed] 都在同一个 C 中被接受。因此，通过 Yoneda 引理的路径会将定理从 Awodey 的假设缩小到一个严格更强的假设。该度量的两个部分固定在 Test/ProbePresheafExp718.v 中——在这些层级上，两个拒绝与七个阳性控制相对比。这本书自己的路线是通过密度的，但它没有被采用。Awodey 通过将 X 写成可表示对象的余极限（他的命题 8.10），然后将该余极限与 [− × P] 交换（他的引理 8.12）来证明命题 8.13。命题 8.10 存在于树中，以预层范畴方向出现，正如 Theory/Density.v 中的 [presheaf_density]；它在此路径被引用，并且故意不被要求。引理 8.12 不存在于树中，而在 Instance/Sets/Cartesian/Closed/Adjunction.v 中看起来像它的两个常量并不适用：[Sets_prod_preserves_colimits] 在 [Sets] 处，而不在函子范畴处；[CCC_prod_preserves_colimits] 将 [Closed] 结构作为假设，并从柯里化伴随中推导余极限保持性，因此在这个文件存在之前在预层范畴上应用它会产生循环。该读数是基于那两个常量的类型，并不是一个编译的实验。Riehl 的练习 6.5.iii 正是要求那个密度证明；这里作为替代记录，但并未提供。

 宇宙，同时从绑定器和约束块中测量，使用 [Set Printing Universes]。

 Functor_Category_Closed@{o h so u} : ∀ C : Category@{o h h},
 Closed@{so h u}
 块: h < so, h < u, o <= h, o <= so, 外加标准库界限。

 presheaf_exp_iso@{u u0 u1 u2} :
 ∀ {C : Category@{u u0 u0}} (X P Q : C^op ⟶ Sets@{u0 u1}), ...
 块: u0 < u1, u0 < u2, u <= u0, u <= u1, 外加标准库界限。

 从中读取三件事。(1) 对象（OBJECT）宇宙不包含同态（hom）宇宙——它被同态宇宙向上界定，但从未被认同。该界限（C 的对象位于或低于 [Sets] 的承载宇宙）是 Awodey 所说的“对于任意小范畴 C”，相对于预层范畴本身而言，它是新的，预层范畴只承载同态的认同。其机制是 Theory/Natural/Transformation.v 的 [Transform]，其结果类型为 [Type@{max(o1,p2)}]：自然变换的集合是一族，由源的对象索引，因此这些对象必须适合目标同态集所在的位置。Construction/Elements/Kan.v 的 [KanNat] 和 [KanCone] 承载相同的界限并具有相同的归属，其标题指出了该点；此处遵循了先例，包括其拒绝宣称该界限不可避免。这里也不声称这是不可避免的，并且没有尝试以更粗略的层次重新表述该定理。(2) 宇宙注释具有承重作用，这是通过测量而非假设得出的。完全没有注释的写作——没有绑定器列表，[C : Category] 空白 和 [Sets] 空白——相同的主体在 [∀ C : Category@{u0 u0 u0}] 处展开，对象、hom 和证明被识别，这是一个最小化伪影，然后在 C 上被拒绝，其对象严格位于其 homs 之下，而已发送的实例被接受。探针携带该克隆，并将拒绝固定在已发送的实例上。狭义地解读归属，因为这是逐注释测量的：当 C 上保留绑定器 [Category@{o h h}] 并丢弃 [Sets@{h so}] 时，对象宇宙保持自由（[o <= h]，并且 [so] 此后未使用）；当 [Sets@{h so}] 保留而 C 空白时，它也保持自由（一个由 [h] 限定的新层级）。所以要么注解本身阻止了坍缩，要么是它们同时缺失才会产生坍缩；两者都不是装饰性的，这对注解被保留是为了使实例声明的级别有名称。尾随的 [+] 是必需的，其原因在于 STATEMENT，而不是 [Program]：没有它，展开器会报告一个未绑定的宇宙，而仅 TYPE ——没有 [Program] 并且没有义务——也会以同样的方式被拒绝，在提供 [+] 后又增加四个级别（已测量）。(3) HOM = 证明在活页夹中是捐赠者的操作，而不是这个文件的操作。  
 [Opposite] 和 [Fun] 分别拒绝一个其同构宇宙被声明为严格低于其证明宇宙的 C，而不参考其他，  
 而 [@Functor C Sets] 在那些级别上被接受——所以 [Functor] 不是捐赠者。 拒绝和该控制都已固定。进一步阅读，因为容易搞反：[PshExp] 单独使用时可能落在比其参数取值的集合更大的 [Sets] 上（其绑定器注明 [C^op ⟶ Sets@{u0 u1} → C^op ⟶ Sets@{u0 u1} → C^op ⟶ Sets@{u3 u2}]，并带有 [u0 <= u3]）。是 [presheaf_exp_iso] 的陈述——它强制指数成为同一预层范畴的对象——将 [u3] 压缩为 [u0]，并由此产生小性限制。此文件中没有 [Set] 出现在绑定器或任何常量的块中。第十二节F的十二个常量——[one_exp_to]、[one_from_comp]、[one_exp_from]、[one_exp_iso]及其义务——携带区块方程，将两个[1^op]预层的宇宙三元组互相识别（[u = u2]、[u0 = u3]、[u1 = u4]；前两个仅有的两个[one_from_comp]常量），已报告但未归属；其余三十四个常量不携带任何方程。

 每个常量消耗的内容。每个条目都标明了实质性输入；[Sets]中每个方程的结构步骤——[proper_morphism]，一个[SetoidMorphism]的一步，以下降到该对的两个分量——在整个过程中使用，并且每个条目不重复说明。PshExp            fmap_respects：C 中组合的尊重性，在其左参数中，对假设进行展开 [op] 后的重写；fmap_comp：C 中的结合性。fmap_id 由文件的默认义务策略解决，并未写出。to_exp_inner      组件的尊重性是 X 的 fmap_respects；自然性方形是 alpha 的自然性，随后是 X 的 fmap_comp。to_exp            fmap_comp 对 X 并且没有进一步操作——特别是没有 alpha 的自然性，也没有关于 [Curried_CoHom] 的引理，表示体的作用已经被约简掉（见下面的 [first] 注释）。from_exp          INNER 变换的自然性，beta 的自然性，以及恒等律。from_to_exp       完全是 X 的 fmap_id。to_from_exp       完全是 beta 的自然性和一个恒等律。这是 Riehl 的 Yoneda 步骤。ump_exponents'    fmap_respects 接着是预上层模范的 fmap_id，用于将 [op id ∘ id] 规范化为 [id]。一个经过衡量的拼写注释。Awodey 的 [y h × 1_P] 是用 [first] 而不是 [split _ id] 写的。两者在相同的印刷类型上都有详细说明，且两者不可互换，这由探针销钉证明；选择 [first] 是因为在逐点笛卡尔预层范畴中，它的恒等分解不会留下任何 [fmap[P] id] 残余，因此该对的第二个分量可以不受影响地通过。探针将该约简表现为两个 [eq_refl] 控件。它为何能够约简尚未明确，也未对其作出任何主张。严格对比 [≈]，先测量严格。运送的五个标识为 [Example ... := eq_refl]，这是文件中 [eq_refl] 语句的全部计数：显示-(8.5) 对象动作；类的 [exponent_obj] 是 [PshExp]；[curry'] 是 [to_exp]；[uncurry'] 是 [from_exp]；以及 [presheaf_terminal] 是 #339 捐赠者。第六个事实是定义性的，尽管它的陈述是用 [≈] 写的，就像这里的每个态射方程一样：X 中自然而然性的 FROM 方向闭合于 [reflexivity]，其中 TO 方向正好消耗一次对所预组合变换自然性域的调用，在其 [naturality_sym] 方向上。恰好有一个标识在 [≈] 出现，而不是在 [eq_refl] 出现，并且其原因是展示出来的而非猜测的。Riehl 的余单位公式 ev_c(γ, y) = γ_c(id_c, y) 是 [eval_is_at_identity]；[eq_refl] 的形式被驳斥并被标记为转换否定。原因是 [eval'] 是 [uncurry' id]，并且函子范畴的恒等式的分量是 [fmap[−] id] 而不是 [id]，因此其值化简为 γ_c(op id ∘ id, y)，其余量恰好是一个恒等律 [id ∘ id ≈ id]，是 [id_left] 和 [id_right] 的一个实例。修复它将意味着改变 [nat_id]，这不在讨论范围内。

 非空性，双向的。当 C := 1 时，该构造恢复了 [Sets_Closed] 的指数：
 [one_exp_iso] 是 [Sets] 中的一个同构，连接了唯一对象的 [PshExp P Q] 的值与 [Sets] 自身的两个值的指数。向后的部分需要在对象上有一个 [match]，而不是一个普通函数，因为 [obj[1] ] 是 [poly_unit]，在这里没有 eta：逐点书写时，成对的第二投影在错误的对象上展开，定义被拒绝。在 C := _2 时，Instance/Fun/Closed.v 的条件定理变为无条件定理。该文件的 Section AwodeyPointwise 是针对任意的 [@Closed ([_2^op, Sets] ) CC] 说明的，其自身的头部记录显示树中没有任何内容证明该假设；这个实例证明了，因此 [awodey_pointwise_not_exponential_unconditional] 和 [pq_point_distinct_unconditional] 在没有未解决假设的情况下到达那里。公开 PIN: [_2] 被声明及其 homs 在字面上的 [Set]，并且 [Fun] 标识源与目标 hom 宇宙，因此推论关于取值于集合族且其载体存在于 [Set] 的预层。这个 pin 属于 [_2]，并被继承，并未在此处引入。以前的技术，既通过形状也通过名称来衡量。在此文件之前，这棵树中的任何函子范畴上都没有 [@Closed] 结构。请阅读该标准，因为计数会随之变化：扫描那些分配了 [exponent_obj] 的行（不包括这两个新文件）返回十五个，其中两个是在注释中的散文，一个是 Instance/Comp.v 的 [Algs_Closed]，它是在块注释中的一个完整实例，留下十二个有效分配；其中两个属于其他类（Instance/Mod/Closed.v 中的 [SymMonClosed]，Structure/Monoidal/Internal/Product.v 中的 [ClosedMonoidal]），剩下十个是 [Closed] 类的有效分配，这十个中没有一个——也包括死亡的第十一个——是在函子范畴上。Instance/Cat/Cartesian/Closed.v 的 [Cat_Closed] 是不同的命题，即 [Cat] 中的指数对象是一个函子范畴。在每次 [@Closed] 出现在函子范畴时，它都是 Instance/Fun/Closed.v 中的一个假设，其 [ccc_point] 家族消耗一个封闭结构，因此无法证明这一点。两个转换值函子到 [Sets] 已经存在，都不是指数型的：Construction/Elements/Kan.v 的 [KanNat]，是一个预层，和 Functor/Hom/Yoneda/Natural.v 的 [YoNat]，是一个从积范畴出的双函子，两者都是纯组合 [Curried_Hom]，零义务，并继承了所有三个函子律，正如每个文件的注释所说。这个文件既不遵循哪一个：[PshExp_obj] 通过 Instance/Fun.v 的符号手工封装了 hom-集合，[PshExp] 是在对对象和箭头作用的单独普通定义上手工构建的 [Program Definition]，它的 [fmap_respects] 和 [fmap_comp] 被显式解除，这正是对象参数上的逆变——对象公式出错的地方——所应得的。该问题的“当前状态”在三个方面都是陈旧的，所有这些都已重新测量。[ls Instance/Fun/] 位于本文件之前的九个 [.v] 文件中，而不是单独的 [Cartesian.v]；确实存在一个 [@Terminal (@Fun _ _)] 实例，即 #339 的 [Functor_Category_Terminal]，这里被使用；其十个 [Closed] 实例的列表中遗漏了 Instance/Theory/Lindenbaum.v 的 [Lind_Closed]，该类型延续到第二行，因此逃过一行扫描，同时统计了位于块注释内的 Instance/Comp.v 的 [Algs_Closed]；其“[exponent_obj :=] 出现在 11 个位置”跨越了十五行，其中十二行有效。每种情况下都有更精确的声明，并且每种声明都在上文中说明。其引用的四个原始行号也已经漂移（Instance/Fun.v 的两个，Functor/Hom/Yoneda.v 的以及 Theory/Sheaf.v 的）。命名风险，记录是因为门是在它可能咬人的地方。
 [print-assumptions] 目标在一个作用域中加载许多模块，并且
 它已经加载了 Instance/Cat/Exponential.v，因此简短模块名
 [Exponential] 在该文件和此文件之间共享。这是合法的
 ——内核路径不同——但是这里的任何内容都不能引用为
 [Exponential.<name>]，并且此文件的每个门条目都是完全限定写的。

 未交付的内容 —— 读作文件的作用域。

 * 不在 P 或 Q 中自然。[PshExp] 没有作为
 双函子 [([C^op, Sets] )^op ∏ [C^op, Sets]  ⟶ [C^op, Sets] 展示，因此
 Awodey 的“在 X 中自然”是唯一被证明的自然性。

 * 没有引理 8.12，也没有稠密性证明。上文引用了 Riehl 的习题 6.5.iii，
 没有任何工件对此作出回答。* 对于 presheaf 类别没有 [ElementaryTopos]。这提供了该组合的笛卡尔闭合部分，分类器部分位于 Instance/Fun/Classifier.v；这里没有任何东西将它们连接起来。

 * 关于 Yoneda 嵌入保持积和指数的内容没有——Awodey 的定理 8.14 第二条款，这是他的第 §8.9 练习 4 和一个单独的目录项。

 * 没有将 [Sets] 替换为一般目标 D。对于完全笛卡尔闭合的 D 的正定理未被尝试，而 Instance/Fun/Closed.v 的反例显示对 D 的假设并非装饰性的。

 * 没有与 [Cat_Closed] 的比较，也没有将这里构建的指数与 [Cat] 的指数相关联的说明。* 除了 [Functor_Category_Closed]，[Instance] 没有被注册。[presheaf_terminal] 和 [Functor_Category_Closed_cov] 是普通定义。

 * 该文件对 [make todo] 没有任何贡献。它的探针会有贡献，正如该树中的每个探针一样，这一点是公开的，而不是隐藏的。
*)

(* * ** A: the exponential presheaf -- Awodey display (8.5) / * ** A：指数预层 -- Awodey 显示 (8.5) *)

Section PshExpSec.

Context {C : Category}.

#[local] Notation PshCart :=
  (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian).

Context (P Q : C^op ⟶ Sets).

(*
 Display (8.5): Q^P(c) is the hom-setoid of the presheaf category at
 the representable on c times P.  Instance/Fun.v's [[[ , ]]]( , )
 notation packages exactly that as an object of [Sets]. 

 --------
 显示 (8.5)：Q^P(c) 是 presheaf 范畴在 c 上的可表示对象乘以 P 的同类集。Instance/Fun.v 的 [[[ , ] ]]( , ) 符号正好将其作为 [Sets] 的一个对象打包。
*)
Definition PshExp_obj (c : C) : Sets :=
  [[[C^op, Sets]]]( @product_obj _ PshCart (Curried_CoHom C c) P, Q ).

(*
 Awodey's Q^P(h) = Hom(y h × 1_P, Q): precomposition with the
 representable's action on h, crossed with the identity of P.  The
 variance comes out on the nose with no transport, because
 [Curried_CoHom C] is [Curried_Hom C^op] and its source is [(C^op)^op],
 which is [C] definitionally: for [h : c ~{C^op}~> c'] the arrow
 [fmap[Curried_CoHom C] h] runs from the representable at [c'] to the
 representable at [c], which is the direction precomposition wants. 

 --------
 Awodey 的 Q^P(h) = Hom(y h × 1_P, Q)：通过 representable 在 h 上的作用进行前合成，并与 P 的恒等映射相乘。方差完全正确，无需任何变换，因为 [Curried_CoHom C] 就是 [Curried_Hom C^op]，它的源是 [(C^op)^op]，而 [(C^op)^op] 根据定义是 [C]：对于 [h : c ~{C^op}~> c']，箭头 [fmap[Curried_CoHom C] h] 从 [c'] 处的 representable 指向 [c] 处的 representable，这正是前合成所需要的方向。
*)
Definition PshExp_fmap (c c' : C) (h : c ~{C^op}~> c') :
  PshExp_obj c ~{Sets}~> PshExp_obj c'.
Proof.
  unshelve econstructor.
  - refine (fun alpha => nat_compose alpha _).
    exact (@first _ PshCart _ _ P (fmap[Curried_CoHom C] h)).
  - proper. exact (X x0 _).
Defined.

(*
 The two functor laws are PROVED, not inherited.  [fmap_id] is the one
 the default obligation tactic closes; a third [Next Obligation] is
 rejected for want of a goal. 

 --------
 两个函子定律是被证明的，而不是继承的。[fmap_id] 是默认的义务策略可以完成的；第三个 [Next Obligation] 因缺少目标而被拒绝。
*)
Program Definition PshExp : C^op ⟶ Sets := {|
  fobj := PshExp_obj;
  fmap := PshExp_fmap
|}.
Next Obligation.
  proper.
  simpl; apply proper_morphism; split; simpl; [ | reflexivity ].
  unfold op; now rewrite X.
Qed.
Next Obligation.
  simpl; intros.
  simpl; apply proper_morphism; split; simpl; [ | reflexivity ].
  unfold op; cat.
Qed.

End PshExpSec.

(* * ** B: the transposition, both ways / * ** B：换位，两种方式 *)

Section Transpose.

Context {C : Category}.

#[local] Notation PshCart :=
  (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian).

Context (X P Q : C^op ⟶ Sets).

(* Riehl's beta_c(x), component at d: the function taking f : c -> d and z in P d to alpha_d ((X f) x, z). / Riehl 的 beta_c(x)，在 d 的分量：将 f : c -> d 和 z 在 P d 中映射到 alpha_d((X f) x, z) 的函数。 *)
Program Definition to_exp_inner_comp
  (alpha : @product_obj _ PshCart X P ⟹ Q) (c : C) (x : fobj[X] c)
  (d : C^op) :
  fobj[@product_obj _ PshCart (Curried_CoHom C c) P] d ~{Sets}~> fobj[Q] d :=
  {| morphism := fun hp => alpha d (fmap[X] (fst hp) x, snd hp) |}.
Next Obligation.
  intros u v [Hu Hv]; simpl in *.
  apply proper_morphism; split; simpl;
    [ exact (@fmap_respects _ _ X _ _ _ _ Hu x) | exact Hv ].
Qed.

Definition to_exp_inner
  (alpha : @product_obj _ PshCart X P ⟹ Q) (c : C) (x : fobj[X] c)
  : @product_obj _ PshCart (Curried_CoHom C c) P ⟹ Q.
Proof.
  unshelve eapply Build_Transform'.
  - exact (to_exp_inner_comp alpha c x).
  - intros d e f hp; simpl.
    etransitivity;
      [ exact (@naturality _ _ _ _ alpha _ _ f
                 (fmap[X] (fst hp) x, snd hp)) | ].
    simpl; apply proper_morphism; split; simpl; [ | reflexivity ].
    symmetry; exact (@fmap_comp _ _ X _ _ _ f (fst hp) x).
Defined.

Program Definition to_exp_comp
  (alpha : @product_obj _ PshCart X P ⟹ Q) (c : C^op) :
  fobj[X] c ~{Sets}~> fobj[PshExp P Q] c :=
  {| morphism := fun x => to_exp_inner alpha c x |}.
Next Obligation.
  intros u v Huv d hp; simpl.
  apply proper_morphism; split; simpl; [ | reflexivity ].
  now apply proper_morphism.
Qed.

(*
 Riehl's beta : H ==> G^F.  Awodey's transpose of Hom(X × P, Q) into
 Hom(X, Q^P). 

 --------
 Riehl 的 β：H ==> G^F。Awodey 将 Hom(X × P, Q) 转换为 Hom(X, Q^P)。
*)
Definition to_exp (alpha : @product_obj _ PshCart X P ⟹ Q)
  : X ⟹ PshExp P Q.
Proof.
  unshelve eapply Build_Transform'.
  - exact (to_exp_comp alpha).
  - intros c c' f x d hp; simpl.
    apply proper_morphism; split; simpl; [ | reflexivity ].
    exact (@fmap_comp _ _ X _ _ _ (fst hp) f x).
Defined.

(* The counit route: alpha_c (x, p) = (beta_c x)_c (id_c, p), which is Riehl's ev composed with beta × F. / 余单位途径：alpha_c (x, p) = (beta_c x)_c (id_c, p)，它是 Riehl 的 ev 与 beta × F 的组合。 *)
Program Definition from_exp_comp (beta : X ⟹ PshExp P Q) (c : C^op) :
  fobj[@product_obj _ PshCart X P] c ~{Sets}~> fobj[Q] c :=
  {| morphism := fun xp => (beta c (fst xp)) c (id[c], snd xp) |}.
Next Obligation.
  intros u v [Hu Hv]; simpl.
  etransitivity;
    [ exact (@proper_morphism _ _ _ _ (transform[beta] c) _ _ Hu c
               (id[c], snd u)) | ].
  apply proper_morphism; split; simpl; [ reflexivity | exact Hv ].
Qed.

Definition from_exp (beta : X ⟹ PshExp P Q)
  : @product_obj _ PshCart X P ⟹ Q.
Proof.
  unshelve eapply Build_Transform'.
  - exact (from_exp_comp beta).
  - intros c c' f xp; simpl.
    transitivity ((beta c (fst xp)) c' (f, fmap[P] f (snd xp))).
    + etransitivity;
        [ exact (@naturality _ _ _ _ (beta c (fst xp)) _ _ f
                   (id[c], snd xp)) | ].
      simpl; apply proper_morphism; split; simpl; [ | reflexivity ].
      unfold op; cat.
    + etransitivity;
        [ | exact (@naturality _ _ _ _ beta _ _ f (fst xp) c'
                     (id[c'], fmap[P] f (snd xp))) ].
      simpl; apply proper_morphism; split; simpl; [ | reflexivity ].
      unfold op; cat.
Defined.

(* One round trip is exactly [fmap_id] of X. / 一次往返正好是 X 的 [fmap_id]。 *)
Lemma from_to_exp (alpha : @product_obj _ PshCart X P ⟹ Q) :
  from_exp (to_exp alpha) ≈[[C^op, Sets]] alpha.
Proof.
  intros c xp; simpl.
  apply proper_morphism; split; simpl; [ | reflexivity ].
  exact (@fmap_id _ _ X c (fst xp)).
Qed.

(*
 The other is Riehl's Yoneda step, and it needs no Yoneda: the
 [naturality] field of beta at [fst hp], plus one identity law. 

 --------
 另一个是Riehl的Yoneda步骤，它不需要Yoneda：在[fst hp]处beta的[naturality]字段，加上一个恒等定律。
*)
Lemma to_from_exp (beta : X ⟹ PshExp P Q) :
  to_exp (from_exp beta) ≈[[C^op, Sets]] beta.
Proof.
  intros c x d hp; simpl.
  symmetry.
  etransitivity;
    [ | exact (@naturality _ _ _ _ beta _ _ (fst hp) x d
                 (id[d], snd hp)) ].
  simpl; apply proper_morphism; split; simpl; [ | reflexivity ].
  unfold op; cat.
Qed.

(*
 Proposition 8.13 / Riehl (4.4.12), as an isomorphism of hom-setoids in
 [Sets].  Only the two isomorphism laws are written: the two
 respectfulness obligations are closed by the default tactic. 

 --------
 命题 8.13 / Riehl (4.4.12)，作为 [Sets] 中同集族的同构。只写了两个同构定律：两个尊重性义务由默认策略解决。
*)
Program Definition presheaf_exp_iso :
  @Isomorphism Sets
    ([[[C^op, Sets]]]( @product_obj _ PshCart X P, Q ))
    ([[[C^op, Sets]]]( X, PshExp P Q )) := {|
  to   := {| morphism := to_exp |};
  from := {| morphism := from_exp |}
|}.
Next Obligation. exact (to_from_exp x x0 x1 x2 (h, c)). Qed.
Next Obligation. exact (from_to_exp x x0 (c, c0)). Qed.

End Transpose.

(*
   * ** C: naturality in X -- Awodey's "And these isos are clearly
   natural in X" 

   --------
   * ** C：X中的自然性——Awodey 的“而这些同构在X中显然是自然的”
*)

Section NaturalX.

Context {C : Category}.

#[local] Notation PshCart :=
  (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian).

Context (X X' P Q : C^op ⟶ Sets).

(*
 One appeal to the naturality field of g -- its [naturality_sym]
 orientation -- and nothing else. 

 --------
 只诉诸于 g 的自然性场 —— 它的 [naturality_sym] 方向 —— 仅此而已。
*)
Lemma to_exp_natural_X (g : X' ~{[C^op, Sets]}~> X)
  (alpha : @product_obj _ PshCart X P ~{[C^op, Sets]}~> Q) :
  to_exp X' P Q (alpha ∘[[C^op, Sets]] @first _ PshCart _ _ P g)
    ≈[[C^op, Sets]] to_exp X P Q alpha ∘[[C^op, Sets]] g.
Proof.
  intros c x d hp; simpl.
  apply proper_morphism; split; simpl; [ | reflexivity ].
  exact (@naturality_sym _ _ _ _ g _ _ (fst hp) x).
Qed.

(* The other direction is DEFINITIONAL: [reflexivity] closes it. / 另一个方向是定义性的：[reflexivity] 关闭它。 *)
Lemma from_exp_natural_X (g : X' ~{[C^op, Sets]}~> X)
  (beta : X ~{[C^op, Sets]}~> PshExp P Q) :
  from_exp X' P Q (beta ∘[[C^op, Sets]] g)
    ≈[[C^op, Sets]] from_exp X P Q beta
                      ∘[[C^op, Sets]] @first _ PshCart _ _ P g.
Proof.
  intros c xp; simpl.
  reflexivity.
Qed.

End NaturalX.

(** ** D: Theorem 8.14, first clause / ** D: 定理 8.14，第一条款 *)

(*
 The universe binders are load-bearing and the trailing [+] is
 required; see the header.  [ump_exponents'] is the one written
 obligation: its goal normalises [op id ∘ id] to [id] by
 [fmap_respects] and then applies [fmap_id]. 

 --------
 宇宙绑定器是承重的，并且需要拖尾 [+]；请参阅标题。[ump_exponents'] 是书面义务：其目标通过 [fmap_respects] 将 [op id ∘ id] 规范化为 [id]，然后应用 [fmap_id]。
*)
#[export] Program Instance Functor_Category_Closed@{o h so +}
  (C : Category@{o h h}) :
  @Closed ([C^op, Sets@{h so}])
    (@Functor_Category_Cartesian (C^op) Sets@{h so} Sets_Cartesian) := {|
  exponent_obj := fun P Q => PshExp P Q;
  exp_iso := fun X P Q => presheaf_exp_iso X P Q
|}.
Next Obligation.
  apply proper_morphism; split; simpl; [ | reflexivity ].
  assert (H : op (@id C x0) ∘ id ≈ @id C x0) by (unfold op; cat).
  etransitivity; [ exact (@fmap_respects _ _ x _ _ _ _ H c) | ].
  exact (@fmap_id _ _ x _ c).
Qed.

(*
 Riehl's Set^C, the covariant reading of the same theorem: a [:=] with
 no tactic and no transport, since [(C^op)^op] is [C].  Annotated like
 the instance so that it is delivered at the same universes; written
 unannotated it minimizes to [Category@{u0 u0 u0}] and is refused where
 the instance is accepted (measured; the probe pins the annotated form
 as a control at that very C). 

 --------
 Riehl 的 Set^C，相同定理的协变表达：一个 [:=]，没有策略也没有传输，因为 [(C^op)^op] 是 [C]。像该实例一样加注释，以便它在相同的宇宙中传递；未加注释地书写，它会简化为 [Category@{u0 u0 u0}]，并且在实例被接受的地方会被拒绝（已测量；探针在那个特定的 C 上将注释形式作为控制）。
*)
Definition Functor_Category_Closed_cov@{o h so +} (C : Category@{o h h}) :
  @Closed ([C, Sets@{h so}])
    (@Functor_Category_Cartesian C Sets@{h so} Sets_Cartesian) :=
  Functor_Category_Closed (C^op).

(* The terminal presheaf is #339's, specialised. With [Functor_Category_Cartesian] this completes the finite-product half of Theorem 8.14. / 终端预层是 #339 的，经过专门化。使用 [Functor_Category_Cartesian]，这完成了定理 8.14 的有限乘积部分。 *)
Definition presheaf_terminal (C : Category) : @Terminal ([C^op, Sets]) :=
  @Functor_Category_Terminal (C^op) Sets Sets_Terminal.

(** ** E: readbacks / ** E: 回读 *)

Section Readbacks.
Context {C : Category}.
Context (X P Q : C^op ⟶ Sets).

#[local] Notation PshCart :=
  (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian).

(* Awodey display (8.5) on the nose. / Awodey 鼻子上的显示为 (8.5)。 *)
Example exp_obj_is_display85 (c : C) :
  fobj[PshExp P Q] c
    = [[[C^op, Sets]]]( @product_obj _ PshCart (Curried_CoHom C c) P, Q )
  := eq_refl.

(* The class's exponential IS the presheaf built above. / 该类的指数是上面构建的预层。 *)
Example exponent_obj_is_PshExp :
  @exponent_obj _ _ (Functor_Category_Closed C) P Q = PshExp P Q := eq_refl.

(* The class's transposes ARE the two maps built above. / 该类的转置是上面构建的两个映射。 *)
Example curry_is_to_exp (alpha : @product_obj _ PshCart X P ⟹ Q) :
  @curry' _ _ (Functor_Category_Closed C) X P Q alpha = to_exp X P Q alpha
  := eq_refl.

Example uncurry_is_from_exp (beta : X ⟹ PshExp P Q) :
  @uncurry' _ _ (Functor_Category_Closed C) X P Q beta = from_exp X P Q beta
  := eq_refl.

(* Riehl's counit formula, at [≈] and not at [eq_refl]; see the header for the residue and the probe for the refutation. / Riehl 的余单元公式，在 [≈] 而不是在 [eq_refl]；参见头部的关于反驳的剩余和探针。 *)
Lemma eval_is_at_identity (c : C)
  (gy : fobj[@product_obj _ PshCart (PshExp P Q) P] c) :
  (@eval' _ _ (Functor_Category_Closed C) P Q) c gy
    ≈ (fst gy) c (id[c], snd gy).
Proof.
  simpl; apply proper_morphism; split; simpl;
    [ unfold op; cat | reflexivity ].
Qed.
End Readbacks.

Example presheaf_terminal_is_donor (C : Category) :
  presheaf_terminal C = @Functor_Category_Terminal (C^op) Sets Sets_Terminal
  := eq_refl.

(* * ** F: at C := 1 the construction recovers [Sets_Closed] / * ** F：在 C := 1 时，该构造恢复 [Sets_Closed] *)

Section AtOne.
Context (P Q : _1^op ⟶ Sets).

#[local] Notation OneCart :=
  (@Functor_Category_Cartesian (_1^op) Sets Sets_Cartesian).

Program Definition one_exp_to :
  fobj[PshExp P Q] ttt
    ~{Sets}~> @exponent_obj Sets Sets_Cartesian Sets_Closed
                 (fobj[P] ttt) (fobj[Q] ttt) :=
  {| morphism := fun alpha => {| morphism := fun p => alpha ttt (ttt, p) |} |}.
Next Obligation.
  proper.
  apply proper_morphism; split; simpl; [ reflexivity | assumption ].
Qed.

(*
 The [match] is forced: [obj[1]] is [poly_unit], which has no eta here,
 so a component written as a plain function elaborates its second
 projection at the wrong object and the definition is rejected. 

 --------
 [match] 被强制：[obj[1] 是 [poly_unit] ，它在这里没有 eta，所以作为普通函数编写的组件会在错误的对象上展开其第二投影，并且定义被拒绝。
*)
Program Definition one_from_comp
  (g : @exponent_obj Sets Sets_Cartesian Sets_Closed
         (fobj[P] ttt) (fobj[Q] ttt)) (d : obj[_1^op])
  : fobj[@product_obj _ OneCart (Curried_CoHom _1 ttt) P] d
      ~{Sets}~> fobj[Q] d :=
  match d with
  | ttt => {| morphism := fun hp => g (snd hp) |}
  end.
Next Obligation. proper. now apply proper_morphism. Qed.

Program Definition one_exp_from :
  @exponent_obj Sets Sets_Cartesian Sets_Closed (fobj[P] ttt) (fobj[Q] ttt)
    ~{Sets}~> fobj[PshExp P Q] ttt :=
  {| morphism := fun g => {| transform := one_from_comp g |} |}.
Next Obligation.
  destruct x, y, f, p; simpl.
  etransitivity; [ exact (@fmap_id _ _ Q ttt (g c)) | ].
  symmetry; apply proper_morphism; exact (@fmap_id _ _ P ttt c).
Qed.
Next Obligation.
  destruct x, y, f, p; simpl.
  symmetry.
  etransitivity; [ exact (@fmap_id _ _ Q ttt (g c)) | ].
  symmetry; apply proper_morphism; exact (@fmap_id _ _ P ttt c).
Qed.
Next Obligation. proper; destruct x0; exact (X H). Qed.

Program Definition one_exp_iso :
  @Isomorphism Sets (fobj[PshExp P Q] ttt)
    (@exponent_obj Sets Sets_Cartesian Sets_Closed
       (fobj[P] ttt) (fobj[Q] ttt)) :=
  {| to := one_exp_to; from := one_exp_from |}.
Next Obligation. destruct x0, p; reflexivity. Qed.
End AtOne.
