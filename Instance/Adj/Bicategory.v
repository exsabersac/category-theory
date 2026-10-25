Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Bicategory.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Adjunction.Compose.
Require Import Category.Adjunction.Square.
Require Import Category.Instance.Adjoints.
Require Import Category.Instance.Adj.
Require Import Category.Instance.Cat.Bicategory.

Generalizable All Variables.

(* * * Adj is two-dimensional: horizontal composition of conjugate pairs / * * Adj 是二维的：共轭对的水平组合 *)

(*
 nLab: https://ncatlab.org/nlab/show/2-category+of+adjunctions
 nLab: https://ncatlab.org/nlab/show/bicategory

 Mac Lane, "Categories for the Working Mathematician", 2nd ed., §IV.8,
 book p. 104 (PDF p. 113): Theorem 2, Exercise 1 and the closing
 remark; catalog ids maclane:IV.8:thm2, maclane:IV.8:ex1,
 maclane:IV.8:remark1.

 THEOREM 2, verbatim from the printed page:

 "Theorem 2. Given two conjugate pairs
 <sigma, tau> : <F,G,eta,eps> => <F',G',eta',eps'> : X -> A,
 <sigma-, tau-> : <F-,G-,eta-,eps-> => <F-',G-',eta-',eps-'> : A -> D
 the (horizontal) composite natural transformations sigma- sigma and
 tau tau- yield a conjugate pair sigma- sigma : F- F => F-' F',
 tau tau- : G' G-' => G G- of natural transformations for the
 composite adjunctions."

 The proof diagram on that page is the chain of hom-set bijections

 D(F-'F'x, d)  ~  A(F'x, G-'d)  ~  X(x, G'G-'d)
 |                |                 |
 D(F- F x, d)  ~  A(F x, G- d)  ~  X(x, G G- d)

 whose vertical maps are precomposition with (sigma- sigma)x on the
 left, precomposition with (sigma x) after postcomposition with
 (tau- d) in the middle, and postcomposition with (tau tau- d) on the
 right.  The closing remark and Exercise 1, again verbatim:

 "Moreover, this operation of (horizontal) composition is a bifunctor
 Adj(A, D) x Adj(X, A) -> Adj(X, D).                            (1)
 This means that Adj is a 'two-dimensional' category, as is Cat
 (see SS II.5).  There is additional discussion in Chapter XII."

 "1. Prove that horizontal composition is a bifunctor, as in (1), and
 that this implies an interchange law between horizontal and vertical
 composition of conjugate pairs."

 ** The orientation dictionary

 Instance/Adj.v declares [AdjObj C D] as a triple (F, U, F <| U) with
 F : D -> C and U : C -> D, so Mac Lane's adjunction <F,G> : X -> A,
 whose F runs X -> A, is an [AdjObj A X]: the TREE's [Adj C D] is the
 BOOK's Adj(D, C), its two arguments reversed.  A 1-cell x -> y of the
 bicategory below is therefore an adjunction whose RIGHT adjoint runs
 x -> y -- the orientation Instance/Adjoints.v already
 documents for its own 1-category -- and Mac Lane's X -> A is a 1-cell
 A -> X here, running along his G.

 The conjugate pair keeps Instance/Adj.v's variance, which is the
 book's own: sigma FORWARD on the left adjoints and tau BACKWARD on the
 right adjoints, so [ConjPair] carries
 [conj_left : adjobj_left x ==> adjobj_left y] and
 [conj_right : adjobj_right y ==> adjobj_right x], and the hom from x
 to y is [Conjugate (adjobj_adj y) (adjobj_adj x)].

 Display (1) is realized by [Adj_Hcompose], whose type at the tree's
 letters is

 (Adj y z (X) Adj x y) --> Adj x z

 pinned by the [Example] [Adj_Hcompose_shape] below, with [fst] the
 OUTER 1-cell exactly as in [Cat_Hcompose]
 (Instance/Cat/Bicategory.v, [([D,E] (X) [C,D]) --> [C,E]]).
 Read the correspondence with the
 book's own listing precisely.  Under the dictionary above his
 Adj(A, D) is the tree's [Adj D A] and his Adj(X, A) is [Adj A X], so
 his product Adj(A,D) x Adj(X,A) is the tree's [Adj D A (X) Adj A X],
 whereas [Adj_Hcompose] at x := D, y := A, z := X is
 [Adj A X (X) Adj D A --> Adj D X]: the two factors are listed in the
 OPPOSITE order, because his product puts first the factor that is
 outer along the LEFT adjoints while the tree puts first the factor
 that is outer along the RIGHT adjoints, and those are opposite.  The
 operation is the same one -- [adjobj_hcompose p q] has left adjoint
 [adjobj_left q (o) adjobj_left p] and right adjoint
 [adjobj_right p (o) adjobj_right q], which is Mac Lane's <F- F, G G->
 -- and the tree's listing is FORCED, since [Bicategory]'s [hcompose]
 field is declared at [bicat y z (X) bicat x y --> bicat x z].

 ** What is delivered, with its grade

 (A) THEOREM 2, route (a).  [conjugate_hcompose] (Qed; six rewrites after one
 [intros … ; simpl]): given [Conjugate A A' s t] and [Conjugate B B' sb tb],
 the two Godement products [nat_hcompose sb s] and [nat_hcompose t tb] are
 conjugate for [Adjunction_Compose A B] and [Adjunction_Compose A' B']. The
 proof is Mac Lane's diagram read left to right: [comp_assoc] regroups,
 [to_adj_nat_l] pulls the left leg out of the B' transpose, the two
 hypotheses fire, [to_adj_nat_r] pulls the right leg out of the A transpose,
 and one more [comp_assoc] closes.  BOTH reviewer checks are met by
 CONSTRUCTION rather than by comparison: the two components ARE
 Theory/Natural/Transformation.v's [nat_hcompose] and the two composite
 adjunctions ARE Adjunction/Compose.v's [Adjunction_Compose], and
 [hcomp_left_is_nat_hcompose], [hcomp_right_is_nat_hcompose] and
 [hcomp_obj_adj] pin all three at [eq_refl] once the bifunctor is in hand.
 Note what the proof does NOT need: [nat_hcompose]'s tau factorisation [t (V'
 e) (o) fmap[U] (tb e)] is exactly the one the goal produces, so no
 naturality step arises on this route.  What the proof DOES need is
 [Category.Instance.Sets] IMPORTED, though no [Sets] token occurs in the CODE
 below the require list (its only occurrences are in this header) and the
 module costs the closure nothing, being reachable already through
 Theory/Adjunction: with that one [Require Import] deleted, a byte-identical
 copy stops at [conjugate_hcompose]'s first [rewrite comp_assoc], the setoid
 rewrite refused on an unresolved [ProperProxy ...  Sets.morphism] --
 instance visibility, not a module, is what the line buys.

 (B) THEOREM 2, route (b), shipped as a CROSS-CHECK against #398. [conj_padL]
 and [conj_padR] (Program, two obligations each, both one application of
 [naturality] or [naturality_sym]) pad a transformation into the shape
 Adjunction/Square.v's [AdjointSquareT] wants at identity bounding functors.
 Then [routeb_hyp] records at [eq_refl] -- a Leibniz equality of TYPES --
 that [AdjointSquareT A A' Id[C] Id[D] (conj_padL s) (conj_padR t)] IS
 [Conjugate A A' s t], and [routeb_sigma] records at [eq_refl] that the sigma
 leg of Square.v's vertical paste at identity bounding functors IS
 [nat_hcompose] componentwise.  The tau leg is NOT: [routeb_tau] is `~=`
 only, one application of [naturality], because Adjunction/Square.v's
 [paste_v_tau] uses the OTHER factorisation of the Godement square ([fmap[U']
 (ta2 e) (o) ta1 (V e)] against [nat_hcompose]'s [t (V' e) (o) fmap[U] (tb
 e)]).  With those, [conjugate_hcompose_via_square] proves the SAME statement
 as [conjugate_hcompose] by [adjoint_square_paste_v] plus [routeb_tau]. So
 Theorem 2 IS #398's vertical pasting at identity bounding functors, up to
 two paddings per side and one naturality of tau on the right leg; the two
 proofs are independent and their terms are not compared at any strength.
 [conj_padL] and [conj_padR] duplicate in shape
 Instance/Cat/Bicategory/Conjugate.v's [Cat_conj_padL] and [Cat_conj_padR] (both are stated over arbitrary functors -- [conj_padL] over
 [P P' : X ⟶ Y], [Cat_conj_padL] with no adjunction in its discharged type --
 and the two are the same construction, their obligation scripts differing
 only by the leading [intros] that Conjugate.v's local [idtac] obligation
 tactic forces).  Requiring that file instead was MEASURED and declined: it
 takes this file's transitive in-project closure from 29 modules to 38, and
 the nine it adds include Adjunction/Natural/Transformation, whose class
 fields [unit] and [counit] SHADOW Theory/Adjunction.v's -- the
 same reason Adjunction/Square.v gives for keeping its own Cat
 comparison in a sibling file.

 (C) THE BIFUNCTOR.  [AdjIdObj X] is the identity 1-cell (the identity
 adjunction, no obligation); [adjobj_hcompose] composes two 1-cells;
 [conj_pair_hcompose] composes two 2-cells, its single obligation ONE
 [exact] of [conjugate_hcompose] with no tactic work; and
 [Adj_Hcompose] assembles them.  Its three functor obligations:
 [fmap_respects] componentwise, [fmap_id] by [cat], and [fmap_comp] --
 the middle-four interchange -- by an [exact] of
 [nat_hcompose_interchange] ON EACH LEG.  That helper is itself CAT's
 OWN interchange CONSUMED rather than restated: it is a plain
 [Definition] whose body is
 [@fmap_comp _ _ (@Cat_Hcompose C D E) _ _ _ (a2, b2) (a1, b1)], with
 no tactic at all, so Instance/Cat/Bicategory.v's proof is what
 discharges both legs.  Requiring Instance/Cat/Bicategory for it costs
 exactly one module (28 -> 29 with Adjunction/Square present).  Five
 [eq_refl] readbacks: [hcomp_obj_adj], [hcomp_obj_left],
 [hcomp_obj_right], [hcomp_left_is_nat_hcompose],
 [hcomp_right_is_nat_hcompose].

 (D) EXERCISE 1, DERIVED.  [conj_interchange] is one [exact] of
 [@fmap_comp _ _ (@Adj_Hcompose x y z) a b c f g] -- the bifunctor's
 own law and nothing else -- and the four corollaries
 [conj_interchange_left], [conj_interchange_right],
 [conj_interchange_sigma] and [conj_interchange_tau] are each a single
 [exact] of [fst] or [snd] of it at explicit arguments.  No
 interchange law is proved independently anywhere in this file.  Two
 spellings that do NOT work and were measured: [apply fmap_comp] does
 not close the goal (the hom-setoid of [Adj] is a conjunction and the
 goal displays unfolded), and a bare pair [(m, n)] does not elaborate
 at a product-category hom without its three object arguments given.

 (E) UNITORS AND ASSOCIATOR, as full [Isomorphism]s in [Adj]:
 [Adj_hunit_left], [Adj_hunit_right], [Adj_hassoc], each with both legs and
 both inverse laws, all four obligations closed by [cat] after a [simpl].
 THE UNITOR DICTIONARY IS CROSSED ONCE MORE THAN CAT'S.
 Instance/Fun.v names [nat_lambda F : F (o) Id ~= F] and [nat_rho F
 : Id (o) F ~= F], against the usual convention, and [Cat_Bicategory] sets
 [hunit_left := nat_rho]; here the LEFT unitor uses [nat_lambda] on the left
 adjoints and [nat_rho] on the right adjoints, because [adjobj_hcompose
 (AdjIdObj y) f] has left adjoint [adjobj_left f (o) Id[y]] and right adjoint
 [Id[y] (o) adjobj_right f] -- the left adjoints compose in the opposite
 order to the right ones. Four [eq_refl] readbacks pin exactly that
 ([hunit_left_obj_left] and its three siblings).  For the same reason the
 associator cannot be one [iso_sym (nat_alpha f g h)] as in Cat: its two
 components take [nat_alpha]'s three functor arguments in OPPOSITE orders
 (left adjoints h, g, f; right adjoints f, g, h), and BOTH legs are the [to]
 direction.  Everything from [Adj_Hcompose_shape] to the end of the file runs
 under [#[local] Obligation Tactic := program_simpl], set after (C)'s
 [idtac]; that is NOT a restoration of the tree default, which
 Lib/Tactics.v declares as [cat_simpl], and it is load-bearing: a
 byte-identical copy with [cat_simpl] on that line stops inside
 [Adj_hunit_left]'s obligations with "No obligations remaining", [cat_simpl]
 having already discharged what the explicit [Next Obligation] scripts of (E)
 then find nothing left to prove.  The [#[local]] keeps it inside this
 module.

 (F) THE FIVE COHERENCE LAWS, stated in [Adj]'s hom-setoid (so each is
 a PAIR of `~=`) through [adj_hcomp2], which is [Adj_Hcompose]'s [fmap]
 at a pair and which [adj_hcomp2_is_conj_pair_hcompose] reads back at
 [eq_refl]: [Adj_hunit_left_natural], [Adj_hunit_right_natural],
 [Adj_hassoc_natural], [Adj_triangle], [Adj_pentagon].  Four of the
 five close by [split; simpl; intros; cat]; only [Adj_hassoc_natural]
 needs the extra [rewrite !fmap_id, fmap_comp], which is the same extra
 step Instance/Cat/Bicategory.v's [Cat_hassoc_natural] takes.

 (G) THE BICATEGORY.  [Adj_Bicategory] is built with the RAW
 [Build_Bicategory], never [Build_Bicategory'], for the reason
 Instance/Cat/Bicategory.v states for Cat and which was measured
 again here: the [symmetry]-derived [comp_assoc_sym] of the smart
 constructor breaks record eta, [bicat x y] is then no longer [Adj x y],
 and [hcompose] no longer typechecks against [Adj_Hcompose].  Feeding
 [Adj]'s own ten projections keeps eta, so [Adj_bicat_is_Adj] closes at
 [eq_refl], as do [Adj_hcompose_readback], [Adj_bi1id_readback] and
 [Adj_hcomp2_readback].  Two further readbacks BRIDGE to Cat at
 [eq_refl]: the two legs of a horizontal composite of 2-cells here ARE
 Cat's own [hcomp2] on the underlying left and right adjoints
 ([Adj_hcomp2_left_is_Cat_hcomp2], [Adj_hcomp2_right_is_Cat_hcomp2]),
 with the two arguments swapped on the left leg, which is the
 contravariance of [adjobj_left] made visible.  A plain [Definition],
 not an [Instance] (there is no bicategory of bicategories to resolve
 in), following [Cat_Bicategory]'s precedent.

 (H) A BRIDGE TO Instance/Adjoints.v.  [adjobj_of_morphism] and
 [morphism_of_adjobj] pass between that file's [adj_morphism] record and
 [AdjObj]; the RECORD round trip [adjoints_round_record] closes at [eq_refl]
 ([adj_morphism] has primitive projections with eta).  The sigT round trip
 does NOT (stdlib [sigT] is not covered by this repo's [Set Primitive
 Projections]), and neither does the composition comparison: [adjunction (mA
 (o) mB) = Adjunction_Compose Aa Bb] is a CONVERSION refusal at one and the
 same type, since [Adjoints] composes by Instance/Adjoints.v's [adj_comp].
 Both were measured and are to be pinned in the probe rather than carried
 here.  The positive half is already in tree: Adjunction/Compose.v's
 [Adjunction_Compose_adj_comp_to] and [_from] show the two constructions have
 definitionally equal transposes in both directions.

 ** Strict or weak: measured, and it is WEAK

 The structure assembled here is a [Bicategory] and not a strict
 2-category, for a TYPING reason and not a stylistic one.
 [Adjunction_Compose (Adjunction_Compose A B) Cc] and
 [Adjunction_Compose A (Adjunction_Compose B Cc)] do not even share a
 type -- the first is [H (o) (G (o) F) <| U (o) V (o) W] and the second
 [H (o) G (o) F <| U (o) (V (o) W)] -- so the associativity equation is
 not statable at all; measured, with both sides' implicits written out,
 the rejection is a plain has-type mismatch with no "cannot unify" and
 no universe clause.  Both unit laws are refused the same way.  One
 level down the underlying functor equations ARE statable and are
 refused at CONVERSION, with [fobj] and [fmap] agreeing definitionally
 on both sides, so what differs is exactly the three law fields of
 [Compose] -- the fact Adjunction/Pare.v and Instance/Cat/Bicategory.v
 already record.  At the [AdjObj] level, [adjobj_hcompose (AdjIdObj D) a
 = a] and the associativity of [adjobj_hcompose] are likewise refused at
 conversion, as is the left-adjoint component of either.

 Theory/TwoCategory.v's arrows-only [StrictTwoCategory] wants a strict 1-cell
 layer with Leibniz equations, so it is not inhabitable here for the same
 reason that file's own header gives for Cat -- underivability recorded, as
 that header is careful to say, not a refutation theorem.  Its cast-carrying
 [Class TwoCategory] does NOT need strictness, and the route with [tcat :=
 Instance/Adjoints.v]'s [Adjoints] was MEASURED and NOT taken.  Three
 findings decided it.  First, [Adjoints] composes by [adj_comp], and
 [adjunction (mA (o) mB) = Adjunction_Compose Aa Bb] is refused at conversion
 (same type), so on that route the conjugacy of the composite would be stated
 for [adj_comp] and not for [Adjunction_Compose] as the issue's second
 reviewer check demands. Second, all three of [tassoc_cast], [tunitl_cast]
 and [tunitr_cast] are genuinely needed: the 2-cell types at the two
 bracketings, and at the unit padding, are measured NON-CONVERTIBLE (each
 [eq_refl] refused with `cannot unify`); no inequality is proved.  Third,
 [Adjoints]'s arrows are RECORDS where [AdjObj] is a sigT, and only the
 record round trip holds at [eq_refl], so every cell would carry a
 record-to-sigT conversion.  Nothing on that route was built; the estimate
 that it is strictly more work is an ARGUMENT from those three measurements
 plus the field counts (25 fields against [Build_Bicategory]'s 21 arguments,
 ten of which are here literally [Adj]'s own projections), not a compiled
 comparison.

 ** Universes

 Measured off BOTH binder and constraint block, and the two halves of the
 identification are recorded in DIFFERENT places, which is why both must be
 read.  Every constant that binds categories binds them at [Category@{_ h h}]
 -- hom identified with proof -- in the BINDER, and no constraint block
 anywhere in the file states that.  The further identification of the three
 (or four) categories' HOM levels with one another is in the BINDER for the
 [Adj]-level constants ([adjobj_hcompose] reads [Category@{u3 u9 u9}],
 [Category@{u8 u9 u9}], [Category@{u2 u9 u9}], one shared [u9], its block
 carrying [u9 < u0] and bounds and no equation; likewise
 [conj_pair_hcompose], [Adj_Hcompose], [nat_hcompose_interchange], the two
 unitors and [Adj_hassoc]), and in the BLOCK for the five constants of (A)
 and (B) -- [conjugate_hcompose] in [Section HorizontalCompose], and
 [conjugate_hcompose_via_square], [routeb_hyp], [routeb_sigma] and
 [routeb_tau] in [Section RouteB], the two sections declaring
 character-identical [Context] lines -- whose binders keep the hom levels
 apart ([u0], [u2] and, for the four that bind [E], [u4]; [routeb_hyp] binds
 only [C] and [D]) and whose blocks then carry [u0 = u2] and [u0 = u4] (the
 two Theorem-2 constants one equation more, [u5 = u8] between the two Sets
 levels; the other 62 blocks carry no equation at all).  Both halves are
 INHERITED.  The binder half has several donors, each sufficient alone -- at
 levels declared apart, [Adjunction] and [Compose] are each refused with no
 other donor in the command (the probe pins both); [nat_hcompose],
 [Cat_Hcompose], Instance/Adj.v's [AdjObj] and [Adj], and this file's
 [adjobj_hcompose] and [Adj_Hcompose] are refused at their own signatures
 while the bare categories pass, though each contains a donor and so is not
 shown to add an identification of its own; [ConjPair] refuses at its
 [AdjObj] argument and measures nothing of its own; and [Functor] and
 [Transform] are NOT donors, a functor and a transformation between two
 functors both being accepted at those levels -- so a constant such as
 [conj_padL], whose type mentions only [Functor], [Transform], [Id] and
 [Compose], inherits it from [Compose] and not from anything in
 Instance/Adj.v; functors in BOTH directions moreover identify the two hom
 levels with each other before any adjunction is formed.  The block half is
 the two sections' [Context]: each declares functors in both directions
 between [C] and [D] and between [C] and [E], the donor named a sentence ago,
 and section discharge hands the resulting equations to every constant
 declared inside -- measured out of tree: a section holding only functors in
 both directions between those pairs gives a trivial [x = x] example over [D]
 the block [u0 = u2], [u0 = u4] with [C] and [E] nowhere in its statement,
 while one functor per pair gives only the bounds [u2 <= u0], [u0 <= u4] --
 which is why [routeb_hyp], binding only [C] and [D], still carries [u0 =
 u4].  Adjunction/Compose.v's [Adjunction_Compose], whose own block
 carries [u0 = u2], [u0 = u4], [u5 = u7], accounts only for the extra [u5 =
 u8] of the two Theorem-2 constants -- it is not the source of the other two,
 [routeb_sigma] and [routeb_tau] carrying both with no adjunction in their
 types.  The isolating probes are in the probe file, not here.  In every case
 the OBJECT universes stay free of the hom universes and of each other -- no
 equation anywhere in the file touches an object universe -- and carry bounds
 only: [<=] bounds, except in the nine constants that mention
 [Adj_Bicategory] or [Adjoints], where the object universe additionally sits
 strictly below the 0-cell universe ([Adj_bicat_is_Adj], the three
 [Adj_*_readback]s and the two [Adj_hcomp2_*_is_Cat_hcomp2] carry [u6 < u];
 [adjobj_of_morphism], [morphism_of_adjobj] and [adjoints_round_record] carry
 [u4 < u]).  [Adj_Bicategory@{u u0 u1 u2 u3 u4 u5 u6 u7} : Bicategory@{u u0
 u1 u0 u1}] is EXACTLY [Cat_Bicategory]'s instantiation shape (nine universe
 parameters against Cat's six), its block [u1 < u0], [u4 < u], [u7 < u], [u7
 < u5] and bounds with no equation, and the 0-cell type [Category] sits one
 level up just as Cat's does.  There is no word-bounded [Set] in any binder
 or block of any constant of this file.

 ** Closure

 The transitive in-project closure of the require list above, excluding
 this file, is 29 modules.  Drop-one marginals: Adjunction/Square 4
 (it brings Adjunction/Map, Construction/Quotient and
 Functor/Construction/Product with it), Instance/Adj 1,
 Instance/Cat/Bicategory 1, and every other require 0.  Without
 Adjunction/Square and without Instance/Cat/Bicategory the closure
 would be 24: route (b) costs 4 and consuming Cat's interchange costs
 1, both paid deliberately.

 ** A stale sentence of the issue

 Its current-state section says "Instance/Adj.v -- a hom-category of
 adjunctions exists, but with no conjugacy condition on its arrows".
 That has been stale since #395: [ConjPair] carries [conj_pair_law] as
 its third field, so an arrow of [Adj C D] is a conjugate pair and not
 a bare pair of transformations, and that file's own header records the
 retyping.

 ** Pinned

 Test/ProbeAdjBicat399.v carries 27 refutation commands: one instrument check
 plus 26 negatives of THREE kinds told apart by the error TEXT.  ELEVEN are
 CONVERSION refusals (both bracketings and both unit paddings of [Compose];
 the four [adjobj_hcompose] laws; the route-(b) tau leg; [Adjoints]'s
 composition against [Adjunction_Compose]; the sigT round trip; and the
 [Build_Bicategory'] churn), FOUR are TYPING refusals (the associativity and
 the two unit laws of [Adjunction_Compose], which are not statable at all,
 and the sigma leg as a WHOLE transformation) and ELEVEN are FORMABILITY
 refusals ([Adjunction] and [Compose] each a donor of hom = proof on their
 own; [AdjObj], [Adj], [ConjPair], [nat_hcompose], [Cat_Hcompose],
 [adjobj_hcompose] and [Adj_Hcompose] inheriting it; and functors in BOTH
 directions identifying the two hom levels before any adjunction is formed).
 Each negative was stripped ONE AT A TIME, compiled alone and its whole error
 read; every constant a negative names is guarded by a [Check] outside every
 refutation command (118 identifiers inside the negatives, 93 also outside,
 the 25 exceptions being two keywords, seven bound variables, the fifteen
 refuted declaration names and the instrument's absent name);
 rename-simulated 15/15 over the constants of this file that a negative
 names, every break landing on a [Check] line.  Two corrections to
 expectation are recorded there: the [Build_Bicategory'] refusal carries a
 "cannot unify" clause and so is CONVERSION rather than TYPING, and the
 [ConjPair] negative refuses at its [AdjObj] ARGUMENT, so whether [ConjPair]
 identifies anything of its own is UNKNOWN, not refuted.  [make todo] grows
 by 41, ALL in the probe; this file contributes ZERO.

 ** Not delivered

 No [TwoCategory] instance, for the three measured obstructions above;
 no double category of adjunctions, and no pasting functoriality of
 mates in an ARBITRARY bicategory -- Theory/Bicategory/Mates.v's
 descope ledger entry 10 is NARROWED by this file, not discharged, and
 its note is edited in the same commit to say exactly that.  No
 comparison of the two Theorem-2 proof terms at any strength (both are
 [Qed], so nothing would reduce).  No naturality of any identification
 in C, D or E, and no functoriality of [Adj_Hcompose] in its three
 category arguments.  No concrete witness at a named pair of
 categories, so nothing here is instantiated.  No strict 2-category and
 no Leibniz equation between the two bracketings.  No relation to
 Instance/Cat/Bicategory/Conjugate.v's mate identification beyond the
 shape of the padding cited in (B).  No pseudofunctor out of
 [Adj_Bicategory] and no comparison with [Cat_Bicategory] beyond the
 two [eq_refl] leg readbacks of (G).  Nothing is registered as an
 [Instance]. 

 --------
 nLab: https://ncatlab.org/nlab/show/2-category+of+adjunctions
 nLab: https://ncatlab.org/nlab/show/bicategory

 Mac Lane，《为工作中的数学家准备的范畴论》，第二版，第§IV.8节，书页104（PDF页113）：定理2，练习1以及结语；目录ID maclane:IV.8:thm2, maclane:IV.8:ex1, maclane:IV.8:remark1。

 定理2，原文如下：

 “定理2。给定两个共轭对
 <sigma, tau> : <F,G,eta,eps> => <F',G',eta',eps'> : X -> A,
 <sigma-, tau-> : <F-,G-,eta-,eps-> => <F-',G-',eta-',eps-'> : A -> D
 其（水平）复合自然变换 sigma- sigma 和 tau tau- 产生一个共轭对 sigma- sigma : F- F => F-' F',
 tau tau- : G' G-' => G G-，它们是复合伴随中的自然变换。”

 该页的证明图是同态集双射链。D(F-'F'x, d)  ~  A(F'x, G-'d)  ~  X(x, G'G-'d)
 |                |                 |
 D(F- F x, d)  ~  A(F x, G- d)  ~  X(x, G G- d)

 其垂直映射在左侧为与 (sigma- sigma)x 的预合成，中间为在与 (tau- d) 后合成后与 (sigma x) 的预合成，右侧为与 (tau tau- d) 的后合成。闭幕语和练习 1，再次逐字如下：

 “此外，这种（水平）组合操作是一个双函子
 Adj(A, D) x Adj(X, A) -> Adj(X, D)。                            (1)
 这意味着 Adj 是一个‘二维’范畴，Cat 也一样（参见 SS II.5）。第 XII 章中有进一步讨论。”1. 证明水平复合是一个双函子，如公式 (1) 所示，并且这意味着共轭对的水平复合与垂直复合之间存在交换律。

 **方向字典

 Instance/Adj.v 将 [AdjObj C D] 声明为三元组 (F, U, F <| U)，其中 F : D -> C 和 U : C -> D，因此 Mac Lane 的挨次 <F,G> : X -> A，其中 F 从 X -> A 运行，是一个 [AdjObj A X]：该 TREE 的 [Adj C D] 是 BOOK 的 Adj(D, C)，其两个参数顺序相反。因此，下述二范畴的 1-箭头 x -> y 是一个挨次，其右伴随沿 x -> y 运行 —— 方向 Instance/Adjoints.v 已经记录了其自身 1-范畴 —— 而 Mac Lane 的 X -> A 在这里是 A -> X 的 1-箭头，沿着他的 G 运行。共轭对保持了实例/形容词 v 的方差，即书本自身的：左伴随上的 sigma FORWARD 和右伴随上的 tau BACKWARD，所以 [ConjPair] 包含 [conj_left : adjobj_left x ==> adjobj_left y] 和 [conj_right : adjobj_right y ==> adjobj_right x]，并且从 x 到 y 的同态是 [Conjugate (adjobj_adj y) (adjobj_adj x)]。

 显示（1）通过 [Adj_Hcompose] 实现，其在树字母上的类型为

 (Adj y z (X) Adj x y) --> Adj x z由下面的 [Example] [Adj_Hcompose_shape] 固定，[fst] 是 OUTER 1-cell，正如在 [Cat_Hcompose] 中的情况一样（Instance/Cat/Bicategory.v，[([D,E] (X) [C,D]）--> [C,E]）。精确阅读与书中自身列表的对应关系。在上面的字典下，他的 Adj(A, D) 是树的 [Adj D A]，而他的 Adj(X, A) 是 [Adj A X]，因此他的乘积 Adj(A,D) x Adj(X,A) 是树的 [Adj D A (X) Adj A X]，而 [Adj_Hcompose] 在 x := D, y := A, z := X 时是 [Adj A X (X) Adj D A --> Adj D X]：两个因子列出的顺序相反，因为他的乘积将沿左伴随的因子放在前面，而树则将沿右伴随的因子放在前面，这两者是相反的。该操作是同一个——[adjobj_hcompose p q] 有左伴随 [adjobj_left q (o) adjobj_left p] 和右伴随 [adjobj_right p (o) adjobj_right q]，这是 Mac Lane 的 <F- F, G G->——并且树的列表是强制的，因为 [Bicategory] 的 [hcompose] 字段是在 [bicat y z (X) bicat x y --> bicat x z] 处声明的。

 ** 所交付的内容及其等级(A) 定理 2，路线 (a)。[conjugate_hcompose]（证毕；一次[intros … ; simpl]后的六次重写）：给定[Conjugate A A' s t]和[Conjugate B B' sb tb]，两个 Godement 积 [nat_hcompose sb s] 和 [nat_hcompose t tb] 对于 [Adjunction_Compose A B] 和 [Adjunction_Compose A' B'] 是共轭的。证明是按从左到右读的 Mac Lane 图：[comp_assoc] 重新组合，[to_adj_nat_l] 将左支从 B' 转置中拉出，两个假设生效，[to_adj_nat_r] 将右支从 A 转置中拉出，再一次 [comp_assoc] 完成闭合。两个审阅者检查通过 CONSTRUCTION 实现，而不是通过比较：两个分量是 Theory/Natural/Transformation.v 的 [nat_hcompose]，两个复合伴随是 Adjunction/Compose.v 的 [Adjunction_Compose]，以及 [hcomp_left_is_nat_hcompose]、[hcomp_right_is_nat_hcompose] 和 [hcomp_obj_adj] 一旦双函子准备好，就将所有三个固定在 [eq_refl]。注意证明不需要的内容：[nat_hcompose] 的 tau 分解 [t (V' e) (o) fmap [U] (tb e)] 恰好是目标产生的分解，所以这条路径上不会出现自然性步骤。证明确实需要的是 [Category.Instance.Sets] 导入，尽管在 require 列表下方的代码中没有 [Sets] 令牌出现（它唯一出现的地方是在这个头部），并且该模块对闭包没有成本，因为它已经可以通过 Theory/Adjunction 访问：删除那一个 [Require Import] 后，一个字节完全相同的副本会在 [conjugate_hcompose] 的第一个 [rewrite comp_assoc] 处停止，集合重写在一个未解决的 [ProperProxy ...  Sets.morphism] 上被拒绝 —— 这一行买到的是实例可见性，而不是模块。(B) 定理 2，路线 (b)，作为对 #398 的交叉检验而发运。[conj_padL] 和 [conj_padR]（程序，每个有两个义务，都应用一次 [naturality] 或 [naturality_sym]）将一个变换填充到形状 Adjunction/Square.v 的 [AdjointSquareT] 想要的在恒等界定函子处。然后 [routeb_hyp] 在 [eq_refl] 记录——类型的莱布尼茨等式——[AdjointSquareT A A' Id[C] Id [D] (conj_padL s) (conj_padR t) 是 [Conjugate A A' s t]，并且 [routeb_sigma] 在 [eq_refl] 记录 Square.v 的垂直粘贴在恒等界定函子处的 sigma 腿是 [nat_hcompose] 分量式。τ 边不是：[routeb_tau] 是 `~=`，仅仅是 [naturality] 的一次应用，因为 Adjunction/Square.v 的 [paste_v_tau] 使用 Godement 方形的另一个分解（[fmap[U'] (ta2 e) (o) ta1 (V e)] 对比 [nat_hcompose] 的 [t (V' e) (o) fmap[U] (tb e)]）。借助这些，[conjugate_hcompose_via_square] 通过 [adjoint_square_paste_v] 加上 [routeb_tau] 证明与 [conjugate_hcompose] 相同的命题。所以定理 2 是 #398 在身份界限函子上的垂直粘贴，最多每边有两个填充，以及 τ 在右边的一个自然性；这两个证明是独立的，它们的项在任何强度下都不进行比较。[conj_padL] 和 [conj_padR] 在形状上重复
 Instance/Cat/Bicategory/Conjugate.v 中的 [Cat_conj_padL] 和 [Cat_conj_padR]（两者都在任意函子上声明——ZWZ81WZZ 在 [P P' : X ⟶ Y] 上，ZWZ83WZZ 在其释放类型中没有伴随——并且这两者是相同的构造，它们的义务脚本仅由于 Conjugate.v 的本地 [idtac] 义务策略强制的前导 [intros] 而不同）。要求使用该文件代替被 MEASURED 并拒绝：它将此文件的传递性项目内闭包从 29 个模块增加到 38 个，并且它新增的九个包括 Adjunction/Natural/Transformation，其类字段 [unit] 和 [counit] 遮蔽（SHADOW）了 Theory/Adjunction.v 的字段——这是 Adjunction/Square.v 保持其兄弟文件中 Cat 比较的相同原因。(C) 双函子。[AdjIdObj X] 是恒等 1-胞（恒等伴随，无义务）；[adjobj_hcompose] 组合两个 1-胞；[conj_pair_hcompose] 组合两个 2-胞，其唯一义务是 [exact] 与 [conjugate_hcompose]，无策略工作；[Adj_Hcompose] 将它们组装起来。它的三个函子义务：[fmap_respects] 按分量，[fmap_id] 通过 [cat]，以及 [fmap_comp]——中间四个交换——通过 [exact] 在每条边上的 [nat_hcompose_interchange]。那个辅助本身就是 CAT 的自身交换，被消耗而不是重述：它是一个普通的 [Definition]，其主体是 [@fmap_comp _ _ (@Cat_Hcompose C D E) _ _ _ (a2, b2) (a1, b1)]，完全没有策略，因此 Instance/Cat/Bicategory.v 的证明解决了两条边。为它要求 Instance/Cat/Bicategory 恰好消耗一个模块（在有 Adjunction/Square 时从 28 -> 29）。五
 [eq_refl]  回放：[hcomp_obj_adj] ，[hcomp_obj_left] ，
 [hcomp_obj_right] ，[hcomp_left_is_nat_hcompose] ，
 [hcomp_right_is_nat_hcompose]。

 (D) 练习 1，派生。[conj_interchange] 是 [exact] 的一个 [@fmap_comp _ _ (@Adj_Hcompose x y z) a b c f g] —— 双函子自身的定律，仅此而已 —— 四个推论 [conj_interchange_left] ，[conj_interchange_right] ，
 [conj_interchange_sigma] 和 [conj_interchange_tau] 各自是 [fst] 的一个单独 [exact] 或者在显式参数下的 [snd]。这个文件中没有任何地方独立证明互换律。两个无效并已测量的写法：[apply fmap_comp] 无法完成目标（[Adj] 的同态-集合是一个合取，目标展示已展开），而一个裸对 [(m, n)] 在没有给出三个对象参数的情况下无法在积范畴的 Hom 中展开。(E) 单元器和联合器，作为完整的 [Isomorphism] s 在 [Adj] 中：[Adj_hunit_left]、[Adj_hunit_right]、[Adj_hassoc]，每个都有两条腿和两条逆律，所有四个义务在 [simpl] 之后由 [cat] 关闭。单元器词典比猫的那一个多交叉一次。实例/函数名 [nat_lambda F : F (o) Id ~= F] 和 [nat_rho F : Id (o) F ~= F]，违反了通常的惯例，并且 [Cat_Bicategory] 设置 [hunit_left := nat_rho]；这里左单元器在左伴随上使用 [nat_lambda]，在右伴随上使用 [nat_rho]，因为 [adjobj_hcompose (AdjIdObj y) f] 的左伴随是 [adjobj_left f (o) Id[y] 和右伴随是 [Id[y] (o) adjobj_right f] —— 左伴随的组合顺序与右伴随相反。四个 [eq_refl] 回读正好对应这个 ([hunit_left_obj_left] 及其三个兄弟)。出于同样的原因，结合子不能是 Cat 中的 [iso_sym (nat_alpha f g h)]：它的两个分量将 [nat_alpha] 的三个函子参数以相反的顺序接受（左伴随 h、g、f；右伴随 f、g、h），并且两个分支都是 [to] 方向。从 [Adj_Hcompose_shape] 到文件末尾的所有内容都在 [#[local] 义务策略 := program_simpl] 下运行，该策略在 (C) 的 [idtac] 之后设置；这并不是树默认的恢复，Lib/Tactics.v 将其声明为 [cat_simpl]，并且是承重的：在该行的 [cat_simpl] 上完全相同的字节副本会在 [Adj_hunit_left] 的义务中停止并显示“No obligations remaining”，[cat_simpl] 已经完成了 (E) 的显式 [Next Obligation] 脚本原本要证明的内容后，发现没有剩余要证明的内容。[#[local] ] 将其保留在此模块内。(F) 五条相干性定律，在 [Adj] 的同态集合（因此每一条都是 `~=` 的一对）中通过 [adj_hcomp2] 陈述，这是 [Adj_Hcompose] 在一对上的 [fmap]，而 [adj_hcomp2_is_conj_pair_hcompose] 在 [eq_refl] 读取：ZW155WZZ，ZW156WZZ，ZW157WZZ，ZW158WZZ，ZW159WZZ。五条中的四条由 [split; simpl; intros; cat] 结束；只有 [Adj_hassoc_natural] 需要额外的 [rewrite !fmap_id, fmap_comp]，这与 Instance/Cat/Bicategory.v 中 [Cat_hassoc_natural] 采取的额外步骤相同。(G) 双范畴。[Adj_Bicategory] 是用 RAW [Build_Bicategory] 构建的，从未使用 [Build_Bicategory']，原因是 Instance/Cat/Bicategory.v 对 Cat 的说明，并且在这里再次测量：由 [symmetry] 派生的 [comp_assoc_sym] 的智能构造器破坏了 eta，[bicat x y] 因此不再是 [Adj x y]，[hcompose] 也不再可以通过 [Adj_Hcompose] 的类型检查。使用 [Adj] 自己的十个投影保持了 eta，因此 [Adj_bicat_is_Adj] 在 [eq_refl] 闭合，[Adj_hcompose_readback]、[Adj_bi1id_readback] 和 [Adj_hcomp2_readback] 也是如此。两个进一步的回读 BRIDGE 到 Cat 位于 [eq_refl]：这里 2-胞复合的水平复合的两条腿是 Cat 自己在底层左右伴随 ([Adj_hcomp2_left_is_Cat_hcomp2], [Adj_hcomp2_right_is_Cat_hcomp2]) 上的 [hcomp2]，左腿上交换了两个参数，这显示了 [adjobj_left] 的逆变性。一个普通的 [Definition]，  
 不是 [Instance]（没有二元类的二元类可供解决），遵循 [Cat_Bicategory] 的先例。(H) 通向 Instance/Adjoints.v 的桥梁。[adjobj_of_morphism] 和 [morphism_of_adjobj] 在该文件的 [adj_morphism] 记录和 [AdjObj] 之间传递；RECORD 往返 [adjoints_round_record] 在 [eq_refl] 关闭（[adj_morphism] 具有带 eta 的原始投影）。sigT 往返不行（stdlib [sigT] 不在本仓库的[设置原始投影]覆盖范围内），合成比较也不行：[adjunction (mA (o) mB) = Adjunction_Compose Aa Bb] 在同一类型上是 CONVERSION 拒绝，因为 [Adjoints] 由 Instance/Adjoints.v 的 [adj_comp] 组成。两者都已测量，应在探针中固定，而不是在此处携带。正半部分已在树中：Adjunction/Compose.v 的 [Adjunction_Compose_adj_comp_to] 和 [_from] 显示这两种构造在两个方向上具有定义上相等的转置。** 严格或宽松：经过测量，它是宽松的这里组装的结构是一个 [Bicategory]，而不是严格的 2-范畴，这是出于类型原因而不是风格原因。[Adjunction_Compose (Adjunction_Compose A B) Cc] 和 [Adjunction_Compose A (Adjunction_Compose B Cc)] 甚至不共享类型——前者是 [H (o) (G (o) F) <| U (o) V (o) W]，后者是 [H (o) G (o) F <| U (o) (V (o) W)]——所以结合律方程根本无法表示；如果测量，把双方的隐式写出来，拒绝的原因只是类型不匹配，没有“无法统一”也没有宇宙条款。两个单位律也以同样的方式被拒绝。再下一层，底层函子方程是可以表示的，并且在转换时被拒绝，[fobj] 和 [fmap] 在双方上在定义上是一致的，所以区别正是 [Compose] 的三个律字段——这是 Adjunction/Pare.v 和 Instance/Cat/Bicategory.v 已经记录的事实。在 [AdjObj] 级别，[adjobj_hcompose (AdjIdObj D) a = a] 以及 [adjobj_hcompose] 的结合律在转换时同样被拒绝，任一的左伴随分量也是如此。Theory/TwoCategory.v 的只含箭头的 [StrictTwoCategory] 需要严格的 1-元层并带有 Leibniz 方程，因此在这里不可居住，原因与该文件自身头部给出的 Cat 理由相同——记录了不可导出性，该头部明确说明，这不是反证定理。它携带 cast 的 [Class TwoCategory] 不需要严格性，并且通过 [tcat := Instance/Adjoints.v] 的 [Adjoints] 的路线已经被测量但未采用。三个发现决定了这一点。首先，[Adjoints] 可通过 [adj_comp] 组合，而 [adjunction (mA (o) mB) = Adjunction_Compose Aa Bb] 在转换时遭到拒绝（类型相同），因此在那个路径上，复合的共轭性将为 [adj_comp] 而不是 [Adjunction_Compose] 陈述，正如问题的第二位审查员检查所要求的。其次，[tassoc_cast]、[tunitl_cast] 和 [tunitr_cast] 都是真正需要的：在两个括号处的两种单元类型，以及在单元填充处的单元类型，被测量为不可转换（每个 [eq_refl] 都被 `cannot unify` 拒绝）；没有不等式被证明。第三，[Adjoints] 的箭头是记录类型，而 [AdjObj] 是 sigT，并且只有在 [eq_refl] 上记录的往返是成立的，因此每个单元都将携带记录到 sigT 的转换。在该路线上的内容未被构建；认为它严格需要更多工作量的估算，是根据这三项测量加上字段计数（25 个字段对 [Build_Bicategory] 的 21 个参数，其中十个实际上是 [Adj] 自己的投影）的推论，而非编译比较。  

 ** 宇宙分别测量了活页夹和约束块，识别的两个部分记录在不同的地方，这就是为什么必须读取两者的原因。每个绑定类别的常量都在活页夹中的 [Category@{_ h h}] 处绑定它们——通过证明识别 —— 文件中的任何地方都没有约束块声明这一点。三个（或四个）类别的 HOM 水平进一步相互识别在 BINDER 中，用于 [Adj] 级常数（[adjobj_hcompose] 包括 [Category@{u3 u9 u9}]、[Category@{u8 u9 u9}]、[Category@{u2 u9 u9}]、一个共享的 [u9]，其区块携带 [u9 < u0] 以及边界且无方程；同样 [conj_pair_hcompose]、[Adj_Hcompose]、[nat_hcompose_interchange]、两个单位器和 [Adj_hassoc]），以及在 (A) 和 (B) 五个常数的 BLOCK 中——[conjugate_hcompose] 在 [Section HorizontalCompose] 中，以及 [conjugate_hcompose_via_square]、[routeb_hyp]、[routeb_sigma] 和 [routeb_tau] 在 [Section RouteB] 中，两个部分声明字符相同的 [Context] 行——其绑定器保持 HOM 水平分离（[u0]、[u2]，并且对于绑定 [E] 的四个，[u4]；[routeb_hyp] 仅绑定 [C] 和 [D]），其区块随后携带 [u0 = u2] 和 [u0 = u4]（两个定理-2常数多一个方程，[u5 = u8]在两个集合层之间；另有62个区块完全不包含方程）。两半都是遗传的。绑定器的一半有几个供体，每个单独足够——在单独声明的级别上，[Adjunction] 和 [Compose] 各自被拒绝且命令中没有其他供体（探针都测试了）；[nat_hcompose]、[Cat_Hcompose]、Instance/Adj.v 的 [AdjObj] 和 [Adj]，以及此文件的 [adjobj_hcompose] 和 [Adj_Hcompose] 在它们各自的签名处被拒绝，而裸类别通过，尽管每个类别都包含一个供体，因此并未显示它自己增加了标识；[ConjPair] 在其 [AdjObj] 参数处被拒绝，并且没有测量它自己的内容；而 [Functor] 和 [Transform] 不是供体，一个是函子，一个是两个函子之间的变换，在这些级别都被接受——所以像 [conj_padL] 这样的常量，其类型只提到 [Functor]、[Transform]、[Id] 和 [Compose]，是从 [AdjObj C D]继承的。73WZZ，而不是来自 Instance/Adj.v 中的任何内容；而且双向的函子在形成任何伴随之前，会将两个同伦层相互识别。块的一半是两个部分的 [Context]：每个部分都在 [C] 和 [D] 之间以及 [C] 和 [E] 之间声明函数子，前面一句话提到的供体，而部分放电将生成的方程交给内部声明的每个常量——从树中测量：一个仅包含在这些配对之间的双向函数子的部分提供了一个平凡的 [x = x] 示例，位于 [D] 块上，[u0 = u2]、[u0 = u4] 与 [C] 和 [E] 在其声明中都未出现，而每对一个函数子只给出界限 [u2 <= u0]、[u0 <= u4]——这就是为什么 [routeb_hyp] 仅绑定 [C] 和 [D] 仍然承载 [u0 = u4]。Adjunction/Compose.v 的 [Adjunction_Compose]，它自己的 block 携带 [u0 = u2]、[u0 = u4]、[u5 = u7]，仅负责两个定理2常数的额外 [u5 = u8] —— 它不是另外两个 [routeb_sigma] 和 [routeb_tau] 的来源，后者两者都携带，类型中没有任何附加。隔离探针在探针文件中，而不在这里。在每一种情况下，OBJECT 宇宙保持独立于 hom 宇宙以及彼此——文件中的任何方程都不涉及对象宇宙——且仅携带界限：[<=] 界限，除了在提到 [Adj_Bicategory] 或 [Adjoints] 的九个常量中，对象宇宙还严格位于 0-单元格宇宙之下（[Adj_bicat_is_Adj]，三个 [Adj_*_readback] 和两个 [Adj_hcomp2_*_is_Cat_hcomp2] 携带 [u6 < u]；[adjobj_of_morphism]、[morphism_of_adjobj] 和 [adjoints_round_record] 携带 [u4 < u]）。[Adj_Bicategory@{u u0 u1 u2 u3 u4 u5 u6 u7} : Bicategory@{u u0 u1 u0 u1}] 精确等于 [Cat_Bicategory] 的实例化形状（九个宇宙参数对比 Cat 的六个），其区块 [u1 < u0]、[u4 < u]、[u7 < u]，[u7 < u5] 以及无方程的界限，且 0-单元格类型 [Category] 与 Cat 的一样，位于更高一级。在此文件的任何绑定器或常量块中都不存在以词为界的 [Set]。

 ** 闭包

 上述 require 列表的传递性项目内闭包（不包括此文件）有 29 个模块。丢弃单一边缘项：Adjunction/Square 4（它会带来 Adjunction/Map、Construction/Quotient 和 Functor/Construction/Product）、Instance/Adj 1、Instance/Cat/Bicategory 1，以及其他所有 require 0。如果没有 Adjunction/Square 和 Instance/Cat/Bicategory，闭包将是 24：路由 (b) 花费 4，消耗 Cat 的互换花费 1，两者都是刻意支付的。

 ** 一个陈旧的问题句子其当前状态部分写道：“Instance/Adj.v —— 存在一个伴随同类，但其箭头上没有共轭条件”。这自 #395 以来就已经过时：[ConjPair] 的第三个字段包含 [conj_pair_law]，所以 [Adj C D] 的一个箭头是一个共轭对，而不是一对单纯的变换，而且该文件自己的头部记录了重新类型化。

 ** 已置顶Test/ProbeAdjBicat399.v 包含 27 条反驳命令：一个仪器检查加上 26 条三种类型的否定，这三种类型可通过错误文本区分。十一项是转换拒绝（[Compose] 的两种括号化和两种单位填充；四个 [adjobj_hcompose] 定律；路线-(b) tau 腿；[Adjoints] 对 [Adjunction_Compose] 的组合；sigT 往返；以及 [Build_Bicategory'] 的挫折），四项是类型拒绝（[Adjunction_Compose] 的结合律和两个单位律，这些根本无法表述，以及作为整体变换的 sigma 腿），十一项是形成性拒绝（[Adjunction] 和 [Compose] 各自作为 hom = 证明的提供者；继承此性质的 [AdjObj]、[Adj]、[ConjPair]、[nat_hcompose]、[Cat_Hcompose]、[adjobj_hcompose] 和 [Adj_Hcompose]；以及在形成任何伴随前，双向函子识别两个 hom 层级）。每个否定都是一次剥离，每次单独编译并读取其完整错误；每个常量的否定名称都由每个反驳命令外的 [Check] 保护（否定中有 118 个标识符，外部也有 93 个，25 个例外是两个关键字、七个绑定变量、十五个被反驳的声明名称以及该工具缺失的名称）；在此文件的否定命名的常量上模拟重命名 15/15，每次中断都落在 [Check] 行。那里记录了对期望的两个更正：[Build_Bicategory'] 拒绝包含“无法统一”条款，因此是 CONVERSION 而不是 TYPING，并且 [ConjPair] 否定在其 [AdjObj] 参数拒绝，所以 [ConjPair] 是否标识它自己的任何内容是未知的，而非被反驳。[make todo] 增长了 41，全部在探测器中；此文件贡献为零。

 ** 未交付对于上述三个测量的阻塞，没有 [TwoCategory] 实例；没有伴随的双重范畴，也没有任意双范畴中伴侣的拼接函子性——Theory/Bicategory/Mates.v 的 descoped 账目条目 10 由于本文件而被缩小，而非解除，并且在同一次提交中其注释被编辑为精确说明这一点。对于两个定理2的证明项，在任何强度下都没有比较（两者都是 [Qed]，因此没有任何可规约）。在 C、D 或 E 中没有任何识别的自然性，也没有 [Adj_Hcompose] 对其三个范畴参数的函子性。在一对命名的范畴上没有具体证明，因此这里没有实例化。没有严格的 2-范畴，也没有两个括号化之间的 Leibniz 方程。与 Instance/Cat/Bicategory/Conjugate.v 中的伴随识别没有关系，仅限于 (B) 中引用的填充形状。没有来自 [Adj_Bicategory] 的伪函子，也没有与 [Cat_Bicategory] 的比较，除了 (G) 中的两个 [eq_refl] 分支读取回。没有任何内容被注册为 [Instance]。
*)

(* * ** (A) Theorem 2: horizontal composites of conjugate pairs are conjugate / * **（A）定理 2：共轭对的水平复合是共轭的 *)

Section HorizontalCompose.

Context {C D E : Category}.
Context {F  : D ⟶ C} {U  : C ⟶ D}.
Context {F' : D ⟶ C} {U' : C ⟶ D}.
Context {G  : C ⟶ E} {V  : E ⟶ C}.
Context {G' : C ⟶ E} {V' : E ⟶ C}.
Context (A  : F ⊣ U)  (A' : F' ⊣ U').
Context (B  : G ⊣ V)  (B' : G' ⊣ V').

(*
 Mac Lane's diagram read left to right.  Nothing here appeals to the
 naturality of tau: [nat_hcompose]'s own factorisation of the Godement
 square is exactly the one the goal produces. 

 --------
 麦克莱恩的图从左到右读取。这里没有任何东西涉及 tau 的自然性：[nat_hcompose] 对 Godement 方格的自身分解正是目标生成的那个。
*)
Theorem conjugate_hcompose (s : F' ⟹ F) (t : U ⟹ U')
                           (sb : G' ⟹ G) (tb : V ⟹ V') :
  Conjugate A A' s t → Conjugate B B' sb tb →
  Conjugate (Adjunction_Compose A B) (Adjunction_Compose A' B')
            (nat_hcompose sb s) (nat_hcompose t tb).
Proof.
  intros H1 H2 x e k; simpl.
  rewrite comp_assoc.
  rewrite to_adj_nat_l.
  rewrite H1.
  rewrite H2.
  rewrite to_adj_nat_r.
  now rewrite comp_assoc.
Qed.

End HorizontalCompose.

(* * ** (B) The same theorem through Adjunction/Square.v's vertical paste / * **（B）通过 Adjunction/Square.v 的垂直粘贴得到的同一命题 *)

(*
 Padding into the shape [AdjointSquareT] wants at identity bounding
 functors.  These duplicate in shape Instance/Cat/Bicategory/Conjugate.v's
 [Cat_conj_padL] and [Cat_conj_padR]; see the header for why that file is
 not required. 

 --------
 在恒等范畴函子处，将形状 [AdjointSquareT] 填充为所需的形状。这些在形状 Instance/Cat/Bicategory/Conjugate.v 的 [Cat_conj_padL] 和 [Cat_conj_padR] 中有重复；参见文件头部了解为什么该文件不是必须的。
*)
Program Definition conj_padL {X Y : Category} {P P' : X ⟶ Y} (s : P' ⟹ P)
  : P' ◯ Id[X] ⟹ Id[Y] ◯ P := {| transform := fun x => s x |}.
Next Obligation. apply (naturality s). Qed.
Next Obligation. apply (naturality_sym s). Qed.

Program Definition conj_padR {X Y : Category} {P P' : X ⟶ Y} (t : P ⟹ P')
  : Id[Y] ◯ P ⟹ P' ◯ Id[X] := {| transform := fun a => t a |}.
Next Obligation. apply (naturality t). Qed.
Next Obligation. apply (naturality_sym t). Qed.

Section RouteB.

Context {C D E : Category}.
Context {F  : D ⟶ C} {U  : C ⟶ D}.
Context {F' : D ⟶ C} {U' : C ⟶ D}.
Context {G  : C ⟶ E} {V  : E ⟶ C}.
Context {G' : C ⟶ E} {V' : E ⟶ C}.
Context (A  : F ⊣ U)  (A' : F' ⊣ U').
Context (B  : G ⊣ V)  (B' : G' ⊣ V').

(* The hypothesis transfer is a Leibniz equality of TYPES. / 假设转移是类型的莱布尼茨等式。 *)
Example routeb_hyp (s : F' ⟹ F) (t : U ⟹ U') :
  AdjointSquareT A A' Id[C] Id[D] (conj_padL s) (conj_padR t)
    = Conjugate A A' s t := eq_refl.

(* The sigma leg of the paste IS the Godement product, componentwise. / 糊的西格玛支腿是 Godement 积，按分量计算。 *)
Example routeb_sigma (s : F' ⟹ F) (sb : G' ⟹ G) (x : D) :
  transform (paste_v_sigma (D:=D) (C:=C) (E:=E) (D':=D) (C':=C) (E':=E)
               (F:=F) (G:=G) (F':=F') (G':=G')
               Id[D] Id[C] Id[E] (conj_padL s) (conj_padL sb)) x
    = transform (nat_hcompose sb s) x := eq_refl.

(*
 The tau leg is not: [paste_v_tau] takes the other factorisation of the
 Godement square, and the two differ by one naturality of t. 

 --------
 tau 腿不是：[paste_v_tau] 取了 Godement 平方的另一个分解，这两个通过 t 的一个自然性而不同。
*)
Lemma routeb_tau (t : U ⟹ U') (tb : V ⟹ V') (e : E) :
  transform (paste_v_tau (D:=D) (C:=C) (E:=E) (D':=D) (C':=C) (E':=E)
               (U:=U) (V:=V) (U':=U') (V':=V')
               Id[D] Id[C] Id[E] (conj_padR t) (conj_padR tb)) e
    ≈ transform (nat_hcompose t tb) e.
Proof. simpl; apply naturality. Qed.

Theorem conjugate_hcompose_via_square
        (s : F' ⟹ F) (t : U ⟹ U') (sb : G' ⟹ G) (tb : V ⟹ V') :
  Conjugate A A' s t → Conjugate B B' sb tb →
  Conjugate (Adjunction_Compose A B) (Adjunction_Compose A' B')
            (nat_hcompose sb s) (nat_hcompose t tb).
Proof.
  intros H1 H2.
  pose proof (adjoint_square_paste_v A B A' B' Id[D] Id[C] Id[E]
                (conj_padL s) (conj_padR t) (conj_padL sb) (conj_padR tb)
                H1 H2) as Hp.
  intros x e k.
  etransitivity; [ exact (Hp x e k) | ].
  apply compose_respects; [ | reflexivity ].
  apply routeb_tau.
Qed.

End RouteB.

(* * ** (C) Horizontal composition as a bifunctor / * **（C）作为双函子的水平组合 *)

(* Cat's own middle-four interchange, consumed rather than restated: this is [Cat_Hcompose]'s [fmap_comp] applied, with no tactic. / 猫自己的中间四交换，消耗而不是重述：这是 [Cat_Hcompose] 的 [fmap_comp] 应用，没有策略。 *)
Definition nat_hcompose_interchange {C D E : Category}
  {P1 P2 P3 : C ⟶ D} {Q1 Q2 Q3 : D ⟶ E}
  (a1 : Q1 ⟹ Q2) (a2 : Q2 ⟹ Q3) (b1 : P1 ⟹ P2) (b2 : P2 ⟹ P3) :
  nat_hcompose (a2 ∙ a1) (b2 ∙ b1)
    ≈ nat_hcompose a2 b2 ∙ nat_hcompose a1 b1
  := @fmap_comp _ _ (@Cat_Hcompose C D E)
       (Q1, P1) (Q2, P2) (Q3, P3) (a2, b2) (a1, b1).

(* The identity 1-cell on a category: the identity adjunction. / 一个范畴上的恒等 1-元：恒等伴随。 *)
Definition AdjIdObj (X : Category) : AdjObj X X :=
  (Id[X]; (Id[X]; @Adjunction_Id X)).

(*
 Composition of 1-cells.  Left adjoints compose in the opposite order to
 right adjoints, which is Mac Lane's <F- F, G G->. 

 --------
 1-胞的组合。左伴随与右伴随的组合顺序相反，这就是 Mac Lane 的 <F- F, G G->。
*)
Definition adjobj_hcompose {x y z : Category}
  (p : AdjObj y z) (q : AdjObj x y) : AdjObj x z :=
  (adjobj_left q ◯ adjobj_left p;
   (adjobj_right p ◯ adjobj_right q;
    Adjunction_Compose (adjobj_adj p) (adjobj_adj q))).

(* Composition of 2-cells: the two Godement products, conjugate by Theorem 2. The single obligation is one [exact], no tactic work. / 2-胞的组合：两个 Godement 乘积，通过定理 2 共轭。唯一的义务是一个 [exact]，没有策略工作。 *)
Program Definition conj_pair_hcompose {x y z : Category}
  {p p' : AdjObj y z} {q q' : AdjObj x y}
  (th : @ConjPair y z p p') (et : @ConjPair x y q q') :
  @ConjPair x z (adjobj_hcompose p q) (adjobj_hcompose p' q') := {|
  conj_left  := nat_hcompose (conj_left et) (conj_left th);
  conj_right := nat_hcompose (conj_right th) (conj_right et)
|}.
Next Obligation.
  exact (conjugate_hcompose (adjobj_adj p') (adjobj_adj p)
           (adjobj_adj q') (adjobj_adj q)
           (conj_left th) (conj_right th) (conj_left et) (conj_right et)
           (conj_pair_law th) (conj_pair_law et)).
Qed.

#[local] Obligation Tactic := idtac.

(* Mac Lane's display (1). [fst] is the outer 1-cell, as in [Cat_Hcompose]; the order of the two factors is forced by the [Bicategory] class's [hcompose] field. / Mac Lane 的展示 (1)。[fst] 是外部 1-胞，如同 [Cat_Hcompose]；两个因子的顺序是由 [Bicategory] 类的 [hcompose] 字段所决定的。 *)
Program Definition Adj_Hcompose {x y z : Category} :
  (Adj y z ∏ Adj x y) ⟶ Adj x z := {|
  fobj := fun pq => adjobj_hcompose (fst pq) (snd pq);
  fmap := fun pq pq' m => conj_pair_hcompose (fst m) (snd m)
|}.
Next Obligation.
  intros x y z [p q] [p' q'] [th et] [th' et'] [[H1 H2] [H3 H4]];
  split; simpl; intro o.
  - now rewrite (H3 _), (H1 o).
  - now rewrite (H2 _), (H4 o).
Qed.
Next Obligation. intros x y z [p q]; split; simpl; intros; cat. Qed.
(* Each leg is Cat's own interchange, applied. / 每条腿都是猫自己使用的交换装置。 *)
Next Obligation.
  intros x y z [p q] [p' q'] [p'' q''] [th et] [th' et']; split.
  - exact (nat_hcompose_interchange (conj_left et') (conj_left et)
             (conj_left th') (conj_left th)).
  - exact (nat_hcompose_interchange (conj_right th) (conj_right th')
             (conj_right et) (conj_right et')).
Qed.

#[local] Obligation Tactic := program_simpl.

(* The bifunctor has exactly the shape of Mac Lane's display (1). / 该双函子正好具有 Mac Lane 展示 (1) 的形状。 *)
Example Adj_Hcompose_shape :
  ∀ x y z : Category, (Adj y z ∏ Adj x y) ⟶ Adj x z := @Adj_Hcompose.

(* The two reviewer checks, at Leibniz equality. / 两个审稿人检查时，处于莱布尼茨等式。 *)
Example hcomp_obj_adj {x y z : Category}
  (p : AdjObj y z) (q : AdjObj x y) :
  adjobj_adj (adjobj_hcompose p q)
    = Adjunction_Compose (adjobj_adj p) (adjobj_adj q) := eq_refl.

Example hcomp_obj_left {x y z : Category}
  (p : AdjObj y z) (q : AdjObj x y) :
  adjobj_left (adjobj_hcompose p q)
    = adjobj_left q ◯ adjobj_left p := eq_refl.

Example hcomp_obj_right {x y z : Category}
  (p : AdjObj y z) (q : AdjObj x y) :
  adjobj_right (adjobj_hcompose p q)
    = adjobj_right p ◯ adjobj_right q := eq_refl.

Example hcomp_left_is_nat_hcompose {x y z : Category}
  {p p' : AdjObj y z} {q q' : AdjObj x y}
  (th : @ConjPair y z p p') (et : @ConjPair x y q q') :
  conj_left (conj_pair_hcompose th et)
    = nat_hcompose (conj_left et) (conj_left th) := eq_refl.

Example hcomp_right_is_nat_hcompose {x y z : Category}
  {p p' : AdjObj y z} {q q' : AdjObj x y}
  (th : @ConjPair y z p p') (et : @ConjPair x y q q') :
  conj_right (conj_pair_hcompose th et)
    = nat_hcompose (conj_right th) (conj_right et) := eq_refl.

(* * ** (D) Exercise 1: the interchange law, derived from bifunctoriality / * **（D）练习 1：互换律，由双函子性推导 *)

(* One [exact] of the bifunctor's own [fmap_comp]. / 双函子的自身 [fmap_comp] 的一个 [exact]。 *)
Theorem conj_interchange {x y z : Category}
  {a b c : Adj y z ∏ Adj x y} (f : b ~> c) (g : a ~> b) :
  fmap[@Adj_Hcompose x y z] (f ∘ g)
    ≈ fmap[Adj_Hcompose] f ∘ fmap[Adj_Hcompose] g.
Proof. exact (@fmap_comp _ _ (@Adj_Hcompose x y z) a b c f g). Qed.

Corollary conj_interchange_left {x y z : Category}
  {a b c : Adj y z ∏ Adj x y} (f : b ~> c) (g : a ~> b) :
  conj_left (fmap[@Adj_Hcompose x y z] (f ∘ g))
    ≈ conj_left (fmap[Adj_Hcompose] f ∘ fmap[Adj_Hcompose] g).
Proof. exact (fst (conj_interchange f g)). Qed.

Corollary conj_interchange_right {x y z : Category}
  {a b c : Adj y z ∏ Adj x y} (f : b ~> c) (g : a ~> b) :
  conj_right (fmap[@Adj_Hcompose x y z] (f ∘ g))
    ≈ conj_right (fmap[Adj_Hcompose] f ∘ fmap[Adj_Hcompose] g).
Proof. exact (snd (conj_interchange f g)). Qed.

(* The two readable componentwise forms, read off the same law. / 两个可读的逐分量形式，读自同一规律。 *)
Corollary conj_interchange_sigma {x y z : Category}
  {p p' p'' : AdjObj y z} {q q' q'' : AdjObj x y}
  (th : p' ~{Adj y z}~> p'') (th' : p ~{Adj y z}~> p')
  (et : q' ~{Adj x y}~> q'') (et' : q ~{Adj x y}~> q') :
  nat_hcompose (conj_left et ∙ conj_left et')
               (conj_left th ∙ conj_left th')
    ≈ nat_hcompose (conj_left et) (conj_left th)
        ∙ nat_hcompose (conj_left et') (conj_left th').
Proof.
  exact (fst (@conj_interchange x y z (p, q) (p', q') (p'', q'')
                (th, et) (th', et'))).
Qed.

Corollary conj_interchange_tau {x y z : Category}
  {p p' p'' : AdjObj y z} {q q' q'' : AdjObj x y}
  (th : p' ~{Adj y z}~> p'') (th' : p ~{Adj y z}~> p')
  (et : q' ~{Adj x y}~> q'') (et' : q ~{Adj x y}~> q') :
  nat_hcompose (conj_right th' ∙ conj_right th)
               (conj_right et' ∙ conj_right et)
    ≈ nat_hcompose (conj_right th') (conj_right et')
        ∙ nat_hcompose (conj_right th) (conj_right et).
Proof.
  exact (snd (@conj_interchange x y z (p, q) (p', q') (p'', q'')
                (th, et) (th', et'))).
Qed.

(* * ** (E) The unitors and the associator / * **（E）幺元和结合子 *)

(* The dictionary is crossed: nat_λ on the left adjoints, nat_ρ on the right adjoints, because the two compose in opposite orders. / 词典是交叉的：左伴随上是 nat_λ，右伴随上是 nat_ρ，因为它们的组合顺序相反。 *)
Program Definition Adj_hunit_left {x y : Category} (f : AdjObj x y) :
  @Isomorphism (Adj x y) (adjobj_hcompose (AdjIdObj y) f) f := {|
  to   := {| conj_left  := to   (nat_λ (adjobj_left  f))
           ; conj_right := from (nat_ρ (adjobj_right f)) |};
  from := {| conj_left  := from (nat_λ (adjobj_left  f))
           ; conj_right := to   (nat_ρ (adjobj_right f)) |}
|}.
Next Obligation. intros a b k; simpl; cat. Qed.
Next Obligation. intros a b k; simpl; cat. Qed.
Next Obligation. split; simpl; intros; cat. Qed.
Next Obligation. split; simpl; intros; cat. Qed.

Program Definition Adj_hunit_right {x y : Category} (f : AdjObj x y) :
  @Isomorphism (Adj x y) (adjobj_hcompose f (AdjIdObj x)) f := {|
  to   := {| conj_left  := to   (nat_ρ (adjobj_left  f))
           ; conj_right := from (nat_λ (adjobj_right f)) |};
  from := {| conj_left  := from (nat_ρ (adjobj_left  f))
           ; conj_right := to   (nat_λ (adjobj_right f)) |}
|}.
Next Obligation. intros a b k; simpl; cat. Qed.
Next Obligation. intros a b k; simpl; cat. Qed.
Next Obligation. split; simpl; intros; cat. Qed.
Next Obligation. split; simpl; intros; cat. Qed.

(*
 Both legs are the [to] direction, and they take nat_α's three functor
 arguments in opposite orders. 

 --------
 两条腿都是 [to] 方向，并且它们以相反的顺序采用 nat_α 的三个函子参数。
*)
Program Definition Adj_hassoc {w x y z : Category}
  (h : AdjObj y z) (g : AdjObj x y) (f : AdjObj w x) :
  @Isomorphism (Adj w z)
    (adjobj_hcompose (adjobj_hcompose h g) f)
    (adjobj_hcompose h (adjobj_hcompose g f)) := {|
  to   := {| conj_left  := to (nat_α (adjobj_left  h) (adjobj_left  g)
                                     (adjobj_left  f))
           ; conj_right := to (nat_α (adjobj_right f) (adjobj_right g)
                                     (adjobj_right h)) |};
  from := {| conj_left  := from (nat_α (adjobj_left  h) (adjobj_left  g)
                                       (adjobj_left  f))
           ; conj_right := from (nat_α (adjobj_right f) (adjobj_right g)
                                       (adjobj_right h)) |}
|}.
Next Obligation. intros a b k; simpl; cat. Qed.
Next Obligation. intros a b k; simpl; cat. Qed.
Next Obligation. split; simpl; intros; cat. Qed.
Next Obligation. split; simpl; intros; cat. Qed.

(* Why the crossing: the padded 1-cell's two adjoints. / 为什么是交叉：填充的1单元的两个伴随。 *)
Example hunit_left_obj_left {x y : Category} (f : AdjObj x y) :
  adjobj_left (adjobj_hcompose (AdjIdObj y) f)
    = adjobj_left f ◯ Id[y] := eq_refl.

Example hunit_left_obj_right {x y : Category} (f : AdjObj x y) :
  adjobj_right (adjobj_hcompose (AdjIdObj y) f)
    = Id[y] ◯ adjobj_right f := eq_refl.

Example hunit_right_obj_left {x y : Category} (f : AdjObj x y) :
  adjobj_left (adjobj_hcompose f (AdjIdObj x))
    = Id[x] ◯ adjobj_left f := eq_refl.

Example hunit_right_obj_right {x y : Category} (f : AdjObj x y) :
  adjobj_right (adjobj_hcompose f (AdjIdObj x))
    = adjobj_right f ◯ Id[x] := eq_refl.

(** ** (F) The five coherence laws / **（F）五条连贯性定律 *)

(* The Godement product of two 2-cells: the bifunctor's action on a pair, which is exactly what the class's [hcomp2] computes to. / 两个 2-胞的 Godement 积：双函子的作用于一对，这正是类 [hcomp2] 所计算的内容。 *)
Definition adj_hcomp2 {x y z : Category}
  {p p' : AdjObj y z} {q q' : AdjObj x y}
  (th : p ~{Adj y z}~> p') (et : q ~{Adj x y}~> q')
  : adjobj_hcompose p q ~{Adj x z}~> adjobj_hcompose p' q'
  := @fmap _ _ (@Adj_Hcompose x y z) (p, q) (p', q') (th, et).

Example adj_hcomp2_is_conj_pair_hcompose {x y z : Category}
  {p p' : AdjObj y z} {q q' : AdjObj x y}
  (th : p ~{Adj y z}~> p') (et : q ~{Adj x y}~> q') :
  adj_hcomp2 th et = conj_pair_hcompose th et := eq_refl.

Theorem Adj_hunit_left_natural {x y : Category} {f f' : AdjObj x y}
  (et : f ~{Adj x y}~> f') :
  et ∘ to (Adj_hunit_left f)
    ≈ to (Adj_hunit_left f') ∘ adj_hcomp2 (@id (Adj y y) (AdjIdObj y)) et.
Proof. split; simpl; intros; cat. Qed.

Theorem Adj_hunit_right_natural {x y : Category} {f f' : AdjObj x y}
  (et : f ~{Adj x y}~> f') :
  et ∘ to (Adj_hunit_right f)
    ≈ to (Adj_hunit_right f') ∘ adj_hcomp2 et (@id (Adj x x) (AdjIdObj x)).
Proof. split; simpl; intros; cat. Qed.

Theorem Adj_hassoc_natural {w x y z : Category}
  {h h' : AdjObj y z} {g g' : AdjObj x y} {f f' : AdjObj w x}
  (th : h ~{Adj y z}~> h') (ga : g ~{Adj x y}~> g')
  (et : f ~{Adj w x}~> f') :
  adj_hcomp2 th (adj_hcomp2 ga et) ∘ to (Adj_hassoc h g f)
    ≈ to (Adj_hassoc h' g' f') ∘ adj_hcomp2 (adj_hcomp2 th ga) et.
Proof. split; simpl; intros; rewrite !fmap_id, fmap_comp; cat. Qed.

Theorem Adj_triangle {x y z : Category}
  (g : AdjObj y z) (f : AdjObj x y) :
  adj_hcomp2 (to (Adj_hunit_right g)) (@id (Adj x y) f)
    ≈ adj_hcomp2 (@id (Adj y z) g) (to (Adj_hunit_left f))
        ∘ to (Adj_hassoc g (AdjIdObj y) f).
Proof. split; simpl; intros; cat. Qed.

Theorem Adj_pentagon {v w x y z : Category}
  (k : AdjObj y z) (h : AdjObj x y) (g : AdjObj w x) (f : AdjObj v w) :
  adj_hcomp2 (@id (Adj y z) k) (to (Adj_hassoc h g f))
    ∘ to (Adj_hassoc k (adjobj_hcompose h g) f)
    ∘ adj_hcomp2 (to (Adj_hassoc k h g)) (@id (Adj v w) f)
  ≈ to (Adj_hassoc k h (adjobj_hcompose g f))
    ∘ to (Adj_hassoc (adjobj_hcompose k h) g f).
Proof. split; simpl; intros; cat. Qed.

(** ** (G) Adj as a bicategory / **（G）作为双范畴的Adj *)

(*
 The raw constructor, never [Build_Bicategory']: feeding [Adj]'s own ten
 projections keeps record eta, so [bicat C D] is definitionally
 [Adj C D] and [hcompose] typechecks against [Adj_Hcompose].  A plain
 [Definition], not an [Instance], following [Cat_Bicategory]. 

 --------
 原始构造函数，永远 [Build_Bicategory']：喂入 [Adj] 自己的十个投影会记录 eta，所以 [bicat C D] 从定义上是 [Adj C D]，并且 [hcompose] 类型检查通过 [Adj_Hcompose]。一个普通的 [Definition]，而不是 [Instance]，后面跟随 [Cat_Bicategory]。
*)
Definition Adj_Bicategory : Bicategory :=
  Build_Bicategory
    Category
    (fun C D => @obj (Adj C D))
    (fun C D => @hom (Adj C D))
    (@AdjIdObj)
    (fun C D => @homset (Adj C D))
    (fun C D => @id (Adj C D))
    (fun C D => @compose (Adj C D))
    (fun C D => @compose_respects (Adj C D))
    (fun C D => @id_left (Adj C D))
    (fun C D => @id_right (Adj C D))
    (fun C D => @comp_assoc (Adj C D))
    (fun C D => @comp_assoc_sym (Adj C D))
    (@Adj_Hcompose)
    (fun C D f => Adj_hunit_left f)
    (fun C D f => Adj_hunit_right f)
    (@Adj_hassoc)
    (@Adj_hunit_left_natural)
    (@Adj_hunit_right_natural)
    (@Adj_hassoc_natural)
    (@Adj_triangle)
    (@Adj_pentagon).

Example Adj_bicat_is_Adj (C D : Category) :
  @bicat Adj_Bicategory C D = Adj C D := eq_refl.

Example Adj_hcompose_readback (x y z : Category) :
  @hcompose Adj_Bicategory x y z = @Adj_Hcompose x y z := eq_refl.

Example Adj_bi1id_readback (C : Category) :
  @bi1id Adj_Bicategory C = AdjIdObj C := eq_refl.

Example Adj_hcomp2_readback {x y z : Category}
  {p p' : AdjObj y z} {q q' : AdjObj x y}
  (th : p ~{Adj y z}~> p') (et : q ~{Adj x y}~> q') :
  @hcomp2 Adj_Bicategory x y z p p' q q' th et
    = conj_pair_hcompose th et := eq_refl.

(*
 The bridge to Cat: each leg of a horizontal composite of 2-cells here
 IS Cat's own [hcomp2] on the underlying adjoints.  The left leg swaps
 its two arguments, which is the contravariance of [adjobj_left]. 

 --------
 到 Cat 的桥：这里的每一条水平复合 2-胞腔的腿都是 Cat 在底层伴随上的自身 [hcomp2]。左边的腿交换了它的两个参数，这就是 [adjobj_left] 的逆变性。
*)
Example Adj_hcomp2_left_is_Cat_hcomp2 {x y z : Category}
  {p p' : AdjObj y z} {q q' : AdjObj x y}
  (th : p ~{Adj y z}~> p') (et : q ~{Adj x y}~> q') :
  conj_left (@hcomp2 Adj_Bicategory x y z p p' q q' th et)
    = @hcomp2 Cat_Bicategory z y x
        (adjobj_left q) (adjobj_left q')
        (adjobj_left p) (adjobj_left p')
        (conj_left et) (conj_left th) := eq_refl.

Example Adj_hcomp2_right_is_Cat_hcomp2 {x y z : Category}
  {p p' : AdjObj y z} {q q' : AdjObj x y}
  (th : p ~{Adj y z}~> p') (et : q ~{Adj x y}~> q') :
  conj_right (@hcomp2 Adj_Bicategory x y z p p' q q' th et)
    = @hcomp2 Cat_Bicategory x y z
        (adjobj_right p') (adjobj_right p)
        (adjobj_right q') (adjobj_right q)
        (conj_right th) (conj_right et) := eq_refl.

(* * ** (H) The bridge to Instance/Adjoints.v / * ** (H) 桥接到 Instance/Adjoints.v *)

Definition adjobj_of_morphism {C D : Category}
  (m : C ~{Adjoints}~> D) : AdjObj C D :=
  (free_functor m; (forgetful_functor m; adjunction m)).

Definition morphism_of_adjobj {C D : Category}
  (x : AdjObj C D) : C ~{Adjoints}~> D := {|
  free_functor      := adjobj_left  x;
  forgetful_functor := adjobj_right x;
  adjunction        := adjobj_adj   x
|}.

(* [adj_morphism] has primitive projections with eta, so this round trip is Leibniz. The sigT one is not; see the header. / [adj_morphism] 有带 eta 的原始投影，所以这个往返是莱布尼茨的。sigT 的不是；见头部。 *)
Example adjoints_round_record {C D : Category} (m : C ~{Adjoints}~> D) :
  morphism_of_adjobj (adjobj_of_morphism m) = m := eq_refl.
