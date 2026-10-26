Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Proset.Limit.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Props.

(*
 The same two as Instance/Powerset.v and Instance/Proset.v:
 [relation] and [PreOrder] below are the stdlib Prop-valued ones, not
 the [crelation] ones [Category.Lib] exports, and they must come AFTER
 [Category.Lib].  The cost is that stdlib's [equiv] then shadows
 [Category.Lib.Setoid.equiv], so every explicit occurrence below is
 written [@Category.Lib.Setoid.equiv].  The [≈] NOTATION is unaffected:
 a notation resolves its head reference when it is declared, so [≈]
 stays bound to the library's [equiv]. 

 --------
 与 Instance/Powerset.v 和 Instance/Proset.v 中的相同两个：
 下面的 [relation] 和 [PreOrder] 是 stdlib 的 Prop 值版本，而不是 
 [crelation] 那些 [Category.Lib] 导出的版本，并且它们必须在 
 [Category.Lib] 之后。代价是 stdlib 的 [equiv] 会覆盖 
 [Category.Lib.Setoid.equiv]，因此下面每个显式出现的都写为 
 [@Category.Lib.Setoid.equiv]。[≈] 的 NOTATION 不受影响：
 一个 notation 在声明时解析它的头引用，所以 [≈] 
 保持绑定到库中的 [equiv]。
*)
Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(*
   * * The quantifiers as adjoints to substitution

   Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.5
   construction 4 (printed pp. 96-97).  Transcribed from the page
   images, in ASCII.  From p. 96, last paragraph:

   “Now consider the first projection P : U x V -> U from the product
   of two sets U and V.  Each subset S subset U x V defines two
   corresponding subsets of U by

   P_* S = {x | exists y, y in V   and       <x,y> in S},
   P_# S = {x | forall y, y in V   implies   <x,y> in S};

   they arise from <x,y> in S by applying the existential quantifier
   exists y,”

   and, continuing on p. 97:

   “'there exists a y' and the universal quantifier forall y, 'for all
   y', respectively to <x,y> in S.  Also P_* S is the direct image of
   S under the projection P.  Now for all subsets X subset U one has

   S <= P^* X <=> P_* S <= X ;    P^* X <= S <=> X <= P_# S,

   where '<=>' means 'if and only if'.  These state that P^*, which
   is the inverse image operation, has both a left adjoint P_* and a
   right adjoint P_#.  In this sense, both quantifiers exists and
   forall can be interpreted as adjoints.

   There is also a geometric interpretation: P^* X is the cylinder
   X x V subset U x V over the base X subset U, P_* S is the
   projection of S subset U x V on the base U, and P_# S is the
   largest subset X of U such that the cylinder on X is wholly
   contained in S.  This analysis has revealed several basic concepts
   of logic (and, or, not, forall y, exists y) to be adjoints.  This
   illustrates the slogan 'adjoints are everywhere'.”

   Awodey, *Category Theory* (1st ed. pre-print), §9.4 Example 9.12
   (printed p. 228) and the paragraph continuing it on p. 229:

   “Example 9.12.  A related example is the adjunction on powersets
   induced by any function f : A -> B, between the inverse image
   operation f^{-1} and the direct image im(f), ...  Here we have an
   adjunction im(f) -| f^{-1} as indicated by the bicondition:

   im(f)(U) subseteq V
   -------------------
   U subseteq f^{-1}(V)

   which is plainly valid for all subsets U subseteq A and
   V subseteq B.

   The inverse image operation f^{-1} : P(B) -> P(A) also has a
   right adjoint, given by:

   f_*(U) = {b in B | f^{-1}(b) subseteq U}

   as we also leave for the reader to verify.”

   and §9.6 (printed p. 236), the preservation corollaries and their
   contrapositives:

   “Similarly, for the quantifiers one has e.g.:

   forall x (phi(x) /\ psi(x)) -||- forall x phi(x) /\ forall x psi(x)

   Since this does not hold for exists x, it cannot be a right
   adjoint to some other 'quantifier'.  Similarly:

   exists x (phi(x) \/ psi(x)) -||- exists x phi(x) \/ exists x psi(x)

   And, as above, forall x cannot be a left adjoint, since it does
   not have this property.”

   Riehl, *Category Theory in Context* (2nd ed.), §4.1 Example 4.1.8
   (printed pp. 134-135):

   “Example 4.1.8.  Consider a function f : A -> B between sets.  The
   subsets of A and subsets of B form posets, PA and PB, ordered by
   inclusion.  The map f induces direct image and inverse image
   functors f_* : PA -> PB and f^{-1} : PB -> PA.  The inverse image
   is right adjoint to the direct image: for A' subset A and
   B' subset B, f(A') subset B' if and only if A' subset f^{-1}(B').

   The inverse image functor has a further right adjoint f_! that
   carries a subset A' subset A to the subset of elements of B whose
   fibers lie entirely in A'.  With this definition,
   B' subset f_!(A') if and only if f^{-1}(B') subset A'.  These
   functors define an adjoint triple: [f_* -| f^{-1} -| f_!].”

   Example 4.1.9 (printed p. 135):

   “Example 4.1.9.  A predicate or propositional function is a
   function p : X -> Omega, where Omega := {bot, top} is the set of
   truth values. ...  The set Omega^X is then the set of predicates
   on X.  The set Omega is given the partial order bot <= top defined
   by logical implication.  The set Omega^X inherits a
   pointwise-defined order: p <= q if and only if p(x) <= q(x) for
   all x in X, which is the case just when p(x) implies q(x) for
   every x.

   The logical operations of universal and existential quantification
   define functors forall_X, exists_X : Omega^X => Omega in the
   expected way: forall_X p = top if and only if p(x) = top for all
   x in X, and exists_X p = top if and only if there exists x in X
   with p(x) = top.  There is also a constant functor
   Delta_X : Omega -> Omega^X, and one can verify that these functors
   define an adjoint triple: [exists_X -| Delta_X -| forall_X].”

   Exercise 4.1.ii (printed p. 138):

   “Exercise 4.1.ii.  Explain why Example 4.1.9 can be regarded as a
   special case of Example 4.1.8.”

   and §4.5's generalization to an arbitrary function (printed
   pp. 156-157):

   “There is a relationship between the cartesian closed structure on
   the category of predicates on X and the adjoint triple of functors
   exists_X -| Delta_X -| forall_X introduced in Example 4.1.9, which
   we first generalize as follows.  For any function f : Y -> X,
   there is an adjoint triple of functors ... defined as follows.
   For a predicate p : X -> Omega on X, Delta_f p is the predicate on
   Y defined by composition: Delta_f p := p f, which is to say that
   Delta_f p(y) := p(f(x)).  For a predicate q : Y -> Omega on Y,
   exists_f q(x) = top if there exists y in the fiber over x so that
   q(y) = top, while forall_f q(x) = top if q(y) = top for all y in
   the fiber over x.”

   Fong and Spivak, *Seven Sketches in Compositionality*, §1.4.3
   Example 1.117 (printed pp. 32-33):

   “Example 1.117.  Let f : A -> B be a function between sets.  We can
   imagine A as a set of apples, B as a set of buckets, and f as
   putting each apple in a bucket.

   Then we have the monotone map f^* : P(Y) -> P(X) that category
   theorists call 'pullback along f.'  This map takes a subset
   B' subseteq B to its preimage f^{-1}(B') subseteq A: that is, it
   takes a collection B' of buckets, and tells you all the apples
   that they contain in total.  This operation is monotonic (more
   buckets means more apples) and it has both a left and a right
   adjoint.

   The left adjoint f_!(A) is given by the direct image: it maps a
   subset A' subseteq A to

   f_!(A') := {b in B | there exists a in A' such that f(a) = b}

   This map takes a set A' of apples, and tells you all the buckets
   that contain at least one of those apples.

   The right adjoint f_* maps a subset A' subseteq A to

   f_*(A') := {b in B | for all a such that f(a) = b, we have a in A'}

   This map takes a set A' of apples, and tells you all the buckets b
   that are all-A': all the apples in b are from the chosen subset
   A'.  Note that if a bucket doesn't contain any apples at all, then
   vacuously all its apples are from A', so empty buckets count as
   far as f_* is concerned.”

   (Their Example 1.117 says “Let f : A -> B” and then writes
   f^* : P(Y) -> P(X); the letters X, Y there are a slip for A, B.
   Quoted as printed.)

   ** THE FOUR BOOKS DISAGREE ABOUT [f_*] AND [f_!], TWO WAYS EACH

   Riehl's [f_*] is the DIRECT image, and Mac Lane writes [P_*] for it
   at the projection; Awodey's [f_*] and Fong-Spivak's [f_*] are the
   DUAL image, Awodey writing [im(f)] for the direct image.  The dual
   image is [f_*] for Awodey and Fong-Spivak, [f_!] for Riehl and [P_#]
   for Mac Lane at the projection; the direct image is [f_!] for
   Fong-Spivak, [f_*] for Riehl, [P_*] for Mac Lane and [im(f)] for
   Awodey.  So the starred name takes two values across the four books
   and the shrieked name two, Riehl and Fong-Spivak opposite on both;
   an earlier draft called the clash “three-way” and an audit corrected
   it.  Riehl's [f_!] for the dual image is
   the reverse of the commonest topos-theoretic convention, in which
   [f_!] is the existential.  This file therefore uses no starred or
   shrieked name at all: the three operations are [Powerset_Prop_image]
   (the donor's), [Powerset_Prop_preimage] (the donor's) and
   [Powerset_Prop_dual] (new here), with the functors [DirectImage],
   [InverseImage] and [DualImage].

   nLab: https://ncatlab.org/nlab/show/existential+quantifier
   nLab: https://ncatlab.org/nlab/show/universal+quantifier
   nLab: https://ncatlab.org/nlab/show/adjoint+triple
   nLab: https://ncatlab.org/nlab/show/Beck-Chevalley+condition
   nLab: https://ncatlab.org/nlab/show/hyperdoctrine
   Wikipedia: https://en.wikipedia.org/wiki/Galois_connection

   ** THE ISSUE'S “Current state” IS STALE, MEASURED AT THE BASE COMMIT

   The catalog entry says the power set of a set as a category “has no
   witness”.  It has one: #382's Instance/Powerset.v declares
   [subset_le], [subset_le_preorder] and
   [Subsets X := Proset (subset_le_preorder X)], and supplies the
   LEFT half of this issue outright -- [image_preimage_galois],
   [DirectImage], [InverseImage], [image_preimage_adjunction], the
   meets and joins [subset_inter] / [subset_union] with
   [Subsets_Cartesian] through [Subsets_Cocomplete], the three
   preservation theorems, the RAPL/LAPC routes and the witnesses.
   All of that is CONSUMED, none
   of it rebuilt: [exists_substitution_adjunction] is literally
   [image_preimage_adjunction] under the name this issue pins, so “the
   existential IS the direct image” holds at a general [f] BY DEFINITION
   rather than by a comparison.

   What was genuinely absent is the RIGHT half.  Three separate
   comments in Instance/Powerset.v say so in terms: each records that
   the dual image and [f^* -| forall_f] are #384's.

   The issue also says “in-tree the dual image has no counterpart of any
   kind”.  That is stale for finite CODES: Instance/FinSet/Subsets.v
   declares [finpow_dual] with [finpow_dual_mem] and six
   [eq_refl] evaluations (among them [dual_apple0] and
   [dual_apple01]), and three of its comments record that only the
   ADJUNCTION is missing and that it is this issue's.  That file is
   cited, not rebuilt, and the finite-code adjunction is NOT built here:
   the setoid-level one is the deliverable.

   Work item 4 -- the slice-level generalization -- is NOT built here.
   Construction/Slice/Pullback.v has [Bang_Functor] (Sigma_f) and
   [Star_Functor] for f^*, and #387 has since PROVED their adjunction
   there as [Base_Functor_Adjunction]; no Pi_f exists anywhere, so the
   triple is still incomplete on the slice side.

   ** WHAT IS DELIVERED, WITH GRADES

   (A0) Three reusable general constants, in the shape #381 uses for
   general lemmas placed in a consumer file, plus one engineering
   helper ([quant_refl]) recorded under the same heading.
   [proset_adjunction_at] builds an adjunction between preorders at
   two GIVEN functors out of the bare biconditional; it is what
   lets the headline be stated at #382's [InverseImage f] rather
   than at a second, parallel preimage functor (see the note
   below).  [gal_r_preserves_glb] and [gal_l_preserves_lub] are the
   order-level “right adjoints preserve meets, left adjoints
   preserve joins”.  None of the three exists in tree, measured two
   ways at the base commit: for the two preservation lemmas,
   Instance/Powerset.v is the ONLY file mentioning both [gal_] and
   [IsGLB]/[IsLUB] and it relates them nowhere; for
   [proset_adjunction_at], the eight [Instance/Proset] files build
   an adjunction between prosets only through
   Instance/Proset/Galois.v's [GaloisAdjunction], which makes its
   own two functors, and its one [Context (Adj : F ⊣ U)]
   -- the only [⊣] in all eight files -- runs the OTHER way,
   consuming an adjunction rather than producing one.  The two
   preservation lemmas are plain terms with no tactic;
   [proset_adjunction_at]'s six [Program] obligations -- two
   [Proper] certificates for the legs, the two isomorphism laws in
   [Sets] and the two naturality clauses -- are each equations
   between parallel arrows in a thin category ([Proset]'s hom-setoid
   is [fun _ _ => True], Instance/Proset.v), which is why the
   default tactic closes all six; an earlier draft said “two”.

   (A)  [Powerset_Prop_dual f S] with predicate
   [fun y => forall x, f x ≈ y -> S x] -- Awodey's
   [{b | f^{-1}(b) subseteq U}], Riehl's [f_!], Fong-Spivak's
   [f_*], Mac Lane's [P_#] at the projection.  NO truncation is
   needed, and that is a fact rather than a convenience: a [forall]
   landing in [Prop] is a [Prop] whatever it quantifies over,
   whereas [Powerset_Prop_image]'s existential has the
   [Type]-valued body [S x /\ f x ≈ y] -- [≈] is [Type]-valued
   here -- and must be squashed.  [dual_mem] reads membership back
   at [eq_refl].

   Then [dual_monotone], the two transposes
   [preimage_transpose_to]/[preimage_transpose_from],
   [preimage_dual_galois] as a [GaloisConnection] (the [_to] one is
   where the subset [T] of the codomain spends its own
   respectfulness: the hypothesis gives membership only at points
   of the inverse image, and [f x ≈ y] is what carries [T y]
   there), [DualImage] as #380's [GaloisFunctor_r] of it, and the
   two pinned names
   **[exists_substitution_adjunction f : DirectImage f ⊣
   InverseImage f]** (a [:=] of #382's) and
   **[substitution_forall_adjunction f : InverseImage f ⊣
   DualImage f]**, packaged as [quantifier_triple].
   [preimage_is_precompose] records at [eq_refl] that the inverse
   image IS Riehl's [Delta_f p := p f].

   WHY THE HEADLINE IS NOT [GaloisAdjunction].  #380's
   [GaloisAdjunction PA PB G] has type
   [GaloisFunctor_l PA PB G ⊣ GaloisFunctor_r PA PB G], and
   [GaloisFunctor_l _ _ preimage_dual_galois] is NOT
   [InverseImage f], which is [GaloisFunctor_r] of the OTHER
   connection.  The two have the same [fobj] and the same [fmap] on
   the nose -- which is why [proset_adjunction_at] applies at all,
   the hom types being convertible -- but [GaloisFunctor_l] and
   [GaloisFunctor_r] are separate [Program Definition]s whose three
   law fields are separate opaque obligations, so the functor
   RECORDS differ.  Stating the theorem with a second preimage
   functor would have made “f^* has both adjoints” false as
   written, the two f^*'s being different objects.  The rejection
   is pinned as the probe's conversion negative 1.

   THE UNIT AND COUNIT ARE THE TWO INCLUSIONS ON THE NOSE.
   [forall_unit_incl] and [forall_counit_incl] are Mac Lane's
   [X <= P_# P^* X] and [P^* P_# S <= S] written as terms, and
   [adj_unit_is_forall_incl] / [adj_counit_is_forall_incl] identify
   the adjunction's OWN [unit] and [counit] with them at Leibniz
   [=].  That is STRICTLY BETTER than #382's corresponding
   [adj_unit_has_incl_type], which is an ascription only; that
   file's note on that constant explains why -- its four donor lemmas
   are [Qed] -- and predicts the strict form would hold were they
   [Defined].  Here every step is a [:=] term, so it does.  In a
   thin category an [≈] between parallel arrows is [True]
   (Instance/Powerset.v), so the Leibniz statement is the only
   informative one available.

   (B)  MAC LANE'S OWN SITE.  [ProdSetoid U V] is [product_obj] over
   [Sets_Cartesian] (measured: for [U V : SetoidObject@{o o}] the
   product is again a [SetoidObject@{o o}], which is what lets
   [Subsets] be formed on it), [proj_fst] is [exl], and his three
   displayed operations are written LITERALLY: [proj_exists S] with
   predicate [fun x => exists y, S (x, y)], [proj_forall S] with
   [fun x => forall y, S (x, y)], and
   [cylinder X := Powerset_Prop_preimage proj_fst X] with
   [cylinder_mem : cylinder X (x, y) = X x] at [eq_refl], which is
   his [P^* X = X x V].  [proj_exists] uses stdlib's Prop-valued
   [ex], not the library's Type-valued [∃]: the body [S (x, y)] is
   already a [Prop], so again no truncation is required -- the same
   measurement (A) makes from the other side.

   His two displayed biconditionals are [proj_exists_transpose] and
   [proj_forall_transpose], proved directly as [iffT]s;
   [proj_forall_largest] is his “the largest subset X of U such
   that the cylinder on X is wholly contained in S”, and the file
   says plainly that it IS the second biconditional together with
   its unit rather than separate content.  [proj_galois_exists] and
   [proj_galois_forall] package the two as [GaloisConnection]s AT
   HIS FORMULAS.

   The identifications with (A) hold at [≈] and NOT at [eq_refl],
   and the cause is measured rather than guessed: [proj_exists] is
   an [ex] over [carrier V] while [Powerset_Prop_image proj_fst] is
   a [Powerset_squash] of a [sigT] over [carrier (ProdSetoid U V)],
   and [proj_forall] quantifies over [carrier V] where
   [Powerset_Prop_dual proj_fst] quantifies over
   [carrier (ProdSetoid U V)].  [proj_exists_is_image] and
   [proj_forall_is_dual] are the [≈] forms; both [eq_refl] forms
   are pinned as probe negatives.  [proj_maps_agree] records that
   the two Galois connections' three maps agree with (A)'s -- two
   at [≈], the cylinder at [eq_refl]; the RECORDS are not compared
   and no comparison of the two ADJUNCTIONS is claimed.

   (C)  BECK-CHEVALLEY for the reindexed projection, at LEIBNIZ [=] on
   the WHOLE SUBSET.  [cyl_reindex g] is [fun z => (g (fst z),
   snd z)], built by hand rather than through [split]/[bimap].
   [beck_chevalley_exists_mem] and [beck_chevalley_forall_mem] are
   the two membership [Prop]s, at [eq_refl] because the inverse
   image is precomposition; [beck_chevalley_exists] and
   [beck_chevalley_forall] are the whole subsets, also at
   [eq_refl]; and [beck_chevalley_exists_equiv]/[_forall_equiv] are
   the [≈] readings.  The whole-subset grade was NOT expected --
   the header first predicted the opposite -- and it deserves its
   reason: [SetoidMorphism] has primitive projections with eta, so
   record equality is field equality, and the [proper_morphism]
   certificate is NOT irrelevant (two arbitrary proofs of one such
   [Proper] statement do not convert, measured out of tree).  What
   happens is that the two certificates genuinely converge, because
   [cyl_reindex] reduces at a literal pair and its own certificate
   projects the pair of hypotheses, which is exactly what the other
   side feeds to [S]'s certificate.

   (D)  AWODEY §9.6.  [dual_image_preserves_meets] is direct;
   [dual_image_preserves_meets_via_galois] is [gal_r_preserves_glb]
   at [preimage_dual_galois] (no adapter: [gal_r] of that
   connection IS the dual image), and
   [dual_image_meet_routes_agree] is the #382-style pair showing
   the two inhabit one type.  #382's
   [inverse_image_preserves_joins] is re-derived as the
   COROLLARY [inverse_image_preserves_joins_via_galois] -- that
   file proved it directly and the comment beside it says why: it
   needed f^*'s right adjoint, which is this file's -- with
   [inverse_image_join_routes_agree] beside it.  #382's
   [direct_image_preserves_joins] is cited, not restated.

   THE CONTRAPOSITIVES ARE THEOREMS ABOUT ADJUNCTIONS, not prose.
   [exists_not_right_adjoint] and [forall_not_left_adjoint] refute
   the EXISTENCE of an adjoint on the wrong side at
   [powerset_const0], by feeding #380's [GaloisOfAdjunction] to the
   (A0) preservation lemmas and contradicting a concrete refutation:
   #382's [direct_image_not_meet_preserving] for the first,
   and the new [dual_image_not_join_preserving] for the second.
   [∃] is the library's Type-valued [sigT] and each sigma binds the
   functor once.

   (E)  RIEHL 4.1.9 AND EXERCISE 4.1.ii.  In this tree a predicate on X
   IS an element of [Powerset_Prop_obj X]: [predicates_are_subsets]
   and [pointwise_is_subset_le] record both readings at [eq_refl],
   so Riehl's [Omega^X] under the pointwise order is [Subsets X] on
   the nose and her Exercise 4.1.ii is DEFINITIONAL here.  No
   functor category [[X, Omega]] is formed and none could be: X is
   a setoid, not a category, and a discrete category on its carrier
   would discard [≈].  That is the honest reading, not a shortcut.

   The triple over the unique map [X -> 1] is
   [Delta_X := InverseImage (quant_bang X)], [exists_X], [forall_X]
   and the two adjunctions INSTANTIATED ([:=] with no tactic),
   which is exactly “4.1.9 is 4.1.8 at [X -> 1]”;
   [Delta_X_obj_mem] reads the constant predicate back at
   [eq_refl].  The truth-value object is [Subsets quant_one], and
   **[subsets_one_Props : Subsets quant_one ≅[Cat] Props]**
   identifies it with Instance/Props.v's [Props].  Read its
   strength: [≅[Cat]] in this library is EQUIVALENCE, [Cat]'s
   hom-setoid being [Functor_Setoid]; an isomorphism OF CATEGORIES
   is unavailable, the two object types being different, and none
   is claimed.

   (F)  SEVEN SKETCHES 1.117 AND AWODEY 9.12, in their own words.
   [apples_buckets_bicondition] is the biconditional
   [f^*(B') subseteq A' <-> B' subseteq f_*(A')] as an [iffT] over
   the two transposes, and [dual_vacuous] is “empty buckets count”:
   a bucket with no apples at all lies in the dual image of every
   subset.

   (G)  NON-VACUITY, over #382's own [powerset_fin2] / [powerset_const0]
   / [powerset_sng1] and Instance/Powerset.v's [powerset_sng0],
   reused rather than rebuilt.  Every negative reaches [False] by
   eliminating a [Powerset_squash] into it or by [discriminate] on
   the discrete carrier -- never by an induction over a quotienting
   relation, which could not yield a negative.
   [dual_const0_sng0_at_1] and [dual_const0_sng0_not_at_0] compute
   the dual image of {0}, and [exists_ne_forall_at_const0] proves
   the two adjoints DIFFER at one input, which is the whole point
   of the third leg.  Over the projection,
   [proj_diag_exists_everywhere] and [proj_diag_forall_nowhere]
   evaluate Mac Lane's two operations at the diagonal, and
   [proj_row_forall_at_0] / [proj_row_forall_not_at_1] at a row.

   ** A CORRECTION TO THE BRIEF, MEASURED

   The brief predicted the dual image of {0} along the constant map at 0
   to be EMPTY, “because each fibre is the whole two-point set”.  That
   is false, and the file proves the opposite: the fibre over 1 is
   EMPTY, so 1 lies in the dual image of EVERY subset, vacuously --
   which is exactly Fong-Spivak's “empty buckets count”.  Only the fibre
   over 0 is the whole set.  So the dual image of {0} is {1}, not the
   empty set, and [dual_const0_sng0_at_1] proves it.  The conclusion the
   prediction was meant to support -- that the dual image does not
   preserve joins -- stands, and is witnessed at the element 0 instead.

   ** WHAT IS NOT DELIVERED

   No dual-image adjunction for Instance/FinSet/Subsets.v's
   [finpow_dual] (finite codes); that file's evaluations are cited and
   its adjunction is left open.  No slice-level
   [Sigma_f -| f^* -| Pi_f] (#387).  No hyperdoctrine, no
   Beck-Chevalley for a general pullback square (only the projection's
   reindexing along [g x id]), and no Frobenius reciprocity.  No
   naturality of any identification in [f], in [g] or in the setoid.  No
   comparison of [proj_galois_exists] with [image_preimage_galois] at
   the RECORD level, and none of the two adjunctions at any level.  No
   idempotent monad or comonad from either adjunction.  No Boolean
   connectives (#383).  No antisymmetric quotient, so two [≈]-equal
   subsets remain distinct objects, exactly as Instance/Powerset.v
   discloses for its own category.  Nothing is registered as an
   [Instance].

   ** AN ENGINEERING FINDING

   [Coq.Classes.Equivalence] and [Coq.Relations.Relation_Definitions]
   have to be imported AFTER [Category.Lib], because [Proset] and
   [GaloisConnection] want the stdlib Prop-valued [PreOrder] and
   [relation] rather than the [crelation] ones the library exports --
   Instance/Powerset.v says so and this file copies it.  What that
   costs, and what the donor never had to pay because it writes no
   explicit [equiv], is that stdlib's [equiv] then SHADOWS
   [Category.Lib.Setoid.equiv].  Two consequences, both measured: an
   explicit [@equiv _ (is_setoid Y)] is rejected with “The term
   'is_setoid Y' has type 'Setoid Y' while it is expected to have type
   'relation ?A'”, so every explicit occurrence here is written
   [@Category.Lib.Setoid.equiv]; and a bare [reflexivity] in TERM
   position is rejected with “Cannot infer the implicit parameter
   Reflexive”, so the term-mode occurrences go through [quant_refl].
   The [≈] NOTATION is unaffected -- a notation resolves its head
   reference when it is declared -- and in TACTIC position the goal
   disambiguates, which is why the donors' bare [reflexivity] works
   there and is left alone.

   ** A DONOR RESTATED RATHER THAN REQUIRED, ON A MEASUREMENT

   [subset_le_antisym] -- mutual inclusion gives [≈] -- already exists,
   at Instance/Grp/Galois.v, with this file's exact statement and
   proof term.  It is NOT required: that module's transitive closure is
   129 modules against this file's 89, so importing it for a one-line
   definition would nearly double the cost.  The single place this file
   needs it, inside [exists_not_right_adjoint], writes the term
   [fun x => conj (H1 x) (H2 x)] inline instead, with no new name and
   hence no third homonym in the `make print-assumptions` scope.

   ** UNIVERSES

   Every constant touching a power set is at one level [o] with
   [Set < o], INHERITED from [Powerset_Prop_obj]'s codomain
   [Powerset_Prop_truth], whose carrier is [Prop : Type@{Set+1}].  The
   binder shape [X Y : SetoidObject@{o o}] is likewise the DONORS'
   identification and not one introduced here: [Powerset_Prop_obj@{o}]
   is the first to impose it, and [subset_le], [subset_le_preorder] and
   [Subsets] each impose it independently, so no one of them is “the”
   cause.  Section (B) additionally uses [product_obj] over
   [Sets_Cartesian], measured to land at [SetoidObject@{o o}] again.
   Measured over all 100 constants: NO block contains a universe
   EQUATION, and exactly 17 blocks are free of [Set] -- [quant_refl],
   the whole of (A0) ([proset_adjunction_at] with its six obligations,
   [gal_r_preserves_glb], [gal_l_preserves_lub]), and the seven
   constants that mention [Sets] but no power set ([ProdSetoid],
   [proj_fst], [proj_fst_computes], [cyl_reindex], [quant_one],
   [quant_bang], [quant_sq]).  The (A0) three are free because they
   mention no setoid at all, their blocks carrying only stdlib bounds.
   The RAPL/LAPC [Set] pin Instance/Powerset.v discloses is NOT
   inherited: nothing here routes through [Proset_Limit] or
   [DiscreteCat_Functor], and every [Set] token above is the LOWER
   bound [Set < o].

   ** CLOSURE

   89 transitive in-project dependencies, excluding this file, measured
   with coqdep given _CoqProject's list plus both new files.
   Instance/Powerset.v's own closure is 87 of the 89, so it dominates;
   per-Require MARGINAL costs, measured by dropping each in turn, are
   Instance/Powerset.v 2, Instance/Sets/Cartesian.v 1, and
   Instance/Cat.v, Instance/Props.v, Structure/Cartesian.v,
   Structure/Terminal.v, Instance/Proset/Limit.v and
   Theory/Isomorphism.v 0 each -- all six already lying inside the
   others' closures, which is why (E) can be packaged as [≅[Cat]] for
   nothing.

   ** TRANSPARENCY

   Eight proofs close with [Defined] (counted by token, inline ones
   included), and SIX are LOAD-BEARING, measured by flipping each one to
   [Qed] in a scratch copy and recompiling: [Powerset_Prop_dual],
   [proj_exists], [proj_forall], [cyl_reindex], [diag_subset] and
   [row0_subset] -- each one's predicate must reduce for the [eq_refl]
   readbacks, for the [destruct]s in the transposes, or for the witness
   computations.  The other two are NOT: [quant_refl] and the
   written-out obligation of [subsets_one_Props] (it raises two; the
   default tactic closes the other) each compile as [Qed], and they
   stay [Defined] because both produce DATA.  [quant_refl] is worth
   a word: the [eq_refl] identifications of the unit and the counit
   survive its being opaque, because [forall_counit_incl] and
   [preimage_transpose_from] both apply THE SAME term
   [quant_refl (f x)], so conversion never has to look inside it.  The
   21 remaining proofs are [Qed] and every other constant is a [:=]
   term.

   ** REGISTRATION

   Nothing here is an [Instance]: a chosen adjoint must not become
   globally resolvable, which is Instance/Powerset.v's and
   Instance/Proset/Limit.v's own convention. 

   --------
   * * 量词作为替换的伴随函子

   Mac Lane, 《为工作数学家准备的范畴论》，第2版，第IV.5节
   构造4（印刷页码96-97）。从页面图像转录，ASCII格式。从第96页最后一段：

   “现在考虑从两个集合 U 和 V 的乘积到 U 的第一投影 P : U x V -> U。每个子集 S ⊆ U x V 都定义了 U 的两个对应子集：

   P_* S = {x | 存在 y，y ∈ V 且 <x,y> ∈ S}，
   P_# S = {x | 对所有 y，y ∈ V 蕴含 <x,y> ∈ S}；

   它们是通过对 <x,y> ∈ S 应用存在量词 exists y 得到的，”

   并继续在第97页：'存在一个 y' 和全称量词 forall y，即 '对所有 y'，分别对应于 S 中的 <x,y>。此外，P_* S 是 S 在投影 P 下的直接像。现在对于所有子集 X ⊆ U，有

   S <= P^* X <=> P_* S <= X ;    P^* X <= S <=> X <= P_# S，

   其中 '<=>' 意味着 '当且仅当'。这些表明 P^*，即逆像操作，既有左伴随 P_*，也有右伴随 P_#。从这个意义上说，存在量词（exists）和全称量词（forall）都可以解释为伴随。还有一种几何解释：P^* X 是柱体 X x V，属于 U x V，在基底 X 属于 U 上；P_* S 是 S 属于 U x V 在基底 U 上的投影；而 P_# S 是 U 的最大子集 X，使得 X 上的柱体完全包含在 S 中。这个分析揭示了逻辑的一些基本概念（与、或、非、对于所有 y、存在 y）是伴随函数。这说明了口号“伴随无处不在”。

   —— Awodey，《范畴论》（第1版预印本），§9.4 示例 9.12（印刷版第228页）及其在第229页的延续段落：例 9.12. 一个相关的例子是由任意函数 f : A -> B 引起的幂集上的伴随关系，即逆象操作 f^{-1} 与直象操作 im(f) 之间的关系……这里我们有一个伴随关系 im(f) -| f^{-1}，由双条件如下所示：

   im(f)(U) ⊆ V
   -------------------
   U ⊆ f^{-1}(V)

   这对于所有子集 U ⊆ A 和 V ⊆ B 显然都是成立的。

   逆象操作 f^{-1} : P(B) -> P(A) 也有一个右伴随，其定义为：

   f_*(U) = {b ∈ B | f^{-1}(b) ⊆ U}

   这一点也留给读者去验证。

   以及 §9.6（印刷第 236 页），保持性推论及其对偶命题：

   同样，对于量词例如有：∀x (phi(x) ∧ psi(x)) -||- ∀x phi(x) ∧ ∀x psi(x)

   由于这对于 ∃x 不成立，它不能是某个其他“量词”的右伴随。同样地：

   ∃x (phi(x) ∨ psi(x)) -||- ∃x phi(x) ∨ ∃x psi(x)

   如上所述，∀x 也不能是左伴随，因为它不具备这个性质。

   Riehl，《语境中的范畴论》（第2版），§4.1 示例4.1.8（印刷版第134-135页）：示例 4.1.8. 考虑集合之间的函数 f : A -> B。A 的子集和 B 的子集形成偏序集 PA 和 PB，按包含关系排序。函数 f 导出直接像和逆像函子 f_* : PA -> PB 和 f^{-1} : PB -> PA。逆像是直接像的右伴随：对于 A' 子集 A 和 B' 子集 B，有 f(A') 子集 B' 当且仅当 A' 子集 f^{-1}(B')。

   逆像函子还有一个进一步的右伴随 f_!，它将子集 A' 子集 A 映射为 B 中那些其纤维完全位于 A' 中的元素的子集。根据此定义，B' 子集 f_!(A') 当且仅当 f^{-1}(B') 子集 A'。这些函子定义了一个伴随三元组：[f_* -| f^{-1} -| f_!]。

   示例 4.1.9（印刷页 135）:示例 4.1.9. 谓词或命题函数是一个函数 p : X -> Ω，其中 Ω := {⊥, ⊤} 是真值集合。……集合 Ω^X 则是 X 上的谓词集合。集合 Ω 被赋予由逻辑蕴涵定义的偏序 ⊥ <= ⊤。集合 Ω^X 继承了逐点定义的序：当且仅当对所有 x 属于 X，p(x) <= q(x) 时，p <= q，这正好对应于对每个 x，p(x) 蕴涵 q(x) 的情况。全称量化和存在量化的逻辑运算以预期方式定义函子 forall_X, exists_X : Omega^X => Omega：当且仅当对于所有 x ∈ X, p(x) = top 时，forall_X p = top；当且仅当存在 x ∈ X 使得 p(x) = top 时，exists_X p = top。还有一个常数函子 Delta_X : Omega -> Omega^X，可以验证这些函子定义了一个伴随三重性：[exists_X -| Delta_X -| forall_X]。

   练习 4.1.ii（印刷版第 138 页）：

   “练习 4.1.ii. 解释为什么例 4.1.9 可以被视为例 4.1.8 的一个特例。”

   以及 §4.5 对任意函数的推广（印刷版第 156-157 页）：在 X 上谓词范畴的笛卡儿闭结构与示例 4.1.9 中引入的函子伴随三重（exists_X ⊣ Delta_X ⊣ forall_X）之间存在关系，我们首先将其推广如下。对于任意函数 f : Y -> X，有一个函子伴随三重... 定义如下。对于 X 上的谓词 p : X -> Omega，Delta_f p 是 Y 上的谓词，通过复合定义：Delta_f p := p f，也就是说 Delta_f p(y) := p(f(y))。对于 Y 上的谓词 q : Y -> Omega，如果存在 x 上纤维中的 y 使得 q(y) = top，则 exists_f q(x) = top；而如果对 x 上纤维中的所有 y 都有 q(y) = top，则 forall_f q(x) = top。Fong 和 Spivak，《组合性七个草图》，§1.4.3
   示例 1.117（印刷页 32-33）：

   “示例 1.117。设 f: A -> B 为集合之间的一个函数。我们可以
   想象 A 是一组苹果，B 是一组桶，而 f 是将每个苹果放入一个桶中。

   那么我们有一个单调映射 f^* : P(Y) -> P(X)，范畴论者称其为“沿 f 的拉回”。
   这个映射将 B 的子集 B' subseteq B 映射到其原像 f^{-1}(B') subseteq A：也就是它
   将一组桶 B' 的集合映射为告诉你这些桶总共包含的所有苹果。
   这个操作是单调的（桶越多意味着苹果越多），并且它有左伴随和右伴随。

   左伴随 f_!(A) 由直接像给出：它将 A 的子集 A' subseteq A 映射为f_!(A') := {b 属于 B | 存在 a 属于 A' 使得 f(a) = b}

   这个映射取一个苹果集合 A'，并告诉你所有至少包含其中一个苹果的桶。

   右伴随 f_* 将 A 的一个子集 A' 映射到

   f_*(A') := {b 属于 B | 对所有满足 f(a) = b 的 a，都有 a 属于 A'}

   这个映射取一个苹果集合 A'，并告诉你所有“完全在 A' 中”的桶 b：b 中的所有苹果都来自选定的子集 A'。注意，如果某个桶根本不包含任何苹果，那么空桶在 f_* 的考虑下也算作它的所有苹果都来自 A'。 

   （他们的例子 1.117 说“设 f : A -> B”，然后写 f^* : P(Y) -> P(X)；这里的字母 X, Y 是写错了，原文应为 A, B。如原文所示。）** 四书在 [f_*] 和 [f_!] 上有分歧，每个都有两种方式Riehl 的 [f_*] 是直接像，而 Mac Lane 在投射下写作 [P_*]；Awodey 的 [f_*] 和 Fong-Spivak 的 [f_*] 是对偶像，Awodey 为直接像写作 [im(f)]。对偶像在 Awodey 和 Fong-Spivak 中是 [f_*]，在 Riehl 中是 [f_!]，在 Mac Lane 的投射下是 [P_#]；直接像在 Fong-Spivak 中是 [f_!]，在 Riehl 中是 [f_*]，在 Mac Lane 中是 [P_*]，在 Awodey 中是 [im(f)]。因此，带星号的名字在四本书中有两个取值，带感叹号的名字也有两个，Riehl 和 Fong-Spivak 在两者上都相反；早期草稿称这种冲突为“三路”，审计进行了更正。Riehl 对对偶像的 [f_!] 是与最常见的拓扑理论惯例相反的，在该惯例中，[f_!] 是存在式。因此，该文件根本没有使用任何加星号或惊叹号的名称：三个操作分别是 [Powerset_Prop_image]（捐赠者的）、[Powerset_Prop_preimage]（捐赠者的）和 [Powerset_Prop_dual]（新加入的），对应的函子是 [DirectImage]、[InverseImage] 和 [DualImage]。

   nLab: https://ncatlab.org/nlab/show/existential+quantifier
   nLab: https://ncatlab.org/nlab/show/universal+quantifier
   nLab: https://ncatlab.org/nlab/show/adjoint+triple
   nLab: https://ncatlab.org/nlab/show/Beck-Chevalley+condition
   nLab: https://ncatlab.org/nlab/show/hyperdoctrine
   Wikipedia: https://en.wikipedia.org/wiki/Galois_connection

   ** 该问题的“当前状态”已经过时，测量于基础提交目录条目称集合的幂集作为一个范畴“没有见证”。它是有的：#382 的 Instance/Powerset.v 声明了 [subset_le]、[subset_le_preorder] 和 [Subsets X := Proset (subset_le_preorder X)]，并直接提供了该问题的左半部分——[image_preimage_galois]、[DirectImage]、[InverseImage]、[image_preimage_adjunction]，以及通过 [Subsets_Cartesian] 到 [Subsets_Cocomplete] 的交与并 [subset_inter] / [subset_union]，三条保持定理，RAPL/LAPC 路径和见证。所有这些都被消耗掉，没有重建：[exists_substitution_adjunction] 实际上是根据该问题所指定的名称的 [image_preimage_adjunction]，因此“存在性等于直接像”在一般情况下 [f] 是由定义成立的，而不是通过比较成立的。真正缺失的是右半部分。Instance/Powerset.v 中有三条独立的评论以这种方式说明：每条评论都记录了对偶图像和 [f^* -| forall_f] 属于 #384。

   问题中还提到“在树中，对偶图像没有任何对应物”。对于有限码来说，这是过时的：Instance/FinSet/Subsets.v 声明了 [finpow_dual] 和 [finpow_dual_mem]，以及六个 [eq_refl] 的评估（其中包括 [dual_apple0] 和 [dual_apple01]），其三条评论记录仅缺少伴随，这是该问题的内容。该文件被引用，而非重建，并且有限码的伴随未在此处构建：可交付的是集合同类层面的伴随。工作项 4 —— 切片级推广 —— 此处未构建。
   Construction/Slice/Pullback.v 中有 [Bang_Functor]（Sigma_f）和 [Star_Functor] 对于 f^*，而 #387 自那时起已在那里证明了它们的伴随关系，作为 [Base_Functor_Adjunction]；没有任何地方存在 Pi_f，因此在切片方面三重结构仍然不完整。

   ** 已交付内容及评分(A0) 三个可重用的一般常量，形状类似 #381 用于放置在消费者文件中的一般引理，再加一个在同一标题下记录的工程辅助（[quant_refl]）。[proset_adjunction_at] 在两个给定函子上从裸双条件构建了一个伴随；它使得标题可以在 #382 的 [InverseImage f] 中陈述，而不是在第二个平行的原像函子上（见下面的注释）。[gal_r_preserves_glb] 和 [gal_l_preserves_lub] 是阶层级别的“右伴随保持交，左伴随保持并”。这三者在树中都不存在，在基提交处用两种方式测量：对于两个保持引理，Instance/Powerset.v 是唯一提到 [gal_] 和 [IsGLB] / [IsLUB] 的文件，并且它们之间没有任何关系；对于 [proset_adjunction_at]，八个 [Instance/Proset] 文件仅通过 Instance/Proset/Galois.v 的 [GaloisAdjunction] 构建了 prosets 之间的一个伴随，其中 [GaloisAdjunction] 自己创建了两个函子，而它的唯一 [Context (Adj : F ⊣ U)] —— 所有八个文件中唯一的 [⊣] —— 则是相反的方向，消耗一个伴随而不是生成一个伴随。这两个保持引理是没有策略的普通项；[proset_adjunction_at] 的六个 [Program] 义务——两条 [Proper] 证明腿的证书，[Sets] 中的两个同构律以及两个自然性条款——每一个都是薄范畴中平行箭头之间的等式（[Proset] 的 Hom-setoid 是 [fun _ _ => True]，Instance/Proset.v），这就是默认策略能够解决六条义务的原因；早期的草稿写的是“两个”。(A)  带谓词的 [Powerset_Prop_dual f S]
   [fun y => forall x, f x ≈ y -> S x] -- Awodey 的
   [{b | f^{-1}(b) subseteq U}]，Riehl 的 [f_!]，Fong-Spivak 的
   [f_*]，Mac Lane 的 [P_#] 在投影上。无需截断，这是事实而不是方便：[forall] 着陆在 [Prop] 是一个 [Prop]，无论它量化的是什麼，而 [Powerset_Prop_image] 的存在量词有 [Type] 值的主体 [S x /\ f x ≈ y] -- [≈] 在这里是 [Type] 值 -- 必须被压缩。[dual_mem] 在 [eq_refl] 处读取成员资格。然后 [dual_monotone]，两个换位 [preimage_transpose_to] / [preimage_transpose_from]，[preimage_dual_galois] 作为 [GaloisConnection]（[_to] 的那个是子集 [T] 在陪域中保持自身尊重的位置：假设只在逆像的点上给出成员资格，而 [f x ≈ y] 是将 [T y] 带到那里的东西），[DualImage] 作为 #380 的 [GaloisFunctor_r]，以及两个固定名称 **[exists_substitution_adjunction f : DirectImage f ⊣ InverseImage f]**（#382 的 [:=]）和 **[substitution_forall_adjunction f : InverseImage f ⊣ DualImage f]**，打包为 [quantifier_triple]。[preimage_is_precompose] 在 [eq_refl] 记录到逆像是 Riehl 的 [Delta_f p := p f]。为什么标题不是 [GaloisAdjunction]。#380 的 [GaloisAdjunction PA PB G] 有类型 [GaloisFunctor_l PA PB G ⊣ GaloisFunctor_r PA PB G]，而且 [GaloisFunctor_l _ _ preimage_dual_galois] 不是 [InverseImage f]，而 [InverseImage f] 是另一个连接的 [GaloisFunctor_r]。这两个有相同的 [fobj] 并且在鼻子上有相同的 [fmap]——这就是为什么 [proset_adjunction_at] 可以适用，hom 类型是可互换的——但是 [GaloisFunctor_l] 和 [GaloisFunctor_r] 是独立的 [Program Definition]，它们的三个法则字段是独立的不透明义务，因此函子 RECORDS 不同。用第二个前像函子陈述定理会使“f^* 有两个伴随”在书写上为假，因为这两个 f^* 是不同的对象。拒绝被固定为探针的转换负 1。单位和余单位是在鼻子上的两个包含。[forall_unit_incl] 和 [forall_counit_incl] 是 Mac Lane 的 [X <= P_# P^* X] 和 [P^* P_# S <= S] 写成的项，而 [adj_unit_is_forall_incl] / [adj_counit_is_forall_incl] 在 Leibniz [=] 中将伴随的自身 [unit] 和 [counit] 与它们对应起来。那比 #382 的相应 [adj_unit_has_incl_type] 严格得多，后者只是一个归属；该文件关于该常量的注释解释了原因——它的四个供体引理是 [Qed]——并预测严格形式如果它们是 [Defined] 就会成立。在这里每一步都是一个 [:=] 项，因此它成立。在稀薄范畴中，平行箭头之间的 [≈] 是 [True]（Instance/Powerset.v），所以 Leibniz 的陈述是唯一可用的有信息的陈述。(B)  MAC LANE 自己的网站。[ProdSetoid U V] 是 [product_obj] 在 [Sets_Cartesian] 上（测量：对于 [U V : SetoidObject@{o o}]，产物再次是 [SetoidObject@{o o}]，这正是使 [Subsets] 能够在其上形成的原因），[proj_fst] 是 [exl]，他展示的三个操作字面上写作：[proj_exists S] 其谓词为 [fun x => exists y, S (x, y)]，[proj_forall S] 其 [fun x => forall y, S (x, y)]，以及 [cylinder X := Powerset_Prop_preimage proj_fst X] 其 [cylinder_mem : cylinder X (x, y) = X x] 在 [eq_refl]，这就是他的 [P^* X = X x V]。[proj_exists] 使用 stdlib 的 Prop 值 [ex]，而不是库的 Type 值 [∃]：主体 [S (x, y)] 已经是 [Prop]，所以同样不需要截断 —— 相同的测量 (A) 从另一侧进行。他展示的两个双条件是 [proj_exists_transpose] 和 [proj_forall_transpose]，可以直接作为 [iffT] 证明；[proj_forall_largest] 是他所说的“U 的最大子集 X，使 X 上的圆柱完全包含在 S 中”，文件明确说明它实际上是第二个双条件及其单位，而不是单独内容。[proj_galois_exists] 和 [proj_galois_forall] 将这两个打包为他公式中的 [GaloisConnection]。(A) 的识别在 [≈] 成立，而在 [eq_refl] 不成立，且原因是被测量的而非猜测的：[proj_exists] 是 [carrier V] 上的 [ex]，而 [Powerset_Prop_image proj_fst] 是 [carrier (ProdSetoid U V)] 上 [sigT] 的 [Powerset_squash]，且 [proj_forall] 对 [carrier V] 进行量化，其中 [Powerset_Prop_dual proj_fst] 对 [carrier (ProdSetoid U V)] 进行量化。[proj_exists_is_image] 和 [proj_forall_is_dual] 是 [≈] 形式；两个 [eq_refl] 形式都被固定为探针阴性。[proj_maps_agree] 记录了两个伽罗华联系的三个映射与 (A) 的一致——两个在 [≈]，圆柱在 [eq_refl]；RECORDS 未进行比较，也未声称对两个 ADJUNCTIONS 进行比较。(C) 对于重新索引的投影，BECK-CHEVALLEY 在 LEIBNIZ [=] 上针对整个子集。[cyl_reindex g] 是 [fun z => (g (fst z), snd z)]，由手工构建，而不是通过 [split] / [bimap]。[beck_chevalley_exists_mem] 和 [beck_chevalley_forall_mem] 是两个成员 [Prop]，在 [eq_refl] 因为逆像是前置组合；[beck_chevalley_exists] 和 [beck_chevalley_forall] 是整个子集，也在 [eq_refl]；而 [beck_chevalley_exists_equiv] / [_forall_equiv] 是 [≈] 读数。整个子集等级是意料之外的——标题最初预测了相反的情况——它是有原因的：[SetoidMorphism] 具有带 eta 的原始投影，因此记录的相等性就是字段的相等性，而 [proper_morphism] 证书并非无关（对某个 [Proper] 语句的两个任意证明无法转换，测量时不考虑树结构）。发生的情况是这两个证书确实会收敛，因为 [cyl_reindex] 在一个字面对上归约，并且它自己的证书投影了假设对，这正是另一方提供给 [S] 证书的内容。(D)  AWODEY §9.6.   [dual_image_preserves_meets] 是直接的；
   [dual_image_preserves_meets_via_galois] 是 [gal_r_preserves_glb]
   在 [preimage_dual_galois] （没有适配器：[gal_r] 的那个
   连接就是双重像），并且
   [dual_image_meet_routes_agree] 是 #382 风格对，显示
   两者属于同一类型。#382 的
   [inverse_image_preserves_joins] 被重新推导为
   推论 [inverse_image_preserves_joins_via_galois] ——该
   文件直接证明了它，旁边的注释说明了原因：它
   需要 f^* 的右伴随，即本文件的这个——旁边是
   [inverse_image_join_routes_agree]。#382 的
   [direct_image_preserves_joins] 被引用，并未重述。逆命题是关于伴随的定理，而不是散文。[exists_not_right_adjoint] 和 [forall_not_left_adjoint] 否定了在错误一侧存在伴随，在 [powerset_const0] 通过将 #380 的 [GaloisOfAdjunction] 输入到 (A0) 保留引理，并与具体反例矛盾：第一个为 #382 的 [direct_image_not_meet_preserving]，第二个为新的 [dual_image_not_join_preserving]。[∃] 是库中的类型值 [sigT]，每个 sigma 都绑定一次函子。(E) RIEHL 4.1.9 以及练习 4.1.ii。在这棵树中，X 上的谓词是 [Powerset_Prop_obj X]: [predicates_are_subsets] 的一个元素，并且 [pointwise_is_subset_le] 在 [eq_refl] 记录了两种读法，所以在点态顺序下，Riehl 的 [Omega^X] 恰好是 [Subsets X]，她的练习 4.1.ii 在这里是定义性的。没有形成任何函子范畴 [[X, Omega] ]，也无法形成：X 是一个集值，同态集，而其载体上的离散范畴会丢弃 [≈]。那才是正确的读法，而不是捷径。在唯一映射 [X -> 1] 上的三重是 [Delta_X := InverseImage (quant_bang X)]、[exists_X]、[forall_X]，以及两个具化的附加（[:=] 没有使用策略），这正是“4.1.9 在 [X -> 1] 上是 4.1.8”；[Delta_X_obj_mem] 在 [eq_refl] 处读取常量谓词。真值对象是 [Subsets quant_one]，**[subsets_one_Props : Subsets quant_one ≅[Cat] Props]** 将其与 Instance/Props.v 的 [Props] 对应。在此库中读取其强度：[≅[Cat] 为 EQUIVALENCE，[Cat] 的同态集为 [Functor_Setoid]；类别同构不可用，因为两个对象类型不同，也没有声明任何同构。(F) 七个草图 1.117 和 Awodey 9.12，用他们自己的话说。  
   [apples_buckets_bicondition] 是双条件  
   [f^*(B') subseteq A' <-> B' subseteq f_*(A')] 作为 [iffT] 对两个转置的运算，且 [dual_vacuous] 是“空桶计数”：  
   一个完全没有苹果的桶存在于每个子集的对偶像中。(G) 非空性，在 #382 自身的 [powerset_fin2] / [powerset_const0] / [powerset_sng1] 和 Instance/Powerset.v 的 [powerset_sng0] 上重用而非重建。每个负值通过将一个 [Powerset_squash] 消除到 [False] 中或者在离散载体上 [discriminate] 来达到 [False] —— 绝不会通过对商关系的归纳，因为那不能产生负值。[dual_const0_sng0_at_1] 和 [dual_const0_sng0_not_at_0] 计算 {0} 的对偶像，而 [exists_ne_forall_at_const0] 证明两个伴随函数在一个输入上存在差异，这正是第三条腿的关键。在投影上，[proj_diag_exists_everywhere] 和 [proj_diag_forall_nowhere] 在对角线上计算 Mac Lane 的两个操作，而 [proj_row_forall_at_0] / [proj_row_forall_not_at_1] 在一行上计算。

   ** 对概述的修正，经过衡量简报预测沿着 0 的恒定映射 {0} 的对偶像是 EMPTY，“因为每个纤维都是整个两点集”。这是错误的，文件证明了相反的情况：1 上的纤维是 EMPTY，所以 1 虚拟地属于每个子集的对偶像——这正是 Fong-Spivak 所说的“空桶也算数”。只有 0 上的纤维是整个集合。因此，{0} 的对偶像是 {1}，而不是空集，[dual_const0_sng0_at_1] 证明了这一点。简报试图支持的结论——对偶像不保持并集——仍然成立，并在元素 0 上得到了体现。  

   ** 未交付的内容对于 Instance/FinSet/Subsets.v 的双像附属关系没有 [finpow_dual]（有限码）；该文件的评估被引用，其附属关系尚未确定。没有切片级别 [Sigma_f -| f^* -| Pi_f]（#387）。没有超命题学，也没有一般拉回方形的 Beck-Chevalley（仅投影沿 [g x id] 的重索引），也没有 Frobenius 对偶律。[f]、[g] 或集合定的任何识别没有自然性。没有在 RECORD 级别比较 [proj_galois_exists] 与 [image_preimage_galois]，也没有任何级别的两个附属关系。没有来自任一附属关系的幂等单子或余单子。没有布尔连词（#383）。没有反对称商，因此两个 [≈] 相等的子集仍然是不同的对象，正如 Instance/Powerset.v 所显示的其自身类别一样。没有任何东西被注册为 [Instance]。

   ** 一项工程发现[Coq.Classes.Equivalence] 和 [Coq.Relations.Relation_Definitions] 必须在 [Category.Lib] 之后导入，因为 [Proset] 和 [GaloisConnection] 想要 stdlib 中 Prop 值的 [PreOrder] 和 [relation]，而不是库导出的 [crelation] —— Instance/Powerset.v 说明了这一点，并且这个文件复制了它。其代价，以及捐赠者从未需要支付的代价，因为它不写显式的 [equiv]，就是 stdlib 的 [equiv] 然后会覆盖 [Category.Lib.Setoid.equiv]。两个后果，两者都经过测量：一个显式的 [@equiv _ (is_setoid Y)] 被拒绝，提示 “The term 'is_setoid Y' has type 'Setoid Y' while it is expected to have type 'relation ?A'”，因此这里每个显式出现都写作 [@Category.Lib.Setoid.equiv]；而 TERM 位置的一个单独 [reflexivity] 被拒绝，提示 “Cannot infer the implicit parameter Reflexive”，所以在术语模式下的出现通过 [quant_refl]。[≈] 符号不受影响——符号在声明时会解析其头部引用——而在战术位置，目标会进行消歧，这就是为什么捐赠者的单独 [reflexivity] 在那里可行且保持不变。  

   ** 一个捐赠者被重述而非在测量中必须[subset_le_antisym]  -- 相互包含会导致 [≈]  -- 已存在，
   在 Instance/Grp/Galois.v 中，具有与此文件完全相同的声明和证明项。 不需要：该模块的传递闭包包含 129 个模块，而此文件包含 89 个模块，因此为了一个单行定义而导入它几乎会使成本加倍。 此文件唯一需要它的地方，在 [exists_not_right_adjoint] 内，直接写入项 [fun x => conj (H1 x) (H2 x)] 作为内联，而没有新名称，因此在 `make print-assumptions` 范围内没有第三个同名。

   ** UNIVERSES每个接触幂集的常量都位于与 [Set < o] 相同的一个层级 [o]，从 [Powerset_Prop_obj] 的陪域 [Powerset_Prop_truth] 继承，其载体是 [Prop : Type@{Set+1}]。绑定器形状 [X Y : SetoidObject@{o o}] 同样是捐赠者的标识，而不是这里引入的：[Powerset_Prop_obj@{o}] 是第一个施加它的，而 [subset_le]、[subset_le_preorder] 和 [Subsets] 都各自独立施加它，所以没有一个是“原因”。(B) 节还在 [Sets_Cartesian] 上使用 [product_obj]，测量后再次落在 [SetoidObject@{o o}]。在所有100个常数中测量：没有块包含宇宙方程（EQUATION），且正好有17个块没有[Set]--[quant_refl]，整个(A0)([proset_adjunction_at]及其六个义务，[gal_r_preserves_glb]，[gal_l_preserves_lub])，以及七个提到[Sets]但没有幂集的常数（[ProdSetoid]，[proj_fst]，[proj_fst_computes]，[cyl_reindex]，[quant_one]，[quant_bang]，[quant_sq]）。(A0)中的三个是自由的，因为它们根本没有提到集合论，其块只包含stdlib边界。RAPL/LAPC [Set] pin Instance/Powerset.v披露的内容不是继承的：这里没有通过[Proset_Limit]或[DiscreteCat_Functor]的路由，并且上述每个[Set]标记都是下界[Set < o]。

   ** 闭包89 个传递的项目内依赖（不包括此文件），使用 coqdep 测量，给定 _CoqProject 的列表加上两个新文件。Instance/Powerset.v 自身的闭包是 89 个中的 87 个，因此它占主导地位；按 Require 的边际成本测量，通过依次删除每个文件，结果为：Instance/Powerset.v 2，Instance/Sets/Cartesian.v 1，以及 Instance/Cat.v、Instance/Props.v、Structure/Cartesian.v、Structure/Terminal.v、Instance/Proset/Limit.v 和 Theory/Isomorphism.v 各为 0 ——所有六个文件已经在其他文件的闭包内，这就是为什么 (E) 可以作为 [≅[Cat] ] 免费打包的原因。

   ** 透明度八个证明以 [Defined] 结束（按标记计数，包括内联的），其中六个是承重的，通过在草稿副本中将每一个翻转为 [Qed] 并重新编译来测量：[Powerset_Prop_dual]、[proj_exists]、[proj_forall]、[cyl_reindex]、[diag_subset] 和 [row0_subset] ——每一个的谓词必须为 [eq_refl] 的回读、变换中的 [destruct]，或见证计算简化。其他两个则不是：[quant_refl] 和 [subsets_one_Props] 的书面义务（它产生两个；默认策略闭合另一个）都编译为 [Qed]，并且它们保持 [Defined]，因为两者都会产生数据。[quant_refl] 值得一提的是：该单元和余单元的 [eq_refl] 识别在它变得不透明时仍然存在，因为 [forall_counit_incl] 和 [preimage_transpose_from] 都应用了相同的项 [quant_refl (f x)]，因此转换从不需要查看其内部。剩下的 21 个证明是 [Qed]，其他每个常数都是 [:=] 项。

   ** 注册

   这里没有任何 [Instance]：所选择的伴随不能变得全局可解，这是 Instance/Powerset.v 和 Instance/Proset/Limit.v 自身的惯例。
*)

(* ------------------------------------------------------------------------ *)
(* * ** (A0) General constants, and one engineering helper / * ** (A0) 一般常数，以及一个工程辅助工具 *)

(*
 Reflexivity of a setoid's own [≈], as a TERM.  It has to be written
 out: [Coq.Classes.Equivalence] is imported above, so a bare
 [reflexivity] in TERM position cannot choose between stdlib's
 Prop-valued [Reflexive] and the [crelation] one this library uses.  In
 TACTIC position the goal disambiguates and the donors' bare
 [reflexivity] works, which is why only the term-mode occurrences below
 go through this. 

 --------
 集的自反性 [≈] ，作为一个项。它必须被写出来：[Coq.Classes.Equivalence] 在上面已被导入，所以在项位置的单独 [reflexivity] 不能在标准库的 Prop 值 [Reflexive] 和本库使用的 [crelation] 之间进行选择。在战术位置，目标会消除歧义，捐赠者的单独 [reflexivity] 可以工作，这就是为什么下面只有项模式的出现可以通过的原因。
*)
Definition quant_refl@{o} {A : SetoidObject@{o o}} (a : carrier A) :
  @Category.Lib.Setoid.equiv _ (is_setoid A) a a.
Proof. reflexivity. Defined.

(*
 An adjunction between preorders AT TWO GIVEN FUNCTORS.  #380's
 [GaloisAdjunction] produces its two functors itself, so it cannot
 state an adjunction whose left functor was built earlier and
 elsewhere -- which is exactly the situation of the headline below,
 where the left functor is #382's [InverseImage].  All six obligations
 -- two [Proper] certificates, two isomorphism laws in [Sets], two
 naturality clauses -- are equations between parallel arrows in a thin
 category, so [Program]'s default tactic closes them. 

 --------
 在两个给定函子之间的预序的伴随。#380 的 [GaloisAdjunction] 自己生成它的两个函子，因此它无法声明一个左函子是之前在别处构建的伴随——这正是下面标题所描述的情况，其中左函子是 #382 的 [InverseImage]。所有六个义务——两个 [Proper] 证书、两个 [Sets] 中的同构定律、两个自然性条款——都是薄范畴中平行箭头之间的方程，因此 [Program] 的默认策略可以解决它们。
*)
Program Definition proset_adjunction_at {A B : Type}
  {RA : relation A} {RB : relation B}
  (PA : PreOrder RA) (PB : PreOrder RB)
  (F : Proset PA ⟶ Proset PB) (U : Proset PB ⟶ Proset PA)
  (tr : ∀ a b, RB (fobj[F] a) b → RA a (fobj[U] b))
  (tl : ∀ a b, RA a (fobj[U] b) → RB (fobj[F] a) b)
  : F ⊣ U :=
  Build_Adjunction' (F:=F) (U:=U)
    (fun a b => {| to   := {| morphism := tr a b |}
                 ; from := {| morphism := tl a b |} |}) _ _.

(* Right adjoints preserve meets, at the level of the order: Seven Sketches Proposition 1.111, Riehl §4.6.3's right-adjoint half. / 右伴随保持交，按序的层面：Seven Sketches 命题 1.111，Riehl §4.6.3 的右伴随部分。 *)
Definition gal_r_preserves_glb {A B : Type}
  {RA : relation A} {RB : relation B} (G : GaloisConnection RA RB)
  {Ix : Type} (d : Ix → B) (m : B) (H : IsGLB RB d m) :
  IsGLB RA (fun i => gal_r G (d i)) (gal_r G m) :=
  (fun i => gal_mono_r G (fst H i),
   fun n Hn => gal_to G n m
                 (snd H (gal_l G n)
                    (fun i => gal_from G n (d i) (Hn i)))).

(*
 Left adjoints preserve joins.  [IsLUB R] IS [IsGLB (op_rel R)], so the
 statement is the dual read at the reversed preorder; the term is
 nevertheless written out, its two clauses using [gal_to] and
 [gal_from] in the mirror order. 

 --------
 左伴随保持并。   [IsLUB R] 等于 [IsGLB (op_rel R)]，所以该命题是在反转的预序下的对偶读；尽管如此，该术语仍然被写出，其两个条款使用 [gal_to] 和 [gal_from]，顺序相反。
*)
Definition gal_l_preserves_lub {A B : Type}
  {RA : relation A} {RB : relation B} (G : GaloisConnection RA RB)
  {Ix : Type} (d : Ix → A) (m : A) (H : IsLUB RA d m) :
  IsLUB RB (fun i => gal_l G (d i)) (gal_l G m) :=
  (fun i => gal_mono_l G (fst H i),
   fun n Hn => gal_from G m n
                 (snd H (gal_r G n)
                    (fun i => gal_to G (d i) n (Hn i)))).

(* ------------------------------------------------------------------------ *)
(* * ** (A) The dual image, and the right adjunction / * **（A）双重像和右伴随 *)

(*
 Awodey's [f_*(U) = {b | f^{-1}(b) subseteq U}], Riehl's [f_!],
 Fong-Spivak's [f_*], Mac Lane's [P_#].  NO truncation: a [forall]
 landing in [Prop] is a [Prop] whatever it quantifies over.
 Respectfulness in [y] transports [f x ≈ y'] back to [f x ≈ y] through
 symmetry and transitivity. 

 --------
 Awodey 的 [f_*(U) = {b | f^{-1}(b) subseteq U}]，Riehl 的 [f_!]，Fong-Spivak 的 [f_*]，Mac Lane 的 [P_#]。没有截断：一个 [forall] 落在 [Prop] 上是一个 [Prop]，无论它量化的是哪个。[y] 中的尊重通过对称性和传递性将 [f x ≈ y'] 传回到 [f x ≈ y]。
*)
Definition Powerset_Prop_dual@{o} {X Y : SetoidObject@{o o}}
  (f : SetoidMorphism@{o o o} X Y)
  (S : carrier (Powerset_Prop_obj@{o} X)) :
  carrier (Powerset_Prop_obj@{o} Y).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier Y) (is_setoid Y) Prop (is_setoid Powerset_Prop_truth@{o})
       (λ y, ∀ x : carrier X,
               @Category.Lib.Setoid.equiv _ (is_setoid Y) (f x) y → S x) _).
  intros y y' Hyy'; split; intros H x Hfx; apply H.
  - now transitivity y'.
  - transitivity y; [ exact Hfx | now symmetry ].
Defined.

Section Dual.

Universe o so u.
Constraint o < so.

Context {X Y : SetoidObject@{o o}}.
Context (f : X ~{Sets@{o so}}~> Y).

(* Membership, on the nose. An equality of [Prop]s, not of morphisms. / 会员，正中要害。[Prop] 的平等，而不是态射的平等。 *)
Example dual_mem (S : carrier (Powerset_Prop_obj@{o} X)) (y : carrier Y) :
  Powerset_Prop_dual@{o} f S y
    = (∀ x : carrier X,
         @Category.Lib.Setoid.equiv _ (is_setoid Y) (f x) y → S x)
  := eq_refl.

(* Riehl §4.5's [Delta_f p := p f] IS the inverse image, on the nose: again an equality of [Prop]s. / Riehl §4.5 的 [Delta_f p := p f] 正是逆像：再次是 [Prop] 的等式。 *)
Example preimage_is_precompose (T : carrier (Powerset_Prop_obj@{o} Y))
  (x : carrier X) :
  Powerset_Prop_preimage@{o} f T x = T (f x) := eq_refl.

(* The dual image is order-preserving. / 双重映像是保持顺序的。 *)
Definition dual_monotone (S T : carrier (Powerset_Prop_obj@{o} X))
  (H : subset_le S T) :
  subset_le (Powerset_Prop_dual@{o} f S) (Powerset_Prop_dual@{o} f T) :=
  fun y Hy x Hfx => H x (Hy x Hfx).

(*
 Mac Lane's second displayed line at a general [f], left to right: from
 [f^* T <= S] infer [T <= forall_f S].  This is where [T]'s own
 respectfulness is spent -- the hypothesis gives [S x] only at points
 of the inverse image, and [f x ≈ y] is what carries [T y] there. 

 --------
 Mac Lane 在一般 [f] 上显示的第二行，从左到右：从 [f^* T <= S] 推断 [T <= forall_f S]。这就是 [T] 自身的尊重所耗尽的地方——假设只在逆像的点上给出 [S x]，而 [f x ≈ y] 才是将 [T y] 带到那里的东西。
*)
Definition preimage_transpose_to (T : carrier (Powerset_Prop_obj@{o} Y))
  (S : carrier (Powerset_Prop_obj@{o} X))
  (H : subset_le (Powerset_Prop_preimage@{o} f T) S) :
  subset_le T (Powerset_Prop_dual@{o} f S) :=
  fun y Hy x Hfx =>
    H x (proj2 (@proper_morphism _ _ _ _ T (f x) y Hfx) Hy).

(*
 ... and right to left.  Evaluating the dual image at [f x] against the
 reflexivity witness is the whole argument. 

 --------
 ... 从右到左。将双重图像在 [f x] 上与自反性证人进行评估就是整个论证。
*)
Definition preimage_transpose_from (T : carrier (Powerset_Prop_obj@{o} Y))
  (S : carrier (Powerset_Prop_obj@{o} X))
  (H : subset_le T (Powerset_Prop_dual@{o} f S)) :
  subset_le (Powerset_Prop_preimage@{o} f T) S :=
  fun x Hx => H (f x) Hx x (quant_refl (f x)).

(* THE GALOIS CONNECTION, all six fields by name. / 伽罗瓦连接，六个领域的名称。 *)
Definition preimage_dual_galois :
  GaloisConnection (@subset_le@{o} Y) (@subset_le@{o} X) :=
  {| gal_l := Powerset_Prop_preimage@{o} f
   ; gal_r := Powerset_Prop_dual@{o} f
   ; gal_mono_l := preimage_monotone f
   ; gal_mono_r := dual_monotone
   ; gal_to   := preimage_transpose_to
   ; gal_from := preimage_transpose_from |}.

(* The dual-image functor: #380's [GaloisFunctor_r] applied. / 双像函子：#380 的 [GaloisFunctor_r] 已应用。 *)
Definition DualImage : Subsets@{o u} X ⟶ Subsets@{o u} Y :=
  GaloisFunctor_r (subset_le_preorder@{o} Y) (subset_le_preorder@{o} X)
    preimage_dual_galois.

(** *** The two pinned adjunctions / *** 两个固定的连接 *)

(* #382's, under this issue's name. A [:=] with no tactic, so “the existential IS the direct image” is definitional at a general [f]. / #382的，以本期名称。一个没有策略的[:=]，所以“存在就是直接图像”在一般[f]中是定义性的。 *)
Definition exists_substitution_adjunction : DirectImage f ⊣ InverseImage f :=
  image_preimage_adjunction f.

(*
 THE HEADLINE.  Stated at #382's [InverseImage f], not at a second
 preimage functor: see the header. 

 --------
 标题。在 #382 的 [InverseImage f] 上声明，而不是在第二个前像函子上：见标题。
*)
Definition substitution_forall_adjunction : InverseImage f ⊣ DualImage :=
  proset_adjunction_at (subset_le_preorder@{o} Y) (subset_le_preorder@{o} X)
    (InverseImage f) DualImage preimage_transpose_to preimage_transpose_from.

(*
 Mac Lane's “P^*, which is the inverse image operation, has both a left
 adjoint P_* and a right adjoint P_#”, packaged.  [*] is [prod]: both
 components are data. 

 --------
 Mac Lane 的 “P^*”, 即逆像操作，具有一个左伴随 P_* 和一个右伴随 P_#，已打包。[*] 是 [prod]：两个组件都是数据。
*)
Definition quantifier_triple :
  (DirectImage f ⊣ InverseImage f) * (InverseImage f ⊣ DualImage) :=
  (exists_substitution_adjunction, substitution_forall_adjunction).

(** *** Readbacks / *** 回读 *)

Example dual_image_obj (S : carrier (Powerset_Prop_obj@{o} X)) :
  fobj[DualImage] S = Powerset_Prop_dual@{o} f S := eq_refl.

Example exists_adj_is_image_preimage :
  exists_substitution_adjunction = image_preimage_adjunction f := eq_refl.

(*
 #380's backward passage returns the connection this section supplied,
 at Leibniz [=] on the WHOLE record: [GaloisOfAdjunction] reads its six
 fields off the two functors and the hom-set isomorphism, and all of
 those were built from those very fields. 

 --------
 #380的反向通路返回了本节提供的连接，
 在莱布尼茨 [=] 上的整个记录：[GaloisOfAdjunction] 从两个函子和同态集同构中读取它的六个字段，所有这些都是由那些字段构建的。
*)
Example dual_galois_round_trip :
  GaloisOfAdjunction (subset_le_preorder@{o} Y) (subset_le_preorder@{o} X)
    (InverseImage f) DualImage substitution_forall_adjunction
  = preimage_dual_galois := eq_refl.

(* * *** The unit and the counit ARE the two inclusions / * *** 单位和余单位是两个包含 *)

(* Mac Lane's [X <= P_# P^* X], written directly. / Mac Lane 的 [X <= P_# P^* X]，直接写成。 *)
Definition forall_unit_incl (T : carrier (Powerset_Prop_obj@{o} Y)) :
  subset_le T
    (Powerset_Prop_dual@{o} f (Powerset_Prop_preimage@{o} f T)) :=
  fun y Hy x Hfx => proj2 (@proper_morphism _ _ _ _ T (f x) y Hfx) Hy.

(* Mac Lane's [P^* P_# S <= S]. / 麦克莱恩的 [P^* P_# S <= S]。 *)
Definition forall_counit_incl (S : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le
    (Powerset_Prop_preimage@{o} f (Powerset_Prop_dual@{o} f S)) S :=
  fun x Hx => Hx x (quant_refl (f x)).

(*
 And the adjunction's OWN unit and counit ARE those two, at Leibniz
 [=].  This is the strict form Instance/Powerset.v predicts for
 its own adjunction and declines to ship; here every step is a term, so
 it holds. 

 --------
 且伴随的自身单位和余单位就是那两个，在 Leibniz [=]。 这是严格形式 Instance/Powerset.v 对其自身伴随所预测的，并且拒绝发布；这里每一步都是一个项，所以它成立。
*)
Example adj_unit_is_forall_incl (T : carrier (Powerset_Prop_obj@{o} Y)) :
  @unit _ _ (InverseImage f) DualImage substitution_forall_adjunction T
    = forall_unit_incl T := eq_refl.

Example adj_counit_is_forall_incl (S : carrier (Powerset_Prop_obj@{o} X)) :
  @counit _ _ (InverseImage f) DualImage substitution_forall_adjunction S
    = forall_counit_incl S := eq_refl.

(* * *** (F) Seven Sketches 1.117 and Awodey 9.12, in their own words / * ***（F）七个素描 1.117 和 Awodey 9.12，用他们自己的话 *)

(*
 “B' subset f_!(A') if and only if f^{-1}(B') subset A'” -- Riehl's own
 phrasing of Example 4.1.8's second half, which is also Awodey's
 “as we also leave for the reader to verify”.  [iffT] is the library's
 Type-valued biconditional. 

 --------
 “B'子集f_！（A'）当且仅当f^{-1}（B'）子集A'”——Riehl自有子集
 示例4.1.8后半部分的措辞，也就是Awodey的
 “我们也留给读者来验证。”[iffT]是图书馆的
 类型价值双条件。
*)
Definition apples_buckets_bicondition
  (T : carrier (Powerset_Prop_obj@{o} Y))
  (S : carrier (Powerset_Prop_obj@{o} X)) :
  iffT (subset_le (Powerset_Prop_preimage@{o} f T) S)
       (subset_le T (Powerset_Prop_dual@{o} f S)) :=
  (preimage_transpose_to T S, preimage_transpose_from T S).

(* “if a bucket doesn't contain any apples at all, then vacuously all its apples are from A', so empty buckets count”. / “如果一个桶里完全没有苹果，那么根据虚假命题原则，它的所有苹果都是来自 A'，所以空桶也算数。” *)
Definition dual_vacuous (S : carrier (Powerset_Prop_obj@{o} X))
  (y : carrier Y)
  (Hy : ∀ x : carrier X,
          @Category.Lib.Setoid.equiv _ (is_setoid Y) (f x) y → False) :
  Powerset_Prop_dual@{o} f S y :=
  fun x Hfx => match Hy x Hfx with end.

(* * *** (D) Awodey §9.6: what each adjoint preserves / * *** (D) Awodey §9.6：每个伴随保持什么 *)

(* The dual image preserves meets, directly: the second clause is the transpose of the family's own second clause. / 双重图像保留会面，直接：第二个从句是家庭自身第二个从句的转置。 *)
Theorem dual_image_preserves_meets {Idx : Type}
  (S : Idx → carrier (Powerset_Prop_obj@{o} X))
  (m : carrier (Powerset_Prop_obj@{o} X))
  (H : IsGLB (@subset_le@{o} X) S m) :
  IsGLB (@subset_le@{o} Y)
    (fun i => Powerset_Prop_dual@{o} f (S i))
    (Powerset_Prop_dual@{o} f m).
Proof.
  split.
  - intro i; exact (dual_monotone m (S i) (fst H i)).
  - intros n Hn.
    refine (preimage_transpose_to n m _).
    refine (snd H (Powerset_Prop_preimage@{o} f n) _).
    intro i; exact (preimage_transpose_from n (S i) (Hn i)).
Qed.

(*
 The same statement read off (A0).  [gal_r preimage_dual_galois] IS the
 dual image, so the general lemma applies with no adapter. 

 --------
 相同的语句从 (A0) 读出。[gal_r preimage_dual_galois] 是对偶像，因此一般引理适用，无需适配器。
*)
Definition dual_image_preserves_meets_via_galois {Idx : Type}
  (S : Idx → carrier (Powerset_Prop_obj@{o} X))
  (m : carrier (Powerset_Prop_obj@{o} X))
  (H : IsGLB (@subset_le@{o} X) S m) :
  IsGLB (@subset_le@{o} Y)
    (fun i => Powerset_Prop_dual@{o} f (S i))
    (Powerset_Prop_dual@{o} f m) :=
  gal_r_preserves_glb preimage_dual_galois S m H.

(* The two routes inhabit ONE type: the pair typechecks. / 这两条路线属于同一种类型：这对能够进行类型检查。 *)
Definition dual_image_meet_routes_agree {Idx : Type}
  (S : Idx → carrier (Powerset_Prop_obj@{o} X))
  (m : carrier (Powerset_Prop_obj@{o} X))
  (H : IsGLB (@subset_le@{o} X) S m) :
  IsGLB (@subset_le@{o} Y)
    (fun i => Powerset_Prop_dual@{o} f (S i))
    (Powerset_Prop_dual@{o} f m)
  * IsGLB (@subset_le@{o} Y)
      (fun i => Powerset_Prop_dual@{o} f (S i))
      (Powerset_Prop_dual@{o} f m) :=
  (dual_image_preserves_meets S m H,
   dual_image_preserves_meets_via_galois S m H).

(*
 Instance/Powerset.v proved this DIRECTLY, and the comment beside it
 says why: the adjoint route needs f^*'s right adjoint,
 which is this file's.  Here it is, as that corollary. 

 --------
 Instance/Powerset.v 直接证明了这一点，旁边的评论说明了原因：伴随路线需要 f^* 的右伴随，而这就是这个文件的内容。这里是它，作为那个推论。
*)
Definition inverse_image_preserves_joins_via_galois {Idx : Type}
  (T : Idx → carrier (Powerset_Prop_obj@{o} Y))
  (m : carrier (Powerset_Prop_obj@{o} Y))
  (H : IsLUB (@subset_le@{o} Y) T m) :
  IsLUB (@subset_le@{o} X)
    (fun i => Powerset_Prop_preimage@{o} f (T i))
    (Powerset_Prop_preimage@{o} f m) :=
  gal_l_preserves_lub preimage_dual_galois T m H.

Definition inverse_image_join_routes_agree {Idx : Type}
  (T : Idx → carrier (Powerset_Prop_obj@{o} Y))
  (m : carrier (Powerset_Prop_obj@{o} Y))
  (H : IsLUB (@subset_le@{o} Y) T m) :
  IsLUB (@subset_le@{o} X)
    (fun i => Powerset_Prop_preimage@{o} f (T i))
    (Powerset_Prop_preimage@{o} f m)
  * IsLUB (@subset_le@{o} X)
      (fun i => Powerset_Prop_preimage@{o} f (T i))
      (Powerset_Prop_preimage@{o} f m) :=
  (inverse_image_preserves_joins f T m H,
   inverse_image_preserves_joins_via_galois T m H).

End Dual.

Arguments dual_monotone {X Y} f S T H.
Arguments preimage_transpose_to {X Y} f T S H.
Arguments preimage_transpose_from {X Y} f T S H.
Arguments preimage_dual_galois {X Y} f.
Arguments DualImage {X Y} f.
Arguments exists_substitution_adjunction {X Y} f.
Arguments substitution_forall_adjunction {X Y} f.
Arguments quantifier_triple {X Y} f.
Arguments forall_unit_incl {X Y} f T.
Arguments forall_counit_incl {X Y} f S.
Arguments apples_buckets_bicondition {X Y} f T S.
Arguments dual_vacuous {X Y} f S y Hy.
Arguments dual_image_preserves_meets {X Y} f {Idx} S m H.

(* ------------------------------------------------------------------------ *)
(* * ** (B) Mac Lane's site: the first projection U x V -> U / * **（B）Mac Lane 的网站：第一个投影 U x V -> U *)

(*
 The product setoid.  Measured: for [U V : SetoidObject@{o o}] this is
 again a [SetoidObject@{o o}], which is what lets [Subsets] be formed
 on it. 

 --------
 乘积等价类。 测量：对于 [U V : SetoidObject@{o o}]，这又是一个 [SetoidObject@{o o}]，这使得可以在其上形成 [Subsets]。
*)
Definition ProdSetoid@{o so} (U V : SetoidObject@{o o}) : SetoidObject@{o o} :=
  @product_obj Sets@{o so} Sets_Cartesian U V.

(* Mac Lane's [P : U x V -> U]. / 麦克莱恩的 [P : U x V -> U] 。 *)
Definition proj_fst@{o so} (U V : SetoidObject@{o o}) :
  ProdSetoid@{o so} U V ~{Sets@{o so}}~> U :=
  @exl Sets@{o so} Sets_Cartesian U V.

(*
 [P_* S = {x | exists y, y in V and <x,y> in S}].  The existential is
 stdlib's Prop-valued [ex], NOT the library's Type-valued [∃]: the body
 [S (x, y)] is already a [Prop], so no truncation is needed -- the
 mirror image of the measurement (A) makes for the dual image. 

 --------
 [P_* S = {x | exists y, y in V and <x,y> in S}]。存在性的是stdlib的Prop值的[ex]，而不是库的Type值的[∃]：主体[S (x, y)]已经是[Prop]，因此不需要截断——测量(A)的镜像构成了对偶像。
*)
Definition proj_exists@{o so} {U V : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))) :
  carrier (Powerset_Prop_obj@{o} U).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier U) (is_setoid U) Prop (is_setoid Powerset_Prop_truth@{o})
       (λ x, ex (fun y : carrier V => S (x, y))) _).
  intros x x' Hxx'; split; intros Hy; destruct Hy as [y Hy]; exists y.
  - exact (proj1 (@proper_morphism _ _ _ _ S (x, y) (x', y)
                    (Hxx', quant_refl y)) Hy).
  - exact (proj2 (@proper_morphism _ _ _ _ S (x, y) (x', y)
                    (Hxx', quant_refl y)) Hy).
Defined.

(* [P_# S = {x | forall y, y in V implies <x,y> in S}]. / [P_# S = {x | forall y, y in V implies <x,y> in S}] 。 *)
Definition proj_forall@{o so} {U V : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))) :
  carrier (Powerset_Prop_obj@{o} U).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier U) (is_setoid U) Prop (is_setoid Powerset_Prop_truth@{o})
       (λ x, ∀ y : carrier V, S (x, y)) _).
  intros x x' Hxx'; split; intros H y.
  - exact (proj1 (@proper_morphism _ _ _ _ S (x, y) (x', y)
                    (Hxx', quant_refl y)) (H y)).
  - exact (proj2 (@proper_morphism _ _ _ _ S (x, y) (x', y)
                    (Hxx', quant_refl y)) (H y)).
Defined.

(* [P^* X], which Mac Lane calls the cylinder [X x V] over the base X. / [P^* X]，Mac Lane 称其为基底 X 上的圆柱 [X x V]。 *)
Definition cylinder@{o so} {U V : SetoidObject@{o o}}
  (Xs : carrier (Powerset_Prop_obj@{o} U)) :
  carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V)) :=
  Powerset_Prop_preimage@{o} (proj_fst@{o so} U V) Xs.

Section Projection.

Universe o so u.
Constraint o < so.

Context (U V : SetoidObject@{o o}).

Example proj_fst_computes (x : carrier U) (y : carrier V) :
  proj_fst@{o so} U V (x, y) = x := eq_refl.

(* The cylinder over X contains exactly the pairs whose first component lies in X: an equality of [Prop]s, on the nose. / X 上的圆柱恰好包含其第一分量位于 X 的对：这正是 [Prop]s 的相等。 *)
Example cylinder_mem (Xs : carrier (Powerset_Prop_obj@{o} U))
  (x : carrier U) (y : carrier V) :
  @cylinder@{o so} U V Xs (x, y) = Xs x := eq_refl.

(* * *** Mac Lane's two displayed biconditionals / * *** 马克·莱恩展示的两个双条件 *)

(* [S <= P^* X <=> P_* S <= X]. *)
Theorem proj_exists_transpose
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V)))
  (Xs : carrier (Powerset_Prop_obj@{o} U)) :
  iffT (subset_le S (@cylinder@{o so} U V Xs))
       (subset_le (@proj_exists@{o so} U V S) Xs).
Proof.
  split.
  - intros H x Hx; destruct Hx as [y Hy]; exact (H (x, y) Hy).
  - intros H z Hz; destruct z as [x y]; exact (H x (ex_intro _ y Hz)).
Qed.

(* [P^* X <= S <=> X <= P_# S]. *)
Theorem proj_forall_transpose
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V)))
  (Xs : carrier (Powerset_Prop_obj@{o} U)) :
  iffT (subset_le (@cylinder@{o so} U V Xs) S)
       (subset_le Xs (@proj_forall@{o so} U V S)).
Proof.
  split.
  - intros H x Hx y; exact (H (x, y) Hx).
  - intros H z Hz; destruct z as [x y]; exact (H x Hz y).
Qed.

(*
 “P_# S is the largest subset X of U such that the cylinder on X is
 wholly contained in S”.  This IS [proj_forall_transpose] together with
 its unit -- the two components are that biconditional read at
 [Xs := proj_forall S] and at an arbitrary [Xs] -- and is stated
 separately only because Mac Lane states it separately. 

 --------
 “P_# S 是 U 的最大子集 X，使得 X 上的圆柱完全包含在 S 中”。这确实是 [proj_forall_transpose] 以及它的单位——两个部分是在 [Xs := proj_forall S] 处和在任意 [Xs] 处读取的双条件——之所以单独陈述，仅仅是因为 Mac Lane 单独陈述了它。
*)
Theorem proj_forall_largest
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))) :
  subset_le (@cylinder@{o so} U V (@proj_forall@{o so} U V S)) S
  * (∀ Xs : carrier (Powerset_Prop_obj@{o} U),
       subset_le (@cylinder@{o so} U V Xs) S
       → subset_le Xs (@proj_forall@{o so} U V S)).
Proof.
  split.
  - exact (snd (proj_forall_transpose S (@proj_forall@{o so} U V S))
             (fun x Hx => Hx)).
  - intros Xs H; exact (fst (proj_forall_transpose S Xs) H).
Qed.

(* * *** The two Galois connections at Mac Lane's own formulas / * *** 马克·莱恩自己公式中的两个伽罗瓦连接 *)

Definition proj_exists_monotone
  (S T : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V)))
  (H : subset_le S T) :
  subset_le (@proj_exists@{o so} U V S) (@proj_exists@{o so} U V T) :=
  fun x Hx =>
    match Hx with ex_intro _ y Hy => ex_intro _ y (H (x, y) Hy) end.

Definition proj_forall_monotone
  (S T : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V)))
  (H : subset_le S T) :
  subset_le (@proj_forall@{o so} U V S) (@proj_forall@{o so} U V T) :=
  fun x Hx y => H (x, y) (Hx y).

Definition cylinder_monotone
  (Xs Ys : carrier (Powerset_Prop_obj@{o} U)) (H : subset_le Xs Ys) :
  subset_le (@cylinder@{o so} U V Xs) (@cylinder@{o so} U V Ys) :=
  preimage_monotone (proj_fst@{o so} U V) Xs Ys H.

Definition proj_galois_exists :
  GaloisConnection (@subset_le@{o} (ProdSetoid@{o so} U V))
                   (@subset_le@{o} U) :=
  {| gal_l := @proj_exists@{o so} U V
   ; gal_r := @cylinder@{o so} U V
   ; gal_mono_l := proj_exists_monotone
   ; gal_mono_r := cylinder_monotone
   ; gal_to   := fun S Xs H => snd (proj_exists_transpose S Xs) H
   ; gal_from := fun S Xs H => fst (proj_exists_transpose S Xs) H |}.

Definition proj_galois_forall :
  GaloisConnection (@subset_le@{o} U)
                   (@subset_le@{o} (ProdSetoid@{o so} U V)) :=
  {| gal_l := @cylinder@{o so} U V
   ; gal_r := @proj_forall@{o so} U V
   ; gal_mono_l := cylinder_monotone
   ; gal_mono_r := proj_forall_monotone
   ; gal_to   := fun Xs S H => fst (proj_forall_transpose S Xs) H
   ; gal_from := fun Xs S H => snd (proj_forall_transpose S Xs) H |}.

(* * *** The identifications with (A), and their exact grade / * *** 与 (A) 的标识，以及它们的确切等级 *)

(*
 “Also P_* S is the direct image of S under the projection P.”  At [≈]
 and NOT at [eq_refl]: [proj_exists] is an [ex] over [carrier V] while
 [Powerset_Prop_image proj_fst] is a [Powerset_squash] of a [sigT] over
 [carrier (ProdSetoid U V)].  The [eq_refl] form is pinned in
 Test/ProbeQuantifier384.v. 

 --------
 “此外，P_* S 是 S 在投影 P 下的直接像。” 在 [≈] 而不是在 [eq_refl]：[proj_exists] 是 [ex] 在 [carrier V] 上，而 [Powerset_Prop_image proj_fst] 是 [Powerset_squash] 的 [sigT] 在 [carrier (ProdSetoid U V)] 上。[eq_refl] 形式固定在 Test/ProbeQuantifier384.v 中。
*)
Theorem proj_exists_is_image
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))) :
  @proj_exists@{o so} U V S
    ≈ Powerset_Prop_image@{o} (proj_fst@{o so} U V) S.
Proof.
  intro x; split.
  - intro Hx; destruct Hx as [y Hy].
    apply Powerset_squash_intro@{o}; exists (x, y); split;
      [ exact Hy | reflexivity ].
  - intro H; refine (H (ex (fun y : carrier V => S (x, y))) _).
    intros Hz; destruct Hz as [z [Hz Hex]]; exists (snd z).
    refine (proj1 (@proper_morphism _ _ _ _ S z (x, snd z) _) Hz).
    exact (Hex, quant_refl (snd z)).
Qed.

(* And [P_#] is the dual image along the same projection, again at [≈]: [proj_forall] quantifies over [carrier V], the dual image over [carrier (ProdSetoid U V)]. / 并且 [P_#] 是沿相同投影的对偶像，同样在 [≈] 处： [proj_forall] 对 [carrier V] 进行量化，是 [carrier (ProdSetoid U V)] 上的对偶像。 *)
Theorem proj_forall_is_dual
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))) :
  @proj_forall@{o so} U V S
    ≈ Powerset_Prop_dual@{o} (proj_fst@{o so} U V) S.
Proof.
  intro x; split.
  - intros H z Hz.
    exact (proj2 (@proper_morphism _ _ _ _ S z (x, snd z)
                    (Hz, quant_refl (snd z))) (H (snd z))).
  - intros H y; exact (H (x, y) (quant_refl x)).
Qed.

(*
 The two Galois connections' three maps agree with (A)'s.  The RECORDS
 are not compared, and no comparison of the two adjunctions is
 claimed. 

 --------
 这两个伽罗瓦对的三个映射与 (A) 的一致。记录没有被比较，也没有声称对这两个伴随关系进行比较。
*)
Definition proj_maps_agree
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V)))
  (Xs : carrier (Powerset_Prop_obj@{o} U)) :
  (gal_l proj_galois_exists S
     ≈ Powerset_Prop_image@{o} (proj_fst@{o so} U V) S)
  * (gal_r proj_galois_forall S
       ≈ Powerset_Prop_dual@{o} (proj_fst@{o so} U V) S)
  * (gal_r proj_galois_exists Xs
       = Powerset_Prop_preimage@{o} (proj_fst@{o so} U V) Xs) :=
  ((proj_exists_is_image S, proj_forall_is_dual S), eq_refl).

End Projection.

(* ------------------------------------------------------------------------ *)
(* * ** (C) Beck-Chevalley for the reindexed projection / * ** (C) Beck-Chevalley 对重新索引的投影 *)

(*
 [g x id], written out rather than assembled from [split]/[bimap].
 Declared at top level, as the donors declare [Powerset_Prop_image] and
 [Powerset_Prop_preimage], so that [g] occurs explicitly in every
 statement below and no [Proof using] clause is needed. 

 --------
 [g x id]，而不是由 [split] / [bimap] 组装而成。  
 在顶层声明，就像捐赠者声明 [Powerset_Prop_image] 和 [Powerset_Prop_preimage] 一样，这样 [g] 会在下面的每个语句中明确出现，而不需要 [Proof using] 子句。
*)
Definition cyl_reindex@{o so} {U U' : SetoidObject@{o o}}
  (V : SetoidObject@{o o}) (g : U' ~{Sets@{o so}}~> U) :
  ProdSetoid@{o so} U' V ~{Sets@{o so}}~> ProdSetoid@{o so} U V.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier (ProdSetoid@{o so} U' V)) (is_setoid (ProdSetoid@{o so} U' V))
       (carrier (ProdSetoid@{o so} U V)) (is_setoid (ProdSetoid@{o so} U V))
       (λ z, (g (fst z), snd z)) _).
  intros z z' Hzz'; split.
  - exact (proper_morphism g _ _ (fst Hzz')).
  - exact (snd Hzz').
Defined.

Section BeckChevalley.

Universe o so.
Constraint o < so.

Context (U U' V : SetoidObject@{o o}).
Context (g : U' ~{Sets@{o so}}~> U).

(*
 Both squares commute POINTWISE ON THE NOSE: the inverse image is
 precomposition, so the two membership [Prop]s beta-iota-reduce to the
 same thing.  These are equalities of [Prop]s, not of morphisms. 

 --------
 两个方框在点上完全对易：逆像是前合成，所以两个成员 [Prop] 经 beta-iota 化简后是相同的。这些是 [Prop] 的等式，而不是态射的等式。
*)
Example beck_chevalley_exists_mem
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V)))
  (x : carrier U') :
  Powerset_Prop_preimage@{o} g (@proj_exists@{o so} U V S) x
    = @proj_exists@{o so} U' V
        (Powerset_Prop_preimage@{o} (cyl_reindex V g) S) x
  := eq_refl.

Example beck_chevalley_forall_mem
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V)))
  (x : carrier U') :
  Powerset_Prop_preimage@{o} g (@proj_forall@{o so} U V S) x
    = @proj_forall@{o so} U' V
        (Powerset_Prop_preimage@{o} (cyl_reindex V g) S) x
  := eq_refl.

(*
 And at WHOLE-SUBSET Leibniz equality too, which is stronger than the
 pointwise form and than [≈].  It was not expected, and what is
 measured is kept apart from what is explained.  Measured:
 [SetoidMorphism] has primitive projections with eta, so record
 equality IS field equality, and the [proper_morphism] certificate is
 NOT irrelevant (two arbitrary proofs of one such [Proper] statement do
 NOT convert -- out of tree).  Hence a typechecking [eq_refl] here
 forces BOTH fields to converge, certificates included.  Explained,
 not measured: they converge because [cyl_reindex] reduces
 [(g (fst z), snd z)] at a literal pair and its own certificate
 projects the pair of hypotheses, which is what the other side feeds
 to [S]'s certificate.  The one experiment available -- flipping
 [cyl_reindex] to [Qed] -- breaks all SIX Beck-Chevalley statements at
 once (the two pointwise [Prop] equalities, these two, and both [≈]
 readings), so it shows transparency of [cyl_reindex] is load-bearing
 for every one of them and isolates nothing about the certificates. 

 --------
 在全子集莱布尼茨相等（WHOLE-SUBSET Leibniz equality）下也是如此，它比逐点形式和 [≈] 更强。这是出乎意料的，而且被测量的与被解释的内容是分开的。被测量的：[SetoidMorphism] 具有带有 eta 的初等投影，因此记录相等就是字段相等，并且 [proper_morphism] 证书也不是无关的（两个任意的此类 [Proper] 声明的证明不会转换——脱离树）。因此这里的类型检查 [eq_refl] 强制要求两个字段都收敛，包括证书。解释的，而非被测量的：它们收敛是因为 [cyl_reindex] 在文字对及其自身证书上化简 [(g (fst z), snd z)]，该证书投影了假设对，这正是另一方提供给 [S] 的证书内容。唯一可用的实验 —— 将 [cyl_reindex] 翻转为 [Qed] —— 一次性打破了所有六个 Beck-Chevalley 陈述（两个逐点 [Prop] 等式，这两个，以及两个 [≈] 读数），所以它显示 [cyl_reindex] 的透明性对每一个都是承重的，并且没有隔离关于证书的任何内容。
*)
Example beck_chevalley_exists
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))) :
  Powerset_Prop_preimage@{o} g (@proj_exists@{o so} U V S)
    = @proj_exists@{o so} U' V (Powerset_Prop_preimage@{o} (cyl_reindex V g) S)
  := eq_refl.

Example beck_chevalley_forall
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))) :
  Powerset_Prop_preimage@{o} g (@proj_forall@{o so} U V S)
    = @proj_forall@{o so} U' V (Powerset_Prop_preimage@{o} (cyl_reindex V g) S)
  := eq_refl.

(* The [≈] readings, for a consumer who wants the order-theoretic form. / 对于想要顺序理论形式的消费者，[≈] 的读数。 *)
Theorem beck_chevalley_exists_equiv
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))) :
  Powerset_Prop_preimage@{o} g (@proj_exists@{o so} U V S)
    ≈ @proj_exists@{o so} U' V (Powerset_Prop_preimage@{o} (cyl_reindex V g) S).
Proof. intro x; split; intro H; exact H. Qed.

Theorem beck_chevalley_forall_equiv
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))) :
  Powerset_Prop_preimage@{o} g (@proj_forall@{o so} U V S)
    ≈ @proj_forall@{o so} U' V (Powerset_Prop_preimage@{o} (cyl_reindex V g) S).
Proof. intro x; split; intro H; exact H. Qed.

End BeckChevalley.

(* ------------------------------------------------------------------------ *)
(* * ** (E) Riehl 4.1.9, and Exercise 4.1.ii / * ** (E) Riehl 4.1.9，以及练习 4.1.ii *)

(* A predicate on X in Riehl's sense IS an element of the power set here. Both readings are equalities of TYPES and of [Prop]s. / 在 Riehl 的意义上，X 上的谓词在这里是幂集的一个元素。两种解读都是类型和 [Prop] 的等式。 *)
Example predicates_are_subsets@{o} (X : SetoidObject@{o o}) :
  carrier (Powerset_Prop_obj@{o} X)
    = SetoidMorphism@{o o o} X Powerset_Prop_truth@{o} := eq_refl.

Example pointwise_is_subset_le@{o} {X : SetoidObject@{o o}}
  (S T : carrier (Powerset_Prop_obj@{o} X)) :
  @subset_le@{o} X S T = (∀ x : carrier X, S x → T x) := eq_refl.

(* The one-point setoid, and the unique map into it. Named locally: both [SetsOne] (Construction/Elements.v, Instance/Sets/Pointed/ Coslice.v) and [Sets_Terminal] are taken. / 单点集合以及指向它的唯一映射。在本地命名：[SetsOne]（Construction/Elements.v, Instance/Sets/Pointed/Coslice.v）和 [Sets_Terminal] 都已被使用。 *)
Definition quant_one@{o so} : SetoidObject@{o o} :=
  @terminal_obj Sets@{o so} Sets_Terminal.

Definition quant_bang@{o so} (X : SetoidObject@{o o}) :
  X ~{Sets@{o so}}~> quant_one@{o so} :=
  @one Sets@{o so} Sets_Terminal X.

Section Riehl.

Universe o so u.
Constraint o < so.

Context (X : SetoidObject@{o o}).

(*
 Riehl's [Delta_X], [exists_X] and [forall_X], as the three functors of
 Example 4.1.8 at the unique map [X -> 1].  That instantiation IS her
 Exercise 4.1.ii. 

 --------
 Riehl 的 [Delta_X]、[exists_X] 和 [forall_X]，作为例 4.1.8 中在唯一映射 [X -> 1] 的三个函子。这个实例化就是她的练习 4.1.ii。
*)
Definition Delta_X : Subsets@{o u} quant_one@{o so} ⟶ Subsets@{o u} X :=
  InverseImage (quant_bang@{o so} X).

Definition exists_X : Subsets@{o u} X ⟶ Subsets@{o u} quant_one@{o so} :=
  DirectImage (quant_bang@{o so} X).

Definition forall_X : Subsets@{o u} X ⟶ Subsets@{o u} quant_one@{o so} :=
  DualImage (quant_bang@{o so} X).

(* [exists_X -| Delta_X -| forall_X], both legs by instantiation. / [exists_X -| Delta_X -| forall_X]，通过实例化两条腿。 *)
Definition riehl_exists_delta : exists_X ⊣ Delta_X :=
  exists_substitution_adjunction (quant_bang@{o so} X).

Definition riehl_delta_forall : Delta_X ⊣ forall_X :=
  substitution_forall_adjunction (quant_bang@{o so} X).

Definition riehl_adjoint_triple :
  (exists_X ⊣ Delta_X) * (Delta_X ⊣ forall_X) :=
  (riehl_exists_delta, riehl_delta_forall).

(*
 [Delta_X] is her constant functor: its value at [P] is the predicate
 constantly [P ttt].  An equality of [Prop]s, on the nose. 

 --------
 [Delta_X] 是她的常量函子：它在 [P] 的值是谓词恒为 [P ttt]。在 [Prop] 之间的相等，完全相同。
*)
Example Delta_X_obj_mem
  (P : carrier (Powerset_Prop_obj@{o} quant_one@{o so})) (x : carrier X) :
  fobj[Delta_X] P x = P ttt := eq_refl.

End Riehl.

(* * *** The truth-value object: [Subsets 1] against [Props] / * *** 真值对象：[Subsets 1] 对 [Props] *)

Section TruthValues.

Universe o so u.
Constraint o < so.

(* Evaluation at the point. Functoriality is free: [Props] is thin. / 在该点的评估。函子性是免费的：[Props] 是薄的。 *)
Program Definition subsets_one_to_Props :
  Subsets@{o u} quant_one@{o so} ⟶ Props@{o u} := {|
  fobj := fun S => S ttt;
  fmap := fun S T (h : subset_le S T) => h ttt
|}.

(*
 The constant predicate on the one-point setoid.  Its respectfulness
 certificate is written out as a term rather than left to instance
 resolution: Theory/Universal/Element.v records that resolving
 [proper_morphism] for a [Sets]-morphism out of a concrete one-point
 setoid pins the carrier universe at [Set], and the pointwise term
 avoids the resolution entirely. 

 --------
 单点集合上的常量谓词。它的尊重性证明被写成一个项，而不是留给实例解析：Theory/Universal/Element.v 记录了解析来自具体单点集合的 [Sets]-态射的 [proper_morphism] 会将承载集合宇宙固定在 [Set]，并且逐点项完全避免了解析。
*)
Program Definition Props_to_subsets_one :
  Props@{o u} ⟶ Subsets@{o u} quant_one@{o so} := {|
  fobj := fun P =>
    @Build_SetoidMorphism@{o o o}
      (carrier quant_one@{o so}) (is_setoid quant_one@{o so})
      Prop (is_setoid Powerset_Prop_truth@{o}) (λ _, P)
      (fun _ _ _ => conj (fun p : P => p) (fun p : P => p));
  fmap := fun P Q (h : P → Q) => fun _ (p : P) => h p
|}.

(*
 Both round trips.  One is the identity on the nose at the level of
 [Prop]s; the other needs the point to be destructed. 

 --------
 两个往返。一个在 [Prop] s 级别上就是精确的恒等；另一个需要将点进行销毁。
*)
Example Props_subsets_one_round (P : Props@{o u}) :
  fobj[subsets_one_to_Props] (fobj[Props_to_subsets_one] P) = P := eq_refl.

Theorem subsets_one_Props_round
  (S : carrier (Powerset_Prop_obj@{o} quant_one@{o so})) :
  fobj[Props_to_subsets_one] (fobj[subsets_one_to_Props] S) ≈ S.
Proof. intro x; destruct x; split; intro H; exact H. Qed.

(*
 Riehl's Omega, up to equivalence.  [≅[Cat]] IS equivalence in this
 library ([Cat]'s hom-setoid is [Functor_Setoid]); an isomorphism OF
 CATEGORIES is unavailable, the object types differing, and none is
 claimed. 

 --------
 Riehl 的 Omega，直到等价。[≅[Cat] 是该库中的等价（[Cat] 的同态集合是 [Functor_Setoid]）；范畴的同构不可用，对象类型不同，也没有声称有同构。
*)
Program Definition subsets_one_Props :
  @Isomorphism Cat (Subsets@{o u} quant_one@{o so}) Props@{o u} := {|
  to   := subsets_one_to_Props;
  from := Props_to_subsets_one
|}.
Next Obligation.
  unshelve eexists.
  - intro S; unshelve econstructor.
    + exact (fun x Hx => proj1 (subsets_one_Props_round S x) Hx).
    + exact (fun x Hx => proj2 (subsets_one_Props_round S x) Hx).
    + exact I.
    + exact I.
  - intros S T h; exact I.
Defined.

End TruthValues.

(* ------------------------------------------------------------------------ *)
(* * ** (D) again: Awodey's two contrapositives, at a concrete witness / * **（D）再次：Awodey 的两个逆命题，在具体证据处 *)

(*
 The witnesses are #382's own: [powerset_fin2] (the two-element
 discrete setoid), [powerset_const0] (the constant map at 0),
 [powerset_sng1] = {1} and Instance/Powerset.v's [powerset_sng0] = {0}.
 None is rebuilt. 

 --------
 证人是 #382 本身的：[powerset_fin2]（两个元素的离散集合）、[powerset_const0]（常值映射为 0）、[powerset_sng1] = {1} 和 Instance/Powerset.v 的 [powerset_sng0] = {0}。没有任何一个被重建。
*)

(*
 The dual image of {0} along the constant map at 0 contains 1 --
 VACUOUSLY, since nothing maps to 1.  This is Fong-Spivak's “empty
 buckets count”, and it refutes the brief's prediction that this dual
 image is empty. 

 --------
 {0} 在 0 的常值映射下的对偶像包含 1——这是空的，因为没有任何东西映射到 1。这是 Fong-Spivak 的“空桶计数”，并且它驳斥了简报中对该对偶像为空的预测。
*)
Theorem dual_const0_sng0_at_1@{o so +} :
  Powerset_Prop_dual@{o} powerset_const0@{o so} powerset_sng0@{o}
    (Fin.FS Fin.F1).
Proof. intros x Heq; discriminate Heq. Qed.

(* ... and does NOT contain 0: the fibre over 0 is the whole set, and 1 is not in {0}. / ... 并且不包含 0：0 的纤维是整个集合，并且 1 不在 {0} 中。 *)
Theorem dual_const0_sng0_not_at_0@{o so +} :
  Powerset_Prop_dual@{o} powerset_const0@{o so} powerset_sng0@{o} Fin.F1
  → False.
Proof.
  intro H.
  refine (H (Fin.FS Fin.F1) eq_refl False _).
  intro Heq; discriminate Heq.
Qed.

(*
 The direct image of {1} DOES contain 0.  This is
 Instance/Sets/Powerset/Universal.v's own [powerset_direct_sng1_at_0]
 read through [Powerset_Prop_fmap_image], not a second proof. 

 --------
 {1} 的直接映像确实包含 0。这是 Instance/Sets/Powerset/Universal.v 自己的 [powerset_direct_sng1_at_0]，通过 [Powerset_Prop_fmap_image] 阅读，而不是第二个证明。
*)
Definition image_const0_sng1_at_0@{o so} :
  Powerset_Prop_image@{o} powerset_const0@{o so} powerset_sng1@{o} Fin.F1 :=
  powerset_direct_sng1_at_0@{o so}.

(* THE TWO ADJOINTS DIFFER. At {1} the existential contains 0 and the universal does not: the whole point of the third leg. / 两个伴随项不同。在 {1} 时，存在量词包含 0，而全称量词不包含：这正是第三条的全部要点。 *)
Theorem exists_ne_forall_at_const0@{o so +} :
  Powerset_Prop_image@{o} powerset_const0@{o so} powerset_sng1@{o}
    ≈ Powerset_Prop_dual@{o} powerset_const0@{o so} powerset_sng1@{o}
  → False.
Proof.
  intro H.
  refine (proj1 (H Fin.F1) image_const0_sng1_at_0@{o so}
            Fin.F1 eq_refl False _).
  intro Heq; discriminate Heq.
Qed.

(* Every element of the two-point carrier lies in {0} join {1}: the exhaustiveness the join witness needs, by the [Fin.caseS']/[Fin.case0] idiom of Structure/Limit/Product/Finite.v. / 两个点载体的每个元素都位于 {0} join {1} 中：由 Structure/Limit/Product/Finite.v 的 [Fin.caseS'] / [Fin.case0] 习语所需的 join 证据的完备性。 *)
Lemma fin2_in_sng0_join_sng1@{o +} (i : Fin.t 2%nat) :
  subset_join powerset_sng0@{o} powerset_sng1@{o} i.
Proof.
  pattern i; apply (Fin.caseS' i).
  - exists true; apply Powerset_squash_intro@{o}; reflexivity.
  - intro j; pattern j; apply (Fin.caseS' j).
    + exists false; apply Powerset_squash_intro@{o}; reflexivity.
    + intro k; apply (Fin.case0 (fun _ => _) k).
Qed.

(*
 THE DUAL IMAGE DOES NOT PRESERVE JOINS.  Stated as the refutation of
 the INCLUSION, which is what the contrapositive below consumes and
 which is strictly stronger than refuting the [≈]. 

 --------
 双重图像不保留连接。表述为对包含关系的反驳，这正是下面的逆否命题所使用的，并且它比反驳 [≈] 更严格。
*)
Theorem dual_image_not_join_preserving@{o so +} :
  subset_le
    (Powerset_Prop_dual@{o} powerset_const0@{o so}
       (subset_join powerset_sng0@{o} powerset_sng1@{o}))
    (subset_join
       (Powerset_Prop_dual@{o} powerset_const0@{o so} powerset_sng0@{o})
       (Powerset_Prop_dual@{o} powerset_const0@{o so} powerset_sng1@{o}))
  → False.
Proof.
  intro H.
  assert (Hin : Powerset_Prop_dual@{o} powerset_const0@{o so}
                  (subset_join powerset_sng0@{o} powerset_sng1@{o}) Fin.F1)
    by (intros x _; exact (fin2_in_sng0_join_sng1 x)).
  destruct (H Fin.F1 Hin) as [b Hb]; destruct b.
  - refine (Hb (Fin.FS Fin.F1) eq_refl False _);
      intro Heq; discriminate Heq.
  - refine (Hb Fin.F1 eq_refl False _); intro Heq; discriminate Heq.
Qed.

Theorem dual_image_not_join_preserving_equiv@{o so +} :
  Powerset_Prop_dual@{o} powerset_const0@{o so}
      (subset_join powerset_sng0@{o} powerset_sng1@{o})
    ≈ subset_join
        (Powerset_Prop_dual@{o} powerset_const0@{o so} powerset_sng0@{o})
        (Powerset_Prop_dual@{o} powerset_const0@{o so} powerset_sng1@{o})
  → False.
Proof.
  intro H.
  exact (dual_image_not_join_preserving (fun x => proj1 (H x))).
Qed.

(*
 Awodey: “Since this does not hold for exists x, it cannot be a right
 adjoint to some other 'quantifier'.”  As a theorem about adjunctions:
 the direct image along [powerset_const0] has NO left adjoint.  [∃] is
 the library's Type-valued [sigT], and the sigma binds the functor
 once. 

 --------
 Awodey: “由于这对于存在 x 不成立，因此它不能是某个其他‘量词’的右伴随。” 作为关于伴随的一条定理：沿着 [powerset_const0] 的直接像没有左伴随。[∃] 是库中的类型值 [sigT]，sigma 绑定这个函子一次。
*)
Theorem exists_not_right_adjoint@{o so u +} :
  (∃ L : Subsets@{o u} powerset_fin2@{o} ⟶ Subsets@{o u} powerset_fin2@{o},
     L ⊣ DirectImage powerset_const0@{o so})
  → False.
Proof.
  intros [L Adj].
  pose (G := GaloisOfAdjunction (subset_le_preorder@{o} powerset_fin2@{o})
               (subset_le_preorder@{o} powerset_fin2@{o})
               L (DirectImage powerset_const0@{o so}) Adj).
  pose (HG := gal_r_preserves_glb G
                (pair_family powerset_sng0@{o} powerset_sng1@{o})
                (subset_meet powerset_sng0@{o} powerset_sng1@{o})
                (subset_inter_IsGLB
                   (pair_family powerset_sng0@{o} powerset_sng1@{o}))).
  (* The nontrivial inclusion, from the adjoint hypothesis. / 从伴随假设出的非平凡包含。 *)
  assert (Hge : subset_le
                  (subset_meet
                     (Powerset_Prop_image@{o} powerset_const0@{o so}
                        powerset_sng0@{o})
                     (Powerset_Prop_image@{o} powerset_const0@{o so}
                        powerset_sng1@{o}))
                  (Powerset_Prop_image@{o} powerset_const0@{o so}
                     (subset_meet powerset_sng0@{o} powerset_sng1@{o}))).
  { refine (snd HG _ _); intros [|].
    - exact (subset_meet_l _ _).
    - exact (subset_meet_r _ _). }
  (* ... and the trivial one, from monotonicity. / ...以及平凡的那个，来自单调性。 *)
  assert (Hle : subset_le
                  (Powerset_Prop_image@{o} powerset_const0@{o so}
                     (subset_meet powerset_sng0@{o} powerset_sng1@{o}))
                  (subset_meet
                     (Powerset_Prop_image@{o} powerset_const0@{o so}
                        powerset_sng0@{o})
                     (Powerset_Prop_image@{o} powerset_const0@{o so}
                        powerset_sng1@{o}))).
  { refine (subset_meet_greatest _ _ _ _ _).
    - exact (image_monotone powerset_const0@{o so} _ _
               (subset_meet_l _ _)).
    - exact (image_monotone powerset_const0@{o so} _ _
               (subset_meet_r _ _)). }
  (*
 Mutual inclusion IS [≈] -- Instance/Grp/Galois.v's
 [subset_le_antisym], written inline for the measured reason in the
 header. 

 --------
 互相包含是 [≈] -- Instance/Grp/Galois.v 的 [subset_le_antisym]，出于头部中说明的理由而内联编写。
*)
  exact (direct_image_not_meet_preserving
           (fun x => conj (Hle x) (Hge x))).
Qed.

(*
 And dually: “as above, forall x cannot be a left adjoint, since it
 does not have this property.” 

 --------
 反之亦然：“如上所述，对于所有 x，它不能是一个左伴随，因为它不具有这个性质。”
*)
Theorem forall_not_left_adjoint@{o so u +} :
  (∃ R : Subsets@{o u} powerset_fin2@{o} ⟶ Subsets@{o u} powerset_fin2@{o},
     DualImage powerset_const0@{o so} ⊣ R)
  → False.
Proof.
  intros [R Adj].
  pose (G := GaloisOfAdjunction (subset_le_preorder@{o} powerset_fin2@{o})
               (subset_le_preorder@{o} powerset_fin2@{o})
               (DualImage powerset_const0@{o so}) R Adj).
  pose (HG := gal_l_preserves_lub G
                (pair_family powerset_sng0@{o} powerset_sng1@{o})
                (subset_join powerset_sng0@{o} powerset_sng1@{o})
                (subset_union_IsLUB
                   (pair_family powerset_sng0@{o} powerset_sng1@{o}))).
  refine (dual_image_not_join_preserving _).
  refine (snd HG _ _); intros [|].
  - exact (subset_join_l _ _).
  - exact (subset_join_r _ _).
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** (G) Non-vacuity over Mac Lane's own site / * **（G）在 Mac Lane 自身站点上的非空性 *)

(* Both factors are the two-element discrete setoid. / 两个因素是双元素离散集合。 *)
Definition quant_sq@{o so} : SetoidObject@{o o} :=
  ProdSetoid@{o so} powerset_fin2@{o} powerset_fin2@{o}.

Section ProjectionWitness.

Universe o so.
Constraint o < so.

(* The diagonal {(x, x)}. / 对角线 {(x, x)}。 *)
Definition diag_subset : carrier (Powerset_Prop_obj@{o} quant_sq@{o so}).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier quant_sq@{o so}) (is_setoid quant_sq@{o so})
       Prop (is_setoid Powerset_Prop_truth@{o})
       (λ z, fst z = snd z) _).
  intros z z' Hzz'; destruct Hzz' as [H1 H2]; split; intro H.
  - rewrite <- H1, <- H2; exact H.
  - rewrite H1, H2; exact H.
Defined.

(* The row {(0, y) | y}. / 行 {(0, y) | y}。 *)
Definition row0_subset : carrier (Powerset_Prop_obj@{o} quant_sq@{o so}).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier quant_sq@{o so}) (is_setoid quant_sq@{o so})
       Prop (is_setoid Powerset_Prop_truth@{o})
       (λ z, fst z = Fin.F1) _).
  intros z z' Hzz'; destruct Hzz' as [H1 _]; split; intro H.
  - rewrite <- H1; exact H.
  - rewrite H1; exact H.
Defined.

(* Mac Lane's projection of the diagonal is everything: every x pairs with itself. / Mac Lane 的对角投影就是一切：每个 x 都与自身配对。 *)
Theorem proj_diag_exists_everywhere (x : Fin.t 2%nat) :
  @proj_exists@{o so} powerset_fin2@{o} powerset_fin2@{o} diag_subset x.
Proof. exists x; reflexivity. Qed.

(* ... while [P_#] of the diagonal is empty: no x pairs with EVERY y. / ... 而当对角线的 [P_#] 为空时：没有 x 与每个 y 配对。 *)
Theorem proj_diag_forall_nowhere (x : Fin.t 2%nat) :
  @proj_forall@{o so} powerset_fin2@{o} powerset_fin2@{o} diag_subset x
  → False.
Proof.
  intro H.
  pose proof (H Fin.F1) as H0; pose proof (H (Fin.FS Fin.F1)) as H1.
  simpl in H0, H1.
  rewrite H0 in H1; discriminate H1.
Qed.

(* At a ROW, [P_#] is the singleton {0}: the row over 0 is full, the row over 1 is empty. / 在一个ROW中，[P_#]是单元素集合{0}：位于0上的行是满的，位于1上的行是空的。 *)
Theorem proj_row_forall_at_0 :
  @proj_forall@{o so} powerset_fin2@{o} powerset_fin2@{o} row0_subset
    Fin.F1.
Proof. intro y; reflexivity. Qed.

Theorem proj_row_forall_not_at_1 :
  @proj_forall@{o so} powerset_fin2@{o} powerset_fin2@{o} row0_subset
    (Fin.FS Fin.F1)
  → False.
Proof. intro H; pose proof (H Fin.F1) as H0; discriminate H0. Qed.

End ProjectionWitness.
