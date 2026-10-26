(* * * The Galois connection of a group acting on a set / * * 群作用于集合上的伽罗瓦连接 *)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Proset.Limit.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Deloop.Functors.
Require Import Category.Instance.Rep.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Adjunction.Right.

(*
 Same two as Instance/Powerset.v and Instance/Proset/Galois.v, and
 for the same reason and in the same position: [relation] and [PreOrder]
 below are the stdlib Prop-valued ones, not Category.Lib's [crelation]
 ones, and they must be required AFTER Category.Lib to win. 

 --------
 与 Instance/Powerset.v 和 Instance/Proset/Galois.v 中的两个相同，并且出于相同的原因、在相同的位置：下面的 [relation] 和 [PreOrder] 是 stdlib 的 Prop 值版本，而不是 Category.Lib 的 [crelation] 版本，并且它们必须在 Category.Lib 之后被引入以生效。
*)
Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(*
   * Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.5
   construction 1 (printed p. 96).  Transcribed from the page image, in
   ASCII:

   “A pair of order-preserving functions L and R which satisfy (1) is
   called a Galois connection from P to Q.  Here is the fundamental
   example, for a group G acting on a set U, by <sigma, x> |-> sigma . x
   for sigma in G, x in U.  Take P = P(U), the set of all subsets
   X subset U, ordered by inclusion, while Q = P(G) is the set of
   subsets S subset G also ordered by inclusion (S <= S' if and only if
   S subset S').  Let L X = {sigma | x in X implies sigma . x = x},
   R S = {x | sigma in S implies sigma . x = x}; in other words, L X is
   the subgroup of G which fixes all points x in X and R S is the set of
   fixed points of the automorphisms of S.  Then L X >= S in Q if and
   only if sigma . x = x for all sigma in S and all x in X, which in
   turn holds if and only if X <= R S in P.  Therefore, L and R form an
   adjoint pair (a Galois connection).  The original instance is that
   with G a group of automorphisms of a field U, as in the classical
   Galois theory.”

   and, from printed p. 95, the theorem the paragraph is a corollary of,
   together with its two displays:

   “Theorem 1 (Galois connections are adjoint pairs).  Let P, Q be two
   preorders and L : P -> Q^op, R : Q^op -> P two order-preserving
   functions.  Then L (regarded as a functor) is a left adjoint to R if
   and only if, for all p in P and q in Q,

   L p >= q  in  Q  if and only if  p <= R q  in  P .       (1)

   When this is the case, there is exactly one adjunction phi making L
   the left adjoint of R.  For all p and q, p <= R L p and L R q >= q;
   hence also

   L p >= L R L p >= L p ,    R q <= R L R q <= R q .        (2)”

   nLab: https://ncatlab.org/nlab/show/Galois+connection
   nLab: https://ncatlab.org/nlab/show/group+action
   nLab: https://ncatlab.org/nlab/show/closure+operator
   nLab: https://ncatlab.org/nlab/show/stabilizer+group
   nLab: https://ncatlab.org/nlab/show/fixed+point
   Wikipedia: https://en.wikipedia.org/wiki/Galois_connection
   Wikipedia:
   https://en.wikipedia.org/wiki/Fundamental_theorem_of_Galois_theory

   ** THE CONNECTION IS ANTITONE, AND THAT IS MAC LANE'S OWN Q^op

   Display (1) reads “L p >= q in Q”, not “L p <= q”: Theorem 1 types L as
   a functor P -> Q^op, and the construction paragraph says “L X >= S in
   Q”.  So the pair here is order-REVERSING in each variable, which is
   what the classical Galois correspondence between subgroups and
   subfields is.  Instance/Proset/Galois.v's [GaloisConnection RA RB]
   is stated covariantly -- its [gal_mono_l] concludes [RB (gal_l a)
   (gal_l a')] from [RA a a'] -- so the antitone reading is obtained by
   taking [RB] to be the REVERSED inclusion on P(G), which is
   Instance/Proset/Limit.v's [op_rel].  That is a faithful rendering
   of the book's [Q^op] and not a departure from it; the covariant
   ascription is rejected, and that rejection is pinned in
   Test/ProbeGalois381.v as a typing negative.

   ** THE ISSUE'S “Current state” IS STALE ON FOUR COUNTS, MEASURED AT THE
   BASE COMMIT

   The catalog entry says: “Absent.  Structure/Group.v declares only
   [GroupObject] ... no action, no subgroup lattice”, and asks for the
   group, the action, the subgroup notion and the powerset preorder to be
   built.  All four exist.

   (1) Instance/Grp.v's [GrpObject] is the setoid-level group (carrier,
   unit, multiplication, inversion, with the right-handed laws and
   respectfulness of inversion DERIVED), with [GrpHom] and the
   category [Grp].

   (2) A monoid acting on a setoid is
   Construction/Deloop/Functors.v's [Record MSetoidAction (M :
   MonObject)] -- fields [act_setoid], [act], [act_respects],
   [act_unit], [act_op], in Riehl 1.3.9's left convention
   [act (g . h) x = act g (act h x)] -- with equivariant maps at
   Instance/Fun/Action.v and the category [MSet M] there.  It is
   CONSUMED below; no second action record is declared.

   (3) Instance/Grp/Quotient.v's [Record Subgroup (G : GrpObject)] --
   fields [sub_mem : carrier G -> Type], [sub_resp], [sub_unit],
   [sub_mul], [sub_inv] -- is the subgroup notion.  It is what
   [stab_Subgroup] below inhabits.

   (4) The powerset preorder is Instance/Powerset.v's
   [subset_le] / [subset_le_preorder] / [Subsets X := Proset
   (subset_le_preorder X)], over Instance/Sets/Powerset.v's
   [Powerset_Prop_obj X] -- the [equiv]-respecting Prop-valued
   predicates on a setoid, that is [SetoidMorphism X
   Powerset_Prop_truth].

   Two further corrections to the surrounding prose.  The issue's
   suggested module [Instance/Group/Galois.v] names a directory that does
   not exist; the tree's group directory is [Instance/Grp/], so the file
   is placed there.  And the bridge from a group to the monoid an
   [MSetoidAction] acts by is Instance/Rep.v's [grp_mon], consumed
   here.  ([Construction/Deloop.v] declares a SECOND record also named
   [GrpObject], layered on [MonObject]; it is not the one
   Instance/Grp/Quotient.v's [Subgroup] is over, so the file imports
   Instance.Grp LAST and every [GrpObject] below is Instance/Grp.v's.)

   ** PRIOR ART: THE THREE EXISTING GALOIS CONNECTIONS, AND WHAT IS NEW

   At the base commit exactly three library constants inhabit
   [GaloisConnection] at NAMED relations (Instance/Proset/Galois.v's
   [GaloisOfAdjunction] and its [galois_of_unit_counit] are parametric
   constructions over arbitrary [RA]/[RB], so a grep finds five):
   Instance/Proset/Galois.v's [nat_shift_galois]
   (truncated subtraction left adjoint to addition on the naturals),
   Instance/Powerset.v's [image_preimage_galois] (direct image left
   adjoint to inverse image) and Instance/FinSet/Subsets.v's
   [finpow_image_preimage_galois] (the same over decidable finite
   subsets).  A fourth occurrence, Test/ProbePowerset382.v, is a probe
   control.  ALL THREE library ones are COVARIANT: each has both maps
   monotone for the given inclusions.  [group_action_galois] below is
   therefore the tree's first ANTITONE one -- the first whose second
   relation is [op_rel] of an inclusion -- which is the shape the
   classical Galois correspondence has.

   NO closure-operator vocabulary existed anywhere: a search for a
   composite [gal_l (gal_r (gal_l _))] or [gal_r (gal_l (gal_r _))], and
   for the tokens [ClosureOperator] and [closure_op], returns nothing
   outside this file.  Section (A) supplies Mac Lane's display (2) over an
   ARBITRARY [GaloisConnection]; it is stated here because
   Instance/Proset/Galois.v is not edited by this change, and it is a
   candidate for moving there when a second consumer appears.

   ** THE ONE DEVIATION FROM THE BOOK, AND WHY IT IS FORCED

   Mac Lane's membership condition is the EQUATION [sigma . x = x] in a
   set.  Here the ambient equality is a setoid's [equiv], which in this
   library is [crelation]-valued, hence [Type]-valued -- while a member of
   [Powerset_Prop_obj X] must be [Prop]-valued, since [subset_le] has to
   be a stdlib [relation] for [Proset] and [GaloisConnection] to apply at
   all (Instance/Powerset.v records that constraint).  The fixing
   condition is therefore TRUNCATED, by Instance/Sets/Powerset.v's
   impredicative [Powerset_squash A := forall Q : Prop, (A -> Q) -> Q],
   exactly as [Powerset_Prop_image] truncates its existential.  Nothing is
   lost where it matters: every goal into which the truncation has to be
   eliminated below is itself a [Prop], and
   Instance/Sets/Powerset/Universal.v's [powerset_squash_prop_inert]
   records that over a [Prop] the truncation is inert -- which is the case
   at both witnesses, whose setoids are [eq_Setoid]s.

   ** WHAT IS DELIVERED, WITH GRADES

   (A) GENERAL, over an arbitrary [GaloisConnection RA RB] with both
   preorders: [gal_lrl_below]/[gal_lrl_above] and
   [gal_rlr_below]/[gal_rlr_above], which ARE Mac Lane's display (2)
   --- [L p >= L R L p >= L p] and [R q <= R L R q <= R q] -- each a
   [:=] term with no tactic over the donor's [gal_unit] and
   [gal_counit]: [gal_lrl_below] IS the counit evaluated at
   [gal_l a] and [gal_rlr_above] IS the unit evaluated at [gal_r b],
   with no further step, while [gal_lrl_above] and [gal_rlr_below]
   are the other two pushed through one monotonicity field; the
   closedness predicates [GalClosed_l]/[GalClosed_r]; that every
   image is closed ([gal_closed_l_image]/[gal_closed_r_image], again
   [:=] terms); and the characterisations
   [gal_closed_l_iff]/[gal_closed_r_iff] -- an element is closed
   exactly when it is mutually related to an image.  The donor's own
   [gal_unit]/[gal_counit] are CONSUMED, not restated.

   (B) [subset_le_antisym]: two mutually included subsets are [equiv] in
   [Powerset_Prop_obj X].  A [:=] term (the setoid's [equiv] on
   that object is pointwise [Powerset_Prop_truth_equiv], so the
   witness is [fun x => conj (H1 x) (H2 x)]).  It belongs beside
   Instance/Powerset.v's [subsets_iso_of_equiv], which is the
   converse direction read into the category; it is declared here
   because that file is not edited.

   (C) THE OPERATORS AND THE CONNECTION.  [stab X] is Mac Lane's [L X] and
   [fixed S] his [R S]; their memberships read back at [eq_refl]
   ([stab_mem], [fixed_mem]).  [FixesAll X S] is his “sigma . x = x
   for all sigma in S and all x in X”, and it is the SAME TERM as one
   side of the biconditional: [stab_transpose_strict] is
   [subset_le S (stab X) = FixesAll X S] by [eq_refl], while
   [fixed_transpose_iff] is the other side, whose whole content is
   the swap of two quantifiers.  [group_action_galois] supplies all
   six fields by name; [gal_to]/[gal_from] are the two halves of
   [fixed_transpose_iff].

   (D) THE STABILISER IS A SUBGROUP.  [stab_Subgroup X : Subgroup G],
   with [sub_mem] the stabiliser on the nose ([stab_Subgroup_mem],
   [eq_refl]).  [sub_resp] is [stab]'s own respectfulness, [sub_unit]
   is [act_unit], [sub_mul] is [act_op], and [sub_inv] is [act_op]
   with [grp_mul_inv_l] and [act_unit].  Nothing dual is claimed for
   [fixed S], which is a subset of U and not of G.

   (E) IDEMPOTENCE.  [stab_fixed_stab] and [fixed_stab_fixed] at the
   carriers' own [equiv], which is what “idempotent” means in a
   preorder that is not a partial order; each is (B) applied to the
   two halves of (A).  The [eq_refl] form is rejected -- the two
   sides are different terms -- and pinned in the probe.

   (F) CLOSED ELEMENTS.  [ClosedG]/[ClosedU], the two general
   characterisations instantiated ([closed_G_iff],
   [closed_U_iff]: a subset of G is closed exactly when it IS a
   stabiliser, a subset of U exactly when it IS a fixed-point set),
   that every image is closed ([closed_G_stab], [closed_U_fixed]),
   and Mac Lane's “L X is the subgroup of G” read at every closed
   subset: [closed_G_Subgroup], whose [sub_mem] is the given subset
   at [eq_refl].

   (G) THE ADJUNCTION.  [StabFunctor], [FixedFunctor] and
   [group_action_adjunction], all three [:=] applications of the
   donor's [GaloisFunctor_l]/[GaloisFunctor_r]/[GaloisAdjunction] --
   no coherence obligation is discharged here, the target being thin.
   Object actions read back at [eq_refl].  The target category is
   [Proset stab_PreOrder_G]; [galois_PG_obj] and [galois_PG_hom]
   record at [eq_refl] that its objects and its homs are those of
   [(Subsets (grp_setoid G))^op], so it IS the opposite category on
   the two components that carry the data.  The WHOLE categories are
   NOT equal, and the cause is NOT [id] or [compose]: those agree at
   [eq_refl] as well, as does the hom-setoid's [equiv] (the probe
   carries all four agreements as controls).  What differs is the
   [homset] RECORD -- [Proset] is a [Program Definition], so its
   [Equivalence] witness is an opaque obligation applied at [(S, T)]
   on one side and at [(T, S)] on the other -- together with the
   rebuilt law fields.  The whole-record rejection is pinned as a
   conversion negative; an earlier draft blamed [id] and [compose],
   which an audit refuted by measurement.  [op_rel_is_flip] records that
   Instance/Proset/Limit.v's [op_rel] and stdlib's [Basics.flip],
   which Instance/Proset/Order.v uses for the same job, are
   the SAME function by [eq_refl].

   (H) TWO WITNESSES, both over transparent groups whose operations
   compute.  Instance/Grp.v's [Z2] is UNUSABLE here and that is
   measured, not guessed: it is declared
   [Z2@{u} : GrpObject@{u Set Set}], so
   [grp_setoid Z2 : SetoidObject@{Set Set}] with both universes the
   literal [Set], while [Subsets] demands a [SetoidObject@{o o}] with
   [Set < o]; [Subsets (grp_setoid Z2)] is rejected with “Cannot
   enforce Set = ...”.  (An earlier revision quoted
   [GrpObject@{u Set u}] / [SetoidObject@{u Set}] and cited [Z2] at a
   line it has since left;
   re-measured after the PR “algebraic carriers are sets”
   (2026-09-17).)  The witnesses are therefore built on [eq_Setoid]
   (Lib/Setoid.v), which is polymorphic in exactly the needed way.
   (CORRECTION, #450: [Z2] is usable here since #450 wrote out its
   universes in place -- [Z2@{p} : GrpObject@{p p p}] -- and the
   probe's rejection of [Subsets (grp_setoid Z2)] is a control since;
   [GalZ2] is kept.)

   (H1) [GalZ2] on [bool] under [xorb], acting on [bool] by [xorb].
   [galois_stab_true_trivial] computes the stabiliser of the
   singleton {true} to be the trivial subgroup {e}, and
   [galois_fixed_true_empty] the fixed-point set of the
   non-identity element to be empty.  Both non-closure witnesses
   are then proved by [discriminate] after eliminating the
   truncation: {true} as a subset of G is NOT closed (its
   closure is all of G, since everything stabilises the empty
   set), and {true} as a subset of U is NOT closed (its closure
   is all of U).  A closed pair is exhibited alongside, and the
   action is proved to move a point, so the connection is not
   the identity one in disguise.

   (H2) THE STABILISER IS NOT ALWAYS ONE OF THE TWO TRIVIAL
   SUBGROUPS.  [GalV4], the Klein four-group on [bool * bool],
   acts on [bool] through the FIRST coordinate alone -- a
   non-free action, which is what makes a proper non-trivial
   stabiliser possible at all.  [galois_v4_stab_proper] and
   [galois_v4_stab_nontrivial] prove the stabiliser of {true}
   is neither the whole group nor the trivial one -- by
   exhibiting one element it omits and one non-unit element it
   contains -- so [stab_Subgroup] is exercised at a subgroup
   that is genuinely both.  NO CARDINALITY IS CLAIMED: nothing
   in the file counts either group and no order is computed.

   (I) MAC LANE'S OWN TYPING.  Theorem 1 types the pair as
   [L : P -> Q^op] and [R : Q^op -> P], which is exactly the shape of
   Adjunction/Right.v's [AdjointOnTheRight]; [StabOp], [FixedOp]
   and [group_action_AdjointOnTheRight] deliver it, with the two
   object actions at [eq_refl] and with the hom-set isomorphism's two
   legs the two projections of [fixed_transpose_iff].  Its eight
   obligations -- four naturality laws, two isomorphism laws, two
   respectfulness certificates -- are equations between parallel
   arrows in a thin category and cost nothing.  The two
   functors' arrow actions ARE [stab_antitone] and [fixed_antitone]
   with their subset arguments swapped -- which is what
   “order-reversing” becomes once the source is an opposite category.
   Requiring Adjunction/Right.v costs THREE modules of closure -- 129
   with it, 126 without, measured by dropping the [Require] -- which
   is why this is delivered rather than only cited.
   Adjunction/Right.v's own two antitone witnesses are a
   three-element chain and the contravariant power set; the tokens
   “group” and “action” occur in that whole file only in one
   unrelated comment, so a group action is a new inhabitant there as
   well.

   ** WHAT IS NOT DELIVERED

   No fundamental theorem of Galois theory, and nothing about fields:
   Mac Lane's “original instance ... a group of automorphisms of a field
   U” is not instantiated, the tree having no automorphism group of a
   field.  No lattice structure on the closed elements and no proof that
   they form a complete lattice.  No orbit, no orbit-stabiliser theorem,
   no transitivity or freeness vocabulary for actions.  No normality: the
   stabiliser is proved a subgroup, and nothing says when it is normal.
   No functoriality of the connection in G, in the action, or in U, and no
   naturality of any identification.  No comparison with
   Instance/Powerset.v's image/preimage connection, and no comparison
   with Adjunction/Right.v's own two antitone witnesses (the
   three-element chain and the contravariant power set) beyond noting
   that neither is a group action.  No proof that the two adjunction
   packagings of (G) and (I) determine one another, and no equation
   between them: they inhabit different classes and no bridge in either
   direction is built.  No dual reading as an [AdjointOnTheLeft], and
   nothing is claimed about whether one exists.  Nothing is registered as
   an [Instance].

   ** CLOSURE, MEASURED BY DROPPING EACH [Require]

   129 modules, transitive in-project [.vo] dependencies excluding the
   file itself.  Only four [Require]s cost anything at all:
   Instance/Rep.v costs 8 (it is where [grp_mon] lives),
   Adjunction/Right.v 3, Instance/Grp/Quotient.v 3 and
   Instance/Powerset.v 2; every other line in the block costs 0, being
   already inside one of those four.  Without the section (I) bridge the
   figure is 126.

   Instance/Grp/Free.v's [grp_deloop_monoid] is the SAME monoid
   bridge by a cheaper route -- swapping it in for [grp_mon] measures 126
   rather than 129, and unlike [grp_mon] it is a plain [Definition]
   rather than a [Program] one -- but the two produce DIFFERENT
   [MonObject] terms -- [grp_mon H = grp_deloop_monoid H] is rejected at
   [eq_refl] (measured out of tree, with “cannot unify”) -- so a
   consumer's [MSetoidAction] is over one or the other and not both.
   [grp_mon] is kept, being the bridge the tree's own index names, and
   the three-module difference is recorded rather than taken.

   ** UNIVERSES

   Section (C) onwards runs over [G : GrpObject@{gu o o}] and
   [A : MSetoidAction@{o o gu gu gu o o gu} (grp_mon@{gu o o} G)] under
   [Constraint Set < o] and [Constraint o <= gu].  The identification of
   the group's carrier and relation universes -- and of the action
   setoid's -- is the DONORS' and not this file's, and it has FOUR donors
   each sufficient alone: [Powerset_Prop_obj] is declared over a
   [SetoidObject@{o o}] (Instance/Sets/Powerset.v) and is the one
   this file meets first, in section (C); [subset_le],
   [subset_le_preorder] and [Subsets] (Instance/Powerset.v) each
   demand the same, measured out of tree at levels declared apart.  So
   both [grp_setoid G] and [act_setoid A] must have their two universes
   equal before any subset can be named, and [Set < o] is
   [Powerset_Prop_obj]'s own (Prop sits at [Type@{Set+1}]).
   [Constraint o <= gu] is [GrpObject]'s own [u <= u1, u0 <= u1].  The
   identification is pinned as the probe's two level negatives at the
   LAST of the four donors, [Subsets], with [grp_setoid G], its carrier
   and [grp_mon G] accepted at levels declared apart as the controls, so
   the rejection is not from naming the group's setoid; an earlier draft
   attributed it to [Subsets] alone.

   Section (A) is universe-free of all that: it mentions no setoid and no
   power set, and its two type parameters stay at SEPARATE levels.

   Measured over all 77 declared heads: NOT ONE carries a universe
   EQUATION, and not one carries [Set] in a universe INSTANCE.  Fifty-nine
   carry [Set] in a constraint block and in every case it is the strict LOWER
   bound [Set < _], which is [Powerset_Prop_obj]'s own ([Prop] sits at
   [Type@{Set+1}]) plus one from [Basics.flip] in [op_rel_is_flip]; a
   lower bound on a level constrains nothing above it.  The remaining
   eighteen carry no [Set] at all: the whole of section (A), plus
   [galois_two], [galois_four], [galois_v4_mul], [galois_z2_act_moves]
   and the two witness groups with their two actions (whose blocks are
   the single bound [wo <= Logic_lemmas.equality.u0]).

   Each half of Mac Lane's display (2) needs only ONE of the two
   preorders, which the discharged signatures record:
   [gal_lrl_below]/[gal_rlr_below] take [PA] and
   [gal_lrl_above]/[gal_rlr_above] take [PB], because each is one
   monotonicity step away from a unit or a counit and only the
   reflexivity of the OTHER relation is spent.  Only the two
   [gal_closed_*_iff] take both.

   ** TRANSPARENCY

   Nine [Defined] tokens, and ALL NINE ARE LOAD-BEARING -- measured by
   flipping each one to [Qed] on its own and recording what stops:
   [stab] stops [stab_mem], [fixed] stops [fixed_mem], [stab_Subgroup]
   stops [stab_Subgroup_mem], [closed_G_Subgroup] stops
   [closed_G_Subgroup_mem], [GalZ2] stops [GalZ2Act], [GalZ2Act] stops
   [galois_z2_act_moves], [galois_sub] stops [galois_z2_stab_forces],
   [GalV4] stops [GalV4Act], and [GalV4Act] stops
   [galois_v4_stab_forces].  Everything else is a [:=] term or a [Qed]
   producing no data.  All 91 constants are closed under the global
   context, with no axiom of any kind -- the 77 declared heads (54 [def]
   and 23 [prf] in the glob) plus the 14 [Program] obligations of section
   (I)'s three [Program Definition]s, which no glob or source sweep sees
   and which [Print Module] lists: three each for [StabOp] and [FixedOp]
   and eight for [group_action_AdjointOnTheRight].  A first draft of this
   paragraph said 77 and that the obligations did not exist; the count
   was corrected by [Print Module] before landing.

   ** REGISTRATION

   Nothing is an [Instance] and no hint is added.  A chosen stabiliser
   must not become globally resolvable, matching Instance/Powerset.v's
   own note on its meets and joins. 

   --------
   * Mac Lane，《为在职数学家准备的范畴》，第2版，第IV.5节，构造1（印刷第96页）。从页面图像转录，使用ASCII：满足 (1) 的一对保持顺序的函数 L 和 R 称为从 P 到 Q 的 Galois 连接。这里是一个基本例子，对于一个群 G 在集合 U 上的作用，由 <σ, x> |-> σ . x 定义，其中 σ ∈ G，x ∈ U。取 P = P(U)，即所有子集 X ⊆ U 的集合，按包含关系排序，而 Q = P(G) 是 G 的子集 S ⊆ G 的集合，也按包含关系排序（S ≤ S' 当且仅当 S ⊆ S'）。定义 L(X) = {σ | 对任意 x ∈ X，有 σ . x = x}，R(S) = {x | 对任意 σ ∈ S，有 σ . x = x}；换句话说，L(X) 是固定 X 中所有点的 G 的子群，R(S) 是 S 的自同构的固定点集合。则 L(X) ≥ S 在 Q 中当且仅当对所有 σ ∈ S 和所有 x ∈ X 有 σ . x = x，而这又当且仅当 X ≤ R(S) 在 P 中成立。因此，L 和 R 构成一对伴随（伽罗瓦连接）。原始实例是 G 为域 U 的自同构群，如经典伽罗瓦理论中所示。

   并且，根据印刷版第 95 页，该段落所依据的定理及其两个公式如下：

   “定理 1（伽罗瓦连接是伴随对）。设 P、Q 为两个前序集，L : P -> Q^op，R : Q^op -> P 为两个保持顺序的函数。则当 L（视为函子）是 R 的左伴随时，当且仅当对所有 p 属于 P、q 属于 Q 有：

   L p >= q 在 Q 中  当且仅当  p <= R q 在 P 中 .       (1)

   当这种情况成立时，存在唯一的伴随变换 phi 使得 L 成为 R 的左伴随。对于所有 p 和 q，有 p <= R L p 并且 L R q >= q；因此也L p >= L R L p >= L p ，    R q <= R L R q <= R q 。        (2)

   nLab:  https://ncatlab.org/nlab/show/Galois+connection 
   nLab:  https://ncatlab.org/nlab/show/group+action 
   nLab:  https://ncatlab.org/nlab/show/closure+operator 
   nLab:  https://ncatlab.org/nlab/show/stabilizer+group 
   nLab:  https://ncatlab.org/nlab/show/fixed+point 
   Wikipedia:  https://en.wikipedia.org/wiki/Galois_connection 
   Wikipedia:
   https://en.wikipedia.org/wiki/Fundamental_theorem_of_Galois_theory

   ** 连接是反音的，这就是 Mac Lane 自己的 Q^op显示 (1) 读作“L p >= q in Q”，而不是“L p <= q”：定理 1 将 L 类型化为一个函子 P -> Q^op，构造段落说“L X >= S in Q”。因此，这里的对在每个变量中都是顺序反转的，这正是子群和子域之间经典 Galois 对应的特性。Instance/Proset/Galois.v 中的 [GaloisConnection RA RB] 是协变声明的——其 [gal_mono_l] 从 [RA a a'] 推出 [RB (gal_l a) (gal_l a')] ——所以通过将 [RB] 视为 P(G) 上的逆向包含，就可以得到逆序解读，这就是 Instance/Proset/Limit.v 中的 [op_rel]。这是对书中 [Q^op] 的真实呈现，而不是偏离；协变指定被拒绝，这种拒绝在 Test/ProbeGalois381.v 中被固定为类型负例。** 该问题的“当前状态”在四个方面都是过时的，在基础提交中测量得到

   目录条目写道：“缺失。Structure/Group.v 仅声明了 [GroupObject] ... 没有操作，没有子群格”，并要求构建群、操作、子群概念以及幂集预序。四者均已存在。

   (1) Instance/Grp.v 的 [GrpObject] 是集合等价类级别的群（承载体、单位元、乘法、逆元，以及右手定律和逆元的相容性已推导），以及 [GrpHom] 和范畴 [Grp]。(2) 一个单子在集合上作用是 Construction/Deloop/Functors.v 中的 [Record MSetoidAction (M : MonObject)] -- 字段 [act_setoid], [act], [act_respects], [act_unit], [act_op]，在 Riehl 1.3.9 的左约定中 [act (g . h) x = act g (act h x)] -- 在 Instance/Fun/Action.v 和那里的类别 [MSet M] 有等变映射。它在下面被使用；没有声明第二个作用记录。

   (3) Instance/Grp/Quotient.v 的 [Record Subgroup (G : GrpObject)] -- 字段 [sub_mem : carrier G -> Type], [sub_resp], [sub_unit], [sub_mul], [sub_inv] -- 是子群的概念。它是 [stab_Subgroup] 在下面所占据的。(4) 幂集预序是 Instance/Powerset.v 的 [subset_le] / [subset_le_preorder] / [Subsets X := Proset (subset_le_preorder X)]，基于 Instance/Sets/Powerset.v 的 [Powerset_Prop_obj X] -- 对集合等价类遵循 [equiv] 的命题值谓词，也就是 [SetoidMorphism X Powerset_Prop_truth]。对周围的散文再做两处修改。问题建议的模块 [Instance/Group/Galois.v] 指向一个不存在的目录；树的组目录是 [Instance/Grp/]，因此文件被放在那里。并且从一个群到其单幺半群的桥 [MSetoidAction] 作用于 Instance/Rep.v 的 [grp_mon]，在这里被使用。（ [Construction/Deloop.v] 声明了一个同样名为 [GrpObject] 的第二个记录，叠加在 [MonObject] 上；它不是 Instance/Grp/Quotient.v 的 [Subgroup] 所覆盖的那个，因此文件导入 Instance.Grp LAST，下面的每个 [GrpObject] 都是 Instance/Grp.v 的。）

   ** 现有技术：已有的三个 Galois 连接，以及新的内容在基础提交中，正好有三个库常量存在于 NAMED 关系中（Instance/Proset/Galois.v 的 [GaloisOfAdjunction] 及其 [galois_of_unit_counit] 是针对任意 [RA] / [RB] 的参数化构造，所以 grep 会找到五个）：
   Instance/Proset/Galois.v 的 [nat_shift_galois]（在自然数上截断减法是加法的左伴随），
   Instance/Powerset.v 的 [image_preimage_galois]（逆像的左伴随为直接像）以及 Instance/FinSet/Subsets.v 的 [finpow_image_preimage_galois]（在可判定有限子集上相同）。第四个出现是在 Test/ProbePowerset382.v，是一个探测控制。所有三个库中的都是协变的：每一个对于给定的包含关系都具有单调映射。[group_action_galois] 下面因此是树的第一个反音 —— 第一个其第二关系是包含的 [op_rel] —— 这就是经典伽罗瓦对应的形状。

   在任何地方都不存在闭包算子词汇：对复合 [gal_l (gal_r (gal_l _))] 或 [gal_r (gal_l (gal_r _))] 的搜索，以及对标记 [ClosureOperator] 和 [closure_op] 的搜索，在此文件之外均无结果。章节（A）提供了 Mac Lane 对任意 [GaloisConnection] 的展示（2）；这里陈述它是因为 Instance/Proset/Galois.v 没有被此更改编辑，并且当出现第二个使用者时，它可能会被移动到那里。

   ** 与书本唯一的偏离，以及它被迫的原因Mac Lane 的成员条件是在一个集合中的方程 [sigma . x = x]。这里的环境等式是集合化的 [equiv]，在这个库中是 [crelation] 值的，因此是 [Type] 值的——而 [Powerset_Prop_obj X] 的成员必须是 [Prop] 值的，因为 [subset_le] 必须是 stdlib 的 [relation]，以使 [Proset] 和 [GaloisConnection] 完全适用（Instance/Powerset.v 记录了该约束）。因此，固定条件被 Instance/Sets/Powerset.v 的不可归纳 [Powerset_squash A := forall Q : Prop, (A -> Q) -> Q] 截断，正如 [Powerset_Prop_image] 截断其存在量一样。在重要的地方没有任何丢失：每个必须在下面消除截断的目标本身都是一个 [Prop]，并且 Instance/Sets/Powerset/Universal.v 的 [powerset_squash_prop_inert] 记录了在一个 [Prop] 上截断是惰性的 —— 这在两个见证处都是如此，它们的集合标准是 [eq_Setoid]。

   ** 已交付内容及等级(A) 一般地，对于任意的 [GaloisConnection RA RB]，具有两个预序：[gal_lrl_below] / [gal_lrl_above] 和 [gal_rlr_below] / [gal_rlr_above]，它们是 Mac Lane 的展示 (2) --- [L p >= L R L p >= L p] 和 [R q <= R L R q <= R q] --- 每个都是一个 [:=] 项，在捐赠者的 [gal_unit] 和 [gal_counit] 上没有策略：[gal_lrl_below] 是在 [gal_l a] 上评估的余单位，[gal_rlr_above] 是在 [gal_r b] 上评估的单位，没有进一步步骤，而 [gal_lrl_above] 和 [gal_rlr_below] 是通过一个单调性域推送的其他两个；闭合性谓词 [GalClosed_l] / [GalClosed_r]；每个像都是闭合的 ([gal_closed_l_image] / [gal_closed_r_image]，再次是 [:=] 项)；以及表征 [gal_closed_l_iff] / [gal_closed_r_iff] --- 一个元素正好在它与某个像相互关联时闭合。捐赠者自己的 [gal_unit] / [gal_counit] 被消耗，而不是重新声明。

   (B) [subset_le_antisym]：两个相互包含的子集是 [equiv] 在 [Powerset_Prop_obj X] 中。一个 [:=] 项（该对象上的集合体的 [equiv] 是逐点 [Powerset_Prop_truth_equiv]，因此见证是 [fun x => conj (H1 x) (H2 x)]）。它属于 Instance/Powerset.v 的 [subsets_iso_of_equiv] 旁边，这是读入范畴的相反方向；它在这里声明是因为该文件没有被编辑。(C) 操作符和连接。[stab X] 是 Mac Lane 的 [L X]，而 [fixed S] 是他的 [R S]；它们的成员在 [eq_refl] 处被回读（[stab_mem], [fixed_mem]）。[FixesAll X S] 是他的“sigma . x = x 对所有 sigma 在 S 中且所有 x 在 X 中”，并且它与双条件的一边是同一个术语：[stab_transpose_strict] 是 [subset_le S (stab X) = FixesAll X S] 由 [eq_refl] ，而 [fixed_transpose_iff] 是另一边，其整个内容是两个量词的互换。[group_action_galois] 按名称提供所有六个字段；[gal_to] / [gal_from] 是 [fixed_transpose_iff] 的两半。(D) 稳定子是一个子群。[stab_Subgroup X : Subgroup G]，带有 [sub_mem] 在鼻子的稳定子（[stab_Subgroup_mem]，[eq_refl]）。[sub_resp] 是 [stab] 自身的尊重，[sub_unit] 是 [act_unit]，[sub_mul] 是 [act_op]，[sub_inv] 是 [act_op]，带有 [grp_mul_inv_l] 和 [act_unit]。没有为 [fixed S] 声称任何对偶性，它是 U 的一个子集，而不是 G 的子集。

   (E) 幂等性。[stab_fixed_stab] 和 [fixed_stab_fixed] 位于载体自身的 [equiv]，这就是在非偏序的预序中“幂等”的意义；每个都是 (B) 应用于 (A) 的两个部分。[eq_refl] 形式被拒绝——两边是不同的项——并固定在探针中。(F) 闭合元素。[ClosedG] / [ClosedU]，这两个一般特征实例化（[closed_G_iff], [closed_U_iff]：一个子集 G 是闭合的当且仅当它是一个稳定子集，一个子集 U 是闭合的当且仅当它是一个不动点集），每个像都是闭合的（[closed_G_stab], [closed_U_fixed]），以及 Mac Lane 的“L X 是 G 的子群”在每个闭合子集上阅读：[closed_G_Subgroup]，其 [sub_mem] 是在 [eq_refl] 给定的子集。(G) 联接。[StabFunctor]、[FixedFunctor] 和 [group_action_adjunction]，三者都是 [:=] 对捐赠者的 [GaloisFunctor_l] / [GaloisFunctor_r] / [GaloisAdjunction] 的应用——这里没有履行一致性义务，目标是薄弱的。对象操作在 [eq_refl] 回读。目标类别是 [Proset stab_PreOrder_G]；[galois_PG_obj] 和 [galois_PG_hom] 在 [eq_refl] 记录其对象和同态属于 [(Subsets (grp_setoid G))^op]，因此它确实是在携带数据的两个组成部分上的对立类别。整个类别不相等，原因不是 [id] 或 [compose]：它们在 [eq_refl] 处也一致，同态集的 [equiv] 也是如此（探针携带所有四个一致性作为控制）。不同的是 [homset] 记录 -- [Proset] 是一个 [Program Definition]，因此它的 [Equivalence] 见证是一个在一侧的 [(S, T)] 和另一侧的 [(T, S)] 施加的不透明义务 -- 以及重建的法律字段。整个记录的拒绝被固定为转换负值；早期的草稿指责 [id] 和 [compose]，但审计通过测量驳斥了这一点。[op_rel_is_flip] 记录了 Instance/Proset/Limit.v 的 [op_rel] 和 stdlib 的 [Basics.flip]，Instance/Proset/Order.v 用于相同任务，它们通过 [eq_refl] 是相同的功能。(H) 两个见证者，都在可计算操作的透明群上。实例/Grp.v 的 [Z2] 在这里不可用，这是经过测量的，而非猜测：它被声明为 [Z2@{u} : GrpObject@{u Set Set}]，因此 [grp_setoid Z2 : SetoidObject@{Set Set}] 与两个宇宙都是字面量 [Set]，而 [Subsets] 要求一个带有 [Set < o] 的 [SetoidObject@{o o}]；[Subsets (grp_setoid Z2)] 被拒绝，提示“无法强制执行 Set = ...”。（早期版本引用了 [GrpObject@{u Set u}] / [SetoidObject@{u Set}] 并在其已离开的行上引用了 [Z2]；在 PR “代数载体是集合”之后重新测量（2026-09-17）。）因此，这些见证者构建于 [eq_Setoid]（Lib/Setoid.v），其多态性正好满足所需方式。(更正，#450：[Z2] 在这里是可用的，因为 #450 已经在原位写出了它的宇宙 —— [Z2@{p} : GrpObject@{p p p}] —— 并且探针拒绝 [Subsets (grp_setoid Z2)] 是一个控制，因为 [GalZ2] 被保留。)(H1) [GalZ2] 在 [bool] 上根据 [xorb] 行动，通过 [xorb] 作用于 [bool]。 
   [galois_stab_true_trivial] 计算单元素集 {true} 的稳定子为平凡子群 {e}，并且 [galois_fixed_true_empty] 计算非单位元素的固定点集为空。随后，经过消去截断后，[discriminate] 证明了两个非闭合证据：作为 G 的子集的 {true} 不是闭合的（其闭包是整个 G，因为所有元素都稳定空集），作为 U 的子集的 {true} 也不是闭合的（其闭包是整个 U）。同时展示了一个闭合对，并且证明了该作用会移动一个点，因此该连接并非伪装的单位元素。(H2) 稳定子并不总是两个平凡子群之一。[GalV4]，ZWW206WZZ上的克莱因四元群，仅通过第一个坐标作用于[bool]——一种非自由作用，这正是使得可能存在适当的非平凡稳定子的原因。[galois_v4_stab_proper]和[galois_v4_stab_nontrivial]证明了{true}的稳定子既不是整个群，也不是平凡群——通过展示它遗漏的一个元素和它包含的一个非单位元素——因此[stab_Subgroup]在一个真正都是的子群上被测试。未声明任何基数：文件中没有计算任何群，也没有计算阶。(我) MAC LANE 自己的打字。定理 1 将该对类型化为 [L : P -> Q^op] 和 [R : Q^op -> P]，这恰好是 Adjunction/Right.v 的 [AdjointOnTheRight] ；[StabOp]、[FixedOp] 和 [group_action_AdjointOnTheRight] 所呈现的形状，在 [eq_refl] 处具有两个对象作用，并且在同态集同构的两个分支上是 [fixed_transpose_iff] 的两个投影。它的八个义务——四条自然性定律、两条同构定律、两张恪守性证明——是薄范畴中平行箭头之间的方程，花费为零。两个函子箭头的作用正是 [stab_antitone] 和 [fixed_antitone]，并且它们的子集参数被交换——这就是当源是对偶范畴时，“逆序”所表现的含义。要求 Adjunction/Right.v 需要三个闭包模块 —— 使用时为 129，不使用时为 126，通过去掉 [Require] 测量 —— 这就是为什么这是交付的而不仅仅是引用的原因。Adjunction/Right.v 自身的两个逆序证据是一个三元素链和逆变幂集；在整个文件中，“group”和“action”这两个词只出现在一个无关的注释中，因此群作用在这里也是一个新的居民。

   ** 未交付的内容是什么没有伽罗瓦理论的基本定理，也没有关于域的内容：
   麦克·莱恩的“原始实例……一个域 U 的自同构群”没有被实例化，这棵树没有域的自同构群。闭合元素没有格结构，也没有证明它们形成完整格。没有轨道，没有轨道-稳定子定理，也没有作用的传递性或自由性词汇。没有正规性：稳定子被证明是子群，但没有说明它何时是正规子群。在 G、作用或 U 中的连接没有函子性，也没有任何同一性的自然性。没有与 Instance/Powerset.v 的像/原像连接进行比较，也没有与 Adjunction/Right.v 自身的两个反单调见证（三元链和逆变幂集）进行比较，除了注意到两者都不是群作用。没有证明 (G) 和 (I) 的两个伴随打包彼此决定，也没有它们之间的方程：它们属于不同的类，并且没有建立任何方向的桥梁。没有作为 [AdjointOnTheLeft] 的对偶读取，也未声明其是否存在。没有记录作为 [Instance]。

   ** 闭包，通过放弃每个 [Require] 来衡量129 个模块，在项目内的传递性 [.vo] 依赖中，不包括文件自身。只有四个 [Require] 需要消耗资源：Instance/Rep.v 消耗 8（这是 [grp_mon] 所在的位置），Adjunction/Right.v 消耗 3，Instance/Grp/Quotient.v 消耗 3，以及 Instance/Powerset.v 消耗 2；块中的其他每一行都消耗 0，因为它们已经包含在这四个模块之一内。如果没有 (I) 桥梁，这个数字是 126。Instance/Grp/Free.v 的 [grp_deloop_monoid] 是通过更便宜的路径连接的相同幺半群——将其替换 [grp_mon] 时测得为 126 而不是 129，并且与 [grp_mon] 不同，它是一个普通的 [Definition] 而不是 [Program] ——但两者产生不同的 [MonObject] 项—— [grp_mon H = grp_deloop_monoid H] 在 [eq_refl] 处被拒绝（在树外测量，显示“无法统一”）——因此消费者的 [MSetoidAction] 在其中之一上而不是两者上。 [grp_mon] 被保留，作为树自身索引名称的桥梁，并且记录了三个模块的差异而不是采取。  

   ** 宇宙从 (C) 节开始，覆盖了 [G : GrpObject@{gu o o}] 和 [A : MSetoidAction@{o o gu gu gu o o gu} (grp_mon@{gu o o} G)]，位于 [Constraint Set < o] 和 [Constraint o <= gu] 下。该组的载体和关系宇宙的识别——以及作用集合的识别——属于捐赠者，而不是本文件，并且它有四个捐赠者，每个捐赠者单独就足够：[Powerset_Prop_obj] 在 [SetoidObject@{o o}]（Instance/Sets/Powerset.v）上声明，是本文件在 (C) 节中首先遇到的；[subset_le]、[subset_le_preorder] 和 [Subsets]（Instance/Powerset.v）每个都要求相同，从树中在分别声明的层次测量。因此，在可以命名任何子集之前，[grp_setoid G] 和 [act_setoid A] 必须让它们的两个宇宙相等，而 [Set < o] 是 [Powerset_Prop_obj] 自己的（Prop 位于 [Type@{Set+1}]）。[Constraint o <= gu] 是 [GrpObject] 自己的 [u <= u1, u0 <= u1]。该识别被固定为探针在四个供体中的最后一个 [Subsets] 的两个级别的负值，与其载体 [grp_setoid G] 和 [grp_mon G] 在单独声明的级别上被接受作为对照，因此拒绝并非来自为该组命名的集合；早期草稿将其归因于仅 [Subsets]。

   第（A）部分完全不涉及这些内容：它没有提及任何集合，也没有提及幂集，并且其两个类型参数保持在独立级别。在所有77个已声明的头中测量：没有一个包含宇宙方程，也没有一个在宇宙实例中包含[Set]。五十九个在约束块中包含[Set]，并且在每种情况下它都是严格的下限[Set < _]，即[Powerset_Prop_obj]自身的（[Prop]位于[Type@{Set+1}]）加上[Basics.flip]在[op_rel_is_flip]中的一个；一个层次的下限不会约束其上方的任何东西。其余18个完全不包含[Set]：整节(A)，加上[galois_two]、[galois_four]、[galois_v4_mul]、[galois_z2_act_moves]以及两个见证组及其两个动作（其块是单个下限[wo <= Logic_lemmas.equality.u0]）。Mac Lane 显示的每一半 (2) 只需要其中一个前序关系，已释放的符号记录如下：
   [gal_lrl_below] / [gal_rlr_below] 取 [PA]，
   [gal_lrl_above] / [gal_rlr_above] 取 [PB]，因为每一个只离一个单位或余单位一步单调性，而只消耗了另一个关系的自反性。只有两个 [gal_closed_*_iff] 取两个。

   ** 透明性九个 [Defined] 代币，且所有九个都是承重的 —— 通过将每个单独翻转为 [Qed] 并记录停止点来测量：[stab] 停止在 [stab_mem]，[fixed] 停止在 [fixed_mem]，[stab_Subgroup] 停止在 [stab_Subgroup_mem]，[closed_G_Subgroup] 停止在 [closed_G_Subgroup_mem]，[GalZ2] 停止在 [GalZ2Act]，[GalZ2Act] 停止在 [galois_z2_act_moves]，[galois_sub] 停止在 [galois_z2_stab_forces]，[GalV4] 停止在 [GalV4Act]，[GalV4Act] 停止在 [galois_v4_stab_forces]。其他所有内容都是 [:=] 术语或 [Qed]，不产生数据。所有 91 个常数在全局上下文下都是封闭的，没有任何公理——在全局中声明的 77 个头（54 个 [def] 和 23 个 [prf]）加上第 (I) 节的三个 [Program Definition] 的 14 个 [Program] 义务，这些义务没有被任何全局或源扫描看到，而 [Print Module] 列出了这些义务：[StabOp] 和 [FixedOp] 各三个，[group_action_AdjointOnTheRight] 八个。该段落的初稿写了 77 并且那时认为这些义务不存在；在落地之前，这一计数由 [Print Module] 修正。

   ** 注册

   没有任何东西是 [Instance]，并且没有添加任何提示。选定的稳定子不得变为全局可解，符合 Instance/Powerset.v 关于其交和并的说明。
*)

(* ------------------------------------------------------------------------ *)
(* * ** (A) Closure operators, over an arbitrary Galois connection / * **（A）闭包算子，在任意加洛瓦联系上 *)

(* Mac Lane's display (2) of Theorem 1, and the closedness vocabulary it supports. Nothing here mentions a group, an action or a power set. / Mac Lane 对定理 1 的展示 (2)，以及它所支持的闭合集词汇。这里没有提到群、作用或幂集。 *)

Section GaloisClosure.

Context {A B : Type}.
Context {RA : relation A} {RB : relation B}.
Context (PA : PreOrder RA) (PB : PreOrder RB).
Context (Gc : GaloisConnection RA RB).

(*
 [L p >= L R L p >= L p]: read at [RB], the composite [gal_l ∘ gal_r] on
 the image of [gal_l] returns it, in both directions.  Both are supplied
 by [:=] with no tactic; the first IS the donor's counit at [gal_l a],
 the second its unit pushed through [gal_mono_l]. 

 --------
 [L p >= L R L p >= L p]：在 [RB] 读取，复合的 [gal_l ∘ gal_r] 在 [gal_l] 的图像上返回它，在两个方向上。两者都由 [:=] 提供，没有策略；第一个是在 [gal_l a] 的捐赠者余单位，第二个是其单位通过 [gal_mono_l] 推送。
*)
Definition gal_lrl_below (a : A) :
  RB (gal_l Gc (gal_r Gc (gal_l Gc a))) (gal_l Gc a) :=
  gal_counit Gc PA (gal_l Gc a).

Definition gal_lrl_above (a : A) :
  RB (gal_l Gc a) (gal_l Gc (gal_r Gc (gal_l Gc a))) :=
  gal_mono_l Gc (gal_unit Gc PB a).

(* [R q <= R L R q <= R q], the mirror. / [R q <= R L R q <= R q]，镜子。 *)
Definition gal_rlr_below (b : B) :
  RA (gal_r Gc (gal_l Gc (gal_r Gc b))) (gal_r Gc b) :=
  gal_mono_r Gc (gal_counit Gc PA b).

Definition gal_rlr_above (b : B) :
  RA (gal_r Gc b) (gal_r Gc (gal_l Gc (gal_r Gc b))) :=
  gal_unit Gc PB (gal_r Gc b).

(* Closedness. One direction of each is free -- [gal_counit] on the [B] side, [gal_unit] on the [A] side -- so the predicate records only the direction that is not. / 封闭性。 每个的一个方向是开放的——在 [B] 侧是 [gal_counit]， 在 [A] 侧是 [gal_unit]——因此谓词只记录不是开放的方向。 *)
Definition GalClosed_l (b : B) : Prop := RB b (gal_l Gc (gal_r Gc b)).
Definition GalClosed_r (a : A) : Prop := RA (gal_r Gc (gal_l Gc a)) a.

Definition gal_closed_l_image (a : A) : GalClosed_l (gal_l Gc a) :=
  gal_lrl_above a.

Definition gal_closed_r_image (b : B) : GalClosed_r (gal_r Gc b) :=
  gal_rlr_below b.

(*
 The characterisation: the closed elements are exactly the images.
 Without antisymmetry the sharpest available reading of “is an image” is
 mutual relatedness, which is what a preorder supplies. 

 --------
 表征：闭合元素恰好是像。没有反对称性时，“是一个像”的最精确可用理解是相互关联，这正是预序提供的。
*)
Lemma gal_closed_l_iff (b : B) :
  GalClosed_l b ↔ ∃ a, RB b (gal_l Gc a) ∧ RB (gal_l Gc a) b.
Proof using A B Gc PA PB RA RB.
  split.
  - intro H; exists (gal_r Gc b); exact (H, gal_counit Gc PA b).
  - intros [a [Hba Hab]].
    exact (@transitivity B RB (@PreOrder_Transitive B RB PB) _ _ _ Hba
             (@transitivity B RB (@PreOrder_Transitive B RB PB) _ _ _
                (gal_lrl_above a)
                (gal_mono_l Gc (gal_mono_r Gc Hab)))).
Qed.

Lemma gal_closed_r_iff (a : A) :
  GalClosed_r a ↔ ∃ b, RA a (gal_r Gc b) ∧ RA (gal_r Gc b) a.
Proof using A B Gc PA PB RA RB.
  split.
  - intro H; exists (gal_l Gc a); exact (gal_unit Gc PB a, H).
  - intros [b [Hab Hba]].
    exact (@transitivity A RA (@PreOrder_Transitive A RA PA) _ _ _
             (@transitivity A RA (@PreOrder_Transitive A RA PA) _ _ _
                (gal_mono_r Gc (gal_mono_l Gc Hab))
                (gal_rlr_below b))
             Hba).
Qed.

End GaloisClosure.

(* ------------------------------------------------------------------------ *)
(* * ** (B) Mutual inclusion is [equiv] of subsets / * ** (B) 相互包含是子集的 [equiv] *)

(*
 [equiv] on [Powerset_Prop_obj X] is [SetoidMorphism_Setoid]'s, that is
 pointwise [Powerset_Prop_truth_equiv], which is the conjunction of two
 implications -- so the witness is the pair of the two inclusions.  This
 is an equation between OBJECTS of the power set (elements of a setoid),
 not between morphisms of a category. 

 --------
 [equiv] 在 [Powerset_Prop_obj X] 上是 [SetoidMorphism_Setoid] 的，也就是说逐点 [Powerset_Prop_truth_equiv]，这是两个蕴涵的合取——所以证据是这两个包含的对。这是幂集（集合化的元素）对象之间的方程，而不是范畴态射之间的方程。
*)
Definition subset_le_antisym@{o} {X : SetoidObject@{o o}}
  {S T : carrier (Powerset_Prop_obj@{o} X)}
  (H1 : subset_le@{o} S T) (H2 : subset_le@{o} T S) : S ≈ T :=
  fun x => conj (H1 x) (H2 x).

(*
 Instance/Proset/Limit.v's reversed preorder and stdlib's [Basics.flip],
 which Instance/Proset/Order.v uses for the same job, are the
 same function: both delta-reduce to [fun x y => R y x]. 

 --------
 Instance/Proset/Limit.v 的反向前序以及 stdlib 的 [Basics.flip]，与 Instance/Proset/Order.v 用于相同工作的函数是相同的：两者通过 delta 简化都得到 [fun x y => R y x]。
*)
Example op_rel_is_flip {A : Type} (R : relation A) :
  op_rel R = Basics.flip R := eq_refl.

(* ------------------------------------------------------------------------ *)
(* * ** (C) The action, the two operators, and the connection / * **（C）动作、两个运算符和连接 *)

Section Action.

(*
 [o] is the one universe at which both the group's setoid and the
 action's live; [Subsets] demands [SetoidObject@{o o}], which is what
 forces the two to coincide, and [Set < o] is [Powerset_Prop_obj]'s.
 [su] is the hom universe of the two thin categories, free of [o].
 [gu] is [GrpObject]'s own AUXILIARY level (the record's own sort).

 An earlier revision of this comment called [gu] “[GrpObject]'s own third
 level” and wrote [GrpObject@{o o gu}].  Since the PR “algebraic carriers
 are sets” (2026-09-17) added [grp_prop], the record's three universe roles
 have permuted from (carrier, proof, aux) to (aux, carrier, proof), so the
 SAME reading is now spelled [GrpObject@{gu o o}]: [gu] keeps its role, only
 its position moved. 

 --------
 [o] 是唯一的宇宙，其中群的集合化结构和值的作用同时存在；[Subsets] 需要 [SetoidObject@{o o}]，这正是迫使两者一致的原因，而 [Set < o] 属于 [Powerset_Prop_obj]。[su] 是这两个单薄范畴的同态宇宙，不包含 [o]。[gu] 是 [GrpObject] 自身的辅助层级（记录自身的种类）。

 本评论的早期版本称 [gu] 为“[GrpObject] 自身的第三级”并写下了 [GrpObject@{o o gu}]。自从 PR “代数承载体是集合”（2026-09-17）增加了 [grp_prop] 后，记录的三个宇宙角色已从（承载体、证明、辅助）排列为（辅助、承载体、证明），因此相同的解释现在拼写为 [GrpObject@{gu o o}]：[gu] 保持其角色，仅位置发生了变化。
*)
Universe o su gu.
Constraint Set < o.
Constraint o <= gu.

Context (G : GrpObject@{gu o o}).
Context (A : MSetoidAction@{o o gu gu gu o o gu} (grp_mon@{gu o o} G)).

(*
 Mac Lane's [sigma . x = x], truncated: [equiv] is [Type]-valued here,
 and a member of a [Powerset_Prop_obj] must be a [Prop].  Every use below
 eliminates the truncation into a [Prop] goal, and over a [Prop] the
 truncation is inert (Instance/Sets/Powerset/Universal.v). 

 --------
 Mac Lane 的 [sigma . x = x]，截断后：[equiv] 在这里是 [Type] 值，并且 [Powerset_Prop_obj] 的成员必须是 [Prop]。下面的每个用法都将截断消除为 [Prop] 目标，并且在 [Prop] 上截断是惰性的（Instance/Sets/Powerset/Universal.v）。
*)
Definition fixes (s : carrier (grp_setoid G))
                 (x : carrier (act_setoid A)) : Prop :=
  Powerset_squash@{o} (act A s x ≈ x).

(*
 [L X], the set of group elements fixing every point of [X].
 Respectfulness in [s] is [act_respects]. 

 --------
 [L X]，固定 [X] 中每一点的群元素集合。
 [s] 中的尊重是 [act_respects]。
*)
Definition stab (X : carrier (Powerset_Prop_obj@{o} (act_setoid A))) :
  carrier (Powerset_Prop_obj@{o} (grp_setoid G)).
Proof using A G.
  unshelve refine (@Build_SetoidMorphism@{o o o}
    (carrier (grp_setoid G)) (is_setoid (grp_setoid G))
    Prop (is_setoid Powerset_Prop_truth@{o})
    (fun s => ∀ x, X x → fixes s x) _).
  intros s s' Hss'; split; intros H x Hx; specialize (H x Hx);
    refine (H _ _); intro Hfix; apply Powerset_squash_intro@{o}.
  - rewrite <- Hss'; exact Hfix.
  - rewrite Hss'; exact Hfix.
Defined.

(* [R S], the set of points fixed by every element of [S]. / [R S]，由 [S] 的每个元素固定的点的集合。 *)
Definition fixed (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) :
  carrier (Powerset_Prop_obj@{o} (act_setoid A)).
Proof using A G.
  unshelve refine (@Build_SetoidMorphism@{o o o}
    (carrier (act_setoid A)) (is_setoid (act_setoid A))
    Prop (is_setoid Powerset_Prop_truth@{o})
    (fun x => ∀ s, S s → fixes s x) _).
  intros x y Hxy; split; intros H s Hs; specialize (H s Hs);
    refine (H _ _); intro Hfix; apply Powerset_squash_intro@{o}.
  - rewrite <- Hxy; exact Hfix.
  - rewrite Hxy; exact Hfix.
Defined.

(*
 The two memberships, on the nose.  Equations between [Prop]s, i.e.
 between OBJECTS, not between morphisms. 

 --------
 这两个成员，恰到好处。在 [Prop] 之间的方程，也就是在对象之间的方程，而不是在态射之间的方程。
*)
Example stab_mem (X : carrier (Powerset_Prop_obj@{o} (act_setoid A)))
  (s : carrier (grp_setoid G)) :
  stab X s = (∀ x, X x → fixes s x) := eq_refl.

Example fixed_mem (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G)))
  (x : carrier (act_setoid A)) :
  fixed S x = (∀ s, S s → fixes s x) := eq_refl.

(*
 Mac Lane's middle term: “sigma . x = x for all sigma in S and all x in
 X”.  It is the SAME TERM as the [Q]-side inclusion. 

 --------
 Mac Lane 的中间项：“sigma . x = x 对所有 sigma 属于 S 且所有 x 属于 X”。它与 [Q] 侧包含是相同的项。
*)
Definition FixesAll (X : carrier (Powerset_Prop_obj@{o} (act_setoid A)))
                    (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G)))
  : Prop := ∀ s, S s → ∀ x, X x → fixes s x.

Example stab_transpose_strict
  (X : carrier (Powerset_Prop_obj@{o} (act_setoid A)))
  (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) :
  subset_le@{o} S (stab X) = FixesAll X S := eq_refl.

(* The other side. Its whole content is the swap of two quantifiers -- so the biconditional Mac Lane states as two steps costs, here, exactly one permutation and one [eq_refl]. / 另一面。它的全部内容是两个量词的交换——所以麦克莱恩所述的双条件作为两步在这里正好花费一个排列和一个 [eq_refl]。 *)
Lemma fixed_transpose_iff
  (X : carrier (Powerset_Prop_obj@{o} (act_setoid A)))
  (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) :
  subset_le@{o} X (fixed S) <-> FixesAll X S.
Proof using A G. split; intros H a Ha b Hb; exact (H b Hb a Ha). Qed.

(* Antitonicity of the two operators, in the elementary form. The connection reads them at [op_rel], where they become the covariant fields the donor record asks for. / 两算子的反单调性，在基本形式中。连接在 [op_rel] 处读取它们，此处它们成为供体记录所要求的协变场。 *)
Lemma stab_antitone (X X' : carrier (Powerset_Prop_obj@{o} (act_setoid A))) :
  subset_le@{o} X X' → subset_le@{o} (stab X') (stab X).
Proof using A G. intros H s Hs x Hx; exact (Hs x (H x Hx)). Qed.

Lemma fixed_antitone (S S' : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) :
  subset_le@{o} S S' → subset_le@{o} (fixed S') (fixed S).
Proof using A G. intros H x Hx s Hs; exact (Hx s (H s Hs)). Qed.

(*
 THE GALOIS CONNECTION.  All six fields by name; the second relation is
 the REVERSED inclusion on P(G), which is Mac Lane's [Q^op]. 

 --------
 伽罗瓦连接。所有六个域按名称列出；第二个关系是 P(G) 上的逆包含关系，即 Mac Lane 的 [Q^op]。
*)
Definition group_action_galois :
  GaloisConnection (@subset_le@{o} (act_setoid A))
                   (op_rel (@subset_le@{o} (grp_setoid G))) :=
  {| gal_l := stab
   ; gal_r := fixed
   ; gal_mono_l := stab_antitone
   ; gal_mono_r := fun S T H => fixed_antitone T S H
   ; gal_to   := fun X S H => proj2 (fixed_transpose_iff X S) H
   ; gal_from := fun X S H => proj1 (fixed_transpose_iff X S) H |}.

(* The two preorders the connection is read at. / 两个先序用于读取连接。 *)
Definition stab_PreOrder_U : PreOrder (@subset_le@{o} (act_setoid A)) :=
  subset_le_preorder@{o} (act_setoid A).

Definition stab_PreOrder_G :
  PreOrder (op_rel (@subset_le@{o} (grp_setoid G))) :=
  op_PreOrder (subset_le_preorder@{o} (grp_setoid G)).

(* ------------------------------------------------------------------------ *)
(* * ** (D) The stabiliser is a subgroup / * ** (D) 稳定子是一个子群 *)

(*
 Mac Lane's “L X is the subgroup of G which fixes all points x in X”,
 as an inhabitant of Instance/Grp/Quotient.v's record.  [sub_mem]
 wants a [Type]-valued membership and [stab X s] is a [Prop], which is a
 [Type] by cumulativity; nothing is wrapped.  The four laws are the four
 the action supplies: saturation is [stab]'s own respectfulness, the unit
 is [act_unit], the product is [act_op], and the inverse is [act_op] with
 [grp_mul_inv_l] and [act_unit]. 

 --------
 Mac Lane 的 “L X 是固定 X 中所有点 x 的 G 的子群”，作为 Instance/Grp/Quotient.v 记录的一个成员。[sub_mem] 需要一个 [Type] 值的成员身份，而 [stab X s] 是一个 [Prop]，这由于累加性而是一个 [Type]；没有任何内容被封装。四条定律是作用提供的四条：饱和值是 [stab] 自身的尊重，单位是 [act_unit]，乘积是 [act_op]，逆元是 [act_op] 与 [grp_mul_inv_l] 和 [act_unit]。
*)
Definition stab_Subgroup
  (X : carrier (Powerset_Prop_obj@{o} (act_setoid A))) : Subgroup G.
Proof using A G.
  unshelve econstructor.
  - exact (fun s => stab X s).
  - intros a b Hab Ha.
    exact (proj1 (@proper_morphism _ _ _ _ (stab X) a b Hab) Ha).
  - intros x Hx; apply Powerset_squash_intro@{o}; exact (act_unit A x).
  - intros a b Ha Hb x Hx.
    refine (Ha x Hx _ _); intro Hax.
    refine (Hb x Hx _ _); intro Hbx.
    apply Powerset_squash_intro@{o}.
    rewrite (act_op A a b x); rewrite Hbx; exact Hax.
  - intros a Ha x Hx.
    refine (Ha x Hx _ _); intro Hax.
    apply Powerset_squash_intro@{o}.
    rewrite <- Hax at 1.
    rewrite <- (act_op A (grp_inv G a) a x).
    rewrite (grp_mul_inv_l G a).
    exact (act_unit A x).
Defined.

Example stab_Subgroup_mem
  (X : carrier (Powerset_Prop_obj@{o} (act_setoid A)))
  (s : carrier (grp_setoid G)) :
  sub_mem (stab_Subgroup X) s = stab X s := eq_refl.

(* ------------------------------------------------------------------------ *)
(* * ** (E) The two closure operators are idempotent / * ** (E) 这两个闭包运算是幂等的 *)

(*
 Mac Lane's display (2) at this connection.  In a preorder that is not a
 partial order the conclusion is mutual inclusion, which for these
 carriers IS the setoid's own [equiv]: (B) converts. 

 --------
 Mac Lane 在这个连接处的显示 (2)。在一个不是偏序的预序中，结论是相互包含，对于这些承载者来说，这正是集合等价自身的 [equiv]：(B) 转换。
*)
Lemma stab_fixed_stab
  (X : carrier (Powerset_Prop_obj@{o} (act_setoid A))) :
  stab (fixed (stab X)) ≈ stab X.
Proof using A G.
  apply subset_le_antisym.
  - exact (gal_lrl_above stab_PreOrder_G group_action_galois X).
  - exact (gal_lrl_below stab_PreOrder_U group_action_galois X).
Qed.

Lemma fixed_stab_fixed
  (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) :
  fixed (stab (fixed S)) ≈ fixed S.
Proof using A G.
  apply subset_le_antisym.
  - exact (gal_rlr_below stab_PreOrder_U group_action_galois S).
  - exact (gal_rlr_above stab_PreOrder_G group_action_galois S).
Qed.

(* Both operators respect [equiv], from antitonicity read both ways. / 两个算子都遵守 [equiv]，从逆单调性可以双向读取。 *)
Lemma stab_respects
  (X X' : carrier (Powerset_Prop_obj@{o} (act_setoid A))) (H : X ≈ X') :
  stab X ≈ stab X'.
Proof using A G.
  apply subset_le_antisym.
  - exact (stab_antitone X' X (fun x Hx => proj2 (H x) Hx)).
  - exact (stab_antitone X X' (fun x Hx => proj1 (H x) Hx)).
Qed.

Lemma fixed_respects
  (S S' : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) (H : S ≈ S') :
  fixed S ≈ fixed S'.
Proof using A G.
  apply subset_le_antisym.
  - exact (fixed_antitone S' S (fun x Hx => proj2 (H x) Hx)).
  - exact (fixed_antitone S S' (fun x Hx => proj1 (H x) Hx)).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** (F) The closed elements / **（F）闭合元素 *)

(*
 Section (A)'s predicates, unfolded at this connection.  A subset of [G]
 is closed when it contains everything that fixes all of its own fixed
 points; the reverse inclusion is free ([gal_counit]).  Dually for [U]. 

 --------
 第（A）节的谓词，在此连接中展开。 当一个  [G] 的子集包含其自身所有不动点的所有固定元素时，它是封闭的；反向包含是自由的（[gal_counit]）。 对于 [U] 同样适用。
*)
Definition ClosedG (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G)))
  : Prop := subset_le@{o} (stab (fixed S)) S.

Definition ClosedU (X : carrier (Powerset_Prop_obj@{o} (act_setoid A)))
  : Prop := subset_le@{o} (fixed (stab X)) X.

Example ClosedG_is_GalClosed_l
  (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) :
  ClosedG S = GalClosed_l group_action_galois S := eq_refl.

Example ClosedU_is_GalClosed_r
  (X : carrier (Powerset_Prop_obj@{o} (act_setoid A))) :
  ClosedU X = GalClosed_r group_action_galois X := eq_refl.

Definition closed_G_stab (X : carrier (Powerset_Prop_obj@{o} (act_setoid A)))
  : ClosedG (stab X) :=
  gal_closed_l_image stab_PreOrder_G group_action_galois X.

Definition closed_U_fixed
  (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) : ClosedU (fixed S) :=
  gal_closed_r_image stab_PreOrder_U group_action_galois S.

(*
 The closed subsets of [G] are EXACTLY the stabilisers, and the closed
 subsets of [U] exactly the fixed-point sets.  Section (A)'s general
 characterisation supplies the mutual-inclusion form; (B) upgrades it to
 the carriers' own [equiv]. 

 --------
 [G] 的闭子集正是稳定子，[U] 的闭子集正是不动点集。第 (A) 节的一般描述提供了相互包含的形式；(B) 将其提升为载体自身的 [equiv]。
*)
Lemma closed_G_iff (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) :
  ClosedG S ↔ ∃ X, S ≈ stab X.
Proof using A G.
  split.
  - intro H.
    destruct (fst (gal_closed_l_iff stab_PreOrder_U stab_PreOrder_G
                     group_action_galois S) H) as [X [H1 H2]].
    exists X; exact (subset_le_antisym H2 H1).
  - intros [X HX].
    refine (snd (gal_closed_l_iff stab_PreOrder_U stab_PreOrder_G
                   group_action_galois S) _).
    exists X; exact (fun s Hs => proj2 (HX s) Hs,
                     fun s Hs => proj1 (HX s) Hs).
Qed.

Lemma closed_U_iff (X : carrier (Powerset_Prop_obj@{o} (act_setoid A))) :
  ClosedU X ↔ ∃ S, X ≈ fixed S.
Proof using A G.
  split.
  - intro H.
    destruct (fst (gal_closed_r_iff stab_PreOrder_U stab_PreOrder_G
                     group_action_galois X) H) as [S [H1 H2]].
    exists S; exact (subset_le_antisym H1 H2).
  - intros [S HS].
    refine (snd (gal_closed_r_iff stab_PreOrder_U stab_PreOrder_G
                   group_action_galois X) _).
    exists S; exact (fun x Hx => proj1 (HS x) Hx,
                     fun x Hx => proj2 (HS x) Hx).
Qed.

(*
 Mac Lane's “L X is the subgroup of G”, read at EVERY closed subset: the
 membership is the given subset on the nose, and the four laws are
 transported from [stab_Subgroup (fixed S)] along the two inclusions. 

 --------
 Mac Lane 的 “L X 是 G 的子群”，在每个闭合子集上阅读：成员资格正是给定的子集，并且四条定律沿着两个包含从 [stab_Subgroup (fixed S)] 传递过来。
*)
Definition closed_G_Subgroup
  (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) (H : ClosedG S)
  : Subgroup G.
Proof using A G.
  unshelve econstructor.
  - exact (fun s => S s).
  - intros a b Hab Ha.
    exact (proj1 (@proper_morphism _ _ _ _ S a b Hab) Ha).
  - exact (H _ (sub_unit (stab_Subgroup (fixed S)))).
  - intros a b Ha Hb.
    refine (H _ (sub_mul (stab_Subgroup (fixed S)) a b _ _)).
    + exact (gal_counit group_action_galois stab_PreOrder_U S a Ha).
    + exact (gal_counit group_action_galois stab_PreOrder_U S b Hb).
  - intros a Ha.
    refine (H _ (sub_inv (stab_Subgroup (fixed S)) a _)).
    exact (gal_counit group_action_galois stab_PreOrder_U S a Ha).
Defined.

Example closed_G_Subgroup_mem
  (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) (H : ClosedG S)
  (s : carrier (grp_setoid G)) :
  sub_mem (closed_G_Subgroup S H) s = S s := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** (G) The adjunction / **（G）连接 *)

(*
 #380 applied: the two functors and the adjunction are [:=] terms, and
 every coherence obligation of [Adjunction] is an equation between
 parallel arrows in a thin category, hence discharged uniformly there. 

 --------
 #380 已应用：两个函子和伴随是 [:=] 项，并且 [Adjunction] 的每个相干性义务都是薄范畴中平行箭头之间的等式，因此在那里统一解决。
*)
Definition StabFunctor :
  Subsets@{o su} (act_setoid A) ⟶ Proset@{o su} stab_PreOrder_G :=
  GaloisFunctor_l stab_PreOrder_U stab_PreOrder_G group_action_galois.

Definition FixedFunctor :
  Proset@{o su} stab_PreOrder_G ⟶ Subsets@{o su} (act_setoid A) :=
  GaloisFunctor_r stab_PreOrder_U stab_PreOrder_G group_action_galois.

Definition group_action_adjunction : StabFunctor ⊣ FixedFunctor :=
  GaloisAdjunction stab_PreOrder_U stab_PreOrder_G group_action_galois.

Example StabFunctor_obj
  (X : carrier (Powerset_Prop_obj@{o} (act_setoid A))) :
  fobj[StabFunctor] X = stab X := eq_refl.

Example FixedFunctor_obj
  (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) :
  fobj[FixedFunctor] S = fixed S := eq_refl.

(*
 The target category IS the opposite of [Subsets (grp_setoid G)] on the
 two components that carry data: its objects are the subsets of [G] and
 its homs are reversed inclusions.  The whole records are not equal --
 not at [id] or [compose], which agree at [eq_refl] too, but at the
 [homset] record, whose [Equivalence] witness is [Proset]'s opaque
 [Program] obligation applied at swapped arguments -- and that is
 pinned in the probe. 

 --------
 目标范畴在承载数据的两个分量上是 [Subsets (grp_setoid G)] 的相反：它的对象是 [G] 的子集，而它的态射是逆包含。整个记录并不相等——在 [id] 或 [compose] 处不相等，它们在 [eq_refl] 也相同，而是在 [homset] 记录处，其 [Equivalence] 见证是 [Proset] 的不透明 [Program] 义务在交换参数上应用——这在探针中被固定。
*)
Example galois_PG_obj :
  obj[Proset@{o su} stab_PreOrder_G]
    = obj[(Subsets@{o su} (grp_setoid G))^op] := eq_refl.

Example galois_PG_hom
  (S T : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) :
  (S ~{Proset@{o su} stab_PreOrder_G}~> T)
    = (S ~{(Subsets@{o su} (grp_setoid G))^op}~> T) := eq_refl.


(* ------------------------------------------------------------------------ *)
(* * ** (I) Mac Lane's own typing: a pair adjoint on the right / * **（I）麦克莱恩自己的打字：右边的伴随对 *)

(*
 Theorem 1 types the two maps as [L : P -> Q^op] and [R : Q^op -> P], and
 Adjunction/Right.v's [AdjointOnTheRight S T] -- for
 [S : A^op ⟶ X] and [T : X^op ⟶ A], with the hom-set isomorphism
 [A(a, T x) ≅ X(x, S a)] -- is exactly that shape.  So the pair here IS a
 pair adjoint on the right, and saying so costs three modules of closure
 (129 with the [Require], 126 without; measured), which is why it is
 delivered rather than only cited.  [Adjunction/Right.v]'s own antitone
 witnesses are a three-element chain and the contravariant power set;
 neither is a group action, and the tokens “group” and “action” occur in
 that file only in one unrelated comment.

 The functors' arrow actions ARE the elementary antitonicity lemmas with
 their two subset arguments swapped, which is what “order-reversing” is
 once the source is written as an opposite category. 

 --------
 定理1将这两个映射归类为 [L : P -> Q^op] 和 [R : Q^op -> P]，并且对 [S : A^op ⟶ X] 和 [T : X^op ⟶ A] 的伴随/右伴随是 [AdjointOnTheRight S T]，其同态集同构 [A(a, T x) ≅ X(x, S a)] 的形状恰好如此。因此，这里的这对确实是一对右伴随，并且这样说需要三个闭包模块（有 [Require] 时为129，没有时为126；已测量），这就是它被提供而不仅仅被引用的原因。[Adjunction/Right.v] 自身的逆序证人是一个三元素链和反变幂集；它们都不是群作用，并且“group”和“action”令牌在该文件中只出现在一个不相关的注释中。

 函子在箭头上的作用是基本的逆序引理，并将它们的两个子集参数交换，这就是当源被写为对立范畴时“顺序反转”的含义。
*)

#[local] Obligation Tactic := simpl; repeat intro; exact I.

Program Definition StabOp :
  (Subsets@{o su} (act_setoid A))^op ⟶ Subsets@{o su} (grp_setoid G) := {|
  fobj := stab;
  fmap := fun X X' f => stab_antitone X' X f
|}.

Program Definition FixedOp :
  (Subsets@{o su} (grp_setoid G))^op ⟶ Subsets@{o su} (act_setoid A) := {|
  fobj := fixed;
  fmap := fun S S' f => fixed_antitone S' S f
|}.

(*
 The hom-set isomorphism IS the transpose of (C): its forward leg is
 [fixed_transpose_iff]'s first projection and its backward leg the
 second, and the target of the forward leg is [FixesAll X S] on the nose
 (by [stab_transpose_strict]).  All eight obligations -- the four
 naturality laws, the two isomorphism laws and the two respectfulness
 certificates of the legs -- are equations between parallel arrows in a
 thin category, hence discharged uniformly. 

 --------
 Hom 集同构本身就是 (C) 的转置：它的前向分支是 [fixed_transpose_iff] 的第一个投影，后向分支是第二个投影，并且前向分支的目标正是 [FixesAll X S] （通过 [stab_transpose_strict]）。所有八个约束——四个自然性定律、两个同构定律以及两条支线的保持性质证明——都是薄范畴中平行箭头之间的方程，因此可以统一解除。
*)
Program Definition group_action_AdjointOnTheRight :
  AdjointOnTheRight StabOp FixedOp := {|
  aor := fun X S =>
    {| to   := {| morphism := fun h => proj1 (fixed_transpose_iff X S) h |}
     ; from := {| morphism := fun h => proj2 (fixed_transpose_iff X S) h |} |}
|}.

Example StabOp_obj (X : carrier (Powerset_Prop_obj@{o} (act_setoid A))) :
  fobj[StabOp] X = stab X := eq_refl.

Example FixedOp_obj (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) :
  fobj[FixedOp] S = fixed S := eq_refl.

End Action.

Arguments fixes {G A} s x.
Arguments stab {G A} X.
Arguments fixed {G A} S.
Arguments FixesAll {G A} X S.
(*
 [A] stays EXPLICIT in [ClosedG]: its argument [S] is a subset of the
 GROUP, which determines [G] but not the action. 

 --------
 [A] 在 [ClosedG] 中保持 EXPLICIT：其参数 [S] 是 GROUP 的一个子集，它决定了 [G] 但不决定动作。
*)
Arguments ClosedG {G} A S.
Arguments ClosedU {G A} X.

(* ------------------------------------------------------------------------ *)
(* * ** (H1) A witness: the two-element group acting on two points / * **（H1）一个证人：作用于两个点的二元群 *)

(*
 The two-point setoid, at ONE universe.  [eq_Setoid] (Lib/Setoid.v) is
 polymorphic in exactly the level [Subsets] needs, which
 Instance/Grp.v's [Z2] is not: that one is declared
 [Z2@{u} : GrpObject@{u Set Set}], pinning both the carrier and the
 relation universe to the literal [Set], and [Subsets (grp_setoid Z2)] is
 then rejected.  The rejection is pinned in Test/ProbeGalois381.v.
 (An earlier revision quoted [GrpObject@{u Set u}] and cited [Z2] at a
 line it has since left;
 re-measured after the PR “algebraic carriers are sets” (2026-09-17), which
 permuted [GrpObject]'s universe roles from (carrier, proof, aux) to
 (aux, carrier, proof).  The obstruction is if anything sharper and the
 conclusion is unchanged.)  CORRECTION (#450): [Z2] is no longer pinned;
 #450 annotated it in place as [Z2@{p} : GrpObject@{p p p}], and
 Test/ProbeGalois381.v's rejection is a control since.  This two-point
 setoid is kept as it is. 

 --------
 在一个宇宙中的二元集合，[eq_Setoid]（Lib/Setoid.v）正好在 [Subsets]  需要的级别上是多态的，而 Instance/Grp.v 的 [Z2]  不是：那个被声明为 [Z2@{u} : GrpObject@{u Set Set}]，将承载类型和关系宇宙都固定为字面量 [Set]，然后 [Subsets (grp_setoid Z2)] 被拒绝。拒绝情况记录在 Test/ProbeGalois381.v 中。（早期修订引用了 [GrpObject@{u Set u}] 并在其已离开的某行引用了 [Z2]；在 PR “代数承载是集合”(2026-09-17) 之后重新测量，该 PR 将 [GrpObject] 的宇宙角色从（承载、证明、辅助）置换为（辅助、承载、证明）。）阻塞如果有任何更尖锐的情况，结论不变。） 修正 (#450)：[Z2] 不再被固定；#450 在原处将其标注为 [Z2@{p} : GrpObject@{p p p}]，Test/ProbeGalois381.v 的拒绝是一个控制。这个两点集合同构保持不变。
*)
Definition galois_two@{wo} : SetoidObject@{wo wo} :=
  {| carrier := bool ; is_setoid := eq_Setoid@{wo} bool |}.

(* Z/2 as [bool] under exclusive or, with [false] the unit and every element its own inverse. Transparent: the [discriminate] arguments below need its operation to compute. / Z/2作为[bool]在异或下，[false]是单位，每个元素都是其自身的逆。透明：下面的[discriminate]参数需要它的运算来计算。 *)
Definition GalZ2@{wo} : GrpObject@{wo wo wo}.
Proof.
  unshelve refine {| grp_setoid := galois_two@{wo}
                   ; grp_unit := false
                   ; grp_mul := xorb
                   ; grp_inv := fun b : bool => b
                   ; grp_prop := eq_PropEquiv@{wo} bool |}.
  - exact (fun x y Hxy u v Huv => f_equal2 xorb Hxy Huv).
  - intros [|] [|] [|]; reflexivity.
  - intros [|]; reflexivity.
  - intros [|]; reflexivity.
Defined.

(*
 Z/2 acting on two points by the flip.  [act_respects] is supplied by
 hand rather than left to resolution, so that no instance search can pin
 a universe (the hazard Theory/Universal/Element.v records). 

 --------
 Z/2 在两个点上通过翻转作用。[act_respects] 是手动提供的，而不是留给求解，以便没有实例搜索可以固定一个宇宙（危险 Theory/Universal/Element.v 记录）。
*)
Definition GalZ2Act@{wo +} : MSetoidAction (grp_mon GalZ2@{wo}).
Proof.
  unshelve refine (@Build_MSetoidAction (grp_mon GalZ2@{wo}) galois_two@{wo}
                     (fun g x => xorb g x)
                     (fun g g' Hg x x' Hx => f_equal2 xorb Hg Hx) _ _).
  - intros [|]; reflexivity.
  - intros [|] [|] [|]; reflexivity.
Defined.

(* The action moves a point, so neither operator is the one belonging to a trivial action. / 该动作移动一个点，因此没有一个算子属于平凡动作。 *)
Example galois_z2_act_moves : act GalZ2Act true true = false := eq_refl.

(*
 Subsets of the two-point setoid.  [equiv] there is Leibniz equality, so
 respectfulness is a substitution. 

 --------
 二点集合的子集。 [equiv] 存在莱布尼茨等式，因此尊重性是一种替换。
*)
Definition galois_sub@{wo} (p : bool → Prop) :
  carrier (Powerset_Prop_obj@{wo} galois_two@{wo}).
Proof.
  unshelve refine (@Build_SetoidMorphism@{wo wo wo}
    bool (is_setoid galois_two@{wo})
    Prop (is_setoid Powerset_Prop_truth@{wo}) p _).
  intros x y Hxy; simpl in Hxy; subst; split; exact (fun h => h).
Defined.

Definition galois_true@{wo} : carrier (Powerset_Prop_obj@{wo} galois_two@{wo})
  := galois_sub@{wo} (fun b => b = true).

Definition galois_false@{wo} : carrier (Powerset_Prop_obj@{wo} galois_two@{wo})
  := galois_sub@{wo} (fun b => b = false).

(* THE STABILISER OF {true} IS THE TRIVIAL SUBGROUP. The forward step eliminates the truncation into a [Prop] goal and closes by [discriminate] on the computed [xorb true true]. / {true} 的稳定子是平凡子群。前进步骤消除了向 [Prop] 目标的截断，并通过在计算出的 [xorb true true] 上的 [discriminate] 关闭。 *)
Lemma galois_z2_stab_forces (s : bool) :
  stab (A := GalZ2Act) galois_true s → s = false.
Proof.
  intro H; refine (H true eq_refl _ _); intro Hfix.
  destruct s; [ discriminate Hfix | reflexivity ].
Qed.

Lemma galois_z2_stab_unit : stab (A := GalZ2Act) galois_true false.
Proof.
  intros x Hx; apply Powerset_squash_intro; reflexivity.
Qed.

Theorem galois_stab_true_trivial :
  stab (A := GalZ2Act) galois_true ≈ galois_false.
Proof.
  apply subset_le_antisym.
  - intros s Hs; exact (galois_z2_stab_forces s Hs).
  - intros s Hs; simpl in Hs; subst s; exact galois_z2_stab_unit.
Qed.

(* THE FIXED-POINT SET OF THE NON-IDENTITY ELEMENT IS EMPTY. / 非单位元的固定点集是空的。 *)
Theorem galois_fixed_true_empty (x : bool) :
  fixed (A := GalZ2Act) galois_true x → False.
Proof.
  intro H; refine (H true eq_refl _ _); intro Hfix.
  destruct x; discriminate Hfix.
Qed.

(* NON-CLOSURE, ON THE GROUP SIDE: {true} is not a stabiliser. Its closure is all of G, because every element stabilises the empty set. / 在群这一边的非闭包：{true} 不是稳定子。它的闭包是整个 G，因为每个元素都会稳定空集。 *)
Theorem galois_true_not_ClosedG :
  ClosedG GalZ2Act galois_true → False.
Proof.
  intro H.
  assert (Hfalse : galois_true false).
  { refine (H false _); intros x Hx.
    destruct (galois_fixed_true_empty x Hx). }
  discriminate Hfalse.
Qed.

(* NON-CLOSURE, ON THE POINT SIDE: {true} is not a fixed-point set. Its closure is all of U, because the trivial subgroup fixes everything. / 非闭包，在点侧：{true} 不是一个不动点集。它的闭包是整个 U，因为平凡子群固定所有元素。 *)
Theorem galois_true_not_ClosedU :
  ClosedU (A := GalZ2Act) galois_true → False.
Proof.
  intro H.
  assert (Hfalse : galois_true false).
  { refine (H false _); intros s Hs.
    apply Powerset_squash_intro.
    rewrite (galois_z2_stab_forces s Hs); reflexivity. }
  discriminate Hfalse.
Qed.

(*
 A CLOSED PAIR, exhibited rather than merely known to exist: the trivial
 subgroup is closed, and so is the whole point set.  Both are instances
 of (F)'s “every image is closed”, with the concrete content supplied by
 [galois_stab_true_trivial]. 

 --------
 一个闭合对，而不仅仅是已知存在：平凡子群是闭合的，整个点集也是闭合的。两者都是(F)的“每个像都是闭合的”实例，其具体内容由[galois_stab_true_trivial]提供。
*)
Theorem galois_false_ClosedG : ClosedG GalZ2Act galois_false.
Proof.
  refine (snd (closed_G_iff GalZ2 GalZ2Act galois_false) (galois_true; _)).
  symmetry; exact galois_stab_true_trivial.
Qed.

(* [stab] is not constant: it separates the empty subset from {true}. / [stab] 不是常量：它将空子集与 {true} 分开。 *)
Definition galois_empty@{wo} : carrier (Powerset_Prop_obj@{wo} galois_two@{wo})
  := galois_sub@{wo} (fun _ => False).

Theorem galois_stab_not_constant :
  stab (A := GalZ2Act) galois_empty true
    * (stab (A := GalZ2Act) galois_true true → False).
Proof.
  split.
  - intros x Hx; destruct Hx.
  - intro H; pose proof (galois_z2_stab_forces true H) as Heq.
    discriminate Heq.
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** (H2) A witness whose stabiliser is a proper non-trivial subgroup / * **（H2）其稳定子是一个适当的非平凡子群的证人 *)

(*
 In (H1) the action is FREE, so every stabiliser is one of the two
 trivial subgroups and [stab_Subgroup] is exercised only at those.  The
 Klein four-group acting on two points through its FIRST coordinate is
 not free, and the stabiliser of {true} is then neither the whole group
 nor the trivial one.  NO CARDINALITY IS CLAIMED: nothing below counts
 either group, and what is proved is one omitted element and one
 contained non-unit element. 

 --------
 在 (H1) 中，该作用是自由的，因此每个稳定子都是两个平凡子群之一，并且 [stab_Subgroup] 仅在这些点上作用。克莱因四元群通过其第一个坐标作用于两个点时并不自由，并且 {true} 的稳定子既不是整个群，也不是平凡子群。没有声称任何基数：下面没有计算任何群，并且所证明的是一个遗漏的元素和一个包含的非单位元素。
*)
Definition galois_four@{wo} : SetoidObject@{wo wo} :=
  {| carrier := (bool * bool)%type
   ; is_setoid := eq_Setoid@{wo} (bool * bool)%type |}.

Definition galois_v4_mul (g h : bool * bool) : bool * bool :=
  (xorb (fst g) (fst h), xorb (snd g) (snd h)).

Definition GalV4@{wo} : GrpObject@{wo wo wo}.
Proof.
  unshelve refine {| grp_setoid := galois_four@{wo}
                   ; grp_unit := (false, false)
                   ; grp_mul := galois_v4_mul
                   ; grp_inv := fun g : bool * bool => g
                   ; grp_prop := eq_PropEquiv@{wo} (bool * bool)%type |}.
  - exact (fun x y Hxy u v Huv => f_equal2 galois_v4_mul Hxy Huv).
  - intros [[|] [|]] [[|] [|]] [[|] [|]]; reflexivity.
  - intros [[|] [|]]; reflexivity.
  - intros [[|] [|]]; reflexivity.
Defined.

Definition GalV4Act@{wo +} : MSetoidAction (grp_mon GalV4@{wo}).
Proof.
  unshelve refine (@Build_MSetoidAction (grp_mon GalV4@{wo}) galois_two@{wo}
                     (fun g x => xorb (fst g) x)
                     (fun g g' Hg x x' Hx =>
                        f_equal2 xorb (f_equal (@fst bool bool) Hg) Hx) _ _).
  - intros [|]; reflexivity.
  - intros [[|] [|]] [[|] [|]] [|]; reflexivity.
Defined.

(* Membership in the stabiliser of {true} is exactly “the first coordinate is the unit”, both ways. / {true} 的稳定子群的成员恰好是“第一个坐标是单位元”，双向成立。 *)
Lemma galois_v4_stab_forces (g : bool * bool) :
  stab (A := GalV4Act) galois_true g → fst g = false.
Proof.
  intro H; refine (H true eq_refl _ _); intro Hfix.
  destruct g as [[|] [|]]; simpl in *; try discriminate Hfix; reflexivity.
Qed.

Lemma galois_v4_stab_holds (g : bool * bool) :
  fst g = false → stab (A := GalV4Act) galois_true g.
Proof.
  intros Hg x Hx; apply Powerset_squash_intro.
  simpl; rewrite Hg; reflexivity.
Qed.

(* NOT the trivial subgroup: it contains an element other than the unit. / 不是平凡子群：它包含除了单位元以外的元素。 *)
Theorem galois_v4_stab_nontrivial :
  sub_mem (stab_Subgroup GalV4 GalV4Act galois_true) (false, true)
    * ((false, true) = grp_unit GalV4 → False).
Proof.
  split.
  - exact (galois_v4_stab_holds (false, true) eq_refl).
  - intro Heq; discriminate Heq.
Qed.

(* NOT the whole group: it omits an element. / 不是整个群体：它省略了一个元素。 *)
Theorem galois_v4_stab_proper :
  sub_mem (stab_Subgroup GalV4 GalV4Act galois_true) (true, false) → False.
Proof.
  intro H; pose proof (galois_v4_stab_forces (true, false) H) as Heq.
  discriminate Heq.
Qed.
