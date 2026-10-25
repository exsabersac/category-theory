Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Coequalizer.Wide.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Parallel.Wide.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Coproduct.
Require Import Category.Instance.Top.Homotopy.
Require Import Category.Instance.Top.Subspace.TypeValued.
Require Import Category.Instance.Top.Quotient.

Generalizable All Variables.

(* * * The category of pairs, and X/A as a left adjoint / * * 对偶范畴，以及 X/A 作为左伴随 *)

(*
 Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
 §V.9, book pp. 134-135 (PDF pp. 143-144), read from the page images:
 "If we consider the category Top^(2) whose objects are pairs ⟨X, A⟩
 (a space X with a subset A) and whose arrows ⟨X, A⟩ → ⟨X', A'⟩ are
 continuous maps X → X' sending A to A', then the definition of X/A,
 for Y a pointed topological space, reads:
 Top_*(X/A, Y) = Top^(2)(⟨X, A⟩, ⟨Y, *⟩).
 Thus ⟨X, A⟩ ↦ X/A is left adjoint to the functor Y ↦ ⟨Y, *⟩ which
 sends each pointed space to the pair ⟨Y, *⟩." (catalog id
 maclane:V.9:construction6; the book numbers it not)
 nLab:      https://ncatlab.org/nlab/show/Top
 nLab:      https://ncatlab.org/nlab/show/pointed+object
 Wikipedia: https://en.wikipedia.org/wiki/Quotient_space_(topology)
 Book:      A. Hatcher, "Algebraic Topology", Cambridge University Press
 (2002), Proposition 2.22 (good pairs)

 BACKGROUND.  Pairs of spaces are where relative homology lives, and
 the quotient is how it is computed: for a good pair (X, A) the
 quotient map induces isomorphisms from the relative homology of
 (X, A) to the reduced homology of X/A (Hatcher, Proposition 2.22).
 Mac Lane's paragraph turns the collapse into a functor on pairs and
 reads its defining property as a hom-set bijection, so that
 ⟨X, A⟩ ↦ X/A is a left adjoint.  The target is the category of pointed
 spaces, the tree's [Top_pointed] (Instance/Top/Homotopy.v).  The nLab
 page on pointed objects records the simplest case: the forgetful
 functor from pointed objects has a left adjoint, adjoining a disjoint
 basepoint, X ↦ X₊ = X ⊔ *.  That is Mac Lane's adjunction at the empty
 subset, since every continuous map carries ∅ into the basepoint.

 AT A = ∅ THE BOOK LEAVES A CHOICE, AND ONE READING MAKES ITS TWO
 CONSTRUCTIONS AGREE.  Mac Lane defines the coequalizer of a pair
 elementarily (book p. 64, PDF p. 73, display (6): an arrow u : b → e
 with uf = ug, universal), reads it as a universal arrow to Δ (p. 65,
 PDF p. 74: "just a universal arrow from ⟨f, g⟩ to the functor Δ"),
 and says coequalizers of any set of maps "are defined in the same
 way", all read from the page images.  The two forms agree on every
 nonempty set; at the empty set the universal arrow is a ⊔ b and the
 elementary form b.  Read as the universal arrow, the reading p. 135
 needs since Top_*(X/A, Y) takes X/A pointed, his X/∅ is X ⊔ * and
 Constructions 5 and 6 agree at every A
 ([pquot_wide_coequalizer_colimit]); read elementarily, as
 Structure/Coequalizer/Wide.v's header reads it, X/∅ is X and they
 part there.  The universal arrow is a colimit over the shape that has
 the domain * as a vertex, Wide.v's [WideCoequalizer]: a cocone has a
 leg out of * as well as one out of X, so no point of A is needed, and
 at the empty family the leg out of * is unconstrained, which gives
 the X₊ of the nLab's adjoint above.  The refutations below are about
 the elementary reading.

 This file defines X/A uniformly as (X ⊔ {∗})/(A ∼ ∗): the points are
 [option X], [None] the new point, [Some x] identified with [None]
 exactly when x lies in A ([pquot_rel]), with the quotient topology
 [TQuot] of Instance/Top/Subspace/TypeValued.v along [Some]
 ([pquot_space]).  No case split on whether A is empty, which is not
 decidable here, is needed.  What is proved about it:
 - It IS the coequalizer of the point-inclusions of A read as the
 universal arrow, for every A, the empty one included, with no
 point of A ([pquot_wide_coequalizer_colimit]: a [WideCoequalizer]
 of exactly Construction 5's family [collapse_sub_family], at the
 type of Instance/Top/Quotient.v's [collapse_colimit]).  Its apex
 is [pquot_space X], its leg out of X is [pquot_in X], and its leg
 out of * sends the one point to the left adjoint's basepoint, all
 at [eq_refl] ([pquot_wide_coequalizer_colimit_apex],
 [pquot_wide_coequalizer_colimit_in],
 [pquot_wide_coequalizer_colimit_base]); and the left adjoint's
 underlying space at every pair IS that apex, at [eq_refl]
 ([pquot_wide_coequalizer_colimit_quotient]), so under that reading
 Mac Lane's two constructions give one space.  Every colimit of
 that family has a point, the image of * ([collapse_colimit_point]).
 - It is the pushout X ⊔_A ∗ in [Top] ([pquot_pushout]), of the
 inclusion of the points of A with the discrete topology
 ([pair_sub_space], [pair_sub_incl]) against the map to the point;
 the apex is [pquot_space X] at [eq_refl] ([pquot_pushout_apex]).
 The colimit above descends through the pushout's mediator
 [pquot_po_med]: a cocone's two legs are a map out of X and a point
 absorbing A.  The discrete topology is a choice: the subspace
 topology is not formable at the points' universe (the header of
 Instance/Top/Subspace/TypeValued.v), and since neither the cocone
 condition nor the mediator's continuity consults the topology of
 A, any topology making the inclusion continuous gives the same
 pushout (argued, not formalized).
 - Given a point [a0] of A, X ~> X/A is also an ELEMENTARY wide
 coequalizer of the point-inclusions of A ([pquot_coequalizer]),
 the record [IsWideCoequalizer] of Structure/Coequalizer/Wide.v
 that Instance/Top/Quotient.v's [collapse_coequalizer] meets for
 every A; so the two readings of X/A are isomorphic in [Top] when A
 has a point ([pquot_collapse_iso], by [wide_coequalizer_unique]),
 the iso being x ↦ [Some x] one way and [Some x] ↦ x, [None] ↦ a0
 the other, at [eq_refl] ([pquot_collapse_iso_to],
 [pquot_collapse_iso_from_some], [pquot_collapse_iso_from_none]).
 They are isomorphic as POINTED spaces as well: Construction 5's
 X/A pointed at [a0] ([collapse_pointed]) is isomorphic in
 [Top_pointed] to the left adjoint's value [fobj[PairQuotient] X]
 ([pquot_collapse_iso_pointed]).
 - X/∅ is X₊: [pquot_empty_sum_iso] identifies [pquot_space] of
 ⟨X, ∅⟩ ([empty_pair]) with Instance/Top/Coproduct.v's
 [Sum_Top X Point_Top] in [Top], [Some x] ↦ [inl x] and
 [None] ↦ [inr ttt] at [eq_refl] ([pquot_empty_sum_iso_some],
 [pquot_empty_sum_iso_none]), an isomorphism, refused at [eq_refl] as
 an equation of spaces (Test/ProbeCollapse459.v's N16); the new
 point is new ([pquot_empty_new_point]).  So, read as the universal
 arrow, the coequalizer of the empty family is X ⊔ *
 ([pquot_wide_coequalizer_colimit_empty], the colimit's apex at
 ⟨X, ∅⟩ against [Sum_Top X Point_Top]).

 THE ELEMENTARY READING AT A = ∅.  [IsWideCoequalizer], book p. 64's
 display (6) extended to a set of maps, states a coequalizer as an
 arrow out of X alone.  At the empty family its condition is vacuous
 and it pins down X itself (Instance/Top/Quotient.v's
 [collapse_empty_iso], X/∅ ≅ X), where the colimit is X ⊔ *: the gap
 between the two forms that the header of Structure/Coequalizer/Wide.v
 records ([wide_coround_trip_needs_point]).  At X = ∅ no elementary
 wide coequalizer of the empty family has a point, whatever its
 construction (Quotient.v's [empty_wide_coequalizer_pointless]).  The
 refutations here are statements about that elementary reading, under
 which Constructions 5 and 6 part at A = ∅, a case the book does not
 treat: no pointed space's underlying space is an elementary wide
 coequalizer of the empty family at ∅
 ([no_pointed_coequalizer_at_empty]); so no assignment of a pointed
 space to each pair, a functor or any other function on objects, makes
 every underlying space an elementary wide coequalizer of the
 point-inclusions ([no_pointed_elementary_coequalizers]); this file's
 X/A at ⟨∅, ∅⟩ is not one, so [pquot_coequalizer]'s point of A cannot
 be dropped ([pquot_empty_not_coequalizer],
 [pquot_coequalizer_needs_point]); and at ⟨∅, ∅⟩ no colimit's apex
 carries one ([empty_colimit_not_elementary]), the two forms parting
 there at [Top] as that header says they part in general.  None uses
 the uniqueness of left adjoints or an initial object of [Top_pointed].

 THE CATEGORY OF PAIRS.  [PairTop]: a space with a Type-valued
 predicate on its points that respects their equality
 ([pair_sub_proper]).  [PairMap]: a continuous map carrying the subset
 into the subset; the hom-setoid is [Top]'s own read on the underlying
 maps, as Instance/Top/Homotopy.v's [PointedMap_Setoid] is, so
 [Top_pairs] has [Top_pointed]'s shape.  What bears on the two choices
 is pinned in Test/ProbeCollapse459.v, which carries this file's import
 list.
 - Type, not Prop, is forced by ⟨Y, *⟩.  The book's ⟨Y, *⟩ is the
 predicate y ≈ y0, whose values are the Type-valued equality of a
 space's points; read as a Prop-valued predicate it is refused,
 "The term "y ≈ ptop_pt Y" has type "Type" while it is expected to
 have type "Prop"" (the probe's N10).  As a Prop it must be
 squashed, [inhabited (y ≈ y0)], and the transpose needs it
 unsquashed ([pquot_from_map]'s case [Some x] ∼ [None]); unsquashing
 is refused, "Incorrect elimination of "H" in the inductive type
 "inhabited": the return type has sort "Type" while it should be
 SProp or Prop" (N11).  Control: the elimination into
 [inhabited (y ≈ y0)] is accepted.
 - The respect field is a design choice, not a necessity.  A subset
 of a setoid is taken closed under the points' equality, the setoid
 reading of Mac Lane's "subset": points equal in the space are one
 point of it.  The alternative is to drop the field and saturate A
 inside the identification, as Instance/Top/Quotient.v's
 [collapse_image] does: the same four-case relation over [option X]
 with the saturation of A, the points equal to a point of A, in
 place of A is an equivalence with no field (Test/ProbeCollapse459.v's
 [p459_sat_rel_Equivalence], closed under the global context).
 What is measured about the field concerns the UNSATURATED relation
 [pquot_rel] only: without the field it is not transitive, on [bool]
 with the total equality and A := (= true), [Some false] ∼
 [Some true] ∼ [None] while [Some false] ≁ [None] (the probe's
 [p459_unsat_rel_not_transitive], closed under the global context).

 THE ADJUNCTION.  [PointPair] sends Y to ⟨Y, *⟩; [PairQuotient] sends
 ⟨X, A⟩ to X/A pointed at [None], and a map f to [Some x] ↦ [Some (f x)],
 [None] ↦ [None].  [pairs_quotient_iso X Y] is the book's display as an
 [Isomorphism] in [Sets]; its "=" is refused at [eq_refl] as an
 equation of hom types (Test/ProbeCollapse459.v's N12).  [pquot_to]
 restricts along [Some], [pquot_from] extends by sending [None] to the
 basepoint, its continuity from [TQuot]'s universal property.
 [pairs_quotient_adjunction] (the issue's pinned name) is
 [Build_Adjunction'] on it, both naturality squares pointwise
 reflexivity; the unit is x ↦ [Some x], the counit [Some y] ↦ y and
 [None] ↦ the basepoint.  It is an [Adjunction] record in [Top], where
 Instance/Top/Subspace/TypeValued.v's sliced quotient adjunction is
 refused, because [Adjunction] identifies the hom levels of its two
 categories (Theory/Adjunction.v, About: [h1 = h2]) and here both
 [Top_pointed@{h o}] and [Top_pairs@{h o}] have their homs at [h].

 THE REALS.  [Top_pointed] lives in Instance/Top/Homotopy.v, which
 requires the stdlib reals and opens [R_scope]; this file reaches them
 through that import, as Instance/Top/Wedge.v does, and every constant
 here still prints "Closed under the global context".  The relation
 [pquot_rel] is written under [%type] for that reason.  Moving
 [PointedTop] and [Top_pointed] to a file free of the reals is left to
 the maintainer.

 STRENGTHS.  At [eq_refl]: [PointPair_sub], [pquot_space_carrier],
 [pquot_basepoint], [pquot_space_open], [pquot_to_eval],
 [pquot_from_eval_some], [pquot_from_eval_none],
 [pairs_quotient_unit_eval], [pairs_quotient_counit_some],
 [pairs_quotient_counit_none], [pairs_quotient_adj_is] (the adjunction's
 hom-set isomorphism IS [pairs_quotient_iso]), [pquot_pushout_apex],
 the four readbacks of the colimit [pquot_wide_coequalizer_colimit]
 (its apex, its two legs and the left adjoint's underlying space), the
 three [pquot_collapse_iso] readbacks and the two [pquot_empty_sum_iso]
 readbacks.  Up to [≈]: the category and functor
 laws, the isomorphism laws, the naturality squares and the universal
 properties.  Eleven [Defined], counted by token, every one
 load-bearing: each closed [Qed] alone in a scratch copy leaves a
 named constant refused — [point_pair_map] ([PointPair]'s first
 obligation), [pquot_fmap_map] ([pquot_fmap_cont]), [pquot_to]
 ([pairs_quotient_iso]'s first obligation), [pquot_from_map]
 ([pquot_from]), [pairs_quotient_adjunction]
 ([pairs_quotient_unit_eval], "cannot unify "unit x" and "Some x""),
 [pquot_po_map] ([pquot_po_med]), [pquot_pushout]
 ([pquot_pushout_apex]), [pquot_coequalizer]
 ([pquot_collapse_iso_from_some]), [pquot_empty_sum_to] and
 [pquot_empty_sum_from] ([pquot_empty_sum_iso]), [pquot_empty_sum_iso]
 ([pquot_empty_sum_iso_some]).

 UNIVERSES, read by [About] under [Set Printing Universes] on all 100
 constants of this file's [Print Module] listing (the two records,
 their constructors and projections, and the fourteen [Program]
 obligations included).  Binder order: [@{h o ...}], the order of
 [Top@{h o}], except for the constants that restate Construction 5's
 wide-coequalizer vocabulary, which keep Instance/Top/Quotient.v's
 [@{o h ...}] and so instantiate like the constants they read (the
 colimit form, [pquot_wide_legs] through
 [pquot_wide_coequalizer_colimit_quotient] and
 [pquot_wide_coequalizer_colimit_empty], with
 [collapse_colimit_point]; [pquot_coequalizer], [pquot_collapse_iso]
 with its three readbacks and [pquot_collapse_iso_pointed]; and the
 refutations [pquot_empty_not_coequalizer],
 [pquot_coequalizer_needs_point], [no_pointed_coequalizer_at_empty],
 [no_pointed_elementary_coequalizers] and
 [empty_colimit_not_elementary]).
 - The constants that mention no arrow of [Top] ([PairTop], its
 constructor and projections, [point_pair], [pquot_rel] through
 [pquot_pointed], [pquot_space_open], [pair_sub_setoid] and its
 [Equivalence], [pair_sub_space], [pair_sub_incl_map],
 [empty_pair], [pquot_empty_new_point], [pquot_empty_sum_to],
 [pquot_empty_sum_from] and [collapse_pointed]): [@{o}], with no
 constraint beyond stdlib caps; X/A is a [TopSpace@{o}], at the
 universe of X.
 - [PairMap], [Top_pairs], [PointPair], [PairQuotient] and the maps
 between them, the section constants [pquot_po_map] and
 [pquot_po_med] and [pquot_empty_sum_iso] with its two readbacks
 among them: [@{h o}] with [o < h] and stdlib caps;
 [Top_pairs@{h o} : Category@{h h h}], the shape of
 [Top_pointed@{u u0}] (About: [Category@{u u u}], [u0 < u]).
 - The colimit form ([pquot_wide_legs], [pquot_wide_legs_coherence],
 [pquot_wide_cocone], [pquot_wide_ump],
 [pquot_wide_coequalizer_colimit] with its four readbacks and
 [pquot_wide_coequalizer_colimit_empty], and
 [collapse_colimit_point]): [@{o h}] with [o < h] and stdlib caps;
 the colimit is a [WideCoequalizer@{h h}] of
 [AWide@{h h h h h} (collapse_sub_family@{o h} X (pair_sub X))],
 the instance of Instance/Top/Quotient.v's [collapse_colimit@{o h}]
 at A := [pair_sub X] (both About).
 - [pairs_quotient_iso@{h o u}]: [o < h] and [h < u], an
 [Isomorphism] in [Sets@{h u}], whose objects, the hom-setoids at
 [h], sit at [u].  [pairs_quotient_adjunction@{h o u v}]: the same
 two bounds, and [v] in no constraint.  [v] is [Adjunction]'s own
 binder [sp] of [Adjunction@{o1 h1 p1 o2 h2 p2 o3 p3 so sh sp}],
 which occurs in no constraint of that record's About block.  The
 statement is written [Adjunction@{h h h h h h h h u h v}]: the same
 [Build_Adjunction'] term stated through the notation [⊣] under the
 closed binder, [v] named in it, is refused at the statement,
 "Universe <1> (...) is unbound" (Test/ProbeCollapse459.v's N13),
 while the finished constant reads through [⊣] once the binder
 names [v] and is refused when it does not (N14 and its control).
 - [pquot_coequalizer], [pquot_empty_not_coequalizer],
 [pquot_coequalizer_needs_point], [no_pointed_coequalizer_at_empty],
 [no_pointed_elementary_coequalizers] and
 [empty_colimit_not_elementary]: [@{o h i}] with [o < h] and
 [o <= i], the flexible index of Instance/Top/Quotient.v's header
 (its W-c).  [pquot_collapse_iso@{o h u}] and
 [pquot_collapse_iso_pointed@{o h u}]: [u] is
 [wide_coequalizer_unique]'s own binder, as in that file; with [u]
 dropped the body of [pquot_collapse_iso] is refused, "Universe <1>
 (...) is unbound" (N15).
 - The five refutations [pquot_empty_not_coequalizer],
 [pquot_coequalizer_needs_point], [no_pointed_coequalizer_at_empty],
 [no_pointed_elementary_coequalizers] and
 [empty_colimit_not_elementary] carry the file's only STRICT stdlib
 cap, [o < False_rect.u0], which is [Empty_Top]'s own (its About:
 [u < False_rect.u0]).
 - No constraint block carries an equation or mentions [Set].  [Set]
 occurs in the statements of nine constants, thirteen times by a
 word count over the About output of all 100 under
 Test/ProbeCollapse459.v's import list: eleven times in eight
 constants of the colimit form, and twice in the refutation
 [empty_colimit_not_elementary] ([colimit_apex@{Set h h h} L], in
 the binder of [e] and in the negated [IsWideCoequalizer]).  Each
 time it is at the slot of the shape's objects in an instance of
 the colimit vocabulary ([Cocone], [cocone_inj], [colimit_apex],
 [colimit_inj], [colimit_is_acolimit]): the objects of the wide
 shape are Instance/Parallel.v's [ParObj : Set].

 NOT DELIVERED.  A Prop-valued subset (refused as above); [Top^(2)] as
 a comma category, a Grothendieck construction or a displayed category
 over [Top]; the pushout for other topologies on A (argued above); an
 initial object of [Top_pointed], and the argument that a left adjoint
 must send the initial pair ⟨∅, ∅⟩ to it (not formalized, and not
 needed: the value of the adjoint built here at every pair is read
 directly as the coequalizer in the universal-arrow reading,
 [pquot_wide_coequalizer_colimit_quotient]); the uniqueness of left
 adjoints applied to [PairQuotient]; X/A, and its colimit form, for a
 pair whose subset is not closed under the points' equality, which the
 saturated relation above would give; any homotopy-theoretic use,
 relative homology among them; and the relocation of [Top_pointed]
 away from the reals. 

 --------
 Mac Lane，《为工作中的数学家而设的范畴》，第2版 (GTM 5)，§V.9，第134-135页（PDF第143-144页），阅读自页面图像：
 “如果我们考虑范畴 Top^(2)，其对象是对 ⟨X, A⟩（一个空间 X 及其子集 A），箭头 ⟨X, A⟩ → ⟨X', A'⟩ 是将 A 映射到 A' 的连续映射 X → X'，那么对于 Y 一个有基点的拓扑空间，X/A 的定义为：
 Top_*(X/A, Y) = Top^(2)(⟨X, A⟩, ⟨Y, *⟩)。
 因此映射 ⟨X, A⟩ ↦ X/A 是函子 Y ↦ ⟨Y, *⟩ 的左伴随函子，该函子将每个有基点的空间映射到对 ⟨Y, *⟩。”（目录ID maclane:V.9:construction6；书中未编号）
 nLab：https://ncatlab.org/nlab/show/Top
 nLab：https://ncatlab.org/nlab/show/pointed+object
 Wikipedia：https://en.wikipedia.org/wiki/Quotient_space_(topology)
 书籍：A. Hatcher，《代数拓扑》，剑桥大学出版社 (2002)，命题 2.22（良对）背景。空间的对（pairs of spaces）是相对同调存在的地方，而商空间（quotient）则是计算相对同调的方法：对于良对 (X, A)，商映射诱导同构从 (X, A) 的相对同调到 X/A 的约化同调（Hatcher，命题 2.22）。Mac Lane 的段落将塌缩（collapse）转化为对空间对的函子，并将其定义性质读取为态射集合的双射，因此 ⟨X, A⟩ ↦ X/A 是一个左伴随。目标是有基空间范畴（the category of pointed spaces），树的 [Top_pointed]（Instance/Top/Homotopy.v）。nLab 上关于基对象的页面记录了最简单的情况：基对象的遗忘函子有一个左伴随，即加入一个独立的基点，X ↦ X₊ = X ⊔ *。这是 Mac Lane 在空子集上的伴随，因为每个连续映射都将 ∅ 映入基点。在 A = ∅ 时，书中留下了一个选择，而一次阅读使它的两种构造一致。Mac Lane 对一对态射的等化子进行了初等定义（书第64页，PDF第73页，公式(6)：一个箭头 u : b → e 满足 uf = ug，且是普适的），将其解读为指向 Δ 的普适箭头（第65页，PDF第74页：“只是从 ⟨f, g⟩ 到函子 Δ 的普适箭头”），并且说任何集合的态射的等化子“定义方式相同”，所有内容均可从页面图像中阅读。这两种形式在每个非空集合上都一致；在空集合上，普适箭头是 a ⊔ b，而初等形式是 b。作为普适箭头来阅读时，阅读 p。135
 由于 Top_*(X/A, Y) 取 X/A 指向，他的 X/∅ 是 X ⊔ * 并且
 构造 5 和 6 在每个 A 上都一致
 ([pquot_wide_coequalizer_colimit])；从基本上阅读，如
 Structure/Coequalizer/Wide.v 的头文件读取，X/∅ 是 X 并且它们
 在那里分开。通用箭头是形状上的一个余极限，该形状以域 * 作为顶点，Wide.v 的 [WideCoequalizer] ：一个余锥既有来自 * 的支腿也有来自 X 的支腿，因此不需要 A 的点，并且在空族上来自 * 的支腿是不受限制的，这给出了 nLab 上述伴随的 X₊。下面的反驳是关于基本阅读的。该文件将 X/A 统一定义为 (X ⊔ {∗})/(A ∼ ∗)：其点为 [option X]、[None] 新点、[Some x] 与 [None] 在 x 位于 A ([pquot_rel]) 时相同，且采用 [TQuot] 的商拓扑，该拓扑来源于 Instance/Top/Subspace/TypeValued.v 沿 [Some] ([pquot_space])。不需要对 A 是否为空进行情况划分，这在此不可判定。其证明内容如下： - 它确实是点包含为 A 的共同等化子，可读作普遍箭头，对于每个 A，包括空集 A，在 A 的任何点（[pquot_wide_coequalizer_colimit]：一个 [WideCoequalizer] 精确属于构造 5 的族 [collapse_sub_family]，在 Instance/Top/Quotient.v 的 [collapse_colimit] 类型上）。它的顶点是 [pquot_space X]，它从 X 出发的腿是 [pquot_in X]，而它从 * 出发的腿将一点发送到左伴随的基点，所有这些都在 [eq_refl]（[pquot_wide_coequalizer_colimit_apex]，[pquot_wide_coequalizer_colimit_in]，[pquot_wide_coequalizer_colimit_base]）；左伴随的每一对底层空间都是那个顶点，在 [eq_refl]（[pquot_wide_coequalizer_colimit_quotient]），所以在这种解读下，Mac Lane 的两个构造给出了同一个空间。那个族的每一个余极限都有一个点，即 * 的像（[collapse_colimit_point]）。- 它是在 [Top]（[pquot_pushout]）中的推出 X ⊔_A ∗，通过将 A 的点（带离散拓扑）（[pair_sub_space]，[pair_sub_incl]）纳入并对映射到该点；顶点是 [pquot_space X]，在 [eq_refl]（[pquot_pushout_apex]）。上面的余极限通过并推的中介下降 [pquot_po_med]：一个余锥的两条腿是一个从 X 出发的映射和一个吸收 A 的点。离散拓扑是一种选择：在点的宇宙（Instance/Top/Subspace/TypeValued.v 的标题）上无法形成子空间拓扑，并且由于余锥条件或中介的连续性都不涉及 A 的拓扑，任何使包含映射连续的拓扑都会给出相同的并推（已论证，但未形式化）。- 给定 A 的一个点 [a0]，X ~> X/A 也是 A 的点包含的 ELEMENTARY 广共等化器（[pquot_coequalizer]），记录 [IsWideCoequalizer] 来自 Structure/Coequalizer/Wide.v，实例 Instance/Top/Quotient.v 的 [collapse_coequalizer] 对每个 A 都成立；因此当 A 有一个点（[pquot_collapse_iso], 由 [wide_coequalizer_unique] 得出）时，X/A 的两种读法在 [Top] 中同构，等距映射是 x ↦ [Some x] 一种方式，[Some x] ↦ x, [None] ↦ a0 另一种方式，在 [eq_refl]（[pquot_collapse_iso_to], [pquot_collapse_iso_from_some], [pquot_collapse_iso_from_none]）。它们作为有基点空间也是同构的：构造 5 中以 [a0] 为基点（[collapse_pointed]）的 X/A 在 [Top_pointed] 中同构于左伴随值 [fobj[PairQuotient] X]（[pquot_collapse_iso_pointed]）。- X/∅ 是 X₊：[pquot_empty_sum_iso] 将 ⟨X, ∅⟩（[empty_pair]）的 [pquot_space] 与 Instance/Top/Coproduct.v 中的 [Sum_Top X Point_Top] 在 [Top] 中、[Some x] ↦ [inl x] 和 [None] ↦ [inr ttt] 于 [eq_refl]（[pquot_empty_sum_iso_some]，[pquot_empty_sum_iso_none]）对应起来，这是一个同构，但在 [eq_refl] 被拒绝作为空间的方程（Test/ProbeCollapse459.v 的 N16）；新点是 new（[pquot_empty_new_point]）。因此，作为通用箭头解读，空族的余等化子是 X ⊔ *（[pquot_wide_coequalizer_colimit_empty]，即⟨X, ∅⟩ 对 [Sum_Top X Point_Top] 的余极点）。在 A = ∅ 的初等阅读中。[IsWideCoequalizer]，书第 64 页显示（6）扩展到一组映射，表示为仅从 X 出发的等化箭头。在空族上，其条件是空洞的，并且它确定了 X 本身（Instance/Top/Quotient.v 的 [collapse_empty_iso]，X/∅ ≅ X），其中余极限是 X ⊔ *：这是 Structure/Coequalizer/Wide.v 标题记录的两种形式之间的间隙（[wide_coround_trip_needs_point]）。在 X = ∅ 时，空族的任何初等宽等化箭头都没有点，无论其构造如何（Quotient.v 的 [empty_wide_coequalizer_pointless]）。这里的反驳是关于该基本阅读的陈述，在该阅读下，构造 5 和 6 在 A = ∅ 时分开，这是书中未涉及的情况：没有一个有底点空间的底空间是空族在 ∅ 处的基本广等化器 ([no_pointed_coequalizer_at_empty])；因此，将每对赋予一个有底点空间，无论是函子还是对象上的任何其他函数，都不能使每个底空间成为点包含的基本广等化器 ([no_pointed_elementary_coequalizers])；该文件的 X/A 在 ⟨∅, ∅⟩ 处不是一个，因此 [pquot_coequalizer] 的 A 点不能被去掉 ([pquot_empty_not_coequalizer], [pquot_coequalizer_needs_point])；并且在 ⟨∅, ∅⟩ 处，没有任何余极点携带一个 ([empty_colimit_not_elementary])，正如那个标题所说的一般情况下它们分开的两种形式在 [Top] 处分开。没有使用左伴随的唯一性或 [Top_pointed] 的初始对象。配对的范畴。[PairTop]：一个在其点上具有类型值谓词并且尊重它们相等性的空间（[pair_sub_proper]）。[PairMap]：一个将子集映射到子集的连续映射；hom-集体是 [Top] 对底层映射自身的阅读，就像 Instance/Top/Homotopy.v 的 [PointedMap_Setoid] 一样，所以 [Top_pairs] 拥有 [Top_pointed] 的形状。关于这两个选择的相关内容固定在 Test/ProbeCollapse459.v 中，它承载了此文件的导入列表。- 类型（Type），而不是命题（Prop），是由 ⟨Y, *⟩ 强制的。书中的 ⟨Y, *⟩ 是谓词 y ≈ y0，其值是一个空间点的类型值相等性；作为命题值谓词时会被拒绝，“项 'y ≈ ptop_pt Y' 的类型是 'Type'，而期望类型是 'Prop'”（探针 N10）。作为一个 Prop 它必须被压缩，[inhabited (y ≈ y0)]，而转置需要它未压缩（[pquot_from_map] 的情况 [Some x] ∼ [None]）；未压缩操作被拒绝，“在归纳类型 'inhabited' 中错误地消除了 'H'：返回类型的 sort 是 'Type'，而它应该是 SProp 或 Prop”（N11）。控制：消除到 [inhabited (y ≈ y0)] 是被接受的。- respect 字段是一个设计选择，而不是必需的。一个集合族的子集在点的等价下被取闭合，集合族对 Mac Lane 的“subset”的解读：在空间中相等的点是其中的一个点。另一种方法是放弃该域，并在识别中对 A 进行饱和，如 Instance/Top/Quotient.v 的 [collapse_image] 所做：在 [option X] 上的相同四种情况关系中，对 A 进行饱和，即用相当于 A 的点替代 A，这是一个没有域的等价关系（Test/ProbeCollapse459.v 的 [p459_sat_rel_Equivalence]，在全局上下文下封闭）。关于该域的测量只涉及未饱和关系 [pquot_rel]：没有该域它不是传递的，在 [bool] 上使用完全相等并设 A := (= true)，[Some false] ∼ [Some true] ∼ [None]，而 [Some false] ≁ [None]（探针的 [p459_unsat_rel_not_transitive]，在全局上下文下封闭）。伴随。[PointPair] 将 Y 发送到 ⟨Y, *⟩；[PairQuotient] 将 ⟨X, A⟩ 发送到指向 [None] 的 X/A，并将映射 f 发送到 [Some x] ↦ [Some (f x)], [None] ↦ [None]。[pairs_quotient_iso X Y] 是书中作为 [Isomorphism] 在 [Sets] 中的显示；它的“=”在 [eq_refl] 处被拒绝，作为同类型方程（Test/ProbeCollapse459.v 的 N12）。[pquot_to] 沿着 [Some] 进行限制，[pquot_from] 通过将 [None] 发送到基点进行扩展，其连续性来源于 [TQuot] 的泛性质。[pairs_quotient_adjunction]（问题的固定名称）在其上为 [Build_Adjunction']，两点自然性方格逐点自反；单位为 x ↦ [Some x]，对单位 [Some y] ↦ y，[None] ↦ 基点。这是 [Adjunction] 在 [Top] 中的记录，其中 Instance/Top/Subspace/TypeValued.v 的切分商伴随被拒绝，因为 [Adjunction] 标识了其两个范畴的同态层次（Theory/Adjunction.v，关于：[h1 = h2]），而在这里 [Top_pointed@{h o}] 和 [Top_pairs@{h o}] 的同态都位于 [h]。

 实数。[Top_pointed] 位于 Instance/Top/Homotopy.v 中，该文件需要 stdlib 实数并打开 [R_scope]；这个文件通过该导入访问它们，就像 Instance/Top/Wedge.v 一样，并且这里的每个常量仍然显示“在全局上下文下封闭”。基于这个原因，关系 [pquot_rel] 在 [%type] 下书写。将 [PointedTop] 和 [Top_pointed] 移动到不包含实数的文件中由维护者负责。优势。在 [eq_refl] ： [PointPair_sub] ， [pquot_space_carrier] ， [pquot_basepoint] ， [pquot_space_open] ， [pquot_to_eval] ， [pquot_from_eval_some] ， [pquot_from_eval_none] ， [pairs_quotient_unit_eval] ， [pairs_quotient_counit_some] ， [pairs_quotient_counit_none] ， [pairs_quotient_adj_is] （该伴随的 Hom 集同构是 [pairs_quotient_iso] ），[pquot_pushout_apex] ，余极限 [pquot_wide_coequalizer_colimit] 的四个回读（它的顶点、它的两条腿和左伴随的基础空间）、三个 [pquot_collapse_iso] 回读和两个 [pquot_empty_sum_iso] 回读。到 [≈] ：范畴和函子律、同构律、自然性方格和普遍性性质。十一 [Defined]，按记号计数，每一个承重：每个封闭的 [Qed] 单独在一个草稿副本中留下一个被拒绝的命名常量——[point_pair_map]（[PointPair] 的第一个义务），[pquot_fmap_map]（[pquot_fmap_cont]），[pquot_to]（[pairs_quotient_iso] 的第一个义务），[pquot_from_map]（[pquot_from]），[pairs_quotient_adjunction]（[pairs_quotient_unit_eval]，“无法统一 'unit x' 和 'Some x'”），[pquot_po_map]（[pquot_po_med]），[pquot_pushout]（[pquot_pushout_apex]），[pquot_coequalizer]（[pquot_collapse_iso_from_some]），[pquot_empty_sum_to] 和 [pquot_empty_sum_from]（[pquot_empty_sum_iso]），[pquot_empty_sum_iso]（[pquot_empty_sum_iso_some]）。UNIVERSES，由 [About] 在 [Set Printing Universes] 下读取本文件 [Print Module] 列表中的所有 100 个常量（两个记录、它们的构造函数和投影，以及包含的十四个 [Program] 义务）。绑定顺序：[@{h o ...}]，[Top@{h o}] 的顺序，除了重新陈述构造 5 的宽余共化对象词汇的常量，它们保留 Instance/Top/Quotient.v 的 [@{o h ...}]，因此像它们读取的常量一样实例化（余极限形式，[pquot_wide_legs] 到 [pquot_wide_coequalizer_colimit_quotient] 和 [pquot_wide_coequalizer_colimit_empty]，其中 [collapse_colimit_point]；[pquot_coequalizer]，[pquot_collapse_iso] 及其三个回读以及 [pquot_collapse_iso_pointed]；以及反驳 [pquot_empty_not_coequalizer]、[pquot_coequalizer_needs_point]、[no_pointed_coequalizer_at_empty]、[no_pointed_elementary_coequalizers] 和 [empty_colimit_not_elementary]）。- 没有提到 [Top] 的箭头的常数（[PairTop]、它的构造函数和投影，[point_pair]，[pquot_rel] 到 [pquot_pointed]，[pquot_space_open]，[pair_sub_setoid] 及其 [Equivalence]、[pair_sub_space]、[pair_sub_incl_map]、[empty_pair]、[pquot_empty_new_point]、[pquot_empty_sum_to]、[pquot_empty_sum_from] 和 [collapse_pointed]）：[@{o}]，不超过 stdlib 限制的约束；X/A 是 [TopSpace@{o}]，在 X 的宇宙中。- [PairMap]、[Top_pairs]、[PointPair]、[PairQuotient] 及其之间的映射，截面常数 [pquot_po_map] 和 [pquot_po_med] 以及 [pquot_empty_sum_iso] 与它们之间的两个回读：[@{h o}] 具有 [o < h] 和 stdlib 限制；[Top_pairs@{h o} : Category@{h h h}]，[Top_pointed@{u u0}] 的形状（关于：[Category@{u u u}]，[u0 < u]）。- 共极限形式（[pquot_wide_legs]、[pquot_wide_legs_coherence]、[pquot_wide_cocone]、[pquot_wide_ump]、[pquot_wide_coequalizer_colimit]及其四个读回，以及[pquot_wide_coequalizer_colimit_empty]和[collapse_colimit_point]）：[@{o h}] 配置有 [o < h] 和 stdlib 上限；该共极限是 [WideCoequalizer@{h h}] 的 [AWide@{h h h h h} (collapse_sub_family@{o h} X (pair_sub X))]，Instance/Top/Quotient.v 的 [collapse_colimit@{o h}] 在 A := [pair_sub X]（两者均关于 About）。 - [pairs_quotient_iso@{h o u}]：[o < h] 和 [h < u]，[Sets@{h u}] 中的 [Isomorphism]，其对象为 [h] 的 Hom-集合，位于 [u]。[pairs_quotient_adjunction@{h o u v}]：相同的两个界限，[v] 不在任何约束中。[v] 是 [Adjunction] 自身的 binder [sp] 的 [Adjunction@{o1 h1 p1 o2 h2 p2 o3 p3 so sh sp}]，这在该记录的 About 块中没有出现在任何约束中。该陈述写为 [Adjunction@{h h h h h h h h u h v}]：同一 [Build_Adjunction'] 项通过符号 [⊣] 在闭合的绑定器下声明，[v] 在其中命名，在陈述时被拒绝，“Universe <1> (...) 是未绑定的”（Test/ProbeCollapse459.v 的 N13），而完成的常数通过 [⊣] 读取一次绑定器命名 [v]，并且在未命名时被拒绝（N14 及其控制）。- [pquot_coequalizer]，[pquot_empty_not_coequalizer]，[pquot_coequalizer_needs_point]，[no_pointed_coequalizer_at_empty]，[no_pointed_elementary_coequalizers] 和 [empty_colimit_not_elementary]：[@{o h i}] 具有 [o < h] 和 [o <= i]，即 Instance/Top/Quotient.v 的标题的灵活索引（它的 W-c）。[pquot_collapse_iso@{o h u}] 和 [pquot_collapse_iso_pointed@{o h u}] ： [u] 是 [wide_coequalizer_unique] 自身的绑定器，如同那个文件中；随着 [u] 被删除，[pquot_collapse_iso] 的主体被拒绝，“宇宙 <1> (...) 未绑定” (N15)。- 这五个驳斥 [pquot_empty_not_coequalizer]、[pquot_coequalizer_needs_point]、[no_pointed_coequalizer_at_empty]、[no_pointed_elementary_coequalizers] 和 [empty_colimit_not_elementary] 承载了该文件唯一的严格标准库权限 [o < False_rect.u0]，这属于 [Empty_Top] 自身（其关于：[u < False_rect.u0]）。- 没有约束块承载方程或提及 [Set]。[Set] 出现在九个常量的声明中，通过对 Test/ProbeCollapse459.v 的导入列表下的全部 100 个输出的字数统计，共出现十三次：在八个 colimit 形式的常量中出现了十一遍，在反驳 [empty_colimit_not_elementary] 中出现两次（在 [colimit_apex@{Set h h h} L] 中，出现在 [e] 的绑定器中以及在否定的 [IsWideCoequalizer] 中）。每一次，它都出现在 colimit 词汇实例中形状对象的槽位上（[Cocone]，[cocone_inj]，[colimit_apex]，[colimit_inj]，[colimit_is_acolimit]）：宽形状的对象是 Instance/Parallel.v 的 [ParObj : Set]。未交付。一个 Prop 值的子集（如上所述被拒绝）；[Top^(2)] 作为逗号范畴、Grothendieck 构造或 [Top] 上的显示范畴；A 上其他拓扑的推挤（如上所述）；[Top_pointed] 的初始对象，以及一个左伴随必须将初始对 ⟨∅, ∅⟩ 发送到它的论证（未形式化，也不需要：此处构建的伴随在每一对上的值可直接作为普适箭头读法中的共同等化器 [pquot_wide_coequalizer_colimit_quotient]）；应用于 [PairQuotient] 的左伴随唯一性；X/A 及其余极形式，对于其子集不对点的相等性封闭的对，上述饱和关系会给出；任何同伦理论的用途，其中包括相对同调；以及将 [Top_pointed] 从实数上移开。
*)

#[local] Obligation Tactic := idtac.

(* * ** The category of pairs [Top^(2)] / * ** 配对类别 [Top^(2)] *)

(* A space with a subset of its points; the subset is a Type-valued predicate that respects the points' equality. / 一个包含其部分点的空间；该子集是一个类型值的谓词，遵循点的相等性。 *)
Record PairTop@{o} := {
  pair_space :> TopSpace@{o};
  pair_sub : carrier (top_carrier pair_space) → Type@{o};
  pair_sub_proper : ∀ x y, x ≈ y → pair_sub x → pair_sub y
}.

(* A map of pairs: a continuous map carrying the subset into the subset. / 对的映射：将子集映射到子集的连续映射。 *)
Record PairMap@{h o | o < h +} (X Y : PairTop@{o}) := {
  pair_map :> pair_space X ~{Top@{h o}}~> pair_space Y;
  pair_carries : ∀ x, pair_sub X x → pair_sub Y (pair_map x)
}.

Arguments pair_map {X Y} _.
Arguments pair_carries {X Y} _ _ _.

(* The hom-setoid is [Top]'s own, read on the underlying maps, as Instance/Top/Homotopy.v's [PointedMap_Setoid] is. / 同态集是 [Top] 自己的，在底层映射上读取，就像 Instance/Top/Homotopy.v 的 [PointedMap_Setoid] 一样。 *)
Lemma PairMap_equiv_Equivalence@{h o | o < h +} {X Y : PairTop@{o}} :
  Equivalence (fun p q : PairMap@{h o} X Y => pair_map p ≈ pair_map q).
Proof.
  constructor.
  - intro p; reflexivity.
  - intros p q Hpq; symmetry; exact Hpq.
  - intros p q r Hpq Hqr.
    transitivity (pair_map q); [ exact Hpq | exact Hqr ].
Qed.

#[export]
Instance PairMap_Setoid@{h o | o < h +} {X Y : PairTop@{o}} :
  Setoid@{h h} (PairMap@{h o} X Y) := {|
  equiv := fun p q => pair_map p ≈ pair_map q;
  setoid_equiv := PairMap_equiv_Equivalence@{h o}
|}.

Definition pair_id@{h o | o < h +} {X : PairTop@{o}} : PairMap@{h o} X X :=
  @Build_PairMap@{h o} X X (@id Top@{h o} (pair_space X)) (fun x a => a).

Definition pair_compose@{h o | o < h +} {X Y Z : PairTop@{o}}
  (p : PairMap@{h o} Y Z) (q : PairMap@{h o} X Y) : PairMap@{h o} X Z :=
  @Build_PairMap@{h o} X Z (pair_map p ∘[Top@{h o}] pair_map q)
    (fun x a => pair_carries p _ (pair_carries q x a)).

Lemma pair_compose_respects@{h o | o < h +} {X Y Z : PairTop@{o}} :
  Proper (equiv ==> equiv ==> equiv) (@pair_compose@{h o} X Y Z).
Proof.
  intros p p' Hp q q' Hq x; simpl.
  transitivity (pair_map p (pair_map q' x)).
  - apply proper_morphism; exact (Hq x).
  - exact (Hp (pair_map q' x)).
Qed.

(*
 Mac Lane's [Top^(2)].

 objects: pairs ⟨X, A⟩         (a space with a subset of its points)
 arrows: maps carrying A into A'
 identity: the identity map
 composition: composition of continuous maps 

 --------
 Mac Lane 的 [Top^(2)]。

 对象：对 ⟨X, A⟩ （一个带有子集的空间）
 箭头：将 A 映射到 A' 的映射
 恒等：恒等映射
 复合：连续映射的复合
*)
Program Definition Top_pairs@{h o | o < h +} : Category@{h h h} := {|
  obj     := PairTop@{o};
  hom     := PairMap@{h o};
  homset  := @PairMap_Setoid@{h o};
  id      := @pair_id@{h o};
  compose := @pair_compose@{h o};

  compose_respects := @pair_compose_respects@{h o}
|}.
Next Obligation. intros X Y f x; simpl. reflexivity. Qed.
Next Obligation. intros X Y f x; simpl. reflexivity. Qed.
Next Obligation. intros X Y Z W f g k x; simpl. reflexivity. Qed.
Next Obligation. intros X Y Z W f g k x; simpl. reflexivity. Qed.

(* * ** The underlying pair of a pointed space / * ** 尖点空间的基础对 *)

(* ⟨Y, *⟩: the subset is the basepoint, up to the points' equality. / ⟨Y, *⟩：这个子集是基点，直到点的相等为止。 *)
Definition point_pair@{o} (Y : PointedTop@{o}) : PairTop@{o} :=
  @Build_PairTop@{o} (ptop_space Y) (fun y => y ≈ ptop_pt Y)
    (fun x y e h => transitivity (symmetry e) h).

Definition point_pair_map@{h o | o < h +} {X Y : PointedTop@{o}}
  (p : X ~{Top_pointed@{h o}}~> Y) :
  point_pair X ~{Top_pairs@{h o}}~> point_pair Y.
Proof.
  refine (@Build_PairMap@{h o} (point_pair X) (point_pair Y) (ptop_map p) _).
  intros x Hx; simpl in *.
  transitivity (ptop_map p (ptop_pt X)).
  - apply proper_morphism; exact Hx.
  - exact (ptop_preserves p).
Defined.

(* Y ↦ ⟨Y, *⟩. *)
Program Definition PointPair@{h o | o < h +} :
  Top_pointed@{h o} ⟶ Top_pairs@{h o} := {|
  fobj := point_pair@{o};
  fmap := @point_pair_map@{h o}
|}.
Next Obligation. intros X Y f g Hfg x; simpl. exact (Hfg x). Qed.
Next Obligation. intros X x; simpl. reflexivity. Qed.
Next Obligation. intros X Y Z f g x; simpl. reflexivity. Qed.

(* * ** The quotient X/A of a pair: (X ⊔ {∗}) / (A ∼ ∗) / * ** 一对的商： (X ⊔ {∗}) / (A ∼ ∗) *)

(* The points are those of X and one new point [None]; a point of X is identified with [None] exactly when it lies in A. / 这些点是 X 的点和一个新点 [None]；当 X 的一个点位于 A 中时，它与 [None] 恰好对应。 *)
Definition pquot_rel@{o} (X : PairTop@{o})
  (u v : option (carrier (top_carrier (pair_space X)))) : Type@{o} :=
  match u, v with
  | Some x, Some y => ((x ≈ y) + (pair_sub X x ∧ pair_sub X y))%type
  | Some x, None => pair_sub X x
  | None, Some y => pair_sub X y
  | None, None => poly_unit@{o}
  end.

Lemma pquot_rel_Equivalence@{o} (X : PairTop@{o}) :
  Equivalence (pquot_rel X).
Proof.
  constructor.
  - intros [x|]; simpl; [left; reflexivity | exact ttt].
  - intros [x|] [y|] H; simpl in *; try exact H.
    destruct H as [H|[H1 H2]]; [left; now symmetry | right; exact (H2, H1)].
  - intros [x|] [y|] [z|] H1 H2; simpl in *; try exact ttt.
    + destruct H1 as [H1|[H1 H1']], H2 as [H2|[H2 H2']].
      * left; now transitivity y.
      * right; split;
          [ exact (pair_sub_proper X _ _ (symmetry H1) H2) | exact H2' ].
      * right; split; [ exact H1 | exact (pair_sub_proper X _ _ H2 H1') ].
      * right; exact (H1, H2').
    + destruct H1 as [H1|[H1 H1']].
      * exact (pair_sub_proper X _ _ (symmetry H1) H2).
      * exact H1.
    + right; exact (H1, H2).
    + exact H1.
    + destruct H2 as [H2|[H2 H2']].
      * exact (pair_sub_proper X _ _ H2 H1).
      * exact H2'.
    + exact H2.
Qed.

Definition pquot_setoid@{o} (X : PairTop@{o}) :
  Setoid@{o o} (option (carrier (top_carrier (pair_space X)))) := {|
  equiv := pquot_rel X;
  setoid_equiv := pquot_rel_Equivalence X
|}.

Definition pquot_carrier@{o} (X : PairTop@{o}) : SetoidObject@{o o} := {|
  carrier := option (carrier (top_carrier (pair_space X)));
  is_setoid := pquot_setoid X
|}.

Definition pquot_some@{o} (X : PairTop@{o}) :
  SetoidMorphism@{o o o} (top_carrier (pair_space X)) (pquot_carrier X) :=
  @Build_SetoidMorphism _ (is_setoid (top_carrier (pair_space X))) _
    (pquot_setoid X) (@Some _)
    (fun x y (e : x ≈ y) => (inl e : pquot_rel X (Some x) (Some y))).

(* X/A: the quotient topology of Instance/Top/Subspace/TypeValued.v along [Some], so an open is a predicate respecting the identification whose restriction to X is open. / X/A：沿着 [Some] 在 Instance/Top/Subspace/TypeValued.v 上的商拓扑，所以一个开集是一个遵守该同一性的谓词，其在 X 上的限制是开集。 *)
Definition pquot_space@{o} (X : PairTop@{o}) : TopSpace@{o} :=
  TQuot (pair_space X) (pquot_carrier X) (pquot_some X).

Definition pquot_pointed@{o} (X : PairTop@{o}) : PointedTop@{o} :=
  @Build_PointedTop@{o} (pquot_space X) None.

Definition pquot_in@{h o | o < h +} (X : PairTop@{o}) :
  pair_space X ~{Top@{h o}}~> pquot_space X :=
  tquot_proj (pair_space X) (pquot_carrier X) (pquot_some X).

(** ** The functor ⟨X, A⟩ ↦ X/A / ** 函子 ⟨X, A⟩ ↦ X/A *)

Definition pquot_fmap_map@{h o | o < h +} {X Y : PairTop@{o}}
  (f : X ~{Top_pairs@{h o}}~> Y) :
  SetoidMorphism@{o o o} (pquot_carrier X) (pquot_carrier Y).
Proof.
  unshelve notypeclasses refine
    (@Build_SetoidMorphism _ (pquot_setoid X) _ (pquot_setoid Y)
       (fun u => match u with
                 | Some x => Some (pair_map f x)
                 | None => None
                 end) _).
  intros [x|] [y|] H; simpl in *; try exact H.
  - destruct H as [H|[H1 H2]].
    + left; apply proper_morphism; exact H.
    + right; exact (pair_carries f _ H1, pair_carries f _ H2).
  - exact (pair_carries f _ H).
  - exact (pair_carries f _ H).
Defined.

Lemma pquot_fmap_cont@{h o | o < h +} {X Y : PairTop@{o}}
  (f : X ~{Top_pairs@{h o}}~> Y) :
  Continuous (pquot_space X) (pquot_space Y) (pquot_fmap_map f).
Proof.
  intros V [HVp HVo]; split.
  - intros u v e w.
    exact (HVp _ _ (proper_morphism (pquot_fmap_map f) u v e) w).
  - exact (continuity (pair_map f) _ HVo).
Qed.

Definition pquot_fmap@{h o | o < h +} {X Y : PairTop@{o}}
  (f : X ~{Top_pairs@{h o}}~> Y) :
  pquot_pointed X ~{Top_pointed@{h o}}~> pquot_pointed Y :=
  @Build_PointedMap@{h o} (pquot_pointed X) (pquot_pointed Y)
    (@Build_ContinuousMorphism@{h o} (pquot_space X) (pquot_space Y)
       (pquot_fmap_map f) (pquot_fmap_cont f))
    ttt.

Program Definition PairQuotient@{h o | o < h +} :
  Top_pairs@{h o} ⟶ Top_pointed@{h o} := {|
  fobj := pquot_pointed@{o};
  fmap := @pquot_fmap@{h o}
|}.
Next Obligation.
  intros X Y f g Hfg [x|]; simpl; [ left; exact (Hfg x) | exact ttt ].
Qed.
Next Obligation. intros X [x|]; simpl; [ left; reflexivity | exact ttt ]. Qed.
Next Obligation.
  intros X Y Z f g [x|]; simpl; [ left; reflexivity | exact ttt ].
Qed.

(* * ** The hom-set bijection Top_*(X/A, Y) ≅ Top^(2)(⟨X, A⟩, ⟨Y, *⟩) / * ** 同态集双射 Top_*(X/A, Y) ≅ Top^(2)(⟨X, A⟩, ⟨Y, *⟩) *)

(* Restrict a based map out of X/A along [Some]. / 沿着 [Some] 从 X/A 限制基于地图的地图。 *)
Definition pquot_to@{h o | o < h +} (X : PairTop@{o}) (Y : PointedTop@{o})
  (p : pquot_pointed X ~{Top_pointed@{h o}}~> Y) :
  X ~{Top_pairs@{h o}}~> point_pair Y.
Proof.
  refine (@Build_PairMap@{h o} X (point_pair Y)
            (ptop_map p ∘[Top@{h o}] pquot_in X) _).
  intros x Hx; simpl.
  transitivity (ptop_map p None).
  - apply (proper_morphism (continuous_map (ptop_map p)) (Some x) None).
    exact Hx.
  - exact (ptop_preserves p).
Defined.

(* Extend a map of pairs by sending the new point to the basepoint. / 通过将新点发送到基点来扩展一对的映射。 *)
Definition pquot_from_map@{h o | o < h +} (X : PairTop@{o})
  (Y : PointedTop@{o}) (g : X ~{Top_pairs@{h o}}~> point_pair Y) :
  SetoidMorphism@{o o o} (pquot_carrier X) (top_carrier (ptop_space Y)).
Proof.
  unshelve notypeclasses refine
    (@Build_SetoidMorphism _ (pquot_setoid X) _
       (is_setoid (top_carrier (ptop_space Y)))
       (fun u => match u with
                 | Some x => pair_map g x
                 | None => ptop_pt Y
                 end) _).
  intros [x|] [y|] H; simpl in *.
  - destruct H as [H|[H1 H2]].
    + apply proper_morphism; exact H.
    + transitivity (ptop_pt Y).
      * exact (pair_carries g _ H1).
      * symmetry; exact (pair_carries g _ H2).
  - exact (pair_carries g _ H).
  - symmetry; exact (pair_carries g _ H).
  - reflexivity.
Defined.

Definition pquot_from@{h o | o < h +} (X : PairTop@{o}) (Y : PointedTop@{o})
  (g : X ~{Top_pairs@{h o}}~> point_pair Y) :
  pquot_pointed X ~{Top_pointed@{h o}}~> Y :=
  @Build_PointedMap@{h o} (pquot_pointed X) Y
    (tquot_desc (pair_space X) (pquot_carrier X) (pquot_some X)
       (ptop_space Y) (pair_map g) (pquot_from_map X Y g)
       (fun x => reflexivity _))
    (reflexivity _).

Program Definition pairs_quotient_iso@{h o u | o < h, h < u +}
  (X : PairTop@{o}) (Y : PointedTop@{o}) :
  @Isomorphism Sets@{h u}
    {| carrier := @hom Top_pointed@{h o} (PairQuotient@{h o} X) Y;
       is_setoid := @homset Top_pointed@{h o} (PairQuotient@{h o} X) Y |}
    {| carrier := @hom Top_pairs@{h o} X (PointPair@{h o} Y);
       is_setoid := @homset Top_pairs@{h o} X (PointPair@{h o} Y) |} := {|
  to   := {| morphism := pquot_to@{h o} X Y |};
  from := {| morphism := pquot_from@{h o} X Y |}
|}.
Next Obligation. intros X Y p q H x; exact (H (Some x)). Qed.
Next Obligation.
  intros X Y p q H [x|]; simpl; [ exact (H x) | reflexivity ].
Qed.
Next Obligation. intros X Y g x; reflexivity. Qed.
Next Obligation.
  intros X Y p [x|]; simpl;
    [ reflexivity | symmetry; exact (ptop_preserves p) ].
Qed.

(* Construction 6: ⟨X, A⟩ ↦ X/A is left adjoint to Y ↦ ⟨Y, *⟩. / 构造6：⟨X, A⟩ ↦ X/A 是 Y ↦ ⟨Y, *⟩ 的左伴随。 *)
Definition pairs_quotient_adjunction@{h o u v | o < h, h < u +} :
  @Adjunction@{h h h h h h h h u h v} Top_pointed@{h o} Top_pairs@{h o}
    PairQuotient@{h o} PointPair@{h o}.
Proof.
  unshelve eapply (@Build_Adjunction' Top_pointed@{h o} Top_pairs@{h o}
                     PairQuotient@{h o} PointPair@{h o}
                     pairs_quotient_iso@{h o u}).
  - intros X Y Z f g x; reflexivity.
  - intros X Y Z f g x; reflexivity.
Defined.

(** ** Readbacks / ** 回读 *)

Example PointPair_sub@{h o | o < h +} (Y : PointedTop@{o})
  (y : carrier (top_carrier (ptop_space Y))) :
  pair_sub (fobj[PointPair@{h o}] Y) y = (y ≈ ptop_pt Y) := eq_refl.

Example pquot_space_carrier@{h o | o < h +} (X : PairTop@{o}) :
  carrier (top_carrier (ptop_space (fobj[PairQuotient@{h o}] X)))
    = option (carrier (top_carrier (pair_space X))) := eq_refl.

Example pquot_basepoint@{h o | o < h +} (X : PairTop@{o}) :
  ptop_pt (fobj[PairQuotient@{h o}] X) = None := eq_refl.

Example pquot_space_open@{o} (X : PairTop@{o})
  (V : pquot_carrier X → Type@{o}) :
  IsOpen (pquot_space X) V
    = tquot_open (pair_space X) (pquot_carrier X) (pquot_some X) V
  := eq_refl.

Example pquot_to_eval@{h o | o < h +} (X : PairTop@{o}) (Y : PointedTop@{o})
  (p : pquot_pointed X ~{Top_pointed@{h o}}~> Y)
  (x : carrier (top_carrier (pair_space X))) :
  continuous_map (pair_map (pquot_to X Y p)) x
    = continuous_map (ptop_map p) (Some x) := eq_refl.

Example pquot_from_eval_some@{h o | o < h +} (X : PairTop@{o})
  (Y : PointedTop@{o}) (g : X ~{Top_pairs@{h o}}~> point_pair Y)
  (x : carrier (top_carrier (pair_space X))) :
  continuous_map (ptop_map (pquot_from X Y g)) (Some x)
    = continuous_map (pair_map g) x := eq_refl.

Example pquot_from_eval_none@{h o | o < h +} (X : PairTop@{o})
  (Y : PointedTop@{o}) (g : X ~{Top_pairs@{h o}}~> point_pair Y) :
  continuous_map (ptop_map (pquot_from X Y g)) None = ptop_pt Y := eq_refl.

Example pairs_quotient_unit_eval@{h o u v | o < h, h < u +}
  (X : PairTop@{o}) (x : carrier (top_carrier (pair_space X))) :
  continuous_map
    (pair_map (@unit _ _ _ _ pairs_quotient_adjunction@{h o u v} X)) x
    = Some x := eq_refl.

Example pairs_quotient_counit_some@{h o u v | o < h, h < u +}
  (Y : PointedTop@{o}) (y : carrier (top_carrier (ptop_space Y))) :
  continuous_map
    (ptop_map (@counit _ _ _ _ pairs_quotient_adjunction@{h o u v} Y)) (Some y)
    = y := eq_refl.

Example pairs_quotient_counit_none@{h o u v | o < h, h < u +}
  (Y : PointedTop@{o}) :
  continuous_map
    (ptop_map (@counit _ _ _ _ pairs_quotient_adjunction@{h o u v} Y)) None
    = ptop_pt Y := eq_refl.

Example pairs_quotient_adj_is@{h o u v | o < h, h < u +} (X : PairTop@{o})
  (Y : PointedTop@{o}) :
  @adj _ _ _ _ pairs_quotient_adjunction@{h o u v} X Y
    = pairs_quotient_iso@{h o u} X Y := eq_refl.

(** ** X/A is the pushout X ⊔_A ∗ / ** X/A 是推挤 X ⊔_A ∗ *)

(* The points of A, with the equality of X, as a discrete space. / A 的点，具有 X 的等式，作为一个离散空间。 *)
Lemma pair_sub_equiv_Equivalence@{o} (X : PairTop@{o}) :
  Equivalence (fun a b : collapse_sub_points (pair_space X) (pair_sub X) =>
                 projT1 a ≈ projT1 b).
Proof.
  constructor.
  - intro a; reflexivity.
  - intros a b H; symmetry; exact H.
  - intros a b c H1 H2; transitivity (projT1 b); assumption.
Qed.

Definition pair_sub_setoid@{o} (X : PairTop@{o}) : SetoidObject@{o o} := {|
  carrier := collapse_sub_points (pair_space X) (pair_sub X);
  is_setoid := {| equiv := fun a b => projT1 a ≈ projT1 b;
                  setoid_equiv := pair_sub_equiv_Equivalence X |}
|}.

Definition pair_sub_space@{o} (X : PairTop@{o}) : TopSpace@{o} :=
  Discrete_Top (pair_sub_setoid X).

Definition pair_sub_incl_map@{o} (X : PairTop@{o}) :
  SetoidMorphism@{o o o} (pair_sub_setoid X) (top_carrier (pair_space X)) :=
  @Build_SetoidMorphism _ (is_setoid (pair_sub_setoid X)) _
    (is_setoid (top_carrier (pair_space X))) (@projT1 _ _)
    (fun a b (e : projT1 a ≈ projT1 b) => e).

Definition pair_sub_incl@{h o | o < h +} (X : PairTop@{o}) :
  pair_sub_space X ~{Top@{h o}}~> pair_space X :=
  @Build_ContinuousMorphism@{h o} (pair_sub_space X) (pair_space X)
    (pair_sub_incl_map X)
    (out_of_discrete_continuous _ (pair_space X) (pair_sub_incl_map X)).

(* The new point, as a map from the one-point space. / 新的点，作为从单点空间映射而来。 *)
Definition pquot_base@{h o | o < h +} (X : PairTop@{o}) :
  Point_Top@{o} ~{Top@{h o}}~> pquot_space X :=
  top_point@{h o} (pquot_space X) None.

Section Pushout.

Universes h o.
Constraint o < h.

Context (X : PairTop@{o}) {Q : Top@{h o}}
  (q1 : pair_space X ~{Top@{h o}}~> Q) (q2 : Point_Top@{o} ~{Top@{h o}}~> Q)
  (Hq : q1 ∘ pair_sub_incl X ≈ q2 ∘ top_one (pair_sub_space X)).

Definition pquot_po_map : SetoidMorphism@{o o o} (pquot_carrier X) Q.
Proof using X Q q1 q2 Hq.
  unshelve notypeclasses refine
    (@Build_SetoidMorphism _ (pquot_setoid X) _ (is_setoid (top_carrier Q))
       (fun u => match u with
                 | Some x => continuous_map q1 x
                 | None => continuous_map q2 ttt
                 end) _).
  assert (HA : ∀ x, pair_sub X x → q1 x ≈ q2 ttt).
  { intros x Hx. exact (Hq (x; Hx)). }
  intros [x|] [y|] H; simpl in *.
  - destruct H as [H|[H1 H2]].
    + apply proper_morphism; exact H.
    + transitivity (q2 ttt); [ exact (HA x H1) | symmetry; exact (HA y H2) ].
  - exact (HA x H).
  - symmetry; exact (HA y H).
  - reflexivity.
Defined.

Definition pquot_po_med : pquot_space X ~{Top@{h o}}~> Q :=
  tquot_desc (pair_space X) (pquot_carrier X) (pquot_some X) Q q1
    pquot_po_map (fun x => reflexivity _).

End Pushout.

Definition pquot_pushout@{h o | o < h +} (X : PairTop@{o}) :
  IsPushout (C := Top@{h o}) (pair_sub_incl X) (top_one (pair_sub_space X)).
Proof.
  unshelve refine (@Build_Pullback (Top@{h o}^op) _ _ _
                     (pair_sub_incl X) (top_one (pair_sub_space X))
                     (pquot_space X) (pquot_in X) (pquot_base X) _ _).
  - intro a; simpl. exact (projT2 a).
  - intros Q q1 q2 Hq.
    unshelve eapply Build_Unique.
    + exact (pquot_po_med X q1 q2 Hq).
    + split.
      * intro x; simpl. reflexivity.
      * intro t; simpl. destruct t. reflexivity.
    + intros v [Hv1 Hv2] [x|]; simpl.
      * symmetry; exact (Hv1 x).
      * symmetry; exact (Hv2 ttt).
Defined.

Example pquot_pushout_apex@{h o | o < h +} (X : PairTop@{o}) :
  pushout_apex (pquot_pushout@{h o} X) = pquot_space X := eq_refl.

(* * ** X/A is the universal-arrow coequalizer of the point-inclusions / * ** X/A 是点包含的普遍箭头余等化器 *)

(*
 Read as a universal arrow to the diagonal functor (book pp. 64-65), the
 coequalizer of a set of maps a → b is a colimit over the shape that has
 a as a vertex, Structure/Coequalizer/Wide.v's [WideCoequalizer]; read
 elementarily (p. 64's display (6)), it is that file's
 [IsWideCoequalizer], and the two agree on every nonempty set of maps.
 The colimit's cocones have a leg out of * as well as one out of X, so
 no point of A is needed: the leg out of * is the new point. 

 --------
 作为对对角函子（书第64-65页）的通用箭头来理解，一组映射 a → b 的余等化子是一个关于形状的余极限，该形状以 a 作为顶点，Structure/Coequalizer/Wide.v 的 [WideCoequalizer]；以基本方式解读（第64页显示的公式（6）），它是该文件的 [IsWideCoequalizer]，并且这两者在每个非空映射集合上都是一致的。余极限的余锥有一条从 * 出发的枝以及一条从 X 出发的枝，因此不需要 A 中的任何点：从 * 出发的枝就是新的点。
*)
Definition pquot_wide_legs@{o h | o < h +} (X : PairTop@{o}) (p : ParObj) :
  fobj[AWide@{h h h h h} (C := Top@{h o})
         (collapse_sub_family (pair_space X) (pair_sub X))] p
    ~{Top@{h o}}~> pquot_space X :=
  match p return
    fobj[AWide@{h h h h h} (C := Top@{h o})
           (collapse_sub_family (pair_space X) (pair_sub X))] p
      ~{Top@{h o}}~> pquot_space X with
  | ParX => pquot_base X
  | ParY => pquot_in X
  end.

Lemma pquot_wide_legs_coherence@{o h | o < h +} (X : PairTop@{o}) :
  ∀ (a b : ParObj)
    (k : b ~{WideParallel@{h h}
               (collapse_sub_points (pair_space X) (pair_sub X))}~> a),
    pquot_wide_legs X a
      ∘ fmap[AWide@{h h h h h} (C := Top@{h o})
               (collapse_sub_family (pair_space X) (pair_sub X))] k
    ≈ pquot_wide_legs X b.
Proof.
  intros a b k.
  destruct a, b; simpl in *.
  - intro t; simpl. exact ttt.
  - destruct k.
  - intro t; simpl. exact (projT2 k).
  - intro t; simpl. left; reflexivity.
Qed.

Definition pquot_wide_cocone@{o h | o < h +} (X : PairTop@{o}) :
  Cocone (AWide@{h h h h h} (C := Top@{h o})
            (collapse_sub_family (pair_space X) (pair_sub X))) :=
  @Build_Cone
    ((WideParallel@{h h}
        (collapse_sub_points (pair_space X) (pair_sub X)))^op)
    (Top@{h o}^op)
    ((AWide@{h h h h h} (C := Top@{h o})
        (collapse_sub_family (pair_space X) (pair_sub X)))^op)
    (pquot_space X)
    (@Build_ACone
       ((WideParallel@{h h}
           (collapse_sub_points (pair_space X) (pair_sub X)))^op)
       (Top@{h o}^op) (pquot_space X)
       ((AWide@{h h h h h} (C := Top@{h o})
           (collapse_sub_family (pair_space X) (pair_sub X)))^op)
       (pquot_wide_legs X) (pquot_wide_legs_coherence X)).

(* A cocone's two legs are a map out of X and a point absorbing A: the data of the pushout, whose mediator [pquot_po_med] is the one here. / 一个余圆锥的两条腿是一个指向 X 的图和一个吸收 A 的点：推出图的数据，其中介 [pquot_po_med] 就是这里的那个。 *)
Lemma pquot_wide_ump@{o h | o < h +} (X : PairTop@{o})
  (N : Cocone (AWide@{h h h h h} (C := Top@{h o})
                 (collapse_sub_family (pair_space X) (pair_sub X)))) :
  ∃! u : pquot_space X ~{Top@{h o}}~> vertex_obj[N],
    ∀ p : ParObj, u ∘ pquot_wide_legs X p ≈ cocone_inj N p.
Proof.
  assert (Hq : cocone_inj N ParY ∘ pair_sub_incl X
               ≈ cocone_inj N ParX ∘ top_one (pair_sub_space X)).
  { intro a.
    exact (cocone_inj_coherence N (a : ParX ~{WideParallel _}~> ParY) ttt). }
  unshelve eapply Build_Unique.
  - exact (pquot_po_med X (cocone_inj N ParY) (cocone_inj N ParX) Hq).
  - intros p; destruct p; intro t; simpl.
    + destruct t; reflexivity.
    + reflexivity.
  - intros v Hv [x|]; simpl.
    + symmetry; exact (Hv ParY x).
    + symmetry; exact (Hv ParX ttt).
Qed.

(*
 Construction 5 read as the universal arrow, for EVERY pair, the empty
 subset included: the colimit of the point-inclusions of A, the type of
 Instance/Top/Quotient.v's [collapse_colimit], with no point of A. 

 --------
 构造 5 被视为通用箭头，对于每一对，空子集包含在内：A 的点包含的余极限，Instance/Top/Quotient.v 的 [collapse_colimit] 类型，没有 A 的点。
*)
Definition pquot_wide_coequalizer_colimit@{o h | o < h +}
  (X : PairTop@{o}) :
  WideCoequalizer (AWide@{h h h h h} (C := Top@{h o})
                     (collapse_sub_family (pair_space X) (pair_sub X))) :=
  {| limit_cone := pquot_wide_cocone X;
     ump_limits := fun N => pquot_wide_ump X N |}.

Example pquot_wide_coequalizer_colimit_apex@{o h | o < h +}
  (X : PairTop@{o}) :
  colimit_apex (pquot_wide_coequalizer_colimit@{o h} X) = pquot_space X
  := eq_refl.

Example pquot_wide_coequalizer_colimit_in@{o h | o < h +}
  (X : PairTop@{o}) :
  colimit_inj (colimit_is_acolimit (pquot_wide_coequalizer_colimit@{o h} X))
    ParY = pquot_in X := eq_refl.

(* The leg out of * picks the left adjoint's basepoint. / 来自 * 的 leg 选择左伴随的基点。 *)
Example pquot_wide_coequalizer_colimit_base@{o h | o < h +}
  (X : PairTop@{o}) :
  continuous_map
    (colimit_inj (colimit_is_acolimit (pquot_wide_coequalizer_colimit@{o h} X))
       ParX) ttt
    = ptop_pt (fobj[PairQuotient@{h o}] X) := eq_refl.

(* The left adjoint's value at every pair IS that colimit's apex. / 左伴随在每一对上的值就是该余极限的顶点。 *)
Example pquot_wide_coequalizer_colimit_quotient@{o h | o < h +}
  (X : PairTop@{o}) :
  ptop_space (fobj[PairQuotient@{h o}] X)
    = colimit_apex (pquot_wide_coequalizer_colimit@{o h} X) := eq_refl.

(* Every colimit of the point-inclusions of a subset has a point, the image of * under its leg out of *, whether or not the subset has one. / 每个子集的点包含的所有余极限都有一个点，即 * 在其从 * 出发的腿下的像，无论该子集是否有一个点。 *)
Definition collapse_colimit_point@{o h | o < h +} (X : TopSpace@{o})
  (A : X → Type@{o})
  (L : WideCoequalizer (AWide@{h h h h h} (C := Top@{h o})
                          (collapse_sub_family X A))) :
  top_carrier (colimit_apex L) :=
  continuous_map (colimit_inj (colimit_is_acolimit L) ParX) ttt.

(* * ** The elementary record, given a point of A / * ** 初等记录，给定点A *)

(* With a point [a0] of A in hand, X ~> X/A IS an elementary wide coequalizer of the point-inclusions of A. / 有了 A 的一点 [a0]，在手的情况下，X ~> X/A 是 A 的点包含的一个基本宽共同余子器。 *)
Definition pquot_coequalizer@{o h i | o < h, o <= i +} (X : PairTop@{o})
  (a0 : collapse_sub_points (pair_space X) (pair_sub X)) :
  IsWideCoequalizer@{i h h} (C := Top@{h o})
    (collapse_sub_family (pair_space X) (pair_sub X))
    (pquot_space X) (pquot_in X).
Proof.
  unshelve econstructor.
  - intros [a Ha] [b Hb] t; simpl; right; exact (Ha, Hb).
  - intros Z k Hk.
    unshelve eapply Build_Unique.
    + refine (pquot_po_med X k (k ∘ top_point (pair_space X) (projT1 a0)) _).
      intro a; simpl. exact (Hk a a0 ttt).
    + intro x; reflexivity.
    + intros v Hv [x|]; simpl.
      * symmetry; exact (Hv x).
      * transitivity (continuous_map v (Some (projT1 a0))).
        -- symmetry; exact (Hv (projT1 a0)).
        -- apply (proper_morphism (continuous_map v) (Some (projT1 a0)) None).
           exact (projT2 a0).
Defined.

(*
 The two readings of X/A are isomorphic in [Top], by the identity on the
 points of X. 

 --------
 X/A 的两种读法在 [Top] 中通过 X 的点上的恒等映射是同构的。
*)
Definition pquot_collapse_iso@{o h u | o < h, h < u +} (X : PairTop@{o})
  (a0 : collapse_sub_points (pair_space X) (pair_sub X)) :
  Top_collapse_sub (pair_space X) (pair_sub X) ≅[Top@{h o}] pquot_space X :=
  wide_coequalizer_unique _
    (collapse_coequalizer@{o h o} (pair_space X) (pair_sub X))
    (pquot_coequalizer@{o h o} X a0).

Example pquot_collapse_iso_to@{o h u | o < h, h < u +} (X : PairTop@{o})
  (a0 : collapse_sub_points (pair_space X) (pair_sub X))
  (x : carrier (top_carrier (pair_space X))) :
  continuous_map (to (pquot_collapse_iso X a0)) x = Some x := eq_refl.

Example pquot_collapse_iso_from_some@{o h u | o < h, h < u +}
  (X : PairTop@{o}) (a0 : collapse_sub_points (pair_space X) (pair_sub X))
  (x : carrier (top_carrier (pair_space X))) :
  continuous_map (from (pquot_collapse_iso X a0)) (Some x) = x := eq_refl.

Example pquot_collapse_iso_from_none@{o h u | o < h, h < u +}
  (X : PairTop@{o}) (a0 : collapse_sub_points (pair_space X) (pair_sub X)) :
  continuous_map (from (pquot_collapse_iso X a0)) None = projT1 a0
  := eq_refl.

(* Construction 5's X/A, pointed at the point [a0] of A. / 构造 5 的 X/A，指向 A 的 [a0] 点。 *)
Definition collapse_pointed@{o} (X : PairTop@{o})
  (a0 : collapse_sub_points (pair_space X) (pair_sub X)) : PointedTop@{o} :=
  @Build_PointedTop@{o} (Top_collapse_sub (pair_space X) (pair_sub X))
    (projT1 a0).

(*
 The comparison as POINTED spaces: the value of the left adjoint at
 ⟨X, A⟩ is Construction 5's X/A pointed at [a0], up to isomorphism in
 [Top_pointed].  Both basepoint conditions hold by the readbacks above:
 [a0] goes to [Some (projT1 a0)], which lies with [None] because a0 is in
 A, and [None] goes back to [projT1 a0] itself. 

 --------
 作为有基点空间的比较：左伴随在 ⟨X, A⟩ 处的值是构造 5 的 X/A 在 [a0] 处取基点，在 [Top_pointed] 中同构。上述读回操作满足了两个基点条件：[a0] 映射到 [Some (projT1 a0)]，该点与 [None] 在一起，因为 a0 在 A 中，并且 [None] 回到 [projT1 a0] 本身。
*)
Definition pquot_collapse_iso_pointed@{o h u | o < h, h < u +}
  (X : PairTop@{o}) (a0 : collapse_sub_points (pair_space X) (pair_sub X)) :
  collapse_pointed X a0 ≅[Top_pointed@{h o}] fobj[PairQuotient@{h o}] X :=
  @Build_Isomorphism Top_pointed@{h o} (collapse_pointed X a0)
    (fobj[PairQuotient@{h o}] X)
    (@Build_PointedMap@{h o} (collapse_pointed X a0)
       (fobj[PairQuotient@{h o}] X) (to (pquot_collapse_iso@{o h u} X a0))
       (projT2 a0))
    (@Build_PointedMap@{h o} (fobj[PairQuotient@{h o}] X)
       (collapse_pointed X a0) (from (pquot_collapse_iso@{o h u} X a0))
       (inl (reflexivity (projT1 a0))))
    (iso_to_from (pquot_collapse_iso@{o h u} X a0))
    (iso_from_to (pquot_collapse_iso@{o h u} X a0)).

(* * ** The empty subset: X/∅ ≅ X₊; no pointed elementary coequalizer / * ** 空子集: X/∅ ≅ X₊；没有基点的初等余等化器 *)

Definition empty_pair@{o} (X : TopSpace@{o}) : PairTop@{o} :=
  @Build_PairTop@{o} X (fun _ => False) (fun _ _ _ f => f).

(* The collapse at ∅ has a genuinely new point ... / 在 ∅ 处的塌陷有一个真正新的点... *)
Lemma pquot_empty_new_point@{o} (X : TopSpace@{o})
  (x : carrier (top_carrier X)) :
  pquot_rel (empty_pair X) (Some x) None → False.
Proof. exact (fun f => f). Qed.

(* ... and is X with a disjoint point added, X₊ = X + 1. / ... 并且是 X，添加了一个不相交的点，X₊ = X + 1。 *)
Definition pquot_empty_sum_to@{o} (X : TopSpace@{o}) :
  SetoidMorphism@{o o o} (pquot_carrier (empty_pair X))
    (sum_carrier X Point_Top@{o}).
Proof.
  unshelve notypeclasses refine
    (@Build_SetoidMorphism _ (pquot_setoid (empty_pair X)) _
       (is_setoid (sum_carrier X Point_Top@{o}))
       (fun u => match u with
                 | Some x => Datatypes.inl x
                 | None => Datatypes.inr ttt
                 end) _).
  intros [x|] [y|] H; simpl in *.
  - destruct H as [H|[H _]]; [ exact H | destruct H ].
  - destruct H.
  - destruct H.
  - reflexivity.
Defined.

Definition pquot_empty_sum_from@{o} (X : TopSpace@{o}) :
  SetoidMorphism@{o o o} (sum_carrier X Point_Top@{o})
    (pquot_carrier (empty_pair X)).
Proof.
  unshelve notypeclasses refine
    (@Build_SetoidMorphism _ (is_setoid (sum_carrier X Point_Top@{o})) _
       (pquot_setoid (empty_pair X))
       (fun w => match w with
                 | Datatypes.inl x => Some x
                 | Datatypes.inr _ => None
                 end) _).
  intros [x|a] [y|b] H; simpl in *.
  - left; exact H.
  - destruct H.
  - destruct H.
  - exact ttt.
Defined.

Definition pquot_empty_sum_iso@{h o | o < h +} (X : TopSpace@{o}) :
  pquot_space (empty_pair X) ≅[Top@{h o}] Sum_Top X Point_Top@{o}.
Proof.
  unshelve refine (@Build_Isomorphism Top@{h o}
            (pquot_space (empty_pair X)) (Sum_Top X Point_Top@{o})
            (@Build_ContinuousMorphism@{h o} (pquot_space (empty_pair X))
               (Sum_Top X Point_Top@{o}) (pquot_empty_sum_to X) _)
            (@Build_ContinuousMorphism@{h o} (Sum_Top X Point_Top@{o})
               (pquot_space (empty_pair X)) (pquot_empty_sum_from X) _)
            _ _).
  - apply (snd (tquot_universal (pair_space (empty_pair X))
                  (pquot_carrier (empty_pair X)) (pquot_some (empty_pair X))
                  (Sum_Top X Point_Top@{o}) (pquot_empty_sum_to X))).
    exact (continuity (Top_inl X Point_Top@{o})).
  - intros V [_ HV]; split.
    + exact HV.
    + exact (open_const Point_Top@{o} (V None)).
  - intros [x|a]; simpl.
    + reflexivity.
    + destruct a; reflexivity.
  - intros [x|]; simpl.
    + left; reflexivity.
    + exact ttt.
Defined.

Example pquot_empty_sum_iso_some@{h o | o < h +} (X : TopSpace@{o})
  (x : carrier (top_carrier X)) :
  continuous_map (to (pquot_empty_sum_iso@{h o} X)) (Some x) = Datatypes.inl x
  := eq_refl.

Example pquot_empty_sum_iso_none@{h o | o < h +} (X : TopSpace@{o}) :
  continuous_map (to (pquot_empty_sum_iso@{h o} X)) None = Datatypes.inr ttt
  := eq_refl.

(*
 So, read as the universal arrow, the coequalizer of the empty family of
 point-inclusions, the colimit above at ⟨X, ∅⟩, is X ⊔ ∗. 

 --------
 因此，作为普适箭头来阅读时，空点包含族的等化子上面在 ⟨X, ∅⟩ 的余极限，就是 X ⊔ ∗。
*)
Definition pquot_wide_coequalizer_colimit_empty@{o h | o < h +}
  (X : TopSpace@{o}) :
  colimit_apex (pquot_wide_coequalizer_colimit@{o h} (empty_pair X))
    ≅[Top@{h o}] Sum_Top X Point_Top@{o} :=
  pquot_empty_sum_iso@{h o} X.

(* The elementary record at ⟨∅, ∅⟩ is not met by this X/A ... / 在 ⟨∅, ∅⟩ 的基础记录不符合这个 X/A ... *)
Lemma pquot_empty_not_coequalizer@{o h i | o < h, o <= i +} :
  IsWideCoequalizer@{i h h} (C := Top@{h o})
    (collapse_sub_family (pair_space (empty_pair Empty_Top@{o}))
       (pair_sub (empty_pair Empty_Top@{o})))
    (pquot_space (empty_pair Empty_Top@{o}))
    (pquot_in (empty_pair Empty_Top@{o})) → False.
Proof.
  intro E.
  destruct (wcoeq_desc E (@id Top@{h o} Empty_Top@{o})
              (fun i => match projT2 i with end)) as [u _ _].
  exact (continuous_map u None).
Qed.

(* ... so [pquot_coequalizer]'s point of A cannot be dropped. / ...所以[pquot_coequalizer]的A点不能被删除。 *)
Lemma pquot_coequalizer_needs_point@{o h i | o < h, o <= i +} :
  (∀ X : PairTop@{o},
     IsWideCoequalizer@{i h h} (C := Top@{h o})
       (collapse_sub_family (pair_space X) (pair_sub X))
       (pquot_space X) (pquot_in X)) → False.
Proof.
  intro H.
  exact (pquot_empty_not_coequalizer@{o h i} (H (empty_pair Empty_Top@{o}))).
Qed.

(* * ** The elementary record and the colimit part at the empty subset / * ** 空子集处的基本记录和余极限部分 *)

(*
 No pointed space's underlying space is an elementary wide coequalizer
 of the empty family of point-inclusions at the empty space: its
 basepoint would be a point of it, which Instance/Top/Quotient.v's
 [empty_wide_coequalizer_pointless] refutes. 

 --------
 没有尖点空间的底层空间是空空间上点包含的空族的一个初等广义共同核：它的基点将是它的一个点，而 Instance/Top/Quotient.v 的 [empty_wide_coequalizer_pointless] 否定了这一点。
*)
Lemma no_pointed_coequalizer_at_empty@{o h i | o < h, o <= i +}
  (Q : PointedTop@{o}) (e : Empty_Top@{o} ~{Top@{h o}}~> ptop_space Q) :
  IsWideCoequalizer@{i h h} (C := Top@{h o})
    (collapse_sub_family Empty_Top@{o} (fun _ => False)) (ptop_space Q) e →
  False.
Proof.
  intro E.
  exact (empty_wide_coequalizer_pointless@{o h i} (ptop_space Q) e E
           (ptop_pt Q)).
Qed.

(*
 Hence no assignment of a pointed space to each pair, a functor or any
 other function on objects, makes every underlying space an elementary
 wide coequalizer of the point-inclusions: at ⟨∅, ∅⟩ there is none.  The
 colimit form is met by [PairQuotient] at every pair
 ([pquot_wide_coequalizer_colimit_quotient]). 

 --------
 因此，将每对对象指定一个有基点空间、函子或任何其他对象上的函数，都不能使每个底层空间成为点包含的初等广义余等化器：在 ⟨∅, ∅⟩ 处没有这样的情况。对于每一对 ( [pquot_wide_coequalizer_colimit_quotient] )，该余极形式都由 [PairQuotient] 满足。
*)
Lemma no_pointed_elementary_coequalizers@{o h i | o < h, o <= i +}
  (L : PairTop@{o} → PointedTop@{o}) :
  (∀ X : PairTop@{o}, ∃ e : pair_space X ~{Top@{h o}}~> ptop_space (L X),
     IsWideCoequalizer@{i h h} (C := Top@{h o})
       (collapse_sub_family (pair_space X) (pair_sub X)) (ptop_space (L X)) e)
  → False.
Proof.
  intro H.
  destruct (H (empty_pair Empty_Top@{o})) as [e E].
  exact (no_pointed_coequalizer_at_empty@{o h i} _ e E).
Qed.

(*
 At the empty family the two forms part: no colimit's apex carries an
 elementary wide coequalizer of the family at ∅, since the colimit has a
 point ([collapse_colimit_point]) and the elementary one has none. 

 --------
 在空族中，两个形式部分：没有余极点承载该族在 ∅ 上的初等宽余等化器，因为余极有一个点（[collapse_colimit_point]），而初等的没有。
*)
Lemma empty_colimit_not_elementary@{o h i | o < h, o <= i +}
  (L : WideCoequalizer (AWide@{h h h h h} (C := Top@{h o})
                          (collapse_sub_family Empty_Top@{o}
                             (fun _ => False))))
  (e : Empty_Top@{o} ~{Top@{h o}}~> colimit_apex L) :
  IsWideCoequalizer@{i h h} (C := Top@{h o})
    (collapse_sub_family Empty_Top@{o} (fun _ => False)) (colimit_apex L) e →
  False.
Proof.
  intro E.
  exact (empty_wide_coequalizer_pointless@{o h i} (colimit_apex L) e E
           (collapse_colimit_point Empty_Top@{o} (fun _ => False) L)).
Qed.
