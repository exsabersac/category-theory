Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Arrow.Dual.
Require Import Category.Adjunction.Opposite.
Require Import Category.Adjunction.Determination.
Require Import Category.Construction.Slice.
Require Import Category.Construction.Quotient.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.One.

(*
   * * Sliced adjoint inverses: Mac Lane's Proposition V.9.1, abstractly

   nLab: https://ncatlab.org/nlab/show/topological+concrete+category
   nLab: https://ncatlab.org/nlab/show/subspace+topology
   nLab: https://ncatlab.org/nlab/show/quotient+space
   nLab: https://ncatlab.org/nlab/show/over+category

   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   GTM 5, Springer 1998, SS V.9, read from the page images: the
   subspace construction (book pp. 132-133, PDF pp. 141-142;
   catalog id maclane:V.9:construction2), Proposition 1 (book
   p. 133, PDF p. 142; maclane:V.9:prop1), the quotient
   construction (book pp. 133-134, PDF pp. 142-143;
   maclane:V.9:construction3), and the one sentence stating the
   dual of Proposition 1 (book p. 134, PDF p. 143), which is the
   first clause of maclane:V.9:remark2, #458's catalog item.  The
   book numbers Proposition 1 and none of the constructions or
   remarks; the catalog ids are names, not book numbering.
   Book: Fong and Spivak, "Seven Sketches in Compositionality", CUP 2019,
   SS 7.3.2, Exercise 7.32 (printed p. 236, PDF p. 248) --
   7sketches:7.3.2:ex7.32.
   Book: Adamek, Herrlich and Strecker, "Abstract and Concrete
   Categories: The Joy of Cats", Wiley 1990, SS 21 (topological
   categories), cited through nLab.

   ** Background

   Mac Lane's SS V.9 recasts two constructions of point-set topology as
   adjunctions over the underlying-set functor [G : Top ⟶ Set], sliced
   at a space.  Over a fixed space [x], the induced functor
   [G↓x : (Top↓x) ⟶ (Set↓Gx)] has a right adjoint [L] that topologizes
   a function [t : S ⟶ Gx] by declaring open exactly the preimages
   [t⁻¹U] of the open sets [U] of [x] (the subspace construction).  When
   [S] is a subset of [Gx] that is the subspace topology, and the book
   observes: "(G↓X)∘L = Id; L is a 'right-adjoint-right-inverse' to
   (G↓X)".  By the naming of SS IV.4, where an adjunction with counit
   the identity makes the left adjoint a left-adjoint-left-inverse, that
   is the adjunction [G↓x ⊣ L] with counit the identity, read from [L];
   the record below states it so.  Mac Lane stresses that the universal
   property concerns arbitrary spaces mapping in, not only other
   subspaces.  Under a space the dual holds: [x↓G] has a left adjoint
   that gives [S] the sets with open preimage -- the quotient, or
   identification, topology when [t] is surjective -- "with unit the
   identity map, so M is left-adjoint-right-inverse to X↓G" (the
   quotient construction).  Between the two the book states, verbatim
   from the page:

   "Proposition 1.  If G: C→D is a faithful functor, if D has
   equalizers, and if, for each x ∈ C, (G↓x): (C↓x)→(D↓Gx) has a
   right-adjoint-right-inverse L, then C has equalizers."

   Its proof builds the equalizer as the lift [L] of the downstairs one,
   which explains the classical equalizer of two maps of spaces -- the
   points where they agree, with the subspace topology -- without
   mentioning points.  The dual is one sentence of the book, "Now
   Proposition 1 was proved just from the axioms for a category, so its
   dual is also true" (book p. 134): coequalizers from sliced
   left-adjoint-right-inverses.  nLab's "subspace topology" records the
   same equalizer computation and identifies the subspace inclusions
   with the regular monomorphisms of Top; its "quotient space" calls the
   dual construction the final, or strong, topology.  Seven Sketches'
   Exercise 7.32 is the elementary side of the subspace construction:
   the open sets of [Y ⊆ X] are the traces [B ∩ Y] of the open sets [B]
   of [X], and the inclusion is continuous.

   The shape has a general theory.  A functor [U : C ⟶ D] along which
   every family of maps [f_i : X ⟶ U S_i] out of an object of [D] has an
   initial lift -- informally the "smallest topology rendering the f_i
   continuous" -- is a topological functor, and [C] a topological
   concrete category over [D]; the forgetful functor from Top to Set is
   the paradigm, every topological functor is faithful (Adamek, Herrlich
   and Strecker, Theorem 21.3), and the notion is self-dual, so such a
   [C] carries final structures as well (nLab, "topological concrete
   category").  Read against that definition, Mac Lane's hypothesis is
   the one-arrow case: a sliced right adjoint at [(S; t)] is a universal
   lift of the single map [t], and the right-inverse clause asks that the
   lift sit over [S] on the nose -- the equation [U(T) = X] of nLab's
   definition of an initial lift, an EXISTENCE condition carried by [S]
   itself.  That such lifts are UNIQUE, literally and not up to
   isomorphism, is a separate condition, which nLab attributes to
   Adamek, Herrlich and Strecker and identifies with [U] being amnestic;
   a chosen right-adjoint-right-inverse does not supply it (argued, not
   built: a faithful functor can have one on every slice without being
   amnestic -- spaces carrying an inert bit that the maps ignore, lifted
   with the bit 0).  This file measures how little of that Proposition 1
   consumes.

   ** What is delivered

   - [Sliced G a : (A ̸ a) ⟶ (X ̸ G a)] and
   [Cosliced G a : (a ̸co A) ⟶ (G a ̸co X)], Mac Lane's [G↓a] and
   [a↓G] on Construction/Slice.v's [Slice] and [Coslice]: an object
   [(d; h)] goes to [(G d; fmap[G] h)], an arrow [m] to [fmap[G] m].
   - [RightAdjointRightInverse S]: a right adjoint [rari_right], the
   adjunction [rari_adj : S ⊣ rari_right], the Leibniz object equation
   [rari_obj c : S (rari_right c) = c], and
   [rari_counit c : counit c ≈ id_cast (rari_obj c)].  "Counit the
   identity" is not an equation between arrows of one hom-set until
   the object equation is supplied, so this is Adjunction/LeftInverse.v's
   design crux one parameter over, and the record is
   [LeftAdjointLeftInverse] with the adjoint moved into the parameter:
   the bridges [rari_lali] and [lali_rari], with both round trips at
   [eq_refl], are in Structure/SlicedInverse/Strict.v.
   - The pointwise cores.  [sliced_equalizer]: given one parallel pair
   [f g : x ~> y], one downstairs equalizer [E] of [fmap[G] f] and
   [fmap[G] g] at [(S, s)], ONE couniversal arrow [U] from
   [Sliced G x] to the slice object [(S; s)], and [Faithful G], the
   arrow [sliced_eq_arrow : sliced_eq_obj ~> x] -- Mac Lane's
   [Lt : Ls ⟶ x] -- is an equalizer of [f] and [g].
   [cosliced_coequalizer] is the dual, over a universal arrow from
   [(Q; q)] to [Cosliced G y], proved directly.
   - The book forms.  [equalizers_from_sliced_right_adjoints] (any right
   adjoints [R a] of the [Sliced G a]) and
   [equalizers_from_sliced_RARI], which is Proposition 1 and is the
   former applied to [rari_right] and [rari_adj];
   [coequalizers_from_sliced_left_adjoints], the dual of Proposition 1
   over whole left adjoints.  The dual over left-adjoint-right-inverses,
   Theory/Equivalence/Strict.v's [LeftAdjointRightInverse], is
   Structure/SlicedInverse/Strict.v's [coequalizers_from_sliced_LARI].
   - What the right-inverse clause buys: [rari_preserves], [G] of the
   lifted equalizer is an equalizer of [fmap[G] f] and [fmap[G] g] (its
   object is [S] up to the Leibniz [rari_over], its arrow [s] up to
   that cast, [rari_arrow_over]); [equalizers_from_sliced_RARI_preserved]
   states it for every equalizer that [equalizers_from_sliced_RARI]
   builds.  The dual, [lari_preserves], is in the satellite.
   - [adj_unit_universal_op]: the unit of an adjunction as a universal
   arrow, read off Adjunction/Determination.v's
   [adj_counit_couniversal] at Adjunction/Opposite.v's
   [Opposite_Adjunction]; the coequalizer book form takes its universal
   arrow from it.
   - [prop1_needs_faithfulness], below.

   ** Where each hypothesis is spent, measured

   The right-inverse clause is not used by Proposition 1: the body of
   [equalizers_from_sliced_RARI] names [rari_right] and [rari_adj] and
   neither [rari_obj] nor [rari_counit], and the theorem it applies,
   [equalizers_from_sliced_right_adjoints], has no right-inverse
   hypothesis at all.  Whole adjoints are not used either: the pointwise
   core takes a single couniversal arrow, at the one slice object
   [(S; s)] that the downstairs equalizer supplies, and the book form
   obtains it from the counit by [adj_counit_couniversal] and consults
   the adjunction nowhere else.  The same holds of the two coequalizer
   forms, which name only [lari_left]/[lari_adj] or the given [L] and
   [adjL].

   Faithfulness is spent in exactly one step per variance, the fork
   equation.  It is a section variable ([GF]) of [SlicedEqualizer] and of
   [CoslicedCoequalizer].  [sliced_desc] and [cosliced_desc] -- the
   existence AND the uniqueness of the mediating arrow -- close under
   [Proof using E U], and their About readbacks carry no [Faithful]
   argument.  [sliced_fork] and [cosliced_cofork] need
   [Proof using E U GF]: on a scratch copy with [Proof using E U] each is
   refused with "The following section variable is used but not
   declared: GF."  So the lift's descent comes from the downstairs
   equalizer and the couniversal property alone, and faithfulness is
   what proves that the lifted arrow forks.

   ** Faithfulness cannot be dropped

   [prop1_needs_faithfulness] refutes Proposition 1 with the
   faithfulness hypothesis deleted, quantified over all [A], [X] and [G]
   at one universe instance.  The countermodel is
   [Erase Parallel : Parallel ⟶ _1] (Instance/Parallel.v,
   Instance/One.v).  Every slice of [Parallel] has the terminal object
   [(a; id)], and [erase_slice_RARI] makes the functor constant at it a
   right-adjoint-right-inverse of each [Sliced (Erase Parallel) a] --
   the object equation is one case analysis over the slice of [_1], and
   the counit condition holds because that slice is thin
   ([slice_one_hom_eq]).  [_1] has equalizers ([One_HasEqualizers]).  But
   the pair [par_arrow_one], [par_arrow_two] has no fork at all
   ([parallel_pair_unforked]), so [Parallel] has no equalizers
   ([Parallel_no_equalizers]), and [Erase Parallel] is not faithful
   ([Erase_Parallel_not_faithful]).  [sliced_RARI_without_faithfulness]
   packages the four facts.  The dual is the satellite's
   [prop1_dual_needs_faithfulness].

   ** Strengths

   Holding at [eq_refl], as [Example]s: [Sliced_fobj], [Sliced_fmap],
   [Cosliced_fobj], [Cosliced_fmap]; [adj_unit_universal_op_obj] and
   [adj_unit_universal_op_arrow] (the universal arrow IS the unit, as
   Adjunction/Determination.v's counit readback has it); [rari_eq_obj]
   and [rari_eq_arrow] (the pointwise equalizer built from a
   right-adjoint-right-inverse IS [rari_right L (S; s)]);
   [equalizers_from_sliced_RARI_obj] and
   [equalizers_from_sliced_RARI_arrow] (the same at the [HasEqualizers]
   level), and [coequalizers_from_sliced_left_adjoints_obj] and
   [coequalizers_from_sliced_left_adjoints_arrow].  Twelve in all.  The
   book forms read the downstairs (co)equalizer by projections
   rather than by a [match] so that those readbacks reach [eq_refl]:
   written with [destruct] on the downstairs equalizer instead, the same
   book form has its object readback refused at [eq_refl] ("cannot
   unify", compiled out of tree), the stdlib [sigT] having no
   definitional eta.

   Leibniz but not [eq_refl]: [rari_over : G (`1 (rari_right L (S; s)))
   = S], which is [f_equal projT1] of the field [rari_obj]; at a variable
   [L] the field is its only source.  Also Leibniz, by [destruct] on the
   equation: [slice_id_cast_1], the first component of a slice arrow
   transported by [id_cast] is the transport of first components, a
   Leibniz equation between arrows at a variable equation, of the kind
   Construction/Quotient.v's [id_cast_refl] already states.  Up to [≈]:
   [rari_arrow_over], the fork equations, and the transported arrows.
   [rari_preserves] is data assembled by [IsEqualizer_transport] from
   [rari_over] and [rari_arrow_over], and
   [equalizers_from_sliced_RARI_preserved] reaches it through the
   [eq_refl] readbacks, with no further cast.  Nothing is claimed about
   the mediating arrow beyond its unique existence.

   The file has six [Defined] (counted by token): [sliced_desc],
   [cosliced_desc], [IsEqualizer_transport], the second obligation of
   [One_HasEqualizers], [erase_slice_adj] and [erase_slice_RARI].  Each
   carries data (a mediating arrow, an equalizer, an adjunction, a
   record) and is kept [Defined] by the data convention; none is
   load-bearing, measured by flipping all six, together with the
   satellite's four, to [Qed] in a scratch copy, which compiles both
   files.

   ** Universes, measured by About on every constant

   [Sliced@{oA hA oX hX u u0 u1 u2}] and [Cosliced] keep the categories
   at their own levels, [A : Category@{oA hA hA}] and
   [X : Category@{oX hX hX}].  Their blocks carry no equation: the bound
   [hA <= hX] that [G : A ⟶ X] itself imposes, and one strict bound per
   slice instance ([hA < u], [hX < u0]), which is Construction/Slice.v's
   own [u2 < u1] on [Slice] and on [Coslice] alike.  The four readbacks
   have the same shape.

   Every other constant over two categories binds them at ONE hom level,
   [A : Category@{oA h h}] and [X : Category@{oX h h}], in the BINDER and
   with no equation in any block.  The identification is inherited, and
   which donor forces it was measured by isolation: a section declaring
   [hA] and [hX] apart, one [Context] line varied, and a trivial
   [Example] read back by About.  The couniversal arrow
   [CouniversalArrow ((S; s)) (Sliced G x)] alone prints [hA = hX]
   (Theory/Universal/Arrow/Dual.v's [CouniversalArrow] carries the
   equation [u0 = u2] in its own block), [Faithful G] alone prints it
   (Theory/Functor.v's [Faithful] binds both categories at one hom level),
   and a sliced adjunction [Sliced G x ⊣ R] prints it (two functors in
   opposite directions already do).  [Sliced G x] alone and
   [IsEqualizer] alone print only [hA <= hX], and so does the DUAL
   arrow: [UniversalArrow ((Q; q)) (Cosliced G y)] alone prints no
   equation.  So the equalizer core is tied by two independent donors,
   the coequalizer core by faithfulness only, and the book forms by the
   adjunctions as well; all of them inherited and none introduced here.
   At Instance/Top/Forgetful.v's [Top_Forget] the two hom levels
   coincide anyway ([Top@{h o}] and [Sets@{h so}] both have homs at
   [h]).

   One identification sits in the universe INSTANCES rather than in any
   block, and is disclosed here.  Wherever the two hom levels coincide,
   the two slice-auxiliary universes of [Sliced] and [Cosliced] (the
   [u] and [u0] of [hA < u] and [hX < u0], one per slice) are
   instantiated at one universe: [equalizers_from_sliced_RARI] reads
   [Sliced@{oA h oX h u u u5 u6}], [sliced_equalizer] and
   [cosliced_coequalizer] read [Sliced@{oA h oX h u3 u3 u0 u}] and its
   [Cosliced] twin, and the refutation below reads
   [Sliced@{u4 u5 u2 u5 u3 u3 u u0}].  No donor forces it: a trivial
   [Example] over [Sliced G x] ALONE, in a section binding both
   categories at one hom level [h], already reads back
   [Sliced@{oA h oX h u u u0 u1}] (About, out of tree), and with the hom
   levels apart [UniversalArrow ((Q; q)) (Cosliced G y)] alone keeps
   both universes; so the two, which then carry the same single bound
   [h < _], are merged when this file's constants are elaborated.  It
   costs nothing where it was measured: Instance/Top/Subspace.v's
   [subspace_RARI] and [quotient_LARI] read [Sliced@{so o so o u0 u0 so
   so}] and [Cosliced@{so o so o u0 u0 so so}] and feed both book forms,
   and the instantiation at [Top_Forget] typechecks.

   [RightAdjointRightInverse@{oA oC h u u0}] has one hom level [h] in the
   binder, forced by its first field: with [hA < hC] declared, a record
   holding only [rari_right : C ⟶ A] beside the parameter [S : A ⟶ C] is
   refused ("Cannot enforce hA = ... because hA < hC <= ...").  Its one
   strict bound [h < u] is Theory/Adjunction.v's [Adjunction] class's own
   [h1 < so], measured by adding the fields one at a time: [rari_right]
   alone leaves the block empty, and [rari_adj] brings [h < u].

   Across the 73 constants of this file (Print Module, the record, its
   constructor and projections, and every [Program] obligation) the
   About log has zero word-bounded [Set] and no block carries an
   equation; in every block whose constant binds categories, each strict
   bound relates a hom level to an auxiliary universe that no category
   binder names.  The witness [One_HasEqualizers] is annotated for a
   measured reason (and the satellite's [One_HasCoequalizers] likewise):
   unannotated it minimizes to [HasEqualizers@{u Set} 1] (compiled out of
   tree), which would confine [prop1_needs_faithfulness] to [Set]-homed
   categories; annotated [@{o h}] it is [HasEqualizers@{o h} _1@{o h h}].
   [prop1_needs_faithfulness@{u u0 u1 u2 u3 u4 u5}] quantifies over
   [A : Category@{u4 u5 u5}] and [X : Category@{u2 u5 u5}] with the one
   strict bound [u5 < u3].  [Parallel@{u u0}] carries no [Set] even
   though its object and arrow types are [Set]-sorted inductives.

   ** Route and cost

   Closure: 41 [Category.*] modules excluding this file ([Print
   Libraries] on its [Require] list).  Dropping each [Require] alone,
   Adjunction/Determination.v costs 4 at the margin,
   Construction/Slice.v, Construction/Quotient.v,
   Structure/Equalizer/Fork.v and Structure/Coequalizer.v 1 each, and the
   other eleven 0.  Two constants are rebuilt rather than consumed, each
   on a measurement against that list:

   - [adj_unit_universal_op] has the statement of
   Adjunction/Representability.v's [adj_unit_universal] and the same
   two [eq_refl] readbacks; requiring that module would add 12
   modules (41 to 53).
   - [IsEqualizer_transport] moves an equalizer along a Leibniz
   equation of apexes; Adjunction/CokernelPair.v's
   [IsEqualizer_along_iso] (an isomorphism of apexes, closed [Qed])
   would serve and would add 20 (41 to 61).

   The strict-inverse half -- the bridges to Adjunction/LeftInverse.v
   and the LARI form of the dual -- is the satellite
   Structure/SlicedInverse/Strict.v, because Theory/Equivalence/Strict.v
   would add 14 modules here (41 to 55; Adjunction/LeftInverse.v alone
   12) and those constants are its only consumers.  The coequalizer
   core is proved directly rather than as the op reading of the
   equalizer core: [Slice (A^op) a] and [(Coslice A a)^op] orient the
   triangle equation oppositely ([`2 y ∘ f ≈ `2 x] against
   [`2 y ≈ f ∘ `2 x]), so that route would need a transport functor --
   argued, not measured.

   [#[local] Obligation Tactic := idtac] is set file-wide, as in
   Adjunction/LeftInverse.v and Theory/Equivalence/Strict.v, and every
   obligation is discharged by hand.

   ** Prior art, measured

   No declaration named [RightAdjointRightInverse] existed: a
   whole-word search before this file found only prose in the header of
   Adjunction/Diagonal/Connected.v, which used the name for a different
   notion and is corrected, in place, alongside this file.
   [LeftAdjointLeftInverse] (#376) and
   [LeftAdjointRightInverse] (#377) existed and set the convention
   followed.  No functor between slices is induced by a functor between
   the ambient categories on the [Slice] encoding:
   Construction/Slice/Pullback.v's [Bang_Functor] (post-composition) and
   [Star_Functor] (base change) move along an arrow of ONE category.
   Construction/Comma/Functorial.v's [Comma_reindex] does give the
   sliced functor in comma form, [(Id[A] ↓ =(a)) ⟶ (Id[X] ↓ =(G a))],
   with its object readback at [eq_refl] (compiled out of tree); [Sliced]
   is stated on [Slice] directly because that is the encoding
   [CouniversalArrow] and the equalizer records are used with here.
   Structure/Limit/Creation.v's [CreatesLimit] is a different notion: it
   starts from a limit of [G ◯ K] and asks for its unique lift, whereas
   here the lift is SUPPLIED by the sliced adjoint and its uniqueness is
   not asserted.

   Collisions: none over the 82 names of this file and its satellite
   (every constant Print Module lists, less the [Program] obligations,
   plus the record and its constructor), by [find | xargs grep -lw] over
   every other [.v] file and instrument-checked on names known to be
   present.  The whole-word hits, measured with the probe registered, are
   three files: Instance/Top/Subspace.v (ten of the names) and
   Test/ProbeSubspace457.v (all 82, in its guard block), which use or
   cite these constants and declare none of the names, and the header prose
   of Adjunction/Diagonal/Connected.v named above (one name).  That is
   after three renames: [par_one] and [par_two] are
   Instance/Proset/Transform.v's and
   Theory/Natural/Transformation/Arrows.v's, and [point_adj] is
   Adjunction/LeftInverse.v's, which the satellite requires.

   ** Registration

   Nothing is registered for instance resolution: a
   right-adjoint-right-inverse is a chosen adjoint, passed explicitly, as
   Adjunction/LeftInverse.v and Theory/Equivalence/Strict.v rule for
   their records.  [Faithful] and the (co)equalizer structures are taken
   instance-implicitly, as their classes are.

   ** NOT DELIVERED

   - No concrete instance in this file.  The witnesses are
   Instance/Top/Subspace.v's, over Instance/Top/Prop.v's Prop-valued
   spaces: [subspace_RARI] and [quotient_LARI] (the subspace and
   quotient constructions, at [Sliced PForget X] and
   [Cosliced PForget X]), and [PTop_HasEqualizers] and
   [PTop_HasCoequalizers], built by [equalizers_from_sliced_RARI] and
   the satellite's [coequalizers_from_sliced_LARI]; Seven Sketches'
   Exercise 7.32 is there too.  At Instance/Top/Forgetful.v's
   [Top_Forget] the types line up -- compiled out of tree, with
   [Top_Forget_Faithful] supplied, [equalizers_from_sliced_RARI] there
   has type
   [HasEqualizers Sets@{h so} → (∀ a, RightAdjointRightInverse
   (Sliced Top_Forget a)) → HasEqualizers Top@{h o}] -- but no
   hypothesis is discharged there, and
   Instance/Top/Subspace/TypeValued.v records why the sliced
   adjunctions are not [Adjunction] records over the Type-valued
   [Top].
   - No converse (nothing here derives sliced adjoints from equalizers), no
   multi-arrow initial lifts, no products or general limits (catalog
   maclane:V.9:remark1, #458's), no uniqueness of a
   right-adjoint-right-inverse, no
   characterization of the functors that have one (the analogue of
   Exercise IV.4.4 for left-adjoint-left-inverses), and no readback of
   the mediating arrow against the adjunction's transpose.
   - No op-duality between the two halves; each is proved on its own. 

   --------
   * * 切片伴随逆：Mac Lane 命题 V.9.1，抽象地

   nLab:  https://ncatlab.org/nlab/show/topological+concrete+category 
   nLab:  https://ncatlab.org/nlab/show/subspace+topology 
   nLab:  https://ncatlab.org/nlab/show/quotient+space 
   nLab:  https://ncatlab.org/nlab/show/over+category书籍：Mac Lane，《为工作数学家准备的范畴论》，第2版，GTM 5，Springer 1998，第V.9章，从页面图像阅读：子空间构造（书籍第132-133页，PDF第141-142页；目录ID maclane:V.9:construction2），命题1（书籍第133页，PDF第142页；maclane:V.9:prop1），商构造（书籍第133-134页，PDF第142-143页；maclane:V.9:construction3），以及一小句说明命题1的对偶（书籍第134页，PDF第143页），这是maclane:V.9:remark2中#458目录项的第一条款。书中只编号了命题1，而没有编号任何构造或备注；目录ID是名称，而不是书籍编号。书籍：Fong 和 Spivak，《组合性的七个草图》，CUP 2019，  
   SS 7.3.2，练习 7.32（印刷本第 236 页，PDF 第 248 页）--  
   7sketches:7.3.2:ex7.32。书籍：Adamek、Herrlich 和 Strecker，《抽象与具体范畴：猫的乐趣》，Wiley 1990，SS 21（拓扑范畴），通过 nLab 引用。  

   ** 背景麦克·莱恩的《SS》第九版将点集拓扑的两个构造重新表述为在基本集合函子[G : Top ⟶ Set]上的伴随，切片于一个空间。在固定空间[x]上，诱导函子[G↓x : (Top↓x) ⟶ (Set↓Gx)]具有一个右伴随[L]，它通过精确地声明开集为[x]开集[U]的逆像[t⁻¹U]来为函数[t : S ⟶ Gx]赋予拓扑（子空间构造）。当[S]是[Gx]的子集时，这就是子空间拓扑，并且书中指出：“(G↓X)∘L = Id；L是(G↓X)的‘右伴随-右逆’”。按照《SS》第四册第四章的命名，其中伴随的余单元是恒等映射使得左伴随成为左伴随-左逆，那就是伴随[G↓x ⊣ L]，其余单元为恒等，从[L]读取；下面的记录就是这样说明它的。Mac Lane 强调，普遍性性质涉及任意映射进来的空间，而不仅仅是其他子空间。对于一个空间，其对偶成立：[x↓G] 有一个左伴随，它赋予 [S] 具有开前像的集合——当 [t] 是满射时，这是商拓扑或同一化拓扑——“单位是恒等映射，所以 M 是 X↓G 的左伴随-右逆”（商构造）。书中逐字原文在两者之间写道：

   “命题 1. 如果 G: C→D 是一个忠实函子，如果 D 有等化器，并且对于每个 x ∈ C, (G↓x): (C↓x)→(D↓Gx) 有一个右伴随-右逆 L，则 C 有等化器。”它的证明将等化器构建为下方等化器的提升 [L]，这解释了空间上两个映射的经典等化器——它们相等的点，以及子空间拓扑——而无需提及具体点。对偶的内容在书中只是一句话，“现在命题1仅凭范畴的公理就已被证明，所以它的对偶也同样成立”（书第134页）：从切片的左伴随-右逆元得到的共等化器。nLab 的“子空间拓扑”记录了相同的等化器计算，并将子空间的包含映射与拓扑中的正规单态射对应；其“商空间”将对偶构造称为最终拓扑或强拓扑。“七个草图”
   练习 7.32 是子空间构造的基础部分：
   [Y ⊆ X] 的开集是 [B] 的开集 [X] 的迹 [B ∩ Y]，并且包含映射是连续的。该形状具有一般理论。一个函子  [U : C ⟶ D]，沿着它，每一个从  [D] 的对象出发的映射族  [f_i : X ⟶ U S_i] 都有一个初始提升——非正式地说就是“使 f_i 连续的最小拓扑”——是一个拓扑函子，而  [C] 是一个  [D] 上的拓扑具体范畴；从 Top 到 Set 的遗忘函子是典范，每个拓扑函子都是忠实的（Adamek、Herrlich 和 Strecker，第 21.3 定理），并且该概念是自对偶的，因此这样的 [C] 也携带最终结构（nLab，“拓扑具体范畴”）。按照这个定义来看，Mac Lane 的假设是单箭头情况：在  [(S; t)] 处的切片右伴随是单一映射  [t]  的一个通用提升，而右逆条件要求该提升精确地位于  [S] 上——即 nLab 对初始提升定义中的方程  [U(T) = X] ，这是由  [S] 本身承载的一个存在性条件。这样的提升是唯一的，字面意义上而非仅仅到同构，是一个独立的条件，nLab 将其归因于 Adamek、Herrlich 和 Strecker，并将其识别为  [U] 是无痕的；选定的右伴随-右逆并不提供这一条件（这是论证出的，而不是建立的：一个忠实函子可以在每个切片上都有这样一个，而不必是无痕的——空间承载被映射忽略的惰性部分，这些部分随着值 0 被提升）。此文件测量第1号提案消耗了多少。

   ** 交付内容- [Sliced G a : (A ̸ a) ⟶ (X ̸ G a)] 和 [Cosliced G a : (a ̸co A) ⟶ (G a ̸co X)]，Mac Lane 的 [G↓a] 和 [a↓G] 关于 Construction/Slice.v 的 [Slice] 和 [Coslice]：一个对象 [(d; h)] 对应到 [(G d; fmap[G] h]，一个箭头 [m] 对应到 [fmap[G] m]。- [RightAdjointRightInverse S]：一个右伴随 [rari_right]，伴随 [rari_adj : S ⊣ rari_right]，Leibniz 对象方程 [rari_obj c : S (rari_right c) = c]，和 [rari_counit c : counit c ≈ id_cast (rari_obj c)]。“Counit 是恒等式”不是单个 hom-集中的箭头之间的方程，直到提供对象方程，所以这是 Adjunction/LeftInverse.v 的设计核心的一个参数，记录是 [LeftAdjointLeftInverse] 且伴随被移入参数中：桥 [rari_lali] 和 [lali_rari]，两个往返都在 [eq_refl]，在 Structure/SlicedInverse/Strict.v 中。- 点对点的核心。[sliced_equalizer]：给定一对平行的复数 [f g : x ~> y] ，一个下层等化器 [E] 对 [fmap[G] f] 和 [fmap[G] g] 在 [(S, s)] ，一个从 [Sliced G x] 到切片对象 [(S; s)] 的通用箭头 [U] ，以及 [Faithful G] ，箭头 [sliced_eq_arrow : sliced_eq_obj ~> x] —— Mac Lane 的 [Lt : Ls ⟶ x] —— 是 [f] 和 [g] 的等化器。[cosliced_coequalizer] 是对偶，在从 [(Q; q)] 到 [Cosliced G y] 的通用箭头上，直接证明。——书中形式。[equalizers_from_sliced_right_adjoints]（任何 [Sliced G a] 的右伴随 [R a]）以及 [equalizers_from_sliced_RARI]，这是命题 1，并且是前者应用于 [rari_right] 和 [rari_adj] ；[coequalizers_from_sliced_left_adjoints]，是命题 1 在整体现左伴随上的对偶。左伴随的右逆元的对偶，
   Theory/Equivalence/Strict.v 的 [LeftAdjointRightInverse]，是
   Structure/SlicedInverse/Strict.v 的 [coequalizers_from_sliced_LARI]。 - 右逆元条款的作用：[rari_preserves]，[G] 提升的等化器是 [fmap[G] f] 和 [fmap[G] g] 的等化器（它的对象为 [S]，直到 Leibniz [rari_over]，它的箭头为 [s]，直到该类型转换，[rari_arrow_over]）；[equalizers_from_sliced_RARI_preserved] 表示它对于 [equalizers_from_sliced_RARI] 构建的每个等化器。对偶，[lari_preserves]，在卫星中。- [adj_unit_universal_op]：伴随的单元作为通用箭头，从 Adjunction/Determination.v 的 [adj_counit_couniversal] 读取，在 Adjunction/Opposite.v 的 [Opposite_Adjunction]；共等化器书形式的通用箭头来自它。- 见下面 [prop1_needs_faithfulness]。

   ** 每个假设的使用和度量位置Proposition 1 没有使用右逆子句：[equalizers_from_sliced_RARI] 的主体命名了 [rari_right] 和 [rari_adj]，但既不命名 [rari_obj] 也不命名 [rari_counit]，而且它所应用的定理 [equalizers_from_sliced_right_adjoints] 根本没有右逆假设。整体伴随也没有被使用：逐点核心取单一的共通箭头，在下层等化子提供的唯一切片对象 [(S; s)] 中，并且书本形式通过 [adj_counit_couniversal] 从余单元获取它，而在其他地方不参考伴随。两个余等化子形式也是如此，它们只命名 [lari_left] / [lari_adj] 或给定的 [L] 和 [adjL]。忠实性在每个方差的恰好一步中花费，分叉方程。它是 [SlicedEqualizer] 和 [CoslicedCoequalizer] 的一个截面变量（[GF]）。[sliced_desc] 和 [cosliced_desc]——介导箭头的存在性与唯一性——在 [Proof using E U] 下闭合，并且它们的关于回读不携带任何 [Faithful] 参数。[sliced_fork] 和 [cosliced_cofork] 需要 [Proof using E U GF]：在带有 [Proof using E U] 的临时副本上，每个都会被拒绝并显示 “使用了以下未声明的截面变量：GF。” 因此，提升的下降仅来自楼下的等化器和余泛性质，而忠实性则证明了提升箭头会分叉。

   ** 忠实性不可省略[prop1_needs_faithfulness] 通过删除忠实性假设，并在一个宇宙实例上对所有 [A]、[X] 和 [G] 量化，驳斥了命题1。反例模型是 [Erase Parallel : Parallel ⟶ _1] (Instance/Parallel.v, Instance/One.v)。[Parallel] 的每个切片都有终对象 [(a; id)]，并且 [erase_slice_RARI] 使得函子在其上保持常量，成为每个 [Sliced (Erase Parallel) a] 的右伴随右逆——对象方程是对 [_1] 切片的一种情况分析，并且伴单位条件成立，因为该切片是薄的 ([slice_one_hom_eq])。[_1] 有等化子 ([One_HasEqualizers])。但是，[par_arrow_one] 和 [par_arrow_two] 这对根本没有分叉 ([parallel_pair_unforked])，所以 [Parallel] 没有等化子 ([Parallel_no_equalizers])，并且 [Erase Parallel] 不是忠实的 ([Erase_Parallel_not_faithful])。[sliced_RARI_without_faithfulness] 汇总了这四个事实。双重是卫星的 [prop1_dual_needs_faithfulness] 。

   ** 优势在 [eq_refl] 处保持，与 [Example] 相同：[Sliced_fobj]、[Sliced_fmap]、[Cosliced_fobj]、[Cosliced_fmap]；[adj_unit_universal_op_obj] 和 [adj_unit_universal_op_arrow]（通用箭头就是单位，如 Adjunction/Determination.v 的 counit 回读所示）；[rari_eq_obj] 和 [rari_eq_arrow]（由右伴随右逆构建的点态等化器就是 [rari_right L (S; s)]）；[equalizers_from_sliced_RARI_obj] 和 [equalizers_from_sliced_RARI_arrow]（在 [HasEqualizers] 层面上相同），以及 [coequalizers_from_sliced_left_adjoints_obj] 和 [coequalizers_from_sliced_left_adjoints_arrow]。总共十二个。书本形式通过投影读取下层（余）等化器，而不是通过 [match]，以便那些回读能够达到 [eq_refl]：如果在下层等化器上用 [destruct] 来书写，相同的书本形式在 [eq_refl] 处其对象回读会被拒绝（"无法统一"，从树中编译出），stdlib 的 [sigT] 没有定义性的 eta。莱布尼茨但不是 [eq_refl] : [rari_over : G (`1 (rari_right L (S; s))) = S]，它是字段 [rari_obj] 的 [f_equal projT1]；在一个变量 [L] 上，该字段是它的唯一来源。同样，莱布尼茨通过 [destruct] 在方程 [slice_id_cast_1] 上：切片箭头的第一个分量被 [id_cast] 传输，是第一个分量的传输，一个变量方程上的箭头之间的莱布尼茨方程，属于 Construction/Quotient.v 的 [id_cast_refl] 已经声明的类型。直到 [≈] ：[rari_arrow_over]，派生方程和传输的箭头。[rari_preserves] 是由 [IsEqualizer_transport] 从 [rari_over] 和 [rari_arrow_over] 组装的数据，[equalizers_from_sliced_RARI_preserved] 通过 [eq_refl] 读取返回达到它，无需进一步转换。关于中介箭头除了其唯一存在性之外没有其他声明。该文件包含六个 [Defined]（按标记计数）：[sliced_desc]，[cosliced_desc]，[IsEqualizer_transport]，[One_HasEqualizers] 的第二个义务，[erase_slice_adj] 和 [erase_slice_RARI]。每个都携带数据（一个中介箭头、一个均衡器、一个附加物、一条记录），并按数据约定保存在 [Defined]；没有一个是承重的，通过将所有六个与卫星的四个一起翻转到 [Qed]，在一个临时副本中测量，该副本可编译两个文件。

   ** 宇宙，通过在每个常量上使用 About 测量[Sliced@{oA hA oX hX u u0 u1 u2}] 和 [Cosliced] 保持类别在它们自己的层次，[A : Category@{oA hA hA}] 和 [X : Category@{oX hX hX}]。它们的区块不携带方程：扎定的 [hA <= hX] 是 [G : A ⟶ X] 自身施加的，以及每个切片实例（[hA < u]，[hX < u0]）的一个严格界限，这是 Construction/Slice.v 对 [Slice] 和 [Coslice] 的自身 [u2 < u1]。四个回读具有相同的形状。每两个类别中的其他常量在一个 Hom 层次上绑定它们，[A : Category@{oA h h}] 和 [X : Category@{oX h h}]，在 BINDER 中并且在任何块中没有方程。识别是继承的，而且哪个供体强制它是通过隔离测量的：一个部分声明 [hA] 和 [hX] 分开，一条 [Context] 线路发生变化，并且一个琐碎的 [Example] 通过 About 读回。共宇箭头 [CouniversalArrow ((S; s)) (Sliced G x)] 单独打印 [hA = hX]（Theory/Universal/Arrow/Dual.v 的 [CouniversalArrow] 在其自身块中承载方程 [u0 = u2]），[Faithful G] 单独打印它（Theory/Functor.v 的 [Faithful] 在一个 Hom 层次上绑定两个类别），并且一个切片伴随 [Sliced G x ⊣ R] 打印它（两个反向方向的函子已经做到了）。[Sliced G x] 单独存在时，
   [IsEqualizer] 单独存在时仅打印 [hA <= hX]，DUAL 箭头也是如此：[UniversalArrow ((Q; q)) (Cosliced G y)] 单独存在时不打印方程。因此，均衡器核心由两个独立的给予者绑定，协同均衡器核心仅通过忠实性绑定，而书本形式通过伴随关系绑定；它们都是继承的，在这里没有引入新的。在 Instance/Top/Forgetful.v 的 [Top_Forget] 处，两个 hom 层无论如何是重合的（[Top@{h o}] 和 [Sets@{h so}] 都在 [h] 处有 hom）。一个同一性位于宇宙实例中，而不是位于任何区块中，并且在此被揭示。无论两个同阶层级何时重合，[Sliced] 和 [Cosliced]（[hA < u] 和 [hX < u0] 的 [u] 和 [u0]，每个片段一个）的两个切片辅助宇宙会在一个宇宙中被实例化：[equalizers_from_sliced_RARI] 读取 [Sliced@{oA h oX h u u u5 u6}]，[sliced_equalizer] 和 [cosliced_coequalizer] 读取 [Sliced@{oA h oX h u3 u3 u0 u}] 及其 [Cosliced] 对应的双胞，下面的反驳读取 [Sliced@{u4 u5 u2 u5 u3 u3 u u0}]。没有捐赠者强制执行：一个琐碎的 [Example] 在 [Sliced G x] 上 单独，在一个绑定两个类别到同一同源级别 [h] 的部分中，已经回读 [Sliced@{oA h oX h u u u0 u1}]（关于，树外），并且当同源级别分开时 [UniversalArrow ((Q; q)) (Cosliced G y)] 单独保持两个宇宙；因此，这两个随后携带相同的单一绑定 [h < _]，当此文件的常量被展开时被合并。它在测量时不花费任何代价：Instance/Top/Subspace.v 的 [subspace_RARI] 和 [quotient_LARI] 读作 [Sliced@{so o so o u0 u0 so so}] 和 [Cosliced@{so o so o u0 u0 so so}] 并为两种书籍形式提供输入，并且位于 [Top_Forget] 的实例化类型检查通过。[RightAdjointRightInverse@{oA oC h u u0}] 在绑定器中有一个同级别 [h]，由其第一个字段强制：在声明 [hA < hC] 后，一个记录除了参数 [S : A ⟶ C] 之外只包含 [rari_right : C ⟶ A] 将被拒绝（"无法强制 hA = ... 因为 hA < hC <= ..."）。它的一个严格界限 [h < u] 是 Theory/Adjunction.v 的 [Adjunction] 类自身的 [h1 < so]，通过逐个添加字段来衡量：仅 [rari_right] 会使块为空，而 [rari_adj] 会引入 [h < u]。在此文件的73个常量中（打印模块、记录、其构造函数及投影，以及每个[Program]义务），关于日志中没有任何字界限的[Set]，并且没有块携带方程；在每个其常量绑定类别的块中，每个严格绑定将一个同构层次关联到一个没有类别绑定器命名的辅助宇宙。见证[One_HasEqualizers] 出于经过测量的原因被注释（卫星的[One_HasCoequalizers] 同样如此）：未注释时，它会最小化为[HasEqualizers@{u Set} 1]（从树中编译出），这会将[prop1_needs_faithfulness] 限定在[Set] 所属的类别中；注释的[@{o h}] 是[HasEqualizers@{o h} _1@{o h h}]。[prop1_needs_faithfulness@{u u0 u1 u2 u3 u4 u5}] 对[A : Category@{u4 u5 u5}] 和[X : Category@{u2 u5 u5}] 进行量化，并具有唯一的严格绑定[u5 < u3]。[Parallel@{u u0}] 即使其对象和箭头类型是 [Set] 排序归纳类型，也不包含 [Set]。

   ** 路径和成本

   闭包：41 个 [Category.*] 模块，不包括此文件（在其 [Require] 列表上的 [打印库]）。单独删除每个 [Require]，Adjunction/Determination.v 的边际成本为 4，Construction/Slice.v、Construction/Quotient.v、Structure/Equalizer/Fork.v 和 Structure/Coequalizer.v 各为 1，其余十一项为 0。有两个常量是重建而不是被消耗，每个都在针对该列表的测量中：- [adj_unit_universal_op] 有 Adjunction/Representability.v 的 [adj_unit_universal] 声明以及相同的两个 [eq_refl] 回读；需要该模块将增加 12 个模块（从 41 增加到 53）。
   - [IsEqualizer_transport] 沿着顶点的 Leibniz 方程移动一个等化器；Adjunction/CokernelPair.v 的 [IsEqualizer_along_iso]（顶点的同构，封闭 [Qed]）可以使用，并会增加 20 个模块（从 41 增加到 61）。严格逆半 -- 通向 Adjunction/LeftInverse.v 的桥梁
   以及对偶的 LARI 形式 -- 是 Structure/SlicedInverse/Strict.v，因为 Theory/Equivalence/Strict.v 会在这里添加 14 个模块（从 41 到 55；仅 Adjunction/LeftInverse.v 就有 12 个）并且那些常量是它唯一的使用者。余等化子核心是直接证明的，而不是作为等化子核心的对偶读取：[Slice (A^op) a] 和 [(Coslice A a)^op] 将三角方程定向相反（[`2 y ∘ f ≈ `2 x] 与 [`2 y ≈ f ∘ `2 x] 相对），因此那条路线需要一个传输函子 -- 是论证的，而非测量的。

   [#[local] 义务战术 := idtac] 在整个文件范围内设置，如同在 Adjunction/LeftInverse.v 和 Theory/Equivalence/Strict.v 中一样，并且每个义务都是手动完成的。

   ** 先前工作，已测量不存在名为 [RightAdjointRightInverse] 的声明：在此文件之前的完整单词搜索仅在 Adjunction/Diagonal/Connected.v 的头部找到了散文，该文件使用这个名称表示不同的概念，并已经在此文件中就地更正。[LeftAdjointLeftInverse] (#376) 和 [LeftAdjointRightInverse] (#377) 存在，并设定了遵循的约定。在 [Slice] 编码上，环境类别之间的函子不会诱导出切片之间的函子：Construction/Slice/Pullback.v 的 [Bang_Functor]（后组合）和 [Star_Functor]（基变换）沿一个类别的箭头移动。Construction/Comma/Functorial.v 的 [Comma_reindex] 确实给出了逗号形式的切片函子，[(Id[A] ↓ =(a)) ⟶ (Id [X] ↓ =(G a))]，其对象回读在 [eq_refl]（从树中编译出来）；[Sliced] 直接在 [Slice] 上声明，因为那是编码 [CouniversalArrow] 并且在这里使用等化器记录。Structure/Limit/Creation.v 的 [CreatesLimit] 是一个不同的概念：它从 [G ◯ K] 的极限开始并要求其唯一的提升，而这里的提升是由切片伴随提供的，并且没有声明其唯一性。碰撞：在此文件及其附属文件的82个名称上没有碰撞（每个常量打印模块列表，除了[Program]的义务，以及记录及其构造函数），由[find | xargs grep -lw]在其他所有[.v]文件上进行，并通过已知存在的名称进行仪器检查。以探针注册测量的全字匹配命中数为三个文件：Instance/Top/Subspace.v（其中十个名称）和Test/ProbeSubspace457.v（全部82个名称，在其保护块中），这些文件使用或引用这些常量，但未声明任何名称，以及前面提到的Adjunction/Diagonal/Connected.v的头部文本（一个名称）。那是在三次重命名之后：[par_one] 和 [par_two] 分别是 Instance/Proset/Transform.v 和 Theory/Natural/Transformation/Arrows.v，而 [point_adj] 是 Adjunction/LeftInverse.v，这是卫星所需的。

   ** 注册

   没有为实例解析注册任何内容：右伴右逆元是一个被选择的伴随，通过显式传递，正如 Adjunction/LeftInverse.v 和 Theory/Equivalence/Strict.v 对它们的记录规定的那样。[Faithful] 和（余）等化器结构是按类隐式获取的实例。

   ** 未交付- 该文件中没有具体实例。见证是  
   Instance/Top/Subspace.v 的，作用于 Instance/Top/Prop.v 的 Prop 值空间：[subspace_RARI] 和 [quotient_LARI]（子空间和商空间构造，见 [Sliced PForget X] 和 [Cosliced PForget X]），以及 [PTop_HasEqualizers] 和 [PTop_HasCoequalizers]，由 [equalizers_from_sliced_RARI] 和卫星的 [coequalizers_from_sliced_LARI] 构建；《七个素描》的练习 7.32 也在其中。在 Instance/Top/Forgetful.v 的
   [Top_Forget] 类型对齐 -- 在树外编译，带有
   [Top_Forget_Faithful] 提供，  [equalizers_from_sliced_RARI] 那里
   的类型是
   [HasEqualizers Sets@{h so} → (∀ a, RightAdjointRightInverse
   (Sliced Top_Forget a)) → HasEqualizers Top@{h o}] -- 但没有假设在那里被解除，并且
   Instance/Top/Subspace/TypeValued.v 记录了为什么切片的
   函子伴随关系不是  [Adjunction] 在 Type-valued 上的记录
   [Top] 。- 没有逆向（这里没有任何内容从等化器推导出切片伴随），没有多箭初始提升，没有积或一般极限（参见 Maclane:V.9:remark1, #458），没有右伴随-右逆的唯一性，没有对具有某个伴随的函子进行刻画（类似于练习 IV.4.4 对左伴随-左逆的情况），也没有对调解箭头与伴随转换的回读。- 两半之间没有对偶性；每一半都是独立证明的。
*)

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(* * ** The sliced functors [G/a] and [a/G] / * ** 切片函子 [G/a] 和 [a/G] *)

(*
 Mac Lane's G↓a : (A↓a) ⟶ (X↓Ga), on this library's [Slice] encoding:
 an object (d; h : d ~> a) goes to (G d; G h), an arrow m to G m. 

 --------
 Mac Lane 的 G↓a : (A↓a) ⟶ (X↓Ga)，在这个库的 [Slice] 编码下：一个对象 (d; h : d ~> a) 映射为 (G d; G h)，一个箭头 m 映射为 G m。
*)
Program Definition Sliced@{oA hA oX hX +} {A : Category@{oA hA hA}}
  {X : Category@{oX hX hX}} (G : A ⟶ X) (a : A) :
  @Slice A a ⟶ @Slice X (G a) := {|
  fobj := fun h => (G (`1 h); fmap[G] (`2 h));
  fmap := fun h k m => (fmap[G] (`1 m); _)
|}.
Next Obligation.
  intros; simpl.
  rewrite <- fmap_comp.
  apply fmap_respects.
  exact (`2 m).
Qed.
Next Obligation.
  intros ? ? ? ? x y m m' Hm; simpl.
  apply fmap_respects.
  exact Hm.
Qed.
Next Obligation.
  intros ? ? ? ? x; simpl.
  apply fmap_id.
Qed.
Next Obligation.
  intros ? ? ? ? x y z m m'; simpl.
  apply fmap_comp.
Qed.

(* The dual, a↓G : (a↓A) ⟶ (Ga↓X), on the [Coslice] encoding. / 双对偶，a↓G : (a↓A) ⟶ (Ga↓X)，在 [Coslice] 编码上。 *)
Program Definition Cosliced@{oA hA oX hX +} {A : Category@{oA hA hA}}
  {X : Category@{oX hX hX}} (G : A ⟶ X) (a : A) :
  @Coslice A a ⟶ @Coslice X (G a) := {|
  fobj := fun h => (G (`1 h); fmap[G] (`2 h));
  fmap := fun h k m => (fmap[G] (`1 m); _)
|}.
Next Obligation.
  intros; simpl.
  rewrite <- fmap_comp.
  apply fmap_respects.
  exact (`2 m).
Qed.
Next Obligation.
  intros ? ? ? ? x y m m' Hm; simpl.
  apply fmap_respects.
  exact Hm.
Qed.
Next Obligation.
  intros ? ? ? ? x; simpl.
  apply fmap_id.
Qed.
Next Obligation.
  intros ? ? ? ? x y z m m'; simpl.
  apply fmap_comp.
Qed.

Example Sliced_fobj@{oA hA oX hX +} {A : Category@{oA hA hA}}
  {X : Category@{oX hX hX}} (G : A ⟶ X) (a : A) (h : @Slice A a) :
  Sliced G a h = (G (`1 h); fmap[G] (`2 h)) := eq_refl.

Example Sliced_fmap@{oA hA oX hX +} {A : Category@{oA hA hA}}
  {X : Category@{oX hX hX}} (G : A ⟶ X) (a : A) (h k : @Slice A a)
  (m : h ~> k) : `1 (fmap[Sliced G a] m) = fmap[G] (`1 m) := eq_refl.

Example Cosliced_fobj@{oA hA oX hX +} {A : Category@{oA hA hA}}
  {X : Category@{oX hX hX}} (G : A ⟶ X) (a : A) (h : @Coslice A a) :
  Cosliced G a h = (G (`1 h); fmap[G] (`2 h)) := eq_refl.

Example Cosliced_fmap@{oA hA oX hX +} {A : Category@{oA hA hA}}
  {X : Category@{oX hX hX}} (G : A ⟶ X) (a : A) (h k : @Coslice A a)
  (m : h ~> k) : `1 (fmap[Cosliced G a] m) = fmap[G] (`1 m) := eq_refl.

(** ** Right-adjoint-right-inverses / ** 右伴随右逆 *)

(*
 [R] is a right-adjoint-right-inverse of [S] when [S ⊣ R] with counit the
 identity.  As in Adjunction/LeftInverse.v, "counit the identity" is the
 Leibniz object equation [S (R c) = c] together with the counit being
 [≈] the identity transported along it. 

 --------
 当  [S ⊣ R]  的余单位是恒等映射时，[R] 是 [S] 的右伴随右逆。如在 Adjunction/LeftInverse.v 中，“余单位是恒等映射”是 Leibniz 对象方程 [S (R c) = c] 与余单位沿它传递的恒等映射 [≈]。
*)
Record RightAdjointRightInverse@{oA oC h +} {A : Category@{oA h h}}
  {C : Category@{oC h h}} (S : A ⟶ C) : Type := {
  rari_right : C ⟶ A;
  rari_adj : S ⊣ rari_right;
  rari_obj (c : C) : S (rari_right c) = c;
  rari_counit (c : C) :
    @counit C A S rari_right rari_adj c ≈ id_cast (rari_obj c)
}.

Arguments rari_right {A C S} _.
Arguments rari_adj {A C S} _.
Arguments rari_obj {A C S} _ _.
Arguments rari_counit {A C S} _ _.

(* * ** The unit of an adjunction as a universal arrow, by duality / * ** 对偶下，伴随的单位作为一个泛箭头 *)

(*
 Adjunction/Determination.v's [adj_counit_couniversal] read at the
 opposite adjunction.  Both readbacks below are [eq_refl]. 

 --------
 Adjunction/Determination.v 的 [adj_counit_couniversal] 在相反的连接处读取。下面的两个回读都是 [eq_refl]。
*)
Definition adj_unit_universal_op@{oC oD h +} {C : Category@{oC h h}}
  {D : Category@{oD h h}} {F : D ⟶ C} {U : C ⟶ D}
  (A : F ⊣ U) (c : D) : UniversalArrow c U :=
  adj_counit_couniversal (Opposite_Adjunction F U A) c.

Example adj_unit_universal_op_obj@{oC oD h +} {C : Category@{oC h h}}
  {D : Category@{oD h h}} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U) (c : D) :
  @arrow_obj _ _ c U (adj_unit_universal_op A c) = F c := eq_refl.

Example adj_unit_universal_op_arrow@{oC oD h +} {C : Category@{oC h h}}
  {D : Category@{oD h h}} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U) (c : D) :
  @arrow _ _ c U (adj_unit_universal_op A c) = @unit _ _ F U A c := eq_refl.

(** ** Proposition 1, pointwise / ** 命题1，逐点 *)

(*
 One parallel pair, its downstairs equalizer (S, s), and ONE couniversal
 arrow from [Sliced G x] to the object (S; s) of the slice over [G x]:
 no adjunction and no right-inverse clause.  Faithfulness is a section
 variable so that [Proof using] records which lemma spends it. 

 --------
 一对平行项，它的下层等化器 (S, s)，以及一个从 [Sliced G x] 到 [G x] 上切片对象 (S; s) 的通用箭头：没有伴随和没有右逆子句。忠实性是一个截面变量，因此 [Proof using] 记录了哪个引理使用了它。
*)
Section SlicedEqualizer.

Universes oA oX h.
Context {A : Category@{oA h h}} {X : Category@{oX h h}}.
Context (G : A ⟶ X).
Context {x y : A}.
Context (f g : x ~> y).
Context {S : X} (s : S ~> G x).
Context (E : IsEqualizer (fmap[G] f) (fmap[G] g) S s).
Context (U : CouniversalArrow ((S; s) : @Slice X (G x)) (Sliced G x)).
Context `{GF : @Faithful A X G}.

(* Mac Lane's L s and L t : L s ~> x. / Mac Lane 的 L s 和 L t：L s ~> x。 *)
Definition sliced_eq_obj : A := `1 (coarrow_obj U).

Definition sliced_eq_arrow : sliced_eq_obj ~> x := `2 (coarrow_obj U).

(* The fork equation: the only step that spends faithfulness. / 分叉方程：唯一消耗忠诚的步骤。 *)
Lemma sliced_fork : f ∘ sliced_eq_arrow ≈ g ∘ sliced_eq_arrow.
Proof using E U GF.
  apply (@fmap_inj _ _ G GF).
  rewrite !fmap_comp.
  pose proof (`2 (coarrow U)) as He; simpl in He.
  unfold sliced_eq_arrow.
  rewrite <- He.
  rewrite !comp_assoc.
  rewrite (fork_eq E).
  reflexivity.
Qed.

(* Descent: existence from the downstairs equalizer followed by the couniversal property, uniqueness from the couniversal property alone. / 下降：从楼下的均衡器存在，然后是余普遍性质，仅从余普遍性质得到唯一性。 *)
Definition sliced_desc {z : A} (h : z ~> x) (Hh : f ∘ h ≈ g ∘ h) :
  ∃! u : z ~> sliced_eq_obj, sliced_eq_arrow ∘ u ≈ h.
Proof using E U.
  assert (HGh : fmap[G] f ∘ fmap[G] h ≈ fmap[G] g ∘ fmap[G] h).
  { rewrite <- !fmap_comp. now rewrite Hh. }
  pose (D := eq_desc E (fmap[G] h) HGh).
  pose (k := (unique_obj D; unique_property D)
             : @hom (@Slice X (G x)) (Sliced G x (z; h)) (S; s)).
  pose (D' := ump_couniversal_arrows U (d:=(z; h)) k).
  unshelve eapply Build_Unique.
  - exact (`1 (unique_obj D')).
  - exact (`2 (unique_obj D')).
  - intros v Hv.
    pose (vv := (v; Hv) : @hom (@Slice A x) (z; h) (coarrow_obj U)).
    apply (uniqueness D' vv).
    simpl.
    apply (uniqueness D).
    rewrite comp_assoc.
    rewrite (`2 (coarrow U)).
    simpl.
    rewrite <- fmap_comp.
    apply fmap_respects.
    exact Hv.
Defined.

Definition sliced_equalizer :
  IsEqualizer f g sliced_eq_obj sliced_eq_arrow :=
  {| fork_eq := sliced_fork; eq_desc := @sliced_desc |}.

End SlicedEqualizer.

Section CoslicedCoequalizer.

Universes oA oX h.
Context {A : Category@{oA h h}} {X : Category@{oX h h}}.
Context (G : A ⟶ X).
Context {x y : A}.
Context (f g : x ~> y).
Context {Q : X} (q : G y ~> Q).
Context (E : IsCoequalizer (fmap[G] f) (fmap[G] g) Q q).
Context (U : UniversalArrow ((Q; q) : @Coslice X (G y)) (Cosliced G y)).
Context `{GF : @Faithful A X G}.

Definition cosliced_coeq_obj : A := `1 (@arrow_obj _ _ _ _ U).

Definition cosliced_coeq_arrow : y ~> cosliced_coeq_obj :=
  `2 (@arrow_obj _ _ _ _ U).

Lemma cosliced_cofork :
  cosliced_coeq_arrow ∘ f ≈ cosliced_coeq_arrow ∘ g.
Proof using E U GF.
  apply (@fmap_inj _ _ G GF).
  rewrite !fmap_comp.
  pose proof (`2 (@arrow _ _ _ _ U)) as He; simpl in He.
  unfold cosliced_coeq_arrow.
  rewrite He.
  rewrite <- !comp_assoc.
  rewrite (cofork E).
  reflexivity.
Qed.

Definition cosliced_desc {z : A} (h : y ~> z) (Hh : h ∘ f ≈ h ∘ g) :
  ∃! u : cosliced_coeq_obj ~> z, u ∘ cosliced_coeq_arrow ≈ h.
Proof using E U.
  assert (HGh : fmap[G] h ∘ fmap[G] f ≈ fmap[G] h ∘ fmap[G] g).
  { rewrite <- !fmap_comp. now rewrite Hh. }
  pose (D := coeq_desc E (fmap[G] h) HGh).
  assert (Hk : fmap[G] h ≈ unique_obj D ∘ q)
    by (symmetry; exact (unique_property D)).
  pose (k := (unique_obj D; Hk)
             : @hom (@Coslice X (G y)) (Q; q) (Cosliced G y (z; h))).
  pose (D' := ump_universal_arrows U (d:=(z; h)) k).
  unshelve eapply Build_Unique.
  - exact (`1 (unique_obj D')).
  - symmetry; exact (`2 (unique_obj D')).
  - intros v Hv.
    assert (Hv' : h ≈ v ∘ cosliced_coeq_arrow) by (symmetry; exact Hv).
    pose (vv := (v; Hv')
                : @hom (@Coslice A y) (@arrow_obj _ _ _ _ U) (z; h)).
    apply (uniqueness D' vv).
    simpl.
    apply (uniqueness D).
    rewrite <- comp_assoc.
    rewrite <- (`2 (@arrow _ _ _ _ U)).
    simpl.
    rewrite <- fmap_comp.
    apply fmap_respects.
    exact Hv.
Defined.

Definition cosliced_coequalizer :
  IsCoequalizer f g cosliced_coeq_obj cosliced_coeq_arrow :=
  {| cofork := cosliced_cofork; coeq_desc := @cosliced_desc |}.

End CoslicedCoequalizer.

(* * ** Proposition 1 and its dual, as stated / * ** 命题 1 及其对偶，如所陈述 *)

(*
 The downstairs equalizer is read out by projections, not by a [match],
 so that the object and arrow readbacks below hold at [eq_refl]. 

 --------
 楼下的均衡器是通过投影读取的，而不是通过 [match]，因此下面的对象和箭头读回在 [eq_refl] 时成立。
*)
Definition equalizers_from_sliced_right_adjoints@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasEqualizers X}
  (R : ∀ a : A, @Slice X (G a) ⟶ @Slice A a)
  (adjR : ∀ a : A, Sliced G a ⊣ R a) : @HasEqualizers A :=
  {| equalizer := fun x y f g =>
       let S := `1 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g)) in
       let s := `1 (`2 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g))) in
       let E := `2 (`2 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g))) in
       let U := adj_counit_couniversal (adjR x) ((S; s) : @Slice X (G x)) in
       (sliced_eq_obj G s U;
        (sliced_eq_arrow G s U; sliced_equalizer G f g s E U)) |}.

(* Mac Lane's Proposition 1. The right-inverse clause is not consulted: only [rari_right] and [rari_adj] occur in the body. / Mac Lane 的命题 1。右逆子句不被参考：在主体中只出现 [rari_right] 和 [rari_adj]。 *)
Definition equalizers_from_sliced_RARI@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasEqualizers X}
  (L : ∀ a : A, RightAdjointRightInverse (Sliced G a)) : @HasEqualizers A :=
  equalizers_from_sliced_right_adjoints G
    (fun a => rari_right (L a)) (fun a => rari_adj (L a)).

(* The equalizer built is L applied to the downstairs one, on the nose. / 建造的均衡器是 L，应用于楼下的那个，正好。 *)
Example equalizers_from_sliced_RARI_obj@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasEqualizers X}
  (L : ∀ a : A, RightAdjointRightInverse (Sliced G a)) {x y : A}
  (f g : x ~> y) :
  `1 (@equalizer A (equalizers_from_sliced_RARI G L) x y f g)
    = `1 (rari_right (L x)
            (`1 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g));
             `1 (`2 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g))))) :=
  eq_refl.

Example equalizers_from_sliced_RARI_arrow@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasEqualizers X}
  (L : ∀ a : A, RightAdjointRightInverse (Sliced G a)) {x y : A}
  (f g : x ~> y) :
  `1 (`2 (@equalizer A (equalizers_from_sliced_RARI G L) x y f g))
    = `2 (rari_right (L x)
            (`1 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g));
             `1 (`2 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g))))) :=
  eq_refl.

(* The dual of Proposition 1, with whole left adjoints; its LARI form is Structure/SlicedInverse/Strict.v's [coequalizers_from_sliced_LARI]. / 命题1的对偶，具有完整的左伴随；其LARI形式是 Structure/SlicedInverse/Strict.v 的 [coequalizers_from_sliced_LARI]。 *)
Definition coequalizers_from_sliced_left_adjoints@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasCoequalizers X}
  (L : ∀ a : A, @Coslice X (G a) ⟶ @Coslice A a)
  (adjL : ∀ a : A, L a ⊣ Cosliced G a) : @HasCoequalizers A :=
  {| coeq := fun x y f g =>
       let Q := `1 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g)) in
       let q := `1 (`2 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g))) in
       let E := `2 (`2 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g))) in
       let U := adj_unit_universal_op (adjL y) ((Q; q) : @Coslice X (G y)) in
       (cosliced_coeq_obj G q U;
        (cosliced_coeq_arrow G q U; cosliced_coequalizer G f g q E U)) |}.

Example coequalizers_from_sliced_left_adjoints_obj@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasCoequalizers X}
  (L : ∀ a : A, @Coslice X (G a) ⟶ @Coslice A a)
  (adjL : ∀ a : A, L a ⊣ Cosliced G a) {x y : A} (f g : x ~> y) :
  `1 (@coeq A (coequalizers_from_sliced_left_adjoints G L adjL) x y f g)
    = `1 (L y (`1 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g));
               `1 (`2 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g))))) :=
  eq_refl.

Example coequalizers_from_sliced_left_adjoints_arrow@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasCoequalizers X}
  (L : ∀ a : A, @Coslice X (G a) ⟶ @Coslice A a)
  (adjL : ∀ a : A, L a ⊣ Cosliced G a) {x y : A} (f g : x ~> y) :
  `1 (`2 (@coeq A (coequalizers_from_sliced_left_adjoints G L adjL) x y f g))
    = `2 (L y (`1 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g));
               `1 (`2 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g))))) :=
  eq_refl.

(* * ** What the right-inverse clause adds / * ** 右逆子句添加的内容 *)

Lemma slice_id_cast_1@{o h +} {C : Category@{o h h}} {u : C}
  {p q : @Slice C u} (e : p = q) :
  `1 (@id_cast (@Slice C u) p q e)
    = @id_cast C (`1 p) (`1 q) (f_equal (@projT1 _ _) e).
Proof. destruct e; reflexivity. Qed.

(* An equalizer moved along a Leibniz equation of apexes. / 一个均衡器沿着顶点的莱布尼茨方程移动。 *)
Definition IsEqualizer_transport@{o h +} {C : Category@{o h h}}
  {a b : C} {f g : a ~> b} {q q' : C} {e : q ~> a} {e' : q' ~> a}
  (p : q' = q) :
  e' ≈ e ∘ id_cast p → IsEqualizer f g q e → IsEqualizer f g q' e'.
Proof.
  destruct p; simpl; intros He E.
  rewrite id_right in He.
  unshelve econstructor.
  - rewrite He; exact (fork_eq E).
  - intros z h Hh.
    unshelve eapply Build_Unique.
    + exact (unique_obj (eq_desc E h Hh)).
    + rewrite He; exact (unique_property (eq_desc E h Hh)).
    + intros v Hv; apply (uniqueness (eq_desc E h Hh)).
      rewrite <- He; exact Hv.
Defined.

Section RARIPreserves.

Universes oA oX h.
Context {A : Category@{oA h h}} {X : Category@{oX h h}}.
Context (G : A ⟶ X).
Context {x y : A}.
Context (f g : x ~> y).
Context {S : X} (s : S ~> G x).
Context (E : IsEqualizer (fmap[G] f) (fmap[G] g) S s).
Context (L : RightAdjointRightInverse (Sliced G x)).

Definition rari_couniversal :
  CouniversalArrow ((S; s) : @Slice X (G x)) (Sliced G x) :=
  adj_counit_couniversal (rari_adj L) (S; s).

Example rari_eq_obj :
  sliced_eq_obj G s rari_couniversal = `1 (rari_right L (S; s)) := eq_refl.

Example rari_eq_arrow :
  sliced_eq_arrow G s rari_couniversal = `2 (rari_right L (S; s)) := eq_refl.

(* The lifted object sits over S: Leibniz, from the field [rari_obj]. / 被提升的物体位于 S 上：莱布尼茨，来自领域 [rari_obj]。 *)
Definition rari_over : G (`1 (rari_right L (S; s))) = S :=
  f_equal (@projT1 _ _) (rari_obj L (S; s)).

Lemma rari_arrow_over :
  fmap[G] (`2 (rari_right L (S; s))) ≈ s ∘ id_cast rari_over.
Proof using Type.
  pose proof (`2 (@counit _ _ _ _ (rari_adj L) (S; s))) as H; simpl in H.
  rewrite <- H.
  apply compose_respects; [reflexivity|].
  transitivity (`1 (@id_cast (@Slice X (G x)) _ _ (rari_obj L (S; s)))).
  - exact (rari_counit L (S; s)).
  - rewrite (slice_id_cast_1 (rari_obj L (S; s))).
    reflexivity.
Qed.

(* G carries the lifted equalizer onto an equalizer of the images. / G 将提升的均衡器带到图像的均衡器上。 *)
Definition rari_preserves :
  IsEqualizer (fmap[G] f) (fmap[G] g)
    (G (`1 (rari_right L (S; s)))) (fmap[G] (`2 (rari_right L (S; s)))) :=
  IsEqualizer_transport rari_over rari_arrow_over E.

End RARIPreserves.

(* The same at the [HasEqualizers] level: [G] preserves every equalizer that [equalizers_from_sliced_RARI] constructs. / 在 [HasEqualizers] 级别上也是一样：[G] 保留了 [equalizers_from_sliced_RARI] 构建的每一个均衡器。 *)
Definition equalizers_from_sliced_RARI_preserved@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasEqualizers X}
  (L : ∀ a : A, RightAdjointRightInverse (Sliced G a)) {x y : A}
  (f g : x ~> y) :
  IsEqualizer (fmap[G] f) (fmap[G] g)
    (G (`1 (@equalizer A (equalizers_from_sliced_RARI G L) x y f g)))
    (fmap[G] (`1 (`2 (@equalizer A (equalizers_from_sliced_RARI G L)
                         x y f g)))) :=
  rari_preserves G f g _ (`2 (`2 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g))))
    (L x).

(* * ** Faithfulness cannot be dropped / * ** 忠诚不能被放弃 *)

(*
 [Parallel]'s two arrows have no fork at all, so [Parallel] has no
 equalizers; its erasure to [_1] is not faithful; and every other
 hypothesis of Proposition 1 holds there. 

 --------
 [Parallel] 的两支箭头根本没有分叉，所以 [Parallel] 没有均衡器；它向 [_1] 的擦除不是忠实的；并且命题1的其他每一个假设在那里都成立。
*)
Definition par_arrow_one : ParX ~{Parallel}~> ParY := (true; ParOne).
Definition par_arrow_two : ParX ~{Parallel}~> ParY := (false; ParTwo).

Lemma parallel_pair_unforked {q : Parallel} (e : q ~> ParX) :
  par_arrow_one ∘ e ≈ par_arrow_two ∘ e → False.
Proof.
  destruct q, e as [b h].
  - inversion h; subst. simpl. discriminate.
  - destruct (ParHom_Y_X_absurd _ h).
Qed.

Definition Parallel_no_equalizers : @HasEqualizers Parallel → False :=
  fun H =>
    parallel_pair_unforked
      (`1 (`2 (@equalizer Parallel H _ _ par_arrow_one par_arrow_two)))
      (fork_eq
         (`2 (`2 (@equalizer Parallel H _ _ par_arrow_one par_arrow_two)))).

Lemma Erase_Parallel_not_faithful : Faithful (Erase Parallel) → False.
Proof.
  intros [inj].
  pose proof (inj _ _ par_arrow_one par_arrow_two eq_refl) as H.
  discriminate H.
Qed.

(* Annotated: unannotated, this witness minimizes its hom level to [Set]. / 注释：未注释时，该证人将其同类水平最小化为 [Set]。 *)
Program Definition One_HasEqualizers@{o h} : @HasEqualizers _1@{o h h} := {|
  equalizer := fun x y f g => (x; (id; {| fork_eq := _; eq_desc := _ |}))
|}.
Next Obligation. intros; reflexivity. Qed.
Next Obligation.
  intros x y f g z h Hh.
  exists h.
  - destruct h; reflexivity.
  - intros v _; destruct h, v; reflexivity.
Defined.

Lemma slice_one_hom_eq@{o h +} (u : _1@{o h h}) (x y : @Slice _1@{o h h} u)
  (f g : x ~> y) : f ≈ g.
Proof. destruct f as [[] ?], g as [[] ?]; reflexivity. Qed.

Section EraseSlice.

Context (a : Parallel).

#[local] Notation B := (Erase Parallel).

(*
 The right adjoint of [Sliced B a] is constant at the terminal object
 (a; id) of the slice over [a]. 

 --------
 [Sliced B a] 的右伴随在 [a] 上的切片中，在终对象 (a; id) 上是恒定的。
*)
Program Definition erase_slice_right : @Slice _1 (B a) ⟶ @Slice Parallel a := {|
  fobj := fun _ => (a; id);
  fmap := fun _ _ _ => id
|}.
Next Obligation. intros; intros ? ? ?; reflexivity. Qed.
Next Obligation. intros; reflexivity. Qed.
Next Obligation. intros; symmetry; apply id_left. Qed.

Program Definition erase_slice_hom_iso (h : @Slice Parallel a)
  (c : @Slice _1 (B a)) :
  @Isomorphism Sets
    {| carrier := @hom (@Slice _1 (B a)) (Sliced B a h) c;
       is_setoid := @homset (@Slice _1 (B a)) (Sliced B a h) c |}
    {| carrier := @hom (@Slice Parallel a) h (erase_slice_right c);
       is_setoid := @homset (@Slice Parallel a) h (erase_slice_right c) |} := {|
  to := {| morphism := fun _ => (`2 h; _) |};
  from := {| morphism := fun _ => (ttt; _) |}
|}.
Next Obligation. intros; apply id_left. Qed.
Next Obligation. intros; intros ? ? ?; simpl; reflexivity. Qed.
Next Obligation. intros; destruct c as [[] []]; reflexivity. Qed.
Next Obligation. intros; intros ? ? ?; simpl; reflexivity. Qed.
Next Obligation.
  intros; intros [v Hv].
  change (`2 h ≈ v).
  rewrite <- Hv; apply id_left.
Qed.
Next Obligation. intros; intros [[] Hv]; reflexivity. Qed.

Definition erase_slice_adj : Sliced B a ⊣ erase_slice_right.
Proof.
  unshelve eapply
    (@Build_Adjunction' _ _ (Sliced B a) erase_slice_right erase_slice_hom_iso).
  - intros x y z f g; simpl.
    symmetry; exact (`2 g).
  - intros x y z f g.
    change (`2 x ≈ id ∘ `2 x).
    symmetry; apply id_left.
Defined.

Definition erase_slice_RARI : RightAdjointRightInverse (Sliced B a).
Proof.
  unshelve refine {| rari_right := erase_slice_right;
                     rari_adj := erase_slice_adj |}.
  - intros [[] []]; reflexivity.
  - intros c; apply slice_one_hom_eq.
Defined.

End EraseSlice.

Definition sliced_RARI_without_faithfulness :
  (∀ a : Parallel, RightAdjointRightInverse (Sliced (Erase Parallel) a))
  * @HasEqualizers _1
  * (Faithful (Erase Parallel) → False)
  * (@HasEqualizers Parallel → False) :=
  (erase_slice_RARI, One_HasEqualizers, Erase_Parallel_not_faithful,
   Parallel_no_equalizers).

(* Proposition 1 with the faithfulness hypothesis deleted is false. / 删除了忠实性假设的命题 1 是错误的。 *)
Definition prop1_needs_faithfulness :
  (∀ (A X : Category) (G : A ⟶ X), @HasEqualizers X →
     (∀ a : A, RightAdjointRightInverse (Sliced G a)) → @HasEqualizers A)
  → False :=
  fun P => Parallel_no_equalizers
             (P Parallel _1 (Erase Parallel) One_HasEqualizers
                erase_slice_RARI).
