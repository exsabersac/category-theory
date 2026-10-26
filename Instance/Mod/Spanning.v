Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Universal.Element.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Construction.Elements.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.SpanningArrow.
Require Import Category.Adjunction.Representability.Sets.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Mod.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Product.
Require Import Category.Instance.Mod.Representable.
Require Import Category.Instance.Mod.Quotient.
Require Import Category.Instance.Mod.Quotient.Isomorphism.
Require Import Category.Instance.Mod.Tensor.
Require Import Category.Instance.Mod.Bimodule.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   * * Spanning bilinear maps, and the solution set for the tensor product

   nLab:      https://ncatlab.org/nlab/show/tensor+product+of+modules
   nLab:      https://ncatlab.org/nlab/show/solution+set+condition
   nLab:      https://ncatlab.org/nlab/show/subobject
   Wikipedia: https://en.wikipedia.org/wiki/Tensor_product_of_modules

   Mac Lane, “Categories for the Working Mathematician”, 2nd ed. (GTM 5),
   §V.7, book p. 128 (PDF p. 137), is the source of everything below: the
   unnumbered construction of the tensor product from the adjoint functor
   theorem (catalog id `maclane:V.7:construction1`) and Exercise 3 (catalog
   id `maclane:V.7:ex3`).  CITED BY LOCATION AND BY THE IN-TREE CATALOG:
   the printed text was not consulted and no sentence of it is reproduced
   here.  The catalog summaries this file works from live in
   doc/plan/books/maclane/inventory/V.json, and they read:

   construction1 -- “For modules A and B over a commutative ring K, a
   tensor product is a universal element of the set Bilin(A,B;C) of
   bilinear functions beta : A x B -> C into a third K-module C;
   Bilin(A,B;-) is (the object part of) a functor of C.  To get a
   solution set it suffices to consider only the bilinear beta which
   span C, i.e. do not factor through a proper submodule of C; such a C
   consists of all finite sums of the form sum beta(a_i,b_i), which
   bounds its cardinality and gives the solution set condition.  Since
   K-Mod is small-complete and Bilin(A,B;-) : K-Mod -> Set is
   continuous, the adjoint functor theorem yields a universal bilinear
   map A x B -> A tensor B.”

   ex3 -- “For R a ring, A a right R-module and B a left R-module, use
   the adjoint functor theorem to construct A tensor_R B ... Prove that
   A tensor_R B is spanned, as an abelian group, by the elements a
   tensor b.  If S -> R is a morphism of rings, examine the relation
   between A tensor_S B and A tensor_R B.”

   THIS FILE IS THE SPANNING HALF of that programme.  It delivers Mac
   Lane's solution set -- the bilinear maps that span their target -- and
   his “spanned by the elementary tensors”, together with the module-side
   vocabulary they need.  It does NOT build the tensor product from the
   adjoint functor theorem: the two remaining premises of
   `representability_theorem` (Adjunction/Representability/Sets.v),
   namely `Complete (RMod R)` and `PreservesImageLimit (Bilin V V')`, are
   not inhabited here, and the comparison of an AFT-produced object with
   Instance/Mod/Tensor.v's [TensorMod] is not attempted.  See NOT
   DELIVERED.

   WHAT IS DELIVERED, IN NINE STEPS, AND AT WHAT STRENGTH.

   (1) THE SUBMODULE/SUBOBJECT BRIDGE.  Mac Lane's §V.7 Definition 1
   records that “these categorical subobjects agree with the
   element-defined ones in Rng, Grp, Ab and R-Mod”; before this PR
   nothing in tree connected the two at [RMod R] -- `git grep -l 'SubObj'
   5f681ba4 -- Instance/Mod.v Instance/Mod/` returns nothing, and that
   command still reproduces from the merged tree.  [smod_subobj] carries
   a [Submodule] (Instance/Mod/Quotient.v) to a [SubObj]
   (Theory/Subobject.v) and [subobj_smod] carries a subobject back, as
   the image submodule of its mono (`ImageSubmod`, Quotient.v).  The
   subobject round trip is at `≈` on [SubObj W] ([smod_subobj_image_equiv],
   through the two [sub_le]s [smod_subobj_image_le] and
   [smod_subobj_image_ge]) and NOT at [eq_refl]; the submodule round trip
   is only inter-derivable, [smod_round_to] and [smod_round_from], because
   the membership of [subobj_smod (smod_subobj S)] is a sigma over the
   submodule's own carrier and so is a different [Type] from [smod_mem S];
   NEGATIVE 1 of Test/ProbeModSpanning449.v pins that the [eq_refl]
   reading is refused, with [smod_round_iff] beside it as the control.
   What IS [eq_refl] is [smod_subobj_dom], [smod_subobj_mono] and
   [subobj_smod_mem].  [smod_subobj] is built with `@Build_SubObj`
   explicitly: a record literal picks the record's category parameter from
   the first field it elaborates, and that trap is on record in the
   project memory.  The one new module fact is [rmod_image_retract] -- a
   monic map retracts its own image submodule -- whose four laws are one
   and the same argument, [rmod_monic_injective] (Instance/Mod.v)
   applied to [rmod_image_witness].

   (2) THE GENERATED SUBMODULE.  [MGen P] is the submodule generated by a
   [Type]-valued predicate, as an inductive family with FIVE constructors,
   packaged as [SubGenMod P : Submodule M].  Negation is NOT a
   constructor: [smod_neg] (Quotient.v) derives it from (−1)·a, which
   is why [MGen] closes under scalar multiplication where [ABGen] of step
   (8) closes under negation; both are five-constructor inductives, with
   four closure constructors each.
   Leastness comes in both orders: [mgen_least], the [Fixpoint] one case
   per constructor in the idiom of Instance/Variety/Spanning.v, and
   [mgen_sub_le_least], the same fact read as [sub_le] in [SubObj M] --
   the statement #448 left unstated for varieties.

   (3) SPANNING, ELEMENTWISE AND CATEGORICALLY, AND THEIR EQUIVALENCE.
   [RBilinearSpanning β] says every element of the target lies in
   [MGen (rbl_image β)]; [Spanning (Bilin V V') (global_element β)] is
   #448's categorical form (Adjunction/SpanningArrow.v) at the functor
   [Bilin V V'] (Instance/Mod/Tensor.v) and the global element
   (Theory/Universal/Element.v) of a bilinear map.  The two are
   equivalent, as two named functions [rbilinear_spanning_to_spanning] and
   [spanning_to_rbilinear_spanning] packaged by [rbilinear_spanning_iff].
   The forward direction is the substantial one: a subobject through which
   β factors bilinearly has an image submodule containing the image of β,
   hence containing everything [MGen] generates, so its mono is surjective
   as well as injective and therefore splits ([rmod_split]).  The backward
   direction corestricts β to [SubGenMod (rbl_image β)]
   ([rbl_gen_corestrict]) and reads the splitting off the conclusion.
   Neither direction goes through [sub_le_top_iso] or
   [spanning_forces_top] (Adjunction/SpanningArrow.v): the
   positive form of [Spanning] hands back the splitting directly, so those
   two are available to a reader but are not consumed here.

   (4) THE ELEMENTARY TENSORS SPAN.  [tensor_gen_spanning] is Mac Lane's
   “spanned by the elements a ⊗ b” for [TensorMod], by induction on
   [MTerm] in five cases -- the same five [tensor_hom_ext]
   (Instance/Mod/Tensor.v) runs one level up -- and
   [tensor_gen_spanning_categorical] is the same fact in the [Spanning]
   form, obtained from (3) rather than re-proved.

   (5) WIDE PULLBACKS IN [RMod R].  [RMod_HasWidePullbacks] is the tree's
   SECOND [HasWidePullbacks] instance (Instance/Sets/SubobjectLattice.v's
   [Sets_HasWidePullbacks] was the only one) and its first at an algebraic
   category.  The apex is the submodule of Instance/Mod/Product.v's
   [ProdMod] on which all the maps of the family agree; the projections
   are [prod_proj] after the inclusion and the mediator is a tuple.

   IT DOES NOT DISCHARGE THE HYPOTHESIS OF [spanning_solution_set], AND
   THE REASON IS A UNIVERSE, MEASURED.  With Set Printing Universes,

   About RMod_HasWidePullbacks.

   reports, RE-MEASURED 2026-09-17 in the PR “algebraic carriers are
   sets” (an earlier revision of this comment printed the ring's three
   universe slots in the wrong order, as [RingObject@{u u2 u3}], and did
   not carry the [Set < u0] line; nothing else in the readback changed,
   and neither correction touches the argument below),

   RMod_HasWidePullbacks@{u u0 u1 u2 u3} :
   ∀ R : RingObject@{u3 u u2},
   HasWidePullbacks@{u u u0 u} (RMod@{u0 u1 u3 u2 u} R)
   ( * ... Set < u0, u < u0, u < u1, u3 <= u0, ... * )

   -- the class's INDEX universe is instantiated at [u], the universe of
   the module CARRIERS, which the block pins strictly BELOW [u0], the
   universe where [RModObject R] itself lives.  [SubObj W] lives at [u0],
   so [FactoringFamily] (Adjunction/SpanningArrow.v) does too, and

   Check (@spanning_solution_set (RMod R) Sets (Bilin V V')
   (RMod_HasWidePullbacks R) GP SetsOne).

   is refused with

   The term “RMod_HasWidePullbacks R” has type
   “HasWidePullbacks@{u_car u_car u_obj u_car} (RMod@{u_obj ...} R)”
   while it is expected to have type
   “HasWidePullbacks@{u_idx u_idx' u_obj' u_car} (RMod@{u_obj' ...} R)”
   (universe inconsistency: Cannot enforce u_car = u_idx because
   u_car < u1 <= u2 <= u_idx)

   (the generated universe names are replaced by readable ones,
   positionally; everything else is verbatim, and NEGATIVE 2 of
   Test/ProbeModSpanning449.v re-runs it).  The pin
   is ATTRIBUTED, not guessed: it is not [Submodule]'s and not the class's
   but [ProdMod]'s, whose carrier is the dependent function space
   [∀ i : I, carrier (cmon_setoid (V i))], so the index universe is at or
   below the carrier universe, while an object of [RMod R] has its carrier
   strictly below the object universe.  A control makes this exact:

   Check (fun (W : obj[RMod R]) (A : @SubObj (RMod R) W -> obj[RMod R])
   => (@ProdMod R (@SubObj (RMod R) W) A : obj[RMod R])).

   is refused with “The term \”ProdMod A\“ has type \”RModObject R\“
   while it is expected to have type \”obj[RMod R]\“ (universe
   inconsistency: Cannot enforce u_prod = u_car because u_car < u1 <= u2
   <= u3 <= u_prod)” -- a four-step chain from the module carrier level
   up to the product's, re-run as NEGATIVE 3 of the probe with a
   [ProdMod] over a bare [Type] beside it.  ANNOTATION WAS TRIED AND
   CANNOT HELP: the two constraints are [index ≤ carrier] (from the
   product) and [carrier < object] (from [RModObject] being a record over
   a [SetoidObject]), and [SubObj W] is at the object universe, so no
   annotation of the instance can satisfy both.  This is the same
   obstruction Adjunction/SpanningArrow.v records for
   [Sets_HasWidePullbacks], reproduced on the module side and now with the
   donor named.  BOTH REFUSALS ARE PINNED: they are NEGATIVES 2 and 3 of
   Test/ProbeModSpanning449.v, each stripped and re-run alone in a copy of
   the whole probe so the refusal kind could be read rather than guessed,
   with the abstract-[HWP] application and a [ProdMod] over a bare [Type]
   as the paired positive controls.  The instance is landed anyway, as a
   wide pullback in [RMod R] worth having; what it does not do is stated
   here rather than left to a reader.

   (6) [Bilin V V'] PRESERVES WIDE PULLBACKS, UNCONDITIONALLY.
   [Bilin_PreservesWidePullbacks] is the first witness of
   [PreservesWidePullbacks] (Adjunction/SpanningArrow.v) for ANY
   functor in the tree.  It is proved against an ARBITRARY
   [IsWidePullback] rather than against the apex of (5) -- which is what
   keeps its index universe free, and therefore what lets it be applied at
   [FactoringFamily] -- by a small element calculus: [wpull_elem_unique]
   (elements of the apex are separated by the projections),
   [wpull_elem] (the element determined by a compatible family) and
   [wpull_elem_proj].  All three go through [rmod_by_element]
   (Instance/Mod/Representable.v), r ↦ r·m, evaluated at the unit of
   R, and through [wide_pullback_jointly_monic] (Structure/Pullback/
   Wide.v).  Monicity of the family is not spent: the hypothesis [Hm]
   of [PreservesWidePullbacks] is accepted and ignored, so the statement
   proved is stronger than the interface asks for.

   (7) THE SOLUTION SET.  Inside a section over
   `Context \`{HWP : @HasWidePullbacks (RMod R)}` -- the ONE premise this
   file leaves open, for the measured reason in (5) --
   [tensor_solution_set] is Mac Lane's covering family for [Bilin V V']
   -- a solution set in the sense of the record, with no smallness -- and
   [tensor_esols] its element-wise form.  Three [eq_refl] readbacks pin
   what survives the two repackagings: [esol_index tensor_esols] IS
   [SpanningArrowsOutOf (Bilin V V') SetsOne], [esol_obj] is the first
   projection and [esol_elem] is the spanning bilinear map evaluated at
   [ttt].  NO SMALLNESS: [sol_index] and [esol_index] are bare [Type]s, so
   Mac Lane's cardinality bound (“all finite sums”) is not part of what
   the records ask for and nothing below supplies it.

   THE OTHER ROUTE TO THE SAME INDEX.  Instance/Mod/TensorAFT.v carries
   [tensor_esols_direct], Mac Lane's p. 128 argument written out
   UNCONDITIONALLY: it corestricts an arbitrary bilinear map to the
   submodule generated by its image ([rbl_gen_corestrict] of step (3)
   below), proves the corestriction spans, and covers by the inclusion --
   no wide pullbacks anywhere, so the hypothesis this section leaves open
   is not needed there.  The two solution sets are indexed by the SAME
   type ON THE NOSE: [tensor_esols_same_index] in that file is
   [esol_index (@tensor_esols R V V' HWP)
   = esol_index (tensor_esols_direct V V') := eq_refl],
   with [HWP] passed EXPLICITLY, since [RMod_HasWidePullbacks] would be
   found by resolution and then refused at the application for the reason
   in (5).  Mac Lane's Lemma 2 route (here) and his p. 128 route (there)
   therefore agree about WHAT the solution set is indexed by and differ
   only in what they assume.

   (8) EXERCISE 3, THE SPANNING CLAUSE.  [ABGen P] is the subgroup of an
   abelian group generated by a predicate and [bal_gen_spanning] says
   Instance/Mod/Bimodule.v's [BalTensor] -- the genuinely balanced
   tensor of a right and a left module over a possibly non-commutative
   ring, which lands in [Ab] -- is spanned as an abelian group by the
   elements [bs_gen n m], by induction on [bsum] in four cases.  [ABGen]
   has an [abgen_neg] constructor where [MGen] has [mgen_smul], there
   being no scalar in [Ab] to derive negation from; the two inductives
   have five constructors each.  Instance/Ab/DirectedColimit.v
   has an [AbSubgroup] record but its generated notion [InGen]
   is generated by a finite LIST rather than by a predicate, so
   nothing there is reused and that file is deliberately not required
   here; [abgen_least] is stated against a bare closed predicate instead.

   (9) EXERCISE 3, THE BASE-CHANGE CLAUSE.  For `phi : T ~{Rng}~> R` --
   Mac Lane's “morphism of rings S → R”, with T for his S -- restriction
   of scalars (Instance/Rng/Mod.v) gives [bal_right_T] and
   [bal_left_T], and [bal_change] is the comparison group homomorphism
   A ⊗_T B → A ⊗_R B.  It carries generators to generators at [eq_refl]
   ([bal_change_gen]); it is SURJECTIVE ([bal_change_surjective], by
   induction on the formal sums of the target), so A ⊗_R B is a quotient
   of A ⊗_T B; and it is characterised as [bal_med] of the R-balanced
   generator read as a T-balanced map ([bal_change_is_med], through
   [bal_med_unique], Bimodule.v).  ITS KERNEL IS NOT DESCRIBED --
   see NOT DELIVERED.

   NOT DELIVERED, and the scope of each statement is this file rather than
   the tree.  (1) NO TENSOR PRODUCT FROM THE ADJOINT FUNCTOR THEOREM IS
   BUILT HERE.  [representability_theorem] needs `Complete (RMod R)` and
   `PreservesImageLimit (Bilin V V')`; neither is built here and no
   constant below mentions either.  Both are landed by the siblings of
   this PR -- [RMod_Complete] at Instance/Mod/Limit.v and
   [Bilin_PreservesImageLimit] in Instance/Mod/TensorAFT.v -- and so is
   the headline of `maclane:V.7:construction1`, the universal bilinear
   map produced by the AFT: [tensor_via_AFT] in that file is
   [representability_theorem] at those two, CONDITIONALLY on an
   [ElementSolutionSet] whose index the theorem pins at the ring's
   CARRIER universe, which neither this file's [tensor_esols] nor that
   file's [tensor_esols_direct] can supply, both being indexed by a sigma
   over the OBJECTS of [RMod R] (the refusal is NEGATIVE 1 of that
   file's probe, Test/ProbeModTensorAFT449.v).  What is landed HERE is
   the solution-set
   half, itself conditional for the different reason of (4).  (2) NO
   COMPARISON WITH [TensorMod].  Nothing below
   relates an AFT-produced representing object to Instance/Mod/Tensor.v's
   [TensorMod], at [eq_refl] or at `≅`; [tensor_gen_spanning] says only
   that the EXISTING tensor's canonical bilinear map is one of the
   spanning arrows the solution set is indexed by.  (3) NO SMALLNESS and
   so no cardinality bound, for the reason in (7); this is inherited from
   the records of Adjunction/GAFT.v and Adjunction/Representability/
   Sets.v, and Adjunction/SpanningArrow.v says the same of
   itself.  (4) NO [HasWidePullbacks] AT THE UNIVERSE THE SOLUTION SET
   WANTS, for the measured reason in (5); [tensor_solution_set] and
   [tensor_esols] are therefore axiom-free CONDITIONALS over that one
   hypothesis, in the sense docs/INHABITATION.md uses.  (5) THE KERNEL OF
   [bal_change] IS NOT DESCRIBED.  Surjectivity is proved; nothing below
   identifies the kernel, exhibits it as generated by the elements
   (a·r) ⊗ b − a ⊗ (r·b) for r outside the image of phi, or shows the
   comparison is an isomorphism in any case.  Mac Lane's “examine the
   relation” is answered with a surjection and its universal
   characterisation, and no more.  (6) NO NON-DEGENERACY WITNESS.  No
   concrete ring map is instantiated, so nothing below shows [bal_change]
   is ever NOT injective; the tree has no non-commutative ring at all
   (Instance/Mod/Tensor.v records that gap), so the
   non-commutative reading of ex3 is uninstantiated here as elsewhere.
   (7) ONLY THREE OF THE BOUNDARIES ARE PINNED IN Test/.
   Test/ProbeModSpanning449.v carries this file's full 25-`Require` list
   plus the file, and pins three: NEGATIVE 1, the submodule round trip
   being inter-derivable and not [eq_refl] (CONVERSION, with
   [smod_round_iff] as the control); NEGATIVE 2, the exported
   [RMod_HasWidePullbacks] not discharging [spanning_solution_set]'s
   hypothesis (UNIVERSE, with the abstract-[HWP] application beside it as
   the positive control); and NEGATIVE 3, the donor one level down at
   [ProdMod] indexed by [SubObj] (UNIVERSE, with a [ProdMod] over a bare
   [Type] as the control).  Each was re-run alone with its guard stripped
   in a copy of the whole probe, and the refusal kinds are read off the
   messages rather than guessed.  Two more facts of this file are pinned
   in Test/ProbeModTensorAFT449.v: the shared index ([c_same_index]) and
   [MGen]'s positional predicate (its NEGATIVE 7).
   Everything else claimed here -- the eq_refl readbacks of section 7, the
   two load-bearing [Defined]s, the equivalence of the two spanning
   forms, the ex3 clauses -- rests on being compiled here and is not
   guarded by a probe.  (8) NO [Complete]-free route: nothing below
   weakens [representability_theorem] or offers a spanning-only
   representability statement.  (9) NO PROPER-RESTRICTION WITNESS.
   Nothing below exhibits a bilinear map that is NOT spanning, so the
   restriction Mac Lane's argument turns on is not shown to cut anything
   down; non-vacuity is witnessed only positively, by
   [tensor_gen_spanning_categorical].  Combined with (3), the solution set
   is Mac Lane's in SHAPE and in nothing that bounds it.

   MEASURED. 80 `.glob` heads -- 40 `def`, 19 `prf`, 10 `constr`, 8
   `scheme`, 2 `ind`, 1 `inst` -- plus 26 [Program] obligations, which
   appear in NEITHER the `.glob` heads NOR `Search inside`, enumerated with
   `strings Instance/Mod/Spanning.vo | grep -o
   '[A-Za-z0-9_]*_obligation_[0-9]*' | sed 's/^[0-9]*//' | sort -u` (the
   junk digit prefix stripped, not dropped) and cross-checked against
   `Print Module Category.Instance.Mod.Spanning`, which lists the same 26
   and no others: four each for [rmod_image_retract], [mgen_sub_include],
   [rmod_split] and [wpull_mod_tuple], five each for [rbl_gen_corestrict]
   and [wpull_bilin_med]. (The census also reports three
   [ImageSubmod_obligation_*]; those are Instance/Mod/Quotient.v's and
   are not counted here.) All 106 are “Closed under the global context”,
   zero `Axioms:` lines, run through a scratch file of `Print Assumptions
   Category.Instance.Mod.Spanning.<name>.` -- the obligations need the
   QUALIFIED name, the short one is not in scope after `Require Import` --
   and all 106 are registered in the `make print-assumptions` gate.
   Counted BY TOKEN with `grep -ow` over the file BELOW this header
   comment: 37 `Qed` and 16 `Defined` as proof terminators. (A `grep -ow`
   over the WHOLE file reports more, because it also counts the occurrences
   of both words in this comment; no whole-file figure is quoted here,
   since quoting one would change it.) EXACTLY TWO of the sixteen are
   LOAD-BEARING, measured by flipping each to `Qed` in a copy of the whole
   file: [WPullSub] (then [wpull_mod_commutes] stops, its `\`2 p i j` no
   longer applying), and [bal_change_bil] (then the [eq_refl] of
   [bal_change_gen] stops). The other fourteen were flipped to `Qed`
   TOGETHER and the file still compiles, so their transparency is a choice.
   Universes ([About] under `Set Printing Universes`, all 106): no [Set]
   in the universe block or printed type of any declared head or
   obligation, the only [Set] in the module being the auto-generated
   [MGen_rec] and [ABGen_rec] motives, which target [Set] by
   construction -- `grep -cw Set` over the 106 [About] blocks returns 2
   and both are those.  Nothing here is pinned, and
   [GAFT_from_spanning]'s [Set] pin was never reached because no constant
   below feeds [GAFT].  (CORRECTION, PR “algebraic carriers are sets”,
   2026-09-17: that pin no longer exists -- [Section GAFTFromSpanning] was
   widened off [Set] and the theorem now reads
   [Category@{u u0 u0}] / [Category@{u1 u2 u2}] with [u <= u0].  The
   sentence is kept in the past tense because the reason it gave for this
   file's independence is unchanged: no constant below feeds [GAFT], and
   the widening does not make [GAFT_from_spanning] reach [RMod R] either
   -- see that file's header for the surviving refusal.) [smod_subobj], [subobj_smod], [mgen_sub_le_least]
   and [RMod_HasWidePullbacks] carry no equation and the same two strict
   constraints of [RMod R] itself -- the module carrier universe strictly
   below two others -- [smod_subobj] printing them as `u1 < u`, `u1 < u0`
   and the other three as `u < u0`, `u < u1`;
   [WPullSub] and [RMod_WidePullback] carry [ProdMod]'s ten
   equations (`u = u3 = u5 = u6 = u7 = u8 = u10 = u11 = u12`, `u1 = u4 =
   u9`); [Bilin_PreservesWidePullbacks] carries `u = u0 = u1`, ATTRIBUTED
   by [About] to [rmod_by_element] (Instance/Mod/Representable.v),
   which reports exactly those two equations while [Bilin],
   [wide_pullback_jointly_monic] and [IsWidePullback] each report none;
   [bal_change] and [bal_change_surjective] carry `u = u0 = u1 = u2 = u3 =
   u4`, identifying the THREE universes of BOTH rings, and those five
   equations are the SECTION BINDER's rather than any constant's, isolated
   with a trivial `Example : T = T := eq_refl` closed in four nested
   Sections: with only `Context {T R : RingObject}` it reports NO
   equation; adding `Context (phi : T ~{Rng}~> R)` alone already reports
   all five; adding the two [RModObject] binders adds none, and the file's
   own [bal_left_T], [bal_right_T], [bal_change] and
   [bal_change_surjective] report exactly the same five and no more.
   [RestrictObj], [RigHom_op], [Ring_op] and [Rig_op] each report none,
   and the control `Definition ctl_hom (T R : RingObject) : Type :=
   T ~{Rng}~> R` prints `RingObject@{u1 u1 u1}` for BOTH rings, so the
   whole identification is already [Rng]'s hom and the [RModObject]
   instances over [Ring_op R] and [Ring_op T] add nothing to it.
   Closure 162 files excluding this one, from
   25 `Require`s, by iterated `coqdep`; at the margin
   Adjunction/Representability/Sets.v costs 28, Instance/Mod/Bimodule.v 17,
   Instance/Rng/Mod.v 6, Instance/Mod/Representable.v 2, and four more cost
   1 each, the rest 0. Every `Require` was tested by deletion:
   Category.Theory.Isomorphism and Category.Instance.Ab.Subtract were
   droppable (marginal closure 0 both) and were removed; the remaining 25
   are each needed. Zero DECLARATION-HEAD COLLISIONS: none of the 106
   names is declared anywhere else, measured by scanning every one of the
   1017 other `.glob` files in the tree for a `def`/`prf`/`ind`/`constr`/
   `scheme`/`inst` head equal to one of them (file list from `find`, fed
   through `xargs`, so no `.gitignore` traversal rule can apply), with
   [tensor_gen] as the positive control (declared in
   Instance/Mod/Tensor.glob and Instance/Ab/Tensor.glob, two files) and a
   nonexistent name as the negative. MENTIONS are a different count and
   are not zero: over the 1021 other `.v` files, exactly three mention any
   of the 106 names, all as USES -- Instance/Mod/TensorAFT.v 25 of them,
   Test/ProbeModSpanning449.v 13 and Test/ProbeModTensorAFT449.v 6.
   `make todo` gains FOUR hits, all of them the four guarded commands of
   Test/ProbeModSpanning449.v (the instrument check and the three
   negatives); this file contributes none, in any letter case. 

   --------
   * * 跨双线性映射，以及张量积的解集

   nLab:       https://ncatlab.org/nlab/show/tensor+product+of+modules 
   nLab:       https://ncatlab.org/nlab/show/solution+set+condition 
   nLab:       https://ncatlab.org/nlab/show/subobject 
   Wikipedia:  https://en.wikipedia.org/wiki/Tensor_product_of_modules 

   Mac Lane，《为在职数学家准备的范畴》，第二版 (GTM 5)，
   §V.7，书中第128页（PDF第137页），是以下内容的来源：
   从伴随函子定理（目录ID `maclane:V.7:construction1`）构造张量积的无编号方法和习题3（目录
   ID `maclane:V.7:ex3`）。通过位置和树内目录引用：
   未参考印刷文本，这里也没有复现其中的任何句子。该文件所依据的目录摘要
   存活于 doc/plan/books/maclane/inventory/V.json 中，其内容如下：construction1 -- “对于交换环K上的模A和B，张量积是集合Bilin(A,B;C)中元素的一个普遍元素，该集合由映射β : A x B -> C到第三个K模C的双线性函数组成；Bilin(A,B;-)是C的一个函子的（对象部分）。为了得到一个解集，只需考虑生成C的双线性β，即不通过C的真子模；这样的C由形式为∑β(a_i,b_i)的所有有限和组成，这限定了其基数并给出了解集条件。由于K-Mod是小完全的，而Bilin(A,B;-) : K-Mod -> Set是连续的，伴随函子定理给出了一个普遍的双线性映射A x B -> A tensor B。”ex3 -- “对于环 R，A 是右 R-模，B 是左 R-模，利用伴随函子定理构造 A ⊗_R B……证明 A ⊗_R B 作为阿贝尔群是由元素 a ⊗ b 张成的。如果 S -> R 是环的态射，考察 A ⊗_S B 与 A ⊗_R B 之间的关系。”该文件是该程序的跨越一半。它提供了 Mac Lane 的解集——跨越其目标的双线性映射——以及他的“由基本张量生成”，以及它们所需的模块端词汇。它并没有从伴随函子定理构建张量积：`representability_theorem`（伴随性/可表示性/集合.v）的另外两个前提，即 `Complete (RMod R)` 和 `PreservesImageLimit (Bilin V V')`，在这里没有被实现，并且没有尝试将 AFT 生成的对象与 Instance/Mod/Tensor.v 的 [TensorMod] 进行比较。请参见未交付部分。

   交付内容分九步进行，并说明其强度。(1) 子模/子对象桥梁。Mac Lane 的 §V.7 定义 1 记录了“这些范畴子对象在 Rng、Grp、Ab 和 R-Mod 中与由元素定义的子对象一致”；在这个 PR 之前，树中没有任何内容将两者在 [RMod R] 处连接起来 -- `git grep -l 'SubObj' 5f681ba4 -- Instance/Mod.v Instance/Mod/` 返回为空，而且该命令在合并后的树中仍能复现。[smod_subobj] 将 [Submodule] (Instance/Mod/Quotient.v) 连接到 [SubObj] (Theory/Subobject.v)，而 [subobj_smod] 将子对象带回，作为其单射 (`ImageSubmod`, Quotient.v) 的像子模。子对象回程位于 `≈` 的 [SubObj W] 上（[smod_subobj_image_equiv]，通过两个 [sub_le] 的 [smod_subobj_image_le] 和 [smod_subobj_image_ge]）而不是在 [eq_refl] 上；子模块回程只是相互可导的，[smod_round_to] 和 [smod_round_from]，因为 [subobj_smod (smod_subobj S)] 的成员身份是子模块自身承载体上的一个 sigma，因此和 [smod_mem S] 是不同的 [Type]；Test/ProbeModSpanning449.v 的 NEGATIVE 1 引脚表明 [eq_refl] 的读取被拒绝，旁边的 [smod_round_iff] 作为控制。真正的 [eq_refl] 是 [smod_subobj_dom]、[smod_subobj_mono] 和 [subobj_smod_mem]。[smod_subobj] 是用 `@Build_SubObj` 明确构建的：记录字面量从它展开的第一个字段中选择记录的类别参数，这个陷阱记录在项目内存中。唯一的新模块事实是 [rmod_image_retract] —— 单射映射会回撤其自身的像子模块 —— 它的四条定律是相同的论点 [rmod_monic_injective]（Instance/Mod.v）应用于 [rmod_image_witness]。(2) 生成的子模。[MGen P] 是由一个 [Type] 值谓词生成的子模，作为具有五个构造子的归纳族，打包为 [SubGenMod P : Submodule M]。否定不是构造子：[smod_neg]（Quotient.v）从 (−1)·a 推导出它，这就是为什么 [MGen] 在标量乘法下封闭，而步骤 (8) 中的 [ABGen] 在取否下封闭；两者都是五构造子的归纳类型，每个都有四个封闭构造子。最小性出现在两个顺序中：[mgen_least]，在 Instance/Variety/Spanning.v 的习惯中，每个构造子有一个 [Fixpoint] 的情况，以及 [mgen_sub_le_least]，将同一事实在 [SubObj M] 中读作 [sub_le] ——语句 #448 对于簇变体未被陈述。(3) 跨越、逐元素与逐范畴及其等价性。[RBilinearSpanning β] 表示目标的每个元素都位于 [MGen (rbl_image β)]；[Spanning (Bilin V V') (global_element β)] 是 #448 的范畴形式（Adjunction/SpanningArrow.v），在函子 [Bilin V V']（Instance/Mod/Tensor.v）及双线性映射的全局元素（Theory/Universal/Element.v）下。两者是等价的，作为两个命名函数 [rbilinear_spanning_to_spanning] 和 [spanning_to_rbilinear_spanning]，由 [rbilinear_spanning_iff] 打包。正向是实质性的一面：通过 β 双线性分解的子对象，其像子模包含 β 的像，因此包含 [MGen] 生成的一切，因此它的单态不仅是单射也是满射，从而分裂（[rmod_split]）。反向则将 β 限定到 [SubGenMod (rbl_image β)]（[rbl_gen_corestrict]）并从结论中读取分裂。两个方向都不经过 [sub_le_top_iso] 或 [spanning_forces_top]（Adjunction/SpanningArrow.v）：[Spanning] 的正形式直接返回拆分，因此这两个对读者是可用的，但在这里不被使用。

   (4) 基本张量张成。[tensor_gen_spanning] 是 Mac Lane 对 [TensorMod] 的“由元素 a ⊗ b 张成”的定义，通过 [MTerm] 的归纳在五种情况下成立——同样的五种 [tensor_hom_ext]（Instance/Mod/Tensor.v）在上一级运行——而 [tensor_gen_spanning_categorical] 是 [Spanning] 形式下的相同事实，是从 (3) 得到的，而不是重新证明。(5) [RMod R] 中的广泛回拉。[RMod_HasWidePullbacks] 是该树的第二个 [HasWidePullbacks] 实例（Instance/Sets/SubobjectLattice.v 的 [Sets_HasWidePullbacks] 是唯一的一个），并且它在代数范畴中是第一次出现。顶点是 Instance/Mod/Product.v 的 [ProdMod] 上的子模，其中家族的所有映射都相等；投影是在包含之后的 [prod_proj]，中介是一个元组。

   它不会解除 [spanning_solution_set] 的假设，原因是一个宇宙，用度量衡量。在集合打印宇宙下，

   关于 RMod_HasWidePullbacks。报告，于 2026-09-17 在 PR “algebraic carriers are sets” 中重新测量（此评论的早期版本将环的三个宇宙槽顺序打印错误，为 [RingObject@{u u2 u3}]，并且没有包含 [Set < u0] 行；回读中没有其他更改，且这些修正都不影响下面的论证），

   RMod_HasWidePullbacks@{u u0 u1 u2 u3} ：
   对任意 R : RingObject@{u3 u u2},
   HasWidePullbacks@{u u u0 u} (RMod@{u0 u1 u3 u2 u} R)
   ( * ... Set < u0, u < u0, u < u1, u3 <= u0, ... * )

   -- 类的 INDEX 宇宙实例化于 [u]，即模块 CARRIERS 的宇宙，该块严格固定在 [u0] 以下，这里 [RModObject R] 自身存在。[SubObj W] 位于 [u0]，因此 [FactoringFamily]（Adjunction/SpanningArrow.v）也位于那里，且检查 (@spanning_solution_set (RMod R) 集合 (Bilin V V')
   (RMod_HasWidePullbacks R) GP 集合一).

   被拒绝，提示

   术语 “RMod_HasWidePullbacks R” 的类型为
   “HasWidePullbacks@{u_car u_car u_obj u_car} (RMod@{u_obj ...} R)”
   而期望的类型为
   “HasWidePullbacks@{u_idx u_idx' u_obj' u_car} (RMod@{u_obj' ...} R)”
   （宇宙不一致：无法强制 u_car = u_idx，因为
   u_car < u1 <= u2 <= u_idx）(生成的宇宙名称被替换为可读的名称，位置保持不变；其他所有内容逐字保留，并且 Test/ProbeModSpanning449.v 的 NEGATIVE 2 再次运行它)。引脚是被归属的，而不是猜测的：它不是 [Submodule] 的，也不是类的，而是 [ProdMod] 的，其承载器是依赖函数空间 [∀ i : I, carrier (cmon_setoid (V i))]，因此索引宇宙在承载器宇宙之上或者之下，而 [RMod R] 的对象的承载器则严格低于对象宇宙。一个控制使其精确：

   Check (fun (W : obj [RMod R] ) (A : @SubObj (RMod R) W -> obj [RMod R] )
   => (@ProdMod R (@SubObj (RMod R) W) A : obj [RMod R] ))。被拒绝，提示“术语 “ProdMod A” 的类型为 “RModObject R”，而期望类型为 “obj [RMod R] ”（宇宙不一致：无法强制 u_prod = u_car 因为 u_car < u1 <= u2 <= u3 <= u_prod）”——这是从模块承载层到产品的四步链，重新运行为探针的负三步，旁边有一个裸 [Type] 上的 [ProdMod]。尝试过注释但无效：两个约束分别为 [index ≤ carrier]（来自产品）和 [carrier < object]（来自作为 [SetoidObject] 的记录的 [RModObject]），而 [SubObj W] 在对象宇宙，因此实例的任何注释都无法同时满足这两个约束。这与 Adjunction/SpanningArrow.v 对 [Sets_HasWidePullbacks] 的记录阻碍相同，在模块端重现，现在捐赠者已命名。两次拒绝都被固定：它们是 Test/ProbeModSpanning449.v 的否定项 2 和 3，每个都是单独剥离后在整个探针的副本中重新运行，以便可以读取拒绝类型而不是猜测，并且使用抽象 [HWP] 应用和裸 [Type] 上的 [ProdMod] 作为配对的阳性对照。无论如何，该实例已经落地，作为 [RMod R] 中值得获取的一个大幅回撤；它没有做的事情在这里说明，而不是留给读者去猜测。(6) [Bilin V V'] 无条件地保持广泛的拉回。[Bilin_PreservesWidePullbacks] 是 [PreservesWidePullbacks]（Adjunction/SpanningArrow.v）在树中对任意函子的第一个见证。它是针对任意 [IsWidePullback] 而非针对（5）的顶点——这正是保持其索引宇宙自由的原因，因此可以在 [FactoringFamily] 上应用——通过一个小元素演算证明的：[wpull_elem_unique]（顶点的元素通过投影分开）、[wpull_elem]（由兼容族确定的元素）以及 [wpull_elem_proj]。三者都经过 [rmod_by_element]（Instance/Mod/Representable.v），r ↦ r·m，在 R 的单位处求值，并经过 [wide_pullback_jointly_monic]（Structure/Pullback/Wide.v）。家庭的单一性没有消耗：[Hm] 的假设 [PreservesWidePullbacks] 被接受并忽略，所以证明的陈述比接口要求的更强。(7) 解集合。在 `Context \` {HWP : @HasWidePullbacks (RMod R)}` 的一个部分中——这个文件为其保留的唯一前提，出于 (5) 中的谨慎理由——[tensor_solution_set] 是 [Bilin V V'] 的 Mac Lane 覆盖族——按记录意义上的解集合，没有小性——以及 [tensor_esols] 其按元素形式。三个 [eq_refl] 回读固定了在两次重新包装后存留下来的内容：[esol_index tensor_esols] 是 [SpanningArrowsOutOf (Bilin V V') SetsOne]，[esol_obj] 是第一投影，[esol_elem] 是在 [ttt] 上评估的生成双线性映射。没有小性：[sol_index] 和 [esol_index] 是简单的 [Type]，因此 Mac Lane 的基数界（“所有有限和”）不是记录要求的一部分，下面也没有提供它。通向相同索引的另一条路径。Instance/Mod/TensorAFT.v 包含 [tensor_esols_direct]，Mac Lane 第128页的论证被无条件地写出：它将任意双线性映射限制到其像生成的子模（下面步骤(3) 的 [rbl_gen_corestrict]），证明了核心限制生成了整个空间，并通过包含来覆盖——没有广义拉回，所以本节留下的假设在那里并不需要。这两个解集的索引完全相同［字面意义上的］：该文件中的 [tensor_esols_same_index] 为 [esol_index (@tensor_esols R V V' HWP) = esol_index (tensor_esols_direct V V') := eq_refl]，并且 [HWP] 被显式传递，因为 [RMod_HasWidePullbacks] 会通过解析发现，但在应用中由于步骤(5) 的原因被拒绝。Mac Lane 的引理2路线（在这里）以及他第128 路由（那里）因此在解决方案集是按什么索引上达成一致，只是在他们假设什么上有所不同。(8) 练习 3，生成子句。[ABGen P] 是由谓词生成的阿贝尔群的子群，而 [bal_gen_spanning] 表示 Instance/Mod/Bimodule.v 的 [BalTensor] ——一个右模和左模在可能非交换环上的真正平衡张量，它属于 [Ab]——作为阿贝尔群由元素 [bs_gen n m] 张成，通过 [bsum] 的归纳分为四种情况。[ABGen] 有一个 [abgen_neg] 构造器，其中 [MGen] 拥有 [mgen_smul]，因为在 [Ab] 中没有标量可用来导出负值；这两个归纳量各有五个构造器。Instance/Ab/DirectedColimit.v 有一个 [AbSubgroup] 记录，但它生成的概念 [InGen] 是由一个有限 LIST 生成的，而不是由一个谓词生成的，因此那里没有任何内容被重用，并且该文件在此刻故意不需要；[abgen_least] 是针对一个纯闭合谓词声明的。(9) 练习 3，底变换子句。对于 `phi : T ~{Rng}~> R`——  
   Mac Lane 的“环 S → R 的态射”，将 T 代替他的 S——标量限制（Instance/Rng/Mod.v）给出 [bal_right_T] 和 [bal_left_T]，而 [bal_change] 是比较群同态  
   A ⊗_T B → A ⊗_R B。它将生成元在 [eq_refl]（[bal_change_gen]）处映射到生成元；它是满射（[bal_change_surjective]，通过对目标的形式和进行归纳），所以 A ⊗_R B 是 A ⊗_T B 的一个商；并且它被描述为 R-平衡生成元作为 T-平衡映射（[bal_change_is_med]，通过 [bal_med_unique]，Bimodule.v）。  
   它的核未被描述——见未提供内容。未交付，并且每个声明的范围是此文件而不是树。（1）这里没有构建来自伴随函子定理的张量积。[representability_theorem] 需要 `Complete (RMod R)` 和 `PreservesImageLimit (Bilin V V')`；两者都没有在此构建，并且下面的常量也没有提到任何一个。这两个都由这个 PR 的兄弟提交——[RMod_Complete] 在 Instance/Mod/Limit.v 中，[Bilin_PreservesImageLimit] 在 Instance/Mod/TensorAFT.v 中——而 `maclane:V.7:construction1` 的标题也是如此，`maclane:V.7:construction1` 是 AFT 产生的通用双线性映射：该文件中的 [tensor_via_AFT] 在这两个处是 [representability_theorem]，有条件地依赖于一个 [ElementSolutionSet]，其索引定在环的 CARRIER 宇宙上定理固定的，这个文件的 [tensor_esols] 和那个文件的 [tensor_esols_direct] 都无法提供，因为它们都由 [RMod R] 对象上的 sigma 索引（拒绝是该文件探针 Test/ProbeModTensorAFT449.v 的负 1）。这里提交的是解集的一半，其条件是出于（4）不同的原因。(2) 不与 [TensorMod] 比较。下面的内容
   并未将 AFT 生成的表示对象与 Instance/Mod/Tensor.v 中的
   [TensorMod]、[eq_refl] 或 `≅` 联系起来；[tensor_gen_spanning] 只是
   表明现有张量的规范双线性映射是解集所索引的生成箭头之一。(3) 无小性限制，因此不存在基数界限，原因见 (7)；这从 Adjunction/GAFT.v 和 Adjunction/Representability/Sets.v 的记录中继承，并且 Adjunction/SpanningArrow.v 对其本身也有相同说明。(4) 在解集所需要的宇宙中没有 [HasWidePullbacks]，原因在 (5) 中有详细说明；因此 [tensor_solution_set] 和 [tensor_esols] 在该假设下是无公理的条件性语句，按照 docs/INHABITATION.md 的定义。(5) [bal_change] 的核未被描述。满射性已被证明；下面没有任何内容识别核，也没有展示它是由元素 (a·r) ⊗ b − a ⊗ (r·b) 生成的，其中 r 不在 phi 的像中，或者在任何情况下显示该比较是同构。Mac Lane 的“检查关系”是用一个满射及其泛性质来回答的，仅此而已。(6) 没有非退化性证据。没有具体的环映射被实例化，因此下面没有任何内容显示 [bal_change] 曾经不是单射；该树根本没有非交换环（Instance/Mod/Tensor.v 记录了这个缺口），因此 ex3 的非交换解释在此处和其他地方一样没有被实例化。(7) 在 Test/ 中只有三个边界被固定。Test/ProbeModSpanning449.v 携带该文件完整的 25- `Require` 列表，以及该文件，并固定三个：NEGATIVE 1，子模块往返可互导且不是 [eq_refl]（转换，[smod_round_iff] 作为控制）；NEGATIVE 2，导出的 [RMod_HasWidePullbacks] 没有解除 [spanning_solution_set] 的假设（宇宙，旁边抽象的 [HWP] 应用作为正控制）；以及 NEGATIVE 3，低一级的捐赠者位于 [ProdMod]，由 [SubObj] 索引（宇宙，[ProdMod] 在裸的 [Type] 上作为控制）。每个都在整个探针的副本中单独重新运行，去掉它的保护，并且拒绝类型是从消息中读取，而不是猜测的。这个文件的另外两个事实被固定在 Test/ProbeModTensorAFT449.v 中：共享索引（[c_same_index]）和 [MGen] 的位置谓词（它的 NEGATIVE 7）。这里声称的其余内容——第 7 节的 eq_refl 回读、两个承重的 [Defined]、两个跨越形式的等价性、ex3 条款——都依赖于在此处编译，并且没有探针保护。(8) 无 [Complete] 自由路径：下面没有任何内容削弱 [representability_theorem] 或提供仅跨越的可表示性声明。(9) 无适当限制证人。下面没有展示任何非跨越的双线性映射，因此 Mac Lane 的论证所依赖的限制并未显示削减任何内容；非空性仅由 [tensor_gen_spanning_categorical] 积极体现。结合（3），解集在形状上是 Mac Lane 的，在任何界定它的东西上都不是。测量的。80 个 `.glob` 头 -- 40 个 `def`, 19 个 `prf`, 10 个 `constr`, 8 个 `scheme`, 2 个 `ind`, 1 个 `inst` -- 以及 26 个 [Program] 义务，它们既不出现在 `.glob` 头中，也不出现在 `Search inside` 中，用 `strings Instance/Mod/Spanning.vo | grep -o ' [A-Za-z0-9_] *_obligation_ [0-9] *' | sed 's/^ [0-9] *//' | sort -u` 枚举（去掉了无用的数字前缀，但未删除）并与 `Print Module Category.Instance.Mod.Spanning` 交叉核对，该文件列出了相同的 26 个且没有其他：[rmod_image_retract]、[mgen_sub_include]、[rmod_split] 和 [wpull_mod_tuple] 各四个，[rbl_gen_corestrict] 和 [wpull_bilin_med] 各五个。（人口普查还报告了三个 [ImageSubmod_obligation_*]；那些是 Instance/Mod/Quotient.v 的文件，这里不计算在内。）所有 106 个都“在全局上下文下关闭”，零 `Axioms:` 行，通过一个 `Print Assumptions Category.Instance.Mod.Spanning.<name>.` 的临时文件运行——这些义务需要完整名称，短名称在 `Require Import` 之后不在作用域内——并且所有 106 个都注册在 `make print-assumptions` 门中。按 TOKEN 计数，`grep -ow` 遍历该文件，在此标题注释下：37 个 `Qed` 和 16 个 `Defined` 作为证明终结符。(A  `grep -ow`  
   在整个文件中报告更多，因为它还计算了该注释中两个单词的出现次数；这里没有引用整个文件的数字，因为引用一个会改变它。) 十六个中恰好有两个是承重的，通过在整个文件的副本中将每一个翻转为 `Qed` 来测量：  [WPullSub]  （然后 [wpull_mod_commutes] 停止，它的 `\` 2 p i j` 不再适用），以及 [bal_change_bil]  （然后 [eq_refl] 的 [bal_change_gen] 停止）。其余十四个被一起翻转为 `Qed` ，文件仍然可以编译，所以它们的透明性是可选择的。宇宙（[About] 在 `Set Printing Universes` 下，总共 106 个）：在宇宙块或任何已声明的头或义务的打印类型中没有 [Set]，模块中唯一的 [Set] 是自动生成的 [MGen_rec] 和 [ABGen_rec] 动机，它们通过构造定位 [Set]——在 106 个 [About] 块上的 `grep -cw Set` 返回 2，而且两者都是这些。这里没有任何内容被固定，并且 [GAFT_from_spanning] 的 [Set] 钉从未达到，因为下面没有常量提供 [GAFT]。（更正，PR “代数载体是集合”，2026-09-17：那个钉不再存在——[Section GAFTFromSpanning] 已从 [Set] 扩展，定理现在读作 [Category@{u u0 u0}] / [Category@{u1 u2 u2}] 与 [u <= u0] 。该句保持过去时态，因为它给出这个文件独立性的原因没有改变：没有任何下属常数供给 [GAFT]，并且扩大也不会使 [GAFT_from_spanning] 达到 [RMod R] —— 参见该文件头部的仍然存在的拒绝记录。）[smod_subobj]、[subobj_smod]、[mgen_sub_le_least] 和 [RMod_HasWidePullbacks] 没有方程，并且具有与 [RMod R] 本身相同的两个严格约束——模块承载宇宙严格低于其他两个——[smod_subobj] 将它们分别打印为 `u1 < u`、`u1 < u0`，而其他三个打印为 `u < u0`、`u < u1`；[WPullSub] 和 [RMod_WidePullback] 承载 [ProdMod] 的十个方程（`u = u3 = u5 = u6 = u7 = u8 = u10 = u11 = u12`，`u1 = u4 = u9 `);  [Bilin_PreservesWidePullbacks]ZZ  carries ` u = u0 = u1`），由 [About] 归于 [rmod_by_element]（Instance/Mod/Representable.v），报告的正是这两个方程，同时 [Bilin]，
   [wide_pullback_jointly_monic] 和 [IsWidePullback] 各自报告无；
   [bal_change] 和 [bal_change_surjective] 包含 `u = u0 = u1 = u2 = u3 = u4`，标识两个环的三个宇宙，并且这五个方程是 SECTION BINDER 的，而不是任何常数的，通过一个平凡的 `Example : T = T := eq_refl` 封闭在四个嵌套 Sections 中隔离：仅有 `Context {T R : RingObject}` 时，它报告没有方程；仅添加 `Context (phi : T ~{Rng}~> R)` 时已报告所有五个；添加两个 [RModObject] 绑定器不增加任何方程，并且文件自身的 [bal_left_T]、ZW235WZZ、ZW236WZZ 和 [bal_change_surjective] 精确报告相同的五个方程且没有更多。[RestrictObj]、[RigHom_op]、[Ring_op] 和 [Rig_op] 都报告无，控制 `Definition ctl_hom (T R : RingObject) : Type := T ~{Rng}~> R ` prints ` RingObject@{u1 u1 u1}` 对两个环都是如此，因此整个识别已经是 [Rng] 的同态，[RModObject] 在 [Ring_op R] 和 [Ring_op T] 上的实例没有增加任何内容。排除本文件在内的闭包 162 个文件，由 25 个 `Require` 通过迭代 `coqdep`；边缘上 Adjunction/Representability/Sets.v 花费 28，Instance/Mod/Bimodule.v 17，Instance/Rng/Mod.v 6，Instance/Mod/Representable.v 2，还有四个各花费 1，其余 0。每个 `Require` 都通过删除测试过：Category.Theory.Isomorphism 和 Category.Instance.Ab.Subtract 可以删除（边缘闭包都为 0）并已移除；剩余的 25 个每一个都是必需的。零声明头冲突：106个名称中没有一个在其他任何地方声明过，通过扫描树中其他1017个`.glob`文件，查找是否有`def` / `prf` / `ind` / `constr` / `scheme` / `inst` 头与其中任意一个名称相等（文件列表来自`find`，通过`xargs`处理，因此不适用`.gitignore`遍历规则），使用[tensor_gen]作为阳性对照（在Instance/Mod/Tensor.glob和Instance/Ab/Tensor.glob两个文件中声明）以及一个不存在的名称作为阴性对照。MENTIONS是不同的计数，并且不为零：在其他1021个`.v`文件中，正好有三个文件提及这106个名称中的任何一个，全部作为用途（USES）——Instance/Mod/TensorAFT.v提到25次，Test/ProbeModSpanning449.v提到13次，以及Test/ProbeModTensorAFT449.v提到6次。`make todo` 获得了四次命中，全部是 Test/ProbeModSpanning449.v 的四条受保护命令（仪器检查和三个负号）；该文件不贡献任何命中，无论字母大小写如何。
*)

(* * ** 1. Submodules and subobjects of [RMod R] / * ** 1. [RMod R] 的子模块和子对象 *)

Definition smod_subobj {R : RingObject} {W : RModObject R} (S : Submodule W) :
  @SubObj (RMod R) W :=
  @Build_SubObj (RMod R) W (SubmoduleMod S) (smod_incl S) (smod_incl_monic S).

Example smod_subobj_dom {R : RingObject} {W : RModObject R} (S : Submodule W) :
  sub_dom (smod_subobj S) = SubmoduleMod S := eq_refl.

Example smod_subobj_mono {R : RingObject} {W : RModObject R} (S : Submodule W) :
  sub_mono (smod_subobj S) = smod_incl S := eq_refl.

Definition subobj_smod {R : RingObject} {W : RModObject R}
  (m : @SubObj (RMod R) W) : Submodule W := ImageSubmod (sub_mono m).

Example subobj_smod_mem {R : RingObject} {W : RModObject R}
  (m : @SubObj (RMod R) W) (b : carrier (cmon_setoid W)) :
  smod_mem (subobj_smod m) b
    = { a : carrier (cmon_setoid (sub_dom m))
      & cmon_map (rm_hom (sub_mono m)) a ≈ b } := eq_refl.

(* The witness carried by a member of an image submodule. / 由图像子模块的成员携带的证人。 *)
Lemma rmod_image_witness {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) (p : smod_carrier (ImageSubmod f)) :
  cmon_map (rm_hom f) (`1 (`2 p)) ≈ `1 p.
Proof. exact (`2 (`2 p)). Qed.

(*
 When f is monic its image submodule retracts onto the source: the
 preimage carried by a member is unique, by injectivity, so the second
 projection is a homomorphism.  All four laws are the SAME argument --
 apply injectivity, then [rmod_image_witness] on both sides. 

 --------
 当 f 是首一的时，其像子模会回退到源上：由单射性，成员所携带的原像是唯一的，所以第二投影是一个同态。四条定律的论证完全相同——先应用单射性，然后在两边应用 [rmod_image_witness]。
*)
Program Definition rmod_image_retract {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) (Hm : Monic f) :
  SubmoduleMod (ImageSubmod f) ~{RMod R}~> M := {|
  rm_hom := {| cmon_map := {| morphism :=
    fun p : smod_carrier (ImageSubmod f) => `1 (`2 p) |} |}
|}.
Next Obligation.
  intros R M N f Hm p q Hpq.
  apply (rmod_monic_injective f Hm).
  rewrite (rmod_image_witness f p), (rmod_image_witness f q); exact Hpq.
Qed.
Next Obligation.
  intros R M N f Hm; simpl.
  apply (rmod_monic_injective f Hm).
  rewrite (rmod_image_witness f (cmon_zero (SubmoduleMod (ImageSubmod f)))).
  simpl; symmetry; exact (cmon_map_zero (rm_hom f)).
Qed.
Next Obligation.
  intros R M N f Hm p q; simpl.
  apply (rmod_monic_injective f Hm).
  rewrite (rmod_image_witness f
             (cmon_plus (SubmoduleMod (ImageSubmod f)) p q)).
  rewrite (cmon_map_plus (rm_hom f)).
  rewrite (rmod_image_witness f p), (rmod_image_witness f q).
  simpl; reflexivity.
Qed.
Next Obligation.
  intros R M N f Hm r p; simpl.
  apply (rmod_monic_injective f Hm).
  rewrite (rmod_image_witness f
             (rm_smul (SubmoduleMod (ImageSubmod f)) r p)).
  rewrite (rm_map_smul f).
  rewrite (rmod_image_witness f p).
  simpl; reflexivity.
Qed.

Lemma rmod_image_retract_commutes {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) (Hm : Monic f) :
  @compose (RMod R) _ _ _ f (rmod_image_retract f Hm)
    ≈ smod_incl (ImageSubmod f).
Proof. intro p; exact (rmod_image_witness f p). Qed.

(* The two halves of the round trip on the SUBOBJECT side. / 在子对象侧圆形行程的两个半程。 *)
Definition smod_subobj_image_le {R : RingObject} {W : RModObject R}
  (m : @SubObj (RMod R) W) : sub_le (smod_subobj (subobj_smod m)) m.
Proof.
  exact (existT _ (rmod_image_retract (sub_mono m) (sub_is_monic m))
                  (rmod_image_retract_commutes (sub_mono m)
                     (sub_is_monic m))).
Defined.

Definition smod_subobj_image_ge {R : RingObject} {W : RModObject R}
  (m : @SubObj (RMod R) W) : sub_le m (smod_subobj (subobj_smod m)).
Proof.
  exact (existT _ (mod_image_cores (sub_mono m))
                  (mod_image_factors (sub_mono m))).
Defined.

(*
 Mac Lane V.7 Definition 1's “these categorical subobjects agree with
 the element-defined ones in R-Mod”, one half: every subobject of a
 module IS its image submodule, at `≈` on [SubObj W]. 

 --------
 Mac Lane V.7 定义 1 中的“这些范畴子对象与 R-Mod 中由元素定义的子对象一致”，其中一半：一个模的每个子对象就是它在 `≈` 上的像子模，在 [SubObj W] 上。
*)
Theorem smod_subobj_image_equiv {R : RingObject} {W : RModObject R}
  (m : @SubObj (RMod R) W) : smod_subobj (subobj_smod m) ≈ m.
Proof.
  apply sub_le_antisym.
  - exact (smod_subobj_image_le m).
  - exact (smod_subobj_image_ge m).
Defined.

(*
 The other half, on the SUBMODULE side.  It is NOT [eq_refl]: the
 membership of [subobj_smod (smod_subobj S)] is a sigma over the
 submodule's own carrier, so the two Types differ even though the two
 memberships are inter-derivable. 

 --------
 另一半在子模块一侧。它不是 [eq_refl]：[subobj_smod (smod_subobj S)] 的成员是对子模块自身载体的 sigma，因此即使两个成员可以相互推导，这两种类型仍然不同。
*)
Definition smod_round_to {R : RingObject} {W : RModObject R}
  (S : Submodule W) (a : carrier (cmon_setoid W)) :
  smod_mem (subobj_smod (smod_subobj S)) a → smod_mem S a.
Proof.
  intros [p Hp]; exact (smod_at S Hp (`2 p)).
Defined.

Definition smod_round_from {R : RingObject} {W : RModObject R}
  (S : Submodule W) (a : carrier (cmon_setoid W)) :
  smod_mem S a → smod_mem (subobj_smod (smod_subobj S)) a.
Proof.
  intro Ha.
  unshelve eexists.
  - exact (existT _ a Ha).
  - simpl; reflexivity.
Defined.

Theorem smod_round_iff {R : RingObject} {W : RModObject R}
  (S : Submodule W) (a : carrier (cmon_setoid W)) :
  smod_mem (subobj_smod (smod_subobj S)) a ↔ smod_mem S a.
Proof.
  split; [ exact (smod_round_to S a) | exact (smod_round_from S a) ].
Defined.

(* * ** 2. The submodule generated by a predicate / * ** 2. 由谓词生成的子模 *)

Section Generated.

Context {R : RingObject}.
Context {M : RModObject R}.
Context (P : carrier (cmon_setoid M) → Type).

(*
 FIVE constructors, not four: [mgen_zero] cannot be dropped (P may be
 empty) and [mgen_resp] is required because [smod_resp] is a FIELD of
 [Submodule].  Closure under negation is DERIVED -- [smod_neg]
 (Instance/Mod/Quotient.v) gets it from (−1)·a -- so there is no
 [mgen_neg]. 

 --------
 五个构造函数，不是四个：[mgen_zero] 不能被省略（P 可能为空），而 [mgen_resp] 是必需的，因为 [smod_resp] 是 [Submodule] 的一个字段。对取负的闭包是推导出来的——[smod_neg]（Instance/Mod/Quotient.v）从 (−1)·a 得到它，所以没有 [mgen_neg]。
*)
Inductive MGen : carrier (cmon_setoid M) → Type :=
  | mgen_base : ∀ a, P a → MGen a
  | mgen_resp : ∀ a b, a ≈ b → MGen a → MGen b
  | mgen_zero : MGen (cmon_zero M)
  | mgen_plus : ∀ a b, MGen a → MGen b → MGen (cmon_plus M a b)
  | mgen_smul : ∀ (r : carrier (rig_setoid (ring_rig R))) a,
      MGen a → MGen (rm_smul M r a).

Definition SubGenMod : Submodule M :=
  @Build_Submodule R M MGen mgen_resp mgen_zero mgen_plus mgen_smul.

Definition mgen_incl (a : carrier (cmon_setoid M)) (Ha : P a) :
  smod_mem SubGenMod a := mgen_base a Ha.

(*
 Leastness, in the [Fixpoint] idiom of Instance/Variety/Spanning.v:
 one case per constructor, no tactic. 

 --------
 在 Instance/Variety/Spanning.v 的 [Fixpoint] 术语中，最小性：每个构造函数一个情况，没有策略。
*)
Fixpoint mgen_least (S : Submodule M) (HS : ∀ a, P a → smod_mem S a)
  (a : carrier (cmon_setoid M)) (D : MGen a) {struct D} : smod_mem S a :=
  match D in MGen a' return smod_mem S a' with
  | mgen_base a Ha      => HS a Ha
  | mgen_resp a b H D'  => smod_resp S a b H (mgen_least S HS a D')
  | mgen_zero           => smod_zero S
  | mgen_plus a b D1 D2 =>
      smod_plus S a b (mgen_least S HS a D1) (mgen_least S HS b D2)
  | mgen_smul r a D'    => smod_smul S r a (mgen_least S HS a D')
  end.

End Generated.

(* Leastness read in the SUBOBJECT order of [RMod R] -- the statement #448 left unstated for varieties. / 在 [RMod R] 的 SUBOBJECT 顺序中读取最小值——#448 声明未针对各种情况说明。 *)
Program Definition mgen_sub_include {R : RingObject} {M : RModObject R}
  (P : carrier (cmon_setoid M) → Type) (S : Submodule M)
  (HS : ∀ a, P a → smod_mem S a) :
  SubmoduleMod (SubGenMod P) ~{RMod R}~> SubmoduleMod S := {|
  rm_hom := {| cmon_map := {| morphism :=
    fun p : smod_carrier (SubGenMod P) =>
      existT _ (`1 p) (mgen_least P S HS (`1 p) (`2 p)) |} |}
|}.
Next Obligation. intros R M P S HS p q Hpq; exact Hpq. Qed.
Next Obligation. intros R M P S HS; simpl; reflexivity. Qed.
Next Obligation. intros R M P S HS p q; simpl; reflexivity. Qed.
Next Obligation. intros R M P S HS r p; simpl; reflexivity. Qed.

Theorem mgen_sub_le_least {R : RingObject} {M : RModObject R}
  (P : carrier (cmon_setoid M) → Type) (S : Submodule M)
  (HS : ∀ a, P a → smod_mem S a) :
  sub_le (smod_subobj (SubGenMod P)) (smod_subobj S).
Proof.
  exists (mgen_sub_include P S HS).
  intro p; simpl; reflexivity.
Defined.

(* * ** 3. Spanning bilinear maps, elementwise and categorically / * ** 3. 跨二次型映射，按元素和按范畴 *)

(* The image of a bilinear map, as a bare [Type]-valued predicate -- the membership shape of [ImageSubmod] (Instance/Mod/Quotient.v) with two preimages instead of one. / 作为一个单纯的 [Type] 值谓词的双线性映射的像——[ImageSubmod]（Instance/Mod/Quotient.v）的成员形态，有两个原像而不是一个。 *)
Definition rbl_image {R : RingObject} {V V' W : RModObject R}
  (β : RBilinear V V' W) (x : carrier (cmon_setoid W)) : Type :=
  { v : carrier (cmon_setoid V) &
    { w : carrier (cmon_setoid V') & rbl_map β v w ≈ x } }.

(* Mac Lane's “β spans C”, elementwise: the submodule generated by the image of β is all of W. / Mac Lane 的“β 跨度 C”，逐元地：由 β 的像生成的子模是 W 的全部。 *)
Definition RBilinearSpanning {R : RingObject} {V V' W : RModObject R}
  (β : RBilinear V V' W) : Type :=
  ∀ x : carrier (cmon_setoid W), MGen (rbl_image β) x.

(*
 A bijective module map splits.  The section is not canonical -- it
 picks the preimage the surjectivity datum carries -- and every one of
 its four laws is injectivity applied to the witness equation. 

 --------
 一个双射的模映射是可分的。这个截面不是典范的——它选择了满射数据携带的前像——并且它的四条定律中的每一条都是将单射性应用到证据方程上。
*)
Program Definition rmod_split {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) (Hi : RModInjective f) (Hs : RModSurjective f) :
  N ~{RMod R}~> M := {|
  rm_hom := {| cmon_map := {| morphism :=
    fun b : carrier (cmon_setoid N) => `1 (Hs b) |} |}
|}.
Next Obligation.
  intros R M N f Hi Hs a b Hab.
  apply Hi; rewrite (`2 (Hs a)), (`2 (Hs b)); exact Hab.
Qed.
Next Obligation.
  intros R M N f Hi Hs; simpl.
  apply Hi; rewrite (`2 (Hs (cmon_zero N))).
  symmetry; exact (cmon_map_zero (rm_hom f)).
Qed.
Next Obligation.
  intros R M N f Hi Hs a b; simpl.
  apply Hi.
  rewrite (cmon_map_plus (rm_hom f)).
  rewrite (`2 (Hs (cmon_plus N a b))), (`2 (Hs a)), (`2 (Hs b)).
  reflexivity.
Qed.
Next Obligation.
  intros R M N f Hi Hs r a; simpl.
  apply Hi.
  rewrite (rm_map_smul f).
  rewrite (`2 (Hs (rm_smul N r a))), (`2 (Hs a)).
  reflexivity.
Qed.

Lemma rmod_split_commutes {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) (Hi : RModInjective f) (Hs : RModSurjective f) :
  @compose (RMod R) _ _ _ f (rmod_split f Hi Hs) ≈ @id (RMod R) N.
Proof. intro b; exact (`2 (Hs b)). Qed.

Section SpanningEquivalence.

Context {R : RingObject}.
Context {V V' W : RModObject R}.
Context (β : RBilinear V V' W).

(* The restriction of β to a submodule it factors through, as a datum. / 将 β 限制到它经过的子模上，作为一个数据。 *)
Definition rbl_restrict_image (m : @SubObj (RMod R) W)
  (β' : RBilinear V V' (sub_dom m))
  (Hβ : ∀ v w, cmon_map (rm_hom (sub_mono m)) (rbl_map β' v w)
                 ≈ rbl_map β v w)
  (a : carrier (cmon_setoid W)) (Ha : rbl_image β a) :
  smod_mem (subobj_smod m) a.
Proof.
  destruct Ha as [v [w Hvw]].
  exists (rbl_map β' v w).
  rewrite (Hβ v w); exact Hvw.
Defined.

(* → : elementwise spanning implies Mac Lane's categorical form. / →：逐元素张成意味着麦克莱恩的范畴形式。 *)
Theorem rbilinear_spanning_to_spanning (H : RBilinearSpanning β) :
  Spanning (Bilin V V') (global_element (X := Bilin V V' W) β).
Proof.
  intros m [k Hk].
  (* the lifted bilinear map, and its commutation / 提升的双线性映射及其换位 *)
  pose (β' := k ttt).
  assert (Hβ : ∀ v w, cmon_map (rm_hom (sub_mono m)) (rbl_map β' v w)
                        ≈ rbl_map β v w) by exact (Hk ttt).
  (* the mono is surjective, because its image submodule contains the image of β and therefore everything [MGen] generates / 单射是满射，因为它的像子模包含 β 的像，因此包含 [MGen] 生成的一切 *)
  assert (Hs : RModSurjective (sub_mono m)).
  { intro x.
    exact (mgen_least (rbl_image β) (subobj_smod m)
             (rbl_restrict_image m β' Hβ) x (H x)). }
  assert (Hi : RModInjective (sub_mono m)) by
    exact (rmod_monic_injective (sub_mono m) (sub_is_monic m)).
  exists (rmod_split (sub_mono m) Hi Hs).
  exact (rmod_split_commutes (sub_mono m) Hi Hs).
Defined.

(* The corestriction of β to the submodule generated by its image. / β 在其像所生成的子模上的余限制。 *)
Program Definition rbl_gen_corestrict :
  RBilinear V V' (SubmoduleMod (SubGenMod (rbl_image β))) := {|
  rbl_map := fun v w =>
    existT _ (rbl_map β v w)
      (mgen_base (rbl_image β) (rbl_map β v w)
         (existT _ v (existT _ w (reflexivity _))))
|}.
Next Obligation. intros v v' Hv w w' Hw; simpl; now rewrite Hv, Hw. Qed.
Next Obligation. intros v v' w; simpl; apply rbl_add_l. Qed.
Next Obligation. intros v w w'; simpl; apply rbl_add_r. Qed.
Next Obligation. intros r v w; simpl; apply rbl_smul_l. Qed.
Next Obligation. intros r v w; simpl; apply rbl_smul_r. Qed.

(* ← : Mac Lane's categorical form implies elementwise spanning. / ←：Mac Lane 的范畴形式意味着逐元素生成。 *)
Theorem spanning_to_rbilinear_spanning
  (H : Spanning (Bilin V V') (global_element (X := Bilin V V' W) β)) :
  RBilinearSpanning β.
Proof.
  assert (Hfac : SubFactorsThrough (Bilin V V')
                   (global_element (X := Bilin V V' W) β)
                   (smod_subobj (SubGenMod (rbl_image β)))).
  { exists (global_element (X := Bilin V V' (SubmoduleMod
                                   (SubGenMod (rbl_image β))))
              rbl_gen_corestrict).
    intros u v w; simpl; reflexivity. }
  destruct (H _ Hfac) as [j Hj].
  intro x.
  exact (mgen_resp (rbl_image β) _ _ (Hj x)
           (`2 (cmon_map (rm_hom j) x))).
Defined.

Theorem rbilinear_spanning_iff :
  RBilinearSpanning β
    ↔ Spanning (Bilin V V') (global_element (X := Bilin V V' W) β).
Proof.
  split.
  - exact rbilinear_spanning_to_spanning.
  - exact spanning_to_rbilinear_spanning.
Defined.

End SpanningEquivalence.

(* * ** 4. The elementary tensors span / * ** 4. 基本张量的张成 *)

(*
 Mac Lane's “A ⊗ B is spanned by the elements a ⊗ b”, by induction on
 [MTerm] in five cases -- the same five [tensor_hom_ext]
 (Instance/Mod/Tensor.v) runs one level up.  The [mt_neg] case
 costs nothing new: [smod_neg] already derives closure under negation
 from the four [Submodule] fields. 

 --------
 Mac Lane 的 “A ⊗ B 由元素 a ⊗ b 张成”，通过对 [MTerm] 的归纳在五种情况下——同样的五种 [tensor_hom_ext]（Instance/Mod/Tensor.v） 在上一级运行。[mt_neg] 情况不需要新的代价：[smod_neg] 已经从四个 [Submodule] 域推导出对取反的封闭性。
*)
Theorem tensor_gen_spanning {R : RingObject} (V V' : RModObject R) :
  RBilinearSpanning (@tensor_gen R V V').
Proof.
  intro t; induction t.
  - refine (mgen_base (rbl_image (@tensor_gen R V V')) _ _).
    exists c, c0; reflexivity.
  - exact (mgen_zero (rbl_image (@tensor_gen R V V'))).
  - exact (mgen_plus (rbl_image (@tensor_gen R V V')) _ _ IHt1 IHt2).
  - exact (smod_neg (SubGenMod (rbl_image (@tensor_gen R V V'))) _ IHt).
  - exact (mgen_smul (rbl_image (@tensor_gen R V V')) _ _ IHt).
Defined.

Theorem tensor_gen_spanning_categorical {R : RingObject}
  (V V' : RModObject R) :
  Spanning (Bilin V V')
    (global_element (X := Bilin V V' (TensorMod V V')) (@tensor_gen R V V')).
Proof.
  exact (rbilinear_spanning_to_spanning (@tensor_gen R V V')
           (tensor_gen_spanning V V')).
Defined.

(** ** 5. Wide pullbacks in [RMod R] / ** 5. [RMod R] 的大幅回调 *)

Section WidePullbackMod.

Context {R : RingObject}.
Context {I : Type}.
Context {A : I → RModObject R}.
Context {z : RModObject R}.
Context (g : ∀ i : I, A i ~{RMod R}~> z).

(* The apex is the submodule of the product on which all the [g i] agree -- Mac Lane's intersection, computed elementwise. / 顶点是该产品的子模，所有 [g i] 都在其上达成一致 -- Mac Lane 的交集，逐元素计算。 *)
Definition wpull_mem (f : carrier (cmon_setoid (ProdMod A))) : Type :=
  ∀ i j : I,
    cmon_map (rm_hom (g i)) (f i) ≈ cmon_map (rm_hom (g j)) (f j).

Definition WPullSub : Submodule (ProdMod A).
Proof using A I R g z.
  unshelve refine (@Build_Submodule R (ProdMod A) wpull_mem _ _ _ _).
  - intros a b Hab Ha i j.
    rewrite <- (Hab i), <- (Hab j); exact (Ha i j).
  - intros i j.
    rewrite (cmon_map_zero (rm_hom (g i))).
    rewrite (cmon_map_zero (rm_hom (g j))).
    reflexivity.
  - intros a b Ha Hb i j.
    rewrite (cmon_map_plus (rm_hom (g i)) (a i) (b i)).
    rewrite (cmon_map_plus (rm_hom (g j)) (a j) (b j)).
    rewrite (Ha i j), (Hb i j); reflexivity.
  - intros r a Ha i j.
    rewrite (rm_map_smul (g i) r (a i)), (rm_map_smul (g j) r (a j)).
    rewrite (Ha i j); reflexivity.
Defined.

Definition WPullMod : RModObject R := SubmoduleMod WPullSub.

Definition wpull_mod_proj (i : I) : WPullMod ~{RMod R}~> A i :=
  @compose (RMod R) _ _ _ (prod_proj A i) (smod_incl WPullSub).

Lemma wpull_mod_commutes (i j : I) :
  @compose (RMod R) _ _ _ (g i) (wpull_mod_proj i)
    ≈ @compose (RMod R) _ _ _ (g j) (wpull_mod_proj j).
Proof. intro p; exact (`2 p i j). Qed.

Program Definition wpull_mod_tuple {Q : RModObject R}
  (q : ∀ i : I, Q ~{RMod R}~> A i)
  (Hq : ∀ i j : I, @compose (RMod R) _ _ _ (g i) (q i)
                     ≈ @compose (RMod R) _ _ _ (g j) (q j)) :
  Q ~{RMod R}~> WPullMod := {|
  rm_hom := {| cmon_map := {| morphism :=
    fun x : carrier (cmon_setoid Q) =>
      existT _ (fun i => cmon_map (rm_hom (q i)) x)
               (fun i j => Hq i j x) |} |}
|}.
Next Obligation.
  intros Q q Hq x y Hxy i; simpl.
  exact (proper_morphism (cmon_map (rm_hom (q i))) x y Hxy).
Qed.
Next Obligation.
  intros Q q Hq i; exact (cmon_map_zero (rm_hom (q i))).
Qed.
Next Obligation.
  intros Q q Hq x y i; exact (cmon_map_plus (rm_hom (q i)) x y).
Qed.
Next Obligation.
  intros Q q Hq r x i; exact (rm_map_smul (q i) r x).
Qed.

Definition RMod_WidePullback : WidePullback g.
Proof using A I R g z.
  unshelve refine (@Build_WidePullback (RMod R) I A z g
                     WPullMod wpull_mod_proj _ _).
  - exact wpull_mod_commutes.
  - intros Q q Hq.
    unshelve refine {| unique_obj := wpull_mod_tuple q Hq |}.
    + intros i x; reflexivity.
    + intros v Hv x i; symmetry; exact (Hv i x).
Defined.

End WidePullbackMod.

#[export] Instance RMod_HasWidePullbacks (R : RingObject) :
  HasWidePullbacks (RMod R) :=
  @Build_HasWidePullbacks (RMod R) (@RMod_WidePullback R).

(* * ** 6. [Bilin V V'] preserves wide pullbacks / * ** 6. [Bilin V V'] 保持大幅回调 *)

Section BilinWidePullbacks.

Context {R : RingObject}.
Context (V V' : RModObject R).

Section AtAFamily.

Context {I : Type}.
Context {B : I → RModObject R}.
Context {zz : RModObject R}.
Context (g : ∀ i : I, B i ~{RMod R}~> zz).
Context {P : RModObject R}.
Context {p : ∀ i : I, P ~{RMod R}~> B i}.
Context (HP : IsWidePullback g P p).

(* Elements of the apex are separated by the projections. The bridge from elements to arrows is [rmod_by_element] (Instance/Mod/Representable.v): r ↦ r·x. / 顶点的元素被投影分开。从元素到箭头的桥接是 [rmod_by_element]（Instance/Mod/Representable.v）：r ↦ r·x。 *)
Lemma wpull_elem_unique (x y : carrier (cmon_setoid P))
  (H : ∀ i, cmon_map (rm_hom (p i)) x ≈ cmon_map (rm_hom (p i)) y) : x ≈ y.
Proof using B HP I P R g p zz.
  assert (Hd : ∀ i, @compose (RMod R) _ _ _ (p i) (rmod_by_element R P x)
                      ≈ @compose (RMod R) _ _ _ (p i) (rmod_by_element R P y)).
  { intros i r; simpl.
    rewrite (rm_map_smul (p i) r x), (rm_map_smul (p i) r y).
    now rewrite (H i). }
  pose proof (wide_pullback_jointly_monic HP
                (rmod_by_element R P x) (rmod_by_element R P y) Hd
                (rig_one (ring_rig R))) as Hone.
  simpl in Hone.
  rewrite (rm_smul_one P x), (rm_smul_one P y) in Hone.
  exact Hone.
Qed.

Lemma wpull_elem_maps_agree (b : ∀ i : I, carrier (cmon_setoid (B i)))
  (Hb : ∀ i j : I, cmon_map (rm_hom (g i)) (b i)
                     ≈ cmon_map (rm_hom (g j)) (b j)) :
  ∀ i j : I,
    @compose (RMod R) _ _ _ (g i) (rmod_by_element R (B i) (b i))
      ≈ @compose (RMod R) _ _ _ (g j) (rmod_by_element R (B j) (b j)).
Proof using B I R g zz.
  intros i j r; simpl.
  rewrite (rm_map_smul (g i) r (b i)), (rm_map_smul (g j) r (b j)).
  now rewrite (Hb i j).
Qed.

(* The element of the apex determined by a compatible family of elements: the mediator applied to the unit of R. / 由兼容族元确定的顶点元素：调解器应用于 R 的单位元。 *)
Definition wpull_elem (b : ∀ i : I, carrier (cmon_setoid (B i)))
  (Hb : ∀ i j : I, cmon_map (rm_hom (g i)) (b i)
                     ≈ cmon_map (rm_hom (g j)) (b j)) :
  carrier (cmon_setoid P) :=
  cmon_map (rm_hom (unique_obj
     (wpull_ump HP (fun i => rmod_by_element R (B i) (b i))
        (wpull_elem_maps_agree b Hb))))
    (rig_one (ring_rig R)).

Lemma wpull_elem_proj (b : ∀ i : I, carrier (cmon_setoid (B i)))
  (Hb : ∀ i j : I, cmon_map (rm_hom (g i)) (b i)
                     ≈ cmon_map (rm_hom (g j)) (b j)) (i : I) :
  cmon_map (rm_hom (p i)) (wpull_elem b Hb) ≈ b i.
Proof using B HP I P R g p zz.
  unfold wpull_elem.
  transitivity (cmon_map (rm_hom (rmod_by_element R (B i) (b i)))
                  (rig_one (ring_rig R))).
  - exact (unique_property
             (wpull_ump HP (fun k => rmod_by_element R (B k) (b k))
                (wpull_elem_maps_agree b Hb)) i (rig_one (ring_rig R))).
  - simpl; apply rm_smul_one.
Qed.

(*
 A compatible family of bilinear maps into the [B i] IS a bilinear map
 into the apex -- the elementwise content of preservation. 

 --------
 一个兼容的双线性映射族进入 [B i] 是一个双线性映射进入顶点——保持的元素内容。
*)
Program Definition wpull_bilin_med
  (β : ∀ i : I, RBilinear V V' (B i))
  (Hβ : ∀ (i j : I) (v : carrier (cmon_setoid V))
          (w : carrier (cmon_setoid V')),
          cmon_map (rm_hom (g i)) (rbl_map (β i) v w)
            ≈ cmon_map (rm_hom (g j)) (rbl_map (β j) v w)) :
  RBilinear V V' P := {|
  rbl_map := fun v w =>
    wpull_elem (fun i => rbl_map (β i) v w) (fun i j => Hβ i j v w)
|}.
Next Obligation.
  intros β Hβ v v' Hv w w' Hw.
  apply wpull_elem_unique; intro i.
  rewrite !wpull_elem_proj.
  now rewrite Hv, Hw.
Qed.
Next Obligation.
  intros β Hβ v v' w.
  apply wpull_elem_unique; intro i.
  rewrite wpull_elem_proj.
  rewrite (cmon_map_plus (rm_hom (p i))).
  rewrite !wpull_elem_proj.
  apply rbl_add_l.
Qed.
Next Obligation.
  intros β Hβ v w w'.
  apply wpull_elem_unique; intro i.
  rewrite wpull_elem_proj.
  rewrite (cmon_map_plus (rm_hom (p i))).
  rewrite !wpull_elem_proj.
  apply rbl_add_r.
Qed.
Next Obligation.
  intros β Hβ r v w.
  apply wpull_elem_unique; intro i.
  rewrite wpull_elem_proj.
  rewrite (rm_map_smul (p i)).
  rewrite !wpull_elem_proj.
  apply rbl_smul_l.
Qed.
Next Obligation.
  intros β Hβ r v w.
  apply wpull_elem_unique; intro i.
  rewrite wpull_elem_proj.
  rewrite (rm_map_smul (p i)).
  rewrite !wpull_elem_proj.
  apply rbl_smul_r.
Qed.

End AtAFamily.

Theorem Bilin_PreservesWidePullbacks : PreservesWidePullbacks (Bilin V V').
Proof using R V V'.
  intros I B zz g Hm P p HP.
  unshelve refine (@Build_IsWidePullback Sets I _ _ _ _ _ _ _).
  - (* the legs agree after the common codomain / 腿在共同陪域之后达成一致 *)
    intros i j β v w.
    exact (wpull_commutes HP i j (rbl_map β v w)).
  - (* the universal property / 通用属性 *)
    intros Q q Hq.
    unshelve refine {| unique_obj := {| morphism := fun x : carrier Q =>
      wpull_bilin_med g HP (fun i => q i x)
        (fun i j v w => Hq i j x v w) |} |}.
    + (* the mediator respects [≈] on Q / 调解员尊重 [≈] 在 Q 上 *)
      intros x y Hxy v w.
      apply (wpull_elem_unique g HP); intro i; simpl.
      rewrite !(wpull_elem_proj g HP).
      exact (proper_morphism (q i) x y Hxy v w).
    + (* it lifts every leg / 它抬起每条腿 *)
      intros i x v w.
      exact (wpull_elem_proj g HP (fun k => rbl_map (q k x) v w)
               (fun k l => Hq k l x v w) i).
    + (* and is the only one / 并且是唯一的一个 *)
      intros u Hu x v w.
      apply (wpull_elem_unique g HP); intro i; simpl.
      rewrite (wpull_elem_proj g HP).
      symmetry; exact (Hu i x v w).
Qed.

End BilinWidePullbacks.

(* * ** 7. The spanning solution set for [Bilin V V'] / * ** 7. [Bilin V V'] 的生成解集 *)

Section TensorSolutionSet.

Context {R : RingObject}.
Context (V V' : RModObject R).
Context `{HWP : @HasWidePullbacks (RMod R)}.

(*
 Mac Lane's “it suffices to consider the bilinear β which span C”:
 the solution set indexed by the spanning bilinear maps out of V × V'.
 The second hypothesis is discharged by [Bilin_PreservesWidePullbacks]
 above; the first is the open one -- see the header. 

 --------
 麦克莱恩的“考虑生成 C 的双线性 β 就足够了”：
 由 V × V' 出发的生成双线性映射索引的解集。
 第二个假设由上面的 [Bilin_PreservesWidePullbacks] 解决；第一个是假设是开放的——见标题。
*)
Definition tensor_solution_set (X : Sets) : SolutionSet (Bilin V V') X :=
  @spanning_solution_set (RMod R) Sets (Bilin V V') HWP
    (Bilin_PreservesWidePullbacks V V') X.

Definition tensor_esols : ElementSolutionSet (Bilin V V') :=
  esols_of_sols (Bilin V V') (tensor_solution_set SetsOne).

(*
 The index, the objects and the elements survive both repackagings on
 the nose. 

 --------
 索引、对象和元素在两次重新包装中都能在鼻子上保存下来。
*)
Example tensor_esol_index :
  esol_index tensor_esols = SpanningArrowsOutOf (Bilin V V') SetsOne
  := eq_refl.

Example tensor_esol_obj (i : SpanningArrowsOutOf (Bilin V V') SetsOne) :
  esol_obj tensor_esols i = `1 i := eq_refl.

Example tensor_esol_elem (i : SpanningArrowsOutOf (Bilin V V') SetsOne) :
  esol_elem tensor_esols i = `1 (`2 i) ttt := eq_refl.

End TensorSolutionSet.

(* * ** 8. Exercise 3: the balanced tensor is spanned by its generators / * ** 8. 练习 3：平衡张量由其生成元生成 *)

Section AbGenerated.

Context {A : AbObject}.
Context (P : carrier (cmon_setoid A) → Type).

(*
 The subgroup of an abelian group generated by a [Type]-valued
 predicate.  The same four closure constructors as [MGen], with
 [abgen_neg] in place of [mgen_smul]: there is no scalar here, so
 negation cannot be derived from (−1)· and must be a constructor of
 its own. 

 --------
 由 [Type] 值谓词生成的阿贝尔群的子群。与 [MGen] 相同的四个闭包构造器，但将 [abgen_neg] 代替 [mgen_smul]：这里没有标量，所以不能从 (−1)· 得出取反，必须作为一个独立的构造器。
*)
Inductive ABGen : carrier (cmon_setoid A) → Type :=
  | abgen_base : ∀ a, P a → ABGen a
  | abgen_resp : ∀ a b, a ≈ b → ABGen a → ABGen b
  | abgen_zero : ABGen (cmon_zero A)
  | abgen_plus : ∀ a b, ABGen a → ABGen b → ABGen (cmon_plus A a b)
  | abgen_neg  : ∀ a, ABGen a → ABGen (ab_neg A a).

(*
 Leastness, against a bare closed predicate rather than against a
 record: Instance/Ab/DirectedColimit.v's [AbSubgroup] is the
 in-tree record, but its own generated notion [InGen] is
 generated by a finite LIST, so nothing there is reused and that file
 is deliberately not [Require]d here. 

 --------
 最小性，是针对一个空的封闭谓词而不是针对一个记录：Instance/Ab/DirectedColimit.v 的 [AbSubgroup] 是树内记录，但它自身生成的概念 [InGen] 是由一个有限列表生成的，因此那里没有任何东西被重用，并且该文件故意没有在这里被 [Require] d。
*)
Fixpoint abgen_least (Q : carrier (cmon_setoid A) → Type)
  (Hresp : ∀ a b, a ≈ b → Q a → Q b)
  (Hzero : Q (cmon_zero A))
  (Hplus : ∀ a b, Q a → Q b → Q (cmon_plus A a b))
  (Hneg : ∀ a, Q a → Q (ab_neg A a))
  (HP : ∀ a, P a → Q a)
  (a : carrier (cmon_setoid A)) (D : ABGen a) {struct D} : Q a :=
  match D in ABGen a' return Q a' with
  | abgen_base a Ha     => HP a Ha
  | abgen_resp a b H D' =>
      Hresp a b H (abgen_least Q Hresp Hzero Hplus Hneg HP a D')
  | abgen_zero          => Hzero
  | abgen_plus a b D1 D2 =>
      Hplus a b (abgen_least Q Hresp Hzero Hplus Hneg HP a D1)
                (abgen_least Q Hresp Hzero Hplus Hneg HP b D2)
  | abgen_neg a D'      =>
      Hneg a (abgen_least Q Hresp Hzero Hplus Hneg HP a D')
  end.

End AbGenerated.

Section BalancedSpanning.

Context {X : RingObject}.
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).

Definition bal_image {A : AbObject} (β : BalBiadditive N M A)
  (x : carrier (cmon_setoid A)) : Type :=
  { n : carrier (cmon_setoid (rm_ab N)) &
    { m : carrier (cmon_setoid (rm_ab M)) & bal_map β n m ≈ x } }.

Definition BalSpanning {A : AbObject} (β : BalBiadditive N M A) : Type :=
  ∀ x : carrier (cmon_setoid A), ABGen (bal_image β) x.

(*
 Mac Lane's Exercise 3, second clause: “A ⊗_R B is spanned, as an
 abelian group, by the elements a ⊗ b.”  Four cases, by induction on
 [bsum]; the [bs_neg] case needs [abgen_neg] because an abelian group
 carries no scalar to derive it from. 

 --------
 麦克莱恩练习 3，第 2 条款：“A ⊗_R B 作为一个阿贝尔群，由元素 a ⊗ b 生成。” 四种情况，通过对 [bsum] 进行归纳；[bs_neg] 情况需要 [abgen_neg]，因为阿贝尔群没有标量可用来推导它。
*)
Theorem bal_gen_spanning : BalSpanning (@bal_gen X N M).
Proof using M N X.
  intro s; induction s as [n m| |s1 IH1 s2 IH2|s IH].
  - refine (abgen_base (bal_image (@bal_gen X N M)) _ _).
    exists n, m; reflexivity.
  - exact (abgen_zero (bal_image (@bal_gen X N M))).
  - exact (abgen_plus (bal_image (@bal_gen X N M)) _ _ IH1 IH2).
  - exact (abgen_neg (bal_image (@bal_gen X N M)) _ IH).
Qed.

End BalancedSpanning.

(* * ** 9. Exercise 3: base change along a ring homomorphism / * ** 9. 练习 3：沿环同态的基变换 *)

Section BalBaseChange.

Context {T R : RingObject}.
Context (phi : T ~{Rng}~> R).
Context (N : RModObject (Ring_op R)).
Context (M : RModObject R).

(*
 The two modules, read over T by restriction of scalars.  Neither
 changes the underlying abelian group, so the generators of the two
 balanced tensors are indexed by the SAME pair of carriers and the
 comparison below needs no transport. 

 --------
 这两个模，通过标量限制在 T 上阅读。两者都不改变底层的阿贝尔群，因此两个平衡张量的生成元由相同的载体对索引，下面的比较不需要进行转移。
*)
Definition bal_right_T : RModObject (Ring_op T) :=
  RestrictObj (RigHom_op phi) N.

Definition bal_left_T : RModObject T := RestrictObj phi M.

(* The R-balanced generator, read as a T-balanced map: the only clause that changes is the balance rule, which is the R-rule at the scalar [phi t]. / R 平衡生成器，读作 T 平衡映射：唯一改变的子句是平衡规则，即标量 [phi t] 的 R 规则。 *)
Definition bal_change_bil :
  BalBiadditive bal_right_T bal_left_T (@BalTensor R N M).
Proof using M N R T phi.
  unshelve refine (@Build_BalBiadditive T bal_right_T bal_left_T
                     (@BalTensor R N M) (@bs_gen R N M) _ _ _ _).
  - intros n n' Hn m m' Hm; exact (@be_gen R N M n n' m m' Hn Hm).
  - intros n n' m; exact (@be_add_l R N M n n' m).
  - intros n m m'; exact (@be_add_r R N M n m m').
  - intros t n m; exact (@be_balance R N M (rig_map phi t) n m).
Defined.

(* The comparison homomorphism A ⊗_T B → A ⊗_R B. / 比较同态 A ⊗_T B → A ⊗_R B。 *)
Definition bal_change :
  @BalTensor T bal_right_T bal_left_T ~{Ab}~> @BalTensor R N M :=
  bal_med bal_change_bil.

(* Generators go to generators, on the nose. / 发电机去发电机，正中目标。 *)
Example bal_change_gen (n : carrier (cmon_setoid (rm_ab N)))
  (m : carrier (cmon_setoid (rm_ab M))) :
  cmon_map bal_change (@bs_gen T bal_right_T bal_left_T n m)
    = @bs_gen R N M n m := eq_refl.

(*
 Mac Lane's “examine the relation”: the comparison is SURJECTIVE --
 A ⊗_R B is a quotient of A ⊗_T B -- by induction on the formal sums
 of the target. 

 --------
 麦克莱恩的“检查关系”：比较是满射的——
 A ⊗_R B 是 A ⊗_T B 的一个商——通过对目标的形式和进行归纳。
*)
Theorem bal_change_surjective : AbSurjective bal_change.
Proof using M N R T phi.
  intro t; induction t as [n m| |t1 IH1 t2 IH2|t IH].
  - exists (@bs_gen T bal_right_T bal_left_T n m); reflexivity.
  - exists (@bs_zero T bal_right_T bal_left_T); reflexivity.
  - destruct IH1 as [s1 H1]; destruct IH2 as [s2 H2].
    exists (@bs_plus T bal_right_T bal_left_T s1 s2).
    exact (be_plus H1 H2).
  - destruct IH as [s H].
    exists (@bs_neg T bal_right_T bal_left_T s).
    exact (be_neg H).
Qed.

(* And it IS [bal_med] of the R-balanced generator read over T: any homomorphism carrying generators to generators equals it. / 并且它确实是 R-平衡生成元的 [bal_med]，通过 T 读取：任何将生成元映射到生成元的同态都等于它。 *)
Theorem bal_change_is_med
  (f : @BalTensor T bal_right_T bal_left_T ~{Ab}~> @BalTensor R N M)
  (Hf : ∀ (n : carrier (cmon_setoid (rm_ab N)))
          (m : carrier (cmon_setoid (rm_ab M))),
          cmon_map f (@bs_gen T bal_right_T bal_left_T n m)
            ≈ @bs_gen R N M n m) :
  f ≈ bal_change.
Proof using M N R T phi. exact (bal_med_unique bal_change_bil f Hf). Qed.

End BalBaseChange.
