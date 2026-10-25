Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Identity.
Require Import Category.Monad.Morphism.
Require Import Category.Monad.Morphism.Algebra.
Require Import Category.Monad.Monadicity.BeckObjects.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Complete.
Require Import Category.Instance.Top.Cocomplete.

Generalizable All Variables.

(*
   * * The discrete-space adjunction induces the identity monad, and is not
   monadic 

   --------
   * * 离散空间的伴随函子会诱导出恒等幺半群，并且不是幺半群性的
*)

(*
 Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
 §VI.3, book p. 144 (PDF p. 153), read from the page image, right
 after the remark, which the page takes over from p. 143, that for
 "other authors (Barr-Wells [1985]), 'triplable' means only that K be
 an equivalence of categories": "However, here is an easy example when K
 is not an isomorphism, and not even an equivalence.  The forgetful
 functor G : Top → Set has a left adjoint D which assigns to each set
 X the discrete topological space (all subsets open in X), for the
 identity arrow η_X : X → GDX is trivially universal from the object
 X to the functor G.  This adjunction ⟨D, G, η, …⟩ : Set ⇀ Top
 defines on Set the monad I = ⟨I, 1, 1⟩ which is the identity
 (identity functor, identity as unit and as multiplication).  The
 I-algebras in Set are just the sets, so the comparison functor
 Top → Top^I = Set is in this case the given forgetful functor G"
 (catalog id maclane:VI.3:remark1).
 Awodey, "Category Theory", Carnegie Mellon pre-print of the 1st ed.
 (September 2005), §10.3, printed p. 278 (PDF p. 287), read from the
 page image, runs the same argument for posets: "An example of a
 right adjoint that is not monadic is the forgetful functor from
 posets, U : Pos → Sets" (awodey:10.3:example-pos-not-monadic);
 that example is Instance/Pos/Monadicity.v's.
 nLab: https://ncatlab.org/nlab/show/monadic+functor
 nLab: https://ncatlab.org/nlab/show/discrete+space

 BACKGROUND.  Every adjunction F ⊣ U induces a monad T = UF, and the
 comparison functor K into the Eilenberg-Moore category of T measures how
 far the right adjoint U is from forgetting algebraic structure; U is
 monadic when K is an equivalence (Monad/Comparison.v's [Monadic], the
 Barr-Wells reading quoted above); Mac Lane's "not an isomorphism, and
 not even an equivalence" covers the stronger reading too.  His example
 is the extreme case.  A set carries a unique discrete topology, so the
 unit is the identity and the induced monad is the identity monad: it
 records no structure at all, its algebras are the sets, and K can be no
 more than the forgetful functor itself.  That functor forgets a
 topology, which is not algebraic structure, and it is not full.  An
 isomorphic monad, with functor Id ◯ Id, is induced by Id ⊣ Id, whose
 right adjoint IS monadic (Monad/Monadicity/Examples.v's
 [identity_monadic]; Monad/Identity.v's header), so a monad does not
 determine whether the right adjoint that induced it is monadic.

 THE READING IMPLEMENTED.  The page prints the target of the
 comparison as "Top^I = Set".  The I-algebras live in Set, so K lands
 in the category of I-algebras in Set, and that is the target taken
 here: [EilenbergMoore] of the induced monad on [Sets].  "= Set" is
 read as an equivalence between that category and [Sets]: an algebra
 keeps its structure map, which is ≈ id and need not be id.  For
 Monad/Eilenberg/Moore/Limit/Examples.v's identity monad [IdSM] on
 [Sets], #467's [A_id_ne_A_true] exhibits two different algebras on one
 carrier; the same is not restated here for [PDiscMonad].

 WHY [PTopCat].  Over the tree's Type-valued [Top] the adjunction is
 not an [Adjunction] record at any universe assignment
 (Instance/Top/Forgetful.v's header; Test/ProbeUniversalArrows312.v
 pins it), so its induced monad and comparison functor cannot be
 formed.  By the maintainer's decision of 2026-09-24 such Top issues
 are built on Instance/Top/Prop.v's Prop-valued [PTopCat], where
 Instance/Top/Complete.v's [PDisc_PForget : PDisc ⊣ PForget] is one
 (#458).  Instance/Top/Monadicity/TypeValued.v states what remains
 formable over [Top]: that its underlying-set functor is not monadic.

 WHAT IS HERE.
 - The induced monad: [PDiscT] is [PForget ◯ PDisc] and [PDiscMonad]
 is Monad/Comparison.v's [Adjunction_Induced_Monad PDisc_PForget].
 Its functor is the identity on objects ([PDiscT_fobj]) and on
 arrows ([PDiscT_fmap]); its unit and multiplication are [id]
 ([PDiscMonad_ret], [PDiscMonad_join]); as functions, its four data
 fields are those of [IdMonad Sets] ([PDiscT_fields],
 [PDiscMonad_fields]); the unit of the adjunction
 is the identity arrow, Mac Lane's η_X ([PDisc_PForget_unit]), and
 the counit at a space is the identity on its points
 ([PDisc_PForget_counit]).
 - "The monad I = ⟨I, 1, 1⟩ which is the identity", as an isomorphism
 [disc_id_iso] in #468's category of monads [Monads Sets]
 (Monad/Morphism.v) between (PDiscT; PDiscMonad) and
 Monad/Identity.v's (Id[Sets]; IdMonad Sets).  Its two morphisms of
 monads, [disc_id_hom] and [id_disc_hom], have the identity as every
 component ([disc_id_hom_component], [id_disc_hom_component]).
 - "The comparison functor is the forgetful functor G": [PDiscK] is
 [EM_Comparison PDisc_PForget].  After the forgetful functor of the
 algebras it is [PForget] on objects and on arrows
 ([PDiscK_forget_obj], [PDiscK_forget_map]), in Theory/Functor.v's
 [Functor_StrictEq_Setoid] with every object equation [eq_refl]
 ([PDiscK_forget_strict]), and at Cat's ≈ ([PDiscK_forget], which is
 Monad/Comparison.v's [EM_Comparison_Forget] at this adjunction).
 The structure map of K X is the identity setoid morphism
 ([PDiscK_alg]).
 - "Top^I = Set": [EM_PDisc_equivalence], the forgetful functor of the
 algebras of [PDiscMonad] is an equivalence with quasi-inverse
 [EM_Free], because every structure map is ≈ id
 ([PDiscMonad_alg_id]); and [PDiscK_free]: K ≈ EM_Free ◯ PForget,
 with identity arrows underneath, so K is G followed by that
 equivalence.  For the identity monad itself, Monad/Identity.v's
 [IdMonad_EM_equivalence] at [Sets]; and [PDiscKI], K followed by
 #468's θ* of [id_disc_hom] (Monad/Morphism/Algebra.v's [mh_EM]), is
 the comparison into the algebras of [IdMonad Sets]: the structure
 map of each image is the identity function ([PDiscKI_alg]) and
 after the forgetful functor it is [PForget] on objects and arrows
 ([PDiscKI_forget_obj], [PDiscKI_forget_map]).  The four constants
 [EM_PDisc_counit], [EM_PDisc_unit_iso], [EM_PDisc_unit] and
 [EM_PDisc_equivalence] repeat Monad/Identity.v's [IdMonad_EM_counit],
 [IdMonad_EM_unit_iso], [IdMonad_EM_unit] and
 [IdMonad_EM_equivalence] line for line at [PDiscMonad]: those are
 stated for [IdMonad], and [PDiscMonad] is not [IdMonad Sets] at
 [eq_refl], neither as a functor (R1) nor as a monad (R3).  Carrying
 [IdMonad_EM_equivalence] across [disc_id_iso] instead, by θ*
 ([mh_EM], [mh_EM_id], [mh_EM_compose]) and Theory/Equivalence/
 Bundled.v's [EquivalenceOfCategories_Compose], is the other route;
 it is not taken.
 - "Not an isomorphism, and not even an equivalence."  Mac Lane gives
 no argument; this is the file's.  [pbool_to_indisc], the identity
 of [bool] from the discrete space [PBool] (Instance/Top/Prop.v) to
 the indiscrete [PTwoIndisc] (Instance/Top/Cocomplete.v), is
 continuous, and no continuous map back is the identity on points
 ([no_pindisc_to_bool]): the preimage of the open {true} would be an
 open of the indiscrete space holding at true and not at false.  So
 [PForget] is not full ([PForget_not_Full]); neither is K, the
 identity of [bool] being an algebra map K PTwoIndisc → K PBool
 ([PDiscK_not_Full]), and neither is [PDiscKI], the comparison into
 the algebras of [IdMonad Sets] itself ([PDiscKI_not_Full],
 [PDiscKI_not_Equivalence]); K is not an equivalence
 ([PDiscK_not_Equivalence], by Theory/Equivalence/FullFaithful.v's
 [Equivalence_Full]) and not an isomorphism in [Cat]
 ([PDiscK_not_Cat_iso]; a [Cat]-isomorphism repacks as an
 equivalence, as in Theory/Equivalence.v's
 [Cat_Iso_to_Equivalence]).
 - [PForget_not_Monadic]: no adjunction at all makes [PForget]
 monadic, not only this one.  The proof is by conservativity: an
 equivalence K is full, and the forgetful functor of any
 Eilenberg-Moore category reflects isomorphisms
 (Monad/Monadicity/BeckObjects.v's [em_forget_reflects_isos]), so K
 of [pbool_to_indisc], an isomorphism once forgotten, has an inverse
 algebra map, which fullness brings back to a continuous map that is
 the identity on points.  [PForget_not_ReflectsIsos] refutes
 conservativity of [PForget] on its own, hypothesis 3 of
 Monad/Monadicity/Crude.v's crude monadicity theorem:
 [pbool_to_indisc] goes to an isomorphism of [Sets] and is not one.
 The adjunction part of the premise is inhabited ([PDisc_PForget]),
 so what is refuted is the equivalence.  Before #469 the tree held no
 negation of [Monadic] (a grep of the .v files for [Monadic] within
 two lines of False, ¬ or Empty); #469 adds the first four, by the
 same grep: [PForget_not_Monadic] here,
 Instance/Top/Monadicity/TypeValued.v's [Top_Forget_not_Monadic],
 and Instance/Pos/Monadicity.v's [Pos_Forget_not_Monadic] and
 [PosPForget_not_Monadic].

 THE ISSUE'S PREMISES, dated.  Issue #469 was filed on 2026-07-23.  Its
 "there is no category Top and no discrete-topology functor" was
 accurate when filed, stale since PR #1054 (merged 2026-08-12, the
 Type-valued [Top]) and PR #1088 (merged 2026-08-14, [Top_Discrete]
 with the transposition [discrete_adj]); [PTopCat] is PR #1331's
 (merged 2026-09-25) and [PDisc_PForget] PR #1332's (merged
 2026-09-25).  Its "the identity monad appears only via the identity
 adjunction" was not accurate when filed: Monad/Strong.v's [Id_Monad]
 dates from 2026-06-18.  Its "(needs the category of posets from
 #641)" has been met since PR #1076 (merged 2026-08-13).

 STRENGTHS.  By [eq_refl]: [PDiscT_fobj], [PDiscT_fmap],
 [PDiscT_fields], [PDisc_PForget_unit], [PDisc_PForget_counit],
 [PDiscMonad_ret], [PDiscMonad_join], [PDiscMonad_fields],
 [disc_id_hom_component], [id_disc_hom_component], [PDiscK_forget_obj],
 [PDiscK_forget_map], [PDiscK_alg], the object equations of
 [PDiscK_forget_strict], [PDiscKI_forget_obj], [PDiscKI_forget_map] and
 [PDiscKI_alg].  [PDiscT_fields] and [PDiscMonad_fields] read the
 book's "identity functor, identity as unit and as multiplication" as
 equations between the four data fields and those of [IdMonad Sets].
 Up to ≈: [disc_id_iso]'s inverse laws, [PDiscK_forget],
 [PDiscMonad_alg_id], [EM_PDisc_equivalence] and [PDiscK_free].

 Refused, each read in a copy of the whole of Test/ProbeMonadicity469.v
 with that one command unguarded, and pinned there with its controls,
 all by conversion ("cannot unify"): the Leibniz equation
 PDiscT = Id[Sets] (R1), and its three proof fields [fmap_respects],
 [fmap_id] and [fmap_comp] one by one (R1a to R1c), the fields [fobj]
 and [fmap] converting (C1, C2); the Leibniz form of the book's "is the
 given forgetful functor G", EM_Forget ◯ PDiscK = PForget (R2), with
 its three proof fields (R2a to R2c) and the two data fields converting
 (C3, C4); the equality of the two monads as objects of [Monads Sets]
 (R3); K against EM_Free ◯ PForget on objects (R14), whose carriers and
 structure maps agree (C39), so [PDiscK_free] is ≈ and no more; and the
 structure map of an image of [PDiscKI] as a setoid morphism (R15), so
 [PDiscKI_alg] is pointwise and no more, while [PDiscK_alg] holds of
 the setoid morphism itself.
 CORRECTION (#1347): R15 now holds at [eq_refl], since Instance/Sets.v
 gives its identity's and composite's properness fields as terms; it is
 a control of the probe, and that structure map IS [setoid_morphism_id]
 as a setoid morphism, though [PDiscKI_alg] still states the pointwise
 form.  The other refusals above stand.

 CAUSES.  The eleven refusals R1 to R3 (with R1a to R1c and R2a to R2c), R14
 and R15 stand, and their controls are accepted, in a copy of this file's
 dependency closure with [Transparent Obligations] set and every [Qed]
 turned into [Defined], obligations included (checked by [About] on them),
 but for four files.  In Instance/Sets.v only the two proofs that occur in
 the refused terms were made transparent, the hom setoid's equivalence and
 [setoid_morphism_compose_respects], the second with a proof free of
 [rewrite], since turning its own [Qed] into [Defined] is refused ("Universe
 ... is unbound"). Instance/Discrete/Reconstruct.v (the same refusal),
 Structure/Limit/Preservation.v and Structure/Cartesian/Closed.v (whose
 proofs stop once the files below them are transparent) keep their [Qed]s;
 none defines a constant in the refused terms.  No flip of the tree reaches
 the standard library, and there the normal forms of the refused proof
 fields (R1a, R1b, R2a and R2b, read by [Eval cbv] in that copy) are headed
 by its opaque [CMorphisms.trans_co_eq_inv_arrow_morphism_obligation_1],
 which the [rewrite] inside [Compose]'s obligations leaves; so is the unit
 law [t_id] of the algebra K X behind R14.  Unfolded by hand, that
 obligation's body is the variable setoid's transitivity applied to X x and
 a reflexivity, and the term is refused against X x (R13), while at the
 Leibniz setoid of [bool] the same term converts (C36). So R1 to R3 with
 their fields, and R14, are STRUCTURAL past the standard library, by the
 hand-unfolded control: the proof fields are different proofs of a
 [Type]-valued ≈, [Compose]'s built from those of its two factors, stuck on
 a projection of variable data.  R15 is STDLIB OPACITY: the properness field
 of the refused structure map normalizes to the standard library's opaque
 [Reflexive_partial_app_morphism], [proper_proper_proxy] and
 [CMorphisms.compose_proper_obligation_1] applied around
 [subrelation_id_proper] twice, where that of [setoid_morphism_id] is
 [subrelation_id_proper] alone; it is the kind of
 Test/ProbeMonadMorphism468.v's R12, which holds at [eq_refl] once
 Instance/Sets.v's properness fields are given as terms, a step argued here
 from the terms and not measured.
 CORRECTION (#1347): the step is now taken and measured: R15 holds at
 [eq_refl], so its classification, STDLIB OPACITY, was right.  The copy
 above predates #1347; R15 stood there because Instance/Sets.v's two
 fields were still those of instance resolution.

 Eleven proofs end [Defined] (counted by token).  Eight are
 load-bearing, measured by closing each alone [Qed] in a copy of this
 file preceded by Monad/Identity.v: [disc_to_id] and [id_to_disc]
 ([disc_id_hom] and [id_disc_hom] are then refused), [disc_id_hom] and
 [id_disc_hom] (their [_component] readbacks), [EM_PDisc_unit_iso]
 ([EM_PDisc_unit]) and [PDiscK_free_iso] ([PDiscK_free]); and, for the
 probe's controls only, [disc_id_iso] (C17) and [PDiscK_forget_strict]
 (C20).  [EM_PDisc_counit], [EM_PDisc_unit] and [PDiscK_free] are
 [Defined] by the data convention only: closed [Qed], nothing here or
 in the probe is refused.

 UNIVERSES, read off [About]; [o] the points and homs of
 [PTopCat@{o so}], [so] its objects; stdlib caps (compose, ID,
 prod_rect, projections, Logic_lemmas.equality, Projections, and
 eq_ind, whose first carrier is the [rewrite] in [no_pindisc_to_bool])
 left out.  [Set] occurs only as [Set < so], implied by [o < so], and no
 block carries an equation.
 - [PDiscT@{o so s}]: o < s is [Compose]'s own strict bound (hom level
 below its auxiliary level) at [PForget ◯ PDisc].  The level is named
 [s] and is the same [s] as the Eilenberg-Moore level below:
 [EM_Comparison] identifies the two.
 - [PDiscMonad@{o so s u u0}] and the monad constants, among them
 [PDiscMonad_fields]: o < u is [PDisc_PForget@{o so u u0}]'s.
 - [disc_id_iso@{o so s u u0 m1 m2}]: [Monads@{so o m1 m2}]'s bounds.
 - [PDiscK@{o so s u u0 e}] and the constants over the algebras,
 [PDiscK_alg], [PDiscKI_not_Full] and [PDiscKI_not_Equivalence]
 among them:
 so <= e, the objects of [Sets] below those of
 [EilenbergMoore@{e so s o}].  [PDiscK_forget_strict] adds [a] and
 [b], the levels of [Functor_StrictEq_Setoid] (o < b its own strict
 bound), with that setoid's transport caps (Logic.transport,
 Logic.transport_r, eq_rect, eq_rect_r and eq_sym_involutive, in
 its block alone).
 - [PDiscK_not_Cat_iso@{o so s u u0 c}] is stated at e := so, the one
 object level [Cat] allows for both ends; c is the object level of
 [Cat] itself, whence so < c.
 - [PForget_not_Monadic@{o so m m0 m1 m3 m6}] states [Monadic@{m m0
 m1 so m3 o so m6}] and carries exactly [Monadic]'s own block there
 with o < so from [PForget]: the refutation holds at every value of
 [Monadic]'s five levels that [PForget@{o so}] leaves free.
 - The witnesses [pbool_to_indisc], [no_pindisc_to_bool],
 [PForget_not_Full] and [PForget_not_ReflectsIsos]: [@{o so}], o < so.

 NOT DELIVERED.  Anything over the Type-valued [Top] but the negation of
 monadicity (Instance/Top/Monadicity/TypeValued.v).  The Leibniz forms
 above (refused).  K is shown not to be an isomorphism in [Cat], whose
 isomorphisms are the equivalences; an isomorphism in
 Instance/StrictCat.v is not considered.  Whether [PForget] meets the
 other hypotheses of the crude theorem, or creates the coequalizers of
 Monad/Monadicity/Beck.v's precise form, is not examined. 

 --------
 Mac Lane，《为在职数学家准备的范畴论》，第2版 (GTM 5)，§VI.3，第144页（PDF第153页），从页图像读取，就在注释之后，该页从第143页接上，即“对于其他作者（Barr-Wells [1985]），‘可三重化’仅意味着K是范畴等价”："然而，这里有一个简单的例子，其中K不是同构，甚至不是等价。遗忘函子 G : Top → Set 有一个左伴随 D，它将每个集合 X 分配为离散拓扑空间（X 中的所有子集都是开集），对于恒等箭头 η_X : X → GDX，从对象 X 到函子 G 的箭头显然是普遍的。"这个伴随 ⟨D, G, η, …⟩ : Set ⇀ Top 定义了 Set 上的单子 I = ⟨I, 1, 1⟩，它是恒等的（恒等函子，恒等作为单位和乘法）。Set 中的 I-代数只是集合，因此比较函子 Top → Top^I = Set 在这种情况下就是给定的遗忘函子 G（目录 id maclane:VI.3:remark1）。Awodey，《范畴论》，卡内基梅隆大学第一版预印本（2005年9月），§10.3，第278页（PDF第287页），从页面图像中读取，对于偏序集运行相同的论证：“一个不是单子的右伴随的例子是来自偏序集的遗忘函子 U : Pos → Sets”（awodey:10.3:example-pos-not-monadic）；该例子是 Instance/Pos/Monadicity.v 的。nLab：https://ncatlab.org/nlab/show/monadic+functor nLab：https://ncatlab.org/nlab/show/discrete+space背景。每一个伴随 F ⊣ U 都会引出一个单子 T = UF，而比较函子 K 到 T 的 Eilenberg-Moore 范畴可以衡量右伴随 U 在多大程度上忘记了代数结构；当 K 是等价时，U 是单子性的（参见 Monad/Comparison.v 的 [Monadic] 以及上文引用的 Barr-Wells 读物）；Mac Lane 所说的“不是同构，甚至不是等价”也适用于更强的理解。他的例子是极端情况。一个集合具有唯一的离散拓扑，因此单位算子是恒等映射，引出的单子是恒等单子：它完全不记录任何结构，其代数就是集合，而 K 充其量也只能是忘记函子自身。该函子会忘记拓扑，而拓扑不是代数结构，而且它也不是满函子。一个同构单子，其函子为 Id ◯ Id，是由 Id ⊣ Id 引起的，其右伴随是单子的（Monad/Monadicity/Examples.v 的 [identity_monadic]；Monad/Identity.v 的头部），所以一个单子并不能决定引出它的右伴随是否是单子的。读取已实现。该页面将比较的目标打印为“Top^I = Set”。I-代数存在于 Set 中，因此 K 落在 Set 中 I-代数的范畴中，而这里采用的目标即为 [EilenbergMoore] 在 [Sets] 上的诱导单子。"= Set" 被理解为该范畴与 [Sets] 之间的等价：一个代数保持其结构映射，该映射近似于 id 并不一定是 id。对于 Monad/Eilenberg/Moore/Limit/Examples.v 中对 [Sets] 的恒等单子 [IdSM]，#467 中的 [A_id_ne_A_true] 在一个承载体上展示了两种不同的代数；这里对 [PDiscMonad] 不再重述相同内容。为什么 [PTopCat]。对于树的类型值 [Top]，伴随不是在任何宇宙分配下的 [Adjunction] 记录（Instance/Top/Forgetful.v 的头文件；Test/ProbeUniversalArrows312.v 作了标记），因此无法形成其诱导的 monad 和比较函子。根据维护者在 2026-09-24 的决定，此类 Top 问题建立在 Instance/Top/Prop.v 的 Prop 值 [PTopCat] 上，其中 Instance/Top/Complete.v 的 [PDisc_PForget : PDisc ⊣ PForget] 是其中之一（#458）。Instance/Top/Monadicity/TypeValued.v 说明了在 [Top] 上仍可形成的内容：其基础集合函子不是 monadic 的。这里是什么。- 诱导的单子：[PDiscT] 是 [PForget ◯ PDisc]，[PDiscMonad] 是 Monad/Comparison.v 中的 [Adjunction_Induced_Monad PDisc_PForget]。它的函子在对象上是恒等的（[PDiscT_fobj]），在箭头上也是恒等的（[PDiscT_fmap]）；它的单位和乘法是 [id]（[PDiscMonad_ret]，[PDiscMonad_join]）；作为函数，它的四个数据域是 [IdMonad Sets] 的那些（[PDiscT_fields]，[PDiscMonad_fields]）；伴随的单位是恒等箭头，即 Mac Lane 的 η_X（[PDisc_PForget_unit]），而在空间上的余单位是其点的恒等（[PDisc_PForget_counit]）。- “单子 I = ⟨I, 1, 1⟩，即恒等”，作为同构 [disc_id_iso] 在 #468 的单子类别中 [Monads Sets]（Monad/Morphism.v）在 (PDiscT; PDiscMonad) 和 Monad/Identity.v 的 (Id [Sets]; IdMonad Sets) 之间。它的两个单子态射，[disc_id_hom] 和 [id_disc_hom]，每个分量都是恒等（[disc_id_hom_component]，[id_disc_hom_component]）。- “比较函子是忘记函子 G”：[PDiscK] 是 [EM_Comparison PDisc_PForget]。在代数的忘记函子之后，它在对象和箭头上是 [PForget]（[PDiscK_forget_obj]，[PDiscK_forget_map]），在 Theory/Functor.v 的 [Functor_StrictEq_Setoid] 中，每个对象的方程是 [eq_refl]（[PDiscK_forget_strict]），在 Cat 的 ≈ 中是 [PDiscK_forget]，这正是 Monad/Comparison.v 在该伴随关系下的 [EM_Comparison_Forget]。K X 的结构映射是恒等 setoid 态射（[PDiscK_alg]）。- “Top^I = Set”：[EM_PDisc_equivalence]，[PDiscMonad] 的代数的遗忘函子是与准逆 [EM_Free] 的等价，因为每个结构映射 ≈ id（[PDiscMonad_alg_id]）；并且 [PDiscK_free]：K ≈ EM_Free ◯ PForget，底下有恒等箭头，因此 K 是 G 跟随那个等价。对于恒等 monad 本身，Monad/Identity.v 中的 [IdMonad_EM_equivalence] 在 [Sets]；以及 [PDiscKI]，K 跟随 #468 的 [id_disc_hom] 的 θ*（Monad/Morphism/Algebra.v 的 [mh_EM]），是进入 [IdMonad Sets] 代数的比较：每个像的结构映射是恒等函数（[PDiscKI_alg]），并且在遗忘函子之后，它在对象和箭头上是 [PForget]（[PDiscKI_forget_obj]，[PDiscKI_forget_map]）。四个常数
 [EM_PDisc_counit] 、 [EM_PDisc_unit_iso] 、 [EM_PDisc_unit] 和
 [EM_PDisc_equivalence] 在 [PDiscMonad] 逐行重复 Monad/Identity.v 的 [IdMonad_EM_counit] 、
 [IdMonad_EM_unit_iso] 、 [IdMonad_EM_unit] 和 [IdMonad_EM_equivalence] ：这些在 [IdMonad] 中声明，
 而 [PDiscMonad] 在 [eq_refl] 并不是 [IdMonad Sets]，无论作为函子 (R1) 还是作为 monad (R3)。
 通过 θ* ([mh_EM], [mh_EM_id], [mh_EM_compose]) 和 Theory/Equivalence/Bundled.v 的 [EquivalenceOfCategories_Compose]
 将 [IdMonad_EM_equivalence] 传递到 [disc_id_iso] 是另一条路径；
 它没有被采用。- “不是同构，甚至不是等价。” 麦克莱恩没有给出论证；这是该文件的内容。[pbool_to_indisc]，从离散空间 [PBool]（Instance/Top/Prop.v）到不可分离空间 [PTwoIndisc]（Instance/Top/Cocomplete.v）的同一性 [bool] 是连续的，而没有连续映射回去能在点上成为同一性（[no_pindisc_to_bool]）：开集 {true} 的逆像将是不可分离空间的一个开集，在 true 上成立而在 false 上不成立。所以
 [PForget] 不是满的 （[PForget_not_Full] ）;K 也不是满的，因为
 [bool]的恒等式是代数映射 K PTwoIndisc → K PBool
 （[PDiscK_not_Full]），也不是[PDiscKI]，比较为
 [IdMonad Sets]本身的代数（[PDiscKI_not_Full]，
 [PDiscKI_not_Equivalence]）;K 不是等价
 （[PDiscK_not_Equivalence]，由Theory/Equivalence/FullFaithful.v's
 [Equivalence_Full]），而不是[Cat]中的同构
 （[PDiscK_not_Cat_iso];[Cat] -同构可重新包装为
 等价，如 Theory/Equivalence.v 中的
 [Cat_Iso_to_Equivalence]）。- [PForget_not_Monadic] ：任何伴随都不构成[PForget]
 莫纳迪克，不仅仅是这个。证明方法是通过守恒性：一个
 等价 K 是满的，且是任意 的遗忘函子
 艾伦伯格-摩尔范畴反映同构
 （Monad/Monadicity/BeckObjects.v 的 [em_forget_reflects_isos]），所以 K
 [pbool_to_indisc] 的同构一旦被遗忘，其逆映射为
 代数映射，使其满映射回一个连续映射，即
 点上的同一性。[PForget_not_ReflectsIsos] 反驳
 [PForget]本身的守恒性，假设3
 Monad/Monadicity/Crude.v 的粗糙单一性定理：
 [pbool_to_indisc] 是 [Sets] 的同构，且不是 。前提中的伴随部分是有元素的（[PDisc_PForget]），
 因此，被推翻的是等价性。在 #469 之前，这棵树没有包含 [Monadic] 的否定（在 .v 文件中 grep [Monadic] 时，查找 False、¬ 或 Empty 两行以内的情况）；#469 通过相同的 grep 添加了前四个：这里的 [PForget_not_Monadic]，Instance/Top/Monadicity/TypeValued.v 中的 [Top_Forget_not_Monadic]，以及 Instance/Pos/Monadicity.v 中的 [Pos_Forget_not_Monadic] 和 [PosPForget_not_Monadic]。问题的前提，已注明日期。问题 #469 于 2026-07-23 提交。其“没有 Top 类别且没有离散拓扑函子”在提交时是准确的，但自 PR #1054（已合并 2026-08-12，类型值 [Top]）和 PR #1088（已合并 2026-08-14，[Top_Discrete] 与换位 [discrete_adj]）以来已过时；[PTopCat] 属于 PR #1331（已合并 2026-09-25），[PDisc_PForget] 属于 PR #1332（已合并 2026-09-25）。其“只有通过恒等陪伴才能出现恒等单子”在提交时不准确：Monad/Strong.v 的 [Id_Monad] 来自 2026-06-18。其“（需要 #641 的偏序集类别）”自 PR #1076（已合并 2026-08-13）以来已经满足。优势。由[eq_refl]：[PDiscT_fobj]，[PDiscT_fmap]，[PDiscT_fields]，[PDisc_PForget_unit]，[PDisc_PForget_counit]，[PDiscMonad_ret]，[PDiscMonad_join]，[PDiscMonad_fields]，[disc_id_hom_component]，[id_disc_hom_component]，[PDiscK_forget_obj]，[PDiscK_forget_map]，[PDiscK_alg]，[PDiscK_forget_strict]，[PDiscKI_forget_obj]，[PDiscKI_forget_map]和[PDiscKI_alg]的对象方程。[PDiscT_fields]和[PDiscMonad_fields]将书中的“恒等函子，恒等作为单位和作为乘法”解读为四个数据字段与[IdMonad Sets]的数据字段之间的方程。在≈下：[disc_id_iso]的逆律，[PDiscK_forget]，[PDiscMonad_alg_id]，[EM_PDisc_equivalence]和[PDiscK_free]。拒绝，每一条都在 Test/ProbeMonadicity469.v 的完整副本中读取  
 使用那个命令不受保护，并用它的控制固定在那里，  
 全部通过转换（“无法统一”）：莱布尼茨方程  
 PDiscT = Id [Sets]（R1），及其三个证明字段 [fmap_respects]、  
 [fmap_id] 和 [fmap_comp] 一一（R1a 到 R1c），字段 [fobj]  
 和 [fmap] 转换（C1、C2）；书中“是给定遗忘函子 G”的莱布尼茨形式，EM_Forget ◯ PDiscK = PForget（R2），  
 及其三个证明字段（R2a 到 R2c）和两个数据字段转换（C3、C4）；  
 两个单子作为 [Monads Sets] 对象的相等性（R3）；K 对 EM_Free ◯ PForget 在对象上的比较（R14），其载体和结构映射一致（C39），所以 [PDiscK_free] 是 ≈，没有更多；以及 [PDiscKI] 作为集合的像的结构映射id 同态 (R15)，因此 [PDiscKI_alg] 是逐点的，仅此而已，而 [PDiscK_alg] 则适用于集合同态本身。更正 (#1347)：R15 现在在 [eq_refl] 保持，因为 Instance/Sets.v 给出了它的身份和复合的适当性字段作为项；它是探针的控制，而那个结构映射确实是 [setoid_morphism_id] 作为集合同态，尽管 [PDiscKI_alg] 仍然声明点态形式。上述其他拒绝仍然有效。原因。十一项拒绝 R1 到 R3（包含 R1a 到 R1c 和 R2a 到 R2c），R14 和 R15 仍然有效，并且它们的控制在这个文件的依赖闭包的副本中被接受，其中 [Transparent Obligations] 已设置，并且每个 [Qed] 都被转换为 [Defined]，包括义务（通过 [About] 检查），但有四个文件除外。在 Instance/Sets.v 中，仅对被拒绝条款中出现的两个证明进行了透明处理，即齐次等价集合的等价及 [setoid_morphism_compose_respects]，后者的第二个证明没有 [rewrite]，因为将其自身的 [Qed] 转换为 [Defined] 被拒绝（“Universe … 未绑定”）。Instance/Discrete/Reconstruct.v（同样的拒绝），Structure/Limit/Preservation.v 和 Structure/Cartesian/Closed.v（当其下文件是透明的时，其证明会停止）保留它们的 [Qed]；没有一个在被拒绝的项中定义常量。树的任何翻转都无法到达标准库，在那里，被拒绝的证明字段（R1a、R1b、R2a 和 R2b，在该副本中由 [Eval cbv] 读取）的标准形式以其不透明的 [CMorphisms.trans_co_eq_inv_arrow_morphism_obligation_1] 为头部，由 [Compose] 中 [rewrite] 的义务留下；同样，代数 K X 的单位律 [t_id] 位于 R14 之后。手工展开时，该义务的主体是将变量集合论的传递性应用于 X x 和一个反身性，且该项在 X x (R13) 上被拒绝，而在 [bool] 的莱布尼茨集合论上相同的项可以转换 (C36)。所以 R1 到 R3 及其字段，以及 R14，是超出标准库的结构，通过手动展开的控制：证明字段是 [Type] 值≈的不同证明，[Compose] 的构造来自其两个因子的构造，固定在变量数据的投影上。R15 是标准库不透明性：被拒绝的结构映射的适当性字段标准化为标准库的不透明 [Reflexive_partial_app_morphism]、[proper_proper_proxy] 和 [CMorphisms.compose_proper_obligation_1]，并在 [subrelation_id_proper] 周围应用两次，而 [setoid_morphism_id] 的则仅为 [subrelation_id_proper]；它是 Test/ProbeMonadMorphism468.v 的 R12 类型，当 Instance/Sets.v 的适当性字段作为项给出时，在 [eq_refl] 上保持一次，这一步从项出发论证，而非通过测量得出。更正 (#1347)：该步骤现在已执行并测量：R15 保持在 [eq_refl]，因此其分类，STDLIB OPACITY，是正确的。上面的副本早于 #1347；R15 之所以停在那里，是因为 Instance/Sets.v 的两个字段仍然属于实例解析。十一个证明结束 [Defined]（按标记计算）。其中八个是承重的，通过在本文件的副本中单独关闭每一个来测量 [Qed]，文件前面是 Monad/Identity.v： [disc_to_id] 和 [id_to_disc]（然后拒绝 [disc_id_hom] 和 [id_disc_hom]），ZW195WZZ 和 [id_disc_hom]（它们的 [_component] 回读），ZW198WZZ（ZW199WZZ）和 [PDiscK_free_iso]（ZW201WZZ）；对于探针的控制，仅 [disc_id_iso]（C17）和 [PDiscK_forget_strict]（C20）。ZW204WZZ、ZW205WZZ 和 [PDiscK_free] 仅由数据约定 [Defined]：关闭 [Qed]，这里或探针中没有内容被拒绝。宇宙，读取 [About]；[o] 的点和 [PTopCat@{o so}]、[so] 的对象；标准库大写（compose、ID、prod_rect、projections、Logic_lemmas.equality、Projections 以及 eq_ind，其第一个载体在 [rewrite] 中的 [no_pindisc_to_bool]）被省略。[Set] 仅作为 [Set < so] 出现，由 [o < so] 推出，并且没有区块包含等式。- [PDiscT@{o so s}]：o < s 是 [Compose] 自身的严格界（在其辅助层以下的同态层）在 [PForget ◯ PDisc]。该层命名为 [s]，并且与下面的 Eilenberg-Moore 层相同 [s]：[EM_Comparison] 识别了这两者。- [PDiscMonad@{o so s u u0}] 以及 monad 常量，其中包括 [PDiscMonad_fields]：o < u 是 [PDisc_PForget@{o so u u0}] 的。- [disc_id_iso@{o so s u u0 m1 m2}]：[Monads@{so o m1 m2}] 的界。- [PDiscK@{o so s u u0 e}] 和代数上的常数，[PDiscK_alg]、[PDiscKI_not_Full] 和 [PDiscKI_not_Equivalence] 之间：所以 so <= e，[Sets] 的对象低于 [EilenbergMoore@{e so s o}] 。[PDiscK_forget_strict] 添加了 [a] 和 [b]，[Functor_StrictEq_Setoid] 的层级（o < b，它自身的严格上界），以及该集合体的传输限制（Logic.transport、Logic.transport_r、eq_rect、eq_rect_r 和 eq_sym_involutive，仅在它的块中）。- [PDiscK_not_Cat_iso@{o so s u u0 c}] 在 e := so 处声明，单对象层级 [Cat] 允许两端；c 是 [Cat] 自身的对象层级，因此 so < c。- [PForget_not_Monadic@{o so m m0 m1 m3 m6}] 表示 [Monadic@{m m0 m1 so m3 o so m6}] 并携带 [Monadic] 自身的区块，其中 o < so 来自 [PForget]：在 [Monadic] 的五个自由层的每一个值上反驳都成立。- 证人 [pbool_to_indisc], [no_pindisc_to_bool], [PForget_not_Full] 和 [PForget_not_ReflectsIsos]：[@{o so}]，o < so。

 未交付。在类型值 [Top] 上的任何内容，但否定单子性 (Instance/Top/Monadicity/TypeValued.v)。上面的莱布尼茨形式（被拒绝）。在 [Cat] 中显示 K 不是同构，其同构是等价；Instance/StrictCat.v 中的同构不被考虑。是否 [PForget] 满足粗略定理的其他假设，或创建 Monad/Monadicity/Beck.v 精确形式的共轭器，尚未检查。
*)

(** ** The induced monad / ** 诱导幺半群 *)

(* [s] is the strict level of [Compose] in [PForget ◯ PDisc]; it is the same [s] as the Eilenberg-Moore level below, which [EM_Comparison] identifies with it. / [s] 是 [PForget ◯ PDisc] 中 [Compose] 的严格层级；它与下面的 Eilenberg-Moore 层级相同，[EM_Comparison] 将其与之对应。 *)
Definition PDiscT@{o so s | o < so, o < s +} :
  Sets@{o so} ⟶ Sets@{o so} :=
  PForget@{o so} ◯ PDisc@{o so}.

Definition PDiscMonad@{o so s u u0 | o < so, o < s, o < u +} :
  @Monad Sets@{o so} PDiscT@{o so s} :=
  @Adjunction_Induced_Monad _ _ _ _ PDisc_PForget@{o so u u0}.

Example PDiscT_fobj@{o so s | o < so, o < s +} (x : Sets@{o so}) :
  fobj[PDiscT@{o so s}] x = x := eq_refl.

Example PDiscT_fmap@{o so s | o < so, o < s +} (x y : Sets@{o so})
  (f : x ~> y) : fmap[PDiscT@{o so s}] f = f := eq_refl.

Example PDisc_PForget_unit@{o so u u0 | o < so, o < u +}
  (x : Sets@{o so}) :
  @unit _ _ _ _ PDisc_PForget@{o so u u0} x = id := eq_refl.

Example PDisc_PForget_counit@{o so u u0 | o < so, o < u +}
  (X : PTopCat@{o so}) :
  pmap (@counit _ _ _ _ PDisc_PForget@{o so u u0} X) = setoid_morphism_id
  := eq_refl.

Example PDiscMonad_ret@{o so s u u0 | o < so, o < s, o < u +}
  (x : Sets@{o so}) : @ret _ _ PDiscMonad@{o so s u u0} x = id := eq_refl.

Example PDiscMonad_join@{o so s u u0 | o < so, o < s, o < u +}
  (x : Sets@{o so}) : @join _ _ PDiscMonad@{o so s u u0} x = id := eq_refl.

(*
 The data fields of the functor and of the monad, as functions: I = ⟨I,
 1, 1⟩ on the nose. 

 --------
 函子和单子的数据信息字段，作为函数：I = ⟨I, 1, 1⟩ 一丝不差。
*)
Example PDiscT_fields@{o so s | o < so, o < s +} :
  (@fobj _ _ PDiscT@{o so s}, @fmap _ _ PDiscT@{o so s})
    = (@fobj _ _ Id[Sets@{o so}], @fmap _ _ Id[Sets@{o so}]) := eq_refl.

Example PDiscMonad_fields@{o so s u u0 | o < so, o < s, o < u +} :
  (@ret _ _ PDiscMonad@{o so s u u0}, @join _ _ PDiscMonad@{o so s u u0})
    = (@ret _ _ (IdMonad@{so o} Sets@{o so}),
       @join _ _ (IdMonad@{so o} Sets@{o so})) := eq_refl.

(* * ** The isomorphism with the identity monad, in [Monads Sets] / * ** 与恒等单子在 [Monads Sets] 中的同构 *)

Definition disc_to_id@{o so s | o < so, o < s +} :
  PDiscT@{o so s} ⟹ Id[Sets@{o so}].
Proof.
  unshelve refine (Build_Transform' (F:=PDiscT@{o so s})
                     (G:=Id[Sets@{o so}]) (fun x => id) _).
  intros x y f z; simpl. reflexivity.
Defined.

Definition id_to_disc@{o so s | o < so, o < s +} :
  Id[Sets@{o so}] ⟹ PDiscT@{o so s}.
Proof.
  unshelve refine (Build_Transform' (F:=Id[Sets@{o so}])
                     (G:=PDiscT@{o so s}) (fun x => id) _).
  intros x y f z; simpl. reflexivity.
Defined.

Definition disc_id_hom@{o so s u u0 | o < so, o < s, o < u +} :
  MonadHom@{so o} PDiscMonad@{o so s u u0} (IdMonad@{so o} Sets@{o so}).
Proof.
  unshelve refine {| mh_transform := disc_to_id@{o so s} |};
    intros x z; simpl; reflexivity.
Defined.

Definition id_disc_hom@{o so s u u0 | o < so, o < s, o < u +} :
  MonadHom@{so o} (IdMonad@{so o} Sets@{o so}) PDiscMonad@{o so s u u0}.
Proof.
  unshelve refine {| mh_transform := id_to_disc@{o so s} |};
    intros x z; simpl; reflexivity.
Defined.

Example disc_id_hom_component@{o so s u u0 | o < so, o < s, o < u +}
  (x : Sets@{o so}) :
  transform[mh_transform disc_id_hom@{o so s u u0}] x = id := eq_refl.

Example id_disc_hom_component@{o so s u u0 | o < so, o < s, o < u +}
  (x : Sets@{o so}) :
  transform[mh_transform id_disc_hom@{o so s u u0}] x = id := eq_refl.

Definition disc_id_iso@{o so s u u0 m1 m2 |
  o < so, o < s, o < u, so <= m1, o <= m1, so <= m2, o <= m2 +} :
  @Isomorphism (Monads@{so o m1 m2} Sets@{o so})
    (existT _ PDiscT@{o so s} PDiscMonad@{o so s u u0})
    (existT _ Id[Sets@{o so}] (IdMonad@{so o} Sets@{o so})).
Proof.
  unshelve refine (@Build_Isomorphism (Monads@{so o m1 m2} Sets@{o so})
                     (existT _ PDiscT@{o so s} PDiscMonad@{o so s u u0})
                     (existT _ Id[Sets@{o so}] (IdMonad@{so o} Sets@{o so}))
                     disc_id_hom@{o so s u u0} id_disc_hom@{o so s u u0}
                     _ _);
    intros x z; simpl; reflexivity.
Defined.

(* * ** The comparison functor is the forgetful functor / * ** 比较函子是忘记函子 *)

Definition PDiscK@{o so s u u0 e | o < so, o < s, o < u, so <= e +} :
  PTopCat@{o so} ⟶
    @EilenbergMoore@{e so s o} Sets@{o so} PDiscT@{o so s}
      PDiscMonad@{o so s u u0} :=
  EM_Comparison PDisc_PForget@{o so u u0}.

Example PDiscK_forget_obj@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} (X : PTopCat@{o so}) :
  fobj[EM_Forget _ ◯ PDiscK@{o so s u u0 e}] X = fobj[PForget@{o so}] X
  := eq_refl.

Example PDiscK_forget_map@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} (X Y : PTopCat@{o so}) (f : X ~> Y) :
  fmap[EM_Forget _ ◯ PDiscK@{o so s u u0 e}] f = fmap[PForget@{o so}] f
  := eq_refl.

(* The structure map of K X is the identity setoid morphism itself. / K X 的结构映射本身就是恒等等价态射。 *)
Example PDiscK_alg@{o so s u u0 e | o < so, o < s, o < u, so <= e +}
  (X : PTopCat@{o so}) :
  t_alg[`2 (fobj[PDiscK@{o so s u u0 e}] X)] = setoid_morphism_id
  := eq_refl.

Definition PDiscK_forget_strict@{o so s u u0 e a b |
  o < so, o < s, o < u, so <= e, o < b, so <= a, o <= a +} :
  @equiv _ (@Functor_StrictEq_Setoid@{a a so so b o} PTopCat@{o so}
              Sets@{o so})
    (EM_Forget _ ◯ PDiscK@{o so s u u0 e}) PForget@{o so}.
Proof.
  exists (fun X => eq_refl).
  intros X Y f. reflexivity.
Defined.

Definition PDiscK_forget@{o so s u u0 e | o < so, o < s, o < u, so <= e +} :
  EM_Forget _ ◯ PDiscK@{o so s u u0 e} ≈ PForget@{o so} :=
  EM_Comparison_Forget PDisc_PForget@{o so u u0}.

(** ** Set^I = Set *)

Lemma PDiscMonad_alg_id@{o so s u u0 | o < so, o < s, o < u +}
  (a : Sets@{o so})
  (ν : @TAlgebra Sets@{o so} PDiscT@{o so s} PDiscMonad@{o so s u u0} a)
  (x : a) : t_alg[ν] x ≈ x.
Proof. exact (@t_id _ _ _ _ ν x). Qed.

Definition EM_PDisc_counit@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} :
  @EM_Forget@{so o s e} Sets@{o so} PDiscT@{o so s} PDiscMonad@{o so s u u0}
    ◯ @EM_Free@{so o s e} Sets@{o so} PDiscT@{o so s}
        PDiscMonad@{o so s u u0}
    ≈ Id[Sets@{o so}].
Proof.
  exists (fun x => iso_id).
  intros x y f z; simpl. reflexivity.
Defined.

Definition EM_PDisc_unit_iso@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +}
  (X : @EilenbergMoore@{e so s o} Sets@{o so} PDiscT@{o so s}
         PDiscMonad@{o so s u u0}) :
  @Isomorphism (@EilenbergMoore@{e so s o} Sets@{o so} PDiscT@{o so s}
                  PDiscMonad@{o so s u u0})
    X (fobj[@EM_Free@{so o s e} Sets@{o so} PDiscT@{o so s}
              PDiscMonad@{o so s u u0}
             ◯ @EM_Forget@{so o s e} Sets@{o so} PDiscT@{o so s}
                 PDiscMonad@{o so s u u0}] X).
Proof.
  unshelve econstructor.
  - unshelve refine (@Build_TAlgebraHom Sets@{o so} PDiscT@{o so s}
                       PDiscMonad@{o so s u u0} _ _ _ _ id _).
    intro x; simpl. exact (PDiscMonad_alg_id _ (`2 X) x).
  - unshelve refine (@Build_TAlgebraHom Sets@{o so} PDiscT@{o so s}
                       PDiscMonad@{o so s u u0} _ _ _ _ id _).
    intro x; simpl. exact (symmetry (PDiscMonad_alg_id _ (`2 X) x)).
  - intro x; simpl. reflexivity.
  - intro x; simpl. reflexivity.
Defined.

Definition EM_PDisc_unit@{o so s u u0 e | o < so, o < s, o < u, so <= e +} :
  Id[@EilenbergMoore@{e so s o} Sets@{o so} PDiscT@{o so s}
       PDiscMonad@{o so s u u0}]
    ≈ @EM_Free@{so o s e} Sets@{o so} PDiscT@{o so s}
        PDiscMonad@{o so s u u0}
        ◯ @EM_Forget@{so o s e} Sets@{o so} PDiscT@{o so s}
            PDiscMonad@{o so s u u0}.
Proof.
  exists EM_PDisc_unit_iso.
  intros X Y f x; simpl. reflexivity.
Defined.

Definition EM_PDisc_equivalence@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} :
  EquivalenceOfCategories
    (@EM_Forget@{so o s e} Sets@{o so} PDiscT@{o so s}
       PDiscMonad@{o so s u u0}) :=
  @Build_EquivalenceOfCategories _ _ _ _
    EM_PDisc_counit@{o so s u u0 e} EM_PDisc_unit@{o so s u u0 e}.

Definition PDiscK_free_iso@{o so s u u0 e | o < so, o < s, o < u, so <= e +}
  (X : PTopCat@{o so}) :
  @Isomorphism (@EilenbergMoore@{e so s o} Sets@{o so} PDiscT@{o so s}
                  PDiscMonad@{o so s u u0})
    (fobj[PDiscK@{o so s u u0 e}] X)
    (fobj[@EM_Free@{so o s e} Sets@{o so} PDiscT@{o so s}
            PDiscMonad@{o so s u u0} ◯ PForget@{o so}] X).
Proof.
  unshelve econstructor;
    [ unshelve refine (@Build_TAlgebraHom Sets@{o so} PDiscT@{o so s}
                         PDiscMonad@{o so s u u0} _ _ _ _ id _)
    | unshelve refine (@Build_TAlgebraHom Sets@{o so} PDiscT@{o so s}
                         PDiscMonad@{o so s u u0} _ _ _ _ id _)
    | | ]; intro x; simpl; reflexivity.
Defined.

Definition PDiscK_free@{o so s u u0 e | o < so, o < s, o < u, so <= e +} :
  PDiscK@{o so s u u0 e}
    ≈ @EM_Free@{so o s e} Sets@{o so} PDiscT@{o so s}
        PDiscMonad@{o so s u u0} ◯ PForget@{o so}.
Proof.
  exists PDiscK_free_iso.
  intros X Y f x; simpl. reflexivity.
Defined.

(*
 The comparison into the algebras of [IdMonad Sets], through θ* of the
 morphism of monads [id_disc_hom]. 

 --------
 通过单子 [id_disc_hom] 的态射 θ* 对 [IdMonad Sets] 的代数进行比较。
*)
Definition PDiscKI@{o so s u u0 e | o < so, o < s, o < u, so <= e +} :
  PTopCat@{o so} ⟶
    @EilenbergMoore@{e so s o} Sets@{o so} Id[Sets@{o so}]
      (IdMonad@{so o} Sets@{o so}) :=
  mh_EM@{so o e s} id_disc_hom@{o so s u u0} ◯ PDiscK@{o so s u u0 e}.

Example PDiscKI_forget_obj@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} (X : PTopCat@{o so}) :
  fobj[EM_Forget Id[Sets@{o so}] ◯ PDiscKI@{o so s u u0 e}] X
    = fobj[PForget@{o so}] X := eq_refl.

Example PDiscKI_forget_map@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} (X Y : PTopCat@{o so}) (f : X ~> Y) :
  fmap[EM_Forget Id[Sets@{o so}] ◯ PDiscKI@{o so s u u0 e}] f
    = fmap[PForget@{o so}] f := eq_refl.

Example PDiscKI_alg@{o so s u u0 e | o < so, o < s, o < u, so <= e +}
  (X : PTopCat@{o so}) (x : X) :
  t_alg[`2 (fobj[PDiscKI@{o so s u u0 e}] X)] x = x := eq_refl.

(* * ** Not full, not an equivalence, not monadic / * ** 不是完整的，不是等价的，不是单元的 *)

Definition pbool_to_indisc@{o so | o < so +} :
  PBool@{o} ~{PTopCat@{o so}}~> PTwoIndisc@{o} :=
  pindisc_mor _ PBool@{o} setoid_morphism_id.

Lemma no_pindisc_to_bool@{o so | o < so +}
  (g : PTwoIndisc@{o} ~{PTopCat@{o so}}~> PBool@{o}) :
  (∀ b : bool, pmap g b = b) → False.
Proof.
  intros Hg.
  assert (Hopen : POpen PTwoIndisc@{o} (fun b => pmap g b = true)).
  { apply (pcont g (fun b => b = true)).
    unfold pdisc_open. intros x y Hxy e. cbn in Hxy. destruct Hxy. exact e. }
  assert (H : pmap g false = true) by exact (Hopen true false (Hg true)).
  rewrite (Hg false) in H. discriminate H.
Qed.

Lemma PForget_not_Full@{o so | o < so +} : Full PForget@{o so} → False.
Proof.
  intros HF.
  apply (no_pindisc_to_bool
           (@prefmap _ _ _ HF PTwoIndisc@{o} PBool@{o} setoid_morphism_id)).
  intro b.
  exact (@fmap_sur _ _ _ HF PTwoIndisc@{o} PBool@{o} setoid_morphism_id b).
Qed.

(*
 Every monadic functor is conservative, and [PForget] is not: it sends
 [pbool_to_indisc] to an isomorphism of [Sets], and that is not one.
 Hypothesis 3 of Monad/Monadicity/Crude.v's crude monadicity theorem. 

 --------
 每个单值函子都是保守的，而 [PForget] 不是：它将 [pbool_to_indisc] 映射为 [Sets] 的一个同构，而那不是同构。
 这是 Monad/Monadicity/Crude.v 中粗糙单值性定理的假设 3。
*)
Lemma PForget_not_ReflectsIsos@{o so | o < so +} :
  ReflectsIsos PForget@{o so} → False.
Proof.
  intros R.
  assert (If : @IsIsomorphism Sets@{o so} _ _
                 (fmap[PForget@{o so}] pbool_to_indisc@{o so})).
  { unshelve econstructor; [ exact setoid_morphism_id | intro b; reflexivity
                            | intro b; reflexivity ]. }
  destruct (@reflects_iso _ _ _ R _ _ _ If) as [g Hr Hl].
  apply (no_pindisc_to_bool g).
  intro b. exact (Hr b).
Qed.

Lemma PDiscK_not_Full@{o so s u u0 e | o < so, o < s, o < u, so <= e +} :
  Full PDiscK@{o so s u u0 e} → False.
Proof.
  intros HF.
  unshelve epose (a := @Build_TAlgebraHom Sets@{o so} _ _ _ _
                    (`2 (fobj[PDiscK@{o so s u u0 e}] PTwoIndisc@{o}))
                    (`2 (fobj[PDiscK@{o so s u u0 e}] PBool@{o}))
                    setoid_morphism_id _).
  { intro b; reflexivity. }
  apply (no_pindisc_to_bool (@prefmap _ _ _ HF PTwoIndisc@{o} PBool@{o} a)).
  intro b. exact (@fmap_sur _ _ _ HF PTwoIndisc@{o} PBool@{o} a b).
Qed.

Lemma PDiscK_not_Equivalence@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} :
  EquivalenceOfCategories PDiscK@{o so s u u0 e} → False.
Proof. intros E. exact (PDiscK_not_Full (Equivalence_Full E)). Qed.

(*
 The comparison into the algebras of [IdMonad Sets] is not full either:
 the identity of [bool] is an algebra map KI PTwoIndisc → KI PBool. 

 --------
 [IdMonad Sets] 的代数比较也不是完全的：
 [bool] 的单位是一个代数映射 KI PTwoIndisc → KI PBool。
*)
Lemma PDiscKI_not_Full@{o so s u u0 e | o < so, o < s, o < u, so <= e +} :
  Full PDiscKI@{o so s u u0 e} → False.
Proof.
  intros HF.
  unshelve epose (a := @Build_TAlgebraHom Sets@{o so} _ _ _ _
                    (`2 (fobj[PDiscKI@{o so s u u0 e}] PTwoIndisc@{o}))
                    (`2 (fobj[PDiscKI@{o so s u u0 e}] PBool@{o}))
                    setoid_morphism_id _).
  { intro b; reflexivity. }
  apply (no_pindisc_to_bool (@prefmap _ _ _ HF PTwoIndisc@{o} PBool@{o} a)).
  intro b. exact (@fmap_sur _ _ _ HF PTwoIndisc@{o} PBool@{o} a b).
Qed.

Lemma PDiscKI_not_Equivalence@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} :
  EquivalenceOfCategories PDiscKI@{o so s u u0 e} → False.
Proof. intros E. exact (PDiscKI_not_Full (Equivalence_Full E)). Qed.

Lemma PDiscK_not_Cat_iso@{o so s u u0 c | o < so, o < s, o < u, so < c +} :
  @IsIsomorphism Cat _ _ PDiscK@{o so s u u0 so} → False.
Proof.
  intros I.
  apply PDiscK_not_Equivalence.
  exact (@Build_EquivalenceOfCategories _ _ _ (@two_sided_inverse _ _ _ _ I)
           (@is_right_inverse _ _ _ _ I)
           (symmetry (@is_left_inverse _ _ _ _ I))).
Qed.

Lemma PForget_not_Monadic@{o so m m0 m1 m3 m6 |
  o < so, o < m0, so <= m, so <= m1, so <= m3, m1 <= m, m3 <= m +} :
  Monadic@{m m0 m1 so m3 o so m6} PForget@{o so} → False.
Proof.
  intros [F [A E]].
  pose proof (Equivalence_Full E) as HF.
  lazymatch type of E with
  | @EquivalenceOfCategories _ ?EM ?K =>
    assert (If : @IsIsomorphism Sets@{o so} _ _
                   (fmap[EM_Forget _] (fmap[K] pbool_to_indisc@{o so})))
  end.
  { unshelve econstructor; [ exact setoid_morphism_id | intro b; reflexivity
                            | intro b; reflexivity ]. }
  destruct (@reflects_iso _ _ _ (em_forget_reflects_isos _) _ _ _ If)
    as [g Hr Hl].
  apply (no_pindisc_to_bool (@prefmap _ _ _ HF PTwoIndisc@{o} PBool@{o} g)).
  intro b. transitivity (t_alg_hom[g] b).
  - exact (@fmap_sur _ _ _ HF PTwoIndisc@{o} PBool@{o} g b).
  - exact (Hr b).
Qed.
