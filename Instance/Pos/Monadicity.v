Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
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
Require Import Category.Monad.Monadicity.BeckObjects.
Require Import Category.Construction.Reflective.Monadic.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.Sets.Propositional.Full.
Require Import Category.Instance.Pos.
Require Import Category.Instance.Proset.Monotone.

Generalizable All Variables.

(*
   * * The discrete-poset adjunction: the identity monad over propositional
   setoids, the truncation monad over [Sets], and [Pos_Forget] not
   monadic 

   --------
   * * 离散偏序集合对偶：命题集合等价类上的恒等单子，  [Sets] 上的截断单子，以及  [Pos_Forget] 非单子化
*)

(*
 Awodey, “Category Theory”, Carnegie Mellon pre-print of the 1st ed.
 (September 2005), §10.3, printed p. 278 (PDF p. 287), read from the
 page image: “An example of a right adjoint that is not monadic is the
 forgetful functor from posets, U : Pos → Sets.  Its left adjoint F is
 the discrete poset functor.  For any set X, therefore, one has as the
 unit the identity function X = UF(X).  The reader can easily show
 that the Eilenberg-Moore category for T = 1_Sets is then just Sets
 itself” (catalog id awodey:10.3:example-pos-not-monadic).
 Mac Lane, “Categories for the Working Mathematician”, 2nd ed. (GTM 5),
 §VI.3, book p. 144 (PDF p. 153), runs the same argument for the
 discrete topology; that example is Instance/Top/Monadicity.v's.
 nLab: https://ncatlab.org/nlab/show/monadic+functor
 nLab: https://ncatlab.org/nlab/show/propositional+truncation
 Library: the standard library's Logic/IndefiniteDescription.v

 BACKGROUND.  Awodey's example has the shape of Mac Lane's.  A set
 carries exactly one discrete order, so the unit of the adjunction is
 the identity, the induced monad is the identity monad, its algebras are
 the sets, and the comparison functor is the forgetful functor itself.
 That functor is not full: the identity of a two-element set is monotone
 from the discrete order to the chain false ≤ true, and not back.  So
 the comparison is not an equivalence and U is not monadic.  Awodey
 leaves the argument to the reader.  This file gives one, in two
 settings, because over this library's [Sets] the induced monad is not
 provably the identity monad without an axiom (below).

 THE READING IMPLEMENTED.  Awodey's Sets has a propositional equality.
 The tree's [Sets] (Instance/Sets.v) is Bishop sets, whose ≈ is
 [Type]-valued.  Instance/Pos.v's [PosetObject] has a [Prop]-valued
 order and antisymmetry into ≈, so every poset's setoid is
 propositional ([pos_PropEquiv]: x ≈ y exactly when x ≤ y and y ≤ x).
 A discrete poset that kept the carrier and ≈ of a setoid S would
 therefore supply a [PropEquiv] on S (Lib/Setoid/Propositional.v); an
 arbitrary object of [Sets] has none in the tree, and a [PropEquiv] on
 every object at once is interderivable with the principle
 [SetsTruncElim] below ([all_PropEquiv_trunc], [trunc_all_PropEquiv]),
 itself interderivable with ∀ A, inhabited A → A ([trunc_choice],
 [choice_trunc]).  So the discrete poset changes the ≈ of its setoid:
 [PosDisc S] compares by [inhabited (x ≈ y)].  Two readings follow, and
 both are built.
 - Over propositional setoids.  Instance/Sets/Propositional/Full.v's
 full subcategory [PropSets] is the reading of Awodey's Sets taken
 here.  [PosDiscP], ordered by the setoid's own [pequiv], is left
 adjoint to [PosPForget], which is [Pos_Forget] factored through
 [PropSets].  The unit is the identity function, as on the page, and
 the induced monad is isomorphic to the identity monad in #468's
 [Monads PropSets] with identity components, UNCONDITIONALLY
 ([MPosP_Id_iso]).
 - Over the tree's [Sets].  The discrete poset is [PosDiscP] after the
 reflector [PropSets_trunc] of [Sets] onto [PropSets], on objects and on
 arrows at [eq_refl] ([PosDisc_obj], [PosDisc_map]); the functor
 equation is refused, structurally past the standard library (R19).  The
 induced monad is the monad of that reflection, the truncation of ≈
 ([MPos_trunc_iso]), and not the identity; its functor agrees with the
 reflection's on objects and arrows at [eq_refl] ([TPos_fobj],
 [TPos_fmap]), and the functor equation is refused only through the
 opacity of the tree's own [Qed] proofs (R16; STRENGTHS below).  It is
 isomorphic to the identity monad EXACTLY WHEN ∀ A : Type@{c}, inhabited
 A → A ([MPos_Id_iff]); even a bare morphism of monads into the identity
 monad gives that principle, from this monad ([MPos_to_Id_trunc]) or
 from the monad of any left adjoint of [Pos_Forget]
 ([any_adj_to_Id_trunc]).  The principle is consistent with
 axiom-free Coq and believed independent of it.  It is consistent,
 argued: the axiom
 [constructive_indefinite_description] of the standard library's
 Logic/IndefiniteDescription.v gives it, as fun A h => proj1_sig
 (constructive_indefinite_description (fun _ : A => True) (match h with
 inhabits a => ex_intro _ a I end)); that term compiles, and [Print
 Assumptions] on it lists that axiom alone, so it is not shipped: no
 constant here depends on an axiom.  It follows from informative
 excluded middle, the tree's [IEM@{c}] written out ([choice_of_IEM]), so
 [MPos_IEM_Id_iso] is an in-tree closed conditional; and it is
 interderivable, level for level, with Instance/Sets/Classifier/
 OneLevel.v's [Untruncate@{c}] written out ([untr_of_choice],
 [choice_of_untr]; both written-out hypotheses are those constants at
 [eq_refl], control C53). CORRECTION (#1349): those two are
 Instance/Sets/Propositional/Full.v's now, moved there unchanged.
 It is not provable without an axiom, by a
 normal-form argument, sketched here and not proved in-tree.  A closed
 proof, every constant unfolded, opaque ones included, would normalize
 to λ A h. t with t : A in the context A : Type@{c}, h : inhabited A. As
 A is a variable type, t is neither an abstraction nor a constructor, so
 it is neutral, headed by A, by h or by an eliminator.  A is not an
 inhabitant of A.  An elimination of h returns in [Prop] or [SProp],
 which A is not (the refusal R10 of the probe, “Incorrect elimination”),
 so a spine from h to A must pass through a proposition with singleton
 elimination eliminated into [Type] (e.g. False, eq, True, and, Acc).
 False has no proof in that context: substituting unit for A and
 inhabits tt for h would give a closed proof of False.  The case of eq
 is where the sketch stops: a branch after matching on an equation
 X = A has type P X, not A, so it turns on which equations between A
 and inhabitable types are derivable, which this sketch does not
 settle (nor Acc's functional argument).  So the unprovability is
 argued, not established.  Cf. the HoTT book, IAS 2013, Exercise 3.11,
 for the univalent counterpart.
 Neither reading corrects the page.  Over the tree's [Sets] “the unit
 the identity function X = UF(X)” holds of carriers and functions
 ([TPos_carrier], [MPos_ret]) and is refused of setoids (R4 in the
 probe); over [PropSets] it holds of setoids ([TPosP_setoid]) and is
 refused only of the [PropEquiv] witness, which [PosPForget] recomputes
 from the order (R7, R12).

 IN-TREE CONNECTIONS.
 - Instance/Pos.v: [Pos], [Pos_Forget] and [PosetObject]; its header
 states antisymmetry at the setoid level, which is what forces the
 truncation above.
 - Instance/Sets/Propositional/Full.v: [PropSets], [PropSets_lift] (so
 [PosPForget]), the reflection [PropSets_trunc_Incl] and its bundle
 [PropSets_Reflective], from which Construction/Reflective/ Monadic.v's
 [Reflective_Monadic] gives [PropSets_Incl_Monadic]. [Pos_Forget] is
 [PropSets_Incl] after [PosPForget], on objects and arrows at [eq_refl]
 and ≈ as functors (the functor equation is refused, structurally past
 the standard library: R18): the first factor is monadic (for the
 truncation monad), the second induces the identity monad and is not
 monadic ([PosPForget_not_Monadic]).  Since #1349 that file also
 holds [SquashSetoid], which [trunc_choice] reads, and
 [untr_of_choice] and [choice_of_untr], moved there.
 - Monad/Identity.v ([IdMonad], [IdMonad_EM_equivalence]), #468's
 Monad/Morphism.v ([MonadHom], [Monads]), Monad/Comparison.v
 ([Adjunction_Induced_Monad], [Monadic]); the non-monadicity uses
 Monad/Monadicity/BeckObjects.v's [em_forget_reflects_isos] and
 Theory/Equivalence/FullFaithful.v's [Equivalence_Full], as
 Instance/Top/Monadicity.v does; the chain is ordered by
 Instance/Proset/Monotone.v's [bool_le].
 - Instance/Top/Monadicity.v is Mac Lane's example over [PTopCat]: a
 topology imposes no antisymmetry, so there the discrete space keeps
 its setoid, and the functor, unit and multiplication of the monad
 are the identity at [eq_refl] on objects and arrows.

 WHAT IS HERE.
 - [pos_PropEquiv]; [PosPForget], with [Pos_Forget_factor_obj],
 [Pos_Forget_factor_map] and [Pos_Forget_factor].
 - Over [PropSets]: [PosDiscPObj], [PosDiscP_fmap], [PosDiscP], the
 transposes [posdiscP_from] and [posdiscP_to], [posdiscP_iso] and
 the adjunction [PosDiscP_PosPForget]; [TPosP] and [MPosP] with the
 readbacks [TPosP_setoid], [TPosP_fmap], [TPosP_pequiv], [MPosP_ret]
 and [MPosP_join]; [TPosP_to_id], [id_to_TPosP], the morphisms of
 monads [MPosP_to_Id] and [Id_to_MPosP] with their component
 readbacks, and [MPosP_Id_iso]; [PropSets_EM_Id_equivalence], the
 Eilenberg-Moore sentence for T = 1 at [PropSets].
 - Over [Sets]: [PosDiscObj] (with [PosDiscObj_le]), [PosDisc] (with
 [PosDisc_obj], [PosDisc_map]), [posdisc_from], [posdisc_to],
 [posdisc_iso] and the adjunction [PosDisc_Pos_Forget]; [TPos] and
 [MPos] with [TPos_fobj], [TPos_fmap], [TPos_carrier], [TPos_equiv],
 [MPos_ret] and [MPos_join]; the truncation monad: [TPos_to_trunc],
 [trunc_to_TPos], [MPos_to_trunc], [trunc_to_MPos] and
 [MPos_trunc_iso]; the identity monad: [id_to_TPos] and [Id_to_MPos]
 (unconditional), [SetsTruncElim] (every setoid of [Sets] eliminates
 its own truncation), [MPos_to_Id_trunc] (any morphism of monads
 MPos → IdMonad gives it), [TPos_to_id], [MPos_to_Id] and
 [MPos_Id_iso] (under it), [choice_setoid], [trunc_choice],
 [choice_trunc] and [MPos_Id_iff]; [all_PropEquiv_trunc] and
 [trunc_all_PropEquiv] (a [PropEquiv] on every object of [Sets]);
 [any_adj_to_Id_trunc] (every left adjoint of [Pos_Forget] whose
 [Adjunction] record sits at that lemma's universe instance, the
 strict slot at so);
 [untr_of_choice], [choice_of_untr], [choice_of_IEM] and
 [MPos_IEM_Id_iso] (the principle under the tree's other names).
 CORRECTION (#1349): [choice_setoid] is now
 Instance/Sets/Propositional/Full.v's [SquashSetoid], by
 definition, and [untr_of_choice] and [choice_of_untr] moved to that
 file.
 - Not monadic: [bool_le_antisym], [BoolDiscPos], [BoolChainPos],
 [bool_disc_to_chain], [no_bool_chain_to_disc], [Pos_Forget_not_Full],
 [Pos_Forget_not_ReflectsIsos], [Pos_Forget_not_Monadic] and
 [PosPForget_not_Monadic]; the two negations of [Monadic] hold for
 every adjunction, since the proof is by conservativity.  The
 contrast is [PropSets_Incl_Monadic].

 THE ISSUE'S PREMISES, dated.  Issue #469 was filed on 2026-07-23.  The
 appended Awodey box's “(needs the category of posets from #641)” was
 accurate when filed and has been met since PR #1076 (merged
 2026-08-13).  Its “the induced monad computed to be the identity” is
 delivered over [PropSets] ([MPosP_Id_iso]) and, over the tree's
 [Sets], as the characterization [MPos_Id_iff]: a stated deviation.

 STRENGTHS.  By [eq_refl]: [Pos_Forget_factor_obj],
 [Pos_Forget_factor_map], [TPosP_setoid], [TPosP_fmap], [TPosP_pequiv],
 [MPosP_ret], [MPosP_join], [MPosP_to_Id_component],
 [Id_to_MPosP_component], [PosDiscObj_le], [PosDisc_obj], [PosDisc_map],
 [TPos_fobj], [TPos_fmap], [TPos_carrier], [TPos_equiv], [MPos_ret] and
 [MPos_join].  Up to ≈: [Pos_Forget_factor], in Theory/Functor.v's
 [Functor_Setoid], and the inverse laws of [MPosP_Id_iso],
 [MPos_trunc_iso], [MPos_Id_iso] and [MPos_IEM_Id_iso].

 Refused, each read in a copy of the whole of Test/ProbeMonadicity469.v
 with that one command unguarded, and pinned there with its controls:
 the setoid equation fobj[TPos] S = S (R4) and its cause, the ≈ of
 fobj[TPos] S against that of S (R11); the functor equation
 TPos = Id[Sets] (R5); the unit ret S = id (R6), refused at the type of
 id, fobj[TPos] S not converting with S; over [PropSets], the object
 equation at a pair (S; P) (R7) and its cause, the recomputed [pequiv]
 against that of P (R12), and the same equation at a variable object
 (R20); TPosP = Id[PropSets] (R8); the two monads as equal objects of
 [Monads PropSets] (R9); TPos = PropSets_Incl ◯ PropSets_trunc (R16);
 (TPos; MPos) and the monad of the reflection [PropSets_trunc_Incl] as
 equal objects of [Monads Sets] (R17); the functor equation
 PropSets_Incl ◯ PosPForget = Pos_Forget (R18), so [Pos_Forget_factor]
 is ≈ and no more; and PosDisc = PosDiscP ◯ PropSets_trunc (R19).  R6
 is a type mismatch at [id], a consequence of R4, with no “cannot
 unify” parenthetical; R10, the naive elimination of the truncation
 that [SetsTruncElim] supplies, is refused by the sort discipline
 (“Incorrect elimination”); the other thirteen are conversion refusals
 (“cannot unify”).  R8, R9 and R20 compare a variable object with a
 rebuilt pair, and Coq's [sigT] has no η: a variable of [PropSets] does
 not convert with (projT1 X; projT2 X) (R21), where a [SetoidObject], a
 record with primitive projections, does convert with its rebuilt
 record (C52).

 CAUSES.  R16 is OPACITY of the tree's own [Qed] proofs.  It is
 refused in the tree and ACCEPTED in the copy of the dependency closure
 described next.  Three further copies of that copy each make one group
 of obligations opaque again, as in the tree, and rebuild what depends
 on it: [Compose]'s two [Next Obligation]s and its automatically solved
 one (Theory/Functor.v), [Incl]'s (Construction/Subcategory.v), and
 [Pos_Forget]'s three (Instance/Pos.v).  R16 is refused in each of the
 three, with the tree's text (checked by [About] on
 [Compose_obligation_1] to [Compose_obligation_3], [Incl_obligation_1]
 and [Pos_Forget_obligation_1] in each copy: opaque in exactly its own
 group, and all opaque in the tree).  So each group alone keeps TPos
 and the reflection's functor apart, [PosDisc]'s proof fields copying
 [PropSets_trunc]'s.  The other conversion refusals stand in that
 copy, each stripped of its refutation keyword in a copy of the whole
 probe with its universe annotations removed (the copies of the two
 files there have none) and with R16 blanked in the copies of the
 commands that follow it, each refused inside its own command with the
 tree's text.  R4, R5, R7 to R9, R11, R12, R20 and R21 are STRUCTURAL:
 the two sides differ in their data (a truncated ≈, a recomputed
 witness), or one is stuck on a variable of a [sigT], which has no η;
 R21 names no constant of the tree.  R17 to R19 are STRUCTURAL past the
 standard library: their data converts (R16 and the unit of R17 are
 accepted there, and C44, C49 hold in the tree), and the normal forms of
 the proof fields behind R18 and R19 ([fmap_respects] and [fmap_id],
 read by [Eval cbv] there) contain the standard library's opaque
 [CMorphisms.trans_co_eq_inv_arrow_morphism_obligation_1], the residue
 Instance/Top/Monadicity.v's header records for its R1; for R17, the
 join's function converts there and the join as a setoid morphism is
 refused, and the normal form of [MPos]'s join properness field (read
 by [Eval cbv] there) contains that obligation four times, the
 reflection's none.  The copy: [Transparent Obligations] set and
 every [Qed] turned into [Defined], obligations included (checked by
 [About] on them), in the copy of the dependency closure made for
 Instance/Top/Monadicity.v, whose header names the four files it keeps
 as they are, extended by the ten modules this file adds, all ten
 turned.  The copies of this file and Instance/Sets/Propositional/
 Full.v there are earlier versions, whose constants in these statements
 are unchanged here, with their universe annotations removed, because a
 [Defined] proof exposes universes of its body that the binders here do
 not name.  Every control of the probe before its guard block is
 accepted there too.

 Thirty proofs end [Defined] (counted by token); closing each alone
 [Qed] in a copy of the two files and an earlier version of the probe,
 all but four stop something: [MPosP_Id_iso], [MPos_trunc_iso],
 [MPos_Id_iso] and [MPos_Id_iff] are [Defined] by the data convention
 only, and no control added to the probe since reads through any of
 the four.  CORRECTION (#1349): twenty-nine, by token, [choice_setoid]
 being a definition by [:=] now, of [SquashSetoid], which is [Defined]
 in Instance/Sets/Propositional/Full.v and load-bearing there for
 [trunc_choice] (that file's STRENGTHS).

 UNIVERSES, read off [About]; stdlib caps (compose, ID, Projections,
 projections, prod_rect, Logic_lemmas.equality, and eq_ind, whose first
 carrier is the [rewrite] in [no_bool_chain_to_disc]) left out, and the [+]
 is for them.  [c] is the carriers and homs, [so] the objects of [Sets] and
 [PropSets], [po] the objects of [Pos], and [p0] to [p3] the four auxiliary
 levels of [Pos@{po p0 p1 p2 p3 c}], whose objects are [PosetObject@{c c p0
 p1 p2 p3}]; [Pos_Forget@{po so p0 p2 p1 p3 c}]. Every block that mentions
 [Sets] or [PropSets] carries c < so, and every block where [Pos] occurs
 carries [Pos]'s own block c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c
 <= p0 and c <= p1.  [Set] occurs only as Set < p2, as Set < w in
 [pos_PropEquiv@{w c cp p0 p1 p2 p3}] ([PropEquivObj]'s own bound, w the
 level of the property, cp the proof level of the setoid; the callers take w
 := so and cp := c), and as Set < so and Set < po, which c < so and c < po
 imply.  The further levels: [s] is [Compose]'s strict level (c < s) in
 [TPos], [TPosP] and the readbacks through a composite; [a] and [r] are the
 free levels of the [Adjunction] records of [PosDisc_Pos_Forget] (or
 [PosDiscP_PosPForget]) and [PropSets_trunc_Incl], left by
 [Build_Adjunction']; [m1] and [m2] are [Monads@{so c m1 m2}]'s, with so and
 c below both; [any_adj_to_Id_trunc] names [s], the strict level of the
 [Compose] in the type of [Adjunction_Induced_Monad] (left unnamed it is
 instantiated at so, measured), and [a], its adjunction's free level;
 [untr_of_choice], [choice_of_untr] and [choice_of_IEM] bind c alone, with
 an empty block on Rocq 9.1.1 (their [+] is for the global levels that
 [inhabited] and [sum] carry on Coq 8.19.2 and 8.20.1); the negations of
 monadicity state [Monadic@{m m0 m1 po m3 c so m6}] with exactly [Monadic]'s
 own block there, so they hold at every value of its levels that
 [Pos_Forget] leaves free, the carrier c included (left unnamed, it is
 pinned to [Set], measured); [PropSets_Incl_Monadic] states [Monadic@{m so
 m1 so m3 c so r}], whose last level is the witness adjunction's own, so it
 is r.  No block has an equation.  On Coq 8.19.2 and 8.20.1 the named levels
 and their blocks are the same, and the [+] also covers eq.u0, sigT.u0,
 sigT.u1, inhabited.u0 and, in [choice_of_IEM], sum.u0 (measured by [About]
 there).  CORRECTION (#1349): [untr_of_choice] and [choice_of_untr] are
 Instance/Sets/Propositional/Full.v's now, with the same blocks (by
 [About] before and after); [choice_setoid], now [SquashSetoid] by definition,
 [trunc_choice] and [MPos_Id_iff] keep theirs on Rocq 9.1.1, the
 refutation in [trunc_choice] chosen for that (its comment).  On Coq
 8.19.2 and 8.20.1 those three gain c <= sum.u1, the level
 [SquashSetoid]'s [squash_rel] carries there, which their [+] covers
 (by [About] in overlays of master with this change and of this tree,
 which agree).

 NOT DELIVERED.  The Eilenberg-Moore category of [MPos] is not shown
 equivalent to [PropSets]: it would follow from [MPos_trunc_iso],
 Construction/Reflective/Monadic.v's [Reflective_EM_Equivalence] and
 #468's [mh_EM], and is not composed.  The comparison functors of the
 two adjunctions are not read back (Instance/Top/Monadicity.v does that
 for [PTopCat]).  For [MPosP] itself only the identity monad's
 Eilenberg-Moore equivalence is instantiated.  No in-tree statement
 says that ∀ A, inhabited A → A is unprovable; that is metatheory. 

 --------
 Awodey，《范畴论》，卡内基梅隆大学第1版预印本（2005年9月），§10.3，第278页（PDF第287页），从页面图像读取：“一个不是单子的右伴随例子是从偏序集到集合的遗忘函子 U : Pos → Sets。它的左伴随 F 是离散偏序集函子。因此，对于任意集合 X，其单位为恒等函数 X = UF(X)。读者可以很容易地证明，对于 T = 1_Sets 的 Eilenberg-Moore 范畴就是集合自身。”（目录编号 awodey:10.3:example-pos-not-monadic）。Mac Lane，《实用数学家的范畴论》，第2版（GTM 5），§VI.3，第144页（PDF第153页），对于离散拓扑运行了相同的论证；该例子即 Instance/Top/Monadicity.v 中的例子。nLab: https://ncatlab.org/nlab/show/monadic+functor 
 nLab: https://ncatlab.org/nlab/show/propositional+truncation 
 库: 标准库的 Logic/IndefiniteDescription.v

 背景。Awodey 的例子具有 Mac Lane 的形式。一个集合恰好携带一个离散序列，因此伴随的单位是恒等映射，诱导的单子是恒等单子，其代数是集合，比较函子就是忘记函子本身。该函子并非满函子：一个两元素集合的恒等映射从离散序到链 false ≤ true 是单调的，但反过来则不是。因此比较不是一个等价映射，U 也不是幂等的。Awodey 将这个论证留给读者。这个文件给出了两种情境下的论证，因为在这个库的 [Sets] 上，诱导的单子在没有引入公理的情况下不能被证明是恒等单子（如下所示）。阅读已实现。Awodey 的《集合》有一个命题等式。树的 [Sets]（Instance/Sets.v）是 Bishop 集合，其 ≈ 是 [Type] 值的。Instance/Pos.v 的 [PosetObject] 具有 [Prop] 值的顺序和进到 ≈ 的反对称性，因此每个偏序集的集合体都是命题性的（[pos_PropEquiv]：当且仅当 x ≤ y 且 y ≤ x 时 x ≈ y）。一个离散偏序集，如果保持集合体 S 的载体和 ≈，因此将会在 S 上提供一个 [PropEquiv]（Lib/Setoid/Propositional.v）；树中的任意对象 [Sets] 没有这样的结构，而同时在每个对象上提供 [PropEquiv] 与下列原理 [SetsTruncElim]（[all_PropEquiv_trunc]，[trunc_all_PropEquiv]）是相互可导的，该原理本身与 ∀ A, inhabited A → A（[trunc_choice]，[choice_trunc]）相互可导。因此离散偏序集改变了其集合体的 ≈：[PosDisc S] 通过 [inhabited (x ≈ y)] 进行比较。接下来是两篇读物，并且都已构建完成。- 关于命题集合范畴。Instance/Sets/Propositional/Full.v 的完整子范畴 [PropSets] 是此处采取的 Awodey 的集合读法。[PosDiscP]，由集合范畴自身的 [pequiv] 排序，是 [PosPForget] 的左伴随，而 [PosPForget] 又经由 [PropSets] 分解的 [Pos_Forget] 。单位是恒等函数，如页面所示，所诱导的幺半群与 #468 的 [Monads PropSets] 中具有恒等分量的恒等幺半群同构，无条件（[MPosP_Id_iso]）。- 关于树的 [Sets]。离散偏序集合是经过 [PropSets_trunc] 的反射器由 [Sets] 映射至 [PropSets] 后的 [PosDiscP]，对象和箭头在 [eq_refl] 上（[PosDisc_obj]，[PosDisc_map]）；函子方程被拒绝，在结构上超出了标准库（R19）。诱导的函子（monad）是该反射（reflection）的函子，是≈([MPos_trunc_iso])的截断，而不是恒等；它的函子在对象和箭头上与[eq_refl] ([TPos_fobj], [TPos_fmap]) 的反射一致，并且函子方程只因树自身[Qed]证明的不可透性而被拒绝（R16；见下文STRENGTHS）。它正好在 ∀ A : Type@{c}, 如果A非空 → A([MPos_Id_iff]) 时与恒等函子同构；即使只是一个进入恒等函子的函子态射，从这个函子([MPos_to_Id_trunc])或从[Pos_Forget]的任何左伴随函子的函子([any_adj_to_Id_trunc])也可以得到该原理。该原理与无公理Coq一致，并被认为与之无关。这是一致的，
 有人争论：标准库的 Logic/IndefiniteDescription.v 的公理 [constructive_indefinite_description] 赋予了它，如 fun A h => proj1_sig (constructive_indefinite_description (fun _ : A => True) (match h with inhabits a => ex_intro _ a I end))；该项可以编译，并且对其执行 [Print Assumptions] 时仅列出该公理，因此它未被随附：此处没有常量依赖于任何公理。它由信息排中律推导得出，树的 [IEM@{c}] 写出后为 ([choice_of_IEM])，所以 [MPos_IEM_Id_iso] 是树内封闭条件；并且它与 Instance/Sets/Classifier/OneLevel.v 的 [Untruncate@{c}] 写出后 ([untr_of_choice], [choice_of_untr]；两个写出的假设是 [eq_refl] 处的那些常量，控制 C53) 在每个级别上是可互推的。更正 (#1349)：那两个现在是 Instance/Sets/Propositional/Full.v 的内容，移动到那里时未作改动。没有公理，它是无法被证明的，通过正常形式的论证，在这里略述，但未在树中证明。一个封闭的证明，每个常量都展开，包括不透明的常量，将归一化为 λ A h. t，其中 t : A 在上下文 A : Type@{c}, h : inhabited A 中。由于 A 是一个变量类型，t 既不是抽象也不是构造函数，因此它是中性的，由 A、h 或消去器引导。A 不是 A 的成员。消去 h 会返回 [Prop] 或 [SProp]，而 A 不是（探针的拒绝 R10，“错误的消去”），因此从 h 到 A 的脊必须通过一个命题，其单元素消去被消去到 [Type]（例如 False、eq、True、and、Acc）。在那个上下文中，False 没有证明：将 unit 替换为 A，并将 inhabits tt 替换为 h，会得到一个关于 False 的封闭证明。eq 的情况是这里草图停止的地方：在匹配一个方程 X = A 后的一个分支的类型是 P X，而不是 A，所以它取决于 A 与可居类型之间哪些方程是可推导的，而这个草图并没有解决这个问题（Acc 的函数参数也没有）。因此其不可证明性是被论证的，而不是被确立的。参见 HoTT 书，IAS 2013，练习 3.11，关于同一性对应的情况。两种阅读方式都没有纠正该页内容。在树的 [Sets] 上，“单位 X = UF(X) 的恒等函数” 对载体和函数 ([TPos_carrier], [MPos_ret]) 成立，但对集合态 (R4 在探针中) 不成立；在 [PropSets] 上，它对集合态 ([TPosP_setoid]) 成立，仅对 [PropEquiv] 证据不成立，而 [PosPForget] 从顺序 (R7, R12) 重新计算。树内连接。- Instance/Pos.v：[Pos], [Pos_Forget] 和 [PosetObject]；其标题在集同类层次上声明反对称性，这正是导致上面的截断。- Instance/Sets/Propositional/Full.v：[PropSets], [PropSets_lift]（所以 [PosPForget]）、反射 [PropSets_trunc_Incl] 及其捆绑 [PropSets_Reflective]，从中 Construction/Reflective/Monadic.v 的 [Reflective_Monadic] 得到 [PropSets_Incl_Monadic]。[Pos_Forget] 在 [PosPForget] 后变为 [PropSets_Incl]，在 [eq_refl] 上的对象和箭头以及 ≈ 作为函子（函子方程被拒绝，结构上超过标准库：R18）：第一个因子是单子型的（用于截断单子），第二个引入恒等单子并非单子型（[PosPForget_not_Monadic]）。自 #1349 起，该文件还包含 [SquashSetoid]，被 [trunc_choice] 读取，以及 [untr_of_choice] 和 [choice_of_untr]，已经移到那里。- Monad/Identity.v ([IdMonad], [IdMonad_EM_equivalence])，#468 的 Monad/Morphism.v ([MonadHom], [Monads])，Monad/Comparison.v ([Adjunction_Induced_Monad], [Monadic])；非单子性使用了 Monad/Monadicity/BeckObjects.v 的 [em_forget_reflects_isos] 和 Theory/Equivalence/FullFaithful.v 的 [Equivalence_Full]，如 Instance/Top/Monadicity.v 所做；链的顺序由 Instance/Proset/Monotone.v 的 [bool_le] 决定。- Instance/Top/Monadicity.v 是 Mac Lane 在 [PTopCat] 上的例子：一个拓扑不强加反对称性，因此离散空间保持其集合等价关系，并且单子函子、单位和乘法在 [eq_refl] 上的对象和箭头上都是恒等的。这里的内容是什么。 - [pos_PropEquiv]；[PosPForget]，带有[Pos_Forget_factor_obj]、[Pos_Forget_factor_map]和[Pos_Forget_factor]。 - 关于[PropSets]：[PosDiscPObj]、[PosDiscP_fmap]、[PosDiscP]，换位[posdiscP_from]和[posdiscP_to]，[posdiscP_iso]以及联结[PosDiscP_PosPForget]；[TPosP]和[MPosP]，带有回读[TPosP_setoid]、[TPosP_fmap]、[TPosP_pequiv]、[MPosP_ret]和[MPosP_join]；[TPosP_to_id]、[id_to_TPosP]，幺半群的态射[MPosP_to_Id]和[Id_to_MPosP]及其组件回读，以及[MPosP_Id_iso]；[PropSets_EM_Id_equivalence]，T = 1在[PropSets]的艾伦伯格-摩尔句。- 超过 [Sets]：[PosDiscObj]（带有 [PosDiscObj_le]）、[PosDisc]（带有 [PosDisc_obj]、[PosDisc_map]）、[posdisc_from]、[posdisc_to]、[posdisc_iso] 及附加的 [PosDisc_Pos_Forget]；[TPos] 和 [MPos]，带有 [TPos_fobj]、[TPos_fmap]、[TPos_carrier]、[TPos_equiv]、[MPos_ret] 和 [MPos_join]；截断幺半群：[TPos_to_trunc]、[trunc_to_TPos]、[MPos_to_trunc]、[trunc_to_MPos] 和 [MPos_trunc_iso]；恒等幺半群：[id_to_TPos] 和 [Id_to_MPos]（无条件），[SetsTruncElim]（[Sets] 的每个集合等价类消除它自身的截断），[MPos_to_Id_trunc]（MPos → IdMonad 的任意幺半群态射赋予它），[TPos_to_id]、[MPos_to_Id] 和 [MPos_Id_iso]（在其下），[choice_setoid]、[trunc_choice]、[choice_trunc] 和 [MPos_Id_iff]；[all_PropEquiv_trunc] 和 [trunc_all_PropEquiv]（在 [Sets] 的每个对象上有一个 [PropEquiv]）；[any_adj_to_Id_trunc]（每个 [Pos_Forget] 的左伴随，其 [Adjunction] 记录位于该引理的宇宙实例中，严格槽位于此）；ZW160WZZ、ZW161WZZ、ZW162WZZ 和 [MPos_IEM_Id_iso]（树下的其他名称原则）。修正 (#1349)：[choice_setoid] 现在按定义为 Instance/Sets/Propositional/Full.v 中的 [SquashSetoid]，[untr_of_choice] 和 [choice_of_untr] 已移动到该文件中。- 非单子：[bool_le_antisym]、[BoolDiscPos]、[BoolChainPos]、[bool_disc_to_chain]、[no_bool_chain_to_disc]、[Pos_Forget_not_Full]、[Pos_Forget_not_ReflectsIsos]、[Pos_Forget_not_Monadic] 和 [PosPForget_not_Monadic]；[Monadic] 的两个否定适用于每个附加操作，因为证明是通过守恒性进行的。对比是 [PropSets_Incl_Monadic]。该问题的前提，已注明日期。问题 #469 于 2026-07-23 提出。附加的 Awodey 框中的“（需要从 #641 获取偏序集的类别）”在提交时是准确的，并且自 PR #1076（于 2026-08-13 合并）以来已得到满足。其“诱导的单子计算为恒等式”被交付在 [PropSets]（[MPosP_Id_iso]）上，并且在树的 [Sets] 上，作为特征 [MPos_Id_iff]：一个已陈述的偏差。

 优势。通过 [eq_refl]：[Pos_Forget_factor_obj]，[Pos_Forget_factor_map]，[TPosP_setoid]，[TPosP_fmap]，[TPosP_pequiv]，[MPosP_ret]，[MPosP_join]，[MPosP_to_Id_component]，[Id_to_MPosP_component]，[PosDiscObj_le]，[PosDisc_obj]，[PosDisc_map]，[TPos_fobj]，[TPos_fmap]，[TPos_carrier]，[TPos_equiv]，[MPos_ret] 和 [MPos_join]。最多 ≈：[Pos_Forget_factor]，在 Theory/Functor.v 的 [Functor_Setoid] 中，以及 [MPosP_Id_iso]，[MPos_trunc_iso]，[MPos_Id_iso] 和 [MPos_IEM_Id_iso] 的逆律。拒绝，每个都在 Test/ProbeMonadicity469.v 的完整副本中读取  
 用那个命令未受保护地执行，并用其控制固定在那里：  
 集合方程 fobj [TPos]  S = S (R4) 及其原因，fobj [TPos]  S 与 S (R11) 的 ≈；函子方程  
 TPos = Id [Sets]  (R5)；单元 ret S = id (R6)，在 id 类型上被拒绝，fobj [TPos]  S 与 S 不可转换；在 [PropSets] 上，对一对 (S; P) 的对象方程 (R7) 及其原因，重新计算的 [pequiv] 与 P (R12) 相比，以及变量对象 (R20) 上的相同方程；TPosP = Id [PropSets]  (R8)；两个单子作为 [Monads PropSets] 的相等对象 (R9)；TPos = PropSets_Incl ◯ PropSets_trunc (R16)；  
 (TPos; MPos) 与反射 [PropSets_trunc_Incl] 的单子作为 [Monads Sets] 的相等对象 (R17)；函子方程n
 PropSets_Incl ◯ PosPForget = Pos_Forget (R18)，所以 [Pos_Forget_factor] 
 大约等于，仅此而已；并且 PosDisc = PosDiscP ◯ PropSets_trunc (R19)。R6 是在 [id] 上的类型不匹配，是 R4 的结果，没有“无法统一”的括号说明；R10，即对 [SetsTruncElim] 提供的截断的天真消除，被排序规则拒绝（“消除不正确”）；其他十三个是转换拒绝（“无法统一”）。R8、R9 和 R20 将变量对象与重建对进行比较，而 Coq 的 [sigT] 没有 η：[PropSets] 的一个变量无法与 (projT1 X; projT2 X) (R21) 转换，其中一个 [SetoidObject]，即具有原始投影的记录，可以与其重建记录转换 (C52)。原因。R16 是树自身 [Qed] 证明的不透明性。在树中它被拒绝，而在接下来描述的依赖闭包副本中被接受。该副本的另外三个副本各自再次使一组义务不透明，就像在树中一样，并重建依赖于它的内容：[Compose] 的两个 [Next Obligation] 及其自动解决的一个（Theory/Functor.v）、[Incl] 的一个（Construction/Subcategory.v）以及 [Pos_Forget] 的三个（Instance/Pos.v）。在这三者中 R16 都被拒绝，其树文本（通过 [About] 在每个副本中从 [Compose_obligation_1] 到 [Compose_obligation_3]、[Incl_obligation_1] 和 [Pos_Forget_obligation_1] 检查：仅在其自身组中不透明，并且在树中全部不透明）。因此，每组单独维持了 TPos 与反射函子分离，[PosDisc] 的证明字段复制了 [PropSets_trunc] 的。其他转换拒绝位于该副本中，每个副本都去掉了它的反驳关键词，并在整个探测副本中移除了其宇宙注释（那里的两个文件副本都没有注释），并且在紧随其后的命令副本中将 R16 清空，每个命令内部都拒绝其对应的命令及其树的文本。R4、R5、R7 到 R9、R11、R12、R20 和 R21 是结构性的：双方在数据上不同（截断的 ≈，重新计算的见证），或者有一方卡在 [sigT] 的变量上，该变量没有 η；R21 没有命名树的常量。R17 到 R19 是 超出标准库的结构：它们的数据会转换（R16 和 R17 的单元在那里被接受，并且树中保持 C44、C49），并且 R18 和 R19 背后的证明字段的标准形式（[fmap_respects] 和 [fmap_id]，由那里 [Eval cbv] 读取）包含标准库的不透明 [CMorphisms.trans_co_eq_inv_arrow_morphism_obligation_1]，Instance/Top/Monadicity.v 的 R1 的头记录；对于 R17，连接的函数在那里转换，而作为集合态射的连接被拒绝，[MPos] 的 join properness 字段的标准形式（由 [Eval cbv] 在那里读取）包含那项义务四次，reflection 的 none。副本：[Transparent Obligations] 设置为每个 [Qed] 都转换为 [Defined]，包含义务（由 [About] 检查），在为 Instance/Top/Monadicity.v 制作的依赖闭包副本中，其头部列出了它保留的四个文件的名称，并扩展了此文件添加的十个模块，这十个模块全部都被转换了。该文件以及 Instance/Sets/Propositional/Full.v 的副本是早期版本，其声明中的常量在此未改变，并且其宇宙注释已被移除，因为 [Defined] 证明暴露了其主体的宇宙，而此处的绑定器没有命名。探针的守护块之前的每个控制也在那儿被接受。三十个证明以 [Defined] 结束（按标记计数）；单独关闭每一个
 [Qed]  在两个文件的副本和探针的早期版本中，
 除了四个之外，都会停止某些内容：[MPosP_Id_iso]、[MPos_trunc_iso]、
 [MPos_Id_iso] 和 [MPos_Id_iff]  仅由数据约定 [Defined]，且在此四个中读取时没有向探针添加任何控制。更正（#1349）：按标记计数为二十九，[choice_setoid]  现在由 [:=] 定义 [SquashSetoid]，而 [Defined] 在 Instance/Sets/Propositional/Full.v 中为 [trunc_choice]（该文件的 STRENGTHS）提供支撑。UNIVERSES，读取 [About]；省略了 stdlib 大写字母（compose, ID, Projections, projections, prod_rect, Logic_lemmas.equality 和 eq_ind，其第一个载体是 [rewrite] 位于 [no_bool_chain_to_disc] 中），而 [+] 是为它们准备的。[c] 是载体和同态，[so] 是 [Sets] 和 [PropSets] 的对象，[po] 是 [Pos] 的对象，而 [p0] 到 [p3] 是 [Pos@{po p0 p1 p2 p3 c}] 的四个辅助层次，其对象为 [PosetObject@{c c p0 p1 p2 p3}]；[Pos_Forget@{po so p0 p2 p1 p3 c}]。每个提到 [Sets] 或 [PropSets] 的模块都携带 c < so，而每个出现 [Pos] 的模块都携带 [Pos] 自己模块的 c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0 和 c <= p1。[Set] 仅作为 Set < p2 出现，作为 Set < w 出现在 [pos_PropEquiv@{w c cp p0 p1 p2 p3}] 中（[PropEquivObj] 自身的界，w 是属性的级别，cp 是集合类型的证明级别；调用者取 w := so 且 cp := c），并且作为 Set < so 和 Set < po，其中 c < so 且 c < po 意味着此情况。更高层次：[s] 在 [TPos]、[TPosP] 及通过复合的回读中是 [Compose] 的严格层级（c < s）；[a] 和 [r] 是 [PosDisc_Pos_Forget]（或 [PosDiscP_PosPForget]）及 [PropSets_trunc_Incl] 的 [Adjunction] 记录的自由层级，由 [Build_Adjunction'] 留下；[m1] 和 [m2] 是 [Monads@{so c m1 m2}] 的，其 so 和 c 都在下面；[any_adj_to_Id_trunc] 代表 [s]，即 [Compose] 在 [Adjunction_Induced_Monad] 类型中的严格层级（未命名时在 so 处实例化并测量），以及它的附加的自由层级 [a]；[untr_of_choice]、[choice_of_untr] 和 [choice_of_IEM] 仅绑定 c，在 Rocq 9.1.1 上有一个空块（它们的 [+] 针对 [inhabited] 和 [sum] 在 Coq 8.19.2 和 8.20.1 上传递的全局层级）；单子性否定表示 [Monadic@{m m0 m1 po m3 c so m6}] 对应于恰好 [Monadic] 的内容。他们在那里有自己的区块，因此它们在 [Pos_Forget] 留下的每个级别值上都保持不变，包括承载体 c（未命名，它固定在 [Set] 上，已测量）；[PropSets_Incl_Monadic] 陈述 [Monadic@{m so m1 so m3 c so r}]，其最后一级是证人附加自身的，因此它是 r。没有块有方程。在 Coq 8.19.2 和 8.20.1 上，命名的级别及其块是相同的，[+] 也涵盖 eq.u0、sigT.u0、sigT.u1、inhabited.u0，并且在 [choice_of_IEM] 中涵盖 sum.u0（通过 [About] 来衡量）。修正 (#1349)：[untr_of_choice] 和 [choice_of_untr] 现在是 Instance/Sets/Propositional/Full.v 的内容，具有相同的块（由 [About] 在变更前后保持）；[choice_setoid] 现在按定义为 [SquashSetoid]，[trunc_choice] 和 [MPos_Id_iff] 在 Rocq 9.1.1 上保持它们的内容，[trunc_choice] 中选择了反证（其注释）。在 Coq 8.19.2 和 8.20.1 上，这三者获得了 c <= sum.u1，级别 [SquashSetoid] 的 [squash_rel] 在那里承载，其 [+] 进行了覆盖（通过 [About] 在 master 的叠加与此更改及该树的叠加中，它们一致）。未交付。[MPos] 的 Eilenberg-Moore 范畴未显示等价于 [PropSets]：它将从 [MPos_trunc_iso]、Construction/Reflective/Monadic.v 的 [Reflective_EM_Equivalence] 以及 #468 的 [mh_EM] 推出，并且尚未组成。这两个伴随的比较函子未被回读（Instance/Top/Monadicity.v 对 [PTopCat] 执行此操作）。对于 [MPosP] 本身，仅实例化了恒等 monad 的 Eilenberg-Moore 等价。树内没有语句表明 ∀ A, inhabited A → A 是不可证明的；这是元理论。
*)

(* * ** Posets are propositional, and [Pos_Forget] factors through [PropSets] / * ** 偏序集合是命题性的，并且 [Pos_Forget] 通过 [PropSets] 因式分解 *)

Definition pos_PropEquiv@{w c cp p0 p1 p2 p3 |
  Set < w, Set < p2, c <= w, cp <= w, c <= p0, c <= p1, cp <= p1,
  p2 <= p0, p3 <= p1}
  (P : PosetObject@{c cp p0 p1 p2 p3}) :
  PropEquivObj@{w c cp} (pos_setoid P).
Proof.
  unshelve refine {| pequiv := fun x y => pos_le P x y /\ pos_le P y x |}.
  - intros x y [H1 H2]. exact (pos_antisym P x y H1 H2).
  - intros x y E. split.
    + apply (proj1 (pos_le_respects P x x (reflexivity x) x y E)).
      apply pos_refl.
    + apply (proj1 (pos_le_respects P x y E x x (reflexivity x))).
      apply pos_refl.
Defined.

Definition PosPForget@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} :
  Pos@{po p0 p1 p2 p3 c} ⟶ PropSets@{c so} :=
  PropSets_lift@{po c c so} Pos_Forget@{po so p0 p2 p1 p3 c}
    pos_PropEquiv@{so c c p0 p1 p2 p3}.

Example Pos_Forget_factor_obj@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} (P : Pos@{po p0 p1 p2 p3 c}) :
  fobj[PropSets_Incl@{c so} ◯ PosPForget@{c so po p0 p1 p2 p3}] P
    = fobj[Pos_Forget@{po so p0 p2 p1 p3 c}] P := eq_refl.

Example Pos_Forget_factor_map@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (P Q : Pos@{po p0 p1 p2 p3 c}) (f : P ~{Pos@{po p0 p1 p2 p3 c}}~> Q) :
  fmap[PropSets_Incl@{c so} ◯ PosPForget@{c so po p0 p1 p2 p3}] f
    = fmap[Pos_Forget@{po so p0 p2 p1 p3 c}] f := eq_refl.

Definition Pos_Forget_factor@{c so po p0 p1 p2 p3 s a b |
  c < so, c < s, c < b, po <= a, po <= b, c <= a, so <= a, c < po, Set < p2,
  p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} :
  @equiv _ (@Functor_Setoid@{a b po s so c} Pos@{po p0 p1 p2 p3 c} Sets@{c so})
    (PropSets_Incl@{c so} ◯ PosPForget@{c so po p0 p1 p2 p3})
    Pos_Forget@{po so p0 p2 p1 p3 c} :=
  PropSets_lift_Incl@{po c so s a b} Pos_Forget@{po so p0 p2 p1 p3 c}
    pos_PropEquiv@{so c c p0 p1 p2 p3}.

(* * ** The discrete poset on a propositional setoid / * ** 命题集合上的离散偏序集 *)

Definition PosDiscPObj@{c so p0 p1 p2 p3 |
  c < so, Set < p2, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  (X : PropSets@{c so}) : PosetObject@{c c p0 p1 p2 p3} := {|
  pos_setoid := projT1 X;
  pos_le := @pequiv _ _ (projT2 X);
  pos_le_respects := @pequiv_Proper _ _ (projT2 X);
  pos_refl := fun x => pequiv_from x x (reflexivity x);
  pos_trans := fun x y z H K =>
    pequiv_from x z (transitivity (pequiv_to x y H) (pequiv_to y z K));
  pos_antisym := fun x y H _ => pequiv_to x y H
|}.

Definition PosDiscP_fmap@{c so p0 p1 p2 p3 |
  c < so, Set < p2, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  {X Y : PropSets@{c so}} (f : X ~{PropSets@{c so}}~> Y) :
  MonoHom@{p0 p1 p2 p3 p1 p3 c} (PosDiscPObj@{c so p0 p1 p2 p3} X)
    (PosDiscPObj@{c so p0 p1 p2 p3} Y).
Proof.
  refine (@Build_MonoHom (PosDiscPObj@{c so p0 p1 p2 p3} X)
            (PosDiscPObj@{c so p0 p1 p2 p3} Y) (projT1 f) _).
  intros x y H. simpl in *.
  exact (pequiv_from _ _ (proper_morphism (projT1 f) x y (pequiv_to x y H))).
Defined.

Definition PosDiscP@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} :
  PropSets@{c so} ⟶ Pos@{po p0 p1 p2 p3 c}.
Proof.
  unshelve refine (@Build_Functor PropSets@{c so} Pos@{po p0 p1 p2 p3 c}
                     PosDiscPObj@{c so p0 p1 p2 p3}
                     (fun X Y f => PosDiscP_fmap@{c so p0 p1 p2 p3} f)
                     _ _ _).
  - intros X Y f g E x. exact (E x).
  - intros X x. simpl. reflexivity.
  - intros X Y Z f g x. simpl. reflexivity.
Defined.

Definition posdiscP_from@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  {X : PropSets@{c so}} {P : Pos@{po p0 p1 p2 p3 c}}
  (g : X ~{PropSets@{c so}}~> PosPForget@{c so po p0 p1 p2 p3} P) :
  PosDiscP@{c so po p0 p1 p2 p3} X ~{Pos@{po p0 p1 p2 p3 c}}~> P.
Proof.
  refine (@Build_MonoHom (PosDiscPObj@{c so p0 p1 p2 p3} X) P (projT1 g) _).
  intros x y H. simpl in *.
  apply (proj1 (pos_le_respects P (projT1 g x) (projT1 g x) (reflexivity _)
                  (projT1 g x) (projT1 g y)
                  (proper_morphism (projT1 g) x y (pequiv_to x y H)))).
  apply pos_refl.
Defined.

Definition posdiscP_to@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  {X : PropSets@{c so}} {P : Pos@{po p0 p1 p2 p3 c}}
  (k : PosDiscP@{c so po p0 p1 p2 p3} X ~{Pos@{po p0 p1 p2 p3 c}}~> P) :
  X ~{PropSets@{c so}}~> PosPForget@{c so po p0 p1 p2 p3} P.
Proof. exists (mono_fn k). exact I. Defined.

#[local] Obligation Tactic := idtac.

Program Definition posdiscP_iso@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  (X : PropSets@{c so}) (P : Pos@{po p0 p1 p2 p3 c}) :
  @Isomorphism Sets@{c so}
    {| carrier := @hom Pos@{po p0 p1 p2 p3 c}
                    (PosDiscP@{c so po p0 p1 p2 p3} X) P ;
       is_setoid := @homset Pos@{po p0 p1 p2 p3 c}
                      (PosDiscP@{c so po p0 p1 p2 p3} X) P |}
    {| carrier := @hom PropSets@{c so} X
                    (PosPForget@{c so po p0 p1 p2 p3} P) ;
       is_setoid := @homset PropSets@{c so} X
                      (PosPForget@{c so po p0 p1 p2 p3} P) |} := {|
  to   := {| morphism := fun k => posdiscP_to@{c so po p0 p1 p2 p3} k |};
  from := {| morphism := fun g => posdiscP_from@{c so po p0 p1 p2 p3} g |}
|}.
Next Obligation. intros X P k k' H x; exact (H x). Qed.
Next Obligation. intros X P g g' H x; exact (H x). Qed.
Next Obligation. intros X P g x; reflexivity. Qed.
Next Obligation. intros X P k x; reflexivity. Qed.

Definition PosDiscP_PosPForget@{c so po p0 p1 p2 p3 a |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} :
  @Adjunction@{po c c so c c c c so c a} Pos@{po p0 p1 p2 p3 c} PropSets@{c so}
    PosDiscP@{c so po p0 p1 p2 p3} PosPForget@{c so po p0 p1 p2 p3}.
Proof.
  unshelve refine (@Build_Adjunction'@{po c c so c c a so} _ _
                     PosDiscP@{c so po p0 p1 p2 p3}
                     PosPForget@{c so po p0 p1 p2 p3}
                     posdiscP_iso@{c so po p0 p1 p2 p3} _ _).
  - intros x y z f g t; simpl. reflexivity.
  - intros x y z f g t; simpl. reflexivity.
Defined.

(* * ** Over [PropSets] the induced monad is the identity monad / * ** 在 [PropSets] 上，诱导的 monad 是恒等 monad *)

Definition TPosP@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  PropSets@{c so} ⟶ PropSets@{c so} :=
  PosPForget@{c so po p0 p1 p2 p3} ◯ PosDiscP@{c so po p0 p1 p2 p3}.

Definition MPosP@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  @Monad PropSets@{c so} TPosP@{c so po p0 p1 p2 p3 s} :=
  Adjunction_Induced_Monad PosDiscP_PosPForget@{c so po p0 p1 p2 p3 a}.

Example TPosP_setoid@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (X : PropSets@{c so}) :
  projT1 (fobj[TPosP@{c so po p0 p1 p2 p3 s}] X) = projT1 X := eq_refl.

Example TPosP_fmap@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (X Y : PropSets@{c so}) (f : X ~{PropSets@{c so}}~> Y) :
  projT1 (fmap[TPosP@{c so po p0 p1 p2 p3 s}] f) = projT1 f := eq_refl.

Example TPosP_pequiv@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (X : PropSets@{c so}) (x y : carrier (projT1 X)) :
  @pequiv _ _ (projT2 (fobj[TPosP@{c so po p0 p1 p2 p3 s}] X)) x y
    = (@pequiv _ _ (projT2 X) x y /\ @pequiv _ _ (projT2 X) y x)
  := eq_refl.

Example MPosP_ret@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (X : PropSets@{c so}) :
  projT1 (@ret _ _ MPosP@{c so po p0 p1 p2 p3 s a} X) = id := eq_refl.

Example MPosP_join@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (X : PropSets@{c so}) :
  projT1 (@join _ _ MPosP@{c so po p0 p1 p2 p3 s a} X) = id := eq_refl.

Definition TPosP_to_id@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  TPosP@{c so po p0 p1 p2 p3 s} ⟹ Id[PropSets@{c so}].
Proof.
  unshelve refine (Build_Transform' (F:=TPosP@{c so po p0 p1 p2 p3 s})
                     (G:=Id[PropSets@{c so}]) (fun X => _) _).
  - exists id. exact I.
  - intros X Y f x; simpl. reflexivity.
Defined.

Definition id_to_TPosP@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  Id[PropSets@{c so}] ⟹ TPosP@{c so po p0 p1 p2 p3 s}.
Proof.
  unshelve refine (Build_Transform' (F:=Id[PropSets@{c so}])
                     (G:=TPosP@{c so po p0 p1 p2 p3 s}) (fun X => _) _).
  - exists id. exact I.
  - intros X Y f x; simpl. reflexivity.
Defined.

Definition MPosP_to_Id@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  MonadHom@{so c} MPosP@{c so po p0 p1 p2 p3 s a}
    (IdMonad@{so c} PropSets@{c so}).
Proof.
  unshelve refine {| mh_transform := TPosP_to_id@{c so po p0 p1 p2 p3 s} |};
    intros x z; simpl; reflexivity.
Defined.

Definition Id_to_MPosP@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  MonadHom@{so c} (IdMonad@{so c} PropSets@{c so})
    MPosP@{c so po p0 p1 p2 p3 s a}.
Proof.
  unshelve refine {| mh_transform := id_to_TPosP@{c so po p0 p1 p2 p3 s} |};
    intros x z; simpl; reflexivity.
Defined.

Example MPosP_to_Id_component@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} (X : PropSets@{c so}) :
  projT1 (transform[mh_transform MPosP_to_Id@{c so po p0 p1 p2 p3 s a}] X)
    = id := eq_refl.

Example Id_to_MPosP_component@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} (X : PropSets@{c so}) :
  projT1 (transform[mh_transform Id_to_MPosP@{c so po p0 p1 p2 p3 s a}] X)
    = id := eq_refl.

Definition MPosP_Id_iso@{c so po p0 p1 p2 p3 s a m1 m2 |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1, so <= m1, c <= m1, so <= m2, c <= m2 +} :
  @Isomorphism (Monads@{so c m1 m2} PropSets@{c so})
    (existT _ TPosP@{c so po p0 p1 p2 p3 s} MPosP@{c so po p0 p1 p2 p3 s a})
    (existT _ Id[PropSets@{c so}] (IdMonad@{so c} PropSets@{c so})).
Proof.
  unshelve refine (@Build_Isomorphism (Monads@{so c m1 m2} PropSets@{c so})
    (existT _ TPosP@{c so po p0 p1 p2 p3 s} MPosP@{c so po p0 p1 p2 p3 s a})
    (existT _ Id[PropSets@{c so}] (IdMonad@{so c} PropSets@{c so}))
    MPosP_to_Id@{c so po p0 p1 p2 p3 s a}
    Id_to_MPosP@{c so po p0 p1 p2 p3 s a} _ _);
    intros x z; simpl; reflexivity.
Defined.

(*
 Awodey's “the Eilenberg-Moore category for T = 1_Sets is then just Sets
 itself”, over [PropSets]: Monad/Identity.v's [IdMonad_EM_equivalence]
 at [PropSets]. 

 --------
 Awodey 的“Eilenberg-Moore 类别对于 T = 1_Sets 则只是 Sets 本身”，出自 [PropSets] : Monad/Identity.v 的 [IdMonad_EM_equivalence] 在 [PropSets] 。
*)
Definition PropSets_EM_Id_equivalence@{c so s e | c < so, c < s, so <= e +} :
  EquivalenceOfCategories
    (@EM_Forget@{so c s e} PropSets@{c so} Id[PropSets@{c so}]
       (IdMonad@{so c} PropSets@{c so})) :=
  IdMonad_EM_equivalence@{so c s e} PropSets@{c so}.

(* * ** Over [Sets] the discrete poset truncates / * ** 在 [Sets] 上，离散偏序集被截断 *)

Definition PosDiscObj@{c so p0 p1 p2 p3 |
  c < so, Set < p2, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} (S : Sets@{c so}) :
  PosetObject@{c c p0 p1 p2 p3} :=
  PosDiscPObj@{c so p0 p1 p2 p3} (PropSets_trunc@{c so} S).

Example PosDiscObj_le@{c so p0 p1 p2 p3 |
  c < so, Set < p2, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  (S : Sets@{c so}) (x y : carrier S) :
  pos_le (PosDiscObj@{c so p0 p1 p2 p3} S) x y = inhabited (x ≈ y)
  := eq_refl.

Definition PosDisc@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} :
  Sets@{c so} ⟶ Pos@{po p0 p1 p2 p3 c}.
Proof.
  unshelve refine (@Build_Functor Sets@{c so} Pos@{po p0 p1 p2 p3 c}
                     PosDiscObj@{c so p0 p1 p2 p3}
                     (fun S T f => PosDiscP_fmap@{c so p0 p1 p2 p3}
                                     (fmap[PropSets_trunc@{c so}] f))
                     _ _ _).
  - intros S T f g E x. exact (inhabits (E x)).
  - intros S x. simpl. exact (inhabits (reflexivity x)).
  - intros S T U f g x. simpl. exact (inhabits (reflexivity _)).
Defined.

Example PosDisc_obj@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  (S : Sets@{c so}) :
  fobj[PosDisc@{c so po p0 p1 p2 p3}] S
    = fobj[PosDiscP@{c so po p0 p1 p2 p3}] (fobj[PropSets_trunc@{c so}] S)
  := eq_refl.

Example PosDisc_map@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  (S T : Sets@{c so}) (f : S ~{Sets@{c so}}~> T) :
  fmap[PosDisc@{c so po p0 p1 p2 p3}] f
    = fmap[PosDiscP@{c so po p0 p1 p2 p3}] (fmap[PropSets_trunc@{c so}] f)
  := eq_refl.

Definition posdisc_from@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  {S : Sets@{c so}} {P : Pos@{po p0 p1 p2 p3 c}}
  (g : S ~{Sets@{c so}}~> Pos_Forget@{po so p0 p2 p1 p3 c} P) :
  PosDisc@{c so po p0 p1 p2 p3} S ~{Pos@{po p0 p1 p2 p3 c}}~> P.
Proof.
  unshelve refine (@Build_MonoHom (PosDiscObj@{c so p0 p1 p2 p3} S) P
                     (@Build_SetoidMorphism _ _ _ _ (fun x => g x) _) _).
  - intros x y H. simpl in *.
    apply (@pequiv_elim_inhabited _ _ (pos_PropEquiv@{so c c p0 p1 p2 p3} P)).
    destruct H as [H]. exact (inhabits (proper_morphism g x y H)).
  - intros x y H. simpl in *. destruct H as [H].
    apply (proj1 (pos_le_respects P (g x) (g x) (reflexivity _) (g x) (g y)
                    (proper_morphism g x y H))).
    apply pos_refl.
Defined.

Definition posdisc_to@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  {S : Sets@{c so}} {P : Pos@{po p0 p1 p2 p3 c}}
  (k : PosDisc@{c so po p0 p1 p2 p3} S ~{Pos@{po p0 p1 p2 p3 c}}~> P) :
  S ~{Sets@{c so}}~> Pos_Forget@{po so p0 p2 p1 p3 c} P.
Proof.
  unshelve refine (@Build_SetoidMorphism _ _ _ _ (fun x => mono_fn k x) _).
  intros x y H. exact (proper_morphism (mono_fn k) x y (inhabits H)).
Defined.

Program Definition posdisc_iso@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  (S : Sets@{c so}) (P : Pos@{po p0 p1 p2 p3 c}) :
  @Isomorphism Sets@{c so}
    {| carrier := @hom Pos@{po p0 p1 p2 p3 c}
                    (PosDisc@{c so po p0 p1 p2 p3} S) P ;
       is_setoid := @homset Pos@{po p0 p1 p2 p3 c}
                      (PosDisc@{c so po p0 p1 p2 p3} S) P |}
    {| carrier := @hom Sets@{c so} S (Pos_Forget@{po so p0 p2 p1 p3 c} P) ;
       is_setoid := @homset Sets@{c so} S
                      (Pos_Forget@{po so p0 p2 p1 p3 c} P) |} := {|
  to   := {| morphism := fun k => posdisc_to@{c so po p0 p1 p2 p3} k |};
  from := {| morphism := fun g => posdisc_from@{c so po p0 p1 p2 p3} g |}
|}.
Next Obligation. intros S P k k' H x; exact (H x). Qed.
Next Obligation. intros S P g g' H x; exact (H x). Qed.
Next Obligation. intros S P g x; reflexivity. Qed.
Next Obligation. intros S P k x; reflexivity. Qed.

Definition PosDisc_Pos_Forget@{c so po p0 p1 p2 p3 a |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} :
  @Adjunction@{po c c so c c c c so c a} Pos@{po p0 p1 p2 p3 c} Sets@{c so}
    PosDisc@{c so po p0 p1 p2 p3} Pos_Forget@{po so p0 p2 p1 p3 c}.
Proof.
  unshelve refine (@Build_Adjunction'@{po c c so c c a so} _ _
                     PosDisc@{c so po p0 p1 p2 p3}
                     Pos_Forget@{po so p0 p2 p1 p3 c}
                     posdisc_iso@{c so po p0 p1 p2 p3} _ _).
  - intros x y z f g t; simpl. reflexivity.
  - intros x y z f g t; simpl. reflexivity.
Defined.

(* * ** Over [Sets] the induced monad is the truncation monad / * ** 在 [Sets] 上，归纳 monad 是截断 monad *)

Definition TPos@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  Sets@{c so} ⟶ Sets@{c so} :=
  Pos_Forget@{po so p0 p2 p1 p3 c} ◯ PosDisc@{c so po p0 p1 p2 p3}.

Definition MPos@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  @Monad Sets@{c so} TPos@{c so po p0 p1 p2 p3 s} :=
  Adjunction_Induced_Monad PosDisc_Pos_Forget@{c so po p0 p1 p2 p3 a}.

Example TPos_fobj@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (S : Sets@{c so}) :
  fobj[TPos@{c so po p0 p1 p2 p3 s}] S
    = fobj[PropSets_Incl@{c so} ◯ PropSets_trunc@{c so}] S := eq_refl.

Example TPos_fmap@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (S T : Sets@{c so}) (f : S ~{Sets@{c so}}~> T) :
  fmap[TPos@{c so po p0 p1 p2 p3 s}] f
    = fmap[PropSets_Incl@{c so} ◯ PropSets_trunc@{c so}] f := eq_refl.

Example TPos_carrier@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (S : Sets@{c so}) :
  carrier (fobj[TPos@{c so po p0 p1 p2 p3 s}] S) = carrier S := eq_refl.

Example TPos_equiv@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (S : Sets@{c so}) (x y : carrier S) :
  @equiv _ (is_setoid (fobj[TPos@{c so po p0 p1 p2 p3 s}] S)) x y
    = inhabited (x ≈ y) := eq_refl.

Example MPos_ret@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (S : Sets@{c so}) :
  @Sets.morphism _ _ _ _ (@ret _ _ MPos@{c so po p0 p1 p2 p3 s a} S)
    = (fun x : carrier S => x) := eq_refl.

Example MPos_join@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (S : Sets@{c so}) :
  @Sets.morphism _ _ _ _ (@join _ _ MPos@{c so po p0 p1 p2 p3 s a} S)
    = (fun x : carrier S => x) := eq_refl.

Definition TPos_to_trunc@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  TPos@{c so po p0 p1 p2 p3 s} ⟹ PropSets_Incl@{c so} ◯ PropSets_trunc@{c so}.
Proof.
  unshelve refine (Build_Transform' (F:=TPos@{c so po p0 p1 p2 p3 s})
                     (G:=PropSets_Incl@{c so} ◯ PropSets_trunc@{c so})
                     (fun S => id) _).
  intros S T f x; simpl. exact (inhabits (reflexivity _)).
Defined.

Definition trunc_to_TPos@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  PropSets_Incl@{c so} ◯ PropSets_trunc@{c so} ⟹ TPos@{c so po p0 p1 p2 p3 s}.
Proof.
  unshelve refine (Build_Transform'
                     (F:=PropSets_Incl@{c so} ◯ PropSets_trunc@{c so})
                     (G:=TPos@{c so po p0 p1 p2 p3 s}) (fun S => id) _).
  intros S T f x; simpl. exact (inhabits (reflexivity _)).
Defined.

Definition MPos_to_trunc@{c so po p0 p1 p2 p3 s a r |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  MonadHom@{so c} MPos@{c so po p0 p1 p2 p3 s a}
    (Adjunction_Induced_Monad PropSets_trunc_Incl@{c so r}).
Proof.
  unshelve refine {| mh_transform := TPos_to_trunc@{c so po p0 p1 p2 p3 s} |};
    intros x z; simpl; exact (inhabits (reflexivity _)).
Defined.

Definition trunc_to_MPos@{c so po p0 p1 p2 p3 s a r |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  MonadHom@{so c} (Adjunction_Induced_Monad PropSets_trunc_Incl@{c so r})
    MPos@{c so po p0 p1 p2 p3 s a}.
Proof.
  unshelve refine {| mh_transform := trunc_to_TPos@{c so po p0 p1 p2 p3 s} |};
    intros x z; simpl; exact (inhabits (reflexivity _)).
Defined.

Definition MPos_trunc_iso@{c so po p0 p1 p2 p3 s a r m1 m2 |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1, so <= m1, c <= m1, so <= m2, c <= m2 +} :
  @Isomorphism (Monads@{so c m1 m2} Sets@{c so})
    (existT _ TPos@{c so po p0 p1 p2 p3 s} MPos@{c so po p0 p1 p2 p3 s a})
    (existT _ (PropSets_Incl@{c so} ◯ PropSets_trunc@{c so})
       (Adjunction_Induced_Monad PropSets_trunc_Incl@{c so r})).
Proof.
  unshelve refine (@Build_Isomorphism (Monads@{so c m1 m2} Sets@{c so})
    (existT _ TPos@{c so po p0 p1 p2 p3 s} MPos@{c so po p0 p1 p2 p3 s a})
    (existT _ (PropSets_Incl@{c so} ◯ PropSets_trunc@{c so})
       (Adjunction_Induced_Monad PropSets_trunc_Incl@{c so r}))
    MPos_to_trunc@{c so po p0 p1 p2 p3 s a r}
    trunc_to_MPos@{c so po p0 p1 p2 p3 s a r} _ _);
    intros x z; simpl; exact (inhabits (reflexivity _)).
Defined.

(* * ** Over [Sets], when the induced monad is the identity / * ** 关于 [Sets]，当所诱导的幺半群是恒等式时 *)

Definition id_to_TPos@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  Id[Sets@{c so}] ⟹ TPos@{c so po p0 p1 p2 p3 s}.
Proof.
  unshelve refine (Build_Transform' (F:=Id[Sets@{c so}])
                     (G:=TPos@{c so po p0 p1 p2 p3 s}) (fun S => _) _).
  - unshelve refine (@Build_SetoidMorphism _ _ _ _ (fun x => x) _).
    intros x y H. exact (inhabits H).
  - intros S T f x; simpl. exact (inhabits (reflexivity _)).
Defined.

Definition Id_to_MPos@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  MonadHom@{so c} (IdMonad@{so c} Sets@{c so}) MPos@{c so po p0 p1 p2 p3 s a}.
Proof.
  unshelve refine {| mh_transform := id_to_TPos@{c so po p0 p1 p2 p3 s} |};
    intros x z; simpl; exact (inhabits (reflexivity _)).
Defined.

Definition SetsTruncElim@{c so | c < so +} : Type@{so} :=
  ∀ (S : Sets@{c so}) (x y : carrier S), inhabited (x ≈ y) → x ≈ y.

Lemma MPos_to_Id_trunc@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (θ : MonadHom@{so c} MPos@{c so po p0 p1 p2 p3 s a}
         (IdMonad@{so c} Sets@{c so})) : SetsTruncElim@{c so}.
Proof.
  intros S x y H.
  pose proof (@mh_ret _ _ _ _ _ θ S x) as Hx. simpl in Hx.
  pose proof (@mh_ret _ _ _ _ _ θ S y) as Hy. simpl in Hy.
  refine (transitivity (symmetry Hx) (transitivity _ Hy)).
  exact (@proper_morphism _ _ _ _ (transform[mh_transform θ] S) x y H).
Qed.

Definition TPos_to_id@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (Htrunc : SetsTruncElim@{c so}) :
  TPos@{c so po p0 p1 p2 p3 s} ⟹ Id[Sets@{c so}].
Proof.
  unshelve refine (Build_Transform' (F:=TPos@{c so po p0 p1 p2 p3 s})
                     (G:=Id[Sets@{c so}]) (fun S => _) _).
  - unshelve refine (@Build_SetoidMorphism _ _ _ _ (fun x => x) _).
    intros x y H. exact (Htrunc S x y H).
  - intros S T f x; simpl. reflexivity.
Defined.

Definition MPos_to_Id@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (Htrunc : SetsTruncElim@{c so}) :
  MonadHom@{so c} MPos@{c so po p0 p1 p2 p3 s a} (IdMonad@{so c} Sets@{c so}).
Proof.
  unshelve refine
    {| mh_transform := TPos_to_id@{c so po p0 p1 p2 p3 s} Htrunc |};
    intros x z; simpl; reflexivity.
Defined.

Definition MPos_Id_iso@{c so po p0 p1 p2 p3 s a m1 m2 |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1, so <= m1, c <= m1, so <= m2, c <= m2 +}
  (Htrunc : SetsTruncElim@{c so}) :
  @Isomorphism (Monads@{so c m1 m2} Sets@{c so})
    (existT _ TPos@{c so po p0 p1 p2 p3 s} MPos@{c so po p0 p1 p2 p3 s a})
    (existT _ Id[Sets@{c so}] (IdMonad@{so c} Sets@{c so})).
Proof.
  unshelve refine (@Build_Isomorphism (Monads@{so c m1 m2} Sets@{c so})
    (existT _ TPos@{c so po p0 p1 p2 p3 s} MPos@{c so po p0 p1 p2 p3 s a})
    (existT _ Id[Sets@{c so}] (IdMonad@{so c} Sets@{c so}))
    (MPos_to_Id@{c so po p0 p1 p2 p3 s a} Htrunc)
    Id_to_MPos@{c so po p0 p1 p2 p3 s a} _ _);
    intros x z; simpl; [ reflexivity | exact (inhabits (reflexivity _)) ].
Defined.

(*
 [choice_setoid] is Instance/Sets/Propositional/Full.v's [SquashSetoid]
 since #1349, which unified the two: [bool] with x ≈ y the sum
 (x = y) + A.  The [+] allows the cap c <= sum.u1 that [SquashSetoid]
 carries on Coq 8.19.2 and 8.20.1 (the header's UNIVERSES). 

 --------
 [choice_setoid] 是 Instance/Sets/Propositional/Full.v 的 [SquashSetoid] 自 #1349 起，它统一了两者：[bool] 与 x ≈ y 的和 (x = y) + A。[+] 允许上限 c <= sum.u1，而 [SquashSetoid] 在 Coq 8.19.2 和 8.20.1（头部的 UNIVERSES）上运行。
*)
Definition choice_setoid@{c | +} (A : Type@{c}) : SetoidObject@{c c} :=
  SquashSetoid@{c} A.

(*
 The setoid read here, [choice_setoid A], has [true ≈ false] the sum of
 A with [true = false], refuted by the standard library's
 [true <> false] in an empty match.  [discriminate] would add
 c <= False_rect.u0 to this block and to [MPos_Id_iff]'s (read by
 [About]); the empty match leaves the block as it was on Rocq 9.1.1
 (the header's UNIVERSES for Coq 8.19.2 and 8.20.1). 

 --------
 此处读取的 setoid，[choice_setoid A]，其 [true ≈ false] 为 A 与 [true = false] 的和，被标准库的 [true <> false] 在空匹配中反驳。[discriminate] 将 c <= False_rect.u0 添加到该块以及 [MPos_Id_iff] 的（由 [About] 读取）；空匹配使得该块保持在 Rocq 9.1.1 时的状态（Coq 8.19.2 和 8.20.1 的头部 UNIVERSES）。
*)
Lemma trunc_choice@{c so | c < so +} (Htrunc : SetsTruncElim@{c so})
  (A : Type@{c}) : inhabited A → A.
Proof.
  intros H.
  destruct (Htrunc (choice_setoid@{c} A) true false
              (match H with inhabits a => inhabits (inr a) end)) as [e|a].
  - exact (match Bool.diff_true_false e with end).
  - exact a.
Qed.

Lemma choice_trunc@{c so | c < so +}
  (G : ∀ A : Type@{c}, inhabited A → A) : SetsTruncElim@{c so}.
Proof. intros S x y. exact (G (x ≈ y)). Qed.

Definition MPos_Id_iff@{c so po p0 p1 p2 p3 s a m1 m2 |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1, so <= m1, c <= m1, so <= m2, c <= m2 +} :
  iffT (@Isomorphism (Monads@{so c m1 m2} Sets@{c so})
          (existT _ TPos@{c so po p0 p1 p2 p3 s}
             MPos@{c so po p0 p1 p2 p3 s a})
          (existT _ Id[Sets@{c so}] (IdMonad@{so c} Sets@{c so})))
       (∀ A : Type@{c}, inhabited A → A).
Proof.
  split.
  - intros Hiso.
    exact (trunc_choice@{c so}
             (MPos_to_Id_trunc@{c so po p0 p1 p2 p3 s a} (to Hiso))).
  - intros G.
    exact (MPos_Id_iso@{c so po p0 p1 p2 p3 s a m1 m2}
             (choice_trunc@{c so} G)).
Defined.

(*
 A [PropEquiv] on every object of [Sets] is the principle again, in both
 directions. 

 --------
 [Sets] 的每个对象上的 [PropEquiv] 原则在两个方向上都是有效的。
*)
Definition all_PropEquiv_trunc@{c so | c < so +}
  (P : ∀ X : Sets@{c so}, PropEquivObj@{so c c} X) : SetsTruncElim@{c so} :=
  fun S x y H => @pequiv_elim_inhabited _ _ (P S) x y H.

Definition trunc_all_PropEquiv@{c so | c < so +}
  (T : SetsTruncElim@{c so}) (X : Sets@{c so}) : PropEquivObj@{so c c} X :=
  @PropEquiv_of_relation (carrier X) (is_setoid X)
    (fun x y => inhabited (x ≈ y)) (fun x y H => T X x y H)
    (fun x y H => inhabits H).

(*
 Not only [PosDisc]: a morphism of monads to the identity monad from the
 monad of ANY left adjoint of [Pos_Forget] gives the principle, since the
 poset F S is propositional ([pos_PropEquiv]) and the unit carries x ≈ y
 into it.  “Any” is at this lemma's universe instance: the [Adjunction]
 record's strict slot is so, not a level of its own. 

 --------
 不仅仅是 [PosDisc]：从 [Pos_Forget] 的任意左伴随的幺半群到单位幺半群的幺半群同态给出了原理，因为偏序集 F S 是命题性的（[pos_PropEquiv]），且单元将 x ≈ y 映射到其中。“任意”在这个引理的泛型实例中：[Adjunction] 记录的严格槽就是这样，而不是它自身的层级。
*)
Lemma any_adj_to_Id_trunc@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (F : Sets@{c so} ⟶ Pos@{po p0 p1 p2 p3 c})
  (A : @Adjunction@{po c c so c c c c so c a} Pos@{po p0 p1 p2 p3 c}
         Sets@{c so} F Pos_Forget@{po so p0 p2 p1 p3 c})
  (θ : MonadHom@{so c}
         (@Adjunction_Induced_Monad@{po c so c so a s} _ _ _ _ A)
         (IdMonad@{so c} Sets@{c so})) :
  SetsTruncElim@{c so}.
Proof.
  intros S x y H.
  pose proof (@mh_ret _ _ _ _ _ θ S x) as Hx. simpl in Hx.
  pose proof (@mh_ret _ _ _ _ _ θ S y) as Hy. simpl in Hy.
  refine (transitivity (symmetry Hx) (transitivity _ Hy)).
  apply (@proper_morphism _ _ _ _ (transform[mh_transform θ] S)).
  apply (@pequiv_elim_inhabited _ _
           (pos_PropEquiv@{so c c p0 p1 p2 p3} (F S))).
  destruct H as [H]. constructor.
  exact (@proper_morphism _ _ _ _
           (@ret _ _ (Adjunction_Induced_Monad A) S) x y H).
Qed.

(*
 The principle under the tree's other names for it, written unfolded so
 that this file needs no further [Require]: the hypothesis of
 [choice_of_untr] is Instance/Sets/Classifier/OneLevel.v's
 [Untruncate@{c}] and that of [choice_of_IEM] its [IEM@{c}], each by
 [eq_refl] (control C53 of Test/ProbeMonadicity469.v).
 Instance/Top/Components.v (#462) already states the same links under
 its own names: its [Untruncate_unsquash] has the statement of
 [choice_of_untr], its [unsquash_Untruncate] is the untruncated form of
 [untr_of_choice], and its [SquashSetoid] is the idea of
 [choice_setoid] below; this file does not require that topology file.
 CORRECTION (#1349): unified on the maintainer's decision.
 [untr_of_choice] and [choice_of_untr] moved, names, binders and terms
 unchanged, to Instance/Sets/Propositional/Full.v, which this file
 requires, and Components.v derives its two constants from them;
 [SquashSetoid] moved there too, and [choice_setoid] is now
 [SquashSetoid] by definition.

 --------
 树下的原理的其他名称，以展开形式书写，因此这个文件不需要进一步的 [Require]：[choice_of_untr] 的假设是 Instance/Sets/Classifier/OneLevel.v 的 [Untruncate@{c}]，[choice_of_IEM] 的假设是它的 [IEM@{c}]，每个由 [eq_refl] 控制（Test/ProbeMonadicity469.v 的控制 C53）。Instance/Top/Components.v (#462) 已经在其自己的名称下声明了相同的链接：其 [Untruncate_unsquash] 有 [choice_of_untr] 的陈述，其 [unsquash_Untruncate] 是 [untr_of_choice] 的未截断形式，并且其 [SquashSetoid] 是下面 [choice_setoid] 的想法；此文件不需要那个拓扑文件。更正 (#1349)：根据维护者的决定统一。[untr_of_choice] 和 [choice_of_untr] 已移动，名称、绑定器和术语保持不变，至 Instance/Sets/Propositional/Full.v，该文件需要它们，而 Components.v 从它们推导出它的两个常量；[SquashSetoid] 也移动到了那里，而 [choice_setoid] 现在根据定义为 [SquashSetoid]。
*)
Definition choice_of_IEM@{c | +} (E : ∀ P : Type@{c}, P + (P → False)) :
  ∀ A : Type@{c}, inhabited A → A :=
  fun A h => match E A with
             | inl a => a
             | inr N => match (match h with inhabits a => N a end) with end
             end.

(*
 Under informative excluded middle the induced monad IS the identity
 monad, up to isomorphism in [Monads Sets]. 

 --------
 在信息排中律下，所诱导的幺半群是单位幺半群，在 [Monads Sets] 中同构时除外。
*)
Definition MPos_IEM_Id_iso@{c so po p0 p1 p2 p3 s a m1 m2 |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1, so <= m1, c <= m1, so <= m2, c <= m2 +}
  (E : ∀ P : Type@{c}, P + (P → False)) :
  @Isomorphism (Monads@{so c m1 m2} Sets@{c so})
    (existT _ TPos@{c so po p0 p1 p2 p3 s} MPos@{c so po p0 p1 p2 p3 s a})
    (existT _ Id[Sets@{c so}] (IdMonad@{so c} Sets@{c so})) :=
  MPos_Id_iso@{c so po p0 p1 p2 p3 s a m1 m2}
    (choice_trunc@{c so} (choice_of_IEM@{c} E)).

(** ** Not monadic / ** 非单子 *)

Lemma bool_le_antisym@{} (x y : bool) :
  bool_le x y → bool_le y x → x = y.
Proof.
  destruct x, y; unfold bool_le; intros H K; try reflexivity.
  - exact (eq_sym (H eq_refl)).
  - exact (K eq_refl).
Qed.

Definition BoolDiscPos@{c p0 p1 p2 p3 |
  Set < p2, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  : PosetObject@{c c p0 p1 p2 p3}.
Proof.
  unshelve refine (@Build_PosetObject bool_setoid_object@{c c} (@eq bool)
                     _ (fun x => eq_refl) (fun x y z H1 H2 => eq_trans H1 H2)
                     (fun x y H _ => H)).
  intros x x' Hx y y' Hy. cbn in Hx, Hy. destruct Hx, Hy.
  exact (conj (fun h => h) (fun h => h)).
Defined.

Definition BoolChainPos@{c p0 p1 p2 p3 |
  Set < p2, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} :
  PosetObject@{c c p0 p1 p2 p3}.
Proof.
  unshelve refine (@Build_PosetObject bool_setoid_object@{c c} bool_le
                     _ (fun x H => H) (fun x y z H K e => K (H e))
                     bool_le_antisym).
  intros x x' Hx y y' Hy. cbn in Hx, Hy. destruct Hx, Hy.
  exact (conj (fun h => h) (fun h => h)).
Defined.

Definition bool_disc_to_chain@{c po p0 p1 p2 p3 |
  c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} :
  BoolDiscPos@{c p0 p1 p2 p3} ~{Pos@{po p0 p1 p2 p3 c}}~>
    BoolChainPos@{c p0 p1 p2 p3}.
Proof.
  refine (@Build_MonoHom BoolDiscPos@{c p0 p1 p2 p3}
            BoolChainPos@{c p0 p1 p2 p3} setoid_morphism_id _).
  intros x y H e. cbn in H. destruct H. exact e.
Defined.

Lemma no_bool_chain_to_disc@{c po p0 p1 p2 p3 |
  c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  (g : BoolChainPos@{c p0 p1 p2 p3} ~{Pos@{po p0 p1 p2 p3 c}}~>
         BoolDiscPos@{c p0 p1 p2 p3}) :
  (∀ b : bool, mono_fn g b = b) → False.
Proof.
  intros Hg.
  assert (H : mono_fn g false = mono_fn g true)
    by (apply (mono_le g); intro e; discriminate e).
  rewrite (Hg false), (Hg true) in H. discriminate H.
Qed.

Lemma Pos_Forget_not_Full@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} :
  Functor.Full Pos_Forget@{po so p0 p2 p1 p3 c} → False.
Proof.
  intros HF.
  apply (no_bool_chain_to_disc@{c po p0 p1 p2 p3}
           (@prefmap _ _ _ HF BoolChainPos@{c p0 p1 p2 p3}
              BoolDiscPos@{c p0 p1 p2 p3} setoid_morphism_id)).
  intro b.
  exact (@fmap_sur _ _ _ HF BoolChainPos@{c p0 p1 p2 p3}
           BoolDiscPos@{c p0 p1 p2 p3} setoid_morphism_id b).
Qed.

Lemma Pos_Forget_not_ReflectsIsos@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} :
  ReflectsIsos Pos_Forget@{po so p0 p2 p1 p3 c} → False.
Proof.
  intros R.
  assert (If : @IsIsomorphism Sets@{c so} _ _
                 (fmap[Pos_Forget@{po so p0 p2 p1 p3 c}]
                    bool_disc_to_chain@{c po p0 p1 p2 p3})).
  { unshelve econstructor; [ exact setoid_morphism_id | intro b; reflexivity
                            | intro b; reflexivity ]. }
  destruct (@reflects_iso _ _ _ R _ _ _ If) as [g Hr Hl].
  apply (no_bool_chain_to_disc@{c po p0 p1 p2 p3} g). intro b. exact (Hr b).
Qed.

Lemma Pos_Forget_not_Monadic@{c so po p0 p1 p2 p3 m m0 m1 m3 m6 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1,
  c < m0, po <= m, po <= m1, c <= m, c <= m1, c <= m3,
  so <= m, so <= m3, m1 <= m, m3 <= m +} :
  Monadic@{m m0 m1 po m3 c so m6} Pos_Forget@{po so p0 p2 p1 p3 c} → False.
Proof.
  intros [F [A E]].
  pose proof (Equivalence_Full E) as HF.
  lazymatch type of E with
  | @EquivalenceOfCategories _ ?EM ?K =>
    assert (If : @IsIsomorphism Sets@{c so} _ _
                   (fmap[EM_Forget _]
                      (fmap[K] bool_disc_to_chain@{c po p0 p1 p2 p3})))
  end.
  { unshelve econstructor; [ exact setoid_morphism_id | intro b; reflexivity
                            | intro b; reflexivity ]. }
  destruct (@reflects_iso _ _ _ (em_forget_reflects_isos _) _ _ _ If)
    as [g Hr Hl].
  apply (no_bool_chain_to_disc@{c po p0 p1 p2 p3}
           (@prefmap _ _ _ HF BoolChainPos@{c p0 p1 p2 p3}
              BoolDiscPos@{c p0 p1 p2 p3} g)).
  intro b. transitivity (t_alg_hom[g] b).
  - exact (@fmap_sur _ _ _ HF BoolChainPos@{c p0 p1 p2 p3}
             BoolDiscPos@{c p0 p1 p2 p3} g b).
  - exact (Hr b).
Qed.

Lemma PosPForget_not_Monadic@{c so po p0 p1 p2 p3 m m0 m1 m3 m6 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1,
  c < m0, po <= m, po <= m1, c <= m, c <= m1, c <= m3,
  so <= m, so <= m3, m1 <= m, m3 <= m +} :
  Monadic@{m m0 m1 po m3 c so m6} PosPForget@{c so po p0 p1 p2 p3} → False.
Proof.
  intros [F [A E]].
  pose proof (Equivalence_Full E) as HF.
  lazymatch type of E with
  | @EquivalenceOfCategories _ ?EM ?K =>
    assert (If : @IsIsomorphism PropSets@{c so} _ _
                   (fmap[EM_Forget _]
                      (fmap[K] bool_disc_to_chain@{c po p0 p1 p2 p3})))
  end.
  { unshelve econstructor;
      [ exists setoid_morphism_id; exact I | intro b; reflexivity
      | intro b; reflexivity ]. }
  destruct (@reflects_iso _ _ _ (em_forget_reflects_isos _) _ _ _ If)
    as [g Hr Hl].
  apply (no_bool_chain_to_disc@{c po p0 p1 p2 p3}
           (@prefmap _ _ _ HF BoolChainPos@{c p0 p1 p2 p3}
              BoolDiscPos@{c p0 p1 p2 p3} g)).
  intro b. transitivity (projT1 (t_alg_hom[g]) b).
  - exact (@fmap_sur _ _ _ HF BoolChainPos@{c p0 p1 p2 p3}
             BoolDiscPos@{c p0 p1 p2 p3} g b).
  - exact (Hr b).
Qed.

Definition PropSets_Incl_Monadic@{c so r m m1 m3 |
  c < so, so <= m1, so <= m3, c <= m1, c <= m3, m1 <= m, m3 <= m +} :
  Monadic@{m so m1 so m3 c so r} PropSets_Incl@{c so} :=
  Reflective_Monadic PropSets_Reflective@{c so r}.
