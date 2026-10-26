(* * * The bimodule tensor-hom adjunction, and its parameter / * * 双模张量-同构配对及其参数 *)

(*
 Book:      Mac Lane, “Categories for the Working Mathematician”, 2nd
 ed., §IV.8 Exercise 3, printed p. 104 (PDF p. 113), ledger
 item `maclane:IV.8:ex3`, issue #401.  Quoted verbatim from
 the rendered scan:

 “3. Let R, S, and T be rings.
 (a) For a bimodule _R E _S, show that − ⊗_R E : Mod_R →
 Mod_S has a right adjoint hom_S(E, −).
 (b) Show that this is an adjunction with parameter
 E ∈ R-Mod-S.
 (c) Describe the composite of this adjunction with a
 similar adjunction Mod_S → Mod_T.”

 Book:      Mac Lane, ibid., §IV.7 Theorem 3, printed pp. 101–102 —
 the right adjoints of a bifunctor's partial functors
 extend uniquely to a bifunctor contravariant in the
 parameter.  That theorem is Adjunction/Parameter.v and is
 CONSUMED here, not restated: part (b) below hands it the
 hypothesis and reads Mac Lane's G off its conclusion.
 Book:      Mac Lane, ibid., §IV.1, printed pp. 79–80 — adjunctions in
 hom-set form, which is the presentation used throughout:
 Theory/Adjunction.v's [Adjunction] record is a natural
 bijection of hom-setoids and its unit and counit are the
 derived ⌊id⌋ and ⌈id⌉.
 Book:      Riehl, “Category Theory in Context”, Dover 2016, §4.4
 Example 4.4.8, printed p. 152 — the tensor over S read as
 a BICLOSED bifunctor _R Mod_S × _S Mod_T → _R Mod_T, with
 a left closure Hom_R and a right closure Hom_T.  READ HER
 PROSE WITH CARE: the sentence “making Hom_R(M,N) into an
 R-T bimodule” is at odds with her own display, which lands
 that hom in _S Mod_T; S-T is what the display says.  The
 general three-ring form is NOT built here (see WHAT IS NOT
 DELIVERED).
 Book:      Riehl, ibid., §4.6 Corollary 4.6.10, printed p. 169 — for
 an R-S bimodule M the functor M ⊗_S − is right exact,
 because it is a left adjoint.  Scoped and deferred below.
 nLab:      https://ncatlab.org/nlab/show/tensor-hom+adjunction
 nLab:      https://ncatlab.org/nlab/show/bimodule
 Wikipedia: https://en.wikipedia.org/wiki/Tensor-hom_adjunction

 HANDEDNESS, WHICH THE PAGE FIXES AND WHICH DECIDES EVERY TYPE BELOW.
 Mod_R is the category of RIGHT R-modules; the bimodule is tensored on
 the RIGHT; N ⊗_R E carries a right S-action through E's right
 S-action; hom_S(E, M) is the set of right-S-module maps E → M, made a
 right R-module through E's LEFT R-action by (f ⊲ r)(e) = f (r · e).
 In this tree a right R-module is an object of
 [ModR R := RMod (Ring_op R)] (Instance/Mod.v), so it IS an
 [RModObject (Ring_op R)] and its homs ARE [RModHom]s.  Do not write
 [ModR (Ring_op R) = RMod R]: [Ring_op] is not strictly involutive.

 WHAT IS DELIVERED IN THIS FILE.

 §A, the engine.  [BalTensor N M], the BALANCED tensor of a right
 X-module N and a left X-module M, as an [AbObject].  It is a new
 inductive in Instance/Ab/Tensor.v's shape — four formers
 ([bs_gen], [bs_zero], [bs_plus], [bs_neg]; no formal scalar) and a
 quotienting relation with that file's eleven constructors plus ONE
 balance rule [be_balance], (n · x) ⊗ m ≈ n ⊗ (x · m).  The rule is
 statable with no transport because
 [carrier (rig_setoid (ring_rig (Ring_op X)))] is
 [carrier (rig_setoid (ring_rig X))] on the nose, recorded as
 [bal_scalars_agree] at [eq_refl].  With it: [BalBiadditive N M A],
 the maps additive in each variable and balanced over X;
 [bal_gen], the universal one; [bal_med], the mediator, a fixpoint,
 so [bal_med_gen] is [eq_refl]; [bal_hom_ext], agreement on
 generators; [bal_med_unique]; and [bal_gen_zero_l]/[bal_gen_zero_r].
 This layer is generic — it mentions no bimodule — and both
 handednesses of Exercise 3 are meant to instantiate it.

 §B, Mac Lane part (a).  [RTensor E N : RModObject (Ring_op S)],
 whose carrier is [BalTensor N (bm_left E)] and whose right S-action
 is the mediator of (n, e) ↦ n ⊗ (e ⊲ s); [TensorWith E : ModR R ⟶
 ModR S]; [HomSObj E M : RModObject (Ring_op R)], the group of
 ModR S-maps E → M with the translated right R-action; [HomS E :
 ModR S ⟶ ModR R]; the two transposes [bth_to]/[bth_from]; the
 hom-setoid isomorphism [bth_adj]; and
 **[bimodule_tensor_hom_adjunction E : TensorWith E ⊣ HomS E]**,
 built through Theory/Adjunction.v's [Build_Adjunction'].

 §C, the parameter.  [BimodHom E E'], a map of the left R-modules
 commuting with the right S-action (one field of its own, the rest
 inherited through the [bh_hom] coercion); its hom-setoid, identity
 and composition; **[BimodCat R S : Category]**; [BimodTensorMap]
 and **[BimodTensor : ModR R ∏ BimodCat R S ⟶ ModR S]**;
 [bt_partial_adj E : Partial_l BimodTensor E ⊣ HomS E]; and
 **[bimodule_parametrized_adjunction :
 ParametrizedAdjunction BimodTensor]**, an inhabitant of
 Adjunction/Parameter.v's record with [pa_right := HomS].  From
 it, [bimodule_hom_bifunctor : (BimodCat R S)^op ∏ ModR S ⟶ ModR R]
 is Mac Lane's G, obtained as
 [parametrized_right_adjoint_bifunctor] applied — its arrow action
 in the bimodule variable is that file's [pa_param_mate] and is
 therefore FORCED by Theorem 3.  Nothing here re-proves it.

 §D, Mac Lane part (c).  The LEFT R-action on a balanced tensor
 over S — [lt_bilin_act], [lt_act], [LTensor] — is §A's engine
 instantiated on the other side and is SHARED with §E.  With it,
 [BimodTensorBimod E E1 : Bimodule R T] carries BOTH residual
 actions on ONE group: its [bm_left] is [LTensor E (bm_left E1)]
 and its right T-action is [RTensor E1 (bimodule_right_RMod E)]'s,
 the two agreeing on carriers at [eq_refl] ([btb_carriers_agree]),
 and its [bm_compat] closing on generators by [reflexivity] —
 both sides send e ⊗ e1 to (r · e) ⊗ (e1 ⊲ t).  Then
 **[bimodule_adjunction_composite E E1 :
 (TensorWith E1 ◯ TensorWith E) ⊣ (HomS E ◯ HomS E1)]**, which is
 Adjunction/Compose.v applied and nothing else, with the
 composite's unit and counit read back at [eq_refl] as the DOUBLE
 generator n ⊗ e ⊗ e1 and DOUBLE evaluation f ⊗ e ⊗ e1 ↦ (f e) e1
 ([bac_unit_is_gen], [bac_counit_is_eval]) and Mac Lane's
 whiskered descriptions carried over from that file's two
 corresponding lemmas —
 at ≈ only, their [eq_refl] forms refuted in the probe (N16, N17).
 The comparison is **[tensor_assoc_iso E E1]**, a natural
 isomorphism in [Functor_Setoid] whose per-object leg [ta_iso] is
 built by a mediator of a mediator in each direction; both round
 trips and the coherence square close by [reflexivity] at the
 double generators, through the two extensionality lemmas
 [ta_double_ext] and [ta_double_ext_r].  Transporting the
 composite along it needs a lemma the tree did not have —
 **[adjunction_along_left_iso]**, a functor naturally isomorphic
 to a left adjoint is a left adjoint with the SAME right adjoint —
 and that gives [bimodule_tensor_bimod_adjunction] and hence, by
 Theory/Adjunction.v's uniqueness of right adjoints,
 **[bimodule_hom_composite_iso : HomS E ◯ HomS E1 ≈
 HomS (BimodTensorBimod E E1)]**.  That pair IS Mac Lane's
 “describe the composite”: the composite adjunction is the
 adjunction of the tensor of the two bimodules, up to natural
 isomorphism on both sides and no further.

 §E, the left-module mirror and Riehl's Corollary 4.6.10.
 [LTensorWith E : RMod S ⟶ RMod R] over §D's engine;
 [LHomSObj E M : RModObject S], the group of RMod R-maps
 [bm_left E] → M with the LEFT S-action (s · f)(e) = f (e ⊲ s), the
 mirror of §B's translation; [LHomS E : RMod R ⟶ RMod S]; and
 **[bimodule_left_tensor_hom_adjunction E : LTensorWith E ⊣
 LHomS E]**, again through [Build_Adjunction'], again with unit
 and counit at [eq_refl].  From it and Adjunction/Continuity.v,
 [bimodule_left_tensor_preserves_colimits], its right-module twin
 [bimodule_tensor_preserves_colimits] and the composite's
 [bimodule_tensor_bimod_preserves_colimits], each a [:=] with no
 tactic.

 §F, the second closure and the two-variable adjunction.
 [HomAbBimod N M : Bimodule R S] for a right R-module N and a
 right S-module M — the group of Ab-maps N → M with
 (r · f)(n) = f (n ⊲ r) and (f ⊲ s)(n) = (f n) ⊲ s, whose
 [bm_compat] holds POINTWISE with no law consumed —
 [HomAbFunctor N : ModR S ⟶ BimodCat R S], and
 [hab_partial_adj N : Partial_r BimodTensor N ⊣ HomAbFunctor N],
 which is exactly the mirror hypothesis Adjunction/Parameter.v
 asks for.  [bimodule_mirror_family] packages it and
 **[bimodule_two_variable_adjunction]** is that file's
 [mutually_right_adjoint] applied, an inhabitant of
 Adjunction/Right.v's own [AdjointOnTheRight]; the third leg
 with both hom-setoids written out is [bimodule_third_leg], a map
 of bimodules E → hom_Ab(N, M) being the same thing as a map of
 right R-modules N → hom_S(E, M).  With §C's [pa_adj] that is all
 three legs of Riehl's Definition 4.4.7 for [BimodTensor].

 §G, a concrete witness.  Everything instantiates at
 Instance/Mod.v's [Int_Bimodule] with no new algebra, and
 COMPUTES on closed integers: the right action, the unit, the
 counit, both actions of the tensor of two bimodules and both legs
 of the associativity comparison are [eq_refl] readbacks, and
 [int_tensor_separates] proves two generators distinct by mapping
 OUT through multiplication — no induction over the quotienting
 relation could produce a negative.  The stdlib identifier [Z] is
 named in no statement (six statements carry [%Z] numerals
 only): the binders go through the ring's own carrier and the
 arithmetic through its own rig laws.

 WHAT THEOREM 3 DOES NOT GIVE, AND WHY §C IS ORGANISED AS IT IS.
 [pa_adj] is typed against [Partial_l F p], so F must already be a
 bifunctor before the hypothesis can even be stated.  Functoriality of
 the tensor in the BIMODULE argument is therefore a PREREQUISITE of
 Mac Lane's Theorem 3, not an output of it; what the theorem supplies
 free is the arrow action of the RIGHT adjoint, [pa_right] being a
 bare function of objects.  [BimodTensorMap] and [bt_map_bal] pay that
 prerequisite, in the bimodule variable and in the module variable at
 once.

 THE ADJUNCTION IS BETWEEN TWO DIFFERENT MODULE CATEGORIES, AND THE
 TWO RINGS ARE UNRELATED.  The whole of §B sits under
 [Context {R S : RingObject}] with no homomorphism between them and no
 relation assumed; [TensorWith E] runs [ModR R ⟶ ModR S] and [HomS E]
 runs back.  At R = S nothing degenerates and nothing is claimed.

 NO COMMUTATIVITY, NO CENTRALITY, AND THAT IS A MEASUREMENT.  Below
 this header the tokens [Rcomm] and [rig_mul_comm] occur nowhere at
 all, and the string “commutativ” occurs exactly once, in a comment
 recording that commutativity is not spent.  The [Context]s are
 rings, bimodules and modules and nothing else — §D and §F add a
 third ring and two module variables, §E none, and no hypothesis
 relating any two rings is ever taken.  Contrast
 Instance/Mod/Closed.v, whose [HomMod] takes a commutativity proof
 as an EXPLICIT ARGUMENT at the signature and so cannot host
 hom_S(E, −) over a non-commutative S; and Instance/Mod/Extension.v,
 whose [CentralImage] hypothesis is spent at eight proof sites (its
 own header names a second and a third) precisely because it
 tensors two LEFT modules and bolts the second action on afterwards.
 Doing the construction bimodule-aware is what removes both.

 THE SPEND LEDGER.  Read as a ledger; each entry is the law the
 obligation actually consumes.

 [bal_med_respects]   ← one case per constructor of the relation,
 each met by the target group's own law; the
 balance case is [bal_balance] of β
 [bal_hom_ext]        ← [cmon_map_zero], [cmon_map_plus] and
 Instance/Ab.v's [ab_map_neg]
 [rt_bilin_act]       balance ← **[bm_compat]**, ONE use, and
 nothing else of the bimodule
 [rt_act_distr_r]     ← [bm_rsmul_distr_r]
 [rt_act_assoc]       ← [bm_rsmul_assoc]      (associativity ONLY)
 [rt_act_one]         ← [bm_rsmul_one]
 [rt_act_distr_l]     ← NOTHING; it is [cmon_map_plus] of the
 mediator, supplied as a field value
 [rt_map_bal]         balance ← [rm_map_smul] of the given map
 [RTensorMap], and [TensorWith]'s three laws ← NOTHING beyond
 [bal_hom_ext]; every generator case closes
 by [reflexivity]
 [hs_act]             [rm_map_smul] ← **[bm_compat]**, the second
 use in the file, then the given map's own
 linearity
 [hs_act_distr_l]     ← NOTHING; it closes by [reflexivity]
 [hs_act_distr_r]     ← [rm_smul_distr_r] of E's left module
 [hs_act_assoc]       ← [rm_smul_assoc]       (associativity ONLY)
 [hs_act_one]         ← [rm_smul_one]
 [HomSMap]'s [rm_map_smul], and [HomS]'s [fmap_id] and [fmap_comp]
 ← NOTHING; all three close by [reflexivity]
 [bth_to_inner]'s [rm_map_smul] ← the given map's own linearity,
 with NO rewriting: n ⊗ (e ⊲ s) IS
 s ·[RTensor E N] (n ⊗ e) on the nose
 [bth_to]'s [rm_map_smul] ← **[be_balance]**, the balance rule read
 as a law: this is why the forward transpose
 is R-linear
 [bth_from_bal]'s balance ← the given map's own R-linearity, again
 with no rewriting, the action on
 hom_S(E, M) being translation
 [bth_adj]'s two round trips ← NOTHING beyond [bal_hom_ext]; the
 first closes by [reflexivity], the second
 through it, so the bijection leaves no
 residue on either side
 [bimodule_tensor_hom_adjunction]'s two naturality clauses ←
 NOTHING; both close by [reflexivity]
 [bt_partial_adj]'s two naturality clauses ← NOTHING likewise
 [bimod_hom_compose]'s [bh_right] ← the two given maps' [bh_right]
 [BimodCat]'s four category laws ← NOTHING; all by [reflexivity]
 [bt_map_bal]'s balance ← [rm_map_smul] of the module map, then
 [be_balance], then [rm_map_smul] of the
 bimodule map
 [BimodTensorMap]'s [rm_map_smul] ← [bh_right] of the bimodule map
 [BimodTensor]'s three laws ← [bal_hom_ext]; the identity and
 composition cases close by [reflexivity]
 [lt_bilin_act]       balance ← **[bm_compat]**, the THIRD use in
 the file, read in the other direction
 ([symmetry])
 [lt_act_distr_r]     ← [rm_smul_distr_r] of E's left module
 [lt_act_assoc]       ← [rm_smul_assoc]       (associativity ONLY)
 [lt_act_one]         ← [rm_smul_one]
 [lt_map_bal]         balance ← [be_balance], then the given map's
 own S-linearity
 [btb_compat]         ← NOTHING; [bal_hom_ext] and one
 [reflexivity] on generators
 [BimodTensorBimod]'s five right-action laws ← [RTensor]'s own,
 each with the two arguments swapped, which
 is the flip [bimodule_right_RMod] performs
 [ta_inner], [ta_binner] balance ← [be_balance] at the OUTER
 tensor, the inner generator being the
 module element it acts on
 [ta_outer], [ta_bouter] balance ← [be_balance] at the INNER one,
 under one [bal_hom_ext]
 [ta_to], [ta_from]'s [rm_map_smul], both round trips and
 [tensor_assoc_iso]'s coherence square ← NOTHING beyond
 [ta_double_ext]; every generator case
 closes by [reflexivity]
 [aali_natural], [adjunction_along_left_iso] ← moved with their
 section to Theory/Adjunction.v (#431), proofs
 unchanged there: the coherence square and
 [iso_to_from]; [A]'s own clauses after one
 [aali_natural] and one [comp_assoc]
 [lhs_act]'s [rm_map_smul] ← **[bm_compat]**, the FOURTH and last
 use in the file
 [lhs_act_assoc]      ← [bm_rsmul_assoc]      (associativity ONLY)
 [lhs_act_one]        ← [bm_rsmul_one]
 [blt_to]'s [rm_map_smul] ← **[be_balance]**, the balance rule read
 as a law, exactly as in §B
 [blt_from_bal]'s balance ← the given map's own S-linearity
 [hab_lact_assoc], [hab_ract_assoc] ← [rm_smul_assoc] of N and of
 M, the reversal absorbed by [Ring_op]
 [hab_compat]         ← NOTHING; both sides are the same term
 [hbt_to_hom]'s [rm_map_smul] ← **[be_balance]** again
 [hbt_from_bal]'s balance ← the bimodule map's own R-linearity
 [hbt_from]'s [rm_map_smul] ← [bh_right] of the bimodule map
 [hab_partial_adj]'s two naturality clauses ← NOTHING; both close
 by [reflexivity], as §B's and §C's do
 [int_mult_bal]       ← [rig_distr_r], [rig_distr_l] and
 [rig_mul_assoc] of ℤ, as a record literal
 with no obligation

 THE UNIT AND THE COUNIT ARE THE EXPECTED ONES, ON THE NOSE.
 [bth_unit_is_gen] states that the unit at N, applied to n and then to
 e, IS the generator n ⊗ e, and [bth_counit_is_eval] that the counit
 sends f ⊗ e to f e.  Both close at [eq_refl], not up to ≈.  So do
 [bth_adj_to_is_bth_to] and [bth_adj_from_is_bth_from], which pin the
 two legs of the class's own [adj] field as the named transposes.
 §D's and §E's do too: the composite's unit and counit are the
 DOUBLE generator and DOUBLE evaluation at [eq_refl], the left
 mirror's are the generator and evaluation at [eq_refl], and both
 legs of the associativity comparison return the other bracketing of
 a double generator at [eq_refl].  EVERY [Example] in the file closes
 at [eq_refl]; nowhere is a strict reading sought and settled for ≈.
 Where a strict reading is REFUTED rather than settled for is part
 (c)'s two whole-record identifications — [TensorWith E1 ◯ TensorWith
 E] against [TensorWith (BimodTensorBimod E E1)] and the two hom
 composites — which are different [Functor] records; they are pinned
 as the probe's N10 and N11, and what holds in their place is the
 natural isomorphism, which is what Mac Lane's “describe” asks for.

 AN Ab-ENRICHMENT THAT WAS ONE NEGATION AWAY.
 Instance/Mod/Coextension.v records that the tree has no
 [AbEnriched (RMod R)] and only Instance/Mod.v's [Preadditive];
 a whole-tree search for the string “AbEnriched (RMod” returns that
 one line of prose and nothing else.  [RMod_AbEnriched] supplies it
 here in thirteen lines, over [rmod_hom_negate] (the obvious name
 [rmod_hom_neg] is taken by Instance/FdVect/DoubleDual.v, a
 collision Instance/Mod/Closed.v also records and works around).
 The payoff is that hom_S(E, M)'s underlying group is
 Adjunction/Additive.v's [hom_ab] read at it, so its carrier,
 addition and zero are [RMod_Preadditive]'s own — pinned by
 [hs_group_carrier], [hs_group_plus] and [hs_group_zero] at
 [eq_refl].  It is a plain [Definition], not an [Instance]: this is a
 reading of a hom-setoid, not something resolution should search for.
 Requiring Adjunction/Additive.v costs ONE module on top of what this
 file needs anyway (measured by dropping the [Require] and rerunning
 [coqdep]).

 A RECORD-LITERAL TRAP, MET AND WORKED AROUND SEVEN TIMES.  Writing
 [{| rm_ab := …; rm_smul := … |} : RModObject (Ring_op S)] elaborates
 the scalar argument's type against S and infers the record's ring
 parameter to be S rather than [Ring_op S] — the two being
 convertible — and then asks the associativity field for the WRONG
 multiplication order.  Instance/Mod.v records the same trap
 for [bimodule_right_RMod].  Both [RTensor] and [HomSObj] therefore
 name [@Build_RModObject] with its ring argument written out, and so
 do §D's, §E's and §F's — five [@Build_RModObject] literals in all,
 and two [@Build_Bimodule].

 FOUR MORE ELABORATION FINDINGS, ALL MET AND ALL WORKED AROUND.
 (i) [be_gen]'s two arguments do not determine its module
 parameters, so a NESTED [be_gen] — one whose own argument is a term
 built from [bm_left E] where the expected module is
 [bimodule_right_RMod E], or the reverse — must either be applied
 through [refine], so that the conclusion is unified first, or be
 given its parameters explicitly; §D writes [@be_gen S EE …] and
 [@be_add_l S EE N …] at every such site, which is stage 1's finding
 about [@be_balance] and [@bs_gen] one level in.
 (ii) [Arguments] declared INSIDE a [Section] do not survive its
 [End]: outside §C the two projections of [BimodHom] have their
 bimodule arguments EXPLICIT again, so §F restores the settings
 before its first use.
 (iii) A [Program Definition] with NO section variables in scope
 leaves its [Proper] obligation as a goal [intros] cannot enter
 (“No product even after head-reduction”), where the same shape
 inside a [Section] can be entered after the section binders; §G's
 [int_mult_bal] is a record literal instead, which is better anyway —
 every field is a rig law applied and it raises no obligation at all.
 (iv) [unit] is Theory/Adjunction.v's, so a witness wanting a
 placeholder type must not write it.

 WHY NOT Instance/Mod/Tensor.v's [TensorMod].  MEASURED, by four
 refutation commands run in a scratch file, each of which fired:
 [TensorMod N (bm_left E)], [@TensorMod R N (bm_left E)],
 [@TensorMod (Ring_op R) N (bm_left E)] and
 [RBilinear N (bm_left E) (bm_left E)] are all rejected, while
 [@TensorMod R (bm_left E) (bm_left E)] is accepted as a control.
 That file's tensor is over ONE ring with the same scalar acting on
 both factors and on the target, so it serves neither handedness of
 Exercise 3.  Worse, and also measured: for [F : Bimodule S R] the
 term [@TensorMod (Ring_op R) N (bimodule_right_RMod F)] IS accepted
 — it is the tensor of two RIGHT R-modules and balances
 (n ⊲ r) ⊗ e against n ⊗ (e ⊲ r), which is not what the page asks
 for.  A reader reaching for [bimodule_right_RMod] to make the types
 fit gets a silently different object.

 THE ISSUE'S “Current state” IS STALE ON EVERY COUNT IT MAKES, and
 the corrections are greps: module categories exist
 (Instance/Mod.v's [RMod] and [ModR]), the [Bimodule] record
 exists with [bimodule_right_RMod] and two witnesses, tensor products
 exist (Instance/Ab/Tensor.v and
 Instance/Mod/Tensor.v), and Adjunction/Parameter.v carries Theorem 3
 with [ParametrizedAdjunction] and
 [parametrized_right_adjoint_bifunctor].  What was genuinely
 absent is narrower and is what this file adds: a search for
 [BimodCat], [BimoduleHom] or [bm_hom] over every `.v` in the tree
 returns ZERO lines outside this file, so there was no category of
 bimodules, no bimodule morphism and no setoid on them; and no tensor
 anywhere pairs a right module with a bimodule.

 MODULE PATH.  The issue suggests Instance/Module/Bimodule.v.  That
 directory does not exist (checked), every module file in the tree
 lives under Instance/Mod/, and the file is registered in _CoqProject
 after Instance/Mod/Coextension.v.  The deviation is deliberate.

 UNIVERSES, MEASURED OFF BOTH BINDER AND BLOCK, AND THE ISOLATING
 EXPERIMENT STAGE 1 DEFERRED HAS NOW BEEN RUN — IT REFUTES THAT
 STAGE'S CONJECTURE.  Read the two halves apart, because the block
 alone gives the wrong answer for the equation-free constants and the
 right one for the rest.  Carrying NO universe equation at all —
 every entry of the block a strict [<] or a bound [<=] — are
 [BalTensor], [RTensor], [TensorWith], [BimodCat], [BimodTensor],
 [LTensor], [LTensorWith], [BimodTensorBimod], [btb_left],
 [btb_right], [ta_iso], [bimodule_third_leg], [rmod_lmul] and all
 three [*_preserves_colimits].  Carrying equations are [HomSObj]
 (four), [HomS] and [bimodule_tensor_hom_adjunction] (five),
 [LHomSObj] (five), [LHomS] and
 [bimodule_left_tensor_hom_adjunction] (six), [HomAbBimod] (five),
 [tensor_assoc_iso] (two), and the part-(c) composite,
 [bimodule_tensor_bimod_adjunction] and [bimodule_hom_composite_iso]
 (ten); [adjunction_along_left_iso]'s one moved with it to
 Theory/Adjunction.v (#431).  There is no word-bounded [Set] in the
 block or binder of any of the 427 constants (440 before that move);
 the only [Set] tokens in the whole [About] dump are the motive
 sorts of the two eliminators [bsum_rec] and [bs_eq_rec].

 AN EARLIER REVISION of the preceding sentence, and of the arithmetic
 below, was taken before the PR “algebraic carriers are sets”
 (2026-09-17).  Since that PR [bs_eq] is a [Prop] inductive, so [bs_eq_rec]
 CEASES TO EXIST (a [Prop] inductive gets [_ind] and [_sind], not [_rec] or
 [_rect]) and the count of generated eliminators drops.
 Test/ProbeTermModelProp.v carries the refusal that replaces
 [bs_eq_rec].

 RE-MEASURED at the end of that PR, and the arithmetic below is adjusted
 to what was measured rather than left standing:

 - generated eliminators: SIX, not eight
 ([grep -c '^scheme ' Instance/Mod/Bimodule.glob]).  The two that
 went are [bs_eq_rec] and [bs_eq_rect].
 - [Print Module] entries at five-space indent: 403, being 190
 [Definition] + 213 [Parameter] (was 192 + 213 -- the two lost
 eliminators were [Definition]s).
 - total constants: 425, not 427 -- 403 + the 2 [Inductive] and 2
 [Record] heads that wrap onto their own line + 16 constructors +
 2 [Build_*].
 - axioms: one [Print Assumptions] per name over all 403, giving 403
 “Closed under the global context” and zero [Axioms:] blocks.
 - [Qed] and [Defined] tokens OUTSIDE comments: 213 and 5, both
 unchanged (a bare [grep] reads 216 and 8, the difference being
 this header's own mentions of the two words).

 The one figure still standing on the old measurement is the [Set]-token
 claim in the preceding sentence: the whole [About] dump was NOT re-run,
 and only the half of it that names [bs_eq_rec] is known to have changed,
 that eliminator no longer existing.

 Stage 1 conjectured that the four on [HomSObj] enter at the
 APPLICATION [hom_ab (RMod_AbEnriched (Ring_op S)) …], and that is
 FALSE.  Measured, one donor at a time: [hom_ab] alone, [AbEnriched]
 alone, [RMod] alone and [RMod_AbEnriched] alone each carry NO
 equation; and the application itself, written at TOP LEVEL with the
 two rings and the bimodule as ordinary parameters, carries none
 either.  Put the SAME body in a [Section] whose [Context] binds the
 bimodule and all four appear.  So the donor is the SECTION VARIABLE:
 a [Context] fixes its universes once, and the elaboration of the
 body then EQUATES where the same term with a parameter merely
 BOUNDS.  The file confirms it against itself — [bimodule_third_leg],
 the only §F constant declared at top level, carries no equation
 while [bimodule_two_variable_adjunction], the same machinery inside
 a [Section], carries one, and [rmod_lmul] (top level) carries none
 where [bal_gen_left] (inside a section) carries two.  Nothing is
 claimed unavoidable: rewriting §B, §E and §F without sections would
 restructure them entirely and was not attempted.  What [hom_ab] and
 [AbEnriched] DO force, in their BINDERS rather than their blocks, is
 a category whose hom and proof universes coincide; [AbEnriched]'s is
 pinned in Test/ProbeBimodule401.v as a formability negative, while
 the [hom_ab] negative there fires at its [AbEnriched] ARGUMENT, so
 [hom_ab]'s own contribution is UNKNOWN, not measured.

 AXIOMS.  427/427 constants report “Closed under the global context”, with
 zero [Axioms:] lines.  The criterion: entries of [Print Module] sit at
 exactly five-space indent, giving 192 [Definition] + 213 [Parameter] — the
 printer's rendering of an opaque constant, a display convention and not an
 axiom — + 2 [Inductive] + 2 [Record] = 409, and the [Inductive] and
 [Record] heads WRAP onto their own line, so a regex anchored to the
 keyword AND the name on one line harvests neither of the four; to those
 add the sixteen inductive constructors and the two [Build_*], which [Print
 Module] lists only inside an [Inductive] body or after a [Record]'s [:=].
 The 409 include the file's [Program] obligations and the eight eliminators
 no source sweep sees.  Every one of the 427 was queried by fully qualified
 name.  (Those four figures are 425/407/190/SIX as re-measured above; the
 sentence is left in its measured-then form with the correction attached.)
 (440, 422, 198 and 220 before #431 moved the thirteen
 AdjunctionAlongIso constants out).  The 213 [Parameter] entries are
 exactly the file's 213 [Qed] tokens, which is a cross-check on the reading
 of that display convention rather than a second measurement.

 DEFINED.  Five [Defined] tokens against 213 [Qed] (six and 220 before
 #431 moved [adjunction_along_left_iso] out), and each was flipped ALONE
 to [Qed] to see which are load-bearing: TWO are —
 [bimodule_tensor_hom_adjunction] and
 [bimodule_left_tensor_hom_adjunction], whose transparency is what the
 [eq_refl] readbacks of the unit, the counit and the transported transpose
 reduce through — and three are not ([bt_partial_adj], [tensor_assoc_iso],
 [hab_partial_adj]), kept [Defined] by the data convention alone.

 NAMES.  All 440 (427 now) were swept whole-word against every `.v`
 in the tree before use; the sweep is clean.  Three collisions were
 avoided by construction: [rmod_hom_neg], taken as above; [HomFrom],
 which Functor/Hom/Limit.v owns and which the brief had suggested
 for the hom functor — hence [HomS] and [HomSObj]; and [unit], which
 Theory/Adjunction.v owns, so §G's witnesses name no [unit] and
 the probe's control uses [nat] where a placeholder is wanted.

 CLOSURE.  93 modules, excluding the file itself, measured with
 [coqdep -sort]; the probe's is 95.  Drop-one marginals, each by
 deleting the [Require] and rerunning [coqdep]: Adjunction/Parameter
 11, Adjunction/Compose 2, Adjunction/Additive 1,
 Adjunction/Continuity 1, Instance/Mod 1, and every other [Require]
 ZERO — including Adjunction/Right and Structure/Limit/Preservation,
 which arrive with Parameter and Continuity respectively.  §D-§F cost
 six modules over stage 1's 87.  Instance/Mod/Extension.v is NOT
 required — it would add twelve more (measured: 94 to 106) through
 the Grothendieck and Displayed stack for nothing this file needs —
 and
 Instance/Mod/Closed.v is not required either.  Its TECHNIQUE (an
 action supplied by the mediator of a biadditive map) is reused; none
 of its code is.

 THE BOUNDARY PROBE.  Test/ProbeBimodule401.v carries 18 refutation
 commands = 1 instrument check + 17 negatives of THREE kinds told
 apart by the error TEXT: six CONVERSION, nine TYPING and two
 FORMABILITY.  Each was stripped ONE AT A TIME into its own scratch
 copy, compiled alone, and its whole error read; guard coverage is
 complete (50 identifiers named inside a refutation command, 40 of
 them also named outside one, the ten others being the command
 keyword, one bound variable, the seven names of the refuted
 declarations and the instrument's absent name); and the rename
 simulation is 5/5, every break landing on a [Check] line of the
 guard block.  The refutation commands live there and not here: this
 file contributes ZERO lines to the [todo] target, the probe 28.

 WHAT IS NOT DELIVERED IN THIS FILE.  The following are declared
 remainder, not claims about the mathematics.

 - Riehl's GENERAL three-ring biclosed form, _R Mod_S × _S Mod_T →
 _R Mod_T with a left closure Hom_R and a right closure Hom_T.
 What §F delivers is the second closure of [BimodTensor] at MAC
 LANE's handedness, which is the honest reading this tree can
 state: a right R-module is not a (ℤ,R)-bimodule here —
 [bm_left] demands [RModObject Int_Ring] where a right R-module
 is [RModObject (Ring_op R)] — so the ℤ-instance route is closed
 off (pinned as the probe's N8 and N9), and the one in-tree
 passage, Instance/Rng/Mod.v's [ZRestrict], is pinned at
 [RingObject@{Set Set Set}].
 - A finite-colimit or right-exactness vocabulary.  A whole-tree
 sweep ([right.?exact] 0 hits, [finitely-cocomplete] 3, [finite
 colimit] 3, all prose in unrelated headers) finds none, and
 the catalogue item that would supply it (#546) is OPEN, so
 Riehl's Corollary 4.6.10 is rendered as preservation of ALL
 colimits — which is STRICTLY STRONGER than right exactness and
 is not the same statement.  Corollary 4.6.9's additivity clause
 is not delivered either.
 - The one-ring tensor-hom parametrized adjunction that
 Adjunction/Parameter.v discloses as its own follow-on.
 It compiles out of tree — twenty-two lines of substance, four
 declarations, re-verified at this commit — over [ModTensor]
 (Instance/Mod/Monoidal.v) and [HomMod]
 (Instance/Mod/Closed.v) with that file's [exp_iso_Mod],
 [cur_natural_V] and [cur_natural_X]; it is NOT shipped here,
 because it is Mac Lane's SECOND example rather than Exercise 3
 and because requiring those two modules would cost this file
 nine more (measured: 94 to 103 modules).
 - Any coherence for the tensor of two bimodules beyond the
 comparison itself: no pentagon, no unit bimodule, no bicategory
 of rings and bimodules, and no naturality of
 [tensor_assoc_iso] in E or E1 — only in the module variable,
 which is what its [Functor_Setoid] statement quantifies over.
 - Any relation between [HomAbBimod] and [HomSObj], between
 [adjunction_along_left_iso] and any other transport, or between
 the two readings of the composite's unit beyond the two
 statements that name them.
 - Limit preservation for the two hom functors.  Only the
 colimit side is read off, and only for the three left adjoints.
 - Any universe claim beyond what is measured above; in
 particular nothing is claimed unavoidable, and the section
 finding is an attribution, not a repair.
 - Nothing is registered as an [Instance] except the two the
 categorical structure needs, [bs_eq_Equivalence] and
 [BimodHom_Setoid], both [#[export]] and both resolvable
 downstream (measured in a consumer); [RMod_AbEnriched] is a plain
 [Definition] and no other construction becomes resolvable. 

 --------
 书籍：Mac Lane，《工作数学家的范畴》，第2版，§IV.8 练习题3，印刷页104（PDF页113），账目编号`maclane:IV.8:ex3`，问题#401。原扫描件逐字引用：

 “3. 设R、S和T为环。
 (a) 对于一个双模_R E _S，证明 − ⊗_R E : Mod_R → Mod_S 有一个右伴随 hom_S(E, −)。
 (b) 证明这是一个参数为 E ∈ R-Mod-S 的伴随关系。
 (c) 描述此伴随关系与一个类似的伴随关系 Mod_S → Mod_T 的复合形式。”书籍：Mac Lane，同上，第IV.7节 定理3，第101–102页印刷版——一个双函子的部分函子的右伴随函子可以唯一地扩展为在该参数下是逆变的双函子。该定理在Adjunction/Parameter.v中，并且在此处已被使用，不再重述：下文的(b)部分将传递假设并从其结论读取Mac Lane的G。书籍：Mac Lane，同上，第IV.1节，第79–80页印刷版——以Hom-Set形式的伴随，这是贯穿全文使用的表示法：Theory/Adjunction.v的[Adjunction]记录是Hom-Setoid的自然双射，其单位和余单位是派生的⌊id⌋与⌈id⌉。书籍：Riehl，《Category Theory in Context》，Dover 2016，第4.4节 示例4.4.8，第页印刷版。152 — 张量作用于 S，可读作一个 BICLOSED 双函子 _R Mod_S × _S Mod_T → _R Mod_T，具有左闭包 Hom_R 和右闭包 Hom_T。仔细阅读她的文字：句子“将 Hom_R(M,N) 变为一个 R-T 双模”与她自己的展示不符，该展示将该 Hom 放在 _S Mod_T 中；展示显示的是 S-T。通用的三环形式此处未建立（见未提供内容）。书籍：Riehl，同上，第 4.6 节，推论 4.6.10，印刷页 169 — 对于一个 R-S 双模 M，函子 M ⊗_S − 是右正的，因为它是一个左伴随。下面有范围和延迟说明。nLab: https://ncatlab.org/nlab/show/tensor-hom+adjunction nLab: https://ncatlab.org/nlab/show/bimodule Wikipedia: https://en.wikipedia.org/wiki/Tensor-hom_adjunction手性，这是本页固定的，并决定下面的每种类型。
 Mod_R 是右 R-模的类别；双模在右侧张量；N ⊗_R E 通过 E 的右侧 S-作用携带一个右侧 S-作用；hom_S(E, M) 是从 E 到 M 的右 S-模映射集合，通过 E 的左 R-作用定义为 (f ⊲ r)(e) = f(r · e) 而成为右 R-模。
 在这棵树中，右 R-模是 [ModR R := RMod (Ring_op R)] (Instance/Mod.v) 的一个对象，所以它是 [RModObject (Ring_op R)] 并且它的 Hom 是 [RModHom]。不要写 [ModR (Ring_op R) = RMod R]：[Ring_op] 并不是严格的自反。

 本文件中提供的内容。§A，引擎。[BalTensor N M]，一个右X-模N和左X-模M的平衡张量，作为[AbObject]。它是Instance/Ab/Tensor.v文件中一种新的归纳形式 — 四个构造器（[bs_gen], [bs_zero], [bs_plus], [bs_neg]；没有形式标量）以及与该文件中的十一构造器加上一个平衡规则[be_balance]的商化关系，(n · x) ⊗ m ≈ n ⊗ (x · m)。该规则可以直接陈述，无需传输，因为[carrier (rig_setoid (ring_rig (Ring_op X)))]在本质上是[carrier (rig_setoid (ring_rig X))]，记录为[bal_scalars_agree]于[eq_refl]。借助它：[BalBiadditive N M A]，各变量上的映射是可加的并且在X上平衡；[bal_gen]，是通用的；[bal_med]，中介，一个不动点，因此[bal_med_gen]是[eq_refl]；[bal_hom_ext]，对生成元的一致性；[bal_med_unique]；以及[bal_gen_zero_l] / [bal_gen_zero_r]。这一层是通用的——它没有提到双模——并且练习3的两种手性都是用来实例化它的。

 §B，Mac Lane 部分(a)。[RTensor E N : RModObject (Ring_op S)]，其载体是[BalTensor N (bm_left E)]，其右S作用是(n, e) ↦ n ⊗ (e ⊲ s)的中介；[TensorWith E : ModR R ⟶ ModR S]；[HomSObj E M : RModObject (Ring_op R)]，ModR S映射E → M组成的群，带有转换后的右R作用；[HomS E : ModR S ⟶ ModR R]；两个转置[bth_to] / [bth_from]；伴随同构[bth_adj]；以及**[bimodule_tensor_hom_adjunction E : TensorWith E ⊣ HomS E]**，通过Theory/Adjunction.v的[Build_Adjunction']构建。§C，参数。[BimodHom E E']，左R-模的映射，与右S作用交换（一个字段是它自身的，其余通过[bh_hom]强制继承）；它的同态集合、恒等和组合；**[BimodCat R S : Category]**；[BimodTensorMap]和**[BimodTensor : ModR R ∏ BimodCat R S ⟶ ModR S]**；[bt_partial_adj E : Partial_l BimodTensor E ⊣ HomS E]；以及**[bimodule_parametrized_adjunction: ParametrizedAdjunction BimodTensor]**，Adjunction/Parameter.v记录中[pa_right := HomS]的一个元素。从它，[bimodule_hom_bifunctor : (BimodCat R S)^op ∏ ModR S ⟶ ModR R]是Mac Lane的G，由[parametrized_right_adjoint_bifunctor]应用获得——其在二模块变量中的箭头作用是该文件的[pa_param_mate]，因此由定理3强制。此处没有重新证明它。§D, Mac Lane 部分 (c)。在 S —  [lt_bilin_act] ,  [lt_act] ,  [LTensor]  上的平衡张量的左 R-作用是 §A 在另一侧实例化的引擎，并且与 §E 共享。借助它，[BimodTensorBimod E E1 : Bimodule R T] 承载 ONE 组上的 BOTH 残余作用：它的 [bm_left] 是 [LTensor E (bm_left E1)] ，它的右 T-作用是 [RTensor E1 (bimodule_right_RMod E)] 的，两者在 [eq_refl] ([btb_carriers_agree]) 上的载体上保持一致，并且它的 [bm_compat] 通过 [reflexivity] 在生成元上闭合——两边都将 e ⊗ e1 映射到 (r · e) ⊗ (e1 ⊲ t)。然后
 **[bimodule_adjunction_composite E E1 :
 (TensorWith E1 ◯ TensorWith E) ⊣ (HomS E ◯ HomS E1)]**，这是
 仅仅应用了 Adjunction/Compose.v，没有其他操作，其
 复合的单位和余单位在 [eq_refl] 处被读取回 DOUBLE
 生成元 n ⊗ e ⊗ e1 和 DOUBLE 求值 f ⊗ e ⊗ e1 ↦ (f e) e1
 ([bac_unit_is_gen], [bac_counit_is_eval])，以及 Mac Lane 的
 鞭状描述从该文件的两个对应引理延续过来——
 大约仅在 ≈ 处，它们的 [eq_refl] 形式在探测中被驳回 (N16, N17).比较是 **[tensor_assoc_iso E E1]**，它是  **[Functor_Setoid]** 中的一个自然同构，其每一对象的分支  **[ta_iso]** 由每个方向上的调解器的调解器构建；通过 [reflexivity] 在双生成元处，圆行程和一致性方形封闭，通过两个延拓引理 [ta_double_ext] 和 [ta_double_ext_r]。从它沿着复合体进行搬运需要一个树没有的引理——**[adjunction_along_left_iso]**，一个函子自然同构于左伴随函子则是具有相同右伴随函子的左伴随函子——并且这给出了 [bimodule_tensor_bimod_adjunction]，因此，根据 Theory/Adjunction.v 中右伴随函子的唯一性，**[bimodule_hom_composite_iso : HomS E ◯ HomS E1 ≈ HomS (BimodTensorBimod E E1)]**。那对是 Mac Lane 的“描述复合”：复合陪伴是两个双模的张量的陪伴，在两边自然同构下如此，仅此而已。

 §E，左模镜像和 Riehl 的推论 4.6.10。[LTensorWith E : RMod S ⟶ RMod R] 在 §D 的引擎上；[LHomSObj E M : RModObject S]，为 RMod R-映射的群组[bm_left E] → M，具有左 S-作用 (s · f)(e) = f (e ⊲ s)，是 §B 的平移镜像；[LHomS E : RMod R ⟶ RMod S]；以及 **[bimodule_left_tensor_hom_adjunction E : LTensorWith E ⊣ LHomS E]**，再次通过 [Build_Adjunction']，再次在 [eq_refl] 上有单位和余单位。从它以及 Adjunction/Continuity.v，[bimodule_left_tensor_preserves_colimits]，它的右模双生 [bimodule_tensor_preserves_colimits] 和复合的 [bimodule_tensor_bimod_preserves_colimits]，每一个都是 [:=] ，没有技巧。§F，第二闭包和双变量伴随。
 对于右 R-模 N 和右 S-模 M，[HomAbBimod N M : Bimodule R S] — N → M 的 Ab-映射群，满足
 (r · f)(n) = f (n ⊲ r) 和 (f ⊲ s)(n) = (f n) ⊲ s，其 [bm_compat] 逐点成立，不使用任何法则 —
 [HomAbFunctor N : ModR S ⟶ BimodCat R S] ，以及
 [hab_partial_adj N : Partial_r BimodTensor N ⊣ HomAbFunctor N] ，
 这正是镜像假设 Adjunction/Parameter.v 所要求的。 [bimodule_mirror_family] 将其封装，
 ** [bimodule_two_variable_adjunction] ** 是该文件的 [mutually_right_adjoint] 应用，是 Adjunction/Right.v 自身 [AdjointOnTheRight] 的一个元素；第三条腿将两个同态集合完整写出为 [bimodule_third_leg]，
 一个 E → hom_Ab(N, M) 的双模映射与 N → hom_S(E, M) 的右 R-模映射是相同的。 使用 §C 的 [pa_adj]，这就是 Riehl 定义 4.4.7 对 [BimodTensor] 的所有三条腿。§G，一个具体的见证。一切都在 Instance/Mod.v 的 [Int_Bimodule] 上实例化，没有新的代数，并且在封闭整数上进行计算：右作用、单位、余单位、两个双模张量的两个作用以及结合性比较的两条腿都是 [eq_refl] 回读，并且 [int_tensor_separates] 通过乘法映射 OUT 证明两个生成元是不同的——对商关系进行归纳无法产生负数。stdlib 标识符 [Z] 在任何语句中都没有命名（六个语句只携带 [%Z] 数字）：绑定器通过环自身的载体，算术则通过其自身的幺半环定律。定理3没有提供的内容，以及为什么§C是这样组织的。
 [pa_adj] 与 [Partial_l F p] 对应，因此在假设可以提出之前，F 必须已经是一个双函子。因此，张量在BIMODULE参数下的函子性是Mac Lane定理3的前提条件，而不是它的结果；定理免费提供的是右伴随的箭头作用，[pa_right] 只是对象的一个函数。[BimodTensorMap] 和 [bt_map_bal] 满足这一前提条件，同时在双模变量和模变量中。这个附加关系存在于两个不同的模范畴之间，并且这两个环是无关的。整个 §B 位于 [Context {R S : RingObject}] 之下，它们之间没有同态，也没有假定任何关系；[TensorWith E] 作用于 [ModR R ⟶ ModR S]，而 [HomS E] 则回作用。在 R = S 时，没有任何退化，也没有任何主张。没有交换性，没有中心性，这就是一个测量。在此标题下，标记 [Rcomm] 和 [rig_mul_comm] 完全没有出现，而字符串 “commutativ” 恰好出现一次，在一个注释中记录了交换性未被使用。[Context] 是环、双模和模，仅此而已——§D 和 §F 添加了第三个环和两个模变量，§E 没有添加任何，且从未假设任何两个环之间存在关系。对比
 Instance/Mod/Closed.v，其 [HomMod] 在签名处以显式参数的形式接受一个交换性证明，因此不能在非交换的 S 上承载 hom_S(E, −)；以及 Instance/Mod/Extension.v，其 [CentralImage] 假设在八个证明位置上被使用（它自己的标题名称分别命名了第二个和第三个），正是因为它对两个左模进行了张量并随后附加了第二个作用。使构造具有双模信息是消除这两者的办法。

 使用记录账本。将其作为账本读取；每一条记录都是该义务实际消耗的定律。[bal_med_respects]    ← 每个关系构造函数对应一个案例，
 每个案例由目标群体自身的法律满足；
 平衡案例是 β 的 [bal_balance]
 [bal_hom_ext]         ←  [cmon_map_zero] 、[cmon_map_plus] 和
 Instance/Ab.v 的 [ab_map_neg]
 [rt_bilin_act]        平衡 ← ** [bm_compat] **，使用一次，且
 双模没有其他使用
 [rt_act_distr_r]      ←  [bm_rsmul_distr_r]
 [rt_act_assoc]        ←  [bm_rsmul_assoc]       （仅结合性）
 [rt_act_one]          ←  [bm_rsmul_one]
 [rt_act_distr_l]      ← 没有；它是调解者的 [cmon_map_plus]，作为字段值提供
 [rt_map_bal]          平衡 ← 给定映射的 [rm_map_smul]
 [RTensorMap] ，以及 [TensorWith] 的三项法律 ← 除 [bal_hom_ext]Z 之外没有其他Z；每个生成器情况由 [reflexivity] 关闭
 [hs_act]               [rm_map_smul]  ← ** [bm_compat] **，文件中的第二次使用，然后是给定映射自身的线性性
 [hs_act_distr_l]      ← 无；它由 [reflexivity] 关闭
 [hs_act_distr_r]      ← E 的左模的 [rm_smul_distr_r]
 [hs_act_assoc]        ← [rm_smul_assoc] （仅结合性）
 [hs_act_one]          ← [rm_smul_one]
 [HomSMap] 的 [rm_map_smul]，以及 [HomS] 的 [fmap_id] 和 [fmap_comp]
 ← 无；三者都由 [reflexivity] 关闭
 [bth_to_inner] 的 [rm_map_smul]  ← 给定映射自身的线性性，
 无需重写：n ⊗ (e ⊲ s) 就是 s · [RTensor E N] (n ⊗ e) 精确相同
 [bth_to] 的 [rm_map_smul]  ← ** [be_balance] **, 平衡规则被读作一条定律：这就是前向换位是 R 线性的原因
 [bth_from_bal] 的平衡 ← 给定映射自身的 R 线性，再次
 不需要重写，在 hom_S(E, M) 上的作用是平移
 [bth_adj] 的两次往返 ← 除了 [bal_hom_ext] 外没有其他；
 第一次通过 [reflexivity] 完成，第二次通过它，
 因此双射两边都没有残留
 [bimodule_tensor_hom_adjunction] 的两个自然性条款 ← 没有；两者通过 [reflexivity] 完成
 [bt_partial_adj] 的两个自然性条款 ← 同样没有
 [bimod_hom_compose] 的 [bh_right] ← 两个给定映射的 [bh_right]
 [BimodCat] 的四条范畴定律← 无；全部由 [reflexivity] 制作
 [bt_map_bal] 的平衡 ← [rm_map_smul] 模块映射，然后
 [be_balance]，然后 [rm_map_smul] 双模块映射的
 [BimodTensorMap] 的 [rm_map_smul] ← [bh_right] 双模块映射的
 [BimodTensor] 的三条定律 ← [bal_hom_ext]；单位元和组合情况由 [reflexivity] 关闭
 [lt_bilin_act]        平衡 ← **[bm_compat]**，在文件中的第三次使用，按另一方向读取
 ([symmetry])
 [lt_act_distr_r]      ← [rm_smul_distr_r] E 的左模块
 [lt_act_assoc]        ← [rm_smul_assoc]（仅结合律）
 [lt_act_one]          ← [rm_smul_one]
 [lt_map_bal]          平衡 ← [be_balance]，然后是给定映射自身的 S 线性
 [btb_compat]          ← 无；  [bal_hom_ext]  和一个
 [reflexivity]  在生成器上
 [BimodTensorBimod] 的五个右作用律 ←  [RTensor] 自身的，
 每个交换了两个参数，这是
 [bimodule_right_RMod] 执行的翻转
 [ta_inner] ，  [ta_binner] 平衡 ← [be_balance] 在外部
 张量上，内部生成器是它作用的
 模块元素
 [ta_outer] ，  [ta_bouter] 平衡 ← [be_balance] 在内部，
 在一个 [bal_hom_ext] 下
 [ta_to] ，  [ta_from] 的 [rm_map_smul] ，包括往返
 以及 [tensor_assoc_iso] 的相干方格 ← 无超过
 [ta_double_ext] 的内容；每个生成器情况
 通过 [reflexivity] 闭合
 [aali_natural] ，[adjunction_along_left_iso] ← 随他们的章节移至 Theory/Adjunction.v (#431)，其证明在此保持不变：相干方格和 [iso_to_from]；[A] 自身条款在一个 [aali_natural] 和一个 [comp_assoc] 之后 [lhs_act] 的 [rm_map_smul] ← **[bm_compat]**，这是文件中的第四次也是最后一次使用 [lhs_act_assoc] ← [bm_rsmul_assoc]（仅结合律） [lhs_act_one] ← [bm_rsmul_one] [blt_to] 的 [rm_map_smul] ← **[be_balance]**，平衡规则作为定律读取，完全如 §B 所示 [blt_from_bal] 的平衡 ← 给定映射自身的 S-线性 [hab_lact_assoc], [hab_ract_assoc] ← [rm_smul_assoc] 的 N 和 M，逆序由 [Ring_op] 吸收 [hab_compat] ← 无；双方是相同的项
 [hbt_to_hom] 的 [rm_map_smul] ← ** [be_balance] ** 再一次
 [hbt_from_bal] 的余额 ← 双模映射自身的 R-线性
 [hbt_from] 的 [rm_map_smul] ← 双模映射的 [bh_right]
 [hab_partial_adj] 的两个自然性条款 ← 无；双方都由 [reflexivity] 关闭，如 §B 和 §C 所示
 [int_mult_bal] ← [rig_distr_r]、[rig_distr_l] 和 [rig_mul_assoc] 在 ℤ 中，作为一个记录字面值，没有义务

 单元和余单元完全符合预期，准确无误。[bth_unit_is_gen] 说明，在 N 点的单元作用于 n 然后作用于 e 时，得到生成元 n ⊗ e，而 [bth_counit_is_eval] 则说明余单元将 f ⊗ e 映射为 f e。两者在 [eq_refl] 闭合，而不是仅仅到 ≈。[bth_adj_to_is_bth_to] 和 [bth_adj_from_is_bth_from] 也是如此，它们将类自身 [adj] 域的两条 leg 固定为命名的转置。§D 和 §E 的情况也是如此：复合体的单元和余单元是在 [eq_refl] 的双重生成元和双重求值，左镜像的是在 [eq_refl] 的生成元和求值，而结合性比较的两条 leg 返回在 [eq_refl] 的双重生成元的另一种括号形式。文件中的每个 [Example] 都在 [eq_refl] 处闭合；没有地方会要求并确定 ≈ 的严格解释。当严格解读被驳斥而不是被解决时，它是第(c)部分的两个完整记录识别——[TensorWith E1 ◯ TensorWith E] 对抗 [TensorWith (BimodTensorBimod E E1)] 和两个同余复合——它们是不同的 [Functor] 记录；它们被固定为探针的 N10 和 N11，其位置上保持的是自然同构，这正是麦克莱恩的“描述”所要求的。一个只差一步否定的Ab-加成。Instance/Mod/Coextension.v记录该树没有[AbEnriched (RMod R)]，且只有Instance/Mod.v的[Preadditive]；对字符串“AbEnriched (RMod”进行全树搜索只返回这一行文本，没有其他结果。[RMod_AbEnriched]在此提供了十三行，超越[rmod_hom_negate]（显而易见的名字[rmod_hom_neg]已被Instance/FdVect/DoubleDual.v占用，Instance/Mod/Closed.v也记录了这个冲突并进行了规避）。回报是，hom_S(E, M)的底层群是通过Adjunction/Additive.v的[hom_ab]读取的，因此其载体、加法和零都是[RMod_Preadditive]自身的——由[hs_group_carrier]、[hs_group_plus]和[hs_group_zero]在[eq_refl]固定。它是一个普通的[Definition]，而不是[Instance]：这是对hom-集合的解读，而不是解析应该搜索的东西。要求 Adjunction/Additive.v 花费比该文件本身所需的额外一个模块（通过删除 [Require] 并重新运行 [coqdep] 进行测量）。

 一个 RECORD-LITERAL 陷阱，遇到并解决了七次。写入 [{| rm_ab := …; rm_smul := … |} : RModObject (Ring_op S)] 展开标量参数的类型以匹配 S，并推断记录的环参数为 S 而不是 [Ring_op S] —— 两者是可互换的 —— 然后向结合性字段请求错误的乘法顺序。Instance/Mod.v 在 [bimodule_right_RMod] 上记录了同样的陷阱。 因此 [RTensor] 和 [HomSObj] 都用写出的环参数命名 [@Build_RModObject]，§D、§E 和 §F 也是如此 —— 总共五个 [@Build_RModObject] 字面量，以及两个 [@Build_Bimodule]。四个额外的阐述发现，全部满足且全部绕过。(i) [be_gen] 的两个参数并不决定它的模块参数，所以一个嵌套的 [be_gen]——其自身参数是由 [bm_left E] 构建的项，其中期望的模块是 [bimodule_right_RMod E]，或者反过来——必须要么通过 [refine] 应用，以便先统一结论，要么显式地给出它的参数；§D 在每个此类位置都写下 [@be_gen S EE …] 和 [@be_add_l S EE N …]，这是一阶段关于 [@be_balance] 和 [@bs_gen] 向里一级的发现。(ii) [Arguments] 在 [Section] 内声明不会在其 [End] 中存活：在 §C 外，[BimodHom] 的两个投影再次具有显式的双模块参数，所以 §F 恢复其第一次使用前的设置。(iii) 一个 [Program Definition] 在作用域内没有节变量时，会将其 [Proper] 义务保留为一个目标 [intros] 不能进入（“即使经过头部约简也没有产物”），而同样的形状在 [Section] 内可以在节绑定之后进入；§G 的 [int_mult_bal] 是一个记录字面值，这反而更好——每个字段都是已应用的刚性定律，并且它不会引起任何义务。(iv) [unit] 来自 Theory/Adjunction.v，因此想要占位类型的证人不能写它。为什么不使用 Instance/Mod/Tensor.v 的 [TensorMod]。通过在一个临时文件中运行的四个反驳命令进行测量，每个命令都触发了：[TensorMod N (bm_left E)]、[@TensorMod R N (bm_left E)]、[@TensorMod (Ring_op R) N (bm_left E)] 和 [RBilinear N (bm_left E) (bm_left E)] 都被拒绝，而 [@TensorMod R (bm_left E) (bm_left E)] 被接受作为对照。该文件的张量是在一个环上，且相同的标量作用于两个因子和目标，因此它不适用于练习 3 的任何一方。更糟糕的是，也被测量到：对于 [F : Bimodule S R]，项 [@TensorMod (Ring_op R) N (bimodule_right_RMod F)] 被接受——它是两个右 R-模的张量，并且平衡 (n ⊲ r) ⊗ e 与 n ⊗ (e ⊲ r)，这不是页面所要求的。读者若想使用 [bimodule_right_RMod] 来使类型匹配，得到的将是一个暗中不同的对象。该问题的“当前状态”在每一方面都是陈旧的，并且修正是通过搜索实现的：模块类别存在（Instance/Mod.v 中的 [RMod] 和 [ModR]），[Bimodule] 记录存在，并有 [bimodule_right_RMod] 和两个见证人，张量积存在（Instance/Ab/Tensor.v 和 Instance/Mod/Tensor.v），Adjunction/Parameter.v 包含定理 3 以及 [ParametrizedAdjunction] 和 [parametrized_right_adjoint_bifunctor]。真正缺失的是更小范围的内容，也是该文件新增的：在树中对每个 `.v` 进行 [BimodCat]、[BimoduleHom] 或 [bm_hom] 的搜索，在该文件之外返回零行，因此不存在双模的类别，也没有双模态射或其上的集合，并且在任何地方的张量积都不会将右模与双模配对。模块路径。问题提示 Instance/Module/Bimodule.v。该目录不存在（已检查），树中的每个模块文件都位于 Instance/Mod/ 下，并且该文件在 Instance/Mod/Coextension.v 之后已在 _CoqProject 中注册。这个偏差是故意的。宇宙，分别从绑定器和区块进行测量，并且延迟的隔离实验阶段1现已运行——它否定了该阶段的猜想。将两半分开读取，因为仅区块会给出无方程常数的错误答案，而对其余部分则给出正确答案。完全不携带宇宙方程——区块的每个条目都是严格的 [<] 或受限的 [<=]——是 [BalTensor]、[RTensor]、[TensorWith]、[BimodCat]、[BimodTensor]、[LTensor]、[LTensorWith]、[BimodTensorBimod]、[btb_left]、[btb_right]、[ta_iso]、[bimodule_third_leg]、[rmod_lmul]，以及所有三个 [*_preserves_colimits]。携带的方程为 [HomSObj]（四），[HomS] 和 [bimodule_tensor_hom_adjunction]（五），[LHomSObj]（五），[LHomS] 和 [bimodule_left_tensor_hom_adjunction]（六），[HomAbBimod]（五），[tensor_assoc_iso]（二），以及部分(c)组合，[bimodule_tensor_bimod_adjunction] 和 [bimodule_hom_composite_iso]（十）；[adjunction_along_left_iso] 的一个随它一起移动到了 Theory/Adjunction.v (#431)。在任何 427 个常数的块或绑定器中（移动前为 440 个），都没有以单词为界的 [Set]；在整个 [About] 转储中，唯一的 [Set] 记号是两个消去器 [bsum_rec] 和 [bs_eq_rec] 的动机类型。前一句及下面算术的一早期修订是在 PR “代数承载器是集合”（2026-09-17）之前进行的。由于该 PR [bs_eq] 是一个 [Prop] 归纳类型，因此 [bs_eq_rec] 停止存在（一个 [Prop] 归纳类型会得到 [_ind] 和 [_sind]，而不是 [_rec] 或 [_rect]），生成的消除器数量减少。Test/ProbeTermModelProp.v 承载了替代 [bs_eq_rec] 的拒绝。

 在该 PR 结束时重新测量，并且下面的算术已经调整为测量值，而不是保持原值：- 生成的消去器：六个，不是八个（[grep -c '^scheme ' Instance/Mod/Bimodule.glob]）。已经去掉的两个是 [bs_eq_rec] 和 [bs_eq_rect]。  
 - [Print Module] 在五格缩进中的条目：403，其中 190 个 [Definition] + 213 个 [Parameter]（原为 192 + 213——丢失的两个消去器是 [Definition]）。  
 - 常量总数：425，不是 427——403 + 另外 2 个 [Inductive] 和 2 个 [Record] 头部各自换行 + 16 个构造函数 + 2 个 [Build_*]。  
 - 公理：每个名字一条 [Print Assumptions]，总共有 403 条，“在全局上下文下封闭”，零个 [Axioms:] 块。  
 - 评论之外的 [Qed] 和 [Defined] 令牌：213 和 5，均未变化（单独的 [grep] 读作 216 和 8，差异在于此标题中对两个词的引用）。在旧测量中仍然存在的一个数字是前一句中提到的 [Set] 令牌声明：整个 [About] 转储没有重新运行，已知只有其中命名为 [bs_eq_rec] 的一半发生了变化，而那个消除器已不存在。第一阶段猜测四个在 [HomSObj] 上的进入 APPLICATION [hom_ab (RMod_AbEnriched (Ring_op S)) …]，但这是错误的。经过测量，每次一个供体：单独的 [hom_ab]、单独的 [AbEnriched]、单独的 [RMod] 以及单独的 [RMod_AbEnriched] 都不携带任何方程；而该应用程序本身，在顶层用两个环和双模作为普通参数书写，也不携带任何方程。将相同的主体放入 [Section]，其 [Context] 绑定双模，四个都出现。因此，供体是 SECTION 变量：一个 [Context] 一次性固定其范畴，然后主体的推导就会把带参数的相同项等式化为只是限定值。该文件对自身进行了确认 — [bimodule_third_leg]，作为唯一在顶层声明的§F常量，没有携带方程，而[bimodule_two_variable_adjunction]，同样的机制在一个[Section]内部，携带了一个方程，[rmod_lmul]（顶层）没有携带任何方程，而[bal_gen_left]（在一个section内部）携带了两个方程。没有声称这是不可避免的：在没有section的情况下重写§B、§E和§F会完全重构它们，而且没有尝试。[hom_ab]和[AbEnriched]在其BINDERS而不是它们的blocks中所强制的，是一个同态和证明宇宙一致的类别；[AbEnriched]在Test/ProbeBimodule401.v中被固定为可形成性为负，而[hom_ab]的负面条件在其[AbEnriched]参数处触发，因此[hom_ab]自身的贡献是未知的，未被测量。公理。427/427 常量报告“在全局上下文下封闭”，且 [Axioms:] 行数为零。标准：[Print Module] 的条目正好缩进五个空格，产生 192 [Definition] + 213 [Parameter] —— 打印机渲染的不透明常量，一种显示约定而非公理 —— + 2 [Inductive] + 2 [Record] = 409，并且 [Inductive] 和 [Record] 头部换行到自己的行上，因此锚定关键字和同一行名称的正则表达式不会收集到这四个；再加上十六个归纳构造函数和两个 [Build_*]，[打印模块] 只在 [Inductive] 本体内或 [Record] 的 [:=] 之后列出它们。这 409 项包括文件的 [Program] 义务以及八个消去器，没有源代码扫面能看到。每一个427项都通过完全限定名进行了查询。（上面重新测量得到的那四个数字是425/407/190/6；该句保持在测量后的形式，并附上了修正。） （在#431将十三个AdjunctionAlongIso常数移出之前为440、422、198和220）。213个[Parameter]条目正好是文件中的213个[Qed]标记，这是对该显示约定读取的交叉检查，而不是第二次测量。已定义。五个 [Defined] 代币对 213 个 [Qed]（在 #431 移动 [adjunction_along_left_iso] 之前为六个和 220 个），每一个都单独翻转为 [Qed]，以查看哪些是承重的：两个是——[bimodule_tensor_hom_adjunction] 和 [bimodule_left_tensor_hom_adjunction]，其透明度是 [eq_refl] 对该单元、对偶单元以及传输转置的读回的结果——三个不是（[bt_partial_adj]、[tensor_assoc_iso]、[hab_partial_adj]），仅由数据约定保留 [Defined]。名称。所有 440 个（现在为 427 个）在使用前都在树中的每个 `.v` 上进行了整字匹配；检查是干净的。通过构造避免了三次冲突：[rmod_hom_neg]，如上所述；[HomFrom]，由 Functor/Hom/Limit.v 拥有，并且简报建议用于同态函子——因此有 [HomS] 和 [HomSObj]；以及 [unit]，由 Theory/Adjunction.v 拥有，所以 §G 的证人没有命名 [unit]，并且探针的控制在需要占位符时使用 [nat]。闭包。共有93个模块，不包括文件本身，通过[coqdep -sort]测量；探针测得为95。删除单个边际，每次通过删除[Require]并重新运行[coqdep]：Adjunction/Parameter 11，Adjunction/Compose 2，Adjunction/Additive 1，Adjunction/Continuity 1，Instance/Mod 1，以及所有其他[Require]为零——包括Adjunction/Right和Structure/Limit/Preservation，它们分别随Parameter和Continuity而来。§D-§F阶段比第一阶段的87增加了六个模块。Instance/Mod/Extension.v不是必须的——它会在Grothendieck和Displayed堆栈中额外增加十二个模块（测量：94到106），这些文件根本不需要——Instance/Mod/Closed.v也不是必须的。它的TECHNIQUE（由双加性映射的调解者提供的操作）被重复使用；其代码未复用。边界探测。Test/ProbeBimodule401.v 包含 18 条反驳命令 = 1 条仪器检查 + 17 条三种类型的否定，通过错误文本区分：六条转换错误，九条类型错误和两条可形成性错误。每条错误都是一次性剥离到单独的临时副本中，单独编译，并读取其完整错误；守护覆盖率是完整的（在反驳命令中命名了 50 个标识符，其中 40 个也在命令之外命名，另外十个是命令关键字、一个绑定变量、七个被反驳的声明名称以及仪器缺失的名称）；重命名模拟为 5/5，每个中断都位于守护块的 [Check] 行上。反驳命令存在于那里而非此处：该文件对 [todo] 目标贡献了零行，而探针贡献了 28 行。此文件中未提供的内容。以下声明的是剩余部分，而不是关于数学的声明。- Riehl 的一般三环双闭形态，_R Mod_S × _S Mod_T → _R Mod_T，具有左闭合 Hom_R 和右闭合 Hom_T。§F 提供的是 MAC LANE 所掌握的 [BimodTensor] 的第二闭合，这是这棵树能够陈述的真实读法：一个右 R-模在这里不是 (ℤ,R)-双模——[bm_left] 需要 [RModObject Int_Ring]，其中一个右 R-模是 [RModObject (Ring_op R)]——因此 ℤ 实例路径被封闭（固定为探针的 N8 和 N9），而树中单一路径，Instance/Rng/Mod.v 的 [ZRestrict]，被固定在 [RingObject@{Set Set Set}]。- 一个有限余极限或右正确性词汇。整棵树的搜索（[right.?exact] 0 次命中，[finitely-cocomplete] 3 次，[有限余极限] 3，所有散文都在无关标题中）没有发现，且可以提供它的目录项（#546）是开放的，因此 Riehl 的推论 4.6.10 被解释为保持所有余极限——这严格地比右完全性更强，并且与该陈述不同。推论 4.6.9 的可加性条款也未实现。- Adjunction/Parameter.v 所揭示的单环张量-Hom 参数化伴随构造作为其自身的后续。它是树外编译的——二十二行实质内容，四个声明，在该提交中重新验证——在 [ModTensor] (Instance/Mod/Monoidal.v) 和 [HomMod] (Instance/Mod/Closed.v) 上以及该文件的 [exp_iso_Mod]、[cur_natural_V] 和 [cur_natural_X]；它**不在这里提供**，因为它是 Mac Lane 的第二个例子，而不是练习 3，并且因为需要这两个模块会使该文件多出九个模块（测量值：从 94 到 103 个模块）。
 - 对于两个双模的张量的任何连贯性，除了比较本身：没有五边形，没有单位双模，没有环与双模的双范畴，也没有 [tensor_assoc_iso] 在 E 或 E1 中的自然性——只有在模块变量中，这正是其 [Functor_Setoid] 陈述所量化的内容。- [HomAbBimod] 与 [HomSObj] 之间是否有任何关系，[adjunction_along_left_iso] 与任何其他传输之间是否有关系，或者复合单元的两次读数之间是否有关系，超出命名它们的两条声明以外。 - 对两个同态函子进行极限保持。只读取余极限的一侧，并且仅适用于三个左伴随。 - 任何超出上述测量的宇宙声明；特别是没有声称是不可避免的，该部分发现是归属，而不是修复。 - 除了范畴结构需要的两个 [Instance] 外，没有其他注册为 [Instance]，分别是 [bs_eq_Equivalence] 和 [BimodHom_Setoid]，二者都是 [#[export]，并且都可以在下游解析（在消费者中测量）；[RMod_AbEnriched] 是一个普通的 [Definition]，且没有其他构造可以解析。
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Adjunction.Parameter.
Require Import Category.Adjunction.Additive.
Require Import Category.Adjunction.Compose.
Require Import Category.Adjunction.Continuity.
Require Import Category.Adjunction.Right.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Structure.AbCategory.
Require Import Category.Theory.Algebra.Rig.
(*
 The integer witness of §G needs the [Z] scope; Theory/Algebra/Rig.v
 takes the same import, this is the spelling the tree uses, and on Rocq
 9.1 it emits the tree-wide “From Coq” deprecation warning, as that
 file does. 

 --------
 §G 的整数证人需要 [Z] 范围；Theory/Algebra/Rig.v 也使用相同的导入，这是该树使用的拼写，并且在 Rocq 9.1 上它会发出树级的“From Coq”弃用警告，就像那个文件一样。
*)
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

Open Scope category_scope.

#[local] Obligation Tactic := idtac.

(* * ** A. The balanced tensor of a right module and a left module / * ** A. 右模和左模的平衡张量 *)

Section BalancedTensor.

Context {X : RingObject}.

(*
 [N] is a RIGHT X-module and [M] a LEFT X-module.  The two scalar
 arguments are of the SAME type: the carrier of the opposite ring's
 additive setoid is the carrier of the ring's, on the nose, and that is
 what lets the balance rule below be stated with no transport. 

 --------
 [N] 是一个右 X-模，而 [M] 是一个左 X-模。两个标量参数类型相同：对立环的加法集合的承载体正好是该环的承载体，这正是使下面的平衡规则可以在无需传输的情况下陈述的原因。
*)
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).

Local Notation XC := (carrier (rig_setoid (ring_rig X))).
Local Notation NC := (carrier (cmon_setoid (rm_ab N))).
Local Notation MC := (carrier (cmon_setoid (rm_ab M))).

Example bal_scalars_agree :
  carrier (rig_setoid (ring_rig (Ring_op X)))
    = carrier (rig_setoid (ring_rig X)) := eq_refl.

(*
 Formal sums over the two carriers: generators, zero, sum, negation.
 There is NO formal scalar former; the result is an abelian group, and
 any residual module structure is bolted on afterwards through the
 universal property. 

 --------
 对两个载体的形式求和：生成元、零、求和、取负。没有形式的标量构造；结果是一个阿贝尔群，并且任何剩余的模结构都是随后通过普遍性质附加上去的。
*)
Inductive bsum : Type :=
  | bs_gen  : NC → MC → bsum
  | bs_zero : bsum
  | bs_plus : bsum → bsum → bsum
  | bs_neg  : bsum → bsum.

(*
 The quotienting relation: Instance/Ab/Tensor.v's eleven constructors
 plus ONE balance rule, (n · x) ⊗ m ≈ n ⊗ (x · m).  Reflexivity is
 derived. 

 --------
 商关系：Instance/Ab/Tensor.v 的十一种构造函数加上一个平衡规则，(n · x) ⊗ m ≈ n ⊗ (x · m)。自反性是推导出来的。
*)
Inductive bs_eq : bsum → bsum → Prop :=
  | be_gen {n n' : NC} {m m' : MC} :
      n ≈ n' → m ≈ m' → bs_eq (bs_gen n m) (bs_gen n' m')
  | be_plus {s s' t t'} :
      bs_eq s s' → bs_eq t t' → bs_eq (bs_plus s t) (bs_plus s' t')
  | be_neg {s s'} : bs_eq s s' → bs_eq (bs_neg s) (bs_neg s')
  | be_assoc (s t u : bsum) :
      bs_eq (bs_plus (bs_plus s t) u) (bs_plus s (bs_plus t u))
  | be_comm (s t : bsum) : bs_eq (bs_plus s t) (bs_plus t s)
  | be_zero_l (s : bsum) : bs_eq (bs_plus bs_zero s) s
  | be_neg_l (s : bsum) : bs_eq (bs_plus (bs_neg s) s) bs_zero
  | be_add_l (n n' : NC) (m : MC) :
      bs_eq (bs_gen (cmon_plus (rm_ab N) n n') m)
            (bs_plus (bs_gen n m) (bs_gen n' m))
  | be_add_r (n : NC) (m m' : MC) :
      bs_eq (bs_gen n (cmon_plus (rm_ab M) m m'))
            (bs_plus (bs_gen n m) (bs_gen n m'))
  | be_balance (x : XC) (n : NC) (m : MC) :
      bs_eq (bs_gen (rm_smul N x n) m) (bs_gen n (rm_smul M x m))
  | be_sym {s t} : bs_eq s t → bs_eq t s
  | be_trans {s t u} : bs_eq s t → bs_eq t u → bs_eq s u.

Lemma bs_refl (s : bsum) : bs_eq s s.
Proof.
  induction s.
  - exact (be_gen (reflexivity _) (reflexivity _)).
  - exact (be_trans (be_sym (be_zero_l bs_zero)) (be_zero_l bs_zero)).
  - exact (be_plus IHs1 IHs2).
  - exact (be_neg IHs).
Qed.

Lemma bs_eq_Equivalence : Equivalence bs_eq.
Proof.
  constructor.
  - exact bs_refl.
  - exact (fun s t => be_sym).
  - exact (fun s t u => be_trans).
Qed.

Definition bs_Setoid : Setoid bsum := {|
  equiv        := bs_eq;
  setoid_equiv := bs_eq_Equivalence
|}.

(*
 The balanced tensor as an abelian group: every group law is a
 constructor of the relation. 

 --------
 作为阿贝尔群的平衡张量：每个群律都是该关系的构造器。
*)
Definition BalTensor : AbObject := {|
  ab_cmon := {|
    cmon_setoid := {| carrier := bsum; is_setoid := bs_Setoid |};
    cmon_zero := bs_zero;
    cmon_plus := bs_plus;
    cmon_plus_respects := fun _ _ Hs _ _ Ht => be_plus Hs Ht;
    cmon_plus_assoc := be_assoc;
    cmon_plus_comm := be_comm;
    cmon_plus_zero_l := be_zero_l;
    (* [bs_eq] IS a [Prop] relation, so it is its own [Prop] mirror. / [bs_eq] 是一个 [Prop] 关系，因此它是它自己的 [Prop] 镜像。 *)
    cmon_prop := @PropEquiv_of_relation _ bs_Setoid bs_eq
                   (fun _ _ h => h) (fun _ _ h => h)
  |};
  ab_neg := bs_neg;
  ab_neg_respects := fun _ _ Hs => be_neg Hs;
  ab_neg_left := be_neg_l
|}.

(* * ** Balanced biadditive maps and the universal property / * ** 平衡双加性映射与泛性质 *)

(*
 A map into an abelian group, additive in each variable and balanced
 over X.  Preservation of zero and negation in each variable follows,
 as always for monoid maps between groups, and is not demanded. 

 --------
 映射到阿贝尔群的映射，在每个变量上都是加法性的，并在 X 上平衡。对零和每个变量的取反的保留是自然的，因为对于群之间的幺半群映射总是如此，并不是要求的。
*)
Record BalBiadditive (A : AbObject) := {
  bal_map : NC → MC → carrier (cmon_setoid A);
  bal_respects : Proper (equiv ==> equiv ==> equiv) bal_map;
  bal_add_l (n n' : NC) (m : MC) :
    bal_map (cmon_plus (rm_ab N) n n') m
      ≈ cmon_plus A (bal_map n m) (bal_map n' m);
  bal_add_r (n : NC) (m m' : MC) :
    bal_map n (cmon_plus (rm_ab M) m m')
      ≈ cmon_plus A (bal_map n m) (bal_map n m');
  bal_balance (x : XC) (n : NC) (m : MC) :
    bal_map (rm_smul N x n) m ≈ bal_map n (rm_smul M x m)
}.

Arguments bal_map {A} _ _ _.
Arguments bal_respects {A} _.
Arguments bal_add_l {A} _ _ _ _.
Arguments bal_add_r {A} _ _ _ _.
Arguments bal_balance {A} _ _ _ _.

(* The universal balanced map: the generator former itself. / 通用平衡地图：发电机本身。 *)
Definition bal_gen : BalBiadditive BalTensor :=
  @Build_BalBiadditive BalTensor bs_gen
    (fun _ _ Hn _ _ Hm => be_gen Hn Hm)
    be_add_l be_add_r be_balance.

(* The mediator: fold a formal sum through the target's operations. It computes on constructors. / 调解者：通过目标的操作折叠一个形式和。它在构造器上进行计算。 *)
Fixpoint bal_med_fun {A : AbObject} (β : BalBiadditive A) (s : bsum) :
  carrier (cmon_setoid A) :=
  match s with
  | bs_gen n m  => bal_map β n m
  | bs_zero     => cmon_zero A
  | bs_plus s t => cmon_plus A (bal_med_fun β s) (bal_med_fun β t)
  | bs_neg s    => ab_neg A (bal_med_fun β s)
  end.

Lemma bal_med_respects {A : AbObject} (β : BalBiadditive A) (s t : bsum) :
  bs_eq s t → bal_med_fun β s ≈ bal_med_fun β t.
Proof.
  intro He.
  (*
 Since the PR “algebraic carriers are sets” (2026-09-17) [bs_eq] is a
 [Prop] inductive and eliminates only into [Prop] goals, while `≈` is
 [Type]-valued.  [pequiv_to] puts a [Prop] goal in front of the
 elimination; each branch returns to `≈` with [pequiv_from].  The twelve
 cases and what discharges each are exactly as before. 

 --------
 自从 PR “代数承载是集合”（2026-09-17）以来，[bs_eq] 是一个 [Prop] 归纳的，并且只消解到 [Prop] 目标，而 `≈` 是 [Type] 值的。[pequiv_to] 在消解前放置一个 [Prop] 目标；每个分支都带着 [pequiv_from] 返回到 `≈`。十二种情况以及每种情况解除的内容完全如以前一样。
*)
  apply pequiv_to.
  induction He as
    [ n n' m m' Hn Hm
    | s s' t t' _ IH1 _ IH2
    | s s' _ IH
    | s t u | s t | s | s
    | n n' m | n m m' | x n m
    | s t _ IH
    | s t u _ IH1 _ IH2 ]; simpl.
  - apply pequiv_from; exact (bal_respects β _ _ Hn _ _ Hm).
  - apply pequiv_from.
    exact (cmon_plus_respects A _ _ (pequiv_to _ _ IH1)
                                _ _ (pequiv_to _ _ IH2)).
  - apply pequiv_from.
    exact (ab_neg_respects A _ _ (pequiv_to _ _ IH)).
  - apply pequiv_from; exact (cmon_plus_assoc A _ _ _).
  - apply pequiv_from; exact (cmon_plus_comm A _ _).
  - apply pequiv_from; exact (cmon_plus_zero_l A _).
  - apply pequiv_from; exact (ab_neg_left A _).
  - apply pequiv_from; exact (bal_add_l β _ _ _).
  - apply pequiv_from; exact (bal_add_r β _ _ _).
  - apply pequiv_from; exact (bal_balance β _ _ _).
  - exact (symmetry IH).
  - exact (transitivity IH1 IH2).
Qed.

Program Definition bal_med {A : AbObject} (β : BalBiadditive A) :
  AbHom BalTensor A := {|
  cmon_map := {| morphism := bal_med_fun β |}
|}.
Next Obligation.
  intros A β s t He; exact (bal_med_respects β s t He).
Qed.
Next Obligation. intros A β; simpl; reflexivity. Qed.
Next Obligation. intros A β s t; simpl; reflexivity. Qed.

Example bal_med_gen {A : AbObject} (β : BalBiadditive A)
  (n : NC) (m : MC) :
  cmon_map (bal_med β) (bs_gen n m) = bal_map β n m := eq_refl.

(* Uniqueness in its consumable form: homomorphisms out of the balanced tensor that agree on generators agree everywhere. The [bs_neg] case is Instance/Ab.v's [ab_map_neg]. / 在其可消耗形式中的唯一性：从平衡张量的同态，如果在生成元上相同，则在任何地方都相同。[bs_neg] 情况是 Instance/Ab.v 的 [ab_map_neg]。 *)
Lemma bal_hom_ext {A : AbObject} (f g : AbHom BalTensor A) :
  (∀ (n : NC) (m : MC),
      cmon_map f (bs_gen n m) ≈ cmon_map g (bs_gen n m)) →
  ∀ s : bsum, cmon_map f s ≈ cmon_map g s.
Proof.
  intros Hgen s; induction s as [n m| |s1 IHs1 s2 IHs2|s IHs].
  - exact (Hgen n m).
  - exact (transitivity (cmon_map_zero f)
             (symmetry (cmon_map_zero g))).
  - refine (transitivity (cmon_map_plus f s1 s2) _).
    refine (transitivity _ (symmetry (cmon_map_plus g s1 s2))).
    exact (cmon_plus_respects A _ _ IHs1 _ _ IHs2).
  - refine (transitivity (ab_map_neg f s) _).
    refine (transitivity _ (symmetry (ab_map_neg g s))).
    exact (ab_neg_respects A _ _ IHs).
Qed.

Lemma bal_med_unique {A : AbObject} (β : BalBiadditive A)
  (f : AbHom BalTensor A) :
  (∀ (n : NC) (m : MC),
      cmon_map f (bs_gen n m) ≈ bal_map β n m) →
  f ≈ bal_med β.
Proof.
  intros Hgen s.
  refine (bal_hom_ext f (bal_med β) _ s).
  intros n m; exact (Hgen n m).
Qed.

(*
 A generator with a zero coordinate is the zero of the tensor.  Both
 halves are needed downstream: the transposes of the adjunction are
 additive because of them. 

 --------
 具有零坐标的生成元是张量的零。下游需要两个部分：挨近的转置是加性的，因为有它们的存在。
*)
Lemma bal_gen_zero_l (m : MC) :
  (bs_gen (cmon_zero (rm_ab N)) m : carrier (cmon_setoid BalTensor))
    ≈ cmon_zero BalTensor.
Proof.
  apply (ab_cancel_l BalTensor (bs_gen (cmon_zero (rm_ab N)) m)).
  exact (be_trans
           (be_trans
              (be_sym (be_add_l (cmon_zero (rm_ab N))
                                (cmon_zero (rm_ab N)) m))
              (be_gen (cmon_plus_zero_l (rm_ab N) (cmon_zero (rm_ab N)))
                      (reflexivity m)))
           (be_sym (cmon_plus_zero_r BalTensor
                      (bs_gen (cmon_zero (rm_ab N)) m)))).
Qed.

Lemma bal_gen_zero_r (n : NC) :
  (bs_gen n (cmon_zero (rm_ab M)) : carrier (cmon_setoid BalTensor))
    ≈ cmon_zero BalTensor.
Proof.
  apply (ab_cancel_l BalTensor (bs_gen n (cmon_zero (rm_ab M)))).
  exact (be_trans
           (be_trans
              (be_sym (be_add_r n (cmon_zero (rm_ab M))
                                  (cmon_zero (rm_ab M))))
              (be_gen (reflexivity n)
                      (cmon_plus_zero_l (rm_ab M) (cmon_zero (rm_ab M)))))
           (be_sym (cmon_plus_zero_r BalTensor
                      (bs_gen n (cmon_zero (rm_ab M)))))).
Qed.

End BalancedTensor.

Arguments bsum {X} N M.
Arguments bs_gen {X N M} n m.
Arguments bs_zero {X N M}.
Arguments bs_plus {X N M} s t.
Arguments bs_neg {X N M} s.
Arguments bs_eq {X N M} s t.
Arguments bs_refl {X N M} s.
Arguments be_gen {X N M n n' m m'} _ _.
Arguments be_plus {X N M s s' t t'} _ _.
Arguments be_neg {X N M s s'} _.
Arguments be_assoc {X N M} s t u.
Arguments be_comm {X N M} s t.
Arguments be_zero_l {X N M} s.
Arguments be_neg_l {X N M} s.
Arguments be_add_l {X N M} n n' m.
Arguments be_add_r {X N M} n m m'.
Arguments be_balance {X N M} x n m.
Arguments be_sym {X N M s t} _.
Arguments be_trans {X N M s t u} _ _.

#[export] Existing Instance bs_eq_Equivalence.
Arguments BalTensor {X} N M.
Arguments BalBiadditive {X} N M A.
Arguments bal_map {X N M A} _ _ _.
Arguments bal_respects {X N M A} _.
Arguments bal_add_l {X N M A} _ _ _ _.
Arguments bal_add_r {X N M A} _ _ _ _.
Arguments bal_balance {X N M A} _ _ _ _.
Arguments bal_gen {X N M}.
Arguments bal_med_fun {X N M A} β s.
Arguments bal_med {X N M A} β.
Arguments bal_med_gen {X N M A} β n m.
Arguments bal_hom_ext {X N M A} f g _ s.
Arguments bal_med_unique {X N M A} β f _.
Arguments bal_gen_zero_l {X} N M m.
Arguments bal_gen_zero_r {X} N M n.

(* * ** B. Mac Lane part (a): − ⊗_R E and hom_S(E, −) / * ** B. 麦克莱恩部分 (a)：− ⊗_R E 和 hom_S(E, −) *)

(* * *** The Ab-enrichment of a module category / * *** 模块范畴的 Ab-增强 *)

(*
 Instance/Mod.v supplies [rmod_hom_add] and [rmod_hom_zero] but no
 negation, and the name [rmod_hom_neg] is taken by
 Instance/FdVect/DoubleDual.v (Instance/Mod/Closed.v records
 the same collision and works around it with a file-local name). 

 --------
 Instance/Mod.v 提供了 [rmod_hom_add] 和 [rmod_hom_zero]，但没有提供取反，并且名称 [rmod_hom_neg] 已被 Instance/FdVect/DoubleDual.v 使用（Instance/Mod/Closed.v 记录了相同的冲突，并通过文件本地名称来解决）。
*)
Program Definition rmod_hom_negate {R : RingObject} {M N : RModObject R}
        (f : RModHom M N) : RModHom M N := {|
  rm_hom := ab_hom_neg (rm_hom f)
|}.
Next Obligation.
  intros R M N f r m; simpl.
  rewrite (rm_map_smul f r m).
  symmetry; apply rm_smul_neg_r.
Qed.

(*
 Instance/Mod/Coextension.v records that the tree has no
 [AbEnriched (RMod R)], only Instance/Mod.v's [Preadditive].  It
 is one negation away, and the hom-group below is Adjunction/
 Additive.v's [hom_ab] read at it, so nothing is rebuilt.  A plain
 [Definition], not an [Instance]: this is a reading of a hom-setoid,
 not something resolution should search for. 

 --------
 Instance/Mod/Coextension.v 记录该树没有 [AbEnriched (RMod R)]，只有 Instance/Mod.v 的 [Preadditive]。它只差一步否定，下面的同构群是 Adjunction/Additive.v 的 [hom_ab] 在它上面读取的，因此没有任何内容被重建。一个普通的 [Definition]，而不是 [Instance]：这是同态集合的读取，而不是求解应该搜索的内容。
*)
Program Definition RMod_AbEnriched (R : RingObject) :
  AbEnriched (RMod R) := {|
  abenriched_preadditive := RMod_Preadditive R;
  abneg := fun M N => @rmod_hom_negate R M N
|}.
Next Obligation.
  intros R M N f g Hfg a; simpl.
  exact (ab_neg_respects N _ _ (Hfg a)).
Qed.
Next Obligation.
  intros R M N f a; simpl.
  exact (ab_neg_right N (cmon_map (rm_hom f) a)).
Qed.

Section BimoduleTensorHom.

Context {R S : RingObject}.
Context (E : Bimodule R S).

Local Notation RC := (carrier (rig_setoid (ring_rig R))).
Local Notation SC := (carrier (rig_setoid (ring_rig S))).
Local Notation EC := (carrier (cmon_setoid (rm_ab (bm_left E)))).
Local Notation EE := (bimodule_right_RMod E).

(* * *** The right S-action on N ⊗_R E / * *** N ⊗_R E 上的右 S-作用 *)

(*
 The action of s is the mediator of (n, e) ↦ n ⊗ (e ⊲ s).  The ONLY
 law of the bimodule the balance clause consumes is [bm_compat]; no
 centrality and no commutativity appears anywhere in this section. 

 --------
 s 的作用是 (n, e) ↦ n ⊗ (e ⊲ s) 的中介。双模的平衡条款消耗的唯一定律是 [bm_compat]；在本节中没有出现中心性和交换性。
*)
Program Definition rt_bilin_act (N : RModObject (Ring_op R)) (s : SC) :
  BalBiadditive N (bm_left E) (BalTensor N (bm_left E)) := {|
  bal_map := fun n e => bs_gen n (bm_rsmul E e s)
|}.
Next Obligation.
  intros N s n n' Hn e e' He.
  exact (be_gen Hn (bm_rsmul_respects E e e' He s s (reflexivity s))).
Qed.
Next Obligation.
  intros N s n n' e; exact (be_add_l n n' (bm_rsmul E e s)).
Qed.
Next Obligation.
  intros N s n e e'.
  exact (be_trans
           (be_gen (reflexivity n) (bm_rsmul_distr_l E e e' s))
           (be_add_r n (bm_rsmul E e s) (bm_rsmul E e' s))).
Qed.
Next Obligation.
  intros N s r n e.
  exact (be_trans
           (be_balance r n (bm_rsmul E e s))
           (be_sym (be_gen (reflexivity n) (bm_compat E r e s)))).
Qed.

Definition rt_smul (N : RModObject (Ring_op R)) (s : SC) :
  AbHom (BalTensor N (bm_left E)) (BalTensor N (bm_left E)) :=
  bal_med (rt_bilin_act N s).

Definition rt_act (N : RModObject (Ring_op R)) (s : SC)
  (x : carrier (cmon_setoid (BalTensor N (bm_left E)))) :
  carrier (cmon_setoid (BalTensor N (bm_left E))) :=
  cmon_map (rt_smul N s) x.

Example rt_act_gen (N : RModObject (Ring_op R)) (s : SC)
  (n : carrier (cmon_setoid (rm_ab N))) (e : EC) :
  rt_act N s (bs_gen n e) = bs_gen n (bm_rsmul E e s) := eq_refl.

(* * *** The four module laws, each by agreement on generators / * *** 四个模法，每个都由生成元协定 *)

Lemma rt_act_scalar (N : RModObject (Ring_op R)) (s s' : SC) :
  s ≈ s' → ∀ x, rt_act N s x ≈ rt_act N s' x.
Proof.
  intros Hs x.
  refine (bal_hom_ext (rt_smul N s) (rt_smul N s') _ x).
  intros n e.
  exact (be_gen (reflexivity n)
           (bm_rsmul_respects E e e (reflexivity e) s s' Hs)).
Qed.

Lemma rt_act_respects (N : RModObject (Ring_op R)) :
  Proper (equiv ==> equiv ==> equiv) (rt_act N).
Proof.
  intros s s' Hs x y Hxy.
  transitivity (rt_act N s y).
  - exact (proper_morphism (cmon_map (rt_smul N s)) x y Hxy).
  - exact (rt_act_scalar N s s' Hs y).
Qed.

Lemma rt_act_distr_r (N : RModObject (Ring_op R)) (s s' : SC)
  (x : carrier (cmon_setoid (BalTensor N (bm_left E)))) :
  rt_act N (rig_add (ring_rig S) s s') x
    ≈ cmon_plus (BalTensor N (bm_left E)) (rt_act N s x) (rt_act N s' x).
Proof.
  refine (bal_hom_ext (rt_smul N (rig_add (ring_rig S) s s'))
            (ab_hom_add (rt_smul N s) (rt_smul N s')) _ x).
  intros n e.
  exact (be_trans
           (be_gen (reflexivity n) (bm_rsmul_distr_r E e s s'))
           (be_add_r n (bm_rsmul E e s) (bm_rsmul E e s'))).
Qed.

(*
 The associativity law is stated over [Ring_op S], where the product
 [rig_mul (ring_rig (Ring_op S)) s s'] reduces to [rig_mul S s' s]; on
 generators the two sides are e ⊲ (s' s) and (e ⊲ s') ⊲ s, which is
 [bm_rsmul_assoc] verbatim.  Associativity ONLY. 

 --------
 结合律在 [Ring_op S] 上陈述，其中乘积 [rig_mul (ring_rig (Ring_op S)) s s'] 简化为 [rig_mul S s' s]；在生成元上，两边分别是 e ⊲ (s' s) 和 (e ⊲ s') ⊲ s，即 [bm_rsmul_assoc] 原样。仅限结合律。
*)
Lemma rt_act_assoc (N : RModObject (Ring_op R)) (s s' : SC)
  (x : carrier (cmon_setoid (BalTensor N (bm_left E)))) :
  rt_act N (rig_mul (ring_rig (Ring_op S)) s s') x
    ≈ rt_act N s (rt_act N s' x).
Proof.
  refine (bal_hom_ext (rt_smul N (rig_mul (ring_rig (Ring_op S)) s s'))
            (cmon_hom_compose (rt_smul N s) (rt_smul N s')) _ x).
  intros n e.
  exact (be_gen (reflexivity n) (bm_rsmul_assoc E e s' s)).
Qed.

Lemma rt_act_one (N : RModObject (Ring_op R))
  (x : carrier (cmon_setoid (BalTensor N (bm_left E)))) :
  rt_act N (rig_one (ring_rig S)) x ≈ x.
Proof.
  refine (bal_hom_ext (rt_smul N (rig_one (ring_rig S)))
            (@cmon_hom_id (BalTensor N (bm_left E))) _ x).
  intros n e.
  exact (be_gen (reflexivity n) (bm_rsmul_one E e)).
Qed.

(*
 N ⊗_R E as an object of [ModR S].  The constructor is named
 explicitly with its ring argument: a record literal here elaborates
 the scalar argument's type against [S] and infers the parameter to be
 [S] rather than [Ring_op S], which silently asks the associativity
 field for the WRONG multiplication order.  This is the trap
 Instance/Mod.v records for [bimodule_right_RMod]. 

 --------
 N ⊗_R E 作为 [ModR S] 的一个对象。构造函数通过它的环参数被明确命名：这里的记录字面量对 [S] 的标量参数类型进行了详细说明，并推断参数为 [S] 而不是 [Ring_op S]，这会在无声中向结合性字段请求错误的乘法顺序。这是 Instance/Mod.v 为 [bimodule_right_RMod] 记录的陷阱。
*)
Definition RTensor (N : RModObject (Ring_op R)) :
  RModObject (Ring_op S) :=
  @Build_RModObject (Ring_op S)
    (BalTensor N (bm_left E))
    (rt_act N)
    (rt_act_respects N)
    (fun s x y => cmon_map_plus (rt_smul N s) x y)
    (rt_act_distr_r N)
    (rt_act_assoc N)
    (rt_act_one N).

Example rt_carrier (N : RModObject (Ring_op R)) :
  rm_ab (RTensor N) = BalTensor N (bm_left E) := eq_refl.

Example rt_zero (N : RModObject (Ring_op R)) :
  cmon_zero (rm_ab (RTensor N)) = bs_zero := eq_refl.

Example rt_plus (N : RModObject (Ring_op R))
  (x y : carrier (cmon_setoid (rm_ab (RTensor N)))) :
  cmon_plus (rm_ab (RTensor N)) x y = bs_plus x y := eq_refl.

Example rt_smul_gen (N : RModObject (Ring_op R)) (s : SC)
  (n : carrier (cmon_setoid (rm_ab N))) (e : EC) :
  rm_smul (RTensor N) s (bs_gen n e) = bs_gen n (bm_rsmul E e s)
  := eq_refl.

(* * *** The arrow action, and the functor − ⊗_R E / * *** 箭头作用，以及函子 − ⊗_R E *)

Program Definition rt_map_bal {N N' : RModObject (Ring_op R)}
  (f : RModHom N N') :
  BalBiadditive N (bm_left E) (BalTensor N' (bm_left E)) := {|
  bal_map := fun n e => bs_gen (cmon_map (rm_hom f) n) e
|}.
Next Obligation.
  intros N N' f n n' Hn e e' He.
  exact (be_gen (proper_morphism (cmon_map (rm_hom f)) n n' Hn) He).
Qed.
Next Obligation.
  intros N N' f n n' e.
  exact (be_trans
           (be_gen (cmon_map_plus (rm_hom f) n n') (reflexivity e))
           (be_add_l (cmon_map (rm_hom f) n)
                     (cmon_map (rm_hom f) n') e)).
Qed.
Next Obligation.
  intros N N' f n e e'.
  exact (be_add_r (cmon_map (rm_hom f) n) e e').
Qed.
Next Obligation.
  intros N N' f r n e.
  exact (be_trans
           (be_gen (rm_map_smul f r n) (reflexivity e))
           (be_balance r (cmon_map (rm_hom f) n) e)).
Qed.

Definition rt_map_ab {N N' : RModObject (Ring_op R)} (f : RModHom N N') :
  AbHom (BalTensor N (bm_left E)) (BalTensor N' (bm_left E)) :=
  bal_med (rt_map_bal f).

Program Definition RTensorMap {N N' : RModObject (Ring_op R)}
  (f : N ~{ModR R}~> N') : RTensor N ~{ModR S}~> RTensor N' := {|
  rm_hom := rt_map_ab f
|}.
Next Obligation.
  intros N N' f s x.
  refine (bal_hom_ext (cmon_hom_compose (rt_map_ab f) (rt_smul N s))
            (cmon_hom_compose (rt_smul N' s) (rt_map_ab f)) _ x).
  intros n e; reflexivity.
Qed.

Program Definition TensorWith : ModR R ⟶ ModR S := {|
  fobj := RTensor;
  fmap := @RTensorMap
|}.
Next Obligation.
  intros N N' f g Hfg x.
  refine (bal_hom_ext (rt_map_ab f) (rt_map_ab g) _ x).
  intros n e.
  exact (be_gen (Hfg n) (reflexivity e)).
Qed.
Next Obligation.
  intros N x.
  refine (bal_hom_ext (rt_map_ab (@id (ModR R) N))
            (@cmon_hom_id (BalTensor N (bm_left E))) _ x).
  intros n e; reflexivity.
Qed.
Next Obligation.
  intros N N' N'' f g x.
  refine (bal_hom_ext (rt_map_ab (f ∘ g))
            (cmon_hom_compose (rt_map_ab f) (rt_map_ab g)) _ x).
  intros n e; reflexivity.
Qed.

Example tw_fobj (N : RModObject (Ring_op R)) :
  fobj[TensorWith] N = RTensor N := eq_refl.

Example tw_fmap_gen {N N' : RModObject (Ring_op R)}
  (f : N ~{ModR R}~> N') (n : carrier (cmon_setoid (rm_ab N))) (e : EC) :
  cmon_map (rm_hom (fmap[TensorWith] f)) (bs_gen n e)
    = bs_gen (cmon_map (rm_hom f) n) e := eq_refl.

(* * *** hom_S(E, M) and its right R-action / * *** hom_S(E, M) 及其右 R-作用 *)

(*
 The underlying abelian group is Adjunction/Additive.v's [hom_ab] read
 at the enrichment above, so its carrier, zero, addition and negation
 are [RMod_Preadditive]'s own; nothing is rebuilt. 

 --------
 基础阿贝尔群是 Adjunction/Additive.v 中的 [hom_ab]，在上面的加强中读取，因此它的载体、零、加法和取反都是 [RMod_Preadditive] 自己的；没有重新构建任何东西。
*)
Definition hs_group (M : RModObject (Ring_op S)) : AbObject :=
  hom_ab (RMod_AbEnriched (Ring_op S)) EE M.

Example hs_group_carrier (M : RModObject (Ring_op S)) :
  carrier (cmon_setoid (hs_group M)) = (EE ~{ModR S}~> M) := eq_refl.

Example hs_group_plus (M : RModObject (Ring_op S)) :
  cmon_plus (hs_group M) = @rmod_hom_add (Ring_op S) EE M := eq_refl.

Example hs_group_zero (M : RModObject (Ring_op S)) :
  cmon_zero (hs_group M) = @rmod_hom_zero (Ring_op S) EE M := eq_refl.

(*
 The right R-action, by TRANSLATION through E's LEFT R-action:
 (f ⊲ r)(e) = f (r · e).  This is Instance/Mod/Coextension.v's idiom,
 with the translating action supplied by the bimodule instead
 of by the ring's own multiplication. 

 --------
 通过 E 的左 R-作用进行的右 R-作用的平移：
 (f ⊲ r)(e) = f (r · e)。这是 Instance/Mod/Coextension.v 的惯用法，
 平移作用由双模提供，而不是由环自身的乘法提供。
*)
Program Definition hs_act (M : RModObject (Ring_op S)) (r : RC)
  (f : EE ~{ModR S}~> M) : EE ~{ModR S}~> M := {|
  rm_hom := {| cmon_map := {| morphism := fun e =>
    cmon_map (rm_hom f) (rm_smul (bm_left E) r e) |} |}
|}.
Next Obligation.
  intros M r f e e' He.
  exact (proper_morphism (cmon_map (rm_hom f)) _ _
           (rm_smul_respects (bm_left E) r r (reflexivity r) e e' He)).
Qed.
Next Obligation.
  intros M r f; simpl.
  transitivity (cmon_map (rm_hom f) (cmon_zero (rm_ab (bm_left E)))).
  - exact (proper_morphism (cmon_map (rm_hom f)) _ _
             (rm_smul_zero_r (bm_left E) r)).
  - exact (cmon_map_zero (rm_hom f)).
Qed.
Next Obligation.
  intros M r f e e'; simpl.
  transitivity (cmon_map (rm_hom f)
                  (cmon_plus (rm_ab (bm_left E))
                     (rm_smul (bm_left E) r e)
                     (rm_smul (bm_left E) r e'))).
  - exact (proper_morphism (cmon_map (rm_hom f)) _ _
             (rm_smul_distr_l (bm_left E) r e e')).
  - exact (cmon_map_plus (rm_hom f) _ _).
Qed.
Next Obligation.
  (* [rm_map_smul] for the translated map: the ONLY use of [bm_compat] in this block, followed by [f]'s own linearity. / [rm_map_smul] 用于翻译后的地图：在此块中唯一使用 [bm_compat]，然后是 [f] 自身的线性。 *)
  intros M r f s e; simpl.
  transitivity (cmon_map (rm_hom f)
                  (bm_rsmul E (rm_smul (bm_left E) r e) s)).
  - exact (proper_morphism (cmon_map (rm_hom f)) _ _
             (symmetry (bm_compat E r e s))).
  - exact (rm_map_smul f s (rm_smul (bm_left E) r e)).
Qed.

Example hs_act_at (M : RModObject (Ring_op S)) (r : RC)
  (f : EE ~{ModR S}~> M) (e : EC) :
  cmon_map (rm_hom (hs_act M r f)) e
    = cmon_map (rm_hom f) (rm_smul (bm_left E) r e) := eq_refl.

Lemma hs_act_respects (M : RModObject (Ring_op S)) :
  Proper (equiv ==> equiv ==> equiv) (hs_act M).
Proof.
  intros r r' Hr f g Hfg e; simpl.
  transitivity (cmon_map (rm_hom f) (rm_smul (bm_left E) r' e)).
  - exact (proper_morphism (cmon_map (rm_hom f)) _ _
             (rm_smul_respects (bm_left E) r r' Hr e e (reflexivity e))).
  - exact (Hfg _).
Qed.

Lemma hs_act_distr_l (M : RModObject (Ring_op S)) (r : RC)
  (f g : EE ~{ModR S}~> M) :
  hs_act M r (cmon_plus (hs_group M) f g)
    ≈ cmon_plus (hs_group M) (hs_act M r f) (hs_act M r g).
Proof. intro e; reflexivity. Qed.

Lemma hs_act_distr_r (M : RModObject (Ring_op S)) (r r' : RC)
  (f : EE ~{ModR S}~> M) :
  hs_act M (rig_add (ring_rig R) r r') f
    ≈ cmon_plus (hs_group M) (hs_act M r f) (hs_act M r' f).
Proof.
  intro e; simpl.
  transitivity (cmon_map (rm_hom f)
                  (cmon_plus (rm_ab (bm_left E))
                     (rm_smul (bm_left E) r e)
                     (rm_smul (bm_left E) r' e))).
  - exact (proper_morphism (cmon_map (rm_hom f)) _ _
             (rm_smul_distr_r (bm_left E) r r' e)).
  - exact (cmon_map_plus (rm_hom f) _ _).
Qed.

(* Associativity ONLY: at e the two sides are f ((r' r) · e) and f (r' · (r · e)), and [rm_smul_assoc] of E's LEFT module is all that is consumed. / 仅结合性：在 e 处，两边是 f ((r' r) · e) 和 f (r' · (r · e))，而 E 的 LEFT 模块的 [rm_smul_assoc] 是消耗的全部内容。 *)
Lemma hs_act_assoc (M : RModObject (Ring_op S)) (r r' : RC)
  (f : EE ~{ModR S}~> M) :
  hs_act M (rig_mul (ring_rig (Ring_op R)) r r') f
    ≈ hs_act M r (hs_act M r' f).
Proof.
  intro e; simpl.
  exact (proper_morphism (cmon_map (rm_hom f)) _ _
           (rm_smul_assoc (bm_left E) r' r e)).
Qed.

Lemma hs_act_one (M : RModObject (Ring_op S)) (f : EE ~{ModR S}~> M) :
  hs_act M (rig_one (ring_rig R)) f ≈ f.
Proof.
  intro e; simpl.
  exact (proper_morphism (cmon_map (rm_hom f)) _ _
           (rm_smul_one (bm_left E) e)).
Qed.

Definition HomSObj (M : RModObject (Ring_op S)) :
  RModObject (Ring_op R) :=
  @Build_RModObject (Ring_op R)
    (hs_group M)
    (hs_act M)
    (hs_act_respects M)
    (hs_act_distr_l M)
    (hs_act_distr_r M)
    (hs_act_assoc M)
    (hs_act_one M).

(* * *** The arrow action, and the functor hom_S(E, −) / * *** 箭头作用，以及函子 hom_S(E, −) *)

Program Definition hs_map_ab {M M' : RModObject (Ring_op S)}
  (g : M ~{ModR S}~> M') : AbHom (hs_group M) (hs_group M') := {|
  cmon_map := {| morphism := fun f =>
    (rmod_hom_compose g f : EE ~{ModR S}~> M') |}
|}.
Next Obligation.
  intros M M' g f f' Hf e; simpl.
  unfold Basics.compose.
  exact (proper_morphism (cmon_map (rm_hom g)) _ _ (Hf e)).
Qed.
Next Obligation.
  intros M M' g e; simpl.
  exact (cmon_map_zero (rm_hom g)).
Qed.
Next Obligation.
  intros M M' g f f' e; simpl.
  exact (cmon_map_plus (rm_hom g) _ _).
Qed.

Program Definition HomSMap {M M' : RModObject (Ring_op S)}
  (g : M ~{ModR S}~> M') : HomSObj M ~{ModR R}~> HomSObj M' := {|
  rm_hom := hs_map_ab g
|}.
Next Obligation. intros M M' g r f e; reflexivity. Qed.

Program Definition HomS : ModR S ⟶ ModR R := {|
  fobj := HomSObj;
  fmap := @HomSMap
|}.
Next Obligation.
  intros M M' g g' Hg f e; simpl.
  exact (Hg _).
Qed.
Next Obligation. intros M f e; reflexivity. Qed.
Next Obligation. intros M M' M'' g g' f e; reflexivity. Qed.

Example hs_fobj (M : RModObject (Ring_op S)) :
  fobj[HomS] M = HomSObj M := eq_refl.

Example hs_fmap_at {M M' : RModObject (Ring_op S)}
  (g : M ~{ModR S}~> M') (f : EE ~{ModR S}~> M) (e : EC) :
  cmon_map (rm_hom (cmon_map (rm_hom (fmap[HomS] g)) f)) e
    = cmon_map (rm_hom g) (cmon_map (rm_hom f) e) := eq_refl.

(* * *** The two transposes and the adjunction / * *** 两个转置和伴随 *)

Program Definition bth_to_inner {N : RModObject (Ring_op R)}
  {M : RModObject (Ring_op S)} (g : RTensor N ~{ModR S}~> M)
  (n : carrier (cmon_setoid (rm_ab N))) : EE ~{ModR S}~> M := {|
  rm_hom := {| cmon_map := {| morphism := fun e =>
    cmon_map (rm_hom g) (bs_gen n e) |} |}
|}.
Next Obligation.
  intros N M g n e e' He.
  exact (proper_morphism (cmon_map (rm_hom g)) _ _
           (be_gen (reflexivity n) He)).
Qed.
Next Obligation.
  intros N M g n; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_zero (BalTensor N (bm_left E)))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (bal_gen_zero_r N (bm_left E) n)).
  - exact (cmon_map_zero (rm_hom g)).
Qed.
Next Obligation.
  intros N M g n e e'; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_plus (BalTensor N (bm_left E))
                     (bs_gen n e) (bs_gen n e'))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (be_add_r n e e')).
  - exact (cmon_map_plus (rm_hom g) _ _).
Qed.
Next Obligation.
  (*
 n ⊗ (e ⊲ s) IS s ·[RTensor N] (n ⊗ e) on the nose, so this is
 [g]'s own linearity with no rewriting. 

 --------
 n ⊗ (e ⊲ s) 就是 s · [RTensor N] (n ⊗ e) 本身，所以这是 [g] 自身的线性，而无需重写。
*)
  intros N M g n s e.
  exact (rm_map_smul g s (bs_gen n e)).
Qed.

Program Definition bth_to_ab {N : RModObject (Ring_op R)}
  {M : RModObject (Ring_op S)} (g : RTensor N ~{ModR S}~> M) :
  AbHom (rm_ab N) (hs_group M) := {|
  cmon_map := {| morphism := fun n => bth_to_inner g n |}
|}.
Next Obligation.
  intros N M g n n' Hn e; simpl.
  exact (proper_morphism (cmon_map (rm_hom g)) _ _
           (be_gen Hn (reflexivity e))).
Qed.
Next Obligation.
  intros N M g e; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_zero (BalTensor N (bm_left E)))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (bal_gen_zero_l N (bm_left E) e)).
  - exact (cmon_map_zero (rm_hom g)).
Qed.
Next Obligation.
  intros N M g n n' e; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_plus (BalTensor N (bm_left E))
                     (bs_gen n e) (bs_gen n' e))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (be_add_l n n' e)).
  - exact (cmon_map_plus (rm_hom g) _ _).
Qed.

(* The forward transpose is R-linear BECAUSE of the balance rule: at e the two sides are g ((r · n) ⊗ e) and g (n ⊗ (r · e)). / 正向转置是 R 线性的，因为平衡规则：在 e 处，两边分别是 g ((r · n) ⊗ e) 和 g (n ⊗ (r · e))。 *)
Program Definition bth_to {N : RModObject (Ring_op R)}
  {M : RModObject (Ring_op S)} (g : RTensor N ~{ModR S}~> M) :
  N ~{ModR R}~> HomSObj M := {|
  rm_hom := bth_to_ab g
|}.
Next Obligation.
  intros N M g r n e; simpl.
  exact (proper_morphism (cmon_map (rm_hom g)) _ _
           (@be_balance R N (bm_left E) r n e)).
Qed.

Program Definition bth_from_bal {N : RModObject (Ring_op R)}
  {M : RModObject (Ring_op S)} (h : N ~{ModR R}~> HomSObj M) :
  BalBiadditive N (bm_left E) (rm_ab M) := {|
  bal_map := fun n e =>
    cmon_map (rm_hom (cmon_map (rm_hom h) n)) e
|}.
Next Obligation.
  intros N M h n n' Hn e e' He.
  transitivity (cmon_map (rm_hom (cmon_map (rm_hom h) n)) e').
  - exact (proper_morphism (cmon_map (rm_hom (cmon_map (rm_hom h) n)))
             e e' He).
  - exact (proper_morphism (cmon_map (rm_hom h)) n n' Hn e').
Qed.
Next Obligation.
  intros N M h n n' e.
  exact (cmon_map_plus (rm_hom h) n n' e).
Qed.
Next Obligation.
  intros N M h n e e'.
  exact (cmon_map_plus (rm_hom (cmon_map (rm_hom h) n)) e e').
Qed.
Next Obligation.
  (*
 Balance is [h]'s own R-linearity, read at e: the action on
 hom_S(E, M) is translation, so (r · h n) e IS (h n) (r · e). 

 --------
 平衡是 [h] 自身的 R-线性，在 e 处读取：对 hom_S(E, M) 的作用是平移，所以 (r · h n) e 是 (h n) (r · e)。
*)
  intros N M h r n e.
  exact (rm_map_smul h r n e).
Qed.

(* Multiplication by a scalar, as a homomorphism of the underlying group; the Instance/Mod/BaseChange.v idiom. / 作为底层群的同态的标量乘法；Instance/Mod/BaseChange.v 习语。 *)
Program Definition bth_lmul (M : RModObject (Ring_op S)) (s : SC) :
  AbHom (rm_ab M) (rm_ab M) := {|
  cmon_map := {| morphism := fun m => rm_smul M s m |}
|}.
Next Obligation.
  intros M s m m' Hm.
  exact (rm_smul_respects M s s (reflexivity s) m m' Hm).
Qed.
Next Obligation. intros M s; simpl; exact (rm_smul_zero_r M s). Qed.
Next Obligation.
  intros M s m m'; simpl; exact (rm_smul_distr_l M s m m').
Qed.

Program Definition bth_from {N : RModObject (Ring_op R)}
  {M : RModObject (Ring_op S)} (h : N ~{ModR R}~> HomSObj M) :
  RTensor N ~{ModR S}~> M := {|
  rm_hom := bal_med (bth_from_bal h)
|}.
Next Obligation.
  intros N M h s x.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med (bth_from_bal h)) (rt_smul N s))
            (cmon_hom_compose (bth_lmul M s)
                              (bal_med (bth_from_bal h))) _ x).
  intros n e.
  exact (rm_map_smul (cmon_map (rm_hom h) n) s e).
Qed.

Example bth_to_at {N : RModObject (Ring_op R)}
  {M : RModObject (Ring_op S)} (g : RTensor N ~{ModR S}~> M)
  (n : carrier (cmon_setoid (rm_ab N))) (e : EC) :
  cmon_map (rm_hom (cmon_map (rm_hom (bth_to g)) n)) e
    = cmon_map (rm_hom g) (bs_gen n e) := eq_refl.

Example bth_from_at {N : RModObject (Ring_op R)}
  {M : RModObject (Ring_op S)} (h : N ~{ModR R}~> HomSObj M)
  (n : carrier (cmon_setoid (rm_ab N))) (e : EC) :
  cmon_map (rm_hom (bth_from h)) (bs_gen n e)
    = cmon_map (rm_hom (cmon_map (rm_hom h) n)) e := eq_refl.

Program Definition bth_adj_to (N : RModObject (Ring_op R))
  (M : RModObject (Ring_op S)) :
  {| carrier := RTensor N ~{ModR S}~> M;
     is_setoid := @homset (ModR S) (RTensor N) M |}
    ~{Sets}~>
  {| carrier := N ~{ModR R}~> HomSObj M;
     is_setoid := @homset (ModR R) N (HomSObj M) |} := {|
  morphism := fun g => bth_to g
|}.
Next Obligation. intros N M g g' Hg n e; exact (Hg _). Qed.

Program Definition bth_adj_from (N : RModObject (Ring_op R))
  (M : RModObject (Ring_op S)) :
  {| carrier := N ~{ModR R}~> HomSObj M;
     is_setoid := @homset (ModR R) N (HomSObj M) |}
    ~{Sets}~>
  {| carrier := RTensor N ~{ModR S}~> M;
     is_setoid := @homset (ModR S) (RTensor N) M |} := {|
  morphism := fun h => bth_from h
|}.
Next Obligation.
  intros N M h h' Hh x.
  refine (bal_hom_ext (bal_med (bth_from_bal h))
                      (bal_med (bth_from_bal h')) _ x).
  intros n e; exact (Hh n e).
Qed.

(* Both round trips close by [reflexivity]: the forward transpose reads a generator and the backward one writes one, so nothing residual is left behind on either side. / 在 [reflexivity] 附近的两个往返路径：正向转置读取一个生成器，反向转置写入一个生成器，因此双方都没有留下任何残余。 *)
Program Definition bth_adj (N : RModObject (Ring_op R))
  (M : RModObject (Ring_op S)) :
  @Isomorphism Sets
    {| carrier := RTensor N ~{ModR S}~> M;
       is_setoid := @homset (ModR S) (RTensor N) M |}
    {| carrier := N ~{ModR R}~> HomSObj M;
       is_setoid := @homset (ModR R) N (HomSObj M) |} := {|
  to   := bth_adj_to N M;
  from := bth_adj_from N M
|}.
Next Obligation. intros N M h n e; reflexivity. Qed.
Next Obligation.
  intros N M g x.
  refine (bal_hom_ext (bal_med (bth_from_bal (bth_to g)))
                      (rm_hom g) _ x).
  intros n e; reflexivity.
Qed.

(*
 Mac Lane part (a).  Both remaining naturality obligations close by
 [reflexivity]. 

 --------
 Mac Lane 第 (a) 部分。两个剩余的自然性义务都由 [reflexivity] 关闭。
*)
Definition bimodule_tensor_hom_adjunction : TensorWith ⊣ HomS.
Proof.
  unshelve eapply (@Build_Adjunction' (ModR S) (ModR R) TensorWith
                     HomS bth_adj).
  - intros N N' M f g n e; reflexivity.
  - intros N M M' f g n e; reflexivity.
Defined.

(** *** Unit and counit / *** 单位和余单位 *)

Definition bth_unit (N : RModObject (Ring_op R)) :
  N ~{ModR R}~> HomSObj (RTensor N) :=
  @unit (ModR S) (ModR R) TensorWith HomS
    bimodule_tensor_hom_adjunction N.

Definition bth_counit (M : RModObject (Ring_op S)) :
  RTensor (HomSObj M) ~{ModR S}~> M :=
  @counit (ModR S) (ModR R) TensorWith HomS
    bimodule_tensor_hom_adjunction M.

(* THE REVIEWER CHECK. The unit IS n ↦ (e ↦ n ⊗ e) and the counit IS f ⊗ e ↦ f e, both on the nose. / 审阅者检查。单位是 n ↦ (e ↦ n ⊗ e)，余单位是 f ⊗ e ↦ f e，都完全一样。 *)
Example bth_unit_is_gen (N : RModObject (Ring_op R))
  (n : carrier (cmon_setoid (rm_ab N))) (e : EC) :
  cmon_map (rm_hom (cmon_map (rm_hom (bth_unit N)) n)) e
    = bs_gen n e := eq_refl.

Example bth_counit_is_eval (M : RModObject (Ring_op S))
  (f : EE ~{ModR S}~> M) (e : EC) :
  cmon_map (rm_hom (bth_counit M))
      (@bs_gen R (HomSObj M) (bm_left E) f e)
    = cmon_map (rm_hom f) e := eq_refl.

Example bth_adj_to_is_bth_to (N : RModObject (Ring_op R))
  (M : RModObject (Ring_op S)) (g : RTensor N ~{ModR S}~> M) :
  to (@adj (ModR S) (ModR R) TensorWith HomS
        bimodule_tensor_hom_adjunction N M) g = bth_to g := eq_refl.

Example bth_adj_from_is_bth_from (N : RModObject (Ring_op R))
  (M : RModObject (Ring_op S)) (h : N ~{ModR R}~> HomSObj M) :
  from (@adj (ModR S) (ModR R) TensorWith HomS
          bimodule_tensor_hom_adjunction N M) h = bth_from h := eq_refl.

End BimoduleTensorHom.

(* * ** C. The category of bimodules, the bifunctor, and Theorem 3 / * ** C. 双模范畴、双函子及定理 3 *)

Section BimoduleCategory.

Context {R S : RingObject}.

Local Notation RC := (carrier (rig_setoid (ring_rig R))).
Local Notation SC := (carrier (rig_setoid (ring_rig S))).

(*
 A morphism of (R,S)-bimodules: a homomorphism of the LEFT R-modules
 that additionally commutes with the right S-action.  Nothing about
 the left action is restated — [bh_hom] is a coercion, and the record
 has exactly one field of its own. 

 --------
 (R,S)-双模的态射：一个左R-模的同态，同时还与右S-作用交换。关于左作用没有重新说明——[bh_hom] 是一种强制转换，并且该记录恰好有一个自己的字段。
*)
Record BimodHom (E E' : Bimodule R S) := {
  bh_hom :> RModHom (bm_left E) (bm_left E');

  bh_right : ∀ m s,
    cmon_map (rm_hom bh_hom) (bm_rsmul E m s)
      ≈ bm_rsmul E' (cmon_map (rm_hom bh_hom) m) s
}.

Arguments bh_hom {E E'} _.
Arguments bh_right {E E'} _ _ _.

(*
 The hom-setoid: two bimodule maps agree when their underlying maps
 agree pointwise, which is Instance/Mod.v's [RModHom_Setoid] one
 field further in.  Neither action plays a part. 

 --------
 同构集：当两个双模映射的基础映射在每个点上都相同时，它们就被认为相等，这对应于 Instance/Mod.v 中 [RModHom_Setoid] 的一个字段。两个作用都不起作用。
*)
#[export]
Program Instance BimodHom_Setoid {E E' : Bimodule R S} :
  Setoid (BimodHom E E') := {|
  equiv := fun f g => ∀ e,
    cmon_map (rm_hom (bh_hom f)) e ≈ cmon_map (rm_hom (bh_hom g)) e
|}.
Next Obligation.
  intros E E'.
  constructor.
  - intros f e; reflexivity.
  - intros f g Hfg e; symmetry; apply Hfg.
  - intros f g h Hfg Hgh e.
    transitivity (cmon_map (rm_hom (bh_hom g)) e).
    + apply Hfg.
    + apply Hgh.
Qed.

Program Definition bimod_hom_id {E : Bimodule R S} : BimodHom E E := {|
  bh_hom := @rmod_hom_id R (bm_left E)
|}.
Next Obligation. intros E m s; simpl; reflexivity. Qed.

Program Definition bimod_hom_compose {E E' E'' : Bimodule R S}
        (f : BimodHom E' E'') (g : BimodHom E E') : BimodHom E E'' := {|
  bh_hom := rmod_hom_compose (bh_hom f) (bh_hom g)
|}.
Next Obligation.
  intros E E' E'' f g m s; simpl.
  unfold Basics.compose.
  transitivity (cmon_map (rm_hom (bh_hom f))
                  (bm_rsmul E' (cmon_map (rm_hom (bh_hom g)) m) s)).
  - exact (proper_morphism (cmon_map (rm_hom (bh_hom f))) _ _
             (bh_right g m s)).
  - exact (bh_right f (cmon_map (rm_hom (bh_hom g)) m) s).
Qed.

Lemma bimod_hom_compose_respects {E E' E'' : Bimodule R S} :
  Proper (equiv ==> equiv ==> equiv) (@bimod_hom_compose E E' E'').
Proof.
  intros f f' Hf g g' Hg e; simpl.
  unfold Basics.compose.
  transitivity (cmon_map (rm_hom (bh_hom f))
                  (cmon_map (rm_hom (bh_hom g')) e)).
  - exact (proper_morphism (cmon_map (rm_hom (bh_hom f))) _ _ (Hg e)).
  - exact (Hf _).
Qed.

Program Definition BimodCat : Category := {|
  obj     := Bimodule R S;
  hom     := BimodHom;
  homset  := fun E E' => @BimodHom_Setoid E E';
  id      := fun E => @bimod_hom_id E;
  compose := fun E E' E'' f g => @bimod_hom_compose E E' E'' f g;

  compose_respects := fun E E' E'' => @bimod_hom_compose_respects E E' E''
|}.
Next Obligation. intros E E' f e; simpl; reflexivity. Qed.
Next Obligation. intros E E' f e; simpl; reflexivity. Qed.
Next Obligation. intros E E' E'' E''' f g h e; simpl; reflexivity. Qed.
Next Obligation. intros E E' E'' E''' f g h e; simpl; reflexivity. Qed.

(*
 A bimodule map IS a map of the associated RIGHT S-modules, and the
 proof is its own [bh_right] field with the two arguments swapped —
 the flip that [bimodule_right_RMod] performs on the action. 

 --------
 一个双模映射是相关右 S-模的映射，证明本身就是它的 [bh_right] 域，将两个参数交换——[bimodule_right_RMod] 在作用上执行的翻转。
*)
Program Definition bimod_hom_right {E E' : Bimodule R S}
  (h : BimodHom E E') :
  bimodule_right_RMod E ~{ModR S}~> bimodule_right_RMod E' := {|
  rm_hom := rm_hom (bh_hom h)
|}.
Next Obligation. intros E E' h s m; exact (bh_right h m s). Qed.

Example bimodcat_hom (E E' : Bimodule R S) :
  (E ~{BimodCat}~> E') = BimodHom E E' := eq_refl.

Example bimodcat_id_map (E : Bimodule R S)
  (e : carrier (cmon_setoid (rm_ab (bm_left E)))) :
  cmon_map (rm_hom (bh_hom (@id BimodCat E))) e = e := eq_refl.

(* * *** The tensor as a bifunctor of both variables / * *** 张量作为两个变量的双函子 *)

(*
 Functoriality in the BIMODULE argument.  Scout B's item 1(ii): this
 is a PREREQUISITE of Mac Lane's Theorem 3, not an output of it — the
 theorem forces the arrow action of the RIGHT adjoint, and says
 nothing about the arrow action of the left one. 

 --------
 BIMODULE 参数中的函子性。侦察 B 的第 1(ii) 项：这是 Mac Lane 定理 3 的前提，而不是其结论——该定理限定了右伴随的箭头作用，但对左伴随的箭头作用没有任何说明。
*)
Program Definition bt_map_bal {N N' : RModObject (Ring_op R)}
  {E E' : Bimodule R S} (f : N ~{ModR R}~> N') (h : E ~{BimodCat}~> E') :
  BalBiadditive N (bm_left E) (BalTensor N' (bm_left E')) := {|
  bal_map := fun n e =>
    bs_gen (cmon_map (rm_hom f) n) (cmon_map (rm_hom (bh_hom h)) e)
|}.
Next Obligation.
  intros N N' E E' f h n n' Hn e e' He.
  exact (be_gen (proper_morphism (cmon_map (rm_hom f)) n n' Hn)
                (proper_morphism (cmon_map (rm_hom (bh_hom h))) e e' He)).
Qed.
Next Obligation.
  intros N N' E E' f h n n' e.
  exact (be_trans
           (be_gen (cmon_map_plus (rm_hom f) n n') (reflexivity _))
           (be_add_l (cmon_map (rm_hom f) n)
                     (cmon_map (rm_hom f) n')
                     (cmon_map (rm_hom (bh_hom h)) e))).
Qed.
Next Obligation.
  intros N N' E E' f h n e e'.
  exact (be_trans
           (be_gen (reflexivity _)
                   (cmon_map_plus (rm_hom (bh_hom h)) e e'))
           (be_add_r (cmon_map (rm_hom f) n)
                     (cmon_map (rm_hom (bh_hom h)) e)
                     (cmon_map (rm_hom (bh_hom h)) e'))).
Qed.
Next Obligation.
  (* The balance clause spends [f]'s linearity and then [h]'s. / 平衡条款先消耗 [f] 的线性，然后消耗 [h] 的线性。 *)
  intros N N' E E' f h r n e.
  exact (be_trans
           (be_trans
              (be_gen (rm_map_smul f r n) (reflexivity _))
              (@be_balance R N' (bm_left E') r
                 (cmon_map (rm_hom f) n)
                 (cmon_map (rm_hom (bh_hom h)) e)))
           (be_gen (reflexivity _)
                   (symmetry (rm_map_smul (bh_hom h) r e)))).
Qed.

Program Definition BimodTensorMap {N N' : RModObject (Ring_op R)}
  {E E' : Bimodule R S} (f : N ~{ModR R}~> N') (h : E ~{BimodCat}~> E') :
  RTensor E N ~{ModR S}~> RTensor E' N' := {|
  rm_hom := bal_med (bt_map_bal f h)
|}.
Next Obligation.
  intros N N' E E' f h s x.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med (bt_map_bal f h)) (rt_smul E N s))
            (cmon_hom_compose (rt_smul E' N' s)
                              (bal_med (bt_map_bal f h))) _ x).
  intros n e; simpl.
  exact (be_gen (reflexivity _) (bh_right h e s)).
Qed.

Program Definition BimodTensor : ModR R ∏ BimodCat ⟶ ModR S := {|
  fobj := fun p => RTensor (snd p) (fst p);
  fmap := fun p q fh => BimodTensorMap (fst fh) (snd fh)
|}.
Next Obligation.
  intros [N E] [N' E'] [f h] [f' h'] [Hf Hh] x; simpl in *.
  refine (bal_hom_ext (bal_med (bt_map_bal f h))
                      (bal_med (bt_map_bal f' h')) _ x).
  intros n e.
  exact (be_gen (Hf n) (Hh e)).
Qed.
Next Obligation.
  intros [N E] x; simpl.
  refine (bal_hom_ext
            (bal_med (bt_map_bal (@id (ModR R) N) (@id BimodCat E)))
            (@cmon_hom_id (BalTensor N (bm_left E))) _ x).
  intros n e; reflexivity.
Qed.
Next Obligation.
  intros [N E] [N' E'] [N'' E''] [f h] [f' h'] x; simpl in *.
  refine (bal_hom_ext
            (bal_med (bt_map_bal
                        (rmod_hom_compose f f') (bimod_hom_compose h h')))
            (cmon_hom_compose (bal_med (bt_map_bal f h))
                              (bal_med (bt_map_bal f' h'))) _ x).
  intros n e; reflexivity.
Qed.

Example bimod_tensor_obj (N : RModObject (Ring_op R))
  (E : Bimodule R S) :
  fobj[BimodTensor] (N, E) = RTensor E N := eq_refl.

Example bimod_tensor_partial_obj (E : Bimodule R S)
  (N : RModObject (Ring_op R)) :
  fobj[Partial_l BimodTensor E] N = RTensor E N := eq_refl.

Example bimod_tensor_partial_gen (E : Bimodule R S)
  {N N' : RModObject (Ring_op R)} (f : N ~{ModR R}~> N')
  (n : carrier (cmon_setoid (rm_ab N)))
  (e : carrier (cmon_setoid (rm_ab (bm_left E)))) :
  cmon_map (rm_hom (fmap[Partial_l BimodTensor E] f)) (bs_gen n e)
    = bs_gen (cmon_map (rm_hom f) n) e := eq_refl.

(* * *** Mac Lane part (b): the adjunction with a parameter / * *** 马克·莱恩部分（b）：带有参数的伴随 *)

(*
 The partial functor at E and [TensorWith E] agree on objects and on
 generators, so the hom-setoid isomorphism of part (a) is reused
 verbatim; both naturality obligations close by [reflexivity]. 

 --------
 在对象和生成元上，E 处的部分函子与 [TensorWith E] 一致，因此部分 (a) 的同态集等价同构被逐字重用；两个自然性义务都通过 [reflexivity] 解决。
*)
Definition bt_partial_adj (E : Bimodule R S) :
  Partial_l BimodTensor E ⊣ HomS E.
Proof.
  unshelve eapply (@Build_Adjunction' (ModR S) (ModR R)
                     (Partial_l BimodTensor E) (HomS E) (bth_adj E)).
  - intros N N' M f g n e; reflexivity.
  - intros N M M' f g n e; reflexivity.
Defined.

Definition bimodule_parametrized_adjunction :
  ParametrizedAdjunction BimodTensor :=
  @Build_ParametrizedAdjunction (ModR R) BimodCat (ModR S)
    BimodTensor (@HomS R S) bt_partial_adj.

Example bimod_pa_right (E : Bimodule R S) :
  pa_right bimodule_parametrized_adjunction E = HomS E := eq_refl.

Example bimod_pa_adj (E : Bimodule R S) :
  pa_adj bimodule_parametrized_adjunction E = bt_partial_adj E := eq_refl.

(* Mac Lane's G : P^op × A → X. Its arrow action in the BIMODULE variable is #396's [pa_param_mate] and is therefore FORCED by Theorem 3; nothing here re-proves functoriality in E. / Mac Lane 的 G：P^op × A → X。它在 BIMODULE 变量中的箭头作用是 #396 的 [pa_param_mate]，因此由定理 3 强制；这里没有重新证明 E 中的函子性。 *)
Definition bimodule_hom_bifunctor :
  (BimodCat)^op ∏ ModR S ⟶ ModR R :=
  parametrized_right_adjoint_bifunctor bimodule_parametrized_adjunction.

Example bimod_hom_bifunctor_obj (E : Bimodule R S)
  (M : RModObject (Ring_op S)) :
  fobj[bimodule_hom_bifunctor] (E, M) = HomSObj E M := eq_refl.

End BimoduleCategory.

Arguments BimodHom {R S} E E'.

(* * ** D. Part (c): the tensor of two bimodules, and the composite / * ** D. 第(c)部分：两个双模的张量，以及复合 *)

(* Two readings of the generator former as a homomorphism of ONE of its two variables. They belong beside §A and are declared here only because §D is their first consumer. / 将发电机的前身作为其两个变量中的一个的同态进行两次读取。它们应当放在§A旁边，这里声明它们只是因为§D是它们的第一个使用者。 *)

Section BalancedGenerators.

Context {X : RingObject}.
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).

Program Definition bal_gen_right
  (n : carrier (cmon_setoid (rm_ab N))) :
  AbHom (rm_ab M) (BalTensor N M) := {|
  cmon_map := {| morphism := fun m => bs_gen n m |}
|}.
Next Obligation.
  intros n m m' Hm; exact (be_gen (reflexivity n) Hm).
Qed.
Next Obligation. intros n; exact (bal_gen_zero_r N M n). Qed.
Next Obligation. intros n m m'; exact (be_add_r n m m'). Qed.

Program Definition bal_gen_left
  (m : carrier (cmon_setoid (rm_ab M))) :
  AbHom (rm_ab N) (BalTensor N M) := {|
  cmon_map := {| morphism := fun n => bs_gen n m |}
|}.
Next Obligation.
  intros m n n' Hn; exact (be_gen Hn (reflexivity m)).
Qed.
Next Obligation. intros m; exact (bal_gen_zero_l N M m). Qed.
Next Obligation. intros m n n'; exact (be_add_l n n' m). Qed.

End BalancedGenerators.

Arguments bal_gen_right {X} N M n.
Arguments bal_gen_left {X} N M m.

(* * *** The left R-action on a balanced tensor over S / * *** 平衡张量在 S 上的左 R-作用 *)

(*
 This engine is shared: §D's tensor of two bimodules and §E's
 left-module mirror are its two instantiations.  Given a bimodule
 _R E _S and a LEFT S-module N, the balanced tensor E ⊗_S N carries a
 left R-action r · (e ⊗ n) := (r · e) ⊗ n, whose balance clause is
 again [bm_compat] and nothing else. 

 --------
 这个引擎是共享的：§D 的两个双模的张量和 §E 的左模镜像是它的两个实例化。给定一个双模 _R E _S 和一个左 S-模 N，平衡张量 E ⊗_S N 承载一个左 R-作用 r · (e ⊗ n) := (r · e) ⊗ n，其平衡条款仍然是 [bm_compat]，没有其他。
*)

Section BimoduleLeftTensor.

Context {R S : RingObject}.
Context (E : Bimodule R S).

Local Notation RC := (carrier (rig_setoid (ring_rig R))).
Local Notation SC := (carrier (rig_setoid (ring_rig S))).
Local Notation EC := (carrier (cmon_setoid (rm_ab (bm_left E)))).
Local Notation EE := (bimodule_right_RMod E).

Program Definition lt_bilin_act (N : RModObject S) (r : RC) :
  BalBiadditive EE N (BalTensor EE N) := {|
  bal_map := fun e n => bs_gen (rm_smul (bm_left E) r e) n
|}.
Next Obligation.
  intros N r e e' He n n' Hn.
  refine (be_gen _ Hn).
  exact (rm_smul_respects (bm_left E) r r (reflexivity r) e e' He).
Qed.
Next Obligation.
  intros N r e e' n.
  refine (be_trans _ (@be_add_l S (bimodule_right_RMod E) N
                        (rm_smul (bm_left E) r e)
                        (rm_smul (bm_left E) r e') n)).
  refine (be_gen _ (reflexivity n)).
  exact (rm_smul_distr_l (bm_left E) r e e').
Qed.
Next Obligation.
  intros N r e n n'.
  exact (@be_add_r S (bimodule_right_RMod E) N
           (rm_smul (bm_left E) r e) n n').
Qed.
Next Obligation.
  intros N r x e n.
  refine (be_trans _ (@be_balance S (bimodule_right_RMod E) N x
                        (rm_smul (bm_left E) r e) n)).
  refine (be_gen _ (reflexivity n)).
  exact (symmetry (bm_compat E r e x)).
Qed.

Definition lt_smul (N : RModObject S) (r : RC) :
  AbHom (BalTensor EE N) (BalTensor EE N) :=
  bal_med (lt_bilin_act N r).

Definition lt_act (N : RModObject S) (r : RC)
  (x : carrier (cmon_setoid (BalTensor EE N))) :
  carrier (cmon_setoid (BalTensor EE N)) :=
  cmon_map (lt_smul N r) x.

Example lt_act_gen (N : RModObject S) (r : RC) (e : EC)
  (n : carrier (cmon_setoid (rm_ab N))) :
  lt_act N r (@bs_gen S (bimodule_right_RMod E) N e n)
    = @bs_gen S (bimodule_right_RMod E) N
        (rm_smul (bm_left E) r e) n := eq_refl.

Lemma lt_act_scalar (N : RModObject S) (r r' : RC) :
  r ≈ r' → ∀ x, lt_act N r x ≈ lt_act N r' x.
Proof.
  intros Hr x.
  refine (bal_hom_ext (lt_smul N r) (lt_smul N r') _ x).
  intros e n.
  refine (be_gen _ (reflexivity n)).
  exact (rm_smul_respects (bm_left E) r r' Hr e e (reflexivity e)).
Qed.

Lemma lt_act_respects (N : RModObject S) :
  Proper (equiv ==> equiv ==> equiv) (lt_act N).
Proof.
  intros r r' Hr x y Hxy.
  transitivity (lt_act N r y).
  - exact (proper_morphism (cmon_map (lt_smul N r)) x y Hxy).
  - exact (lt_act_scalar N r r' Hr y).
Qed.

Lemma lt_act_distr_r (N : RModObject S) (r r' : RC)
  (x : carrier (cmon_setoid (BalTensor EE N))) :
  lt_act N (rig_add (ring_rig R) r r') x
    ≈ cmon_plus (BalTensor EE N) (lt_act N r x) (lt_act N r' x).
Proof.
  refine (bal_hom_ext (lt_smul N (rig_add (ring_rig R) r r'))
            (ab_hom_add (lt_smul N r) (lt_smul N r')) _ x).
  intros e n.
  refine (be_trans _ (@be_add_l S (bimodule_right_RMod E) N
                        (rm_smul (bm_left E) r e)
                        (rm_smul (bm_left E) r' e) n)).
  refine (be_gen _ (reflexivity n)).
  exact (rm_smul_distr_r (bm_left E) r r' e).
Qed.

Lemma lt_act_assoc (N : RModObject S) (r r' : RC)
  (x : carrier (cmon_setoid (BalTensor EE N))) :
  lt_act N (rig_mul (ring_rig R) r r') x ≈ lt_act N r (lt_act N r' x).
Proof.
  refine (bal_hom_ext (lt_smul N (rig_mul (ring_rig R) r r'))
            (cmon_hom_compose (lt_smul N r) (lt_smul N r')) _ x).
  intros e n.
  refine (be_gen _ (reflexivity n)).
  exact (rm_smul_assoc (bm_left E) r r' e).
Qed.

Lemma lt_act_one (N : RModObject S)
  (x : carrier (cmon_setoid (BalTensor EE N))) :
  lt_act N (rig_one (ring_rig R)) x ≈ x.
Proof.
  refine (bal_hom_ext (lt_smul N (rig_one (ring_rig R)))
            (@cmon_hom_id (BalTensor EE N)) _ x).
  intros e n.
  refine (be_gen _ (reflexivity n)).
  exact (rm_smul_one (bm_left E) e).
Qed.

(* E ⊗_S N as a LEFT R-module. / E ⊗_S N 作为左 R-模。 *)
Definition LTensor (N : RModObject S) : RModObject R :=
  @Build_RModObject R
    (BalTensor EE N)
    (lt_act N)
    (lt_act_respects N)
    (fun r x y => cmon_map_plus (lt_smul N r) x y)
    (lt_act_distr_r N)
    (lt_act_assoc N)
    (lt_act_one N).

Example lt_carrier (N : RModObject S) :
  rm_ab (LTensor N) = BalTensor EE N := eq_refl.

Example lt_smul_gen (N : RModObject S) (r : RC) (e : EC)
  (n : carrier (cmon_setoid (rm_ab N))) :
  rm_smul (LTensor N) r (@bs_gen S (bimodule_right_RMod E) N e n)
    = @bs_gen S (bimodule_right_RMod E) N
        (rm_smul (bm_left E) r e) n := eq_refl.

End BimoduleLeftTensor.

Arguments lt_bilin_act {R S} E N r.
Arguments lt_smul {R S} E N r.
Arguments lt_act {R S} E N r x.
Arguments LTensor {R S} E N.

(** *** The tensor of two bimodules / *** 两个双模的张量 *)

(*
 For _R E _S and _S E1 _T, the balanced tensor E ⊗_S E1 carries BOTH
 residual actions on ONE group: the left R-action of §D's engine and
 the right T-action of §B's, and they commute for a reason with no
 content — on a generator both sides are (r · e) ⊗ (e1 ⊲ t). 

 --------
 对于 _R E _S 和 _S E1 _T，平衡张量 E ⊗_S E1 承载两者的剩余作用在同一组上：§D 的引擎的左 R 作用和 §B 的右 T 作用，它们因为一个没有实际内容的原因而可交换——在一个生成元上，两边都是 (r · e) ⊗ (e1 ⊲ t)。
*)

Section BimoduleTensorBimodule.

Context {R S T : RingObject}.
Context (E : Bimodule R S).
Context (E1 : Bimodule S T).

Local Notation RC := (carrier (rig_setoid (ring_rig R))).
Local Notation TC := (carrier (rig_setoid (ring_rig T))).
Local Notation EE := (bimodule_right_RMod E).
Local Notation BTC := (BalTensor EE (bm_left E1)).

Definition btb_left : RModObject R := LTensor E (bm_left E1).
Definition btb_right : RModObject (Ring_op T) := RTensor E1 EE.

Example btb_carriers_agree : rm_ab btb_left = rm_ab btb_right := eq_refl.

Lemma btb_rsmul_respects :
  Proper (equiv ==> equiv ==> equiv)
    (fun (x : carrier (cmon_setoid BTC)) (t : TC) =>
       rm_smul btb_right t x).
Proof.
  intros x y Hxy t t' Ht.
  exact (rm_smul_respects btb_right t t' Ht x y Hxy).
Qed.

(* The ONE clause with content, and it has none: [bal_hom_ext] reduces it to a reflexivity on generators. / 唯一有内容的子句，而它没有内容：[bal_hom_ext] 将其简化为生成元上的自反性。 *)
Lemma btb_compat (r : RC) (x : carrier (cmon_setoid BTC)) (t : TC) :
  rm_smul btb_right t (rm_smul btb_left r x)
    ≈ rm_smul btb_left r (rm_smul btb_right t x).
Proof.
  refine (bal_hom_ext
            (cmon_hom_compose (rt_smul E1 EE t)
                              (lt_smul E (bm_left E1) r))
            (cmon_hom_compose (lt_smul E (bm_left E1) r)
                              (rt_smul E1 EE t)) _ x).
  intros e e1; reflexivity.
Qed.

Definition BimodTensorBimod : Bimodule R T :=
  @Build_Bimodule R T btb_left
    (fun x t => rm_smul btb_right t x)
    btb_rsmul_respects
    (fun x y t => rm_smul_distr_l btb_right t x y)
    (fun x t t' => rm_smul_distr_r btb_right t t' x)
    (fun x t t' => rm_smul_assoc btb_right t' t x)
    (fun x => rm_smul_one btb_right x)
    btb_compat.

Example btb_bm_left : bm_left BimodTensorBimod = btb_left := eq_refl.

Example btb_carrier :
  rm_ab (bm_left BimodTensorBimod) = BalTensor EE (bm_left E1) := eq_refl.

Example btb_left_gen (r : RC)
  (e : carrier (cmon_setoid (rm_ab (bm_left E))))
  (e1 : carrier (cmon_setoid (rm_ab (bm_left E1)))) :
  rm_smul (bm_left BimodTensorBimod) r
    (@bs_gen S EE (bm_left E1) e e1)
    = @bs_gen S EE (bm_left E1) (rm_smul (bm_left E) r e) e1 := eq_refl.

Example btb_right_gen (t : TC)
  (e : carrier (cmon_setoid (rm_ab (bm_left E))))
  (e1 : carrier (cmon_setoid (rm_ab (bm_left E1)))) :
  bm_rsmul BimodTensorBimod (@bs_gen S EE (bm_left E1) e e1) t
    = @bs_gen S EE (bm_left E1) e (bm_rsmul E1 e1 t) := eq_refl.

End BimoduleTensorBimodule.

Arguments btb_left {R S T} E E1.
Arguments btb_right {R S T} E E1.
Arguments BimodTensorBimod {R S T} E E1.

(* * *** Mac Lane part (c): the composite adjunction / * *** Mac Lane 部分 (c)：复合伴随 *)

Section BimoduleAdjunctionComposite.

Context {R S T : RingObject}.
Context (E : Bimodule R S).
Context (E1 : Bimodule S T).

Local Notation EE := (bimodule_right_RMod E).

(*
 Adjunction/Compose.v, applied.  Nothing is re-proved: the composite
 of two hom-setoid bijections is one, and all four naturality fields are
 that file's. 

 --------
 Adjunction/Compose.v，已应用。没有重新证明：两个同态集合双射的复合还是一个双射，并且所有四个自然性字段都属于该文件。
*)
Definition bimodule_adjunction_composite :
  (TensorWith E1 ◯ TensorWith E) ⊣ (HomS E ◯ HomS E1) :=
  Adjunction_Compose (bimodule_tensor_hom_adjunction E)
                     (bimodule_tensor_hom_adjunction E1).

Definition bac_unit (N : RModObject (Ring_op R)) :
  N ~{ModR R}~> HomSObj E (HomSObj E1 (RTensor E1 (RTensor E N))) :=
  @unit (ModR T) (ModR R) (TensorWith E1 ◯ TensorWith E)
    (HomS E ◯ HomS E1) bimodule_adjunction_composite N.

Definition bac_counit (M : RModObject (Ring_op T)) :
  RTensor E1 (RTensor E (HomSObj E (HomSObj E1 M))) ~{ModR T}~> M :=
  @counit (ModR T) (ModR R) (TensorWith E1 ◯ TensorWith E)
    (HomS E ◯ HomS E1) bimodule_adjunction_composite M.

(*
 The composite's unit is the DOUBLE generator and its counit DOUBLE
 evaluation, both on the nose. 

 --------
 这个复合体的单位是 DOUBLE 生成器，它的余单位是 DOUBLE 求值，都是直接的。
*)
Example bac_unit_is_gen (N : RModObject (Ring_op R))
  (n : carrier (cmon_setoid (rm_ab N)))
  (e : carrier (cmon_setoid (rm_ab (bm_left E))))
  (e1 : carrier (cmon_setoid (rm_ab (bm_left E1)))) :
  cmon_map (rm_hom (cmon_map (rm_hom
     (cmon_map (rm_hom (bac_unit N)) n)) e)) e1
    = @bs_gen S (RTensor E N) (bm_left E1)
        (@bs_gen R N (bm_left E) n e) e1 := eq_refl.

Example bac_counit_is_eval (M : RModObject (Ring_op T))
  (f : EE ~{ModR S}~> HomSObj E1 M)
  (e : carrier (cmon_setoid (rm_ab (bm_left E))))
  (e1 : carrier (cmon_setoid (rm_ab (bm_left E1)))) :
  cmon_map (rm_hom (bac_counit M))
      (@bs_gen S (RTensor E (HomSObj E (HomSObj E1 M))) (bm_left E1)
         (@bs_gen R (HomSObj E (HomSObj E1 M)) (bm_left E) f e) e1)
    = cmon_map (rm_hom (cmon_map (rm_hom f) e)) e1 := eq_refl.

(*
 Mac Lane's own description of the composite's unit and counit, read
 off Adjunction/Compose.v's own two lemmas. 

 --------
 Mac Lane 对复合体的单位和余单位的描述，可以从 Adjunction/Compose.v 自身的两个引理中读出。
*)
Lemma bac_unit_whiskered (N : RModObject (Ring_op R)) :
  bac_unit N
    ≈ fmap[HomS E]
        (@unit (ModR T) (ModR S) (TensorWith E1) (HomS E1)
           (bimodule_tensor_hom_adjunction E1) (RTensor E N))
      ∘ @unit (ModR S) (ModR R) (TensorWith E) (HomS E)
          (bimodule_tensor_hom_adjunction E) N.
Proof.
  exact (@Adjunction_Compose_unit (ModR S) (ModR R) (ModR T)
           (TensorWith E) (HomS E) (TensorWith E1) (HomS E1)
           (bimodule_tensor_hom_adjunction E)
           (bimodule_tensor_hom_adjunction E1) N).
Qed.

Lemma bac_counit_whiskered (M : RModObject (Ring_op T)) :
  bac_counit M
    ≈ @counit (ModR T) (ModR S) (TensorWith E1) (HomS E1)
        (bimodule_tensor_hom_adjunction E1) M
      ∘ fmap[TensorWith E1]
          (@counit (ModR S) (ModR R) (TensorWith E) (HomS E)
             (bimodule_tensor_hom_adjunction E) (HomSObj E1 M)).
Proof.
  exact (@Adjunction_Compose_counit (ModR S) (ModR R) (ModR T)
           (TensorWith E) (HomS E) (TensorWith E1) (HomS E1)
           (bimodule_tensor_hom_adjunction E)
           (bimodule_tensor_hom_adjunction E1) M).
Qed.

End BimoduleAdjunctionComposite.

Arguments bimodule_adjunction_composite {R S T} E E1.

(* * *** The associativity comparison, and part (c)'s conclusion / * *** 结合律比较，以及(c)部分的结论 *)

(*
 (N ⊗_R E) ⊗_S E1  ≅  N ⊗_R (E ⊗_S E1), in [ModR T].  Both legs are a
 mediator of a mediator: the outer balanced map sends (x, e1) to the
 value at x of the inner one, so every clause below is [bal_hom_ext] at
 one or two levels with a reflexivity on generators at the bottom. 

 --------
 (N ⊗_R E) ⊗_S E1 ≅ N ⊗_R (E ⊗_S E1)，在 [ModR T] 中。两个分支都是一个中介的中介：外部平衡映射将 (x, e1) 发送到内部映射在 x 处的值，因此下面的每个条款在一个或两个层次上都是 [bal_hom_ext]，并且在底层对生成元具有自反性。
*)

Section TensorAssocAt.

Context {R S T : RingObject}.
Context (E : Bimodule R S).
Context (E1 : Bimodule S T).
Context (N : RModObject (Ring_op R)).

Local Notation EE := (bimodule_right_RMod E).
Local Notation BTB := (BimodTensorBimod E E1).
Local Notation EC := (carrier (cmon_setoid (rm_ab (bm_left E)))).
Local Notation E1C := (carrier (cmon_setoid (rm_ab (bm_left E1)))).
Local Notation NC := (carrier (cmon_setoid (rm_ab N))).
Local Notation TGT := (BalTensor N (bm_left BTB)).
Local Notation SRC := (BalTensor (RTensor E N) (bm_left E1)).

(** **** Left to right / **** 从左到右 *)

Program Definition ta_inner (e1 : E1C) :
  BalBiadditive N (bm_left E) TGT := {|
  bal_map := fun n e =>
    @bs_gen R N (bm_left BTB) n (@bs_gen S EE (bm_left E1) e e1)
|}.
Next Obligation.
  intros e1 n n' Hn e e' He.
  refine (be_gen Hn _).
  exact (@be_gen S EE (bm_left E1) e e' e1 e1 He (reflexivity e1)).
Qed.
Next Obligation.
  intros e1 n n' e.
  exact (@be_add_l R N (bm_left BTB) n n'
           (@bs_gen S EE (bm_left E1) e e1)).
Qed.
Next Obligation.
  intros e1 n e e'.
  refine (be_trans _ (@be_add_r R N (bm_left BTB) n
                        (@bs_gen S EE (bm_left E1) e e1)
                        (@bs_gen S EE (bm_left E1) e' e1))).
  refine (be_gen (reflexivity n) _).
  exact (@be_add_l S EE (bm_left E1) e e' e1).
Qed.
Next Obligation.
  intros e1 r n e.
  exact (@be_balance R N (bm_left BTB) r n
           (@bs_gen S EE (bm_left E1) e e1)).
Qed.

Program Definition ta_outer :
  BalBiadditive (RTensor E N) (bm_left E1) TGT := {|
  bal_map := fun x e1 => cmon_map (bal_med (ta_inner e1)) x
|}.
Next Obligation.
  intros x x' Hx e1 e1' He1.
  transitivity (cmon_map (bal_med (ta_inner e1)) x').
  - exact (proper_morphism (cmon_map (bal_med (ta_inner e1))) x x' Hx).
  - refine (bal_hom_ext (bal_med (ta_inner e1))
              (bal_med (ta_inner e1')) _ x').
    intros n e.
    refine (be_gen (reflexivity n) _).
    exact (@be_gen S EE (bm_left E1) e e e1 e1' (reflexivity e) He1).
Qed.
Next Obligation.
  intros x x' e1.
  exact (cmon_map_plus (bal_med (ta_inner e1)) x x').
Qed.
Next Obligation.
  intros x e1 e1'.
  refine (bal_hom_ext (bal_med (ta_inner
             (cmon_plus (rm_ab (bm_left E1)) e1 e1')))
            (ab_hom_add (bal_med (ta_inner e1))
                        (bal_med (ta_inner e1'))) _ x).
  intros n e.
  refine (be_trans _ (@be_add_r R N (bm_left BTB) n
                        (@bs_gen S EE (bm_left E1) e e1)
                        (@bs_gen S EE (bm_left E1) e e1'))).
  refine (be_gen (reflexivity n) _).
  exact (@be_add_r S EE (bm_left E1) e e1 e1').
Qed.
Next Obligation.
  intros s x e1.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med (ta_inner e1)) (rt_smul E N s))
            (bal_med (ta_inner (rm_smul (bm_left E1) s e1))) _ x).
  intros n e.
  refine (be_gen (reflexivity n) _).
  exact (@be_balance S EE (bm_left E1) s e e1).
Qed.

Program Definition ta_to : RTensor E1 (RTensor E N) ~{ModR T}~> RTensor BTB N
  := {| rm_hom := bal_med ta_outer |}.
Next Obligation.
  intros t x.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med ta_outer)
                              (rt_smul E1 (RTensor E N) t))
            (cmon_hom_compose (rt_smul BTB N t) (bal_med ta_outer))
            _ x).
  intros x0 e1; simpl.
  refine (bal_hom_ext (bal_med (ta_inner (bm_rsmul E1 e1 t)))
            (cmon_hom_compose (rt_smul BTB N t)
                              (bal_med (ta_inner e1))) _ x0).
  intros n e; reflexivity.
Qed.

(** **** Right to left / **** 从右到左 *)

Program Definition ta_binner (n : NC) :
  BalBiadditive EE (bm_left E1) SRC := {|
  bal_map := fun e e1 =>
    @bs_gen S (RTensor E N) (bm_left E1) (@bs_gen R N (bm_left E) n e) e1
|}.
Next Obligation.
  intros n e e' He e1 e1' He1.
  refine (be_gen _ He1).
  exact (@be_gen R N (bm_left E) n n e e' (reflexivity n) He).
Qed.
Next Obligation.
  intros n e e' e1.
  refine (be_trans _ (@be_add_l S (RTensor E N) (bm_left E1)
                        (@bs_gen R N (bm_left E) n e)
                        (@bs_gen R N (bm_left E) n e') e1)).
  refine (be_gen _ (reflexivity e1)).
  exact (@be_add_r R N (bm_left E) n e e').
Qed.
Next Obligation.
  intros n e e1 e1'.
  exact (@be_add_r S (RTensor E N) (bm_left E1)
           (@bs_gen R N (bm_left E) n e) e1 e1').
Qed.
Next Obligation.
  intros n s e e1.
  exact (@be_balance S (RTensor E N) (bm_left E1) s
           (@bs_gen R N (bm_left E) n e) e1).
Qed.

Program Definition ta_bouter :
  BalBiadditive N (bm_left BTB) SRC := {|
  bal_map := fun n y => cmon_map (bal_med (ta_binner n)) y
|}.
Next Obligation.
  intros n n' Hn y y' Hy.
  transitivity (cmon_map (bal_med (ta_binner n)) y').
  - exact (proper_morphism (cmon_map (bal_med (ta_binner n))) y y' Hy).
  - refine (bal_hom_ext (bal_med (ta_binner n))
              (bal_med (ta_binner n')) _ y').
    intros e e1.
    refine (be_gen _ (reflexivity e1)).
    exact (@be_gen R N (bm_left E) n n' e e Hn (reflexivity e)).
Qed.
Next Obligation.
  intros n n' y.
  refine (bal_hom_ext (bal_med (ta_binner (cmon_plus (rm_ab N) n n')))
            (ab_hom_add (bal_med (ta_binner n))
                        (bal_med (ta_binner n'))) _ y).
  intros e e1.
  refine (be_trans _ (@be_add_l S (RTensor E N) (bm_left E1)
                        (@bs_gen R N (bm_left E) n e)
                        (@bs_gen R N (bm_left E) n' e) e1)).
  refine (be_gen _ (reflexivity e1)).
  exact (@be_add_l R N (bm_left E) n n' e).
Qed.
Next Obligation.
  intros n y y'.
  exact (cmon_map_plus (bal_med (ta_binner n)) y y').
Qed.
Next Obligation.
  intros r n y.
  refine (bal_hom_ext (bal_med (ta_binner (rm_smul N r n)))
            (cmon_hom_compose (bal_med (ta_binner n))
                              (lt_smul E (bm_left E1) r)) _ y).
  intros e e1.
  refine (be_gen _ (reflexivity e1)).
  exact (@be_balance R N (bm_left E) r n e).
Qed.

Program Definition ta_from : RTensor BTB N ~{ModR T}~> RTensor E1 (RTensor E N)
  := {| rm_hom := bal_med ta_bouter |}.
Next Obligation.
  intros t y.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med ta_bouter) (rt_smul BTB N t))
            (cmon_hom_compose (rt_smul E1 (RTensor E N) t)
                              (bal_med ta_bouter)) _ y).
  intros n y0; simpl.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med (ta_binner n))
                              (rt_smul E1 EE t))
            (cmon_hom_compose (rt_smul E1 (RTensor E N) t)
                              (bal_med (ta_binner n))) _ y0).
  intros e e1; reflexivity.
Qed.

(** **** The two round trips / **** 两次往返 *)

Lemma ta_to_from (y : carrier (cmon_setoid TGT)) :
  cmon_map (rm_hom ta_to) (cmon_map (rm_hom ta_from) y) ≈ y.
Proof.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med ta_outer) (bal_med ta_bouter))
            (@cmon_hom_id TGT) _ y).
  intros n y0.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med ta_outer)
                              (bal_med (ta_binner n)))
            (bal_gen_right N (bm_left BTB) n) _ y0).
  intros e e1; reflexivity.
Qed.

Lemma ta_from_to (x : carrier (cmon_setoid SRC)) :
  cmon_map (rm_hom ta_from) (cmon_map (rm_hom ta_to) x) ≈ x.
Proof.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med ta_bouter) (bal_med ta_outer))
            (@cmon_hom_id SRC) _ x).
  intros x0 e1.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med ta_bouter)
                              (bal_med (ta_inner e1)))
            (bal_gen_left (RTensor E N) (bm_left E1) e1) _ x0).
  intros n e; reflexivity.
Qed.

Program Definition ta_iso :
  @Isomorphism (ModR T) (RTensor E1 (RTensor E N)) (RTensor BTB N) := {|
  to   := ta_to;
  from := ta_from
|}.
Next Obligation. intros y; exact (ta_to_from y). Qed.
Next Obligation. intros x; exact (ta_from_to x). Qed.

Example ta_to_gen (n : NC) (e : EC) (e1 : E1C) :
  cmon_map (rm_hom ta_to)
      (@bs_gen S (RTensor E N) (bm_left E1)
         (@bs_gen R N (bm_left E) n e) e1)
    = @bs_gen R N (bm_left BTB) n (@bs_gen S EE (bm_left E1) e e1)
  := eq_refl.

Example ta_from_gen (n : NC) (e : EC) (e1 : E1C) :
  cmon_map (rm_hom ta_from)
      (@bs_gen R N (bm_left BTB) n (@bs_gen S EE (bm_left E1) e e1))
    = @bs_gen S (RTensor E N) (bm_left E1)
        (@bs_gen R N (bm_left E) n e) e1 := eq_refl.

End TensorAssocAt.

(* * *** Extensionality at the double tensor, and the natural comparison / * *** 双张量的外延性，以及自然比较 *)

Section TensorAssocNatural.

Context {R S T : RingObject}.
Context (E : Bimodule R S).
Context (E1 : Bimodule S T).

Local Notation EE := (bimodule_right_RMod E).
Local Notation BTB := (BimodTensorBimod E E1).

(*
 Two homomorphisms out of (N ⊗_R E) ⊗_S E1 agreeing on the DOUBLE
 generators agree, and dually out of N ⊗_R (E ⊗_S E1).  Each is
 [bal_hom_ext] applied twice, the inner application through the
 one-variable readings of the generator former. 

 --------
 两个从 (N ⊗_R E) ⊗_S E1 出发的同态在双重生成元上相符合，则它们相同，反之亦然，从 N ⊗_R (E ⊗_S E1) 出发亦然。每个都被 [bal_hom_ext] 应用两次，内部应用通过生成元原构造的单变量读取得出。
*)
Lemma ta_double_ext (N : RModObject (Ring_op R)) (A : AbObject)
  (u v : AbHom (BalTensor (RTensor E N) (bm_left E1)) A) :
  (∀ n e e1,
      cmon_map u (@bs_gen S (RTensor E N) (bm_left E1)
                    (@bs_gen R N (bm_left E) n e) e1)
        ≈ cmon_map v (@bs_gen S (RTensor E N) (bm_left E1)
                        (@bs_gen R N (bm_left E) n e) e1)) →
  ∀ x, cmon_map u x ≈ cmon_map v x.
Proof.
  intros H x.
  refine (bal_hom_ext u v _ x).
  intros x0 e1.
  refine (bal_hom_ext
            (cmon_hom_compose u
               (bal_gen_left (RTensor E N) (bm_left E1) e1))
            (cmon_hom_compose v
               (bal_gen_left (RTensor E N) (bm_left E1) e1)) _ x0).
  intros n e; exact (H n e e1).
Qed.

Lemma ta_double_ext_r (N : RModObject (Ring_op R)) (A : AbObject)
  (u v : AbHom (BalTensor N (bm_left BTB)) A) :
  (∀ n e e1,
      cmon_map u (@bs_gen R N (bm_left BTB) n
                    (@bs_gen S EE (bm_left E1) e e1))
        ≈ cmon_map v (@bs_gen R N (bm_left BTB) n
                        (@bs_gen S EE (bm_left E1) e e1))) →
  ∀ y, cmon_map u y ≈ cmon_map v y.
Proof.
  intros H y.
  refine (bal_hom_ext u v _ y).
  intros n y0.
  refine (bal_hom_ext
            (cmon_hom_compose u (bal_gen_right N (bm_left BTB) n))
            (cmon_hom_compose v (bal_gen_right N (bm_left BTB) n))
            _ y0).
  intros e e1; exact (H n e e1).
Qed.

(*
 THE COMPARISON.  [≈] at a functor category is Theory/Functor.v's
 [Functor_Setoid]: a family of isomorphisms together with the coherence
 square, and both halves are supplied here. 

 --------
 比较。在函子范畴中的 [≈] 是 Theory/Functor.v 的
 [Functor_Setoid]：一族同构及其相容性方形，这里提供了两个部分。
*)
Definition tensor_assoc_iso :
  (TensorWith E1 ◯ TensorWith E : ModR R ⟶ ModR T)
    ≈ TensorWith (BimodTensorBimod E E1).
Proof.
  exists (fun N => ta_iso E E1 N).
  intros N N' f x.
  refine (ta_double_ext N _
            (rm_hom (fmap[TensorWith E1 ◯ TensorWith E] f))
            (rm_hom (from (ta_iso E E1 N')
                     ∘ fmap[TensorWith BTB] f
                     ∘ to (ta_iso E E1 N))) _ x).
  intros n e e1; reflexivity.
Defined.

End TensorAssocNatural.

Arguments tensor_assoc_iso {R S T} E E1.

(* * *** Transporting an adjunction along an isomorphism of left adjoints / * *** 沿着左伴随的同构传递伴随 *)

(*
 [adjunction_along_left_iso] — a functor naturally isomorphic to a left
 adjoint is a left adjoint with the SAME right adjoint — was built here
 for part (c) as its first consumer and moved, verbatim and still
 [Defined] (plus a section-local [Obligation Tactic := idtac], this
 file's setting), to the end of Theory/Adjunction.v by #431, its second
 consumer; [aali_cell], [aali_iso], [aali_to_is_transpose] moved too. 

 --------
 [adjunction_along_left_iso] — 一个函子自然同构于一个左伴随函子，即具有相同右伴随函子的左伴随函子 — 在这里为部分 (c) 构建了它的第一个使用者，并逐字移动到 Theory/Adjunction.v 的末尾（仍为 [Defined]，加上一个部分局部 [Obligation Tactic := idtac]，即本文件的设置），通过 #431，作为它的第二个使用者；[aali_cell]、[aali_iso]、[aali_to_is_transpose] 也进行了移动。
*)

(* * *** Mac Lane's “describe the composite” / * *** 马克·莱恩的“描述复合” *)

Section BimoduleCompositeConclusion.

Context {R S T : RingObject}.
Context (E : Bimodule R S).
Context (E1 : Bimodule S T).

(*
 The composite adjunction IS the adjunction of the tensor of the two
 bimodules, up to the natural isomorphism above — on the left by
 transport, and then on the right by uniqueness of right adjoints. 

 --------
 复合伴随是两个双模的张量的伴随，上述自然同构下——先通过左侧的迁移，然后通过右伴随的唯一性在右侧。
*)
Definition bimodule_tensor_bimod_adjunction :
  TensorWith (BimodTensorBimod E E1) ⊣ (HomS E ◯ HomS E1) :=
  adjunction_along_left_iso
    (symmetry (tensor_assoc_iso E E1))
    (bimodule_adjunction_composite E E1).

Definition bimodule_hom_composite_iso :
  (HomS E ◯ HomS E1 : ModR T ⟶ ModR R)
    ≈ HomS (BimodTensorBimod E E1) :=
  right_adjoint_iso (TensorWith (BimodTensorBimod E E1))
    (HomS E ◯ HomS E1) (HomS (BimodTensorBimod E E1))
    bimodule_tensor_bimod_adjunction
    (bimodule_tensor_hom_adjunction (BimodTensorBimod E E1)).

(*
 The transported transpose is the composite's own, precomposed with
 the comparison; on a generator the comparison is [ta_from]. 

 --------
 传递转置是复合本身的，与比较预组合；在生成器上比较是 [ta_from]。
*)
Example btba_to_is_transposed (N : RModObject (Ring_op R))
  (M : RModObject (Ring_op T))
  (g : RTensor (BimodTensorBimod E E1) N ~{ModR T}~> M) :
  to (@adj (ModR T) (ModR R) (TensorWith (BimodTensorBimod E E1))
        (HomS E ◯ HomS E1) bimodule_tensor_bimod_adjunction N M) g
    = to (@adj (ModR T) (ModR R) (TensorWith E1 ◯ TensorWith E)
            (HomS E ◯ HomS E1) (bimodule_adjunction_composite E E1) N M)
        (g ∘ from (aali_cell (symmetry (tensor_assoc_iso E E1)) N))
  := eq_refl.

End BimoduleCompositeConclusion.

Arguments bimodule_tensor_bimod_adjunction {R S T} E E1.
Arguments bimodule_hom_composite_iso {R S T} E E1.

(* * ** E. The left-module mirror, and Riehl's Corollary 4.6.10 / * ** E. 左模镜像，以及Riehl的推论4.6.10 *)

(*
 Riehl, “Category Theory in Context”, §4.6 Corollary 4.6.10, printed
 p. 169: for an R-S bimodule M the functor M ⊗_S − is right exact,
 because Corollary 4.6.9 makes a left adjoint between abelian
 categories right exact.  The adjunction it needs is the LEFT-module
 one, S-Mod ⇄ R-Mod, and it is §B read on the other side: the same
 balanced tensor of §A, with the residual action taken from E's LEFT
 R-module structure and the hom-module translated through E's RIGHT
 S-action. 

 --------
 Riehl，《范畴论的语境》，§4.6 推论 4.6.10，印刷第 169 页：对于一个 R-S 双模 M，函子 M ⊗_S − 是右正合的，因为推论 4.6.9 使阿贝尔范畴之间的左伴随函子是右正合的。所需的伴随关系是左模的，即 S-Mod ⇄ R-Mod，并且在 §B 中在另一边阅读：与 §A 中相同的平衡张量，其中剩余作用取自 E 的左 R-模结构，且同构模通过 E 的右 S-作用进行转换。
*)

(* Multiplication by a scalar as an endomorphism of the underlying group, over an ARBITRARY ring. [bth_lmul] of §B is its instance at an opposite ring, and is left as it stands. / 作为基础群的自同态的标量乘法，在任意环上。§B 中的 [bth_lmul] 是其在对偶环上的实例，并保持原样。 *)
Program Definition rmod_lmul {X : RingObject} (M : RModObject X)
  (x : carrier (rig_setoid (ring_rig X))) :
  AbHom (rm_ab M) (rm_ab M) := {|
  cmon_map := {| morphism := fun m => rm_smul M x m |}
|}.
Next Obligation.
  intros X M x m m' Hm.
  exact (rm_smul_respects M x x (reflexivity x) m m' Hm).
Qed.
Next Obligation. intros X M x; simpl; exact (rm_smul_zero_r M x). Qed.
Next Obligation.
  intros X M x m m'; simpl; exact (rm_smul_distr_l M x m m').
Qed.

Section BimoduleLeftTensorHom.

Context {R S : RingObject}.
Context (E : Bimodule R S).

Local Notation RC := (carrier (rig_setoid (ring_rig R))).
Local Notation SC := (carrier (rig_setoid (ring_rig S))).
Local Notation EC := (carrier (cmon_setoid (rm_ab (bm_left E)))).
Local Notation EE := (bimodule_right_RMod E).

(** *** The functor E ⊗_S − / *** 函子 E ⊗_S − *)

Program Definition lt_map_bal {N N' : RModObject S} (f : RModHom N N') :
  BalBiadditive EE N (BalTensor EE N') := {|
  bal_map := fun e n => bs_gen e (cmon_map (rm_hom f) n)
|}.
Next Obligation.
  intros N N' f e e' He n n' Hn.
  refine (be_gen He _).
  exact (proper_morphism (cmon_map (rm_hom f)) n n' Hn).
Qed.
Next Obligation.
  intros N N' f e e' n.
  exact (@be_add_l S EE N' e e' (cmon_map (rm_hom f) n)).
Qed.
Next Obligation.
  intros N N' f e n n'.
  refine (be_trans _ (@be_add_r S EE N' e
                        (cmon_map (rm_hom f) n)
                        (cmon_map (rm_hom f) n'))).
  refine (be_gen (reflexivity e) _).
  exact (cmon_map_plus (rm_hom f) n n').
Qed.
Next Obligation.
  intros N N' f x e n.
  refine (be_trans (@be_balance S EE N' x e (cmon_map (rm_hom f) n)) _).
  refine (be_gen (reflexivity e) _).
  exact (symmetry (rm_map_smul f x n)).
Qed.

Definition lt_map_ab {N N' : RModObject S} (f : RModHom N N') :
  AbHom (BalTensor EE N) (BalTensor EE N') :=
  bal_med (lt_map_bal f).

Program Definition LTensorMap {N N' : RModObject S}
  (f : N ~{RMod S}~> N') : LTensor E N ~{RMod R}~> LTensor E N' := {|
  rm_hom := lt_map_ab f
|}.
Next Obligation.
  intros N N' f r x.
  refine (bal_hom_ext
            (cmon_hom_compose (lt_map_ab f) (lt_smul E N r))
            (cmon_hom_compose (lt_smul E N' r) (lt_map_ab f)) _ x).
  intros e n; reflexivity.
Qed.

Program Definition LTensorWith : RMod S ⟶ RMod R := {|
  fobj := LTensor E;
  fmap := @LTensorMap
|}.
Next Obligation.
  intros N N' f g Hfg x.
  refine (bal_hom_ext (lt_map_ab f) (lt_map_ab g) _ x).
  intros e n.
  refine (be_gen (reflexivity e) _).
  exact (Hfg n).
Qed.
Next Obligation.
  intros N x.
  refine (bal_hom_ext (lt_map_ab (@id (RMod S) N))
            (@cmon_hom_id (BalTensor EE N)) _ x).
  intros e n; reflexivity.
Qed.
Next Obligation.
  intros N N' N'' f g x.
  refine (bal_hom_ext (lt_map_ab (f ∘ g))
            (cmon_hom_compose (lt_map_ab f) (lt_map_ab g)) _ x).
  intros e n; reflexivity.
Qed.

Example ltw_fobj (N : RModObject S) : fobj[LTensorWith] N = LTensor E N
  := eq_refl.

Example ltw_fmap_gen {N N' : RModObject S} (f : N ~{RMod S}~> N')
  (e : EC) (n : carrier (cmon_setoid (rm_ab N))) :
  cmon_map (rm_hom (fmap[LTensorWith] f))
      (@bs_gen S EE N e n)
    = @bs_gen S EE N' e (cmon_map (rm_hom f) n) := eq_refl.

(* * *** hom_R(E, M) and its left S-action / * *** hom_R(E, M) 及其左 S-作用 *)

Definition lhs_group (M : RModObject R) : AbObject :=
  hom_ab (RMod_AbEnriched R) (bm_left E) M.

Example lhs_group_carrier (M : RModObject R) :
  carrier (cmon_setoid (lhs_group M)) = (bm_left E ~{RMod R}~> M)
  := eq_refl.

(*
 (s · f)(e) = f (e ⊲ s): translation through the RIGHT action, the
 mirror of §B's (f ⊲ r)(e) = f (r · e). 

 --------
 (s · f)(e) = f (e ⊲ s)：通过右作用进行平移，§B 中 (f ⊲ r)(e) = f (r · e) 的镜像。
*)
Program Definition lhs_act (M : RModObject R) (s : SC)
  (f : bm_left E ~{RMod R}~> M) : bm_left E ~{RMod R}~> M := {|
  rm_hom := {| cmon_map := {| morphism := fun e =>
    cmon_map (rm_hom f) (bm_rsmul E e s) |} |}
|}.
Next Obligation.
  intros M s f e e' He.
  exact (proper_morphism (cmon_map (rm_hom f)) _ _
           (bm_rsmul_respects E e e' He s s (reflexivity s))).
Qed.
Next Obligation.
  intros M s f; simpl.
  transitivity (cmon_map (rm_hom f) (cmon_zero (rm_ab (bm_left E)))).
  - exact (proper_morphism (cmon_map (rm_hom f)) _ _
             (rm_smul_zero_r (bimodule_right_RMod E) s)).
  - exact (cmon_map_zero (rm_hom f)).
Qed.
Next Obligation.
  intros M s f e e'; simpl.
  transitivity (cmon_map (rm_hom f)
                  (cmon_plus (rm_ab (bm_left E))
                     (bm_rsmul E e s) (bm_rsmul E e' s))).
  - exact (proper_morphism (cmon_map (rm_hom f)) _ _
             (bm_rsmul_distr_l E e e' s)).
  - exact (cmon_map_plus (rm_hom f) _ _).
Qed.
Next Obligation.
  (* the ONLY use of [bm_compat] in this block / 在此区块中 [bm_compat] 的唯一用途 *)
  intros M s f r e; simpl.
  transitivity (cmon_map (rm_hom f)
                  (rm_smul (bm_left E) r (bm_rsmul E e s))).
  - exact (proper_morphism (cmon_map (rm_hom f)) _ _
             (bm_compat E r e s)).
  - exact (rm_map_smul f r (bm_rsmul E e s)).
Qed.

Example lhs_act_at (M : RModObject R) (s : SC)
  (f : bm_left E ~{RMod R}~> M) (e : EC) :
  cmon_map (rm_hom (lhs_act M s f)) e
    = cmon_map (rm_hom f) (bm_rsmul E e s) := eq_refl.

Lemma lhs_act_respects (M : RModObject R) :
  Proper (equiv ==> equiv ==> equiv) (lhs_act M).
Proof.
  intros s s' Hs f g Hfg e; simpl.
  transitivity (cmon_map (rm_hom f) (bm_rsmul E e s')).
  - exact (proper_morphism (cmon_map (rm_hom f)) _ _
             (bm_rsmul_respects E e e (reflexivity e) s s' Hs)).
  - exact (Hfg _).
Qed.

Lemma lhs_act_distr_l (M : RModObject R) (s : SC)
  (f g : bm_left E ~{RMod R}~> M) :
  lhs_act M s (cmon_plus (lhs_group M) f g)
    ≈ cmon_plus (lhs_group M) (lhs_act M s f) (lhs_act M s g).
Proof. intro e; reflexivity. Qed.

Lemma lhs_act_distr_r (M : RModObject R) (s s' : SC)
  (f : bm_left E ~{RMod R}~> M) :
  lhs_act M (rig_add (ring_rig S) s s') f
    ≈ cmon_plus (lhs_group M) (lhs_act M s f) (lhs_act M s' f).
Proof.
  intro e; simpl.
  transitivity (cmon_map (rm_hom f)
                  (cmon_plus (rm_ab (bm_left E))
                     (bm_rsmul E e s) (bm_rsmul E e s'))).
  - exact (proper_morphism (cmon_map (rm_hom f)) _ _
             (bm_rsmul_distr_r E e s s')).
  - exact (cmon_map_plus (rm_hom f) _ _).
Qed.

Lemma lhs_act_assoc (M : RModObject R) (s s' : SC)
  (f : bm_left E ~{RMod R}~> M) :
  lhs_act M (rig_mul (ring_rig S) s s') f
    ≈ lhs_act M s (lhs_act M s' f).
Proof.
  intro e; simpl.
  exact (proper_morphism (cmon_map (rm_hom f)) _ _
           (bm_rsmul_assoc E e s s')).
Qed.

Lemma lhs_act_one (M : RModObject R) (f : bm_left E ~{RMod R}~> M) :
  lhs_act M (rig_one (ring_rig S)) f ≈ f.
Proof.
  intro e; simpl.
  exact (proper_morphism (cmon_map (rm_hom f)) _ _ (bm_rsmul_one E e)).
Qed.

Definition LHomSObj (M : RModObject R) : RModObject S :=
  @Build_RModObject S
    (lhs_group M)
    (lhs_act M)
    (lhs_act_respects M)
    (lhs_act_distr_l M)
    (lhs_act_distr_r M)
    (lhs_act_assoc M)
    (lhs_act_one M).

Program Definition lhs_map_ab {M M' : RModObject R}
  (g : M ~{RMod R}~> M') : AbHom (lhs_group M) (lhs_group M') := {|
  cmon_map := {| morphism := fun f =>
    (rmod_hom_compose g f : bm_left E ~{RMod R}~> M') |}
|}.
Next Obligation.
  intros M M' g f f' Hf e; simpl.
  unfold Basics.compose.
  exact (proper_morphism (cmon_map (rm_hom g)) _ _ (Hf e)).
Qed.
Next Obligation.
  intros M M' g e; simpl; exact (cmon_map_zero (rm_hom g)).
Qed.
Next Obligation.
  intros M M' g f f' e; simpl; exact (cmon_map_plus (rm_hom g) _ _).
Qed.

Program Definition LHomSMap {M M' : RModObject R}
  (g : M ~{RMod R}~> M') : LHomSObj M ~{RMod S}~> LHomSObj M' := {|
  rm_hom := lhs_map_ab g
|}.
Next Obligation. intros M M' g s f e; reflexivity. Qed.

Program Definition LHomS : RMod R ⟶ RMod S := {|
  fobj := LHomSObj;
  fmap := @LHomSMap
|}.
Next Obligation. intros M M' g g' Hg f e; simpl; exact (Hg _). Qed.
Next Obligation. intros M f e; reflexivity. Qed.
Next Obligation. intros M M' M'' g g' f e; reflexivity. Qed.

End BimoduleLeftTensorHom.

(* * *** The left-module tensor-hom adjunction / * *** 左模张量-宿同余伴随 *)

Section BimoduleLeftAdjunction.

Context {R S : RingObject}.
Context (E : Bimodule R S).

Local Notation RC := (carrier (rig_setoid (ring_rig R))).
Local Notation SC := (carrier (rig_setoid (ring_rig S))).
Local Notation EC := (carrier (cmon_setoid (rm_ab (bm_left E)))).
Local Notation EE := (bimodule_right_RMod E).

Program Definition blt_to_inner {N : RModObject S} {M : RModObject R}
  (g : LTensor E N ~{RMod R}~> M)
  (n : carrier (cmon_setoid (rm_ab N))) :
  bm_left E ~{RMod R}~> M := {|
  rm_hom := {| cmon_map := {| morphism := fun e =>
    cmon_map (rm_hom g) (@bs_gen S EE N e n) |} |}
|}.
Next Obligation.
  intros N M g n e e' He.
  refine (proper_morphism (cmon_map (rm_hom g)) _ _ _).
  exact (@be_gen S EE N e e' n n He (reflexivity n)).
Qed.
Next Obligation.
  intros N M g n; simpl.
  transitivity (cmon_map (rm_hom g) (cmon_zero (BalTensor EE N))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (bal_gen_zero_l EE N n)).
  - exact (cmon_map_zero (rm_hom g)).
Qed.
Next Obligation.
  intros N M g n e e'; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_plus (BalTensor EE N)
                     (@bs_gen S EE N e n) (@bs_gen S EE N e' n))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (@be_add_l S EE N e e' n)).
  - exact (cmon_map_plus (rm_hom g) _ _).
Qed.
Next Obligation.
  (* (r · e) ⊗ n IS r ·[LTensor] (e ⊗ n) on the nose. / (r · e) ⊗ n 就是 r · [LTensor] (e ⊗ n) 的精确对应。 *)
  intros N M g n r e.
  exact (rm_map_smul g r (@bs_gen S EE N e n)).
Qed.

Program Definition blt_to_ab {N : RModObject S} {M : RModObject R}
  (g : LTensor E N ~{RMod R}~> M) :
  AbHom (rm_ab N) (lhs_group E M) := {|
  cmon_map := {| morphism := fun n => blt_to_inner g n |}
|}.
Next Obligation.
  intros N M g n n' Hn e; simpl.
  refine (proper_morphism (cmon_map (rm_hom g)) _ _ _).
  exact (@be_gen S EE N e e n n' (reflexivity e) Hn).
Qed.
Next Obligation.
  intros N M g e; simpl.
  transitivity (cmon_map (rm_hom g) (cmon_zero (BalTensor EE N))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (bal_gen_zero_r EE N e)).
  - exact (cmon_map_zero (rm_hom g)).
Qed.
Next Obligation.
  intros N M g n n' e; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_plus (BalTensor EE N)
                     (@bs_gen S EE N e n) (@bs_gen S EE N e n'))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (@be_add_r S EE N e n n')).
  - exact (cmon_map_plus (rm_hom g) _ _).
Qed.

(* The forward transpose is S-linear BECAUSE of the balance rule. / 前向转置是S线性的，因为平衡规则。 *)
Program Definition blt_to {N : RModObject S} {M : RModObject R}
  (g : LTensor E N ~{RMod R}~> M) : N ~{RMod S}~> LHomSObj E M := {|
  rm_hom := blt_to_ab g
|}.
Next Obligation.
  intros N M g s n e; simpl.
  refine (proper_morphism (cmon_map (rm_hom g)) _ _ _).
  exact (symmetry (@be_balance S EE N s e n)).
Qed.

Program Definition blt_from_bal {N : RModObject S} {M : RModObject R}
  (h : N ~{RMod S}~> LHomSObj E M) :
  BalBiadditive EE N (rm_ab M) := {|
  bal_map := fun e n => cmon_map (rm_hom (cmon_map (rm_hom h) n)) e
|}.
Next Obligation.
  intros N M h e e' He n n' Hn.
  transitivity (cmon_map (rm_hom (cmon_map (rm_hom h) n)) e').
  - exact (proper_morphism (cmon_map (rm_hom (cmon_map (rm_hom h) n)))
             e e' He).
  - exact (proper_morphism (cmon_map (rm_hom h)) n n' Hn e').
Qed.
Next Obligation.
  intros N M h e e' n.
  exact (cmon_map_plus (rm_hom (cmon_map (rm_hom h) n)) e e').
Qed.
Next Obligation.
  intros N M h e n n'.
  exact (cmon_map_plus (rm_hom h) n n' e).
Qed.
Next Obligation.
  (* Balance is [h]'s own S-linearity read at e. / 余额是 [h] 在 e 时自己 S 线性的读数。 *)
  intros N M h s e n.
  exact (symmetry (rm_map_smul h s n e)).
Qed.

Program Definition blt_from {N : RModObject S} {M : RModObject R}
  (h : N ~{RMod S}~> LHomSObj E M) : LTensor E N ~{RMod R}~> M := {|
  rm_hom := bal_med (blt_from_bal h)
|}.
Next Obligation.
  intros N M h r x.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med (blt_from_bal h))
                              (lt_smul E N r))
            (cmon_hom_compose (rmod_lmul M r)
                              (bal_med (blt_from_bal h))) _ x).
  intros e n.
  exact (rm_map_smul (cmon_map (rm_hom h) n) r e).
Qed.

Example blt_to_at {N : RModObject S} {M : RModObject R}
  (g : LTensor E N ~{RMod R}~> M)
  (n : carrier (cmon_setoid (rm_ab N))) (e : EC) :
  cmon_map (rm_hom (cmon_map (rm_hom (blt_to g)) n)) e
    = cmon_map (rm_hom g) (@bs_gen S EE N e n) := eq_refl.

Example blt_from_at {N : RModObject S} {M : RModObject R}
  (h : N ~{RMod S}~> LHomSObj E M)
  (n : carrier (cmon_setoid (rm_ab N))) (e : EC) :
  cmon_map (rm_hom (blt_from h)) (@bs_gen S EE N e n)
    = cmon_map (rm_hom (cmon_map (rm_hom h) n)) e := eq_refl.

Program Definition blt_adj (N : RModObject S) (M : RModObject R) :
  @Isomorphism Sets
    {| carrier := LTensor E N ~{RMod R}~> M;
       is_setoid := @homset (RMod R) (LTensor E N) M |}
    {| carrier := N ~{RMod S}~> LHomSObj E M;
       is_setoid := @homset (RMod S) N (LHomSObj E M) |} := {|
  to   := {| morphism := fun g => blt_to g |};
  from := {| morphism := fun h => blt_from h |}
|}.
Next Obligation. intros N M g g' Hg n e; exact (Hg _). Qed.
Next Obligation.
  intros N M h h' Hh x.
  refine (bal_hom_ext (bal_med (blt_from_bal h))
                      (bal_med (blt_from_bal h')) _ x).
  intros e n; exact (Hh n e).
Qed.
Next Obligation. intros N M h n e; reflexivity. Qed.
Next Obligation.
  intros N M g x.
  refine (bal_hom_ext (bal_med (blt_from_bal (blt_to g)))
                      (rm_hom g) _ x).
  intros e n; reflexivity.
Qed.

Definition bimodule_left_tensor_hom_adjunction :
  LTensorWith E ⊣ LHomS E.
Proof using E R S.
  unshelve eapply (@Build_Adjunction' (RMod R) (RMod S)
                     (LTensorWith E) (LHomS E) blt_adj).
  - intros N N' M f g n e; reflexivity.
  - intros N M M' f g n e; reflexivity.
Defined.

Definition blt_unit (N : RModObject S) :
  N ~{RMod S}~> LHomSObj E (LTensor E N) :=
  @unit (RMod R) (RMod S) (LTensorWith E) (LHomS E)
    bimodule_left_tensor_hom_adjunction N.

Definition blt_counit (M : RModObject R) :
  LTensor E (LHomSObj E M) ~{RMod R}~> M :=
  @counit (RMod R) (RMod S) (LTensorWith E) (LHomS E)
    bimodule_left_tensor_hom_adjunction M.

Example blt_unit_is_gen (N : RModObject S)
  (n : carrier (cmon_setoid (rm_ab N))) (e : EC) :
  cmon_map (rm_hom (cmon_map (rm_hom (blt_unit N)) n)) e
    = @bs_gen S EE N e n := eq_refl.

Example blt_counit_is_eval (M : RModObject R)
  (f : bm_left E ~{RMod R}~> M) (e : EC) :
  cmon_map (rm_hom (blt_counit M))
      (@bs_gen S EE (LHomSObj E M) e f)
    = cmon_map (rm_hom f) e := eq_refl.

End BimoduleLeftAdjunction.

(* * *** Riehl 4.6.10, at the strength the tree can state / * *** Riehl 4.6.10，在树可以说明的强度下 *)

(*
 Riehl's conclusion is right exactness; a whole-tree sweep for
 right-exactness or finite-colimit vocabulary returns three lines, all
 prose in unrelated headers, so there is no [RightExact] and no
 [PreservesFiniteColimits] to inhabit.  What IS available is
 Structure/Limit/Preservation.v's [PreservesAllColimits] through
 Adjunction/Continuity.v, and preservation of ALL colimits is
 STRICTLY STRONGER than right exactness — it is not the same
 statement, and the difference is disclosed rather than glossed.
 Riehl's Corollary 4.6.9 additivity clause is NOT delivered. 

 --------
 Riehl 的结论是右精确；对右精确性或有限余极限词汇的全树扫描返回三行，所有内容都是无关标题下的散文，因此没有 [RightExact]，也没有 [PreservesFiniteColimits] 可以存在。可用的是 Structure/Limit/Preservation.v 中的 [PreservesAllColimits] 通过 Adjunction/Continuity.v，并且对所有余极限的保持严格比右精确性更强——它不是同一个陈述，其差异是被揭示而不是被掩盖的。Riehl 的推论 4.6.9 的可加性条款未被实现。
*)

Definition bimodule_left_tensor_preserves_colimits
  {R S : RingObject} (E : Bimodule R S) :
  PreservesAllColimits (LTensorWith E) :=
  left_adjoint_preserves_colimits (bimodule_left_tensor_hom_adjunction E).

Definition bimodule_tensor_preserves_colimits
  {R S : RingObject} (E : Bimodule R S) :
  PreservesAllColimits (TensorWith E) :=
  left_adjoint_preserves_colimits (bimodule_tensor_hom_adjunction E).

(*
 The composite of part (c) is a left adjoint too, so it preserves all
 colimits by the same one-line reading. 

 --------
 部分(c)的复合也是一个左伴随，因此通过相同的单行理解它保留所有余极限。
*)
Definition bimodule_tensor_bimod_preserves_colimits
  {R S T : RingObject} (E : Bimodule R S) (E1 : Bimodule S T) :
  PreservesAllColimits (TensorWith (BimodTensorBimod E E1)) :=
  left_adjoint_preserves_colimits (bimodule_tensor_bimod_adjunction E E1).

(*
 [Arguments] declared inside a [Section] do not survive its [End], so
 §C's two settings for the projections of [BimodHom] are gone outside
 it; they are restored here, before §F's first use. 

 --------
 在 [Section] 中声明的 [Arguments] 无法在其 [End] 中存活，因此 [BimodHom] 的投影的 §C 的两个设置在它之外消失；它们在此恢复，在 §F 第一次使用之前。
*)
Arguments bh_hom {R S E E'} b.
Arguments bh_right {R S E E'} b m s.

(* * ** F. The second closure, and the two-variable adjunction / * ** F. 第二闭包，以及两变量伴随 *)

(*
 Riehl, “Category Theory in Context”, §4.4 Definition 4.4.7: a
 two-variable adjunction is a triple F : A × B → C, G : A^op × C → B,
 H : B^op × C → A with C(F(a,b),c) ≅ B(b,G(a,c)) ≅ A(a,H(b,c)).  For
 [BimodTensor] the first leg is §C's [bimodule_parametrized_adjunction]
 and the bifunctor G is [bimodule_hom_bifunctor]; what is added here is
 the SECOND closure, the right adjoint of ⊗ in the MODULE variable, and
 with it the third leg through Adjunction/Parameter.v's
 [mutually_right_adjoint].

 The second closure of a bimodule tensor is again a BIMODULE: for a
 right R-module N and a right S-module M the abelian group of group
 homomorphisms N → M carries a left R-action (r · f)(n) = f (n ⊲ r) and
 a right S-action (f ⊲ s)(n) = (f n) ⊲ s, and these commute for a
 reason with no content — both sides send n to (f (n ⊲ r)) ⊲ s. 

 --------
 Riehl，《语境中的范畴论》，§4.4 定义 4.4.7：一个双变量伴随是一组三元组 F : A × B → C, G : A^op × C → B, H : B^op × C → A，使得 C(F(a,b),c) ≅ B(b,G(a,c)) ≅ A(a,H(b,c))。对于 [BimodTensor]，第一段是 §C 的 [bimodule_parametrized_adjunction]，双函子 G 是 [bimodule_hom_bifunctor]；这里增加的是第二个闭包，即在 MODULE 变量中的 ⊗ 的右伴随，并通过 Adjunction/Parameter.v 的 [mutually_right_adjoint] 得到第三段。  

 双模张量的第二个闭包仍然是一个双模：对于一个右 R-模 N 和一个右 S-模 M，群同态 N → M 构成的阿贝尔群带有一个左 R-作用 (r · f)(n) = f(n ⊲ r) 和一个右 S-作用 (f ⊲ s)(n) = (f n) ⊲ s，并且两者交换，原因不重要——两边都将 n 映射为 (f (n ⊲ r)) ⊲ s。
*)

Section HomAbBimodule.

Context {R S : RingObject}.

Local Notation RC := (carrier (rig_setoid (ring_rig R))).
Local Notation SC := (carrier (rig_setoid (ring_rig S))).

Context (N : RModObject (Ring_op R)).
Context (M : RModObject (Ring_op S)).

Definition hab_group : AbObject :=
  hom_ab Ab_AbEnriched (rm_ab N) (rm_ab M).

Example hab_group_carrier :
  carrier (cmon_setoid hab_group) = (rm_ab N ~{Ab}~> rm_ab M) := eq_refl.

Program Definition hab_lact (r : RC) (f : rm_ab N ~{Ab}~> rm_ab M) :
  rm_ab N ~{Ab}~> rm_ab M := {|
  cmon_map := {| morphism := fun n => cmon_map f (rm_smul N r n) |}
|}.
Next Obligation.
  intros r f n n' Hn.
  exact (proper_morphism (cmon_map f) _ _
           (rm_smul_respects N r r (reflexivity r) n n' Hn)).
Qed.
Next Obligation.
  intros r f; simpl.
  transitivity (cmon_map f (cmon_zero (rm_ab N))).
  - exact (proper_morphism (cmon_map f) _ _ (rm_smul_zero_r N r)).
  - exact (cmon_map_zero f).
Qed.
Next Obligation.
  intros r f n n'; simpl.
  transitivity (cmon_map f
                  (cmon_plus (rm_ab N) (rm_smul N r n) (rm_smul N r n'))).
  - exact (proper_morphism (cmon_map f) _ _ (rm_smul_distr_l N r n n')).
  - exact (cmon_map_plus f _ _).
Qed.

Program Definition hab_ract (f : rm_ab N ~{Ab}~> rm_ab M) (s : SC) :
  rm_ab N ~{Ab}~> rm_ab M := {|
  cmon_map := {| morphism := fun n => rm_smul M s (cmon_map f n) |}
|}.
Next Obligation.
  intros f s n n' Hn.
  exact (rm_smul_respects M s s (reflexivity s) _ _
           (proper_morphism (cmon_map f) n n' Hn)).
Qed.
Next Obligation.
  intros f s; simpl.
  transitivity (rm_smul M s (cmon_zero (rm_ab M))).
  - exact (rm_smul_respects M s s (reflexivity s) _ _
             (cmon_map_zero f)).
  - exact (rm_smul_zero_r M s).
Qed.
Next Obligation.
  intros f s n n'; simpl.
  transitivity (rm_smul M s
                  (cmon_plus (rm_ab M) (cmon_map f n) (cmon_map f n'))).
  - exact (rm_smul_respects M s s (reflexivity s) _ _
             (cmon_map_plus f n n')).
  - exact (rm_smul_distr_l M s _ _).
Qed.

Lemma hab_lact_respects : Proper (equiv ==> equiv ==> equiv) hab_lact.
Proof.
  intros r r' Hr f g Hfg n; simpl.
  transitivity (cmon_map f (rm_smul N r' n)).
  - exact (proper_morphism (cmon_map f) _ _
             (rm_smul_respects N r r' Hr n n (reflexivity n))).
  - exact (Hfg _).
Qed.

Lemma hab_lact_distr_l (r : RC) (f g : rm_ab N ~{Ab}~> rm_ab M) :
  hab_lact r (cmon_plus hab_group f g)
    ≈ cmon_plus hab_group (hab_lact r f) (hab_lact r g).
Proof. intro n; reflexivity. Qed.

Lemma hab_lact_distr_r (r r' : RC) (f : rm_ab N ~{Ab}~> rm_ab M) :
  hab_lact (rig_add (ring_rig R) r r') f
    ≈ cmon_plus hab_group (hab_lact r f) (hab_lact r' f).
Proof.
  intro n; simpl.
  transitivity (cmon_map f
                  (cmon_plus (rm_ab N) (rm_smul N r n) (rm_smul N r' n))).
  - exact (proper_morphism (cmon_map f) _ _ (rm_smul_distr_r N r r' n)).
  - exact (cmon_map_plus f _ _).
Qed.

Lemma hab_lact_assoc (r r' : RC) (f : rm_ab N ~{Ab}~> rm_ab M) :
  hab_lact (rig_mul (ring_rig R) r r') f ≈ hab_lact r (hab_lact r' f).
Proof.
  intro n; simpl.
  exact (proper_morphism (cmon_map f) _ _ (rm_smul_assoc N r' r n)).
Qed.

Lemma hab_lact_one (f : rm_ab N ~{Ab}~> rm_ab M) :
  hab_lact (rig_one (ring_rig R)) f ≈ f.
Proof.
  intro n; simpl.
  exact (proper_morphism (cmon_map f) _ _ (rm_smul_one N n)).
Qed.

Definition hab_left : RModObject R :=
  @Build_RModObject R hab_group hab_lact hab_lact_respects
    hab_lact_distr_l hab_lact_distr_r hab_lact_assoc hab_lact_one.

Lemma hab_ract_respects : Proper (equiv ==> equiv ==> equiv) hab_ract.
Proof.
  intros f g Hfg s s' Hs n; simpl.
  exact (rm_smul_respects M s s' Hs _ _ (Hfg n)).
Qed.

Lemma hab_ract_distr_l (f g : rm_ab N ~{Ab}~> rm_ab M) (s : SC) :
  hab_ract (cmon_plus hab_group f g) s
    ≈ cmon_plus hab_group (hab_ract f s) (hab_ract g s).
Proof. intro n; simpl; exact (rm_smul_distr_l M s _ _). Qed.

Lemma hab_ract_distr_r (f : rm_ab N ~{Ab}~> rm_ab M) (s s' : SC) :
  hab_ract f (rig_add (ring_rig S) s s')
    ≈ cmon_plus hab_group (hab_ract f s) (hab_ract f s').
Proof. intro n; simpl; exact (rm_smul_distr_r M s s' _). Qed.

Lemma hab_ract_assoc (f : rm_ab N ~{Ab}~> rm_ab M) (s s' : SC) :
  hab_ract f (rig_mul (ring_rig S) s s')
    ≈ hab_ract (hab_ract f s) s'.
Proof. intro n; simpl; exact (rm_smul_assoc M s' s _). Qed.

Lemma hab_ract_one (f : rm_ab N ~{Ab}~> rm_ab M) :
  hab_ract f (rig_one (ring_rig S)) ≈ f.
Proof. intro n; simpl; exact (rm_smul_one M _). Qed.

(* The compatibility law holds POINTWISE, with no law of either module consumed: both sides send n to (f (n ⊲ r)) ⊲ s. / 兼容性定律逐点成立，两个模块都不被消耗：两边都将 n 发送到 (f (n ⊲ r)) ⊲ s。 *)
Lemma hab_compat (r : RC) (f : rm_ab N ~{Ab}~> rm_ab M) (s : SC) :
  hab_ract (hab_lact r f) s ≈ hab_lact r (hab_ract f s).
Proof. intro n; reflexivity. Qed.

Definition HomAbBimod : Bimodule R S :=
  @Build_Bimodule R S hab_left hab_ract hab_ract_respects
    hab_ract_distr_l hab_ract_distr_r hab_ract_assoc hab_ract_one
    hab_compat.

Example hab_bimod_left_at (r : RC) (f : rm_ab N ~{Ab}~> rm_ab M)
  (n : carrier (cmon_setoid (rm_ab N))) :
  cmon_map (rm_smul (bm_left HomAbBimod) r f) n
    = cmon_map f (rm_smul N r n) := eq_refl.

Example hab_bimod_right_at (f : rm_ab N ~{Ab}~> rm_ab M) (s : SC)
  (n : carrier (cmon_setoid (rm_ab N))) :
  cmon_map (bm_rsmul HomAbBimod f s) n
    = rm_smul M s (cmon_map f n) := eq_refl.

End HomAbBimodule.

Arguments hab_group {R S} N M.
Arguments hab_left {R S} N M.
Arguments HomAbBimod {R S} N M.

(* * *** The second closure as a functor, and the mirror adjunction / * *** 第二闭包作为函子，以及镜像伴随 *)

Section HomAbFunctorSection.

Context {R S : RingObject}.
Context (N : RModObject (Ring_op R)).

Local Notation RC := (carrier (rig_setoid (ring_rig R))).
Local Notation SC := (carrier (rig_setoid (ring_rig S))).
Local Notation NC := (carrier (cmon_setoid (rm_ab N))).

Program Definition hab_map_ab {M M' : RModObject (Ring_op S)}
  (g : M ~{ModR S}~> M') :
  RModHom (hab_left N M) (hab_left N M') := {|
  rm_hom := {| cmon_map := {| morphism := fun f =>
    (cmon_hom_compose (rm_hom g) f : rm_ab N ~{Ab}~> rm_ab M') |} |}
|}.
Next Obligation.
  intros M M' g f f' Hf n; simpl.
  unfold Basics.compose.
  exact (proper_morphism (cmon_map (rm_hom g)) _ _ (Hf n)).
Qed.
Next Obligation.
  intros M M' g n; simpl; exact (cmon_map_zero (rm_hom g)).
Qed.
Next Obligation.
  intros M M' g f f' n; simpl; exact (cmon_map_plus (rm_hom g) _ _).
Qed.
Next Obligation. intros M M' g r f n; reflexivity. Qed.

Program Definition HomAbMap {M M' : RModObject (Ring_op S)}
  (g : M ~{ModR S}~> M') :
  HomAbBimod N M ~{@BimodCat R S}~> HomAbBimod N M' := {|
  bh_hom := hab_map_ab g
|}.
Next Obligation.
  intros M M' g f s n; simpl.
  exact (rm_map_smul g s (cmon_map f n)).
Qed.

Program Definition HomAbFunctor : ModR S ⟶ @BimodCat R S := {|
  fobj := HomAbBimod N;
  fmap := @HomAbMap
|}.
Next Obligation.
  intros M M' g g' Hg f n; simpl; exact (Hg _).
Qed.
Next Obligation. intros M f n; reflexivity. Qed.
Next Obligation. intros M M' M'' g g' f n; reflexivity. Qed.

Example hab_functor_obj (M : RModObject (Ring_op S)) :
  fobj[HomAbFunctor] M = HomAbBimod N M := eq_refl.

(* * *** The bijection: bimodule maps into hom_Ab(N, M) / * *** 双射：从双模映射到 hom_Ab(N, M) *)

Program Definition hbt_to_inner {E : Bimodule R S}
  {M : RModObject (Ring_op S)} (g : RTensor E N ~{ModR S}~> M)
  (e : carrier (cmon_setoid (rm_ab (bm_left E)))) :
  rm_ab N ~{Ab}~> rm_ab M := {|
  cmon_map := {| morphism := fun n =>
    cmon_map (rm_hom g) (@bs_gen R N (bm_left E) n e) |}
|}.
Next Obligation.
  intros E M g e n n' Hn.
  refine (proper_morphism (cmon_map (rm_hom g)) _ _ _).
  exact (@be_gen R N (bm_left E) n n' e e Hn (reflexivity e)).
Qed.
Next Obligation.
  intros E M g e; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_zero (BalTensor N (bm_left E)))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (bal_gen_zero_l N (bm_left E) e)).
  - exact (cmon_map_zero (rm_hom g)).
Qed.
Next Obligation.
  intros E M g e n n'; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_plus (BalTensor N (bm_left E))
                     (@bs_gen R N (bm_left E) n e)
                     (@bs_gen R N (bm_left E) n' e))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (@be_add_l R N (bm_left E) n n' e)).
  - exact (cmon_map_plus (rm_hom g) _ _).
Qed.

Program Definition hbt_to_hom {E : Bimodule R S}
  {M : RModObject (Ring_op S)} (g : RTensor E N ~{ModR S}~> M) :
  RModHom (bm_left E) (hab_left N M) := {|
  rm_hom := {| cmon_map := {| morphism := fun e => hbt_to_inner g e |} |}
|}.
Next Obligation.
  intros E M g e e' He n; simpl.
  refine (proper_morphism (cmon_map (rm_hom g)) _ _ _).
  exact (@be_gen R N (bm_left E) n n e e' (reflexivity n) He).
Qed.
Next Obligation.
  intros E M g n; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_zero (BalTensor N (bm_left E)))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (bal_gen_zero_r N (bm_left E) n)).
  - exact (cmon_map_zero (rm_hom g)).
Qed.
Next Obligation.
  intros E M g e e' n; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_plus (BalTensor N (bm_left E))
                     (@bs_gen R N (bm_left E) n e)
                     (@bs_gen R N (bm_left E) n e'))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (@be_add_r R N (bm_left E) n e e')).
  - exact (cmon_map_plus (rm_hom g) _ _).
Qed.
Next Obligation.
  (* R-linearity of the transpose IS the balance rule, again. / 转置的R线性再次就是平衡规则。 *)
  intros E M g r e n; simpl.
  refine (proper_morphism (cmon_map (rm_hom g)) _ _ _).
  exact (symmetry (@be_balance R N (bm_left E) r n e)).
Qed.

Program Definition hbt_to {E : Bimodule R S}
  {M : RModObject (Ring_op S)} (g : RTensor E N ~{ModR S}~> M) :
  E ~{@BimodCat R S}~> HomAbBimod N M := {|
  bh_hom := hbt_to_hom g
|}.
Next Obligation.
  intros E M g e s n; simpl.
  exact (rm_map_smul g s (@bs_gen R N (bm_left E) n e)).
Qed.

Program Definition hbt_from_bal {E : Bimodule R S}
  {M : RModObject (Ring_op S)}
  (h : E ~{@BimodCat R S}~> HomAbBimod N M) :
  BalBiadditive N (bm_left E) (rm_ab M) := {|
  bal_map := fun n e =>
    cmon_map (cmon_map (rm_hom (bh_hom h)) e) n
|}.
Next Obligation.
  intros E M h n n' Hn e e' He.
  transitivity (cmon_map (cmon_map (rm_hom (bh_hom h)) e) n').
  - exact (proper_morphism (cmon_map (cmon_map (rm_hom (bh_hom h)) e))
             n n' Hn).
  - exact (proper_morphism (cmon_map (rm_hom (bh_hom h))) e e' He n').
Qed.
Next Obligation.
  intros E M h n n' e.
  exact (cmon_map_plus (cmon_map (rm_hom (bh_hom h)) e) n n').
Qed.
Next Obligation.
  intros E M h n e e'.
  exact (cmon_map_plus (rm_hom (bh_hom h)) e e' n).
Qed.
Next Obligation.
  intros E M h r n e.
  exact (symmetry (rm_map_smul (bh_hom h) r e n)).
Qed.

Program Definition hbt_from {E : Bimodule R S}
  {M : RModObject (Ring_op S)}
  (h : E ~{@BimodCat R S}~> HomAbBimod N M) :
  RTensor E N ~{ModR S}~> M := {|
  rm_hom := bal_med (hbt_from_bal h)
|}.
Next Obligation.
  intros E M h s x.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med (hbt_from_bal h)) (rt_smul E N s))
            (cmon_hom_compose (rmod_lmul M s)
                              (bal_med (hbt_from_bal h))) _ x).
  intros n e.
  exact (bh_right h e s n).
Qed.

Program Definition hab_adj (E : Bimodule R S)
  (M : RModObject (Ring_op S)) :
  @Isomorphism Sets
    {| carrier := RTensor E N ~{ModR S}~> M;
       is_setoid := @homset (ModR S) (RTensor E N) M |}
    {| carrier := E ~{@BimodCat R S}~> HomAbBimod N M;
       is_setoid := @homset (@BimodCat R S) E (HomAbBimod N M) |} := {|
  to   := {| morphism := fun g => hbt_to g |};
  from := {| morphism := fun h => hbt_from h |}
|}.
Next Obligation. intros E M g g' Hg e n; exact (Hg _). Qed.
Next Obligation.
  intros E M h h' Hh x.
  refine (bal_hom_ext (bal_med (hbt_from_bal h))
                      (bal_med (hbt_from_bal h')) _ x).
  intros n e; exact (Hh e n).
Qed.
Next Obligation. intros E M h e n; reflexivity. Qed.
Next Obligation.
  intros E M g x.
  refine (bal_hom_ext (bal_med (hbt_from_bal (hbt_to g)))
                      (rm_hom g) _ x).
  intros n e; reflexivity.
Qed.

Definition hab_partial_adj :
  Partial_r (@BimodTensor R S) N ⊣ HomAbFunctor.
Proof using N R S.
  unshelve eapply (@Build_Adjunction' (ModR S) (@BimodCat R S)
                     (Partial_r (@BimodTensor R S) N) HomAbFunctor
                     hab_adj).
  - intros E E' M f g e n; reflexivity.
  - intros E M M' f g e n; reflexivity.
Defined.

End HomAbFunctorSection.

Arguments HomAbFunctor {R S} N.

(* * *** All three legs of Riehl's Definition 4.4.7 / * *** 里尔定义4.4.7的三条全部条件 *)

(*
 The mirror hypothesis of Adjunction/Parameter.v is a family
 [∀ x, Partial_r F x ⊣ H x], which is exactly what §F has just built;
 [mirror_family] packages it, and [mutually_right_adjoint] then
 supplies Riehl's Proposition 4.4.6(iii) — her Exercise 4.4.ii — as an
 inhabitant of Adjunction/Right.v's own [AdjointOnTheRight].  With
 §C's [pa_adj] that is all three legs of Definition 4.4.7 for
 [BimodTensor]. 

 --------
 Adjunction/Parameter.v 的镜像假设是一个族 [∀ x, Partial_r F x ⊣ H x]，这正是 §F 刚刚构建的；[mirror_family] 对其进行打包，然后 [mutually_right_adjoint] 提供 Riehl 的命题 4.4.6(iii) —— 她的练习 4.4.ii —— 作为 Adjunction/Right.v 自身的 [AdjointOnTheRight] 的一个元素。结合 §C 的 [pa_adj]，这就是 [BimodTensor] 的定义 4.4.7 的所有三条支腿。
*)

Section BimoduleTwoVariable.

Context {R S : RingObject}.

Definition bimodule_mirror_family :
  ParametrizedAdjunction
    ((@BimodTensor R S) ◯ @Swap (@BimodCat R S) (ModR R)) :=
  mirror_family (@BimodTensor R S) (fun N => HomAbFunctor N)
    (fun N => hab_partial_adj N).

Definition bimodule_two_variable_adjunction
  (M : RModObject (Ring_op S)) :
  AdjointOnTheRight
    (mr_left (@bimodule_parametrized_adjunction R S) M)
    (mr_right bimodule_mirror_family M) :=
  mutually_right_adjoint (@bimodule_parametrized_adjunction R S)
    bimodule_mirror_family M.

Example btv_left_obj (M : RModObject (Ring_op S)) (E : Bimodule R S) :
  mr_left (@bimodule_parametrized_adjunction R S) M E = HomSObj E M
  := eq_refl.

Example btv_right_obj (M : RModObject (Ring_op S))
  (N : RModObject (Ring_op R)) :
  mr_right bimodule_mirror_family M N = HomAbBimod N M := eq_refl.

End BimoduleTwoVariable.

(*
 Riehl's third leg, with its two hom-setoids written out: a map of
 bimodules E → hom_Ab(N, M) is the same thing as a map of right
 R-modules N → hom_S(E, M).  The term is the class's own [aor]. 

 --------
 Riehl的第三条腿，其两个hom-集合被写出来：一个从bimodules E → hom_Ab(N, M) 的映射，与一个从右R-模 N → hom_S(E, M) 的映射是同一件事。这个术语是该类自身的[aor]。
*)
Definition bimodule_third_leg {R S : RingObject}
  (M : RModObject (Ring_op S)) (E : Bimodule R S)
  (N : RModObject (Ring_op R)) :
  @Isomorphism Sets
    {| carrier := E ~{@BimodCat R S}~> HomAbBimod N M;
       is_setoid := @homset (@BimodCat R S) E (HomAbBimod N M) |}
    {| carrier := N ~{ModR R}~> HomSObj E M;
       is_setoid := @homset (ModR R) N (HomSObj E M) |} :=
  @aor (@BimodCat R S) (ModR R)
    (mr_left (@bimodule_parametrized_adjunction R S) M)
    (mr_right (@bimodule_mirror_family R S) M)
    (bimodule_two_variable_adjunction M) E N.

(* * ** G. A concrete witness at a named pair of rings / * ** G. 指定一对戒指的具体证人 *)

(*
 Instance/Mod.v's [Ring_Bimodule] makes every ring an
 (R,R)-bimodule over itself and its [Int_Bimodule] is that at ℤ, so
 the whole development instantiates with no new algebra.  Everything
 below COMPUTES: the actions, the unit, the counit and both legs of the
 associativity comparison reduce on closed integers.  The stdlib
 identifier [Z] is never named (only the [%Z] numerals carry the
 scope) — the binders go through the ring's own carrier and the
 arithmetic through its own rig laws — so this section adds no [Require]
 to the file. 

 --------
 Instance/Mod.v 的 [Ring_Bimodule] 使每个环成为它自身的 (R,R)-双模，并且它的 [Int_Bimodule] 是 ℤ 上的，所以整个发展实例化时没有新的代数。以下所有内容 COMPUTES：作用、单位、余单位以及结合性比较的两条腿在封闭整数上都会化简。stdlib 标识符 [Z] 从未被命名（只有 [%Z] 数字带有作用域）——绑定器通过环自身的载体进行，算术通过其自身的幺半环律进行——所以本节不会为文件添加任何 [Require]。
*)

Section IntegerWitness.

Local Notation ZC := (carrier (rig_setoid (ring_rig Int_Ring))).

(* ℤ read as a RIGHT ℤ-module, i.e. as an object of [ModR Int_Ring]. / ℤ 被读作一个右 ℤ-模，即作为 [ModR Int_Ring] 的一个对象。 *)
Definition ZRight : RModObject (Ring_op Int_Ring) :=
  bimodule_right_RMod Int_Bimodule.

Local Notation ZG := (@bs_gen Int_Ring ZRight (bm_left Int_Bimodule)).

Example z_tensor_smul_gen (a b s : ZC) :
  rm_smul (RTensor Int_Bimodule ZRight) s (ZG a b)
    = ZG a (rig_mul (ring_rig Int_Ring) b s) := eq_refl.

Example z_tensor_smul_computes :
  rm_smul (RTensor Int_Bimodule ZRight) 5%Z (ZG 2%Z 3%Z) = ZG 2%Z 15%Z
  := eq_refl.

Example z_tensor_unit_computes :
  cmon_map (rm_hom (cmon_map (rm_hom
      (bth_unit Int_Bimodule ZRight)) 2%Z)) 3%Z = ZG 2%Z 3%Z := eq_refl.

Example z_tensor_counit_computes :
  cmon_map (rm_hom (bth_counit Int_Bimodule ZRight))
      (@bs_gen Int_Ring (HomSObj Int_Bimodule ZRight)
         (bm_left Int_Bimodule) (@id (ModR Int_Ring) ZRight) 7%Z)
    = 7%Z := eq_refl.

(*
 Multiplication is balanced and biadditive, so it descends; it is what
 SEPARATES two generators, since no induction over the quotienting
 relation could produce a negative. 

 --------
 乘法是平衡的且双加的，因此它是可下降的；它是分离两个生成元的，因为没有关于商关系的归纳可以产生负数。
*)
(* Every field is a rig law of ℤ applied, so the record literal raises no obligation at all: multiplication is biadditive by distributivity and balanced by associativity. / 每个域都是 ℤ 的严格律的应用，因此记录文本根本不产生任何义务：乘法通过分配律是双加性的，并且通过结合律保持平衡。 *)
Definition int_mult_bal :
  BalBiadditive ZRight (bm_left Int_Bimodule) (ring_ab Int_Ring) :=
  @Build_BalBiadditive Int_Ring ZRight (bm_left Int_Bimodule)
    (ring_ab Int_Ring)
    (rig_mul (ring_rig Int_Ring))
    (rig_mul_respects (ring_rig Int_Ring))
    (fun a a' b => rig_distr_r (ring_rig Int_Ring) a a' b)
    (fun a b b' => rig_distr_l (ring_rig Int_Ring) a b b')
    (fun x a b => rig_mul_assoc (ring_rig Int_Ring) a x b).

Example int_mult_gen (a b : ZC) :
  cmon_map (bal_med int_mult_bal) (ZG a b)
    = rig_mul (ring_rig Int_Ring) a b := eq_refl.

Lemma int_tensor_separates :
  (ZG 1%Z 1%Z
     : carrier (cmon_setoid (rm_ab (RTensor Int_Bimodule ZRight))))
    ≈ ZG 1%Z 2%Z → False.
Proof.
  intro H.
  pose proof (bal_med_respects ZRight (bm_left Int_Bimodule)
                int_mult_bal _ _ H) as Hm.
  simpl in Hm; discriminate Hm.
Qed.

(* * *** The tensor of two bimodules, and the comparison, at ℤ / * *** 两个双模的张量，以及在 ℤ 上的比较 *)

Local Notation ZZ := (BimodTensorBimod Int_Bimodule Int_Bimodule).
Local Notation ZGG :=
  (@bs_gen Int_Ring (bimodule_right_RMod Int_Bimodule)
     (bm_left Int_Bimodule)).

Example z_btb_left_computes :
  rm_smul (bm_left ZZ) 2%Z (ZGG 3%Z 5%Z) = ZGG 6%Z 5%Z := eq_refl.

Example z_btb_right_computes :
  bm_rsmul ZZ (ZGG 3%Z 5%Z) 2%Z = ZGG 3%Z 10%Z := eq_refl.

Example z_assoc_to_computes (a b c : ZC) :
  cmon_map (rm_hom (ta_to Int_Bimodule Int_Bimodule ZRight))
      (@bs_gen Int_Ring (RTensor Int_Bimodule ZRight)
         (bm_left Int_Bimodule) (ZG a b) c)
    = @bs_gen Int_Ring ZRight (bm_left ZZ) a (ZGG b c) := eq_refl.

Example z_assoc_from_computes (a b c : ZC) :
  cmon_map (rm_hom (ta_from Int_Bimodule Int_Bimodule ZRight))
      (@bs_gen Int_Ring ZRight (bm_left ZZ) a (ZGG b c))
    = @bs_gen Int_Ring (RTensor Int_Bimodule ZRight)
        (bm_left Int_Bimodule) (ZG a b) c := eq_refl.

(* * *** The left-module mirror, and the second closure, at ℤ / * *** 左模镜像，以及在 ℤ 的第二闭包 *)

Example z_ltensor_smul_gen (a b r : ZC) :
  rm_smul (LTensor Int_Bimodule (Ring_RMod Int_Ring)) r
      (@bs_gen Int_Ring (bimodule_right_RMod Int_Bimodule)
         (Ring_RMod Int_Ring) a b)
    = @bs_gen Int_Ring (bimodule_right_RMod Int_Bimodule)
        (Ring_RMod Int_Ring) (rig_mul (ring_rig Int_Ring) r a) b
  := eq_refl.

Example z_hab_left_computes (f : rm_ab ZRight ~{Ab}~> rm_ab ZRight)
  (r n : ZC) :
  cmon_map (rm_smul (bm_left (HomAbBimod ZRight ZRight)) r f) n
    = cmon_map f (rig_mul (ring_rig Int_Ring) n r) := eq_refl.

Example z_hab_right_computes (f : rm_ab ZRight ~{Ab}~> rm_ab ZRight)
  (s n : ZC) :
  cmon_map (bm_rsmul (HomAbBimod ZRight ZRight) f s) n
    = rig_mul (ring_rig Int_Ring) (cmon_map f n) s := eq_refl.

End IntegerWitness.
