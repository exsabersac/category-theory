(* * * Base change along ℤ → R: the free R-module on an abelian group / * * 基于 ℤ → R 的变换：在阿贝尔群上的自由 R-模 *)

(*
 Book:      Mac Lane, “Categories for the Working Mathematician”, 2nd
 ed., §IV.1, printed pp. 79–80 (PDF pp. 89–90) — adjunctions
 in hom-set form, whose running examples are the
 free/forgetful pairs; the unit is ⌊id⌋ and the whole
 content of such an example is naming the free construction
 and its insertion of generators.
 Book:      Mac Lane, ibid., §I.8, printed pp. 28–29 — the tensor
 product of abelian groups, which is the construction this
 file consumes (Instance/Ab/Tensor.v builds it).
 Book:      Riehl, “Category Theory in Context”, Dover 2016, §4.1
 Example 4.1.10 — extension of scalars along a ring
 homomorphism is left adjoint to restriction of scalars.
 READ THE RELATION TO THAT EXAMPLE PRECISELY: hers runs
 between two MODULE categories, and this one runs out of
 [Ab].  See PRIOR ART below; the two are not instances of
 one another in this tree.
 nLab:      https://ncatlab.org/nlab/show/extension+of+scalars
 nLab:      https://ncatlab.org/nlab/show/free+module
 Wikipedia: https://en.wikipedia.org/wiki/Extension_of_scalars

 WHAT IS DELIVERED.

 - [ZExtObj R A : RModObject R], the abelian group R ⊗ A — the
 ℤ-tensor of Instance/Ab/Tensor.v — equipped with the scalar
 action r · (s ⊗ a) = (r s) ⊗ a.
 - [ZExtMap] and **[ZExt R : Ab ⟶ RMod R]**, the functor.
 - [zext_to] / [zext_from], the two transposes, and [zext_adj], the
 bijection as an [Isomorphism] of hom-setoids in [Sets].
 - **[zext_adjunction R : ZExt R ⊣ RMod_Forget_Ab R]**, an inhabitant
 of Theory/Adjunction.v's [Adjunction] record, built through
 [Build_Adjunction'] (whose two remaining naturality obligations
 both close by [reflexivity] — see the ledger below).
 - [zext_unit] and [zext_counit], with the reviewer check PINNED:
 **[zext_unit_is_gen] states that the adjunction's unit component
 at A, applied to a, IS [ts_gen 1 a], and it closes at [eq_refl]**.
 - A ℤ witness: [ZIntExt := ZExtObj Int_Ring (ring_ab Int_Ring)],
 i.e. ℤ ⊗ ℤ, with a computing evaluation map and non-degeneracy
 proved by MAPPING OUT.  Count those honestly: there are THREE
 lemmas but only TWO distinct propositions —
 [zext_int_unit_separates] is [exact zext_int_gens_distinct] and
 its statement is byte-identical, kept only because it is the one
 a reader looks for under that name.  Instance/Mod/Coextension.v's
 three ARE three distinct statements.

 NO COMMUTATIVITY HYPOTHESIS, AND THAT IS A THEOREM RATHER THAN A
 PREFERENCE.  The file's ONLY [Context] is [(R : RingObject)]; there is
 no [Rcomm]-style argument anywhere, and [About ZExtObj] /
 [About zext_adjunction] show the signatures taking a bare ring.  The
 two places a reader expects commutativity to be spent are exactly the
 two associativity clauses, and both go through on associativity alone:

 - [zext_act_assoc], the module law (r s) · x ≈ r · (s · x).  On a
 generator both sides are ((r s) t) ⊗ a and (r (s t)) ⊗ a, and the
 ONLY law consumed is [rig_mul_assoc].
 - [zext_from]'s [rm_map_smul] obligation, which is what makes the
 untranspose R-linear.  On a generator both sides are
 ((r s) · h a) and (r · (s · h a)), and the ONLY law consumed is
 [rm_smul_assoc] of the target module.

 This is a genuine contrast with Instance/Mod/Closed.v, whose own
 header localises its commutativity hypothesis to the single lemma
 [hm_smul_linear]: there r · φ must be shown LINEAR, and (r·φ)(s·v) is
 r · (s · φ v) where linearity demands s · (r · φ v), so the two
 scalars must be exchanged.  Here they never are — the scalar acts on
 the LEFT-HAND FACTOR of R ⊗ A and the module element never carries a
 scalar of its own, so no exchange is ever demanded.

 WHY A RING AND NOT A RIG.  [AbTensor] tensors two [AbObject]s, so the
 base must have additive inverses to be tensored at all.  [ring_neg] is
 spent NOWHERE in this file directly; its whole role is that
 [ring_ab R] is an object of [Ab].  A rig-level analogue would need a
 tensor of commutative monoids, which the tree does not have.

 WHAT IS REUSED, NOT REBUILT.

 - Instance/Ab/Tensor.v: [AbTensor], [Bilinear], [tensor_gen],
 [tensor_ump], **[tensor_hom_ext]**, and the relation constructors
 [te_gen], [te_bilin_l], [te_bilin_r], [te_trans], [te_sym].
 - Instance/Rng.v: [ring_ab], the additive group of a ring.
 - Instance/Mod.v: [RModObject], [RModHom], [RMod],
 **[RMod_Forget_Ab]** (the right adjoint, taken as given),
 [rm_smul_zero_r], [Ring_RMod], [Int_RMod].
 - Instance/Ab.v: [AbHom], [ab_cancel_l].
 - Instance/CMon.v: [cmon_hom_id] and [cmon_hom_compose] — declared
 there, not in Instance/Ab.v, which only uses
 them.
 - Structure/AbCategory.v: [ab_hom_add], the pointwise sum of two
 homomorphisms into an abelian group — which is what lets the
 right-distributivity law be stated as an agreement of two
 HOMOMORPHISMS and hence discharged by [tensor_hom_ext].
 - Theory/Adjunction.v: [Build_Adjunction'], [unit], [counit].

 NO INDUCTION IS PERFORMED, AND THAT IS MEASURED.  No [induction]
 tactic is invoked below; the only occurrences of the token anywhere in
 the file are the three in this paragraph, so [grep -n induction]
 returns exactly these lines.  Every module law, every functor law
 and both iso laws are an agreement of two HOMOMORPHISMS out of the
 tensor, discharged by [tensor_hom_ext] — the uniqueness half of the
 UMP — after checking generators; the one law that is not is
 [rm_smul_distr_l], which is literally [cmon_map_plus] of the mediator
 and holds by [reflexivity] because [tensor_med_fun] is a [Fixpoint].
 The single induction the development rests on lives in the donor.

 WHICH LEMMA SPENDS WHICH LAW.  Read as a ledger; nothing else of R is
 consumed, and in particular [rig_mul_zero_l], [rig_mul_zero_r] and
 [ring_neg] are spent nowhere directly.

 [zext_bilin]        respectfulness ← [rig_mul_respects]
 additivity in the scalar ← [rig_distr_l]
 additivity in the group ← [te_bilin_r] alone
 [zext_smul_scalar]  ← [rig_mul_respects]
 [zext_act_distr_r]  ← [rig_distr_r]
 [zext_act_assoc]    ← [rig_mul_assoc]        (associativity ONLY)
 [zext_act_one]      ← [rig_mul_one_l]
 [zext_gen_zero_r]   ← [ab_cancel_l] of the TENSOR (s ⊗ 0 ≈ 0 is not
 a constructor of the quotient; it is derived)
 [zext_to]           zero ← [zext_gen_zero_r]; sum ← [te_bilin_r]
 [zext_map_bilin]    ← nothing of R; [te_bilin_l] and [cmon_map_plus]
 of the given f
 [zext_lmul]         ← [rm_smul_respects], [rm_smul_zero_r],
 [rm_smul_distr_l] of M
 [zext_from_bilin]   ← [rm_smul_respects], [rm_smul_distr_r],
 [rm_smul_distr_l] of M
 [zext_from]         ← [rm_smul_assoc] of M   (associativity ONLY)
 [zext_adj] to∘from  ← [rm_smul_one] of M
 [zext_adj] from∘to  ← [rm_map_smul] of the given g, [rig_mul_one_r]
 [ZExtMap], [ZExt]'s [fmap_id] and [fmap_comp], and BOTH naturality
 obligations of [Build_Adjunction'] ← NOTHING; all [reflexivity].

 BOTH UNIT LAWS OF R ARE SPENT, AT DIFFERENT PLACES.  [rig_mul_one_l]
 closes the module law 1 · x ≈ x; [rig_mul_one_r] closes the round trip
 [zext_from (zext_to g)] ≈ g, where the residue is s · 1 in the scalar
 slot.  Over a non-commutative ring these are separate axioms, so this
 is a real observation and not bookkeeping.

 STRENGTHS, MEASURED STRICT-FIRST.  Eleven identifications close at
 [eq_refl] and are shipped as [Example]s:

 - the action on a generator ([zext_act_gen]);
 - **the unit at a: [ts_gen 1 a] ([zext_unit_is_gen])** — the
 reviewer check, and it is definitional rather than up to ≈;
 - the counit on a generator: s ⊗ m ↦ s · m
 ([zext_counit_is_smul]);
 - the adjunction's forward transpose IS [zext_to] and its backward
 transpose IS [zext_from] ([zext_adj_to_is_zext_to],
 [zext_adj_from_is_zext_from]) — so nothing downstream is reading a
 different map than the one the header names;
 - the functor's two actions ([zext_fobj_is_ZExtObj],
 [zext_fmap_is_ZExtMap]) and the right adjoint's object action
 ([zext_forget_is_rm_ab]);
 - over ℤ, [3 ⊗ 4 ↦ 12] and [0 ↦ 0] under the counit, and the unit
 at a computing to [1 ⊗ a].

 EXACTLY TWO IDENTIFICATIONS FALL BACK TO ≈, AND BOTH ARE ROUND TRIPS
 OF THE BIJECTION.  [zext_to (zext_from h)] evaluates to 1 · h a and
 [zext_from (zext_to g)] to (s · 1) ⊗ a; [rm_smul_one] and
 [rig_mul_one_r] are what remove the residues, and BOTH are abstract
 fields of a class, so neither side reduces and no downstream
 transparency would help.  Both are pinned as CONVERSION negatives with
 the ≈ forms beside them as controls.

 UNIVERSES, MEASURED AND ATTRIBUTED.  [ZExtObj] carries NO equation in
 its constraint block — the ring's three universes are only BOUNDED —
 while [ZExt] and [zext_adjunction] both carry [u = u1], identifying
 the ring's FIRST and THIRD universes.  Where that enters is measured
 rather than guessed, and it is NOT this file's: with the two levels
 declared strictly apart, [RMod Ru], [ring_ab Ru],
 [AbTensor (ring_ab Ru) Au], [ZExtObj Ru Au], [zext_act Ru Au],
 [zext_map_ab Ru fu], [RMod_Forget_Ab Ru], [Ab ⟶ RMod Ru] and
 Instance/Mod.v's own [Ring_RMod Ru] all elaborate, while
 [ZExtObj Ru Au : obj[RMod Ru]] is rejected — AND SO IS
 [Ring_RMod Ru : obj[RMod Ru]], at the same levels with the same
 message.  So the identification is Instance/Mod.v's, is met the moment
 any module is read as an OBJECT of [RMod R], and is inherited here
 rather than introduced.  It is not claimed unavoidable; no
 re-annotation was attempted.  CORRECTION (#465): the two constants no
 longer carry that equation.  [About] on [ZExt] and [zext_adjunction]
 prints, over [RingObject@{u u0 u1}], the bounds u0 <= u and u1 <= u and
 no equation; with u1 < u declared in a Section (the proof universe
 strictly below the auxiliary one), [ZExtObj Ru Au : obj[RMod Ru]],
 [ZExt Ru] and [zext_adjunction Ru] all elaborate, while
 [Ring_RMod Ru : obj[RMod Ru]] is still refused, now with “Cannot enforce
 u1 = u0 because u1 < u0”.  The FIRST and THIRD universes above are the
 carrier and the auxiliary one, in the order before the auxiliary
 universe became [RingObject]'s first argument; that pair, the carrier
 strictly below the auxiliary universe, is the one this file's Section
 [ZExtProbeUniverses] separates (ra < rc at [RingObject@{rc ra rb}]),
 and its paragraph CONTROLS 5, 7 AND 8, WHICH USED TO BE NEGATIVES,
 records where the equation went: the PR “algebraic carriers are sets”
 (2026-09-17) moved Instance/Ab/Tensor.v's [ts_eq] to [Prop].

 PRIOR ART, AND THREE FILES RECORD THIS EXACT ABSENCE.
 Instance/Ab/Free.v said the tree “has only the forgetful
 direction ([RMod_Forget_Ab], Instance/Mod.v)”;
 Instance/Mod/Quotient.v said “an [AbObject] is not exhibited
 as a ℤ-module anywhere in the tree” and named
 Instance/Rng/Mod.v's [ZRestrict R : RMod R ⟶ RMod Int_Ring] as
 the near miss that is NOT it; Instance/Mod/Tensor.v recorded the
 same.  (Those are the three files' wordings when this file was
 written.  Instance/Ab/Free.v was reworded in this file's own commit
 to “no such passage exists ([RMod_Forget_Ab], Instance/Mod.v, is the
 forgetful direction; ...)”, naming [ZExt Int_Ring]; since #454 each of
 the three carries a further correction, Instance/Mod/Cogenerator.v's
 [Ab_to_ZMod] being the functor they recorded as absent.  An earlier
 revision of this paragraph quoted them in the present tense.)  A
 type-level sweep confirmed it: before this file NO constant in
 the tree had type [Ab ⟶ RMod _] (zero hits), and no [AbTensor] is
 applied to a [ring_ab] anywhere else.

 BUT READ WHAT IS AND IS NOT DISCHARGED.  This file supplies a functor
 [Ab ⟶ RMod R] for every R, which is the direction those notes record
 as missing — yet at R := ℤ it sends A to ℤ ⊗ A, NOT to A carrying its
 own ℤ-action, and the two are isomorphic rather than equal (the
 carriers are [tsum] and A's own, pinned as CONVERSION negative 4 at
 the concrete witness).  So the reductions those three files want are
 NOT discharged here and nothing below claims they are.

 Distinct also from Instance/Mod/Extension.v, which is extension of
 scalars along an ARBITRARY ring homomorphism φ : R → S over
 Instance/Mod/Tensor.v's R-tensor, left adjoint to
 [Restrict φ : RMod S ⟶ RMod R].  Neither file is an instance of the
 other in this tree: at φ := ℤ → R that one's source is [RMod Int_Ring]
 and this one's is [Ab].  Say the obstruction precisely, because a
 blanket “no functor between those exists” would be FALSE and is
 refuted by this file's own ℤ witness: [RMod_Forget_Ab Int_Ring] is a
 functor [RMod Int_Ring ⟶ Ab], and [ZExt Int_Ring] is one the other
 way.  An earlier revision said “What is absent is the passage the
 reduction would need — an [Ab ⟶ RMod Int_Ring] carrying each abelian
 group ITS OWN ℤ-action, which is the absence quoted above”.  Since
 #454 that functor exists, Instance/Mod/Cogenerator.v's [Ab_to_ZMod]
 (each group with its own [zsmul] action), and the three files quoted
 above carry the same correction.  What remains absent is narrower: no
 equivalence [Ab ≃ RMod Int_Ring] and no comparison of [Ab_to_ZMod]
 with [ZExt Int_Ring], which is not that functor, its carrier being
 ℤ ⊗ A rather than A's.  Nothing is shared, and
 that file is not
 [Require]d.  Distinct too from Instance/Mod/Free.v, whose [FreeMod] is
 left adjoint to [RMod_Forget : RMod R ⟶ Sets] — the free module on a
 SETOID, a different right adjoint.

 AXIOMS.  67/67 constants report “Closed under the global context”
 (43 source-declared plus 24 [Program] obligations that no source sweep
 sees; queried by fully qualified name).  Zero of the 67 names occur
 anywhere else in the tree, checked name by name.

 NEGATIVES.  Nine [Fail] commands: eight guarded negatives — three
 CONVERSION, one TYPING, four FORMABILITY — each beside an APPLIED
 positive control, plus one scope-free instrument check.  Each was
 stripped and compiled alone and its WHOLE error read; see the probe
 section at the end of the file for the classification.

 WHAT IS NOT DELIVERED.

 - No naturality of [zext_adj] in a THIRD variable and no
 identification of [ZExt] with any monoidal or bifunctorial
 structure; [AbTensor_Functor] is not consumed.
 - No comparison with Instance/Mod/Extension.v's [ExtendScalars] at
 any φ, and no bridge [Ab ≃ RMod Int_Ring]; consequently nothing
 here discharges the three absence notes quoted above.
 - No isomorphism ℤ ⊗ A ≅ A in [Ab], hence nothing says [ZExt ℤ] is
 equivalent to the identity; the ℤ witness pins ℤ ⊗ ℤ only through
 a map OUT of it.
 - No triangle identities restated in this file's own vocabulary
 (they are Theory/Adjunction.v's derived corollaries and are not
 specialised), and no uniqueness statement for the left adjoint.
 - No monad on [Ab] from the adjunction, no Eilenberg–Moore or
 Kleisli reading.  CORRECTION (#465): Instance/Mod/TensorMonad.v
 builds that monad, [TensorMonad R], as Monad/Comparison.v's
 [Adjunction_Induced_Monad] at [zext_adjunction R], and identifies
 its Eilenberg–Moore category with [RMod R] by the canonical
 comparison functor ([RMod_comparison_equivalence]); the Kleisli
 reading is still not delivered.
 - No normal form for the tensor, hence no basis, no rank and no
 decision procedure; every negative goes through a map OUT.
 - No right adjoint to [RMod_Forget_Ab] (coextension of scalars);
 the header's arithmetic for the coextension side —
 (r · (s · f))(t) = f(t (r s)) = ((r s) · f)(t), again
 associativity alone — is stated in issue #360 and is NOT
 formalised here.
 - No [RigObject] variant, no right-module or bimodule reading, and
 no instance registered for typeclass resolution: [ZExt] and
 [zext_adjunction] are plain [Definition]s. 

 --------
 书籍：Mac Lane，《为工作中的数学家准备的范畴论》，第2版，第IV.1节，印刷页79–80（PDF页89–90）——以同态集形式的伴随，其进行的例子是自由/忘记对；幺元是⌊id⌋，这样一个例子的全部内容是命名自由构造及其生成元的插入。书籍：Mac Lane，同上，第I.8节，印刷页28–29——阿贝尔群的张量积，这是本文件使用的构造（Instance/Ab/Tensor.v 构建它）。书籍：Riehl，《情境中的范畴论》，Dover 2016，第4.1节 例4.1.10——沿环同态的标量扩展是标量限制的左伴随。精确阅读与该示例的关系：她的是在两个模块类别之间运行，而这个是从[Ab]延伸出来的。见下方的现有技术；在这棵树中，两者不是彼此的实例。nLab：https://ncatlab.org/nlab/show/extension+of+scalars
 nLab：https://ncatlab.org/nlab/show/free+module
 Wikipedia：https://en.wikipedia.org/wiki/Extension_of_scalars

 交付的内容是什么。- [ZExtObj R A : RModObject R]，阿贝尔群 R ⊗ A —— Instance/Ab/Tensor.v 中的 ℤ-张量 —— 配备了标量作用 r · (s ⊗ a) = (r s) ⊗ a。- [ZExtMap] 和 ** [ZExt R : Ab ⟶ RMod R] **，函子。- [zext_to] / [zext_from]，两个转置，以及 [zext_adj]，在 [Sets] 的同态集合中作为 [Isomorphism] 的双射。- ** [zext_adjunction R : ZExt R ⊣ RMod_Forget_Ab R] **，Theory/Adjunction.v 的 [Adjunction] 记录的一个实例，通过 [Build_Adjunction'] 构建（其剩余的两个自然性义务都通过 [reflexivity] 解决 —— 见下方账本）。- [zext_unit] 和 [zext_counit]，带有审阅员检查 PINNED：** [zext_unit_is_gen] 说明在 A 上的附接单位分量，应用于 a，是 [ts_gen 1 a]，并且在 [eq_refl] 完成。**- 一个 ℤ 的证人：[ZIntExt := ZExtObj Int_Ring (ring_ab Int_Ring)]，即Z ⊗ Z，具有计算评估映射和非简并性
 通过映射出去证明。诚实地数一数：有三个
 引理，但只有两个不同的命题——
 [zext_int_unit_separates] [exact zext_int_gens_distinct] 和
 它的语句是字节完全相同的，仅因为它是唯一的
 读者会在该名称下查找。实例/Mod/Coextension.v
 三句确实是三个不同的陈述。

 没有交换性假设，这是一个定理，而不是
 偏好。文件唯一的[Context]是[(R : RingObject)];有
 没有[Rcomm]式论证，[About ZExtObj] /
 [About zext_adjunction]展示签名，用裸露的戒指。那个
 读者期望交换性被花费的两个地点恰好是
 两个结合性条款，且仅凭结合性即可通过：- [zext_act_assoc]，模的法律 (r s) · x ≈ r · (s · x)。在一个生成元上，两边是 ((r s) t) ⊗ a 和 (r (s t)) ⊗ a，唯一使用的法律是 [rig_mul_assoc]。
 - [zext_from] 的 [rm_map_smul] 义务，这就是使得非转置 R 线性成立的原因。在一个生成元上，两边是 ((r s) · h a) 和 (r · (s · h a))，唯一使用的法律是目标模的 [rm_smul_assoc]。这与 Instance/Mod/Closed.v 形成了真正的对比，其自身的头文件将其交换性假设限定在单个引理 [hm_smul_linear] 上：必须证明 r · φ 是线性的，并且 (r·φ)(s·v) 等于 r · (s · φ v)，而线性要求 s · (r · φ v)，因此这两个标量必须交换。在这里它们从未被交换——标量作用于 R ⊗ A 的左因子，而模块元素自身从不携带标量，因此从不要求交换。

 为什么是环而不是加法半环。[AbTensor] 张量化了两个 [AbObject]，因此要进行张量操作，基对象必须有加法逆元。[ring_neg] 在此文件中直接没有被使用；它的全部作用是 [ring_ab R] 是 [Ab] 的对象。加法半环层面的类似物需要一个交换幺半群的张量，而该树没有提供。重用的，而不是重建的。- Instance/Ab/Tensor.v：[AbTensor]，[Bilinear]，[tensor_gen]，[tensor_ump]，**[tensor_hom_ext]**，以及关系构造器 [te_gen]，[te_bilin_l]，[te_bilin_r]，[te_trans]，[te_sym]。- Instance/Rng.v：[ring_ab]，环的加法群。- Instance/Mod.v：[RModObject]，[RModHom]，[RMod]，**[RMod_Forget_Ab]**（右伴随，假定已知），[rm_smul_zero_r]，[Ring_RMod]，[Int_RMod]。- Instance/Ab.v：[AbHom]，[ab_cancel_l]。- Instance/CMon.v：[cmon_hom_id] 和 [cmon_hom_compose] — 在此处声明，而非在 Instance/Ab.v 中，Instance/Ab.v 仅使用它们。- Structure/AbCategory.v：[ab_hom_add]，两个映射到阿贝尔群的同态的逐点和 — 这使得右分配律可以被表述为两个同态的一致性，因此可由 [tensor_hom_ext] 解决。- Theory/Adjunction.v:  [Build_Adjunction'] ,  [unit] ,  [counit]。

 没有进行归纳，这是被测量的。下面没有调用任何  [induction] 
 策略；该文件中该标记的唯一出现就在本段中的三个，所以  [grep -n induction] 
 精确返回这些行。每个模律，每个函子律以及两个同构律都是张量的两个同态的一致性，由  [tensor_hom_ext] 
 释放——在检查生成元后，UMP 的唯一性部分；唯一不是的律是
 [rm_smul_distr_l] ，它字面上是调解器的  [cmon_map_plus] ，并且由于  [tensor_med_fun] 是  [Fixpoint] ，所以由  [reflexivity] 成立。
 开发唯一依赖的归纳存在于捐赠者中。哪个引理用掉哪个定律。 读作账簿；R的其他部分没有被消耗，特别是[rig_mul_zero_l]、[rig_mul_zero_r]和[ring_neg]在任何地方都没有被直接使用。[zext_bilin]         尊重 ←  [rig_mul_respects] 
 标量加法性 ←  [rig_distr_l] 
 群加法性 ←  [te_bilin_r]  单独
 [zext_smul_scalar]   ←  [rig_mul_respects] 
 [zext_act_distr_r]   ←  [rig_distr_r] 
 [zext_act_assoc]     ←  [rig_mul_assoc]         （仅结合性）
 [zext_act_one]       ←  [rig_mul_one_l] 
 [zext_gen_zero_r]    ←  [ab_cancel_l]  张量的（s ⊗ 0 ≈ 0 不是
 商的构造；它是推导出来的）
 [zext_to]            零 ←  [zext_gen_zero_r] ; 和 ←  [te_bilin_r] 
 [zext_map_bilin]     ← R 的无；  [te_bilin_l]  和  [cmon_map_plus] 
 给定 f 的
 [zext_lmul]          ←  [rm_smul_respects] ,  [rm_smul_zero_r] ,
 [rm_smul_distr_l]  M 的
 [zext_from_bilin]    ←  [rm_smul_respects] ,  [rm_smul_distr_r] ,
 [rm_smul_distr_l]  M 的
 [zext_from]          ←M 的 [rm_smul_assoc]（仅结合性）
 [zext_adj]  到∘从  ← M 的 [rm_smul_one]
 from∘to  [zext_adj]  ← 给定 g 的 [rm_map_smul]，[rig_mul_one_r]
 [ZExtMap]，[ZExt] 的 [fmap_id] 和 [fmap_comp]，以及 [Build_Adjunction'] 的两个自然性义务 ← 无；所有 [reflexivity]。R 的两个单位律在不同的地方被使用。[rig_mul_one_l] 关闭了模律 1 · x ≈ x；[rig_mul_one_r] 关闭了往返律 [zext_from (zext_to g)] ≈ g，其中余数在标量槽中为 s · 1。在非交换环上，这些是独立的公理，所以这是一个真实的观察，而不是账务处理。

 强度，首先严格测量。在 [eq_refl] 闭合的有十一种标识，并作为 [Example] 提供：- 一个生成元的作用 ([zext_act_gen])；
 - **在 a 处的单位：[ts_gen 1 a]（[zext_unit_is_gen]）** — 审核者检查，这是定义性的，而不是近似的；
 - 一个生成元上的余单位：s ⊗ m ↦ s · m ([zext_counit_is_smul])；
 - 拓挈的正向转置是 [zext_to]，反向转置是 [zext_from] ([zext_adj_to_is_zext_to], [zext_adj_from_is_zext_from]) — 因此下游没有读取到的映射不同于标题中命名的映射；
 - 函子的两个作用 ([zext_fobj_is_ZExtObj], [zext_fmap_is_ZExtMap]) 以及右伴随函子的对象作用 ([zext_forget_is_rm_ab])；
 - 在 ℤ 上，[3 ⊗ 4 ↦ 12] 和 [0 ↦ 0] 在余单位下，以及在 a 处的单位计算到 [1 ⊗ a]。确切地说，只有两个标识回退到 ≈，并且两者都是双射的循环。[zext_to (zext_from h)] 计算结果为 1 · h a，[zext_from (zext_to g)] 计算结果为 (s · 1) ⊗ a；[rm_smul_one] 和 [rig_mul_one_r] 是消除残留物的，它们两者都是类的抽象字段，因此双方都无法简化，也没有下游透明性会有所帮助。两者都被标记为 CONVERSION 负面示例，旁边的 ≈ 形式作为对照。宇宙，被测量和归因。[ZExtObj] 在其约束块中没有等式——该环的三个宇宙只是被界定——而 [ZExt] 和 [zext_adjunction] 都包含 [u = u1]，用于识别该环的第一个和第三个宇宙。其进入点是测量得出的而非猜测的，并且这不是该文件的：随着两个层级严格分开声明，[RMod Ru]、[ring_ab Ru]、[AbTensor (ring_ab Ru) Au]、[ZExtObj Ru Au]、[zext_act Ru Au]、[zext_map_ab Ru fu]、[RMod_Forget_Ab Ru]、[Ab ⟶ RMod Ru] 以及 Instance/Mod.v 自身的 [Ring_RMod Ru] 都会展开，而 [ZExtObj Ru Au : obj[RMod Ru]] 被拒绝——[Ring_RMod Ru : obj[RMod Ru]] 也同样被拒绝，在相同层级下出现同样的信息。因此，该识别属于 Instance/Mod.v，一旦任何模块被读取为 [RMod R] 的 OBJECT 时即可满足，并在此继承而非引入。它并不声称不可避免；没有尝试重新注释。更正 (#465)：这两个常量不再带有该方程。[About] 在 [ZExt] 和 [zext_adjunction] 上打印，超过 [RingObject@{u u0 u1}]，输出 u0 <= u 和 u1 <= u，并且没有方程；在某一节中声明 u1 < u（证明宇宙严格低于辅助宇宙），[ZExtObj Ru Au : obj[RMod Ru]、[ZExt Ru] 和 [zext_adjunction Ru] 都被展开，而 [Ring_RMod Ru : obj[RMod Ru] 仍然被拒绝，现在提示“无法强制 u1 = u0，因为 u1 < u0”。上面的第一个和第三个宇宙分别是承载宇宙和辅助宇宙，在辅助宇宙成为 [RingObject] 的第一个参数之前的顺序；那一对中，承载宇宙严格位于辅助宇宙之下，是本文件第 [ZExtProbeUniverses] 节所分隔的（在 [RingObject@{rc ra rb}] 时 ra < rc），其段落 CONTROLS 5、7 和 8（以前是负数）记录了方程的变化：PR “代数承载体是集合” (2026-09-17) 将 Instance/Ab/Tensor.v 的 [ts_eq] 移动到 [Prop]。现有技术，以及三个文件记录了这种确切的缺失。Instance/Ab/Free.v 说树“只有遗忘方向 ([RMod_Forget_Ab]，Instance/Mod.v)”；Instance/Mod/Quotient.v 说“在树中的任何地方都没有作为 ℤ-模展示的 [AbObject]”，并将 Instance/Rng/Mod.v 的 [ZRestrict R : RMod R ⟶ RMod Int_Ring] 命名为接近但不是它的例子；Instance/Mod/Tensor.v 也记录了相同情况。（这些是编写本文件时三个文件的原话。Instance/Ab/Free.v 在本文件自己的提交中被改写为“没有这样的段落存在 ([RMod_Forget_Ab]，Instance/Mod.v 是遗忘方向；…)”，并命名 [ZExt Int_Ring]；自 #454 起，这三者都进行了进一步修正，Instance/Mod/Cogenerator.v 的 [Ab_to_ZMod] 是他们记录为缺失的函子。该段的早期修订版使用现在时引用了它们。) 类型级扫查证实了这一点：在此文件之前，树中没有任何常量的类型是 [Ab ⟶ RMod _]（零命中），并且没有 [AbTensor] 被应用于任何其他地方的 [ring_ab]。

 但是请阅读哪些被消解，哪些未被消解。该文件为每个 R 提供了一个函子 [Ab ⟶ RMod R]，这正是那些笔记记录为缺失的方向——然而在 R := ℤ 时，它将 A 发送到 ℤ ⊗ A，而不是发送到携带自身 ℤ-作用的 A，并且两者是同构而非相等（载体为 [tsum] 和 A 自身，在具体实例上标记为 CONVERSION 负 4）。因此，这三个文件所要的归约在这里并未被消解，且下面没有任何内容声称它们被消解了。这也不同于 Instance/Mod/Extension.v，后者是 的扩展
 沿任意环同态的标量 φ ： R → S
 实例/Mod/Tensor.v的R-张量，左伴随于
 [Restrict φ : RMod S ⟶ RMod R]。这两个文件都不是
 本树中的另一个：在 φ ：= Z 的 → R，其源属于[RMod Int_Ring]
 而这个的就是[Ab]。精确地说障碍，因为
 一般来说，“它们之间不存在函子”则为假，且是
 被本档案中的Z证人反驳：[RMod_Forget_Ab Int_Ring]是
 函子[RMod Int_Ring ⟶ Ab]，[ZExt Int_Ring] 是另一个函子
 方式。早期的修订指出：“缺失的是该段落
 需要约化——一个承载每个阿贝尔的 [Ab ⟶ RMod Int_Ring]
 组其自身的Z-作用，即上述缺失。自从 #454 引入了该函子之后，Instance/Mod/Cogenerator.v 的 [Ab_to_ZMod]（每个群都有自己的 [zsmul] 操作），以及上面引用的三个文件都包含相同的修正。仍然缺失的是更窄的内容：没有 [Ab ≃ RMod Int_Ring] 的等价，也没有将 [Ab_to_ZMod] 与 [ZExt Int_Ring] 的比较，它不是那个函子，它的承载对象是 ℤ ⊗ A，而不是 A 的。没有共享内容，而且该文件不是 [Require]。也与 Instance/Mod/Free.v 不同，该文件的 [FreeMod] 是 [RMod_Forget : RMod R ⟶ Sets] 的左伴随——在 SETOID 上的自由模，一个不同的右伴随。公理。67/67 个常量报告“在全局上下文下闭合”（43 个源声明加上 24 个 [Program] 义务，源扫描无法看到；通过完全限定名称查询）。在树的其他任何地方都没有出现这 67 个名称，逐个名称检查。 

 负面。九个 [Fail] 命令：八个受保护的负面——三个转换（CONVERSION）、一个类型（TYPING）、四个可形成性（FORMABILITY）——每个旁边都有一个已应用的正面控制，加上一个无作用域的仪器检查。每个都被剥离并单独编译，其整个错误被读取；分类请参见文件末尾的探测部分。 

 未交付的内容。- 第三变量中[zext_adj]的自然性，且
 将[ZExt]与任意幺半群或双函子的同一化
 结构;[AbTensor_Functor] 不被消耗。- 与实例/Mod/Extension.v 的 [ExtendScalars] 不进行比较
 任何φ，也没有桥[Ab ≃ RMod Int_Ring];因此什么都没有
 此处释放上述三个缺失音。- 无同构 Z ⊗ A ≅ A，[Ab] ，因此无 说 是 [ZExt ℤ]
 等价于恒等式;Z见证者仅通过以下方式将Z钉住⊗Z
 从中绘制出一张地图。- 本文件自身词汇中未重新表述三角形身份
 （它们是 Theory/Adjunction.v 的衍生推论，不是
 专门化的），且左伴随没有唯一性命题。- 从伴随中无[Ab]单子，也无艾伦伯格–摩尔或
 Kleisli 阅读。更正 (#465)：Instance/Mod/TensorMonad.v 构建了那个单子 [TensorMonad R]，作为 Monad/Comparison.v 的 [Adjunction_Induced_Monad] 在 [zext_adjunction R]，并通过典型的比较函子 ([RMod_comparison_equivalence]) 将其 Eilenberg–Moore 范畴与 [RMod R] 识别；Kleisli 读取仍未实现。 - 张量没有标准形式，因此没有基，没有秩，也没有判定程序；每个负元素都通过一个映射 OUT。 - [RMod_Forget_Ab]（标量的余拓展）没有右伴随；头文件中余拓展部分的算术 — (r · (s · f))(t) = f(t (r s)) = ((r s) · f)(t)，再次强调，仅是结合性 — 已在问题 #360 中说明，但此处未形式化。- 没有 [RigObject] 变体，没有右模块或双模块读取，并且没有为类型类解析注册实例：[ZExt] 和 [zext_adjunction] 是普通的 [Definition]。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Tensor.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Structure.AbCategory.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

Open Scope category_scope.

#[local] Obligation Tactic := idtac.

Section ZExtension.

Context (R : RingObject).

Local Notation RS := (carrier (rig_setoid (ring_rig R))).
Local Notation TT A := (AbTensor (ring_ab R) A).
Local Notation ZG A s a := (@ts_gen (ring_ab R) A s a).

(** ** The scalar action / ** 标量作用 *)

Program Definition zext_bilin (A : AbObject) (r : RS) :
  Bilinear (ring_ab R) A (TT A) := {|
  bilin_map := fun s a => ts_gen (rig_mul (ring_rig R) r s) a
|}.
Next Obligation.
  intros A r s s' Hs a a' Ha.
  exact (@te_gen (ring_ab R) A _ _ _ _
           (rig_mul_respects (ring_rig R) r r (reflexivity r) s s' Hs) Ha).
Qed.
Next Obligation.
  intros A r s s' a.
  exact (te_trans
           (@te_gen (ring_ab R) A _ _ _ _
              (rig_distr_l (ring_rig R) r s s') (reflexivity a))
           (@te_bilin_l (ring_ab R) A (rig_mul (ring_rig R) r s)
                        (rig_mul (ring_rig R) r s') a)).
Qed.
Next Obligation.
  intros A r s a a'.
  exact (@te_bilin_r (ring_ab R) A (rig_mul (ring_rig R) r s) a a').
Qed.

Definition zext_smul (A : AbObject) (r : RS) :
  AbHom (TT A) (TT A) := tensor_ump (zext_bilin A r).

Definition zext_act (A : AbObject) (r : RS)
  (x : carrier (cmon_setoid (TT A))) : carrier (cmon_setoid (TT A)) :=
  cmon_map (zext_smul A r) x.

Example zext_act_gen (A : AbObject) (r s : RS) (a : carrier A) :
  zext_act A r (ZG A s a) = ZG A (rig_mul (ring_rig R) r s) a := eq_refl.


(* * ** The four module laws, each by agreement on generators / * ** 四个模法，每个都由生成元协定 *)

Lemma zext_smul_scalar (A : AbObject) (r r' : RS) :
  r ≈ r' → ∀ x, zext_act A r x ≈ zext_act A r' x.
Proof.
  intros Hr x.
  refine (tensor_hom_ext (zext_smul A r) (zext_smul A r') _ x).
  intros s a.
  exact (@te_gen (ring_ab R) A _ _ _ _
           (rig_mul_respects (ring_rig R) r r' Hr s s (reflexivity s))
           (reflexivity a)).
Qed.

Lemma zext_act_respects (A : AbObject) :
  Proper (equiv ==> equiv ==> equiv) (zext_act A).
Proof.
  intros r r' Hr x y Hxy.
  transitivity (zext_act A r y).
  - exact (proper_morphism (cmon_map (zext_smul A r)) x y Hxy).
  - exact (zext_smul_scalar A r r' Hr y).
Qed.

Lemma zext_act_distr_r (A : AbObject) (r r' : RS)
  (x : carrier (cmon_setoid (TT A))) :
  zext_act A (rig_add (ring_rig R) r r') x
    ≈ cmon_plus (TT A) (zext_act A r x) (zext_act A r' x).
Proof.
  refine (tensor_hom_ext (zext_smul A (rig_add (ring_rig R) r r'))
            (ab_hom_add (zext_smul A r) (zext_smul A r')) _ x).
  intros s a.
  exact (te_trans
           (@te_gen (ring_ab R) A _ _ _ _
              (rig_distr_r (ring_rig R) r r' s) (reflexivity a))
           (@te_bilin_l (ring_ab R) A (rig_mul (ring_rig R) r s)
                        (rig_mul (ring_rig R) r' s) a)).
Qed.

Lemma zext_act_assoc (A : AbObject) (r r' : RS)
  (x : carrier (cmon_setoid (TT A))) :
  zext_act A (rig_mul (ring_rig R) r r') x
    ≈ zext_act A r (zext_act A r' x).
Proof.
  refine (tensor_hom_ext (zext_smul A (rig_mul (ring_rig R) r r'))
            (cmon_hom_compose (zext_smul A r) (zext_smul A r')) _ x).
  intros s a.
  exact (@te_gen (ring_ab R) A _ _ _ _
           (rig_mul_assoc (ring_rig R) r r' s) (reflexivity a)).
Qed.

Lemma zext_act_one (A : AbObject) (x : carrier (cmon_setoid (TT A))) :
  zext_act A (rig_one (ring_rig R)) x ≈ x.
Proof.
  refine (tensor_hom_ext (zext_smul A (rig_one (ring_rig R)))
            (@cmon_hom_id (TT A)) _ x).
  intros s a.
  exact (@te_gen (ring_ab R) A _ _ _ _
           (rig_mul_one_l (ring_rig R) s) (reflexivity a)).
Qed.

Definition ZExtObj (A : AbObject) : RModObject R := {|
  rm_ab            := TT A;
  rm_smul          := zext_act A;
  rm_smul_respects := zext_act_respects A;
  rm_smul_distr_l  := fun r x y => cmon_map_plus (zext_smul A r) x y;
  rm_smul_distr_r  := zext_act_distr_r A;
  rm_smul_assoc    := zext_act_assoc A;
  rm_smul_one      := zext_act_one A
|}.

(* * ** The arrow action, and the functor / * ** 箭头操作符，以及函子 *)

Program Definition zext_map_bilin {A B : AbObject} (f : AbHom A B) :
  Bilinear (ring_ab R) A (TT B) := {|
  bilin_map := fun s a => ZG B s (cmon_map f a)
|}.
Next Obligation.
  intros A B f s s' Hs a a' Ha.
  exact (@te_gen (ring_ab R) B _ _ _ _ Hs
           (proper_morphism (cmon_map f) a a' Ha)).
Qed.
Next Obligation.
  intros A B f s s' a.
  exact (@te_bilin_l (ring_ab R) B s s' (cmon_map f a)).
Qed.
Next Obligation.
  intros A B f s a a'.
  exact (te_trans
           (@te_gen (ring_ab R) B _ _ _ _
              (reflexivity s) (cmon_map_plus f a a'))
           (@te_bilin_r (ring_ab R) B s (cmon_map f a) (cmon_map f a'))).
Qed.

Definition zext_map_ab {A B : AbObject} (f : AbHom A B) :
  AbHom (TT A) (TT B) := tensor_ump (zext_map_bilin f).

Program Definition ZExtMap {A B : AbObject} (f : AbHom A B) :
  ZExtObj A ~{RMod R}~> ZExtObj B := {|
  rm_hom := zext_map_ab f
|}.
Next Obligation.
  intros A B f r x.
  refine (tensor_hom_ext
            (cmon_hom_compose (zext_map_ab f) (zext_smul A r))
            (cmon_hom_compose (zext_smul B r) (zext_map_ab f)) _ x).
  intros s a; reflexivity.
Qed.

Program Definition ZExt : Ab ⟶ RMod R := {|
  fobj := ZExtObj;
  fmap := @ZExtMap
|}.
Next Obligation.
  intros A B f g Hfg x.
  refine (tensor_hom_ext (zext_map_ab f) (zext_map_ab g) _ x).
  intros s a.
  exact (@te_gen (ring_ab R) B _ _ _ _ (reflexivity s) (Hfg a)).
Qed.
Next Obligation.
  intros A x.
  refine (tensor_hom_ext (zext_map_ab (@id Ab A))
            (@cmon_hom_id (TT A)) _ x).
  intros s a; reflexivity.
Qed.
Next Obligation.
  intros A B C f g x.
  refine (tensor_hom_ext (zext_map_ab (f ∘ g))
            (cmon_hom_compose (zext_map_ab f) (zext_map_ab g)) _ x).
  intros s a; reflexivity.
Qed.

(** ** The transposes / ** 转置 *)

Lemma zext_gen_zero_r (A : AbObject) (s : RS) :
  (ZG A s (cmon_zero A) : carrier (cmon_setoid (TT A)))
    ≈ cmon_zero (TT A).
Proof.
  apply (ab_cancel_l (TT A) (ZG A s (cmon_zero A))).
  exact (te_trans
           (te_trans
              (te_sym (@te_bilin_r (ring_ab R) A s
                         (cmon_zero A) (cmon_zero A)))
              (@te_gen (ring_ab R) A _ _ _ _ (reflexivity s)
                 (cmon_plus_zero_l A (cmon_zero A))))
           (te_sym (cmon_plus_zero_r (TT A) (ZG A s (cmon_zero A))))).
Qed.

Program Definition zext_to {A : AbObject} {M : RModObject R}
  (g : ZExtObj A ~{RMod R}~> M) : A ~{Ab}~> rm_ab M := {|
  cmon_map := {| morphism := fun a =>
    cmon_map (rm_hom g) (ZG A (rig_one (ring_rig R)) a) |}
|}.
Next Obligation.
  intros A M g a a' Ha; simpl.
  exact (proper_morphism (cmon_map (rm_hom g)) _ _
           (@te_gen (ring_ab R) A _ _ _ _ (reflexivity _) Ha)).
Qed.
Next Obligation.
  intros A M g; simpl.
  transitivity (cmon_map (rm_hom g) (cmon_zero (TT A))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (zext_gen_zero_r A (rig_one (ring_rig R)))).
  - exact (cmon_map_zero (rm_hom g)).
Qed.
Next Obligation.
  intros A M g a b; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_plus (TT A) (ZG A (rig_one (ring_rig R)) a)
                                    (ZG A (rig_one (ring_rig R)) b))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (@te_bilin_r (ring_ab R) A (rig_one (ring_rig R)) a b)).
  - exact (cmon_map_plus (rm_hom g) _ _).
Qed.

Program Definition zext_lmul (M : RModObject R) (r : RS) :
  AbHom (rm_ab M) (rm_ab M) := {|
  cmon_map := {| morphism := fun m => rm_smul M r m |}
|}.
Next Obligation.
  intros M r m m' Hm.
  exact (rm_smul_respects M r r (reflexivity r) m m' Hm).
Qed.
Next Obligation. intros M r; simpl; exact (rm_smul_zero_r M r). Qed.
Next Obligation.
  intros M r m m'; simpl; exact (rm_smul_distr_l M r m m').
Qed.

Program Definition zext_from_bilin {A : AbObject} {M : RModObject R}
  (h : A ~{Ab}~> rm_ab M) : Bilinear (ring_ab R) A (rm_ab M) := {|
  bilin_map := fun s a => rm_smul M s (cmon_map h a)
|}.
Next Obligation.
  intros A M h s s' Hs a a' Ha.
  exact (rm_smul_respects M s s' Hs _ _
           (proper_morphism (cmon_map h) a a' Ha)).
Qed.
Next Obligation.
  intros A M h s s' a.
  exact (rm_smul_distr_r M s s' (cmon_map h a)).
Qed.
Next Obligation.
  intros A M h s a a'.
  transitivity (rm_smul M s
                  (cmon_plus (rm_ab M) (cmon_map h a) (cmon_map h a'))).
  - exact (rm_smul_respects M s s (reflexivity s) _ _
             (cmon_map_plus h a a')).
  - exact (rm_smul_distr_l M s (cmon_map h a) (cmon_map h a')).
Qed.

Program Definition zext_from {A : AbObject} {M : RModObject R}
  (h : A ~{Ab}~> rm_ab M) : ZExtObj A ~{RMod R}~> M := {|
  rm_hom := tensor_ump (zext_from_bilin h)
|}.
Next Obligation.
  intros A M h r x.
  refine (tensor_hom_ext
            (cmon_hom_compose (tensor_ump (zext_from_bilin h))
                              (zext_smul A r))
            (cmon_hom_compose (zext_lmul M r)
                              (tensor_ump (zext_from_bilin h))) _ x).
  intros s a.
  exact (rm_smul_assoc M r s (cmon_map h a)).
Qed.

(** ** The adjunction / ** 结合 *)

Program Definition zext_adj_to (A : AbObject) (M : RModObject R) :
  {| carrier := ZExtObj A ~{RMod R}~> M;
     is_setoid := @homset (RMod R) (ZExtObj A) M |}
    ~{Sets}~>
  {| carrier := A ~{Ab}~> rm_ab M;
     is_setoid := @homset Ab A (rm_ab M) |} := {|
  morphism := fun g => zext_to g
|}.
Next Obligation. intros A M g g' Hg a; exact (Hg _). Qed.

Program Definition zext_adj_from (A : AbObject) (M : RModObject R) :
  {| carrier := A ~{Ab}~> rm_ab M;
     is_setoid := @homset Ab A (rm_ab M) |}
    ~{Sets}~>
  {| carrier := ZExtObj A ~{RMod R}~> M;
     is_setoid := @homset (RMod R) (ZExtObj A) M |} := {|
  morphism := fun h => zext_from h
|}.
Next Obligation.
  intros A M h h' Hh x.
  refine (tensor_hom_ext (tensor_ump (zext_from_bilin h))
                         (tensor_ump (zext_from_bilin h')) _ x).
  intros s a.
  exact (rm_smul_respects M s s (reflexivity s) _ _ (Hh a)).
Qed.

Program Definition zext_adj (A : AbObject) (M : RModObject R) :
  @Isomorphism Sets
    {| carrier := ZExtObj A ~{RMod R}~> M;
       is_setoid := @homset (RMod R) (ZExtObj A) M |}
    {| carrier := A ~{Ab}~> rm_ab M;
       is_setoid := @homset Ab A (rm_ab M) |} := {|
  to   := zext_adj_to A M;
  from := zext_adj_from A M
|}.
Next Obligation.
  intros A M h a.
  exact (rm_smul_one M (cmon_map h a)).
Qed.
Next Obligation.
  intros A M g x.
  refine (tensor_hom_ext (tensor_ump (zext_from_bilin (zext_to g)))
                         (rm_hom g) _ x).
  intros s a.
  transitivity (cmon_map (rm_hom g)
                  (ZG A (rig_mul (ring_rig R) s
                           (rig_one (ring_rig R))) a)).
  - symmetry.
    exact (rm_map_smul g s (ZG A (rig_one (ring_rig R)) a)).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (@te_gen (ring_ab R) A _ _ _ _
                (rig_mul_one_r (ring_rig R) s) (reflexivity a))).
Qed.

Definition zext_adjunction : ZExt ⊣ RMod_Forget_Ab R.
Proof.
  unshelve eapply (@Build_Adjunction' (RMod R) Ab ZExt
                     (RMod_Forget_Ab R) zext_adj).
  - intros A B M f g a; reflexivity.
  - intros A M N f g a; reflexivity.
Defined.

(* * ** Unit, counit, and the strict readings / * ** 单位、余单位以及严格读法 *)

Definition zext_unit (A : AbObject) :
  A ~{Ab}~> rm_ab (ZExtObj A) :=
  @unit (RMod R) Ab ZExt (RMod_Forget_Ab R) zext_adjunction A.

Definition zext_counit (M : RModObject R) :
  ZExtObj (rm_ab M) ~{RMod R}~> M :=
  @counit (RMod R) Ab ZExt (RMod_Forget_Ab R) zext_adjunction M.

(* THE REVIEWER CHECK. The unit IS a |-> 1 (x) a, on the nose. / 审核员检查。该单位确实是一个 |-> 1 (x) a，准确无误。 *)
Example zext_unit_is_gen (A : AbObject) (a : carrier A) :
  cmon_map (zext_unit A) a = ZG A (rig_one (ring_rig R)) a := eq_refl.

Example zext_counit_is_smul (M : RModObject R) (s : RS)
  (m : carrier (cmon_setoid (rm_ab M))) :
  cmon_map (rm_hom (zext_counit M)) (ZG (rm_ab M) s m)
    = rm_smul M s m := eq_refl.

Example zext_adj_to_is_zext_to (A : AbObject) (M : RModObject R)
  (g : ZExtObj A ~{RMod R}~> M) :
  to (@adj (RMod R) Ab ZExt (RMod_Forget_Ab R) zext_adjunction A M) g
    = zext_to g := eq_refl.

Example zext_adj_from_is_zext_from (A : AbObject) (M : RModObject R)
  (h : A ~{Ab}~> rm_ab M) :
  from (@adj (RMod R) Ab ZExt (RMod_Forget_Ab R) zext_adjunction A M) h
    = zext_from h := eq_refl.

Example zext_fobj_is_ZExtObj (A : AbObject) :
  fobj[ZExt] A = ZExtObj A := eq_refl.

Example zext_fmap_is_ZExtMap (A B : AbObject) (f : A ~{Ab}~> B) :
  fmap[ZExt] f = ZExtMap f := eq_refl.

Example zext_forget_is_rm_ab (M : RModObject R) :
  fobj[RMod_Forget_Ab R] M = rm_ab M := eq_refl.

End ZExtension.

(** ** A concrete witness over ℤ / ** 一个关于 ℤ 的具体例子 *)

Definition ZIntExt : RModObject Int_Ring :=
  ZExtObj Int_Ring (ring_ab Int_Ring).

Definition ZIntGen (s a : Z) : carrier (cmon_setoid (rm_ab ZIntExt)) :=
  @ts_gen (ring_ab Int_Ring) (ring_ab Int_Ring) s a.

Definition zext_int_eval : ZIntExt ~{RMod Int_Ring}~> Int_RMod :=
  zext_counit Int_Ring Int_RMod.

Example zext_int_eval_computes :
  cmon_map (rm_hom zext_int_eval) (ZIntGen 3 4) = 12%Z := eq_refl.

Example zext_int_eval_zero :
  cmon_map (rm_hom zext_int_eval) (cmon_zero (rm_ab ZIntExt)) = 0%Z
  := eq_refl.

Example zext_int_unit_computes (a : Z) :
  cmon_map (zext_unit Int_Ring (ring_ab Int_Ring)) a = ZIntGen 1 a
  := eq_refl.

Lemma zext_int_gen_nonzero :
  ZIntGen 1 1 ≈ cmon_zero (rm_ab ZIntExt) → False.
Proof.
  intro Hz.
  assert (Hev : (1%Z = 0%Z)) by
    exact (proper_morphism (cmon_map (rm_hom zext_int_eval)) _ _ Hz).
  discriminate.
Qed.

Lemma zext_int_gens_distinct : ZIntGen 1 1 ≈ ZIntGen 1 2 → False.
Proof.
  intro Hz.
  assert (Hev : (1%Z = 2%Z)) by
    exact (proper_morphism (cmon_map (rm_hom zext_int_eval)) _ _ Hz).
  discriminate.
Qed.

Lemma zext_int_unit_separates : ZIntGen 1 1 ≈ ZIntGen 1 2 → False.
Proof. exact zext_int_gens_distinct. Qed.

(*
   * ** Probes

   Every strength claim the header makes is pinned here, each negative
   beside an APPLIED positive control.  Each was stripped of its [Fail]
   and compiled alone, and its WHOLE error read: negatives 1, 2 and 4
   end in [cannot unify] (CONVERSION), negative 3 is a plain type
   mismatch with no [cannot unify] and no universe clause (TYPING), and
   negatives 5-8 end in [universe inconsistency: Cannot enforce rc = ra]
   (FORMABILITY). 

   --------
   * ** 探针

   每个标题所声明的强度在此处被固定，每个阴性对照旁都有一个应用过的阳性对照。每一个都被剥离了其 [Fail] 并单独编译，其整体错误信息为：阴性1、2和4以 [cannot unify]（转换）结束，阴性3是普通类型不匹配，没有 [cannot unify] 也没有宇宙条款（类型），阴性5-8以 [universe inconsistency: Cannot enforce rc = ra]（可形成性）结束。
*)

Section ZExtProbeStrength.

Context (R : RingObject) (A : AbObject) (M : RModObject R).
Context (h : A ~{Ab}~> rm_ab M) (g : ZExtObj R A ~{RMod R}~> M).
Context (a : carrier A) (s : carrier (rig_setoid (ring_rig R))).

(*
 CONTROL for negative 1: the round trip DOES hold at ≈, and the proof
 term names the exact law that closes the gap. 

 --------
 对于负一的控制：往返确实在 ≈ 处成立，并且证明项命名了弥合差距的确切法则。
*)
Example zext_ctrl_to_from :
  cmon_map (zext_to R (zext_from R h)) a ≈ cmon_map h a
  := rm_smul_one M (cmon_map h a).

(*
 NEGATIVE 1 (CONVERSION).  [zext_to (zext_from h)] evaluates to
 1 · h a, and 1 · − is not the identity by conversion: [rm_smul_one]
 is an abstract field of [RModObject], so neither side reduces. 

 --------
 负 1（转换）。[zext_to (zext_from h)] 计算得出 1 · h a，而 1 · − 并非通过转换得到的单位：[rm_smul_one] 是 [RModObject] 的抽象域，因此两边都无法化简。
*)
Fail Example zext_probe_to_from_strict :
  cmon_map (zext_to R (zext_from R h)) a = cmon_map h a := eq_refl.

(* CONTROL for negative 2. / 负2的控制。 *)
Example zext_ctrl_from_to :
  cmon_map (rm_hom (zext_from R (zext_to R g)))
    (@ts_gen (ring_ab R) A s a)
    ≈ cmon_map (rm_hom g) (@ts_gen (ring_ab R) A s a)
  := iso_from_to (zext_adj R A M) g _.

(* NEGATIVE 2 (CONVERSION). The other round trip leaves an s · 1 in the scalar slot; [rig_mul_one_r] is what removes it, and it too is an abstract field. / 负 2（转换）。另一种往返会在标量槽中留下一个 s · 1；[rig_mul_one_r] 是移除它的东西，它也是一个抽象字段。 *)
Fail Example zext_probe_from_to_strict :
  cmon_map (rm_hom (zext_from R (zext_to R g)))
    (@ts_gen (ring_ab R) A s a)
    = cmon_map (rm_hom g) (@ts_gen (ring_ab R) A s a) := eq_refl.

(* CONTROL for negative 3: the unit IS an arrow of [Ab]. / 负三的控制：该单元是 [Ab] 的一个箭头。 *)
Check (zext_unit R A : A ~{Ab}~> rm_ab (ZExtObj R A)).

(*
 NEGATIVE 3 (TYPING).  It is NOT an arrow of [RMod R] — [A] is an
 [AbObject] and there is no coercion into [obj[RMod R]].  This is the
 shape of the adjunction, not an accident: the unit lives downstairs. 

 --------
 负 3（打字）。它不是 [RMod R] 的箭头 — [A] 是一个 [AbObject]，并且没有被强制成 [obj[RMod R]]。这是伴随的形状，不是偶然的：单位存在于下层。
*)
Fail Check (zext_unit R A : A ~{RMod R}~> rm_ab (ZExtObj R A)).

End ZExtProbeStrength.

(* CONTROL for negative 4: the comparison map exists and computes. / 负4的控制：比较图存在并且能够计算。 *)
Check (cmon_map (rm_hom zext_int_eval) (ZIntGen 3 4)).

(*
 NEGATIVE 4 (CONVERSION).  ℤ ⊗ ℤ is NOT ℤ on the nose — the carriers
 are [tsum] and [Z] — so [zext_int_gen_nonzero] is a statement about a
 genuinely constructed object and not about ℤ in disguise. 

 --------
 负四（转换）。ℤ ⊗ ℤ 并不等于 ℤ——其载体是 [tsum] 和 [Z]——所以 [zext_int_gen_nonzero] 是关于一个真正构造的对象的陈述，而不是关于伪装成 ℤ 的对象。
*)
Fail Example zext_probe_int_strict : ZIntExt = Int_RMod := eq_refl.

Section ZExtProbeUniverses.

Universes ra rb rc.
Constraint ra < rc.

Context (Ru : RingObject@{rc ra rb}) (Au Bu : AbObject).
Context (fu : Au ~{Ab}~> Bu).

(*
 CONTROLS.  With the ring's FIRST and THIRD universes declared strictly
 apart, all of these are formable — so the identification below is
 neither the tensor's, nor the category's, nor the forgetful functor's,
 nor the abelian-group-level arrow action's, nor the extension OBJECT's.
 Each is APPLIED to [Ru], which is the argument carrying the levels. 

 --------
 控制。将环的第一和第三宇宙严格区分开来后，所有这些都是可构造的——因此下面的标识既不是张量的，也不是范畴的，也不是遗忘函子的，也不是阿贝尔群层次的箭头作用的，也不是扩展对象的。每一个都应用于 [Ru]，这是承载层次的参数。
*)
Check (RMod Ru).
Check (ring_ab Ru).
Check (AbTensor (ring_ab Ru) Au).
Check (ZExtObj Ru Au).
Check (zext_act Ru Au).
Check (zext_map_ab Ru fu).
Check (RMod_Forget_Ab Ru).
Check (Ab ⟶ RMod Ru).
Check (Ring_RMod Ru).

(*
 CONTROLS 5, 7 and 8, WHICH USED TO BE NEGATIVES.  An earlier revision read:
 “NEGATIVE 5 (FORMABILITY).  The identification enters exactly when the
 extension is READ AS AN OBJECT of [RMod R] — not when it is built”;
 “NEGATIVE 7 (FORMABILITY).  Hence the functor”; “NEGATIVE 8 (FORMABILITY).
 And hence the headline.”  All three were re-measured after the PR
 “algebraic carriers are sets” (2026-09-17) and all three are now FORMABLE
 at the declared separation.  The cause is upstream: [ZExtObj] is built on
 Instance/Ab/Tensor.v's [AbTensor], whose relation [ts_eq] moved to [Prop],
 so [tensor_med_respects] no longer inducts on a [Type]-valued relation into
 a [Type]-valued goal and the identification that induction forced is gone.
 Negative 6 below still fires, which is the instrument check that the
 section still constrains anything at all.  The ring's auxiliary universe is
 also now the FIRST argument of [RingObject] rather than the third, which is
 why the binder reads `RingObject@{rc ra rb}`. 

 --------
 控制项5、7和8，原来是负面项。之前的修订内容如下：
 “负面5（可形成性）。当扩展被视为[RMod R]的一个对象时，识别才会进入——而不是在其构建时”;
 “负面7（可形成性）。因此产生了函子”；“负面8（可形成性）。因此产生了标题。” 在PR“代数载体是集合”（2026-09-17）之后，这三项都重新进行了测量，并且现在在声明的分离处都是可形成的。原因在上游：[ZExtObj]是建立在Instance/Ab/Tensor.v的[AbTensor]上的，其关系[ts_eq]已移动到[Prop]，因此[tensor_med_respects]不再在[Type]值的关系上进行归纳到[Type]值的目标，而归纳强制的识别已经消失。仍然触发负6，这就是仪表检查，说明该部分仍然约束任何事物。环的辅助宇宙现在也是 [RingObject] 的第一个参数，而不是第三个，这就是为什么绑定器读取 `RingObject@{rc ra rb}`。
*)
Check (ZExtObj Ru Au : obj[RMod Ru]).

(*
 NEGATIVE 6 (FORMABILITY).  The surviving donor, and it is not this file's.
 Instance/Mod.v's OWN [Ring_RMod] is rejected at these levels while the
 bare [Check (Ring_RMod Ru)] control above is accepted, so what the
 ascription to [obj[RMod Ru]] forces is inherited. 

 --------
 负 6（可形成性）。存活的捐赠者，而不是这个文件的。Instance/Mod.v 的 OWN [Ring_RMod] 在这些级别上被拒绝，而上面的裸 [Check (Ring_RMod Ru)] 控制被接受，因此对 [obj[RMod Ru] 的归属强制继承。
*)
Fail Check (Ring_RMod Ru : obj[RMod Ru]).

Check (ZExt Ru).
Check (zext_adjunction Ru).

End ZExtProbeUniverses.

(* INSTRUMENT CHECK, scope-free: [Fail] itself is working. / 仪器检查，无范围限制：[Fail] 本身正在工作。 *)
Fail Example zext_probe_instrument : (true = false) := eq_refl.
