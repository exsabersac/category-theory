(*
   * * Watt's theorem with no hypothesis: every additive T : (R-Mod)^op ⟶ Ab
   carrying colimits to limits is Hom(−, A) 

   --------
   * * 瓦特定理无假设：每个加性函子 T : (R-Mod)^op ⟶ Ab 将余极限映射为极限，即 Hom(−, A)
*)

(*
 Book:      Mac Lane, “Categories for the Working Mathematician”, 2nd
 ed. (GTM 5), §V.8, printed p. 131 (PDF p. 140; ledger item
 `maclane:V.8:thm-watt`, issue #454), read from the printed
 page: “any contravariant additive functor T on R-Mod to Ab
 which takes small colimits to limits is representable by a
 group isomorphism T ≅ hom_R(−, C) for some R-module C”.  (The
 in-repo catalog, doc/plan/books/maclane/inventory/V.json,
 summarises it in its own words, “every contravariant
 additive functor T on R-Mod to Ab which carries small
 colimits to limits is representable: T is naturally
 isomorphic to hom_R(-, C) for some R-module C”.)
 Book:      Mac Lane, ibid., §V.6 Theorem 3 and Definition 3 — the
 representability theorem with its element-wise solution set
 condition, Adjunction/Representability/Sets.v, which is the
 theorem actually applied here.
 nLab:      https://ncatlab.org/nlab/show/Eilenberg-Watts+theorem
 nLab:      https://ncatlab.org/nlab/show/adjoint+functor+theorem
 nLab:      https://ncatlab.org/nlab/show/representable+functor

 A DEVIATION, STATED PLAINLY.  The issue asks for Watt's theorem
 “derived from SAFT”, and its Reviewer line reads “the representability
 must be derived from SAFT plus additivity”.  This file does NOT use the
 special adjoint functor theorem.  It applies the GENERAL one, in the
 form of Mac Lane's §V.6 Theorem 3 ([representability_theorem], whose
 proof is Adjunction/GAFT.v's comma-initial step), to an explicit
 element-wise solution set, and the covering step of that solution set
 is the Eilenberg–Watts construction read in solution-set form.  The
 reason is measured, not preferred: SAFT at (R-Mod)^op asks for the
 co-well-poweredness of R-Mod, which the tree has only under the
 hypothesis [Untruncate] (Instance/Mod/WellPowered.v's
 [RMod_CoWellPowered_untruncate]; that header quotes the refusals
 without it), and its cogenerator [RModop_Cogenerator] exists only at
 [RingObject@{c c c}].  The route here needs neither, so it delivers the
 book's contravariant statement with NO hypothesis beyond the book's
 own two.  “Plus additivity” is kept verbatim: the Ab-level conclusion
 is Functor/Representable/Additive.v's [watt_ab_iso].  #454's
 SAFT-derived conditional form is not replaced by this file.

 THE HEADLINE, AND THE SAFT ROUTE.  For the book's contravariant
 statement this file is #454's headline.  Instance/Mod/Watts.v keeps
 Mac Lane's own route, the one the Reviewer line names, as
 [watts_theorem]: SAFT at (RMod R)^op, under the hypothesis
 [Untruncate] and with the ring at [RingObject@{c c c}].  Its statement
 is a special case of [watts_theorem_unconditional]'s, and Watts.v,
 which imports this file, derives it from this theorem in its section
 6 ([watts_theorem_via_unconditional], with [Untruncate] carried and not
 consumed); the SAFT route is kept for its fidelity to the Reviewer
 line, not for its strength.  Of Watts.v's constants, this theorem
 subsumes three.  The first is [watts_theorem], in tree as just said.
 The second is [watts_theorem_coext]: its statement elaborates verbatim
 from [watts_theorem_unconditional] at [HomAbForget R A], closed and
 with no universe equation.  The third is [watts_theorem_sets], but
 only at the instance whose second [Representable] universe is RMod's
 object universe, since [RModop_continuous_representable] returns a
 [Representable@{u o s o c}]; the same elaboration reads back
 [o = rt].  (Both measured in a scratch file importing Watts.v, with
 each statement copied from Watts.v and [U] left unused.)
 [watts_theorem_coext_obj] and [watts_theorem_coext_obj_2a] have
 unconditional counterparts, Watts.v's [watts_unconditional_coext] and
 [watts_unconditional_coext_2a], which identify the module THIS theorem
 returns.  Not subsumed: [watts_theorem_adjoint], the book's left
 adjoint of T, which only SAFT builds here, and [watts_theorem_Fz], the
 comparison with it; the readbacks [watts_theorem_obj] and
 [watts_theorem_to_at], which are about the SAFT object; and the
 covariant Exercise 3 family ([watts_ex3], [watts_ex3_sets],
 [watts_ex3_QZ], [watts_ex3_QZ_cogenerator], [watts_ex3_forget],
 [watts_ex3_forget_obj]).  Watts.v's other constants
 ([RMod_Forget_Ab_additive], [RMod_Forget_equiv], [watt_at_forget],
 [HomAbForget], [HomAbForget_additive], [HomAbForget_continuous],
 [coext_representable], [Ab_Forget_Id_equiv], [ab_hom_Z_iso]) carry no
 hypothesis to remove.

 WHAT IS CONSUMED.  Adjunction/Representability/Sets.v's
 [representability_theorem] and [ElementSolutionSet];
 Instance/Mod/Colimit.v's [RMod_Cocomplete_via_GAFT], read in the
 opposite by Construction/Product/Limit.v's [Complete_op_of_Cocomplete];
 Instance/Mod/Free.v's [FreeModObject], [fv_gen] and [fv_extend];
 Instance/Mod/WellPowered.v's [PSubmodule], [psm_sub] and [pker];
 Instance/Mod/Quotient.v's [QuotientMod] and [mquot_med];
 Instance/Discrete.v's [DiscreteCat_Functor];
 Functor/Representable/Additive.v's [CoHomAb], [HomAb_additive],
 [HomAb_representable], [CoHomAb_continuous], [LocallyPropositional_op],
 [watt_ab_iso] and [wab_obj]; Adjunction/Additive.v's [AbEnriched_op];
 Instance/Ab/Limit.v's [Ab_Forget_creates_continuous];
 Structure/Limit/Preservation.v's [continuous_compose] and [FCone];
 Construction/Comma/Creation.v's [Continuous_PreservesImageLimit];
 Functor/Hom/Continuous.v's [hom_continuous_at].

 WHAT IS BUILT.

 - [MultiSpan X], a thin shape: nodes [ms_mod], [ms_free] and
 [ms_gen m] for m : X, with one arrow from each [ms_gen m] to each of
 the other two; [ms_diagram] draws it in any category.
 - [sets_limit_point]: a compatible family of elements over a limiting
 cone of setoids is the image of one element of the apex (the
 mediator out of the singleton cone, at its point).
 - [ew_Gen], the free module on one generator [ew_g0], and [ew_ev m],
 the homomorphism sending [ew_g0] to m ([ew_ev_g0] at [eq_refl]).
 - **[RModop_esols K contK : ElementSolutionSet K]** for every
 continuous K : (RMod R)^op ⟶ Sets, and
 **[RModop_continuous_representable K contK : Representable K]**.
 - **[watts_theorem_unconditional T AF contT]**: for T : (RMod R)^op ⟶
 Ab additive and continuous, a module A with [CoHomAb A ≅ T] in the
 functor category, i.e. T ≅ Hom_R(−, A) as Ab-valued functors.
 - The witnesses of NON-VACUITY below.  The continuity of the
 Ab-valued hom functors, [HomAb_continuous] and
 [CoHomAb_continuous], is not built here but consumed from
 Functor/Representable/Additive.v.

 THE ARGUMENT.  Fix a continuous K : (R-Mod)^op ⟶ Sets.  Let Cop be the
 coproduct of copies of [ew_Gen], one for each element i of K(ew_Gen),
 with injections inj_i ([ew_Cop], [ew_inj]); it is ONE module, fixed
 once K is.  K carries it to a product, so the tautological family
 i ↦ i is the image of one y0 in K(Cop) ([ew_y0_leg]).  Now take any
 module M and any x in K(M).  Put a_m := K(ev_m)(x) in K(ew_Gen) and let
 P be the colimit of the multi-span M ← ew_Gen → Cop, drawn once for
 each m, by ev_m and inj_{a_m}.  Its legs identify inj_{a_m}(g0) with m
 ([ew_key]).  K carries P to a limit, and (x, y0, (a_m)_m) is a
 compatible family over it (by the definition of a_m and by y0's), so
 it is the image of one e in K(P) ([ew_e_leg]).  The member of the
 solution set is Q := Cop / N, with N the [Prop] kernel of the leg
 Cop → P ([ew_N], a [PSubmodule] of the fixed Cop, and [ew_Q]).  The map
 t : M → Q is m ↦ [inj_{a_m}(g0)] ([ew_t_at] at [eq_refl]).  NO CHOICE is
 made anywhere: the generator of each copy is an explicit element, where
 the SAFT route must invert an epi.  The quotient maps into P by
 [mquot_med] ([ew_k], with k ∘ t ≈ the leg at M, [ew_k_t]), so
 K(t)(K(k)(e)) ≈ x ([ew_t_covers]).  The index, a [PSubmodule] of Cop
 paired with an element of K at the quotient ([ew_WIdx]), sits at the
 carrier universe, which is where [representability_theorem] pins it.
 The route is GAFT over a [Prop]-indexed family of quotients of one
 free module, with two choices made against the evident ones.  The
 free module on one generator stands in for the ring, which avoids
 [Ring_RMod]'s collapse of the ring's universes.  And one multi-span
 colimit replaces the pushout of the canonical free presentation
 F(U M) → M, so K is never evaluated at F(U M) and no joint
 monicity is needed.  Additivity is not used for [RModop_esols]; it
 enters only through [watt_ab_iso].

 STRENGTHS, strict first.  At [eq_refl]: [ew_ev_g0] (evaluation at the
 generator), [ew_t_at] (the covering map on the nose) and
 [watts_theorem_unconditional_obj] (the representing module IS the
 object [representability_theorem] produces for [Ab_Forget ◯ T]); the
 two components of the isomorphism ARE the representation's, by
 Functor/Representable/Additive.v's [watt_ab_iso_to_at] and
 [watt_ab_iso_from_at].  Up to ≈: the covering ([ew_t_covers]) and the
 natural isomorphism, componentwise in the functor category.  Up to ≅:
 the witnesses' identification of the module found with the expected
 one.  Flip census, each [Defined] turned to [Qed] one at a time in a
 copy of the whole file: 12 [Defined] (counted by token outside
 comments), of which six are LOAD-BEARING.  [ms_fmap] stops
 [ms_diagram]'s first obligation, [ew_efam] stops [ew_e_ex]'s coherence
 case, [ew_k] stops [ew_k_t], [ew_ev] stops [ew_ev_g0], [ew_t] stops
 [ew_t_at], and [watts_theorem_unconditional] stops
 [watts_theorem_unconditional_obj].  Six recompile as [Qed]: [ms_id],
 [ms_comp], [sets_limit_point], [ew_y0_ex], [ew_e_ex] and
 [RModop_esols].  They are kept [Defined] because they produce data.

 UNIVERSES, measured by [About] under [Set Printing Universes], stdlib
 bounds omitted.

 watts_theorem_unconditional@{a c p o x b s …} :
 ∀ {R : RingObject@{a c p}} (T : (RMod@{o x a p c} R)^op ⟶ Ab@{b c}),
 AdditiveFunctor@{o c b} T → ContinuousFunctor@{u u o c b c c b o s} T
 → { A & CoHomAb@{o c b} (RMod_AbEnriched@{x o a p c} R) A ≅ T }
 ( * Set < c, Set < o, Set < b, c < o, c < x, c < b, c < s, c <= a,
 p <= a, a <= o, … — no equation * )

 RModop_continuous_representable@{a c p o x s …} :
 ∀ {R : RingObject@{a c p}} (K : (RMod@{o x a p c} R)^op ⟶ Sets@{c s}),
 ContinuousFunctor@{u u o c s c c s o s} K → Representable K
 ( * Set < c, Set < o, c < o, c < x, c < s, … — no equation * )

 The ring keeps its three universes APART.  The SAFT route's
 [RModop_Cogenerator] is at [RingObject@{c c c}], and here nothing
 identifies them: [watts_unconditional_at_Z] instantiates the theorem
 at [Int_Ring@{c p a}] with the three distinct.  [Set < c] is GENUINE:
 deleted from [RModop_continuous_representable]'s binder in a copy of
 the whole file, it is re-inferred.  Deleted from the section's
 [Constraint], it is re-added per constant, first at [ew_CC] (the
 cocompleteness, Instance/Mod/Colimit.v's [Set < c]), and not at
 [ew_Idx] or [ew_CopD].  [PSubmodule]'s sort, [Type@{max(Set+1,m3)}] by
 its [About], would need it again for [ew_WIdx : Type@{c}].  So ℤ with
 its carrier at [Set] is excluded, and ℤ above [Set] is not.
 Test/ProbeWatts454.v pins this: its N24 refuses
 [watts_unconditional_at_Z] at a module of [RMod@{o x Set Set Set}
 Int_Ring@{Set Set Set}], and its N25 refuses the theorem itself at
 [RingObject@{Set Set Set}], beside the controls [p454_unc_Z_ccc] and
 [p454_unc_Z_apart] (ℤ above [Set], its universes collapsed and apart),
 [p454_rmod_at_set] (the category of ℤ-modules at a [Set] carrier is
 formed, so the refusals are the theorem's) and [p454_unc_apart] (a
 ring above [Set] with its three universes strictly apart); its
 [p454_unc_x_below_s] and [p454_unc_s_below_x] accept the theorem with
 x and s apart in both orders.  The only universe equations in
 the module ([About] on all of its 67 names)
 are c = u2 and c = u4 on the continuity hypothesis's own instance: its
 shape-object slot and a universe of its [IsLimitCone]s.  They are
 carried by [RModop_esols] and by the nine section constants that use
 the hypothesis, and they sit at the carrier because the hypothesis is
 used at [MultiSpan@{c}] and [DiscreteCat@{c c c}], the shape universe
 [representability_theorem] fixes.  The two headlines and the
 witnesses carry none.  Three auxiliary universes are pinned by name in
 the covering section: w for [DiscreteCat_Functor] and [ms_diagram],
 and w0, w1 for [RMod_Cocomplete_via_GAFT].  Without them, measured in
 copies of the whole file, [ew_P] carried universes of its own.  Its
 first was instantiated at the continuity hypothesis's last slot inside
 [ew_e] and at x inside [ew_k], and their meeting at [ew_eQ] identified
 RMod's second universe x with that slot, which
 [representability_theorem] identifies with the target's s.  No single
 pin removed the equation; the three together do.  The statement's
 [ContinuousFunctor@{_ _ _ _ _ _ _ _ _ s} T] names that last slot for
 the same reason: left flexible, it was set to x, and [About] read back
 x = s until it was named.

 NON-VACUITY.  Functor/Representable/Additive.v's [CoHomAb_continuous]
 proves the contravariant Ab-valued hom functor continuous for every
 locally propositional Ab-enriched category.  So T := [CoHomAb A]
 meets both premises for EVERY ring and EVERY module A, and
 [watts_unconditional_CoHomAb_obj] shows that the module the theorem
 returns is isomorphic to A ([repr_unique_iso] against
 [HomAb_representable]).  [RModop_hom_representable_obj] is the same at
 the set-valued level, for the plain hom-functor.  At a concrete ring,
 [watts_unconditional_at_Z] instantiates all of it at ℤ.  These three
 feed the theorem a hom functor, whose representation is known in
 advance.  A witness that is not one is in Instance/Mod/Watts.v, which
 imports this file: its section 6 applies the theorem at
 [HomAbForget R A], M ↦ Hom_Ab(U M, A) for an abelian group A, whose
 continuity comes from the coextension adjunction rather than from a
 hom functor of RMod R.  [watts_unconditional_coext] identifies the
 module returned with [CoextObj R A] ([repr_unique_iso] against
 [coext_representable]), and [watts_unconditional_coext_2a] with
 Exercise 2(a)'s hom_ℤ(R, A).  Neither needs [Untruncate]; both are at
 [RingObject@{c c c}], which [CoextObj] imposes (Instance/Mod/
 Coextension.v).

 THE CONDITIONS, plainly.  T is additive; this is used only by the Ab
 upgrade.  T is continuous in the cone sense ([ContinuousFunctor]) at
 the shapes whose objects sit at the carrier universe.  The shape
 discipline is the one [Complete] and [representability_theorem]
 impose, so every colimit of modules over such a shape goes to a limit
 of groups; that is the book's “takes small colimits to limits”.
 Finally, [Set < c].  No
 [Untruncate], no cogenerator, no co-well-poweredness, no choice and no
 axiom: every constant of this module is “Closed under the global
 context”.

 SIZE.  374 non-blank lines of code once comments are stripped,
 including the 33 [Require]s.

 NOT DELIVERED.  Exercise 3 (the covariant form) is not delivered
 unconditionally: Instance/Mod/Watts.v delivers it only over
 [Untruncate] and a cogenerator of R-Mod, through the special adjoint
 functor theorem, whose solution set the cogenerator supplies.  No
 other route to it is attempted, and nothing in tree proves either
 hypothesis necessary.  What is proved classical is the book's ℚ/ℤ
 premise (Instance/Mod/Cogenerator.v's metatheorems), and [RMod R]
 well-powered at the pin without [Untruncate] is neither built nor
 refuted (Instance/Mod/WellPowered.v).  The representing module is not
 identified with T(R), or with T(ew_Gen), carrying the Eilenberg–Watts
 action.  It is the object the representability theorem produces, and
 only [repr_unique_iso] compares it with anything.  The module has no
 naturality in T and no functoriality of T ↦ A.  The additivity
 premise [AF] is redundant in principle and is not eliminated: a
 functor between additive categories that preserves finite products
 is additive, and a continuous T : (R-Mod)^op → Ab carries the zero
 module and binary direct sums, which are colimits of modules, to a
 terminal group and to products.  The statement keeps it because the
 book states it; that argument is not formalised here.  No [Instance]
 is registered.

 COQ 8.19 AND 8.20.  A dependency closure of 250 files, containing
 the seven development files #454 adds, this one among them, was
 built by [coq_makefile] with the nix-store Coq 8.19.2 and 8.20.1 and
 Equations 1.3: make rc=0 on each.  There [Print Assumptions] reports
 all 132 constants of Functor/Representable/Additive.v, this file and
 Watts.v closed, and the same ten constants carry the same two
 equations as on 9.1.  The copies were taken before a last round of
 comment-only edits; the code is the same modulo comments and
 whitespace, compared file by file.  The same two trees were then
 brought to the later sources, replacing the three files that differed
 from them (this one, Instance/Mod/Watts.v and
 Instance/Mod/Cogenerator.v, each in its header alone), and
 Test/ProbeWatts454.v, which pins this file's [Set] boundary as its N24
 and N25, was added: [coq_makefile] compiled those four files on each,
 make returned 0 on both, and the probe's stripped refutations are
 refused there as its header records.  Those closures are not the
 whole library; the Nix flake's builds of the committed revision are
 the authoritative gate, and docs/INDEX.md's bullet for this file
 records their result. 

 --------
 书籍：Mac Lane，《为工作中的数学家准备的范畴》，第2版（GTM 5），§V.8，印刷页131（PDF页140；分类账项目`maclane:V.8:thm-watt`，第454期），从印刷页阅读：“任何从R-Mod到Ab的逆变加法函子T，如果将小余极限映射为极限，则存在某个R-模C，使得T可由一个群同构表示，即T ≅ hom_R(−, C)。”（仓库中的目录 doc/plan/books/maclane/inventory/V.json 用它自己的话总结道：“每个从 R-Mod 到 Ab 的逆变加法函子 T，如果将小余积映射为极限，则是可表示的：T 自然同构于 hom_R(-, C) 对于某个 R-模 C。”）
 书籍：Mac Lane，同上，第 §V.6 定理 3 和定义 3——带有逐元素解集条件的可表示性定理，Adjunction/Representability/Sets.v，这是实际在此处应用的定理。
 nLab：https://ncatlab.org/nlab/show/Eilenberg-Watts+theorem
 nLab：https://ncatlab.org/nlab/show/adjoint+functor+theorem
 nLab：https://ncatlab.org/nlab/show/representable+functor一个偏离，直白地说。问题要求瓦特定理“源自 SAFT”，其审稿人备注中写道“可表示性必须从 SAFT 加上可加性推导”。该文件没有使用特殊伴随函子定理。它应用了一般的伴随函子定理，以 Mac Lane §V.6 定理 3 的形式（[representability_theorem]，其证明在 Adjunction/GAFT.v 的逗号初始步骤中），对一个显式的元素级解集进行操作，并且对该解集的覆盖步骤是以解集形式阅读的 Eilenberg–Watts 构造。原因是可测量的，而非偏好的：在 (R-Mod)^op 上的 SAFT 需要 R-Mod 的余良幂性，而树只有在假设 [Untruncate]（Instance/Mod/WellPowered.v 的 [RMod_CoWellPowered_untruncate]；该标题引用了在没有它时的拒绝）下才具有这种性质，并且它的余生成元 [RModop_Cogenerator] 仅在 [RingObject@{c c c}] 时存在。这里的路径不需要其中任何一个，因此它给出了书中的逆变陈述，而没有超出书本自身的两个假设。“加法性”按原文保留：Ab 级结论是 Functor/Representable/Additive.v 的 [watt_ab_iso]。#454 的 SAFT 推导条件形式并没有被此文件替代。标题，以及 SAFT 路线。对于本书的对变陈述，本文件是 #454 的标题。Instance/Mod/Watts.v 保留了 Mac Lane 自己的路线，即 Reviewer 行所命名的路线，作为 [watts_theorem] : SAFT 在 (RMod R)^op 下，在假设 [Untruncate] 并且在 [RingObject@{c c c}] 处具有环。这一陈述是 [watts_theorem_unconditional] 的特例，而 Watts.v 导入此文件，并在其第 6 节中从该定理导出它（[watts_theorem_via_unconditional]，并携带 [Untruncate] 而不消耗）；SAFT 路线被保留是为了忠实于 Reviewer 的路线，而不是为了其强度。在 Watts.v 的常量中，该定理包含了三个。第一个是 [watts_theorem]，如前述树中所示。第二个是 [watts_theorem_coext]：其陈述逐字 elaborates 自 [watts_theorem_unconditional] 在 [HomAbForget R A]，闭合且无宇宙方程。第三个是 [watts_theorem_sets]，但仅在其第二个 [Representable] 宇宙是 RMod 的对象宇宙的实例中，因为 [RModop_continuous_representable] 返回一个 [Representable@{u o s o c}]；同样的展开会读回 [o = rt]。（都在导入 Watts.v 的临时文件中测量，每个语句都从 Watts.v 复制而来，并且 [U] 未使用。）ZWZ25WZZ 和 [watts_theorem_coext_obj_2a] 有无条件对应物，即 Watts.v 的 [watts_unconditional_coext] 和 [watts_unconditional_coext_2a]，它们识别该模块 THIS 定理返回的内容。未被包含：[watts_theorem_adjoint]，即书中 T 的左伴随，仅在此由 SAFT 构建，以及 [watts_theorem_Fz]，即与之比较；读回 [watts_theorem_obj] 和 [watts_theorem_to_at]，涉及 SAFT 对象；以及共变练习 3 系列（[watts_ex3]、[watts_ex3_sets]、[watts_ex3_QZ]、[watts_ex3_QZ_cogenerator]、[watts_ex3_forget]、[watts_ex3_forget_obj]）。Watts.v 的其他常数
 ([RMod_Forget_Ab_additive], [RMod_Forget_equiv], [watt_at_forget],
 [HomAbForget], [HomAbForget_additive], [HomAbForget_continuous],
 [coext_representable], [Ab_Forget_Id_equiv], [ab_hom_Z_iso]) 没有需要移除的假设。消耗的内容。Adjunction/Representability/Sets.v 的 [representability_theorem] 和 [ElementSolutionSet]；
 Instance/Mod/Colimit.v 的 [RMod_Cocomplete_via_GAFT]，通过 Construction/Product/Limit.v 的 [Complete_op_of_Cocomplete] 反向读取；
 Instance/Mod/Free.v 的 [FreeModObject]、[fv_gen] 和 [fv_extend]；
 Instance/Mod/WellPowered.v 的 [PSubmodule]、[psm_sub] 和 [pker]；
 Instance/Mod/Quotient.v 的 [QuotientMod] 和 [mquot_med]；
 Instance/Discrete.v 的 [DiscreteCat_Functor]；
 Functor/Representable/Additive.v 的 [CoHomAb]、[HomAb_additive]、[HomAb_representable]、[CoHomAb_continuous]、[LocallyPropositional_op]、[watt_ab_iso] 和 [wab_obj]；Adjunction/Additive.v 的 [AbEnriched_op]；
 Instance/Ab/Limit.v 的 [Ab_Forget_creates_continuous]；
 Structure/Limit/Preservation.v 的 [continuous_compose] 和 [FCone]；
 Construction/Comma/Creation.v 的 [Continuous_PreservesImageLimit]；
 Functor/Hom/Continuous.v 的 [hom_continuous_at]。

 构建的内容。- [MultiSpan X]，一个薄形：节点 [ms_mod]、[ms_free] 和 [ms_gen m] 对于 m：X，每个 [ms_gen m] 指向其他两个节点；[ms_diagram] 在任何范畴中绘制它。- [sets_limit_point]：在集合点的极限锥上的兼容元素族是顶点的一个元素的像（从单元素锥的点出发的中介）。- [ew_Gen]，带一个生成元的自由模 [ew_g0]，以及 [ew_ev m]，将 [ew_g0] 映射到 m（[ew_ev_g0] 在 [eq_refl]）。- **[RModop_esols K contK : ElementSolutionSet K]** 对于每个连续的 K:(RMod R)^op ⟶ Sets，以及 **[RModop_continuous_representable K contK : Representable K]**。- **[watts_theorem_unconditional T AF contT]**：对于 T:(RMod R)^op ⟶ Ab 加法的且连续，一个模 A 在函子范畴中有 [CoHomAb A ≅ T]，即 T ≅ Hom_R(−, A) 作为 Ab 值函子。- 下面是非空性的证据。Ab 值的同态函子 [HomAb_continuous] 和 [CoHomAb_continuous] 的连续性在这里没有构建，而是从 Functor/Representable/Additive.v 中使用。论证。固定一个连续函子 K : (R-Mod)^op ⟶ 集合。令 Cop 为若干 [ew_Gen] 的直和，每个 K(ew_Gen) 的元素 i 对应一个 [ew_Gen]，带有映射 inj_i ( [ew_Cop] ,  [ew_inj])；它是一个模块，一旦 K 固定，它也就固定。K 将其映射到一个乘积上，因此自明族 i ↦ i 是 K(Cop) 中某个 y0 的像 ([ew_y0_leg])。现在取任意模块 M 和 K(M) 中的任意 x。定义 a_m := K(ev_m)(x) ∈ K(ew_Gen)，并令 P 为多重图 M ← ew_Gen → Cop 的余极限，对每个 m ，由 ev_m 和 inj_{a_m} 绘制一次。它的腿将 inj_{a_m}(g0) 与 m 对应起来 ([ew_key])。K 将 P 映射到一个极限，并且 (x, y0, (a_m)_m) 是其上的一个相容族（由 a_m 的定义和 y0 的定义），因此它是 K(P) 中某个 e 的像 ([ew_e_leg])。解集的成员是 Q := Cop / N，其中 N 是腿 Cop → P ([ew_N], 一个固定 Cop 的 [PSubmodule], 和 [ew_Q]) 的 [Prop] 核。映射 t : M → Q 定义为 m ↦ [inj_{a_m}(g0)] ([ew_t_at] 在 [eq_refl])。任何地方都没有进行任何选择：每个副本的生成元都是一个明确的元素，其中 SAFT 路径必须反转一个 epi。商映射到 P 通过 [mquot_med] ([ew_k], 其中 k ∘ t ≈ M 上的腿, [ew_k_t])，因此 K(t)(K(k)(e)) ≈ x ([ew_t_covers])。Cop 的指数 a [PSubmodule] 与商中 K 的一个元素 ([ew_WIdx]) 配对，位于载体宇宙中，这里 [representability_theorem] 固定了它。该路径是 GAFT 在一个 [Prop] 索引的一族自由模的商上进行的，并且在明显的选择之外进行了两次选择。一个生成元上的自由模替代了环，从而避免了 [Ring_RMod] 中环的宇宙坍塌。而一个多跨 colimit 替代了典型自由表示 F(U M) → M 的推挤出，因此 K 从不在 F(U M) 上被计算，也不需要联合单射性。加法性在 [RModop_esols] 中未被使用；它仅通过 [watt_ab_iso] 才引入。优势，严格的开始。在 [eq_refl]：[ew_ev_g0]（在生成器处评估），[ew_t_at]（覆盖映射精确）以及 [watts_theorem_unconditional_obj]（表示模块就是 [representability_theorem] 为 [Ab_Forget ◯ T] 产生的对象）；同构的两个分量是由 Functor/Representable/Additive.v 的 [watt_ab_iso_to_at] 和 [watt_ab_iso_from_at] 所表示的。直到 ≈：覆盖（[ew_t_covers]）和自然同构，在函子范畴中按分量。直到 ≅：证明者对找到的模块与预期模块的识别。翻转抽样，每个 [Defined] 一次翻转为 [Qed]，在整份文件的副本中：12 [Defined]（按注释外的标记计数），其中六个是承重的。[ms_fmap] 停止 [ms_diagram] 的首次义务，[ew_efam] 停止 [ew_e_ex] 的连贯性案例，[ew_k] 停止 [ew_k_t]，[ew_ev] 停止 [ew_ev_g0]，[ew_t] 停止 [ew_t_at]，[watts_theorem_unconditional] 停止 [watts_theorem_unconditional_obj]。六个重新编译为 [Qed]：[ms_id]、[ms_comp]、[sets_limit_point]、[ew_y0_ex]、[ew_e_ex] 和 [RModop_esols]。它们被保留 [Defined]，因为它们产生数据。

 UNIVERSES，由 [About] 在 [Set Printing Universes] 下测量，省略 stdlib 边界。watts_theorem_unconditional@{a c p o x b s …} ：
 对任意 {R : RingObject@{a c p}} （T : (RMod@{o x a p c} R)^op ⟶ Ab@{b c}），
 AdditiveFunctor@{o c b} T → ContinuousFunctor@{u u o c b c c b o s} T
 → { A & CoHomAb@{o c b} (RMod_AbEnriched@{x o a p c} R) A ≅ T }
 ( * Set < c, Set < o, Set < b, c < o, c < x, c < b, c < s, c <= a,
 p <= a, a <= o, … — 无方程 * )

 RModop_continuous_representable@{a c p o x s …} ：
 对任意 {R : RingObject@{a c p}} （K : (RMod@{o x a p c} R)^op ⟶ Sets@{c s}），
 ContinuousFunctor@{u u o c s c c s o s} K → Representable K
 ( * Set < c, Set < o, c < o, c < x, c < s, … — 无方程 * )这个环保持其三个宇宙分开。SAFT 路径的 [RModop_Cogenerator] 位于 [RingObject@{c c c}]，这里没有任何东西识别它们：[watts_unconditional_at_Z] 在 [Int_Ring@{c p a}] 实例化定理，并有三个不同的。[Set < c] 是真实的：从 [RModop_continuous_representable] 的绑定器中的整个文件副本中删除后，它被重新推导。从该部分的 [Constraint] 中删除后，它根据常量重新添加，首次在 [ew_CC]（上完备性，Instance/Mod/Colimit.v 的 [Set < c]），而不是在 [ew_Idx] 或 [ew_CopD]。[PSubmodule] 的类型，[Type@{max(Set+1,m3)}] 由其 [About]，需要它再次用于 [ew_WIdx : Type@{c}]。因此带有 [Set] 载体的 ℤ 被排除，[Set] 以上的 ℤ 也不包括。Test/ProbeWatts454.v 固定了这一点：它的 N24 拒绝在 [RMod@{o x Set Set Set} Int_Ring@{Set Set Set}] 的模块处 [watts_unconditional_at_Z]，且它的 N25 拒绝定理本身在 [RingObject@{Set Set Set}] 处，旁边是控件 [p454_unc_Z_ccc] 和 [p454_unc_Z_apart]（ℤ 在 [Set] 之上，其宇宙已塌缩并分离），ZWZ173WZZ（带有 [Set] 承载的 ℤ-模的范畴被形成，因此拒绝是定理的）和 [p454_unc_apart]（ZWZ176WZZ 之上的环，其三个宇宙严格分离）；它的 [p454_unc_x_below_s] 和 [p454_unc_s_below_x] 接受定理，在两种顺序下 x 和 s 分别分开。模块中的唯一宇宙方程（ZWZ179WZZ 在其全部 67 个名称上）是 c = u2 和 c = u4，这在连续性假设自身的实例上：它的形状对象插槽和其 [IsLimitCone] 的一个宇宙。它们由 [RModop_esols] 以及使用该假设的九个段常数承载，它们位于承载器上，因为该假设在 [MultiSpan@{c}] 和 [DiscreteCat@{c c c}] 上被使用，形状宇宙 [representability_theorem] 固定。两个标题和见证者不承载任何。三个辅助宇宙在覆盖段中按名称固定：w 对应 [DiscreteCat_Functor] 和 [ms_diagram]，w0, w1 对应 [RMod_Cocomplete_via_GAFT]。没有它们，以整个文件副本计量，[ew_P] 承载了它自己的宇宙。它的第一个在 [ew_e] 内的连续性假设的最后槽位及 [ew_k] 内的 x 上被实例化，它们在 [ew_eQ] 的会合点将 RMod 的第二个宇宙 x 与该槽位识别，[representability_theorem] 将该槽位识别为目标的 s。没有单一固定点可以移除等式；三者一起可以。该语句的 [ContinuousFunctor@{_ _ _ _ _ _ _ _ _ s} T] 名称用于最后一个槽，原因相同：保持灵活，它被设置为 x，而 [About] 读取回 x = s，直到它被命名。非空性。Functor/Representable/Additive.v 的 [CoHomAb_continuous] 证明了对每一个局部命题 Ab-增强范畴，逆变 Ab 值的 Hom 函子是连续的。因此 T := [CoHomAb A] 满足每一个环和每一个模 A 的两个前提，并且 [watts_unconditional_CoHomAb_obj] 显示该定理返回的模与 A 同构（[repr_unique_iso] 对应 [HomAb_representable]）。[RModop_hom_representable_obj] 在集合值层面上是相同的，对于普通 Hom 函子。在一个具体的环上，[watts_unconditional_at_Z] 将所有这些实例化到 ℤ。这三者为定理提供了一个 Hom 函子，其表示已知于事先。在 Instance/Mod/Watts.v 中有一个并非证人的 witness，它导入了这个文件：其第 6 节在 [HomAbForget R A] 上应用该定理，M ↦ Hom_Ab(U M, A) 对于一个阿贝尔群 A，其连续性来自共延拓陪伴而非 RMod R 的 Hom 函子。[watts_unconditional_coext] 将返回的模与 [CoextObj R A]（ [repr_unique_iso] 对 [coext_representable] ）以及 [watts_unconditional_coext_2a] 与练习 2(a) 的 hom_ℤ(R, A) 进行识别。两者都不需要 [Untruncate]；两者位于 [RingObject@{c c c}]，[CoextObj] 对其施加约束（Instance/Mod/Coextension.v）。条件，简单明了。T 是可加的；这仅用于 Ab 升级。T 在锥意义上是连续的（[ContinuousFunctor]），适用于其对象位于承载宇宙的形状。形状规则是 [Complete] 和 [representability_theorem] 所施加的，所以每个这样的形状上模块的余极限都会映射到群的极限；这就是书中所谓的“将小余极限映射为极限”。最后，[Set < c]。没有 [Untruncate]，没有余生成器，没有余完备性，没有选择也没有公理：此模块的每个常量都“在全局上下文下闭合”。

 大小。剔除注释后共有 374 行非空代码，包括 33 个 [Require]。未交付。练习3（协变形式）不是无条件交付的：Instance/Mod/Watts.v 仅在 [Untruncate] 和 R-Mod 的一个余生成子上交付它，通过特殊伴随函子定理，由余生成子提供其解集。没有尝试其他途径，而且树中的任何内容都未证明任何假设是必要的。被证明为经典的，是书中的 ℚ/ℤ 前提（Instance/Mod/Cogenerator.v 的元定理），以及 [RMod R] 在没有 [Untruncate] 的情况下在引脚处良好有幂也既未被建立也未被反驳（Instance/Mod/WellPowered.v）。表示模未被识别为 T(R)，或 T(ew_Gen) 携带 Eilenberg–Watts 作用。它是表示性定理生成的对象，且只有 [repr_unique_iso] 将其与任何东西进行比较。该模在 T 上没有自然性，也没有从 T ↦ A 的函子性。可加性前提 [AF] 在原理上是多余的，并未被消除：一个在加法范畴之间且保持有限积的函子是可加的，而连续函子 T : (R-Mod)^op → Ab 会将零模和二元直和（它们是模的余极限）映射到终端群和积。该陈述保留它是因为书中如此说明；该论证在此未形式化。没有注册 [Instance]。COQ 8.19 和 8.20。一个包含 250 个文件的依赖闭包，其中包含 #454 添加的七个开发文件，这个文件在其中，由 [coq_makefile] 使用 nix-store Coq 8.19.2 和 8.20.1 以及 Equations 1.3 构建：每个文件的 make rc=0。在那里 [Print Assumptions] 报告 Functor/Representable/Additive.v 的全部 132 个常量，这个文件和 Watts.v 已关闭，并且相同的十个常量具有与 9.1 相同的两个方程。在最后一轮仅评论的编辑之前，复制品已被获取；代码除去注释和空白外逐文件比较是相同的。然后将相同的两棵树带到后来的源代码中，替换掉与它们不同的三个文件（这一个、Instance/Mod/Watts.v 和 Instance/Mod/Cogenerator.v，每个仅在其头部），并添加了 Test/ProbeWatts454.v，它将此文件的 [Set] 边界作为其 N24 和 N25：[coq_makefile] 对每个文件编译了这四个文件，make 在两者上都返回 0，并且探针的剥离反驳在那儿被拒绝，因为其头部记录了这些情况。这些闭包并不是整个库；Nix flake 对已提交版本的构建才是权威入口，而 docs/INDEX.md 中关于此文件的项目符号记录了它们的结果。
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Hom.Continuous.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Structure.AbCategory.
Require Import Category.Construction.Product.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Adjunction.Additive.
Require Import Category.Adjunction.Representability.Sets.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Free.
Require Import Category.Instance.Mod.Quotient.
Require Import Category.Instance.Mod.Bimodule.
Require Import Category.Instance.Mod.WellPowered.
Require Import Category.Instance.Mod.Colimit.
Require Import Category.Functor.Representable.Additive.

Generalizable All Variables.

(*
   * ** 1. The multi-span shape

   Objects: one node [ms_mod], one node [ms_free], and one node [ms_gen m]
   for every [m : X]; besides the identities, exactly one arrow from each
   [ms_gen m] to each of the other two nodes.  Every hom-set has at most
   one element up to the identification of equality proofs, so the
   hom-setoids are the total relation and every category law is [I]. 

   --------
   * ** 1. 多跨形状

   对象：每个 [m : X] 对应一个节点 [ms_mod]、一个节点 [ms_free] 和一个节点 [ms_gen m]；除了恒等映射，每个 [ms_gen m] 到其他两个节点各有且只有一条箭头。每个同态集最多有一个元素（在等式证明的识别下），因此同态集等价类是全关系，并且每个范畴法则都是 [I]。
*)

Inductive MSObj@{u} (X : Type@{u}) : Type@{u} :=
  | ms_mod
  | ms_free
  | ms_gen (m : X).

Arguments ms_mod {X}.
Arguments ms_free {X}.
Arguments ms_gen {X} m.

Definition MSHom@{u} {X : Type@{u}} (i j : MSObj@{u} X) : Type@{u} :=
  match i, j with
  | ms_mod, ms_mod => poly_unit@{u}
  | ms_free, ms_free => poly_unit@{u}
  | ms_gen m, ms_gen m' => m = m'
  | ms_gen _, ms_mod => poly_unit@{u}
  | ms_gen _, ms_free => poly_unit@{u}
  | _, _ => False
  end.

Definition ms_id@{u} {X : Type@{u}} (i : MSObj@{u} X) : MSHom i i.
Proof. destruct i; simpl; first [ exact ttt | reflexivity ]. Defined.

Definition ms_comp@{u} {X : Type@{u}} {i j k : MSObj@{u} X} :
  MSHom j k → MSHom i j → MSHom i k.
Proof.
  destruct i, j, k; simpl; intros g f;
    first [ exact ttt | contradiction | exact (eq_trans f g) ].
Defined.

#[local] Obligation Tactic := idtac.

Program Definition MultiSpan@{u} (X : Type@{u}) : Category@{u u u} := {|
  obj := MSObj@{u} X;
  hom := @MSHom@{u} X;
  homset := fun i j => {| equiv := fun _ _ => True |};
  id := @ms_id@{u} X;
  compose := fun i j k => @ms_comp@{u} X i j k
|}.
Solve All Obligations with
  (intros;
   first [ constructor; repeat intro; exact I | repeat intro; exact I ]).

(* A diagram of that shape: two arrows out of [G] for each [m : X]. / 该形状的图示：每个 [m : X] 对应两个来自 [G] 的箭头。 *)
Section MSDiagram.

Universes o h.

Context {X : Type@{h}} {C : Category@{o h h}} (A B G : C)
        (u : X → G ~{C}~> A) (v : X → G ~{C}~> B).

Definition ms_fobj (i : MSObj@{h} X) : C :=
  match i with ms_mod => A | ms_free => B | ms_gen _ => G end.

Definition ms_fmap {i j : MSObj@{h} X} :
  MSHom i j → ms_fobj i ~{C}~> ms_fobj j.
Proof using u v.
  destruct i as [| | m], j as [| | m']; simpl; intro f;
    first [ exact id | contradiction | exact (u m) | exact (v m) ].
Defined.

Program Definition ms_diagram : MultiSpan@{h} X ⟶ C := {|
  fobj := ms_fobj;
  fmap := fun i j f => ms_fmap f
|}.
Next Obligation.
  intros i j f g _.
  destruct i as [| | m], j as [| | m']; simpl in *;
    first [ contradiction | reflexivity ].
Qed.
Next Obligation.
  intro i; destruct i; simpl; reflexivity.
Qed.
Next Obligation.
  intros i j k f g.
  destruct i as [| | m], j as [| | m'], k as [| | m'']; simpl in *;
    try contradiction; solve [ subst; cat ].
Qed.

End MSDiagram.

(*
   * ** 2. A point of a limit of setoids

   A compatible family of elements over a limiting cone in [Sets] is the
   image of one element of the apex: the mediator out of the singleton
   cone, evaluated at its point. 

   --------
   * ** 2. 集族的极限的一个点

   在  [Sets]  中一个极限锥上的元素的相容族是顶点的一个元素的像：从单点锥出的中介，在其点处被评估。
*)

Definition sets_limit_point@{j c s +}
  {J : Category@{j c c}} {F : J ⟶ Sets@{c s}} (N : Cone F) (HN : IsLimitCone N)
  (e : ∀ i : J, carrier (F i))
  (He : ∀ (i i' : J) (f : i ~{J}~> i'), fmap[F] f (e i) ≈ e i') :
  { v : carrier (vertex_obj[N]) & ∀ i : J, cone_leg N i v ≈ e i }.
Proof.
  unshelve epose (P := @Build_Cone J Sets F unit_setoid_object
           (@Build_ACone J Sets unit_setoid_object F
              (fun i => {| morphism := fun _ => e i |}) _)).
  - intros w w' _; reflexivity.
  - intros i i' f w; simpl; exact (He i i' f).
  - destruct (HN P) as [w Hw _].
    exists (w ttt).
    intro i; exact (Hw i ttt).
Defined.

(* * ** 3. The free module on one generator, and evaluation at an element / * ** 3. 单生成元的自由模，以及在一个元素上的取值 *)

Definition ew_Gen@{a c p o x +|
    Set < o, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} : obj[RMod@{o x a p c} R] :=
  @FreeModObject R unit_setoid_object@{c c}.

Definition ew_g0@{a c p o x +|
    Set < o, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} : carrier (cmon_setoid (@ew_Gen@{a c p o x} R)) :=
  @fv_gen R unit_setoid_object@{c c} ttt.

(* [m ↦ the homomorphism sending the generator to m]: the free module's own extension, so it needs no choice and computes. / [m ↦ the homomorphism sending the generator to m]：自由模的自身扩展，因此它不需要选择并且可以计算。 *)
Definition ew_ev@{a c p o x +|
    Set < o, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} {M : obj[RMod@{o x a p c} R]}
  (m : carrier (cmon_setoid M)) :
  @ew_Gen@{a c p o x} R ~{RMod@{o x a p c} R}~> M.
Proof.
  refine (@fv_extend R unit_setoid_object@{c c} M
            {| morphism := fun _ => m |}).
  intros ? ? ?; reflexivity.
Defined.

Example ew_ev_g0@{a c p o x +|
    Set < o, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} {M : obj[RMod@{o x a p c} R]}
  (m : carrier (cmon_setoid M)) :
  cmon_map (rm_hom (ew_ev@{a c p o x} m)) ew_g0 = m := eq_refl.

(* * ** 4. The element-wise solution set at (R-Mod)^op / * ** 4. 在 (R-Mod)^op 中的按元素的解集 *)

Section Covering.

(*
 The ring (a c p), [RMod] (o x), the target of [K] (s), and three
 auxiliary universes pinned by name (w for [DiscreteCat_Functor] and
 [ms_diagram], w0 w1 for [RMod_Cocomplete_via_GAFT]): left free, they
 gave [ew_P] universes of its own, instantiated differently inside
 [ew_e] and inside [ew_k], and [ew_eQ] identified the two (see the
 header, UNIVERSES). 

 --------
 环 (a c p)、[RMod] (o x)、[K] (s) 的目标，以及三个按名称固定的辅助宇宙（w 对于 [DiscreteCat_Functor] 和 [ms_diagram]，w0 w1 对于 [RMod_Cocomplete_via_GAFT]）：如果不加限制，它们给了 [ew_P] 自己的宇宙，在 [ew_e] 内和 [ew_k] 内以不同方式实例化，而 [ew_eQ] 将两者识别为同一宇宙（参见标题，UNIVERSES）。
*)
Universes a c p o x s w w0 w1.
Constraint Set < c, c < o, c < x, p <= a, c <= a, a <= o, c < s, c < w,
  o <= w1, x <= w1.

Context {R : RingObject@{a c p}}.
Context (K : (RMod@{o x a p c} R)^op ⟶ Sets@{c s}).
Context (contK : ContinuousFunctor K).

#[local] Notation Gen := (@ew_Gen@{a c p o x} R).
#[local] Notation g0 := (@ew_g0@{a c p o x} R).

(*
 The ONE fixed object: the coproduct of copies of [Gen], one per element
 of [K Gen], taken from [RMod_Cocomplete_via_GAFT]. 

 --------
 唯一固定对象：从 ZZ W2WZZ 中取出的 ZZ W1WZZ 每个元素对应的 ZZ W0WZZ 副本的余积。
*)
Definition ew_Idx : Type@{c} := carrier (K Gen).

Definition ew_CopD : DiscreteCat@{c c c} ew_Idx ⟶ RMod@{o x a p c} R :=
  DiscreteCat_Functor@{c c c o c c w} (fun _ => Gen).

Definition ew_CC : @Cocomplete@{c c c o} (RMod@{o x a p c} R) :=
  RMod_Cocomplete_via_GAFT@{a c p o x c w0 w1} R.

Definition ew_CopL : Colimit ew_CopD := ew_CC _ ew_CopD.

Definition ew_Cop : obj[RMod@{o x a p c} R] :=
  vertex_obj[@limit_cone _ _ _ ew_CopL].

Definition ew_inj (i : ew_Idx) : Gen ~{RMod@{o x a p c} R}~> ew_Cop :=
  cone_leg (@limit_cone _ _ _ ew_CopL) i.

(* [K] carries that coproduct to a product, so the tautological family [i ↦ i] is the image of one element [ew_y0] of [K ew_Cop]. / [K] 将该余积映射为一个积，因此自明的族 [i ↦ i] 是 [K ew_Cop] 中一个元素 [ew_y0] 的像。 *)
Definition ew_y0_ex :
  { w : carrier (K ew_Cop)
  & ∀ i : ew_Idx, @fmap _ _ K ew_Cop Gen (ew_inj i) w ≈ i }.
Proof using contK.
  destruct (sets_limit_point (FCone K (@limit_cone _ _ _ ew_CopL))
              (contK _ _ (@limit_cone _ _ _ ew_CopL) (limit_limitcone ew_CopL))
              (fun i : ew_Idx => i)) as [w Hw].
  - intros i i' f; destruct f; simpl.
    exact (@fmap_id _ _ K Gen _).
  - exists w; exact Hw.
Defined.

Definition ew_y0 : carrier (K ew_Cop) := projT1 ew_y0_ex.

Definition ew_y0_leg (i : ew_Idx) :
  @fmap _ _ K ew_Cop Gen (ew_inj i) ew_y0 ≈ i :=
  projT2 ew_y0_ex i.

Section AtElement.

Context (M : obj[RMod@{o x a p c} R]) (x0 : carrier (K M)).

(* For each m, the element [K(ev m)(x0)] of [K Gen] names a copy of [Gen] inside [ew_Cop]. / 对于每个 m，[K Gen] 的元素 [K(ev m)(x0)] 命名了 [ew_Cop] 内的 [Gen] 的一个副本。 *)
Definition ew_am (m : carrier (cmon_setoid M)) : ew_Idx :=
  @fmap _ _ K M Gen (ew_ev m) x0.

(* The diagram M ← Gen → ew_Cop, one span per element m of M, and its colimit P. / 图 M ← Gen → ew_Cop，每个 M 元素 m 对应一个跨度，以及它的余极限 P。 *)
Definition ew_PD :
  MultiSpan@{c} (carrier (cmon_setoid M)) ⟶ RMod@{o x a p c} R :=
  ms_diagram@{o c w} M ew_Cop Gen
    (fun m => ew_ev m) (fun m => ew_inj (ew_am m)).

Definition ew_PL : Colimit ew_PD := ew_CC _ ew_PD.

Definition ew_P : obj[RMod@{o x a p c} R] :=
  vertex_obj[@limit_cone _ _ _ ew_PL].

Definition ew_pM : M ~{RMod@{o x a p c} R}~> ew_P :=
  cone_leg (@limit_cone _ _ _ ew_PL) ms_mod.

Definition ew_pF : ew_Cop ~{RMod@{o x a p c} R}~> ew_P :=
  cone_leg (@limit_cone _ _ _ ew_PL) ms_free.

Definition ew_pG (m : carrier (cmon_setoid M)) :
  Gen ~{RMod@{o x a p c} R}~> ew_P :=
  cone_leg (@limit_cone _ _ _ ew_PL) (ms_gen m).

Lemma ew_pM_ev (m : carrier (cmon_setoid M)) : ew_pM ∘ ew_ev m ≈ ew_pG m.
Proof.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ (@limit_cone _ _ _ ew_PL))
           ms_mod (ms_gen m) ttt).
Qed.

Lemma ew_pF_inj (m : carrier (cmon_setoid M)) :
  ew_pF ∘ ew_inj (ew_am m) ≈ ew_pG m.
Proof.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ (@limit_cone _ _ _ ew_PL))
           ms_free (ms_gen m) ttt).
Qed.

(* The one equation the covering rests on: P identifies m with the generator of the copy of [Gen] that [ew_am m] names. / 覆盖所依赖的一个方程：P 将 m 与 [ew_am m] 命名的 [Gen] 副本的生成元对应起来。 *)
Lemma ew_key (m : carrier (cmon_setoid M)) :
  cmon_map (rm_hom ew_pF) (cmon_map (rm_hom (ew_inj (ew_am m))) g0)
    ≈ cmon_map (rm_hom ew_pM) m.
Proof.
  pose proof (ew_pF_inj m g0) as H1; pose proof (ew_pM_ev m g0) as H2.
  simpl in H1, H2.
  exact (Equivalence_Transitive _ _ _ H1 (Equivalence_Symmetric _ _ H2)).
Qed.

(* [K] carries the colimit P to a limit, so the compatible family (x0 at M, ew_y0 at ew_Cop, ew_am m at each copy of Gen) is the image of one element [ew_e] of [K P]. / [K] 将余极限 P 变为极限，因此兼容族 (x0 在 M 上, ew_y0 在 ew_Cop 上, ew_am m 在 Gen 的每个副本上) 是 [K P] 中一个元素 [ew_e] 的像。 *)
Definition ew_efam (i : MultiSpan@{c} (carrier (cmon_setoid M))) :
  carrier ((K ◯ ew_PD^op) i).
Proof using contK.
  destruct i as [| | m]; [ exact x0 | exact ew_y0 | exact (ew_am m) ].
Defined.

Definition ew_e_ex :
  { w : carrier (K ew_P)
  & ∀ i, cone_leg (FCone K (@limit_cone _ _ _ ew_PL)) i w ≈ ew_efam i }.
Proof using contK.
  refine (sets_limit_point (FCone K (@limit_cone _ _ _ ew_PL))
            (contK _ _ (@limit_cone _ _ _ ew_PL) (limit_limitcone ew_PL))
            ew_efam _).
  intros i i' f.
  destruct i as [| | m], i' as [| | m']; simpl in f |- *;
    try contradiction;
    first [ exact (@fmap_id _ _ K _ _)
          | reflexivity
          | exact (ew_y0_leg _)
          | (subst; exact (@fmap_id _ _ K _ _)) ].
Defined.

Definition ew_e : carrier (K ew_P) := projT1 ew_e_ex.

Lemma ew_e_leg : @fmap _ _ K ew_P M ew_pM ew_e ≈ x0.
Proof using contK. exact (projT2 ew_e_ex ms_mod). Qed.

(* The member of the solution set: [ew_Cop] modulo the [Prop] kernel of [ew_pF], a [PSubmodule] of the ONE fixed module [ew_Cop]. / 解集的成员：[ew_Cop] 模 [Prop] 的核 [ew_pF]，一个 [PSubmodule] 的 ONE 固定模 [ew_Cop]。 *)
Definition ew_N : PSubmodule ew_Cop := pker ew_pF.

Definition ew_Q : obj[RMod@{o x a p c} R] := QuotientMod (psm_sub ew_N).

Definition ew_k : ew_Q ~{RMod@{o x a p c} R}~> ew_P.
Proof.
  refine (mquot_med (psm_sub ew_N) (existT _ ew_pF _)).
  intros z Hz; exact (pequiv_to _ _ Hz).
Defined.

Lemma ew_qrel_of (z z' : carrier (cmon_setoid ew_Cop)) :
  cmon_map (rm_hom ew_pF) z ≈ cmon_map (rm_hom ew_pF) z' →
  mquot_rel (psm_sub ew_N) z z'.
Proof.
  intro H; constructor; simpl.
  apply pequiv_from.
  rewrite (ab_map_sub (rm_hom ew_pF) z z').
  apply (snd (ab_sub_eq_zero_iff _ _ _)); exact H.
Qed.

(* The covering map, with NO choice: m ↦ the generator of the copy that [ew_am m] names, read in the quotient. / 覆盖映射，没有选择：m ↦ 在商中读取的 [ew_am m] 所命名的副本的生成元。 *)
Definition ew_tfun (m : carrier (cmon_setoid M)) :
  carrier (cmon_setoid ew_Cop) :=
  cmon_map (rm_hom (ew_inj (ew_am m))) g0.

Definition ew_t : M ~{RMod@{o x a p c} R}~> ew_Q.
Proof.
  unshelve econstructor; [unshelve econstructor; [unshelve econstructor|..]|].
  - exact ew_tfun.
  - intros m m' Hm; apply ew_qrel_of; unfold ew_tfun.
    rewrite (ew_key m), (ew_key m'); now rewrite Hm.
  - apply ew_qrel_of; unfold ew_tfun.
    rewrite (ew_key (cmon_zero M)).
    rewrite (cmon_map_zero (rm_hom ew_pM)).
    symmetry; exact (cmon_map_zero (rm_hom ew_pF)).
  - intros m m'; apply ew_qrel_of; unfold ew_tfun.
    rewrite (ew_key (cmon_plus M m m')).
    rewrite (cmon_map_plus (rm_hom ew_pF)).
    rewrite (ew_key m), (ew_key m').
    exact (cmon_map_plus (rm_hom ew_pM) m m').
  - intros r m; apply ew_qrel_of; unfold ew_tfun.
    rewrite (ew_key (rm_smul M r m)).
    rewrite (rm_map_smul ew_pF).
    rewrite (ew_key m).
    exact (rm_map_smul ew_pM r m).
Defined.

Example ew_t_at (m : carrier (cmon_setoid M)) :
  cmon_map (rm_hom ew_t) m = cmon_map (rm_hom (ew_inj (ew_am m))) g0 := eq_refl.

Lemma ew_k_t : ew_k ∘ ew_t ≈ ew_pM.
Proof. intro m; simpl; exact (ew_key m). Qed.

Definition ew_eQ : carrier (K ew_Q) := @fmap _ _ K ew_P ew_Q ew_k ew_e.

Lemma ew_t_covers : @fmap _ _ K ew_Q M ew_t ew_eQ ≈ x0.
Proof using contK.
  unfold ew_eQ.
  pose proof (@fmap_comp _ _ K ew_P ew_Q M ew_t ew_k ew_e) as Hc; simpl in Hc.
  pose proof (@fmap_respects _ _ K ew_P M (ew_k ∘ ew_t) ew_pM ew_k_t ew_e)
    as Hr;
    simpl in Hr.
  rewrite <- ew_e_leg.
  exact (Equivalence_Transitive _ _ _ (Equivalence_Symmetric _ _ Hc) Hr).
Qed.

End AtElement.

(* The index: a [Prop] submodule of the fixed [ew_Cop] with an element of [K] at the quotient. It sits at the carrier universe [c]. / 索引：固定子 [ew_Cop] 的一个子模 [Prop]，在商上有一个元素 [K]。它位于承载宇宙 [c] 中。 *)
Definition ew_WIdx : Type@{c} :=
  { N : PSubmodule ew_Cop & carrier (K (QuotientMod (psm_sub N))) }.

Definition RModop_esols : ElementSolutionSet K.
Proof using contK.
  refine (@Build_ElementSolutionSet ((RMod@{o x a p c} R)^op) K ew_WIdx
            (fun i => QuotientMod (psm_sub (projT1 i))) (fun i => projT2 i) _).
  intros M x.
  exists (existT (fun N : PSubmodule ew_Cop =>
                    carrier (K (QuotientMod (psm_sub N))))
            (ew_N M x) (ew_eQ M x)).
  exists (ew_t M x).
  exact (ew_t_covers M x).
Defined.

End Covering.

(* * ** 5. Every continuous K : (R-Mod)^op ⟶ Sets is representable / * ** 5. 每个连续的 K : (R-Mod)^op ⟶ 集合 是可表示的 *)

Definition RModop_continuous_representable@{a c p o x s +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, c < s +}
  {R : RingObject@{a c p}} (K : (RMod@{o x a p c} R)^op ⟶ Sets@{c s})
  (contK : ContinuousFunctor K) : Representable K :=
  representability_theorem K
    (Complete_op_of_Cocomplete (RMod_Cocomplete_via_GAFT R))
    (Continuous_PreservesImageLimit contK) (RModop_esols K contK).

(* * ** 6. Watt's theorem, contravariant form, with no hypothesis / * ** 6. 瓦特定理，反变形式，无假设 *)

Definition watts_theorem_unconditional@{a c p o x b s +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, c < s, Set < b, c < b +}
  {R : RingObject@{a c p}} (T : (RMod@{o x a p c} R)^op ⟶ Ab@{b c})
  (AF : @AdditiveFunctor _ _ (AbEnriched_op (RMod_AbEnriched R))
          Ab_AbEnriched T)
  (contT : ContinuousFunctor@{_ _ _ _ _ _ _ _ _ s} T) :
  { A : RMod@{o x a p c} R &
    @Isomorphism (@Fun ((RMod@{o x a p c} R)^op) Ab@{b c})
      (@CoHomAb _ (RMod_LocallyPropositional R) (RMod_AbEnriched R) A) T }.
Proof.
  pose (Rp := RModop_continuous_representable (Ab_Forget@{b s c} ◯ T)
                (continuous_compose contT Ab_Forget_creates_continuous)).
  exists (wab_obj Rp).
  exact (@watt_ab_iso _ (LocallyPropositional_op (RMod_LocallyPropositional R))
           (AbEnriched_op (RMod_AbEnriched R)) T AF Rp).
Defined.

(*
 The representing module IS the object the representability theorem
 produces for [Ab_Forget ◯ T]. 

 --------
 表示模块是表示性定理为 [Ab_Forget ◯ T] 产生的对象。
*)
Example watts_theorem_unconditional_obj@{a c p o x b s +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, c < s, Set < b, c < b +}
  {R : RingObject@{a c p}} (T : (RMod@{o x a p c} R)^op ⟶ Ab@{b c})
  (AF : @AdditiveFunctor _ _ (AbEnriched_op (RMod_AbEnriched R))
          Ab_AbEnriched T)
  (contT : ContinuousFunctor@{_ _ _ _ _ _ _ _ _ s} T) :
  projT1 (watts_theorem_unconditional T AF contT)
    = wab_obj (RModop_continuous_representable (Ab_Forget@{b s c} ◯ T)
                 (continuous_compose contT Ab_Forget_creates_continuous))
  := eq_refl.

(** ** 7. Non-vacuity / ** 7. 非空性 *)

(*
 Every module A gives an instance of the theorem, through
 Functor/Representable/Additive.v's [CoHomAb_continuous], and the
 module the theorem returns is isomorphic to A. 

 --------
 每个模块 A 都通过 Functor/Representable/Additive.v 的 [CoHomAb_continuous] 提供一个定理的实例，而定理返回的模块与 A 同构。
*)
Definition watts_unconditional_CoHomAb_obj@{a c p o x b +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, Set < b, c < b +}
  {R : RingObject@{a c p}} (A : RMod@{o x a p c} R) :
  projT1 (watts_theorem_unconditional
            (@CoHomAb _ (RMod_LocallyPropositional R) (RMod_AbEnriched R) A
             : _ ⟶ Ab@{b c})
            (@HomAb_additive _
               (LocallyPropositional_op (RMod_LocallyPropositional R))
               (AbEnriched_op (RMod_AbEnriched R)) A)
            (CoHomAb_continuous (RMod_AbEnriched R) A))
    ≅[(RMod@{o x a p c} R)^op] A :=
  repr_unique_iso
    (@HomAb_representable _
       (LocallyPropositional_op (RMod_LocallyPropositional R))
       (AbEnriched_op (RMod_AbEnriched R)) A)
    (RModop_continuous_representable _
       (continuous_compose (CoHomAb_continuous (RMod_AbEnriched R) A)
          Ab_Forget_creates_continuous)).

(* The set-valued form at the plain hom-functor. / 在平凡同态函子上的集合值形式。 *)
Definition RModop_hom_representable_obj@{a c p o x s +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, c < s +}
  {R : RingObject@{a c p}} (A : RMod@{o x a p c} R) :
  @repr_obj _ _ (RModop_continuous_representable
                   (@HomFrom_at ((RMod@{o x a p c} R)^op) A : _ ⟶ Sets@{c s})
                   (@hom_continuous_at ((RMod@{o x a p c} R)^op) A))
    ≅[(RMod@{o x a p c} R)^op] A :=
  repr_unique_iso (@Hom_Representable ((RMod@{o x a p c} R)^op) A)
    (RModop_continuous_representable _
       (@hom_continuous_at ((RMod@{o x a p c} R)^op) A)).

(* At a concrete ring: ℤ, with its three universes apart. / 在一个具体的环：ℤ，其有三个截然不同的宇宙。 *)
Definition watts_unconditional_at_Z@{a c p o x b +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, Set < b, c < b +}
  (A : RMod@{o x a p c} Int_Ring@{c p a}) :
  projT1 (watts_theorem_unconditional
            (@CoHomAb _ (RMod_LocallyPropositional _) (RMod_AbEnriched _) A
             : _ ⟶ Ab@{b c})
            (@HomAb_additive _
               (LocallyPropositional_op (RMod_LocallyPropositional _))
               (AbEnriched_op (RMod_AbEnriched _)) A)
            (CoHomAb_continuous (RMod_AbEnriched _) A))
    ≅[(RMod@{o x a p c} Int_Ring@{c p a})^op] A :=
  watts_unconditional_CoHomAb_obj A.
