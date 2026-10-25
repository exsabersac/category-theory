Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.

Generalizable All Variables.

(* * * Limits of abelian groups are computed on underlying sets / * * 阿贝尔群的极限是在底层集合上计算的 *)

(*
 nLab: https://ncatlab.org/nlab/show/created+limit
 nLab: https://ncatlab.org/nlab/show/limit#limits_in_categories_of_algebras
 nLab: https://ncatlab.org/nlab/show/Ab
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_abelian_groups
 Mac Lane: Categories for the Working Mathematician, 2nd ed. (GTM 5),
 §V.1 Theorems 2 and 3, book pp. 111-112 (PDF pp. 120-121)
 Awodey:   Category Theory, 1st ed. (CMU pre-print, September 2005),
 §5.6 Proposition 5.32, printed p. 119 (PDF p. 128)

 [Ab_Forget] (Instance/Ab.v) STRICTLY CREATES every limit.  Given a
 limiting cone over the underlying diagram of sets, there is exactly one
 abelian-group structure on its apex making every projection a
 homomorphism ([alim_structure_unique], Mac Lane's Theorem 2), the
 resulting cone lies over the given one ON THE NOSE ([alim_over_obj] and
 [alim_over_legs] are both [eq_refl], because [Ab_Forget]'s object map is
 the [cmon_setoid ∘ ab_cmon] projection), it is limiting
 ([alim_created]), and a cone of abelian groups whose image is limiting is
 itself limiting ([ab_reflects]).  Packaged as
 Structure/Limit/Creation.v's own classes --
 [Ab_Forget_StrictlyCreatesLimit], [Ab_Forget_CreatesLimit] and
 [Ab_Forget_creates_limits] -- from which the standard corollaries follow
 by application: [Ab_Complete] (Mac Lane's Theorem 3) and
 [Ab_Forget_creates_continuous : ContinuousFunctor Ab_Forget], the
 cone-level reading, with the apex-only [Ab_Forget_PreservesAllLimits]
 derived from it and [Ab_Forget_reflects_limits] alongside.

 ** WHY A SECOND [ContinuousFunctor Ab_Forget] -- THE MAIN REASON THIS
 FILE EXISTS

 Instance/Ab/FreeNotContinuous.v ALREADY declares
 [Ab_Forget_Continuous : ContinuousFunctor Ab_Forget], and its proof term
 is [right_adjoint_Continuous free_ab_adjunction] -- RAPL applied
 to Instance/Ab/Free.v's [free_ab_adjunction : FreeAb ⊣ Ab_Forget].
 That constant is not touched here, not reused here, and not restated:
 the one declared below is [Ab_Forget_creates_continuous]
 (a DIFFERENT name for a DIFFERENT term), and the difference is the
 point.

 [Ab_Forget_Continuous] PRESUPPOSES the free/forgetful adjunction.
 [Ab_Forget_creates_continuous] presupposes NOTHING beyond
 [Sets_Complete] and the creation result below; no adjunction, no free
 object, no [FreeAb].  That matters for exactly one consumer shape.
 Freyd's General Adjoint Functor Theorem (Adjunction/GAFT.v) takes
 [comp : @Complete C] and [cont : @PreservesImageLimit C D U] and RETURNS
 a left adjoint to [U].  Feeding it [Ab_Forget_Continuous] would feed it
 a term built out of the very adjunction it is being asked to produce, so
 the application would be circular and would establish nothing; feeding
 it [Ab_Forget_creates_continuous] does not, and that is what makes an
 [Ab] analogue of Instance/Grp/FreeAFT.v possible.

 ONE CORRECTION TO AN EARLIER REVISION OF THIS PARAGRAPH, since it would
 mislead the reader who tries the application.  [ContinuousFunctor] does
 NOT ascribe where GAFT asks for [PreservesImageLimit]: measured,
 [GAFT Ab_Forget Ab_Complete Ab_Forget_creates_continuous sols] is
 refused with "The term \"Ab_Forget_creates_continuous\" has type
 \"ContinuousFunctor Ab_Forget\" while it is expected to have type
 \"Limit.PreservesImageLimit\" (cannot unify \"Limit.Limit K\" and
 \"Cone.Cone K\")".  The bridge
 [Continuous_PreservesImageLimit] (Construction/Comma/Creation.v) is
 load-bearing and must stand in the term, exactly as it does at [Grp]
 (Instance/Grp/FreeAFT.v's [free_group_via_GAFT]), whose probe pins the
 same refusal as its N6.  So the [Ab] triple would be [Ab_Complete],
 [Continuous_PreservesImageLimit Ab_Forget_creates_continuous], and a
 solution set.  NO such [Ab] application is built here -- see NOT
 DELIVERED -- so what is claimed is availability, not use.

 Two further differences, stated so the two constants are not confused.
 [ContinuousFunctor] is not a class and nothing here is registered as an
 [Instance], so the two never compete in resolution; and continuity is
 only one of three things the creation result yields, the other two being
 [Ab_Complete] and the reflection clause [Ab_Forget_reflects_limits],
 which RAPL does not give at all.  No claim is made here that creation is
 formally stronger than continuity -- nothing in this file compares the
 two as propositions.

 ** THE HEADLINE SENTENCE IS MACHINE-CHECKED AT [eq_refl], NOT ARGUED

 At the limits [Sets_Complete] chooses -- the compatible families of
 Instance/Sets/Complete.v -- the created abelian group is the
 COORDINATEWISE one on the nose: [ab_complete_carrier],
 [ab_complete_plus], [ab_complete_zero], [ab_complete_neg] and
 [ab_complete_leg] are five [eq_refl] Examples, at an ARBITRARY shape and
 an ARBITRARY diagram of abelian groups.  Nothing in them is specific to a
 witness category, and no isomorphism is interposed; this file therefore
 needs no concrete witness to be non-vacuous, and builds none.

 ** WHAT IS LIFTED, AND WHY IT IS ONE OPERATION MORE THAN [CMon]

 Instance/Ab.v's [AbObject] EXTENDS Instance/CMon.v's
 [CMonObject] by [ab_neg] with [ab_neg_respects] and [ab_neg_left]; the
 coercion [ab_cmon :> CMonObject] supplies [carrier], [cmon_zero],
 [cmon_plus] and the four commutative-monoid laws.  So three operations
 are lifted -- [cmon_plus], [cmon_zero], [ab_neg] -- against six laws:
 associativity, COMMUTATIVITY, the left unit law, the left inverse law,
 and the two [Proper] clauses.  Commutativity is the one law with no
 counterpart in the group template Instance/Grp/Limit.v, and it costs
 exactly the same three lines as the others, because joint monicity of
 the legs does not care what the law says.

 THE MORPHISM SIDE COSTS EXACTLY WHAT THE GROUP CASE COSTS -- an earlier
 draft of this header said it was cheaper, and the measurement refutes
 that.  [AbHom A B] is DEFINED as [CMonHom A B] (Instance/Ab.v), so a
 homomorphism owes [cmon_map_zero] and [cmon_map_plus] and nothing else,
 preservation of negation being the theorem [ab_map_neg] rather
 than a field -- but [GrpHom] is the same shape, with [grp_map_inv]
 (Instance/Grp.v) playing [ab_map_neg]'s part.  Measured on the two
 [.vo] files, both carry TEN [Program] obligations with matching names:
 two each for the legs, the mediator and the reflected mediator, one each
 for the three leg families and the constant map.

 THE OBJECT SIDE COSTS TWO CONSTANTS MORE, AND EXACTLY TWO.  Counting
 [def]+[prf] heads in the [.glob] files, this file declares 75 against
 Instance/Grp/Limit.v's 73; the two extra are [alim_comm], which has no
 counterpart because [GrpObject] states no commutativity, and
 [alim_neg_respects], which has none because [GrpObject] does not make
 respectfulness of inversion a FIELD (Instance/Grp.v lists only
 [grp_mul_respects]; [grp_inv_Proper] is derived afterwards)
 whereas [AbObject] does (Instance/Ab.v).

 ** THE ENGINE IS ONE REUSABLE LEMMA WITH NOTHING ALGEBRAIC IN IT

 [absets_limit_ext] says the legs of a limiting cone in [Sets] are jointly
 monic ELEMENTWISE: two points of the apex agreeing at every leg are
 equal.  It is proved from the mediator's uniqueness alone, with the two
 constant maps out of the apex itself as probes -- so it needs no terminal
 object and pulls in no further module.  Every abelian-group law below is
 then three lines: apply it, rewrite the defining triangle, apply the law
 in [K j].

 ON THE DUPLICATION, DISCLOSED RATHER THAN GLOSSED, AND THE COUNT IS
 FOUR.  [absets_pre], [absets_med_eq], [absets_const] and
 [absets_limit_ext] are Instance/Grp/Limit.v's [sets_pre],
 [sets_med_eq], [sets_const] and [sets_limit_ext] reproved here under
 different names -- character-for-character identical after
 [s/absets_/sets_/g], which is how the audit measured it.  An earlier
 revision of this paragraph said "this lemma and its two helpers" and
 listed only three donors, dropping [sets_pre]; that undercount is
 corrected here rather than silently.  Neither file is the other's
 dependency and the names do not collide, so a consumer may import both.
 The reason for the copy is not mathematical: the block belongs beside its
 donors in Instance/Sets/Complete.v, and putting it there would edit an
 upstream file, which this change does not do.  Importing
 Instance/Grp/Limit.v to borrow it would drag the whole of Instance/Grp.v
 into [Ab]'s dependency cone for four generic lemmas about [Sets], which
 is worse.  Factoring all FOUR into Instance/Sets/Complete.v and having
 both files consume them is the right repair and is NOT done here.

 ** UNIQUENESS IS THE WHOLE CONTENT OF THEOREM 2, PROVED TWICE OVER

 Elementwise, [alim_zero_unique], [alim_plus_unique] and
 [alim_neg_unique] show each operation is determined by the leg
 conditions, and [alim_structure_unique] bundles them; note what those
 consume -- ONLY that the legs preserve the candidate structure, NO law of
 it, so the statement is sharper than "any abelian-group structure making
 the projections homomorphisms is this one".  Categorically,
 [Ab_lift_cone_unique] is the generic [screates_lift_unique] at this
 instance, giving the canonical cone isomorphism.  A whole-record
 statement "[A' = LimitAb] for any abelian group [A'] on that carrier" is
 NOT delivered and is not a gap more work here could close: it would need
 [cmon_setoid (ab_cmon A') = vertex_obj[L]] as a Leibniz equality and a
 transport in the type of every operation.

 ** ON THE HOUSE RULE THAT MORPHISMS ARE COMPARED WITH [≈]

 Four statements here write [=] between morphisms -- [alim_over_legs],
 [ab_lift_legs], [ab_fcone_leg] and [ab_complete_leg] -- and each does so
 because both sides are the SAME TERM, the witness being [eq_refl].  They
 record Mac Lane's [F sigma = tau] at full strength, which is strictly
 stronger than the [≈] the [StrictLift] clause asks for; every law, every
 proof and the [slift_legs] clause consumed by [ab_strict_lift] use [≈].
 The same applies to the object-level [=] of [alim_over_obj],
 [ab_lift_apex], [ab_fcone_apex], [ab_complete_carrier] and the three
 [ab_complete_*] element equations, which compare OBJECTS and ELEMENTS
 rather than morphisms and are the discipline's sanctioned exception.

 ** UNIVERSES, measured off BOTH binder and block over all 86 constants

 RE-MEASURED after the PR "algebraic carriers are sets" (2026-09-17), by
 [About] under [Set Printing Universes] on every name [Print Module]
 lists.  TWO figures in this paragraph moved and the rest reproduce.
 First, the file now holds 86 constants, not 85 -- 76 declaration heads
 plus the same ten [Program] obligations.  Second, the "ZERO word-bounded
 [Set] occurrences anywhere" is gone: 81 of the 86 blocks mention [Set],
 and all 82 occurrences are the strict bound [Set < u], never an equation
 and never an instance.  That bound is what [PropEquiv] costs, [Prop]'s
 sort entering every object record through [cmon_prop]; a bound is not a
 pin, which is the distinction the paragraph draws throughout.  The
 equation count is still TEN, but its membership changed: [absets_pre] is
 no longer among them, and [LimitAb] and [ab_strict_lift] now are, so the
 ten read [absets_med_eq], [absets_limit_ext], [absets_const],
 [absets_const_obligation_1], [LimitAb], [ab_strict_lift] and four
 [ab_complete_*] ([_carrier], [_leg], [_neg], [_plus]).  The sentence
 below is left in its measured-then form, with this correction attached.

 The 85 are the 75 declaration heads plus the ten [Program] obligations,
 read back with [Set Printing Universes] and [About].  ZERO word-bounded
 [Set] occurrences anywhere, and only TEN carry a block EQUATION at all
 (every block carries the strict inequality [u0 < u1] or a relabelling of
 it, which is not an equation and is not counted).  Five of the ten are
 the generic [Sets] section -- [absets_pre], [absets_med_eq],
 [absets_limit_ext], [absets_const] and its obligation
 [absets_const_obligation_1], which no source-level reading sees -- all
 five carrying [u0 = u3], which identifies the shape's hom-and-proof
 universe with [Sets]' carrier universe, and the first three additionally
 [u1 = u2], which identifies two of the ambient's; that [u0 = u3] is
 [IsALimit]'s doing and not this file's.  The other five are the
 [ab_complete_*] readbacks, which BIND their shape explicitly and so carry
 [u = u0], identifying the shape's object universe with its hom-and-proof
 universe -- that is [Complete]'s own [@{u u u u0}] shape written out,
 inherited from [Sets_Complete] and not narrowed here.  The remaining 75
 constants (76 as re-measured above) carry no block equation,
 [Ab_Complete@{u u0 u1} :
 Complete@{u u u u0}] with [u < u0] and [u0 <= u1] among them, so the
 smallness discipline is exactly [Sets_Complete]'s.  This is the same
 count and the same split as Instance/Grp/Limit.v records for its own 83.

 ** WHAT WAS IN TREE BEFORE, MEASURED

 Measured on the worktree this file was written against, by grepping all
 [.v] files for the tokens: [Ab_Complete], [Ab_Forget_creates],
 [Ab_Forget_Preserves] and [Ab_Forget_reflects] each returned ZERO hits,
 so no completeness, creation, preservation or reflection statement about
 [Ab] or [Ab_Forget] existed.  What DID exist about [Ab_Forget] and limits
 is the single constant discussed above, [Ab_Forget_Continuous]
 (Instance/Ab/FreeNotContinuous.v), together with its file's negative
 results about the LEFT adjoint [FreeAb].  No [CMon_Complete]
 exists either; the argument below is written at [Ab] and the [CMon] case
 is not extracted from it.

 ** STATUS: axiom-free

 [Print Assumptions] reports "Closed under the global context" for all of
 [Ab_Complete], [Ab_Forget_creates_continuous], [Ab_Forget_creates_limits],
 [Ab_Forget_StrictlyCreatesLimit], [Ab_Forget_CreatesLimit],
 [Ab_Forget_StrictlyCreatesLimits], [Ab_Forget_PreservesAllLimits],
 [Ab_Forget_reflects_limits], [Ab_Forget_lifts_limits], [LimitAb],
 [ab_reflects], [alim_created], [alim_structure_unique] and
 [Ab_lift_cone_unique], and for all ten [Program] obligations named in the
 UNIVERSES paragraph.  That is twenty-four readbacks, not a
 directory-wide certification of the remaining sixty-one constants;
 nothing here is registered with [make print-assumptions].

 RE-MEASURED after the PR "algebraic carriers are sets" (2026-09-17):
 one [Print Assumptions] per name over all 86 gives 86 "Closed under
 the global context" and zero [Axioms:] blocks.  The twenty-four
 readbacks above are therefore now a whole-file measurement, with
 sixty-two constants rather than sixty-one outside the original list;
 it is still a ONE-TIME measurement and still not a standing gate.

 ** NOT DELIVERED

 No colimits and no cocompleteness for [Ab] (Instance/Ab/Coproduct.v and
 Instance/Ab/DirectedColimit.v cover pieces of that ground and are not
 touched).  No application of Adjunction/GAFT.v's [GAFT] at [Ab_Forget]
 is built, and no [Ab] counterpart of Instance/Grp/FreeAFT.v.  An
 earlier revision said "No GAFT application at [Ab]: the two hypotheses
 are made available, nothing consumes them"; since #449 and #454 both
 are consumed in code elsewhere, measured by their occurrences outside
 comments in the .v files outside Test/: [Ab_Complete] by Instance/Mod/
 Limit.v (limits created along [RMod_Forget_Ab]) and by Instance/Mod/
 TensorAFT.v, which applies Adjunction/Representability/Sets.v's
 [representability_theorem], the adjoint functor theorem in
 representability form, at [Ab]; [Ab_Forget_creates_continuous] by
 Instance/Mod/Limit.v, Instance/Mod/TensorAFT.v, Instance/Rng/AFT.v,
 Instance/Mod/Watts.v and Instance/Mod/Watts/Unconditional.v.  No
 comparison of the created binary product with any cartesian or
 biproduct structure on [Ab], which would go
 through a discrete diagram and so through Instance/Discrete.v's
 unannotated [DiscreteCat_Functor].  No [CMon] analogue, though the engine
 transfers unchanged -- drop [ab_neg] and its two laws.  No monadicity
 statement and no comparison functor, so nothing here says [Ab] IS an
 Eilenberg-Moore category.  No signature-generic statement covering [Grp],
 [Ab], [CMon] and [Rng] at once; the duplication noted above is real and
 is left standing.  And NOTHING is registered as an [Instance] -- the file
 declares none, following its template, since a chosen limit must not
 become globally resolvable.  No [Test/Probe] file accompanies this one,
 so the [eq_refl] readbacks below are guarded only by being [Example]s in
 this file. 

 --------
 nLab：https://ncatlab.org/nlab/show/created+limit
 nLab：https://ncatlab.org/nlab/show/limit#limits_in_categories_of_algebras
 nLab：https://ncatlab.org/nlab/show/Ab
 维基百科：https://en.wikipedia.org/wiki/Category_of_abelian_groups
 Mac Lane：《为工作数学家而作的范畴论》，第二版（GTM 5），§V.1 定理 2 和 3，书页 111-112（PDF 页 120-121）
 Awodey：《范畴论》，第一版（CMU 预印本，2005 年 9 月），§5.6 命题 5.32，印刷页 119（PDF 页 128）[Ab_Forget]（实例/Ab.v）严格地创造每一个极限。给定一个基于集合的底层图的限制锥，其顶点上恰好有一个阿贝尔群结构，使得每一个投影都是同态（[alim_structure_unique]，Mac Lane 定理 2），由此得到的锥精确地位于给定锥之上（[alim_over_obj] 和 [alim_over_legs] 都是 [eq_refl]，因为 [Ab_Forget] 的对象映射是 [cmon_setoid ∘ ab_cmon] 的投影），它是极限的（[alim_created]），并且一个阿贝尔群锥的像是极限时，该锥自身也是极限的（[ab_reflects]）。打包为
 Structure/Limit/Creation.v 自己的类 --
 [Ab_Forget_StrictlyCreatesLimit] 、[Ab_Forget_CreatesLimit] 和
 [Ab_Forget_creates_limits] -- 从中通过应用得到标准推论：
 [Ab_Complete]（Mac Lane 的定理 3）和
 [Ab_Forget_creates_continuous : ContinuousFunctor Ab_Forget]，
 锥层读取，其中只有顶点的 [Ab_Forget_PreservesAllLimits]
 从中导出，以及旁边的 [Ab_Forget_reflects_limits]。

 ** 为什么需要第二个 [ContinuousFunctor Ab_Forget] -- 这是本文件存在的主要原因

 Instance/Ab/FreeNotContinuous.v 已经声明
 [Ab_Forget_Continuous : ContinuousFunctor Ab_Forget]，其证明项是
 [right_adjoint_Continuous free_ab_adjunction] -- RAPL 应用于 Instance/Ab/Free.v 的 [free_ab_adjunction : FreeAb ⊣ Ab_Forget]。
 该常量在这里未被触及、未重复使用，也未重述：
 下面声明的则是 [Ab_Forget_creates_continuous]
 （不同项的不同名称），差异就是关键所在。[Ab_Forget_Continuous]  假定自由/忘记伴随。
 [Ab_Forget_creates_continuous]  不假定除以下之外的任何东西：
 [Sets_Complete]  和下面的创建结果；没有伴随，没有自由对象，没有 [FreeAb] 。这对于恰好一个消费者形式很重要。
 Freyd 的一般伴随函子定理（Adjunction/GAFT.v）接受 [comp : @Complete C] 和 [cont : @PreservesImageLimit C D U]，并返回 [U] 的一个左伴随。给它提供 [Ab_Forget_Continuous] 就相当于给它提供一个由它被要求产生的伴随自身构建的项，因此该应用将是循环的，并且什么都不会建立；给它提供 [Ab_Forget_creates_continuous] 则不会如此，这正是使 Instance/Grp/FreeAFT.v 的 [Ab] 类似体成为可能的原因。针对本段先前修订的一个更正，因为它会误导尝试应用的读者。[ContinuousFunctor] 并不像 GAFT 要求 [PreservesImageLimit] 那样进行归属：已测量，[GAFT Ab_Forget Ab_Complete Ab_Forget_creates_continuous sols] 被拒绝，显示“术语 \"Ab_Forget_creates_continuous\" 的类型为 \"ContinuousFunctor Ab_Forget\"，而预期类型为 \"Limit.PreservesImageLimit\"（无法统一 \"Limit.Limit K\" 和 \"Cone.Cone K\"）”。桥 [Continuous_PreservesImageLimit]（Construction/Comma/Creation.v）是承重的，必须出现在术语中，正如在 [Grp]（Instance/Grp/FreeAFT.v 的 [free_group_via_GAFT]）中所做的那样，其探针固定了与其 N6 相同的拒绝。因此 [Ab] 三元组将是 [Ab_Complete]、[Continuous_PreservesImageLimit Ab_Forget_creates_continuous] 和一个解集。这里没有构建任何 [Ab] 应用程序 -- 见未交付 -- 因此所声称的是可用性，而不是使用。

 另外两个区别已说明，以免混淆两个常数。[ContinuousFunctor] 不是类，并且这里没有任何东西注册为 [Instance]，因此两者在解析中从不竞争；连续性只是创建结果产生的三件事之一，另外两个是 [Ab_Complete] 和反射条款 [Ab_Forget_reflects_limits]，而 RAPL 完全不给出。这里没有声称创建在形式上比连续性更强 -- 本文件中没有将两者作为命题进行比较。

 ** 头条句子在 [eq_refl] 处通过机器检查，而不是讨论在极限处  [Sets_Complete]  选择了 -- 兼容的族
 Instance/Sets/Complete.v -- 创建的阿贝尔群恰好是
 坐标方式的： [ab_complete_carrier] ,
 [ab_complete_plus] ,  [ab_complete_zero] ,  [ab_complete_neg] 和
 [ab_complete_leg] 是五个  [eq_refl] 示例，在任意形状和
 任意阿贝尔群图中。在它们中没有任何东西是特定于
 证明类别的，也没有引入同构；因此该文件不需要具体的证明即可非空，并且也没有构建任何。

 ** 被提升的是什么，以及为什么它比  [CMon] 多一个操作实例/Ab.v 的 [AbObject] 通过 [ab_neg_respects] 和 [ab_neg_left] 扩展实例/CMon.v 的 [CMonObject] 。强制转换 [ab_cmon :> CMonObject] 提供了 [carrier]、[cmon_zero]、[cmon_plus] 以及四条交换幺半群定律。因此三个操作被提升——[cmon_plus]、[cmon_zero]、[ab_neg]——对应六条定律：结合律、交换律、左单位律、左逆元律，以及两条 [Proper] 条款。交换律是唯一一条在群模板实例/Grp/Limit.v 中没有对应的定律，它的实现成本与其他定律完全相同，因为腿的联合单射性不关心定律的内容。态射方面的成本完全与群的情况成本相同——这一标题的早期草稿说它更便宜，但测量结果否定了这一点。[AbHom A B] 定义为 [CMonHom A B]（Instance/Ab.v），所以一个同态需要 [cmon_map_zero] 和 [cmon_map_plus]，而无需其他，取反的保持是定理 [ab_map_neg]，而不是一个域——但 [GrpHom] 拥有相同的形状，[grp_map_inv]（Instance/Grp.v）扮演 [ab_map_neg] 的角色。在对两个 [.vo] 文件的测量中，它们都承担了十个 [Program] 义务，并且名称匹配：为两条腿、调解器和反射调解器各两个，为三条腿家族和常值映射各一个。对象侧多了两个常量，而且正好是两个。在 [.glob] 文件中计算 [def] + [prf] 个头，这个文件声明了 75 个，而 Instance/Grp/Limit.v 中是 73 个；这多出的两个是 [alim_comm]，它没有对应项，因为 [GrpObject] 没有声明交换性，以及 [alim_neg_respects]，它没有对应项，因为 [GrpObject] 没有将逆运算的尊重性作为一个字段（Instance/Grp.v 仅列出了 [grp_mul_respects]；[grp_inv_Proper] 是之后推导的），而 [AbObject] 则有（Instance/Ab.v）。

 ** 引擎是一个可复用的引理，其中没有任何代数内容[absets_limit_ext] 说在 [Sets] 中，极限锥的各条边在元素上是联合单射的：顶点上两点在每条边上都相同则它们相等。 这一点仅从中介的唯一性即可证明，使用两个来自顶点自身的常数映射作为探针——因此不需要终对象，也不引入其他模块。 以下每条阿贝尔群定律都是三行：应用它，重写定义三角形，在 [K j] 中应用该定律。关于重复，公开而非掩饰，数量是四个。[absets_pre]、[absets_med_eq]、[absets_const] 和 [absets_limit_ext] 是 Instance/Grp/Limit.v 的 [sets_pre]、[sets_med_eq]、[sets_const] 和 [sets_limit_ext]，在此以不同的名称重新证明——在 [s/absets_/sets_/g] 之后字符完全相同，这就是审计测量的方法。该段落的早期修订版写道“这个引理及其两个辅助引理”，只列出了三个贡献者，遗漏了 [sets_pre]；这种计数不足在此处得到了更正，而非悄然处理。两个文件彼此并非依赖关系，名称也不冲突，因此用户可以同时导入。复制的原因不是数学上的：该模块属于 Instance/Sets/Complete.v 中其贡献者旁边，如果放在那里将编辑上游文件，而此次更改没有这样做。导入
 Instance/Grp/Limit.v 来借用它会将整个 Instance/Grp.v 拖入 [Ab] 的依赖锥中，以用于关于 [Sets] 的四个通用引理，这是更糟的。将全部四个引理归入 Instance/Sets/Complete.v 并让两个文件都使用它们才是正确的修复，而这里并没有这样做。

 ** 唯一性是定理 2 的全部内容，并已被证明两次逐元素地，[alim_zero_unique]、[alim_plus_unique] 和 [alim_neg_unique] 显示每个操作都由腿的条件决定，而 [alim_structure_unique] 将它们打包；注意它们消耗的内容——仅仅是腿保持候选结构，而不是其任何规律，因此该陈述比“任何使投影为同态的阿贝尔群结构都是这个”更明确。从范畴论的角度看，[Ab_lift_cone_unique] 是这一实例下的通用 [screates_lift_unique]，给出了典范锥同构。整个记录的陈述“[A' = LimitAb] 对该承载上的任何阿贝尔群 [A'] 成立”并没有给出，也不是这里进一步工作可以弥补的空白：它将需要 [cmon_setoid (ab_cmon A') = vertex_obj[L] 作为莱布尼兹等式，并在每个操作类型中进行传输。

 ** 关于“态射用 [≈] 比较”的内部规则这里有四个陈述在态射之间写 [=] -- [alim_over_legs]、[ab_lift_legs]、[ab_fcone_leg] 和 [ab_complete_leg] -- 每个都是因为两边是相同的项，证据是 [eq_refl]。它们完全记录了 Mac Lane 的 [F sigma = tau]，其强度严格高于 [StrictLift] 条款要求的 [≈]；每条定律、每个证明以及 [ab_strict_lift] 使用的 [slift_legs] 条款都使用 [≈]。对 [alim_over_obj] 的对象级 [=]、[ab_lift_apex]、[ab_fcone_apex]、[ab_complete_carrier] 以及三个 [ab_complete_*] 元素方程也同样适用，它们比较的是对象和元素而非态射，这是该学科允许的例外。

 ** 宇宙，通过对所有 86 个常量的绑定器和代码块进行测量在 PR “代数载体是集合” (2026-09-17) 之后重新测量，由 [About] 在 [Set Printing Universes] 下对每个名称 [Print Module] 列表进行测量。本段中的两个图移动了，其余保持不变。首先，文件现在包含 86 个常量，而不是 85 个——76 个声明头加上相同的十个 [Program] 义务。其次，“零单词边界 [Set] 出现于任何地方”已消失：86 个块中有 81 个提到 [Set]，并且所有 82 次出现都是严格界限 [Set < u]，从不为方程，也从不为实例。该界限是 [PropEquiv] 的成本，[Prop] 的类型通过 [cmon_prop] 进入每个对象记录；界限不是销，这就是本段始终所强调的区别。方程数量仍然是十个，但其成员发生了变化：[absets_pre] 不再其中，而 [LimitAb] 和 [ab_strict_lift] 现在在其中，因此这十个读作 [absets_med_eq]、[absets_limit_ext]、[absets_const]、[absets_const_obligation_1]、[LimitAb]、[ab_strict_lift] 以及四个 [ab_complete_*]（[_carrier]、[_leg]、[_neg]、[_plus]）。下面的句子保持其先测量后格式，并附上此更正。这85个是75个声明头加上十个[Program]义务，通过[Set Printing Universes]和[About]回读。任何地方都没有[Set]的字界出现，只有十个携带块方程（每个块都携带严格不等式[u0 < u1]或其重命名，这不是方程且不计入）。十个中有五个是通用的[Sets]部分——[absets_pre]、[absets_med_eq]、[absets_limit_ext]、[absets_const]及其义务[absets_const_obligation_1]，在源代码级别没有人看到——这五个都携带[u0 = u3]，它将形的同态与证明宇宙与[Sets]的承载宇宙关联，前三个额外有[u1 = u2]，它标识其中两个环境的；[u0 = u3]是[IsALimit]的工作，而不是这个文件的。其他五个是 [ab_complete_*] 回读，它们明确绑定了它们的形状，因此携带 [u = u0]，将形状的对象宇宙与其同构和证明宇宙识别 —— 即 [Complete] 自己的 [@{u u u u0}] 形状被写出，继承自 [Sets_Complete] 并且在此未被缩小。剩下的 75 个常量（如上重新测量为 76 个）不携带任何块方程，[Ab_Complete@{u u0 u1} : Complete@{u u u u0}]，其中包括 [u < u0] 和 [u0 <= u1]，因此小型化规则恰好是 [Sets_Complete] 的。这与 Instance/Grp/Limit.v 记录的其自身 83 个的数量和分配相同。

 ** 之前在树中的内容，经测量在该文件所基于的工作树上，通过在所有 [.v] 文件中查找以下标记：[Ab_Complete]、[Ab_Forget_creates]、[Ab_Forget_Preserves] 和 [Ab_Forget_reflects]，均未找到任何匹配，因此关于 [Ab] 或 [Ab_Forget] 的完整性、创建、保存或反映声明不存在。关于 [Ab_Forget] 和限制的唯一存在信息是上述讨论的单一常量 [Ab_Forget_Continuous]（Instance/Ab/FreeNotContinuous.v），以及其文件对左伴随 [FreeAb] 的负面结果。[CMon_Complete] 也不存在；下面的论证写于 [Ab]，并且 [CMon] 的情况并未从中提取。

 ** 状态：无公理[Print Assumptions] 对所有的 [Ab_Complete]、[Ab_Forget_creates_continuous]、[Ab_Forget_creates_limits]、[Ab_Forget_StrictlyCreatesLimit]、[Ab_Forget_CreatesLimit]、[Ab_Forget_StrictlyCreatesLimits]、[Ab_Forget_PreservesAllLimits]、[Ab_Forget_reflects_limits]、[Ab_Forget_lifts_limits]、[LimitAb]、[ab_reflects]、[alim_created]、[alim_structure_unique] 和 [Ab_lift_cone_unique] 报告“在全局上下文下关闭”，并且对 UNIVERSES 段落中命名的十个 [Program] 义务也报告“在全局上下文下关闭”。这总共有二十四个回读，而不是对剩余六十一常量的整个目录认证；此处没有任何内容在 [make print-assumptions] 中注册。在 PR “代数载体是集合”（2026-09-17）之后重新测量：
 对所有 86 个名称，每个名称一个 [Print Assumptions]，总计 86 个“在全局上下文下封闭”，且 [Axioms:] 块为零。上述二十四次回读现在因此为整个文件的测量，常量为 62 个，而非原始列表之外的 61 个；
 这仍然是一次性测量，仍然不是常驻门。

 ** 未交付对于 [Ab] 没有余极限和余完备（Instance/Ab/Coproduct.v 和 Instance/Ab/DirectedColimit.v 涵盖了这部分内容，但没有涉及）。没有在 [Ab_Forget] 上构建 Adjunction/GAFT.v 的 [GAFT] 的应用，也没有 Instance/Grp/FreeAFT.v 的 [Ab] 对应部分。较早的修订版本中说“在 [Ab] 上没有 GAFT 应用：两个假设已提供，但没有任何东西使用它们”；由于 #449 和 #454 都在其他地方的代码中被使用，通过在 Test/ 之外的 .v 文件中的注释外出现次数来衡量：[Ab_Complete] 由 Instance/Mod/Limit.v（沿 [RMod_Forget_Ab] 创建的极限）和 Instance/Mod/TensorAFT.v 使用，后者在 [Ab] 应用 Adjunction/Representability/Sets.v 的 [representability_theorem]，即表示形式下的伴随函子定理；[Ab_Forget_creates_continuous] 由 Instance/Mod/Limit.v、Instance/Mod/TensorAFT.v、Instance/Rng/AFT.v、Instance/Mod/Watts.v 和 Instance/Mod/Watts/Unconditional.v 使用。没有将所创建的二元积与 [Ab] 上的任何笛卡尔积或积余结构进行比较，这将通过一个离散图进行，因此通过 Instance/Discrete.v 中未标注的 [DiscreteCat_Functor]。没有 [CMon] 的类比，尽管引擎保持不变——删除 [ab_neg] 及其两个定律。没有单子性声明，也没有比较函子，因此这里没有任何内容表明 [Ab] 是一个 Eilenberg-Moore 范畴。没有涵盖 [Grp]、[Ab]、[CMon] 和 [Rng] 的通用签名声明；上文指出的重复是真实存在的，并且保持不变。并且没有任何东西被注册为 [Instance]——文件未声明任何内容，遵循其模板，因为所选的极限不能成为全局可解析的。没有 [Test/Probe] 文件随此文件一起提供，因此下面的 [eq_refl] 读回仅通过作为此文件中的 [Example] 来保护。
*)

(* * * Joint monicity of limit legs in [Sets], elementwise / * * 在 [Sets] 中极限腿的联合单调性，按元素 *)

Section AbSetsExt.

Context {J : Category}.
Context {F : J ⟶ Sets}.
Context {c : Sets}.
Context (H : IsALimit F c).

Definition absets_pre {d : Sets} (u : d ~{Sets}~> c) : Cone F :=
  @Build_Cone J Sets F d
    (@Build_ACone J Sets d F (fun j => limit_leg H j ∘ u)
       (fun x y f =>
          transitivity (comp_assoc _ _ _)
            (@compose_respects Sets _ _ _ _ _ (limit_leg_coherence H f) _ _
               (reflexivity u)))).

Lemma absets_med_eq {d : Sets} (u v : d ~{Sets}~> c) :
  (∀ j : J, limit_leg H j ∘ u ≈ limit_leg H j ∘ v) → u ≈ v.
Proof.
  intro Huv.
  apply (limit_med_eq H (absets_pre u)).
  - intro j; reflexivity.
  - intro j; symmetry; apply Huv.
Qed.

Program Definition absets_const (x : carrier c) : c ~{Sets}~> c :=
  {| morphism := fun _ => x |}.

Lemma absets_limit_ext (x y : carrier c) :
  (∀ j : J, limit_leg H j x ≈ limit_leg H j y) → x ≈ y.
Proof.
  intro Hxy.
  exact (absets_med_eq (absets_const x) (absets_const y) (fun j a => Hxy j) x).
Qed.

End AbSetsExt.

(* * * The created abelian-group structure on a limit of underlying sets / * * 在基础集合的极限上创建的阿贝尔群结构 *)

Section AbLift.

Context {J : Category}.
Context (K : J ⟶ Ab).
Context (L : Limit (Ab_Forget ◯ K)).

Definition alim_leg (j : J) :
  vertex_obj[L] ~{Sets}~> cmon_setoid (ab_cmon (K j)) :=
  limit_leg (limit_is_alimit L) j.

Lemma alim_leg_coherence {x y : J} (f : x ~{J}~> y)
  (a : carrier vertex_obj[L]) :
  cmon_map (fmap[K] f) (alim_leg x a) ≈ alim_leg y a.
Proof. exact (limit_leg_coherence (limit_is_alimit L) f a). Qed.

Lemma alim_ext (x y : carrier vertex_obj[L]) :
  (∀ j : J, alim_leg j x ≈ alim_leg j y) → x ≈ y.
Proof. exact (absets_limit_ext (limit_is_alimit L) x y). Qed.

(** ** The addition / ** 加法 *)

Definition alim_pair : Sets :=
  {| carrier   := carrier vertex_obj[L] * carrier vertex_obj[L]
   ; is_setoid := prod_setoid |}.

Program Definition alim_plus_leg (j : J) :
  alim_pair ~{Sets}~> cmon_setoid (ab_cmon (K j)) :=
  {| morphism := fun p =>
       cmon_plus (K j) (alim_leg j (fst p)) (alim_leg j (snd p)) |}.
Next Obligation.
  intros p q Hpq.
  destruct Hpq as [H1 H2].
  now rewrite H1, H2.
Qed.

Lemma alim_plus_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Ab_Forget ◯ K] f ∘ alim_plus_leg x ≈ alim_plus_leg y.
Proof.
  intro p; simpl.
  rewrite cmon_map_plus.
  now rewrite !alim_leg_coherence.
Qed.

Definition alim_plus_cone : Cone (Ab_Forget ◯ K) :=
  @Build_Cone J Sets (Ab_Forget ◯ K) alim_pair
    (@Build_ACone J Sets alim_pair (Ab_Forget ◯ K)
       alim_plus_leg (@alim_plus_coherence)).

Definition alim_plus_map : alim_pair ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) alim_plus_cone.

Definition alim_plus (a b : carrier vertex_obj[L]) : carrier vertex_obj[L] :=
  alim_plus_map (a, b).

Lemma alim_plus_triangle (j : J) (a b : carrier vertex_obj[L]) :
  alim_leg j (alim_plus a b)
    ≈ cmon_plus (K j) (alim_leg j a) (alim_leg j b).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) alim_plus_cone j (a, b)).
Qed.

Lemma alim_plus_respects :
  Proper (equiv ==> equiv ==> equiv) alim_plus.
Proof.
  intros a a' Ha b b' Hb.
  exact (proper_morphism alim_plus_map (a, b) (a', b') (Ha, Hb)).
Qed.

(** ** The zero *)

Program Definition alim_zero_leg (j : J) :
  unit_setoid_object ~{Sets}~> cmon_setoid (ab_cmon (K j)) :=
  {| morphism := fun _ => cmon_zero (K j) |}.

Lemma alim_zero_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Ab_Forget ◯ K] f ∘ alim_zero_leg x ≈ alim_zero_leg y.
Proof. intro p; simpl; apply cmon_map_zero. Qed.

Definition alim_zero_cone : Cone (Ab_Forget ◯ K) :=
  @Build_Cone J Sets (Ab_Forget ◯ K) unit_setoid_object
    (@Build_ACone J Sets unit_setoid_object (Ab_Forget ◯ K)
       alim_zero_leg (@alim_zero_coherence)).

Definition alim_zero_map : unit_setoid_object ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) alim_zero_cone.

Definition alim_zero : carrier vertex_obj[L] := alim_zero_map ttt.

Lemma alim_zero_triangle (j : J) :
  alim_leg j alim_zero ≈ cmon_zero (K j).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) alim_zero_cone j ttt).
Qed.

(** ** The negation / ** 否定 *)

Program Definition alim_neg_leg (j : J) :
  vertex_obj[L] ~{Sets}~> cmon_setoid (ab_cmon (K j)) :=
  {| morphism := fun a => ab_neg (K j) (alim_leg j a) |}.
Next Obligation. intros a b Hab; now rewrite Hab. Qed.

Lemma alim_neg_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Ab_Forget ◯ K] f ∘ alim_neg_leg x ≈ alim_neg_leg y.
Proof.
  intro a; simpl.
  rewrite ab_map_neg.
  now rewrite alim_leg_coherence.
Qed.

Definition alim_neg_cone : Cone (Ab_Forget ◯ K) :=
  @Build_Cone J Sets (Ab_Forget ◯ K) vertex_obj[L]
    (@Build_ACone J Sets vertex_obj[L] (Ab_Forget ◯ K)
       alim_neg_leg (@alim_neg_coherence)).

Definition alim_neg_map : vertex_obj[L] ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) alim_neg_cone.

Definition alim_neg (a : carrier vertex_obj[L]) : carrier vertex_obj[L] :=
  alim_neg_map a.

Lemma alim_neg_triangle (j : J) (a : carrier vertex_obj[L]) :
  alim_leg j (alim_neg a) ≈ ab_neg (K j) (alim_leg j a).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) alim_neg_cone j a).
Qed.

Lemma alim_neg_respects : Proper (equiv ==> equiv) alim_neg.
Proof.
  intros a a' Ha.
  exact (proper_morphism alim_neg_map a a' Ha).
Qed.

(* * ** The abelian-group laws, by joint monicity of the legs / * ** 阿贝尔群定律，由腿的联合单射性 *)

Lemma alim_assoc (a b c : carrier vertex_obj[L]) :
  alim_plus (alim_plus a b) c ≈ alim_plus a (alim_plus b c).
Proof.
  apply alim_ext; intro j.
  rewrite !alim_plus_triangle.
  apply cmon_plus_assoc.
Qed.

(* The one law with no counterpart in the group template, and it costs exactly what the others cost: joint monicity does not care what the law says. / 在组模板中没有对应条款的一条法律，其费用正好与其他条款相同：联合单调性不关心法律怎么说。 *)
Lemma alim_comm (a b : carrier vertex_obj[L]) :
  alim_plus a b ≈ alim_plus b a.
Proof.
  apply alim_ext; intro j.
  rewrite !alim_plus_triangle.
  apply cmon_plus_comm.
Qed.

Lemma alim_zero_l (a : carrier vertex_obj[L]) : alim_plus alim_zero a ≈ a.
Proof.
  apply alim_ext; intro j.
  rewrite alim_plus_triangle, alim_zero_triangle.
  apply cmon_plus_zero_l.
Qed.

Lemma alim_neg_l (a : carrier vertex_obj[L]) :
  alim_plus (alim_neg a) a ≈ alim_zero.
Proof.
  apply alim_ext; intro j.
  rewrite alim_plus_triangle, alim_neg_triangle, alim_zero_triangle.
  apply ab_neg_left.
Qed.

(* * ** The vertex's equality is propositional / * ** 顶点的相等性是命题性的 *)

(*
 Since the PR "algebraic carriers are sets" (2026-09-17) an [AbObject]
 carries [cmon_prop], so the lifted group owes a [Prop]-valued relation on
 [vertex_obj[L]] -- and [L] here is an ARBITRARY limit of the underlying
 sets, not the one [Sets_Complete] chooses, so
 Instance/Sets/Propositional.v's [limit_PropEquiv] does not apply on the
 nose.  The edit list for this phase predicted a hypothesis on [L],
 discharged at [Ab_Complete]; that turned out not to be needed, and taking
 one would have been fatal, since [CreatesLimits] quantifies over every [L]
 and leaves no place to put it.

 The relation below is instead the one the section already has a theorem
 about: two points of the vertex are related when every LEG relates them.
 [alim_ext] is exactly the implication into `≈`, and it holds at an
 arbitrary limit because a limit's vertex is detected by its projections;
 the converse is each leg being a setoid map.  So a limit of propositional
 carriers is propositional, with no extra hypothesis anywhere. 

 --------
 自从 PR “代数载体是集合”(2026-09-17) 以来，[AbObject] 承载 [cmon_prop]，因此提升的群在 [vertex_obj[L] 上欠一个 [Prop] 值的关系——这里的 [L] 是底层集合的任意极限，而不是 [Sets_Complete] 选择的那个，所以 Instance/Sets/Propositional.v 的 [limit_PropEquiv] 并不能直接应用。此阶段的编辑列表预测了 [L] 上的一个假设，该假设在 [Ab_Complete] 处被解除；事实证明这是不需要的，而采取这样一个假设将是致命的，因为 [CreatesLimits] 对每一个 [L] 进行量化，并且没有地方可以放它。下面的关系实际上是该部分已经有定理的内容：当每条边（LEG）都将两个顶点点联系起来时，两个顶点就关联。[alim_ext] 正好是 `≈` 的推论，并且它在任意极限下成立，因为极限的顶点可以通过其投影来确定；反过来，每条边都是一个集同态映射。因此，命题载体的极限是命题性的，且在任何地方都没有额外假设。
*)
Definition alim_prop : PropEquiv (is_setoid vertex_obj[L]) :=
  @PropEquiv_of_relation _ (is_setoid vertex_obj[L])
    (fun x y => forall j : J,
       @pequiv _ _ (cmon_prop (K j)) (alim_leg j x) (alim_leg j y))
    (fun x y H => alim_ext x y (fun j => pequiv_to _ _ (H j)))
    (fun x y H j => pequiv_from _ _ (proper_morphism (alim_leg j) x y H)).

(** ** The lifted abelian group / ** 提升的阿贝尔群 *)

Definition LimitAb : AbObject :=
  {| ab_cmon :=
       {| cmon_setoid        := vertex_obj[L]
        ; cmon_zero          := alim_zero
        ; cmon_plus          := alim_plus
        ; cmon_plus_respects := alim_plus_respects
        ; cmon_plus_assoc    := alim_assoc
        ; cmon_plus_comm     := alim_comm
        ; cmon_plus_zero_l   := alim_zero_l
        ; cmon_prop          := alim_prop |}
   ; ab_neg          := alim_neg
   ; ab_neg_respects := alim_neg_respects
   ; ab_neg_left     := alim_neg_l |}.

(** ** The legs are homomorphisms / ** 腿是同态 *)

(*
 Only [cmon_map_zero] and [cmon_map_plus] are owed: [AbHom] IS [CMonHom]
 (Instance/Ab.v), and preservation of negation is the theorem
 [ab_map_neg] rather than a field. 

 --------
 只有 [cmon_map_zero] 和 [cmon_map_plus] 是欠的：[AbHom] 是 [CMonHom] （实例/缩写），而否定的保持是定理 [ab_map_neg] 而不是一个域。
*)
Program Definition alim_hom (j : J) : AbHom LimitAb (K j) :=
  {| cmon_map := alim_leg j |}.
Next Obligation. apply alim_zero_triangle. Qed.
Next Obligation. apply alim_plus_triangle. Qed.

Lemma alim_hom_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[K] f ∘ alim_hom x ≈ alim_hom y.
Proof. intro a; exact (alim_leg_coherence f a). Qed.

Definition alim_cone : Cone K :=
  @Build_Cone J Ab K LimitAb
    (@Build_ACone J Ab LimitAb K alim_hom (@alim_hom_coherence)).

(* * ** Strictness: the lifted cone lies over [L] on the nose / * ** 严格性：被抬起的圆锥位于鼻子上的 [L] 上 *)

Definition alim_over_obj : Ab_Forget LimitAb = vertex_obj[L] := eq_refl.

Definition alim_over_legs (j : J) :
  fmap[Ab_Forget] (cone_leg alim_cone j) = alim_leg j := eq_refl.

(** ** The lifted cone is limiting / ** 提升的锥体是有限的 *)

Definition acar_med (N : Cone K) :
  cmon_setoid (ab_cmon vertex_obj[N]) ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) (FCone Ab_Forget N).

Lemma acar_med_commutes (N : Cone K) (j : J) (a : carrier vertex_obj[N]) :
  alim_leg j (acar_med N a) ≈ cmon_map (cone_leg N j) a.
Proof.
  exact (limit_med_commutes (limit_is_alimit L) (FCone Ab_Forget N) j a).
Qed.

Lemma acar_med_zero (N : Cone K) :
  acar_med N (cmon_zero vertex_obj[N]) ≈ alim_zero.
Proof.
  apply alim_ext; intro j.
  rewrite acar_med_commutes, alim_zero_triangle.
  apply cmon_map_zero.
Qed.

Lemma acar_med_plus (N : Cone K) (a b : carrier vertex_obj[N]) :
  acar_med N (cmon_plus vertex_obj[N] a b)
    ≈ alim_plus (acar_med N a) (acar_med N b).
Proof.
  apply alim_ext; intro j.
  rewrite acar_med_commutes, alim_plus_triangle, !acar_med_commutes.
  apply cmon_map_plus.
Qed.

Program Definition alim_med (N : Cone K) : vertex_obj[N] ~{Ab}~> LimitAb :=
  {| cmon_map := acar_med N |}.
Next Obligation. apply acar_med_zero. Qed.
Next Obligation. apply acar_med_plus. Qed.

Definition alim_created : IsALimit K LimitAb.
Proof.
  unshelve refine {| limit_acone := @coneFrom _ _ _ alim_cone |}.
  intro N.
  unshelve refine {| unique_obj := alim_med N |}.
  - intros j a.
    exact (acar_med_commutes N j a).
  - intros v Hv a.
    exact (limit_med_unique (limit_is_alimit L) (FCone Ab_Forget N)
             (cmon_map v) Hv a).
Defined.

(* * ** Uniqueness of the lifted structure (Mac Lane's Theorem 2) / * ** 提升结构的唯一性（Mac Lane 定理 2） *)

Lemma alim_zero_unique (e : carrier vertex_obj[L])
  (He : ∀ j : J, alim_leg j e ≈ cmon_zero (K j)) : e ≈ alim_zero.
Proof.
  apply alim_ext; intro j.
  now rewrite He, alim_zero_triangle.
Qed.

Lemma alim_plus_unique
  (m : carrier vertex_obj[L] → carrier vertex_obj[L] → carrier vertex_obj[L])
  (Hm : ∀ (j : J) a b,
     alim_leg j (m a b) ≈ cmon_plus (K j) (alim_leg j a) (alim_leg j b))
  (a b : carrier vertex_obj[L]) : m a b ≈ alim_plus a b.
Proof.
  apply alim_ext; intro j.
  now rewrite Hm, alim_plus_triangle.
Qed.

Lemma alim_neg_unique
  (n : carrier vertex_obj[L] → carrier vertex_obj[L])
  (Hn : ∀ (j : J) a, alim_leg j (n a) ≈ ab_neg (K j) (alim_leg j a))
  (a : carrier vertex_obj[L]) : n a ≈ alim_neg a.
Proof.
  apply alim_ext; intro j.
  now rewrite Hn, alim_neg_triangle.
Qed.

(*
 The three clauses together: Mac Lane's "there is exactly one
 abelian-group structure on the limit making every projection a
 homomorphism".  No law of the candidate structure is consumed -- not
 even commutativity -- only that the legs preserve it. 

 --------
 三条子句合起来：Mac Lane 的“在极限上正好有一个阿贝尔群结构，使每个投影都是同态”。候选结构的任何定律都没有被使用——甚至连交换律也没有——只是每条腿保持它。
*)
Lemma alim_structure_unique
  (e : carrier vertex_obj[L])
  (m : carrier vertex_obj[L] → carrier vertex_obj[L] → carrier vertex_obj[L])
  (n : carrier vertex_obj[L] → carrier vertex_obj[L])
  (He : ∀ j : J, alim_leg j e ≈ cmon_zero (K j))
  (Hm : ∀ (j : J) a b,
     alim_leg j (m a b) ≈ cmon_plus (K j) (alim_leg j a) (alim_leg j b))
  (Hn : ∀ (j : J) a, alim_leg j (n a) ≈ ab_neg (K j) (alim_leg j a)) :
  (e ≈ alim_zero)
    * (∀ a b, m a b ≈ alim_plus a b)
    * (∀ a, n a ≈ alim_neg a).
Proof.
  split; [ split | ].
  - exact (alim_zero_unique e He).
  - exact (alim_plus_unique m Hm).
  - exact (alim_neg_unique n Hn).
Qed.

End AbLift.

(* * * Reflection: a cone of abelian groups whose image is limiting is limiting / * * 反思：一个其像是极限的阿贝尔群圆锥是极限 *)

Section AbReflect.

Context {J : Category}.
Context (K : J ⟶ Ab).
Context (M : Cone K).
Context (HM : IsLimitCone (FCone Ab_Forget M)).

Definition arefl_med (N : Cone K) :
  cmon_setoid (ab_cmon vertex_obj[N]) ~{Sets}~>
    cmon_setoid (ab_cmon vertex_obj[M]) :=
  limit_med (limitcone_isalimit HM) (FCone Ab_Forget N).

Lemma arefl_med_commutes (N : Cone K) (j : J) (a : carrier vertex_obj[N]) :
  cmon_map (cone_leg M j) (arefl_med N a) ≈ cmon_map (cone_leg N j) a.
Proof using All.
  exact (limit_med_commutes (limitcone_isalimit HM) (FCone Ab_Forget N) j a).
Qed.

Lemma arefl_ext (x y : carrier vertex_obj[M]) :
  (∀ j : J, cmon_map (cone_leg M j) x ≈ cmon_map (cone_leg M j) y) → x ≈ y.
Proof using All. exact (absets_limit_ext (limitcone_isalimit HM) x y). Qed.

Lemma arefl_med_zero (N : Cone K) :
  arefl_med N (cmon_zero vertex_obj[N]) ≈ cmon_zero vertex_obj[M].
Proof using All.
  apply arefl_ext; intro j.
  rewrite arefl_med_commutes, !cmon_map_zero.
  reflexivity.
Qed.

Lemma arefl_med_plus (N : Cone K) (a b : carrier vertex_obj[N]) :
  arefl_med N (cmon_plus vertex_obj[N] a b)
    ≈ cmon_plus vertex_obj[M] (arefl_med N a) (arefl_med N b).
Proof using All.
  apply arefl_ext; intro j.
  rewrite arefl_med_commutes, !cmon_map_plus, !arefl_med_commutes.
  reflexivity.
Qed.

Program Definition arefl_hom (N : Cone K) :
  vertex_obj[N] ~{Ab}~> vertex_obj[M] := {| cmon_map := arefl_med N |}.
Next Obligation. apply arefl_med_zero. Qed.
Next Obligation. apply arefl_med_plus. Qed.

Definition ab_reflects : IsLimitCone M.
Proof using All.
  intro N.
  unshelve refine {| unique_obj := arefl_hom N |}.
  - intros j a.
    exact (arefl_med_commutes N j a).
  - intros v Hv a.
    exact (limit_med_unique (limitcone_isalimit HM) (FCone Ab_Forget N)
             (cmon_map v) Hv a).
Defined.

End AbReflect.

(* * * [Ab_Forget] strictly creates every limit / * * [Ab_Forget] 严格地创造每一个限制 *)

Section AbStrictlyCreates.

Context {J : Category}.
Context (K : J ⟶ Ab).

Definition ab_strict_lift (N : Cone (Ab_Forget ◯ K)) (HN : IsLimitCone N) :
  StrictLift K Ab_Forget N :=
  @Build_StrictLift J Ab Sets K Ab_Forget N
    (alim_cone K (@Build_Limit J Sets (Ab_Forget ◯ K) N HN))
    eq_refl
    (fun x => reflexivity _).

Definition Ab_Forget_StrictlyCreatesLimit : StrictlyCreatesLimit K Ab_Forget.
Proof.
  unshelve refine {| screates := ab_strict_lift |}.
  - intros N HN.
    exact (@ump_limit _ _ _ _
             (alim_created K (@Build_Limit J Sets (Ab_Forget ◯ K) N HN))).
  - intros M HM.
    exact (ab_reflects K M HM).
Defined.

Definition Ab_Forget_CreatesLimit : CreatesLimit K Ab_Forget :=
  StrictlyCreatesLimit_CreatesLimit Ab_Forget_StrictlyCreatesLimit.

End AbStrictlyCreates.

Definition Ab_Forget_StrictlyCreatesLimits :
  StrictlyCreatesLimits Ab_Forget :=
  fun J K => Ab_Forget_StrictlyCreatesLimit K.

Definition Ab_Forget_creates_limits : CreatesAllLimits Ab_Forget :=
  fun J K => Ab_Forget_CreatesLimit K.

Definition Ab_Forget_reflects_limits {J : Category} (K : J ⟶ Ab) :
  ReflectsLimitCone K Ab_Forget :=
  creates_reflects_limits (Ab_Forget_CreatesLimit K).

(*
 Mac Lane's uniqueness clause at the categorical level: any cone of
 abelian groups lying over [N] is canonically isomorphic to the created
 one.  This is the generic [screates_lift_unique] at this instance, not a
 restatement. 

 --------
 麦克莱恩在范畴层次上的唯一性条款：任何位于  [N]  上的阿贝尔群锥都与所生成的锥自然同构。这是该实例下的通用  [screates_lift_unique] ，而不是重述。
*)

Definition Ab_lift_cone_unique {J : Category} (K : J ⟶ Ab)
  (N : Cone (Ab_Forget ◯ K)) (HN : IsLimitCone N)
  (M : Cone K) (i : ConeIso (FCone Ab_Forget M) N) :
  ConeIso M (slift_cone (screates N HN)) :=
  screates_lift_unique (Ab_Forget_StrictlyCreatesLimit K) N HN M i.

(* * * The image of a cone of abelian groups is the elementwise cone / * * 阿贝尔群锥的图像是逐元素锥 *)

Example ab_fcone_apex {J : Category} (K : J ⟶ Ab) (N : Cone K) :
  vertex_obj[FCone Ab_Forget N] = cmon_setoid (ab_cmon vertex_obj[N])
  := eq_refl.

Example ab_fcone_leg {J : Category} (K : J ⟶ Ab) (N : Cone K) (j : J) :
  cone_leg (FCone Ab_Forget N) j = cmon_map (cone_leg N j) := eq_refl.

(* * * Mac Lane's Theorem 2: the lifting half / * * 麦克雷恩定理2：提升部分 *)

Definition Ab_Forget_lifts_limits {J : Category} (K : J ⟶ Ab)
  (L : Limit (Ab_Forget ◯ K)) : Limit K :=
  creates_limit_lift (Ab_Forget_CreatesLimit K) L.

Example ab_lift_apex {J : Category} (K : J ⟶ Ab)
  (L : Limit (Ab_Forget ◯ K)) :
  Ab_Forget (vertex_obj[Ab_Forget_lifts_limits K L]) = vertex_obj[L]
  := eq_refl.

Example ab_lift_legs {J : Category} (K : J ⟶ Ab)
  (L : Limit (Ab_Forget ◯ K)) (j : J) :
  fmap[Ab_Forget]
    (cone_leg (@limit_cone _ _ _ (Ab_Forget_lifts_limits K L)) j)
    = limit_leg (limit_is_alimit L) j
  := eq_refl.

(* * * Corollaries: [Ab] is complete and [Ab_Forget] is continuous / * * 推论：[Ab] 是完备的，[Ab_Forget] 是连续的 *)

Definition Ab_Complete : @Complete Ab :=
  creates_limits_Complete Ab_Forget Sets_Complete Ab_Forget_creates_limits.

(*
 [ContinuousFunctor] is [PreservesLimitCone] quantified over every shape
 and diagram, which is what the word means in Mac Lane §V.4 -- the
 apex-only [PreservesAllLimits] below is its CONSEQUENCE, not the
 definition (Structure/Limit/Preservation.v).

 NAME.  This is NOT Instance/Ab/FreeNotContinuous.v's
 [Ab_Forget_Continuous], which is the same TYPE by a different TERM:
 that one is [right_adjoint_Continuous free_ab_adjunction] and so
 presupposes Instance/Ab/Free.v's adjunction, while this one comes
 from limit creation and presupposes only [Sets_Complete].  See the
 header for why the distinction is load-bearing rather than cosmetic. 

 --------
 [ContinuousFunctor] 是对每一个形状和图表进行量化的 [PreservesLimitCone]，这正是 Mac Lane §V.4 中该词的含义——下面仅有顶点的 [PreservesAllLimits] 是它的结果，而不是定义（Structure/Limit/Preservation.v）。

 名称。 这不是 Instance/Ab/FreeNotContinuous.v 的 [Ab_Forget_Continuous]，它是用不同术语的同一类型：那一个是 [right_adjoint_Continuous free_ab_adjunction]，因此预设了 Instance/Ab/Free.v 的伴随性，而这个则来源于极限创建，仅预设 [Sets_Complete]。请参阅标题，了解为什么这种区别是承重而非装饰性的。
*)

Definition Ab_Forget_creates_continuous : ContinuousFunctor Ab_Forget :=
  creates_limits_continuous Ab_Forget Sets_Complete Ab_Forget_creates_limits.

Definition Ab_Forget_PreservesAllLimits : PreservesAllLimits Ab_Forget :=
  creates_limits_PreservesAllLimits Ab_Forget Sets_Complete
    Ab_Forget_creates_limits.

(* * * "Limits of abelian groups are computed on underlying sets", literally / * * “阿贝尔群的极限是在底层集合上计算的”，字面意思 *)

(*
 At the limits [Sets_Complete] chooses -- the compatible families of
 Instance/Sets/Complete.v -- the created abelian group is the
 coordinatewise one ON THE NOSE: carrier, addition, zero, negation and
 every projection are all [eq_refl], at an ARBITRARY shape and an
 ARBITRARY diagram of abelian groups.  Nothing here is specific to a
 witness category; the readbacks below are the section header's sentence
 machine-checked. 

 --------
 在极限处，[Sets_Complete] 选择了 -- Instance/Sets/Complete.v 的兼容族 -- 所创建的阿贝尔群正好是逐坐标的：载体、加法、零、取负以及每个投影在任意形状和任意阿贝尔群图下都是 [eq_refl] 。这里没有任何内容特定于见证范畴；下面的回读是章节标题的句子经过机器校验的。
*)

Section AbComputed.

Context {J : Category}.
Context (K : J ⟶ Ab).

Example ab_complete_carrier :
  cmon_setoid (ab_cmon (vertex_obj[Ab_Complete J K]))
    = Sets_limit_obj (Ab_Forget ◯ K) := eq_refl.

Example ab_complete_plus
  (a b : carrier (Sets_limit_obj (Ab_Forget ◯ K))) (d : J) :
  `1 (cmon_plus (vertex_obj[Ab_Complete J K]) a b) d
    = cmon_plus (K d) (`1 a d) (`1 b d) := eq_refl.

Example ab_complete_zero (d : J) :
  `1 (cmon_zero (vertex_obj[Ab_Complete J K])) d = cmon_zero (K d) := eq_refl.

Example ab_complete_neg
  (a : carrier (Sets_limit_obj (Ab_Forget ◯ K))) (d : J) :
  `1 (ab_neg (vertex_obj[Ab_Complete J K]) a) d
    = ab_neg (K d) (`1 a d) := eq_refl.

Example ab_complete_leg (d : J) :
  cmon_map (cone_leg (@limit_cone _ _ _ (Ab_Complete J K)) d)
    = Sets_limit_leg (Ab_Forget ◯ K) d := eq_refl.

End AbComputed.
