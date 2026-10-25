Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Free.
Require Import Category.Instance.Mon.Free.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.Quotient.Colimit.
Require Import Category.Instance.Rng.MonoidRing.
Require Import Category.Instance.Rng.GroupRing.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   * * The group completion of a MONOID, as a left adjoint

   nLab:      https://ncatlab.org/nlab/show/group+completion
   nLab:      https://ncatlab.org/nlab/show/free+group
   nLab:      https://ncatlab.org/nlab/show/presentation+of+a+group
   Wikipedia: https://en.wikipedia.org/wiki/Grothendieck_group

   Book: Riehl, "Category Theory in Context" (2nd ed., Dover 2016), §4.1
   Example 4.1.10 (catalogue item [riehl:4.1:example10]), which
   lists the group completion in TWO forms: a left adjoint
   [CMonoid → Ab] and a left adjoint [Monoid → Group].

   [Instance/CMon/Grothendieck.v] delivers the FIRST form.  This file
   delivers the SECOND: for a monoid M, a group K(M) with a monoid
   homomorphism M → U K(M) through which every monoid homomorphism from
   M into the underlying monoid of a group factors uniquely by a group
   homomorphism, assembled into
   [completion_adjunction : CompletionLeft ⊣ Grp_MonSets].

   ** NOT the Grothendieck construction, and not the pairs construction

   [Construction/Grothendieck.v] builds the total category of an indexed
   category; it shares only a name and is neither required nor mentioned
   again.  More importantly this file does NOT reuse
   [Instance/CMon/Grothendieck.v]'s pairs quotient, and the reason is a
   theorem rather than taste -- see the next section.

   ** Two corrections to [Instance/CMon/Grothendieck.v]'s deferral

   That file gives three reasons for not delivering the second form.
   Read them separately: one is FALSE, one is CORRECT AND DECISIVE, and
   the third describes exactly the route taken here.

   (1) FALSE.  It says stating the second form needs "a forgetful
   [Grp ⟶ Mon] that does not exist".  It exists:
   [Grp_MonSets : Grp ⟶ MonSets] at Instance/Rng/GroupRing.v,
   over [MonSets := @Mon Sets Sets_Product_Monoidal]
   (Instance/Rng/MonoidRing.v).  An internal monoid in the
   cartesian monoidal category of setoids IS an ordinary setoid
   monoid, and Instance/Rng/MonoidRing.v supplies the element-level
   dictionary ([mcar], [mop], [mone], [mmap], [mhom]) that a
   construction by generators and relations consumes.  The second
   form is therefore statable, and it is stated here with no new
   category and no new forgetful functor.  (That file's OTHER clause
   in reason (1) -- that Theory/Algebra/Monoid/Hom.v's [Mon] is the
   category of INTERNAL monoids and Construction/Deloop.v's
   [MonObject] carries no category -- is accurate; what does not
   follow is that no forgetful functor exists.)

   (2) CORRECT, AND IT IS WHY THIS FILE LOOKS THE WAY IT DOES.  The
   pairs construction M×M/~ cannot be this adjoint.  It produces an
   ABELIAN group for every input -- definitionally, its [ab_neg]
   being the swap -- whereas the left adjoint of [Group → Monoid]
   must produce non-abelian groups.  Nothing below reuses or adapts
   it, and the file proves it did not silently rebuild it:
   [completion_can_be_nonabelian] exhibits two elements of a
   completion that do not commute, and
   [completion_free_mon_two_nonabelian] does so at the canonical
   example, the free monoid on two letters.

   (3) The route described there IS the route taken: the free group on
   the underlying setoid of M, quotiented by the normal closure of
   the relators.  Its two halves were already in tree and are
   reused, not rebuilt.

   ** The construction

   [comp_free M := FreeGrpObject (mcar M)] is Instance/Grp/Free.v's free
   group on M's underlying setoid; [comp_rel_word a b] is the word
   [ι(a)·ι(b)·ι(a·b)⁻¹]; [CompletionNS M] is the normal closure of the
   relators and [CompletionObject M] the quotient.

   TWO POINTS ABOUT THE RELATORS.

   First, only ONE family of relators is imposed.  The evident second
   relator [ι(1)] is REDUNDANT, and [comp_class_one] proves it rather
   than assuming it: the multiplicative relator at [a = b = 1] makes the
   class of the unit idempotent, and an idempotent of a GROUP is its
   unit.  (This is the one place where the target being a group, rather
   than a monoid, does work that the presentation does not have to.)

   Second, [Instance/Grp/Quotient/Colimit.v]'s [NormalClosure] closes the
   IMAGE OF A HOMOMORPHISM, not an arbitrary set of elements.  Rather
   than write a second normal-closure inductive, the relators are
   presented AS such an image: [CompRelIdx M] is the setoid of pairs and
   [comp_relator_hom M] is the free group on it mapped into [comp_free M]
   by [free_grp_extend].  So the free group is used TWICE, and
   [NormalClosure] applies verbatim.  The price is one lemma,
   [free_grp_hom_trivial]: a homomorphism out of a free group killing
   every generator is trivial.  It costs no induction on words -- it and
   the constant-unit homomorphism extend the same map, so
   [free_grp_extend_unique] applies twice.

   ** What is reused, and what is built

   Reused with no modification: [FreeGrpObject], [fg_insert],
   [free_grp_extend], [free_grp_extend_generators],
   [free_grp_extend_unique], [free_group_universal_arrow] and
   [free_group_two_generators_nonabelian] (Instance/Grp/Free.v);
   [NormalSubgroup], [QuotientGrp], [quot_proj], [quot_rel_of_equiv],
   [quot_med], [quot_med_unique], [Kills] (Instance/Grp/Quotient.v);
   [InNormalClosure], [NormalClosure], [normal_closure_killed]
   (Instance/Grp/Quotient/Colimit.v); [Grp_MonSets] (GroupRing.v) and
   the element dictionary (MonoidRing.v); [FreeMonSetsObject],
   [free_mon_insert], [free_mon_hom], [free_mon_extend_generator],
   [free_mon_extend_unique] (Instance/Mon/Free.v); [S3] and
   [S3_nonabelian] (Instance/Grp/TwoFunctors.v);
   [universal_arrow_from_UMP], [universal_arrow_iso], [ua_med_commutes],
   [LeftAdjointFunctorFromUniversalArrows],
   [AdjunctionFromUniversalArrows] (Theory/Universal/Arrow.v).

   Built here: the relator index and the relator homomorphism; the
   quotient and its insertion; the extension, its uniqueness and the
   universal property; both encodings of the universal arrow;
   [CompletionFunctor] directly and [CompletionLeft] through the generic
   machinery, with the two related rather than identified;
   [free_grp_hom_trivial] and the two-line [grp_trivial_hom] it needs
   (built locally so that Instance/Grp.v's [Set]-pinned [Grp_Zero] is not
   dragged in -- see the universe section; CORRECTION, #450: [Grp_Zero]
   is no longer [Set]-pinned, #450 having written out its universes in
   Instance/Grp.v, so the local constant is now a choice and not a
   necessity); and the two non-vacuity witnesses.

   ** Riehl's own instance, delivered

   [completion_free_monoid_iso X : CompletionObject (FreeMonSetsObject X)
   ≅[Grp] FreeGrpObject X] -- the completion of a free monoid is the free
   group.  No comparison map is built by hand: both sides are universal
   arrows from X to [Grp_Forget] (note [UMonS ◯ Grp_MonSets] IS
   [Grp_Forget] by CONVERSION, both being [fun H => grp_setoid H]), so
   [universal_arrow_iso] supplies it and [ua_med_commutes] supplies the
   leg equation [completion_free_monoid_iso_gen] that a bare [≅] would
   not carry.

   ** Strengths, measured strict-first

   Strict ([eq_refl], shipped as [Example]s): the class of a generator IS
   the free group's insertion ([completion_class_is_generator]); the
   insertion's action IS that class ([completion_insert_computes]); the
   completion's multiplication IS the free group's
   ([completion_mul_is_free_mul]); both functors' OBJECT actions, and
   their agreement ([completion_functor_obj], [CompletionLeft_obj],
   [completion_functor_obj_agrees]); the universal arrow IS the insertion
   in both encodings ([completion_arrow_is_insert],
   [completion_auniversal_arrow_is_insert]); the mediator IS word
   evaluation ([completion_extend_is_bar]); and the UNIT computes
   ([completion_unit_is_insert]) -- [unit] is DERIVED in
   Theory/Adjunction.v as the transpose of the identity, so this had to
   be checked rather than assumed.

   Not strict.  Three CONVERSION refutations, each pinned as a [Fail]
   probe in the "Measured negatives" section, stripped once and confirmed
   a genuine "cannot unify", each with a positive control:

   - The COUNIT does not compute: it is
   [unique_obj (ump_universal_arrows …)] and
   [ump_universal_arrows] (Theory/Universal/Arrow.v) is [Qed], so
   nothing reduces through it.  What holds is [≈]
   ([completion_counit_evaluates]).  The probe DISCRIMINATES: the
   UNIT at the SAME adjunction closes by [eq_refl].
   - [fmap[CompletionLeft]] does not compute, for the same reason:
   [LeftAdjointFunctorFromUniversalArrows] defines it by universal
   factorization, not by a formula.  That is precisely why
   [CompletionFunctor] is built directly and why
   [completion_fmap_agrees] is [≈]; the control is that the OBJECT
   actions DO agree strictly.
   - The insertion is multiplicative only up to [≈]: the completion is
   a genuine QUOTIENT and the two sides are distinct words of the
   free group, identified by the relator.  [comp_class_op] is the
   [≈] statement, and supplying it is what the whole presentation
   exists for.

   ** Universes: a donor [Set] pin, LOCATED and DISCLOSED

   Measured off the constraint blocks, not read off binders.  No explicit
   universe instance is written on any functor or adjunction here: the
   [Functor] universe arity is not portable across the supported Rocq and
   Coq versions.

   [Grp_MonSets] is instantiable only at [Set]-carrier groups.  This is
   visible in [grp_monoid]'s own signature, which reads
   [∀ G : GrpObject@{Set Set u}, Monoid@{_ Set} G], and it is inherited
   by [Grp_MonSets@{…} : Grp@{u Set} ⟶ MonSets@{Set u}].  The pin is the
   DONOR's, is NOT repaired here, and is NOT claimed unavoidable: the
   "Measured negatives" section ships a positive control showing that the
   TYPE [grp_monoid] inhabits, [@Monoid Sets Sets_Product_Monoidal
   (grp_setoid G)], IS formable at a carrier universe strictly above
   [Set], so the pin is introduced by that DEFINITION (an unannotated
   [Sets], the universe-minimization family the tree records elsewhere)
   and not demanded by its statement.  [mcar], [mop], [mhom] and
   [Sets_Product_Monoidal] were each checked and are all free of it.

   THE BOUNDARY IS MEASURED, not guessed.  The presentation layer is NOT
   pinned: [comp_free], [CompletionObject] and [comp_class_op] all
   elaborate over a monoid whose carrier universe sits strictly above
   [Set] (three positive controls), and it is exactly the first constant
   whose TYPE names [Grp_MonSets] -- [completion_insert] -- that is
   rejected there (formability negative,
   "Cannot enforce Set = uo").  So the ADJUNCTION, the functors and
   everything downstream are statements about [Set]-carrier monoids and
   groups; the presentation, the quotient and their laws are not.

   What the presentation layer DOES carry is an identification of
   [GrpObject]'s three universes with one another
   ([comp_free@{u u0 u1} : obj[MonSets] → GrpObject@{u0 u0 u0}]), and
   that is Instance/Grp/Free.v's doing:
   [FreeGrpObject@{u u0} : SetoidObject@{u u} → GrpObject@{u u u}].
   Nothing here adds to it.  [Set] otherwise occurs in these blocks only
   as a LOWER bound on three STDLIB universes ([Basics.flip.u0/u1/u2]),
   inherited from the free-group layer; a bound is not an identification.

   ** Dependency footprint, measured

   Reusing [Grp_MonSets] rather than rebuilding a forgetful functor costs
   25 modules: the transitive [Require] closure of this file is 109
   modules, against 84 for the same file with the two [Instance/Rng]
   requires removed (the ring/rig/matrix stack that GroupRing.v sits on).
   Recorded because it is a real cost of the reuse, and chosen anyway --
   rebuilding [Grp_MonSets] here would duplicate an existing constant.

   ** Non-vacuity: the completion can be non-abelian

   Proved by mapping OUT into concrete groups, since no induction on a
   quotienting congruence can yield a negative.

   - [completion_can_be_nonabelian]: over [S3Mon := Grp_MonSets S3],
   the classes of the rotation and the reflection do NOT commute.
   The argument extends the identity monoid homomorphism to a group
   homomorphism K(U S3) → S3 and reads off [S3_nonabelian].  Since
   the same retraction is injective on classes
   ([completion_S3_insert_injective]), the completion of a group's
   underlying monoid does not collapse it either, and the two
   generators are distinct ([completion_S3_generators_distinct]).
   - [completion_free_mon_two_nonabelian]: the canonical instance.
   Through [completion_free_monoid_iso] the completion of the free
   monoid on two letters IS the free group on two letters, so
   Instance/Grp/Free.v's [free_group_two_generators_nonabelian]
   transports; it is transported, not reproved.

   Both are witnesses that the construction is not the pairs one in
   disguise -- reason (2) above, discharged by proof.

   ** Axioms

   76/76 constants closed under the global context: 71 source
   declarations plus 5 [Program] obligations, the count taken from
   [Print Module] rather than from the [.glob], which lists only the 71.

   ** NOT delivered

   No normal form for the relator congruence, hence no decision
   procedure for equality in a completion and no word problem; the
   negatives above all go through a concrete group instead.  No
   cancellativity criterion: nothing here says WHEN the insertion is
   injective in general (it is proved injective only when M is already a
   group's underlying monoid, where a retraction is available), and in
   particular no analogue of [Instance/CMon/Grothendieck.v]'s
   [groth_nat_Z_iso] computing a completion in closed form.  No
   comparison with that file: the composite
   [CMon → Mon → Grp] versus [CMon → Ab → Grp] is not built, and no
   statement relates [GrothendieckObject] to [CompletionObject] at a
   commutative monoid -- they agree up to isomorphism there, but the
   abelianization bridge that would prove it is not developed.  No
   functoriality of the relator subgroup in M beyond [CompletionFunctor]
   itself; no naturality clauses of the adjunction restated in the
   completion's own vocabulary; no monadicity, and no idempotency
   statement.  The [Set] pin above is disclosed, not repaired. 

   --------
   * * 单子的群完备作为一个左伴随

   nLab:       https://ncatlab.org/nlab/show/group+completion 
   nLab:       https://ncatlab.org/nlab/show/free+group 
   nLab:       https://ncatlab.org/nlab/show/presentation+of+a+group 
   维基百科:   https://en.wikipedia.org/wiki/Grothendieck_group 

   书籍: Riehl, 《范畴论的背景》(第2版, Dover 2016), §4.1
   例4.1.10 (目录项 [riehl:4.1:example10])，其中
   列出了两种形式的群完备：一个左伴随
   [CMonoid → Ab] 和一个左伴随 [Monoid → Group]。

   [Instance/CMon/Grothendieck.v] 给出了第一种形式。该文件
   提供了第二种形式：对于一个单子 M，存在一个群 K(M) 和一个单子同态 M → U K(M)，通过它，每个从 M 到群的基础单子的单子同态都唯一地由一个群同态分解，组合成
   [completion_adjunction : CompletionLeft ⊣ Grp_MonSets]。

   ** 不是格罗滕迪克构造，也不是对构造[Construction/Grothendieck.v] 构建了一个索引范畴的总范畴；它仅共享一个名称，并且既不是必须的，也没有再次被提及。更重要的是，这个文件没有重用 [Instance/CMon/Grothendieck.v] 的对偶商，而原因是定理而非偏好——见下一节。

   ** 对 [Instance/CMon/Grothendieck.v] 的延迟的两个更正

   该文件给出了不提供第二种形式的三个原因。分别阅读：一个是错误的，一个是正确且决定性的，第三个准确描述了此处采用的路径。(1) 错误。它说说明第二种形式需要“一个不存在的遗忘 [Grp ⟶ Mon]”。它是存在的：[Grp_MonSets : Grp ⟶ MonSets] 在 Instance/Rng/GroupRing.v 中，基于 [MonSets := @Mon Sets Sets_Product_Monoidal]（Instance/Rng/MonoidRing.v）。在集合同构范畴的笛卡尔单体范畴中的一个内部幺半群确实是一个普通的集合同构幺半群，而 Instance/Rng/MonoidRing.v 提供了生成器和关系构造所需要的元素级字典（[mcar]，[mop]，[mone]，[mmap]，[mhom]）。因此，第二种形式是可以说明的，而且这里说明时没有引入新的范畴和新的遗忘函子。（该文件在原因（1）中的其他条款——即 Theory/Algebra/Monoid/Hom.v 的 [Mon] 是内部幺半群的范畴，而 Construction/Deloop.v 的 [MonObject] 不承载任何范畴——是准确的；不成立的是不存在任何忘记函子。）(2) 正确，这就是该文件看起来如此的原因。M×M/~ 的配对构造不可能是这个伴随的。它会为每个输入生成一个阿贝尔群——从定义上讲，其 [ab_neg] 是交换——而 [Group → Monoid] 的左伴随必须生成非阿贝尔群。下面的内容没有重用或改编它，而且文件证明它没有在背后重新构建它：ZWZ24WZZ 展示了一个完成中两个不交换的元素，ZWZ25WZZ 在典型示例中，即两个字母上的自由单子，也展示了这一点。

   (3)那里描述的路径确实是所采用的路径：在 M 的底层集合上生成的自由群，按约束条件的正规闭包进行商。它的两部分已经在树结构中，并被重用，而不是重新构建。** 构造

   [comp_free M := FreeGrpObject (mcar M)] 是 Instance/Grp/Free.v 上 M 的底集合体的自由群；[comp_rel_word a b] 是字 [ι(a)·ι(b)·ι(a·b)⁻¹]；[CompletionNS M] 是关系元的正规闭包，[CompletionObject M] 是商群。

   关于关系元的两点说明。

   首先，只强加了一族关系元。明显的第二个关系元 [ι(1)] 是多余的，[comp_class_one] 是证明它而不是假设它：在 [a = b = 1] 的乘法关系元使单位的等价类成为幂等元，而群中的幂等元就是它的单位。（这是唯一一个目标是群而不是幺半群的地方，在这里群的性质起了作用，而该表述不必要求它。）其次，[Instance/Grp/Quotient/Colimit.v] 的 [NormalClosure] 闭合的是同态的像，而不是任意元素集合。不像写第二个正规闭包归纳，关系子被作为这样的像来呈现：[CompRelIdx M] 是对的集合，[comp_relator_hom M] 是其上的自由群，通过 [free_grp_extend] 映射到 [comp_free M]。因此自由群被使用了两次，并且 [NormalClosure] 可以按原文应用。代价是一个引理 [free_grp_hom_trivial]：从自由群出去消去每个生成元的同态是平凡的。这不需要对字进行归纳——它与常数单位同态扩展同一个映射，因此 [free_grp_extend_unique] 可以使用两次。

   ** 什么被重用，什么被构建未经修改重复使用：[FreeGrpObject]，[fg_insert]，[free_grp_extend]，[free_grp_extend_generators]，[free_grp_extend_unique]，[free_group_universal_arrow] 和 [free_group_two_generators_nonabelian]（Instance/Grp/Free.v）；[NormalSubgroup]，[QuotientGrp]，[quot_proj]，[quot_rel_of_equiv]，[quot_med]，[quot_med_unique]，[Kills]（Instance/Grp/Quotient.v）；[InNormalClosure]，[NormalClosure]，[normal_closure_killed]（Instance/Grp/Quotient/Colimit.v）；[Grp_MonSets]（GroupRing.v）和元素字典（MonoidRing.v）；[FreeMonSetsObject]，[free_mon_insert]，[free_mon_hom]，[free_mon_extend_generator]，[free_mon_extend_unique]（Instance/Mon/Free.v）；[S3] 和 [S3_nonabelian]（Instance/Grp/TwoFunctors.v）；[universal_arrow_from_UMP]，[universal_arrow_iso]，[ua_med_commutes]，[LeftAdjointFunctorFromUniversalArrows]，[AdjunctionFromUniversalArrows]（Theory/Universal/Arrow.v）。在这里构建：关系子索引和关系同态；商及其插入；扩展，其唯一性及其普遍性；普遍箭头的两种编码；[CompletionFunctor] 直接方式和 [CompletionLeft] 通过通用机制的方式，两者相互关联而非相同；[free_grp_hom_trivial] 及其所需的两行 [grp_trivial_hom]（局部构建，因此 Instance/Grp.v 的 [Set] 锁定的 [Grp_Zero] 不会被拖入——参见宇宙部分；更正，#450：[Grp_Zero] 不再是 [Set] 锁定，#450 已在 Instance/Grp.v 中展开其宇宙，因此局部常量现在是可选而非必要）；以及两个非空性证人。

   ** Riehl 本人的实例，已交付[completion_free_monoid_iso X : CompletionObject (FreeMonSetsObject X) ≅ [Grp]  FreeGrpObject X] -- 自由幺半群的完备化是自由群。没有手工构建比较映射：双方都是从 X 到 [Grp_Forget] 的通用箭头（注意 [UMonS ◯ Grp_MonSets] 是通过转换得到的 [Grp_Forget]，两者都是 [fun H => grp_setoid H]），所以 [universal_arrow_iso] 提供它，而 [ua_med_commutes] 提供腿方程 [completion_free_monoid_iso_gen]，这是一个普通的 [≅] 所不具备的。

   ** 优点，测量严格优先严格（[eq_refl]，作为[Example]发送）：生成元的类是自由群的插入（[completion_class_is_generator]）；插入的作用是该类（[completion_insert_computes]）；完备的乘法是自由群的（[completion_mul_is_free_mul]）；两个函子对对象的作用，以及它们的一致性（[completion_functor_obj]、[CompletionLeft_obj]、[completion_functor_obj_agrees]）；在两种编码中，通用箭头是插入（[completion_arrow_is_insert]、[completion_auniversal_arrow_is_insert]）；调解器是字词求值（[completion_extend_is_bar]）；并且单位计算（[completion_unit_is_insert]）——[unit] 在 Theory/Adjunction.v 中被推导为恒等的转置，因此必须检查而不能假设。不严格。三个转换反驳，每个都标记为“测量阴性”部分的 [Fail] 探针，剥离一次并确认为真正的“无法统一”，每个都有一个阳性对照：- COUNIT 无法计算：它是 [unique_obj (ump_universal_arrows …)] 并且 [ump_universal_arrows]（Theory/Universal/Arrow.v）是 [Qed]，因此没有任何东西可以通过它进行化简。成立的是 [≈]（[completion_counit_evaluates]）。探针可以区分：在相同附加下的 UNIT 通过 [eq_refl] 关闭。 - [fmap[CompletionLeft]] 无法计算，原因相同：[LeftAdjointFunctorFromUniversalArrows] 通过通用分解定义它，而不是通过公式。这正是 [CompletionFunctor] 被直接构建的原因，以及 [completion_fmap_agrees] 是 [≈] 的原因；控制点是 OBJECT 的动作严格一致。 - 插入仅在 [≈] 上是乘法性的：完成是一个真正的商，并且两边是自由群中不同的词，由重整子标识。[comp_class_op] 是 [≈] 声明，提供它就是整个演示存在的意义。

   ** 宇宙：一个提供的 [Set] 引脚，已定位并披露

   根据约束块测量，而不是从活页夹读取。这里没有在任何函子或伴随上写明显式宇宙实例：[Functor] 宇宙元数在支持的 Rocq 和 Coq 版本之间不可移植。[Grp_MonSets] 只能在 [Set] 载体群组中实例化。这在 [grp_monoid] 自身的签名中可见，其内容为 [∀ G : GrpObject@{Set Set u}, Monoid@{_ Set} G]，并且被 [Grp_MonSets@{…} : Grp@{u Set} ⟶ MonSets@{Set u}] 继承。该引脚属于 DONOR，在这里没有修复，也不被声明为不可避免：“测量的负值”部分提供了一个阳性对照，显示 TYPE [grp_monoid] 所在的 [@Monoid Sets Sets_Product_Monoidal (grp_setoid G)]，可以在严格高于 [Set] 的载体宇宙中形成，因此该引脚是由那个定义引入的（一个未标注的 [Sets]，树的其他地方记录的宇宙最小化系列），而不是由其声明所要求的。[mcar]、[mop]、[mhom] 和 [Sets_Product_Monoidal] 都已检查，且都不含该问题。边界是测量的，而不是猜测的。表示层没有固定：[comp_free]、[CompletionObject] 和 [comp_class_op] 都在一个载体宇宙严格位于 [Set]（三个正控制）之上的幺半群上进行展开，并且正是第一个类型名称为 [Grp_MonSets] -- [completion_insert] 的常量在此被拒绝（可形成性为负，"无法强制 Set = uo"）。因此，伴随、函子及其下游的一切都是关于 [Set]-载体幺半群和群的陈述；表示、商及其定律则不是。演示层确实携带的是对 [GrpObject] 的三个宇宙之间相互关系的识别 ([comp_free@{u u0 u1} : obj[MonSets] → GrpObject@{u0 u0 u0}])，这是 Instance/Grp/Free.v 的工作：[FreeGrpObject@{u u0} : SetoidObject@{u u} → GrpObject@{u u u}]。这里没有任何内容会增加它。[Set] 否则仅在这些模块中出现，作为三个 STDLIB 宇宙 ([Basics.flip.u0/u1/u2]) 的下界，这些下界继承自自由群层；下界并不是一个识别。

   ** 依赖性足迹，测量重用 [Grp_MonSets] 而不是重建一个遗忘函子会花费 25 个模块：该文件的传递闭包 [Require] 是 109 个模块，而同一个文件在移除两个 [Instance/Rng] 需求后为 84 个模块（GroupRing.v 所依赖的环/半环/矩阵堆）。记录下来是因为这确实是重用的成本，而且无论如何都是选择的——在这里重建 [Grp_MonSets] 会重复已有的常量。

   ** 非空性：完成体可以是非阿贝尔的

   通过将 OUT 映射到具体群来证明，因为对商同余类的归纳不能得出负结论。- [completion_can_be_nonabelian]：超过 [S3Mon := Grp_MonSets S3]，旋转类和反射类不交换。这个论证将单位幺半群同态扩展到群同态 K(U S3) → S3，并读取 [S3_nonabelian]。由于相同的收缩在类上是单射的（[completion_S3_insert_injective]），群的底层幺半群的完备化也不会使其塌缩，并且两个生成元是不同的（[completion_S3_generators_distinct]）。
   - [completion_free_mon_two_nonabelian]：规范实例。通过 [completion_free_monoid_iso]，对两个字母的自由幺半群的完备化确实是两个字母的自由群，因此 Instance/Grp/Free.v 的 [free_group_two_generators_nonabelian] 可以进行迁移；它被迁移，而不是重新证明。两者都是证据，表明该构造并非上述成对构造的伪装——理由（2）已通过证据解除。

   ** 公理

   76/76 常量在全局上下文下封闭：71 个源声明加上 5 个 [Program] 义务，计数取自 [Print Module] 而非 [.glob] ，后者仅列出 71 个。

   ** 未交付对于关系子同余没有标准形式，因此在一个完备结构中没有判定相等的过程，也没有字问题；上述所有负面结果都是通过一个具体的群来实现的。没有可消性判据：这里没有说明在一般情况下何时插入是单射的（仅在 M 已经是一个群的底层幺半群且存在重traction时才证明了单射），特别地没有 [Instance/CMon/Grothendieck.v] 的类似方案 [groth_nat_Z_iso] 来以闭合形式计算完备结构。没有与该文件的比较：复合 [CMon → Mon → Grp] 与 [CMon → Ab → Grp] 未建立，也没有声明将 [GrothendieckObject] 与 [CompletionObject] 在交换幺半群中关联——在该情况下它们在同构意义下是相同的，但证明这一点的阿贝尔化桥尚未建立。在 M 中除了 [CompletionFunctor] 本身之外，关系子群没有函子性；在完备体自身的词汇中没有重申伴随的自然性条款；没有单子性，也没有幂等性声明。上述 [Set] 引脚是被披露的，而不是被修复的。
*)

(* * ** A trivial homomorphism, and rigidity of free groups / * ** 一个平凡同态，以及自由群的刚性 *)

Definition grp_trivial_hom (G H : GrpObject) : G ~{Grp}~> H :=
  @Build_GrpHom' G H
    {| morphism        := fun _ : carrier G => grp_unit H
     ; proper_morphism := fun a b (_ : a ≈ b) => reflexivity (grp_unit H) |}
    (fun a b => symmetry (grp_mul_unit_l H (grp_unit H))).

Definition grp_unit_map (X : SetoidObject) (H : GrpObject)
  : X ~{Sets}~> Grp_Forget H :=
  {| morphism        := fun _ : carrier X => grp_unit H
   ; proper_morphism := fun a b (_ : a ≈ b) => reflexivity (grp_unit H) |}.

(*
 A homomorphism out of a free group that kills every generator is
 trivial.  No induction on words: both it and the constant-unit
 homomorphism extend the same map, so [free_grp_extend_unique] applies
 twice. 

 --------
 一个将自由群中每个生成元都映为零的同态是平凡的。不要对字进行归纳：它和恒等单位同态扩展的是同一个映射，所以 [free_grp_extend_unique] 可以应用两次。
*)
Lemma free_grp_hom_trivial {X : SetoidObject} {H : GrpObject}
  (g : FreeGrpObject X ~{Grp}~> H)
  (Hg : ∀ a : carrier X, grp_map g (fg_insert X a) ≈ grp_unit H)
  (w : FGWord X) : grp_map g w ≈ grp_unit H.
Proof.
  transitivity (grp_map (free_grp_extend (grp_unit_map X H)) w).
  - exact (free_grp_extend_unique X H (grp_unit_map X H) g Hg w).
  - symmetry.
    exact (free_grp_extend_unique X H (grp_unit_map X H)
             (grp_trivial_hom (FreeGrpObject X) H)
             (fun a => reflexivity (grp_unit H)) w).
Qed.

(** ** The presentation / ** 演示 *)

Section Completion.

Context (M : MonSets).

(* The free group on the underlying setoid of M. / 在 M 的基础集合等价类上的自由群。 *)
Definition comp_free : GrpObject := FreeGrpObject (mcar M).

Definition comp_gen (a : carrier (mcar M)) : carrier comp_free :=
  fg_insert (mcar M) a.

#[local] Instance comp_gen_respects : Proper (equiv ==> equiv) comp_gen :=
  proper_morphism (fg_insert (mcar M)).

#[local] Instance comp_mop_respects
  : Proper (equiv ==> equiv ==> equiv) (mop M) := mop_respects M.

(*
 The relator word attached to a pair: what must become trivial for the
 insertion to be multiplicative. 

 --------
 附加到一对的连接词：为了使插入具有乘法性，什么必须变得琐碎。
*)
Definition comp_rel_word (a b : carrier (mcar M)) : carrier comp_free :=
  grp_mul comp_free (grp_mul comp_free (comp_gen a) (comp_gen b))
    (grp_inv comp_free (comp_gen (mop M a b))).

Lemma comp_rel_word_respects (a a' b b' : carrier (mcar M)) :
  a ≈ a' → b ≈ b' → comp_rel_word a b ≈ comp_rel_word a' b'.
Proof.
  intros Ha Hb; unfold comp_rel_word.
  now rewrite Ha, Hb.
Qed.

(* The relator index: a pair of elements of M, compared componentwise. / 关系索引：M 的一对元素，按分量进行比较。 *)
Program Definition CompRelSetoid
  : Setoid (carrier (mcar M) * carrier (mcar M)) := {|
  equiv := fun p q => (fst p ≈ fst q) * (snd p ≈ snd q)
|}.
Next Obligation.
  constructor.
  - intros [a b]; split; reflexivity.
  - intros [a b] [c d] [H1 H2]; split; symmetry; assumption.
  - intros [a b] [c d] [e f] [H1 H2] [H3 H4]; split;
      [ transitivity c | transitivity d ]; assumption.
Qed.

Definition CompRelIdx : SetoidObject :=
  {| carrier := carrier (mcar M) * carrier (mcar M)
   ; is_setoid := CompRelSetoid |}.

Definition comp_relator (p : carrier CompRelIdx) : carrier comp_free :=
  comp_rel_word (fst p) (snd p).

Definition comp_relator_map : CompRelIdx ~{Sets}~> Grp_Forget comp_free :=
  {| morphism        := comp_relator
   ; proper_morphism := fun p q H =>
       comp_rel_word_respects (fst p) (fst q) (snd p) (snd q)
         (fst H) (snd H) |}.

(* Read as a homomorphism out of the free group on the relator index, so that [NormalClosure] -- which closes the IMAGE of a homomorphism -- applies verbatim. / 将其读作自由群上关于关系元索引的同态，因此 [NormalClosure] —— 它封闭了同态的像 —— 可以逐字应用。 *)
Definition comp_relator_hom : FreeGrpObject CompRelIdx ~{Grp}~> comp_free :=
  free_grp_extend comp_relator_map.

Definition CompletionNS : NormalSubgroup comp_free :=
  NormalClosure comp_relator_hom.

Definition CompletionObject : GrpObject := QuotientGrp CompletionNS.

Definition comp_class (a : carrier (mcar M)) : carrier CompletionObject :=
  comp_gen a.

(*
 Two conversion helpers.  An earlier revision said "both bodies are the
 corresponding [quot_rel] fact verbatim: `≈` at [CompletionObject] IS
 [quot_rel CompletionNS], so no proof step intervenes".  Since the PR
 "algebraic carriers are sets" (2026-09-17) the quotient's `≈` is the
 PROPOSITIONAL TRUNCATION of [quot_rel CompletionNS], so each body is that
 same fact under one [inhabits] -- still no mathematical step. 

 --------
 两个转换助手。早期的修订版本说“两个主体都是相应的 [quot_rel] 事实逐字：`≈` 在 [CompletionObject] 是 [quot_rel CompletionNS]，因此没有证明步骤介入”。自从 PR “代数载体是集合”（2026-09-17）之后，商的 `≈` 是 [quot_rel CompletionNS] 的命题截断，因此每个主体在一个 [inhabits] 下都是相同的事实——仍然没有数学步骤。
*)
Lemma comp_quot_of_equiv (x y : carrier comp_free) :
  x ≈ y → (x : carrier CompletionObject) ≈ y.
Proof. exact (fun H => inhabits (quot_rel_of_equiv CompletionNS x y H)). Qed.

Lemma comp_quot_of_mem (x y : carrier comp_free) :
  sub_mem CompletionNS (grp_mul comp_free x (grp_inv comp_free y)) →
  (x : carrier CompletionObject) ≈ y.
Proof. exact (fun H => inhabits H). Qed.

(* Every relator lies in the normal closure. / 每个关系词都包含在正规闭包中。 *)
Lemma comp_relator_mem (p : carrier CompRelIdx) :
  sub_mem CompletionNS (comp_relator p).
Proof.
  exact (nc_resp
           (free_grp_extend_generators CompRelIdx comp_free
              comp_relator_map p)
           (nc_gen (fg_insert CompRelIdx p))).
Qed.

Lemma comp_class_respects (a b : carrier (mcar M)) :
  a ≈ b → comp_class a ≈ comp_class b.
Proof. intro Hab; apply comp_quot_of_equiv; now rewrite Hab. Qed.

(* The insertion is multiplicative: this is exactly the relator, inverted. / 插入是乘法性的：这正是关系子，只是颠倒过来。 *)
Lemma comp_class_op (a b : carrier (mcar M)) :
  comp_class (mop M a b)
    ≈ grp_mul CompletionObject (comp_class a) (comp_class b).
Proof.
  apply comp_quot_of_mem.
  apply (sub_at CompletionNS
           (a := grp_inv comp_free (comp_rel_word a b))).
  - unfold comp_rel_word.
    rewrite grp_inv_mul, grp_inv_inv.
    reflexivity.
  - exact (sub_inv CompletionNS _ (comp_relator_mem (a, b))).
Qed.

(*
 ...and unital, which is a CONSEQUENCE rather than a second relator: an
 idempotent of a group is its unit. 

 --------
 ...并且是幺元的，这是一个结果而不是第二个关系元：群的幂等元就是它的单位元。
*)
Lemma comp_class_one : comp_class (mone M) ≈ grp_unit CompletionObject.
Proof.
  assert (Hu : grp_mul CompletionObject
                 (comp_class (mone M)) (comp_class (mone M))
                 ≈ comp_class (mone M)).
  { transitivity (comp_class (mop M (mone M) (mone M))).
    - symmetry; apply comp_class_op.
    - apply comp_class_respects, mop_one_l. }
  apply (grp_cancel_r CompletionObject (comp_class (mone M))).
  rewrite grp_mul_unit_l.
  exact Hu.
Qed.

End Completion.

Arguments comp_free M : clear implicits.
Arguments CompletionObject M : clear implicits.

(*
 The insertion, as a morphism of [MonSets].  It is declared OUTSIDE the
 section above deliberately: [Grp_MonSets] is instantiable only at
 [Set]-carrier groups (see the header), and a section variable
 [M : MonSets] has its universes fixed before that constraint can be
 imposed, so naming [Grp_MonSets] inside the section is a universe
 inconsistency.  Outside it, each definition is generalized on its own
 and the instantiation goes through. 

 --------
 作为 [MonSets] 的一个态射的插入。它被有意地声明在上述部分之外：[Grp_MonSets] 只能在 [Set] 载体群上实例化（参见头文件），而一个部分变量 [M : MonSets] 在施加该约束之前已经固定了它的宇宙，因此在部分内部命名 [Grp_MonSets] 会导致宇宙不一致。在部分之外，每个定义都会自行泛化，并且实例化可以进行。
*)
Definition completion_insert (M : MonSets)
  : M ~{MonSets}~> Grp_MonSets (CompletionObject M) :=
  @mhom M (Grp_MonSets (CompletionObject M))
    (comp_class M) (comp_class_respects M) (comp_class_op M)
    (comp_class_one M).

(* * ** The extension of a monoid homomorphism into a group / * ** 将幺半群同态扩展到群 *)

Section Extend.

Context (M : MonSets) (H : Grp) (h : M ~{MonSets}~> Grp_MonSets H).

Definition comp_target_map : mcar M ~{Sets}~> Grp_Forget H := `1 h.

(*
 The word evaluation.  It is the free group's own extension of the
 underlying setoid map of [h]; the monoid structure of [M] is not
 consulted here at all -- it enters only in [comp_bar_relator]. 

 --------
 单词“evaluation”。它是自由群自身对 [h] 基础集合图的扩展；这里完全没有使用 [M] 的幺半群结构——它仅在 [comp_bar_relator] 中出现。
*)
Definition comp_bar : comp_free M ~{Grp}~> H :=
  free_grp_extend comp_target_map.

Lemma comp_bar_gen (a : carrier (mcar M)) :
  grp_map comp_bar (comp_gen M a) ≈ mmap h a.
Proof. exact (free_grp_extend_generators (mcar M) H comp_target_map a). Qed.

(* [h] being multiplicative is exactly what kills the relators. / [h] 是乘法性的正是消除关系子的原因。 *)
Lemma comp_bar_relator (a b : carrier (mcar M)) :
  grp_map comp_bar (comp_rel_word M a b) ≈ grp_unit H.
Proof.
  unfold comp_rel_word.
  rewrite (grp_map_mul comp_bar), (grp_map_mul comp_bar),
    (grp_map_inv comp_bar), !comp_bar_gen.
  rewrite (mmap_op h a b).
  apply grp_mul_inv_r.
Qed.

Lemma comp_bar_kills (x : carrier (comp_free M)) :
  sub_mem (CompletionNS M) x → grp_map comp_bar x ≈ grp_unit H.
Proof.
  apply (normal_closure_killed (comp_relator_hom M) comp_bar).
  intro w.
  refine (free_grp_hom_trivial (comp_bar ∘ comp_relator_hom M) _ w).
  intro p.
  transitivity (grp_map comp_bar (comp_relator M p)).
  - exact (proper_morphism (grp_map comp_bar) _ _
             (free_grp_extend_generators (CompRelIdx M) (comp_free M)
                (comp_relator_map M) p)).
  - exact (comp_bar_relator (fst p) (snd p)).
Qed.

Definition comp_kills : Kills (CompletionNS M) H :=
  existT _ comp_bar comp_bar_kills.

Definition completion_extend : CompletionObject M ~{Grp}~> H :=
  quot_med (CompletionNS M) comp_kills.

Lemma completion_extend_gen (a : carrier (mcar M)) :
  grp_map completion_extend (comp_class M a) ≈ mmap h a.
Proof. exact (comp_bar_gen a). Qed.

Lemma completion_extend_unique (g : CompletionObject M ~{Grp}~> H)
  (Hg : ∀ a : carrier (mcar M), grp_map g (comp_class M a) ≈ mmap h a) :
  g ≈ completion_extend.
Proof.
  symmetry.
  apply (quot_med_unique (CompletionNS M) comp_kills g).
  intro w.
  exact (free_grp_extend_unique (mcar M) H comp_target_map
           (g ∘ quot_proj (CompletionNS M)) Hg w).
Qed.

End Extend.

Arguments comp_bar {M H} h.
Arguments completion_extend {M H} h.
Arguments completion_extend_gen {M H} h a.
Arguments completion_extend_unique {M H} h g Hg.

(** ** The universal property / ** 通用性质 *)

Theorem completion_universal (M : MonSets) :
  ∀ (H : Grp) (h : M ~{MonSets}~> Grp_MonSets H),
    ∃! g : CompletionObject M ~{Grp}~> H,
      h ≈ fmap[Grp_MonSets] g ∘ completion_insert M.
Proof.
  intros H h.
  unshelve eexists.
  - exact (completion_extend h).
  - intro a.
    symmetry; exact (completion_extend_gen h a).
  - intros g Hg.
    symmetry.
    exact (completion_extend_unique h g (fun a => symmetry (Hg a))).
Qed.

(* * ** The universal arrow, in both encodings / * ** 通用箭头，在两种编码中 *)

Definition completion_universal_arrow (M : MonSets)
  : UniversalArrow M Grp_MonSets :=
  universal_arrow_from_UMP M Grp_MonSets (CompletionObject M)
    (completion_insert M) (completion_universal M).

Program Definition completion_AUniversalArrow (M : MonSets)
  : AUniversalArrow M Grp_MonSets (CompletionObject M) := {|
  universal_arrow := completion_insert M
|}.
Next Obligation.
  intros M H h.
  unshelve eexists.
  - exact (completion_extend h).
  - intro a.
    exact (completion_extend_gen h a).
  - intros g Hg.
    symmetry.
    exact (completion_extend_unique h g Hg).
Qed.

(* * ** The completion functor, built directly / * ** 完成函子，直接构建 *)

Program Definition CompletionFunctor : MonSets ⟶ Grp := {|
  fobj := CompletionObject;
  fmap := fun X Y f => completion_extend (completion_insert Y ∘ f)
|}.
Next Obligation.
  intros X Y f g Hfg.
  symmetry.
  apply completion_extend_unique.
  intro a.
  transitivity (comp_class Y (mmap g a)).
  - exact (completion_extend_gen (completion_insert Y ∘ g) a).
  - exact (comp_class_respects Y _ _ (symmetry (Hfg a))).
Qed.
Next Obligation.
  intros X.
  symmetry.
  apply completion_extend_unique.
  intro a; reflexivity.
Qed.
Next Obligation.
  intros X Y Z f g.
  symmetry.
  apply completion_extend_unique.
  intro a.
  transitivity (grp_map (completion_extend (completion_insert Z ∘ f))
                  (comp_class Y (mmap g a))).
  - exact (proper_morphism
             (grp_map (completion_extend (completion_insert Z ∘ f))) _ _
             (completion_extend_gen (completion_insert Y ∘ g) a)).
  - exact (completion_extend_gen (completion_insert Z ∘ f) (mmap g a)).
Qed.

(** ** The adjunction / ** 结合 *)

Definition CompletionLeft : MonSets ⟶ Grp :=
  LeftAdjointFunctorFromUniversalArrows Grp_MonSets completion_universal_arrow.

Definition completion_adjunction : CompletionLeft ⊣ Grp_MonSets :=
  AdjunctionFromUniversalArrows Grp_MonSets completion_universal_arrow.

(* * ** Strengths, measured strict-first / * ** 优点，严格优先测量 *)

Example completion_class_is_generator (M : MonSets) (a : carrier (mcar M)) :
  comp_class M a = fg_insert (mcar M) a := eq_refl.

Example completion_insert_computes (M : MonSets) (a : carrier (mcar M)) :
  mmap (completion_insert M) a = comp_class M a := eq_refl.

Example completion_mul_is_free_mul (M : MonSets) :
  grp_mul (CompletionObject M) = grp_mul (comp_free M) := eq_refl.

Example completion_functor_obj (M : MonSets) :
  fobj[CompletionFunctor] M = CompletionObject M := eq_refl.

Example CompletionLeft_obj (M : MonSets) :
  CompletionLeft M = CompletionObject M := eq_refl.

Example completion_functor_obj_agrees (M : MonSets) :
  fobj[CompletionFunctor] M = CompletionLeft M := eq_refl.

Example completion_arrow_is_insert (M : MonSets) :
  @arrow _ _ M Grp_MonSets (completion_universal_arrow M)
    = completion_insert M := eq_refl.

Example completion_auniversal_arrow_is_insert (M : MonSets) :
  @universal_arrow _ _ M Grp_MonSets (CompletionObject M)
    (completion_AUniversalArrow M) = completion_insert M := eq_refl.

Example completion_extend_is_bar (M : MonSets) (H : Grp)
  (h : M ~{MonSets}~> Grp_MonSets H) (x : carrier (comp_free M)) :
  grp_map (completion_extend h) x = grp_map (comp_bar h) x := eq_refl.

Definition completion_unit (M : MonSets)
  : M ~{MonSets}~> Grp_MonSets (CompletionLeft M) :=
  @Category.Theory.Adjunction.unit _ _ _ _ completion_adjunction M.

Example completion_unit_is_insert (M : MonSets) (a : carrier (mcar M)) :
  mmap (completion_unit M) a = comp_class M a := eq_refl.

(* * ** The counit evaluates a word, and the triangle identities / * ** 协同单位评估一个词，以及三角恒等式 *)

Definition completion_counit (H : Grp)
  : CompletionLeft (Grp_MonSets H) ~{Grp}~> H :=
  @Category.Theory.Adjunction.counit _ _ _ _ completion_adjunction H.

Lemma completion_counit_class (H : Grp) (a : carrier (grp_setoid H)) :
  grp_map (completion_counit H) (comp_class (Grp_MonSets H) a) ≈ a.
Proof. exact (@to_adj_counit _ _ _ _ completion_adjunction H a). Qed.

Theorem completion_counit_evaluates (H : Grp)
  (x : carrier (CompletionObject (Grp_MonSets H))) :
  grp_map (completion_counit H) x
    ≈ grp_map (completion_extend (@id MonSets (Grp_MonSets H))) x.
Proof.
  exact (completion_extend_unique (@id MonSets (Grp_MonSets H))
           (completion_counit H) (completion_counit_class H) x).
Qed.

Corollary completion_triangle_left (M : MonSets) :
  completion_counit (CompletionLeft M)
    ∘ fmap[CompletionLeft] (completion_unit M)
    ≈ @id Grp (CompletionLeft M).
Proof. exact (@counit_fmap_unit _ _ _ _ completion_adjunction M). Qed.

Corollary completion_triangle_right (H : Grp) :
  fmap[Grp_MonSets] (completion_counit H) ∘ completion_unit (Grp_MonSets H)
    ≈ @id MonSets (Grp_MonSets H).
Proof. exact (@fmap_counit_unit _ _ _ _ completion_adjunction H). Qed.

(** ** The two left functors agree / ** 两个左函子一致 *)

Theorem completion_fmap_agrees {X Y : MonSets} (f : X ~{MonSets}~> Y) :
  fmap[CompletionLeft] f ≈ fmap[CompletionFunctor] f.
Proof.
  apply (uniqueness (ump_universal_arrows (completion_universal_arrow X)
                       (completion_insert Y ∘ f))).
  intro a.
  symmetry.
  exact (completion_extend_gen (completion_insert Y ∘ f) a).
Qed.

(* * ** Non-vacuity: the completion can be non-abelian / * ** 非空性：完成可以是非交换的 *)

Definition S3Mon : MonSets := Grp_MonSets S3.

Definition comp_S3 : GrpObject := CompletionObject S3Mon.

Definition comp_S3_down : comp_S3 ~{Grp}~> S3 :=
  completion_extend (@id MonSets S3Mon).

Definition comp_S3_r : carrier comp_S3 := comp_class S3Mon S3_r.
Definition comp_S3_s : carrier comp_S3 := comp_class S3Mon S3_s.

Lemma comp_S3_down_class (a : carrier S3) :
  grp_map comp_S3_down (comp_class S3Mon a) ≈ a.
Proof. exact (completion_extend_gen (@id MonSets S3Mon) a). Qed.

(*
 The insertion of a GROUP's underlying monoid is injective, because the
 completion retracts onto it. 

 --------
 一个群的基础幺半群的插入是单射的，因为完备性会收缩到它上面。
*)
Theorem completion_S3_insert_injective (a b : carrier S3) :
  comp_class S3Mon a ≈ comp_class S3Mon b → a ≈ b.
Proof.
  intro Hab.
  transitivity (grp_map comp_S3_down (comp_class S3Mon a)).
  - symmetry; exact (comp_S3_down_class a).
  - transitivity (grp_map comp_S3_down (comp_class S3Mon b)).
    + exact (proper_morphism (grp_map comp_S3_down) _ _ Hab).
    + exact (comp_S3_down_class b).
Qed.

Theorem completion_can_be_nonabelian :
  grp_mul comp_S3 comp_S3_r comp_S3_s ≈ grp_mul comp_S3 comp_S3_s comp_S3_r
    → False.
Proof.
  intro Hcomm.
  apply S3_nonabelian.
  transitivity (grp_map comp_S3_down (grp_mul comp_S3 comp_S3_r comp_S3_s)).
  - rewrite (grp_map_mul comp_S3_down).
    unfold comp_S3_r, comp_S3_s.
    now rewrite !comp_S3_down_class.
  - rewrite Hcomm, (grp_map_mul comp_S3_down).
    unfold comp_S3_r, comp_S3_s.
    now rewrite !comp_S3_down_class.
Qed.

Theorem completion_S3_generators_distinct : comp_S3_r ≈ comp_S3_s → False.
Proof.
  intro H.
  pose proof (completion_S3_insert_injective S3_r S3_s H) as E.
  discriminate E.
Qed.

(*
   * ** The completion of a free monoid is the free group

   Riehl's own headline instance, and the one
   [Instance/CMon/Grothendieck.v]'s reason (2) argues from: the group
   completion of the free monoid on X is the free group on X.  Both are
   universal arrows from X to [Grp_Forget] -- note [UMonS ∘ Grp_MonSets]
   IS [Grp_Forget] by conversion, both being [fun H => grp_setoid H] --
   so [universal_arrow_iso] supplies the comparison and nothing is
   constructed by hand. 

   --------
   * ** 自由幺半群的完备是自由群

   Riehl 自己的标题实例，以及 [Instance/CMon/Grothendieck.v] 的理由 (2) 所论证的例子：自由幺半群关于 X 的群完备是 X 上的自由群。两者都是从 X 到 [Grp_Forget] 的通用箭头——注意 [UMonS ∘ Grp_MonSets] 通过转换等于 [Grp_Forget]，二者都是 [fun H => grp_setoid H]——因此 [universal_arrow_iso] 提供了比较，没有任何东西是手工构建的。
*)

Definition comp_free_mon_insert (X : Sets)
  : X ~{Sets}~> Grp_Forget (CompletionObject (FreeMonSetsObject X)) :=
  `1 (completion_insert (FreeMonSetsObject X)) ∘ free_mon_insert X.

Theorem comp_free_mon_universal (X : Sets) :
  ∀ (H : Grp) (k : X ~{Sets}~> Grp_Forget H),
    ∃! g : CompletionObject (FreeMonSetsObject X) ~{Grp}~> H,
      k ≈ fmap[Grp_Forget] g ∘ comp_free_mon_insert X.
Proof.
  intros H k.
  pose (km := @free_mon_hom X (Grp_MonSets H) k (proper_morphism k)).
  unshelve eexists.
  - exact (completion_extend km).
  - intro a.
    symmetry.
    transitivity (mmap km (free_mon_insert X a)).
    + exact (completion_extend_gen km (free_mon_insert X a)).
    + exact (@free_mon_extend_generator X (Grp_MonSets H) k a).
  - intros g Hg.
    symmetry.
    apply (completion_extend_unique km g).
    intro w.
    exact (@free_mon_extend_unique X (Grp_MonSets H) k
             (fmap[Grp_MonSets] g ∘ completion_insert (FreeMonSetsObject X))
             (fun a => symmetry (Hg a)) w).
Qed.

Definition comp_free_mon_universal_arrow (X : Sets)
  : UniversalArrow X Grp_Forget :=
  universal_arrow_from_UMP X Grp_Forget
    (CompletionObject (FreeMonSetsObject X)) (comp_free_mon_insert X)
    (comp_free_mon_universal X).

Definition completion_free_monoid_iso (X : Sets)
  : CompletionObject (FreeMonSetsObject X) ≅[Grp] FreeGrpObject X :=
  @universal_arrow_iso Sets Grp X Grp_Forget
    (comp_free_mon_universal_arrow X) (free_group_universal_arrow X).

(* The comparison carries the class of a one-letter word to the corresponding free generator -- the leg equation a bare [≅] would not carry. / 该比较赋予与相应自由生成元相关联的一字类——一个单独的 [≅] 等式本身是不会赋予的。 *)
Lemma completion_free_monoid_iso_gen (X : Sets) (a : carrier X) :
  grp_map (to (completion_free_monoid_iso X))
    (comp_class (FreeMonSetsObject X) (free_mon_insert X a))
    ≈ fg_insert X a.
Proof.
  exact (ua_med_commutes (comp_free_mon_universal_arrow X)
           (free_group_universal_arrow X) a).
Qed.

(* Hence the canonical non-abelian instance, transported from [Instance/Grp/Free.v]'s witness rather than reproved. / 因此，这是典型的非阿贝尔实例，是从[Instance/Grp/Free.v]的证据中传递过来的，而不是重新证明的。 *)
Theorem completion_free_mon_two_nonabelian :
  grp_mul (CompletionObject (FreeMonSetsObject TwoLetters))
    (comp_class (FreeMonSetsObject TwoLetters)
       (free_mon_insert TwoLetters true))
    (comp_class (FreeMonSetsObject TwoLetters)
       (free_mon_insert TwoLetters false))
  ≈ grp_mul (CompletionObject (FreeMonSetsObject TwoLetters))
      (comp_class (FreeMonSetsObject TwoLetters)
         (free_mon_insert TwoLetters false))
      (comp_class (FreeMonSetsObject TwoLetters)
         (free_mon_insert TwoLetters true))
    → False.
Proof.
  intro Hcomm.
  apply free_group_two_generators_nonabelian.
  pose proof (proper_morphism
                (grp_map (to (completion_free_monoid_iso TwoLetters)))
                _ _ Hcomm) as Hi.
  rewrite !(grp_map_mul (to (completion_free_monoid_iso TwoLetters))) in Hi.
  rewrite !completion_free_monoid_iso_gen in Hi.
  exact Hi.
Qed.

(*
   * ** Measured negatives

   Each [Fail] below was stripped once and its failure KIND read off the
   error message, and each is paired with a positive control that must
   succeed.  Three are CONVERSION failures ("cannot unify") and three are
   FORMABILITY failures (universe inconsistencies naming the declared
   level); they are kept lexically apart. 

   --------
   * ** 测量的负面情况

   下面的每个 [Fail] 都只被剥离过一次，并从错误信息中读取其失败类型（KIND），每个都与必须成功的阳性对照配对。三个是转换失败（"无法统一"），三个是可形成性失败（命名声明等级的宇宙不一致）；它们在词汇上保持分开。
*)

(*
 Instrument check: the mechanism reports a genuine failure on a
 scope-free proposition. 

 --------
 仪器检查：该机制报告在无范围命题上的真实故障。
*)
Fail Definition completion_probe_instrument : true = false := eq_refl.

(** *** Conversion negatives / *** 转换负面 *)

(*
 (1) The COUNIT does not compute.  It is
 [unique_obj (ump_universal_arrows …)] and [ump_universal_arrows]
 (Theory/Universal/Arrow.v) is [Qed], so nothing reduces through it.
 The probe DISCRIMINATES: [completion_unit_is_insert] above closes by
 [eq_refl] at the SAME adjunction, so the obstruction is that one
 constant's opacity and not the adjunction packaging. 

 --------
 (1) COUNIT 无法计算。它是 [unique_obj (ump_universal_arrows …)] 和 [ump_universal_arrows]（Theory/Universal/Arrow.v）是 [Qed]，所以没有任何东西可以通过它化简。探针区分了：上面的 [completion_unit_is_insert] 在相同的结合处由 [eq_refl] 关闭，因此障碍是那个常量的不透明性，而不是结合的包装。
*)
Fail Example completion_probe_counit (H : Grp)
  (x : carrier (CompletionObject (Grp_MonSets H))) :
  grp_map (completion_counit H) x
    = grp_map (completion_extend (@id MonSets (Grp_MonSets H))) x := eq_refl.

(*
 (2) [fmap[CompletionLeft]] does not compute either, for the same
 reason: [LeftAdjointFunctorFromUniversalArrows] defines it by universal
 factorization rather than by a formula.  This is why
 [CompletionFunctor] is built directly and why [completion_fmap_agrees]
 is [≈].  The control is [completion_functor_obj_agrees], where the
 OBJECT actions do agree strictly. 

 --------
 (2)  [fmap[CompletionLeft] 也无法计算，原因相同：[LeftAdjointFunctorFromUniversalArrows] 通过普适分解而不是通过公式来定义它。这就是为什么 [CompletionFunctor] 是直接构建的，以及为什么 [completion_fmap_agrees] 是 [≈]。控制是 [completion_functor_obj_agrees]，其中 OBJECT 动作确实完全一致。
*)
Fail Example completion_probe_fmap (X Y : MonSets) (f : X ~{MonSets}~> Y) :
  fmap[CompletionLeft] f = fmap[CompletionFunctor] f := eq_refl.

(*
 (3) The insertion is multiplicative only up to [≈]: the completion is a
 genuine QUOTIENT, and the two sides are distinct words of the free
 group identified by the relator.  [comp_class_op] is the [≈]
 statement, and it is what the whole presentation exists to supply. 

 --------
 (3) 插入仅在 [≈] 上是乘法性的：完成是一个真正的商，并且两边是由该关系子标识的自由群的不同单词。[comp_class_op] 是 [≈] 的陈述，它正是整个表述存在的目的所在。
*)
Fail Example completion_probe_insert_op (M : MonSets)
  (a b : carrier (mcar M)) :
  comp_class M (mop M a b)
    = grp_mul (CompletionObject M) (comp_class M a) (comp_class M b)
  := eq_refl.

(*
   * *** Formability negatives: the donor's [Set] pin

   [Grp_MonSets] is instantiable only at [GrpObject@{Set Set _}] --
   measured off [grp_monoid]'s own signature, which reads
   [∀ G : GrpObject@{Set Set u}, Monoid@{_ Set} G].  The two controls
   below show that the group's own data is formable at a strictly larger
   carrier universe, and (crucially) that the TYPE [grp_monoid] inhabits
   is formable there too, so the pin is introduced by that DEFINITION and
   is not demanded by its statement.  It is the universe-minimization
   family the tree records elsewhere; it is NOT claimed unavoidable, and
   it is NOT repaired here. 

   --------
   * *** 可成形性负面影响：捐赠者的 [Set] 引脚

   [Grp_MonSets] 只能在 [GrpObject@{Set Set _}] 实例化——
   测量基于 [grp_monoid] 自身的签名，其读数为 [∀ G : GrpObject@{Set Set u}, Monoid@{_ Set} G] 。以下两个控件
   显示该组的数据在严格更大的承载宇宙中是可成形的，并且（关键）
   TYPE [grp_monoid] 所在的类型在那里也是可成形的，因此该引脚是由该定义引入的，
   而不是由其陈述所要求的。它是树记录的宇宙最小化系列；
   并不声称不可避免，也没有在此修复。
*)

Section CompletionSetPin.

Universe uo uh up.
Constraint Set < uo.

Check (fun G : GrpObject@{uo uh up} => grp_setoid G).
Check (fun G : GrpObject@{uo uh up} =>
         @Monoid Sets Sets_Product_Monoidal (grp_setoid G)).

(* Control: [grp_monoid] must be named OUTSIDE a [Fail], or renaming it would turn the negative below vacuously green on "reference not found" while this file still compiled. / 控制：[grp_monoid] 必须在 [Fail] 之外命名，否则重命名它会在“未找到参考”时使负值虚无地显示为绿色，而此文件仍能编译。 *)
Check @grp_monoid.

Fail Check (fun G : GrpObject@{uo uh up} => grp_monoid G).
Fail Check (fun G : GrpObject@{uo uh up} => Grp_MonSets G).

End CompletionSetPin.

(*
 And the pin's BOUNDARY is measured rather than assumed: the whole
 presentation layer -- the free group, the relator subgroup, the
 quotient and its multiplicativity -- is formable over a monoid whose
 carrier universe sits strictly ABOVE [Set], and it is exactly the first
 constant whose TYPE names [Grp_MonSets] that is rejected there. 

 --------
 并且引脚的边界是测量而不是假定的：整个表示层——自由群、关系子群、商群及其乘法性——可以在一个载体宇宙严格高于 [Set] 的幺半群上构建，并且正是第一个类型为 [Grp_MonSets] 的常量在那里被拒绝。
*)

Section CompletionInsertPin.

Universe uo uh.
Constraint Set < uo.

Check (fun M : obj[MonSets@{uo uh}] => comp_free M).
Check (fun M : obj[MonSets@{uo uh}] => CompletionObject M).
Check (fun (M : obj[MonSets@{uo uh}]) (a b : carrier (mcar M)) =>
         comp_class_op M a b).

Fail Check (fun M : obj[MonSets@{uo uh}] => completion_insert M).

End CompletionInsertPin.
