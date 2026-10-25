Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Reflexive.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.SubobjectClassifier.Natural.
Require Import Category.Structure.Topos.
Require Import Category.Structure.Topos.Power.
Require Import Category.Functor.Hom.Internal.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Monadicity.Crude.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(*
 See the note in Structure/Topos/Power.v: [Category.Functor.Opposite]
 opens [functor_scope], so [category_scope] is reopened here. 

 --------
 请参见 Structure/Topos/Power.v 中的注释：[Category.Functor.Opposite] 打开了 [functor_scope]，因此 [category_scope] 在这里被重新打开。
*)
Open Scope category_scope.

(*
 Monadicity of the power-object functor: Paré's theorem.

 nLab:      https://ncatlab.org/nlab/show/Pare%27s+theorem
 nLab:      https://ncatlab.org/nlab/show/monadicity+theorem
 Wikipedia: https://en.wikipedia.org/wiki/Beck%27s_monadicity_theorem
 Paper:     Paré, "Colimits in topoi", Bulletin of the American
 Mathematical Society 80 (1974), pp. 556-561

 Mac Lane, "Categories for the Working Mathematician", 2nd ed., §IV.10,
 book p. 107 (`maclane:IV.10:remark2`):

 "The axioms for a topos have many useful consequences. For exam-
 ples, every topos has all finite colimits."

 and the Appendix, book p. 290 (`maclane:App.1:remark2`), on the same
 axioms:

 "These axioms for a topos then hold for the category of sets. They
 have a number of strong consequences. For example, they give all
 finite cate- gorical products and pullbacks, as well as all finite
 coproducts, including an initial object 0, the empty set."

 Neither passage carries a proof, and neither does Awodey §8.8 nor
 Seven Sketches §7.2.1 (both quoted in Structure/Topos/Colimits.v).
 The proof is Paré's, via monadicity of P; Mac Lane-Moerdijk, the usual
 reference, was not available, so the argument here was reconstructed
 and CHECKED BY COMPILATION.

 THIS FILE PROVES `power_object_monadic : Monadic PowF` by CONSUMING the
 in-tree crude monadicity theorem, Monad/Monadicity/Crude.v's
 [crude_monadicity], rather than reproving any monadicity theorem.  Its
 three hypotheses are discharged here as:

 (a) [op_HasReflexiveCoequalizers] -- reflexive coequalizers in C^op,
 which is three applications of pre-existing reductions;
 (b) [pow_PreservesReflexiveCoequalizers] -- the substantial half;
 (c) [PowF_ReflectsIsos] -- through balancedness.

 Beck's precise theorem ([Monad/Monadicity/Beck.v], whose hypothesis is
 [CreatesUSplitCoequalizers]) should ALSO apply, since the image pair is not
 merely P-split but SPLIT -- an ARGUMENT and not a compiled check, that route
 not having been built; it is not taken because creation would need the
 comparison isomorphism and the reflection clause on top of exactly the same
 split data, so the crude form is strictly cheaper here.

 WHAT WAS ABSENT BEFORE THIS FILE.  Every search below was re-run over the
 whole tree with these five new files EXCLUDED, and the counts are what that
 measurement returned, not what a plan predicted.  "A topos is balanced": 119
 case-insensitive hits for "balanced" across 18 files and none about a topos
 -- they are the balanced monoidal categories and twists of
 Structure/Monoidal/*, the balanced tensors and balanced laws of
 Instance/Mod/*, and the balancedness of [Sets], [Set_*], [Met] and [C, D]
 (asserted, denied or deferred there), with Instance/Two.v REFUTING it for 2,
 plus [Par_BalancedMonoidal] in Instance/Coq/Par.v, the module-tensor probe
 Test/ProbeModTensor.v and one header mention in Adjunction/Unitalization.v --
 and NOT ONE of those 18 files so much as mentions [ElementaryTopos], which is
 the sharper check.  "Every mono in a topos is regular": the name
 [RegularMono] occurs on exactly ONE line outside these files, in
 Adjunction/CokernelPair.v, which says in terms that the tree has no such
 class; the only other .v mentions of a regular monomorphism are two more
 prose lines of that file and one comment in Theory/Morphisms.v.  The
 singleton map: the 4 hits for [singleton_map] are two declarations and their
 two uses in Instance/Sets/Powerset.v, about setoid power sets and not about
 toposes.  [PowFunctor], [PowF], [Pow_Functor], [pow_reflects_isos],
 [pow_monadic] and [power_object]: zero files each.  So balancedness, the
 singleton map and P's faithfulness are new here by those searches; the direct
 image and Beck-Chevalley are new AT THE LEVEL OF SUBOBJECTS in an arbitrary
 category, since the tree's existing [DirectImage] (Instance/Powerset.v) and
 [beck_chevalley_exists]/[beck_chevalley_forall]
 (Instance/Powerset/Quantifier.v) are about power sets of a setoid and neither
 is stated for [SubObj].

 THE HARD STEP IS §E, AND ITS SHAPE IS BETTER THAN FEARED.  Unfolded at
 U := P, the crude hypothesis asks: given f, g : b ⇉ a in E with a
 common RETRACTION r, and ANY equalizer e : k ~> b of the pair, show
 P e : P b ~> P k is a coequalizer of P f, P g.  The triple
 (P f, P g, P e) is a genuine SPLIT coequalizer, and
 Structure/Coequalizer/Split.v's [SplitCoequalizer] record wants exactly
 the four equations the argument produces:

 law1  P e ∘ P f ≈ P e ∘ P g   -- contravariant functoriality
 plus the equalizer's [fork_eq];
 law2  P e ∘ ∃_e ≈ id          -- [pow_ex_mono] at m := e;
 law3  P f ∘ ∃_f ≈ id          -- [pow_ex_mono] at m := f;
 law4  P g ∘ ∃_f ≈ ∃_e ∘ P e   -- [pow_bc], Beck-Chevalley.

 THE DIRECT IMAGE NEEDS NO IMAGE FACTORIZATION, and that is why the
 step is tractable at all: ∃ is taken only along a MONO, so
 [second m ∘ (membership mono)] is already a mono and its characteristic
 map exists outright.  Epi-mono factorization in a topos is a separate
 obligation and is NOT built here.

 §D's [IsPullback_sym], [second_pullback], [first_second_pullback] and
 [bc_mono] use no classifier -- the first mentions nothing beyond
 [IsPullback], the next two only the cartesian structure, and [bc_mono] only
 chosen pullbacks and [SubObj] -- yet all four carry an [ElementaryTopos C]
 argument in their types, because this section's
 [Set Default Proof Using "All"] discharges the whole context into every
 [Qed]-closed lemma; a move to Theory/Morphisms/Stability.v beside
 [pullback_paste] (or, for [bc_mono], to Theory/Subobject/Functor.v beside
 [sub_reindex]) would first shed that argument.  They are kept here to avoid a
 wide rebuild, and this sentence is the record of the debt.

 Of this file's two [Defined] tokens, [pow_split_coequalizer] is LOAD-BEARING
 -- flipped alone to [Qed], [pow_PreservesReflexiveCoequalizers] no longer
 typechecks -- and [PowF_Faithful] is not: flipped alone, this file,
 Structure/Topos/Colimits.v and the probe all compile unchanged. 

 --------
 幂对象函子单子性：Paré 定理。

 nLab:       https://ncatlab.org/nlab/show/Pare%27s+theorem 
 nLab:       https://ncatlab.org/nlab/show/monadicity+theorem 
 Wikipedia:  https://en.wikipedia.org/wiki/Beck%27s_monadicity_theorem 
 论文:       Paré, 《在拓扑中余积》, 《美国数学学会公报》 80 (1974), 第 556-561 页

 Mac Lane, 《为工作数学家准备的范畴论》, 第二版, §IV.10, 书第 107 页 (`maclane:IV.10:remark2`):

 “拓扑的公理具有许多有用的结果。例如，每个拓扑都具有所有有限余积。”

 以及附录，书第 290 页 (`maclane:App.1:remark2`)，关于相同的公理：

 “这些拓扑公理也适用于集合范畴。它们有许多强有力的结果。例如，它们给出所有有限范畴积和拉回积，以及所有有限余积，包括初始对象 0，即空集。”没有一段文字提供证明，Awodey §8.8 也没有，Seven Sketches §7.2.1 也没有（两者都在 Structure/Topos/Colimits.v 中引用）。
 证明是 Paré 的，通过 P 的单子性；Mac Lane-Moerdijk，这是通常的参考文献，不可用，因此这里的论证是重新构建的，并通过编译进行了检查。

 这个文件通过使用 in-tree 粗单子定理（Monad/Monadicity/Crude.v 中的 [crude_monadicity]），而不是重新证明任何单子定理，来证明 `power_object_monadic : Monadic PowF`。
 它的三个假设在这里被解除为：

 (a) [op_HasReflexiveCoequalizers] —— C^op 中的自反余等化，这是三次应用已有的约简；
 (b) [pow_PreservesReflexiveCoequalizers] —— 实质性的一半；
 (c) [PowF_ReflectsIsos] —— 通过平衡性。贝克的精确定理（[Monad/Monadicity/Beck.v]，其假设是[CreatesUSplitCoequalizers]）也应适用，因为图像对不仅仅是P-分裂，而是分裂——这是一个论证，而不是编译的检查，那条路径尚未构建；它之所以未被采用，是因为创建将需要比较同构和反射子句，而这正好基于相同的分裂数据，因此在这里粗略形式严格来说更便宜。在此文件之前缺失的内容。下面的每次搜索都是在整个树上重新运行，排除了这五个新文件，显示的数量是该测量返回的结果，而不是计划预测的结果。“一个上层是平衡的”：在18个文件中对“平衡”不区分大小写的搜索命中119次，但没有一次涉及到一个上层——它们是 Structure/Monoidal/* 中的平衡单范畴和扭转、Instance/Mod/* 中的平衡张量和平衡律，以及 [Sets]、[Set_*]、[Met] 和 [C, D] 的平衡性（在那里被断言、否认或延迟），Instance/Two.v 对其中的2予以驳斥，还有 Instance/Coq/Par.v 中的 [Par_BalancedMonoidal]，模块-张量探针 Test/ProbeModTensor.v 以及 Adjunction/Unitalization.v 中的一个头文件提及 —— 并且在这18个文件中没有一个提到 [ElementaryTopos]，这是更严格的检查。“在一个拓扑中每个单射都是正规单射”：名字 [RegularMono] 在这些文件之外恰好出现在 một 行，即 Adjunction/CokernelPair.v 文件中，该文件的意思是树中没有这样的类；该文件中关于正规单射的唯一其他 .v 提及是其两行散文和 Theory/Morphisms.v 文件中的一条注释。单元素映射：[singleton_map] 的 4 个命中是两个声明及它们在 Instance/Sets/Powerset.v 文件中的两个使用，这些关于集合的幂集而不是关于拓扑。[PowFunctor]、[PowF]、[Pow_Functor]、[pow_reflects_isos]、[pow_monadic] 和 [power_object]：每个零个文件。所以平衡性、单元素映射和 P 的忠实性在这些搜索中是新的；而直接像和 Beck-Chevalley 定理在任意范畴的子对象层面上是新的，因为树中已有的 [DirectImage] (Instance/Powerset.v) 和 [beck_chevalley_exists] / [beck_chevalley_forall] (Instance/Powerset/Quantifier.v) 是关于集合等价类的幂集，而且都没有针对 [SubObj] 给出说明。

 难点在于 §E，其形状比预期要好。在 U := P 展开时，粗略假设要求：给定 f, g : b ⇉ a 在 E 中具有公共收缩 r，并且任意等化器 e : k ~> b 对该对，证明 P e : P b ~> P k 是 P f, P g 的一个共同等化器。三元组 (P f, P g, P e) 是一个真正的分裂共同等化器，而 Structure/Coequalizer/Split.v 的 [SplitCoequalizer] 记录正好需要论证产生的四个方程。law1  P e ∘ P f ≈ P e ∘ P g   -- 逆变函子性
 加上等化器的 [fork_eq]；
 law2  P e ∘ ∃_e ≈ id          --  [pow_ex_mono] 于 m := e;
 law3  P f ∘ ∃_f ≈ id          --  [pow_ex_mono] 于 m := f;
 law4  P g ∘ ∃_f ≈ ∃_e ∘ P e   --  [pow_bc]，Beck-Chevalley。

 直接像不需要像分解，这也是为什么这一步完全可处理的原因：∃ 只沿着单射取，所以
 [second m ∘ (membership mono)] 已经是单射且其特征映射直接存在。拓扑中的满单分解是一个单独的义务，并且这里未构建。§D 的 [IsPullback_sym]、[second_pullback]、[first_second_pullback] 和 [bc_mono] 不使用分类器——第一个除了 [IsPullback] 外没有提及其他内容，接下来的两个只提到笛卡尔结构，而 [bc_mono] 只提到选定的拉回和 [SubObj]——然而这四个在它们的类型中都携带一个 [ElementaryTopos C] 参数，因为本节的 [Set Default Proof Using "All"] 将整个上下文释放到每个 [Qed] 闭合的引理中；移动到 Theory/Morphisms/Stability.v 旁的 [pullback_paste]（或者对于 [bc_mono]，移动到 Theory/Subobject/Functor.v 旁的 [sub_reindex]）首先会丢弃该参数。它们保留在这里以避免大范围重建，而这句话记录了这个债务。在这个文件的两个 [Defined] 标记中，[pow_split_coequalizer] 是承重的 —— 单独翻转为 [Qed] 后，[pow_PreservesReflexiveCoequalizers] 不再类型检查 —— 而 [PowF_Faithful] 不是：单独翻转时，这个文件、Structure/Topos/Colimits.v 和测试探针都可以正常编译。
*)

Section ToposMonadic.

Context {C : Category}.
Context `{H : @ElementaryTopos C}.

#[local] Set Default Proof Using "All".

(* * ** (A) Finite completeness, and reflexive coequalizers in C^op / * **（A）有限完备性，以及 C^op 中的自反共等化器 *)

(*
 Mac Lane's finite-limit half, at the level of the four elementary
 generators.  Equalizers are DERIVED from the terminal object and pullbacks by
 Structure/Pullback/Reduction.v's Awodey square, which builds the products it
 needs from those two ([Cartesian_of_HasPullbacks_Terminal]) rather than
 consuming the class's own [topos_cartesian]; the class carries the other
 three as fields. 

 --------
 Mac Lane 的有限极限一半，在四个基本生成元的层面上。等化器是由终对象和拉回导出的，通过 Structure/Pullback/Reduction.v 的 Awodey 方框，它从这两个（[Cartesian_of_HasPullbacks_Terminal]）构建所需的积，而不是使用该类自身的 [topos_cartesian]；该类将另外三个作为字段保存。
*)
Definition topos_HasEqualizers : @HasEqualizers C :=
  HasEqualizers_of_HasPullbacks_Terminal topos_pullbacks.

(*
 The appended Seven Sketches checkbox, at generator level: terminal
 object, binary products, pullbacks, equalizers.  NO finite-shape
 induction is performed here, so this is NOT a [Limit]-shaped "all finite
 limits"; that statement is Structure/Limit/Finite.v's [FinitelyComplete].

 That checkbox asks this to close a reduction Structure/Topos.v's header
 "records as not formalized"; the premise is stale -- since #326 that header
 says the reduction and its converse ARE formalized.  What it records as not
 done is the finite-shape induction, and that is still not done:
 [topos_finitely_complete] is at generator level. 

 --------
 附加的“七个草图”复选框，在生成器级别：终端对象、二元积、拉回、等化器。这里没有进行有限形状归纳，因此这不是一个 [Limit] 形状的“所有有限极限”；该陈述是 Structure/Limit/Finite.v 中的 [FinitelyComplete]。

 该复选框要求在 Structure/Topos.v 的头部“记录为未形式化”时关闭一个归约；前提已经过时——自 #326 起，该头部说明归约及其逆归约已经形式化。记录为未完成的是有限形状归纳，而这仍然未完成：[topos_finitely_complete] 在生成器级别。
*)
Definition topos_finitely_complete :
  @Terminal C * @Cartesian C * @HasPullbacks C * @HasEqualizers C :=
  (topos_terminal, topos_cartesian, topos_pullbacks, topos_HasEqualizers).

(*
 A reflexive pair in C^op is a CO-reflexive pair in C, and a coequalizer
 in C^op is an equalizer in C.  Both readings are definitional, so the
 whole of Crude.v's first hypothesis is three pre-existing reductions.
 [(C^op)^op = C] by reflexivity is what makes the middle line typecheck. 

 --------
 C^op 中的自反对是 C 中的 CO-自反对，而 C^op 中的余等化子是 C 中的等化子。两种理解都是定义性的，因此 Crude.v 的第一个假设整体上是三个预先存在的化简。通过自反性，[(C^op)^op = C] 使中间的行类型检查通过。
*)
Definition op_HasCoequalizers : @HasCoequalizers (C^op) :=
  @HasCoequalizers_of_HasEqualizers_op (C^op) topos_HasEqualizers.

Definition op_HasReflexiveCoequalizers : HasReflexiveCoequalizers (C^op) :=
  @HasCoequalizers_HasReflexiveCoequalizers (C^op) op_HasCoequalizers.

(*
 The monad of the self-adjunction, P ◯ P^op.  Declared here rather than
 in Structure/Topos/Power.v because [Adjunction_Induced_Monad] costs
 that file +6 modules of closure, while this file requires Crude.v --
 and hence Comparison.v -- anyway. 

 --------
 自伴随的单子，P ◯ P^op。这里声明，而不是在 Structure/Topos/Power.v 中声明，因为 [Adjunction_Induced_Monad] 会增加那个文件 +6 个闭包模块，而这个文件无论如何都需要 Crude.v —— 因此也需要 Comparison.v。
*)
Definition pow_monad : @Monad C (PowF ◯ Opposite_Functor PowF) :=
  @Adjunction_Induced_Monad (C^op) C (Opposite_Functor PowF) PowF
    pow_adjunction.

(* * ** (B) Balancedness, the singleton map, and reflection of isos / * **（B）平衡性、单元素映射和同构的反射 *)

(*
 A topos is balanced.  The classifying square of a MONIC epi forces its
 characteristic map down to [truth ∘ one], after which the identity
 lies over truth and factors through f. 

 --------
 一个拓扑是平衡的。单射-满射的分类方格迫使其特征映射下降到 [truth ∘ one]，此后恒等映射位于真值之上并通过 f 分解。
*)
Theorem topos_balanced {x y : C} (f : x ~> y) (Mf : Monic f) (Ef : Epic f) :
  IsIsomorphism f.
Proof.
  pose proof (char_pullback f Mf) as PB.
  assert (Hc : char f Mf ≈ truth ∘ one).
  { apply (epic (Epic := Ef)).
    rewrite (is_pullback_commutes PB).
    rewrite <- comp_assoc.
    now rewrite (one_unique (one ∘ f) one). }
  destruct (is_pullback_ump PB y id one) as [u [Hu1 Hu2] Huniq].
  { rewrite id_right, Hc; reflexivity. }
  unshelve refine {| two_sided_inverse := u |}.
  - exact Hu1.
  - apply (monic (Monic := Mf)).
    rewrite comp_assoc, Hu1, id_left, id_right.
    reflexivity.
Qed.

Definition topos_diag (x : C) : x ~> x × x := id △ id.

Lemma diag_Monic (x : C) : Monic (topos_diag x).
Proof.
  apply sections_are_monic.
  unshelve refine {| section := exl |}.
  unfold topos_diag; cat.
Qed.

(* The singleton map: the transpose of the characteristic map of the diagonal, i.e. x ↦ {x}. / 单例映射：对角线特征映射的转置，即 x ↦ {x}。 *)
Definition sing (x : C) : x ~> Pow x :=
  curry (char (topos_diag x) (diag_Monic x)).

Lemma sing_Monic (x : C) : Monic (sing x).
Proof.
  constructor; intros z u v Huv.
  pose proof (char_pullback (topos_diag x) (diag_Monic x)) as PB.
  assert (Hun : char (topos_diag x) (diag_Monic x) ∘ first u
                ≈ char (topos_diag x) (diag_Monic x) ∘ first v).
  { unfold sing in Huv.
    apply curry_inj.
    rewrite <- !curry_comp_l.
    exact Huv. }
  assert (Hq : char (topos_diag x) (diag_Monic x) ∘ (v △ u) ≈ truth ∘ one).
  { transitivity (char (topos_diag x) (diag_Monic x) ∘ (u △ u)).
    - rewrite <- (id_right (v △ u)).
      transitivity ((char (topos_diag x) (diag_Monic x) ∘ first v)
                      ∘ (id △ u)).
      + rewrite <- comp_assoc.
        apply compose_respects; [reflexivity|].
        unfold first; unfork.
      + rewrite <- Hun, <- comp_assoc.
        apply compose_respects; [reflexivity|].
        unfold first; unfork.
    - transitivity (char (topos_diag x) (diag_Monic x)
                      ∘ (topos_diag x ∘ u)).
      + apply compose_respects; [reflexivity|].
        unfold topos_diag; unfork.
      + rewrite comp_assoc, (is_pullback_commutes PB), <- comp_assoc.
        now rewrite (one_unique (one ∘ u) one). }
  destruct (is_pullback_ump PB z (v △ u) one Hq) as [w [Hw1 _] _].
  transitivity w.
  - rewrite <- (exr_fork v u), <- Hw1.
    unfold topos_diag; unfork.
  - rewrite <- (exl_fork v u), <- Hw1.
    unfold topos_diag; unfork.
Qed.

(*
 The diagonal is a SYMMETRIC relation, so its characteristic map is
 invariant under [swap]; hence the singleton is its own [flip]. 

 --------
 对角线是一个对称关系，所以它的特征映射在 [swap] 下是不变的；因此单例是其自身的 [flip]。
*)
Lemma char_diag_swap (x : C) :
  char (topos_diag x) (diag_Monic x) ∘ swap
    ≈ char (topos_diag x) (diag_Monic x).
Proof.
  apply char_unique.
  pose proof (char_pullback (topos_diag x) (diag_Monic x)) as PB.
  assert (Hsd : swap ∘ topos_diag x ≈ topos_diag x)
    by (unfold topos_diag; unfork).
  constructor.
  - rewrite <- comp_assoc, Hsd.
    exact (is_pullback_commutes PB).
  - intros Q q1 q2 Hq.
    destruct (is_pullback_ump PB Q (swap ∘ q1) q2) as [w [Hw1 Hw2] Hwu].
    { rewrite comp_assoc; exact Hq. }
    unshelve refine {| unique_obj := w |}.
    + split; [| exact Hw2].
      rewrite <- (id_left q1), <- swap_invol, <- comp_assoc, <- Hw1.
      rewrite comp_assoc, Hsd; reflexivity.
    + intros v [Hv1 Hv2].
      apply Hwu; split; [| exact Hv2].
      rewrite <- Hv1, comp_assoc, Hsd; reflexivity.
Qed.

Lemma flip_sing (x : C) : flip (sing x) ≈ sing x.
Proof.
  unfold flip, sing.
  rewrite uncurry_curry.
  now rewrite char_diag_swap.
Qed.

(*
 P IS FAITHFUL, AND THE PROOF USES STEP TWO RATHER THAN THE ADJUNCTION
 MACHINERY.  From [flip_pow_comp] at p := sing a, precomposing the
 singleton with an arrow is [flip] of its P-image postcomposed with the
 singleton; [sing_Monic] then cancels.  (Adjunction/FullFaithful.v's
 counit criterion [right_adjoint_faithful_iff_counit_epic] is NOT used:
 it would cost a Require, and this route needs only step two.) 

 --------
 P 是忠实的，证明使用的是步骤二，而不是伴随结构。从 [flip_pow_comp] 在 p := sing a 起，通过与箭头预组合单元素是 [flip]，其 P-像再与单元素后组合；然后 [sing_Monic] 取消。（Adjunction/FullFaithful.v 的余单位判据 [right_adjoint_faithful_iff_counit_epic] 没有使用：它会需要一个 Require，而这条路径只需要步骤二。）
*)
#[export] Instance PowF_Faithful : Faithful PowF.
Proof.
  constructor; intros a0 b0 f g Hfg.
  apply (monic (Monic := sing_Monic a0)).
  assert (Ef : sing a0 ∘ f ≈ flip (fmap[PowF] f ∘ sing a0))
    by (rewrite flip_pow_comp, flip_sing; reflexivity).
  assert (Eg : sing a0 ∘ g ≈ flip (fmap[PowF] g ∘ sing a0))
    by (rewrite flip_pow_comp, flip_sing; reflexivity).
  rewrite Ef, Eg.
  unfold flip.
  now rewrite Hfg.
Defined.

(*
 Carrying [IsIsomorphism] between C and C^op is a permutation of the
 three fields.  The tree's own copy of this permutation is
 Theory/Morphisms/CokernelPair.v's [IsIsomorphism_of_op] /
 [op_IsIsomorphism_of].  Requiring that module would cost this file exactly
 ONE module of closure (measured with coqdep: its closure minus this file's is
 that module alone), so the thirteen-line duplication below is a choice about
 coupling and not about cost; it is recorded here rather than defended. 

 --------
 在 C 和 C^op 之间携带 [IsIsomorphism] 是三个字段的一个置换。该树自身的这个置换的副本是 Theory/Morphisms/CokernelPair.v 中的 [IsIsomorphism_of_op] / [op_IsIsomorphism_of]。要求使用该模块将使此文件正好增加一个闭包模块（用 coqdep 测量：其闭包减去此文件的闭包就是该模块本身），因此下面的十三行重复是关于耦合的选择，而不是关于成本的选择；它在此处被记录而不是进行辩护。
*)
Definition IsIso_of_op {a b : C} (h : b ~> a)
  (I : @IsIsomorphism (C^op) a b h) : @IsIsomorphism C b a h :=
  @Build_IsIsomorphism C b a h
    (@two_sided_inverse (C^op) a b h I)
    (@is_left_inverse (C^op) a b h I)
    (@is_right_inverse (C^op) a b h I).

Definition op_IsIso_of {a b : C} (h : b ~> a)
  (I : @IsIsomorphism C b a h) : @IsIsomorphism (C^op) a b h :=
  @Build_IsIsomorphism (C^op) a b h
    (@two_sided_inverse C b a h I)
    (@is_left_inverse C b a h I)
    (@is_right_inverse C b a h I).

(*
 P REFLECTS ISOMORPHISMS: the image is monic and epic, faithfulness
 reflects both into C^op, the duality quartet of
 Theory/Morphisms/Duality.v exchanges them in C, and balancedness
 concludes. 

 --------
 P 反映同构：图像是单态的和满态的，忠实性在 C^op 中反映两者，Theory/Morphisms/Duality.v 的对偶四重奏在 C 中交换它们，最后得出平衡性。
*)
#[export] Instance PowF_ReflectsIsos : ReflectsIsos PowF.
Proof.
  constructor; intros a0 b0 f Hiso.
  pose proof (iso_to_monic (IsIsoToIso _ Hiso)) as Mi.
  pose proof (iso_to_epic  (IsIsoToIso _ Hiso)) as Ei.
  simpl in Mi, Ei.
  pose proof (faithful_reflects_monic PowF f Mi) as Mf.
  pose proof (faithful_reflects_epic  PowF f Ei) as Ef.
  apply op_IsIso_of.
  apply topos_balanced.
  - exact (@Monic_of_op_Epic C b0 a0 f Ef).
  - exact (@Epic_of_op_Monic C b0 a0 f Mf).
Qed.

(* * ** (C) The direct image along a mono / * ** (C) 沿单态的直接映像 *)

(* [second] of a mono is a mono: read both components off the product. / [second] 单态的就是单态：从乘积中读取两个组成部分。 *)
Lemma second_Monic {u x z : C} (m : u ~> x) (M : Monic m) :
  Monic (@second C _ u x z m).
Proof.
  constructor; intros w p q Hpq.
  assert (H1 : exl ∘ p ≈ exl ∘ q).
  { rewrite <- (exl_second (z:=z) m), <- !comp_assoc, Hpq; reflexivity. }
  assert (H2 : exr ∘ p ≈ exr ∘ q).
  { apply (monic (Monic := M)).
    rewrite !comp_assoc, <- !(exr_second m), <- !comp_assoc, Hpq;
      reflexivity. }
  rewrite <- (id_left p), <- (id_left q), <- fork_exl_exr,
          <- !fork_comp, H1, H2; reflexivity.
Qed.

(* Pushing a subobject forward along a MONO is just composing the two monos -- no image factorization is needed, and none is available. / 沿着 MONO 推动一个子对象只是将两个单射组合——不需要图像分解，也没有可用的分解。 *)
Definition sub_push {x y : C} (n : y ~> x) (N : Monic n) (s : SubObj y)
  : SubObj x :=
  {| sub_dom := sub_dom s
   ; sub_mono := n ∘ sub_mono s
   ; sub_is_monic := monic_compose N (sub_is_monic s) |}.

Lemma sub_push_respects {x y : C} (n : y ~> x) (N : Monic n)
      (s s' : SubObj y) (Hs : s ≈ s') :
  sub_push n N s ≈ sub_push n N s'.
Proof.
  destruct Hs as [i Hi].
  exists i; simpl.
  rewrite <- comp_assoc.
  now rewrite Hi.
Qed.

(* Reindexing a pushed subobject along the same mono returns it. / 沿同一个单态重新索引已推送的子对象会返回它。 *)
Lemma sub_reindex_push {x y : C} (n : y ~> x) (N : Monic n) (s : SubObj y) :
  sub_reindex n (sub_push n N s) ≈ s.
Proof.
  apply (sub_reindex_transport n (sub_push n N s) s id).
  constructor.
  - simpl; cat.
  - simpl; intros Q q1 q2 Hq.
    unshelve refine {| unique_obj := q2 |}.
    + split; [| cat].
      apply (monic (Monic := N)).
      rewrite Hq, comp_assoc; reflexivity.
    + intros w [Hw1 Hw2]; simpl in *.
      now rewrite <- Hw2; cat.
Qed.

(* The membership subobject of Pow x × x, and its characteristic map. / Pow x × x 的成员子对象及其特征映射。 *)
Definition pow_mem (x : C) : SubObj (Pow x × x) :=
  sub_reindex eval truth_subobject.

Lemma char_mem (x : C) : char_sub (pow_mem x) ≈ eval.
Proof. exact (classifier_char_roundtrip eval). Qed.

(* Classification is injective on subobjects: pull truth back on both sides and use the round trip twice. / 分类在子对象上是单射的：在两边拉回真理，并使用往返两次。 *)
Lemma char_sub_inj {x : C} (s s' : SubObj x) :
  char_sub s ≈ char_sub s' → s ≈ s'.
Proof.
  intros Hc.
  transitivity (sub_reindex (char_sub s) truth_subobject).
  - symmetry; apply classifier_pullback_roundtrip.
  - transitivity (sub_reindex (char_sub s') truth_subobject).
    + apply sub_reindex_respects_mor; exact Hc.
    + apply classifier_pullback_roundtrip.
Qed.

(*
 Evaluation intertwines the P-image of m on the left with m on the
 right: the substitution law for the membership relation. 

 --------
 评估将左侧的 m 的 P-像与右侧的 m 交织在一起：成员关系的替代律。
*)
Lemma eval_pow_square {u x : C} (m : u ~> x) :
  eval ∘ first (fmap[PowF] m) ≈ eval ∘ second m.
Proof.
  rewrite eval_first.
  simpl.
  rewrite uncurry_curry, id_left.
  reflexivity.
Qed.

(* The same square one level up, on membership subobjects. / 同样的平方，上升一个级别，在成员子对象上。 *)
Lemma mem_pow_square {u x : C} (m : u ~> x) :
  sub_reindex (first (fmap[PowF] m)) (pow_mem u)
    ≈ sub_reindex (second m) (pow_mem x).
Proof.
  apply char_sub_inj.
  rewrite !char_reindex, !char_mem.
  apply eval_pow_square.
Qed.

(*
 THE DIRECT IMAGE along a mono m: classify the pushed membership
 relation and transpose. 

 --------
 沿着单一 m 的直接映像：分类推动的隶属关系并转置。
*)
Definition ex_mono {u x : C} (m : u ~> x) (M : Monic m) : Pow u ~> Pow x :=
  curry (char_sub (sub_push (second m) (second_Monic m M) (pow_mem u))).

(* THE RETRACTION LAW: P m splits the direct image along m. / 收缩定律：P m 沿 m 分裂直像。 *)
Theorem pow_ex_mono {u x : C} (m : u ~> x) (M : Monic m) :
  fmap[PowF] m ∘ ex_mono m M ≈ id.
Proof.
  unfold ex_mono.
  rewrite pow_precompose.
  rewrite <- char_reindex.
  rewrite (char_sub_respects _ _
             (sub_reindex_push (second m) (second_Monic m M) (pow_mem u))).
  rewrite char_mem.
  apply curry_eval.
Qed.

(* * ** (D) Pullback plumbing and Beck-Chevalley / * **（D）拉回管道与 Beck-Chevalley *)

Lemma IsPullback_sym {x y z : C} {f : x ~> z} {g : y ~> z}
      {P : C} {p1 : P ~> x} {p2 : P ~> y} :
  IsPullback f g P p1 p2 → IsPullback g f P p2 p1.
Proof.
  intros HP; constructor.
  - symmetry; exact (is_pullback_commutes HP).
  - intros Q q1 q2 Hq.
    destruct (is_pullback_ump HP Q q2 q1 (symmetry Hq)) as [u [U1 U2] Uu].
    unshelve refine {| unique_obj := u |}.
    + split; assumption.
    + intros v [V1 V2]; apply Uu; split; assumption.
Qed.

(*
 A pullback square multiplied on the left by a fixed object stays a
 pullback. 

 --------
 在左边被一个固定对象相乘的拉回平方仍然是拉回。
*)
Lemma second_pullback {b a k : C} {f g : b ~> a} {p1 p2 : k ~> b}
      (HP : IsPullback f g k p1 p2) (z : C) :
  IsPullback (@second C _ b a z f) (@second C _ b a z g)
             (z × k) (second p1) (second p2).
Proof.
  constructor.
  - rewrite <- !second_comp.
    now rewrite (is_pullback_commutes HP).
  - intros Q q1 q2 Hq.
    assert (Hl : exl ∘ q1 ≈ exl ∘ q2).
    { transitivity (exl ∘ (second f ∘ q1)).
      - rewrite comp_assoc, exl_second; reflexivity.
      - rewrite Hq, comp_assoc, exl_second; reflexivity. }
    assert (Hr : f ∘ (exr ∘ q1) ≈ g ∘ (exr ∘ q2)).
    { transitivity (exr ∘ (second f ∘ q1)).
      - rewrite !comp_assoc, exr_second; reflexivity.
      - rewrite Hq, !comp_assoc, exr_second; reflexivity. }
    destruct (is_pullback_ump HP Q (exr ∘ q1) (exr ∘ q2) Hr)
      as [v [V1 V2] Vu].
    unshelve refine {| unique_obj := (exl ∘ q1) △ v |}.
    + split; unfold second.
      * rewrite <- fork_comp; cat.
        rewrite <- comp_assoc; cat.
        rewrite V1.
        rewrite <- (id_left q1) at 3.
        now rewrite <- fork_exl_exr, <- fork_comp.
      * rewrite <- fork_comp; cat.
        rewrite <- comp_assoc; cat.
        rewrite V2, Hl.
        rewrite <- (id_left q2) at 3.
        now rewrite <- fork_exl_exr, <- fork_comp.
    + intros w [W1 W2].
      assert (Ew : exr ∘ w ≈ v).
      { symmetry; apply Vu; split.
        - rewrite <- W1, !comp_assoc, exr_second; reflexivity.
        - rewrite <- W2, !comp_assoc, exr_second; reflexivity. }
      assert (El : exl ∘ w ≈ exl ∘ q1).
      { rewrite <- W1, !comp_assoc, exl_second; reflexivity. }
      rewrite <- (id_left w), <- fork_exl_exr, <- fork_comp, El, Ew.
      reflexivity.
Qed.

(*
 [first] of one arrow and [second] of another form a pullback square in
 the product, with NO monicity hypothesis on either: the two act in
 independent coordinates.  This is the square Beck-Chevalley is applied
 to on the right-hand side of [pow_bc]. 

 --------
 [first] 的一个箭头和 [second] 的另一个箭头在积中形成一个拉回图，并且对任意一个都没有单射性假设：它们在独立的坐标上作用。这就是在 [pow_bc] 右侧应用 Beck-Chevalley 的方形。
*)
Lemma first_second_pullback {z w u x : C} (phi : z ~> w) (m : u ~> x) :
  IsPullback (@first C _ z w x phi) (@second C _ u x w m)
             (z × u) (@second C _ u x z m) (@first C _ z w u phi).
Proof.
  constructor.
  - unfold first, second; unfork.
  - intros Q q1 q2 Hq.
    assert (Hl : phi ∘ (exl ∘ q1) ≈ exl ∘ q2).
    { transitivity (exl ∘ (first phi ∘ q1)).
      - rewrite !comp_assoc, exl_first; reflexivity.
      - rewrite Hq, comp_assoc, exl_second; reflexivity. }
    assert (Hr : exr ∘ q1 ≈ m ∘ (exr ∘ q2)).
    { transitivity (exr ∘ (first phi ∘ q1)).
      - rewrite comp_assoc, exr_first; reflexivity.
      - rewrite Hq, !comp_assoc, exr_second; reflexivity. }
    unshelve refine {| unique_obj := (exl ∘ q1) △ (exr ∘ q2) |}.
    + split.
      * unfold second.
        rewrite <- fork_comp; cat.
        rewrite <- comp_assoc; cat.
        rewrite <- Hr.
        rewrite <- (id_left q1) at 3.
        now rewrite <- fork_exl_exr, <- fork_comp.
      * unfold first.
        rewrite <- fork_comp; cat.
        rewrite <- comp_assoc; cat.
        rewrite Hl.
        rewrite <- (id_left q2) at 3.
        now rewrite <- fork_exl_exr, <- fork_comp.
    + intros v [V1 V2].
      assert (El : exl ∘ v ≈ exl ∘ q1).
      { rewrite <- V1, comp_assoc, exl_second; reflexivity. }
      assert (Er : exr ∘ v ≈ exr ∘ q2).
      { rewrite <- V2, comp_assoc, exr_first; reflexivity. }
      rewrite <- (id_left v), <- fork_exl_exr, <- fork_comp, El, Er.
      reflexivity.
Qed.

(*
 BECK-CHEVALLEY at the level of subobjects, for a pushforward along a
 MONO: reindexing a pushed subobject along the other leg of a pullback square
 is pushing forward the reindexed one.  Eight lines of [pullback_paste]. 

 --------
 BECK-CHEVALLEY 在子对象的层次上，对于沿 MONO 的推进：沿拉回方块的另一条边重新索引一个推进的子对象，就是推进重新索引的那个。[pullback_paste] 的八行。
*)
Lemma bc_mono {X Y Z K : C} {F : X ~> Z} {G : Y ~> Z}
      {p1 : K ~> X} {p2 : K ~> Y}
      (HP : IsPullback F G K p1 p2) (MF : Monic F) (M2 : Monic p2)
      (R : SubObj X) :
  sub_reindex G (sub_push F MF R) ≈ sub_push p2 M2 (sub_reindex p1 R).
Proof.
  apply (sub_reindex_transport G (sub_push F MF R)
           (sub_push p2 M2 (sub_reindex p1 R))
           (pullback_snd p1 (sub_mono R) (pullback p1 (sub_mono R)))).
  apply IsPullback_sym.
  exact (pullback_paste HP
           (IsPullback_sym
              (pullback_is_pullback p1 (sub_mono R)
                 (pullback p1 (sub_mono R))))).
Qed.

(*
 A co-reflexive parallel pair -- one with a common RETRACTION -- has its
 equalizer as the pullback of the pair against itself, with BOTH legs
 the equalizing map.  This is where co-reflexivity is spent. 

 --------
 一个共自反平行对——一个具有共同的收缩——其等化子是该对自身的拉回，其两条边都是等化映射。这就是共自反性发挥作用的地方。
*)
Lemma coreflexive_equalizer_pullback {a b k : C} {f g : b ~> a}
      {r : a ~> b} (Hf : r ∘ f ≈ id) (Hg : r ∘ g ≈ id)
      {e : k ~> b} (HE : IsEqualizer f g k e) :
  IsPullback f g k e e.
Proof.
  constructor.
  - exact (fork_eq HE).
  - intros Q q1 q2 Hq.
    assert (Hq12 : q1 ≈ q2).
    { rewrite <- (id_left q1), <- Hf, <- comp_assoc, Hq,
              comp_assoc, Hg, id_left; reflexivity. }
    assert (Hfork : f ∘ q1 ≈ g ∘ q1).
    { rewrite Hq, Hq12; reflexivity. }
    destruct (eq_desc HE q1 Hfork) as [u Hu Huniq].
    unshelve refine {| unique_obj := u |}.
    + split.
      * exact Hu.
      * rewrite Hu; exact Hq12.
    + intros v [V1 V2]; apply Huniq; exact V1.
Qed.

(*
 THE BECK-CHEVALLEY LAW FOR P, [SplitCoequalizer]'s fourth field.  Both
 sides are transposes; [pow_precompose] and [curry_comp_l] reduce them
 to characteristic maps, [char_reindex] turns those into subobjects, and
 the two [bc_mono] applications meet at [mem_pow_square]. 

 --------
 贝克-谢瓦利定律对于 P，[SplitCoequalizer] 的第四个域。两边都是转置；[pow_precompose] 和 [curry_comp_l] 将它们化为特征映射，[char_reindex] 将那些映射转为子对象，而两个 [bc_mono] 的应用在 [mem_pow_square] 汇合。
*)
Theorem pow_bc {a b k : C} {f g : b ~> a} {e : k ~> b}
      (Mf : Monic f) (Me : Monic e) (HP : IsPullback f g k e e) :
  fmap[PowF] g ∘ ex_mono f Mf ≈ ex_mono e Me ∘ fmap[PowF] e.
Proof.
  unfold ex_mono.
  rewrite pow_precompose.
  transitivity (curry (char_sub (sub_push (second e) (second_Monic e Me)
                                   (pow_mem k)) ∘ first (fmap[PowF] e))).
  - apply curry_respects.
    rewrite <- !char_reindex.
    apply char_sub_respects.
    transitivity (sub_push (second e) (second_Monic e Me)
                    (sub_reindex (second e) (pow_mem b))).
    + exact (bc_mono (second_pullback HP (Pow b))
               (second_Monic f Mf) (second_Monic e Me) (pow_mem b)).
    + transitivity (sub_push (second e) (second_Monic e Me)
                      (sub_reindex (first (fmap[PowF] e)) (pow_mem k))).
      * apply sub_push_respects.
        symmetry.
        apply mem_pow_square.
      * symmetry.
        exact (bc_mono
                 (IsPullback_sym (first_second_pullback (fmap[PowF] e) e))
                 (second_Monic e Me) (second_Monic e Me) (pow_mem k)).
  - symmetry.
    apply curry_comp_l.
Qed.

(* * ** (E) The split coequalizer, and monadicity / * **（E）分裂共同余子对象，及单子性 *)

(*
 Contravariant functoriality of P, in the orientation the laws want:
 [P e ∘ P f] is [P (f ∘ e)], with both composites read in C.  Stated as
 a lemma because [Program] and [simpl] unfold [fmap[PowF]] to its
 [curry] normal form, after which [fmap_comp] no longer matches. 

 --------
 P 的逆变函子性，在定向下，定律要求：
 [P e ∘ P f] 是 [P (f ∘ e)]，两者的复合在 C 中读取。表述为引理是因为 [Program] 和 [simpl] 展开 [fmap[PowF] 到其 [curry] 的规范形式，之后 [fmap_comp] 不再匹配。
*)
Lemma pow_fmap_comp {a b k : C} (f : b ~> a) (e : k ~> b) :
  fmap[PowF] e ∘ fmap[PowF] f ≈ fmap[PowF] (f ∘ e).
Proof. symmetry; exact (@fmap_comp (C^op) C PowF a b k e f). Qed.

(*
 THE HEART OF THE ARGUMENT.  For a co-reflexive pair f, g : b ⇉ a with
 common retraction r, and any equalizer e of the pair, the P-images form
 a SPLIT coequalizer: the two direct images ∃_e and ∃_f are the two
 sections the record asks for, and its four laws are exactly
 functoriality, [pow_ex_mono] twice, and [pow_bc].  Co-reflexivity is
 spent in TWO places: both halves at [coreflexive_equalizer_pullback],
 which turns the equalizer into the pullback square Beck-Chevalley
 needs, and the retraction of f alone at [sections_are_monic], which
 makes f a mono so that the direct image ∃_f exists at all.

 Built with [unshelve refine] rather than [Program] deliberately: the
 obligation statements [Program] generates have [fmap[PowF]] unfolded to
 its [curry] normal form, and neither [fmap_comp] nor [pow_ex_mono] then
 matches. 

 --------
 论点的核心。对于一个具有共同收缩 r 的共反身对 f, g : b ⇉ a，以及该对的任意等化器 e，P-像形成了一个拆分余等化器：两个直接像 ∃_e 和 ∃_f 就是记录所要求的两个截面，它的四条定律恰好是函子性、[pow_ex_mono] 两次，以及 [pow_bc]。共反身性在两个地方使用：在 [coreflexive_equalizer_pullback] 的两部分，将等化器转化为 Beck-Chevalley 所需的拉回平方；以及仅在 [sections_are_monic] 的 f 的收缩，使 f 成为单射，从而直接像 ∃_f 的存在成为可能。

 刻意使用 [unshelve refine] 而不是 [Program]：由 [Program] 生成的义务声明将 [fmap[PowF] 展开为其 [curry] 正规形式，而 [fmap_comp] 和 [pow_ex_mono] 都不匹配。
*)
Definition pow_split_coequalizer
  {a b k : C} {f g : b ~> a} {r : a ~> b}
  (Hf : r ∘ f ≈ id) (Hg : r ∘ g ≈ id)
  {e : k ~> b} (HE : IsEqualizer f g k e) :
  SplitCoequalizer (fmap[PowF] f) (fmap[PowF] g).
Proof.
  unshelve refine {| scoeq_obj := Pow k
                   ; scoeq_e   := fmap[PowF] e
                   ; scoeq_s   := ex_mono e (equalizer_monic f g HE)
                   ; scoeq_t   := ex_mono f (@sections_are_monic C b a f
                                    {| section := r
                                     ; section_comp := Hf |}) |}.
  - (* law1: P e coforks the image pair / law1：P e 分叉图像对 *)
    rewrite !pow_fmap_comp.
    now rewrite (fork_eq HE).
  - (* law2: ∃_e splits P e / law2: 存在_e 分裂 P e *)
    apply pow_ex_mono.
  - (* law3: ∃_f splits P f / law3: 存在 _f 将 P f 分开 *)
    apply pow_ex_mono.
  - (* law4: Beck-Chevalley / law4：贝克-谢瓦利定律 *)
    apply (pow_bc _ _ (coreflexive_equalizer_pullback Hf Hg HE)).
Defined.

(*
 Crude monadicity's second hypothesis.  In C^op a reflexive pair is a
 CO-reflexive pair of C and a coequalizer is an equalizer, both
 definitionally; [IsEqualizer_op_of_IsCoequalizer] read at C^op is the
 field repackaging that makes the conversion available to [Monic e]
 through [equalizer_monic].  The obligation quantifies over ANY
 coequalizer of the pair, not a chosen one, and the argument is uniform
 in e. 

 --------
 粗单元性的第二个假设。在 C^op 中，一个自反对是一对 C 的 CO-自反对，并且一个余等化器是一个等化器，两者都是定义上的；在 C^op 中读取 [IsEqualizer_op_of_IsCoequalizer] 是一个字段重新打包，使得通过 [equalizer_monic] 将转换提供给 [Monic e]。这个义务量化了该对的任意余等化器，而不是选定的一个，并且该论证在 e 中是统一的。
*)
Definition pow_PreservesReflexiveCoequalizers :
  PreservesReflexiveCoequalizers PowF :=
  fun a b f g RP k e HC =>
    split_coequalizer_is_coequalizer _ _
      (pow_split_coequalizer (refl_section_f RP) (refl_section_g RP)
         (@IsEqualizer_op_of_IsCoequalizer (C^op) a b f g k e HC)).

(* The equivalence C^op ≃ EM(P ◯ P^op), CONSUMED from Crude.v. / 等价 C^op ≃ EM(P ◯ P^op)，从 Crude.v 消耗。 *)
Definition pow_equivalence :
  EquivalenceOfCategories (EM_Comparison pow_adjunction) :=
  crude_monadicity pow_adjunction op_HasReflexiveCoequalizers
    pow_PreservesReflexiveCoequalizers PowF_ReflectsIsos.

(* PARÉ'S THEOREM: the power-object functor is monadic. / 帕雷定理：幂对象函子是单子的。 *)
Definition power_object_monadic : Monadic PowF :=
  (Opposite_Functor PowF; (pow_adjunction; pow_equivalence)).

End ToposMonadic.
