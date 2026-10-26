(** * The finite-shape rows of the diagonal-adjoint table  / * 对角伴随表的有限形状行*)

(*
nLab:      https://ncatlab.org/nlab/show/equalizer
   nLab:      https://ncatlab.org/nlab/show/coequalizer
   nLab:      https://ncatlab.org/nlab/show/pullback
   nLab:      https://ncatlab.org/nlab/show/pushout
   nLab:      https://ncatlab.org/nlab/show/diagonal+functor
   Wikipedia: https://en.wikipedia.org/wiki/Equaliser_(mathematics)
   Wikipedia: https://en.wikipedia.org/wiki/Pullback_(category_theory)

   Mac Lane, “Categories for the Working Mathematician”, Springer GTM 5,
   2nd ed., §IV.2 (p. 90) tabulates a long list of adjunctions together
   with their units and counits, and Exercise 6 of that section asks for
   the entries of four of its rows: the equalizer, the coequalizer, the
   pullback and the pushout.  Each is an instance of the sandwich
   colim ⊣ Δ ⊣ lim at a FIXED finite shape --

     - the walking parallel pair (Instance/Parallel.v's [Parallel]): a
       limit over it is an equalizer, a colimit a coequalizer;
     - the walking cospan ([Roof^op], Structure/Span.v's [Cospan]): a
       limit over it is a pullback;
     - the walking span ([Roof], [Span]): a colimit over it is a pushout

   -- so the FUNCTORS come by instantiation.  The content of the exercise
   is the other column of the table: what the unit and the counit ARE,
   read as the elementary data those four words name.  Riehl, “Category
   Theory in Context”, Dover 2016, states the general form as Proposition
   4.6.1 with Exercise 4.6.ii asking for exactly this identification (the
   counit is the universal cone, the unit the universal cocone); Awodey,
   “Category Theory”, Oxford 2nd ed. 2010, runs the same argument for the
   special shapes in §9.3, and treats the four elementary universal
   properties themselves in §5.2 and §3.4.

   Read the four rows in the two variances and the pattern is visible:

     Δ[Parallel] ⊣ Eq      counit = the equalizing arrow (at ParX)
                           unit   = an isomorphism (see below)
     Coeq ⊣ Δ[Parallel]    unit   = the coequalizing arrow (at ParY)
                           counit = an isomorphism
     Δ[Roof^op] ⊣ Pb       counit = the two projections (at RNeg, RPos)
                           unit   = an isomorphism
     Po ⊣ Δ[Roof]          unit   = the two injections (at RNeg, RPos)
                           counit = an isomorphism

   THE “IDENTITY” ENTRIES ARE NOT IDENTITIES, AND THIS FILE DOES NOT
   CLAIM THEY ARE.  For Δ ⊣ lim the unit at x is a morphism
   x ~> lim(Δ[J](x)) -- an arrow between two DIFFERENT objects -- so
   [dia_unit L x = id[x]] is not merely false but ill-typed, which is
   measured below as a rejection of TYPING kind.  What is true, and is
   what the table's entry means, is that the unit is INVERTIBLE, with the
   limiting leg at a distinguished shape object as its inverse; that is
   [dia_unit_iso], and dually [dia_counit_iso].  Both hold over any shape
   satisfying the sufficient condition [ShapeLinked] introduced here, and
   all three finite shapes satisfy it. 

--------
nLab：https://ncatlab.org/nlab/show/equalizer
 nLab：https://ncatlab.org/nlab/show/coequalizer
 nLab：https://ncatlab.org/nlab/show/pullback
 nLab：https://ncatlab.org/nlab/show/pushout
 nLab：https://ncatlab.org/nlab/show/diagonal+functor
 维基百科：https://en.wikipedia.org/wiki/Equaliser_(mathematics)
 维基百科：https://en.wikipedia.org/wiki/Pullback_(category_theory)

Mac Lane，“工作数学家的类别”，Springer GTM 5，
 第二版，§IV.2（第 90 页）列出了一长串附加词
 及其单位和单位，该部分的练习 6 要求
 其四行的条目：均衡器、共均衡器、
 回调和推出。 每个都是三明治的一个实例
 colim ⊣ Δ ⊣ lim 处于固定有限形状 --

- 行走平行对（Instance/Parallel.v 的 [Parallel]）：a
 limit over it 是一个均衡器，colimit 是一个co均衡器；
 - 行走 cospan（[Roof^op]、Structure/Span.v 的 [Cospan]）：
 超过限制即为回调；
 - 步行跨度（[Roof]、[Span]）：超过它的 colimit 是推出

——所以 FUNCTORS 是通过实例化来的。 练习内容
 是表的另一列：单位和数量是什么，
 将这四个字的名称读作基本数据。 里尔，“类别
 语境中的理论”，Dover 2016，将一般形式表述为命题
 4.6.1 和练习 4.6.ii 要求准确地进行此识别（
 counit 是通用圆锥体，单位是通用圆锥体）； 阿沃迪，
 《范畴论》，牛津第二版。 2010 年，也提出了同样的论点
 §9.3 中的特殊形状，并处理四个基本通用
 §5.2 和 §3.4 中的属性本身。

读取两个方差中的四行，模式可见：

Δ[Parallel] ⊣ Eq counit = 均衡箭头（在 ParX）
 单位 = 同构（见下文）
 Coeq ⊣ Δ[Parallel] 单位 = 共均衡箭头（在 ParY）
 计数 = 同构
 Δ[Roof^op] ⊣ Pb 单位 = 两个投影（在 RNeg、RPos 处）
 单位 = 同构
 Po ⊣ Δ[Roof] 单位 = 两次进样（在 RNeg、RPos）
 计数 = 同构

“身份”条目不是身份，此文件也不是
 声称他们是。 对于 Δ ⊣ lim，x 处的单位是态射
 x ~> lim(Δ[J](x)) -- 两个不同对象之间的箭头 -- 所以
 [dia_unit L x = id[x]] 不仅错误而且类型错误，这是
 下面测量为打字类型的拒绝。 什么是真实的，什么是
 该表的条目意味着该单位是不可逆的，其中
 将腿限制在一个独特的形状对象上作为其反面； 那就是
 [dia_unit_iso] 和双 [dia_counit_iso]。 两者都可以容纳任何形状
 满足这里介绍的[ShapeLinked]的充分条件，并且
 所有三个有限形状都满足它。 
*)

(*
What is consumed here, and what is built

   CONSUMED, not rebuilt:

     - Adjunction/Diagonal/Limit.v, in full: [HasLimitsOfShape],
       [HasColimitsOfShape], [LimitFunctor], [ColimitFunctor],
       [Diagonal_Limit_Adjunction], [Colimit_Diagonal_Adjunction],
       [lim_counit], [colim_unit], [lim_counit_is_limit_leg],
       [colim_unit_is_colimit_inj], [lim_transpose_to],
       [lim_transpose_to_commutes], [colim_transpose_from],
       [colim_transpose_from_commutes], [Cocone_of], [lim_leg],
       [lim_med_eq], [colim_inj], [colim_med_eq], [colim_med_commutes],
       [colim_med_unique], [lim_leg_coherence], [colim_inj_coherence],
       [limits_iff_diagonal_right_adjoint],
       [colimits_iff_diagonal_left_adjoint], [Sets_HasLimitsOfShape],
       [Sets_HasColimitsOfShape], and its witness object [DiagBoolSet].
       Not one general limit or colimit result is re-proved; every row
       below is that file applied at a fixed shape.  The issue's
       Current-state section says “Adjunction/Diagonal/Product.v only
       covers the binary-product shape”; that is STALE, since
       Adjunction/Diagonal/Limit.v covers every shape.  A second entry of
       that section is stale differently: it lists Structure/Cocone.v
       among the in-tree donors, and NO SUCH FILE EXISTS -- [Cocone] and
       [ACocone] are declared in Structure/Cone.v, which is the donor
       actually consumed here.
     - Instance/Parallel.v: [Parallel], [ParObj], [ParX], [ParY],
       [ParOne], [APair].
     - Instance/Roof.v: [Roof], [RoofObj], [RNeg], [RZero], [RPos],
       [ZeroNeg], [ZeroPos], [IdZero], and the [roof_laws] hint database.
     - Structure/Span.v: [ASpan], [Span], [Cospan].
     - Structure/Equalizer.v: [Equalizer], [Coequalizer].
     - Structure/Equalizer/Fork.v: [IsEqualizer], [HasEqualizers],
       [fork_eq], [eq_desc], [equalizer_monic],
       [equalizer_is_equalizer].
     - Structure/Coequalizer.v: [IsCoequalizer], [HasCoequalizers],
       [cofork], [coeq_desc], [coequalizer_epic],
       [coequalizer_is_coequalizer].
     - Theory/Morphisms/Stability.v: [IsPullback], [is_pullback_commutes],
       [is_pullback_ump], [is_pullback_pullback], [pullback_is_pullback].
     - Structure/Pullback.v: [Pullback], [Pull], [HasPullbacks].
     - Structure/Pullback/Limit.v: [Pullback_to_Universal],
       [Pullback_Limit], [Pushout_Limit].
     - Structure/Pushout.v: [IsPushout], [pushout_apex], [HasPushouts].
     - Theory/Morphisms/CokernelPair.v: [IsPushoutSquare],
       [Build_IsPushoutSquare], [is_pushout_square_commutes],
       [is_pushout_square_ump], [is_pushout_square_pushout].
     - Theory/Morphisms.v: [Monic], [Epic], [monic], [epic].

   BUILT here:

     - The four rows: [EqualizerFunctor], [CoequalizerFunctor],
       [PullbackFunctor], [PushoutFunctor], each with its adjunction
       ([Diagonal_Equalizer_Adjunction], [Coequalizer_Diagonal_Adjunction],
       [Diagonal_Pullback_Adjunction], [Pushout_Diagonal_Adjunction]) and
       its named unit or counit.  Every statement is COVARIANT: no [^op]
       occurs in the type of the coequalizer or pushout row, and the
       [Roof^op] that occurs in the pullback row is the SHAPE, not a
       dualized ambient category.
     - The identifications the exercise asks for, against the ELEMENTARY
       APIs rather than the cone machinery: [eq_counit_IsEqualizer],
       [coeq_unit_IsCoequalizer], [pb_counit_IsPullback] and
       [po_unit_IsPushoutSquare].
     - Their packagings [HasLimitsOfShape_HasEqualizers],
       [HasColimitsOfShape_HasCoequalizers],
       [HasLimitsOfShape_HasPullbacks] and
       [HasColimitsOfShape_HasPushouts], so a consumer who has limits of
       one of these shapes gets the elementary class whose chosen arrow IS
       the counit (dually the unit) component.
     - [ShapeLinked] with [dia_unit_iso] and [dia_counit_iso]: the
       “identity” entries of the table, at their true strength.  Those
       three head a general constant-diagram development of ELEVEN
       constants over an arbitrary [J] and [C], the other eight being
       [lim_const_legs], [colim_const_injs], [dia_unit],
       [dia_unit_strict], [dia_unit_leg], [dia_counit],
       [dia_counit_strict] and [dia_counit_inj].  [ShapeLinked] itself
       carries only BOUNDS ([u0 <= u], [u1 <= u]) and no equation; the
       other ten, with the four obligations of the two [_iso] constants,
       are exactly the fourteen constants carrying [u0 = u2], as the
       universes section below records.
     - Four transports, [IsEqualizer_respects], [IsCoequalizer_respects],
       [IsPullback_respects] and [IsPushoutSquare_respects].  None of the
       three elementary records is stated up to [≈] in its distinguished
       arrow, and each is needed here at an arrow that differs by a unit
       residue from the one the tree's own conversions produce, so the
       transports are not optional.  The last of the four is the primal
       one read at [C^op] -- a [:=] with no tactic.
     - The pushout half of the shape/elementary bridge:
       [po_inj_commutes], [po_legs], [po_legs_coherence], [po_cocone],
       [po_inj_ump] and [po_inj_IsPushoutSquare].  THE TREE HAS THE
       PULLBACK BRIDGE AND NOT THE PUSHOUT ONE, measured:
       Structure/Pullback/Limit.v gives [Pullback_to_Universal], but its
       [Pushout_Limit] is a bare alias for [Colimit] with no
       conversion to any pushout universal property, and outside this file
       [IsPushoutSquare] occurs only in Theory/Morphisms/CokernelPair.v,
       its probe, and Instance/Sets/CokernelPair.v, none of which builds
       one from a colimit.  So the pullback row is REUSE and the pushout
       row is CONSTRUCTION, and the two are not symmetric in cost.
     - Four degenerate readings used by the witnesses:
       [equalizer_of_equal_pair], [coequalizer_of_equal_pair],
       [pullback_of_identity], [pushout_of_identity].
     - [ACospan], the cospan of a pair of morphisms as a diagram of shape
       [Roof^op].  It is [ASpan] in [C^op], opposed -- not a new functor:
       Structure/Pullback/Limit.v already writes that composite inline,
       and it is given a name here because three results need it.
     - The four biconditionals by instantiation, and the readbacks tying
       the two Roof rows to Structure/Span.v's [Span] and [Cospan] and the
       two Parallel rows to Structure/Equalizer.v's [Equalizer] and
       [Coequalizer], all at [eq_refl].

   NO EQUALIZER, COEQUALIZER, PULLBACK OR PUSHOUT FUNCTOR EXISTED IN THE
   TREE.  That absence was measured by the issue's author with a
   multi-line-aware sweep over the TYPES of every constant in the tree's
   802 [.v] files (803 with this one), finding seven constants whose name
   mentions one of those words and whose type contains [⟶], in all seven
   of which the [⟶] is in an ARGUMENT
   (a diagram [Parallel ⟶ C]) rather than in the constant's own type.  A
   first run of that sweep reported SIX: it keyed on
   [Definition|Theorem|Lemma|Instance] and so missed
   [Structure/Coequalizer/Split.v]'s [split_coequalizer_preserved],
   which is declared with [Corollary].  Widening the keyword list is what
   yields seven, and the characterization is unchanged by it -- that
   constant's own type is an [IsCoequalizer], its [F : C ⟶ D] being an
   argument.  The
   check re-run here is weaker and only corroborating: a name sweep for a
   [Definition] or [Program Definition] called [EqualizerFunctor],
   [CoequalizerFunctor], [PullbackFunctor] or [PushoutFunctor] returns
   nothing outside this file. 

--------
这里消耗了什么，建造了什么

已消耗，未重建：

- Adjunction/Diagonal/Limit.v，完整：[HasLimitsOfShape]，
 [HasColimitsOfShape]、[LimitFunctor]、[ColimitFunctor]、
 [Diagonal_Limit_Adjunction]、[Colimit_Diagonal_Adjunction]、
 XPTECT6X、[colim_unit]、[lim_counit_is_limit_leg]、
 XPTECT9X、[lim_transpose_to]、
 [lim_transpose_to_commutes]、[colim_transpose_from]、
 XPTECT13X、[Cocone_of]、[lim_leg]、
 [lim_med_eq]、[colim_inj]、[colim_med_eq]、[colim_med_commutes]、
 [colim_med_unique]、[lim_leg_coherence]、[colim_inj_coherence]、
 [limits_iff_diagonal_right_adjoint]，
 [colimits_iff_diagonal_left_adjoint]、[Sets_HasLimitsOfShape]、
 [Sets_HasColimitsOfShape] 及其见证对象 [DiagBoolSet]。 没有重新证明任何一般极限或共同极限结果； 每行
 下面是应用在固定形状的文件。 问题的
 当前状态部分显示“仅 Adjunction/Diagonal/Product.v
 覆盖二元产品形状”； 这是陈旧的，因为
 Adjunction/Diagonal/Limit.v 涵盖了所有形状。
第二个条目
 该部分已经过时了：它列出了 Structure/Cocone.v
 在树内捐赠者中，并且不存在这样的文件 - [Cocone] 和
 [ACocone] 在 Structure/Cone.v 中声明，它是捐赠者
 实际消费在这里。 - 实例/并行.v：[Parallel]、[ParObj]、[ParX]、[ParY]、
 [ParOne]、[APair]。 - 实例/屋顶.v：[Roof]、[RoofObj]、[RNeg]、[RZero]、[RPos]、
 [ZeroNeg]、[ZeroPos]、[IdZero] 和 [roof_laws] 提示数据库。 - 结构/Span.v：[ASpan]、[Span]、[Cospan]。 - 结构/均衡器.v：[Equalizer]、[Coequalizer]。 - 结构/均衡器/前叉.v：[IsEqualizer]、[HasEqualizers]、
 XPTECT52X、[eq_desc]、[equalizer_monic]、
 [equalizer_is_equalizer]。 - 结构/辅助均衡器.v：[IsCoequalizer]、[HasCoequalizers]、
 XPTECT58X、[coeq_desc]、[coequalizer_epic]、
 [coequalizer_is_coequalizer]。
- 理论/态射/稳定性.v：[IsPullback]、[is_pullback_commutes]、
 XPTECT64X、[is_pullback_pullback]、[pullback_is_pullback]。 - 结构/回调.v：[Pullback]、[Pull]、[HasPullbacks]。 - 结构/回调/限制.v：[Pullback_to_Universal]，
 [Pullback_Limit]、[Pushout_Limit]。 - 结构/推出.v：[IsPushout]、[pushout_apex]、[HasPushouts]。 - 理论/态射/CokernelPair.v：[IsPushoutSquare]，
 [Build_IsPushoutSquare]、[is_pushout_square_commutes]、
 [is_pushout_square_ump]、[is_pushout_square_pushout]。 - 理论/态射.v：[Monic]、[Epic]、[monic]、[epic]。

建在这里：

- 四行：[EqualizerFunctor]、[CoequalizerFunctor]、
 [PullbackFunctor]、[PushoutFunctor]，各有其附件
 （[Diagonal_Equalizer_Adjunction]、[Coequalizer_Diagonal_Adjunction]、
 [Diagonal_Pullback_Adjunction]、[Pushout_Diagonal_Adjunction]) 和
 它的命名单位或单位。 每个语句都是 COVARIANT：没有 [^op]
 发生在 coequalizer 或 pushout row 的类型中，并且
 出现在回拉行中的 [Roof^op] 是 SHAPE，而不是
 二元环境类别。 - 练习要求的识别信息，针对 Elementary
 API 而不是锥体机械：[eq_counit_IsEqualizer]，
 [coeq_unit_IsCoequalizer]、[pb_counit_IsPullback] 和
 XPTECT98X。 - 他们的包装 [HasLimitsOfShape_HasEqualizers]，
 [HasColimitsOfShape_HasCoequalizers]，
 [HasLimitsOfShape_HasPullbacks] 和
 [HasColimitsOfShape_HasPushouts]，因此有限制的消费者
 这些形状之一获得其选择的箭头是的基本类
 counit（双重单位）组件。
- [ShapeLinked] 与 [dia_unit_iso] 和 [dia_counit_iso]：
 表中的“身份”条目，展现出它们的真正实力。 那些
 三头一般常图发展十一
 任意 [J] 和 [C] 上的常数，其他八个是
 [lim_const_legs]、[colim_const_injs]、[dia_unit]、
 [dia_unit_strict]、[dia_unit_leg]、[dia_counit]、
 [dia_counit_strict] 和 [dia_counit_inj]。 [ShapeLinked] 本身
 仅包含 BOUNDS ([u0 <= u]、[u1 <= u])，没有方程； 的
 其他十个，具有两个 [_iso] 常量的四个义务，
 正是携带 [u0 = u2] 的十四个常数，如
 记录下面的宇宙部分。 - 四种传输，[IsEqualizer_respects]，[IsCoequalizer_respects]，
 [IsPullback_respects] 和 [IsPushoutSquare_respects]。
没有一个
 [≈] 在其杰出的版本中规定了三个基本记录
 箭头，这里每个箭头都需要一个单位不同的箭头
 树自身转换产生的残留物，所以
 运输不是可选的。 四个中的最后一个是原始的
 有人读过 [C^op]——一款没有策略的 [:=]。 - 形状/基本桥的推出一半：
 [po_inj_commutes]、[po_legs]、[po_legs_coherence]、[po_cocone]、
 [po_inj_ump] 和 [po_inj_IsPushoutSquare]。
这棵树有
 拉式桥而不是推式桥，测量：
 Structure/Pullback/Limit.v 提供 [Pullback_to_Universal]，但其
 [Pushout_Limit] 是 [Colimit] 的裸别名，没有
 转换为任何推出通用属性，并在此文件之外
 [IsPushoutSquare] 仅出现在 Theory/Morphisms/CokernelPair.v 中，
 它的探针和 Instance/Sets/CokernelPair.v，都没有构建
 来自 colimit 的一个。 所以回拉行是REUSE，推出行是REUSE
 row 是 CONSTRUCTION，两者在成本上并不对称。 - 证人使用的四种简陋读法：
 XPTECT138X、[coequalizer_of_equal_pair]、
 XPTECT140X、[pushout_of_identity]。 - [ACospan]，一对态射的余跨作为形状图
 [Roof^op]。
它是 [C^op] 中的 [ASpan]，相反——不是一个新函子：
 Structure/Pullback/Limit.v 已经写了复合内联，
 在这里给它一个名字是因为三个结果需要它。 - 四个双条件的实例化和回读绑定
 Structure/Span.v 的 [Span] 和 [Cospan] 的两行屋顶以及
 Structure/Equalizer.v 的 [Equalizer] 的两个平行行和
 [Coequalizer]，全部在 [eq_refl]。

不存在均衡器、共均衡器、回拉或推出功能
 树。 该问题的作者用以下指标来衡量缺席情况：
 多行感知扫描树中每个常量的类型
 802 个 [.v] 文件（803 个），找到 7 个常量，其名称
 在所有七个单词中提到其中一个单词，其类型包含 [⟶]
 其中 [⟶] 位于 ARGUMENT 中
 （如图[Parallel ⟶ C]）而不是在常量自己的类型中。 一个
 该扫描的第一次运行报告了六：它关键了
 [Definition|Theorem|Lemma|Instance] 等错过了
 [Structure/Coequalizer/Split.v] 的 [split_coequalizer_preserved]，
 这是用 [Corollary] 声明的。 扩大关键词列表是什么
 产生七，并且特征没有因此改变——即
 常量自己的类型是 [IsCoequalizer]，其 [F : C ⟶ D] 是
 论点。 的
 此处重新运行的检查较弱，仅证实：对 a 的名称扫描
 [Definition] 或 [Program Definition] 称为 [EqualizerFunctor]，
 [CoequalizerFunctor]、[PullbackFunctor] 或 [PushoutFunctor] 返回
 该文件之外没有任何内容。 
*)

(*
Strengths, measured strict-first

   THIRTY-THREE identifications hold at Leibniz [eq] and are shipped as
   [eq_refl] Examples -- every [Example] in the file is one.  The ones
   worth knowing:

     - the unit of Δ ⊣ lim IS the transpose of the identity
       ([dia_unit_strict]), and dually the counit of colim ⊣ Δ IS the
       transpose of the identity ([dia_counit_strict]);
     - each row's unit or counit IS the general one
       ([eq_row_counit], [coeq_row_unit], [pb_row_counit],
       [po_row_unit]);
     - each row functor's object action IS the (co)limit object
       ([EqualizerFunctor_obj] and its three siblings);
     - the chosen apex of each derived elementary class IS the (co)limit
       object ([HasEqualizers_apex] and its three siblings);
     - the six counit/unit components of the four rows (1+1+2+2) are
       the six legs with a unit residue ([eq_arrow_strict],
       [coeq_arrow_strict], [pb_fst_strict], [pb_snd_strict],
       [po_in1_strict], [po_in2_strict]);
     - the legs of [ACospan f g] and [ASpan f g] ARE f and g
       ([acospan_left], [acospan_right], [aspan_left], [aspan_right]);
     - the two Roof-indexed functor categories' objects ARE [Cospan C]
       and [Span C], and all four shape hypotheses ARE the tree's own
       aliases ([pullback_shape_hypothesis] and its three siblings).

   [pb_leg_IsPullback] is not an [eq_refl] but is the same kind of fact:
   it is Structure/Pullback/Limit.v's [Pullback_to_Universal] read through
   the apex-pinned predicate, supplied by [:=] WITH NO TACTIC, so the
   limit apex and both limiting legs land on the pullback's apex and
   projections by conversion alone.

   SEVEN strict attempts were made and REJECTED.  Every one was verified
   by STRIPPING the guard and reading the whole error; [Fail]'s own
   message is INVISIBLE under this repository's [coqc] invocation (a
   [Fail] command that succeeds prints nothing at all), so reading the
   stripped error is the only way to learn the failure kind here.  Six are
   CONVERSION failures (“cannot unify”) and one is a TYPING failure; each
   is stated so it can be pinned as a probe.

     R1. [eq_arrow L F = lim_leg L F ParX] -- the counit component carries
         a residual [∘ id]; the control at [lim_leg L F ParX ∘ id]
         succeeds.  This is Adjunction/Diagonal/Limit.v's own rejection R1
         instantiated at [Parallel], not a new phenomenon.
     R2. [coeq_arrow M F = colim_inj M F ParY] -- dually, an [id ∘]
         residue; control at [id ∘ colim_inj M F ParY].
     R3. [pb_fst P F = lim_leg P F RNeg] -- as R1 at [Roof^op].
     R4. [pushout_inj1 Q F = colim_inj Q F RNeg] -- as R2 at [Roof].
     R5. [dia_unit L x = id[x]] -- a TYPING failure, and the sharpest
         measurement in the file: the two sides have codomains
         [lim_obj L (Δ[J](x))] and [x], so the table's “unit = identity”
         entry is not a proposition one can even state at [eq].  What
         replaces it is [dia_unit_iso].
     R6. [Opposite Roof = Roof] -- the walking span is not its own
         opposite on the nose, which is why the pullback and pushout rows
         are two separate sections over two different shapes rather than
         one section read twice.
     R7. [Opposite Parallel = Parallel] -- likewise for the walking
         parallel pair; the equalizer and coequalizer rows share a SHAPE
         but not a variance, and it is [Colimit F := Limit (F^op)] that
         dualizes, not the shape.

   A NOTATION HAZARD BIT WHILE MEASURING R6 AND R7, AND IT PRODUCED A
   FALSE PASS.  Written [Roof^op = Roof], the negative fails with “The
   term Roof has type Category while it is expected to have type ?C ⟶ ?D”
   -- Functor/Opposite.v opens [functor_scope], and in the argument of an
   [eq] there is no expected type for [Bind Scope category_scope with
   Category] to rescue, so [^op] parses as the FUNCTOR opposite and the
   command fails on notation rather than on the mathematics.  Both
   negatives must be spelled [Opposite Roof] and [Opposite Parallel].
   Inside the file the same [Roof^op] is harmless, every occurrence
   sitting in an argument or ascription position whose expected type is
   [Category]. 

--------
优势，严格优先衡量

Leibniz [eq] 拥有三十三个标识，并作为
 [eq_refl] 示例——文件中的每个 [Example] 都是一个。 那些
 值得了解：

- Δ ⊣ lim 的单位是恒等式的转置
 ([dia_unit_strict])，并且 colim ⊣ Δ 的对偶单位是
 身份转置（[dia_counit_strict]）；
 - 每行的单位或数量是通用的
 （[eq_row_counit]、[coeq_row_unit]、[pb_row_counit]、
 [po_row_unit]）；
 - 每行函子的对象动作是（co）限制对象
 （[EqualizerFunctor_obj] 及其三个兄弟姐妹）；
 - 每个派生基本类的选定顶点是（共同）极限
 对象（[HasEqualizers_apex] 及其三个兄弟）；
 - 四行 (1+1+2+2) 的六个单位/单位分量是
 具有单位残基的六个腿（[eq_arrow_strict]，
 [coeq_arrow_strict]、[pb_fst_strict]、[pb_snd_strict]、
 XPTECT15X、[po_in2_strict]）；
 - [ACospan f g] 和 [ASpan f g] 的腿为 f 和 g
 （[acospan_left]、[acospan_right]、[aspan_left]、[aspan_right]）；
 - 两个 Roof 索引函子类别的对象是 [Cospan C]
 和 [Span C]，所有四种形状假设都是树自己的
 别名（[pullback_shape_hypothesis] 及其三个兄弟）。

[pb_leg_IsPullback] 不是 [eq_refl]，但事实相同：
 它是 Structure/Pullback/Limit.v 的 [Pullback_to_Universal] 通读
 顶点固定谓词，由 [:=] 提供，没有策略，所以
 限制顶点并且两个限制腿都落在回撤的顶点上并且
 仅通过转换进行预测。

进行了七次严格的尝试并被拒绝。 每一项都经过验证
 通过剥离防护装置并读取整个错误； [Fail] 自己的
 在此存储库的 [coqc] 调用下消息是不可见的（a
 成功的 [Fail] 命令根本不打印任何内容），因此读取
 剥离错误是了解此处失败类型的唯一方法。 六个是
 转换失败（“无法统一”），其中之一是打字失败； 每个
 已说明，因此可以将其固定为探针。

R1。 [eq_arrow L F = lim_leg L F ParX]——单元组件携带
 剩余的 [∘ id]； [lim_leg L F ParX ∘ id] 的控制
 成功了。 这是Adjunction/Diagonal/Limit.v自己的拒绝R1
 在 [Parallel] 上实例化，这并不是一个新现象。 
R2。 [coeq_arrow M F = colim_inj M F ParY]——双重，[id ∘]
 残留物； [id ∘ colim_inj M F ParY] 上的控制。 
R3。 [pb_fst P F = lim_leg P F RNeg]——作为 [Roof^op] 的 R1。 
R4。 [pushout_inj1 Q F = colim_inj Q F RNeg]——作为 [Roof] 的 R2。 
R5。 [dia_unit L x = id[x]]——打字失败，最尖锐的
 文件中的测量：两侧有共域
 [lim_obj L (Δ[J](x))] 和 [x]，因此表的“单位 = 标识”
 进入甚至不是一个可以在 [eq] 上陈述的命题。 什么
 取代它的是 [dia_unit_iso]。 
R6。 [Opposite Roof = Roof]——行走跨度不是自己的
 与鼻子相反，这就是拉回和推出行的原因
 是两个不同形状的两个独立部分，而不是
 一节读两遍。 
R7。 [Opposite Parallel = Parallel]——同样适合步行
 平行对； 均衡器和辅助均衡器行共享一个 SHAPE
 但不是差异，[Colimit F := Limit (F^op)]
 二元化，而不是形状。

测量 R6 和 R7 时的符号危险位，它产生了
 错误通过。 写 [Roof^op = Roof]，否定失败，并显示“The
 术语 Roof 具有类别类型，而预期具有类型 ?C ⟶ ?D“
 -- Functor/Opposite.v 打开 [functor_scope]，并在一个参数中
 [eq] [Bind Scope Category_scope with 没有预期的类型
 Category] 来救援，因此 [^op] 解析为相反的 FUNCTOR 和
 命令在符号上失败，而不是在数学上失败。 两者都
 底片必须拼写为 [Opposite Roof] 和 [Opposite Parallel]。 
在文件内，每次出现相同的 [Roof^op] 都是无害的
 坐在预期类型为的论证或归属位置
 [Category]。 
*)

(*
Universes, measured off BOTH the binder and the constraint block

   Every [Category@{...}] occurrence in the file -- 119 of them, swept
   over the printed signatures of all 140 constants -- identifies the hom
   universe with the proof universe.  That is entirely the donors' doing,
   and the attribution is probed rather than assumed: in a section
   declaring [Universes uo uh up] with [Constraint uh < up], NINE donors
   are each rejected ALONE with “Cannot enforce up = uh” --
   [HasLimitsOfShape], [Limit], [Diagonal], [Fun] (as [[Parallel, D]]),
   [Opposite], [IsEqualizer], [IsCoequalizer], [IsPullback] and
   [IsPushoutSquare].  At most EIGHT of the nine are independent:
   [HasLimitsOfShape] is defined as [∀ F, Limit F], so its rejection does
   not discriminate against [Limit]'s.  Meanwhile the hom type
   [x ~{D}~> y], the identity
   [id[x]] AND [Cone] are all ACCEPTED at those very levels.  The [Cone]
   control is what makes the attribution discriminate: the cone RECORD is
   innocent, so “the cone vocabulary” would be the wrong cause.  Nothing
   in this file adds to the identification, and none of it is claimed
   unavoidable.

   FOURTEEN constants carry a universe EQUATION, all of them [u0 = u2],
   and they are exactly the two GENERIC constant-diagram sections:
   [lim_const_legs], [colim_const_injs], [dia_unit], [dia_unit_strict],
   [dia_unit_leg], [dia_unit_iso] with its two obligations, and the five
   [dia_counit] counterparts.  The equation identifies the shape's
   hom-and-proof universe with the ambient category's; it is INHERITED
   from Adjunction/Diagonal/Limit.v, whose header records exactly [u0 = u2]
   for [LimitFunctor] and its neighbours, and whose binder-versus-block
   disagreement is inherited too -- [dia_unit]'s binder reads
   [{J : Category@{u u0 u0}} {C : Category@{u1 u2 u2}}], which looks as
   though the two hom levels are independent, while the block carries
   [u0 = u2].

   THE FOUR ROW SECTIONS CARRY NO UNIVERSE EQUATION AT ALL.  Their blocks
   are bounds only.  Read that at its true strength, which is smaller than
   it looks: nothing is thereby made more general.  The identification the
   general theorem records as an equation is DISCHARGED BY INSTANTIATION
   -- the row constants read [Parallel@{u3 u0}] and [Roof@{u3 u0}], taking
   C's hom universe as the shape's own -- which they may do because both
   shapes are universe-polymorphic with an EMPTY constraint block
   ([Parallel@{u u0} : Category@{u u0 u0}] and likewise [Roof], measured).
   What a consumer gains is only that no equation between two categories
   THEY declared ever appears.

   Neither finite shape carries [Set].  This is worth saying because the
   degenerate rows of the same table do: Adjunction/Diagonal/Limit.v
   records that [_0]'s own signature is [Category@{u Set Set}], so its
   empty-shape corollaries inherit a [Set] pin.  [Parallel] and [Roof] do
   not, and so neither does any general result below.

   TWENTY constants carry the literal [Set], and they are exactly the
   concrete [Sets] witness block, from [SetsConstTrue] onwards.  The token
   appears in universe INSTANCES in the signature ([Sets@{Set u}],
   [DiagBoolSet@{u Set}]); the only [Set] in any constraint BLOCK is the
   bound [Set < u].  The cause is the two-element carrier: [DiagBoolSet]
   is itself polymorphic ([DiagBoolSet@{u u0} : obj[Sets@{u0 u}]], no
   [Set] in its binder), and it is universe MINIMIZATION at the use site
   that instantiates its relation universe at [Set].  The obvious
   alternative explanation is ruled out by a control: this tree records a
   hazard by which a [Sets]-morphism whose [proper_morphism] is left to
   instance resolution pins the carrier universe, with the repair being to
   supply the certificate as an explicit pointwise term -- BOTH forms were
   compiled here and BOTH give the identical [Sets@{Set u}], so the
   resolution hazard is not what is happening.  A third variant, the same
   morphism inside a section declaring [Constraint Set < o], elaborates at
   [Sets@{o so}] with [Set] appearing only as a strict lower bound, so the
   pin is liftable.  It is NOT lifted here: the witness block is a
   witness, and Adjunction/Diagonal/Limit.v's own [Sets] witness carries
   the same [Set < u].  Not claimed unavoidable.

   The four [Sets_*] adjunctions and the four [Sets_Has*] classes are
   [Set]-FREE -- the pin begins only where [bool] does. 

--------
宇宙，从粘合剂和约束块上测量

文件中出现的每个 [Category@{...}] —— 其中 119 个，被扫描
 在所有 140 个常量的打印签名上——识别 hom
 宇宙与证明宇宙。 这完全是捐助者做的，
 并且归因是探查的而不是假设的：在一个部分中
 宣布 [Universes uo uh up] 与 [Constraint uh < up]、九个捐赠者
 均被单独拒绝，并显示“无法强制执行 = 呃”——
 [HasLimitsOfShape]、[Limit]、[Diagonal]、[Fun]（如 [[Parallel, D]]）、
 [Opposite]、[IsEqualizer]、[IsCoequalizer]、[IsPullback] 和
 [IsPushoutSquare]。 九个中最多八个是独立的：
 [HasLimitsOfShape] 被定义为 [∀ F, Limit F]，因此它的拒绝不会
 不歧视 [Limit]。 同时 hom 类型
 [x ~{D}~> y]，身份
 [id[x]] 和 [Cone] 在这些级别上都被接受。 [Cone]
 控制是使归因具有区分性的原因：锥体 RECORD 是
 无辜的，所以“圆锥词汇”将是错误的原因。 什么都没有
 在这个文件中添加了身份证明，并且没有一个被声明
 不可避免的。

十四个常数带有一个宇宙方程，全部是 [u0 = u2]，
 它们正是两个通用常量图部分：
 [lim_const_legs]、[colim_const_injs]、[dia_unit]、[dia_unit_strict]、
 [dia_unit_leg]、[dia_unit_iso] 及其两项义务和五项义务
 [dia_counit]对应。 该方程确定了形状的
 与环境类别的 hom-and-proof 宇宙； 它是遗传的
 来自 Adjunction/Diagonal/Limit.v，其标头准确记录了 [u0 = u2]
 对于 [LimitFunctor] 及其邻居，以及其绑定器与块
 分歧也会遗传——[dia_unit] 的活页夹上写着
 [{J : Category@{u u0 u0}} {C : Category@{u1 u2 u2}}]，看起来像
 虽然两个 hom 级别是独立的，但块承载
 [u0 = u2]。

四行部分根本不包含宇宙方程。 他们的街区
 仅是界限。 阅读它的真实强度，该强度小于
 看起来：没有什么因此变得更加普遍。 鉴定的
 一般定理记录为方程，通过实例化释放
 -- 行常量读取 [Parallel@{u3 u0}] 和 [Roof@{u3 u0}]，取
 C 的 hom 宇宙作为形状自己的宇宙——他们可能会这样做，因为两者
 形状是具有空约束块的宇宙多态性
 （[Parallel@{u u0} : Category@{u u0 u0}] 和 [Roof] 同样进行测量）。 
消费者得到的只是两个类别之间不存在等式
 他们宣称曾经出现过。

两种有限形状都没有携带 [Set]。 这一点值得一说，因为
 同一个表的退化行执行：Adjunction/Diagonal/Limit.v
 记录[_0]自己的签名是[Category@{u Set Set}]，所以它的
 空形状推论继承了 [Set] 引脚。 [Parallel] 和 [Roof] 可以
 不是，所以下面的一般结果也不是。

二十个常量带有文字 [Set]，它们正是
 混凝土 [Sets] 见证块，从 [SetsConstTrue] 开始。 代币
 出现在签名中的 Universe INSTANCES 中（[Sets@{Set u}]，
 [DiagBoolSet@{u Set}]）； 任何约束块中唯一的 [Set] 是
 绑定 [Set < u]。 原因是二元载体：[DiagBoolSet]
 本身是多态的（[DiagBoolSet@{u u0} : obj[Sets@{u0 u}]]，没有
 [Set] 在其活页夹中），并且在使用现场是宇宙最小化
 在 [Set] 实例化其关系域。
显而易见的
 另一种解释被控件排除：这棵树记录了
 [Sets] 态射的 [proper_morphism] 留下的危险
 实例解析固定载体宇宙，修复是
 提供证书作为明确的逐点术语——两种形式都是
 在这里编译并且两者都给出相同的 [Sets@{Set u}]，所以
 解决风险并不是正在发生的事情。 第三种变体，相同
 声明 [Constraint Set < o] 的部分内的态射，详细说明于
 [Sets@{o so}] 和 [Set] 仅作为严格的下界出现，因此
 销钉是可抬起的。 这里没有被解除：见证人块是
 见证人，以及 Adjunction/Diagonal/Limit.v 自己的 [Sets] 见证人携带
 相同的 [Set < u]。 不主张不可避免。

四个 [Sets_*] 附件和四个 [Sets_Has*] 类别是
 [Set]-FREE——引脚仅从 [bool] 所在的位置开始。 
*)

(*
Non-vacuity

   All four rows are inhabited at [Sets], which is both complete and
   cocomplete in tree: [Sets_Diagonal_Equalizer_Adjunction],
   [Sets_Coequalizer_Diagonal_Adjunction],
   [Sets_Diagonal_Pullback_Adjunction] and
   [Sets_Pushout_Diagonal_Adjunction], with the four elementary classes
   [DiagSets_HasEqualizers], [DiagSets_HasCoequalizers],
   [Sets_HasPullbacks_of_shape] and [Sets_HasPushouts_of_shape] falling
   out of the rows.

   That the witnesses are not degenerate is PROVED, in two senses and for
   all four rows.  First, the diagrams are not constant: each is built
   from [SetsConstTrue], the constant map at [true] on the two-element
   discrete setoid, and [SetsPairDiagram_not_constant],
   [SetsCospanDiagram_not_constant] and [SetsSpanDiagram_not_constant]
   show that the arrow the diagram carries is not an identity (each is
   [sets_const_true_not_id] by conversion, the conversion itself pinned by
   [sets_pair_arrow_strict] and its two siblings).  A constant diagram
   sends every arrow to an identity, so none of the three is one.  Second,
   the four objects produced are not subsingletons:
   [sets_equalizer_two_elements], [sets_coequalizer_two_elements],
   [sets_pullback_two_elements] and [sets_pushout_two_elements] each
   exhibit two elements that are provably not [≈]-equal.  The two elements
   are obtained by transporting [true] and [false] backwards along the
   four isomorphisms [sets_equalizer_iso], [sets_coequalizer_iso],
   [sets_pullback_iso] and [sets_pushout_iso], and the separation is
   discharged by [discriminate] on the underlying [bool]; no induction on
   a (co)limit construction could yield a negative.  Those four
   isomorphisms are not assumed either -- each is an instance of one of
   the four degenerate readings, so what is computed is the equalizer of a
   pair whose legs agree, the pullback of a cospan one of whose legs is an
   identity, and their duals.

   The route the witnesses do NOT take is worth naming: they use the
   UNIVERSAL PROPERTY, not the construction, so nothing here computes the
   compatible-family setoid of Instance/Sets/Complete.v or the inductive
   quotient of Instance/Sets/Cocomplete.v.  No [eq_refl] below evaluates a
   (co)limit element. 

--------
非空性

所有四行都位于 [Sets]，既完整又完整
 树中的共同完成：[Sets_Diagonal_Equalizer_Adjunction]，
 [Sets_Coequalizer_Diagonal_Adjunction]，
 [Sets_Diagonal_Pullback_Adjunction] 和
 [Sets_Pushout_Diagonal_Adjunction]，包含四个基本类
 [DiagSets_HasEqualizers]、[DiagSets_HasCoequalizers]、
 [Sets_HasPullbacks_of_shape] 和 [Sets_HasPushouts_of_shape] 下降
 出行。

证人并未堕落，这在两个意义上得到了证明：
 所有四行。 首先，图表不是恒定的：每个图表都是构建的
 来自 [SetsConstTrue]，两元素上 [true] 的常量映射
 离散集合体和 [SetsPairDiagram_not_constant]，
 [SetsCospanDiagram_not_constant] 和 [SetsSpanDiagram_not_constant]
 表明该图所带有的箭头不是一个恒等式（每个都是
 [sets_const_true_not_id] 通过转换，转换本身由
 [sets_pair_arrow_strict] 及其两个兄弟姐妹）。 常数图
 将每个箭头发送到一个身份，因此这三个箭头都不是一个。 第二，
 生成的四个对象不是子单例：
 [sets_equalizer_two_elements]、[sets_coequalizer_two_elements]、
 [sets_pullback_two_elements] 和 [sets_pushout_two_elements] 各
 表现出两个可证明不等于 [≈] 的元素。
两个要素
 通过沿 [true] 和 [false] 向后传输
 四种同构 [sets_equalizer_iso]、[sets_coequalizer_iso]、
 [sets_pullback_iso] 和 [sets_pushout_iso]，分离度为
 由 [discriminate] 在底层 [bool] 上放电； 没有感应
 （共）极限构造可能会产生负值。 那四个人
 也不假定同构——每个都是以下之一的实例
 四个简并读数，因此计算的是 a 的均衡器
 一对腿一致的 cospan 的回拉，其中一条腿是
 身份，以及他们的双重身份。

目击者不采取的路线值得一提：他们使用
 通用属性，而不是构造，所以这里没有任何内容计算
 Instance/Sets/Complete.v 的兼容系列 setoid 或归纳式
 Instance/Sets/Cocomplete.v 的商。 下面没有 [eq_refl] 评估
 （共）极限元素。 
*)

(*
What is NOT delivered

     - THE FOUR [Sets]-LEVEL CLASSES ARE SECOND INHABITANTS, AND NO
       AGREEMENT WITH THE FIRST IS CLAIMED.  Each of
       [DiagSets_HasEqualizers], [DiagSets_HasCoequalizers],
       [Sets_HasPullbacks_of_shape] and [Sets_HasPushouts_of_shape]
       duplicates a pre-existing inhabitant of its class --
       [Adjunction/GAFT/Sets.v]'s [Sets_HasEqualizers],
       [Instance/Sets/Coequalizer.v]'s [Sets_HasCoequalizers],
       [Instance/Sets/Pullback.v]'s [Sets_HasPullbacks] and
       [Instance/Sets/Pushout.v]'s [Sets_HasPushouts].  The four
       built here come from the general theorem applied to
       [Sets_HasLimitsOfShape]; the four pre-existing ones are direct
       constructions.  NOTHING relates the two -- no isomorphism, no
       [≈], not even a comparison of chosen apexes -- so these are a
       second route to the same classes and not an identification of
       the tree's own objects.  The names differ deliberately, and the
       four here are plain [Definition]s rather than [Instance]s, so
       the pre-existing exported instances still win every resolution.
     - NO CONVERSE for any of the four packagings.  Nothing builds
       [HasLimitsOfShape Parallel C] from [HasEqualizers C], nor any of
       the other three directions.  The obstruction is real rather than
       neglect: the elementary classes quantify over PAIRS and SPANS,
       whose diagrams are [APair f g], [ASpan f g] and [ACospan f g], and
       a general [F : Parallel ⟶ C] is not one of those records on the
       nose; transporting a limit along an isomorphism of diagrams is not
       attempted and no such transport is used.  So each [Has*] result
       here runs one way only.  CORRECTION (#477): accurate when written;
       for the coequalizer row a converse now exists outside this file.
       Structure/Coequalizer.v's [HasCoequalizers_HasColimitsOfShape]
       builds a colimit of every [F : Parallel ⟶ C] from
       [HasCoequalizers C], its type being [HasColimitsOfShape Parallel C]
       by δ (Test/ProbeAbsolute477.v, C31), and it identifies F with no
       [APair] record: it takes the elementary coequalizer of the pair F
       names, the images of the two arrows, and reads the colimiting
       cocone off it.  The equalizer, pullback and pushout rows still
       have no converse.
     - No uniqueness for any of the four functors.  [left_adjoint_iso] and
       [right_adjoint_iso] are not instantiated, so nothing says
       [EqualizerFunctor] is THE right adjoint of [Δ[Parallel]] up to
       natural isomorphism, and the four biconditionals assert only the
       EXISTENCE of an adjoint, not that it is the one named.
     - No naturality for any identification.  [eq_counit_IsEqualizer] and
       its three siblings are statements about one diagram at a time;
       nothing exhibits the assignment as natural in the diagram, and
       there is no comparison of the four elementary APIs as functors.
     - Nothing about preservation, reflection or creation of these four
       shapes, and no instantiation of RAPL or LAPC at these rows.
     - The pushout row is NOT derived from the pullback row.  It could
       have been: [fun H F => H (Opposite_Functor F)] inhabits
       [HasLimitsOfShape (Opposite Roof) (Opposite C) →
       HasColimitsOfShape Roof C], and that was compiled to check.  It is
       not used, because every statement downstream would then be about
       [C^op] and the covariance the issue asks for would be lost.
     - [ShapeLinked] is a SUFFICIENT condition and is not claimed to be
       connectedness.  No general theory of connected shapes is developed,
       nothing relates it to Structure/Groupoid/Connected.v's [Connected],
       and no shape is exhibited that fails it.
     - The four row functors and the four [Has*] results are plain
       [Definition]s, NOT registered [Instance]s: each takes a
       [HasLimitsOfShape] or [HasColimitsOfShape] parameter, which is not
       a class, so resolution could never produce it.  This follows
       Adjunction/Diagonal/Limit.v, which gives the same reason for
       [LimitFunctor].
     - No wide equalizers or wide pullbacks: Structure/Equalizer/Wide.v
       and Structure/Pullback/Wide.v are untouched, and nothing here says
       anything about the shapes they use.
     - No relation to Structure/Pullback/Reduction.v's interdefinability
       results, so nothing connects these four rows to each other.
     - No concrete computation of any of the four objects: the witnesses
       are up to isomorphism only, and no element of any (co)limit is
       evaluated.
     - Nothing at a shape other than these three, and no finite-shape
       row for the terminal or initial object -- those are the degenerate
       rows Adjunction/Diagonal/Limit.v already delivers. 

--------
未交付的内容

- 四个 [Sets] 级别类别是第二居民，并且没有
 声称与第一个一致。 每一个
 [DiagSets_HasEqualizers]、[DiagSets_HasCoequalizers]、
 [Sets_HasPullbacks_of_shape] 和 [Sets_HasPushouts_of_shape]
 复制一个先前存在的同类居民——
 [Adjunction/GAFT/Sets.v] 的 [Sets_HasEqualizers]，
 [Instance/Sets/Coequalizer.v] 的 [Sets_HasCoequalizers]，
 [Instance/Sets/Pullback.v] 的 [Sets_HasPullbacks] 和
 [Instance/Sets/Pushout.v] 的 [Sets_HasPushouts]。 四个
 这里建立的来自应用于的一般定理
 [Sets_HasLimitsOfShape]； 四个预先存在的都是直接的
 建筑。 两者没有任何关系——没有同构，没有
 [≈]，甚至不是所选顶点的比较 - 所以这些是
 通往同一班级的第二条路线，而不是身份证明
 树自己的对象。
名称故意不同，并且
 这里的四个是普通 [Definition]，而不是 [Instance]，所以
 预先存在的导出实例仍然赢得所有解决方案。 - 四个包装中的任何一个都没有匡威。 没有任何构建
 [HasLimitsOfShape Parallel C] 或 [HasEqualizers C] 中的任何一个
 其他三个方向。 障碍是真实存在的而不是
 忽略：初级课程对 PAIRS 和 SPANS 进行量化，
 其图为 [APair f g]、[ASpan f g] 和 [ACospan f g]，以及
 一般 [F : Parallel ⟶ C] 不是这些记录之一
 鼻子； 沿着图的同构传输极限不是
 已尝试但未使用此类传输。 所以每个 [Has*] 结果
 这里只运行一种方式。 更正（#477）：书写准确；
 对于 coequalizer 行，现在该文件外部存在一个相反的情况。
结构/Coequalizer.v 的 [HasCoequalizers_HasColimitsOfShape]
 建立每个 [F : Parallel ⟶ C] 的余限
 [HasCoequalizers C]，型号为[HasColimitsOfShape Parallel C]
 通过 δ (Test/ProbeAbsolute477.v, C31)，它识别出 F，没有
 [APair]记录：它采用F对的初等均衡器
 名称、两个箭头的图像，并读取共同限制
 可可关闭它。 均衡器、回拉和推出行仍然
 没有交谈。 - 四个函子中的任何一个都没有唯一性。 [left_adjoint_iso] 和
 [right_adjoint_iso] 没有实例化，所以什么也没说
 [EqualizerFunctor] 是 [Δ[Parallel] 的右伴随] 最多
 自然同构，四个双条件仅断言
 伴随词的存在，而不是它被命名的伴随词。 - 没有任何识别的自然性。
[eq_counit_IsEqualizer] 和
 它的三个兄弟姐妹一次只对一个图表进行陈述；
 图中没有任何内容显示出自然的分配，并且
 没有将四个基本 API 作为函子进行比较。 - 没有关于这四者的保存、反思或创造
 形状，并且这些行中没有 RAPL 或 LAPC 的实例化。 - 推出排不是从拉回排派生的。 它可以
 已：[fun H F => H (Opposite_Functor F)] 栖息
 [HasLimitsOfShape（屋顶对面）（C 对面）→
 HasColimitsOfShape Roof C]，并进行编译以进行检查。 它是
 不使用，因为下游的每个语句都将是关于
 [C^op] 和问题要求的协方差将会丢失。 - [ShapeLinked] 是一个充分条件，并未声称是
 连通性。
没有发展出连接形状的一般理论，
 它与 Structure/Groupoid/Connected.v 的 [Connected] 没有任何关系，
 没有任何形状会失败。 - 四行函子和四个 [Has*] 结果很简单
 [Definition]、未注册的 [Instance]：每个都需要一个
 [HasLimitsOfShape] 或 [HasColimitsOfShape] 参数，这不是
 一个类，所以解析永远无法产生它。 这如下
 Adjunction/Diagonal/Limit.v，给出了相同的理由
 [LimitFunctor]。 - 没有宽均衡器或宽回调：Structure/Equalizer/Wide.v
 和 Structure/Pullback/Wide.v 未受影响，这里什么也没说
 关于他们使用的形状的任何信息。 - 与 Structure/Pullback/Reduction.v 的互定义性无关
 结果，因此没有任何东西将这四行相互连接起来。
- 没有对四个对象中的任何一个进行具体计算：证人
 仅取决于同构，并且没有任何（共）极限的元素
 评价。 - 除了这三种形状之外，没有任何其他形状，并且没有有限形状
 终端或初始对象的行——这些是退化的
 rows Adjunction/Diagonal/Limit.v 已经交付。 
*)

(*
Axiom status and counts

   140/140 constants report “Closed under the global context”.  Method:
   [Print Module Category.Adjunction.Diagonal.Finite] with whitespace
   FLATTENED before matching (it wraps long entries onto their own lines)
   enumerates 140 names; the file declares no [Record], [Class] or
   [Inductive], so there is no unlisted [Build_*] constructor, and the
   count decomposes as 136 source-declared names plus the 4 [Program]
   obligations of [dia_unit_iso] and [dia_counit_iso], which a [.glob]
   sweep does not record.  The file's third [Program], [SetsConstTrue],
   generates no obligation at all -- its [proper_morphism] is discharged
   during elaboration.  Each name was queried by its FULLY QUALIFIED name,
   in seven chunks of twenty, and the same chunking was used to pair every
   [About] output with its constant (an unchunked run cannot be parsed
   reliably: [About]'s record boundaries are ambiguous, and interleaving
   [Print Assumptions] gives a separator that is). 

--------
Axiom 状态和计数

140/140常量报告“在全局背景下关闭”。 方法：
 [Print Module Category.Adjunction.Diagonal.Finite] 带有空格
 匹配前扁平化（它将长条目包装到自己的行中）
 列举了140个名字； 该文件声明没有 [Record]、[Class] 或
 [Inductive]，因此没有未列出的 [Build_*] 构造函数，并且
 count 分解为 136 个源声明名称加上 4 [Program]
 [dia_unit_iso] 和 [dia_counit_iso] 的义务，其中 [.glob]
 扫不记录。 该文件的第三个[Program]、[SetsConstTrue]、
 完全不产生任何义务——其 [proper_morphism] 已解除
 在阐述过程中。 每个名称均按其完全限定名称进行查询，
 分为七块，每块二十块，并且使用相同的块来配对每个
 [About] 输出及其常量（无法解析未分块的运行
 可靠：[About] 的记录边界不明确，并且交错
 [Print Assumptions] 给出的分隔符是）。 
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Span.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Limit.
Require Import Category.Structure.Pushout.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Morphisms.CokernelPair.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Roof.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Cocomplete.
Require Import Category.Adjunction.Diagonal.Limit.

Generalizable All Variables.

(** * Transport of the elementary predicates along [≈]  / * 沿 [≈] 传输基本谓词*)

(*
None of the three elementary records is stated up to [≈] in its
   distinguished arrow, and each is needed here at an arrow that differs
   from the one the tree's conversions produce by a unit residue.  These
   four transports supply exactly that. 

--------
[≈] 在其文件中没有说明这三个基本记录中的任何一个。 
区分箭头，并且这里需要每个不同的箭头
 来自树的转换产生的单位残差。 这些
 四种运输方式正是满足这一需求。 
*)

Section Respects.

Context {C : Category}.

Lemma IsEqualizer_respects {x y q : C} {f g : x ~> y} {e e' : q ~> x} :
  IsEqualizer f g q e → e ≈ e' → IsEqualizer f g q e'.
Proof.
  intros E He.
  unshelve econstructor.
  - rewrite <- He; exact (fork_eq E).
  - intros z h Hh.
    unshelve eapply Build_Unique.
    + exact (unique_obj (eq_desc E h Hh)).
    + rewrite <- He; exact (unique_property (eq_desc E h Hh)).
    + intros v Hv.
      apply (uniqueness (eq_desc E h Hh)).
      rewrite He; exact Hv.
Defined.

Lemma IsCoequalizer_respects {x y q : C} {f g : x ~> y} {e e' : y ~> q} :
  IsCoequalizer f g q e → e ≈ e' → IsCoequalizer f g q e'.
Proof.
  intros E He.
  unshelve econstructor.
  - rewrite <- He; exact (cofork E).
  - intros z h Hh.
    unshelve eapply Build_Unique.
    + exact (unique_obj (coeq_desc E h Hh)).
    + rewrite <- He; exact (unique_property (coeq_desc E h Hh)).
    + intros v Hv.
      apply (uniqueness (coeq_desc E h Hh)).
      rewrite He; exact Hv.
Defined.

Lemma IsPullback_respects {x y z P : C} {f : x ~> z} {g : y ~> z}
  {p1 p1' : P ~> x} {p2 p2' : P ~> y} :
  IsPullback f g P p1 p2 → p1 ≈ p1' → p2 ≈ p2' →
  IsPullback f g P p1' p2'.
Proof.
  intros H H1 H2.
  unshelve econstructor.
  - rewrite <- H1, <- H2; exact (is_pullback_commutes H).
  - intros Q q1 q2 Hc.
    unshelve eapply Build_Unique.
    + exact (unique_obj (is_pullback_ump H Q q1 q2 Hc)).
    + split.
      * rewrite <- H1.
        exact (fst (unique_property (is_pullback_ump H Q q1 q2 Hc))).
      * rewrite <- H2.
        exact (snd (unique_property (is_pullback_ump H Q q1 q2 Hc))).
    + intros v [Hv1 Hv2].
      apply (uniqueness (is_pullback_ump H Q q1 q2 Hc)).
      split.
      * rewrite H1; exact Hv1.
      * rewrite H2; exact Hv2.
Defined.

End Respects.

(*
The pushout square is [IsPullback] in the opposite category, and the
   two hom-setoids agree there, so its transport is the primal one read at
   [C^op]: a [:=] with no tactic. 

--------
推出方块是相反类别中的 [IsPullback]，并且
 两个 hom-setoids 在那里一致，所以它的运输是第一个读取的
 [C^op]：没有策略的 [:=]。 
*)
Definition IsPushoutSquare_respects {C : Category} {x y z P : C}
  {f : x ~> y} {g : x ~> z} {i1 i1' : y ~> P} {i2 i2' : z ~> P} :
  IsPushoutSquare f g P i1 i2 → i1 ≈ i1' → i2 ≈ i2' →
  IsPushoutSquare f g P i1' i2' :=
  @IsPullback_respects (C^op) y z x P f g i1 i1' i2 i2'.

(** * Constant diagrams: the unit and the counit at a linked shape  / * 常数图：链接形状上的单位和计数单位*)

(*
[j0] links the shape [J] when every object of [J] is joined to it by a
   single arrow, in one direction or the other.  Over a CONSTANT diagram
   any such arrow becomes an equation between two legs, because the
   constant diagram sends every arrow to an identity; so over a linked
   shape all the legs of a cone (dually, all the injections of a cocone)
   over a constant diagram agree.  This is a sufficient condition for
   connectedness of the shape, not the general one, and it is all three
   finite shapes below need. 

--------
当 [J] 的每个对象都通过
 单箭头，朝一个方向或另一个方向。 在常数图上
 任何这样的箭头都会成为两条腿之间的方程，因为
 常量图将每个箭头发送到一个恒等式； 所以通过链接
 塑造圆锥体的所有腿（对偶，圆锥体的所有注射）
 在常数图上同意。 这是一个充分条件
 形状的连通性，不是一般的，三者皆有
 低于需要的有限形状。 
*)
Definition ShapeLinked {J : Category} (j0 : J) : Type :=
  ∀ j : J, (j0 ~{J}~> j) + (j ~{J}~> j0).

Section ConstantLimit.

Context {J C : Category}.
Context (L : HasLimitsOfShape J C).

Lemma lim_const_legs (x : C) (j0 : J) (Hl : ShapeLinked j0) (j : J) :
  lim_leg L (Δ[J](x)) j ≈ lim_leg L (Δ[J](x)) j0.
Proof.
  destruct (Hl j) as [k | k].
  - transitivity (fmap[Δ[J](x)] k ∘ lim_leg L (Δ[J](x)) j0).
    + symmetry; exact (lim_leg_coherence L (Δ[J](x)) k).
    + apply id_left.
  - transitivity (fmap[Δ[J](x)] k ∘ lim_leg L (Δ[J](x)) j).
    + symmetry; apply id_left.
    + exact (lim_leg_coherence L (Δ[J](x)) k).
Qed.

(* The unit of Δ ⊣ lim, named.  / Δ⊣lim的单位，命名为。*)
Definition dia_unit (x : C) : x ~{C}~> lim_obj L (Δ[J](x)) :=
  @unit ([J, C]) C (@Diagonal C J) (LimitFunctor L)
        (Diagonal_Limit_Adjunction L) x.

(* The unit IS the transpose of the identity, on the nose.  / 该单位是身份的转置，在鼻子上。*)
Example dia_unit_strict (x : C) :
  dia_unit x = lim_transpose_to L (@id ([J, C]) (Δ[J](x))) := eq_refl.

Lemma dia_unit_leg (x : C) (j : J) :
  lim_leg L (Δ[J](x)) j ∘ dia_unit x ≈ id[x].
Proof.
  exact (lim_transpose_to_commutes L
           (@id ([J, C]) (Δ[J](x))) j).
Qed.

(*
Over a linked shape the unit is invertible, its inverse being the
   limiting leg at the linking object.  This is the precise sense in
   which the unit of the equalizer and pullback rows “is the identity”. 

--------
在链接形状上，单位是可逆的，其倒数是
 限制连接对象处的腿。 这就是准确的意义
 其中均衡器和回拉行的单位“是同一性”。 
*)
Program Definition dia_unit_iso (j0 : J) (Hl : ShapeLinked j0) (x : C) :
  x ≅ lim_obj L (Δ[J](x)) := {|
  to   := dia_unit x;
  from := lim_leg L (Δ[J](x)) j0
|}.
Next Obligation.
  refine (lim_med_eq L (@limit_cone J C (Δ[J](x)) (L (Δ[J](x)))) _ _ _ _);
  intro j.
  - rewrite comp_assoc, dia_unit_leg, id_left.
    symmetry; exact (lim_const_legs x j0 Hl j).
  - apply id_right.
Qed.
Next Obligation. apply dia_unit_leg. Qed.

End ConstantLimit.

Section ConstantColimit.

Context {J C : Category}.
Context (M : HasColimitsOfShape J C).

Lemma colim_const_injs (x : C) (j0 : J) (Hl : ShapeLinked j0) (j : J) :
  colim_inj M (Δ[J](x)) j ≈ colim_inj M (Δ[J](x)) j0.
Proof.
  destruct (Hl j) as [k | k].
  - transitivity (colim_inj M (Δ[J](x)) j ∘ fmap[Δ[J](x)] k).
    + symmetry; apply id_right.
    + exact (colim_inj_coherence M (Δ[J](x)) k).
  - transitivity (colim_inj M (Δ[J](x)) j0 ∘ fmap[Δ[J](x)] k).
    + symmetry; exact (colim_inj_coherence M (Δ[J](x)) k).
    + apply id_right.
Qed.

(* The counit of colim ⊣ Δ, named.  / colim ⊣ Δ 的计数单位，命名为。*)
Definition dia_counit (x : C) : colim_obj M (Δ[J](x)) ~{C}~> x :=
  @counit C ([J, C]) (ColimitFunctor M) (@Diagonal C J)
          (Colimit_Diagonal_Adjunction M) x.

Example dia_counit_strict (x : C) :
  dia_counit x = colim_transpose_from M (@id ([J, C]) (Δ[J](x)))
  := eq_refl.

Lemma dia_counit_inj (x : C) (j : J) :
  dia_counit x ∘ colim_inj M (Δ[J](x)) j ≈ id[x].
Proof.
  exact (colim_transpose_from_commutes M
           (@id ([J, C]) (Δ[J](x))) j).
Qed.

Program Definition dia_counit_iso (j0 : J) (Hl : ShapeLinked j0) (x : C) :
  colim_obj M (Δ[J](x)) ≅ x := {|
  to   := dia_counit x;
  from := colim_inj M (Δ[J](x)) j0
|}.
Next Obligation. apply dia_counit_inj. Qed.
Next Obligation.
  refine (colim_med_eq M (@limit_cone (J^op) (C^op) ((Δ[J](x))^op)
                            (M (Δ[J](x)))) _ _ _ _);
  intro j.
  - rewrite <- comp_assoc, dia_counit_inj, id_right.
    symmetry; exact (colim_const_injs x j0 Hl j).
  - apply id_left.
Qed.

End ConstantColimit.

(** * The three finite shapes are linked  / * 三个有限形状是相连的*)

Definition Parallel_linked : @ShapeLinked Parallel ParX.
Proof.
  intro j; destruct j.
  - left; exact ((true; ParIdX) : ParX ~{Parallel}~> ParX).
  - left; exact ((true; ParOne) : ParX ~{Parallel}~> ParY).
Defined.

Definition Roof_linked : @ShapeLinked Roof RZero.
Proof.
  intro j; destruct j.
  - left; exact ZeroNeg.
  - left; exact IdZero.
  - left; exact ZeroPos.
Defined.

Definition Roofop_linked : @ShapeLinked (Roof^op) RZero.
Proof.
  intro j; destruct j.
  - right; exact ZeroNeg.
  - left; exact IdZero.
  - right; exact ZeroPos.
Defined.

(** * Row 1: equalizers as the right adjoint of Δ[Parallel]  / * 第 1 行：均衡器作为 Δ[Parallel] 的右伴随*)

Section EqualizerRow.

Context {C : Category}.
Context (L : HasLimitsOfShape Parallel C).

Definition EqualizerFunctor : [Parallel, C] ⟶ C := LimitFunctor L.

Definition Diagonal_Equalizer_Adjunction :
  @Diagonal C Parallel ⊣ EqualizerFunctor := Diagonal_Limit_Adjunction L.

Definition eq_counit (F : Parallel ⟶ C) : Δ[Parallel](lim_obj L F) ⟹ F :=
  lim_counit L F.

(* Mac Lane's counit entry for the equalizer row: the equalizing arrow.  / Mac Lane 均衡器行的计数条目：均衡箭头。*)
Definition eq_arrow (F : Parallel ⟶ C) : lim_obj L F ~{C}~> F ParX :=
  transform[eq_counit F] ParX.

Example eq_arrow_strict (F : Parallel ⟶ C) :
  eq_arrow F = lim_leg L F ParX ∘ id := eq_refl.

Lemma eq_leg_is_arrow (F : Parallel ⟶ C) :
  lim_leg L F ParX ≈ eq_arrow F.
Proof. symmetry; exact (lim_counit_is_limit_leg L F ParX). Qed.

(* The identification against the ELEMENTARY equalizer API.  / 针对 ELEMENTARY 均衡器 API 的识别。*)
Definition eq_counit_IsEqualizer {x y : C} (f g : x ~> y) :
  IsEqualizer f g (lim_obj L (APair f g)) (eq_arrow (APair f g)) :=
  IsEqualizer_respects (equalizer_is_equalizer f g (L (APair f g)))
    (eq_leg_is_arrow (APair f g)).

Definition HasLimitsOfShape_HasEqualizers : HasEqualizers C :=
  {| equalizer := fun x y f g =>
       (lim_obj L (APair f g);
         (eq_arrow (APair f g); eq_counit_IsEqualizer f g)) |}.

(*
Mac Lane's unit entry: the identity, in the precise sense that the
   unit is invertible with the limiting leg as its inverse. 

--------
麦克莱恩的单元条目：身份，准确地说是
 单位是可逆的，限制腿作为其倒转。 
*)
Definition eq_unit_iso (x : C) : x ≅ lim_obj L (Δ[Parallel](x)) :=
  dia_unit_iso L ParX Parallel_linked x.

End EqualizerRow.

(** * Row 2: coequalizers as the left adjoint of Δ[Parallel]  / * 第 2 行：辅助均衡器作为 Δ[Parallel] 的左伴随*)

Section CoequalizerRow.

Context {C : Category}.
Context (M : HasColimitsOfShape Parallel C).

Definition CoequalizerFunctor : [Parallel, C] ⟶ C := ColimitFunctor M.

Definition Coequalizer_Diagonal_Adjunction :
  CoequalizerFunctor ⊣ @Diagonal C Parallel := Colimit_Diagonal_Adjunction M.

Definition coeq_unit (F : Parallel ⟶ C) : F ⟹ Δ[Parallel](colim_obj M F) :=
  colim_unit M F.

(* Mac Lane's unit entry for the coequalizer row: the coequalizing arrow.  / Mac Lane 的共均衡器行的单位条目：共均衡箭头。*)
Definition coeq_arrow (F : Parallel ⟶ C) : F ParY ~{C}~> colim_obj M F :=
  transform[coeq_unit F] ParY.

Example coeq_arrow_strict (F : Parallel ⟶ C) :
  coeq_arrow F = id ∘ colim_inj M F ParY := eq_refl.

Lemma coeq_inj_is_arrow (F : Parallel ⟶ C) :
  colim_inj M F ParY ≈ coeq_arrow F.
Proof. symmetry; exact (colim_unit_is_colimit_inj M F ParY). Qed.

Definition coeq_unit_IsCoequalizer {x y : C} (f g : x ~> y) :
  IsCoequalizer f g (colim_obj M (APair f g)) (coeq_arrow (APair f g)) :=
  IsCoequalizer_respects (coequalizer_is_coequalizer f g (M (APair f g)))
    (coeq_inj_is_arrow (APair f g)).

Definition HasColimitsOfShape_HasCoequalizers : HasCoequalizers C :=
  {| coeq := fun x y f g =>
       (colim_obj M (APair f g);
         (coeq_arrow (APair f g); coeq_unit_IsCoequalizer f g)) |}.

Definition coeq_counit_iso (x : C) : colim_obj M (Δ[Parallel](x)) ≅ x :=
  dia_counit_iso M ParX Parallel_linked x.

End CoequalizerRow.

(** * Row 3: pullbacks as the right adjoint of Δ[Roof^op]  / * 第 3 行：回调作为 Δ[Roof^op] 的右伴随*)

Section PullbackRow.

Context {C : Category}.
Context (L : HasLimitsOfShape (Roof^op) C).

(* The two legs of a cospan, read covariantly in C.  / cospan 的两条腿，在 C 中读作协变。*)
Definition cospan_left (F : Roof^op ⟶ C) : F RNeg ~{C}~> F RZero :=
  fmap[F] (ZeroNeg : RNeg ~{Roof^op}~> RZero).

Definition cospan_right (F : Roof^op ⟶ C) : F RPos ~{C}~> F RZero :=
  fmap[F] (ZeroPos : RPos ~{Roof^op}~> RZero).

Definition PullbackFunctor : [Roof^op, C] ⟶ C := LimitFunctor L.

Definition Diagonal_Pullback_Adjunction :
  @Diagonal C (Roof^op) ⊣ PullbackFunctor := Diagonal_Limit_Adjunction L.

Definition pb_counit (F : Roof^op ⟶ C) : Δ[Roof^op](lim_obj L F) ⟹ F :=
  lim_counit L F.

(* Mac Lane's counit entry for the pullback row: the two projections.  / Mac Lane 的回调行的计数条目：两个投影。*)
Definition pb_fst (F : Roof^op ⟶ C) : lim_obj L F ~{C}~> F RNeg :=
  transform[pb_counit F] RNeg.

Definition pb_snd (F : Roof^op ⟶ C) : lim_obj L F ~{C}~> F RPos :=
  transform[pb_counit F] RPos.

Example pb_fst_strict (F : Roof^op ⟶ C) :
  pb_fst F = lim_leg L F RNeg ∘ id := eq_refl.

Example pb_snd_strict (F : Roof^op ⟶ C) :
  pb_snd F = lim_leg L F RPos ∘ id := eq_refl.

Lemma pb_leg_is_fst (F : Roof^op ⟶ C) : lim_leg L F RNeg ≈ pb_fst F.
Proof. symmetry; exact (lim_counit_is_limit_leg L F RNeg). Qed.

Lemma pb_leg_is_snd (F : Roof^op ⟶ C) : lim_leg L F RPos ≈ pb_snd F.
Proof. symmetry; exact (lim_counit_is_limit_leg L F RPos). Qed.

(*
The limiting legs of a cospan ARE its pullback projections.  This is
   Structure/Pullback/Limit.v's [Pullback_to_Universal] read through the
   apex-pinned predicate: a [:=] with no tactic, the apex and both
   projections landing on the nose. 

--------
cospan 的限制腿是其回调预测。 这是
 Structure/Pullback/Limit.v 的 [Pullback_to_Universal] 读取
 顶点固定谓词：没有策略、顶点和两者的 [:=]
 投影落在鼻子上。 
*)
Definition pb_leg_IsPullback (F : Roof^op ⟶ C) :
  IsPullback (cospan_left F) (cospan_right F) (lim_obj L F)
             (lim_leg L F RNeg) (lim_leg L F RPos) :=
  pullback_is_pullback _ _ (Pullback_to_Universal F (L F)).

(* The identification against the ELEMENTARY pullback API.  / 针对 ELEMENTARY 回调 API 的识别。*)
Definition pb_counit_IsPullback (F : Roof^op ⟶ C) :
  IsPullback (cospan_left F) (cospan_right F) (lim_obj L F)
             (pb_fst F) (pb_snd F) :=
  IsPullback_respects (pb_leg_IsPullback F)
    (pb_leg_is_fst F) (pb_leg_is_snd F).

(* A cospan in C, as a diagram of shape Roof^op.  / C 中的 cospan，作为形状 Roof^op 的图。*)
Definition ACospan {x y z : C} (f : x ~> z) (g : y ~> z) : Roof^op ⟶ C :=
  (@ASpan (C^op) z x y f g)^op.

Example acospan_left {x y z : C} (f : x ~> z) (g : y ~> z) :
  cospan_left (ACospan f g) = f := eq_refl.

Example acospan_right {x y z : C} (f : x ~> z) (g : y ~> z) :
  cospan_right (ACospan f g) = g := eq_refl.

Definition HasLimitsOfShape_HasPullbacks : HasPullbacks C :=
  {| pullback := fun x y z f g =>
       is_pullback_pullback (pb_counit_IsPullback (ACospan f g)) |}.

Definition pb_unit_iso (x : C) : x ≅ lim_obj L (Δ[Roof^op](x)) :=
  dia_unit_iso L RZero Roofop_linked x.

End PullbackRow.

(** * Row 4: pushouts as the left adjoint of Δ[Roof]  / * 第 4 行：推出作为 Δ[Roof] 的左伴随*)

Section PushoutRow.

Context {C : Category}.
Context (M : HasColimitsOfShape Roof C).

Definition span_left (F : Roof ⟶ C) : F RZero ~{C}~> F RNeg :=
  fmap[F] ZeroNeg.

Definition span_right (F : Roof ⟶ C) : F RZero ~{C}~> F RPos :=
  fmap[F] ZeroPos.

Definition PushoutFunctor : [Roof, C] ⟶ C := ColimitFunctor M.

Definition Pushout_Diagonal_Adjunction :
  PushoutFunctor ⊣ @Diagonal C Roof := Colimit_Diagonal_Adjunction M.

Definition po_unit (F : Roof ⟶ C) : F ⟹ Δ[Roof](colim_obj M F) :=
  colim_unit M F.

(* Mac Lane's unit entry for the pushout row: the two injections.  / Mac Lane 推出行的单位条目：两次注射。*)
Definition pushout_inj1 (F : Roof ⟶ C) : F RNeg ~{C}~> colim_obj M F :=
  transform[po_unit F] RNeg.

Definition pushout_inj2 (F : Roof ⟶ C) : F RPos ~{C}~> colim_obj M F :=
  transform[po_unit F] RPos.

Example po_in1_strict (F : Roof ⟶ C) :
  pushout_inj1 F = id ∘ colim_inj M F RNeg := eq_refl.

Example po_in2_strict (F : Roof ⟶ C) :
  pushout_inj2 F = id ∘ colim_inj M F RPos := eq_refl.

Lemma po_inj_is_in1 (F : Roof ⟶ C) : colim_inj M F RNeg ≈ pushout_inj1 F.
Proof. symmetry; exact (colim_unit_is_colimit_inj M F RNeg). Qed.

Lemma po_inj_is_in2 (F : Roof ⟶ C) : colim_inj M F RPos ≈ pushout_inj2 F.
Proof. symmetry; exact (colim_unit_is_colimit_inj M F RPos). Qed.

(* The colimiting square of a span commutes.  / 跨度的共界正方形是通勤的。*)
Lemma po_inj_commutes (F : Roof ⟶ C) :
  colim_inj M F RNeg ∘ span_left F ≈ colim_inj M F RPos ∘ span_right F.
Proof.
  transitivity (colim_inj M F RZero).
  - exact (colim_inj_coherence M F (ZeroNeg : RZero ~{Roof}~> RNeg)).
  - symmetry.
    exact (colim_inj_coherence M F (ZeroPos : RZero ~{Roof}~> RPos)).
Qed.

(*
Every hom-setoid of [Roof] is trivially true, so a functor out of it
   carries any two parallel arrows to [≈]-equal morphisms; the identity
   arrows go to identities.  These two facts discharge every case of the
   cocone coherence below. 

--------
[Roof] 的每个 hom-setoid 都是平凡真实的，因此它是一个函子
 携带任何两个平行箭头到 [≈] 等态射； 身份
 箭头指向身份。 这两个事实说明了每一个案例
 可果连贯性如下。 
*)
Lemma roof_fmap_any (F : Roof ⟶ C) {a b : Roof} (k k' : a ~{Roof}~> b) :
  fmap[F] k ≈ fmap[F] k'.
Proof. apply fmap_respects; exact I. Qed.

Lemma roof_fmap_id (F : Roof ⟶ C) (a : Roof) (k : a ~{Roof}~> a) :
  fmap[F] k ≈ id.
Proof.
  rewrite (roof_fmap_any F k (id[a])).
  apply fmap_id.
Qed.

(*
The cocone under a span determined by a competing commuting square:
   the leg at the apex RZero is forced to be the common composite. 

--------
由竞争通勤方确定的跨度下的可锥体：
 顶点 RZero 处的腿被迫成为普通复合材料。 
*)
Definition po_legs (F : Roof ⟶ C) (Q : C)
  (q1 : F RNeg ~> Q) (q2 : F RPos ~> Q) (j : Roof) : F j ~{C}~> Q :=
  match j return F j ~{C}~> Q with
  | RNeg  => q1
  | RZero => q1 ∘ span_left F
  | RPos  => q2
  end.

Lemma po_legs_coherence (F : Roof ⟶ C) (Q : C)
  (q1 : F RNeg ~> Q) (q2 : F RPos ~> Q)
  (Hc : q1 ∘ span_left F ≈ q2 ∘ span_right F) :
  ∀ (a b : Roof) (k : a ~{Roof}~> b),
    po_legs F Q q1 q2 b ∘ fmap[F] k ≈ po_legs F Q q1 q2 a.
Proof.
  intros a b k.
  destruct a, b; simpl in k; auto with roof_laws; simpl.
  - rewrite (roof_fmap_id F RNeg k); apply id_right.
  - rewrite (roof_fmap_any F k (ZeroNeg : RZero ~{Roof}~> RNeg)).
    reflexivity.
  - rewrite (roof_fmap_id F RZero k); apply id_right.
  - rewrite (roof_fmap_any F k (ZeroPos : RZero ~{Roof}~> RPos)).
    symmetry; exact Hc.
  - rewrite (roof_fmap_id F RPos k); apply id_right.
Qed.

Definition po_cocone (F : Roof ⟶ C) (Q : C)
  (q1 : F RNeg ~> Q) (q2 : F RPos ~> Q)
  (Hc : q1 ∘ span_left F ≈ q2 ∘ span_right F) : Cocone F :=
  @Cocone_of Roof C F Q (po_legs F Q q1 q2) (po_legs_coherence F Q q1 q2 Hc).

Lemma po_inj_ump (F : Roof ⟶ C) (Q : C)
  (q1 : F RNeg ~> Q) (q2 : F RPos ~> Q)
  (Hc : q1 ∘ span_left F ≈ q2 ∘ span_right F) :
  ∃! u : colim_obj M F ~> Q,
    u ∘ colim_inj M F RNeg ≈ q1 ∧ u ∘ colim_inj M F RPos ≈ q2.
Proof.
  unshelve eapply Build_Unique.
  - exact (colim_med M (po_cocone F Q q1 q2 Hc)).
  - split.
    + exact (colim_med_commutes M (po_cocone F Q q1 q2 Hc) RNeg).
    + exact (colim_med_commutes M (po_cocone F Q q1 q2 Hc) RPos).
  - intros v [Hv1 Hv2].
    apply (colim_med_unique M (po_cocone F Q q1 q2 Hc)).
    intro j; destruct j.
    + exact Hv1.
    + rewrite <- (colim_inj_coherence M F
                    (ZeroNeg : RZero ~{Roof}~> RNeg)).
      now rewrite comp_assoc, Hv1.
    + exact Hv2.
Qed.

(*
The colimiting injections of a span form a pushout square, in the
   apex-pinned sense of Theory/Morphisms/CokernelPair.v. 

--------
跨度的共界注入形成一个推出正方形，在
 Theory/Morphisms/CokernelPair.v 的顶点固定意义。 
*)
Definition po_inj_IsPushoutSquare (F : Roof ⟶ C) :
  IsPushoutSquare (span_left F) (span_right F) (colim_obj M F)
                  (colim_inj M F RNeg) (colim_inj M F RPos) :=
  Build_IsPushoutSquare (po_inj_commutes F) (po_inj_ump F).

(* The identification against the ELEMENTARY pushout API.  / 针对 ELEMENTARY Pushout API 的识别。*)
Definition po_unit_IsPushoutSquare (F : Roof ⟶ C) :
  IsPushoutSquare (span_left F) (span_right F) (colim_obj M F)
                  (pushout_inj1 F) (pushout_inj2 F) :=
  IsPushoutSquare_respects (po_inj_IsPushoutSquare F)
    (po_inj_is_in1 F) (po_inj_is_in2 F).

Example aspan_left {S x y : C} (f : S ~> x) (g : S ~> y) :
  span_left (ASpan f g) = f := eq_refl.

Example aspan_right {S x y : C} (f : S ~> x) (g : S ~> y) :
  span_right (ASpan f g) = g := eq_refl.

Definition HasColimitsOfShape_HasPushouts : HasPushouts C :=
  {| pushout := fun x y z f g =>
       is_pushout_square_pushout (po_unit_IsPushoutSquare (ASpan f g)) |}.

Definition po_counit_iso (x : C) : colim_obj M (Δ[Roof](x)) ≅ x :=
  dia_counit_iso M RZero Roof_linked x.

End PushoutRow.

(** * Degenerate rows of the elementary data  / * 基本数据的简并行*)

(*
Four small readings of the elementary predicates, used below to compute
   the four (co)limit objects at a concrete witness.  Each is proved from
   the descent property alone, with no reference to the shape categories. 

--------
基本谓词的四个小读数，下面用于计算
 四个（共同）限制对象在具体见证人处。 每一个都证明自
 单独的血统属性，不涉及形状类别。 
*)

Section Degenerate.

Context {C : Category}.

(*
A pair whose two legs agree is equalized by an isomorphism onto the
   common domain: the identity forks such a pair, and the equalizing
   arrow is monic. 

--------
两条腿一致的一对通过同构到
 公共域：恒等分叉这样的一对，并且均衡
 箭头是莫尼克。 
*)
Definition equalizer_of_equal_pair {x y : C} (f : x ~> y) {q : C}
  {e : q ~> x} (E : IsEqualizer f f q e) : q ≅ x.
Proof.
  assert (Hf : f ∘ id[x] ≈ f ∘ id[x]) by reflexivity.
  pose proof (eq_desc E (id[x]) Hf) as D.
  unshelve refine {| to := e; from := unique_obj D |}.
  - exact (unique_property D).
  - apply (@monic _ _ _ e (equalizer_monic f f E)).
    rewrite comp_assoc, (unique_property D), id_left, id_right.
    reflexivity.
Defined.

(*
Dually, a pair whose two legs agree is coequalized by an isomorphism
   onto the common codomain. 

--------
对偶而言，两条腿一致的一对通过同构而相等
 到公共密码域上。 
*)
Definition coequalizer_of_equal_pair {x y : C} (f : x ~> y) {q : C}
  {e : y ~> q} (E : IsCoequalizer f f q e) : q ≅ y.
Proof.
  assert (Hf : id[y] ∘ f ≈ id[y] ∘ f) by reflexivity.
  pose proof (coeq_desc E (id[y]) Hf) as D.
  unshelve refine {| to := unique_obj D; from := e |}.
  - exact (unique_property D).
  - apply (@epic _ _ _ e (coequalizer_epic f f E)).
    rewrite <- comp_assoc, (unique_property D), id_left, id_right.
    reflexivity.
Defined.

(*
The pullback of a cospan one of whose legs is an identity is the
   domain of the other leg, projected by the second projection. 

--------
其中一条腿是恒等式的 cospan 的回调是
 由第二个投影投影的另一条腿的域。 
*)
Definition pullback_of_identity {y z P : C} (g : y ~> z)
  {p1 : P ~> z} {p2 : P ~> y} (H : IsPullback (id[z]) g P p1 p2) : P ≅ y.
Proof.
  assert (Hc : id[z] ∘ g ≈ g ∘ id[y]).
  { rewrite id_left, id_right; reflexivity. }
  pose proof (is_pullback_ump H y g (id[y]) Hc) as D.
  pose proof (is_pullback_ump H P p1 p2 (is_pullback_commutes H)) as DP.
  unshelve refine {| to := p2; from := unique_obj D |}.
  - exact (snd (unique_property D)).
  - transitivity (unique_obj DP).
    + symmetry.
      apply (uniqueness DP); split.
      * rewrite comp_assoc, (fst (unique_property D)).
        rewrite <- (is_pullback_commutes H).
        apply id_left.
      * rewrite comp_assoc, (snd (unique_property D)).
        apply id_left.
    + apply (uniqueness DP); split; apply id_right.
Defined.

(*
Dually, the pushout of a span one of whose legs is an identity is the
   codomain of the other leg, injected by the second injection. 

--------
对偶而言，其中一条腿是恒等式的跨度的推出是
 另一条腿的共域，通过第二次注射注射。 
*)
Definition pushout_of_identity {x z P : C} (g : x ~> z)
  {i1 : x ~> P} {i2 : z ~> P} (H : IsPushoutSquare (id[x]) g P i1 i2) :
  P ≅ z.
Proof.
  assert (Hc : g ∘ id[x] ≈ id[z] ∘ g).
  { rewrite id_left, id_right; reflexivity. }
  pose proof (is_pushout_square_ump H z g (id[z]) Hc) as D.
  pose proof (is_pushout_square_ump H P i1 i2
                (is_pushout_square_commutes H)) as DP.
  unshelve refine {| to := unique_obj D; from := i2 |}.
  - exact (snd (unique_property D)).
  - transitivity (unique_obj DP).
    + symmetry.
      apply (uniqueness DP); split.
      * rewrite <- comp_assoc, (fst (unique_property D)).
        rewrite <- (is_pushout_square_commutes H).
        apply id_right.
      * rewrite <- comp_assoc, (snd (unique_property D)).
        apply id_right.
    + apply (uniqueness DP); split; apply id_left.
Defined.

End Degenerate.

(** * Non-vacuity: the four rows at Sets  / * 非空：集合的四行*)

Definition SetsEq : HasLimitsOfShape Parallel Sets :=
  Sets_HasLimitsOfShape Parallel.

Definition SetsParallelColim : HasColimitsOfShape Parallel Sets :=
  Sets_HasColimitsOfShape Parallel.

Definition SetsPb : HasLimitsOfShape (Roof^op) Sets :=
  Sets_HasLimitsOfShape (Roof^op).

Definition SetsPo : HasColimitsOfShape Roof Sets :=
  Sets_HasColimitsOfShape Roof.

Definition Sets_Diagonal_Equalizer_Adjunction :
  @Diagonal Sets Parallel ⊣ EqualizerFunctor SetsEq :=
  Diagonal_Equalizer_Adjunction SetsEq.

Definition Sets_Coequalizer_Diagonal_Adjunction :
  CoequalizerFunctor SetsParallelColim ⊣ @Diagonal Sets Parallel :=
  Coequalizer_Diagonal_Adjunction SetsParallelColim.

Definition Sets_Diagonal_Pullback_Adjunction :
  @Diagonal Sets (Roof^op) ⊣ PullbackFunctor SetsPb :=
  Diagonal_Pullback_Adjunction SetsPb.

Definition Sets_Pushout_Diagonal_Adjunction :
  PushoutFunctor SetsPo ⊣ @Diagonal Sets Roof :=
  Pushout_Diagonal_Adjunction SetsPo.

(* All four elementary classes are inhabited at Sets by the rows above.  / 所有四个小学班级都居住在上面几排的 Sets 中。*)

Definition DiagSets_HasEqualizers : HasEqualizers Sets :=
  HasLimitsOfShape_HasEqualizers SetsEq.

Definition DiagSets_HasCoequalizers : HasCoequalizers Sets :=
  HasColimitsOfShape_HasCoequalizers SetsParallelColim.

Definition Sets_HasPullbacks_of_shape : HasPullbacks Sets :=
  HasLimitsOfShape_HasPullbacks SetsPb.

Definition Sets_HasPushouts_of_shape : HasPushouts Sets :=
  HasColimitsOfShape_HasPushouts SetsPo.

(** ** A concrete, non-constant diagram  / ** 具体的非常量图*)

(*
The constant map at [true] on the two-element discrete setoid.  Nothing
   below is a constant DIAGRAM: [SetsConstTrue] is not an identity, which
   is what [sets_const_true_not_id] records. 

--------
二元离散集合体上 [true] 处的常量映射。 什么都没有
 下面是一个常量图： [SetsConstTrue] 不是一个恒等式，
 这是 [sets_const_true_not_id] 记录的内容。 
*)
Program Definition SetsConstTrue : DiagBoolSet ~{Sets}~> DiagBoolSet := {|
  morphism := fun _ => true
|}.

Lemma sets_const_true_not_id : SetsConstTrue ≈ id[DiagBoolSet] → False.
Proof. intro H; discriminate (H false). Qed.

Definition SetsPairDiagram : Parallel ⟶ Sets :=
  APair SetsConstTrue SetsConstTrue.

Lemma SetsPairDiagram_not_constant :
  fmap[SetsPairDiagram] ((true; ParOne) : ParX ~{Parallel}~> ParY)
    ≈ id[DiagBoolSet] → False.
Proof. exact sets_const_true_not_id. Qed.

Definition SetsCospanDiagram : Roof^op ⟶ Sets :=
  ACospan (id[DiagBoolSet]) SetsConstTrue.

Lemma SetsCospanDiagram_not_constant :
  fmap[SetsCospanDiagram] (ZeroPos : RPos ~{Roof^op}~> RZero)
    ≈ id[DiagBoolSet] → False.
Proof. exact sets_const_true_not_id. Qed.

Definition SetsSpanDiagram : Roof ⟶ Sets :=
  ASpan (id[DiagBoolSet]) SetsConstTrue.

Lemma SetsSpanDiagram_not_constant :
  fmap[SetsSpanDiagram] (ZeroPos : RZero ~{Roof}~> RPos)
    ≈ id[DiagBoolSet] → False.
Proof. exact sets_const_true_not_id. Qed.

(** ** The four objects computed, and each proved not a subsingleton  / ** 计算了四个对象，并且每个对象都被证明不是子单例*)

Lemma sets_two_elements_of_iso {X : Sets} (i : X ≅ DiagBoolSet) :
  { a : carrier X & { b : carrier X & a ≈ b → False } }.
Proof.
  exists (from i true).
  exists (from i false).
  intro H.
  pose proof (iso_to_from i true) as H1.
  pose proof (iso_to_from i false) as H2.
  simpl in H1, H2.
  assert (Hb : (true : carrier DiagBoolSet) ≈ false).
  { transitivity (to i (from i true)).
    - symmetry; exact H1.
    - transitivity (to i (from i false)).
      + apply (proper_morphism (to i)); exact H.
      + exact H2. }
  discriminate Hb.
Qed.

Definition sets_equalizer_iso :
  lim_obj SetsEq SetsPairDiagram ≅ DiagBoolSet :=
  equalizer_of_equal_pair SetsConstTrue
    (eq_counit_IsEqualizer SetsEq SetsConstTrue SetsConstTrue).

Definition sets_coequalizer_iso :
  colim_obj SetsParallelColim SetsPairDiagram ≅ DiagBoolSet :=
  coequalizer_of_equal_pair SetsConstTrue
    (coeq_unit_IsCoequalizer SetsParallelColim SetsConstTrue SetsConstTrue).

Definition sets_pullback_iso :
  lim_obj SetsPb SetsCospanDiagram ≅ DiagBoolSet :=
  pullback_of_identity SetsConstTrue
    (pb_counit_IsPullback SetsPb SetsCospanDiagram).

Definition sets_pushout_iso :
  colim_obj SetsPo SetsSpanDiagram ≅ DiagBoolSet :=
  pushout_of_identity SetsConstTrue
    (po_unit_IsPushoutSquare SetsPo SetsSpanDiagram).

Definition sets_equalizer_two_elements :
  { a : carrier (lim_obj SetsEq SetsPairDiagram)
  & { b : carrier (lim_obj SetsEq SetsPairDiagram) & a ≈ b → False } } :=
  sets_two_elements_of_iso sets_equalizer_iso.

Definition sets_coequalizer_two_elements :
  { a : carrier (colim_obj SetsParallelColim SetsPairDiagram)
  & { b : carrier (colim_obj SetsParallelColim SetsPairDiagram)
    & a ≈ b → False } } :=
  sets_two_elements_of_iso sets_coequalizer_iso.

Definition sets_pullback_two_elements :
  { a : carrier (lim_obj SetsPb SetsCospanDiagram)
  & { b : carrier (lim_obj SetsPb SetsCospanDiagram) & a ≈ b → False } } :=
  sets_two_elements_of_iso sets_pullback_iso.

Definition sets_pushout_two_elements :
  { a : carrier (colim_obj SetsPo SetsSpanDiagram)
  & { b : carrier (colim_obj SetsPo SetsSpanDiagram) & a ≈ b → False } } :=
  sets_two_elements_of_iso sets_pushout_iso.

(** ** Readbacks pinning the concrete diagrams  / ** 回读固定具体图表*)

Example sets_pair_arrow_strict :
  fmap[SetsPairDiagram] ((true; ParOne) : ParX ~{Parallel}~> ParY)
    = SetsConstTrue := eq_refl.

Example sets_cospan_arrow_strict :
  fmap[SetsCospanDiagram] (ZeroPos : RPos ~{Roof^op}~> RZero)
    = SetsConstTrue := eq_refl.

Example sets_span_arrow_strict :
  fmap[SetsSpanDiagram] (ZeroPos : RZero ~{Roof}~> RPos)
    = SetsConstTrue := eq_refl.

(** * Readbacks of the four rows against their adjunctions  / * 对照附加词重读四行*)

Section Readbacks.

Context {C : Category}.

Example eq_row_counit (L : HasLimitsOfShape Parallel C)
  (F : Parallel ⟶ C) :
  @counit ([Parallel, C]) C (@Diagonal C Parallel) (EqualizerFunctor L)
          (Diagonal_Equalizer_Adjunction L) F = eq_counit L F := eq_refl.

Example coeq_row_unit (M : HasColimitsOfShape Parallel C)
  (F : Parallel ⟶ C) :
  @unit C ([Parallel, C]) (CoequalizerFunctor M) (@Diagonal C Parallel)
        (Coequalizer_Diagonal_Adjunction M) F = coeq_unit M F := eq_refl.

Example pb_row_counit (L : HasLimitsOfShape (Roof^op) C)
  (F : Roof^op ⟶ C) :
  @counit ([Roof^op, C]) C (@Diagonal C (Roof^op)) (PullbackFunctor L)
          (Diagonal_Pullback_Adjunction L) F = pb_counit L F := eq_refl.

Example po_row_unit (M : HasColimitsOfShape Roof C) (F : Roof ⟶ C) :
  @unit C ([Roof, C]) (PushoutFunctor M) (@Diagonal C Roof)
        (Pushout_Diagonal_Adjunction M) F = po_unit M F := eq_refl.

(* The four functors' object actions are the four (co)limit objects.  / 四个函子的对象动作是四个（共）极限对象。*)

Example EqualizerFunctor_obj (L : HasLimitsOfShape Parallel C)
  {x y : C} (f g : x ~> y) :
  fobj[EqualizerFunctor L] (APair f g) = lim_obj L (APair f g) := eq_refl.

Example CoequalizerFunctor_obj (M : HasColimitsOfShape Parallel C)
  {x y : C} (f g : x ~> y) :
  fobj[CoequalizerFunctor M] (APair f g) = colim_obj M (APair f g) := eq_refl.

Example PullbackFunctor_obj (L : HasLimitsOfShape (Roof^op) C)
  {x y z : C} (f : x ~> z) (g : y ~> z) :
  fobj[PullbackFunctor L] (ACospan f g) = lim_obj L (ACospan f g) := eq_refl.

Example PushoutFunctor_obj (M : HasColimitsOfShape Roof C)
  {S x y : C} (f : S ~> x) (g : S ~> y) :
  fobj[PushoutFunctor M] (ASpan f g) = colim_obj M (ASpan f g) := eq_refl.

(*
The chosen (co)limit of the elementary classes built above is the
   (co)limit object of the corresponding diagram, on the nose. 

--------
上面构建的基本类的选择（共同）限制是
 (co)限制对应图的物体，在鼻子上。 
*)

Example HasEqualizers_apex (L : HasLimitsOfShape Parallel C)
  {x y : C} (f g : x ~> y) :
  projT1 (@equalizer C (HasLimitsOfShape_HasEqualizers L) x y f g)
    = lim_obj L (APair f g) := eq_refl.

Example HasCoequalizers_apex (M : HasColimitsOfShape Parallel C)
  {x y : C} (f g : x ~> y) :
  projT1 (@coeq C (HasColimitsOfShape_HasCoequalizers M) x y f g)
    = colim_obj M (APair f g) := eq_refl.

Example HasPullbacks_apex (L : HasLimitsOfShape (Roof^op) C)
  {x y z : C} (f : x ~> z) (g : y ~> z) :
  Pull f g (@pullback C (HasLimitsOfShape_HasPullbacks L) x y z f g)
    = lim_obj L (ACospan f g) := eq_refl.

Example HasPushouts_apex (M : HasColimitsOfShape Roof C)
  {x y z : C} (f : x ~> y) (g : x ~> z) :
  pushout_apex (@pushout C (HasColimitsOfShape_HasPushouts M) x y z f g)
    = colim_obj M (ASpan f g) := eq_refl.

End Readbacks.

(** * The four rows as biconditionals, and the tree's shape vocabulary  / * 作为双条件的四行，以及树的形状词汇*)

Section Biconditionals.

Context (C : Category).

(*
Riehl's Proposition 4.6.1 at the three finite shapes, by instantiation.
   Read the right-hand sides exactly: they assert the EXISTENCE of an
   adjoint functor, not that it is the one named above. 

--------
通过实例化，Riehl 的命题 4.6.1 在三个有限形状上。 
准确地阅读右侧：它们断言一个事物的存在
 伴随，而不是上面命名的函子。 
*)

Definition equalizers_iff_diagonal_right_adjoint :
  HasLimitsOfShape Parallel C
    ↔ { R : [Parallel, C] ⟶ C & @Diagonal C Parallel ⊣ R } :=
  limits_iff_diagonal_right_adjoint Parallel C.

Definition coequalizers_iff_diagonal_left_adjoint :
  HasColimitsOfShape Parallel C
    ↔ { K : [Parallel, C] ⟶ C & K ⊣ @Diagonal C Parallel } :=
  colimits_iff_diagonal_left_adjoint Parallel C.

Definition pullbacks_iff_diagonal_right_adjoint :
  HasLimitsOfShape (Roof^op) C
    ↔ { R : [Roof^op, C] ⟶ C & @Diagonal C (Roof^op) ⊣ R } :=
  limits_iff_diagonal_right_adjoint (Roof^op) C.

Definition pushouts_iff_diagonal_left_adjoint :
  HasColimitsOfShape Roof C
    ↔ { K : [Roof, C] ⟶ C & K ⊣ @Diagonal C Roof } :=
  colimits_iff_diagonal_left_adjoint Roof C.

(*
The objects of the two Roof-indexed functor categories ARE the tree's
   spans and cospans, and the two shape hypotheses ARE “every cospan has
   a pullback-limit” and “every span has a pushout-colimit”, in the
   vocabulary of Structure/Span.v and Structure/Pullback/Limit.v. 

--------
两个 Roof 索引函子类别的对象是树的
 span 和 cospan，这两个形状假设是“每个 cospan 都有
 回拉限制”和“每个跨度都有推出限制”，在
 Structure/Span.v 和 Structure/Pullback/Limit.v 的词汇表。 
*)

Example cospan_is_pullback_shape : obj[[Roof^op, C]] = Cospan C := eq_refl.

Example span_is_pushout_shape : obj[[Roof, C]] = Span C := eq_refl.

Example pullback_shape_hypothesis :
  HasLimitsOfShape (Roof^op) C = (∀ F : Cospan C, Pullback_Limit F)
  := eq_refl.

Example pushout_shape_hypothesis :
  HasColimitsOfShape Roof C = (∀ F : Span C, Pushout_Limit F) := eq_refl.

(*
The two Parallel rows likewise land on Structure/Equalizer.v's own
   aliases. 

--------
两个平行行同样落在 Structure/Equalizer.v 自己的上
 别名。 
*)

Example equalizer_shape_hypothesis :
  HasLimitsOfShape Parallel C = (∀ F : Parallel ⟶ C, Equalizer F) := eq_refl.

Example coequalizer_shape_hypothesis :
  HasColimitsOfShape Parallel C = (∀ F : Parallel ⟶ C, Coequalizer F)
  := eq_refl.

End Biconditionals.
