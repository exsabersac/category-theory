Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Finite.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Free.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Limit.
Require Import Category.Instance.Rng.Free.
Require Import Category.Instance.Rng.AFT.

Generalizable All Variables.

(* * * Colimits of rings, from the adjoint functor theorem / * * 环的余极限，来自伴随函子定理 *)

(*
 nLab:      https://ncatlab.org/nlab/show/adjoint+functor+theorem
 nLab:      https://ncatlab.org/nlab/show/Ring
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_rings
 Wikipedia: https://en.wikipedia.org/wiki/Free_product_of_associative_algebras

 Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
 §V.7 Exercise 2 (book p. 128, PDF p. 137) asks for the coproduct of two
 rings from the adjoint functor theorem.  Mac Lane's [Rng] is the category
 of rings WITH identity, and so is this tree's: Instance/Rng.v defines
 [Rng] as Theory/Algebra/Rig.v's [Ring], unital rings and unit-preserving
 homomorphisms (the non-unital category is Instance/Rg.v's [Rg]).
 Wikipedia's "Category of rings" records that the coproduct of two rings
 exists and is, for commutative rings, the tensor product over ℤ; for
 rings in general it is a free product, which this file never describes
 element-wise.

 ** THE ISSUE'S SURVEY, MEASURED

 Issue #450 says there is "no [Rng]" (#257).  [Rng] is Instance/Rng.v,
 complete by Instance/Rng/Limit.v's [Rng_Complete], with a free ring
 obtained from [GAFT] in Instance/Rng/AFT.v.  What WAS absent, measured
 at the parent commit (e139ecfb) by [grep -rn --include='*.v'] over the
 whole tree: any [Cocartesian Rng] or [Cocartesian Ring] (pattern
 ['Cocartesian (Rng|Ring)\b'], no hit), any [HasCoequalizers Rng] (no
 hit), and any colimit of rings beyond the initial ring.  A declaration
 typed by a colimit structure on rings, the [git grep -nE] pattern
 [': *@?[A-Za-z]*(Initial|Cocartesian|Coequalizers?|Pushouts?|Cocomplete|Colimit) *[(]?(Rng|Ring|CRng)([^A-Za-z_0-9]|$)']
 at e139ecfb, hits exactly two lines: Instance/Rng.v's
 [Rng_Initial_Z], the initial ring ℤ -- the colimit of the empty
 diagram, at [Set] carriers only (NON-VACUITY, below) -- and its alias
 [roster_Rng_Initial] in Instance/Roster.v.  (Instrument check: with
 [Grp] in place of the ring names the same pattern finds
 Instance/Grp.v's [Grp_Initial] and Instance/Grp/Pushout.v's
 [Grp_HasPushouts] and [Grp_Cocartesian].)

 NAMES.  The issue suggests a module Instance/Rng/Coproduct.v, not
 used, and its verification block runs [Print Assumptions
 Rng_coproduct]; no constant of that name exists (measured: [grep -rnw
 Rng_coproduct] over the [.v] files finds only this paragraph).  The
 coproduct of two rings is this file's [Rng_Cocartesian_via_GAFT].

 ** THE ROUTE

 Exactly Instance/Grp/Colimit.v's, whose header gives the argument in
 full: for each shape J the UNIVERSES section below allows (homs at the
 carrier universe), Adjunction/GAFT.v's [GAFT] is applied to
 the diagonal Δ[J] : Rng ⟶ [J, Rng] ([Rng_colim_via_GAFT]), with
 [Rng_Complete], Adjunction/Diagonal/Limit.v's [Diagonal_continuous]
 through [Continuous_PreservesImageLimit], and a solution set at each
 diagram ([Diagonal_Rng_solution_set]); [Diagonal_left_adjoint_HasColimits]
 then reads the colimits off, and [Rng_Cocomplete_via_GAFT] assembles
 them.

 The solution set indexes [Prop]-valued congruences on
 Instance/Rng/AFT.v's term model [FRTerm] over the free abelian group
 [RGenAb] on the disjoint union [RGen] = Σ j, carrier (D j) (Leibniz
 equality).  A member ([RDCongIdx]) is a relation with a proof of
 [IsRngCoconeCong]: a ring congruence ([IsRngCongruence], Instance/Rng/
 AFT.v) that identifies the letters of `≈`-equal elements ([rcc_resp]),
 makes each insertion preserve zero, addition, one and multiplication
 ([rcc_zero], [rcc_add], [rcc_one], [rcc_mul]) and identifies each
 element with its image under the arrows of the diagram ([rcc_nat]).
 Those clauses make the insertions ring homomorphisms into the quotient
 [RDQ i] ([rdq_leg]; Theory/Algebra/Rig.v's [RigHom] carries all four
 laws as fields, and no smart constructor deriving one of them exists --
 [git grep -n "Build_RigHom'"] at the parent commit e139ecfb returns
 nothing (after #450 its one hit is this sentence) -- whereas
 the group case derives the unit law) and a cocone ([rdq_arr]).
 The covering is the kernel [rng_ker] of the cocone's extension to the
 term model ([rhab], through Instance/Ab/Free.v's [free_ab_extend]),
 which is a cocone congruence ([rker_cocone]) because the target carries
 [rig_prop]; the covering equation holds by [reflexivity], the term
 model's evaluation of an inserted letter computing to the leg.

 [rker_cocone] ENDS IN [Defined], AND MUST, for the reason
 Instance/Grp/Colimit.v gives for [dker_cocone]: measured by closing it
 with [Qed] in a copy of this file, [Diagonal_Rng_solution_set] is then
 refused with "The term "rng_ker_med (rhab c h)" has type "RigHom (QRng
 (rng_ker (rhab c h)) (rng_ker_is_cong (rhab c h))) c" while it is
 expected to have type "RDQ (rker_idx c h) ~{ Rng }~> c"" (universe
 instances elided).

 The finite colimits come from Structure/Limit/Finite.v's bridges, as in
 Instance/Grp/Colimit.v: [Rng_Cocartesian_via_GAFT] is the coproduct of
 rings Mac Lane's Exercise 2 asks for, [Rng_HasCoequalizers_via_GAFT] the
 coequalizers and [Rng_Initial_via_GAFT] the initial ring.  Read off
 the bridges' bodies (Instance/Grp/Colimit.v's FINITE COLIMITS gives
 the detail), the coproduct is the AFT pushout over the AFT initial
 object, the coequalizer is assembled from AFT pushouts and the AFT
 initial object, and the initial ring is the AFT colimit of the empty
 diagram; each of those is itself a [GAFT] colimit at a diagonal.  The
 direct reading at a discrete two-object shape or at the walking
 parallel pair is not the one used.  Nothing in
 this file is registered as an [Instance], and no other [Cocartesian Rng]
 exists in tree to be picked up by resolution.

 ** A CONTRAST WITH GROUPS

 Instance/Grp/Colimit.v proves the injections of a coproduct of groups
 monic; nothing like it is claimed here, and nothing like it holds: in
 the coproduct of ℤ/2 and ℤ/3 the common unit satisfies 2 = 0 and 3 = 0,
 hence 1 = 0, so the coproduct is the zero ring and neither injection is
 monic.  [Rng] has no zero object -- the zero ring is terminal
 (Instance/Rng.v's [Rng_Terminal_zero]) but not initial, there being no
 homomorphism from it to ℤ (Instance/Rg.v's [Rng_terminal_not_initial])
 -- and a zero object is what the group argument,
 Theory/Subobject/Disjoint.v's, needs.  The ℤ/2 ⊔ ℤ/3 computation is a
 remark, not a theorem in tree.

 ** STRENGTHS

 Nothing about a colimit object computes: [GAFT] ends in [Qed], so each
 colimit is an existence result, and every agreement with another
 construction would be an isomorphism.  No such agreement is stated.

 ** UNIVERSES, MEASURED

 By [About] under [Set Printing Universes], dropping bounds on stdlib
 globals: [Diagonal_Rng_solution_set@{u u0 u1 u2 u3}] takes
 J : Category@{u u0 u0} and D : J ⟶ Rng@{u1 u0} and returns
 [SolutionSet@{u2 u1 u1 u0}] with [u0 <= u2] and [Set < u2] on the
 index, and no [Set] bound on the carrier [u0]; [Rng_colim_via_GAFT]
 takes J : Category@{u2 u3 u3} with [u2 <= u3];
 [Rng_Cocomplete_via_GAFT] is [Cocomplete@{u u0 u u1}] with [Set < u],
 [u < u1] and [u0 <= u].  The side condition is [Set < carrier], as for
 [free_ring_via_GAFT], and it is [GAFT]'s, not the solution set's:
 [GAFT] takes its solution set's index AT the carrier universe, and
 this index sits strictly above [Set].  Measured in a scratch file
 under [Monomorphic Constraint Set < gu], at J : Category@{Set Set Set}
 and D : J ⟶ Rng@{gu Set}: [@Diagonal_Rng_solution_set J D] is
 accepted, and [Rng_colim_via_GAFT@{gu _ _ Set Set} J] is refused with
 "Universe inconsistency. Cannot enforce Set < Set because Set = Set."
 Test/ProbeAlgColimit450.v's N5 pins the refusal, with the solution set
 and [GAFT] applied to every argument but it both accepted at the same
 J as its controls.
 [Rng_Cocartesian_via_GAFT] and [Rng_HasCoequalizers_via_GAFT] add the
 strict stdlib bound carrier < [eq_rect_r.u0], inherited from
 Structure/Limit/Finite.v's [FinitelyComplete_HasPullbacks];
 [Rng_Initial_via_GAFT] does not carry it.

 ** NON-VACUITY, AND WHY THE INITIAL RING IS NOT COMPARED

 No nontrivial ring above [Set] is exhibited here.  The natural witness
 would compare [Rng_Initial_via_GAFT] with Instance/Rng.v's ℤ, but
 [About] reads [Rng_Initial_Z@{…} : @Initial Rng@{u Set}]: ℤ is initial
 only at [Set] carriers, while [Rng_colim_via_GAFT] and every colimit
 read off it need [Set < carrier] (UNIVERSES, above: the requirement is
 [GAFT]'s, the solution set itself elaborating at [Set] carriers), so
 the two cannot be stated together.  That is the same kind of donor
 pin #450 lifted for [Grp]'s zero object and [Z2] in Instance/Grp.v; it
 is not lifted for ℤ here.  Test/ProbeAlgColimit450.v's N13 pins the
 refusal of [initial_unique Rng_Initial_via_GAFT Rng_Initial_Z]; it is
 expected to turn over if ℤ's pin is ever lifted, and this paragraph
 then needs a correction.

 ** AXIOMS

 Every constant of this file reports "Closed under the global context".

 ** NOT DELIVERED

 No element-level description of the coproduct (no free product of
 rings, no normal form); no comparison with the tensor product of
 commutative rings; no comparison of the initial ring with ℤ (above);
 no statement about the injections; no explicit coequalizer as a
 quotient by a two-sided ideal (Instance/Rng/Quotient.v's quotient is not
 connected to [Rng_HasCoequalizers_via_GAFT]); nothing registered as an
 [Instance]. 

 --------
 nLab:       https://ncatlab.org/nlab/show/adjoint+functor+theorem 
 nLab:       https://ncatlab.org/nlab/show/Ring 
 维基百科:  https://en.wikipedia.org/wiki/Category_of_rings 
 维基百科:  https://en.wikipedia.org/wiki/Free_product_of_associative_algebras 

 Mac Lane，《为在职数学家准备的范畴论》，第2版（GTM 5），
 §V.7 第2题（书本第128页，PDF第137页）要求通过伴随函子定理求两个环的余积。Mac Lane 的 [Rng] 是带单位的环的范畴，这个树上的也一样：Instance/Rng.v 将 [Rng] 定义为 Theory/Algebra/Rig.v 的 [Ring]，即带单位环以及保持单位的同态（非单位范畴是 Instance/Rg.v 的 [Rg]）。
 维基百科的“环的范畴”记载了两个环的余积存在，对于交换环，其余积是 ℤ 上的张量积；对于一般的环，它是自由积，而这个文件从未以元素方式描述过。

 ** 问题的概述，已测量问题 #450 表示没有 "[Rng]" (#257)。[Rng] 是 Instance/Rng.v，通过 Instance/Rng/Limit.v 的 [Rng_Complete] 完成，并且有一个自由环是从 Instance/Rng/AFT.v 的 [GAFT] 获取的。在父提交 (e139ecfb) 上，由 [grep -rn --include='*.v'] 对整个树测量的缺失内容包括：任何 [Cocartesian Rng] 或 [Cocartesian Ring]（模式 ['Cocartesian (Rng|Ring)\b']，没有命中），任何 [HasCoequalizers Rng]（没有命中），以及初始环之外的任何环的余极限。一个声明
 由环上的余极限结构键入，[git grep -nE] 模式
 [': *@?[A-Za-z] *(初始|余笛卡尔|余等化?|推挤?|完备余极限|余极限) * [(] ?(Rng|Ring|CRng)( [^A-Za-z_0-9] |$)']
 在 e139ecfb 上，精确匹配两行：Instance/Rng.v 的
 [Rng_Initial_Z] ，初始环 ℤ -- 空图的余极限，在 [Set] 仅包含承载者（非空性，见下文）-- 及其别名
 [roster_Rng_Initial] 在 Instance/Roster.v 中。（工具检查：用 [Grp] 代替环名称，相同模式可以找到
 Instance/Grp.v 的 [Grp_Initial] 和 Instance/Grp/Pushout.v 的 [Grp_HasPushouts] 及 [Grp_Cocartesian]。）名称。该问题涉及一个模块 Instance/Rng/Coproduct.v，它未被使用，其验证块运行 [Print Assumptions Rng_coproduct]；不存在该名称的常量（测量：在 [.v] 文件中对 Rng_coproduct 进行 [grep -rnw] 仅找到这一段）。两个环的余积就是本文件的 [Rng_Cocartesian_via_GAFT]。

 ** 路径

 完全是 Instance/Grp/Colimit.v 的，其头部完整给出了参数：对于每个形状 J，下面的 UNIVERSES 部分允许（载体宇宙上的同态），Adjunction/GAFT.v 的 [GAFT] 应用于对角线 Δ [J] : Rng ⟶ [J, Rng] ([Rng_colim_via_GAFT])，以及 [Rng_Complete]，Adjunction/Diagonal/Limit.v 的 [Diagonal_continuous] 通过 [Continuous_PreservesImageLimit]，并且在每个图表处有一个解集 ([Diagonal_Rng_solution_set])；[Diagonal_left_adjoint_HasColimits] 然后读取余极限，[Rng_Cocomplete_via_GAFT] 组装它们。解集索引 [Prop] 值模在 Instance/Rng/AFT.v 的项模型 [FRTerm] 上的自由阿贝尔群 [RGenAb] 对于不相交并集 [RGen] = Σ j, carrier (D j)（莱布尼茨相等）的同余。一个成员（[RDCongIdx]）是一个关系，并带有 [IsRngCoconeCong] 的证明：一个环同余（[IsRngCongruence]，Instance/Rng/AFT.v），它识别 `≈`-相等元素（[rcc_resp]）的字母，使每个插入保持零、加法、一和乘法（[rcc_zero]、[rcc_add]、[rcc_one]、[rcc_mul]），并将每个元素与其在图的箭头下的像（[rcc_nat]）识别起来。这些子句使插入成为商环中的环同态  [RDQ i]  （[rdq_leg]；Theory/Algebra/Rig.v 的 [RigHom]  作为域承载所有四个定律，并且不存在派生其中一个的智能构造函数 -- [git grep -n "Build_RigHom'"] 在父提交 e139ecfb 返回无（在 #450 之后，它的唯一一次命中是这个句子）-- 而群的情况派生单位定律）以及一个余圆锥（[rdq_arr]）。覆盖是余圆锥扩展到项模型（[rhab]，通过 Instance/Ab/Free.v 的 [free_ab_extend]）的核 [rng_ker]，它是一个余圆锥同余（[rker_cocone]），因为目标承载 [rig_prop]；覆盖方程通过 [reflexivity] 成立，项模型对插入字母的求值结果计算到腿上。[rker_cocone] 以 [Defined] 结束，并且必须这样，原因是
 Instance/Grp/Colimit.v 对 [dker_cocone] 给出的说明：通过在该文件的副本中用 [Qed] 封闭它来测量，[Diagonal_Rng_solution_set] 随后被拒绝，并显示“术语 "rng_ker_med (rhab c h)" 的类型为 "RigHom (QRng (rng_ker (rhab c h)) (rng_ker_is_cong (rhab c h))) c"，而它预期的类型为 "RDQ (rker_idx c h) ~{ Rng }~> c"”（省略了宇宙实例）。有限余极限来自 Structure/Limit/Finite.v 的桥梁，如在 Instance/Grp/Colimit.v 中：[Rng_Cocartesian_via_GAFT] 是 Mac Lane 练习 2 要求的环的直和，[Rng_HasCoequalizers_via_GAFT] 是余等化器，[Rng_Initial_via_GAFT] 是初始环。读取桥梁的主体（Instance/Grp/Colimit.v 的 FINITE COLIMITS 给出了详细信息），直和是 AFT 初始对象上的 AFT 推出，余等化器由 AFT 推出和 AFT 初始对象组成，初始环是空图的 AFT 余极限；其中每一个自身都是在对角线上的 [GAFT] 余极限。在离散的两个对象形状或行走平行对上直接读取的并不是使用的方式。该文件中没有被注册为 [Instance]，树中也不存在其他 [Cocartesian Rng] 可由推理选取。** 与群的对比

 Instance/Grp/Colimit.v 证明了群的直和的单射是单的；这里并没有声称类似的内容，而且也不存在类似的情况：在 ℤ/2 和 ℤ/3 的直和中，共同单位满足 2 = 0 和 3 = 0，因此 1 = 0，所以直和是零环，两个注入都不是单射。[Rng] 没有零对象——零环是终对象（Instance/Rng.v 的 [Rng_Terminal_zero]），但不是初对象，因为不存在从它到 ℤ 的同态（Instance/Rg.v 的 [Rng_terminal_not_initial]）——而零对象正是那个群论论证（Theory/Subobject/Disjoint.v 所需的）所需要的。ℤ/2 ⊔ ℤ/3 的计算只是一个备注，不是 tree 中的定理。

 ** 优势没有关于余极限对象的计算：[GAFT] 以 [Qed] 结尾，因此每个余极限都是一个存在性结果，并且与其他构造的任何一致将是一个同构。没有声明这种一致。

 ** 宇宙，测量由 [About] 在 [Set Printing Universes] 下，放宽 stdlib 的界限
 全局变量：[Diagonal_Rng_solution_set@{u u0 u1 u2 u3}] 接受
 J : Category@{u u0 u0} 和 D : J ⟶ Rng@{u1 u0} 并返回
 [SolutionSet@{u2 u1 u1 u0}]，带有 [u0 <= u2] 和 [Set < u2] 在索引上，并且在载体 [u0] 上没有 [Set] 的界限；[Rng_colim_via_GAFT]
 接受 J : Category@{u2 u3 u3} ，带有 [u2 <= u3]；
 [Rng_Cocomplete_via_GAFT] 是 [Cocomplete@{u u0 u u1}]，带有 [Set < u]、
 [u < u1] 和 [u0 <= u]。附带条件是 [Set < carrier]，如同 [free_ring_via_GAFT]，且它是 [GAFT] 的，而不是解集的：
 [GAFT] 在其解集的载体宇宙上获取索引，并且该索引严格高于 [Set]。 在 [Monomorphic Constraint Set < gu] 下的临时文件中测量，在 J : Category@{Set Set Set}
 和 D : J ⟶ Rng@{gu Set}：[@Diagonal_Rng_solution_set J D] 被接受，而 [Rng_colim_via_GAFT@{gu _ _ Set Set} J] 被拒绝并显示
 “宇宙不一致。”无法强制执行 Set < Set，因为 Set = Set。
 Test/ProbeAlgColimit450.v 的 N5 固定了拒绝，具有解集，并且 [GAFT] 应用于每个参数，但它在与其控件相同的 J 上都被接受。[Rng_Cocartesian_via_GAFT] 和 [Rng_HasCoequalizers_via_GAFT] 添加了严格的 stdlib 有界承载 < [eq_rect_r.u0]，从 Structure/Limit/Finite.v 的 [FinitelyComplete_HasPullbacks] 继承；[Rng_Initial_via_GAFT] 不携带它。

 ** 非空性，以及为什么初始环没有被比较这里没有展示 [Set] 之上的非平凡环。自然的证据会将 [Rng_Initial_via_GAFT] 与 Instance/Rng.v 中的 ℤ 进行比较，但 [About] 仅在 [Set] 承载类型下读取 [Rng_Initial_Z@{…} : @Initial Rng@{u Set}] : ℤ 是初始的，而 [Rng_colim_via_GAFT] 及其每个余极限读取它都需要 [Set < carrier]（宇宙，上述要求是 [GAFT] 的，解集本身在 [Set] 承载类型上展开），所以这两者不能同时陈述。这与 Instance/Grp.v 中为 [Grp] 的零对象和 [Z2] 提出的 donor 引脚 #450 是同一种情况；这里 ℤ 没有被提升。Test/ProbeAlgColimit450.v 的 N13 引脚钉住了 [initial_unique Rng_Initial_via_GAFT Rng_Initial_Z] 的拒绝；如果 ℤ 的引脚被提升，预计它会翻转，那么这一段就需要修正。

 ** 公理这个文件的每个常量都报告“在全局上下文下关闭”。

 ** 未交付

 没有关于余积的元素级描述（没有环的自由积，没有规范形式）；没有与交换环的张量积的比较；没有将初始环与 ℤ 的比较（如上所述）；没有关于注射的声明；没有明确的以双边理想为商的余等化（Instance/Rng/Quotient.v 的商与 [Rng_HasCoequalizers_via_GAFT] 无关）；没有注册为 [Instance] 。
*)

(** ** The solution set at a diagram / ** 图表上的解集 *)

Section RngDiagonalSolutionSet.

Context {J : Category}.
Context (D : J ⟶ Rng).

(* The generators: the disjoint union of the carriers, with Leibniz equality, and the free abelian group on them. / 生成元：载体的互不相交并集，带有莱布尼茨等式，以及在它们上的自由阿贝尔群。 *)
Definition RGen : SetoidObject :=
  {| carrier := { j : obj[J] & carrier (rig_setoid (D j)) };
     is_setoid := eq_Setoid _ |}.

Definition RGenAb : AbObject := FreeAbObject RGen.

Definition rins (j : J) (a : carrier (rig_setoid (D j))) : FRTerm RGenAb :=
  @fr_gen RGenAb (@fa_gen RGen (j; a)).

(* A congruence on the term model that makes the insertions a cocone of ring homomorphisms. / 在项模型上的一个同余，使得插入成为环同态的余锥。 *)
Record IsRngCoconeCong (Rq : FRTerm RGenAb → FRTerm RGenAb → Prop) : Prop := {
  rcc_rng  : IsRngCongruence Rq;
  rcc_resp : ∀ j a b, a ≈ b → Rq (rins j a) (rins j b);
  rcc_zero : ∀ j, Rq (rins j (rig_zero (D j))) (@fr_zero RGenAb);
  rcc_add  : ∀ j a b, Rq (rins j (rig_add (D j) a b))
                         (@fr_plus RGenAb (rins j a) (rins j b));
  rcc_one  : ∀ j, Rq (rins j (rig_one (D j))) (@fr_one RGenAb);
  rcc_mul  : ∀ j a b, Rq (rins j (rig_mul (D j) a b))
                         (@fr_mul RGenAb (rins j a) (rins j b));
  rcc_nat  : ∀ j k (f : j ~{J}~> k) a,
               Rq (rins k (rig_map (fmap[D] f) a)) (rins j a)
}.

Definition RDCongIdx : Type :=
  { Rq : FRTerm RGenAb → FRTerm RGenAb → Prop & IsRngCoconeCong Rq }.

Definition RDQ (i : RDCongIdx) : obj[Rng] := QRng (`1 i) (rcc_rng _ (`2 i)).

Definition rdq_leg (i : RDCongIdx) (j : J) : D j ~{Rng}~> RDQ i.
Proof.
  unshelve refine (@Build_RigHom (D j) (RDQ i)
                     {| morphism := rins j |} _ _ _ _).
  - intros a b Hab; exact (rcc_resp _ (`2 i) j a b Hab).
  - exact (rcc_zero _ (`2 i) j).
  - intros a b; exact (rcc_add _ (`2 i) j a b).
  - exact (rcc_one _ (`2 i) j).
  - intros a b; exact (rcc_mul _ (`2 i) j a b).
Defined.

Definition rdq_arr (i : RDCongIdx) :
  D ~{[J, Rng]}~> fobj[@Diagonal Rng J] (RDQ i).
Proof.
  unshelve refine (@Build_Transform' J Rng D (fobj[@Diagonal Rng J] (RDQ i))
                     (fun j => rdq_leg i j) _).
  intros j k f a; simpl.
  apply (rc_sym _ _ (rcc_rng _ (`2 i))).
  exact (rcc_nat _ (`2 i) j k f a).
Defined.

(* The covering: the kernel of a cocone's extension to the term model. / 覆盖：余圆扩展到项模型的核心。 *)
Section Cover.

Context (c : Rng) (h : D ~{[J, Rng]}~> fobj[@Diagonal Rng J] c).

Definition rflat : RGen ~{Sets}~> Ab_Forget (Rng_Forget_Ab c).
Proof using h.
  unshelve refine {| morphism := fun p => rig_map (transform[h] (`1 p)) (`2 p) |}.
  intros p q Hpq; simpl in Hpq; subst; reflexivity.
Defined.

Definition rhab : RGenAb ~{Ab}~> Rng_Forget_Ab c :=
  @free_ab_extend RGen (Rng_Forget_Ab c) rflat.

(* Transparent on purpose: see the header. / 故意透明：请参阅标题。 *)
Lemma rker_cocone : IsRngCoconeCong (rng_ker rhab).
Proof using h.
  constructor.
  - exact (rng_ker_is_cong rhab).
  - intros j a b Hab; unfold rng_ker; apply (@pequiv_from _ _ (rig_prop c)); simpl.
    now rewrite Hab.
  - intros j; unfold rng_ker; apply (@pequiv_from _ _ (rig_prop c)); simpl.
    apply (rig_map_zero (transform[h] j)).
  - intros j a b; unfold rng_ker; apply (@pequiv_from _ _ (rig_prop c)); simpl.
    apply (rig_map_add (transform[h] j)).
  - intros j; unfold rng_ker; apply (@pequiv_from _ _ (rig_prop c)); simpl.
    apply (rig_map_one (transform[h] j)).
  - intros j a b; unfold rng_ker; apply (@pequiv_from _ _ (rig_prop c)); simpl.
    apply (rig_map_mul (transform[h] j)).
  - intros j k f a; unfold rng_ker; apply (@pequiv_from _ _ (rig_prop c)); simpl.
    pose proof (@naturality_sym _ _ _ _ h j k f a) as Hn; simpl in Hn.
    rewrite Hn; reflexivity.
Defined.

Definition rker_idx : RDCongIdx := (rng_ker rhab; rker_cocone).

End Cover.

Definition Diagonal_Rng_solution_set : SolutionSet (@Diagonal Rng J) D.
Proof.
  unshelve refine (@Build_SolutionSet Rng ([J, Rng]) (@Diagonal Rng J) D
                     RDCongIdx RDQ rdq_arr _).
  intros c h.
  exists (rker_idx c h).
  exists (rng_ker_med (rhab c h)).
  intros j a; simpl.
  reflexivity.
Defined.

End RngDiagonalSolutionSet.

(* * ** Every colimit of rings within the shape discipline / * ** 在形状学科中的每个环的余极限 *)

Definition Rng_colim_via_GAFT (J : Category) :
  { K : [J, Rng] ⟶ Rng & K ⊣ @Diagonal Rng J } :=
  GAFT (@Diagonal Rng J) Rng_Complete
       (Continuous_PreservesImageLimit Diagonal_continuous)
       (@Diagonal_Rng_solution_set J).

Definition Rng_Cocomplete_via_GAFT : @Cocomplete Rng :=
  fun J F => Diagonal_left_adjoint_HasColimits (projT2 (Rng_colim_via_GAFT J)) F.

(* * ** The coproduct of rings, coequalizers and the initial ring / * ** 环的余积、共同化子与初等环 *)

Definition Rng_FinitelyCocomplete_via_GAFT : @FinitelyCocomplete Rng :=
  Cocomplete_FinitelyCocomplete Rng_Cocomplete_via_GAFT.

(* Mac Lane §V.7 Exercise 2. / 麦克莱恩 §V.7 练习 2。 *)
Definition Rng_Cocartesian_via_GAFT : @Cocartesian Rng :=
  FinitelyComplete_Cartesian
    (FinitelyCocomplete_FinitelyComplete_op Rng_FinitelyCocomplete_via_GAFT).

Definition Rng_HasCoequalizers_via_GAFT : HasCoequalizers Rng :=
  HasCoequalizers_of_HasEqualizers_op
    (FinitelyComplete_HasEqualizers
       (FinitelyCocomplete_FinitelyComplete_op Rng_FinitelyCocomplete_via_GAFT)).

Definition Rng_Initial_via_GAFT : @Initial Rng :=
  FinitelyCocomplete_Initial Rng_FinitelyCocomplete_via_GAFT.
