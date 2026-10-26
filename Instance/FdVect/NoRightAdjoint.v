Require Import Coq.Lists.List.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Adjunction.Right.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Adjunction.Continuity.
Require Import Category.Structure.Monoidal.StarAutonomous.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Quotient.
Require Import Category.Instance.Mod.Product.
Require Import Category.Instance.Mod.Tensor.
Require Import Category.Instance.Mod.Closed.
Require Import Category.Instance.FdVect.
Require Import Category.Instance.FdVect.DoubleDual.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

(*
   * * The dual functor on vector spaces has no right adjoint

   Mac Lane §V.5 Exercise 2 (book p. 120, `maclane:V.5:ex2`, #433): the
   dualization functor D : Vct^op ⟶ Vct, adjoint to itself on the right,
   has no right adjoint, so it is not the left adjoint of its opposite.
   The tree has TWO readings of D over Instance/FdVect.v's [Vct_F F :=
   RMod (field_ring F)]: Instance/FdVect/DoubleDual.v's [Dual F], on
   ALL F-modules with precomposition on the nose ([dual_precompose]),
   and Structure/Monoidal/StarAutonomous.v's dual-object functor
   [dual] read at the line through Instance/Mod/Closed.v's
   [RMod_SymMonClosed] — here [VctDual359], the functor the issue names,
   since Structure/Monoidal/Dual.v (#359) proves it adjoint to itself on
   the right ([dual_self_adjoint_on_the_right]).  The exercise is
   proved for BOTH: for [Dual F] directly ([dual_functor_no_right_adjoint]
   and its corollary [dual_not_left_adjoint_of_op]) and for [VctDual359]
   by transport along the natural isomorphism [dual_iso359 : Dual F ≈
   VctDual359] ([dual359_no_right_adjoint], [dual359_not_left_adjoint_of_op]).
   The file sits beside [Dual], where the issue's placement clause puts it.

   STALE PREMISES.  The issue's “Current state” says the tree has no
   category of vector spaces and no dual functor: FALSE twice — [Vct_F] and
   [Dual] above, with [DualMod], [eta] and [double_dual_natural]
   beside them.  It calls the dual-object functor “#359's”: [dual] is
   StarAutonomous.v's (2026-07-10), and #359 added the self-adjunction.
   The two readings are different [Program] records, naturally isomorphic
   but NOT convertible (probe N1), not even objectwise (N5: the carriers of
   [VctDual359 x] and [Dual F x] coincide at [eq_refl], the packed modules
   do not — [HomMod]'s and [DualMod]'s proof fields are different opaque
   constants).  DoubleDual.v said [Vct_F F] “lacked” a monoidal
   structure — stale since Instance/Mod/Monoidal.v and Instance/Mod/
   Closed.v (2026-08-31); repaired in place, line-neutrally.  And the
   exercise is FALSE over [FdVect F]: DoubleDual.v's [DualFd] is
   pointwise invertible by [double_dual_iso], mathematically an
   equivalence with adjoints on both sides (not formalized as such) — the
   statement needs infinite dimension, which is why everything here runs
   in [Vct_F F].

   THE MATHEMATICS AND ITS BOUNDARY.  A right adjoint of D would make D a
   left adjoint, hence carry colimit cocones to colimit cocones
   (Adjunction/Continuity.v [left_adjoint_PreservesColimitCocone]).
   D's source is Vct^op, so a colimit there is a PRODUCT in Vct: Mac
   Lane's is the countable power F^ℕ, whose dual (F^ℕ)* would have to be
   the direct sum ⊕_ℕ F of the coordinate functionals if D preserved it.
   (The issue's own sentence, “the dual of a direct sum is a product”,
   describes the OTHER direction: D does carry the direct sum ⊕_ℕ F, a
   colimit of Vct, to a product — that is the positive half below, not
   the obstruction.)  The tree has no indexed coproducts in [RMod R], and
   none is needed: the power is [PowLine := ProdMod (fun _ => VctLine)] of
   Instance/Mod/Product.v (new, #433) with coordinate projections
   [vct_coord n], packaged as [PowCocone : Cocone LineDiagram] over the
   constant discrete diagram [LineDiagram : DiscreteCat nat ⟶ Vct^op] and
   proved colimiting, [PowCocone_IsColimitCocone], by [prod_tuple] — the
   CONCRETE colimit the issue's reviewer asks for.  Its image under D is
   the cocone of coordinate functionals [D (vct_coord n) : D VctLine ~>
   D PowLine], ψ ↦ ψ ∘ coord n.  If that image were colimiting, the two
   mediators to the competing cocone [ZeroCocone] (apex: the quotient
   [SpanQuot] of D PowLine by the span [SpanCoords] of the coordinate
   functionals; legs: the quotient map [span_quot] after each
   D (vct_coord n)) — the quotient map itself and the zero map
   [vct_zero_hom], both compatible because every ψ ∘ coord n lies in the
   span ([dual_coord_in_span], the ONE place field commutativity is spent)
   — would coincide, so every functional on F^ℕ would lie in the span.
   Mac Lane's own sentence is that some functional does not; that is
   [CoordSpanProper : Type], and [dual_not_PreservesColimitCocone (H :
   CoordSpanProper)] closes the argument through Instance/Mod/Quotient.v's
   [mquot_proj_kills] and [mquot_proj_kernel]; [dual_functor_no_right_adjoint]
   is the exercise and [dual_not_left_adjoint_of_op] its corollary, both
   one-line compositions.

   WHY CONDITIONAL — analysis, not formalized.  Classically
   [CoordSpanProper F] holds for every field (Erdős–Kaplansky: the dual of
   an infinite-dimensional space has dimension |F|^dim, so countably many
   coordinates cannot span it), but it is NOT provable without choice: in
   a model of ZF + DC where every set of reals has the Baire property
   (Solovay; Shelah), every additive map ℚ^ℕ → ℚ is continuous by Pettis'
   automatic-continuity theorem, and a continuous functional on ℚ^ℕ with
   ℚ discrete vanishes on a basic neighbourhood of 0, so it is a finite
   combination of coordinates.  For F = ℚ the premise is therefore
   independent of ZF + DC, and no axiom-free witness can be built in this
   tree; docs/INHABITATION.md records the row as one that will never get a
   constructive inhabitant, unlike the “awaiting a model” rows.  Finite
   shapes give no obstruction (finite products of modules are biproducts,
   which D carries to biproducts — analysis again), so the countability is
   load-bearing here, where in Instance/Ab/FreeNotContinuous.v (#430) it
   was inert.

   THE UNCONDITIONAL HALF.  [vct_transpose f := fmap[Dual F] f ∘ eta F x]
   turns a ~> D x into x ~> D a and is an involution
   ([vct_transpose_invol], [reflexivity] after [simpl]); its
   respectfulness, the two round trips and the four naturality squares are
   closed by the tree's default tactic: [dual_vct_AdjointOnTheRight :
   AdjointOnTheRight (Dual F) (Dual F)] (Adjunction/Right.v's class),
   [dual_vct_Adjunction : (Dual F)^op ⊣ Dual F] through
   [Adjunction_of_AdjointOnTheRight], and Mac Lane's contrast
   [dual_vct_Continuous : ContinuousFunctor (Dual F)] by RAPL
   (Adjunction/Continuity.v [right_adjoint_Continuous]).  The
   direction matters and the probe pins it (N3): the self-adjunction runs
   [(Dual F)^op ⊣ Dual F]; the exercise's [Dual F ⊣ (Dual F)^op] is
   exactly the ascription that is refused.

   THE FUNCTOR THE ISSUE NAMES.  [VctDual359 x] is the internal hom
   [HomMod x VctLine]; its carrier, zero, sum and scalar action coincide
   with [DualMod]'s at [eq_refl], so the identity on functionals is a
   module homomorphism each way ([to359], [from359], packaged as
   [iso359]).  [dual]'s arrow action is the closed transpose of
   evaluation, [dcur (eval' ∘ (id ⨂ f))], an OPAQUE mediator
   (StarAutonomous.v's [dcur] is the [unique_obj] of [ump_exponents], which
   at RMod is the `Qed` theorem [ump_exponents_Mod]), so it does not compute;
   [dual359_fmap_pre] identifies it with precomposition by the uniqueness
   clause [dcur_uniq], checked on the tensor's generators through
   Instance/Mod/Tensor.v's [tensor_hom_ext] by [reflexivity].  That gives
   [dual_iso359 : Dual F ≈ VctDual359] in [Fun]'s [≈] (Theory/Functor.v's
   [Functor_Setoid], a bundled natural isomorphism), and
   Theory/Adjunction.v's [adjunction_along_left_iso] (#431) turns any
   [VctDual359 ⊣ Rt] into [Dual F ⊣ Rt], so [dual359_no_right_adjoint]
   and [dual359_not_left_adjoint_of_op] follow from the refutation above.

   UNIVERSES ([About] under `Set Printing Universes`, all 41 heads).  No
   [Set] anywhere: the shape is Structure/Limit/Comparison.v's
   annotated [DiscreteCat_Functor'], because Instance/Discrete.v's
   unannotated [DiscreteCat_Functor] pins the shape's hom level to [Set]
   and no cocone in Vct^op can share it (probe N4, “Cannot enforce Set =
   …”).  Every head but [vct_zero_hom] carries the two equations `u0 = u`,
   `u1 = u` identifying the three [FieldObject] levels — they arrive with
   [VctLine := Ring_RMod (field_ring F)] and with [Dual@{u u u _}] alike,
   and [vct_zero_hom], stated over bare objects of Vct, carries none.
   Strict constraints are of one kind, the field levels below the
   category's object level (`u < u2` and its renamings; the four
   list-shaped heads [span_sum], [span_sum_app], [span_sum_scale] and
   [dual_coord_in_span] state it for all three identified levels), plus
   [dual_vct_Continuous]'s shape level (`u5 < u2`) and [vct_zero_hom]'s
   second object level (`u < u3`).  Stdlib caps by FIRST carrier in file
   order: `Basics.compose` and `ID` at [VctLine] (inherited from
   Instance/FdVect.v), `prod_rect` at [vct_zero_hom], `list_rect` and
   `app` at [span_sum_app], `ListDef.Map` and `projections` at
   [span_sum_scale], `JMeq`, `eq`, `eq_ind`, `eq_ind_r`, `eq_rect_r`,
   `EqdepFacts.eq_sigT_sig_eq` and `Logic_lemmas.equality` at
   [LineDiagram] (inherited from [DiscreteCat_Functor']; the shape's hom
   is [eq]), and Specif's `Projections` at [CoordSpanProper] (a sigma
   type).

   MEASURED.  41 `.glob` heads (34 `def`, 7 `prf`) and 17 [Program]
   obligations (8 closed by hand under [Obligation Tactic := idtac] for
   [vct_zero_hom] and [SpanCoords], 9 by [cat_simpl] for the four records
   [vct_transpose_morphism], [vct_aor], [dual_vct_AdjointOnTheRight] and
   [iso359]), all 58 “Closed under the global context”, zero `Axioms:`
   lines; the `make print-assumptions` gate carries the 41 heads.  Six
   `Defined`, each LOAD-BEARING (flipped to `Qed` one at a time in a copy
   of the whole file: [op_discrete_cone] stops [PowCocone_IsColimitCocone],
   [ZeroCocone] stops [dual_not_PreservesColimitCocone],
   [PowCocone_IsColimitCocone] stops the readback
   [pow_cocone_mediator_component], [to359] and [from359] stop
   [dual_iso359]'s proof, and [dual_iso359] stops the readback
   [iso359_to_component] — the two readbacks exist for that reason);
   fourteen `Qed`.  Closure 103 files excluding self (Adjunction/Right.v
   18 at the margin, Structure/Limit/Comparison.v 5, Instance/Mod/Closed.v
   2, Instance/Mod/Quotient.v 2, DoubleDual.v 1, Instance/Mod/Product.v 1,
   the other nineteen `Require`s 0; none of the 25 is droppable — each
   was removed in a copy of the file and the copy stopped compiling).
   Zero name collisions for the 41 names (`grep -rlw --include='*.v'`;
   DoubleDual.v's header mentions [dual_iso359] by design; [SpanQuot],
   [span_quot] and Product.v's [modprod_*] were chosen because
   Construction/PROP/Presentation.v owns [quot] and Lib/Datatypes.v
   owns [prod_setoid]).  Test/ProbeDualNoRightAdjoint433.v mirrors the
   `Require` list plus Structure/Monoidal/Dual.v (the #359 control) and
   Structure/Limit/Product.v (the indexed-product readback) and carries 6
   refutation commands = 1 instrument + N1, N5 CONVERSION ([VctDual359 F =
   Dual F] at [eq_refl]: “has type VctDual359 F = VctDual359 F while it is
   expected to have type VctDual359 F = Dual F”; objectwise the same, with
   the carriers accepted beside it) + N2-N3 TYPING (the unconditional
   [∀ Rt, Dual F ⊣ Rt → False] does not ascribe; the exercise's direction
   of the self-adjunction is refused) + N4 UNIVERSE, each stripped one at
   a time in a copy of the whole file beside its accepted control; seven
   `eq_refl` readbacks; guard coverage 25/19 with six exhaustive
   exceptions (identifier tokens inside the six refutation commands /
   also named outside them, comments stripped; the exceptions are the
   refutation keyword itself, `fun`, `obj`, the two refuted Examples' own
   names and the instrument's absent name); rename-simulated 16 library
   names — [VctDual359], [Dual],
   [dual_functor_no_right_adjoint], [dual_vct_Adjunction],
   [Opposite_Functor], [Cocone], [DiscreteCat_Functor], [VctLine],
   [LineDiagram], [CoordSpanProper], [eq_refl], [False], [nat], [Vct_F],
   [carrier], [cmon_setoid] — every first break on a positive line.
   `make todo` grows by the 6 refutation lines only (2266 → 2272 over
   64b94901), so the issue's “adds no new hits” box is not met as written
   (disclosed, as in #430); the Coq 8.19 and 8.20 boxes are checked by nix
   source builds of the committed revision, which the PR records.

   NOT DELIVERED: the unconditional refutation (impossible without a
   choice principle, above); the [HasIndexedProducts (RMod R)] instance
   and indexed coproducts ⊕_I (Product.v's header); the isomorphism of the
   two duals in any form other than [Functor_Setoid]'s (no [⟹] pair, no
   [≅] in a functor category — the bundled form is what
   [adjunction_along_left_iso] consumes); a self-adjunction of
   [VctDual359] of this file's own (#359's is the probe's control);
   anything over [FdVect F], where the exercise is false; no edit to
   Instance/FdVect.v, Instance/Mod.v, Instance/Mod/Quotient.v,
   Instance/Mod/Closed.v, Structure/Monoidal/StarAutonomous.v,
   Structure/Monoidal/Dual.v, Structure/Limit/Comparison.v or
   Adjunction/Continuity.v. 

   --------
   * * 向量空间上的对偶函子没有右伴随函子Mac Lane §V.5 练习 2（书籍第 120 页，`maclane:V.5:ex2`，#433）：函子对偶化 D : Vct^op ⟶ Vct，自身在右边是伴随的，它没有右伴随，因此它不是其对偶的左伴随。该树对 Instance/FdVect.v 的 [Vct_F F := RMod (field_ring F)] 上的 D 有两种读取方式：Instance/FdVect/DoubleDual.v 的 [Dual F]，在所有 F-模上并且使用原样前组合（[dual_precompose]），以及 Structure/Monoidal/StarAutonomous.v 的对偶对象函子 [dual]，在 Instance/Mod/Closed.v 的 [RMod_SymMonClosed] 的行上读取 — 此处 [VctDual359]，即问题中命名的函子，因为 Structure/Monoidal/Dual.v (#359) 证明它在右边自伴随（[dual_self_adjoint_on_the_right]）。该练习已被证明适用于两者：直接适用于 [Dual F]（[dual_functor_no_right_adjoint] 及其推论 [dual_not_left_adjoint_of_op]）以及通过沿着自然同构 [dual_iso359 : Dual F ≈ VctDual359]（[dual359_no_right_adjoint]，[dual359_not_left_adjoint_of_op]）传递适用于 [VctDual359]。该文件与 [Dual] 并列放置，这是该问题的放置条款所指定的位置。陈旧前提。问题的“当前状态”显示该树没有向量空间类别，也没有对偶函子：两次为假 — 上述 [Vct_F] 和 [Dual]，旁边是 [DualMod]、[eta] 和 [double_dual_natural]。它将对偶对象函子称为“#359 的”：[dual] 是 StarAutonomous.v 的（2026-07-10），而 #359 添加了自伴随。两种读法不同 [Program] 记录，自然同构但不可转换（探针 N1），甚至对象层面也不可转换（N5：[VctDual359 x] 和 [Dual F x] 的承载在 [eq_refl] 上相同，但打包模块不同 — [HomMod] 的和 [DualMod] 的证明字段是不同的不透明常数）。DoubleDual.v 说 [Vct_F F] “缺少”一个单对象结构——自 Instance/Mod/Monoidal.v 和 Instance/Mod/Closed.v (2026-08-31) 以来一直如此；已在原地修复，且不影响行数。而且对于 [FdVect F]，这个练习是 FALSE ：DoubleDual.v 的 [DualFd] 在 [double_dual_iso] 下是逐点可逆的，从数学上讲这是一个带有双边伴随的等价（未正式形式化）——该命题需要无限维，这也是这里的一切在 [Vct_F F] 中运行的原因。数学及其边界。D 的右伴随会使 D 成为左伴随，从而将余极限锥映射为余极限锥（Adjunction/Continuity.v  [left_adjoint_PreservesColimitCocone]）。D 的源是 Vct^op，因此那里的余极限在 Vct 中是一个积：Mac Lane 的例子是可数次方 F^ℕ，其对偶 (F^ℕ)* 如果 D 保持它，则必须是坐标泛函的直和 ⊕_ℕ F。(问题自身的句子，“直和的对偶是积”，描述了相反的方向：D 确实将直和 ⊕_ℕ F，一个 Vct 的余极限，映射为积——这是下面的积极部分，而不是障碍。) 在 [RMod R] 中该树没有索引余积，也不需要：其能力是 [PowLine := ProdMod (fun _ => VctLine)] 来源于 Instance/Mod/Product.v（新的，#433）具有坐标射影 [vct_coord n]，并包装为 [PowCocone : Cocone LineDiagram] 在常量离散图 [LineDiagram : DiscreteCat nat ⟶ Vct^op] 上，并由 [prod_tuple] 证明其为余极限 [PowCocone_IsColimitCocone]——这是问题审阅者要求的具体 colimit。它在 D 下的像是坐标函数 [D (vct_coord n) : D VctLine ~> D PowLine] 的余锥，ψ ↦ ψ ∘ coord n。如果该图是余极限的，则通向竞争余锥 [ZeroCocone]（顶点：D PowLine 被坐标泛函的张 [SpanCoords] 所商的商对象 [SpanQuot]；腿：D (vct_coord n) 之后的商映射 [span_quot]）——商映射本身和零映射 [vct_zero_hom]，两者都是兼容的，因为每个 ψ ∘ coord n 都在张 [dual_coord_in_span]（ONE 场的交换性发挥的地方）中——将会重合，因此 F^ℕ 上的每个泛函都将位于该张中。Mac Lane 自己的陈述是某些泛函不在；也就是 [CoordSpanProper : Type]，并且 [dual_not_PreservesColimitCocone (H : CoordSpanProper)] 通过 Instance/Mod/Quotient.v 中的 [mquot_proj_kills] 和 [mquot_proj_kernel] 结束论证；[dual_functor_no_right_adjoint] 是练习题，[dual_not_left_adjoint_of_op] 是其推论，都是一行的组合。为什么是有条件的——分析，而非形式化。经典上，[CoordSpanProper F] 对每个域都成立（Erdős–Kaplansky：无限维空间的对偶空间的维数为 |F|^dim，因此可数多的坐标不能生成它），但在没有选择公理的情况下它并不可证明：在一个 ZF + DC 模型中，每个实数集都具有贝尔性质（Solovay；Shelah），根据 Pettis 的自动连续性定理，每个加性映射 ℚ^ℕ → ℚ 是连续的，并且在 ℚ 离散的情况下，ℚ^ℕ 上的连续函数在 0 的一个基本邻域上为零，因此它是坐标的有限组合。因此，对于 F = ℚ，该前提在 ZF + DC 下是独立的，且在此树中无法构建无公理的证明；docs/INHABITATION.md 记录了该行将永远不会有构造性实例的情况，与“等待模型”的行不同。有限的形状不会造成阻碍（模的有限积是双积，D 将其映射到双积——再次进行分析），因此可数性在这里是支撑性的，而在 Instance/Ab/FreeNotContinuous.v (#430) 中它是惰性的。无条件的一半。[vct_transpose f := fmap[Dual F]  f ∘ eta F x] 将 a ~> D x 转换为 x ~> D a 并且是一个自反变换（[vct_transpose_invol]，[reflexivity] 在 [simpl] 之后）；它的尊重性、两个往返行程和四个自然性方块由树的默认策略封闭：[dual_vct_AdjointOnTheRight : AdjointOnTheRight (Dual F) (Dual F)]（Adjunction/Right.v 的类），[dual_vct_Adjunction : (Dual F)^op ⊣ Dual F] 直到 [Adjunction_of_AdjointOnTheRight]，以及 Mac Lane 的对比 [dual_vct_Continuous : ContinuousFunctor (Dual F)] 通过 RAPL（Adjunction/Continuity.v  [right_adjoint_Continuous]）。方向很重要，探测针针对此（N3）：自伴随运行 [(Dual F)^op ⊣ Dual F]；练习的 [Dual F ⊣ (Dual F)^op] 正是被拒绝的归属。函子问题名称。[VctDual359 x] 是内部 Hom [HomMod x VctLine]；它的载体、零、和以及标量作用与 [DualMod] 在 [eq_refl] 上一致，因此泛函上的恒等映射是双向的模同态（[to359]、[from359]，打包为 [iso359]）。[dual] 的箭头作用是评价的闭转置，[dcur (eval' ∘ (id ⨂ f))]，是一个不透明的中介（StarAutonomous.v 的 [dcur] 是 [unique_obj] 的 [ump_exponents]，在 RMod 上是 `Qed` 定理 [ump_exponents_Mod]），因此它不可计算；[dual359_fmap_pre] 通过唯一性条款 [dcur_uniq] 将其识别为前复合，通过 Instance/Mod/Tensor.v 的 [tensor_hom_ext] 用 [reflexivity] 在张量生成元上进行检查。这给出了
   [dual_iso359 : Dual F ≈ VctDual359] 在 [Fun] 的 [≈]（Theory/Functor.v 的
   [Functor_Setoid]，一个捆绑的自然同构），并且
   Theory/Adjunction.v 的 [adjunction_along_left_iso] （#431）将任何
   [VctDual359 ⊣ Rt] 转换为 [Dual F ⊣ Rt]，因此 [dual359_no_right_adjoint]
   和 [dual359_not_left_adjoint_of_op] 从上述反驳中得出。UNIVERSES（[About] 在 `Set Printing Universes` 下，全部 41 个头）。没有 [Set] 出现：形状是 Structure/Limit/Comparison.v 的标注 [DiscreteCat_Functor']，因为 Instance/Discrete.v 的未标注 [DiscreteCat_Functor] 将形状的同类型级别固定为 [Set]，并且 Vct^op 中没有余圆锥可以共享它（探针 N4，“无法强制 Set = …”）。每个头除了 [vct_zero_hom] 都携带两个方程 `u0 = u`, `u1 = u` 来识别三个 [FieldObject] 级别——它们随着 [VctLine := Ring_RMod (field_ring F)] 和 [Dual@{u u u _}] 一同到达，并且 [vct_zero_hom]，在 Vct 的裸对象上陈述，不携带任何方程。严格约束有一种，即类别对象级别以下的字段级别（`u < u2`及其重命名；四个列表形状的头[span_sum]、[span_sum_app]、[span_sum_scale]和[dual_coord_in_span]对所有三个已识别级别都进行了说明），此外还有[dual_vct_Continuous]的形状级别（`u5 < u2`）和[vct_zero_hom]的第二对象级别（`u < u3`）。Stdlib 按文件中的第一个承运人限制顺序：`Basics.compose` 和 `ID` 在 [VctLine]（继承自 Instance/FdVect.v），`prod_rect` 在 [vct_zero_hom]，`list_rect` 和 `app` 在 [span_sum_app]，`ListDef.Map` 和 `projections` 在 [span_sum_scale]，`JMeq`、`eq`、`eq_ind`、`eq_ind_r`、`eq_rect_r`、`EqdepFacts.eq_sigT_sig_eq` 和 `Logic_lemmas.equality` 在 [LineDiagram]（继承自 [DiscreteCat_Functor']；该形状的 hom 是 [eq]），以及 Specif 的 `Projections` 在 [CoordSpanProper]（一个 sigma 类型）。测量。41 个 `.glob` 头（34 个 `def`，7 个 `prf`）和 17 个 [Program] 义务（8 个通过 [Obligation Tactic := idtac] 在 [vct_zero_hom] 和 [SpanCoords] 下手动关闭，9 个通过 [cat_simpl] 对四条记录 [vct_transpose_morphism]、[vct_aor]、[dual_vct_AdjointOnTheRight] 和 [iso359]），总共 58 个“在全局上下文中关闭”，零个 `Axioms:` 行；`make print-assumptions` 门承载 41 个头。六个 `Defined`，每个都是承重的（在整个文件的副本中一次翻转到 `Qed`：[op_discrete_cone] 停止 [PowCocone_IsColimitCocone]，[ZeroCocone] 停止 [dual_not_PreservesColimitCocone]，[PowCocone_IsColimitCocone] 停止读回 [pow_cocone_mediator_component]，[to359] 和 [from359] 停止 [dual_iso359] 的证明，[dual_iso359] 停止读回 [iso359_to_component]——这两个读回的存在就是这个原因）；十四个 `Qed`。关闭 103 个文件，不包括自身 (Adjunction/Right.v 18 在边缘，Structure/Limit/Comparison.v 5，Instance/Mod/Closed.v 2，Instance/Mod/Quotient.v 2，DoubleDual.v 1，Instance/Mod/Product.v 1，其余十九个 `Require` 为 0；25 个中没有可以删除的——每个文件在复制时都被删除，且复制停止编译)。41 个名称没有冲突 (`grep -rlw --include='*.v'`；DoubleDual.v 的头部设计上提到 [dual_iso359]；[SpanQuot]、[span_quot] 和 Product.v 的 [modprod_*] 是因为 Construction/PROP/Presentation.v 拥有 [quot]，而 Lib/Datatypes.v 拥有 [prod_setoid])。Test/ProbeDualNoRightAdjoint433.v 镜像了 `Require` 列表，加上 Structure/Monoidal/Dual.v（#359 控制）和 Structure/Limit/Product.v（索引积回读），并包含 6 条驳斥命令 = 1 个工具 + N1, N5 转换（[VctDual359 F = Dual F] 在 [eq_refl]：“类型是 VctDual359 F = VctDual359 F，但期望类型是 VctDual359 F = Dual F”；对象上相同，并在其旁接受载体） + N2-N3 类型（无条件 [∀ Rt, Dual F ⊣ Rt → False] 不赋予类型；练习的自伴随方向被拒绝） + N4 宇宙，每次都在整个文件的副本中逐一去掉，与其接受的控制文件并排；七个 `eq_refl` 回读；守卫覆盖 25/19，有六个详尽的例外（六条驳斥命令中的标识符标记/在它们之外命名，注释已被删除；例外情况包括反驳关键字本身、`fun`、`obj`、两个被反驳示例的名称以及工具的缺失名称；模拟重命名了16个库名称——[VctDual359]、[Dual]、[dual_functor_no_right_adjoint]、[dual_vct_Adjunction]、[Opposite_Functor]、[Cocone]、[DiscreteCat_Functor]、[VctLine]、[LineDiagram]、[CoordSpanProper]、[eq_refl]、[False]、[nat]、[Vct_F]、[carrier]、[cmon_setoid]——每条正面行的首次断行。`make todo` 仅通过 6 条反证行增长（2266 → 2272，提交版本 64b94901），所以问题的“没有新增命中”选项框未按原文满足（已披露，如 #430 所示）；Coq 8.19 和 8.20 选项框通过 Nix 对已提交修订版本的源码构建进行了检查，PR 中有记录。未交付：无条件反驳（没有选择公理是不可能的，上文）；[HasIndexedProducts (RMod R)] 实例和索引余积 ⊕_I（Product.v 的头部）；两个对偶的同构形式，除了 [Functor_Setoid] 的形式（没有 [⟹] 对，没有 [≅] 在函子范畴中——捆绑形式是 [adjunction_along_left_iso] 使用的）；本文件自身 [VctDual359] 的自伴随（#359 的是探针控制的）；任何关于 [FdVect F] 的内容，其中练习是错误的；不修改 Instance/FdVect.v、Instance/Mod.v、Instance/Mod/Quotient.v、Instance/Mod/Closed.v、Structure/Monoidal/StarAutonomous.v、Structure/Monoidal/Dual.v、Structure/Limit/Comparison.v 或 Adjunction/Continuity.v。
*)

#[local] Obligation Tactic := idtac.

Import ListNotations.

Section DualNoRightAdjoint.

Context (F : FieldObject).

Notation Vct := (Vct_F F).

(* * ** The line, its countable power and the coordinate functionals / * ** 这条线，其可计数的幂以及坐标泛函 *)

Definition VctLine : Vct := Ring_RMod (field_ring F).

Definition PowLine : Vct := ProdMod (fun _ : nat => VctLine).

Definition vct_coord (n : nat) : PowLine ~{Vct}~> VctLine :=
  prod_proj (fun _ : nat => VctLine) n.

Notation DP := (DualMod F PowLine).

(* The zero homomorphism between two vector spaces. / 两个向量空间之间的零同态。 *)
Program Definition vct_zero_hom (M N : Vct) : M ~{Vct}~> N := {|
  rm_hom := {| cmon_map := {| morphism := fun _ => cmon_zero N |} |}
|}.
Next Obligation. intros M N a b _; reflexivity. Qed.
Next Obligation. intros M N; reflexivity. Qed.
Next Obligation. intros M N a b; simpl; symmetry; apply cmon_plus_zero_l. Qed.
Next Obligation. intros M N r m; simpl; symmetry; apply rm_smul_zero_r. Qed.

(* * ** The span of the coordinate functionals inside the dual of the power / * ** 幂的对偶空间内坐标泛函的张成空间 *)

(* A finite formal combination of coordinate functionals, evaluated. / 有限形式的坐标泛函的组合，经评估。 *)
Fixpoint span_sum (p : list (nat * carrier (cmon_setoid VctLine)))
  : carrier (cmon_setoid DP) :=
  match p with
  | nil => cmon_zero DP
  | (n, c) :: q => cmon_plus DP (rm_smul DP c (vct_coord n)) (span_sum q)
  end.

Lemma span_sum_app (p q : list (nat * carrier (cmon_setoid VctLine))) :
  span_sum (p ++ q) ≈ cmon_plus DP (span_sum p) (span_sum q).
Proof.
  intro v.
  induction p as [|[n c] p IH]; simpl.
  - symmetry; apply rig_add_zero_l.
  - rewrite IH; symmetry; apply rig_add_assoc.
Qed.

Lemma span_sum_scale (r : carrier (cmon_setoid VctLine))
  (p : list (nat * carrier (cmon_setoid VctLine))) :
  rm_smul DP r (span_sum p)
    ≈ span_sum
        (map (fun nc => (fst nc, rig_mul (ring_rig (field_ring F)) r (snd nc)))
             p).
Proof.
  intro v.
  induction p as [|[n c] p IH]; simpl.
  - apply rig_mul_zero_r.
  - rewrite rig_distr_l, IH.
    apply rig_add_respects; [| reflexivity].
    symmetry; apply rig_mul_assoc.
Qed.

(* The submodule of [DP] spanned by the coordinates: the functionals that ARE finite linear combinations of coordinate projections. / 由以下坐标生成的 [DP] 的子模：那些是坐标投影的有限线性组合的泛函。 *)
Program Definition SpanCoords : Submodule DP := {|
  smod_mem := fun phi => { p : list (nat * carrier (cmon_setoid VctLine))
                         & phi ≈ span_sum p }
|}.
Next Obligation.
  intros a b Hab [p Hp]; exists p; now rewrite <- Hab.
Qed.
Next Obligation. exists nil; simpl; reflexivity. Qed.
Next Obligation.
  intros a b [p Hp] [q Hq]; exists (p ++ q).
  rewrite span_sum_app, Hp, Hq; reflexivity.
Qed.
Next Obligation.
  intros r a [p Hp].
  exists (map (fun nc => (fst nc, rig_mul (ring_rig (field_ring F)) r (snd nc)))
              p).
  rewrite Hp; apply span_sum_scale.
Qed.

(* Every functional of the form [ψ ∘ coord n] lies in the span — the one place field commutativity is spent. / 每个形式为 [ψ ∘ coord n] 的泛函都位于生成空间——唯一耗尽场交换性的地方。 *)
Lemma dual_coord_in_span (n : nat)
  (psi : carrier (cmon_setoid (DualMod F VctLine))) :
  smod_mem SpanCoords (cmon_map (rm_hom (fmap[Dual F] (vct_coord n))) psi).
Proof.
  exists [(n, cmon_map (rm_hom psi) (rig_one (ring_rig (field_ring F))))].
  intro v; simpl.
  rewrite rig_add_zero_r.
  transitivity (cmon_map (rm_hom psi)
                  (rm_smul VctLine (v n) (rig_one (ring_rig (field_ring F))))).
  - apply (proper_morphism (cmon_map (rm_hom psi))).
    simpl; symmetry; apply rig_mul_one_r.
  - rewrite (rm_map_smul psi (v n)).
    apply field_comm.
Qed.

(* * ** The concrete colimit: the countable power, as a cocone in Vct^op / * ** 具体余极限：可数幂，作为 Vct^op 中的余锥 *)

Definition LineDiagram : DiscreteCat nat ⟶ Vct^op :=
  DiscreteCat_Functor' (fun _ : nat => VctLine : obj[Vct^op]).

(*
 A family of maps out of an apex in Vct is a cocone over [LineDiagram]
 in [Vct^op]; the coherence over a discrete shape is [fmap_id]. 

 --------
 从 Vct 中一个顶点出发的一族映射是 [LineDiagram] 在 [Vct^op] 上的余锥；在离散形状上的相干性是 [fmap_id] 。
*)
Definition op_discrete_cone (c : Vct) (pi : ∀ n : nat, c ~{Vct}~> VctLine) :
  Cocone LineDiagram.
Proof.
  unshelve refine (@Build_Cone ((DiscreteCat nat)^op) ((Vct^op)^op)
                     (LineDiagram^op) c
                     (@Build_ACone ((DiscreteCat nat)^op) ((Vct^op)^op) c
                        (LineDiagram^op) pi _)).
  intros x y e; destruct e.
  change (@eq_refl nat y) with (@id ((DiscreteCat nat)^op) y).
  rewrite fmap_id.
  apply id_left.
Defined.

Definition PowCocone : Cocone LineDiagram := op_discrete_cone PowLine vct_coord.

(*
 The power is the colimit of the constant diagram in [Vct^op]: the
 product's universal property, read backwards. 

 --------
 幂是在  [Vct^op] 中常值图的余极限：乘积的普适性质，反过来读。
*)
Lemma PowCocone_IsColimitCocone : IsColimitCocone PowCocone.
Proof.
  intro M.
  unshelve refine {| unique_obj := _ |}.
  - exact (prod_tuple (fun _ : nat => VctLine)
             (fun n => @vertex_map _ _ _ _ (@coneFrom _ _ _ M) n)).
  - intros n z; reflexivity.
  - intros u Hu z n; symmetry; apply (Hu n z).
Defined.

(* * ** The obstruction hypothesis, in Mac Lane's own words / * ** 阻碍假设，用麦克莱恩自己的话说 *)

(*
 Some functional on [F^ℕ] is NOT a finite linear combination of the
 coordinate projections.  Classically true (Erdős–Kaplansky); not
 provable in ZF + DC, hence a hypothesis — see the header. 

 --------
 在 [F^ℕ] 上的一些泛函不是坐标投影的有限线性组合。经典结论（Erdős–Kaplansky）；在 ZF + DC 中不可证，因此是一种假设——见标题。
*)
Definition CoordSpanProper : Type :=
  { phi : carrier (cmon_setoid DP) & smod_mem SpanCoords phi → False }.

(** ** The refutation / ** 反驳 *)

Definition SpanQuot : Vct := QuotientMod SpanCoords.

Definition span_quot : Dual F PowLine ~{Vct}~> SpanQuot :=
  mquot_proj SpanCoords.

(*
 The competing cocone under the image diagram: the quotient by the span,
 with the composite legs. 

 --------
 在像图下的竞争余锥：由跨度商构成，带有复合的边。
*)
Definition ZeroCocone : Cocone (Dual F ◯ LineDiagram).
Proof.
  unshelve refine (@Build_Cone ((DiscreteCat nat)^op) (Vct^op)
                     ((Dual F ◯ LineDiagram)^op) SpanQuot
                     (@Build_ACone ((DiscreteCat nat)^op) (Vct^op) SpanQuot
                        ((Dual F ◯ LineDiagram)^op)
                        (fun n => span_quot ∘ fmap[Dual F] (vct_coord n)) _)).
  intros x y e; destruct e.
  change (@eq_refl nat y) with (@id ((DiscreteCat nat)^op) y).
  rewrite fmap_id.
  apply id_left.
Defined.

(*
 If [Dual F] preserved the colimit, the image cocone would be colimiting,
 and two mediators to [ZeroCocone] — the quotient map and the zero map —
 would coincide; then every functional lies in the span. 

 --------
 如果 [Dual F] 保留余极限，像余锥将是余极限的，并且到 [ZeroCocone] 的两个中介——商映射和零映射——将重合；那么每个泛函都在张成空间中。
*)
Theorem dual_not_PreservesColimitCocone (H : CoordSpanProper) :
  PreservesColimitCocone LineDiagram (Dual F) → False.
Proof.
  intro P.
  destruct H as [phi Hphi].
  pose proof (P PowCocone PowCocone_IsColimitCocone) as HC.
  destruct (HC ZeroCocone) as [w Hw Huniq].
  assert (Hq : w ≈ span_quot) by (apply Huniq; intros n psi; reflexivity).
  assert (Hz : w ≈ vct_zero_hom (Dual F PowLine) SpanQuot).
  { apply Huniq; intros n psi.
    symmetry.
    exact (mquot_proj_kills SpanCoords _ (dual_coord_in_span n psi)). }
  (*
 [mquot_proj_kernel]'s right-hand side is the [inhabited] truncation of
 membership since the PR “algebraic carriers are sets” (2026-09-17), so
 the witness is opened here rather than applied directly.  The goal is
 [False], a [Prop], so the elimination is allowed and nothing is lost. 

 --------
 [mquot_proj_kernel] 的右侧是自 PR “代数承载是集合”（2026-09-17）以来成员资格的 [inhabited] 截断，因此在此处展开了证人，而不是直接应用。目标是 [False]，一个 [Prop]，因此允许消元且不会丢失任何内容。
*)
  unshelve refine
    (match fst (mquot_proj_kernel SpanCoords phi) _ with
     | inhabits Hm => Hphi Hm
     end).
  transitivity (cmon_map (rm_hom w) phi).
  - symmetry; exact (Hq phi).
  - exact (Hz phi).
Qed.

(*
 Mac Lane §V.5 Exercise 2: a right adjoint of [Dual F] would make it a
 left adjoint, hence carry the colimit above to a colimit. 

 --------
 Mac Lane §V.5 练习 2：[Dual F] 的右伴随会使其成为左伴随，因此会将上面的余极限映射为余极限。
*)
Definition dual_functor_no_right_adjoint (H : CoordSpanProper)
  (Rt : Vct ⟶ Vct^op) (A : Dual F ⊣ Rt) : False :=
  dual_not_PreservesColimitCocone H
    (left_adjoint_PreservesColimitCocone A LineDiagram).

(* The corollary: [Dual F] is not the left adjoint of its opposite. / 推论：[Dual F] 不是其对偶的左伴随。 *)
Definition dual_not_left_adjoint_of_op (H : CoordSpanProper)
  (A : Dual F ⊣ Opposite_Functor (Dual F)) : False :=
  dual_functor_no_right_adjoint H (Opposite_Functor (Dual F)) A.

(* * ** The unconditional positive half: [Dual F] is adjoint to itself on the right, so it is continuous / * **无条件正半部分：[Dual F] 在右侧与自身是伴随的，所以它是连续的 *)

(*
 The remaining obligations (respectfulness, the two round trips, the four
 naturality squares) are closed by the tree's default tactic. 

 --------
 剩余的义务（尊重、两次往返、四个自然性方格）由树的默认策略完成。
*)
#[local] Obligation Tactic := cat_simpl.

(* The transpose [a ~> D x ↦ x ~> D a]: [D f ∘ η x]. / 转置 [a ~> D x ↦ x ~> D a] : [D f ∘ η x] 。 *)
Definition vct_transpose {a x : Vct} (f : a ~{Vct}~> Dual F x) :
  x ~{Vct}~> Dual F a :=
  fmap[Dual F] f ∘ eta F x.

Lemma vct_transpose_invol {a x : Vct} (f : a ~{Vct}~> Dual F x) :
  vct_transpose (vct_transpose f) ≈ f.
Proof. intros v w; simpl; reflexivity. Qed.

Program Definition vct_transpose_morphism (a x : Vct) :
  @SetoidMorphism _ (@homset Vct a (Dual F x))
                  _ (@homset Vct x (Dual F a)) := {|
  morphism := @vct_transpose a x
|}.

Program Definition vct_aor (a x : Vct) :
  @Isomorphism Sets
    {| carrier := @hom Vct a (Dual F x);
       is_setoid := @homset Vct a (Dual F x) |}
    {| carrier := @hom Vct x (Dual F a);
       is_setoid := @homset Vct x (Dual F a) |} := {|
  to   := vct_transpose_morphism a x;
  from := vct_transpose_morphism x a
|}.

Program Definition dual_vct_AdjointOnTheRight :
  @AdjointOnTheRight Vct Vct (Dual F) (Dual F) := {|
  aor := vct_aor
|}.

Definition dual_vct_Adjunction : Opposite_Functor (Dual F) ⊣ Dual F :=
  Adjunction_of_AdjointOnTheRight dual_vct_AdjointOnTheRight.

(*
 Mac Lane's contrast: as a right adjoint, [Dual F] carries every colimit
 of Vct to a limit; the exercise is about the other direction. 

 --------
 麦克莱恩的对比：作为一个右伴随，[Dual F] 会将 Vct 的每个余极限带到一个极限；本练习是关于相反方向的。
*)
Definition dual_vct_Continuous : ContinuousFunctor (Dual F) :=
  right_adjoint_Continuous dual_vct_Adjunction.

(* * ** The functor the issue names: StarAutonomous.v's [dual] at the line / * ** 函子问题名称：StarAutonomous.v 文件第 [dual] 行 *)

(*
 Instance/Mod/Closed.v's [RMod_SymMonClosed] makes Vct symmetric
 monoidal closed, and Structure/Monoidal/StarAutonomous.v's [dual],
 read at the line, is the dual-object functor #359 proves self-adjoint on
 the right.  Its objects are the internal homs [HomMod x VctLine], whose
 carriers and operations coincide with [DualMod]'s on the nose; only the
 packed records differ (probe N1, N5). 

 --------
 Instance/Mod/Closed.v 中的 [RMod_SymMonClosed] 使 Vct 成为对称幺半闭类别，而 Structure/Monoidal/StarAutonomous.v 中的 [dual] ，在该行读取时，是对偶对象函子 #359 证明在右侧自伴的。它的对象是内部同态 [HomMod x VctLine] ，其载体和运算与 [DualMod] 的完全相同；只有打包记录不同（探测 N1, N5）。
*)
Definition VctSMC : @SymMonClosed Vct :=
  RMod_SymMonClosed (field_ring F) (field_comm F).

Definition VctDual359 : Vct^op ⟶ Vct := @dual Vct VctSMC VctLine.

(* The identity on functionals, as a module homomorphism each way. / 作为模同态的泛函上的恒等映射，两种方式。 *)
Definition to359 (x : Vct) : Dual F x ~{Vct}~> VctDual359 x.
Proof.
  unshelve notypeclasses refine
    (@Build_RModHom (field_ring F) (Dual F x) (VctDual359 x)
       (@Build_CMonHom (ab_cmon (Dual F x)) (ab_cmon (VctDual359 x))
          (@Build_SetoidMorphism _ _ _ _ (fun g => g) _) _ _) _).
  - intros g g' Hg; exact Hg.
  - intro v; reflexivity.
  - intros g h v; reflexivity.
  - intros r g v; reflexivity.
Defined.

Definition from359 (x : Vct) : VctDual359 x ~{Vct}~> Dual F x.
Proof.
  unshelve notypeclasses refine
    (@Build_RModHom (field_ring F) (VctDual359 x) (Dual F x)
       (@Build_CMonHom (ab_cmon (VctDual359 x)) (ab_cmon (Dual F x))
          (@Build_SetoidMorphism _ _ _ _ (fun g => g) _) _ _) _).
  - intros g g' Hg; exact Hg.
  - intro v; reflexivity.
  - intros g h v; reflexivity.
  - intros r g v; reflexivity.
Defined.

Program Definition iso359 (x : Vct) : Dual F x ≅[Vct] VctDual359 x := {|
  to := to359 x; from := from359 x
|}.

(*
 [dual]'s arrow action is the closed transpose of evaluation; by the
 uniqueness clause of the exponential's universal property it is
 precomposition, checked on the tensor's generators. 

 --------
 [dual] 的箭头作用是评估的闭合转置；根据指数的泛性质的唯一性条款，它是前组合，在张量的生成元上进行了检查。
*)
Lemma dual359_fmap_pre {x y : Vct} (f : y ~{Vct}~> x) :
  fmap[VctDual359] (f : x ~{Vct^op}~> y)
    ≈ to359 y ∘ fmap[Dual F] f ∘ from359 x.
Proof.
  apply (@dcur_uniq Vct VctSMC).
  refine (tensor_hom_ext _ _ _).
  intros g w; reflexivity.
Qed.

(* The natural isomorphism [Dual F ≈ VctDual359], in [Fun]'s [≈]. / 自然同构 [Dual F ≈ VctDual359]，在 [Fun] 的 [≈] 中。 *)
Definition dual_iso359 : Dual F ≈ VctDual359.
Proof.
  exists (fun x : Vct^op => iso359 x).
  intros x y f.
  rewrite (dual359_fmap_pre f).
  intros g v; simpl; reflexivity.
Defined.

(*
 Mac Lane §V.5 Exercise 2 for the functor the issue names, by transport
 of the adjunction along the isomorphism (Theory/Adjunction.v's
 [adjunction_along_left_iso], #431). 

 --------
 Mac Lane §V.5 练习 2 对于函子，通过沿同构的伴随关系的搬运来命名问题（Theory/Adjunction.v 的 [adjunction_along_left_iso]，#431）。
*)
Definition dual359_no_right_adjoint (H : CoordSpanProper)
  (Rt : Vct ⟶ Vct^op) (A : VctDual359 ⊣ Rt) : False :=
  dual_functor_no_right_adjoint H Rt (adjunction_along_left_iso dual_iso359 A).

Definition dual359_not_left_adjoint_of_op (H : CoordSpanProper)
  (A : VctDual359 ⊣ Opposite_Functor VctDual359) : False :=
  dual359_no_right_adjoint H (Opposite_Functor VctDual359) A.

(** ** Readbacks / ** 回读 *)

Example vct_coord_component (n : nat) (v : carrier (cmon_setoid PowLine)) :
  cmon_map (rm_hom (vct_coord n)) v = v n := eq_refl.

Example pow_line_carrier :
  carrier (cmon_setoid PowLine) = (nat → carrier (cmon_setoid VctLine))
  := eq_refl.

Example vct_transpose_component {a x : Vct} (f : a ~{Vct}~> Dual F x)
  (v : carrier (cmon_setoid x)) (w : carrier (cmon_setoid a)) :
  cmon_map (rm_hom (cmon_map (rm_hom (vct_transpose f)) v)) w
    = cmon_map (rm_hom (cmon_map (rm_hom f) w)) v := eq_refl.

(*
 The isomorphism's components are the identity on functionals; this is
 what keeps [dual_iso359] transparent. 

 --------
 同构的组成部分在泛函上是恒等的；这就是使 [dual_iso359] 透明的原因。
*)
Example iso359_to_component (x : Vct) (g : carrier (cmon_setoid (Dual F x))) :
  cmon_map (rm_hom (to (projT1 dual_iso359 x))) g = g := eq_refl.

(* The colimit mediator computes: at a vector [z] of the competing apex it is the family of that cocone's legs at [z]. This is what keeps [PowCocone_IsColimitCocone] transparent. / 余极限中介计算：在竞争顶点的向量 [z] 处，它是该余锥在 [z] 处支腿的族。这就是保持 [PowCocone_IsColimitCocone] 透明的原因。 *)
Example pow_cocone_mediator_component (M : Cocone LineDiagram)
  (z : carrier (cmon_setoid (vertex_obj[M] : Vct))) (n : nat) :
  cmon_map (rm_hom (unique_obj (PowCocone_IsColimitCocone M))) z n
    = cmon_map (rm_hom (@vertex_map _ _ _ _ (@coneFrom _ _ _ M) n)) z
  := eq_refl.

End DualNoRightAdjoint.
