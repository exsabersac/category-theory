Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Product.
Require Import Category.Construction.Product.Limit.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Arrow.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* * * The arrow-category projection creates limits / * * 箭头类别投影创建了限制 *)

(*
 Mac Lane, Categories for the Working Mathematician, 2nd ed., §V.1
 Exercise 3 (book p. 112): the projection [C^→ ⟶ C × C] sending an arrow
 to its (domain, codomain) pair creates limits.  nLab: "arrow category",
 "created limit".

 WHAT IS DELIVERED, AND AT WHAT STRENGTH.  The exercise is the case
 [S = T = Id] of a statement about the TWO-SIDED comma projection
 [comma_proj : (S ↓ T) ⟶ A ∏ B] of Construction/Comma.v, and the proof
 at [Id] IS the general proof, so the general form is what is built and
 the arrow category is read off it.  Over [S : A ⟶ C], [T : B ⟶ C], a
 diagram [K : J ⟶ (S ↓ T)] and the ONE hypothesis
 [HT : PreservesLimitCone (comma_proj2 ◯ K) T] — that [T] carries the
 limit of the codomain diagram to a limit; nothing whatever is asked of
 [S], and the section binds nothing about [S] beyond its type —

 - [comma_lift_arrow N HN : S (fst apex) ~> T (snd apex)], the
 comparison arrow induced between the two limits, is the mediator of
 the cone [dom_cone N] (apex [S] of the domain apex, legs the comma
 arrows of [K] after the domain legs) into [FCone T (cod_cone N)],
 limiting by [HT]; [comma_lift_arrow_commutes] is its square with
 every leg and [comma_lift_arrow_unique] is Mac Lane's uniqueness
 clause — ANY arrow making all the squares commute IS this one.
 - [comma_lift_cone N HN : Cone K] with apex [(vertex_obj[N]; h)] and
 legs [(cone_leg N j; square)]; [comma_lift_apex_strict] and
 [comma_lift_leg_strict] record that its projection IS [N]'s apex
 and legs at [eq_refl], which is what makes
 [comma_lift_StrictLift : StrictLift K comma_proj N] a record literal
 with [eq_refl] for the object equation.
 - [comma_proj_reflect]: a cone over [K] whose projection is limiting
 is limiting.  The mediator's square is forced by JOINT MONICITY of
 the legs [T q_j] of the preserved limit ([limit_med_eq] at
 [FCone T (cod_cone (FCone comma_proj M))]), and its uniqueness is
 the downstairs uniqueness read through the comma hom-setoid, which
 compares underlying pairs only.
 - [comma_proj_StrictlyCreatesLimit : StrictlyCreatesLimit K comma_proj]
 — Riehl's on-the-nose reading (Structure/Limit/Creation.v) — and
 [comma_proj_CreatesLimit : CreatesLimit K comma_proj] through the
 bridge [StrictlyCreatesLimit_CreatesLimit]; [comma_proj_Limit] is the
 existence half bundled, its apex the downstairs apex and its arrow
 [comma_lift_arrow] at [eq_refl] ([comma_proj_Limit_apex],
 [comma_proj_Limit_arrow]).

 For the arrow category [C^→ := Id[C] ↓ Id[C]] (Construction/Arrow.v):
 [arrow_proj_creates_limits] (the issue's pinned name),
 [arrow_proj_strictly_creates_limits], [arrow_proj_creates_all_limits],
 and the corollary the exercise is used for, [Arrow_Complete : Complete C
 → Complete (C^→)] (the issue's other pinned name), through
 [creates_limits_Complete] over Construction/Product/Limit.v's
 [Product_Complete HC HC].  Limits are COMPUTED COMPONENTWISE and that is
 a readback, not prose: [Arrow_Complete_dom]/[Arrow_Complete_cod] show at
 [eq_refl] that the chosen limit's domain and codomain are [HC]'s own
 chosen limits of [Fst ◯ (comma_proj ◯ K)] and [Snd ◯ (comma_proj ◯ K)].
 The [Id] instantiation needs [Id_PreservesLimitCone], which the tree
 did not have (measured: no constant of the shape [PreservesLimitCone _
 Id] anywhere; the nearest neighbour, Theory/Equivalence/Creation.v's
 [Id_CreatesAllLimits], does not serve, because turning creation into
 cone-level preservation through Structure/Limit/Creation.v's
 [creation_preserves_limit] costs an extra [L : Limit (F ◯ K)] that the
 new lemma does not need); it is declared at the head of this file and
 belongs beside [PreservesLimitCone] in Structure/Limit/Preservation.v,
 where it
 is not placed only because that module is upstream of most of the tree
 and the move would cost a wide rebuild for one twelve-line lemma.

 WHAT IS CONSUMED.  #418's [Snd_PreservesLimitCone] (Construction/
 Product/Limit.v, unconditional) is what turns a limiting cone in
 [A ∏ B] into a limiting cone in [B]; [cod_cone] repackages its image
 over [comma_proj2 ◯ K], because [Snd ◯ (comma_proj ◯ K)] and
 [comma_proj2 ◯ K] agree on BOTH actions at [eq_refl] but are different
 functor RECORDS ([Compose]'s law fields are separate opaque obligations),
 so a cone over one is not a cone over the other — pinned in the probe
 with the two action agreements as controls.  Structure/Limit/Creation.v
 supplies the classes, the bridge and [creates_limits_Complete];
 Structure/Limit/Preservation.v supplies [limit_med_eq].  The ONE-SIDED
 donor the issue points at, Construction/Comma/Creation.v's
 [comma_CreatesLimit] for [comma_proj2 : (=(d) ↓ U) ⟶ C], is NOT
 consumed, and the [apex_obj]/[apex_leg] beneath it — declared in
 Construction/Comma/Limit.v, the module Creation.v builds
 on, and not in Creation.v itself — are not reused: those are stated
 over the constant-domain comma, whose objects are [(ttt, b)]-pairs and
 whose lifting argument goes through the fixed [Gdiag]; the two-sided
 projection needs the domain half to vary, and the argument here is the
 same shape one level up rather than an instance.  Issue #438, which
 asks for that one-sided lemma (Mac Lane §V.6 Lemma 1), is still OPEN at
 the time of writing although its content is in that file; nothing here
 depends on how it is resolved.

 STRICTNESS, MEASURED STRICT FIRST.  Six statements close by [eq_refl]
 in this file (the two [comma_lift_*_strict] readbacks, the two
 [comma_proj_Limit_*] readbacks, [Arrow_Complete_dom],
 [Arrow_Complete_cod]); the probe adds the witness readbacks.  The WHOLE
 record [FCone comma_proj (comma_lift_cone N HN) = N] is refused at
 [eq_refl] although apex and every leg are [N]'s on the nose — the
 coherence field is a rebuilt proof and [≈] is Type-valued — pinned
 with those two controls.  Non-vacuity COMPUTES, at a shape that is
 DEGENERATE and labelled so: over [Coq] at the point shape [_1] (one
 object, one arrow, so cone coherence is vacuous and the comparison
 arrow is the diagram's own), with the diagram constant at the arrow
 [negb] and the limiting cone Structure/Limit/Initial.v's [initial_cone]
 (whose mediator is definitionally the leg), the created arrow IS [negb]
 at [eq_refl], and [true ↦ false], [false ↦ true] by computation — what
 that shows is that the whole chain REDUCES, not that a non-trivial
 limit is computed; it lives in the probe because it costs
 [Instance/Coq], [Instance/One] and [Structure/Limit/Initial] and this
 file should not.

 UNIVERSES, MEASURED OFF BOTH BINDER AND BLOCK.  Every one of the 24
 constants of the two-sided section binds [A : Category@{u u0 u0}],
 [B : Category@{u1 u2 u2}], [C : Category@{u3 u4 u4}],
 [J : Category@{u5 u6 u6}] — hom identified with proof in the BINDER,
 with no such equation in any block.  EIGHTEEN of them carry the block
 equations [u0 = u2], [u0 = u4], [u0 = u6] and [u0 = u9], so the four
 categories' hom-and-proof levels collapse to one — [u9] is NOT the
 comma category's own level (that category sits at
 [Category@{u7 u4 u4}], its hom level being C's [u4], and [u7] carries
 no equation anywhere) but the level instantiating [comma_proj2]'s own
 universe [u6], an auxiliary bounded below by A's and B's hom levels
 (a mislabel the fess audit caught); the SIX cone-building constants of
 the two halves — [cod_leg], [cod_coherence], [cod_cone], [dom_leg],
 [dom_coherence], [dom_cone] — carry [u2 = u4], [u2 = u6], [u2 = u9]
 instead and leave A's hom level [u0] only BOUNDED; the ten
 [Section Lift] constants add [u15 = u20] and [u17 = u18] on auxiliary
 levels that occur in no [Category] binder (they sit inside the
 [PreservesLimitCone], [Compose] and [IsLimitCone] instances of the
 [HT] and [HN] binders).  No equation
 in any of the 31 blocks touches an OBJECT universe.  The collapse is
 NOT the comma category's doing: [Comma@{…}] binds [A], [B] and [C] at
 three separate hom levels and [Su ↓ Tu] is ACCEPTED at [ah < bh]; it is
 [Compose]'s, met first at [comma_proj ◯ K] — at a shape whose homs are
 declared strictly below the factors', [Su ↓ Tu], [K] and a [Cone] over
 [K] are accepted while [comma_proj ◯ K] is refused ("Cannot enforce
 ch = jh"), and [comma_proj_CreatesLimit] with it (pinned as the probe's
 universe negative, with those three as controls).  The arrow section's
 six constants carry NO block equation at all — the identification is
 discharged in the binders [C : Category@{u u0 u0}] and, where a shape is
 bound, [J : Category@{u17 u0 u0}], J's hom-and-proof at C's level — and
 [Arrow_Complete] is accepted at [Set < ch]; [Id_PreservesLimitCone]
 likewise carries none, binding [J : Category@{u2 u4 u4}] and
 [D : Category@{u3 u4 u4}].  No word-bounded [Set] occurs in the binder
 or block of any of the 31 constants.

 COUNTS.  31 constants — 26 declared heads plus the 5 [Qed]-closed
 lemmas [Print Module] renders as [Parameter] are all 31 [Print Module]
 entries; the file has no [Program], no [Record]/[Class]/[Inductive], so
 there is no obligation and no unlisted [Build_*] — all closed under the
 global context with zero [Axioms:] lines, and all gated fully qualified
 in [make print-assumptions].  Four [Defined] tokens, THREE load-bearing
 by flipping each alone to [Qed]: [Id_PreservesLimitCone] and
 [cod_limiting] each stop the probe's witness at [neg_created = negb]
 (the created arrow no longer reduces), and
 [comma_proj_StrictlyCreatesLimit] stops this file's own
 [comma_proj_Limit_apex]; [comma_proj_reflect] flips with both files
 compiling and is [Defined] by the data convention only.  Transitive
 in-project closure 33 modules excluding this file (probe 65), measured
 per [Require]: Construction/Product/Limit costs 6, Construction/Arrow
 1, every other [Require] 0.  [make todo] grows by the probe's
 refutation commands and the prose lines naming that token, this file
 contributing ZERO — so the issue's "adds no new hits" box is NOT met
 as written; CLAUDE.md carries the exact figure.

 NOT DELIVERED.  Colimits: no [Arrow_Cocomplete] and no dual of the
 two-sided statement — it would need [S] to preserve the COLIMIT of the
 domain diagram and a comma read at the opposites, and neither the
 duality [(S ↓ T)^op] against [(T^op ↓ S^op)] nor a direct cocone
 development is attempted here.  No converse: nothing says [T] MUST
 preserve the limit for [comma_proj] to create it.  No comparison of
 [Arrow_Complete]'s limits with the one-sided [Comma_Complete]'s, and no
 identification of [Fst ◯ comma_proj] with [comma_proj1] beyond their
 agreeing actions (both exhibited at [eq_refl] in the probe, mirroring
 the [Snd] pair), and none with [Arrow_dom] at all — the readbacks are
 stated in the [Fst ◯ (comma_proj ◯ K)] form [Product_Complete] chooses.
 No
 functoriality of the lift in [K], no naturality of the comparison
 arrow, and nothing registered as an [Instance]: a chosen limit must not
 become globally resolvable. 

 --------
 Mac Lane，《为在职数学家准备的范畴论》，第2版，第§V.1节
 练习 3（书第112页）：投影 [C^→ ⟶ C × C] 将一个箭头映射到它的（定义域，陪域）对，从而产生极限。nLab：“箭头范畴”，“生成极限”。

 提供了什么，以及其强度如何。练习是关于 Construction/Comma.v 中双边逗号投影 [comma_proj : (S ↓ T) ⟶ A ∏ B] 的陈述的 [S = T = Id] 情况，其证明在 [Id] 是一般证明，因此建立的是一般形式，箭头范畴可以从中读取。在 [S : A ⟶ C]，[T : B ⟶ C] 上，有一个图 [K : J ⟶ (S ↓ T)] 和唯一假设 [HT : PreservesLimitCone (comma_proj2 ◯ K) T]——即 [T] 将陪域图的极限映射到极限；对 [S] 没有任何额外要求，章节除了类型之外不对 [S] 做任何约束——-  [comma_lift_arrow N HN : S (fst apex) ~> T (snd apex)]，在两个极限之间诱导的比较箭头，是将锥 [dom_cone N]（范畴顶点 [S]，边为 [K] 在范畴边之后的逗号箭头）引入 [FCone T (cod_cone N)] 的中介，通过 [HT] 极限；[comma_lift_arrow_commutes] 是其正方形，带有每条边，[comma_lift_arrow_unique] 是 Mac Lane 的唯一性条款——任意使所有正方形交换的箭头就是这个。-  [comma_lift_cone N HN : Cone K] 的顶点为 [(vertex_obj[N] ; h)] 和边 [(cone_leg N j; square)]；[comma_lift_apex_strict] 和 [comma_lift_leg_strict] 记录了其投影是 [N] 的顶点和 [eq_refl] 上的边，这正是使 [comma_lift_StrictLift : StrictLift K comma_proj N] 成为带有 [eq_refl] 对象方程的记录字面量。-  [comma_proj_reflect]：一个锥体，其投影是极限的 [K]，是极限。中介方的方形是由保留极限的边  [T q_j]  的联合单调性强制的（ [limit_med_eq] 在 [FCone T (cod_cone (FCone comma_proj M))] ），其唯一性是通过逗号同态集合读取的下层唯一性，它只比较底层对。—  [comma_proj_StrictlyCreatesLimit : StrictlyCreatesLimit K comma_proj] — Riehl 的精确解读（Structure/Limit/Creation.v）— 以及通过桥  [StrictlyCreatesLimit_CreatesLimit] 的 [comma_proj_CreatesLimit : CreatesLimit K comma_proj] ；[comma_proj_Limit] 是 existence 半捆绑，其顶点为下层顶点，其箭头 [comma_lift_arrow] 在 [eq_refl] （[comma_proj_Limit_apex], [comma_proj_Limit_arrow]）。对于箭头类别 [C^→ := Id[C] ↓ Id [C] ]（Construction/Arrow.v）：
 [arrow_proj_creates_limits]（问题的固定名称），
 [arrow_proj_strictly_creates_limits]，[arrow_proj_creates_all_limits]，
 以及该练习所使用的推论，[Arrow_Complete : Complete C → Complete (C^→)]（问题的另一个固定名称），通过
 [creates_limits_Complete] 在 Construction/Product/Limit.v 的
 [Product_Complete HC HC] 上。极限是按分量计算的，这是一种回读，而不是文字描述：[Arrow_Complete_dom] / [Arrow_Complete_cod] 在 [eq_refl] 显示所选极限的定义域和值域是 [HC] 自己所选的 [Fst ◯ (comma_proj ◯ K)] 和 [Snd ◯ (comma_proj ◯ K)] 的极限。[Id] 的实例化需要 [Id_PreservesLimitCone]，而树中没有这个（测量结果：没有形如 [PreservesLimitCone _ Id] 的常量；最近的邻居，Theory/Equivalence/Creation.v 的 [Id_CreatesAllLimits] 也不行，因为通过 Structure/Limit/Creation.v 的 [creation_preserves_limit] 将 creation 转换为锥级保持会额外消耗 [L : Limit (F ◯ K)]，而新引理并不需要）；它在此文件的开头被声明，并且应当放在 Structure/Limit/Preservation.v 中 [PreservesLimitCone] 的旁边，只是该模块位于树的大多数部分的上游，将其移动会导致重建整个树，仅为一个十二行的引理，这就是它没有被放置在那里。什么被消耗。#418 的 [Snd_PreservesLimitCone]（Construction/Product/Limit.v，无条件）是将 [A ∏ B] 中的限制锥转化为 [B] 中的限制锥的东西；[cod_cone] 在 [comma_proj2 ◯ K] 上重新打包它的像，因为 [Snd ◯ (comma_proj ◯ K)] 和 [comma_proj2 ◯ K] 在 [eq_refl] 上对两个动作达成一致，但它们是不同的函子记录（[Compose] 的法律字段是独立的不透明义务），所以一个上的锥不是另一个上的锥——在探针中固定，以两个动作协议作为控制。Structure/Limit/Creation.v 提供类、桥和 [creates_limits_Complete]；Structure/Limit/Preservation.v 提供 [limit_med_eq]。单边的捐赠者问题指向 Construction/Comma/Creation.v 中的 [comma_CreatesLimit] 代替 [comma_proj2 : (=(d) ↓ U) ⟶ C]，并未被使用，而其下方的 [apex_obj] / [apex_leg]——在 Construction/Comma/Limit.v 中声明，Creation.v 模块是在其上构建的，而不是在 Creation.v 本身——也未被重用：这些是在常量域逗号上声明的，其对象是 [(ttt, b)] 对，并且其提升参数通过固定的 [Gdiag]；双边投影需要域的一半变化，而此处的参数是在上一级相同形状而非实例。问题 #438（要求那个单边引理，Mac Lane §V.6 引理 1）在写作时仍然未解决，尽管其内容在该文件中；这里没有任何内容依赖于其如何解决。严格性，先测量严格性。六条声明由 [eq_refl] 在此文件中关闭（两个 [comma_lift_*_strict] 回读，两个 [comma_proj_Limit_*] 回读，[Arrow_Complete_dom]，[Arrow_Complete_cod]）；探针添加了见证回读。整个记录 [FCone comma_proj (comma_lift_cone N HN) = N] 在 [eq_refl] 被拒绝，尽管顶点和每一段都在 [N] 的精确范围内——相干场是一个重建的证明，并且 [≈] 是类型值——用这两个控制固定。非空计算，在一个退化并标记为：在点形状 [_1] 上的 [Coq] 上（一个对象，一个箭头，所以锥一致性是空的，比较箭头是图自身的），箭头 [negb] 上的图常量和极限锥 Structure/Limit/Initial.v 的 [initial_cone]（其中介在定义上是腿），创建的箭头是 [negb] 在 [eq_refl] 上，以及通过计算得到的 [true ↦ false]、[false ↦ true]——这表明的是整个链被归约，而不是计算出一个非平凡的极限；它存在于探针中，因为它花费了 [Instance/Coq]、[Instance/One] 和 [Structure/Limit/Initial]，而这个文件不应该。宇宙，同时从活页夹和块中测量。两面部分的 24 个常数中的每一个都绑定了 [A : Category@{u u0 u0}]、[B : Category@{u1 u2 u2}]、[C : Category@{u3 u4 u4}]、[J : Category@{u5 u6 u6}] —— 在活页夹中通过证明确认的同构，在任何块中都没有这样的方程。其中十八个携带块方程 [u0 = u2]、[u0 = u4]、[u0 = u6] 和 [u0 = u9]，因此四个类别的同态和证明级别归为一类——[u9] 并不是逗号类别自身的级别（该类别位于 [Category@{u7 u4 u4}]，其同态级别为 C 的 [u4]，而 [u7] 在任何地方都不携带方程），而是实例化 [comma_proj2] 自身宇宙 [u6] 的级别，一个由 A 和 B 的同态级别下界辅助的辅助级别（fess 审计发现的标签错误）；两半的六个锥构建常量——[cod_leg]、[cod_coherence]、[cod_cone]、[dom_leg]、[dom_coherence]、[dom_cone]——相反地携带 [u2 = u4]、[u2 = u6]、[u2 = u9]，并仅将 A 的同态级别 [u0] 限定；十个 [Section Lift] 常量在辅助级别上添加了 [u15 = u20] 和 [u17 = u18]，这些级别出现于 i在 [Category] 绑定器中（它们位于 [PreservesLimitCone]、[Compose] 和 [IsLimitCone] 的 [HT] 和 [HN] 绑定器实例中）。在31个区块中的任何方程都没有接触到OBJECT宇宙。坍塌并不是逗号范畴的作用：[Comma@{…}]绑定了[A]、[B]和[C]在三个不同的hom级别上，而[Su ↓ Tu]在[ah < bh]被接受；它是[Compose]的，最先在[comma_proj ◯ K]遇到——在其hom被声明严格低于因子的形状上，[Su ↓ Tu]、[K]和一个[Cone]在[K]上被接受，而[comma_proj ◯ K]被拒绝（"无法强制 ch = jh"），与其一起的[comma_proj_CreatesLimit]（作为探针宇宙负极固定，三者作为控制）。箭头部分的六个常量完全没有块方程——标识在绑定器 [C : Category@{u u0 u0}] 中解除，并且在形状被绑定时，[J : Category@{u17 u0 u0}]、J 在 C 的级别的同态与证明——并且 [Arrow_Complete] 在 [Set < ch] 被接受；[Id_PreservesLimitCone] 同样没有任何方程，绑定 [J : Category@{u2 u4 u4}] 和 [D : Category@{u3 u4 u4}]。没有以单词为界的 [Set] 出现在任何 31 个常量的绑定器或块中。统计。31 个常量——26 个已声明的头加上 5 个 [Qed] 闭合的引理 [Print Module] 渲染为 [Parameter]，总共有 31 个 [Print Module] 条目；该文件没有 [Program]，没有 [Record]/[Class]/[Inductive]，因此没有义务，也没有未列出的 [Build_*]——在全局上下文下全部闭合，零 [Axioms:] 行，并且全部在 [make print-assumptions] 中完全限定。四个 [Defined] 标记，其中三个是承重标记，通过单独翻转到 [Qed]：[Id_PreservesLimitCone] 和 [cod_limiting] 分别阻止探针的见证在 [neg_created = negb]（创建的箭头不再缩减），而 [comma_proj_StrictlyCreatesLimit] 阻止该文件自身的 [comma_proj_Limit_apex]；[comma_proj_reflect] 与两个文件一起翻转编译，并且仅按数据约定为 [Defined]。及物  
 项目内闭包 33 个模块（不包括此文件，probe 65），根据 [Require] 测量：Construction/Product/Limit 成本 6，Construction/Arrow 1，其他每个 [Require] 为 0。[make todo] 通过探针的反驳命令以及命名该标记的散文行增长，此文件贡献为零——因此按原文书写的问题的“未增加新命中”框未满足；CLAUDE.md 载有确切数字。未交付。余极限：没有 [Arrow_Cocomplete]，也没有双边陈述的对偶——需要 [S] 来保持域图的余极限，并且在对偶处读取一个逗号，而既没有 [(S ↓ T)^op] 对 [(T^op ↓ S^op)] 的对偶，也没有尝试直接的余锥展开。没有逆命题：没有任何东西说 [T] 必须保持 [comma_proj] 的极限以创建它。没有将 [Arrow_Complete] 的极限与单边 [Comma_Complete] 的极限进行比较，也没有将 [Fst ◯ comma_proj] 与 [comma_proj1] 识别为相同，除了它们相同的作用（两者在探针中均展示于 [eq_refl]，反映了 [Snd] 对），并且与 [Arrow_dom] 完全没有关系——回读以 [Fst ◯ (comma_proj ◯ K)] 形式陈述，由 [Product_Complete] 选择。在 [K] 中提升没有函子性，比较箭头没有自然性，也没有作为 [Instance] 注册的内容：选定的极限不能变成全局可解的。
*)

(* * ** The identity functor preserves limiting cones / * ** 恒等函子保持极限锥 *)

(*
 [FCone Id[D] N] has [N]'s apex and legs on the nose, over the diagram
 [Id[D] ◯ G] instead of [G]; the two [Cone] types differ only in that
 functor record, so a competitor over one repackages over the other. 

 --------
 [FCone Id[D] N] 在图上鼻子处有 [N] 的顶点和腿，[Id[D] ◯ G] 代替 [G]；这两种 [Cone] 类型的区别仅在于函子记录，因此竞争者在一个上重新打包，另一方也会重新打包。
*)

Definition Id_PreservesLimitCone {J D : Category} (G : J ⟶ D) :
  PreservesLimitCone G Id[D].
Proof.
  intros N HN M.
  pose (M' := @Build_Cone J D G vertex_obj[M]
                (@Build_ACone J D vertex_obj[M] G (cone_leg M)
                   (fun x y f => cone_leg_coh M f))).
  destruct (HN M') as [u Hu Huniq].
  exists u.
  - intro j; exact (Hu j).
  - intros v Hv; apply Huniq; intro j; exact (Hv j).
Defined.

(* * ** The two-sided comma projection creates limits / * ** 双面逗号投影创建限制 *)

Section TwoSided.

Context {A B C : Category}.
Context {S : A ⟶ C} {T : B ⟶ C}.
Context {J : Category}.
Context (K : J ⟶ (S ↓ T)).
Context (HT : PreservesLimitCone (comma_proj2 ◯ K) T).

(*
 The codomain half of a cone over the projected diagram, read over
 [comma_proj2 ◯ K].  [FCone Snd N] is a cone over [Snd ◯ (comma_proj ◯ K)],
 a different functor record with the same actions. 

 --------
 在投影图上的圆锥的余域部分，读取为 [comma_proj2 ◯ K]。[FCone Snd N] 是 [Snd ◯ (comma_proj ◯ K)] 上的一个圆锥，一个具有相同行为的不同函子记录。
*)

Definition cod_leg (N : Cone (comma_proj ◯ K)) (j : J) :
  snd vertex_obj[N] ~{B}~> (comma_proj2 ◯ K) j := snd (cone_leg N j).

Lemma cod_coherence (N : Cone (comma_proj ◯ K)) {x y : J} (f : x ~{J}~> y) :
  fmap[comma_proj2 ◯ K] f ∘ cod_leg N x ≈ cod_leg N y.
Proof. exact (snd (cone_leg_coh N f)). Qed.

Definition cod_cone (N : Cone (comma_proj ◯ K)) : Cone (comma_proj2 ◯ K) :=
  @Build_Cone J B (comma_proj2 ◯ K) (snd vertex_obj[N])
    (@Build_ACone J B (snd vertex_obj[N]) (comma_proj2 ◯ K) (cod_leg N)
       (fun x y f => cod_coherence N f)).

(*
 #418's second projection preserves limiting cones unconditionally; the
 competitor is repackaged across the same record boundary. 

 --------
 #418 的第二次投影无条件地保留限制锥；竞争者在相同的记录边界上重新打包。
*)

Definition cod_limiting (N : Cone (comma_proj ◯ K)) (HN : IsLimitCone N) :
  IsLimitCone (cod_cone N).
Proof.
  intro M.
  pose (M' := @Build_Cone J B (Snd ◯ (comma_proj ◯ K)) vertex_obj[M]
                (@Build_ACone J B vertex_obj[M] (Snd ◯ (comma_proj ◯ K))
                   (cone_leg M) (fun x y f => cone_leg_coh M f))).
  destruct (Snd_PreservesLimitCone (comma_proj ◯ K) N HN M') as [u Hu Huniq].
  exists u.
  - intro j; exact (Hu j).
  - intros v Hv; apply Huniq; intro j; exact (Hv j).
Defined.

Definition tcod_limiting (N : Cone (comma_proj ◯ K)) (HN : IsLimitCone N) :
  IsLimitCone (FCone T (cod_cone N)) :=
  HT (cod_cone N) (cod_limiting N HN).

(*
 The cone over [T ◯ (comma_proj2 ◯ K)] with apex [S] of the domain apex,
 whose legs are the comma arrows of [K] after the domain legs. 

 --------
 以域顶点的顶点 [S] 为顶点，[T ◯ (comma_proj2 ◯ K)] 上的锥体，其边是域边后的 [K] 的逗号箭头。
*)

Definition dom_leg (N : Cone (comma_proj ◯ K)) (j : J) :
  S (fst vertex_obj[N]) ~{C}~> (T ◯ (comma_proj2 ◯ K)) j :=
  `2 (K j) ∘ fmap[S] (fst (cone_leg N j)).

Lemma dom_coherence (N : Cone (comma_proj ◯ K)) {x y : J} (f : x ~{J}~> y) :
  fmap[T ◯ (comma_proj2 ◯ K)] f ∘ dom_leg N x ≈ dom_leg N y.
Proof.
  unfold dom_leg.
  change (fmap[T] (snd `1 (fmap[K] f))
            ∘ (`2 (K x) ∘ fmap[S] (fst (cone_leg N x)))
            ≈ `2 (K y) ∘ fmap[S] (fst (cone_leg N y))).
  rewrite comp_assoc.
  rewrite <- (`2 (fmap[K] f)).
  rewrite <- comp_assoc, <- fmap_comp.
  now rewrite (fst (cone_leg_coh N f)).
Qed.

Definition dom_cone (N : Cone (comma_proj ◯ K)) :
  Cone (T ◯ (comma_proj2 ◯ K)) :=
  @Build_Cone J C (T ◯ (comma_proj2 ◯ K)) (S (fst vertex_obj[N]))
    (@Build_ACone J C (S (fst vertex_obj[N])) (T ◯ (comma_proj2 ◯ K))
       (dom_leg N) (fun x y f => dom_coherence N f)).

Section Lift.

Context (N : Cone (comma_proj ◯ K)) (HN : IsLimitCone N).

(*
 The comparison arrow: the mediator of [dom_cone N] into the preserved
 codomain limit. 

 --------
 比较箭头：将 [dom_cone N] 引入保留的余域极限的中介。
*)

Definition comma_lift_arrow :
  S (fst vertex_obj[N]) ~{C}~> T (snd vertex_obj[N]) :=
  unique_obj (tcod_limiting N HN (dom_cone N)).

Lemma comma_lift_arrow_commutes (j : J) :
  fmap[T] (snd (cone_leg N j)) ∘ comma_lift_arrow
    ≈ `2 (K j) ∘ fmap[S] (fst (cone_leg N j)).
Proof. exact (unique_property (tcod_limiting N HN (dom_cone N)) j). Qed.

(*
 Mac Lane's uniqueness clause: any arrow making every square commute is
 the comparison arrow. 

 --------
 麦克·莱恩的唯一性条款：任何使每个方形交换的箭头都是比较箭头。
*)

Lemma comma_lift_arrow_unique
  (h : S (fst vertex_obj[N]) ~{C}~> T (snd vertex_obj[N])) :
  (∀ j : J, fmap[T] (snd (cone_leg N j)) ∘ h
              ≈ `2 (K j) ∘ fmap[S] (fst (cone_leg N j))) →
  comma_lift_arrow ≈ h.
Proof. intro Hh. exact (uniqueness (tcod_limiting N HN (dom_cone N)) h Hh). Qed.

Definition comma_lift_obj : S ↓ T := (vertex_obj[N]; comma_lift_arrow).

Definition comma_lift_leg (j : J) : comma_lift_obj ~{S ↓ T}~> K j :=
  (cone_leg N j; symmetry (comma_lift_arrow_commutes j)).

Lemma comma_lift_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[K] f ∘ comma_lift_leg x ≈ comma_lift_leg y.
Proof. exact (cone_leg_coh N f). Qed.

Definition comma_lift_cone : Cone K :=
  @Build_Cone J (S ↓ T) K comma_lift_obj
    (@Build_ACone J (S ↓ T) comma_lift_obj K comma_lift_leg
       (fun x y f => comma_lift_coherence f)).

(* The lift lies over [N] ON THE NOSE. / 升力位于鼻子上的 [N] 之上。 *)

Example comma_lift_apex_strict :
  comma_proj vertex_obj[comma_lift_cone] = vertex_obj[N] := eq_refl.

Example comma_lift_leg_strict (j : J) :
  fmap[comma_proj] (cone_leg comma_lift_cone j) = cone_leg N j := eq_refl.

Definition comma_lift_StrictLift : StrictLift K comma_proj N :=
  @Build_StrictLift J (S ↓ T) (A ∏ B) K comma_proj N comma_lift_cone eq_refl
    (fun j => reflexivity _).

End Lift.

(*
 Reflection: a cone over [K] whose projection is limiting is limiting.
 The mediator downstairs is a comma morphism because the legs of the
 preserved codomain limit are jointly monic. 

 --------
 反思：一个位于 [K] 上的圆锥，其投影是极限的，则该圆锥也是极限的。楼下的中介是一个逗号态射，因为被保留余域极限的支腿是联合单性的。
*)

Definition comma_proj_reflect (M : Cone K)
  (HM : IsLimitCone (FCone comma_proj M)) : IsLimitCone M.
Proof using HT.
  intro M'.
  destruct (HM (FCone comma_proj M')) as [w Hw Hwu].
  assert (Hsq : (`2 vertex_obj[M]) ∘ fmap[S] (fst w)
                  ≈ fmap[T] (snd w) ∘ (`2 vertex_obj[M'])).
  { apply (limit_med_eq
             (limitcone_isalimit (tcod_limiting (FCone comma_proj M) HM))
             (dom_cone (FCone comma_proj M'))).
    - intro j.
      change (fmap[T] (snd `1 (cone_leg M j))
                ∘ ((`2 vertex_obj[M]) ∘ fmap[S] (fst w))
                ≈ (`2 (K j)) ∘ fmap[S] (fst `1 (cone_leg M' j))).
      rewrite comp_assoc.
      rewrite <- (`2 (cone_leg M j)).
      rewrite <- comp_assoc, <- fmap_comp.
      now rewrite (fst (Hw j)).
    - intro j.
      change (fmap[T] (snd `1 (cone_leg M j))
                ∘ (fmap[T] (snd w) ∘ (`2 vertex_obj[M']))
                ≈ (`2 (K j)) ∘ fmap[S] (fst `1 (cone_leg M' j))).
      rewrite comp_assoc, <- fmap_comp.
      rewrite (snd (Hw j)).
      symmetry.
      exact (`2 (cone_leg M' j)). }
  unshelve refine {| unique_obj := (w; Hsq) |}.
  - intro j. exact (Hw j).
  - intros v Hv. apply Hwu. intro j. exact (Hv j).
Defined.

Definition comma_proj_StrictlyCreatesLimit : StrictlyCreatesLimit K comma_proj.
Proof using HT.
  unshelve refine {| screates := fun N HN => comma_lift_StrictLift N HN |}.
  - intros N HN.
    apply comma_proj_reflect.
    exact (limitcone_transport
             (ConeIso_sym (slift_iso (comma_lift_StrictLift N HN);
                           slift_iso_legs (comma_lift_StrictLift N HN))) HN).
  - exact comma_proj_reflect.
Defined.

Definition comma_proj_CreatesLimit : CreatesLimit K comma_proj :=
  StrictlyCreatesLimit_CreatesLimit comma_proj_StrictlyCreatesLimit.

Definition comma_proj_Limit (L : Limit (comma_proj ◯ K)) : Limit K :=
  creates_limit_lift comma_proj_CreatesLimit L.

Example comma_proj_Limit_apex (L : Limit (comma_proj ◯ K)) :
  (`1 vertex_obj[comma_proj_Limit L]) = vertex_obj[L] := eq_refl.

Example comma_proj_Limit_arrow (L : Limit (comma_proj ◯ K)) :
  (`2 vertex_obj[comma_proj_Limit L])
    = comma_lift_arrow (@limit_cone _ _ _ L) (limit_limitcone L) := eq_refl.

End TwoSided.

(* * ** The arrow category: Mac Lane §V.1 Exercise 3 / * ** 箭头范畴：Mac Lane §V.1 练习 3 *)

Section ArrowLimit.

Context {C : Category}.

Definition arrow_proj_creates_limits {J : Category} (K : J ⟶ @Arrow C) :
  CreatesLimit K comma_proj :=
  comma_proj_CreatesLimit K (Id_PreservesLimitCone (comma_proj2 ◯ K)).

Definition arrow_proj_strictly_creates_limits {J : Category}
  (K : J ⟶ @Arrow C) :
  StrictlyCreatesLimit K comma_proj :=
  comma_proj_StrictlyCreatesLimit K (Id_PreservesLimitCone (comma_proj2 ◯ K)).

Definition arrow_proj_creates_all_limits :
  CreatesAllLimits (@comma_proj C C C Id[C] Id[C]) :=
  fun J K => arrow_proj_creates_limits K.

(*
 The corollary: the arrow category is complete whenever the base is, its
 limits computed on domains and codomains. 

 --------
 推论：每当基类是完备的时，箭头范畴也是完备的，其极限在源对象和目标对象上计算。
*)

Definition Arrow_Complete (HC : @Complete C) : @Complete (@Arrow C) :=
  creates_limits_Complete comma_proj (Product_Complete HC HC)
    arrow_proj_creates_all_limits.

Example Arrow_Complete_dom (HC : @Complete C) {J : Category}
  (K : J ⟶ @Arrow C) :
  fst (`1 vertex_obj[Arrow_Complete HC J K])
    = vertex_obj[HC J (Fst ◯ (comma_proj ◯ K))] := eq_refl.

Example Arrow_Complete_cod (HC : @Complete C) {J : Category}
  (K : J ⟶ @Arrow C) :
  snd (`1 vertex_obj[Arrow_Complete HC J K])
    = vertex_obj[HC J (Snd ◯ (comma_proj ◯ K))] := eq_refl.

End ArrowLimit.
