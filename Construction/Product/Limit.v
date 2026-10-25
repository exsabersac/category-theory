Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cartesian.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Product.Indexed.
Require Import Category.Functor.Opposite.

Generalizable All Variables.

(*
   * * Limits in a product of categories are computed componentwise 

   --------
   * * 类别的积中的极限是按分量计算的
*)

(*
 Book:  Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 §V.2 Exercise 2, printed p. 114 (PDF p. 123) — maclane:V.2:ex2
 Book:  Riehl, "Category Theory in Context", 2nd ed., §3.4 Exercise
 3.4.v, printed p. 108 (PDF p. 128) — riehl:3.4:exv
 nLab:  https://ncatlab.org/nlab/show/product+category
 nLab:  https://ncatlab.org/nlab/show/complete+category

 Mac Lane's exercise: a product of complete categories is complete, and
 dually for cocompleteness — limits in [C ∏ D] are computed one factor
 at a time.  Riehl's exercise says the same thing more precisely, for a
 product [∏_{i ∈ I} C_i] of categories: (i) each projection preserves
 limits; (ii) the projections JOINTLY CREATE limits — if every component
 diagram has a limit then those limits are the components of a limit of
 the whole diagram; and (iii) a product of categories has a given class
 of limits or colimits if and only if each factor does.

 WHAT IS DELIVERED, AND AT WHICH STRENGTH.

 For the binary product [C ∏ D] of Construction/Product.v, over a
 diagram [K : J ⟶ C ∏ D]:

 - [prod_cone] pairs a cone over [Fst ◯ K] with a cone over [Snd ◯ K]
 into a cone over [K]; the apex is the pair of apexes and every leg
 the pair of legs, on the nose ([prod_cone_apex], [prod_cone_leg]).
 - [prod_IsLimitCone]: the pairing of two limiting cones is limiting,
 and its mediator IS the pair of the two mediators, on the nose
 ([prod_IsLimitCone_med]).  This is Riehl's clause (ii), existence
 half, and the engine of everything below.
 - [Fst_PreservesLimitCone], [Snd_PreservesLimitCone]: Riehl's clause
 (i), UNCONDITIONALLY — no limit is assumed to exist in either
 factor.  The argument splices a competing cone in [C] with the
 [D]-image of the given limiting cone, reads the [C]-component of
 the mediator, and gets uniqueness by observing that [(v, id)] is a
 mediator for the spliced cone.
 - [prod_reflect]: a cone over [K] both of whose projections are
 limiting is limiting — Riehl's clause (ii), reflection half — by
 transporting [prod_IsLimitCone] across the cone isomorphism
 [prod_cone_iso : prod_cone (FCone Fst N) (FCone Snd N) ≅ N], whose
 apex isomorphism is [(id, id)].
 - [Product_JointlyCreateLimit]: the two projections, packaged as the
 [bool]-indexed family [ProdProj], inhabit Structure/Limit/Creation.v's
 [JointlyCreateLimit] — the creation reading of the exercise.
 - [Product_Limit], [Product_Complete], [Product_Cocomplete] —
 Mac Lane's statement and its dual.  The dual costs NOTHING: the
 opposite of a product is the product of the opposites BY
 CONVERSION ([Product_Opposite], Construction/Product.v, closes
 by [reflexivity]), so [Product_Cocomplete] is [Product_Complete] at
 [C^op] and [D^op] applied to [K^op], with [Complete_op_of_Cocomplete]
 the one-line passage that [Cocomplete C] IS [Complete (C^op)] up to
 the definitional [(G^op)^op = G].
 - Riehl's clause (iii), the "only if" direction, under an EXPLICIT
 POINT of the other factor: [Product_Limit_Fst : Limit (pair_const d G)
 → Limit G] and [Product_Complete_Fst : Complete (C ∏ D) → D →
 Complete C], with the [Snd] mirrors.  The point is needed to form a
 diagram in the product from a diagram in one factor (the constant
 diagram at [d] fills the other slot), and it is what the exercise
 silently assumes: with [D] empty, [C ∏ D] is empty and has no
 terminal object, so it is not complete whatever [C] is.  Deriving
 the point from completeness itself would go through the limit of
 the empty diagram, i.e. through Instance/Zero.v's [_0], whose
 hom and proof universes are pinned to [Set]; the explicit hypothesis
 keeps the statement universe-clean.
 - The componentwise [Product_Terminal], [Product_Initial] and
 [Product_Cocartesian] the verifier's survey found missing beside the
 pre-existing [Product_Cartesian] (Structure/Cartesian/Product.v).
 The two duals are the primal instances at the opposite categories,
 again by the conversion [Product_Opposite]; they are plain
 [Definition]s rather than registered instances, since a
 resolution goal [Terminal ((C ∏ D)^op)] does not syntactically
 match [Terminal (?C ∏ ?D)].

 For the [I]-indexed product [PiCat D] of Construction/Product/Indexed.v:

 - [pi_cone], [pi_IsLimitCone] (mediator the family of mediators, on
 the nose), [pi_cone_iso], [pi_reflect], [PiCat_JointlyCreateLimit],
 [PiCat_Limit], [PiCat_Complete] — Riehl's clause (ii) at arbitrary
 index, and the completeness half of (iii).  [PiCat] is consumed as
 the tree's [I]-indexed product of categories; the QA note on the
 issue points at a [Cat_HasIndexedProducts], since built in
 Instance/Cat/Limit.v with [PiCat] ITSELF as its object field, and
 nothing here depends on it.

 NOT DELIVERED, AND WHY.

 - Riehl's clause (i) at arbitrary index: that EACH [PiCat_Proj D i]
 preserves limits.  The binary argument splices a competing cone in
 one factor with the image of the limiting cone in the OTHER; at an
 arbitrary index type that splice must decide, for every [j], whether
 [j = i], and so needs decidable equality on [I] together with a
 transport of the spliced component — neither of which the binary
 case, where the two factors are told apart by the type checker,
 has to pay.  It is delivered for the BINARY product only, as
 [Fst_PreservesLimitCone] and [Snd_PreservesLimitCone] stated for the
 two projections directly — not as a family and not through
 [ProdProj], which packages the pair for clause (ii) alone — and is
 left open at a general [I].
 - [PiCat_Cocomplete].  [(PiCat D)^op] and [PiCat (fun i => (D i)^op)]
 agree on objects, homs, identities and composition but NOT as
 records: [PiCat]'s law fields are [Program] obligations, so the two
 are refused at [eq_refl] (pinned in Test/ProbeProductLimit418.v)
 and the free duality route of the binary case is unavailable.  A
 direct cocone development, or a transport of [Complete] along the
 identity-on-everything equivalence, would supply it; neither is
 attempted here.
 - Clause (iii)'s "only if" at arbitrary index, for the same
 point-of-the-other-factors reason as the binary case plus the
 splicing above.
 - Any comparison of [Product_Limit] at a discrete shape with
 [Product_Cartesian], or of the empty-shape limit with
 [Product_Terminal]: both would route through Instance/Discrete.v's
 universe-unannotated [DiscreteCat_Functor], which pins the ambient
 hom and proof universes to [Set] (the measurement recorded at
 Structure/Limit/Product/Finite.v and Functor/Hom/Limit.v).

 STRICTNESS, MEASURED STRICT FIRST.  Fifteen readbacks close by
 [eq_refl] and ship as [Example]s: the paired apex and legs, the
 [Fst]/[Snd] images of a paired cone leg by leg, the paired mediator,
 the pairing functor's object action, the recovered limit's apex, the
 terminal, initial and coproduct objects, and the family apex, projected
 legs, mediator and limit apex on the [PiCat] side.  The WHOLE-RECORD
 identifications do not — [FCone Fst (prod_cone N1 N2)] is not [N1]
 because the coherence field is a rebuilt proof and [≈] is Type-valued,
 and [prod_cone (FCone Fst N) (FCone Snd N)] is not [N] because a [prod]
 has no definitional eta — and are pinned as conversion negatives in
 Test/ProbeProductLimit418.v, with [prod_cone_iso] and [pi_cone_iso] the
 [≈]-level statements that do hold; on the [PiCat] side even the legs
 agree on the nose by function eta, which locates the whole-record
 refusal exactly in the coherence field.  Of the fifteen [Defined]
 tokens, exactly SIX are load-bearing — flipping any one of [prod_cone],
 [prod_IsLimitCone], [pair_const], [const_pair], [pi_cone] or
 [pi_IsLimitCone] alone to [Qed] breaks an [eq_refl] readback below it —
 and the other nine are [Defined] by the data convention only (measured
 by flipping each alone).

 UNIVERSES, MEASURED OFF BOTH BINDER AND BLOCK.  [Product] is fully
 polymorphic and [PiCat] ITSELF bounds only by the index (its block is
 four bounds and no equation), but every constant here that mentions a
 composite [Fst ◯ K] or [PiCat_Proj D i ◯ K] identifies the SHAPE's hom
 level with every factor's and the product's, and hom with proof —
 [prod_cone]'s block carries [u0 = u2], [u0 = u4], [u0 = u6] over the
 binders [J : Category@{u u0 u0}], [C : Category@{u1 u2 u2}],
 [D : Category@{u3 u4 u4}] — and on the binary side that is [Compose]'s
 doing, which is declared over three categories sharing ONE
 hom-and-proof level: at a shape whose homs are declared strictly below
 the factors' homs, the diagram [K : Ju ⟶ Cu ∏ Du] and a [Cone] over it
 are accepted while [Fst ◯ K] is refused (pinned in the probe as N6 with
 those two as controls).  THE [PiCat] SIDE CARRIES A SECOND
 IDENTIFICATION THE BINARY SIDE DOES NOT, AND IT RESTRICTS THE INDEX:
 all twelve [PiCat]-side constants put the index type's universe at the
 factors' hom-and-proof level — eleven in the BLOCK ([pi_cone] carries
 [u = u1], [u = u3], [u = u5] over [I : Type@{u}] and
 [D : I → Category@{u0 u1 u1}]) and [PiCat_Complete] in its BINDER
 alone ([D : I → Category@{u5 u u}] with NO block equation, so a
 block-only reader sees nothing) — so [I] must live at exactly the hom
 level of the factors.  The donor is [PiCat_Proj], whose own binder is
 [C : I → Category@{u1 u u}], and NOT [Compose]: at an index declared
 strictly above the factors' homs, [PiCat Du] is accepted while
 [PiCat_Proj Du], [pi_cone] and [PiCat_Complete] are each refused with
 [Cannot enforce dh = … because dh < ii], every refusal firing at the
 argument [Du] (pinned in the probe as N7 with [PiCat] as the control;
 the inherited constants cannot be tested apart from the donor, so
 whether any identifies anything of its own is not measured).  The
 first commit's header attributed everything to [Compose] and said
 nothing of this; a fess audit found it.  The donor is unannotated and
 the restriction is NOT claimed unavoidable.  The OBJECT universes of
 the shape, both factors and the product stay free of one another, only
 bounded.  The completeness
 statements additionally read [C] and [D] at one hom level in the
 BINDER with no block equation at all, [Complete]'s own shape; no
 word-bounded [Set] occurs in the binder or block of any of the 52
 constants.  All 52 — the 51 declared heads plus the single [Program]
 obligation [Product_Terminal_obligation_1], counted on [Print Module];
 the file declares no [Record]/[Class]/[Inductive], so there is no
 unlisted [Build_*] — are closed under the global context and gated in
 [make print-assumptions] fully qualified, as are the ten new constants
 of Structure/Limit/Creation.v; the transitive in-project closure is 29
 modules excluding this file; on the same convention, excluding itself,
 Construction/Product/Indexed's own closure is 17 and
 Structure/Limit/Creation's 23 (a first draft gave 18 and 24, counting
 each file in its own closure, a convention shift a fess audit
 caught). 

 --------
 书籍: Mac Lane, 《为数学工作者准备的范畴论》, 第2版, §V.2 练习2, 印刷页114 (PDF第123页) — maclane:V.2:ex2
 书籍: Riehl, 《语境中的范畴论》, 第2版, §3.4 练习 3.4.v, 印刷页108 (PDF第128页) — riehl:3.4:exv
 nLab: https://ncatlab.org/nlab/show/product+category
 nLab: https://ncatlab.org/nlab/show/complete+categoryMac Lane 的练习：完全范畴的积是完全的，余完全性亦然 —— 在 [C ∏ D] 中的极限可以一次对一个因子计算。Riehl 的练习更精确地说明了同样的内容，对于一个范畴的积 [∏_{i ∈ I} C_i]：（i）每个投影保持极限；（ii）这些投影联合创造极限 —— 如果每个组成图都有极限，那么这些极限就是整个图极限的组成部分；以及（iii）范畴的积具有某个类的极限或余极限，当且仅当每个因子具有相同的极限或余极限。

 交付了什么，以及以何种强度交付。

 对于 Construction/Product.v 中的二元积 [C ∏ D]，关于一个图 [K : J ⟶ C ∏ D]：- [prod_cone] 将 [Fst ◯ K] 的一个圆锥与 [Snd ◯ K] 的一个圆锥配对为 [K] 的一个圆锥；顶点是两个顶点的配对，每条边是边的配对，完全吻合（[prod_cone_apex], [prod_cone_leg]）。
 - [prod_IsLimitCone]：两个极限圆锥的配对是极限的，其中介是两个中介的配对，完全吻合（[prod_IsLimitCone_med]）。这是 Riehl 的条款 (ii)，存在性部分，也是以下所有内容的核心。
 - [Fst_PreservesLimitCone], [Snd_PreservesLimitCone]：Riehl 的条款 (i)，无条件——不假设任何一个因子中存在极限。该论证将 [C] 中一个竞争圆锥与给定极限圆锥的 [D] 映像拼接，读取中介的 [C] 分量，并通过观察 [(v, id)] 是拼接圆锥的中介来得到唯一性。- [prod_reflect]：一个在 [K] 之上的圆锥，其两个投影都是极限，则该圆锥也是极限——Riehl 的条款(ii)，反射半——通过将 [prod_IsLimitCone] 转移到圆锥同构 [prod_cone_iso : prod_cone (FCone Fst N) (FCone Snd N) ≅ N] 上，其顶点同构为 [(id, id)]。- [Product_JointlyCreateLimit]：两个投影，打包为 [bool] 索引的族 [ProdProj]，属于 Structure/Limit/Creation.v 的 [JointlyCreateLimit]——练习的创制解读。- [Product_Limit]，[Product_Complete]，[Product_Cocomplete]——Mac Lane 的陈述及其对偶。双重成本为零：一个乘积的相反数是通过转换（[Product_Opposite]，Construction/Product.v，由[reflexivity]关闭）的相反数的乘积，因此[Product_Cocomplete]是在[C^op]下的[Product_Complete]，并将[D^op]应用于[K^op]，其中[Complete_op_of_Cocomplete]是一行通道，使[Cocomplete C]成为[Complete (C^op)]，直到定义性的[(G^op)^op = G]。- Riehl的条款(iii)，“只有如果”方向，在另一个因子的明确点下：[Product_Limit_Fst : Limit (pair_const d G) → Limit G] 和 [Product_Complete_Fst : Complete (C ∏ D) → D → Complete C]，带有[Snd]的镜像。这个点是需要用来从一个因子的图在乘积中形成图（在 [d] 上的常数图填充另一个槽），这也是练习默默假设的：当 [D] 为空时，[C ∏ D] 为空且没有终对象，因此无论 [C] 是什么，它都不完整。从完整性本身推导出这个点将通过空图的极限，即通过 Instance/Zero.v 的 [_0]，其同态和证明宇宙固定在 [Set] 上；显式假设保持了陈述宇宙的干净。- 分量 [Product_Terminal]、[Product_Initial] 和 [Product_Cocartesian]，由验证者调查发现缺失在预先存在的 [Product_Cartesian]（Structure/Cartesian/Product.v）旁边。这两个对偶是在相对范畴中的原始实例，同样通过转换 [Product_Opposite]；它们是普通的 [Definition]，而不是注册实例，因为一个解析目标 [Terminal ((C ∏ D)^op)] 在语法上与 [Terminal (?C ∏ ?D)] 不匹配。

 对于 Construction/Product/Indexed.v 中的 [I] 索引的乘积 [PiCat D]：-  [pi_cone]，[pi_IsLimitCone]（调停者的调停者家族，正中），[pi_cone_iso]，[pi_reflect]，[PiCat_JointlyCreateLimit]，[PiCat_Limit]，[PiCat_Complete] — Riehl 的条款 (ii) 在任意索引，以及 (iii) 的完整性部分。[PiCat] 被用作树的 [I] 索引的类别乘积；关于这个问题的 QA 注释指向一个 [Cat_HasIndexedProducts]，因为它内置于 Instance/Cat/Limit.v 中，[PiCat] 本身作为其对象字段，并且这里没有任何内容依赖它。

 未交付，原因如下。- Riehl 的子句 (i) 在任意索引处：每个 [PiCat_Proj D i] 保留极限。二元参数将一个竞争锥在一个因子中与极限锥在另一个因子中的像拼接；在任意索引类型中，该拼接必须为每个 [j] 决定是否 [j = i]，因此需要在 [I] 上具备可判定的等式以及拼接组件的传递——而在二元情况中，类型检查器可以区分两个因子时，这两点都不必考虑。它仅针对二元积提供，如 [Fst_PreservesLimitCone] 和 [Snd_PreservesLimitCone] 对两个投影直接说明——不是作为族，也不是通过 [ProdProj] 提供，后者仅为子句 (ii) 打包对——并且在一般 [I] 上仍然开放。- [PiCat_Cocomplete].[(PiCat D)^op] 和 [PiCat (fun i => (D i)^op)] 在对象、同态、恒等式和复合上是一致的，但作为记录却不一致：[PiCat] 的法律字段是 [Program] 义务，因此两者在 [eq_refl] 被拒绝（固定在 Test/ProbeProductLimit418.v），而二元情况的自由对偶路径不可用。直接的余锥构造，或者沿着对所有事物的恒等等价的 [Complete] 传输，可以提供它；这里都没有尝试。—条款(iii) 在任意指标处的“仅当”，原因与二元情况相同，即因为其他因素的作用以及上述拼接。- 在离散形状下对 [Product_Limit] 与 [Product_Cartesian] 的任何比较，或对空形状极限与 [Product_Terminal] 的任何比较：两者都会通过 Instance/Discrete.v 中未注释宇宙的 [DiscreteCat_Functor]，该 [DiscreteCat_Functor] 将环境同态和证明宇宙固定在 [Set]（在 Structure/Limit/Product/Finite.v 和 Functor/Hom/Limit.v 中记录的测量值）。严格性，首先测量严格。十五个回读接近 [eq_refl] 并作为 [Example] 发送：成对的顶点和边，[Fst] / [Snd] 成对圆锥的逐边图像，成对的中介，配对函子的对象作用，恢复的极限顶点，以及终端、初始和余积对象，还有 [PiCat] 端的族顶点、投影边、中介和极限顶点。整个记录的识别并不——[FCone Fst (prod_cone N1 N2)] 不是 [N1]，因为相干场是重建证明，并且 [≈] 是类型值，而 [prod_cone (FCone Fst N) (FCone Snd N)] 不是 [N]，因为 [prod] 没有定义性 eta——并且被固定为 Test/ProbeProductLimit418.v 中的转换否定，[prod_cone_iso] 和 [pi_cone_iso] 是 [≈] 级别的成立语句；在 [PiCat] 端，即使各个部分也通过函数 eta 完全一致，这正好在相干场定位了整个记录拒绝的原因。在十五个 [Defined] 代币中，正好有六个是承重的 —— 单独将 [prod_cone]、[prod_IsLimitCone]、[pair_const]、[const_pair]、[pi_cone] 或 [pi_IsLimitCone] 翻转为 [Qed] 会破坏其下方的 [eq_refl] 读取 —— 而另外九个仅根据数据约定是 [Defined]（通过单独翻转每一个进行测量）。宇宙，同时从绑定器和块中测量。[Product] 是完全多态的，而 [PiCat] 本身仅通过索引进行绑定（它的块有四个边界且没有方程），但这里每一个提到复合 [Fst ◯ K] 或 [PiCat_Proj D i ◯ K] 的常量都标识了 SHAPE 的同态级别以及每个因子和乘积的同态，并带有证明——[prod_cone] 的块携带 [u0 = u2]、[u0 = u4]、[u0 = u6]，通过绑定器 [J : Category@{u u0 u0}]、[C : Category@{u1 u2 u2}]、[D : Category@{u3 u4 u4}]——而在二进制方面，这是 [Compose] 的操作，它在三个类别上声明，共享一个同态和证明级别：在一个其同态严格低于因子同态的形状上，图 [K : Ju ⟶ Cu ∏ Du] 及其上的 [Cone] 被接受，而 [Fst ◯ K] 被拒绝（在探针中固定为 N6，以前两者作为控制）。[PiCat] 侧携带第二个标识，而二进制侧没有，并且它限制索引：所有十二个 [PiCat] 侧常数将索引类型的宇宙置于因子的同态与证明水平——BLOCK 中的十一项（[pi_cone] 携带 [u = u1]、[u = u3]、[u = u5] 超过 [I : Type@{u}] 和 [D : I → Category@{u0 u1 u1}]）以及 [PiCat_Complete] 单独在其 BINDER 中（[D : I → Category@{u5 u u}] 没有块方程，所以仅块阅读器看不到任何内容）——因此 [I] 必须恰好处于因子的同态水平。捐赠者是 [PiCat_Proj]，其自身绑定器是 [C : I → Category@{u1 u u}]，而不是 [Compose]：在因子的同态严格以上声明的索引处，[PiCat Du] 被接受，而 [PiCat_Proj Du]、[pi_cone] 和 [PiCat_Complete] 都被 [Cannot enforce dh = … because dh < ii] 拒绝，每次拒绝都是在参数 [Du] 上触发（在探针中固定为 N7，[PiCat] 作为控制；继承的常量不能离开捐赠者单独测试，因此是否有任何识别其自身内容尚未测量）。第一次提交的标题将所有内容归因于 [Compose]，并对此未作说明；一次 Fess 审计发现了它。捐赠者未加注释，并且未声明该限制不可避免。形状的 OBJECT 宇宙，包括因子和乘积，彼此保持独立，仅被约束。完整性声明另外在 BINDER 中的一个同类级别上读取 [C] 和 [D]，但完全没有块方程，[Complete] 自身的形状；在任意 52 个常数的绑定器或块中都没有出现以单词为界的 [Set]。所有 52 个——51 个已声明的头部加上单个 [Program] 义务 [Product_Terminal_obligation_1]，计数于 [Print Module]；文件未声明 [Record] / [Class] / [Inductive]，因此没有未列出的 [Build_*]——在全局上下文下关闭，并在 [make print-assumptions] 中完全限定地控制，就像 Structure/Limit/Creation.v 的十个新常量一样；项目内传递闭包为 29 个模块，不包括此文件；按照相同的约定，不包括自身，Construction/Product/Indexed 的闭包为 17，Structure/Limit/Creation 的闭包为 23（初稿给出的是 18 和 24，计算每个文件在自身闭包中，一个约定变更被 fess 审计捕获）。
*)

(* * ** Cones over a diagram in a binary product / * ** 二元乘积图上的圆锥 *)

Section ProductCones.

Context {J C D : Category}.
Context (K : J ⟶ C ∏ D).

(*
 Pairing: a cone over each projected diagram assembles into a cone over
 [K], with the pair of apexes and the pairs of legs. 

 --------
 配对：每个投影图上的锥体组装成 [K] 上的锥体，包含顶点对和边对。
*)

Definition prod_cone (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K)) : Cone K.
Proof.
  unshelve refine
    (@Build_Cone J (C ∏ D) K (vertex_obj[N1], vertex_obj[N2])
       (@Build_ACone J (C ∏ D) (vertex_obj[N1], vertex_obj[N2]) K
          (fun x => (cone_leg N1 x, cone_leg N2 x)) _)).
  intros x y f; split.
  - exact (cone_leg_coh N1 f).
  - exact (cone_leg_coh N2 f).
Defined.

Example prod_cone_apex (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K)) :
  vertex_obj[prod_cone N1 N2] = (vertex_obj[N1], vertex_obj[N2]) := eq_refl.

Example prod_cone_leg (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K)) (x : J) :
  cone_leg (prod_cone N1 N2) x = (cone_leg N1 x, cone_leg N2 x) := eq_refl.

(*
 Projecting the pairing returns each component leg by leg, on the nose;
 the whole cone records differ only in their rebuilt coherence proofs. 

 --------
 将配对投影会逐腿精确返回每个组件；整个锥体的记录仅在其重建的相干性证明上有所不同。
*)

Example prod_cone_fst_leg (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K)) (x : J) :
  cone_leg (FCone Fst (prod_cone N1 N2)) x = cone_leg N1 x := eq_refl.

Example prod_cone_snd_leg (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K)) (x : J) :
  cone_leg (FCone Snd (prod_cone N1 N2)) x = cone_leg N2 x := eq_refl.

Definition prod_cone_fst_iso (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K)) :
  ConeIso (FCone Fst (prod_cone N1 N2)) N1.
Proof.
  exists iso_id.
  intro x; simpl; now rewrite id_right.
Defined.

Definition prod_cone_snd_iso (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K)) :
  ConeIso (FCone Snd (prod_cone N1 N2)) N2.
Proof.
  exists iso_id.
  intro x; simpl; now rewrite id_right.
Defined.

(* * ** The pairing of two limiting cones is limiting / * ** 两个限制性圆锥的配对是有限的 *)

(*
 The mediator out of a competing cone is the pair of the two mediators
 out of its projections; uniqueness is uniqueness in each factor. 

 --------
 来自竞争锥的中介是其投影的两个中介的配对；唯一性是在每个因子中的唯一性。
*)

Definition prod_IsLimitCone {N1 : Cone (Fst ◯ K)} {N2 : Cone (Snd ◯ K)}
  (H1 : IsLimitCone N1) (H2 : IsLimitCone N2) :
  IsLimitCone (prod_cone N1 N2).
Proof.
  intro M.
  unshelve refine
    {| unique_obj := (unique_obj (H1 (FCone Fst M)),
                      unique_obj (H2 (FCone Snd M))) |}.
  - intro x; split.
    + exact (unique_property (H1 (FCone Fst M)) x).
    + exact (unique_property (H2 (FCone Snd M)) x).
  - intros [v1 v2] Hv; split.
    + apply (uniqueness (H1 (FCone Fst M))).
      intro x; exact (fst (Hv x)).
    + apply (uniqueness (H2 (FCone Snd M))).
      intro x; exact (snd (Hv x)).
Defined.

Example prod_IsLimitCone_med {N1 : Cone (Fst ◯ K)} {N2 : Cone (Snd ◯ K)}
  (H1 : IsLimitCone N1) (H2 : IsLimitCone N2) (M : Cone K) :
  unique_obj (prod_IsLimitCone H1 H2 M)
    = (unique_obj (H1 (FCone Fst M)), unique_obj (H2 (FCone Snd M)))
  := eq_refl.

(*
   * ** Each projection preserves limits, unconditionally (Riehl (i)) 

   --------
   * ** 每个投影无条件地保持极限 (Riehl (i))
*)

(*
 Given a limiting cone [N] over [K] and a competing cone [M] over
 [Fst ◯ K], splice [M] with the [D]-image of [N] into a cone over [K];
 the [C]-component of its mediator into [N] is the wanted arrow.  For
 uniqueness, any [v] commuting with the [C]-legs makes [(v, id)] a
 mediator for the spliced cone, so [v] is that component. 

 --------
 给定一个在  [K] 上的极限锥  [N]  以及一个在  [Fst ◯ K] 上的竞争锥  [M] ，将  [M]  与  [D] -像的  [N] 拼接成一个在  [K] 上的锥；其到  [N] 的中介的  [C]  分量就是所需箭头。对于唯一性，任何与  [C] 腿交换的  [v] 都使  [(v, id)] 成为拼接锥的中介，因此  [v] 就是该分量。
*)

Definition Fst_PreservesLimitCone : PreservesLimitCone K Fst.
Proof.
  intros N HN M.
  pose (P := prod_cone M (FCone Snd N)).
  unshelve refine {| unique_obj := fst (unique_obj (HN P)) |}.
  - intro x; exact (fst (unique_property (HN P) x)).
  - intros v Hv.
    refine (fst (uniqueness (HN P) (v, id) _)).
    intro x; split.
    + exact (Hv x).
    + simpl; now rewrite id_right.
Defined.

Definition Snd_PreservesLimitCone : PreservesLimitCone K Snd.
Proof.
  intros N HN M.
  pose (P := prod_cone (FCone Fst N) M).
  unshelve refine {| unique_obj := snd (unique_obj (HN P)) |}.
  - intro x; exact (snd (unique_property (HN P) x)).
  - intros v Hv.
    refine (snd (uniqueness (HN P) (id, v) _)).
    intro x; split.
    + simpl; now rewrite id_right.
    + exact (Hv x).
Defined.

(*
   * ** A cone is limiting when both its projections are (Riehl (ii)) 

   --------
   * ** 当圆锥的两个投影都是极限时，该圆锥是限制性的（Riehl (ii))
*)

(*
 A cone over [K] is isomorphic to the pairing of its two projections; the
 apex isomorphism is [(id, id) : (fst n, snd n) ≅ n], which is not the
 identity only because [prod] has no definitional eta. 

 --------
 [K] 上的一个圆锥同构于它的两个投影的配对；顶点同构是 [(id, id) : (fst n, snd n) ≅ n]，只有因为 [prod] 没有定义性的 eta，它才不是恒等映射。
*)

Definition prod_cone_iso (N : Cone K) :
  ConeIso (prod_cone (FCone Fst N) (FCone Snd N)) N.
Proof.
  unshelve refine ((_; _)).
  - unshelve refine (@Build_Isomorphism (C ∏ D)
        (vertex_obj[prod_cone (FCone Fst N) (FCone Snd N)]) (vertex_obj[N])
        (id, id) (id, id) _ _).
    + split; simpl; apply id_left.
    + split; simpl; apply id_left.
  - intro x; split; simpl; apply id_right.
Defined.

Definition prod_reflect (N : Cone K)
  (H1 : IsLimitCone (FCone Fst N)) (H2 : IsLimitCone (FCone Snd N)) :
  IsLimitCone N :=
  limitcone_transport (prod_cone_iso N) (prod_IsLimitCone H1 H2).

(* * ** The projections jointly create limits / * ** 这些投影共同构成了限制 *)

(*
 The two projections as a [bool]-indexed family, so that the creation
 vocabulary of Structure/Limit/Creation.v applies verbatim. 

 --------
 将这两个投影作为 [bool] 索引的族，以便 Structure/Limit/Creation.v 的创建词汇可以逐字应用。
*)

Definition ProdFactor (b : bool) : Category := if b then C else D.

Definition ProdProj (b : bool) : C ∏ D ⟶ ProdFactor b :=
  match b as b0 return C ∏ D ⟶ ProdFactor b0 with
  | true  => Fst
  | false => Snd
  end.

Definition Product_JointlyCreateLimit : JointlyCreateLimit K ProdProj.
Proof.
  unshelve refine
    {| jcreates_lift := fun N HN => prod_cone (N true) (N false) |}.
  - intros N HN b.
    destruct b.
    + exact (prod_cone_fst_iso (N true) (N false)).
    + exact (prod_cone_snd_iso (N true) (N false)).
  - intros M H.
    exact (prod_reflect M (H true) (H false)).
Defined.

(*
   * ** Limits of the projected diagrams give a limit of the diagram 

   --------
   * ** 投影图的极限给出图的极限
*)

Definition Product_Limit (L1 : Limit (Fst ◯ K)) (L2 : Limit (Snd ◯ K)) :
  Limit K :=
  limitcone_limit _ (prod_IsLimitCone (limit_limitcone L1) (limit_limitcone L2)).

Example Product_Limit_apex (L1 : Limit (Fst ◯ K)) (L2 : Limit (Snd ◯ K)) :
  vertex_obj[Product_Limit L1 L2] = (vertex_obj[L1], vertex_obj[L2])
  := eq_refl.

End ProductCones.

(*
   * ** Mac Lane §V.2 Exercise 2: a product of complete categories is
   complete, and dually 

   --------
   * ** Mac Lane §V.2 练习 2：完全范畴的乘积是完全的，反之亦然
*)

Definition Product_Complete {C D : Category}
  (HC : @Complete C) (HD : @Complete D) : @Complete (C ∏ D) :=
  fun J K => Product_Limit K (HC J (Fst ◯ K)) (HD J (Snd ◯ K)).

(*
 [Cocomplete C] is [Complete (C^op)] up to the definitional involutions
 [(J^op)^op = J] and [(G^op)^op = G]; no cone is repackaged. 

 --------
 [Cocomplete C] 与 [Complete (C^op)] 在定义的对换下是等价的 [(J^op)^op = J] 和 [(G^op)^op = G]；没有圆锥被重新包装。
*)

Definition Complete_op_of_Cocomplete {E : Category} (H : @Cocomplete E) :
  @Complete (E^op) :=
  fun J G => H (Opposite J) (Opposite_Functor G).

(*
 The dual, through the conversion [(C ∏ D)^op = C^op ∏ D^op]. 

 --------
 双重，通过转换 [(C ∏ D)^op = C^op ∏ D^op]。
*)

Definition Product_Cocomplete {C D : Category}
  (HC : @Cocomplete C) (HD : @Cocomplete D) : @Cocomplete (C ∏ D) :=
  fun J K =>
    @Product_Complete (Opposite C) (Opposite D)
      (Complete_op_of_Cocomplete HC) (Complete_op_of_Cocomplete HD)
      (Opposite J) (Opposite_Functor K).

(*
   * ** The "only if" direction, at an explicit point of the other factor 

   --------
   * ** “只有在”方向，在另一个因子的明确点上
*)

Section ProductOnlyIf.

Context {C D : Category}.

(*
 The diagram in [C ∏ D] whose [C]-component is [G] and whose
 [D]-component is constant at [d]. 

 --------
 图 [C ∏ D] 中，其 [C] 分量为 [G]，且 [D] 分量恒定为 [d]。
*)

Definition pair_const (d : D) {J : Category} (G : J ⟶ C) : J ⟶ C ∏ D.
Proof.
  unshelve refine
    (@Build_Functor J (C ∏ D) (fun x => (G x, d))
       (fun _ _ f => (fmap[G] f, id)) _ _ _).
  - repeat intro; split; simpl; [ now apply fmap_respects | reflexivity ].
  - intro x; split; simpl; [ apply fmap_id | reflexivity ].
  - intros x y z f g; split; simpl;
      [ apply fmap_comp | symmetry; apply id_left ].
Defined.

Definition const_pair (c : C) {J : Category} (G : J ⟶ D) : J ⟶ C ∏ D.
Proof.
  unshelve refine
    (@Build_Functor J (C ∏ D) (fun x => (c, G x))
       (fun _ _ f => (id, fmap[G] f)) _ _ _).
  - repeat intro; split; simpl; [ reflexivity | now apply fmap_respects ].
  - intro x; split; simpl; [ reflexivity | apply fmap_id ].
  - intros x y z f g; split; simpl;
      [ symmetry; apply id_left | apply fmap_comp ].
Defined.

Example pair_const_obj (d : D) {J : Category} (G : J ⟶ C) (x : J) :
  fobj[pair_const d G] x = (G x, d) := eq_refl.

(*
 A cone over [Fst ◯ pair_const d G] IS a cone over [G]: the two functors
 agree on objects and arrows by conversion, so the repackaging carries
 the same apex and the same legs, and the two readings of "limiting"
 are convertible. 

 --------
 [Fst ◯ pair_const d G]上的一个锥体是[G]上的一个锥体：两个函子在对象和箭头上通过转换是一致的，所以重新包装具有相同的顶点和相同的边，两种“极限”的解读是可转换的。
*)

Definition repack_fst {d : D} {J : Category} {G : J ⟶ C}
  (N : Cone (Fst ◯ pair_const d G)) : Cone G :=
  @Build_Cone J C G (vertex_obj[N])
    (@Build_ACone J C (vertex_obj[N]) G (fun x => cone_leg N x)
       (fun x y f => cone_leg_coh N f)).

Definition repack_fst_inv {d : D} {J : Category} {G : J ⟶ C}
  (M : Cone G) : Cone (Fst ◯ pair_const d G) :=
  @Build_Cone J C (Fst ◯ pair_const d G) (vertex_obj[M])
    (@Build_ACone J C (vertex_obj[M]) (Fst ◯ pair_const d G)
       (fun x => cone_leg M x) (fun x y f => cone_leg_coh M f)).

Definition Product_Limit_Fst (d : D) {J : Category} (G : J ⟶ C)
  (L : Limit (pair_const d G)) : Limit G :=
  limitcone_limit (repack_fst (FCone Fst (@limit_cone _ _ _ L)))
    (fun M => Fst_PreservesLimitCone (pair_const d G)
                (@limit_cone _ _ _ L) (limit_limitcone L) (repack_fst_inv M)).

Definition repack_snd {c : C} {J : Category} {G : J ⟶ D}
  (N : Cone (Snd ◯ const_pair c G)) : Cone G :=
  @Build_Cone J D G (vertex_obj[N])
    (@Build_ACone J D (vertex_obj[N]) G (fun x => cone_leg N x)
       (fun x y f => cone_leg_coh N f)).

Definition repack_snd_inv {c : C} {J : Category} {G : J ⟶ D}
  (M : Cone G) : Cone (Snd ◯ const_pair c G) :=
  @Build_Cone J D (Snd ◯ const_pair c G) (vertex_obj[M])
    (@Build_ACone J D (vertex_obj[M]) (Snd ◯ const_pair c G)
       (fun x => cone_leg M x) (fun x y f => cone_leg_coh M f)).

Definition Product_Limit_Snd (c : C) {J : Category} (G : J ⟶ D)
  (L : Limit (const_pair c G)) : Limit G :=
  limitcone_limit (repack_snd (FCone Snd (@limit_cone _ _ _ L)))
    (fun M => Snd_PreservesLimitCone (const_pair c G)
                (@limit_cone _ _ _ L) (limit_limitcone L) (repack_snd_inv M)).

Definition Product_Complete_Fst (H : @Complete (C ∏ D)) (d : D) :
  @Complete C :=
  fun J G => Product_Limit_Fst d G (H J (pair_const d G)).

Definition Product_Complete_Snd (H : @Complete (C ∏ D)) (c : C) :
  @Complete D :=
  fun J G => Product_Limit_Snd c G (H J (const_pair c G)).

(*
 The recovered limit sits on the [C]-component of the product limit's
 apex, on the nose. 

 --------
 回收的极限位于乘积极限顶点的 [C] 组件上，正好在顶端。
*)

Example Product_Limit_Fst_apex (d : D) {J : Category} (G : J ⟶ C)
  (L : Limit (pair_const d G)) :
  vertex_obj[Product_Limit_Fst d G L] = fst (vertex_obj[L]) := eq_refl.

End ProductOnlyIf.

(*
   * ** Componentwise terminal and initial objects, and coproducts 

   --------
   * ** 分量终对象和始对象，以及余积
*)

Section ProductTerminal.

Context {C D : Category}.

#[export]
Program Instance Product_Terminal `{@Terminal C} `{@Terminal D} :
  @Terminal (C ∏ D) := {
  terminal_obj := (1, 1);
  one := fun _ => (one, one)
}.
Next Obligation. split; apply one_unique. Qed.

Example Product_Terminal_obj `{@Terminal C} `{@Terminal D} :
  @terminal_obj (C ∏ D) Product_Terminal = (@terminal_obj C _, @terminal_obj D _)
  := eq_refl.

End ProductTerminal.

(*
 The duals are the primal instances at the opposite categories, through
 the conversion [Product_Opposite]; not registered for resolution. 

 --------
 对偶是在相反范畴下的原始实例，通过转换 [Product_Opposite]；未注册以进行解析。
*)

Definition Product_Initial {C D : Category}
  (HC : @Initial C) (HD : @Initial D) : @Initial (C ∏ D) :=
  @Product_Terminal (C^op) (D^op) HC HD.

Definition Product_Cocartesian {C D : Category}
  (HC : @Cocartesian C) (HD : @Cocartesian D) : @Cocartesian (C ∏ D) :=
  @Product_Cartesian (C^op) (D^op) HC HD.

Example Product_Initial_obj {C D : Category}
  (HC : @Initial C) (HD : @Initial D) :
  @initial_obj (C ∏ D) (Product_Initial HC HD)
    = (@initial_obj C HC, @initial_obj D HD)
  := eq_refl.

Example Product_Cocartesian_obj {C D : Category}
  (HC : @Cocartesian C) (HD : @Cocartesian D) (x y : C ∏ D) :
  @Coprod (C ∏ D) (Product_Cocartesian HC HD) x y
    = (@Coprod C HC (fst x) (fst y), @Coprod D HD (snd x) (snd y))
  := eq_refl.

(*
   * ** The set-indexed product: Riehl's clause (ii) at arbitrary index 

   --------
   * ** 集合索引积：任意索引下 Riehl 的条款 (ii)
*)

Section PiCatCones.

Context {I : Type} {D : I → Category} {J : Category}.
Context (K : J ⟶ PiCat D).

Definition pi_cone (N : ∀ i : I, Cone (PiCat_Proj D i ◯ K)) : Cone K.
Proof.
  unshelve refine
    (@Build_Cone J (PiCat D) K (fun i => vertex_obj[N i])
       (@Build_ACone J (PiCat D) (fun i => vertex_obj[N i]) K
          (fun x i => cone_leg (N i) x) _)).
  intros x y f i.
  exact (cone_leg_coh (N i) f).
Defined.

Example pi_cone_apex (N : ∀ i : I, Cone (PiCat_Proj D i ◯ K)) :
  vertex_obj[pi_cone N] = fun i => vertex_obj[N i] := eq_refl.

Example pi_cone_proj_leg (N : ∀ i : I, Cone (PiCat_Proj D i ◯ K))
  (i : I) (x : J) :
  cone_leg (FCone (PiCat_Proj D i) (pi_cone N)) x = cone_leg (N i) x
  := eq_refl.

Definition pi_cone_proj_iso (N : ∀ i : I, Cone (PiCat_Proj D i ◯ K)) (i : I) :
  ConeIso (FCone (PiCat_Proj D i) (pi_cone N)) (N i).
Proof.
  exists iso_id.
  intro x; simpl; now rewrite id_right.
Defined.

Definition pi_IsLimitCone (N : ∀ i : I, Cone (PiCat_Proj D i ◯ K))
  (HN : ∀ i : I, IsLimitCone (N i)) : IsLimitCone (pi_cone N).
Proof.
  intro M.
  unshelve refine
    {| unique_obj := fun i => unique_obj (HN i (FCone (PiCat_Proj D i) M)) |}.
  - intros x i.
    exact (unique_property (HN i (FCone (PiCat_Proj D i) M)) x).
  - intros v Hv i.
    apply (uniqueness (HN i (FCone (PiCat_Proj D i) M))).
    intro x; exact (Hv x i).
Defined.

Example pi_IsLimitCone_med (N : ∀ i : I, Cone (PiCat_Proj D i ◯ K))
  (HN : ∀ i : I, IsLimitCone (N i)) (M : Cone K) :
  unique_obj (pi_IsLimitCone N HN M)
    = fun i => unique_obj (HN i (FCone (PiCat_Proj D i) M))
  := eq_refl.

(*
 Here the apex isomorphism IS [iso_id]: a function has definitional eta
 where a pair does not, so the two apexes are the same object. 

 --------
 这里顶点同构是 [iso_id]：一个函数有定义性的 eta，而一对没有，所以这两个顶点是相同的对象。
*)

Definition pi_cone_iso (N : Cone K) :
  ConeIso (pi_cone (fun i => FCone (PiCat_Proj D i) N)) N.
Proof.
  exists iso_id.
  intros x i; simpl; apply id_right.
Defined.

Definition pi_reflect (N : Cone K)
  (H : ∀ i : I, IsLimitCone (FCone (PiCat_Proj D i) N)) : IsLimitCone N :=
  limitcone_transport (pi_cone_iso N)
    (pi_IsLimitCone (fun i => FCone (PiCat_Proj D i) N) H).

Definition PiCat_JointlyCreateLimit : JointlyCreateLimit K (PiCat_Proj D).
Proof.
  unshelve refine {| jcreates_lift := fun N HN => pi_cone N |}.
  - intros N HN i; exact (pi_cone_proj_iso N i).
  - exact pi_reflect.
Defined.

Definition PiCat_Limit (L : ∀ i : I, Limit (PiCat_Proj D i ◯ K)) : Limit K :=
  limitcone_limit _
    (pi_IsLimitCone (fun i => @limit_cone _ _ _ (L i))
       (fun i => limit_limitcone (L i))).

Example PiCat_Limit_apex (L : ∀ i : I, Limit (PiCat_Proj D i ◯ K)) :
  vertex_obj[PiCat_Limit L] = fun i => vertex_obj[L i] := eq_refl.

End PiCatCones.

Definition PiCat_Complete {I : Type} {D : I → Category}
  (HD : ∀ i : I, @Complete (D i)) : @Complete (PiCat D) :=
  fun J K => PiCat_Limit K (fun i => HD i J (PiCat_Proj D i ◯ K)).
