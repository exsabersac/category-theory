Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Instance.Sets.Cocartesian.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Discrete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Limit.Indexed.Hom.
Require Import Category.Structure.Limit.Power.
Require Coq.Vectors.Fin.

Generalizable All Variables.

Import EqNotations.

(* * * The characterizing isomorphisms of a power and a copower / * * 幂与协幂的特征同构 *)

(*
 nLab:      https://ncatlab.org/nlab/show/power
 nLab:      https://ncatlab.org/nlab/show/copower

 Sources are those of Structure/Limit/Power.v, whose header carries the
 full citation block; the two statements this file exists for are

 - Riehl, "Category Theory in Context", 2nd ed., section 3.5, printed
 p. 110 (PDF p. 130), item [riehl:3.5:example4]:
 [C(X, A^I) ≅ C(X, A)^I], natural in [X], given by composing with the
 projections [ev_i]; in Set [A^I] is the ordinary function set and
 [ev_i] is evaluation at [i].
 - the same, printed p. 111 (PDF p. 131), item [riehl:3.5:example8]:
 [C(∐_I A, X) ≅ C(A, X)^I]; in Set the copower is [I × A].
 - Awodey, "Category Theory", 1st ed. (Carnegie Mellon pre-print,
 September 2005), section 3.2, unnumbered remark, printed p. 61 (PDF
 p. 70): in Sets a finite set is [1 + 1 + ⋯ + 1].

 NOTHING HERE IS A NEW THEOREM, AND THAT IS THE POINT.

 Structure/Limit/Indexed/Hom.v already proves, for an ARBITRARY family
 [f : A → C], that the comparison map from the representable to
 [c ↦ ∏ₐ C(c, f a)] is invertible exactly when [f] has an indexed product,
 and packages the invertible case as an [Isomorphism] in [[C^op, Sets]]
 natural in the varying object.  A power is that at the CONSTANT family, so
 every isomorphism below is [iprod_hom_iso] or [icoprod_hom_iso] applied,
 supplied by [:=] with no tactic and no obligation.  [power_hom_iso_is_donor]
 and [copower_hom_iso_is_donor] record by [eq_refl] that the derived form is
 the donor's TERM, not merely an isomorphism with the same type; likewise
 for the two comparison maps, the two inverses and the two biconditionals.

 What the constant family buys, beyond the name, is that the RIGHT-HAND
 SIDE becomes a power too -- in [Sets].  [power_hom_functor_is_Sets_power]
 and its dual record, by [eq_refl],

 fobj[power_hom_functor J b] c   =  power J (hom-setoid c b)
 fobj[copower_hom_functor J b] c =  power J (hom-setoid b c)

 with [power] on the right read at [Sets_HasIndexedProducts].  That is what
 turns Riehl's [C(X, A)^I] from a suggestive superscript into the same
 operator applied in another category, and it is why both of her examples
 -- the power one and the copower one -- have a POWER on the right.

 THE POINTWISE FORM IS DERIVED, NOT ASSUMED.  [power_hom_iso_at] evaluates
 the natural isomorphism at an object and lands at the literal shape

 [C(X, A^I) ≅[Sets] C(X, A)^I]

 using nothing but the natural isomorphism's own two laws plus [id_right]:
 the identity transformation's component at [c] is [fmap] of an identity,
 not an identity, so one [id_right] is the whole gap.  Naturality in [X] is
 NOT lost by evaluating -- it stays available in the natural form the
 pointwise one is derived from.

 THE [Sets] IDENTIFICATIONS, AND HOW MUCH OF EACH WAS ALREADY THERE

 Power side: mostly already in tree, and reused rather than reproved.
 Instance/Sets/Products.v already builds
 [Sets_exponent_IsIndexedProduct] and [Sets_constant_iprod_exponent] -- the
 function set [X ^ Sets_discrete I] satisfying the constant-family universal
 property, and its isomorphism with [indexed_product (fun _ : I => X)] --
 for Awodey 2.9 exercise 7(b).  [Sets_power_exponent] IS that isomorphism,
 by [:=].  What is added is the power vocabulary and three strict readings
 the donor file does not state: the carrier of [power J X] is literally the
 function type [J → X] ([Sets_power_carrier]), [power_ev] is literally
 evaluation ([Sets_power_ev_computes], [g j] on the nose), and evaluation in
 the exponential agrees with it across the isomorphism
 ([Sets_power_ev_is_exponent_eval], at [≈] -- it is an equation between
 morphisms).

 Copower side: new here.  [Sets_copower_prod] is Riehl's [I · A ≅ I × A],
 with [I] read as the discrete setoid [Sets_discrete I] -- the same reading
 Instance/Sets/Products.v takes for the exponential, and forced by the
 same fact, that the index of [HasIndexedCoproducts] is a bare [Type] while
 a product in [Sets] takes two setoids.  No claim is made about a coarser
 setoid on the index.

 AWODEY'S FINITE DECOMPOSITION IS THE [b := 1] READING AND NOT A SECOND
 CONSTRUCTION.  [Sets_copower_one : J · 1 ≅ Sets_discrete J] is assembled
 from two named maps with a three-tactic isomorphism proof -- built directly
 rather than by composing [Sets_copower_prod] with a right-unit isomorphism
 of the product, which would be longer, not shorter --
 [Sets_copower_fin] is it at [Fin.t n], and
 [Sets_copower_two] -- Awodey's [2 = 1 + 1] -- is
 [Sets_icoprod_bool] at the constant family, so the passage to the BINARY
 coproduct of Instance/Sets/Cocartesian.v costs nothing.  Non-vacuity is
 proved rather than gestured at: [Sets_copower_three_distinct] exhibits
 three pairwise-distinct elements of [Fin.t 3 · 1], so the [n]-fold copower
 of the terminal object is not collapsing.

 AN ENGINEERING FINDING, MEASURED, AND A SECOND SIGHTING OF A KNOWN HAZARD

 Instance/Sets/Products.v records that letting instance resolution
 close a [proper_morphism] field can pin a constant's index universe to
 [Set].  That happened again here, at a different construction, and was
 fixed the same way.  Written as a [Program Definition],
 [Sets_copower_one_from] raises NO obligation -- resolution closes the field
 during elaboration, the domain being the discrete setoid [Sets_discrete J]
 whose [≈] is Leibniz [eq] -- and [Set Printing Universes. About ...] then
 prints [Set = u] in its constraint block, an EQUALITY on the index
 universe, so [Sets_copower_one] would have applied only to indices in
 [Set].  Supplying the certificate by hand under [unshelve refine] removes
 it: the constant now carries [u < u0] and no [Set].  This is not left as a
 remembered fact -- Test/ProbePower.v declares the [Program] variant and
 pins its rejection at an index strictly above [Set], against the shipped
 constant at the same index as a control.  The mechanism behind the pinning
 was not investigated further; only the symptom and the fix were measured,
 which is also the scope of the note this repeats.

 UNIVERSES, MEASURED IN THE CONSTRAINT BLOCKS

 Reproduce with [Set Printing Universes.] and [About]; reading the binder
 alone gets this wrong.  Everything here inherits Structure/Limit/Indexed/
 Hom.v's situation exactly -- nothing below widens or narrows it -- and the
 inheritance was measured constant by constant rather than assumed:

 [power_hom_functor@{u u0 u1 u2 u3 u4}] takes [C : Category@{u3 u4 u4}]
 and an index [Type@{u}] with [u <= u1] and [u4 <= u1], so the index
 universe and [C]'s hom universe are each bounded by the target [Sets]'
 carrier universe [u1] and are unrelated to each other -- the same block
 the donor [iprod_hom_functor] carries.  [copower_hom_functor] prints the
 identical block.

 [power_hom_iso@{u u0 u1 u2 u3}] takes [C : Category@{u3 u u}] with the
 index at [Type@{u}]: the index universe IS [C]'s hom universe, an
 IDENTIFICATION and not merely a bound, and [C]'s proof universe is
 dragged along with it.  The donor [iprod_hom_iso] prints exactly the
 same shape, so this is inherited in full.  Structure/Limit/Indexed/Hom.v
 analyses the cause -- a [SetoidObject] is not cumulative here, so the
 [Sets] the comparison lives in has its carrier universe forced EQUAL to
 [C]'s hom universe -- and pins it as a formability negative.
 [copower_hom_iso] and [power_hom_iso_at] print the same shape.

 The [Sets] witnesses below carry only [u < u0] -- index strictly below the
 [Sets] carrier universe -- with no [Set] anywhere; see the finding just
 above for the one place that had to be worked for.

 WHAT IS NOT DELIVERED

 No naturality in the INDEX [J] or in the object [b]: both isomorphisms are
 natural in the varying object only, exactly as their donors are.  No
 [Representable] instance for [power_hom_functor] and no universal-element
 packaging.  No [HasIndexedCoproducts FinSet], so Awodey's decomposition is
 delivered at [Sets] only and nothing is claimed about skeletal [FinSet];
 the issue's own wording allows either.  No cardinality statement: [Fin.t n
 · 1] is shown isomorphic to the discrete setoid on [Fin.t n] and shown to
 have three pairwise-distinct elements at [n = 3], but no counting argument
 is made and Instance/FinSet/Skeleton.v is not invoked.  No comparison of
 the copower with the exponential, and no monoidal or enriched reading of
 either operator.

 STATUS: axiom-free.  All 58 constants -- 51 named plus 7 [Program]
 obligations, enumerated by [Print Module] per the docs/AXIOMS.md
 methodology -- report "Closed under the global context"; the Makefile's
 [print-assumptions] target audits the headline ones.  (Note that [Print
 Module] displays a [Qed]-opaque constant as [Parameter]; running it here
 shows NINE of them -- the seven [Program] obligations, which are opaque
 too, plus the two named lemmas
 [Sets_power_ev_is_exponent_eval] and [Sets_copower_three_distinct] --
 and all nine are ordinary opaque proofs, not axioms, which is what the
 audit above checks.) 

 --------
 nLab:       https://ncatlab.org/nlab/show/power 
 nLab:       https://ncatlab.org/nlab/show/copower 

 来源是 Structure/Limit/Power.v 中的源码，其标题包含完整的引用块；本文件存在的两个陈述是

 - Riehl, 《Category Theory in Context》，第二版，第 3.5 节，印刷页 110（PDF 第 130 页），项  [riehl:3.5:example4] ：
 [C(X, A^I) ≅ C(X, A)^I] ，在 [X] 中是自然的，通过与投影 [ev_i] 组合给出；在 Set 中 [A^I] 是普通函数集，
 [ev_i] 是在 [i] 上的计算。
 - 同上，印刷页 111（PDF 第 131 页），项 [riehl:3.5:example8] ：
 [C(∐_I A, X) ≅ C(A, X)^I]；在 Set 中余幂是 [I × A]。
 - Awodey, 《Category Theory》，第一版（卡内基梅隆预印本，2005 年 9 月），第 3.2 节，未编号的备注，印刷页 61（PDF 第 70 页）：在 Sets 中有限集合是 [1 + 1 + ⋯ + 1]。这里没有任何新的定理，这正是重点。

 Structure/Limit/Indexed/Hom.v 已经证明，对于任意族
 [f : A → C]，从可表示对象到
 [c ↦ ∏ₐ C(c, f a)] 的比较映射恰好在 [f] 有索引积时可逆，
 并将可逆的情况打包为 [Isomorphism] 在 [[C^op, Sets] 中，自然作用于变化的对象。一个幂就是在恒定族上，
 所以下面的每个同构都是 [iprod_hom_iso] 或 [icoprod_hom_iso] 的应用，
 由 [:=] 提供，无需策略，也无义务。[power_hom_iso_is_donor]
 和 [copower_hom_iso_is_donor] 通过 [eq_refl] 记录派生形式是
 供体的 TERM，不仅仅是具有相同类型的同构；同样适用于两个比较映射、两个逆映射和两个双条件。恒定族所获得的，除了名称之外，是右侧也变成一个幂——在 [Sets]、[power_hom_functor_is_Sets_power] 及其对偶记录 [eq_refl] 中，

 fobj [power_hom_functor J b]  c   =  power J (hom-setoid c b)
 fobj [copower_hom_functor J b]  c =  power J (hom-setoid b c)

 右侧用 [power] 在 [Sets_HasIndexedProducts] 处读取。这就是将 Riehl 的 [C(X, A)^I] 从一个提示性的上标变成在另一范畴上应用的相同算子的原因，也正是她的两个例子——幂例子和余幂例子——在右侧都有一个幂的原因。

 点态形式是推导出来的，而不是假定的。[power_hom_iso_at] 在一个对象处评估自然同构，并落到字面形状

 [C(X, A^I) ≅[Sets]  C(X, A)^I]仅使用自然同构自身的两个定律加上 [id_right]：
 恒等变换在 [c] 的分量是 [fmap] 的恒等，
 不是一个恒等，因此一个 [id_right] 就是整个差距。在 [X] 中的自然性
 通过求值不会丢失——它以点态形式可导出的自然形式保持可用。

 [Sets] 的识别，以及每个已经存在了多少幂集方面：大部分已在树中，且是重复使用而非重新证明。
 Instance/Sets/Products.v 已经构建了
 [Sets_exponent_IsIndexedProduct] 和 [Sets_constant_iprod_exponent] ——该
 函数集 [X ^ Sets_discrete I] 满足常数族的普遍性性质，并且它与 [indexed_product (fun _ : I => X)] 的同构 ——
 对于 Awodey 2.9 练习 7(b)。[Sets_power_exponent] 就是该同构，
 由 [:=] 给出。新增的是幂集词汇表和三个严格定义，
 原文件没有说明：[power J X] 的承载类型字面上是函数类型 [J → X] ([Sets_power_carrier])，
 [power_ev] 字面上是评估 ([Sets_power_ev_computes], [g j] 精确计算)，并且指数中的评估在同构中一致
 ([Sets_power_ev_is_exponent_eval]，在 [≈] ——它是在态射之间的一个等式)。Copower 方面：这里是新的。[Sets_copower_prod] 是 Riehl 的 [I · A ≅ I × A]，[I] 读作离散的集合等价 [Sets_discrete I]——Instance/Sets/Products.v 对指数函数的处理也是相同的，且由相同的事实强制：[HasIndexedCoproducts] 的指标是一个裸 [Type]，而 [Sets] 中的乘积需要两个集合等价。对于指标上的较粗集合等价，没有提出任何主张。AWODEY 的有限分解是 [b := 1] 的读法，而不是第二种构造。[Sets_copower_one : J · 1 ≅ Sets_discrete J] 是由两个已命名的映射及一个三策略同构证明组装而成 —— 是直接构建的，而不是通过与积的右单位同构组合 [Sets_copower_prod] 构建的，那样会更长而不是更短 —— [Sets_copower_fin] 在 [Fin.t n] 上是它自己，[Sets_copower_two] —— Awodey 的 [2 = 1 + 1] —— 在常数族上为 [Sets_icoprod_bool]，因此转向 Instance/Sets/Cocartesian.v 的二元余积不花费任何额外成本。非空性是经过证明的，而不是仅仅手势表示：[Sets_copower_three_distinct] 展示了 [Fin.t 3 · 1] 的三个两两不同元素，因此终对象的 [n] 重复幂不坍塌。一个经过测量的工程发现，以及已知风险的第二次目击。Instance/Sets/Products.v 记录了让实例解析关闭 [proper_morphism] 字段可能会将常量的索引宇宙固定到 [Set] 。这在这里再次发生，在一个不同的构造中，并以同样的方式修复。写成 [Program Definition] 时，[Sets_copower_one_from] 不会引发任何义务 —— 在展开过程中解析关闭了该字段，其域为离散的等价集合 [Sets_discrete J]，其 [≈] 为 Leibniz [eq] —— 然后 [Set Printing Universes. About ...] 在其约束块中打印 [Set = u]，这是索引宇宙上的一个等式，因此 [Sets_copower_one] 只会应用于 [Set] 中的索引。在 [unshelve refine] 下手动提供证明可以移除它：现在常量携带 [u < u0] 而不带 [Set]。这并不是作为一个被记住的事实留下的——Test/ProbePower.v 声明了 [Program] 变体，并将其拒绝固定在严格高于 [Set] 的索引处，以出货的常量在同一索引作为控制。固定的机制没有进一步研究；只测量了症状和修复，这也是本说明重复的范围。

 在约束块中测量的 UNIVERSES

 通过 [Set Printing Universes.] 和 [About] 进行重现；仅读取绑定器会出错。这里的所有内容完全继承了 Structure/Limit/Indexed/Hom.v 的情况——没有下层扩展或缩小——继承是逐个常量测量的，而不是假设的。[power_hom_functor@{u u0 u1 u2 u3 u4}] 接受 [C : Category@{u3 u4 u4}] 和一个索引 [Type@{u}]，以及 [u <= u1] 和 [u4 <= u1]，因此索引宇宙和 [C] 的 hom 宇宙各自被目标 [Sets] 的承载宇宙 [u1] 所限制，彼此无关 —— 与供体 [iprod_hom_functor] 携带的相同区块。[copower_hom_functor] 打印相同的区块。[power_hom_iso@{u u0 u1 u2 u3}] 使用 [C : Category@{u3 u u}] ，索引为 [Type@{u}]：索引宇宙是 [C] 的同构宇宙，是一个标识而不仅仅是一个界限，并且 [C] 的证明宇宙随之被带上。捐赠者 [iprod_hom_iso] 打印完全相同的形状，因此这是完整继承的。Structure/Limit/Indexed/Hom.v 分析了原因——这里 [SetoidObject] 不是累积的，因此 [Sets] 比较所处的宇宙被强制其载体宇宙等于 [C] 的同构宇宙——并且将其固定为不可形成的形式。[copower_hom_iso] 和 [power_hom_iso_at] 打印相同的形状。下面的[Sets]见证人仅携带[u < u0]——其索引严格低于[Sets]承载宇宙——且任何地方都没有[Set]；有关必须处理的唯一位置，请参见上方的发现。

 未交付的内容是什么在索引 [J] 或对象 [b] 中没有自然性：这两个同构仅在变化对象中是自然的，正如它们的原始对象一样。没有 [Representable] 对 [power_hom_functor] 的实例，也没有通用元素封装。没有 [HasIndexedCoproducts FinSet]，因此 Awodey 的分解仅在 [Sets] 处实现，并且对骨架 [FinSet] 没有任何声明；问题本身的措辞允许两种情况。没有基数声明：[Fin.t n · 1] 被证明同构于 [Fin.t n] 上的离散集合，并在 [n = 3] 被证明具有三个两两不同的元素，但没有进行计数论证，也没有调用 Instance/FinSet/Skeleton.v。没有比较余积与指数，也没有对任一运算符进行单体或丰富化解释。状态：无公理。所有 58 个常量——51 个有名称的加上 7 个 [Program] 义务，根据文档/AXIOMS.md 的 [Print Module] 方法列出——报告“在全局上下文下封闭”；Makefile 的 [print-assumptions] 目标审计主要的那些。（注意 [打印模块] 会将一个 [Qed] 不透明常量显示为 [Parameter]；在这里运行显示有九个——七个 [Program] 义务，它们也是不透明的，再加上两个命名的引理 [Sets_power_ev_is_exponent_eval] 和 [Sets_copower_three_distinct] ——而且这九个都是普通的不透明证明，不是公理，这正是上述审计检查的内容。）
*)

#[local] Obligation Tactic := idtac.

(* * ** The two hom functors, at a constant family / * ** 两个 hom 函子，在一个常数族上 *)

(* [c ↦ ∏_J C(c, b)], the right-hand side of Riehl's [C(X, A)^I]. / [c ↦ ∏_J C(c, b)]，Riehl 的 [C(X, A)^I] 的右侧。 *)
Definition power_hom_functor {C : Category} (J : Type) (b : C) : C^op ⟶ Sets :=
  iprod_hom_functor (fun _ : J => b).

(* [c ↦ ∏_J C(b, c)], the right-hand side of [C(∐_I A, X) ≅ C(A, X)^I]. / [c ↦ ∏_J C(b, c)]，[C(∐_I A, X) ≅ C(A, X)^I] 的右侧。 *)
Definition copower_hom_functor {C : Category} (J : Type) (b : C) : C ⟶ Sets :=
  icoprod_hom_functor (fun _ : J => b).

(* Each right-hand side is itself a power, in [Sets]. / 每个右侧本身都是 [Sets] 中的一个幂。 *)
Example power_hom_functor_is_Sets_power {C : Category} (J : Type) (b c : C) :
  fobj[power_hom_functor J b] c
  = @power Sets Sets_HasIndexedProducts J
      {| carrier := @hom C c b ; is_setoid := @homset C c b |} := eq_refl.

Example copower_hom_functor_is_Sets_power {C : Category} (J : Type) (b c : C) :
  fobj[copower_hom_functor J b] c
  = @power Sets Sets_HasIndexedProducts J
      {| carrier := @hom C b c ; is_setoid := @homset C b c |} := eq_refl.

(* * ** The comparison maps: composing with the evaluations, resp. injections / * ** 比较图：与评估、对应注入组合 *)

Definition power_hom_transform {C : Category} {J : Type} (b p : C)
  (ev : ∀ _ : J, p ~> b) :
  @Transform (C^op) Sets (@Curried_CoHom C p) (power_hom_functor J b) :=
  @iprod_hom_transform C J (fun _ : J => b) p ev.

Definition copower_hom_transform {C : Category} {J : Type} (b p : C)
  (inj : ∀ _ : J, b ~> p) :
  @Transform C Sets (@Curried_Hom C p) (copower_hom_functor J b) :=
  @icoprod_hom_transform C J (fun _ : J => b) p inj.

Example power_hom_transform_computes {C : Category} {J : Type} (b p : C)
  (ev : ∀ _ : J, p ~> b) (c : C) (u : c ~> p) :
  transform (power_hom_transform b p ev) c u = fun j : J => ev j ∘ u := eq_refl.

Example copower_hom_transform_computes {C : Category} {J : Type} (b p : C)
  (inj : ∀ _ : J, b ~> p) (c : C) (u : p ~> c) :
  transform (copower_hom_transform b p inj) c u = fun j : J => u ∘ inj j
  := eq_refl.

(* * ** The isomorphisms, derived at the constant family / * ** 在恒定族中得到的同构 *)

Definition power_hom_inverse {C : Category} {J : Type} {b p : C}
  {ev : ∀ _ : J, p ~> b} (H : IsPower b p ev) :
  @Transform (C^op) Sets (power_hom_functor J b) (@Curried_CoHom C p) :=
  @iprod_hom_inverse C J (fun _ : J => b) p ev H.

Definition copower_hom_inverse {C : Category} {J : Type} {b p : C}
  {inj : ∀ _ : J, b ~> p} (H : IsCopower b p inj) :
  @Transform C Sets (copower_hom_functor J b) (@Curried_Hom C p) :=
  @icoprod_hom_inverse C J (fun _ : J => b) p inj H.

(* Riehl 3.5.4: [C(X, A^I) ≅ C(X, A)^I], natural in [X]. / Riehl 3.5.4：[C(X, A^I) ≅ C(X, A)^I]，自然出现在[X]中。 *)
Definition power_hom_iso {C : Category} {J : Type} {b p : C}
  {ev : ∀ _ : J, p ~> b} (H : IsPower b p ev) :
  @Isomorphism ([C^op, Sets]) (@Curried_CoHom C p) (power_hom_functor J b) :=
  @iprod_hom_iso C J (fun _ : J => b) p ev H.

(* Riehl 3.5.8: [C(I · A, X) ≅ C(A, X)^I], natural in [X]. / Riehl 3.5.8：[C(I · A, X) ≅ C(A, X)^I]，在[X]中是自然的。 *)
Definition copower_hom_iso {C : Category} {J : Type} {b p : C}
  {inj : ∀ _ : J, b ~> p} (H : IsCopower b p inj) :
  @Isomorphism ([C, Sets]) (@Curried_Hom C p) (copower_hom_functor J b) :=
  @icoprod_hom_iso C J (fun _ : J => b) p inj H.

(*
 The converse, and the biconditional: an invertible comparison map is a
 universal property.  Both are the donor's, at the constant family. 

 --------
 逆命题以及双条件命题：可逆的比较映射是一个普适性质。两者都属于捐赠者，在恒定族上。
*)
Definition power_of_hom_iso {C : Category} {J : Type} {b p : C}
  {ev : ∀ _ : J, p ~> b}
  (I : @IsIsomorphism ([C^op, Sets]) (@Curried_CoHom C p)
                      (power_hom_functor J b)
                      (power_hom_transform b p ev)) :
  IsPower b p ev :=
  @iprod_of_hom_iso C J (fun _ : J => b) p ev I.

Definition copower_of_hom_iso {C : Category} {J : Type} {b p : C}
  {inj : ∀ _ : J, b ~> p}
  (I : @IsIsomorphism ([C, Sets]) (@Curried_Hom C p)
                      (copower_hom_functor J b)
                      (copower_hom_transform b p inj)) :
  IsCopower b p inj :=
  @icoprod_of_hom_iso C J (fun _ : J => b) p inj I.

Definition power_iff_hom_iso {C : Category} {J : Type} (b p : C)
  (ev : ∀ _ : J, p ~> b) :
  IsPower b p ev ↔
  @IsIsomorphism ([C^op, Sets]) (@Curried_CoHom C p) (power_hom_functor J b)
                 (power_hom_transform b p ev) :=
  @iprod_iff_hom_iso C J (fun _ : J => b) p ev.

Definition copower_iff_hom_iso {C : Category} {J : Type} (b p : C)
  (inj : ∀ _ : J, b ~> p) :
  IsCopower b p inj ↔
  @IsIsomorphism ([C, Sets]) (@Curried_Hom C p) (copower_hom_functor J b)
                 (copower_hom_transform b p inj) :=
  @icoprod_iff_hom_iso C J (fun _ : J => b) p inj.

(* * ** The derived forms are the donors' TERMS, not merely their types / * ** 派生形式是捐赠者的条款，而不仅仅是它们的类型 *)

Example power_hom_functor_is_donor {C : Category} (J : Type) (b : C) :
  power_hom_functor J b = @iprod_hom_functor C J (fun _ : J => b) := eq_refl.

Example copower_hom_functor_is_donor {C : Category} (J : Type) (b : C) :
  copower_hom_functor J b = @icoprod_hom_functor C J (fun _ : J => b)
  := eq_refl.

Example power_hom_transform_is_donor {C : Category} {J : Type} (b p : C)
  (ev : ∀ _ : J, p ~> b) :
  power_hom_transform b p ev = @iprod_hom_transform C J (fun _ : J => b) p ev
  := eq_refl.

Example copower_hom_transform_is_donor {C : Category} {J : Type} (b p : C)
  (inj : ∀ _ : J, b ~> p) :
  copower_hom_transform b p inj
  = @icoprod_hom_transform C J (fun _ : J => b) p inj := eq_refl.

Example power_hom_inverse_is_donor {C : Category} {J : Type} {b p : C}
  {ev : ∀ _ : J, p ~> b} (H : IsPower b p ev) :
  power_hom_inverse H = @iprod_hom_inverse C J (fun _ : J => b) p ev H
  := eq_refl.

Example copower_hom_inverse_is_donor {C : Category} {J : Type} {b p : C}
  {inj : ∀ _ : J, b ~> p} (H : IsCopower b p inj) :
  copower_hom_inverse H = @icoprod_hom_inverse C J (fun _ : J => b) p inj H
  := eq_refl.

Example power_hom_iso_is_donor {C : Category} {J : Type} {b p : C}
  {ev : ∀ _ : J, p ~> b} (H : IsPower b p ev) :
  power_hom_iso H = @iprod_hom_iso C J (fun _ : J => b) p ev H := eq_refl.

Example copower_hom_iso_is_donor {C : Category} {J : Type} {b p : C}
  {inj : ∀ _ : J, b ~> p} (H : IsCopower b p inj) :
  copower_hom_iso H = @icoprod_hom_iso C J (fun _ : J => b) p inj H := eq_refl.

Example power_iff_hom_iso_is_donor {C : Category} {J : Type} (b p : C)
  (ev : ∀ _ : J, p ~> b) :
  power_iff_hom_iso b p ev = @iprod_iff_hom_iso C J (fun _ : J => b) p ev
  := eq_refl.

Example copower_iff_hom_iso_is_donor {C : Category} {J : Type} (b p : C)
  (inj : ∀ _ : J, b ~> p) :
  copower_iff_hom_iso b p inj = @icoprod_iff_hom_iso C J (fun _ : J => b) p inj
  := eq_refl.

(*
 And the backward leg still computes to the mediator the [∃!] accessor
 names, so the packaging cannot drift from the universal property. 

 --------
 而后退的腿仍然将 [∃!] 访问器名称计算给中介，因此包装不能偏离通用属性。
*)
Example power_hom_iso_from_is_desc {C : Category} {J : Type} {b p : C}
  {ev : ∀ _ : J, p ~> b} (H : IsPower b p ev)
  (c : C) (fam : ∀ _ : J, c ~> b) :
  transform (from (power_hom_iso H)) c fam = unique_obj (power_desc H fam)
  := eq_refl.

Example copower_hom_iso_from_is_desc {C : Category} {J : Type} {b p : C}
  {inj : ∀ _ : J, b ~> p} (H : IsCopower b p inj)
  (c : C) (fam : ∀ _ : J, b ~> c) :
  transform (from (copower_hom_iso H)) c fam = unique_obj (copower_desc H fam)
  := eq_refl.

(*
   * ** The pointwise form, evaluated at an object

   Riehl states [C(X, A^I) ≅ C(X, A)^I].  Evaluating the natural
   isomorphism above at [X] lands at exactly that shape, the right-hand side
   being a power in [Sets] by [power_hom_functor_is_Sets_power].  The only
   step is a unit law -- [id_right] on the power side, [id_left] on the
   copower side, the orientation flipping with the variance -- because the
   identity transformation's component is [fmap] of an identity. 

   --------
   * ** 点态形式，在某个对象上求值

   Riehl 陈述了 [C(X, A^I) ≅ C(X, A)^I]。在上述自然同构在 [X] 上求值时，正好得到那个形式，右边是 [Sets] 对 [power_hom_functor_is_Sets_power] 的一个幂。唯一的步骤是单位律 —— 在幂的一边是 [id_right]，在余幂的一边是 [id_left]，并且方向随变异而翻转 —— 因为恒等变换的分量是一个恒等的 [fmap]。
*)

Program Definition power_hom_iso_at {C : Category} {J : Type} {b p : C}
  {ev : ∀ _ : J, p ~> b} (H : IsPower b p ev) (c : C) :
  @Isomorphism Sets {| carrier := @hom C c p ; is_setoid := @homset C c p |}
    (@power Sets Sets_HasIndexedProducts J
       {| carrier := @hom C c b ; is_setoid := @homset C c b |}) := {|
  to   := transform (to (power_hom_iso H)) c;
  from := transform (from (power_hom_iso H)) c
|}.
Next Obligation.
  intros C J b p ev H c fam j.
  pose proof (iso_to_from (power_hom_iso H) c fam j) as Hr; simpl in *.
  now rewrite id_right in Hr.
Qed.
Next Obligation.
  intros C J b p ev H c u.
  pose proof (iso_from_to (power_hom_iso H) c u) as Hl; simpl in *.
  now rewrite id_right in Hl.
Qed.

Program Definition copower_hom_iso_at {C : Category} {J : Type} {b p : C}
  {inj : ∀ _ : J, b ~> p} (H : IsCopower b p inj) (c : C) :
  @Isomorphism Sets {| carrier := @hom C p c ; is_setoid := @homset C p c |}
    (@power Sets Sets_HasIndexedProducts J
       {| carrier := @hom C b c ; is_setoid := @homset C b c |}) := {|
  to   := transform (to (copower_hom_iso H)) c;
  from := transform (from (copower_hom_iso H)) c
|}.
Next Obligation.
  intros C J b p inj H c fam j.
  pose proof (iso_to_from (copower_hom_iso H) c fam j) as Hr; simpl in *.
  now rewrite id_left in Hr.
Qed.
Next Obligation.
  intros C J b p inj H c u.
  pose proof (iso_from_to (copower_hom_iso H) c u) as Hl; simpl in *.
  now rewrite id_left in Hl.
Qed.

(* * ** At the chosen (co)power of a category that has all of them / * ** 在具有所有这些的类别的选定（共）幂次 *)

Definition class_power_hom_iso {C : Category} {HP : @HasIndexedProducts C}
  (J : Type) (b : C) :
  @Isomorphism ([C^op, Sets]) (@Curried_CoHom C (power J b))
               (power_hom_functor J b) :=
  power_hom_iso (power_ump J b).

Definition class_copower_hom_iso {C : Category} {HC : @HasIndexedCoproducts C}
  (J : Type) (b : C) :
  @Isomorphism ([C, Sets]) (@Curried_Hom C (copower J b))
               (copower_hom_functor J b) :=
  copower_hom_iso (copower_ump J b).

(*
   * ** Riehl 3.5.4 in [Sets]: the power is the function set, [ev_i] is
   evaluation at [i]

   The object-level half was already proved in Instance/Sets/Products.v for
   Awodey 2.9 exercise 7(b), and is reused by [:=] rather than reproved. 

   --------
   * ** Riehl 3.5.4 在 [Sets]：幂集是函数集，[ev_i] 是在 [i] 的取值

   对象层面的部分已经在 Instance/Sets/Products.v 中为 Awodey 2.9 练习 7(b) 证明过，并且被 [:=] 重用，而不是重新证明。
*)

Definition Sets_power_exponent (J : Type) (X : obj[Sets]) :
  @power Sets Sets_HasIndexedProducts J X ≅[Sets] Sets_pow J X :=
  Sets_constant_iprod_exponent J X.

Example Sets_power_carrier (J : Type) (X : obj[Sets]) :
  carrier (@power Sets Sets_HasIndexedProducts J X) = (J → carrier X)
  := eq_refl.

Example Sets_power_ev_computes (J : Type) (X : obj[Sets]) (j : J)
  (g : carrier (@power Sets Sets_HasIndexedProducts J X)) :
  @power_ev Sets Sets_HasIndexedProducts J X j g = g j := eq_refl.

Lemma Sets_power_ev_is_exponent_eval (J : Type) (X : obj[Sets]) (j : J) :
  Sets_exponent_eval J X j ∘ to (Sets_power_exponent J X)
    ≈ @power_ev Sets Sets_HasIndexedProducts J X j.
Proof. intros g; reflexivity. Qed.

(* * ** Riehl 3.5.8 in [Sets]: the copower is the product with the index / * ** Riehl 3.5.8 在 [Sets] 中：余幂是带指标的积 *)

Example Sets_copower_carrier (J : Type) (Y : obj[Sets]) :
  carrier (@copower Sets Sets_HasIndexedCoproducts J Y)
  = { _ : J & carrier Y } := eq_refl.

Example Sets_copower_inj_computes (J : Type) (Y : obj[Sets]) (j : J)
  (y : carrier Y) :
  @copower_inj Sets Sets_HasIndexedCoproducts J Y j y
  = existT (fun _ : J => carrier Y) j y := eq_refl.

Program Definition Sets_copower_prod_to (J : Type) (Y : obj[Sets]) :
  @copower Sets Sets_HasIndexedCoproducts J Y
    ~{Sets}~> (Sets_discrete J × Y)%object := {|
  morphism := fun p : { _ : J & carrier Y } => (projT1 p, projT2 p)
|}.
Next Obligation.
  intros J Y [i x] [j y] [e Hxy]; simpl in *; destruct e; simpl in *.
  split; [reflexivity|exact Hxy].
Qed.

Program Definition Sets_copower_prod_from (J : Type) (Y : obj[Sets]) :
  (Sets_discrete J × Y)%object
    ~{Sets}~> @copower Sets Sets_HasIndexedCoproducts J Y := {|
  morphism := fun p : (J * carrier Y)%type =>
                existT (fun _ : J => carrier Y) (fst p) (snd p)
|}.
Next Obligation.
  intros J Y [i x] [j y] [He Hxy]; simpl in *; destruct He; simpl in *.
  exists eq_refl; exact Hxy.
Qed.

Definition Sets_copower_prod (J : Type) (Y : obj[Sets]) :
  @copower Sets Sets_HasIndexedCoproducts J Y
    ≅[Sets] (Sets_discrete J × Y)%object.
Proof.
  refine {| to := Sets_copower_prod_to J Y
          ; from := Sets_copower_prod_from J Y |}.
  - intros [i x]; split; reflexivity.
  - intros [i x]; exists eq_refl; reflexivity.
Defined.

(*
   * ** Awodey 3.2: a finite set is the [n]-fold copower of the terminal object

   This is the [b := 1] reading of [Sets_copower_prod]'s statement and not a
   second construction; it is proved directly because doing so is shorter
   than composing with a right-unit isomorphism of the product. 

   --------
   * ** Awodey 3.2：一个有限集合是终对象的  [n] 倍积幂

   这是对 [Sets_copower_prod] 声明的 [b := 1] 读法，而不是第二种构造；它直接被证明，因为这样做比与积的右单位同构组合更简短。
*)

Program Definition Sets_copower_one_to (J : Type) :
  @copower Sets Sets_HasIndexedCoproducts J 1%object
    ~{Sets}~> Sets_discrete J := {|
  morphism := fun p : { _ : J & poly_unit } => projT1 p
|}.
Next Obligation.
  intros J [i x] [j y] [e Hxy]; simpl in *; destruct e; reflexivity.
Qed.

(*
 The [proper_morphism] certificate is supplied by hand deliberately: under
 [Program] it is closed by instance resolution instead, and that pins this
 constant's index universe to [Set].  See the header. 

 --------
 [proper_morphism] 证书是故意手工提供的：在 [Program] 下，它则通过实例解析关闭，这将把该常量的索引宇宙固定到 [Set]。参见头文件。
*)
Definition Sets_copower_one_from (J : Type) :
  Sets_discrete J
    ~{Sets}~> @copower Sets Sets_HasIndexedCoproducts J 1%object.
Proof.
  unshelve refine {| morphism := fun i : J =>
                       existT (fun _ : J => poly_unit) i ttt |}.
  intros i j Hij; destruct Hij; exists eq_refl; reflexivity.
Defined.

Definition Sets_copower_one (J : Type) :
  @copower Sets Sets_HasIndexedCoproducts J 1%object ≅[Sets] Sets_discrete J.
Proof.
  refine {| to := Sets_copower_one_to J; from := Sets_copower_one_from J |}.
  - intros i; reflexivity.
  - intros [i []]; exists eq_refl; reflexivity.
Defined.

(* The finite case: a set of [n] elements is the [n]-fold copower of [1]. / 有限情况：一个包含 [n] 个元素的集合是 [n] 倍的 [1] 的共幂。 *)
Definition Sets_copower_fin (n : nat) :
  @copower Sets Sets_HasIndexedCoproducts (Fin.t n) 1%object
    ≅[Sets] Sets_discrete (Fin.t n) :=
  Sets_copower_one (Fin.t n).

(*
 Awodey's [2 = 1 + 1], through the BINARY coproduct of
 Instance/Sets/Cocartesian.v: the constant-family instance of the
 pre-existing [Sets_icoprod_bool], so the passage costs nothing. 

 --------
 Awodey 的 [2 = 1 + 1]，通过 Instance/Sets/Cocartesian.v 的 BINARY coproduct：预先存在的 [Sets_icoprod_bool] 的常数族实例，因此这个过程不花费任何成本。
*)
Definition Sets_copower_two :
  @copower Sets Sets_HasIndexedCoproducts bool 1%object ≅[Sets] (1 + 1)%object :=
  Sets_icoprod_bool (fun _ : bool => 1%object).

(* * ** Non-vacuity: the [n]-fold copower of [1] does not collapse / * ** 非空性：[1] 的 [n] 倍余幂不会塌缩 *)

Definition Sets_copower_pt {n : nat} (k : Fin.t n) :
  carrier (@copower Sets Sets_HasIndexedCoproducts (Fin.t n) 1%object) :=
  existT (fun _ : Fin.t n => poly_unit) k ttt.

Definition fin3_0 : Fin.t 3 := Fin.F1.
Definition fin3_1 : Fin.t 3 := Fin.FS Fin.F1.
Definition fin3_2 : Fin.t 3 := Fin.FS (Fin.FS Fin.F1).

Lemma Sets_copower_three_distinct :
  ((Sets_copower_pt fin3_0 ≈ Sets_copower_pt fin3_1) → False) *
  ((Sets_copower_pt fin3_1 ≈ Sets_copower_pt fin3_2) → False) *
  ((Sets_copower_pt fin3_0 ≈ Sets_copower_pt fin3_2) → False).
Proof.
  repeat split; intros [e _]; simpl in e.
  - discriminate.
  - apply Fin.FS_inj in e; discriminate.
  - discriminate.
Qed.
