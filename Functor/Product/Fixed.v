Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Binoidal.
Require Import Category.Structure.Monoidal.Cartesian.
Require Import Category.Structure.Premonoidal.Monoidal.
Require Import Category.Structure.ZeroObject.
Require Import Category.Construction.Product.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Product.Internal.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.

Generalizable All Variables.

(**
The fixed-factor product functor H × − and Mac Lane's induced
    transformation "f × id". 

--------
固定因子乘积函子 H × − 和 Mac Lane 的诱导
 变换“f × id”。 
*)

(*
nLab: https://ncatlab.org/nlab/show/natural+transformation
   nLab: https://ncatlab.org/nlab/show/product

   For a fixed object H of a cartesian category C, the assignment
   G ↦ H × G is a functor C ⟶ C: on a morphism g : G ~> G' it acts by
   [second g] : H × G ~> H × G', the identity on the fixed left factor and
   g on the moving right factor.  For a morphism f : H ~> K of fixed
   factors, the family whose component at G is [first f] : H × G ~> K × G
   is natural in G, the naturality square being exactly the interchange
   of [first] and [second].

   A word on the spelling of that component.  Mac Lane writes it
   "f × id".  This tree has no morphism-level × notation; the product of
   two morphisms is [split] (Structure/Cartesian.v), which is
   definitionally the action of the product bifunctor,
   [bimap[×(C)] f g] (Functor/Product/Internal.v).  So the literal
   in-tree reading of "f × id" is [split f id], and [first f] is that
   only up to ≈ — the identity survives inside the fork until [id_left]
   removes it, which is what [fixed_product_transform_bimap] below
   records.  The components below are [first f] because that is what
   issue #240's "Work to be done" prescribes verbatim ("components
   `first f` and naturality by `first_second`"); [alt_transform] carries
   the [split f id] spelling beside it, and [alt_transform_agrees]
   proves the two equal up to ≈.

   Provenance.  This is the exercise catalogued in this library's issue
   tracker as `maclane:I.4:ex2`, located there at Mac Lane, "Categories
   for the Working Mathematician", 2nd ed. (GTM 5), §I.4, printed p. 18,
   exercise 2, and reported there as posing the case C = Grp.  Both the
   location and the wording of the exercise are taken from that catalogue
   entry; the printed text was NOT consulted while writing this file, and
   nothing here is offered as a quotation from it.  What is machine-
   checked below is the mathematical content, in the generality of an
   arbitrary cartesian category, together with the instantiation at Grp
   that the exercise asks for. 

--------
nLab：https://ncatlab.org/nlab/show/natural+transformation
 nLab：https://ncatlab.org/nlab/show/product

对于笛卡尔类别 C 的固定对象 H，赋值
 G ↦ H × G 是一个函子 C ⟶ C：在态射 g : G ~> G' 上，它的作用是
 [second g] : H × G ~> H × G'，固定左因子上的恒等式和
 g 向右移动的因子。 对于固定的态射 f : H ~> K
 因子，G 处的组件为 [first f] 的族： H × G ~> K × G
 在 G 中是自然的，自然性平方正是交换
 [first] 和 [second]。

关于该组件的拼写的一个词。 麦克莱恩写的
 “f×id”。 这棵树没有态射级 × 表示法； 的产物
 两个态射是 [split] (Structure/Cartesian.v)，即
 定义上是乘积双函子的动作，
 [bimap[×(C)] f g]（函子/产品/内部.v）。 所以字面意思
 “f × id”的树内读取是 [split f id]，[first f] 是
 仅达到 ≈ — 身份在分叉内保留，直到 [id_left]
 删除它，这就是下面的[fixed_product_transform_bimap]
 记录。 下面的组件是 [first f]，因为这就是
 问题 #240 的“待完成的工作”逐字规定（“组件
 `first f` 和 `first_second` 的自然性"); [alt_transform] 携带
 旁边的 [split f id] 拼写，以及 [alt_transform_agrees]
 证明两者在 ≈ 之间相等。

出处。 这是本图书馆期刊中编录的练习
 跟踪器为 `maclane:I.4:ex2`，位于 Mac Lane，“类别
 为工作数学家”，第二版。 (GTM 5)，§I.4，印刷页。 18、
 练习 2，并报告为假设案例 C = Grp。 两者都
 练习的地点和措辞取自该目录
 进入； 编写此文件时未查阅印刷文本，并且
 这里没有提供任何内容作为其中的引用。 什么是机器-
 下面检查的是数学内容，一般而言
 任意笛卡尔类别，以及 Grp 的实例化
 练习要求的。 
*)

(*
What is reused, and what is new

   Nearly all the mathematical content of the exercise was already proven
   in this library, as equations about the cartesian combinators.  This
   file supplies the packaging.  The ledger:

   REUSED (nothing below re-derives these):
     - [second_id]     (Structure/Cartesian.v)  — the functor's
                        identity law, verbatim.
     - [second_comp]   (Structure/Cartesian.v)  — the functor's
                        composition law, verbatim.
     - [first_second]  (Structure/Cartesian.v)  — the naturality
                        square, verbatim.  [Transform] carries both
                        orientations as fields
                        (Theory/Natural/Transformation.v),
                        so the two obligations come out as
                        naturality := symmetry (first_second f g) and
                        naturality_sym := first_second f g, in that
                        order.
     - [first_id]      (Structure/Cartesian.v)  and
       [first_comp]    (Structure/Cartesian.v)  — the functor laws of
                        the mirror [fixed_product_functor_right], and
                        (together with [second_id]) the identity and
                        composition laws of the assignment f ↦ (f × −)
                        into [C, C].
     - [exl_first]     (Structure/Cartesian.v)  and [exl_fork]
                        (Structure/Cartesian.v) — the two cartesian
                        equations behind [fixed_product_transform_faithful],
                        used there alongside [comp_assoc] and [id_right].
     - [InternalProductFunctor] (Functor/Product/Internal.v) — the
                        product bifunctor, compared to this file's
                        functor by [fixed_product_bimap] and to its
                        transformation by [fixed_product_transform_bimap].
     - [Grp_Cartesian] (Instance/Grp.v) — binary direct products in
                        Grp.  These were already delivered by the Grp
                        work, so this file does NOT construct them; it
                        was checked before writing that Instance/Grp.v
                        is the only definition of that name in the tree
                        (the one other occurrence, Instance/Grp.v, is a
                        prose mention in that file's header) and that it
                        is an `#[export] Program Instance`, hence found
                        here by inference.
     - [Z2], [Z2_nontrivial], [Grp_injectivity_is_monic], [Grp_Zero]
                        (Instance/Grp.v) and [sections_are_monic]
                        (Theory/Morphisms.v) — the ingredients of the
                        non-vacuity witnesses.

   NEW here: the two packagings the exercise asks for
   ([fixed_product_functor], [fixed_product_transform]); the mirror
   functor − × K ([fixed_product_functor_right]); the [split f id]
   spelling of the same transformation and its agreement with the one
   above ([alt_transform], [alt_transform_agrees]); the currying
   ([fixed_product_curried]); the terminal-free [Cartesian_Binoidal] and
   the comparison against the binoidal composite the tree already
   reaches ([Section BinoidalComparison], including
   [alt_is_inj_left]/[alt_is_inj_right]); the non-degeneracy results
   ([fixed_product_transform_faithful],
   [fixed_product_transform_reflects_id]); and the Grp instantiation
   with its witnesses ([Grp_Z2_zero_not_iso],
   [Grp_fixed_product_transform_not_id],
   [Grp_fixed_product_component_moves],
   [Grp_fixed_product_component_not_monic]). 

--------
什么是重用的，什么是新的

练习中几乎所有的数学内容都已被证明
 在这个库中，作为有关笛卡尔组合器的方程。 这个
 文件提供包装。 账本：

重用（下面没有重新推导这些）：
 - [second_id] (Structure/Cartesian.v) — 函子的
 身份法，逐字逐句。 - [second_comp] (Structure/Cartesian.v) — 函子的
 逐字构成法。 - [first_second] (Structure/Cartesian.v) — 自然性
 方方正正，逐字逐句。 [Transform] 同时具备
 方向作为场
 （理论/自然/转化.v），
 所以这两项义务是
 自然性 := 对称性 (first_second f g) 和
 natureity_sym :=first_second f g，其中
 订单。
- [first_id]（结构/Cartesian.v）和
 [first_comp] (Structure/Cartesian.v) — 函子定律
 [fixed_product_functor_right] 镜子，以及
 （与 [second_id] 一起）身份和
 赋值的复合律 f ↦ (f × −)
 进入 [C, C]。 - [exl_first]（结构/Cartesian.v）和 [exl_fork]
 (Structure/Cartesian.v) — 两个笛卡尔
 [fixed_product_transform_faithful] 背后的方程式，
 与 [comp_assoc] 和 [id_right] 一起使用。 - [InternalProductFunctor] (Functor/Product/Internal.v) —
 乘积双函子，与此文件的相比
 [fixed_product_bimap] 的函子及其
 通过 [fixed_product_transform_bimap] 进行改造。
- [Grp_Cartesian] (Instance/Grp.v) — 二进制直接乘积
 组。 这些已经由 Grp 交付
 工作，所以这个文件不构造它们； 它
 在编写 Instance/Grp.v 之前进行了检查
 是树中该名称的唯一定义
 （另一个事件 Instance/Grp.v 是
 散文在该文件的标题中提到）并且它
 是一个`#[export]程序实例`，因此找到
 这里通过推论。 - [Z2]、[Z2_nontrivial]、[Grp_injectivity_is_monic]、[Grp_Zero]
 （实例/Grp.v）和 [sections_are_monic]
 (Theory/Morphisms.v) — 的成分
 非空证人。

新功能：练习要求的两种包装
 （[fixed_product_functor]、[fixed_product_transform]）； 镜子
 函子 − × K ([fixed_product_functor_right])； [split f id]
 相同变换的拼写及其与变换的一致性
 以上（[alt_transform]、[alt_transform_agrees]）； 柯里化
 （[fixed_product_curried]）； 无终端 [Cartesian_Binoidal] 和
 与二元复合树的比较已经
 达到（[Section BinoidalComparison]，包括
 XPTECT33X/[alt_is_inj_right]）； 非简并结果
 （[fixed_product_transform_faithful]，
 [fixed_product_transform_reflects_id]）； 和 Grp 实例化
 及其见证者（[Grp_Z2_zero_not_iso]，
 [Grp_fixed_product_transform_not_id]，
 [Grp_fixed_product_component_moves]，
 [Grp_fixed_product_component_not_monic]）。 
*)

(*
On [inj_left] / [inj_right] (Structure/Binoidal.v)

   These are the one-variable tensoring functors in the binoidal
   vocabulary, and they are the right abstraction for this exercise.
   They are FIELDS of the class [Binoidal], so using them needs a
   [Binoidal] structure in hand — and the tree already reaches one for
   cartesian categories by a two-step composite:

     [Cartesian_Monoidal] (Structure/Monoidal/Cartesian.v) makes a
     cartesian category THAT ALSO HAS A TERMINAL OBJECT monoidal, with
     tensor := [InternalProductFunctor] (via [CC_Monoidal],
     Structure/Monoidal/Internal/Product.v); and [Monoidal_Binoidal]
     (Structure/Premonoidal/Monoidal.v) makes any monoidal category
     binoidal.

   So this file does NOT claim [inj_right] was unavailable, and it does
   not claim to improve on it as a spelling of "f × id".  On that point
   the existing composite is the better match, and the difference runs
   the opposite way to what one might guess.  Since the product of two
   morphisms in this tree is [split] = [bimap[×(C)]] (see the header
   above), and the composite's tensor IS [InternalProductFunctor], the
   composite's morphism maps are the product of morphisms ON THE NOSE:

     fmap[@inj_left  C Cartesian_Monoidal_Binoidal G] f = split f id[G]
     fmap[@inj_right C Cartesian_Monoidal_Binoidal H] g = split id[H] g

   both by [eq_refl].  It is this file's [first f] and [second g] that
   match [split] only up to ≈ — precisely the content of
   [fixed_product_bimap] and [fixed_product_transform_bimap] below.

   [Section BinoidalComparison] states the comparison in that direction:
   [fixed_product_inj_right_obj] shows the object maps of the composite
   and of [fixed_product_functor] are equal by [reflexivity];
   [fixed_product_inj_right_fmap] shows the morphism maps agree up to ≈
   but not on the nose — the composite acts by
   [split id g] = (id ∘ exl) △ (g ∘ exr) whereas [second g] is
   exl △ (g ∘ exr); and [alt_is_inj_left] exhibits, by [reflexivity],
   that the component of [alt_transform] — the [split f id] spelling —
   IS the composite's action on f.  The mirror pair
   [fixed_product_inj_left_obj]/[fixed_product_inj_left_fmap] does the
   same for [inj_left].

   What the existing composite genuinely does not give, and the sole
   reason [Cartesian_Binoidal] is defined below, is the hypothesis
   count.  The composite requires a [Terminal] object to supply the
   monoidal unit, and this library's [Cartesian] class carries no
   terminal object (its fields are product_obj, fork, exl, exr,
   fork_respects, ump_products); the exercise needs none.
   [Cartesian_Binoidal] drops that hypothesis by assembling the
   [Binoidal] structure out of the two functors defined here.  Its two
   corollaries then read those functors back out — see the note at
   [Cartesian_Binoidal_inj_right] for what that does and does not
   establish. 

--------
关于 [inj_left] / [inj_right] (Structure/Binoidal.v)

这些是二元曲线中的单变量张量函子
 词汇，它们是本练习的正确抽象。 
它们是 [Binoidal] 类的字段，因此使用它们需要
 [Binoidal] 结构已在手 — 并且树已经达到一棵
 通过两步复合的笛卡尔类别：

[Cartesian_Monoidal] (Structure/Monoidal/Cartesian.v) 使
 笛卡尔类别也有一个终端对象幺半群，其中
 张量 := [InternalProductFunctor] （通过 [CC_Monoidal]，
 结构/单形/内部/产品.v); 和 [Monoidal_Binoidal]
 (Structure/Premonoidal/Monoidal.v) 生成任何幺半群范畴
 双曲线。

所以这个文件并没有声称 [inj_right] 不可用，它确实如此
 不声称将其改进为“f × id”的拼写。 关于这一点
 现有的复合材料是更好的匹配，并且差异运行
 与人们可能猜测的相反。 由于两个的乘积
 这棵树中的态射是 [split] = [bimap[×(C)]] （参见标题
 上面），复合材料的张量是 [InternalProductFunctor]，
 复合体的态射映射是鼻子上态射的乘积：

fmap[@inj_left  C Cartesian_Monoidal_Binoidal G] f = 分割 f id[G]
 fmap[@inj_right C Cartesian_Monoidal_Binoidal H] g = 分割 id[H] g

均由 [eq_refl] 提供。 正是这个文件的 [first f] 和 [second g]
 仅匹配 [split] 至 ≈ — 精确的内容
 下面是 [fixed_product_bimap] 和 [fixed_product_transform_bimap]。

[Section BinoidalComparison] 说明了该方向的比较：
 [fixed_product_inj_right_obj] 显示复合材料的对象图
 [fixed_product_functor] 的 和 与 [reflexivity] 相同；
 [fixed_product_inj_right_fmap] 显示态射图一致达到 ≈
 但不是在鼻子上——复合材料的作用是
 [split id g] = (id ∘ exl) △ (g ∘ exr) 而 [second g] 是
 exl △ (g ∘ exr); 和 [alt_is_inj_left] 展品，由 [reflexivity] 展示，
 [alt_transform] 的组成部分 — [split f id] 拼写 —
 是复合材料对 f 的作用。 镜子对
 [fixed_product_inj_left_obj]/[fixed_product_inj_left_fmap] 执行以下操作
 [inj_left] 也是如此。

现有的复合材料确实无法提供什么，而唯一的
 [Cartesian_Binoidal]定义如下的原因是假设
 计数。 该复合材料需要 [Terminal] 对象来提供
 幺半群单位，该库的 [Cartesian] 类不包含
 终端对象（其字段为product_obj、fork、exl、exr、
 fork_respects、ump_products）； 这项练习不需要任何东西。 
[Cartesian_Binoidal] 通过组装
 [Binoidal] 结构由此处定义的两个函子组成。 它的两个
 然后推论将这些函子读回来——请参阅注释
 [Cartesian_Binoidal_inj_right] 的作用和不作用
 建立。 
*)

(*
A note on layering.  This file ends in a Grp section and therefore
   imports Category.Instance.Grp, which is heavier than a Functor/ file
   usually needs.  The exercise is stated for groups and issue #240 asks
   for the instantiation alongside the general result, so the import is
   deliberate — but it is a genuinely new dependency, and the precedent
   for it is thinner than a bare appeal to "Functor/ files already
   import instances" would suggest.  Those precedents (Functor/Hom.v
   imports Instance/Fun.v and Instance/Sets.v; Functor/Diagonal.v
   imports Instance/Fun.v, Instance/One.v and Instance/Two/Discrete.v)
   are all foundational category instances that much of the tree already
   pulls in.  Instance/Grp.v is 1166 lines, and this is the only file in
   the tree that requires it. 

--------
关于分层的注意事项。 该文件以 Grp 部分结尾，因此
 导入 Category.Instance.Grp，它比 Functor/ 文件重
 通常需要。 该练习是针对团体进行的，问题 #240 提出
 为了与一般结果一起实例化，所以导入是
 故意的——但这确实是一种新的依赖关系，而且有先例
 因为它比单纯地呼吁“Functor/ 文件已经
 导入实例”会建议。 那些先例（Functor/Hom.v
 导入 Instance/Fun.v 和 Instance/Sets.v； 函子/Diagonal.v
 导入 Instance/Fun.v、Instance/One.v 和 Instance/Two/Discrete.v）
 都是树的大部分的基础类别实例
 Instance/Grp.v 有 1166 行，这是唯一的文件
 需要它的树。 
*)

Section FixedProduct.

Context {C : Category}.
Context `{CC : @Cartesian C}.

(** ** The functor H × −  / ** 函子 H × −*)

(*
Object map G ↦ H × G, morphism map g ↦ [second g].  The two functor
   laws are [second_id] and [second_comp] with no further argument. 

--------
对象映射 G ↦ H × G，态射映射 g ↦ [second g]。 两个函子
 定律是 [second_id] 和 [second_comp]，没有进一步的论证。 
*)
Program Definition fixed_product_functor (H : C) : C ⟶ C := {|
  fobj := fun G => H × G;
  fmap := fun _ _ g => second g
|}.
Next Obligation. apply second_id. Qed.
Next Obligation. apply second_comp. Qed.

(*
The mirror: fixed factor on the RIGHT, G ↦ G × K, acting by [first].
   It is not part of the exercise; it is here because the [Binoidal]
   structure below needs both one-variable tensorings. 

--------
镜子：右侧固定系数，G ↦ G × K，由 [first] 作用。 
这不是练习的一部分； 它在这里是因为 [Binoidal]
 下面的结构需要两个一变量张量。 
*)
Program Definition fixed_product_functor_right (K : C) : C ⟶ C := {|
  fobj := fun G => G × K;
  fmap := fun _ _ g => first g
|}.
Next Obligation. apply first_id. Qed.
Next Obligation. apply first_comp. Qed.

(*
Both actions are the advertised ones, definitionally.

   On the use of [=] rather than [≈] between morphisms here and in the
   other on-the-nose statements below ([fixed_product_first],
   [Cartesian_Binoidal_inj_right]/[_inj_left], the [_obj] comparisons,
   [alt_is_inj_left]/[alt_is_inj_right]): the whole point of those
   statements is that the two sides are the very same term, which [≈]
   would not say.  The convention is the tree's, recorded at
   [bimap_fmap] (Functor/Bifunctor.v, in the comment above it).  Every
   statement in this file that carries mathematical content — the
   naturality squares, the [bimap] comparisons, the faithfulness
   results, the Grp witnesses — uses [≈]. 

--------
从定义上讲，这两种操作都是广告中的操作。 

关于在此处和中的态射之间使用 [=] 而不是 [≈]
 下面的其他直观陈述（[fixed_product_first]、
 [Cartesian_Binoidal_inj_right]/[_inj_left]、[_obj] 比较、
 [alt_is_inj_left]/[alt_is_inj_right])：这些的全部意义
 声明是两侧是完全相同的术语，即 [≈]
 不会说。 约定是树的约定，记录于
 [bimap_fmap]（Functor/Bifunctor.v，在上面的评论中）。 每个
 该文件中包含数学内容的语句 -
 自然性方块、[bimap] 比较、忠实度
 结果，Grp 目击者 — 使用 [≈]。 
*)
Corollary fixed_product_fmap {H x y : C} (g : x ~> y) :
  fmap[fixed_product_functor H] g = second g.
Proof. reflexivity. Qed.

Corollary fixed_product_fmap_right {K x y : C} (g : x ~> y) :
  fmap[fixed_product_functor_right K] g = first g.
Proof. reflexivity. Qed.

(** ** The induced transformation H × − ⟹ K × −  / ** 诱导变换 H × − ⟹ K × −*)

(*
Components [first f]; naturality is [first_second], whose symmetry
   discharges [naturality] and whose direct form discharges
   [naturality_sym] (that field order is the one
   Theory/Natural/Transformation.v declares — the obligations come out in
   that order, so obligation 1 is the symmetric one). 

--------
组件 XPTECT0X； 自然性是 [first_second]，其对称性
 放电 [naturality] 且其直接形式放电
 [naturality_sym]（场序是
 Theory/Natural/Transformation.v 声明 — 义务出现在
 该顺序，因此义务 1 是对称的）。 
*)
Program Definition fixed_product_transform {H K : C} (f : H ~> K) :
  fixed_product_functor H ⟹ fixed_product_functor K := {|
  transform := fun _ => first f
|}.
Next Obligation. symmetry; apply first_second. Qed.
Next Obligation. apply first_second. Qed.

Corollary fixed_product_first {H K : C} (f : H ~> K) (G : C) :
  transform[fixed_product_transform f] G = first f.
Proof. reflexivity. Qed.

(** ** Agreement with the product bifunctor  / ** 与产品双函子达成协议*)

(*
[InternalProductFunctor] sends (f, g) to (f ∘ exl) △ (g ∘ exr).  Both
   actions above are that bifunctor with one argument held at an
   identity — up to ≈, not up to =, since the identity survives inside
   the fork (as `id ∘ exl` against [second], as `id ∘ exr` against
   [first]) until [id_left] removes it. 

--------
[InternalProductFunctor] 将 (f, g) 发送到 (f ∘ exl) △ (g ∘ exr)。 两者都
 上述动作是具有一个参数的双函子
 恒等式 — 直到 ≈，而不是 =，因为恒等式在内部存在
 分叉（如针对 [second] 的 `id ∘ exl`，如针对 [second] 的 `id ∘ exr`
 [first]) 直到 [id_left] 将其删除。 
*)
Theorem fixed_product_bimap {H x y : C} (g : x ~> y) :
  fmap[fixed_product_functor H] g ≈ bimap[×(C)] (id[H]) g.
Proof.
  simpl; unfold second.
  now rewrite id_left.
Qed.

Theorem fixed_product_transform_bimap {H K : C} (f : H ~> K) (G : C) :
  transform[fixed_product_transform f] G ≈ bimap[×(C)] f (id[G]).
Proof.
  simpl; unfold first.
  now rewrite id_left.
Qed.

(** ** The same transformation with its component spelled [split f id]  / ** 相同的转换，其组件拼写为 [split f id]*)

(*
The literal in-tree reading of Mac Lane's "f × id" (see the header):
   [split f id], which is [bimap[×(C)] f id] definitionally.  Both
   naturality obligations fall to [unfork] with nothing else.  This is
   here so that the comparison against the binoidal composite the tree
   already reaches is a checkable fact rather than a remark — see
   [alt_is_inj_left] in [Section BinoidalComparison]. 

--------
Mac Lane 的“f × id”的字面树内读取（参见标题）：
 [split f id]，其定义为 [bimap[×(C)] f id]。 两者都
 自然性义务仅由 [unfork] 承担。 这是
 在这里与二元复合树进行比较
 已经达到是一个可检查的事实而不是一个评论 - 请参阅
 [Section BinoidalComparison] 中的 [alt_is_inj_left]。 
*)
Program Definition alt_transform {H K : C} (f : H ~> K) :
  fixed_product_functor H ⟹ fixed_product_functor K := {|
  transform := fun G => split f (id[G])
|}.
Next Obligation. unfork. Qed.
Next Obligation. unfork. Qed.

(*
The two spellings agree up to ≈, and not more than that: [first f] is
   (f ∘ exl) △ exr while [split f id] is (f ∘ exl) △ (id ∘ exr), and no
   conversion removes that [id ∘ −] — it takes [id_left]. 

--------
这两种拼写一致到 ≈，但不会超过这个值：[first f] 是
 (f ∘ exl) △ exr 而 [split f id] 是 (f ∘ exl) △ (id ∘ exr)，并且没有
 转换删除了 [id ∘ −] — 它需要 [id_left]。 
*)
Theorem alt_transform_agrees {H K : C} (f : H ~> K) :
  alt_transform f ≈ fixed_product_transform f.
Proof.
  intro G; simpl.
  symmetry.
  apply (fixed_product_transform_bimap f G).
Qed.

(** ** A terminal-free binoidal structure on any cartesian category  / ** 任何笛卡尔范畴上的无终结二元结构*)

(*
Assembled from the two functors above.  Kept a [Definition] rather
   than an [Instance], following [Cartesian_Monoidal]
   (Structure/Monoidal/Cartesian.v, whose header gives the reason), so
   that it cannot silently capture [Binoidal] resolution elsewhere. 

--------
由上面的两个函子组装而成。 保留了 [Definition] 而不是
 比 [Instance] 跟随 [Cartesian_Monoidal]
 （Structure/Monoidal/Cartesian.v，其标题给出了原因），所以
 它无法在其他地方默默地捕获 [Binoidal] 分辨率。 
*)
Definition Cartesian_Binoidal : @Binoidal C :=
  @Build_Binoidal C
    (fun x y => x × y)
    (fun K => ToAFunctor (fixed_product_functor_right K))
    (fun H => ToAFunctor (fixed_product_functor H)).

(*
Reading the two functors back out of the structure just built.  Note
   what this is and is not.  [inj_right x'] is DEFINED as
   [FromAFunctor (right_functor x')] (Structure/Binoidal.v), and
   [Cartesian_Binoidal] supplied [right_functor] as
   [ToAFunctor (fixed_product_functor H)]; so these two corollaries are
   instances of [FromAFunctor_ToAFunctor] (Theory/Functor.v), which
   holds of every functor whatsoever.  They confirm that the packaging
   round-trips — nothing about products, and nothing specific to this
   exercise, is being established here. 

--------
从刚刚构建的结构中读回两个函子。 注意事项
 这是什么，不是什么。 [inj_right x'] 定义为
 [FromAFunctor (right_functor x')]（结构/Binoidal.v），以及
 [Cartesian_Binoidal] 提供 [right_functor] 作为
 [ToAFunctor (fixed_product_functor H)]； 所以这两个推论是
 [FromAFunctor_ToAFunctor] (Theory/Functor.v) 的实例，其中
 任何函子都成立。 他们确认包装
 往返——与产品无关，也没有任何具体内容
 锻炼，正在这里建立。 
*)
Corollary Cartesian_Binoidal_inj_right (H : C) :
  @inj_right C Cartesian_Binoidal H = fixed_product_functor H.
Proof. reflexivity. Qed.

Corollary Cartesian_Binoidal_inj_left (K : C) :
  @inj_left C Cartesian_Binoidal K = fixed_product_functor_right K.
Proof. reflexivity. Qed.

(** ** Non-degeneracy: distinct f give distinct transformations  / ** 非简并性：不同的 f 给出不同的变换*)

(*
The assignment f ↦ (f × −) is injective on hom-setoids.  The proof
   needs no terminal object: probe the component at G := H with the
   diagonal id △ id, which [exl_fork] splits.  So the transformation
   below can never be accidentally trivial — it remembers f exactly. 

--------
赋值 f ↦ (f × −) 在 hom-setoids 上是内射的。 证明
 不需要终端对象：用以下命令探测 G := H 处的组件
 对角线 id △ id，由 [exl_fork] 分割。 所以转型
 下面永远不会是偶然的琐碎——它准确地记住了 f。 
*)
Theorem fixed_product_transform_faithful {H K : C} (f g : H ~> K) :
  fixed_product_transform f ≈ fixed_product_transform g → f ≈ g.
Proof.
  intro Heq.
  assert (Hprobe : ∀ h : H ~> K, h ≈ (exl ∘ first (z:=H) h) ∘ (id △ id)).
  { intro h.
    rewrite exl_first.
    rewrite <- comp_assoc.
    rewrite exl_fork.
    now rewrite id_right. }
  rewrite (Hprobe f), (Hprobe g).
  now rewrite (Heq H).
Qed.

(*
Hence the induced transformation is the identity transformation only
   when f itself is an identity: no unlucky choice of f can produce a
   degenerate witness. 

--------
因此，诱导变换只是恒等变换
 当 f 本身是一个恒等式时：f 的任何不幸选择都不能产生
 堕落的证人。 
*)
Corollary fixed_product_transform_reflects_id {H : C} (f : H ~> H) :
  fixed_product_transform f ≈ nat_id → f ≈ id.
Proof.
  intro Heq.
  apply fixed_product_transform_faithful.
  intro G.
  rewrite (Heq G).
  simpl.
  now rewrite first_id, second_id.
Qed.

(** ** Functoriality in the fixed factor  / ** 固定因子的函数性*)

Theorem fixed_product_transform_id {H : C} :
  fixed_product_transform (id[H]) ≈ nat_id.
Proof.
  intro G; simpl.
  now rewrite first_id, second_id.
Qed.

Theorem fixed_product_transform_comp {H K L : C} (f : K ~> L) (g : H ~> K) :
  fixed_product_transform (f ∘ g)
    ≈ nat_compose (fixed_product_transform f) (fixed_product_transform g).
Proof.
  intro G; simpl.
  apply first_comp.
Qed.

(*
Packaging both: H ↦ (H × −) and f ↦ (f × −) form a functor into the
   functor category — the product bifunctor curried in its first
   argument.  It agrees pointwise up to ≈ with currying
   [InternalProductFunctor] in both halves: on objects (that is, on each
   functor's action on morphisms) by [fixed_product_bimap], and on
   morphisms (that is, on each transformation's components) by
   [fixed_product_transform_bimap].  It is not claimed equal to that
   currying on the nose. 

--------
将 H ↦ (H × −) 和 f ↦ (f × −) 打包为函子
 函子类别——第一个柯里化的产品双函子
 论点。 它与柯里化在点上一致到 ≈
 两半中的 [InternalProductFunctor]：在对象上（即在每个
 函子对态射的作用）由 [fixed_product_bimap] 提供，以及
 态射（即，在每个变换的分量上）
 [fixed_product_transform_bimap]。 据称不等于
 咖喱在鼻子上。 
*)
Program Definition fixed_product_curried : C ⟶ [C, C] := {|
  fobj := fixed_product_functor;
  fmap := fun _ _ f => fixed_product_transform f
|}.
Next Obligation.
  intros f g Hfg G; simpl.
  now rewrite Hfg.
Qed.
Next Obligation. apply fixed_product_transform_id. Qed.
Next Obligation. apply fixed_product_transform_comp. Qed.

End FixedProduct.

(** ** Comparison with the binoidal structure the tree already reaches  / ** 与树已经达到的二元结构进行比较*)

(*
With a terminal object the tree already composes its way to a
   [Binoidal] structure on a cartesian category, as described in the
   header.  These statements pin down exactly how that composite relates
   to this file's functors: same objects on the nose, same morphism
   action only up to ≈ — and, in [alt_is_inj_left]/[alt_is_inj_right],
   the composite's morphism action IS the product of morphisms, [split],
   on the nose. 

--------
有了终端对象，树就已经组成了一个
 笛卡尔类别上的 [Binoidal] 结构，如中所述
 标头。 这些陈述准确地说明了复合材料如何关联
 到该文件的函子：鼻子上的相同对象，相同的态射
 作用仅达到 ≈ — 并且，在 [alt_is_inj_left]/[alt_is_inj_right] 中，
 复合材料的态射作用是态射的产物，[split]，
 在鼻子上。 
*)

Section BinoidalComparison.

Context {C : Category}.
Context `{CC : @Cartesian C}.
Context `{T : @Terminal C}.

Definition Cartesian_Monoidal_Binoidal : @Binoidal C :=
  @Monoidal_Binoidal C (@Cartesian_Monoidal C CC T).

Corollary fixed_product_inj_right_obj (H G : C) :
  (@inj_right C Cartesian_Monoidal_Binoidal H) G = fixed_product_functor H G.
Proof. reflexivity. Qed.

Theorem fixed_product_inj_right_fmap (H : C) {x y : C} (g : x ~> y) :
  fmap[@inj_right C Cartesian_Monoidal_Binoidal H] g
    ≈ fmap[fixed_product_functor H] g.
Proof.
  simpl; unfold second.
  now rewrite id_left.
Qed.

Corollary fixed_product_inj_left_obj (K G : C) :
  (@inj_left C Cartesian_Monoidal_Binoidal K) G
    = fixed_product_functor_right K G.
Proof. reflexivity. Qed.

Theorem fixed_product_inj_left_fmap (K : C) {x y : C} (g : x ~> y) :
  fmap[@inj_left C Cartesian_Monoidal_Binoidal K] g
    ≈ fmap[fixed_product_functor_right K] g.
Proof.
  simpl; unfold first.
  now rewrite id_left.
Qed.

(*
The direction the header insists on: on the "f × id" spelling the
   pre-existing composite is exact, not approximate.  The component of
   [alt_transform] at G IS the composite's action on f, by
   [reflexivity]; [alt_transform_agrees] then relates that to this
   file's [first]-valued transformation, up to ≈. 

--------
标头坚持的方向：在“f × id”上拼写
 预先存在的复合材料是精确的，而不是近似的。 的组成部分
 [alt_transform] at G 是复合材料对 f 的作用，通过
 [reflexivity]； [alt_transform_agrees] 然后将其与此相关联
 文件的 [first] 值转换，最高可达 ≈。 
*)
Corollary alt_is_inj_left {H K : C} (f : H ~> K) (G : C) :
  transform[alt_transform f] G
    = fmap[@inj_left C Cartesian_Monoidal_Binoidal G] f.
Proof. reflexivity. Qed.

Corollary alt_is_inj_right (H : C) {x y : C} (g : x ~> y) :
  split (id[H]) g = fmap[@inj_right C Cartesian_Monoidal_Binoidal H] g.
Proof. reflexivity. Qed.

End BinoidalComparison.

(** ** The exercise's own setting: C = Grp  / ** 练习自己的设置：C = Grp*)

(*
[Grp_Cartesian] (Instance/Grp.v) already supplies the binary
   direct products, so the instantiation is a specialization and nothing
   more. 

--------
[Grp_Cartesian]（Instance/Grp.v）已经提供了二进制文件
 直接产品，所以实例化是一种专业化，没有什么
 更多。 
*)

Definition Grp_fixed_product (H : Grp) : Grp ⟶ Grp :=
  fixed_product_functor H.

Definition Grp_fixed_product_transform {H K : Grp} (f : H ~{Grp}~> K) :
  Grp_fixed_product H ⟹ Grp_fixed_product K :=
  fixed_product_transform f.

(* The object map is the direct product G ↦ H × G on the nose.  / 物体贴图是鼻子上的直积 G ↦ H × G。*)
Corollary Grp_fixed_product_obj (H G : Grp) :
  Grp_fixed_product H G = Grp_product H G.
Proof. reflexivity. Qed.

(** ** Non-vacuity  / ** 非空性*)

(*
A degenerate witness would show nothing, so the witness is chosen to
   dodge every degeneracy at once.  Take H = K = Z/2 and for f the zero
   homomorphism through the zero object [Grp_Zero], which sends both
   elements of Z/2 to the unit `false`.  Then:

     - f has no left inverse at all ([Grp_Z2_zero_no_left_inverse],
       through [Grp_Z2_zero_not_section] and [Grp_Z2_zero_not_monic]),
       hence is not an isomorphism ([Grp_Z2_zero_not_iso], which is that
       lemma applied to the inverse's left-inverse law);
     - the induced transformation is not the identity transformation
       ([Grp_fixed_product_transform_not_id]).  H = K is what makes that
       statement available at all: [nat_id] inhabits F ⟹ F, so for
       H ≠ K a comparison of the induced transformation with [nat_id]
       does not typecheck (the two sides live in
       Grp_fixed_product H ⟹ Grp_fixed_product K and
       Grp_fixed_product H ⟹ Grp_fixed_product H, which do not unify).
       It is therefore not a claim that would hold for type reasons; it
       is not a claim.  With H = K the two functors are the same term
       and the comparison against [nat_id] is a genuine one;
     - its component at Z/2 genuinely moves an element
       ([Grp_fixed_product_component_moves]) and is not monic
       ([Grp_fixed_product_component_not_monic]), so the transformation
       is not invertible either. 

--------
堕落的证人不会表现出任何东西，因此证人被选择
 立即避免一切堕落。 取 H = K = Z/2 并且 f 为零
 通过零对象 [Grp_Zero] 实现同态，它发送两者
 Z/2 的元素到单位“false”。 然后：

- f 根本没有左逆 ([Grp_Z2_zero_no_left_inverse],
 通过 [Grp_Z2_zero_not_section] 和 [Grp_Z2_zero_not_monic]），
 因此不是同构（[Grp_Z2_zero_not_iso]，即
 引理应用于逆的左逆定律）；
 - 诱导变换不是身份变换
 ([Grp_fixed_product_transform_not_id])。 H = K 就是这样的
 完全可用的陈述：[nat_id] 位于 F ⟹ F，所以对于
 H ≠ K 与 [nat_id] 诱导转化的比较
 不进行类型检查（双方居住在
 Grp_fixed_product H ⟹ Grp_fixed_product K 和
 Grp_fixed_product H ⟹ Grp_fixed_product H，不统一）。 
因此，由于类型原因，该主张不成立； 它
 不是一个主张。 当 H = K 时，两个函子是同一项
 与 [nat_id] 的对比是真实的；
 - Z/2 处的组件真正移动了一个元素
 ([Grp_fixed_product_component_moves]) 并且不是莫尼克
 ([Grp_fixed_product_component_not_monic])，所以变换
 也不是可逆的。 
*)

Definition Grp_Z2_zero : Z2 ~{Grp}~> Z2 := @zero_mor Grp Grp_Zero Z2 Z2.

(* The zero homomorphism collapses Z/2 onto its unit.  / 零同态将 Z/2 折叠到它的单位上。*)
Lemma Grp_Z2_zero_const (b : carrier Z2) : grp_map Grp_Z2_zero b ≈ false.
Proof. reflexivity. Qed.

Lemma Grp_Z2_zero_not_injective :
  (∀ a b : carrier Z2, grp_map Grp_Z2_zero a ≈ grp_map Grp_Z2_zero b → a ≈ b)
    → False.
Proof.
  intro Hinj.
  apply Z2_nontrivial.
  apply Hinj.
  reflexivity.
Qed.

Theorem Grp_Z2_zero_not_monic : Monic Grp_Z2_zero → False.
Proof.
  intro Hm.
  apply Grp_Z2_zero_not_injective.
  destruct (Grp_injectivity_is_monic Grp_Z2_zero) as [_ Hback].
  exact (Hback Hm).
Qed.

(* Not split monic, by [sections_are_monic].  / 未拆分莫尼克，由 [sections_are_monic] 提供。*)
Theorem Grp_Z2_zero_not_section : Section Grp_Z2_zero → False.
Proof.
  intro Hs.
  apply Grp_Z2_zero_not_monic.
  now apply sections_are_monic.
Qed.

(* Hence no left inverse.  / 因此没有左逆。*)
Theorem Grp_Z2_zero_no_left_inverse (g : Z2 ~{Grp}~> Z2) :
  g ∘ Grp_Z2_zero ≈ id → False.
Proof.
  intro Hg.
  apply Grp_Z2_zero_not_section.
  now refine {| section := g |}.
Qed.

(*
And hence not an isomorphism: a two-sided inverse is in particular a
   left inverse.  Stated at the [IsIsomorphism] level (the predicate form
   on a single morphism, Theory/Isomorphism.v) so that the prose
   above has a theorem behind it rather than an inference left to the
   reader. 

--------
因此不是同构：双边逆尤其是
 左逆。 在 [IsIsomorphism] 级别声明（谓词形式
 在单一态射上，Theory/Isomorphism.v) 使得散文
 上面有一个定理，而不是留给下面的推论
 读者。 
*)
Theorem Grp_Z2_zero_not_iso : IsIsomorphism Grp_Z2_zero → False.
Proof.
  intro Hi.
  exact (Grp_Z2_zero_no_left_inverse
           (@two_sided_inverse Grp Z2 Z2 Grp_Z2_zero Hi)
           (@is_left_inverse Grp Z2 Z2 Grp_Z2_zero Hi)).
Qed.

(*
The component at Z/2 sends (true, true) to (false, true): it moves the
   fixed factor and leaves the moving factor alone. 

--------
Z/2 处的组件将 (true, true) 发送到 (false, true)：它移动
 固定因子并保留移动因子。 
*)
Example Grp_fixed_product_moves :
  grp_map (transform[Grp_fixed_product_transform Grp_Z2_zero] Z2) (true, true)
    ≈ (false, true).
Proof. split; reflexivity. Qed.

(* And (true, true) is not (false, true).  / 并且（真，真）不是（假，真）。*)
Lemma Grp_Z2_pair_distinct :
  (@equiv _ (grp_setoid (Grp_product Z2 Z2)) (true, true) (false, true))
    → False.
Proof. intros [Hl _]; discriminate. Qed.

(* Put together: the component really does move (true, true).  / 放在一起：该组件确实移动（true，true）。*)
Theorem Grp_fixed_product_component_moves :
  grp_map (transform[Grp_fixed_product_transform Grp_Z2_zero] Z2) (true, true)
    ≈ (true, true) → False.
Proof.
  intro Hfix.
  apply Grp_Z2_pair_distinct.
  rewrite <- Hfix.
  exact Grp_fixed_product_moves.
Qed.

Theorem Grp_fixed_product_transform_not_id :
  Grp_fixed_product_transform Grp_Z2_zero ≈ nat_id → False.
Proof.
  intro Heq.
  apply Z2_nontrivial.
  symmetry.
  exact (fixed_product_transform_reflects_id Grp_Z2_zero Heq true).
Qed.

(*
The component identifies (true, true) with (false, true), so it is not
   injective, hence not monic, hence not invertible. 

--------
该组件将 (true, true) 标识为 (false, true)，因此它不是
 单射，因此不是单子，因此不可逆。 
*)
Theorem Grp_fixed_product_component_not_monic :
  Monic (transform[Grp_fixed_product_transform Grp_Z2_zero] Z2) → False.
Proof.
  intro Hm.
  apply Grp_Z2_pair_distinct.
  destruct (Grp_injectivity_is_monic
              (transform[Grp_fixed_product_transform Grp_Z2_zero] Z2))
    as [_ Hback].
  apply (Hback Hm).
  split; reflexivity.
Qed.
