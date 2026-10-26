Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Kan extensions / * Kan 扩张 *)

(*
nLab: https://ncatlab.org/nlab/show/Kan+extension
   Wikipedia: https://en.wikipedia.org/wiki/Kan_extension

   Given a functor F : A ⟶ B, precomposition with F induces the restriction
   functor Induced := (− ◯ F) : [B, C] ⟶ [A, C]. The Kan extensions along F
   are its adjoints, when they exist: the left Kan extension Lan is the LEFT
   adjoint to Induced (Lan ⊣ Induced), and the right Kan extension Ran is the
   RIGHT adjoint to Induced (Induced ⊣ Ran). Equivalently, by the hom-set
   adjunctions, [A,C](X, M ◯ F) ≅ [B,C](Lan X, M) naturally in M, and
   [A,C](M ◯ F, X) ≅ [B,C](M, Ran X) naturally in M.

   These are the GLOBAL Kan extensions (the adjoint functors). The LOCAL Kan
   extension of a single functor X : A ⟶ C can exist even when the global
   adjoint does not; it is the universal pair given by a unit X ⟹ LocalLan ◯ F
   (left, initial) or a counit LocalRan ◯ F ⟹ X (right, terminal). When C' = 1
   the left/right Kan extensions specialise to colimits/limits of X. The
   slogan “all concepts are Kan extensions” (Mac Lane) records that limits,
   colimits, adjoints, ends, and coends are all instances.

--------
nLab：https://ncatlab.org/nlab/show/Kan+extension
维基百科：https://en.wikipedia.org/wiki/Kan_extension

给定一个函子 F : A ⟶ B，与 F 的复合诱导出限制函子 Induced := (− ◯ F) : [B, C] ⟶ [A, C]。沿 F 的 Kan 扩展是它的伴随，当它们存在时：左 Kan 扩展 Lan 是 Induced 的左伴随（Lan ⊣ Induced），右 Kan 扩展 Ran 是 Induced 的右伴随（Induced ⊣ Ran）。等价地，通过 Hom 集的伴随关系，[A,C](X, M ◯ F) ≅ [B,C](Lan X, M)，并且 [A,C](M ◯ F, X) ≅ [B,C](M, Ran X)，这在 M 中是自然的。

这些是全局 Kan 扩张（伴随）。单个函子 X : A ⟶ C 的局部 Kan 扩张即使在全局伴随不存在时也可以存在；它是由一个单位 X ⟹ LocalLan ◯ F（左、初始）或一个余单位 LocalRan ◯ F ⟹ X（右、终结）给出的普遍对。当 C' = 1 时，左/右 Kan 扩张特殊化为 X 的余极限/极限。口号“所有概念都是 Kan 扩张”（Mac Lane）指出，极限、余极限、伴随、端、余端都是其实例。
*)

(*
Where Kan extensions come from, and what they are for

   nLab:  https://ncatlab.org/nlab/show/codensity+monad
   nLab:  https://ncatlab.org/nlab/show/nerve+and+realization
   Paper: Kan, “Adjoint functors”, Transactions of the American
          Mathematical Society 87, 1958
   Paper: Leinster, “Codensity and the ultrafilter monad”, Theory and
          Applications of Categories 28, 2013
   Paper: Hinze, “Kan Extensions for Program Optimisation — Or: Art and
          Dan Explain an Old Trick”, MPC 2012

   Adjoint functors and Kan extensions entered mathematics in the same
   paper.  Daniel Kan, after whom Kan complexes and Kan fibrations are
   named, wrote “Adjoint functors” (1958) to codify the formal
   properties of the passage between spaces and simplicial sets; the
   memorial note of Barwick, Hopkins, Miller and Moerdijk (“Daniel M.
   Kan (1927–2013)”) records that Eilenberg insisted on the name
   “adjoint”, that the same paper defines limits, colimits, and what
   are now called Kan extensions, and that Mac Lane's dictum is “only a
   mild exaggeration”.  The word “extension” is homotopical in origin:
   Kan had defined homotopy groups of cubical sets by extending maps
   from the boundary of a cube minus one face, the extension condition
   now named after him.  Mac Lane devotes Chapter X of Categories for
   the Working Mathematician to the concept, with §X.7 titled “All
   Concepts Are Kan Extensions”; Riehl titles Chapter 6 of Category
   Theory in Context (2016) the same way; the Lehner thesis quoted
   later in this file works that program out in detail.

   The problem the definitions answer is extension along a change of
   index: given X : A ⟶ C and F : A ⟶ B, produce the functor B ⟶ C
   that best extends X through F, “best” splitting into a free (left,
   initial) and a cofree (right, terminal) answer.  Because the global
   forms are the two adjoints of [Induced], a Kan extension is an
   adjunction one level up, and the slogan becomes a theorem schedule.
   The header's specialization to (co)limits is realized in-tree by
   [Kan_Limit] in Structure/Limit/Kan/Extension.v — a limit is a right
   Kan extension along the functor erasing the diagram shape — and a
   functor has a left adjoint precisely when the right Kan extension of
   the identity along it exists and is preserved by it (Wikipedia, “Kan
   extension”), the adjoint functor theorem of Lehner's thesis and the
   reason [preserves_left_Kan], [preserves_right_Kan] and
   [left_adjoint_impl] appear below.  Pointwise, the left extension at
   b is a colimit over the comma category F ↓ b and the right a limit
   over b ↓ F, equivalently Kelly's coend and end formulas (nLab, “Kan
   extension”).  The comma-category formulas are formalized in
   Structure/Limit/Kan/Pointwise.v ([Pointwise_LocalRightKan] and
   [Pointwise_LocalLeftKan], inhabiting the local classes below from
   per-object comma (co)limits); the coend calculus of Structure/Coend.v
   and Instance/Sets/{End,Coend}.v is the in-tree machinery the
   COEND/END formulas would rest on, the half of the bridge still not
   formalized.

   Much of the utility lies where adjoints do not exist.  The right Kan
   extension of a functor G along itself is always a monad — the
   codensity monad, Mac Lane's Exercise X.7.3 — the monad G induces
   even in the absence of a left adjoint, measuring how far G is from
   being codense (nLab, “codensity monad”).  For the inclusion of
   finite sets into sets it is the ultrafilter monad (Kennison,
   Gildenhuys, “Equational completion, model induced triples and
   pro-objects”, JPAA 1, 1971), a result Leinster revived, adding that
   for finite-dimensional vector spaces in all vector spaces it is
   double dualization.  Geometric realization is the left Kan extension
   of a cosimplicial space along the Yoneda embedding, the nerve its
   restricted-Yoneda right adjoint — already §3 of Kan's companion
   paper “Functors involving c.s.s. complexes” (1958; nLab, “nerve and
   realization”) — and total derived functors are Kan extensions along
   localization at the weak equivalences (Riehl, Category Theory in
   Context, §6.4).  In-tree, Construction/Day.v exhibits Day
   convolution as the left Kan extension of the external tensor of two
   presheaves along the tensor of the base.

   The computational reading is continuation-passing style.  Hinze (MPC
   2012) states it directly: continuations implement a right Kan
   extension — the end formula is the rank-2 type of a CPS computation,
   and the codensity monad the case where answer types live under the
   extended functor itself.  Re-representing a free-monad program in
   its codensity monad right-associates its binds and can improve
   quadratic running time to linear (Voigtländer, “Asymptotic
   Improvement of Computations over Free Monads”, MPC 2008); Kmett's
   kan-extensions Haskell package ships Ran, Lan, Yoneda and Codensity
   in this rank-2 form.  This file proves against what Hinze calls the
   specification — the adjunctions [ran_adjoint] and [lan_adjoint] —
   rather than those rank-2 implementations.

--------
Kan 扩展从何而来以及它们的用途

nLab：https://ncatlab.org/nlab/show/codensity+monad
 nLab：https://ncatlab.org/nlab/show/nerve+and+realization
 论文：Kan，“伴随”，美国汇刊
 数学会 87, 1958
 论文：伦斯特，“Co密度和超滤单子”，理论和
 范畴28的应用，2013
 论文：Hinze，“程序优化的 Kan 扩展 — 或者：艺术与
 Dan 解释一个老把戏”，MPC 2012

伴随和 Kan 扩展同时进入数学领域
 纸。 Daniel Kan，Kan 复合体和 Kan 纤维是在他之后命名的
 命名，写了“伴随”（1958）来编纂正式的
 空间和单纯集之间的通道的性质； 的
 巴威克、霍普金斯、米勒和莫尔迪克的纪念笔记（“丹尼尔·M.
 Kan（1927-2013）”）记录了艾伦伯格坚持使用这个名字
 “伴随”，同一篇论文定义了极限、余极限以及什么
 现在被称为 Kan 扩展，Mac Lane 的格言是“仅
 轻微夸张”。 “扩展”这个词在起源上是同伦的：
 Kan通过扩展映射定义了立方集的同伦群
 从立方体的边界减去一个面，扩展条件
 现在以他的名字命名。 Mac Lane 致力于范畴的第十章
 工作数学家对这个概念的理解，§X.7 标题为“所有
 概念是 Kan 的延伸”； Riehl 标题范畴第 6 章
 语境理论（2016）同样的方式； 引用的莱纳论文
 该文件稍后将详细介绍该程序。

定义回答的问题是沿着变化延伸
 索引：给定 X : A ⟶ C 和 F : A ⟶ B，生成函子 B ⟶ C
 最好地将 X 延伸到 F，“最佳”分裂成一个自由的（左，
 初始）和一个 cofree （正确，终端）答案。 因为全球
 形式是 [Induced] 的两个伴随，Kan 扩展是
 附加物上升一级，口号就变成了定理表。 标头对（共同）限制的专门化是通过以下方式在树中实现的
 Structure/Limit/Kan/Extension.v 中的 [Kan_Limit] — 限制就是权利
 Kan 沿着函子延伸，擦除图表形状——以及
 当函子的右 Kan 延拓恰好有左伴随时
 沿着它的恒等存在并被它保存（维基百科，“Kan
 扩展”），Lehner 论文的伴随定理和
 原因 [preserves_left_Kan]、[preserves_right_Kan] 和
 [left_adjoint_impl] 如下所示。
逐点地，左延伸位于
 b 是逗号范畴 F ↓ b 和右侧 a 极限上的上界
 b ↓ F 上，等价于 Kelly 的 coend 和 end 公式 (nLab, “Kan
 扩展”）。 逗号范畴公式形式化为
 Structure/Limit/Kan/Pointwise.v（[Pointwise_LocalRightKan] 和
 [Pointwise_LocalLeftKan]，居住在下面的本地类中
 每个对象逗号（co）限制）； Structure/Coend.v 的共端演算
 Instance/Sets/{End,Coend}.v 是树内机制
 COEND/END 公式将继续存在，桥的一半仍然没有
 正式化。

大部分实用性在于不存在伴随物的地方。 右坎
 函子 G 沿其自身的扩展始终是一个单子——
 co密度 monad，Mac Lane 的练习 X.7.3 — monad G 诱导
 即使没有左伴随，测量 G 距离
 是代码密集的（nLab，“代码密度单子”）。 为了纳入
 将有限集转化为集合，这就是超滤单子（Kennison，
 Gildenhuys，“方程完成、模型导出的三元组和
 支持对象”，JPAA 1, 1971），伦斯特复兴了这一结果，并补充说
 对于所有向量空间中的有限维向量空间，它是
 双二元化。 几何实现是左Kan延伸
 沿着米田嵌入的共形空间，神经是
 限制-米田右伴随 — 已经是 Kan 伴生的 §3
 论文“函子涉及 c.s.s.
复合体”（1958 年；nLab，“神经和
 实现”）——并且总导出函子是 Kan 扩展
 弱等价的本地化（Riehl，范畴论
 上下文，第 6.4 节）。 In-tree，Construction/Day.v 展示 Day
 卷积作为两个外部张量的左 Kan 扩展
 沿着底座张量预滑。

计算阅读是连续传递的风格。 欣泽 (MPC
 2012）直接指出：延续实现了正确的 Kan
 扩展 — 最终公式是 CPS 计算的 2 阶类型，
 以及代码密度单子，答案类型位于
 扩展函子本身。 重新表示一个 free-monad 程序
 它的代码密度单子右关联它的绑定并且可以改进
 二次运行时间转为线性（Voigtländer，“渐近
 相对于自由 Monad 的计算改进”，MPC 2008）； 克梅特的
 kan-extensions Haskell 软件包提供 Ran、Lan、Yoneda 和 Codensity
 在这个二级形态中。 该文件证明了 Hinze 所称的
 规范 — 附件 [ran_adjoint] 和 [lan_adjoint] —
 而不是那些 2 级实现。
*)

Section KanExtension.

Context {A : Category}.
Context {B : Category}.
Context {F : A ⟶ B}.
Context {C : Category}.

(*
The restriction (precomposition) functor Induced := (− ◯ F) : [B,C] ⟶ [A,C],
   written F* or p* in the literature.  On objects it sends G : B ⟶ C to G ◯ F;
   on a natural transformation f : G ⟹ H it whiskers by F, giving the component
   (Induced f)_z = f_(F z).  The Kan extensions along F are the adjoints of this
   functor.
   nLab: https://ncatlab.org/nlab/show/Kan+extension

--------
限制（前复合）函子 Induced := (− ◯ F) : [B,C] ⟶ [A,C]，在文献中写作 F* 或 p*。在对象上，它将 G : B ⟶ C 映射为 G ◯ F；在自然变换 f : G ⟹ H 上，它通过 F 进行修饰，给出分量 (Induced f)_z = f_(F z)。沿 F 的 Kan 扩展是该函子的伴随。nLab: https://ncatlab.org/nlab/show/Kan+extension
*)

Program Definition Induced : ([B, C]) ⟶ ([A, C]) := {|
  fobj := fun G => G ◯ F;
  fmap := fun _ _ f => {| transform := fun z => transform[f] (F z) |}
|}.
Next Obligation. apply naturality. Qed.
Next Obligation. apply naturality_sym. Qed.

(*
Global right Kan extension along F: the right adjoint Ran of the restriction
   functor Induced = (− ◯ F).  The adjunction Induced ⊣ Ran corresponds to the
   hom-set isomorphism [A,C](M ◯ F, X) ≅ [B,C](M, Ran X), natural in M.
   nLab: https://ncatlab.org/nlab/show/Kan+extension
   Wikipedia: https://en.wikipedia.org/wiki/Kan_extension

--------
沿 F 的全局右 Kan 扩张：约束函子 Induced = (− ◯ F) 的右伴随 Ran。伴随关系 Induced ⊣ Ran 对应于同构 [A,C](M ◯ F, X) ≅ [B,C](M, Ran X) 的同态集合映射，并且在 M 中是自然的。
nLab: https://ncatlab.org/nlab/show/Kan+extension
Wikipedia: https://en.wikipedia.org/wiki/Kan_extension
*)

Class RightKan := {
  (*
jww (2017-06-09): Rename this to ran_functor, RightKan to Ran, and then a
     coercion from Ran to functor?

--------
jww (2017-06-09)：将此重命名为 ran_functor，将 RightKan 改为 Ran，然后从 Ran 到 functor 进行一个强制转换？
*)
  Ran : [A, C] ⟶ [B, C];           (* the right Kan extension functor / 右 Kan 延拓函子       *)

  ran_adjoint : Induced ⊣ Ran      (* universal property: Induced ⊣ Ran / 泛性质：诱导 ⊣ Ran     *)
}.

(*
Local (pointwise-free) right Kan extension of a single functor X : A ⟶ C
   along F.  This is the terminal object among pairs (functor, counit), and can
   exist even when the global adjoint Ran above does not.  The counit
   ran_transform : LocalRan ◯ F ⟹ X is universal: every μ : M ◯ F ⟹ X factors
   through it via a unique δ : M ⟹ LocalRan.

--------
单个函子 X : A ⟶ C 沿 F 的局部（逐点自由）右 Kan 延拓。这是在（函子, 对单位）对之间的终对象，即使上面的全局伴随 Ran 不存在，它也可能存在。对单位 ran_transform : LocalRan ◯ F ⟹ X 是普遍的：每个 μ : M ◯ F ⟹ X 都通过一个唯一的 δ : M ⟹ LocalRan 来因式分解。
*)

Class LocalRightKan (X : A ⟶ C) := {
  LocalRan : B ⟶ C;                       (* the extending functor R : B ⟶ C / 扩展函子 R : B ⟶ C *)

  ran_transform : LocalRan ◯ F ⟹ X;       (* counit ε : R ◯ F ⟹ X / 余单位 ε : R ◯ F ⟹ X            *)

  (*
terminality / universal property: μ factors uniquely through the counit
     as μ ≈ ran_transform ∙ (δ ⊲ F), with δ the unique mediating arrow

--------
终结性 / 泛性质：μ 唯一地通过余单位进行分解，即 μ ≈ ran_transform ∙ (δ ⊲ F)，其中 δ 是唯一的中介箭头
*)
  ump_ran (M : B ⟶ C) (μ : M ◯ F ⟹ X) :
    (∃! δ, μ ≈ ran_transform ∙ δ ⊲ F);
}.

(*
Wikipedia: “There is also a local definition of 'the Kan extension of a
   given functor F along p' which can exist even if the entire functor defined
   above [global Kan extension] does not. This is a generalization of the fact
   that a particular diagram of shape C can have a limit even if not every
   such diagram does. It is also a special case of the fact discussed at
   adjoint functor that an adjoint functor can fail to exist completely, but
   may still be partially defined. If the local Kan extension of every single
   functor exists for some given p : C → C' and D, then these local Kan
   extensions fit together to define a functor which is the global Kan
   extension.”

--------
维基百科：“还有一个‘沿着 p 的给定函子 F 的 Kan 延拓’的局部定义，即使上面定义在 [global Kan extension] 的整个函子不存在，它也可以存在。这是一个推广事实：一个特定形状为 C 的图可以有极限，即使并非每个该类图都有极限。它也是在伴随中讨论的一个特殊情况，即伴随可能完全不存在，但仍可以部分定义。如果对于某个给定的 p : C → C' 和 D，每一个单独的函子的局部 Kan 延拓都存在，那么这些局部 Kan 延拓可以组合在一起定义一个函子，这个函子就是全局 Kan 延拓。”
*)

(*
A global right Kan extension restricts to a local one at each X: take the
   extending functor to be Ran X and the counit to be the image of the identity
   under the adjunction iso (the counit of Induced ⊣ Ran at X).

--------
一个全局右Kan扩张在每个X处限制为局部右Kan扩张：取扩展函子为Ran X，余单位为在伴随同构下恒等映射的像（Induced ⊣ Ran在X处的余单位）。
*)

#[export] Program Instance RightKan_to_LocalRightKan {R : RightKan} (X : A ⟶ C) :
  LocalRightKan X := {|
  LocalRan := Ran X;
  ran_transform := from (@adj _ _ _ _ ran_adjoint (Ran X) X) nat_id
|}.
Next Obligation.
  exists (to (@adj _ _ _ _ (@ran_adjoint R) M X) μ).
  - intros.
    spose (@from_adj_nat_l _ _ _ _ ran_adjoint) as X0.
    rewrite <- X0; clear X0.
    spose (@iso_from_to _ _ _ (@adj _ _ _ _ ran_adjoint M X) μ x) as X0.
    unfold nat_compose; simpl in *.
    rewrites.
    sapply (proper_morphism (@from _ _ _ (@adj _ _ _ _ ran_adjoint M X))).
    simpl; intros; cat.
  - intros.
    assert (μ ≈ (adj[ran_adjoint])⁻¹ v). {
      intro.
      specialize (X0 x).
      rewrite X0; clear X0.
      srewrite_r (@from_adj_nat_l _ _ _ _ ran_adjoint).
      destruct (adj[ran_adjoint]); simpl in *.
      destruct from; simpl in *.
      apply proper_morphism; simpl.
      now apply nat_id_left.
    }
    clear -X1.
    destruct (adj[ran_adjoint]); simpl in *.
    intros.
    rewrite <- (iso_to_from v).
    destruct to; simpl in *.
    apply proper_morphism.
    simpl.
    now apply X1.
Qed.

(*
Global left Kan extension along F: the left adjoint Lan of the restriction
   functor Induced = (− ◯ F).  The adjunction Lan ⊣ Induced corresponds to the
   hom-set isomorphism [A,C](X, M ◯ F) ≅ [B,C](Lan X, M), natural in M.
   nLab: https://ncatlab.org/nlab/show/Kan+extension
   Wikipedia: https://en.wikipedia.org/wiki/Kan_extension

--------
沿 F 的全局左 Kan 延拓：约束函子 Induced = (− ◯ F) 的左伴随 Lan。伴随关系 Lan ⊣ Induced 对应于同构态集合 [A,C](X, M ◯ F) ≅ [B,C](Lan X, M)，在 M 中自然。nLab: https://ncatlab.org/nlab/show/Kan+extension Wikipedia: https://en.wikipedia.org/wiki/Kan_extension
*)

Class LeftKan := {
  Lan : [A, C] ⟶ [B, C];           (* the left Kan extension functor / 左 Kan 延拓函子        *)

  lan_adjoint : Lan ⊣ Induced      (* universal property: Lan ⊣ Induced / 泛性质：Lan ⊣ Induced     *)
}.

(*
Local left Kan extension of a single functor X : A ⟶ C along F.  This is the
   initial object among pairs (functor, unit), and can exist even when the
   global adjoint Lan above does not.  The unit lan_transform : X ⟹ LocalLan ◯ F
   is universal: every ε : X ⟹ M ◯ F factors through it via a unique
   δ : LocalLan ⟹ M.

--------
沿着 F 的单个函子 X : A ⟶ C 的局部左 Kan 扩张。这是在 (函子, 单位) 对中初始对象，即使上面的全局伴随 Lan 不存在，它也可能存在。单位 lan_transform : X ⟹ LocalLan ◯ F 是通用的：每一个 ε : X ⟹ M ◯ F 都可以通过唯一的 δ : LocalLan ⟹ M 分解经过它。
*)

Class LocalLeftKan (X : A ⟶ C) := {
  LocalLan : B ⟶ C;                       (* the extending functor L : B ⟶ C / 扩展函子 L : B ⟶ C *)

  lan_transform : X ⟹ LocalLan ◯ F;       (* unit η : X ⟹ L ◯ F / 单位 η : X ⟹ L ◯ F              *)

  (*
initiality / universal property: ε factors uniquely through the unit as
     ε ≈ (δ ⊲ F) ∙ lan_transform, with δ the unique mediating arrow

--------
初始性 / 泛性质：ε 唯一地通过单位分解为
     ε ≈ (δ ⊲ F) ∙ lan_transform，其中 δ 是唯一的中介箭头
*)
  ump_lan (M : B ⟶ C) (ε : X ⟹ M ◯ F) :
    ∃! δ, ε ≈ δ ⊲ F ∙ lan_transform;
}.

(*
A global left Kan extension restricts to a local one at each X: take the
   extending functor to be Lan X and the unit to be the image of the identity
   under the adjunction iso (the unit of Lan ⊣ Induced at X).

--------
全局左Kan延拓在每个X处限制为局部左Kan延拓：将延拓函子取为Lan X，单位取为在伴随同构下的恒等映射的像（Lan ⊣ 在X处诱导的单位）。
*)

#[export] Program Instance LeftKan_to_LocalLeftKan {R : LeftKan} (X : A ⟶ C) :
  LocalLeftKan X := {|
  LocalLan := Lan X;
  lan_transform := to (@adj _ _ _ _ lan_adjoint X (Lan X)) nat_id
|}.
Next Obligation.
  exists (from (@adj _ _ _ _ (@lan_adjoint R) X M) ε).
  - intros.
    spose (@to_adj_nat_r _ _ _ _ lan_adjoint) as X0.
    rewrite <- X0; clear X0.
    spose (@iso_to_from _ _ _ (@adj _ _ _ _ lan_adjoint X M) ε x) as X0.
    unfold nat_compose; simpl in *.
    rewrites.
    sapply (proper_morphism (@to _ _ _ (@adj _ _ _ _ lan_adjoint X M))).
    simpl; intros; cat.
  - intros.
    assert (ε ≈ (to adj[lan_adjoint]) v). {
      intro.
      specialize (X0 x).
      rewrite X0; clear X0.
      srewrite_r (@to_adj_nat_r _ _ _ _ lan_adjoint).
      destruct (to adj[lan_adjoint]); simpl in *.
      apply proper_morphism; simpl.
      now apply nat_id_right.
    }
    clear -X1.
    destruct (adj[lan_adjoint]); simpl in *.
    intros.
    rewrite <- (iso_from_to v).
    destruct from; simpl in *.
    apply proper_morphism.
    simpl.
    now apply X1.
Qed.

End KanExtension.

Arguments RightKan {_ _} F _.
Arguments Ran {_ _} F {_ _}.

Arguments LocalRightKan {_ _} F {_} _.
Arguments LocalRan {_ _} F {_} _ {_}.

Arguments LeftKan {_ _} F _.
Arguments Lan {_ _} F {_ _}.

Arguments LocalLeftKan {_ _} F {_} _.
Arguments LocalLan {_ _} F {_} _ {_}.

(*
From “All Concepts are Kan Extensions”, by Marina Christina Lehner:

   “A functor preserves a Kan extension when composing then extending is
   equivalent to extending then composing.”

--------
摘自 Marina Christina Lehner 的《所有概念都是 Kan 扩展》：

“当先组合再扩展等价于先扩展再组合时，一个函子就保持 Kan 扩展。”
*)

(*
A functor L preserves left Kan extensions when applying L after extending
   agrees with extending after applying L, i.e. L ◯ Lan K G ≈ Lan K (L ◯ G).
   The two LeftKan hypotheses supply the extensions on each side.

--------
函子 L 在应用 L 后保留左 Kan 扩展时，结果与先扩展后应用 L 相同，即 L ◯ Lan K G ≈ Lan K (L ◯ G)。两个 LeftKan 假设提供了每一边的扩展。
*)

Definition preserves_left_Kan `(L : E ⟶ F) :=
  ∀ C D (G : C ⟶ E) (K : C ⟶ D)
    `(!LeftKan K E) `(!LeftKan K F), L ◯ Lan K G ≈ Lan K (L ◯ G).

(* Dual: R preserves right Kan extensions when R ◯ Ran K G ≈ Ran K (R ◯ G). / 对偶：当 R ◯ Ran K G ≈ Ran K (R ◯ G) 时，R 保持右 Kan 扩张。 *)

Definition preserves_right_Kan `(R : E ⟶ F) :=
  ∀ C D (G : C ⟶ E) (K : C ⟶ D)
    `(!RightKan K E) `(!RightKan K F), R ◯ Ran K G ≈ Ran K (R ◯ G).

(*
“We show that left adjoints preserve left Kan extensions, while right
   adjoints will preserve right adjoints [sic]. These connections with
   adjoints run deeper. We will show an adjoint functor theorem which says
   the existence of an adjoint is conditional on a functor having and
   preserving certain Kan extensions.”

--------
我们展示了左伴随会保持左 Kan 扩展，而右伴随会保持右伴随 [sic]。这些与伴随的联系更加深刻。我们将展示一个伴随定理，该定理说明伴随的存在取决于一个函子是否具有并保持某些 Kan 扩展。
*)

(*
If L ⊣ R then precomposition by L is hom-isomorphic to postcomposition by R:
   [E,D](L ◯ G, H) ≊ [E,C](G, R ◯ H), the functor-category lift of the
   defining hom-set adjunction.  This is the lemma used to show that left
   adjoints preserve left Kan extensions.

--------
如果 L ⊣ R，那么由 L 进行的前复合在同构上等价于由 R 进行的后复合：
   [E,D](L ◯ G, H) ≊ [E,C](G, R ◯ H)，这是定义同态集伴随关系的函子范畴提升。 这是用于证明左伴随保持左 Kan 扩张的引理。
*)

Theorem left_adjoint_impl `(L : C ⟶ D) :
  ∀ R : D ⟶ C, L ⊣ R ->
  ∀ {E} (G : E ⟶ C) (H : E ⟶ D),
    [[[E,D]]](L ◯ G, H) ≊ [[[E,C]]](G, R ◯ H).
Proof.
  intros.
  simpl.
  isomorphism; simpl.
  - construct.
    + transform.
      * intros.
        apply X; simpl.
        now apply X0.
      * simpl.
        rewrite <- to_adj_nat_l.
        rewrite <- to_adj_nat_r.
        now srewrite (@naturality _ _ _ _ X0 _ _ f).
      * simpl.
        rewrite <- to_adj_nat_l.
        rewrite <- to_adj_nat_r.
        now srewrite (@naturality _ _ _ _ X0 _ _ f).
    + simpl.
      proper.
      apply to_adj_respects.
      now apply X0.
  - construct.
    + transform.
      * intros.
        apply X; simpl.
        now apply X0.
      * simpl.
        rewrite <- from_adj_nat_l.
        rewrite <- from_adj_nat_r.
        now srewrite (@naturality _ _ _ _ X0 _ _ f).
      * simpl.
        rewrite <- from_adj_nat_l.
        rewrite <- from_adj_nat_r.
        now srewrite (@naturality _ _ _ _ X0 _ _ f).
    + simpl.
      proper.
      apply from_adj_respects.
      now apply X0.
  - simpl.
    now apply from_adj_comp_law.
  - simpl.
    now apply to_adj_comp_law.
Qed.

(*
Work in progress: left adjoints preserve left Kan extensions (Lehner, “All
   Concepts are Kan Extensions”).  The proof is incomplete — three obligations
   are left open and the proof script is abandoned before `Qed`, so the theorem
   is NOT added to the environment and introduces no axioms.  Retained as a
   proof sketch.  jww: complete the remaining isomorphism/identity obligations.
   The adjoint-continuity machinery this wants now exists —
   [right_adjoint_preserves_limits] and the preservation vocabulary in
   Adjunction/Continuity.v and Structure/Limit/Preservation.v — and is the
   natural toolkit for a future completion of this sketch.

--------
进行中的工作：左伴随保持左Kan扩张（Lehner，《所有概念都是Kan扩张》）。证明尚未完成——三个义务尚未解决，并且在`Qed`之前放弃了证明脚本，因此该定理未被添加到环境中，也未引入任何公理。保留为证明草图。jww：完成剩余的同构/恒等义务。现在所需的伴随-连续性机制已经存在——[right_adjoint_preserves_limits] 以及 Adjunction/Continuity.v 和 Structure/Limit/Preservation.v 中的保持词汇——是未来完成此草图的自然工具。
*)

Theorem left_adjoints_preserve `(L : C ⟶ D) :
  ∀ R : D ⟶ C, L ⊣ R → preserves_left_Kan L.
Proof.
  intros.
  construct.
  - isomorphism.
    + apply X; simpl.
      rewrite <- fobj_Compose.
      apply LeftKan0; simpl.
      spose (left_adjoint_impl _ _ X G (Lan K (L ◯ G) ◯ K)) as X0.
      transitivity (R ◯ (Lan K (L ◯ G) ◯ K)).
      * apply (to X0); simpl.
        apply LeftKan1; simpl.
        exact nat_id.
      * now apply fun_comp_assoc.
    + rewrite <- fobj_Compose.
      apply LeftKan1; simpl.
      spose (left_adjoint_impl _ _ X G (L ◯ Lan K G ◯ K)) as X0.
      apply X0; simpl; clear X0.
      transitivity (R ◯ L ◯ fobj[Lan _] G ◯ K). {
        apply LeftKan0; simpl.
        transform.
        - intros.
          apply unit.
        - simpl.
          unfold unit.
          rewrite <- to_adj_nat_l.
          rewrite <- to_adj_nat_r.
          rewrite id_left, id_right.
          reflexivity.
        - simpl.
          unfold unit.
          rewrite <- to_adj_nat_l.
          rewrite <- to_adj_nat_r.
          rewrite id_left, id_right.
          reflexivity.
      }
      pose proof (@fun_comp_assoc_sym _ _ _ _ R L (Lan K G ◯ K)).
      pose proof (@fun_comp_assoc_sym _ _ _ _ R (L ◯ Lan K G) K).
      pose proof (@fun_comp_assoc_sym _ _ _ _ (R ◯ L) (Lan K G) K).
      transitivity ((R ◯ L) ◯ ((fobj[Lan _] G) ◯ K)); auto.
      transitivity (R ◯ (L ◯ ((fobj[Lan _] G) ◯ K))); auto.
      transitivity (R ◯ ((L ◯ (fobj[Lan _] G)) ◯ K)).
      * apply whisker_left.
        apply fun_comp_assoc.
      * exact nat_id.
    + simpl.
      admit.
    + simpl.
      admit.
  - simpl.
    admit.
Abort.
