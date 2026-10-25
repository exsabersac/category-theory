Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Initial.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Comma.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Universal arrows / * 通用箭头 *)

(*
nLab: https://ncatlab.org/nlab/show/universal+morphism
   Wikipedia: https://en.wikipedia.org/wiki/Universal_property

   A universal arrow from an object c : C to a functor F : D ⟶ C is a pair
   (a, u) consisting of an object a : D and a morphism u : c ~> F a, such that
   for every object d : D and every morphism h : c ~> F d there exists a
   unique g : a ~> d satisfying h ≈ fmap[F] g ∘ u. Equivalently, (a, u) is an
   initial object of the comma category =(c) ↓ F (objects are pairs (d, f)
   with f : c ~> F d). The dual notion, a universal arrow from F to c, is a
   terminal object of F ↓ =(c). Universal arrows are the unifying notion
   behind limits, representables, and adjunctions: when every c : C has a
   universal arrow to U : D ⟶ C, the assignment c ↦ a extends to a left
   adjoint of U, with the arrows u serving as the components of the unit.

--------
nLab: https://ncatlab.org/nlab/show/universal+morphism
Wikipedia: https://en.wikipedia.org/wiki/Universal_property

从对象 c : C 到函子 F : D ⟶ C 的一个通用箭头是一对 (a, u)，由对象 a : D 和态射 u : c ~> F a 组成，使得对于每个对象 d : D 和每个态射 h : c ~> F d，存在唯一的 g : a ~> d 满足 h ≈ fmap[F] g ∘ u。等价地，(a, u) 是逗号范畴 =(c) ↓ F 的初始对象（对象是一对 (d, f)，其中 f : c ~> F d）。对偶概念，从 F 到 c 的通用箭头是 F ↓ =(c) 的终端对象。通用箭头是极限、可表示函子和伴随的统一概念：当每个 c : C 都有到 U : D ⟶ C 的通用箭头时，映射 c ↦ a 可以扩展为 U 的左伴随，箭头 u 则作为单位的分量。
*)

(*
From universal mappings to adjoint functors

   nLab:  https://ncatlab.org/nlab/show/universal+construction
   Paper: Samuel, "On universal mappings and free topological groups",
          Bull. Amer. Math. Soc. 54(6), 1948
   Paper: Porst, "The history of the General Adjoint Functor Theorem",
          arXiv:2310.19528, 2024

   The universal arrow is the common shape of the universal mapping
   problems of classical algebra and topology, isolated before category
   theory had vocabulary to state it.  Free groups were current in the
   1920s, the Stone–Čech compactification in the 1930s, and Markov's free
   topological groups in the 1940s, each with its own bespoke existence
   proof (Porst 2024).  The general problem was first posed by Pierre
   Samuel, whose 1948 paper opens by observing that "constructions so
   apparently different as Kronecker products, ... field of quotients of
   an integral domain, free groups, free topological groups, completion
   of a uniform space, Čech compactification enter in the same frame".
   Samuel worked without functors — his axiomatized "kinds of structure"
   derive from Bourbaki's theory of structures, cited from unpublished
   manuscripts and the 1939 Résultats — yet his problem of universal
   mappings asks exactly for a universal arrow to a forgetful functor,
   unique up to isomorphism.  Mac Lane's chapter notes credit Samuel with
   "the bold step of really formulating the general notion", suggest that
   uniqueness only up to isomorphism is why the notion was slow to
   develop, and record that Bourbaki then popularized it lavishly; the
   notes to the adjunctions chapter add that Bourbaki's one-sided
   formulation "lacks the symmetry of the adjunction problem" and so
   just missed adjoint functors, whose discovery was left to Kan in
   1958 (Mac Lane, "Categories for the Working Mathematician", Springer
   1998, notes to Chapters III and IV).  Products described by the
   universal property of their projections date from about the same
   time (Mac Lane, 1948/1950); Functor/Diagonal.v plays out that dual
   story in-tree.

   The purpose of the notion is codified by Theorem IV.1.2 of the same
   book: a functor has a left adjoint precisely when every object of its
   codomain has a universal arrow to it, and those arrows are then the
   components of the unit.  A universal arrow is thus the local,
   pointwise form of an adjunction, and this file implements the
   local-to-global direction: [LeftAdjointFunctorFromUniversalArrows]
   assembles the functor, and [AdjunctionFromUniversalArrows] the
   adjunction, from a family of [UniversalArrow] witnesses.  The
   comma-category packaging does real work here: because [arrow_initial]
   is an initial object, uniqueness up to unique isomorphism is the
   generic initial-object argument rather than a lemma re-proved per
   construction — in Riehl's phrasing, "universal" is "a synonym for
   either 'initial' or 'terminal'" (Riehl, "Category Theory in Context",
   Dover 2016).  Structure/UniversalProperty/Universal/Arrow.v keeps the
   representability face: [UniversalArrowIsUniversalProperty] identifies
   an [AUniversalArrow] with a hom-set isomorphism via Yoneda.

   The adjoint functor theorems are machines for manufacturing these
   witnesses.  Samuel's own existence proof — form the product of all
   mappings into structures of bounded cardinal, then cut down by
   closure — is the skeleton of Freyd's proof of the General Adjoint
   Functor Theorem (1960 thesis, printed 1964), which Porst accordingly
   proposes to rename the Samuel–Freyd theorem.  In-tree the route is
   Mac Lane's: Adjunction/GAFT.v produces an initial object of each comma
   category, and its [GAFT_from_initials] concludes with the two
   constructors of this file; Monad/Lifting.v proves the Dubuc
   adjoint-triangle theorem the same way, one universal arrow per object;
   and Construction/Free/Quiver.v instantiates the oldest pattern, a free
   construction as a universal arrow to a forgetful functor
   ([UniversalArrowQuiverCat]).

   The rendering throughout is proof-relevant.  [ump_universal_arrows]
   returns the mediating morphism as data together with its uniqueness
   certificate, and [LeftAdjointFunctorFromUniversalArrows] computes the
   action of the induced functor on a morphism f as the unique g with
   arrow ∘ f ≈ fmap[U] g ∘ arrow: a free functor acts on arrows by
   factorization rather than by choice.  The setoid discipline surfaces
   in the direct encoding: uniqueness in [universal_arrow_universal] is
   uniqueness up to ≈, and [AUniversalArrowEquiv] declares two universal
   arrows at the same object equivalent precisely when their underlying
   morphisms are ≈, the uniqueness half carrying no further data.  The
   method remains in use well outside foundations (Pestov, "Universal
   arrows to forgetful functors from categories of topological algebra",
   1992), and Milewski teaches it to programmers as the "universal
   construction": pick a shape, enumerate its occurrences, rank
   candidates by unique factorization (Milewski, "Products and
   Coproducts", 2015).

--------
从通用映射到伴随

nLab：https://ncatlab.org/nlab/show/universal+construction
 论文：Samuel，“论通用映射和自由拓扑群”，
 公牛。 阿米尔。 数学。 苏克。 54(6), 1948
 论文：Porst，“一般伴随定理的历史”，
 arXiv:2310.19528, 2024

通用箭头是通用映射的常见形状
 经典代数和拓扑问题，在范畴之前被隔离
 理论有词汇来表述它。 自由团体目前在
 1920 年代、1930 年代的 Stone-Čech 紧化以及马尔可夫的自由
 20 世纪 40 年代的拓扑群，每个都有自己定制的存在
 证明（2024 年之后）。 一般性问题首先由皮埃尔提出
 塞缪尔 (Samuel) 在其 1948 年的论文中指出，“结构如此
 显然与克罗内克积不同，...商的领域
 积分域、自由群、自由拓扑群、补全
 均匀空间的切赫紧化进入同一框架”。
塞缪尔在没有函子的情况下工作——他的公理化“结构类型”
 源自布尔巴基的结构理论，引用自未发表的文献
 手稿和 1939 年的结果——然而他的普遍问题
 映射准确地要求一个指向健忘函子的通用箭头，
 直到同构为止唯一。 麦克莱恩的章节注释将塞缪尔归功于
 “真正制定一般概念的大胆步骤”，建议
 唯一性仅达到同构，这就是为什么这个概念发展缓慢的原因
 发展并记录布尔巴基随后大力推广它； 的
 附加章节的注释补充说，布尔巴基的片面性
 公式“缺乏附加问题的对称性”等等
 刚刚错过了伴随，其发现被留给了 Kan
 1958（Mac Lane，“工作数学家的范畴”，施普林格
 1998 年，第三章和第四章的注释）。
所描述的产品
 他们的预测的普遍性可以追溯到同一时期
 时间（Mac Lane，1948/1950）； Functor/Diagonal.v 展现了对偶
 树中的故事。

该概念的目的由相同的定理 IV.1.2 编码
 书：函子有一个左伴随，恰好当它的每个对象
 共域有一个通用箭头，这些箭头就是
 单元的组成部分。 因此，通用箭头是局部箭头，
 附加的逐点形式，该文件实现了
 本地到全局方向：[LeftAdjointFunctorFromUniversalArrows]
 组装函子，[AdjunctionFromUniversalArrows]
 来自 [UniversalArrow] 目击者家庭的辅助。 的
 逗号范畴打包在这里确实有效：因为 [arrow_initial]
 是一个初始对象，唯一性直到唯一同构是
 通用初始对象参数而不是重新证明的引理
 构造——用里尔的措辞来说，“通用”是“
 “初始”或“终端””（Riehl，“语境中的范畴论”，
 多佛 2016）。 Structure/UniversalProperty/Universal/Arrow.v 保留
 可表现性面：[UniversalArrowIsUniversalProperty] 识别
 Yoneda 提供的具有 hom-set 同构的 [AUniversalArrow]。

伴随定理是制造这些的机器
 证人。 塞缪尔自己的存在证明——形成所有的产物
 映射到有界基数的结构，然后通过
 闭包 — 是 Freyd 广义伴随证明的骨架
 函子定理（1960 年论文，1964 年印刷），波斯特相应地
 建议重新命名塞缪尔-弗雷德定理。 树内路线是
 Mac Lane 的：Adjunction/GAFT.v 生成每个逗号的初始对象
 范畴，其 [GAFT_from_initials] 以两个结尾
 该文件的构造函数； Monad/Lifting.v 证明了 Dubuc
 伴随三角形定理同样如此，每个对象一个通用箭头；
 Construction/Free/Quiver.v 实例化了最古老的模式，一个免费的模式
 构造为指向健忘函子的通用箭头
 ([UniversalArrowQuiverCat])。

整个渲染都是与证据相关的。 保护8X
 将中介态射作为数据返回及其唯一性
 证书，[LeftAdjointFunctorFromUniversalArrows] 计算
 诱导函子对态射 f 的作用作为唯一的 g
 arrow ∘ f ≈ fmap[U] g ∘ arrow：自由函子通过以下方式作用于箭头
 分解而不是选择。 集合体学科表面
 在直接编码中：[universal_arrow_universal] 中的唯一性是
 唯一性高达 ≈，[AUniversalArrowEquiv] 声明了两个通用的
 指向同一个对象的箭头恰好等于其底层的箭头
 态射是 ≈，唯一性一半不携带进一步的数据。 的
 该方法在基金会之外仍然广泛使用（Pestov，“Universal
 从拓扑代数范畴到健忘函子的箭头”，
 1992），Milewski 将其作为“通用工具”教授给程序员
 构造”：选择一个形状，枚举它的出现次数，排名
 通过独特的因式分解候选（Milewski，“产品和
 联产品”，2015）。
*)

(*
Two encodings of this notion are given below. UniversalArrow packages the
   property as an initial object of the comma category =(c) ↓ F, which makes
   the universal mapping property [ump_universal_arrows] an immediate
   consequence; AUniversalArrow records the same data directly as a morphism
   together with its [Unique] factorization, without naming the object a as a
   projection out of the comma category.

--------
下面给出了这个概念的两种编码。UniversalArrow 将该属性封装为逗号范畴 =(c) ↓ F 的初始对象，这使得泛映射性质 [ump_universal_arrows] 成为直接的结果；AUniversalArrow 直接作为态射及其 [Unique] 分解记录相同的数据，而不将对象 a 命名为逗号范畴中的投影。
*)

Section UniversalArrow.

Context `{C : Category}.
Context `{D : Category}.

(*
A universal arrow from c to F is an initial object of the comma category
   =(c) ↓ F.  Its underlying object [arrow_obj] and morphism [arrow] are read
   off as the two projections of that initial object.

--------
从 c 到 F 的一个通用箭头是逗号范畴 =(c) ↓ F 的一个初始对象。其底层对象 [arrow_obj] 和态射 [arrow] 可以从该初始对象的两个投影中读取。
*)
Class UniversalArrow (c : C) (F : D ⟶ C) := {
  arrow_initial : @Initial (=(c) ↓ F);   (* the universal property, as initiality / 普遍性质，作为初始性 *)

  arrow_obj := snd (`1 (@initial_obj _ arrow_initial));     (* the universal object a : D / 全体对象 a : D *)
  arrow : c ~> F arrow_obj := `2 (@initial_obj _ arrow_initial)  (* the universal morphism u : c ~> F a / 通用态射 u : c ~> F a *)
}.

Notation "c ⟿ F" := (UniversalArrow c F) (at level 20) : category_theory_scope.

(*
The universal mapping property: any h : c ~> F d factors as h ≈ fmap[F] g ∘
   arrow through a unique g : arrow_obj ~> d.  This follows directly from the
   initiality of arrow_obj in the comma category =(c) ↓ F.

--------
通用映射性质：任意 h : c ~> F d 都可以分解为 h ≈ fmap[F] g ∘ 穿过一个唯一的 g : arrow_obj ~> d 的箭头。这直接来源于箭头对象在逗号范畴 =(c) ↓ F 中的初始性。
*)
Corollary ump_universal_arrows `(c ⟿ F) `(h : c ~> F d) :
  ∃! g : arrow_obj ~> d, h ≈ fmap[F] g ∘ arrow.
Proof.
  unfold arrow_obj, arrow; simpl.
  destruct (@zero _ arrow_initial ((ttt, d); h)), x.
  simpl in *.
  rewrite id_right in e.
  exists h1.
  - assumption.
  - intros.
    rewrite <- id_right in e.
    rewrite <- id_right in X.
    exact (snd (@zero_unique _ arrow_initial ((ttt, d); h)
                             ((ttt, h1); e) ((ttt, v); X))).
Qed.

(*
Conversely, the universal mapping property reconstructs the initial object,
   hence a UniversalArrow: given η : c ~> F d that factors every f : c ~> F d'
   uniquely, (d, η) is initial in =(c) ↓ F.

--------
相反，通用映射性质重构初始对象，因此存在一个通用箭头：给定 η : c ~> F d，它唯一地分解每个 f : c ~> F d'，则 (d, η) 是 =(c) ↓ F 中的初始对象。
*)
Definition universal_arrow_from_UMP (c : C) (F : D ⟶ C) (d : D) (η : c ~> fobj[F] d)
  (u : ∀ (d' : D) (f : c ~> fobj[F] d'), ∃! g : d ~> d', f ≈ fmap[F] g ∘ η)
  : UniversalArrow c F.
Proof.
  unshelve eapply Build_UniversalArrow. simpl. unshelve esplit.
  - simpl. unshelve esplit; [ split; [ exact ttt | exact d ] | exact η ].
  - simpl. intros [ [unit d'] f]; simpl in *.
    unshelve esplit; [ split ; [ exact ttt | exact (unique_obj (u d' f))] | ].
    rewrite id_right; simpl. exact (unique_property (u d' f)).
  - simpl. intros [[unit d']  f]; simpl in *.
    intros [[unit2 g] g_eq]. simpl in g_eq.
    intros [[unit3 h] h_eq]. split.
    + simpl. destruct unit2, unit3; reflexivity.
    + simpl. rewrite id_right in g_eq, h_eq. simpl in h_eq.
      rewrite <- (uniqueness (u d' f) _ g_eq).
      exact (uniqueness (u d' f) _ h_eq).
Defined.

(** ** Uniqueness up to a unique isomorphism / ** 至多唯一同构的唯一性 *)

(*
Awodey, "Category Theory" (1st ed., Carnegie Mellon pre-print, September
   2005), Proposition 1.10, printed p. 22, states for free monoids what holds
   of every universal arrow: two solutions of the same universal mapping
   problem are connected by exactly one isomorphism COMPATIBLE WITH the
   universal arrows.  The compatibility clause is not decoration.  The
   header of this file already observes that a universal arrow is an initial
   object of a comma category and that uniqueness is therefore "the generic
   initial-object argument"; [initial_unique_up_to_unique_iso]
   (Structure/Initial.v) carries out that argument, but it lives in the comma
   category =(c) ↓ F and its uniqueness clause ranges over comma
   isomorphisms.  Read down in D — which is where a consumer wants it, since
   the object of interest is [arrow_obj], not the comma pair — the predicate
   [True] would be FALSE: [arrow_obj] can have automorphisms (the free monoid
   on two generators has one exchanging them), and those are isomorphisms
   between the two universal objects that do not commute with the arrows.
   What is unique is the isomorphism satisfying
   [fmap[F] (to i) ∘ arrow₁ ≈ arrow₂], and that is the statement proved here.

   The proof does not go through the comma category at all: it is the
   two-line mediator argument run on [ump_universal_arrows], with
   [to_equiv_implies_iso_equiv] (Theory/Isomorphism.v) supplying the step
   from agreement of the [to] components to equality in [iso_setoid].  Both
   encodings of the notion are covered — [universal_arrow_unique] for the
   comma-packaged [UniversalArrow], where the object is projected out, and
   [auniversal_arrow_unique] for [AUniversalArrow], where it is named.

--------
Awodey，《范畴论》（第1版，卡内基梅隆预印本，2005年9月），命题1.10，第22页，陈述了自由monoid的情况，即每个普适箭头成立：同一普适映射问题的两个解由恰好一个与普适箭头兼容的同构连接。兼容条款不是装饰。本文件的标题已经指出，普适箭头是逗号范畴的初始对象，因此唯一性是“通用的初始对象论证”；[initial_unique_up_to_unique_iso]（Structure/Initial.v）执行了该论证，但它存在于逗号范畴=(c) ↓ F中，并且其唯一性条款适用于逗号同构。
在 D 中向下阅读 —— 这是消费者希望的，因为感兴趣的对象是 [arrow_obj]，而不是逗号对 —— 谓词 [True] 将为 FALSE：[arrow_obj] 可以有自同构（两个生成元上的自由幺半群有一个交换它们的），这些自同构是两个普遍对象之间的同构，但不与箭头交换。唯一的是满足 [fmap[F]（到 i）∘ arrow₁ ≈ arrow₂ 的同构，这正是这里证明的陈述。

这个证明完全没有通过逗号范畴：它是在 [ump_universal_arrows] 上运行的两行中介论证，其中 [to_equiv_implies_iso_equiv]（Theory/Isomorphism.v）提供了从 [to] 组件的一致性到 [iso_setoid] 相等性的步骤。两种表示该概念的方法都涵盖了——[universal_arrow_unique] 用于逗号包装的 [UniversalArrow]，其中对象被投影出去，[auniversal_arrow_unique] 用于 [AUniversalArrow]，其中对象被命名。
*)

Section UniversalArrowUnique.

Context {c : C}.
Context {F : D ⟶ C}.

(*
The canonical mediating morphism: the unique factorization of the second
   universal arrow through the first.

--------
典型的中介态射：第二个泛箭通过第一个的唯一分解。
*)
Definition ua_med (U1 U2 : UniversalArrow c F)
  : @arrow_obj c F U1 ~{D}~> @arrow_obj c F U2 :=
  unique_obj (@ump_universal_arrows c F U1 (@arrow_obj c F U2) (@arrow c F U2)).

Lemma ua_med_commutes (U1 U2 : UniversalArrow c F) :
  fmap[F] (ua_med U1 U2) ∘ @arrow c F U1 ≈ @arrow c F U2.
Proof.
  symmetry.
  exact (unique_property
           (@ump_universal_arrows c F U1 (@arrow_obj c F U2) (@arrow c F U2))).
Qed.

(* Any morphism commuting with the two universal arrows IS the mediator. / 任何与两个普遍箭头交换的态射就是中介者。 *)
Lemma ua_med_unique (U1 U2 : UniversalArrow c F)
      (g : @arrow_obj c F U1 ~{D}~> @arrow_obj c F U2) :
  fmap[F] g ∘ @arrow c F U1 ≈ @arrow c F U2 → ua_med U1 U2 ≈ g.
Proof.
  intro Hg.
  exact (uniqueness
           (@ump_universal_arrows c F U1 (@arrow_obj c F U2) (@arrow c F U2))
           g (symmetry Hg)).
Qed.

Lemma ua_med_id (U1 : UniversalArrow c F) : ua_med U1 U1 ≈ id.
Proof.
  apply ua_med_unique.
  rewrite fmap_id.
  apply id_left.
Qed.

Lemma ua_med_comp (U1 U2 U3 : UniversalArrow c F) :
  ua_med U2 U3 ∘ ua_med U1 U2 ≈ ua_med U1 U3.
Proof.
  symmetry.
  apply ua_med_unique.
  rewrite fmap_comp, <- comp_assoc.
  rewrite ua_med_commutes.
  apply ua_med_commutes.
Qed.

(*
The two mediators are mutually inverse, so the universal objects are
   isomorphic.

--------
这两个中介是相互逆的，因此泛对象是同构的。
*)
Program Definition universal_arrow_iso (U1 U2 : UniversalArrow c F)
  : @arrow_obj c F U1 ≅ @arrow_obj c F U2 := {|
  to   := ua_med U1 U2;
  from := ua_med U2 U1
|}.
Next Obligation. rewrite ua_med_comp; apply ua_med_id. Qed.
Next Obligation. rewrite ua_med_comp; apply ua_med_id. Qed.

(*
An isomorphism is determined by its [to] component
   ([to_equiv_implies_iso_equiv]), so compatibility with the universal
   arrows pins it down completely.

--------
一个同构由其 [to] 组件（[to_equiv_implies_iso_equiv]）决定，因此与通用箭头的兼容性完全确定了它。
*)
Lemma universal_arrow_iso_unique (U1 U2 : UniversalArrow c F)
      (v : @arrow_obj c F U1 ≅ @arrow_obj c F U2) :
  fmap[F] (to v) ∘ @arrow c F U1 ≈ @arrow c F U2 →
  universal_arrow_iso U1 U2 ≈ v.
Proof.
  intro Hv.
  apply to_equiv_implies_iso_equiv; simpl.
  now apply ua_med_unique.
Qed.

(*
Awodey's Proposition 1.10 in general form: exactly one isomorphism of the
   universal objects carries the first universal arrow to the second.

--------
Awodey 的命题 1.10 的一般形式：唯一的一个同构将第一个通用箭头映射到第二个通用箭头。
*)
Program Definition universal_arrow_unique (U1 U2 : UniversalArrow c F) :
  Unique (fun i : @arrow_obj c F U1 ≅ @arrow_obj c F U2 =>
            fmap[F] (to i) ∘ @arrow c F U1 ≈ @arrow c F U2) := {|
  unique_obj      := universal_arrow_iso U1 U2;
  unique_property := ua_med_commutes U1 U2
|}.
Next Obligation. exact (universal_arrow_iso_unique U1 U2 v X). Qed.

End UniversalArrowUnique.

Context (U : @Functor D C).

Arguments arrow : clear implicits.
Arguments arrow_obj : clear implicits.

(*
A universal arrow to U from every object c : C assembles into a left adjoint
   of U.  The object map sends c to its universal object arrow_obj, and the
   morphism map sends f : x ~> y to the unique factorization of arrow ∘ f
   through arrow_obj x.

--------
从每个对象 c : C 到 U 的一个通用箭头组装成 U 的一个左伴随。对象映射将 c 发送到它的通用对象 arrow_obj，态射映射将 f : x ~> y 发送到通过 arrow_obj x 对箭头 ∘ f 的唯一分解。
*)
Definition LeftAdjointFunctorFromUniversalArrows (H : forall c : C, UniversalArrow c U)
  : @Functor C D.
Proof.
  refine
    ({|
        fobj := (fun c => arrow_obj _ _ (H c));
        fmap := (fun x y f => unique_obj (ump_universal_arrows (H x)
                                            ((arrow _ _ (H y) ∘ f))))

      |}).
  - abstract(intros x y f g f_eq_g;
             apply uniqueness;
             rewrite <- (unique_property
                  (ump_universal_arrows (H x) (arrow y U (H y) ∘ g)));
             now rewrite f_eq_g).
  - abstract(intros ?; apply uniqueness; cat_simpl).
  - abstract(intros c1 c2 c3 g f; apply uniqueness;
      rewrite fmap_comp,
      <- comp_assoc,
      <- (unique_property (ump_universal_arrows (H c1) _)),
      2! comp_assoc;
      exact (compose_respects _ _
             (unique_property (ump_universal_arrows (H c2) _))
             f f (Equivalence_Reflexive _))).
Defined.

(*
The induced functor is genuinely left adjoint to U: the hom-set isomorphism
   (LeftAdjoint c ~> d) ≊ (c ~> U d) is exactly the universal factorization,
   with the universal arrows u serving as the unit of the adjunction.

--------
诱导函子实际上是 U 的左伴随：同值集合的同构
   (LeftAdjoint c ~> d) ≊ (c ~> U d) 正是普遍分解，
   其中普遍箭头 u 作为伴随的单位。
*)
Definition AdjunctionFromUniversalArrows (H: forall c : C, UniversalArrow c U) :
  @Adjunction _ _ (LeftAdjointFunctorFromUniversalArrows H) U.
Proof.
  unshelve eapply Build_Adjunction'.
  + intros c d; unshelve eapply Isomorphism.Build_Isomorphism.
  - unshelve eapply Sets.Build_SetoidMorphism.
    * exact (fun g => (fmap[U] g) ∘ (arrow _ _ (H c))).
    * abstract(intros ? ? g1_eq_g2; rewrite g1_eq_g2; reflexivity).
  - unshelve eapply Sets.Build_SetoidMorphism.
    * exact(fun f => unique_obj (ump_universal_arrows (H c) f)).
    * abstract(intros f1 f2 f1_eq_f2; apply uniqueness; rewrite f1_eq_f2;
               apply (unique_property (ump_universal_arrows (H c) f2))).
  - abstract(intro f; symmetry; exact (unique_property (ump_universal_arrows (H c) f))).
  - abstract(simpl; intro g; apply uniqueness; reflexivity).
  + abstract(intros c1 c2 d f g;
             simpl; rewrite fmap_comp, <- 2! comp_assoc;
             apply (compose_respects (fmap[U] f) _ (Equivalence_Reflexive _) _ _);
             symmetry;
             apply (unique_property (ump_universal_arrows (H c1) _))).
  + abstract(intros ? ? ? ? ?; simpl; rewrite fmap_comp, <- comp_assoc; reflexivity).
Defined.


(*
The same notion stated directly, with the universal object a : D given as a
   parameter rather than projected from a comma category.  The data is the
   universal morphism together with its uniqueness-of-factorization property.

--------
同样的概念直接陈述，普遍对象 a : D 作为参数给出，而不是从逗号范畴中投射。数据是普遍态射以及它的因式分解唯一性属性。
*)
Class AUniversalArrow (c : C) (F : D ⟶ C) (a : D) := {
    universal_arrow : c ~> fobj[F] a ;                 (* the universal morphism u : c ~> F a / 通用态射 u : c ~> F a *)
    universal_arrow_universal {d} {f : c ~> (fobj[F] d)} :  (* the universal property: f factors uniquely as fmap[F] g ∘ u / 泛性质：f 唯一分解为 fmap[F] g ∘ u *)
    Unique (fun g : hom a d => fmap[F] g ∘ universal_arrow ≈ f)
  }.

(*
Two universal arrows at the same object are equivalent when their underlying
   morphisms agree; the uniqueness property carries no further data.

--------
当两个指向同一对象的通用箭头的底层态射相同时，它们是等价的；唯一性性质不携带额外的数据。
*)
#[export] Program Instance AUniversalArrowEquiv (c : C) (F : D ⟶ C) (a : D) :
  Setoid (AUniversalArrow c F a) :=
  {| equiv := fun X Y => (@universal_arrow _ _ _ X) ≈ (@universal_arrow _ _ _ Y) |}.

(*
[universal_arrow_unique] restated for the direct encoding, where the
   universal object is a parameter rather than a projection.  This is the
   shape Awodey's Proposition 1.10 has: two monoids M and N, each carrying a
   generator insertion that satisfies the UMP, are connected by exactly one
   isomorphism commuting with the two insertions.  Nothing here is inherited
   from the block above; [AUniversalArrow]'s own uniqueness field is the
   entire proof, and its orientation
   ([fmap[F] g ∘ universal_arrow ≈ f]) already matches, so no [symmetry] is
   needed where the comma-packaged version needed one.

--------
[universal_arrow_unique] 在直接编码中重述，其中通用对象是一个参数而不是一个投影。这就是 Awodey 的命题 1.10 的形式：两个单元 M 和 N，每个都携带一个满足 UMP 的生成元插入，通过且仅通过一个与这两个插入交换的同构连接。在这里没有任何内容是从上面的模块继承的；[AUniversalArrow] 自身的唯一性字段就是整个证明，并且它的方向（[fmap[F] g ∘ universal_arrow ≈ f）已经匹配，因此在逗号打包版本需要 [symmetry] 的地方无需使用它。
*)

Section AUniversalArrowUnique.

Context {c : C}.
Context {F : D ⟶ C}.

Definition aua_med {a b : D} (U1 : AUniversalArrow c F a)
           (U2 : AUniversalArrow c F b) : a ~{D}~> b :=
  unique_obj (@universal_arrow_universal c F a U1 b
                (@universal_arrow c F b U2)).

Lemma aua_med_commutes {a b : D} (U1 : AUniversalArrow c F a)
      (U2 : AUniversalArrow c F b) :
  fmap[F] (aua_med U1 U2) ∘ @universal_arrow c F a U1
    ≈ @universal_arrow c F b U2.
Proof.
  exact (unique_property
           (@universal_arrow_universal c F a U1 b (@universal_arrow c F b U2))).
Qed.

Lemma aua_med_unique {a b : D} (U1 : AUniversalArrow c F a)
      (U2 : AUniversalArrow c F b) (g : a ~{D}~> b) :
  fmap[F] g ∘ @universal_arrow c F a U1 ≈ @universal_arrow c F b U2 →
  aua_med U1 U2 ≈ g.
Proof.
  intro Hg.
  exact (uniqueness
           (@universal_arrow_universal c F a U1 b (@universal_arrow c F b U2))
           g Hg).
Qed.

Lemma aua_med_id {a : D} (U1 : AUniversalArrow c F a) : aua_med U1 U1 ≈ id.
Proof.
  apply aua_med_unique.
  rewrite fmap_id.
  apply id_left.
Qed.

Lemma aua_med_comp {a b e : D} (U1 : AUniversalArrow c F a)
      (U2 : AUniversalArrow c F b) (U3 : AUniversalArrow c F e) :
  aua_med U2 U3 ∘ aua_med U1 U2 ≈ aua_med U1 U3.
Proof.
  symmetry.
  apply aua_med_unique.
  rewrite fmap_comp, <- comp_assoc.
  rewrite aua_med_commutes.
  apply aua_med_commutes.
Qed.

Program Definition auniversal_arrow_iso {a b : D} (U1 : AUniversalArrow c F a)
        (U2 : AUniversalArrow c F b) : a ≅ b := {|
  to   := aua_med U1 U2;
  from := aua_med U2 U1
|}.
Next Obligation. rewrite aua_med_comp; apply aua_med_id. Qed.
Next Obligation. rewrite aua_med_comp; apply aua_med_id. Qed.

Lemma auniversal_arrow_iso_unique {a b : D} (U1 : AUniversalArrow c F a)
      (U2 : AUniversalArrow c F b) (v : a ≅ b) :
  fmap[F] (to v) ∘ @universal_arrow c F a U1 ≈ @universal_arrow c F b U2 →
  auniversal_arrow_iso U1 U2 ≈ v.
Proof.
  intro Hv.
  apply to_equiv_implies_iso_equiv; simpl.
  now apply aua_med_unique.
Qed.

Program Definition auniversal_arrow_unique {a b : D}
        (U1 : AUniversalArrow c F a) (U2 : AUniversalArrow c F b) :
  Unique (fun i : a ≅ b =>
            fmap[F] (to i) ∘ @universal_arrow c F a U1
              ≈ @universal_arrow c F b U2) := {|
  unique_obj      := auniversal_arrow_iso U1 U2;
  unique_property := aua_med_commutes U1 U2
|}.
Next Obligation. exact (auniversal_arrow_iso_unique U1 U2 v X). Qed.

End AUniversalArrowUnique.

(** ** The two packagings of a universal arrow are interchangeable / ** 一种通用箭的两种包装是可以互换的 *)

(*
Mac Lane, CWM 2nd ed., §IV.1, Corollary 2 (book p. 85), runs the chain "a
   representation of X(x, G−) at every x" ⟹ "a universal arrow at every x" ⟹
   "a left adjoint".  In this file the last step is
   [AdjunctionFromUniversalArrows], which consumes [UniversalArrow] — the
   comma-initial packaging.  The representability side arrives at the OTHER
   one: [AUniversalArrow] is what
   [Structure/UniversalProperty/Universal/Arrow.v]'s
   [UniversalArrowIsUniversalProperty] is stated over, and what
   [Theory/Universal/Element.v]'s [universal_element_arrow_subsumption]
   reaches from a universal element.

   Both classes have been in this file since it was written, each with its own
   mediator kit ([ua_med] against [aua_med]) and its own uniqueness theorem
   ([universal_arrow_unique] against [auniversal_arrow_unique]) — and nothing
   converted between them, so the chain could not be run end to end.  These
   two passages close that gap.

   They are not a new idea, and the file is careful to say so:
   Theory/Universal/Arrow/Dual.v already carries the COUNIVERSAL twin, as
   [ACouniversalArrow_of_CouniversalArrow] and
   [CouniversalArrow_of_ACouniversalArrow], with the same two strict
   readbacks recorded there ([..._arrow] and [..._obj]).  What was missing
   was the PRIMAL side — the one this file's own two classes need — so what
   follows is the mirror of an existing passage rather than an invention.

   They differ in more than packaging, which is why neither is a coercion.
   [UniversalArrow] HIDES its object: [arrow_obj] is a projection out of an
   initial object of =(c) ↓ F, so the object is whatever the comma category
   supplies.  [AUniversalArrow] takes the object as a PARAMETER, so its type
   mentions it.  The forward passage therefore forgets an index and the
   backward passage invents one — and that asymmetry is exactly why the two
   round trips below are not the same statement.

   The orientations differ too, and each passage pays for it twice:
   [ump_universal_arrows] concludes [h ≈ fmap[F] g ∘ arrow] while
   [universal_arrow_universal] concludes [fmap[F] g ∘ universal_arrow ≈ f], so
   a [symmetry] is spent in each of the two proof fields of [Unique].  The
   file's own remark at [auniversal_arrow_unique] records the same mismatch
   seen from the other side.

--------
Mac Lane，《CWM》第2版，第IV.1节，推论2（书第85页），运行链“在每个x处的X(x, G−)的一个表示”⟹“在每个x处的一个泛箭”⟹“一个左伴随”。在此文件中，最后一步是[AdjunctionFromUniversalArrows]，它消耗[UniversalArrow]——以逗号开头的封装。可表示性方面得到另一个：[AUniversalArrow]是[Structure/UniversalProperty/Universal/Arrow.v]的[UniversalArrowIsUniversalProperty]所陈述的，以及[Theory/Universal/Element.v]的[universal_element_arrow_subsumption]从一个泛元素达到的。

自从这个文件被编写以来，这两个类一直存在，每个类都有自己的中介套件（[ua_med] 对抗 [aua_med]）和自己的唯一性定理（[universal_arrow_unique] 对抗 [auniversal_arrow_unique]）——而且它们之间没有任何转换，所以链无法端到端运行。这两个段落弥补了这个空白。

它们并不是一个新想法，这个文件小心地指出了这一点：
   Theory/Universal/Arrow/Dual.v 已经包含了 COUNIVERSAL 对应项，作为
   [ACouniversalArrow_of_CouniversalArrow] 和
   [CouniversalArrow_of_ACouniversalArrow]，并且记录了相同的两个严格回读（[..._arrow] 和 [..._obj]）。缺少的是 PRIMAL 一侧——也就是这个文件自身两个类所需要的——所以接下来的是现有段落的镜像，而不是发明。

它们的差异不仅在于包装，这就是为什么它们都不是一个强制转换。[UniversalArrow] 隐藏了它的对象：[arrow_obj] 是从初始对象 =(c) ↓ F 投射出来的，因此对象是逗号范畴提供的任何内容。[AUniversalArrow] 将对象作为一个参数，因此它的类型涉及它。因此，正向传递会忘记一个索引，而反向传递会发明一个索引——这种不对称性正是下面两个往返操作不是相同表达的原因。

方向也不同，每个推导都要付出两次代价：
   [ump_universal_arrows] 得出 [h ≈ fmap[F] g ∘ 箭头]，而
   [universal_arrow_universal] 得出 [fmap[F] g ∘ 通用箭头 ≈ f]，因此
   [symmetry] 在 [Unique] 的两个证明域中各花费一次。该文件在 [auniversal_arrow_unique] 的注释记录了从另一侧看到的相同不匹配。
*)

Section UniversalArrowPackaging.

Context {c : C}.
Context {F : D ⟶ C}.

(*
Naming the object and its factorization property is enough to rebuild the
   comma-initial packaging: this is [universal_arrow_from_UMP] fed the class's
   own two fields.

--------
命名对象及其因子分解属性就足以重建逗号起始的封装：这是 [universal_arrow_from_UMP]，提供给类自身的两个字段。
*)
Definition ua_of_aua {a : D} (W : AUniversalArrow c F a) : UniversalArrow c F.
Proof.
  unshelve eapply (universal_arrow_from_UMP c F a (@universal_arrow c F a W)).
  intros d' f.
  unshelve econstructor.
  - exact (unique_obj (@universal_arrow_universal c F a W d' f)).
  - simpl; symmetry.
    exact (unique_property (@universal_arrow_universal c F a W d' f)).
  - simpl; intros v Hv.
    apply (uniqueness (@universal_arrow_universal c F a W d' f)).
    now symmetry.
Defined.

(*
And conversely, the projected object and arrow carry the direct form, with
   the uniqueness clause read off [ump_universal_arrows].

--------
相反，投射出的宾语和箭头携带直接形式，并且唯一性条款从 [ump_universal_arrows] 中读取。
*)
Definition aua_of_ua (W : UniversalArrow c F)
  : AUniversalArrow c F (@arrow_obj c F W).
Proof.
  unshelve econstructor.
  - exact (@arrow c F W).
  - intros d f.
    unshelve econstructor.
    + exact (unique_obj (ump_universal_arrows W f)).
    + simpl; symmetry.
      exact (unique_property (ump_universal_arrows W f)).
    + simpl; intros v Hv.
      apply (uniqueness (ump_universal_arrows W f)).
      now symmetry.
Defined.

(*
STRENGTH, measured strict-first.  The forward passage disturbs neither the
   object nor the arrow: [universal_arrow_from_UMP] builds the comma object as
   ((ttt, a); η), so both projections return what they were given.

--------
强度，严格优先测量。前向传递既不干扰对象也不干扰箭头：[universal_arrow_from_UMP] 将逗号对象构建为 ((ttt, a); η)，因此两个投影都会返回它们接收到的内容。
*)
Example ua_of_aua_obj {a : D} (W : AUniversalArrow c F a) :
  @arrow_obj c F (ua_of_aua W) = a := eq_refl.

Example ua_of_aua_arrow {a : D} (W : AUniversalArrow c F a) :
  @arrow c F (ua_of_aua W) = @universal_arrow c F a W := eq_refl.

(*
Because the object returns on the nose, the round trip STARTING from the
   direct packaging lands back at the SAME index [a] — it typechecks against
   [AUniversalArrow c F a] with no transport — and returns the underlying
   morphism unchanged.

--------
因为对象按预期返回，从直接包装开始的往返会回到相同的索引 [a]——它在没有传输的情况下与 [AUniversalArrow c F a] 进行类型检查——并返回未改变的底层态射。
*)
Example aua_ua_round_arrow {a : D} (W : AUniversalArrow c F a) :
  @universal_arrow c F a (aua_of_ua (ua_of_aua W))
    = @universal_arrow c F a W := eq_refl.

(*
Hence at [AUniversalArrowEquiv] — which compares the underlying morphism
   and nothing else, the uniqueness field carrying no further data — that
   round trip is the identity.

--------
因此，在 [AUniversalArrowEquiv]——它只比较底层的态射，别无其他，唯一性字段不携带额外数据——那个往返过程就是恒等变换。
*)
Lemma aua_ua_round {a : D} (W : AUniversalArrow c F a) :
  aua_of_ua (ua_of_aua W) ≈ W.
Proof. simpl; reflexivity. Qed.

(*
The other composite is weaker, and the difference is real rather than an
   artifact of how it is stated.  [ua_of_aua (aua_of_ua W)] rebuilds the whole
   [Initial] record of the comma category from the UMP, so the [arrow_initial]
   field is a different term and the two [UniversalArrow]s are NOT
   [eq_refl]-equal — pinned as a conversion negative in
   Test/ProbeRepresentability348.v.  What does survive is everything a
   consumer reads: both derived projections return on the nose.  [Setoid]
   there is no help either, [UniversalArrow] carrying none.

--------
另一个复合物较弱，这种差异是真实的，而不是表述方式造成的假象。[ua_of_aua (aua_of_ua W)] 重新构建了 UMP 中逗号范畴的整个 [Initial] 记录，因此 [arrow_initial] 字段是一个不同的术语，而两个 [UniversalArrow] 并不是 [eq_refl] 相等的——在 Test/ProbeRepresentability348.v 中作为转换负值固定。幸存下来的都是消费者能读取的内容：两个导出投影都完全返回。[Setoid] 在那里也无济于事，[UniversalArrow] 未携带任何内容。
*)
Example ua_aua_round_obj (W : UniversalArrow c F) :
  @arrow_obj c F (ua_of_aua (aua_of_ua W)) = @arrow_obj c F W := eq_refl.

Example ua_aua_round_arrow (W : UniversalArrow c F) :
  @arrow c F (ua_of_aua (aua_of_ua W)) = @arrow c F W := eq_refl.

End UniversalArrowPackaging.

End UniversalArrow.
