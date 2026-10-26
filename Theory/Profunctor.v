Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** Profunctors and representable profunctors. / 概函子与可表示概函子。 *)

(*
nLab: https://ncatlab.org/nlab/show/profunctor
   Wikipedia: https://en.wikipedia.org/wiki/Profunctor

   A profunctor from C to D (also called a distributor or a bimodule, written
   C ⇸ D) is a functor

     C^op ∏ D ⟶ Sets,

   contravariant in its first argument and covariant in its second. It sends a
   pair (c, d) to a setoid P(c, d) of “heteromorphisms” from c to d, carrying a
   left action of C and a right action of D by composition. Since hom-sets here
   are setoids, profunctors land in Sets, the category of setoids.

   Following the binding universe discipline of this development, a profunctor
   is kept as a per-pair object: the profunctors C ⇸ D are the objects of the
   functor category [C^op ∏ D, Sets] (Instance/Fun.v), whose morphisms are
   natural transformations and whose object equivalence Prof_Setoid is a natural
   isomorphism (Functor_Setoid, Theory/Functor.v). We never assemble a single
   category of all profunctors between all categories — that would raise the
   universe level — so the bicategory-lite composition and coherence live as
   lemmas in these per-pair functor categories (the Construction/Profunctor
   modules).

--------
nLab: https://ncatlab.org/nlab/show/profunctor
   Wikipedia: https://en.wikipedia.org/wiki/Profunctor

   从 C 到 D 的双函子 (profunctor)（也称 distributor 或 bimodule，写作 C ⇸ D）是函子

     C^op ∏ D ⟶ Sets,

   在第一变元反变、第二变元共变。它把对 (c, d) 送到「异态射」的 setoid P(c, d)，
   携带 C 的左作用与 D 的右作用（经复合）。因此处 hom 集是 setoid，双函子落在 setoid
   范畴 Sets。

   依本开发的绑定宇宙纪律，双函子保持为按对对象：C ⇸ D 的双函子是函子范畴
   [C^op ∏ D, Sets]（Instance/Fun.v）的对象，其态射是自然变换，对象等价 Prof_Setoid
   是自然同构（Functor_Setoid，Theory/Functor.v）。我们从不组装「所有范畴之间所有双函子」
   的单一范畴——那会抬高宇宙层级——故轻量双范畴式复合与连贯作为这些按对函子范畴中的
   引理存在（Construction/Profunctor 模块）。
*)

(*
Where profunctors come from, and what they are for

   nLab: https://ncatlab.org/nlab/show/profunctor
   Paper: Bénabou, “Les distributeurs”, Institut de Mathématique Pure
          et Appliquée, Rapport 33, Univ. Cath. de Louvain (1973)
   Paper: Lawvere, “Metric Spaces, Generalized Logic, and Closed
          Categories”, Rend. Sem. Mat. Fis. Milano 43 (1973)

   The notion, and the several names it travels under, accumulated over
   roughly a decade.  Lawvere presented some of these ideas at
   Oberwolfach in 1966; the surviving record is a set of notes taken by
   Anders Kock of a talk by Lawvere, with a passing mention of
   “generalised functors” (now called profunctors) and their
   “generalised matrix multiplication” (nLab).  Jean Bénabou coined the
   word “profunctor” and later preferred “distributor” (distributeur),
   on the ground that a lax functor into the bicategory of distributors
   is a “distribution on a category”, formally resembling a distribution
   as a generalized function (nLab).  The “bimodule” the header records,
   and the related name “module”, come from the Australian school: for
   one-object V-categories, that is, monoids in V, a profunctor is
   literally a bimodule in the classical algebraic sense (nLab;
   Wikipedia).

   A profunctor is, in one image, a matrix of sets.  Where the header
   presents [Profunctor] C D as the functor type C^op ∏ D ⟶ Sets, the
   reading that motivates it is relational: P(c, d) is a proof-relevant
   relation between the objects of C and those of D, generalizing a
   functor as a relation generalizes a function.  Two such matrices
   compose by generalized matrix multiplication, a coend that traces out
   the shared middle index: (Q ∘ P)(c, e) = ∫^d P(c, d) × Q(d, e).  The
   unit of this composition is the hom-bifunctor, exactly [Id_Profunctor]
   C, that is Hom C.  Categories, profunctors, and natural
   transformations thereby form a bicategory, written Prof (also Mod or
   Dist), the setting in which much of formal and enriched category
   theory is carried out (nLab; Wikipedia).

   The library builds this bicategory not as one category but, keeping
   the binding discipline the header describes, as coherence lemmas over
   the per-pair functor categories.  Composition is [prof_compose] of
   Construction/Profunctor/Compose.v, assembled from the coend integrand
   [prof_integrand] via the coend calculus of Structure/Coend.v and
   Instance/Sets/Coend.v, with unit [prof_id] taken to be Hom C; the
   unitors and associator [prof_unit_left_iso], [prof_unit_right_iso],
   and [prof_assoc_iso] of Construction/Profunctor/Laws.v are the
   co-Yoneda unit laws and the associativity coherence, the last a
   Fubini-style rebracketing of the triple coend; Day convolution
   (Construction/Day.v) reuses the same integrand pattern.

   The header's [Repr_left] and [Repr_right] place ordinary functors
   inside this bicategory.  A functor gives a pair of representable
   profunctors that are adjoint in Prof, so the inclusion Cat ⟶ Prof is
   a proarrow equipment in Wood's sense, and the right-adjoint
   profunctors are exactly the functors into the Cauchy completion of
   the codomain (nLab).  In this file the corresponding statement is
   [representable_adjunction] of Theory/Profunctor/Adjunction.v: F ⊣ U
   holds precisely when [Repr_left] F ≅ [Repr_right] U as profunctors,
   the natural isomorphism recorded by [Prof_Setoid].

   The enriched case is where the notion earns much of its use.  A
   metric space is a category enriched over ([0, ∞], ≥, +), on Lawvere's
   reading (Lawvere 1973); profunctors between such enriched categories
   are the enriched distributors, and weighted colimits over them
   recover Cauchy-sequence completion.  At the discrete extreme a
   profunctor between sets is a span, and dg-bimodules between
   dg-categories are the profunctors appearing in the definition of
   noncommutative motives (nLab).

   Computationally, the profunctor is a familiar type class.  Haskell's
   Profunctor p, with dimap :: (c -> a) -> (b -> d) -> p a b -> p c d, is
   the functorial action of a profunctor Hask^op × Hask ⟶ Set; Milewski
   reads p a b as a proof-relevant relation, a container of values of
   type b keyed by a, and realizes coend composition by an existentially
   quantified datatype that collapses the shared middle variable, with
   the hom-functor as the identity by the ninja-Yoneda lemma (Milewski,
   “Ends and Coends”, 2017; see Theory/Coend/Yoneda.v).  On this footing
   the optics — lenses, prisms, traversals — are polymorphic profunctor
   transformers, composed by function composition and proved equivalent
   to the concrete getter/setter representations (Pickering, Gibbons,
   Wu, “Profunctor Optics: Modular Data Accessors”, Art, Science, and
   Engineering of Programming 1(2):7, 2017).

--------
Profunctor 的来源以及它们的用途

nLab: https://ncatlab.org/nlab/show/profunctor
   论文: Bénabou, 《Les distributeurs》, 纯粹与应用数学研究所, 报告 33, 鲁汶天主教大学 (1973)
   论文: Lawvere, 《度量空间、广义逻辑与闭类》, 米兰数学物理研讨会纪要 43 (1973)

这个概念，以及它所使用的几个不同名称，大约在十年间逐渐积累起来。Lawvere 在 1966 年于 Oberwolfach 会议上展示了其中的一些思想；现存的记录是一份 Anders Kock 针对 Lawvere 演讲所做的笔记，其中偶尔提到了“广义函子”（现在称为 profunctors）及其“广义矩阵乘法”（nLab）。Jean Bénabou 创造了“profunctor”这个词，后来更喜欢用“distributor”（法语原词 distributeur），理由是一个到分配器二范畴的松弛函子是“在范畴上的分布”，形式上类似于作为广义函数的分布（nLab）。标题中提到的“bimodule”，以及相关的“module”名称，来自澳大利亚学派：对于单对象的 V-范畴，即 V 中的幺半群，一个 profunctor 从字面上来说就是经典代数意义上的双模（bimodule）（nLab；Wikipedia）。

一个前函子（profunctor）在一种图像中，可以看作是一个集合矩阵。其中表头将 [Profunctor] C D 呈现为函子类型 C^op ∏ D ⟶ Sets，其背后的动机理解是关系性的：P(c, d) 是 C 类对象与 D 类对象之间的一个证明相关的关系，这种关系推广了函子作为关系推广函数的概念。两个这样的矩阵通过广义矩阵乘法组合，这是一个共端（coend），追踪共享的中间指标：(Q ∘ P)(c, e) = ∫^d P(c, d) × Q(d, e)。这种组合的单位是同构二函子（hom-bifunctor），即 [Id_Profunctor] C，也就是 Hom C。由此，范畴、前函子和自然变换构成一个二范畴，记作 Prof（也称为 Mod 或 Dist），这是进行形式范畴论和丰富范畴论的许多工作所依托的背景（nLab；维基百科）。

该库构建这个双范畴不是作为一个范畴，而是保持头文件所描述的绑定纪律，作为对每对函子范畴的相干引理。组合是 Construction/Profunctor/Compose.v 的 [prof_compose]，由 Structure/Coend.v 和 Instance/Sets/Coend.v 的共端演算从共端积分函数 [prof_integrand] 组装而成，单位元 [prof_id] 取为 Hom C；Construction/Profunctor/Laws.v 中的单元子和结合子 [prof_unit_left_iso]、[prof_unit_right_iso] 和 [prof_assoc_iso] 是共 Yoneda 单元律和结合性相干，最后是三重共端的 Fubini 风格重新加括号；Day 卷积 (Construction/Day.v) 重用了相同的积分函数模式。

头部的 [Repr_left] 和 [Repr_right] 将普通函子置于这个二范畴中。一个函子给出一对在 Prof 中是伴随的可表示副函子，所以包含映射 Cat ⟶ Prof 在 Wood 的意义下是一个前向箭头设备，而右伴随副函子正好是到陪域的 Cauchy 完备的函子（nLab）。在这个文件中，相应的陈述是 Theory/Profunctor/Adjunction.v 的 [representable_adjunction]: F ⊣ U 当且仅当 [Repr_left] F ≅ [Repr_right] U 作为副函子成立，自然同构由 [Prof_Setoid] 记录。

丰富的情形是这个概念发挥其大部分作用的地方。根据Lawvere的理解（Lawvere 1973），度量空间是一个在 ([0, ∞], ≥, +) 上丰富的范畴；在这种丰富范畴之间的预函子就是丰富的分配子，并且在它们上的加权余极限可以恢复柯西序列完备。在离散的极端情况下，集合之间的预函子是一个跨度，而微分分次模之间的微分分次范畴是非交换动机定义中出现的预函子（nLab）。

在计算上，profunctor 是一个熟悉的类型类。Haskell 的 Profunctor p，带有 dimap :: (c -> a) -> (b -> d) -> p a b -> p c d，是 Hask^op × Hask ⟶ Set 的 profunctor 的函子作用；Milewski 将 p a b 视为一个与证明相关的关系，是按 a 键索引的 b 类型值的容器，并通过一个存在量化的数据类型实现 coend 组合，该数据类型压缩了共享的中间变量，同时通过 ninja-Yoneda 引理将 hom-函子作为恒等（Milewski，《Ends and Coends》，2017；见 Theory/Coend/Yoneda.v）。在此基础上，optics——镜头、棱镜、遍历器——是多态 profunctor 变换器，通过函数组合进行组合，并被证明与具体的 getter/setter 表示等价（Pickering, Gibbons, Wu，《Profunctor Optics: Modular Data Accessors》，Art, Science, and Engineering of Programming 1(2):7, 2017）。
*)

(*
   【Profunctor 定义展开】/ Definition walkthrough

   1) 这是什么 / What this is
      前函子 C ⇸ D := (C^op ∏ D) ⟶ Sets —— 「混合方差」的 Set 值双函子。
      Profunctor = Set-valued functor of mixed variance.
      Haskell：Data.Profunctor 的 dimap；复合用 coend（见 Construction/Profunctor）。
      Haskell dimap; composition via coend.

   2) 邻近 / Nearby
      Id_Profunctor = Hom C（单位）
      Repr_left F / Repr_right U —— 函子诱导的可表前函子；F⊣U ⇔ 二者同构
      Prof_Setoid —— 前函子相等 = 自然同构

   阅读：Functor/Hom → 本定义 → Repr_* → Adjunction/Hom；optics 是其计算影。
   Read: Hom → here → Repr_* → adjunction; optics are the FP shadow.
*)

Definition Profunctor (C D : Category) := (C^op ∏ D) ⟶ Sets.

Notation "C ⇸ D" := (Profunctor C D)
  (at level 90, right associativity) : category_scope.

(*
The identity profunctor on C is the hom-bifunctor Hom C : C^op ∏ C ⟶ Sets of
   Functor/Hom.v, viewed at the profunctor type C ⇸ C. On (c, c') it is the
   hom-set C(c, c'), with C acting on both sides by composition; it is the unit
   for profunctor composition (Construction/Profunctor/Compose.v reuses Hom C as
   its prof_id).

--------
C 上的恒等前函子是同构双函子 Hom C : C^op ∏ C ⟶ Sets，从 Functor/Hom.v 中查看，视作前函子类型 C ⇸ C。在 (c, c') 上，它是同态集合 C(c, c')，C 在双方通过复合作用；它是前函子复合的单位（Construction/Profunctor/Compose.v 将 Hom C 重新用作其 prof_id）。
*)
Definition Id_Profunctor (C : Category) : C ⇸ C := Hom C.

(*
Representable profunctors. A functor F : C ⟶ D presents the profunctor

     Repr_left F : C ⇸ D,     (c, d) ↦ D(F c, d),

   covariantly representable on the left, while a functor U : D ⟶ C presents

     Repr_right U : C ⇸ D,    (c, d) ↦ C(c, U d),

   representable on the right. Both are built from the hom-bifunctor of the
   target (resp. source) precomposed with F (resp. U) in one slot and the
   identity in the other, exactly the two composites appearing in the hom-set
   adjunction hom_adj of Adjunction/Hom.v:

     Repr_left F  = Hom D ◯ (F^op ∏⟶ Id),
     Repr_right U = Hom C ◯ (Id^op ∏⟶ U).

   When F ⊣ U (the library orients F : D ⟶ C and U : C ⟶ D), these specialise
   to the two sides Hom C ◯ (F^op ∏⟶ Id) and Hom D ◯ (Id^op ∏⟶ U) of hom_adj,
   so the adjunction is precisely a natural isomorphism Repr_left F ≅ Repr_right
   U in the profunctor category (developed in Theory/Profunctor/Adjunction.v).

--------
可表示的前函子。函子 F : C ⟶ D 表示前函子

Repr_left F : C ⇸ D,     (c, d) ↦ D(F c, d),

在左侧协变可表示，而函子 U : D ⟶ C 表示

Repr_right U : C ⇸ D,    (c, d) ↦ C(c, U d),

可以在右侧表示。两者都是由目标（分别是源）在一个位置上与 F（分别是 U）预组合的同态双函子，以及在另一个位置上的恒等函数构建的，正好是出现在 Adjunction/Hom.v 的同集陪伴 hom_adj 中的两个复合式：

Repr_left F  = 同构 D ◯ (F^op ∏⟶ Id),
Repr_right U = 同构 C ◯ (Id^op ∏⟶ U).

当 F ⊣ U（库将 F : D ⟶ C 和 U : C ⟶ D 定向）时，这些会特化为 hom_adj 的两边 Hom C ◯ (F^op ∏⟶ Id) 和 Hom D ◯ (Id^op ∏⟶ U)，因此该伴随恰好是在拟函子范畴中一个自然同构 Repr_left F ≅ Repr_right U（在 Theory/Profunctor/Adjunction.v 中展开）。
*)

Definition Repr_left {C D : Category} (F : C ⟶ D) : C ⇸ D :=
  Hom D ◯ (F^op ∏⟶ (@Id D)).

Definition Repr_right {C D : Category} (U : D ⟶ C) : C ⇸ D :=
  Hom C ◯ ((@Id C)^op ∏⟶ U).

(*
The equivalence of profunctors C ⇸ D is inherited from the functor category
   [C^op ∏ D, Sets]: two profunctors are equivalent exactly when they are
   naturally isomorphic (Functor_Setoid). This is a plain setoid handle, not a
   registered category instance, keeping the development fully polymorphic.

--------
从函子范畴继承了 C ⇸ D 的前函子等价性：当且仅当前两个前函子自然同构时，它们是等价的（Functor_Setoid）。这是一个普通的集等价处理，而不是已注册的范畴实例，从而保持开发完全多态化。
*)
Definition Prof_Setoid (C D : Category) : Setoid (C ⇸ D) :=
  @Functor_Setoid (C^op ∏ D) Sets.
