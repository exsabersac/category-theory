Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** Representable functors.  / 可表示的函子。*)

(*
nLab: https://ncatlab.org/nlab/show/representable+functor
   Wikipedia: https://en.wikipedia.org/wiki/Representable_functor

   A functor F : C ⟶ Sets is representable when it is naturally isomorphic to
   a covariant hom-functor Hom(A, ─) for some object A of C, the representing
   object. In library notation this natural isomorphism is

       [Hom A,─] ≅ F     (an iso in the functor category [C, Sets]),

   so [represented] below is precisely Wikipedia's pair (A, Φ): [repr_obj] is
   A and [represented] is the natural iso Φ : Hom(A, ─) ⟹ F. By the Yoneda
   lemma such a Φ is determined by a single universal element of F(A), namely
   Φ_A(id A), and the representing object is unique up to (unique) isomorphism;
   the universal-element half is developed in Structure/UniversalProperty.v,
   and the uniqueness half is [repr_unique_iso] below, the τ = id case of the
   induced-arrow correspondence in the second half of this file. A contravariant
   representable G : C^op ⟶ Sets (a presheaf) is instead naturally isomorphic
   to Hom(─, A); see [Hom ─,A] (Curried_CoHom) in Functor/Hom.v. 

--------
nLab: https://ncatlab.org/nlab/show/representable+functor
   Wikipedia: https://en.wikipedia.org/wiki/Representable_functor

   函子 F : C ⟶ Sets 可表 (representable)，当它自然同构于某对象 A ∈ C 的共变
   hom 函子 Hom(A, ─)。库记号中该自然同构为

       [Hom A,─] ≅ F     （函子范畴 [C, Sets] 中的同构），

   故下文 [represented] 恰是 Wikipedia 的对 (A, Φ)：[repr_obj] 是 A，[represented]
   是自然同构 Φ : Hom(A, ─) ⟹ F。由 Yoneda 引理，此类 Φ 由 F(A) 的单个普遍元决定，
   即 Φ_A(id A)，且表示对象在（唯一）同构下唯一；普遍元半边在 Structure/UniversalProperty.v
   开发，唯一性半边是下文 [repr_unique_iso]，即本文件后半诱导箭头对应的 τ = id 情形。
   反变可表 G : C^op ⟶ Sets（预层）则自然同构于 Hom(─, A)；见 Functor/Hom.v 的
   [Hom ─,A]（Curried_CoHom）。 
*)

(*
Wikipedia: “Let C be a locally small category and let Set be the category
   of sets. For each object A of C let Hom(A,–) be the hom functor that maps
   object X to the set Hom(A,X).

   A functor F : C → Set is said to be representable if it is naturally
   isomorphic to Hom(A,–) for some object A of C. A representation of F is a
   pair (A, Φ) where

       Φ : Hom(A,–) → F

   is a natural isomorphism.

   A contravariant functor G from C to Set is the same thing as a functor G :
   Cop → Set and is commonly called a presheaf. A presheaf is representable
   when it is naturally isomorphic to the contravariant hom-functor Hom(–,A)
   for some object A of C.” 

--------
维基百科：“设 C 为局部小范畴，设 Set 为范畴
 套数。 对于 C 的每个对象 A，令 Hom(A,–) 为映射的 hom 函子
 对象 X 到集合 Hom(A,X)。 

函子 F : C → Set 被认为是可表示的，如果它是自然的
 对于 C 的某个对象 A，与 Hom(A,–) 同构。F 的表示是
 对 (A, Φ) 其中

 Φ : Hom(A,–) → F

 是自然同构。 

从 C 到 Set 的逆变函子 G 与函子 G 是一样的：
 警察 → 设定，通常称为预捆。 预轴是有代表性的
 当它与逆变 hom 函子 Hom(–,A) 自然同构时
 对于某个对象 A 或 C。” 
*)

(*
   【Class Representable 语法与字段展开】/ Syntax & field walkthrough

   1) 这是什么 / What this is
      F : C ⟶ Sets「可表」⇔ 存在 A 使 Hom(A,─) ≅ F（函子范畴中的自然同构）。
      F is representable iff naturally iso to a covariant hom-functor.
      Haskell/Yoneda 直觉：F 的行为由「在 A 处的一个普遍元」完全决定。
      Yoneda intuition: F is determined by a universal element of F(A).

   2) 数据字段 / Data
      - repr_obj : C —— 表示对象 A / the representing object A
      - represented : [Hom repr_obj,─] ≅ F —— 自然同构 Φ
        / natural iso Φ : Hom(A,─) ⟹ F in [C, Sets]

   3) 邻近 / Nearby
      下文 repr_unique_iso：表示对象在同构下唯一；反变情形见 Hom ─,A。
      Uniqueness up to iso below; contravariant case → Hom(─,A).

   阅读：Hom 函子 → Yoneda → repr_obj → represented → 唯一性。
   Read: Hom → Yoneda → repr_obj → represented → uniqueness.
*)

Class Representable `(F : C ⟶ Sets) := {
  repr_obj : C;                          (* the representing object A  / 代表对象A*)
  represented : [Hom repr_obj,─] ≅ F     (* natural iso Φ : Hom(A, ─) ⟹ F  / 自然 iso Φ : Hom(A, ─) ⟹ F*)
}.

Coercion Representable_to_obj `(F : C ⟶ Sets) (R : Representable F) : C :=
  @repr_obj _ _ R.

(**
* Representations are functorial in natural transformations

    Book: Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
          Springer 1998, §III.2, Exercise 1, printed p. 62.
    nLab: https://ncatlab.org/nlab/show/representable+functor
    nLab: https://ncatlab.org/nlab/show/Yoneda+embedding

    Mac Lane's exercise reads: given representations ⟨r, ψ⟩ of K and
    ⟨r', ψ'⟩ of K', every natural transformation τ : K ⟹ K' is induced
    by a unique arrow h : r' → r between the representing objects,
    compatibly with the two representations.  The direction of h is the
    exercise's, not a slip: transformations between covariant hom-functors
    run against the arrows, Nat(Hom(r,−), Hom(r',−)) ≅ Hom(r', r), so a
    transformation K ⟹ K' is named by an arrow r' → r.  (When the base
    category is itself an opposite — the presheaf reading, where the objects
    of C are the objects of the ambient C^op — the same statement reads
    covariantly in C; Structure/SubobjectClassifier/Natural.v's
    [Sub_Representable] and Instance/FinSet/Powerset.v's
    [FinPowerset_Representable] are representations of that kind.)

    The exercise is a corollary of the Yoneda lemma in the following exact
    sense.  Conjugating τ by the two representations gives a transformation
    of representable copresheaves,

        σ := ψ'⁻¹ ∘ τ ∘ ψ  :  Hom(r, −) ⟹ Hom(r', −)     ([repr_transport]),

    and the Yoneda embedding, being fully faithful, identifies such σ with
    arrows r' → r.  Fullness produces the arrow — it is σ's value at the
    identity, [repr_induced] — and faithfulness is what makes it unique.
    The two halves are here in elementary form rather than through the
    packaged bijection; see the universe note below for why.

    This is the step at which representability stops being a property of one
    functor and becomes a construction on the category of functors.  The
    correspondence is what makes “the representing object” well defined up
    to a canonical isomorphism (the τ = id case, [repr_unique_iso]), and it
    is why a universal construction is functorial with no extra hypothesis:
    the assignment K ↦ r is the fully faithful functor built in
    Functor/Representable/Functorial.v.

    WHAT IS DELIVERED HERE

    - [repr_transport] and [repr_induced], the conjugated transformation and
      the arrow it names, together with the compatibility predicate
      [ReprCompatible] — Mac Lane's condition stated as an equation in the
      functor category [C, Sets], with [repr_compatible_at] and
      [repr_compatible_of_at] converting it to and from the pointwise form
      (both by [:=], with no tactic: the two are convertible).
    - Existence ([repr_induced_compatible]) and uniqueness
      ([repr_induced_unique]), packaged as
      [repr_induced_universal : ∃! h, ReprCompatible R R' τ h] over
      Lib/Setoid.v's [Unique] at the hom-setoid of C.  [Unique] is what
      Structure/UniversalProperty.v uses for the τ = id case too, though
      there at the setoid of isomorphisms rather than at a hom-setoid.
    - Functoriality: [repr_induced_respects], [repr_induced_id],
      [repr_induced_comp].  Note the composition law's shape,
      h(τ' ∙ τ) ≈ h(τ) ∘ h(τ'): the assignment is contravariant into C, which
      is why the packaged functor in the companion file lands in C^op.
    - [repr_induced_iso], upgrading a natural ISOMORPHISM K ≅ K' to an
      isomorphism of representing objects, and its τ = id specialization
      [repr_unique_iso] with the uniqueness clause
      [repr_unique_iso_universal].
    - [Hom_Representable], the tautological representation of Hom(c, −) by c,
      and [repr_induced_hom], the round trip: the arrow named by
      fmap[Curried_Hom] f is f again.  This is deliberately NOT registered as
      an [Instance]: the tree's [Representable] instances are found by
      resolution (Structure/Cartesian/Closed/Adjunction.v's
      [Curry_Representable_resolves] is solved by resolution alone, and says
      so), so a globally registered tautological instance would add a
      candidate to every such search.  Whether it would in fact divert any
      existing search was not measured; the point is that a [Definition]
      raises the question and an [Instance] would not.

    WHAT IS NOT DELIVERED HERE

    - The cross-link with Structure/UniversalProperty.v's
      [univ_property_unique_up_to_unique_iso], the packaging of K ↦ r as a
      functor, and the concrete witnesses are in
      Functor/Representable/Functorial.v.  They are not here because the
      cross-link needs Structure/UniversalProperty.v, and making the file
      that DECLARES [Representable] depend on it would invert the dependency
      and impose Yoneda plus Construction/Groupoid.v on every consumer of the
      class.  Everything in this section, by contrast, costs no new import at
      all: [Theory.Natural.Transformation], [Construction.Opposite] and
      [Instance.Fun] were already transitive requirements of
      [Category.Functor.Hom].
    - No contravariant restatement.  None is needed and none would be
      separate content: a presheaf is a functor out of C^op, and
      [Curried_CoHom C] IS [Curried_Hom C^op] by definition, so the
      statements below read at C^op are the presheaf statements.
    - No comparison with Theory/Universal/Element.v's [UniversalElement], and
      no claim that τ ↦ h is the ONLY such correspondence; what is proved is
      that h is unique given the compatibility condition.

    A UNIVERSE NOTE, MEASURED

    The issue this development answers suggests routing through
    [Yoneda_Embedding'] (Functor/Hom.v), which packages the hom-bijection
    as an [IsIsomorphism] in Sets.  That route was not taken, because
    [Yoneda_Embedding'] — like [Yoneda_Full] and [Yoneda_Faithful], from which
    it is assembled — is stated over [C : Category@{u u u}], with the object,
    hom and proof universes IDENTIFIED, while the [Representable] class itself
    is over [Category@{o h h}] with the object universe FREE.  That
    identification is an artifact of top-level minimization on an unannotated
    [(C : Category)] binder and not inherent: re-running those two proof
    scripts verbatim inside a section whose category is annotated
    [Category@{uo uh uh}] with [uo < uh] declared succeeds.  Nothing here
    repairs the donors — that is a change to a file with wide blast radius and
    is out of this development's scope — but nothing here inherits their pin
    either.  The whole of this section is over an annotated
    [C : Category@{o h h}], and the one thing the Yoneda bijection was needed
    for, that a transformation of representable copresheaves acts by
    precomposition with its value at the identity, is [hom_transform_precomp]
    below: one naturality square, evaluated at the identity.  Measured per
    constant, the result is that [repr_induced], [repr_induced_universal],
    [repr_unique_iso] and [Hom_Representable] leave the object universe [o]
    unconstrained relative to the hom universe [h] — their constraint blocks
    carry no [o = h] and not even [o <= h] — and the
    difference is guarded in Test/ProbeRepresentableInduced.v, where the
    donors are rejected at a category whose objects sit strictly below its
    homs and these constants are accepted.  (The companion file's
    [ReprObjFunctor] does pick up [o <= h], from packaging the assignment as
    a functor into C^op; still no [o = h].)  [Representable]'s own hom = proof
    identification comes from [Instance/Fun.v]'s [Fun], which takes and
    returns categories of the shape [Category@{a b b}], and [represented] is
    an isomorphism in [C, Sets]; nothing here touches it.  Read constraint
    blocks rather than binders: the companion file's
    [repr_pair_iso_from_is_induced] DISPLAYS its binder as
    [Category@{u u0 u0}] and carries [u = u0] in its constraint set. 

--------
* 表示在自然变换中是函数式的

书：Mac Lane，“工作数学家的类别”，第二版，
 Springer 1998，§III.2，练习 1，印刷页。 62.
 nLab：https://ncatlab.org/nlab/show/representable+functor
 nLab：https://ncatlab.org/nlab/show/Yoneda+embedding

Mac Lane 的练习如下：给定 K 的表示 ⟨r, ψ⟩ 和
 K' 的 ⟨r', ψ'⟩，每个自然变换 τ : K ⟹ K' 都会被诱导
 通过表示对象之间的唯一箭头 h : r' → r，
 与两种表示法兼容。 h 的方向是
 练习，而不是失误：协变 hom 函子之间的转换
 逆着箭头运行，Nat(Hom(r,−), Hom(r',−)) ≅ Hom(r', r)，所以
 变换 K ⟹ K' 由箭头 r' → r 命名。 （当基
 范畴本身就是一个对立面——预习读法，其中物体
 C 的对象是环境 C^op 的对象 - 相同的语句读取
 C 中的协变； 结构/子对象分类器/Natural.v 的
 [Sub_Representable] 和 Instance/FinSet/Powerset.v 的
 [FinPowerset_Representable] 就是此类的代表。）

该练习是米田引理的推论，如下所示：
 感觉。 通过两种表示法将 τ 结合起来可以得到一个变换
 代表性的绳轮，

σ := ψ'⁻¹ ∘ τ ∘ ψ : Hom(r, −) ⟹ Hom(r', −) ([repr_transport]),

完全忠实的米田嵌入将这样的 σ 识别为
 箭头 r' → r。 饱满度产生箭头——它是 σ 在
 身份、[repr_induced]——以及忠诚度使其独一无二。 
这两半在这里是基本形式，而不是通过
 打包双射； 请参阅下面的宇宙注释了解原因。

这是代表性不再是一个人的属性的步骤
 函子并成为函子范畴的构造。 的
 对应性是使“代表对象”得到明确定义的原因
 到规范同构（τ = id 情况，[repr_unique_iso]），并且它
 这就是为什么通用构造是函数式的，没有额外的假设：
 赋值 K ↦ r 是内置的完全忠实函子
 Functor/Representable/Functorial.v.

这里提供什么

- [repr_transport] 和 [repr_induced]，共轭变换和
 它命名的箭头以及兼容性谓词
 [ReprCompatible] — Mac Lane 的条件表示为方程
 函子类别 [C, Sets]、[repr_compatible_at] 和
 [repr_compatible_of_at] 将其与点形式相互转换
 （两者均由 [:=] 提供，无策略：两者可转换）。 - 存在性（[repr_induced_compatible]）和唯一性
 ([repr_induced_unique])，封装为
 [repr_induced_universal : ∃! h, ReprCompatible R R' τ h] 过
 Lib/Setoid.v 的 [Unique] 位于 C 的 hom-setoid 处。 [Unique] 是什么
 不过，Structure/UniversalProperty.v 也用于 τ = id 情况
 位于同构集合而不是同构集合处。 - 功能：[repr_induced_respects]、[repr_induced_id]、
 [repr_induced_comp]。
注意组合律的形状，
 h(τ' ∙ τ) ≈ h(τ) ∘ h(τ')：分配与 C 是逆变的，其中
 这就是伴随文件中的打包函子落在 C^op 中的原因。 - [repr_induced_iso]，将自然同构 K ≅ K' 升级为
 表示对象的同构及其 τ = id 特化
 带有唯一性子句的 [repr_unique_iso]
 [repr_unique_iso_universal]。 - [Hom_Representable]，由 c 表示的 Hom(c, −) 的同义反复表示，
 [repr_induced_hom]，往返：由 命名的箭头
 fmap[Curried_Hom] f 又是 f。 这是故意不注册为
 [Instance]：树的 [Representable] 实例通过以下方式找到
 分辨率（Structure/Cartesian/Closed/Adjunction.v 的
 [Curry_Representable_resolves] 仅通过分辨率来解决，并表示
 so)，因此全局注册的同义反复实例将添加
 每次此类搜索的候选者。
它实际上是否会转移任何
 未测量现有搜索； 重点是 [Definition]
 会提出这个问题，而 [Instance] 则不会。

这里不提供什么

- 与 Structure/UniversalProperty.v 的交叉链接
 [univ_property_unique_up_to_unique_iso]，将 K ↦ r 封装为
 函子，具体见证人在
 Functor/Representable/Functorial.v. 他们不在这里是因为
 交叉链接需要Structure/UniversalProperty.v，并制作文件
 DECLARES [Representable] 依赖它会反转依赖关系
 并将 Yoneda plus Construction/Groupoid.v 强加给每个消费者
 类。 相比之下，本节中的所有内容都不需要花费新的进口成本
 所有：[Theory.Natural.Transformation]、[Construction.Opposite] 和
 [Instance.Fun] 已经是传递要求
 [Category.Functor.Hom]。 
- 没有逆变重述。 不需要，也不会
 单独的内容：presheaf 是 C^op 中的一个函子，并且
 根据定义，[Curried_CoHom C] 是 [Curried_Hom C^op]，因此
 下面在 C^op 处读取的语句是 presheaf 语句。 
- 没有与 Theory/Universal/Element.v 的 [UniversalElement] 进行比较，并且
 没有声称 τ ↦ h 是唯一这样的对应关系； 证明的是
 考虑到兼容性条件，h 是唯一的。

测量的宇宙音符

此开发解决的问题建议通过
 [Yoneda_Embedding'] (Functor/Hom.v)，封装了 hom-bijection
 作为套装中的 [IsIsomorphism]。 没有走那条路，因为
 [Yoneda_Embedding'] — 与 [Yoneda_Full] 和 [Yoneda_Faithful] 类似，来自
 它已组装 — 通过 [C : Category@{u u u}] 与物体进行说明，
 hom 和证明宇宙已识别，而 [Representable] 类本身
 已通过 [Category@{o h h}]，对象宇宙免费。 那
 识别是未注释的顶级最小化的产物
 [(C : Category)] 绑定器并不是固有的：重新运行这两个证明
 在类别已注释的部分中逐字编写脚本
 [Category@{uo uh uh}] 和 [uo < uh] 均宣告成功。 这里什么都没有
 修复捐赠者——这是对具有宽爆炸半径的文件的更改，并且
 超出了此开发的范围 - 但这里没有任何内容继承他们的 pin
 要么。
本节的全部内容都在带注释的内容之上
 [C : Category@{o h h}]，以及米田双射所需要的一件事
 因为，可表示的 copresheaves 的变换通过
 预组合的值是恒等式，是 [hom_transform_precomp]
 下图：一个自然性方块，根据同一性进行评估。 测量每
 常数，结果是 [repr_induced]、[repr_induced_universal]、
 [repr_unique_iso] 和 [Hom_Representable] 离开物体宇宙 [o]
 相对于 hom 宇宙 [h] 不受约束 - 它们的约束块
 没有携带 [o = h]，甚至没有携带 [o <= h] — 而且
 差异在 Test/ProbeRepresentableInduced.v 中受到保护，其中
 捐赠者在其捐赠对象严格低于其捐赠对象的类别中被拒绝
 homs 和这些常量被接受。
（配套文件的
 [ReprObjFunctor] 确实拾取了 [o <= h]，将任务打包为
 C^op 中的函子； 仍然没有 [o = h]。）[Representable] 自己的 hom = 证明
 识别来自 [Instance/Fun.v] 的 [Fun]，它采用和
 返回形状 [Category@{a b b}] 的类别，[represented] 是
 [C, Sets] 中的同构； 这里没有任何东西触及它。 读取约束
 块而不是活页夹：伴随文件的
 [repr_pair_iso_from_is_induced] 将其活页夹显示为
 [Category@{u u0 u0}] 并在其约束集中携带 [u = u0]。 
*)

Section ReprInduced.

Universes o h.
Context (C : Category@{o h h}).

(*
The computational half of the Yoneda lemma for covariant representables,
   in the only form used below: a transformation between representable
   copresheaves acts by PRECOMPOSITION with its value at the identity.  This
   is naturality at g, evaluated at id, with [id_right] cleaning up.  Up to
   the orientation of [≈] it is the same equation as [Yoneda_Full]'s
   [fmap_sur] obligation (Functor/Hom.v), with the same proof,
   re-derived here so that this development does not inherit that constant's
   universe pin. 

--------
协变可表示的米田引理的计算部分，
 下面使用的唯一形式：可表示之间的转换
 copresheaves 通过 PRECOMPOSITION 进行操作，其值为恒等值。 这个
 是 g 处的自然度，在 id 处评估，并使用 [id_right] 进行清理。 最多
 [≈] 的方向与 [Yoneda_Full] 的方程相同
 [fmap_sur]义务（Functor/Hom.v），具有相同的证明，
 在这里重新派生，以便此开发不会继承该常量
 宇宙针。 
*)
Lemma hom_transform_precomp (r r' : C)
  (sigma : [Hom r,─] ~{[C, Sets]}~> [Hom r',─]) (d : C) (g : r ~> d) :
  transform[sigma] d g ≈ g ∘ transform[sigma] r id.
Proof.
  pose proof (@naturality _ _ _ _ sigma r d g id{C}) as N; simpl in N.
  rewrite id_right in N.
  now symmetry.
Qed.

Context {K K' : C ⟶ Sets}.
Context (R : Representable K) (R' : Representable K').

(*
Mac Lane's ψ'⁻¹ ∘ τ ∘ ψ : the transformation τ carried across the two
   representations, where it becomes a transformation of representable
   copresheaves. 

--------
Mac Lane 的 ψ'⁻¹ ∘ τ ∘ ψ ：两者之间进行的变换 τ
 表示，它变成了可表示的转换
 绳轮。 
*)
Definition repr_transport (tau : K ⟹ K')
  : [Hom (@repr_obj _ _ R),─] ~{[C, Sets]}~> [Hom (@repr_obj _ _ R'),─] :=
  from (@represented _ _ R') ∘[Fun] (tau ∘[Fun] to (@represented _ _ R)).

(*
...and the arrow it names, its value at the identity of the representing
   object.  Unfolded: ψ'⁻¹_r (τ_r (ψ_r id)), so the universal element ψ_r id
   of K is where the construction starts. 

--------
...以及它命名的箭头，其值代表代表的身份
 对象。 展开：ψ'⁻1_r(τ_r(ψ_r id))，所以通用元素ψ_r id
 K 是构造开始的地方。 
*)
Definition repr_induced (tau : K ⟹ K') : @repr_obj _ _ R' ~> @repr_obj _ _ R :=
  transform[repr_transport tau] (@repr_obj _ _ R) id.

(*
Mac Lane's compatibility condition, as an equation in [C, Sets]:
   ψ' ∘ Hom(h, −) ≈ τ ∘ ψ.  The sides are written in the mirror of the
   issue's display, which is the same statement since [≈] is symmetric.  Note
   that [fmap[Curried_Hom C]] wants a C^op-arrow, so [h : r' ~> r] enters as
   [op h]. 

--------
Mac Lane 的兼容性条件，如 [C, Sets] 中的方程所示：
 ψ' ∘ Hom(h, −) ≈ τ ∘ ψ。 侧面都写在镜子里
 问题的显示，这是相同的陈述，因为 [≈] 是对称的。 注意事项
 [fmap[Curried_Hom C]] 想要一个 C^op 箭头，因此 [h : r' ~> r] 输入为
 [op h]。 
*)
Definition ReprCompatible (tau : K ⟹ K')
  (hh : @repr_obj _ _ R' ~> @repr_obj _ _ R) : Type :=
  to (@represented _ _ R') ∘[Fun] fmap[Curried_Hom C] (op hh)
    ≈[Fun] tau ∘[Fun] to (@represented _ _ R).

(*
The pointwise reading, in both directions.  Both are supplied by [:=] with
   no tactic: the hom-setoid of [C, Sets] is componentwise and the hom-setoid
   of Sets is pointwise, so the two statements are convertible. 

--------
双向的逐点阅读。 两者均由 [:=] 提供
 无策略：[C, Sets] 的 hom-setoid 是组件式的，并且 hom-setoid
 of Sets 是逐点的，因此这两个语句是可转换的。 
*)
Definition repr_compatible_at {tau hh} (compat : ReprCompatible tau hh)
  (d : C) (g : @repr_obj _ _ R ~> d) :
  transform[to (@represented _ _ R')] d (g ∘ hh)
    ≈ transform[tau] d (transform[to (@represented _ _ R)] d g) := compat d g.

Definition repr_compatible_of_at {tau : K ⟹ K'}
  {hh : @repr_obj _ _ R' ~> @repr_obj _ _ R}
  (at_ : ∀ (d : C) (g : @repr_obj _ _ R ~> d),
       transform[to (@represented _ _ R')] d (g ∘ hh)
         ≈ transform[tau] d (transform[to (@represented _ _ R)] d g)) :
  ReprCompatible tau hh := at_.

(*
Existence: the arrow named by τ is compatible with the two
   representations.  The proof is [hom_transform_precomp] read backwards —
   turning g ∘ h into σ's value at g — followed by ψ' cancelling ψ'⁻¹. 

--------
存在性：由τ命名的箭头与两者兼容
 交涉。 证明是 [hom_transform_precomp] 逆读 —
 将 g ∘ h 转换为 σ 在 g 处的值 — 随后用 ψ' 抵消 ψ'⁻¹。 
*)
Lemma repr_induced_compatible (tau : K ⟹ K') :
  ReprCompatible tau (repr_induced tau).
Proof.
  apply repr_compatible_of_at; intros d g.
  unfold repr_induced; simpl.
  rewrite <- (hom_transform_precomp _ _ (repr_transport tau) d g).
  pose proof (iso_to_from (@represented _ _ R') d
    (transform[tau] d (transform[to (@represented _ _ R)] d g))) as HH;
    simpl in HH; rewrite HH.
  srewrite (@fmap_id _ _ K' d); reflexivity.
Qed.

(*
Uniqueness: a compatible arrow is determined by the condition at the one
   place it can be probed, the identity of the representing object. 

--------
唯一性：兼容箭头由该箭头处的条件决定
 可以探测到代表对象的身份。 
*)
Lemma repr_induced_unique (tau : K ⟹ K') hh :
  ReprCompatible tau hh → hh ≈ repr_induced tau.
Proof.
  intro compat.
  pose proof (repr_compatible_at compat (@repr_obj _ _ R) id) as E; simpl in E.
  unfold repr_induced; simpl.
  rewrite <- E.
  pose proof (iso_from_to (@represented _ _ R') (@repr_obj _ _ R)
                (id{C} ∘ hh)) as HH; simpl in HH; rewrite HH.
  now rewrite !id_left.
Qed.

(*
The exercise as one statement: a unique compatible arrow between the
   representing objects. 

--------
该练习作为一个陈述：在
 代表对象。 
*)
Program Definition repr_induced_universal (tau : K ⟹ K') :
  @Unique _ (@homset C (@repr_obj _ _ R') (@repr_obj _ _ R))
          (ReprCompatible tau) := {|
  unique_obj := repr_induced tau;
  unique_property := repr_induced_compatible tau
|}.
Next Obligation. symmetry; now apply repr_induced_unique. Qed.

Lemma repr_induced_respects (tau tau' : K ⟹ K') :
  tau ≈ tau' → repr_induced tau ≈ repr_induced tau'.
Proof.
  intro E; unfold repr_induced; simpl.
  apply proper_morphism, (E (@repr_obj _ _ R) _).
Qed.

End ReprInduced.

Arguments repr_transport {C K K'} R R' tau.
Arguments repr_induced {C K K'} R R' tau.
Arguments ReprCompatible {C K K'} R R' tau hh.
Arguments repr_compatible_at {C K K' R R' tau hh} compat d g.
Arguments repr_compatible_of_at {C K K' R R' tau hh} at_.
Arguments repr_induced_compatible {C K K'} R R' tau.
Arguments repr_induced_unique {C K K'} R R' tau hh.
Arguments repr_induced_universal {C K K'} R R' tau.
Arguments repr_induced_respects {C K K'} R R' tau tau'.

(** ** Functoriality  / ** 功能性*)

Section ReprInducedLaws.

Universes o h.
Context (C : Category@{o h h}).
Context {K K' K'' : C ⟶ Sets}.
Context (R : Representable K) (R' : Representable K') (R'' : Representable K'').

(*
The identity transformation names the identity arrow.  [nat_id]'s component
   is [fmap[K] id] rather than [id] (Theory/Natural/Transformation.v), so
   [fmap_id] is spent once here and once in [repr_induced_compatible]. 

--------
恒等变换命名为恒等箭头。 [nat_id] 的组件
 是 [fmap[K] id] 而不是 [id] (Theory/Natural/Transformation.v)，所以
 [fmap_id] 在这里使用一次，在 [repr_induced_compatible] 中使用一次。 
*)
Lemma repr_induced_id : repr_induced R R nat_id ≈ id.
Proof.
  unfold repr_induced, repr_transport; simpl.
  srewrite (@fmap_id _ _ K (@repr_obj _ _ R)).
  pose proof (iso_from_to (@represented _ _ R) (@repr_obj _ _ R) id{C})
    as HH; simpl in HH; rewrite HH.
  now rewrite id_left.
Qed.

(*
...and a composite names the composite, in the opposite order: the
   assignment is contravariant into C.  Proved by uniqueness, not by
   unfolding: the composite arrow is shown compatible, and then it IS the
   induced one. 

--------
...并且复合材料以相反的顺序命名复合材料：
 赋值与 C 是逆变的。通过唯一性证明，而不是通过
 展开：复合箭头显示为兼容，然后它就是
 诱发一。 
*)
Lemma repr_induced_comp (tau : K ⟹ K') (tau' : K' ⟹ K'') :
  repr_induced R R'' (tau' ∙ tau)
    ≈ repr_induced R R' tau ∘ repr_induced R' R'' tau'.
Proof.
  symmetry; apply repr_induced_unique.
  apply repr_compatible_of_at; intros d g; simpl.
  rewrite comp_assoc.
  rewrite (repr_compatible_at (repr_induced_compatible R' R'' tau') d _).
  now rewrite (repr_compatible_at (repr_induced_compatible R R' tau) d g).
Qed.

End ReprInducedLaws.

Arguments repr_induced_id {C K} R.
Arguments repr_induced_comp {C K K' K''} R R' R'' tau tau'.

(** ** Isomorphisms, and Mac Lane's τ = id case  / ** 同构，以及 Mac Lane 的 τ = id case*)

Section ReprInducedIso.

Universes o h.
Context (C : Category@{o h h}).
Context {K K' : C ⟶ Sets}.
Context (R : Representable K) (R' : Representable K').

(*
A natural isomorphism of represented functors induces an isomorphism of
   representing objects; both triangle laws are the composition law followed
   by the identity law. 

--------
所表示函子的自然同构会导致以下同构
 代表物体； 两个三角形定律都是遵循的合成定律
 由身份法。 
*)
Program Definition repr_induced_iso (i : K ≅[Fun] K')
  : @repr_obj _ _ R' ≅ @repr_obj _ _ R := {|
  to   := repr_induced R R' (to i);
  from := repr_induced R' R (from i)
|}.
Next Obligation.
  rewrite <- repr_induced_comp.
  rewrite (repr_induced_respects R R (from i ∙ to i) nat_id).
  - now apply repr_induced_id.
  - apply (iso_from_to i).
Qed.
Next Obligation.
  rewrite <- repr_induced_comp.
  rewrite (repr_induced_respects R' R' (to i ∙ from i) nat_id).
  - now apply repr_induced_id.
  - apply (iso_to_from i).
Qed.

End ReprInducedIso.

Arguments repr_induced_iso {C K K'} R R' i.

Section ReprUnique.

Universes o h.
Context (C : Category@{o h h}).
Context {K : C ⟶ Sets}.
Context (R R' : Representable K).

(*
Mac Lane's τ = id case: two representations of ONE functor have
   canonically isomorphic representing objects.  This is [repr_induced_iso]
   at the identity isomorphism; no separate argument. 

--------
Mac Lane 的 τ = id 情况：一个函子的两种表示有
 规范同构表示对象。 这是 [repr_induced_iso]
 在恒等同构处； 没有单独的论据。 
*)
Definition repr_unique_iso : @repr_obj _ _ R' ≅ @repr_obj _ _ R :=
  repr_induced_iso R R' iso_id.

(*
...and the isomorphism's forward leg is the unique compatible arrow, which
   is the clause a bare [≅] does not carry.  Uniqueness is inherited from
   [repr_induced_universal]; it is stated separately because the isomorphism
   is what a consumer names. 

--------
...而同构的前腿是独特的兼容箭头，它
 是裸 [≅] 不携带的子句。 独特性是继承自
 [repr_induced_universal]； 单独说明是因为同构
 是消费者的名字。 
*)
Program Definition repr_unique_iso_universal :
  @Unique _ (@homset C (@repr_obj _ _ R') (@repr_obj _ _ R))
          (ReprCompatible R R' nat_id) := {|
  unique_obj := to repr_unique_iso;
  unique_property := repr_induced_compatible R R' nat_id
|}.
Next Obligation. symmetry; now apply repr_induced_unique. Qed.

End ReprUnique.

Arguments repr_unique_iso {C K} R R'.
Arguments repr_unique_iso_universal {C K} R R'.

(** ** The tautological representation, and the round trip  / ** 同义反复表示和往返*)

Section TautologicalRepresentation.

Universes o h.
Context (C : Category@{o h h}).

(*
Hom(c, −) represents itself, by the identity isomorphism.  Deliberately a
   plain [Definition] and not an [Instance]: see the header. 

--------
Hom(c, −) 通过恒等同构表示自身。 故意一个
 普通 [Definition] 而不是 [Instance]：请参阅标题。 
*)
Definition Hom_Representable (c : C) : Representable ([Hom c,─]) := {|
  repr_obj := c;
  represented := iso_id
|}.

(*
Against those representations the correspondence is the identity on
   arrows: the arrow named by Hom(f, −) is f.  Both sides of Mac Lane's
   bijection are visible here, and the residue is three identity laws. 

--------
与这些陈述相对应的是对应的身份
 arrows：由 Hom(f, −) 命名的箭头为 f。 麦克巷两侧
 这里可以看到双射，剩下的是三个恒等律。 
*)
Lemma repr_induced_hom (c c' : C) (f : c' ~> c) :
  repr_induced (Hom_Representable c) (Hom_Representable c')
    (fmap[Curried_Hom C] (op f)) ≈ f.
Proof.
  unfold repr_induced, repr_transport; simpl; unfold op.
  now rewrite !id_left.
Qed.

End TautologicalRepresentation.

Arguments Hom_Representable {C} c.
Arguments repr_induced_hom {C} c c' f.
