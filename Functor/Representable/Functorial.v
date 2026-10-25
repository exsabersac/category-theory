Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Deloop.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Yoneda.
Require Import Category.Functor.Hom.Yoneda.Iso.
Require Import Category.Functor.Hom.Yoneda.Natural.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Structure.UniversalProperty.

Generalizable All Variables.

(**
* Taking the representing object, as a functor

    Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
          Springer 1998, §III.2, Exercise 1, printed p. 62.
    nLab: https://ncatlab.org/nlab/show/representable+functor

    Functor/Representable.v proves Mac Lane's exercise: a natural
    transformation τ : K ⟹ K' between represented functors is named by a
    unique arrow [repr_induced R R' τ : repr_obj R' ~> repr_obj R] compatible
    with the two representations.  This file collects the three things that
    statement makes available and that its own file cannot host.

    (1) THE COMPARISON WITH THE YONEDA EMBEDDING.  The issue this development
    answers suggests obtaining the arrow by transporting τ to ψ'⁻¹ ∘ τ ∘ ψ and
    inverting the hom-bijection [Yoneda_Embedding'] (Functor/Hom.v).
    Functor/Representable.v does the first half — that is [repr_transport] —
    and then names the arrow directly rather than through the packaged
    bijection, for the universe reason recorded in that file's header.  The
    two agree: [repr_induced_is_yoneda_transpose] is [eq_refl], so wherever
    both are formable they are the same TERM, not merely equivalent arrows.

    (2) THE CROSS-LINK WITH Structure/UniversalProperty.v.  That file's
    [univ_property_unique_up_to_unique_iso] is the τ = id case for
    objects satisfying a universal PREDICATE, and its [univ_property_unique]
 is the underlying uniqueness.  Before this file there was no
    passage in either direction between [IsUniversalProperty] and
    [Representable] anywhere in the tree — before this one the two names
    occurred together in only two files, Structure/UniversalProperty.v (where
    "representable" is a URL and a paragraph of prose) and
    Structure/Cartesian/Closed/Adjunction.v
    (a comment, now that it has been amended to point here) — so the
    cross-link is a construction and not a citation, and the absence claim is
    scoped to what was searched: the two class NAMES, over every [.v] file in
    the tree.  It is a short one: [Representable_of_UnivProperty] is a record
    literal, and [UnivProperty_of_Representable] takes the predicate
    "c represents F" and the identity isomorphism.  With it,
    [univ_property_iso_from_is_induced] identifies the backward leg of that
    proposition's isomorphism with [repr_induced] at the identity
    transformation.  The identification factors through [repr_pair_iso]
    (Functor/Hom/Yoneda/Iso.v), which is what [univ_property_unique]
    consumes: [up_unique_obj_is_repr_pair_iso] records by [eq_refl] that the
    proposition's [unique_obj] IS that isomorphism, and
    [repr_pair_iso_from_is_induced] compares it with the induced arrow.

    (3) THE FUNCTOR.  [repr_induced_id] and [repr_induced_comp] say that
    K ↦ repr_obj is functorial, contravariantly into C.  [ReprCat C] is the
    category of functors C ⟶ Sets equipped with a chosen representation — the
    full subcategory of [C, Sets] cut out by [Representable], built with
    Construction/Subcategory.v's [Sub], so its objects are pairs ⟨K, R⟩ and
    its morphisms are natural transformations of the underlying functors
    (formally, paired with a trivial membership witness that the hom-setoid
    ignores, [Sub] comparing morphisms by first projection) —
    and [ReprObjFunctor C : ReprCat C ⟶ C^op] is the assignment.  It is FULL
    ([ReprObj_Full]) and FAITHFUL ([ReprObj_Faithful]): fullness is Mac Lane's
    correspondence run backwards, an arrow h being carried to
    ψ' ∘ Hom(h, −) ∘ ψ⁻¹, and faithfulness is the compatibility condition
    probed through the surjectivity of ψ.  That is the Yoneda embedding read
    from the other side; the equivalence with C^op that the slogan suggests is
    NOT assembled here — see below.

    WHAT IS DELIVERED

    - [repr_induced_is_yoneda_transpose] ([eq_refl]).
    - [repr_of_representation], [Representable_of_UnivProperty],
      [UnivProperty_of_Representable]; [up_unique_obj_is_repr_pair_iso]
      ([eq_refl]); [repr_pair_iso_from_is_induced],
      [repr_pair_iso_to_is_induced], [univ_property_iso_from_is_induced].
    - [ReprSubcat], [ReprCat], [ReprObjFunctor], [ReprObj_Full],
      [ReprObj_Faithful].
    - Non-vacuity over the delooping of (ℕ, +): a non-identity τ whose induced
      arrow is a non-identity too, in two forms — against the tautological
      representations of Functor/Representable.v ([wit_tau], where the induced
      arrow COMPUTES, [wit_induced_computes] being [eq_refl]) and against the
      in-tree [YoEvalAt_Representable] (Functor/Hom/Yoneda/Natural.v),
      where it does not compute on the nose and the agreement is [≈].

    WHAT IS NOT DELIVERED

    - No claim that the passages of (2) are mutually inverse.  They are not
      even composable in general: [Representable_of_UnivProperty] needs a
      point of the predicate, and going the other way replaces the predicate
      by "c represents F", which is not the predicate one started with.  What
      is proved is that each passage exists and that the τ = id isomorphisms
      agree.
    - No essential-surjectivity or equivalence claim for [ReprObjFunctor].
      Full and faithful are proved, and [Hom_Representable] does exhibit, for
      every object c of C, an object of [ReprCat C] whose representing object
      is c on the nose — but the essential-surjectivity witness is not
      packaged, the equivalence is not assembled, and no
      [EquivalenceOfCategories] is claimed.
    - No repleteness or 2-categorical statement about [ReprCat], and no
      comparison with Construction/Elements.v or with
      Theory/Universal/Element.v's [UniversalElement].  [ReprObj_Full] and
      [ReprObj_Faithful] are plain definitions rather than registered
      instances, so a consumer wanting [FullyFaithful] must supply them by
      name; that follows the header's reason for [Hom_Representable] being a
      [Definition] and keeps resolution unperturbed.
    - The witness's category is one-object, so "the induced arrow is not an
      identity" is a statement about an ENDOmorphism.  No witness with two
      DISTINCT representing objects and a non-identity induced arrow is given
      here; at distinct objects "is not an identity" is not a well-typed
      claim, and what would replace it — that the correspondence separates
      transformations — is [ReprObj_Faithful], proved in general.

    A UNIVERSE NOTE, MEASURED PER CONSTANT

    Functor/Representable.v's constants leave the object universe
    unconstrained relative to the hom universe.  An audit corrected an
    earlier draft of this note, which blamed section (2) as a whole: the
    pin follows [repr_pair_iso], NOT the section boundary.  Measured per
    constant, the partition is

      - FREE (no [o = h], no [o <= h]): [repr_of_representation],
        [Representable_of_UnivProperty], [UnivProperty_of_Representable] —
        i.e. the passage between the two classes, which consumes
        [repr_pair_iso] nowhere — together with [ReprSubcat] and [ReprCat];
      - [o <= h] with no [o = h]: [ReprObjFunctor], [ReprObj_Full],
        [ReprObj_Faithful], the price of packaging the assignment as a
        functor into C^op;
      - PINNED at [o = h]: exactly the four constants that consume
        [repr_pair_iso] — [repr_pair_iso_from_is_induced],
        [repr_pair_iso_to_is_induced], [up_unique_obj_is_repr_pair_iso],
        [univ_property_iso_from_is_induced] — plus
        [repr_induced_is_yoneda_transpose], which NAMES [Yoneda_Embedding']
        in its own statement.

    The inherited pin is invisible in the printed BINDER —
    [repr_pair_iso_from_is_induced] displays as [∀ (C : Category@{u u0 u0})]
    — and appears only in the constraint block, as [u = u0].  Section (1) is pinned by
    construction and deliberately so — [repr_induced_is_yoneda_transpose]
    NAMES [Yoneda_Embedding'] in its own statement, so it can only be stated
    where that constant is formable, and its category is left unannotated for
    that reason.  Both the pins and the freedom are guarded in
    Test/ProbeRepresentableInduced.v. 

--------
* 将表示对象作为函子

书：Mac Lane，“工作数学家的类别”，第二版，
 Springer 1998，§III.2，练习 1，印刷页。 62.
 nLab：https://ncatlab.org/nlab/show/representable+functor

Functor/Representable.v 证明了 Mac Lane 的练习：自然的
 表示函子之间的变换 τ : K ⟹ K' 由 a 命名
 兼容独特的箭头 [repr_induced R R' τ : repr_obj R' ~> repr_obj R]
 与两个表示。 该文件收集了三件事
 声明使其可用，并且其自己的文件无法托管。

(1)与米田嵌入的比较。 这个问题的发展
 答案建议通过将 τ 传输到 ψ'⁻¹ ∘ τ ∘ ψ 来获得箭头，并且
 反转 hom 双射 [Yoneda_Embedding'] (Functor/Hom.v)。 
Functor/Representable.v 完成前半部分 — 即 [repr_transport] —
 然后直接命名箭头而不是通过打包的
 双射，出于该文件头中记录的宇宙原因。 的
 两个同意：[repr_induced_is_yoneda_transpose] 是 [eq_refl]，所以无论在哪里
 两者都是可形成的，它们是相同的术语，而不仅仅是等效的箭头。

(2) 与 Structure/UniversalProperty.v 的交叉链接。 那个文件的
 [univ_property_unique_up_to_unique_iso] 是 τ = id 的情况
 满足通用 PREDICATE 的对象及其 [univ_property_unique]
 是潜在的独特性。 在这个文件之前没有
 [IsUniversalProperty] 和之间任一方向的通道
 [Representable] 树中的任何位置 — 在此之前的两个名称
 仅在两个文件 Structure/UniversalProperty.v 中同时出现（其中
 “可代表”是一个 URL 和一段散文）以及
 结构/笛卡尔/闭合/附加.v
 （一条评论，现在已经修改为指向这里） - 所以
 交叉链接是一种构造，而不是引用，并且缺席声明是
 范围为搜索内容：两个类名称，在每个 [.v] 文件中
 树。
这是一个简短的：[Representable_of_UnivProperty] 是一个记录
 文字，[UnivProperty_of_Representable] 采用谓词
 “c代表F”，恒等同构。 有了它，
 [univ_property_iso_from_is_induced] 识别该条的后腿
 命题与 [repr_induced] 在恒等式上的同构
 转变。 通过 [repr_pair_iso] 识别因素
 (Functor/Hom/Yoneda/Iso.v)，这就是 [univ_property_unique]
 消耗：[up_unique_obj_is_repr_pair_iso] 由 [eq_refl] 记录
 命题的 [unique_obj] IS 即同构，并且
 [repr_pair_iso_from_is_induced] 将其与诱导箭头进行比较。

(3)函子。 [repr_induced_id] 和 [repr_induced_comp] 表示
 K ↦ repr_obj 是函子，与 C 逆变。 [ReprCat C] 是
 函子类别 C ⟶ 配备有选定表示的集合 —
 [C, Sets] 的完整子类别，由 [Representable] 剪裁而成，内置
 Construction/Subcategory.v 的 [Sub]，因此它的对象是对 ⟨K、R⟩ 和
 它的态射是底层函子的自然变换
 （正式地，与一个微不足道的成员证人配对，即 hom-setoid
 忽略，[Sub] 通过第一次投影比较态射） —
 [ReprObjFunctor C : ReprCat C ⟶ C^op] 是作业。 已满
 ([ReprObj_Full]) 和 FAITHFUL ([ReprObj_Faithful])：饱满度是 Mac Lane 的
 对应关系向后运行，箭头 h 被带到
 ψ' ∘ Hom(h, −) ∘ ψ⁻¹，忠实度为相容条件
 通过 ψ 的满射性进行探测。 这就是米田嵌入读
 从另一边； 口号暗示的与 C^op 的等价是
 此处未组装 - 见下文。

交付了什么

- [repr_induced_is_yoneda_transpose] ([eq_refl])。 
- [repr_of_representation]、[Representable_of_UnivProperty]、
 [UnivProperty_of_Representable]； 保护35X
 （[eq_refl]）； [repr_pair_iso_from_is_induced]，
 [repr_pair_iso_to_is_induced]、[univ_property_iso_from_is_induced]。 
- [ReprSubcat]、[ReprCat]、[ReprObjFunctor]、[ReprObj_Full]、
 [ReprObj_Faithful]。 
- (ℕ, +) 解环上的非空性：一个非恒等式 τ，其诱导
 箭头也是一种非同一性，有两种形式——反对同义反复
 Functor/Representable.v 的表示（[wit_tau]，其中诱导
 箭头计算，[wit_induced_computes] 为 [eq_refl]）并针对
 树内 [YoEvalAt_Representable] (Functor/Hom/Yoneda/Natural.v),
 它不在鼻子上计算，协议是 [≈]。

未交付的内容

- 没有声称(2) 的段落是互逆的。 他们不是
 甚至一般可组合：[Representable_of_UnivProperty] 需要
 谓词的点，反之则替换谓词
 “c 代表 F”，这不是开头的谓词。 什么
 证明了每一段都存在并且 τ = id 同构
 同意。 - [ReprObjFunctor] 没有本质满射性或等效性声明。 充分和忠实得到了证明，[Hom_Representable] 确实展示了，对于
 C 的每个对象 c，[ReprCat C] 的对象，其代表对象
 鼻子上是c——但本质主观见证人不是
 封装后，等价未组装，且无
 [EquivalenceOfCategories] 已被索赔。
- 没有关于 [ReprCat] 的完整性或 2 类声明，并且没有
 与 Construction/Elements.v 或与
 Theory/Universal/Element.v 的 [UniversalElement]。 [ReprObj_Full] 和
 [ReprObj_Faithful] 是简单定义而不是注册
 实例，因此想要 [FullyFaithful] 的消费者必须通过以下方式提供它们：
 姓名； 遵循标头的 [Hom_Representable] 的原因
 [Definition] 并保持分辨率不受干扰。 - 证人的类别是单一对象，因此“诱导箭头不是一个
 同一性”是关于内同态的陈述。 没有证人两人
 给出了表示对象的 DISTINCT 和非同一性诱导箭头
 在这里； 在不同的对象上“不是身份”不是类型良好的
 声称，以及替代它的东西——信件分开
 转换 — 是 [ReprObj_Faithful]，已得到一般证明。

通用注释，按常数测量

Functor/Representable.v 的常量离开对象宇宙
 相对于本宇宙不受约束。 审计更正了
 本说明的早期草案，将第 (2) 部分作为一个整体归咎于：
 引脚遵循 [repr_pair_iso]，而不是部分边界。 测量每
 常数，分区为

- 免费（无 [o = h]、无 [o <= h]）：[repr_of_representation]、
 [Representable_of_UnivProperty]、[UnivProperty_of_Representable] —
 即两个类之间的传递，这消耗了
 [repr_pair_iso] 不存在 — 与 [ReprSubcat] 和 [ReprCat] 一起；
 - [o <= h]，不带 [o = h]：[ReprObjFunctor]、[ReprObj_Full]、
 [ReprObj_Faithful]，将作业打包为
 函子进入 C^op；
 - 固定在 [o = h]：正是消耗的四个常量
 XPTECT78X — XPTECT79X，
 [repr_pair_iso_to_is_induced]、[up_unique_obj_is_repr_pair_iso]、
 [univ_property_iso_from_is_induced] — 加
 [repr_induced_is_yoneda_transpose]，命名为 [Yoneda_Embedding']
 在其自己的声明中。

继承的引脚在打印的 BINDER 中是不可见的 —
 [repr_pair_iso_from_is_induced] 显示为 [∀ (C : Category@{u u0 u0})]
 - 并且仅出现在约束块中，如 [u = u0]。 第 (1) 节固定为
 构造并故意如此 — [repr_induced_is_yoneda_transpose]
 NAMES [Yoneda_Embedding']在自己的声明中，所以只能说明
 其中该常量是可形成的，并且其类别未注释
 那个原因。 销钉和自由都受到保护
 测试/探针RepresentableInduced.v。 
*)

(** ** The comparison with the Yoneda embedding  / ** 与米田嵌入的比较*)

Section YonedaTranspose.

Context (C : Category).
Context {K K' : C ⟶ Sets}.
Context (R : Representable K) (R' : Representable K').

(*
The issue's suggested route — transport τ across the representations, then
   invert the hom-bijection — produces the same TERM as [repr_induced], not
   merely an equivalent arrow.  [eq_refl] is the convertibility exception:
   [Yoneda_Embedding']'s two-sided inverse is [Yoneda_Full]'s [prefmap],
   which is evaluation at the identity, which is what [repr_induced] is. 

--------
该问题的建议路线——跨表征传输 τ，然后
 反转 hom-bijection — 产生与 [repr_induced] 相同的 TERM，而不是
 只是一个等效的箭头。 [eq_refl] 是可转换性例外：
 [Yoneda_Embedding']的双面逆是[Yoneda_Full]的[prefmap]，
 这是对身份的评估，这就是 [repr_induced]。 
*)
Definition repr_induced_is_yoneda_transpose (tau : K ⟹ K') :
  @two_sided_inverse _ _ _ _
    (Yoneda_Embedding' C (@repr_obj _ _ R) (@repr_obj _ _ R'))
    (repr_transport R R' tau)
  = repr_induced R R' tau := eq_refl.

End YonedaTranspose.

(** ** The passage between [IsUniversalProperty] and [Representable]  / ** [IsUniversalProperty] 和 [Representable] 之间的通道*)

Section Bridge.

Universes o h.
Context (C : Category@{o h h}).

(*
A representation, packaged.  Used below to name the two representations a
   [repr_pair_iso] is built from. 

--------
代表，包装。 下面用于将这两个表示命名为a
 [repr_pair_iso] 是从 构建的。 
*)
Definition repr_of_representation {F : C ⟶ Sets} (c : C)
  (b : [Hom c,─] ≅[Fun] F) : Representable F := {|
  repr_obj := c;
  represented := b
|}.

Context (P : C → Type) (eqP : ∀ c, Setoid (P c)).

(*
An object satisfying a universal property represents the functor that
   property is the representability of.  [repr_equivalence] carries the proof
   of [P c] to the representation; nothing else is needed. 

--------
满足通用属性的对象表示函子
 财产是事物的代表性。 [repr_equivalence] 提供证据
 [P c] 的表示； 不需要其他任何东西。 
*)
Definition Representable_of_UnivProperty (H : IsUniversalProperty C P eqP)
  (c : C) (t : P c) : Representable (@repr_functor C P eqP H) := {|
  repr_obj := c;
  represented := to (repr_equivalence c) t
|}.

End Bridge.

Arguments repr_of_representation {C F} c b.
Arguments Representable_of_UnivProperty {C P eqP} H c t.

Section BridgeBack.

Universes o h.
Context (C : Category@{o h h}).
Context (F : C ⟶ Sets).

(*
...and conversely, representability of a FIXED functor is itself a
   universal property, of the predicate "c represents F".  The equivalence
   between proofs of the predicate and representations is the identity, which
   is the honest content of the direction: the class [IsUniversalProperty] is
   representability with the predicate left free, so instantiating the
   predicate at representability is where it becomes a tautology. 

--------
...相反，FIXED 函子的可表示性本身就是
 谓词“c 代表 F”的普遍性质。 等价性
 谓词证明和表示之间是恒等式，
 是方向的诚实内容：[IsUniversalProperty] 类是
 谓词保持自由的可表示性，因此实例化
 可表示性的谓词是它成为同义反复的地方。 
*)
Program Definition UnivProperty_of_Representable
  : IsUniversalProperty C (fun c => @Isomorphism ([C, Sets]) [Hom c,─] F)
      (fun c => iso_setoid) := {|
  repr_functor := F;
  repr_equivalence := fun c => iso_id
|}.

End BridgeBack.

Arguments UnivProperty_of_Representable {C} F.

(** ** The τ = id case, cross-linked  / ** τ = id 情况下，交联*)

Section CrossLink.

Context (C : Category).
Context {F : C ⟶ Sets}.
Context {c v : C}.
Context (b1 : [Hom c,─] ≅[Fun] F) (b2 : [Hom v,─] ≅[Fun] F).

(*
[repr_pair_iso] (Functor/Hom/Yoneda/Iso.v) is the isomorphism of
   representing objects that Structure/UniversalProperty.v consumes.  Its two
   legs are the two induced arrows at the identity transformation.  They are
   NOT the same term — [nat_id]'s component is [fmap[F] id] rather than [id],
   so the induced arrow carries one application of [fmap] that
   [repr_pair_iso]'s leg does not — and the [eq_refl] negative is pinned in
   Test/ProbeRepresentableInduced.v. 

--------
[repr_pair_iso] (Functor/Hom/Yoneda/Iso.v) 是以下同构
 表示 Structure/UniversalProperty.v 使用的对象。 它的两个
 腿是身份转换时的两个诱导箭头。 他们是
 不是同一个术语 — [nat_id] 的组件是 [fmap[F] id] 而不是 [id]，
 因此诱导箭头带有 [fmap] 的一项应用：
 [repr_pair_iso] 的腿没有 — 并且 [eq_refl] 负极固定在
 测试/探针RepresentableInduced.v。 
*)
Lemma repr_pair_iso_from_is_induced :
  from (repr_pair_iso b1 b2)
    ≈ repr_induced (repr_of_representation c b1)
                   (repr_of_representation v b2) nat_id.
Proof.
  unfold repr_induced, repr_transport; simpl.
  apply proper_morphism.
  symmetry; srewrite (@fmap_id _ _ F c); reflexivity.
Qed.

Lemma repr_pair_iso_to_is_induced :
  to (repr_pair_iso b1 b2)
    ≈ repr_induced (repr_of_representation v b2)
                   (repr_of_representation c b1) nat_id.
Proof.
  unfold repr_induced, repr_transport; simpl.
  apply proper_morphism.
  symmetry; srewrite (@fmap_id _ _ F v); reflexivity.
Qed.

End CrossLink.

Section UnivPropertyCrossLink.

Context (C : Category).
Context (P : C → Type) (eqP : ∀ c, Setoid (P c)).
Context (H : IsUniversalProperty C P eqP).

(*
The isomorphism [univ_property_unique_up_to_unique_iso] produces IS the
   [repr_pair_iso] of the two representations, on the nose: the underlying
   [univ_property_unique] is [Defined] and its [uniqueness] field reduces.
   [eq_refl] is the convertibility exception. 

--------
[univ_property_unique_up_to_unique_iso] 产生的同构是
 [repr_pair_iso] 的两种表示，在鼻子上：底层
 [univ_property_unique]是[Defined]，其[uniqueness]场减少。 
[eq_refl] 是可转换性例外。 
*)
Definition up_unique_obj_is_repr_pair_iso (c d : C) (t : P c) (s : P d) :
  unique_obj (univ_property_unique_up_to_unique_iso C P eqP H c d t s)
  = repr_pair_iso (to (repr_equivalence c) t) (to (repr_equivalence d) s)
  := eq_refl.

(*
...so Mac Lane's τ = id case, read through the passage of this file, is
   that proposition's isomorphism: its backward leg is the arrow induced by
   the identity transformation between the two representations. 

--------
...所以 Mac Lane 的 τ = id 情况，通读该文件的段落，是
 该命题的同构：它的后腿是由
 两种表示之间的恒等变换。 
*)
Corollary univ_property_iso_from_is_induced (c d : C) (t : P c) (s : P d) :
  from (unique_obj (univ_property_unique_up_to_unique_iso C P eqP H c d t s))
    ≈ repr_induced (Representable_of_UnivProperty H c t)
                   (Representable_of_UnivProperty H d s) nat_id.
Proof. apply repr_pair_iso_from_is_induced. Qed.

End UnivPropertyCrossLink.

(**
** The category of represented functors, and the representing-object
       functor 

--------
** 表示函子的类别和表示对象
 函子 
*)

Section ReprFunctor.

Universes o h.
Context (C : Category@{o h h}).

(*
The full subcategory of [C, Sets] on the functors carrying a chosen
   representation.  [shom := True] is the full-subcategory idiom of
   Theory/Skeleton.v and Construction/Localization.v. 

--------
[C, Sets] 的完整子类别在函子上携带所选的
 代表。 [shom := True] 是以下的完整子类别惯用语
 Theory/Skeleton.v 和 Construction/Localization.v。 
*)
Program Definition ReprSubcat : Subcategory ([C, Sets]) := {|
  sobj := fun K => Representable K;
  shom := fun _ _ _ _ _ => True
|}.

Definition ReprCat : Category := @Sub ([C, Sets]) ReprSubcat.

(*
...and the assignment ⟨K, R⟩ ↦ repr_obj R, τ ↦ the arrow τ names.  It
   lands in C^op because [repr_induced_comp] reverses composition. 

--------
...以及赋值 ⟨K, R⟩ ↦ repr_obj R, τ ↦ 箭头 τ 名称。 它
 落在 C^op 中是因为 [repr_induced_comp] 反转了组合。 
*)
Program Definition ReprObjFunctor : ReprCat ⟶ C^op := {|
  fobj := fun X => @repr_obj _ _ (`2 X);
  fmap := fun X Y f => repr_induced (`2 X) (`2 Y) (`1 f)
|}.
Next Obligation. intros f g Hfg; now apply repr_induced_respects. Qed.
Next Obligation. now apply repr_induced_id. Qed.
Next Obligation. now apply repr_induced_comp. Qed.

(*
Fullness: Mac Lane's correspondence run backwards.  An arrow h between the
   representing objects is carried to ψ' ∘ Hom(h, −) ∘ ψ⁻¹, and that
   transformation names h again — by uniqueness, once ψ⁻¹ ∘ ψ has been
   cancelled. 

--------
完整性：麦克莱恩的信件是倒着写的。 之间的箭头 h
 表示对象被带入 ψ' ∘ Hom(h, −) ∘ ψ⁻¹，并且
 变换再次命名 h — 通过唯一性，一旦 ψ⁻¹ ∘ ψ 已被
 取消了。 
*)
Program Definition ReprObj_Full : Functor.Full ReprObjFunctor := {|
  prefmap := fun X Y h =>
    (to (@represented _ _ (`2 Y))
       ∘[Fun] (fmap[Curried_Hom C] (op h) ∘[Fun] from (@represented _ _ (`2 X)))
     ; I)
|}.
Next Obligation.
  symmetry; apply (repr_induced_unique X0 X _ g).
  apply repr_compatible_of_at; intros d k; simpl.
  apply proper_morphism.
  pose proof (iso_from_to (@represented _ _ X0) d k) as HH; simpl in HH.
  rewrite HH.
  now rewrite id_left.
Qed.

(*
Faithfulness: the compatibility condition determines τ at every element,
   because ψ is invertible and so every element of K d is ψ_d of something. 

--------
忠实度：相容条件决定了每个元素的 τ，
 因为 ψ 是可逆的，所以 K d 的每个元素都是某物的 ψ_d 。 
*)
Definition ReprObj_Faithful : Functor.Faithful ReprObjFunctor.
Proof.
  constructor; simpl; intros X Y f g E d z.
  assert (Hz : transform[to (@represented _ _ (`2 X))] d
                 (transform[from (@represented _ _ (`2 X))] d z) ≈ z).
  { pose proof (iso_to_from (@represented _ _ (`2 X)) d z) as HT; simpl in HT.
    rewrite HT.
    srewrite (@fmap_id _ _ (`1 X) d); reflexivity. }
  pose proof (repr_compatible_at
                (repr_induced_compatible (`2 X) (`2 Y) (`1 f)) d
                (transform[from (@represented _ _ (`2 X))] d z)) as Ef.
  pose proof (repr_compatible_at
                (repr_induced_compatible (`2 X) (`2 Y) (`1 g)) d
                (transform[from (@represented _ _ (`2 X))] d z)) as Eg.
  simpl in Ef, Eg.
  rewrite <- Hz, <- Ef, <- Eg.
  now rewrite E.
Qed.

End ReprFunctor.

Arguments ReprSubcat C.
Arguments ReprCat C.
Arguments ReprObjFunctor C.

(**
** Non-vacuity

    Over the delooping of (ℕ, +) — one object, hom-set ℕ, composition
    addition, identity 0 — a natural transformation between representable
    copresheaves is a natural number, and the arrow it names is that number.
    Both the transformation and the induced arrow are non-identities, which is
    what makes the correspondence's content visible: a witness at which both
    sides were identities would demonstrate nothing. 

--------
** 非空性

 在 (ℕ, +) 的解环上 — 一个对象，hom-set ℕ，组合
 另外，身份 0 — 可表示之间的自然转换
 copresheaves 是一个自然数，它命名的箭头就是该数字。 
变换和诱导箭头都是非恒等式，即
 是什么让信件的内容可见：双方都在见证人
 双方的身份并不能证明什么。 
*)

Section Witness.

Notation BNat := (Deloop Nat_Plus).

(* The transformation named by n, against the tautological representations.  / 由 n 命名的变换，反对同义反复表示。*)
Definition wit_tau (n : nat) := @fmap _ _ (Curried_Hom BNat) ttt ttt n.

(*
The induced arrow COMPUTES here: it is n on the nose.  [eq_refl] is the
   convertibility exception. 

--------
诱导箭头在这里计算：它位于鼻子上。 [eq_refl] 是
 兑换异常。 
*)
Definition wit_induced_computes (n : nat) :
  repr_induced (Hom_Representable (C:=BNat) ttt)
               (Hom_Representable (C:=BNat) ttt) (wit_tau n) = n := eq_refl.

Lemma wit_tau_not_id : wit_tau 3%nat ≈ nat_id → False.
Proof. intro Hx; pose proof (Hx ttt 0%nat) as H0; simpl in H0; discriminate. Qed.

Lemma wit_induced_not_id :
  repr_induced (Hom_Representable (C:=BNat) ttt)
               (Hom_Representable (C:=BNat) ttt) (wit_tau 3%nat)
    ≈ id{BNat} → False.
Proof. intro Hx; simpl in Hx; discriminate. Qed.

(*
The same at an in-tree [Representable] instance rather than the
   tautological one: [YoEvalAt_Representable] (Functor/Hom/Yoneda/Natural.v)
   represents evaluation at an object by the representable copresheaf.  Acting
   on each functor by [fmap] at n is a transformation of evaluations. 

--------
在树内 [Representable] 实例而不是
 同义反复一：[YoEvalAt_Representable] (Functor/Hom/Yoneda/Natural.v)
 表示可表示的 copresheaf 对对象的评估。 演戏
 [fmap] 在 n 处的每个函子上是评估的转换。 
*)
Program Definition wit_ev_tau (n : nat)
  : @YoEvalAt BNat ttt ⟹ @YoEvalAt BNat ttt := {|
  transform := fun F => fmap[F] n
|}.
Next Obligation. exact (@naturality_sym _ _ _ _ f ttt ttt n x0). Qed.
Next Obligation. exact (@naturality _ _ _ _ f ttt ttt n x0). Qed.

(*
Here the induced arrow does NOT come out on the nose — the Yoneda
   isomorphism's backward leg leaves an [∘ id], which over (ℕ, +) is a
   [n + 0] — so the agreement is stated at [≈], and the [eq_refl] negative is
   pinned in Test/ProbeRepresentableInduced.v. 

--------
这里诱导箭不会从鼻子上射出——米田
 同构的后腿留下一个 [∘ id]，它在 (ℕ, +) 上是一个
 [n + 0] — 因此协议在 [≈] 中表述，而 [eq_refl] 的否定是
 固定在 Test/ProbeRepresentableInduced.v 中。 
*)
Lemma wit_ev_induced (n : nat) :
  repr_induced (YoEvalAt_Representable BNat ttt)
               (YoEvalAt_Representable BNat ttt) (wit_ev_tau n)
    ≈ wit_tau n.
Proof. simpl; intros; unfold op; now rewrite <- plus_n_O. Qed.

Lemma wit_ev_tau_not_id : wit_ev_tau 3%nat ≈ nat_id → False.
Proof.
  intro Hx.
  pose proof (Hx (fobj[Curried_Hom BNat] ttt) 0%nat) as H0; simpl in H0.
  discriminate.
Qed.

Lemma wit_ev_induced_not_id :
  repr_induced (YoEvalAt_Representable BNat ttt)
               (YoEvalAt_Representable BNat ttt) (wit_ev_tau 3%nat)
    ≈ id → False.
Proof. intro Hx; pose proof (Hx ttt 0%nat) as H0; simpl in H0; discriminate. Qed.

End Witness.
