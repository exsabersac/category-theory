Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Monad.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(** * Morphisms of monads, and the category of monads on C  / * 单子的态射以及 C 上单子的范畴*)

(*
Book: Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
         Springer GTM 5, 1998, §VI.2 Exercise 3(a), printed p. 142
         (PDF p. 151) — maclane:VI.2:ex3; with §VI.1, printed pp. 138-139
         (PDF pp. 147-148), and §VII.3, printed p. 171 (PDF p. 179)
   nLab: https://ncatlab.org/nlab/show/monad (section “The 2-category of
         monads”)
   Paper: Eilenberg, Moore, “Adjoint functors and triples”, Illinois
          Journal of Mathematics 9(3), 1965
   Paper: Street, “The formal theory of monads”, Journal of Pure and
          Applied Algebra 2(2), 1972, pp. 149-168

   WHAT THE BOOK ASKS.  Exercise 3(a), read from the page image: “For
   monads ⟨T, η, μ⟩ and ⟨T', η', μ'⟩ on X, define a morphism θ of monads
   as a suitable natural transformation θ : T ⇝ T', and construct the
   category of all monads in X.”  Part (b), the functor θ* between the
   categories of algebras, is Monad/Morphism/Algebra.v.  The exercise
   repeats a request of §VI.1, which ends on p. 139 with “We leave the
   reader to describe a morphism ⟨T, μ, η⟩ → ⟨T', μ', η'⟩ of monads (a
   suitable natural transformation T ⇝ T') and the category of all
   monads in a given category X.”

   MAC LANE'S OWN ANSWER.  Two other pages settle what “suitable” and
   “the category of all monads” mean for him.  On p. 138: “All told, a
   monad in X is just a monoid in the category of endofunctors of X, with
   product × replaced by composition of endofunctors and unit set by the
   identity endofunctor.”  In §VII.3, p. 171: “A morphism f : ⟨c, μ, η⟩ →
   ⟨c', μ', η'⟩ of monoids is an arrow f : c → c' such that fμ = μ'(f □ f)
   : c □ c → c', fη = η' : e → c'.  With these arrows, the monoids in B
   constitute a category Mon_B”, and the table below it pairs the
   monoidal category ⟨C^C, ∘, Id⟩ with “Monads (cf. Chapter VI!)”.  So
   Mac Lane's category of all monads in X is Mon_{X^X}, and a morphism is
   a transformation θ with θ ∘ μ = μ' ∘ (θ □ θ) and θ ∘ η = η', where
   θ □ θ is the horizontal composite of θ with itself.

   THIS FILE'S READING.  [MonadHom M M'] is a class over two monads on
   one category C, whose fields are Mac Lane's data and his two
   equations, with ≈ for his =: [mh_transform], a [Transform] T ⟹ T' of
   Theory/Natural/Transformation.v (the book's “suitable natural
   transformation”); [mh_ret], θ_x ∘ η_x ≈ η'_x (fη = η'); and
   [mh_join], θ_x ∘ μ_x ≈ μ'_x ∘ (θ_{T'x} ∘ T(θ_x)) (fμ = μ'(f □ f)).
   The factor θ_{T'x} ∘ T(θ_x) is the library's horizontal composite:
   [mh_join_hcompose] shows that it IS the component at x of
   [nat_hcompose θ θ], by [eq_refl].  Its other form,
   T'(θ_x) ∘ θ_{Tx}, equal by naturality, is [mh_join_nat].  Mac Lane's
   Mon_{X^X} is in the tree already: Theory/Algebra/Monoid/Hom.v's [Mon]
   over the endofunctor category [C, C] with Structure/Monoidal/
   Compose.v's composition tensor.  The functor from the category below
   into it, and the reading of [mh_join] as its multiplication law, are
   Monad/Morphism/Monoid.v.

   [Monads C] is the category: objects are the pairs (T; M) of an
   endofunctor and a [Monad] on it, arrows are [MonadHom]s, and two
   arrows are ≈ when their components are, which is literally the ≈ of
   [C, C] on [mh_transform] ([Monads_equiv_is_Fun_equiv], [eq_refl]).
   The identity has components [id] ([mh_id], [mh_id_component]) and
   composition is componentwise ([mh_compose], [mh_compose_component]);
   the category laws are C's, componentwise.  [Monads_Forget] forgets
   the monad structure into [C, C], sending θ to [mh_transform θ] on the
   nose, and it is faithful by conversion: the two ≈ coincide, so
   [Monads_Forget_Faithful] is the identity on proofs.  Fullness is not
   claimed.

   Why a field of type [Transform] and not a bare family of components
   with a naturality law.  The [Transform] is the book's phrase, and it
   lets [Monads_Forget] send θ to its transformation with no
   repackaging.  Monad/Transformer.v's [MonadTransformer] carries its
   [lift] as a bare family, with no naturality field.

   WHERE THE NOTION COMES FROM.  Eilenberg and Moore (op. cit.) built
   the category of algebras of a monad, then called a triple, and Mac
   Lane's §VI.2 follows them; his book leaves the morphisms to the reader,
   as quoted above.  Street (op. cit.) made monads, and their morphisms,
   2-categorical: a monad in any 2-category K, and a 2-category of monads
   in K.  nLab's section “The 2-category of monads” gives that
   definition, cites Street, remarks that the orientation of the
   transformation in a morphism of monads is a convention that authors
   choose differently, and specializes it, in its example “transformation
   of monads on a fixed category”, to the notion of this file: a natural
   transformation between the underlying functors of two monads on one
   category, compatible with the units and the multiplications, a special
   case the page calls “of relevance notably for monads in computer
   science” (citing Moggi 1989, Def. 4.0.11).  The 2-category itself,
   with monads on different categories and 2-cells between morphisms, is
   not built here.

   In the tree, before this file existed, one functor between categories
   of algebras was built by hand, Instance/Fun/Action/Monad/BG.v's
   [BG_Act_EM] (#464), and the object part of another, Instance/SupLat/
   Free.v's [SL_induced_repack] (#466), whose functor that file does not
   build.  Each has the shape of the θ* of Monad/Morphism/Algebra.v for a
   morphism of monads with identity components.  Neither file is changed
   here; Instance/Fun/Action/Monad/BG/Morphism.v and Instance/SupLat/
   Free/Morphism.v state the two morphisms of monads and compare each
   with θ*.

   STRENGTHS.  By [eq_refl]: [mh_join_hcompose] (the right factor of
   [mh_join] is the horizontal composite), [mh_id_component],
   [mh_compose_component], [Monads_equiv_is_Fun_equiv] (the ≈ of
   [Monads C] is the ≈ of [C, C] on [mh_transform]),
   [Monads_Forget_obj] and [Monads_Forget_map] (the forgetful functor is
   the first projection on objects and [mh_transform] on arrows), and
   [Monads_Forget_comp_component] (its composition law at each
   component: both sides are φ_x ∘ θ_x).  At ≈: the laws of [MonadHom]
   and of [Monads C], [mh_join_nat], and the two functor laws of
   [Monads_Forget] between whole transformations.  Refused at [eq_refl],
   by conversion, each pinned in Test/ProbeMonadMorphism468.v with its
   positive controls:
   - the composition law between whole transformations (R18; control
     C37 at a component): the two [Transform]s have the same components
     and different naturality proofs, [mh_compose]'s chain against the
     obligation of the composite in [C, C];
   - [Monads_Forget] on an identity, compared with the identity of
     [C, C] even at a component (R6; controls C3 and C4): the identity
     of [Monads C] has components [id] and the identity of [C, C] is
     [nat_id], whose components are [fmap[T] id], and T is a variable,
     so the two do not reduce to one term.
   Both refusals stand in a copy of the dependency closure with every
   [Qed] turned into [Defined] and [Transparent Obligations] set
   (Instance/Sets.v keeping its [Qed]s, where that change is itself
   refused with a universe error), where Theory/Natural/Transformation.v's
   [nat_compose_obligation_1] reports “is transparent” and in the tree
   “is opaque”: they are not opacity.

   UNIVERSES, read off [About].  [MonadHom@{o h}] over [Category@{o h h}],
   with [Monad@{o h}] at both ends and no constraint; [mh_join_nat],
   [mh_id] and [mh_compose] are [@{o h}] with the constraint list closed
   and empty.  They stay so because their proofs use no setoid
   [rewrite]: the same [mh_id] proved with [rewrite id_left] is
   [@{o h u}] with h < u (measured).  The two component readbacks are
   [@{o h}] with no constraint on Rocq 9.1, but their lists end with [+]:
   on Coq 8.19 and 8.20 a statement = between arrows of C also carries
   h <= eq.u0, the universe of the standard library's [eq], and a closed
   list refuses it (measured on both, at [mh_join_hcompose]); every
   readback of this file and of Monad/Morphism/Algebra.v states = and
   ends its list with [+].
   [mh_join_hcompose] adds s with h < s, the strict level of
   [nat_hcompose], whose own block states it.  [Monads@{o h m1 m2}] is
   [Category@{m1 m2 m2}], with its object and hom levels chosen
   independently, as [Fun]'s are, above o and h; it also carries
   o <= Projections.u0/u1 and h <= Projections.u0/u1, the universes of
   the sigma projections, which its [hom] applies to the objects.  A
   binder cannot name those, so its constraint list ends with [+].
   [Monads_equiv_is_Fun_equiv], [Monads_Forget] and the constants after
   it add u with h < u, the strict level of [Fun], whose own block states
   it ([u0 < u5]); [C, C] is taken at [Fun@{o h o h m1 m2 u}], the levels
   of [Monads C].  No [Set] and no equation occur.

   REQUIRE COST.  Only [Monads_equiv_is_Fun_equiv], [Monads_Forget], its
   readbacks and [Monads_Forget_Faithful] use Instance/Fun.v; its
   [Require] is kept here, with the category the functor forgets, rather
   than in a satellite.  Measured by a script over coqdep's output, this
   file's [Require] closure has 21 files, itself included, and 14 without
   that line: Instance/Fun.v brings seven, itself, Instance/Sets.v,
   Structure/Monoidal.v, Functor/Bifunctor.v, Construction/Product.v,
   Structure/Initial.v and Structure/Terminal.v.

   NOT DELIVERED.  Street's 2-category of monads, with monads on
   different categories and 2-cells.  Comonad morphisms, which duality
   would give as [MonadHom] on C^op with the two comonads exchanged.
   Isomorphisms of [Monads C] are not characterized, and fullness of
   [Monads_Forget] is not claimed.  The Kleisli functor induced by θ is
   not built. 

--------
图书: Mac Lane，“工作数学家的类别”，第二版，
施普林格GTM 5，1998，§ VI.2练习3(a)，印刷142页
(PDF 151页)-maclane:VI.2:ex3; 与 § VI.1，印刷第138页-139页
(PDF 147至148页) 和 § VII.3，印刷171页 (PDF 179页)
nLab: https://ncatlab.org/nlab/show/monad (“2-类别” 部分
单子 “)
论文: Eilenberg，Moore，“伴随和三元组”，伊利诺伊州
数学学报9(3)，1965
论文: Street，“单子的形式理论”，“纯粹与
应用代数2(2)，1972，149-168页

书在问什么。练习3(a)，从页面图像中读取: “对于
X上的单子 ⟨ t，η，μ ⟩ 和 ⟨ T&#39;，η&#39;，μ&#39; ⟩，定义了单子的态射 θ
作为合适的自然变换 θ: T-，并构造
X中所有单子的类别。“(b) 部分，函数 θ *
代数的类别是Monad/态射/代数。v.练习
重复 § VI.1的请求，该请求在139页以 “我们离开
读者描述单子的态射 ⟨ t，μ，η ⟩ → ⟨ T&#39;，μ&#39;，η&#39; ⟩ (a
合适的自然转化T-T&#39;) 和所有的类别
给定类别X中的单子。“

麦克莱恩自己的答案。另外两页明确了“适当”的含义以及
“所有单子的类别” 对他来说意味着。在138页上: “总而言之，a
X中的monad只是X的endofunctors类别中的一个monoid，具有
乘积 × 替换为内函数的组成和单位集
身份代言人。“在 § VII.3中，p。171: “一个态射f: ⟨ c，μ，η ⟩ →
单音的 ⟨ c&#39;，μ&#39;，η&#39; ⟩ 是箭头f: c → c&#39;，使得f μ = μ&#39;(f □ f)
: c □ c → c&#39;，f η = η&#39; : e → c&#39;。借助这些箭头，B中的幺半群
构成一个类别Mon_B ”，它下面的表将
单音类别 ⟨ C ^ C，○，id ⟩，带 “Monads (参见第六章!)”。所以
Mac Lane在X中所有单子的类别是mon_ {X ^ X}，态射是
Θ ○ μ = μ&#39; ○ (θ □ θ) 和 θ ○ η = η&#39; 的变换 θ，其中
Θ □ θ 是 θ 与自身的水平合成。

该文件正在读取。[MonadHom M M']是在两个monad上的类
一个C类，其字段是麦克莱恩的数据和他的两个
方程，具有 ≈ his =: [mh_transform]，[Transform] T ⟹ T&#39;
理论/自然/转化。v (该书的 “合适的自然
变换 ”); [mh_ret]，θ_x ○ η_x ≈ η&#39; _x (fη = η&#39; ); 以及
[mh_join]，θ_x ○ μ _x ≈ μ&#39;_x ○ (θ_{T&#39;x} ○ T(θ_x)) (f μ = μ&#39;(f □ f))。
因子 θ_{T&#39;x} ○ T(θ_x) 是库的水平组合:
[mh_join_hcompose]显示它是x处的组件
[nat_hcompose θ θ]，由[eq_refl]。它的另一种形式，
T&#39;(θ_x) ○ θ_{Tx}，自然相等，是[mh_join_nat]。麦克莱恩的
Mon_{X ^ X} 已经在树中: 理论/代数/Monoid/Hom.v的[Mon]
在具有结构/Monoidal/的endofunctor类别[C, C]上
Compose.v的构图张量。下面范畴中的函子
它和[mh_join]的读数作为它的乘法定律，是
单子/态射/幺半群.v。

[Monads C]是类别: 对象是对 (T; M) 的
endofunctor和一个[Monad]，箭头是[MonadHom]s，两个
当箭头的分量为时，箭头为 ≈，这实际上是
[mh_transform]上的[C, C] ([Monads_equiv_is_Fun_equiv]、[eq_refl])。
标识具有组件[id] ([mh_id]，[mh_id_component]) 和
组合是组件式的 ([mh_compose]，[mh_compose_component])；
类别定律是C的，按分量计算。[Monads_Forget]忘记
将monad结构转换为[C, C]，将 θ 发送到
鼻子，通过转换是忠实的: 两个 ≈ 重合，所以
[Monads_Forget_Faithful]是证明上的标识。饱满不是
声称。

为什么是[Transform]类型的字段，而不是一个裸露的组件系列
自然法则。[Transform]是这本书的短语，它
让[Monads_Forget]将 θ 发送到其转换，不带
重新包装。Monad/Transformer.v的[MonadTransformer]带有其
[lift]作为一个裸露的家庭，没有自然领域。

这个概念是从哪里来的。Eilenberg和Moore (同前) 建成
monad的代数类别，然后称为三元组，而Mac
莱恩的 § VI.2跟着他们; 他的书把态射留给了读者，
如上所述。街 (同上)。制作单子，以及它们的态射，
2类: 任何2类K中的单子，以及2类单子
在K。nLab的 “2类单子” 部分给出了
定义，引用街道，说明
单子态射中的转换是作者的惯例
在其示例 “转换” 中进行不同的选择，并对其进行专业化
固定类别上的单子 “，这个文件的概念: 一个自然的
两个单子在一个上的基础函子之间的转换
类别，与单位和乘法兼容，一个特殊的
案例页面称 “特别与计算机中的单子相关”
科学 ”(引用Moggi 1989，Def。4.0.11)。2类本身，
在不同类别上的单子和态射之间的2个单元，是
不是在这里建的。

在树中，在此文件存在之前，类别之间有一个函子
代数是手工建立的，实例/有趣/动作/Monad/BG.v的
[BG_Act_EM] (#464) 和另一个的对象部分，实例/SupLat/
Free.v的[SL_induced_repack] (#466)，其函子文件不
构建。每个都具有单子/态射/代数的 θ * 的形状。
具有身份成分的单子的态射。两个文件都没有被更改
这里; 实例/乐趣/动作/Monad/BG/Morphism.v和实例/SupLat/
自由/态射.v陈述单子的两种态射，并对它们进行比较
与 θ *。

优势。由[eq_refl]: [mh_join_hcompose] (正确的因素
[mh_join]是水平复合)，[mh_id_component]，
[mh_compose_component]、[Monads_equiv_is_Fun_equiv] (的 ≈
[Monads C]是[mh_transform]上[C, C]的 ≈)，
[Monads_Forget_obj]和[Monads_Forget_map] (健忘的函子是
对象上的第一个投影和箭头上的[mh_transform])，以及
[Monads_Forget_comp_component] (其在每个
分量: 两边都是 φ_x ○ θ_x)。At ≈: [MonadHom]定律
和[Monads C]，[mh_join_nat]，以及
整个转换之间的[Monads_Forget]。
拒绝在[eq_refl]，
通过转换，每个固定在测试一下/ProbeMonadMorphism468.v中，其
阳性对照:
-整体转换之间的组成定律 (R18; 控制
C37在一个组件上): 两个xprotect53x具有相同的组件
和不同的自然性证明，[mh_compose]的链对
[C, C]中复合材料的义务；
-[Monads_Forget]上的标识，与
[C, C]甚至在一个组件 (R6; 控制C3和C4): 身份
的[Monads C]具有组件[id]和[C, C]的标识是
[nat_id]，其组件是[fmap[T] id]，T是一个变量，
所以两者不会减少到一个任期。
这两个拒绝都站在依赖闭包的副本中，每个
[Qed]变成[Defined]和[Transparent Obligations]集
(实例/Sets.v保持其[Qed]s，其中该更改本身就是
拒绝宇宙错误)，其中理论/自然/变换.v的
[nat_compose_obligation_1]报告 “是透明的”，并在树
“是不透明的”: 它们不是不透明的。

宇宙，读出[About]。[MonadHom@{o h}]高于[Category@{o h h}]，
两端都有[Monad@{o h}]，并且没有约束; [mh_join_nat]，
[mh_id]和[mh_compose]是约束列表关闭的[@{o h}]
而且是空的。他们之所以如此，是因为他们的证明没有使用setoid
[rewrite]: 使用[rewrite id_left]证明的[mh_id]是相同的
[@{o h u}]与h &lt;u (测量)。这两个组件的回读是
[@{o h}]对Rocq 9.1没有约束，但它们的列表以[+]结尾:
在Coq 8.19和8.20上，C的箭头之间的语句 = 也带有
h &lt;= eq.u0，标准库的[eq]的宇宙，和一个封闭的
列表拒绝它 (在两者上测量，在[mh_join_hcompose]); 每
此文件和单子/态射/代数的回读。v状态 = 和
以[+]结束其列表。[mh_join_hcompose]增加了s和h &lt;s，严格的水平
[nat_hcompose]，其自己的块状态。
[Monads@{o h m1 m2}]是
[Category@{m1 m2 m2}]，选择其对象和hom级别
独立地，就像[Fun]一样，高于o和h; 它也带有
o &lt;= 投影。u0/u1和h &lt;= 投影。u0/u1，宇宙
sigma投影，其[hom]应用于对象。一个
binder无法命名这些，因此其约束列表以[+]结尾。[Monads_equiv_is_Fun_equiv]、[Monads_Forget]和后面的常量
它将u加上h &lt;u，即[Fun]的严格级别，它自己的块状态
它 ([u0 < u5]); [C, C]在[Fun@{o h o h m1 m2 u}]，水平
的[Monads C]。无[Set]且无方程发生。

需要成本。只有[Monads_equiv_is_Fun_equiv]，[Monads_Forget]，其
回读和[Monads_Forget_Faithful]使用实例/Fun.v; 其
[Require]保留在这里，函子忘记的类别，而不是
比在卫星上。由coqdep输出的脚本测量，这
文件的[Require]闭包有21个文件，包括本身，14个没有
那条线: Instance/Fun.v本身带来七个，Instance/Sets.v，
结构/单体.v，函子/双函数.v，结构/产品.v，
结构/初始.v和结构/终端.v.

未交付。Street&#39;s 2-monads类别，带有monads
不同的类别和2-细胞。Comonad态射，对偶
将在C ^ op上给出[MonadHom]，两个comonads交换。
[Monads C]的同构没有特征，并且
[Monads_Forget]未声明。由 θ 引起的Kleisli函子是
没有建造。 
*)

(** ** Morphisms of monads  / ** 单子的态射*)

(*
A transformation T ⟹ T' preserving the unit (Mac Lane's fη = η') and
   the multiplication (his fμ = μ'(f □ f)), the horizontal composite
   f □ f written in [nat_hcompose]'s form at x. 

--------
保留单位的变换 T ⟹ T'（Mac Lane 的 fη = η'）和
 乘法（his fμ = μ'(f □ f)），水平复合
 f □ f 以 [nat_hcompose] 的形式写在 x 处。 
*)

Class MonadHom@{o h | } {C : Category@{o h h}} {T T' : C ⟶ C}
      (M : @Monad C T) (M' : @Monad C T') := {
  mh_transform : T ⟹ T';
  mh_ret {x : C} : mh_transform x ∘ @ret C T M x ≈ @ret C T' M' x;
  mh_join {x : C} :
    mh_transform x ∘ @join C T M x
      ≈ @join C T' M' x ∘ (mh_transform (T' x) ∘ fmap[T] (mh_transform x))
}.

Arguments mh_transform {C T T' M M'} _.
Arguments mh_ret {C T T' M M'} _ {x}.
Arguments mh_join {C T T' M M'} _ {x}.

(* The right factor of [mh_join] is the horizontal composite θθ.  / [mh_join] 的正确因子是水平合成 θθ。*)

Example mh_join_hcompose@{o h s | h < s +} {C : Category@{o h h}}
  {T T' : C ⟶ C} {M : @Monad C T} {M' : @Monad C T'}
  (θ : MonadHom@{o h} M M') (x : C) :
  transform[nat_hcompose@{s o o o h} (mh_transform θ) (mh_transform θ)] x
    = mh_transform θ (T' x) ∘ fmap[T] (mh_transform θ x) := eq_refl.

(* The other form of θθ, T'(θ_x) ∘ θ_{Tx}, by naturality of θ.  / θθ 的另一种形式，T'(θ_x) ∘ θ_{Tx}，由 θ 的自然性决定。*)

Lemma mh_join_nat@{o h | } {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M') (x : C) :
  mh_transform θ x ∘ @join C T M x
    ≈ @join C T' M' x ∘ (fmap[T'] (mh_transform θ x) ∘ mh_transform θ (T x)).
Proof.
  etransitivity; [ apply (mh_join θ) | ].
  apply compose_respects; [ reflexivity | ].
  symmetry. apply (naturality (mh_transform θ)).
Qed.

(*
Identity and composite.  The proofs are chains of [etransitivity],
   [compose_respects] and the associativity laws, with no setoid
   [rewrite], which would add a universe (see UNIVERSES above). 

--------
同一性和复合性。 证明是 [etransitivity] 的链，
 [compose_respects] 和结合律，无集合体
 [rewrite]，这将添加一个宇宙（参见上面的宇宙）。 
*)

Definition mh_id@{o h | } {C : Category@{o h h}} {T : C ⟶ C}
  (M : @Monad C T) : MonadHom@{o h} M M.
Proof.
  unshelve refine {| mh_transform := Build_Transform'@{o h h o h h}
                       (F:=T) (G:=T) (fun x => id) _ |}.
  - intros x y f.
    transitivity (fmap[T] f); [ apply id_right | symmetry; apply id_left ].
  - intros x; cbn. apply id_left.
  - intros x; cbn.
    transitivity (@join C T M x); [ apply id_left | ].
    symmetry.
    transitivity (@join C T M x ∘ id); [ | apply id_right ].
    apply compose_respects; [ reflexivity | ].
    transitivity (fmap[T] (@id C (T x))); [ apply id_left | apply fmap_id ].
Defined.

Example mh_id_component@{o h | +} {C : Category@{o h h}} {T : C ⟶ C}
  (M : @Monad C T) (x : C) :
  mh_transform (mh_id@{o h} M) x = id := eq_refl.

Definition mh_compose@{o h | } {C : Category@{o h h}} {T T' T'' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} {M'' : @Monad C T''}
  (φ : MonadHom@{o h} M' M'') (θ : MonadHom@{o h} M M') :
  MonadHom@{o h} M M''.
Proof.
  unshelve refine {| mh_transform := Build_Transform'@{o h h o h h}
                       (F:=T) (G:=T'')
                       (fun x => mh_transform φ x ∘ mh_transform θ x) _ |}.
  - intros x y f; cbn.
    etransitivity; [ apply comp_assoc | ].
    etransitivity;
      [ apply compose_respects;
          [ apply (naturality (mh_transform φ)) | reflexivity ] | ].
    etransitivity; [ apply comp_assoc_sym | ].
    etransitivity;
      [ apply compose_respects;
          [ reflexivity | apply (naturality (mh_transform θ)) ] | ].
    apply comp_assoc.
  - intros x; cbn.
    etransitivity; [ apply comp_assoc_sym | ].
    etransitivity;
      [ apply compose_respects; [ reflexivity | apply (mh_ret θ) ] | ].
    apply (mh_ret φ).
  - intros x; cbn.
    etransitivity; [ apply comp_assoc_sym | ].
    etransitivity;
      [ apply compose_respects; [ reflexivity | apply (mh_join θ) ] | ].
    etransitivity; [ apply comp_assoc | ].
    etransitivity;
      [ apply compose_respects; [ apply (mh_join φ) | reflexivity ] | ].
    etransitivity; [ apply comp_assoc_sym | ].
    apply compose_respects; [ reflexivity | ].
    etransitivity; [ apply comp_assoc_sym | ].
    etransitivity;
      [ apply compose_respects; [ reflexivity | apply comp_assoc ] | ].
    etransitivity;
      [ apply compose_respects;
          [ reflexivity
          | apply compose_respects;
              [ apply (naturality (mh_transform θ)) | reflexivity ] ] | ].
    etransitivity;
      [ apply compose_respects; [ reflexivity | apply comp_assoc_sym ] | ].
    etransitivity;
      [ apply compose_respects;
          [ reflexivity
          | apply compose_respects;
              [ reflexivity | symmetry; apply fmap_comp ] ] | ].
    apply comp_assoc.
Defined.

Example mh_compose_component@{o h | +} {C : Category@{o h h}}
  {T T' T'' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} {M'' : @Monad C T''}
  (φ : MonadHom@{o h} M' M'') (θ : MonadHom@{o h} M M') (x : C) :
  mh_transform (mh_compose@{o h} φ θ) x
    = mh_transform φ x ∘ mh_transform θ x := eq_refl.

(** ** The category of monads on C  / ** C 上的单子范畴*)

(*
Objects are monads, arrows are morphisms of monads, and ≈ compares
   components, as the ≈ of [C, C] does. 

--------
对象是单子，箭头是单子的态射，并且 ≈ 进行比较
 组件，就像 [C, C] 的 ≈ 一样。 
*)

Definition Monads@{o h m1 m2 | o <= m1, h <= m1, o <= m2, h <= m2 +}
  (C : Category@{o h h}) : Category@{m1 m2 m2}.
Proof.
  unshelve refine
    {| obj := { T : C ⟶ C & @Monad C T }
     ; hom := fun M N => MonadHom@{o h} (projT2 M) (projT2 N)
     ; homset := fun M N =>
         {| equiv := fun θ φ => ∀ x : C,
              @equiv _ (@homset C _ _) (mh_transform θ x) (mh_transform φ x) |}
     ; id := fun M => mh_id (projT2 M)
     ; compose := fun M N P φ θ => mh_compose φ θ |}.
  - constructor.
    + intros θ x. reflexivity.
    + intros θ φ E x. symmetry. apply E.
    + intros θ φ ψ E F x.
      transitivity (mh_transform φ x); [ apply E | apply F ].
  - intros M N P φ φ' Eφ θ θ' Eθ x; cbn.
    apply compose_respects; [ exact (Eφ x) | exact (Eθ x) ].
  - intros M N θ x; cbn. apply id_left.
  - intros M N θ x; cbn. apply id_right.
  - intros M N P Q f g k x; cbn. apply comp_assoc.
  - intros M N P Q f g k x; cbn. apply comp_assoc_sym.
Defined.

Example Monads_equiv_is_Fun_equiv@{o h m1 m2 u |
  h < u, o <= m1, h <= m1, o <= m2, h <= m2 +}
  (C : Category@{o h h}) (N N' : Monads@{o h m1 m2} C)
  (θ φ : N ~{Monads@{o h m1 m2} C}~> N') :
  @equiv _ (@homset (Monads@{o h m1 m2} C) N N') θ φ
    = @equiv _ (@homset (@Fun@{o h o h m1 m2 u} C C) (projT1 N) (projT1 N'))
        (mh_transform θ) (mh_transform φ) := eq_refl.

(** ** The forgetful functor into [C, C]  / ** [C, C] 中的健忘函子*)

Definition Monads_Forget@{o h m1 m2 u |
  h < u, o <= m1, h <= m1, o <= m2, h <= m2 +} (C : Category@{o h h}) :
  Monads@{o h m1 m2} C ⟶ @Fun@{o h o h m1 m2 u} C C.
Proof.
  unshelve refine
    (@Build_Functor (Monads@{o h m1 m2} C) (@Fun@{o h o h m1 m2 u} C C)
       (fun N : { T : C ⟶ C & @Monad C T } => projT1 N)
       (fun N N' θ => mh_transform θ) _ _ _).
  - intros N N' θ θ' E. exact E.
  - intros N x. simpl. symmetry. apply fmap_id.
  - intros N N' N'' φ θ x. simpl. reflexivity.
Defined.

Example Monads_Forget_obj@{o h m1 m2 u |
  h < u, o <= m1, h <= m1, o <= m2, h <= m2 +} (C : Category@{o h h})
  (N : Monads@{o h m1 m2} C) :
  fobj[Monads_Forget@{o h m1 m2 u} C] N = projT1 N := eq_refl.

Example Monads_Forget_map@{o h m1 m2 u |
  h < u, o <= m1, h <= m1, o <= m2, h <= m2 +} (C : Category@{o h h})
  (N N' : Monads@{o h m1 m2} C) (θ : N ~{Monads@{o h m1 m2} C}~> N') :
  fmap[Monads_Forget@{o h m1 m2 u} C] θ = mh_transform θ := eq_refl.

(* The composition law at a component: both sides are φ_x ∘ θ_x.  / 某分量的合成定律：两边都是 φ_x ∘ θ_x。*)

Example Monads_Forget_comp_component@{o h m1 m2 u |
  h < u, o <= m1, h <= m1, o <= m2, h <= m2 +} (C : Category@{o h h})
  (N N' N'' : Monads@{o h m1 m2} C)
  (φ : N' ~{Monads@{o h m1 m2} C}~> N'')
  (θ : N ~{Monads@{o h m1 m2} C}~> N') (x : C) :
  transform[fmap[Monads_Forget@{o h m1 m2 u} C] (φ ∘ θ)] x
    = transform[fmap[Monads_Forget@{o h m1 m2 u} C] φ
                ∘ fmap[Monads_Forget@{o h m1 m2 u} C] θ] x := eq_refl.

(* Faithful by conversion: the hypothesis is already the conclusion.  / 通过转换而忠实：假设已经是结论。*)

Definition Monads_Forget_Faithful@{o h m1 m2 u |
  h < u, o <= m1, h <= m1, o <= m2, h <= m2 +} (C : Category@{o h h}) :
  Faithful (Monads_Forget@{o h m1 m2 u} C).
Proof. constructor. intros N N' θ θ' E. exact E. Defined.
