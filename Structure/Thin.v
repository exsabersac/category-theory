Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(* * * Thin categories, and the hom-preorder of a category / * * 细范畴，以及范畴的同态预序 *)

(*
 nLab:      https://ncatlab.org/nlab/show/thin+category
 nLab:      https://ncatlab.org/nlab/show/preorder
 Wikipedia: https://en.wikipedia.org/wiki/Preorder
 Book:      Mac Lane, “Categories for the Working Mathematician”,
 Springer GTM 5, 2nd ed. 1998, §I.2 (construction 7, def. 4)
 Book:      Riehl, “Category Theory in Context”, Dover 2016, §1.2
 Book:      Fong and Spivak, “Seven Sketches in Compositionality”,
 CUP 2019, §§1.2.2, 1.3.1

 A category is THIN when any two parallel morphisms agree: the hom-setoid
 `x ~> y` has at most one element up to `≈`.  nLab equivalently calls such a
 category a (0,1)-category.  Mac Lane arrives at the same notion from the
 other side: CWM §I.2 builds a category from a preordered set, one arrow
 `x → y` per instance of `x ≤ y`, and defines a linear (total) order in the
 same section.  (The internal numbering — construction 7, definition 4 — is
 as cited by the issue this file answers; the section is the one to read.)

 The predicate below is stated exactly as Structure/Discrete.v states its
 own: a property ASSERTED of a given category, rather than a construction
 BUILDING one.  That is why this file sits in Structure/ next to
 [Discrete] rather than in Instance/ next to [Proset] — Instance/Discrete.v
 records the same split in its header, calling [DiscreteCat] the
 object-level construction and Structure/Discrete.v's [Discrete] the
 predicate, and its [DiscreteCat_Discrete] the bridge.  Here
 Instance/Proset.v's [Proset] is the construction, [Thin] is the
 predicate, and [proset_thin] (Instance/Proset/Order.v) is the bridge.

 Thinness is what makes the order-theoretic dictionary of
 Instance/Poset.v work: with all parallel arrows identified, every
 diagram commutes and every coherence law holds for free.  The library
 already exploits this pointwise — Instance/Two/Monoidal.v's [two_thin]
 discharges the whole [Two_Cartesian] obligation and the
 [Two_Terminal] one by a single appeal each (the monoidal structure is then derived from those through [Cartesian_Monoidal]), and
 Construction/Enriched/Two.v closes the three enrichment laws the
 same way — but the property itself had no name.  This file gives it one,
 and Instance/Proset/Order.v puts it to work.

 The second half of the file goes back the other way.  Every category C
 carries a preorder on its objects, “x ≤ y when there is an arrow x ~> y”.
 Since Coq's [relation] is Prop-valued while a hom lives in [Type], the
 passage squashes: [thin_preorder] uses [inhabited].  That squash is the
 whole content of the round trip measured in Instance/Proset/Order.v — it
 is invertible on a [Proset], whose homs are already Props, and in general
 it is not, which is why [HomChoice] is introduced here as an explicit
 hypothesis rather than assumed.

 NOTE on instance resolution: [thin_PreOrder] is deliberately left a plain
 [Definition] rather than being registered as a typeclass instance, and is
 passed explicitly at each use.  That matches how the tree already handles
 [PreOrder] arguments — Instance/Poset.v hands [PeanoNat.Nat.le_preorder]
 to [Poset] by hand — and it keeps a rule whose conclusion is
 [PreOrder (thin_preorder ?C)] out of the search space for [PreOrder] goals
 whose relation is still a metavariable. 

 --------
 nLab:       https://ncatlab.org/nlab/show/thin+category 
 nLab:       https://ncatlab.org/nlab/show/preorder 
 维基百科:  https://en.wikipedia.org/wiki/Preorder 
 书籍:      Mac Lane, 《为在职数学家准备的范畴论》，
 Springer GTM 5, 第二版 1998, §I.2 (构造 7, 定义 4)
 书籍:      Riehl, 《语境中的范畴论》，Dover 2016, §1.2
 书籍:      Fong 和 Spivak, 《组合性的七个草图》，
 CUP 2019, §§1.2.2, 1.3.1当任意两个平行态射相同的时候，类别是稀薄的：同集 `x ~> y` 至多有一个元素在 `≈` 下同余。nLab 同样称这样的类别为 (0,1)-类别。Mac Lane 从另一方面得出了相同的概念：《CWM》第 I.2 节从预序集合构造一个类别，每一个 `x ≤ y` 的实例对应一个箭头 `x → y`，并在同一节中定义了线性（全）序。（内部编号——构造 7，定义 4——如本文件所回答的问题所引用；这一节才是需要阅读的部分。）下面的谓词正如 Structure/Discrete.v 所陈述的那样：它是针对给定类别声明的属性，而不是构建一个属性。这也是为什么该文件位于 Structure/ 目录下，与 [Discrete] 并列，而不是在 Instance/ 目录下与 [Proset] 并列——Instance/Discrete.v 在其头部记录了相同的划分，将 [DiscreteCat] 称为对象级构造，将 Structure/Discrete.v 的 [Discrete] 称为谓词，其 [DiscreteCat_Discrete] 为桥。在这里，Instance/Proset.v 的 [Proset] 是构造，[Thin] 是谓词，而 [proset_thin]（Instance/Proset/Order.v）是桥。纤薄性是使 Instance/Poset.v 的序论字典起作用的原因：当所有平行箭头被识别时，每个图都是交换的，每个一致性定律都是自动成立的。库已经在逐点利用这一点——Instance/Two/Monoidal.v 的 [two_thin] 单次解决了整个 [Two_Cartesian] 的义务，以及 [Two_Terminal] 的义务（随后通过 [Cartesian_Monoidal] 从这些导出单体结构），Construction/Enriched/Two.v 以同样的方式完成了三个增广定律——但该性质本身没有名字。这个文件给了它一个名字，而 Instance/Proset/Order.v 将其付诸实践。文件的后半部分以相反的方向回去。每个 C 类别在其对象上都有一个预序，“当存在一个箭头 x ~> y 时，x ≤ y”。由于 Coq 的 [relation] 是 Prop 值，而一个同态位于 [Type] 中，这个过程被压缩：[thin_preorder] 使用 [inhabited]。这个压缩就是在 Instance/Proset/Order.v 中测量的整个往返内容——它在 [Proset] 上是可逆的，该同态已经是 Props，而通常它不是，这就是为什么在这里引入 [HomChoice] 作为一个显式假设，而不是默认假设。关于实例解析的说明：[thin_PreOrder] 被故意保留为普通的 [Definition]，而不是注册为类型类实例，并且在每次使用时显式传递。这与树已经处理 [PreOrder] 参数的方式相匹配——Instance/Poset.v 手动将 [PeanoNat.Nat.le_preorder] 传递给 [Poset]——并且它将一个结论为 [PreOrder (thin_preorder ?C)] 的规则排除在那些关系仍是元变量的 [PreOrder] 目标的搜索空间之外。
*)

(*
 A category is thin when parallel morphisms are identified by the hom-setoid
 equivalence.  Note that this is `≈`, not `=`: on the library's setoid
 hom-sets that is the right notion, and it is what Instance/Proset.v
 supplies for a proset by declaring the equivalence to be [True]. 

 --------
 当通过同态集合的等价关系识别平行态射时，一个范畴是稀薄的。请注意，这里是 `≈`，而不是 `=`：在库的集合同态集中，这是正确的概念，并且正是 Instance/Proset.v 为一个预序集合提供的，通过声明等价关系为 [True]。
*)
Definition Thin (C : Category) : Type :=
  ∀ (x y : C) (f g : x ~{C}~> y), f ≈ g.

(*
 Thinness is self-dual: reversing arrows neither creates nor merges parallel
 pairs.  Both directions hold on the nose because Construction/Opposite.v
 defines hom[C^op] x y as hom[C] y x and reuses the same hom-setoid. 

 --------
 薄性是自对偶的：反转箭头既不会创建也不会合并平行对。两个方向都完全成立，因为 Construction/Opposite.v 将 hom [C^op] x y 定义为 hom [C] y x，并且重用了相同的 hom-集体。
*)

Lemma Thin_Opposite {C : Category} : Thin C → Thin (C^op).
Proof. intros T x y f g; exact (T y x f g). Qed.

Lemma Opposite_Thin {C : Category} : Thin (C^op) → Thin C.
Proof. intros T x y f g; exact (T y x f g). Qed.

(*
 In a thin category every morphism is both monic and epic (the classes at
 Theory/Morphisms.v), because both cancellation laws conclude
 an equation between parallel morphisms.  The converse does not hold: being
 a bimorphism everywhere is far weaker than thinness. 

 --------
 在一个薄范畴中，每个态射都是单的和满的（在 Theory/Morphisms.v 中的类），因为两个消去律都得出平行态射之间的等式。反之则不成立：处处是双态射远比薄弱性要弱。
*)

Lemma thin_Monic {C : Category} (T : Thin C) {x y : C} (f : x ~> y) : Monic f.
Proof. constructor; intros z g1 g2 _; apply T. Qed.

Lemma thin_Epic {C : Category} (T : Thin C) {x y : C} (f : x ~> y) : Epic f.
Proof. constructor; intros z g1 g2 _; apply T. Qed.

(*
 A pair of opposing morphisms in a thin category is automatically an
 isomorphism: the two composites are endomorphisms, hence equal to the
 identity.  This is the categorical reading of “x ≤ y and y ≤ x”, and it is
 exactly what antisymmetry rules out in Instance/Poset.v — a poset is a
 SKELETAL thin category (Instance/Poset.v), the isomorphic objects being
 forced equal.

 Both inverse laws are supplied directly rather than through [Program], so
 that the two appeals to thinness are visible in the term instead of being
 found by the [cat_simpl] obligation tactic (Lib/Tactics.v), whose [auto]
 would pick [T] out of the context. 

 --------
 在一个薄范畴中，一对相对的态射自动就是一个同构：两个复合态射是自同态，因此等于恒等态射。这就是“x ≤ y 且 y ≤ x”的范畴论解读，并且它正是 Instance/Poset.v 中反对称性所排除的——一个偏序集是一个 SKELETAL 薄范畴（Instance/Poset.v），同构对象被迫相等。

 两个逆元律都是直接提供的，而不是通过 [Program]，这样在项中可以直接看到两次对薄性的调用，而不是通过 [cat_simpl] 义务策略（Lib/Tactics.v）找到，其中 [auto] 会从上下文中选出 [T]。
*)
Definition thin_iso {C : Category} (T : Thin C) {x y : C}
  (f : x ~> y) (g : y ~> x) : x ≅ y :=
  {| to          := f
   ; from        := g
   ; iso_to_from := T y y (f ∘ g) id
   ; iso_from_to := T x x (g ∘ f) id |}.

(* * ** The hom-preorder of a category / * ** 一个范畴的 hom-预序 *)

(*
 The ∃-a-morphism preorder on objects, squashed to Prop.

 The library ALREADY carries a preorder of this shape at the Type level:
 Theory/Category.v's exported instance [hom_preorder : PreOrder hom[C]]
 over CRelationClasses, whose “proofs” are the morphisms themselves.  That
 instance is deliberately NOT reused here, and the reason is the honest
 version of this file's choice story: fed to a Type-valued preorder, the
 reconstruction below would need no [HomChoice] at all -- the witness IS the
 morphism.  What forces the squash is Instance/Proset.v's [Proset], which
 is hard-wired to [Relation_Definitions.relation], i.e. Prop-valued; a
 Prop-squashed relation is the only thing it accepts, and recovering a
 morphism from the squash is then a genuine choice.  (Instance/Omega.v
 documents the same Prop-vs-Type obstruction and routes around it with a
 bespoke Type-valued order; here the point is precisely to meet [Proset]
 where it is.)  The new name [thin_preorder] avoids shadowing the exported
 instance. 

 --------
 对象上的 ∃-a-同态预序，归约为命题。该库在类型级别上已经携带了这种形状的预序：
 Theory/Category.v 导出的实例 [hom_preorder : PreOrder hom[C]
 基于 CRelationClasses，其“证明”本身就是态射。该实例在此处故意不被重用，原因在于该文件的选择故事的真实版本：如果输入的是类型值预序，下面的重建根本不需要 [HomChoice] ——见证本身就是态射。强制压扁的是 Instance/Proset.v 的 [Proset]，它被硬编码为 [Relation_Definitions.relation]，即 Prop 值；它只接受 Prop 压扁的关系，并且从压扁中恢复态射才是真正的选择。(Instance/Omega.v 记录了相同的 Prop 与 Type 的障碍，并通过定制的类型值顺序绕过它；这里的重点正是要在 [Proset] 遇到它的位置处处理它。) 新的名称 [thin_preorder] 避免了对导出实例的遮蔽。
*)
Definition thin_preorder (C : Category) : relation (obj[C]) :=
  fun x y => inhabited (x ~{C}~> y).

(*
 It is a preorder: reflexivity is the identity arrow, transitivity is
 composition.  The [inhabited] witnesses may be eliminated here because the
 goal is itself a Prop. 

 --------
 它是一个预序：自反性是恒等箭头，传递性是合成。这里可以消除 [inhabited] 见证，因为目标本身就是一个命题（Prop）。
*)
Definition thin_PreOrder (C : Category) : PreOrder (thin_preorder C).
Proof.
  constructor.
  - intro x; exact (inhabits (@id C x)).
  - intros x y z Hxy Hyz.
    destruct Hxy as [f], Hyz as [g].
    exact (inhabits (g ∘ f)).
Defined.

(*
 Opposition on categories is order reversal on hom-preorders, and the two
 relations are not merely pointwise equivalent but CONVERTIBLE: both sides
 reduce to [inhabited (y ~{C}~> x)].  [Basics.flip] is the stdlib operation
 [flip R x y = R y x]. 

 --------
 类别上的对立是同预序上的顺序逆转，这两个关系不仅在点上是等价的，而且是可互换的：双方都可以化简为 [inhabited (y ~{C}~> x)] 。 [Basics.flip] 是标准库操作 [flip R x y = R y x] 。
*)
Lemma hom_preorder_op (C : Category) (x y : obj[C]) :
  thin_preorder (C^op) x y = Basics.flip (thin_preorder C) x y.
Proof. reflexivity. Qed.

(*
 Choosing an arrow from the bare knowledge that one exists.  This is
 elimination of the Prop [inhabited (x ~> y)] into [Type], which Coq's
 elimination rules do not grant: [inhabited] has a [Type]-valued argument in
 its constructor, so its eliminator is restricted to Prop targets, and no
 [match] on the witness can produce a morphism.  The hypothesis is therefore
 taken explicitly wherever it is needed, never assumed.  It is free of charge
 whenever the homs of C are themselves Props — in particular on every
 [Proset], where [proset_HomChoice] discharges it (Instance/Proset/Order.v).

 What is claimed here is only that the obvious definition does not
 typecheck; no impossibility theorem is being asserted. 

 --------
 从仅知道存在一个箭头的基础知识中选择一个箭头。这是将 Prop [inhabited (x ~> y)] 消除到 [Type]，而 Coq 的消除规则并不允许：[inhabited] 的构造函数中有一个 [Type] 值的参数，因此它的消除器只能用于 Prop 目标，并且见证上的 [match] 无法产生一个态射。因此，该假设在需要的时候必须显式获取，而不能假定。当 C 的霍姆自身就是 Prop 时，它是免费的——特别是在每个 [Proset] 上，[proset_HomChoice] 负责处理它（Instance/Proset/Order.v）。

 这里声明的只是显而易见的定义类型检查不通过；并没有任何不可能性定理被断言。
*)
Definition HomChoice (C : Category) : Type :=
  ∀ (x y : obj[C]), thin_preorder C x y → x ~{C}~> y.

(* * ** Closure of thinness (Mac Lane §II.3 Ex. 2 / §II.4 Ex. 4, structural halves) / * ** 薄性的闭包（Mac Lane §II.3 习题 2 / §II.4 习题 4，结构半） *)

#[local] Obligation Tactic := idtac.

(*
 Products of thin categories are thin: parallel pairs are componentwise
 parallel.  Instance/Proset/Closure.v instantiates this at preorders. 

 --------
 薄范畴的积是薄的：平行对是按组分平行的。Instance/Proset/Closure.v 在预序中实例化了这一点。
*)
Lemma Thin_Product {C D : Category} :
  Thin C → Thin D → Thin (C ∏ D).
Proof.
  intros TC TD [a b] [c d] [f g] [f' g']; split.
  - exact (TC a c f f').
  - exact (TD b d g g').
Qed.

(*
 Into a thin target, any component family is natural — both naturality
 squares are equations between parallel morphisms.  Functors into thin
 categories are therefore compared by their object actions alone. 

 --------
 对于一个稀疏的目标，任何组件族都是自然的——自然性平方都是平行态射之间的方程。因此，映入稀疏范畴的函子仅通过它们的对象作用来比较。
*)
Program Definition thin_natural {C D : Category} (TD : Thin D)
  (F G : C ⟶ D) (η : ∀ x : C, F x ~> G x) : F ⟹ G := {|
  transform := η
|}.
Next Obligation.
  intros C D TD F G η x y f.
  exact (TD _ _ _ _).
Qed.
Next Obligation.
  intros C D TD F G η x y f.
  exact (TD _ _ _ _).
Qed.

(*
 Parallel natural transformations into a thin target agree pointwise:
 their components are parallel.  (The functor-category packaging of
 this — a functor category into a thin target is thin — lives in
 Instance/Proset/Closure.v, where [Fun] is available.) 

 --------
 平行自然变换到一个稀薄的目标在每一点上都是一致的：它们的分量是平行的。（其函子范畴的封装——到一个稀薄目标的函子范畴是稀薄的——位于 Instance/Proset/Closure.v，其中 [Fun] 可用。）
*)
Lemma Thin_Transform {C D : Category} (TD : Thin D)
  (F G : C ⟶ D) (σ τ : F ⟹ G) :
  ∀ x : C, transform σ x ≈ transform τ x.
Proof.
  intro x.
  exact (TD _ _ _ _).
Qed.
