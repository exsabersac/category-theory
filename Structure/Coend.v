Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Wedge.
Require Import Category.Structure.End.

Generalizable All Variables.

(* * * Coends: ergonomic covariant accessors / * * Coends：符合人体工学的协变访问器 *)

(*
 nLab:      https://ncatlab.org/nlab/show/coend
 Wikipedia: https://en.wikipedia.org/wiki/Coend

 The COEND of a functor of mixed variance `F : C^op ∏ C ⟶ D`, written
 `∫^c F(c,c)`, is the UNIVERSAL (initial) COWEDGE: an object `coend_obj : D`
 together with injections `coend_inj_x : F (x, x) ~> coend_obj`, one per
 object `x : C`, satisfying the covariant (co)dinaturality condition and
 through which every other cowedge factors uniquely. It is the dinatural
 analogue of a colimit, dual to the END of Structure/End.

 In this library a coend is DEFINED as an end in the opposite categories,

 Coend F := @End (C^op) (D^op) (F^op)          (Structure/End.v)

 so its underlying datum is a `Wedge F^op` (equivalently a `Cowedge F`, see
 Structure/Wedge) whose legs `F (x, x) ~{D}~> coend_obj` are the reversed
 wedge legs and whose universal property runs OUT of the coend. Reasoning
 directly with that opposite-category packaging forces every morphism to be
 read reversed, which is awkward downstream.

 This file supplies a thin convenience layer, in the exact spirit of
 Structure/Pushout (a covariant reader over the dualized `Pullback`): the
 accessors `coend_obj` and `coend_inj`, the covariant cowedge condition
 `coend_cowedge`, the universal property `coend_ump`, the mediator
 `coend_med` (with its computation and uniqueness rules), and a smart
 constructor `Build_Coend` assembling a coend from covariant cowedge data.
 Each accessor is an op-read of the corresponding `End`/`Wedge` accessor
 (`end_wedge`, `wedge_map`, `ump_wedges`, `ump_ends`) with the morphisms
 inverted, so downstream code can reason entirely in `C` and `D`. Nothing
 here alters Structure/End.

 The covariant cowedge condition, for `f : x ~> y`, both sides
 `F (y, x) ~> coend_obj`:

 coend_inj_x ∘ bimap[F] (op f) id ≈ coend_inj_y ∘ bimap[F] id f

 This is the dual of the wedge condition of Structure/Wedge: the leg at `x`
 precomposed with the contravariant action `F(f, 1)` agrees with the leg at
 `y` precomposed with the covariant action `F(1, f)`. Because `Coend`,
 `F^op`, `op` and the reversed hom-sets are all involutive on the nose, the
 op-reads below are the underlying `End`/`Wedge` data up to one `symmetry`,
 with no coherence obligations of their own. 

 --------
 nLab:       https://ncatlab.org/nlab/show/coend 
 维基百科:  https://en.wikipedia.org/wiki/Coend 

 一个混合变性函子  `F : C^op ∏ C ⟶ D` 的 COEND，记作 `∫^c F(c,c)`，是一个普遍的（初始的）余楔：一个对象 `coend_obj : D`
 以及每个对象 `x : C` 对应的注入映射 `coend_inj_x : F (x, x) ~> coend_obj`，满足协变（余）自然性条件，并且通过它每一个其他的余楔都能够唯一分解。它是极限的挠性类似物，与 Structure/End 的 END 对偶。

 在这个库中，余极被定义为对偶范畴中的端：

 Coend F := @End (C^op) (D^op) (F^op)          (Structure/End.v)所以它的底层数据是一个 `Wedge F^op`（同样是一个 `Cowedge F`，见 Structure/Wedge），它的腿 `F (x, x) ~{D}~> coend_obj` 是反向的楔形腿，其泛性质从共端向外运行。直接用那个对偶范畴的封装进行推理会迫使每个态射都要反向读取，这在后续处理中很不方便。该文件提供了一个薄的便捷层，完全遵循 Structure/Pushout（在双化的 `Pullback` 上的协变读取器）的精神：访问器 `coend_obj` 和 `coend_inj`、协变共楔条件 `coend_cowedge`、普遍性 `coend_ump`、中介器 `coend_med`（及其计算和唯一性规则）以及一个智能构造函数 `Build_Coend`，从协变共楔数据组装一个协端。每个访问器都是对相应 `End` / `Wedge` 访问器（`end_wedge`、`wedge_map`、`ump_wedges`、`ump_ends`）的 op-读取，带有反转的态射，因此下游代码可以完全在 `C` 和 `D` 中进行推理。这里没有任何内容会更改 Structure/End。

 对 `f : x ~> y` 的协变共楔条件，双方 `F (y, x) ~> coend_obj`：coend_inj_x ∘ bimap [F] (op f) id ≈ coend_inj_y ∘ bimap [F] id f

 这是 Structure/Wedge 楔形条件的对偶：在 `x` 上的腿与对偶作用 `F(f, 1)` 预合成后，与在 `y` 上的腿与协变作用 `F(1, f)` 预合成后的结果一致。由于 `Coend`、`F^op`、`op` 以及反向的 hom 集都是严格自反的，下方的 op-读取是底层 `End` / `Wedge` 数据的一部分，至多相差一个 `symmetry`，并且它们自身没有一致性义务。
*)

(*
 The coend calculus, its history, and the existential reading

 nLab:  https://ncatlab.org/nlab/show/coend
 Book:  Loregian, “(Co)end Calculus”, London Math. Soc. Lecture Note
 Series 468, Cambridge University Press 2021
 Paper: Yoneda, “On Ext and exact sequences”, J. Fac. Sci. Univ. Tokyo
 Sec. I, 8 (1960) 507–576
 Book:  Mac Lane, “Categories for the Working Mathematician”, Springer
 1971 (2nd ed. 1998), chapter IX
 Paper: Day, “On closed categories of functors”, Midwest Category
 Seminar IV, Springer LNM 137 (1970) 1–38

 A coend integrates a functor of mixed variance over its diagonal into
 a single object of the target, and it does so where an ordinary
 colimit cannot.  A colimit glues a covariant diagram; [coend_obj] is
 instead the universal object receiving the injections [coend_inj]
 that COEQUALIZE the two functorial actions of `F`.  Concretely it is
 the coequalizer

 ∐_{f : c → c'} F(c', c) ⇉ ∐_c F(c, c) → ∫^c F(c, c)

 forcing the contravariant action `F(f, 1)` and the covariant action
 `F(1, f)` to agree (nLab, “coend”); this is [coend_cowedge] read as a
 quotient rather than as a family of equations.  Many canonical
 constructions are inherently of mixed variance, and it is these, not
 covariant diagrams, that a coend is built to express.

 The notation and the calculus accumulated in layers.  Yoneda
 introduced the integral sign for ends and coends in §4 of his 1960
 dissertation, though under a convention reversed from the modern one:
 he named the coend “integration” and the end “cointegration” (Yoneda
 1960; nLab, “end”).  Mac Lane gave the textbook account — chapter IX
 of “Categories for the Working Mathematician” defines dinatural
 transformations and presents ends and coends as universal (co)wedges,
 the presentation this file inherits through Structure/Wedge and
 Structure/End (Mac Lane 1971).  Mac Lane also used a coend to render a
 construction in algebraic topology as a tensor product of functors,
 `F ⊗_C G ≅ ∫^c F c ⊗ G c`, with `C` cast in the role of the ring
 (reported in Loregian's survey).  Loregian later supplied the first
 book-length treatment and described the technique as a “secret weapon”
 of working category theorists (Loregian 2021).

 The utility is the calculus itself: a compact algebra of integral
 manipulations that replaces long diagram chases.  Its basic reduction
 is the co-Yoneda, or “ninja Yoneda”, lemma — every functor is a coend
 of representables, `∫^{c'} C(c', c) · F c' ≅ F c` — proven in Sets in
 Theory/Coend/Yoneda.v; its second rule is the Fubini interchange
 `∫^{(c,d)} H ≅ ∫^c ∫^d H` (Theory/Coend/Fubini.v).  Over these run the
 applications: Day convolution, which makes a functor category
 monoidal by `(F * G) c ≅ ∫^{a,b} C(a ⊗ b, c) · F a · G b`
 (Day 1970; Construction/Day.v); profunctor composition
 `(Q ∘ P)(c, e) ≅ ∫^d P(c, d) × Q(d, e)` (Theory/Profunctor.v,
 Construction/Profunctor/Compose.v); the pointwise left Kan extension
 `∫^c D(K c, d) · F c`, the coend presentation of the extension that
 Theory/Kan/Extension.v instead builds through an adjunction; and the
 geometric realization of a simplicial set as a single coend (nLab,
 “coend”).

 Computationally a coend is an existential type.  An element of
 `∫^c F(c, c)` is a pair `(c, a)` with `a : F(c, c)` — a hidden object
 together with a value — taken modulo the dinaturality gluing that
 identifies `(c, F(f, 1) b)` with `(c', F(1, f) b)`; dually an end is
 a polymorphic `∀ c. …` carrying a naturality side-condition
 (Milewski, “Category Theory for Programmers”, §26).  This is the
 shape of the concrete coend in Instance/Sets/Coend.v, where an
 injection at a witness is quotiented by exactly that relation, and it
 is why existential and parametric encodings stand in for coends in
 profunctor-optics libraries (Clarke et al., “Profunctor Optics, a
 Categorical Update”, arXiv 2020). 

 --------
 共端演算、它的历史以及存在性解读

 nLab: https://ncatlab.org/nlab/show/coend
 书籍: Loregian, “(Co)end Calculus”, 伦敦数学会讲义系列 468, 剑桥大学出版社 2021
 论文: Yoneda, “关于 Ext 与正合列”, 东京大学理学院学报 第 I 卷, 8 (1960) 507–576
 书籍: Mac Lane, “面向工作数学家的范畴论”, 施普林格 1971 (第 2 版 1998), 第九章
 论文: Day, “关于函子闭范畴”, 中西部范畴研讨会 IV, 施普林格 LNM 137 (1970) 1–38共端(coend)将一个混合方差的函子在其对角线上积分为目标范畴中的单一对象，它可以完成普通余极限无法完成的工作。余极限可以粘合一个协变图；而共端则是接收注入且使得两个函子作用相等的普适对象。具体来说，它是下列的等化子(coequalizer)

 ∐_{f : c → c'} F(c', c) ⇉ ∐_c F(c, c) → ∫^c F(c, c)

 迫使逆变作用和协变作用一致(nLab, “coend”)；这可以将共端理解为一个商，而不是一族方程。许多典型构造本质上是混合方差的，正是这些构造，而不是协变图，才是共端旨在表达的。符号和微积分逐层积累。Yoneda 在他 1960 年的论文第 §4 节中引入了端与共端的积分符号，尽管采用的约定与现代的相反：他将共端称为“积分”，将端称为“共积分”（Yoneda 1960；nLab，“end”）。Mac Lane 给出了教材式的描述——《Categories for the Working Mathematician》第 IX 章定义了准自然变换，并将端与共端作为普遍的（共）楔子呈现，本文件通过 Structure/Wedge 和 Structure/End 继承了该呈现方式（Mac Lane 1971）。Mac Lane 还使用共端将代数拓扑中的一个构造表示为函子张量积，`F ⊗_C G ≅ ∫^c F c ⊗ G c`，其中 `C` 被赋予环的角色（Loreggian 的综述中有报道）。Loregian 后来提供了第一本书长度的论述，并将这一技术描述为范畴论工作者的“秘密武器”（Loregian 2021）。这个工具本身就是微积分：一种紧凑的积分操作代数，可以替代冗长的图式追踪。它的基本约化是共约内达引理（co-Yoneda，或者称“忍者约内达”引理）——每个函子都是可表示函子的共内端，`∫^{c'} C(c', c) · F c' ≅ F c`——在 Sets 的 Theory/Coend/Yoneda.v 中证明；它的第二条规则是 Fubini 交换律 `∫^{(c,d)} H ≅ ∫^c ∫^d H`（Theory/Coend/Fubini.v）。在这些之上运行的应用包括：Day卷积，它通过`(F * G) c ≅ ∫^{a,b} C(a ⊗ b, c) · F a · G b`使函子范畴成为幺半群 (Day 1970；Construction/Day.v)；Profunctor的复合`(Q ∘ P)(c, e) ≅ ∫^d P(c, d) × Q(d, e)` (Theory/Profunctor.v, Construction/Profunctor/Compose.v)；逐点左Kan扩展`∫^c D(K c, d) · F c`，扩展的coend表示，而Theory/Kan/Extension.v通过伴随建立该表示；以及将单纯集合的几何实现作为单个coend (nLab, “coend”)。从计算的角度来看，coend 是一种存在类型。`∫^c F(c, c)` 的一个元素是一个对 `(c, a)` 和 `a : F(c, c)` —— 一个隐藏对象和一个值 —— 根据同自然性粘合模掉的，其中 `(c, F(f, 1) b)` 被识别为 `(c', F(1, f) b)`；相对地，end 是一个多态的 `∀ c. …`，并携带一个自然性附加条件（Milewski，《程序员的范畴论》，§26）。这是 Instance/Sets/Coend.v 中具体 coend 的形式，其中一个在见证上的注入正是通过该关系取商，并且这也解释了为什么存在类型和参数编码在 profunctor-optics 库中可以代替 coend（Clarke 等，《Profunctor Optics，一次范畴更新》，arXiv 2020）。
*)

(*
   【Coend API 展开】/ API walkthrough（薄）

   1) Coend 定义在 End.v（对偶）；本文件给**共变**访问器与建造。
      Coend is defined by duality in End.v; this file is the covariant API.
      ∫^c F(c,c) ≈「存在类型」：隐藏对象 c 与值，按余楔关系商掉。
      Computational reading: existential (c, a : F(c,c)) modulo cowedge.

   2) 要点 / Key pieces
      coend_obj / coend_inj —— 顶点与内射
      Cowedge_cond / coend_med / Build_Coend —— 余楔条件、中介、构造
      连到 profunctor 复合、Day 卷积、Kan（见文首史注）。

   阅读：End/Wedge → 本 Section → Yoneda/Fubini（Theory/Coend/）。
   Read: End/Wedge → this Section → Yoneda/Fubini under Theory/Coend/.
*)

Section Coend.

Context {C : Category}.
Context {D : Category}.
Context {F : C^op ∏ C ⟶ D}.

(*
   * The coend object `∫^c F(c,c)` of `D`: the apex of the underlying end
   wedge, read as an object of `D` (objects of `D^op` are objects of `D`). 

   --------
   * `D` 的余联合对象 `∫^c F(c,c)`：基础端楔的顶点，作为 `D` 的对象来读取（`D^op` 的对象是 `D` 的对象）。
*)
Definition coend_obj (E : Coend F) : D :=
  @Wedge_to_obj (C^op) (D^op) (F^op) (@end_wedge (C^op) (D^op) (F^op) E).

(*
   * The injection `coend_inj_x : F (x, x) ~> coend_obj`: the underlying wedge
   leg `wedge_obj ~{D^op}~> F^op (x, x)`, read reversed in `D`. 

   --------
   * 注射 `coend_inj_x : F (x, x) ~> coend_obj`：基础楔子腿 `wedge_obj ~{D^op}~> F^op (x, x)`，在 `D` 中反向读取。
*)
Definition coend_inj (E : Coend F) {x : C} :
  F (x, x) ~{D}~> coend_obj E :=
  @wedge_map (C^op) (D^op) (F^op) (@end_wedge (C^op) (D^op) (F^op) E) x.

(*
   * The covariant cowedge (co-dinaturality) condition, obtained from the
   underlying wedge condition of `end_wedge` by one `symmetry`. For
   `f : x ~> y` both composites run `F (y, x) ~> coend_obj`. 

   --------
   * 协变余楔（共自然性）条件，由 `end_wedge` 的基础楔条件通过一个 `symmetry` 得到。对于 `f : x ~> y`，两个复合都运行 `F (y, x) ~> coend_obj`。
*)
Lemma coend_cowedge (E : Coend F) {x y : C} (f : x ~{C}~> y) :
  @coend_inj E x ∘ bimap[F] (op f) id ≈ @coend_inj E y ∘ bimap[F] id f.
Proof.
  symmetry.
  exact (@ump_wedges (C^op) (D^op) (F^op)
           (@end_wedge (C^op) (D^op) (F^op) E) y x (op f)).
Qed.

(*
   * Covariant cowedge data on a candidate apex `w`: a family of legs
   `i x : F (x, x) ~> w` satisfying the cowedge condition. This packages the
   hypotheses of the coend's universal property and of the smart constructor
   below. 

   --------
   * 候选顶点 `w` 上的协变 cowedge 数据：一族满足 cowedge 条件的边 `i x : F (x, x) ~> w`。它封装了余端的普遍性性质假设以及下方智能构造函数的假设。
*)
Definition Cowedge_cond (w : D) (i : ∀ x : C, F (x, x) ~{D}~> w) : Type :=
  ∀ (x y : C) (f : x ~{C}~> y),
    i x ∘ bimap[F] (op f) id ≈ i y ∘ bimap[F] id f.

(*
   * Covariant cowedge data assembles into an underlying `Wedge F^op`
   (equivalently a `Cowedge F`). The wedge condition is the covariant
   `cond` read back through `F^op` by one `symmetry`; this is the inverse of
   the reading performed in [coend_cowedge]. 

   --------
   * 协变楔形数据组装成一个底层的 `Wedge F^op`（等价于 `Cowedge F`）。楔形条件是通过一个 `symmetry` 从 `F^op` 读取回来的协变 `cond`；这是在 [coend_cowedge] 中执行读取的逆操作。
*)
Definition covariant_cowedge (w : D)
  (i : ∀ x : C, F (x, x) ~{D}~> w) (cond : Cowedge_cond w i) :
  @Wedge (C^op) (D^op) (F^op).
Proof.
  unshelve refine (@Build_Wedge (C^op) (D^op) (F^op) w (fun x => i x) _).
  intros x y f.
  symmetry.
  exact (cond y x f).
Defined.

(*
   * The coend universal property, stated covariantly: every cowedge
   `(w, i)` over `F` factors through the coend by a unique mediator
   `u : coend_obj ~> w` recovering each leg, `u ∘ coend_inj_x ≈ i x`. This is
   the end UMP `ump_ends` read on the cowedge `covariant_cowedge w i cond`. 

   --------
   * 共终端的泛性质，协变表述：每一个在 `F` 上的余楔 `(w, i)` 都可以通过一个唯一的中介 `u : coend_obj ~> w` 因式分解，从而恢复每一条腿 `u ∘ coend_inj_x ≈ i x`。这是读取余楔 `covariant_cowedge w i cond` 时的终端 UMP `ump_ends`。
*)
Lemma coend_ump (E : Coend F)
  (w : D) (i : ∀ x : C, F (x, x) ~{D}~> w) (cond : Cowedge_cond w i) :
  ∃! u : coend_obj E ~{D}~> w, ∀ x : C, u ∘ coend_inj E ≈ i x.
Proof.
  exact (@ump_ends (C^op) (D^op) (F^op) E (covariant_cowedge w i cond)).
Qed.

(** The mediating morphism out of a coend into any cowedge. / 从共端到任意余楔的中介态射。 *)
Definition coend_med (E : Coend F) (w : D)
  (i : ∀ x : C, F (x, x) ~{D}~> w) (cond : Cowedge_cond w i) :
  coend_obj E ~{D}~> w :=
  unique_obj (coend_ump E w i cond).

(** The mediator recovers each leg of the target cowedge. / 调解人恢复目标牛楔的每条腿。 *)
Lemma coend_med_inj (E : Coend F) (w : D)
  (i : ∀ x : C, F (x, x) ~{D}~> w) (cond : Cowedge_cond w i) (x : C) :
  coend_med E w i cond ∘ coend_inj E ≈ i x.
Proof.
  unfold coend_med.
  exact (unique_property (coend_ump E w i cond) x).
Qed.

(*
   * Any morphism factoring the injections through the same legs equals the
   mediator. 

   --------
   * 通过相同支腿分解注入的任何态射都等于中介态射。
*)
Lemma coend_med_unique (E : Coend F) (w : D)
  (i : ∀ x : C, F (x, x) ~{D}~> w) (cond : Cowedge_cond w i)
  (v : coend_obj E ~{D}~> w) :
  (∀ x : C, v ∘ coend_inj E ≈ i x) -> coend_med E w i cond ≈ v.
Proof.
  intro Hv.
  unfold coend_med.
  exact (uniqueness (coend_ump E w i cond) v Hv).
Qed.

(*
   * Two mediators out of a coend that agree on every injection are equal.
   This lets one prove `u ≈ v` without exhibiting `coend_med` explicitly. 

   --------
   * 两个在每个单射上都一致的余端中介是相等的。  
   这让人可以在不显式展示 `coend_med` 的情况下证明 `u ≈ v`。
*)
Lemma coend_med_eq (E : Coend F) (w : D)
  (i : ∀ x : C, F (x, x) ~{D}~> w) (cond : Cowedge_cond w i)
  (u v : coend_obj E ~{D}~> w) :
  (∀ x : C, u ∘ coend_inj E ≈ i x) ->
  (∀ x : C, v ∘ coend_inj E ≈ i x) -> u ≈ v.
Proof.
  intros Hu Hv.
  transitivity (coend_med E w i cond).
  - symmetry.
    now apply coend_med_unique.
  - now apply coend_med_unique.
Qed.

(*
   * A `Build_Coend`-style smart constructor: a coend is assembled from
   covariant cowedge data `(w, i, cond)` together with its covariant
   universal property `ump`. The underlying end wedge is
   `covariant_cowedge w i cond`; the end UMP `ump_ends` is discharged by
   reading each competing `Wedge F^op` back into covariant cowedge data and
   applying `ump`. 

   --------
   * `Build_Coend` 风格的智能构造器：coend 是由协变 cowedge 数据 `(w, i, cond)` 以及它的协变通用性质 `ump` 组装而成的。其底层的 end wedge 为 `covariant_cowedge w i cond`；end UMP `ump_ends` 通过将每个竞争的 `Wedge F^op` 重新读回协变 cowedge 数据，并应用 `ump` 来处理。
*)
Definition Build_Coend (w : D)
  (i : ∀ x : C, F (x, x) ~{D}~> w) (cond : Cowedge_cond w i)
  (ump : ∀ (w' : D) (i' : ∀ x : C, F (x, x) ~{D}~> w')
           (cond' : Cowedge_cond w' i'),
           ∃! u : w ~{D}~> w', ∀ x : C, u ∘ i x ≈ i' x) :
  Coend F.
Proof.
  unshelve refine
    (@Build_End (C^op) (D^op) (F^op) (covariant_cowedge w i cond) _).
  intros W.
  refine (ump (@Wedge_to_obj (C^op) (D^op) (F^op) W)
              (fun x => @wedge_map (C^op) (D^op) (F^op) W x)
              (fun x y f => _)).
  symmetry.
  exact (@ump_wedges (C^op) (D^op) (F^op) W y x (op f)).
Defined.

End Coend.

Arguments coend_obj {C D F} E.
Arguments coend_inj {C D F} E {x}.
Arguments Cowedge_cond {C D} F w i.
Arguments coend_cowedge {C D F} E {x y} f.
Arguments coend_ump {C D F} E w i cond.
Arguments coend_med {C D F} E w i cond.
Arguments Build_Coend {C D F} w i cond ump.
