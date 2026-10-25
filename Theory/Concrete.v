Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Sets.
Require Import Category.Functor.Hom.

Generalizable All Variables.

(** * Concrete categories / * 具体范畴 *)

(*
nLab:      https://ncatlab.org/nlab/show/concrete+category
   Wikipedia: https://en.wikipedia.org/wiki/Concrete_category
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              GTM 5, Springer 1998, §I.7 ("Large Categories"), printed p. 26
   Book:      Riehl, "Category Theory in Context", Dover 2016, §1.6,
              Definition 1.6.18 and Example 1.6.19, printed pp. 45-46
   Book:      Awodey, "Category Theory", 2nd ed., OUP 2010, §1.5, Remark 1.7,
              printed p. 15
   Paper:     Freyd, "Homotopy is not concrete", in "The Steenrod Algebra and
              Its Applications", Lecture Notes in Mathematics 168, Springer
              1970, pp. 25-34

   A concrete category, in Mac Lane's §I.7 sense, is a PAIR `⟨C, U⟩`: a
   category together with a chosen faithful functor `U : C ⟶ Sets`.  The
   pairing is the whole point.  Concreteness is not a property a category has
   on its own; it is structure one equips a category with, and different
   choices of `U` on the same `C` give different concrete categories.  The
   class below therefore carries the functor as a field rather than
   existentially quantifying it.

   The intended reading — every object has an underlying set, and every arrow
   is an actual function between those sets — is recorded here as a
   definitional unfolding rather than as a separate axiom, since it IS what
   the two fields say once they are unfolded:

     - the object part `underlying x` is the underlying set of `x`;
     - the arrow part `fmap[underlying] f` is the actual function
       carried by `f`, and `fmap_respects` says an arrow determines its
       function;
     - `underlying_faithful` says the function determines the arrow.

   [concrete_arrow_eq] below is the second bullet's converse spelled out at
   the level of elements: two parallel arrows agreeing pointwise on the
   underlying sets are already equal in `C`.  This is Riehl's gloss
   (Definition 1.6.18): being a morphism is a PROPERTY of the underlying
   function — continuity, say — rather than extra data, and a forgetful
   functor is not faithful exactly when morphisms carry structure invisible
   on the underlying sets.

   Note the setoid discipline of this library.  `Sets` (Instance/Sets.v) is
   the category of setoids, so "the underlying set" is a carrier type plus an
   equivalence relation, and "actual function" means a setoid map.  Equality
   of arrows in THIS FILE and its two companions is `≈` throughout, never
   `=` — a claim about these three files only, not about the library, which
   does state a few deliberate arrow equalities elsewhere (for instance
   Construction/Quotient.v's cast-irrelevance lemmas).  Concretely, faithfulness reads
   `fmap f ≈ fmap g → f ≈ g` with `≈` at both ends: the `Sets`-side `≈` is
   pointwise equivalence of setoid maps, the `C`-side `≈` is `C`'s hom-setoid.

   Awodey's refinement (§1.5, Remark 1.7) is developed in the second half of
   this file.  He observes that the naive notion is defective and proposes
   testing arrows against GENERALIZED ELEMENTS: arrows `f, g : x ~> y` should
   be determined by their composites `f ∘ e`, `g ∘ e` with maps `e : t ~> x`
   out of a test object `t`.  An object with that property is a separator (a
   generator): [Separator] below.  A separator is exactly what makes the
   representable `Hom(t, −) : C ⟶ Sets` faithful, so every separator
   concretizes its category — [Concrete_of_Separator].  Awodey's own case is
   `t` terminal, i.e. testing by global elements; that is
   [WellPointedCategory], and it yields [Concrete_of_WellPointed].

   Naming caution: [WellPointedCategory] here is unrelated to the
   [WellPointed] class of Instance/Fun.v, which is a condition on a
   POINTED ENDOFUNCTOR (`F ⊳ point` and `point ⊲ F` agreeing), not on a
   category.  The two notions share only the English adjective; hence the
   distinct name.

   Disclosed deferrals (the two negative halves of Mac Lane's §I.7 remark)
   ---------------------------------------------------------------------

   (1) Toph, the pointed homotopy category, has NO faithful functor to
       sets whatsoever (Freyd 1970).  That theorem is out of scope here and
       is not proved, weakened, or assumed anywhere in this development.  It
       is not even stateable in-tree yet: the library has no homotopy
       category.  Riehl records the same result as a footnote to Definition
       1.6.18.

   (2) Rel, the category of sets and relations (Instance/Rel.v), is often
       quoted alongside Toph as "not concrete".  That quotation is too
       strong, and this development does not repeat it.  What is true, and
       what Instance/Concrete.v proves, is a statement about the EVIDENT
       candidate functor: no functor `U : Rel ⟶ Sets` whose value at the
       one-element set is a subsingleton can be faithful, because Rel already
       has two distinct endorelations of the one-element set.  The evident
       "underlying set" candidate has exactly that property, so it is not
       faithful.  Rel is nevertheless concretizable — Instance/Concrete.v
       exhibits `Rel_Concrete` via the direct-image (powerset) functor, whose
       value at the one-element set is a two-element setoid, precisely
       escaping the obstruction.  So the honest reading of Mac Lane's remark
       is "not concrete via its evident forgetful functor", and that is what
       is proved.  Non-concretizability of Rel is not claimed and would in
       fact be false.

--------
nLab:      https://ncatlab.org/nlab/show/concrete+category
   维基百科: https://en.wikipedia.org/wiki/Concrete_category
   书籍:      Mac Lane, 《为工作数学家准备的范畴论》，第2版，
              GTM 5, Springer 1998, §I.7（“大范畴”），印刷页 26
   书籍:      Riehl, 《语境中的范畴论》，Dover 2016, §1.6,
              定义 1.6.18 和 例子 1.6.19，印刷页 45-46
   书籍:      Awodey, 《范畴论》，第2版，OUP 2010, §1.5, 注释 1.7,
              印刷页 15
   论文:     Freyd, 《同伦不是具体的》，收录于《Steenrod 代数及其应用》，
              数学讲义 168, Springer 1970, 页 25-34

在麦克·莱恩（Mac Lane）§I.7 的定义中，一个具体范畴是一个成对的结构：一个范畴以及一个选定的忠实函子。这个配对是关键所在。具体性不是范畴自身所具有的属性；它是你为范畴配备的一种结构，在同一个范畴上不同的选择会产生不同的具体范畴。因此，下述类将函子作为一个字段携带，而不是通过存在量化去描述它。

预期的理解——每个对象都有一个基本集合，每个箭头都是这些集合之间的实际函数——在这里被记录为定义性的展开，而不是作为一个单独的公理，因为一旦展开，这正是两个领域所表达的内容：

- 对象部分 `underlying x` 是 `x` 的底层集合；
- 箭头部分 `fmapXPROTECT0X f` 是 `f` 实际携带的函数，而 `fmap_respects` 表示箭头决定其函数；
- `underlying_faithful` 表示函数决定箭头。

[concrete_arrow_eq] 下面是第二个要点的逆命题，在元素层面上展开：在基础集合上逐点相合的两条平行箭头在 `C` 中已经相等。这是 Riehl 的解释（定义 1.6.18）：作为态射是一种基础函数的属性——例如连续性——而不是额外的数据，而一个遗忘函子在态射承载在基础集合上不可见的结构时恰好不是忠实的。

注意这个库的集合体（setoid）纪律。`Sets`（Instance/Sets.v）是集合体的范畴，所以“底层集合”是一个承载类型加上一个等价关系，而“实际函数”意味着集合体映射。本文件及其两个伴随文件中的箭头等式始终使用`≈`，从不使用`=`——这只适用于这三个文件，并不适用于整个库，库中在其他地方确实声明了一些刻意的箭头等式（例如Construction/Quotient.v中的cast-irrelevance引理）。具体来说，忠实性读作两端都是`fmap f ≈ fmap g → f ≈ g`：`Sets`侧的`≈`是集合体映射的逐点等价，`C`侧的`≈`是`C`的Hom-集合体。

Awodey 的精炼（§1.5，注释 1.7）在本文件的下半部分展开。他指出天真的概念是有缺陷的，并提议使用广义元素对箭头进行测试：箭头 `f, g : x ~> y` 应通过它们与测试对象 `t` 的映射 `e : t ~> x` 的组合 `f ∘ e`、`g ∘ e` 来确定。具有该属性的对象是一个分离器（生成器）：下文的 [Separator]。分离器正是使可表示的 `Hom(t, −) : C ⟶ Sets` 具有忠实性的原因，因此每个分离器都能使其范畴具象化 — [Concrete_of_Separator]。Awodey 自己的例子是 `t` 终对象，即通过全局元素进行测试；也就是 [WellPointedCategory]，并且它产生 [Concrete_of_WellPointed]。

命名注意：这里的 [WellPointedCategory] 与 Instance/Fun.v 中的 [WellPointed] 类无关，后者是关于一个指向函子（`F ⊳ point` 和 `point ⊲ F` 同意）的条件，而不是关于一个范畴。这两个概念仅共享英语形容词，因此使用了不同的名称。

披露的延期（麦克莱恩 §I.7 备注的两个负半部分）
---------------------------------------------------------------------

(1) Toph，即尖点同伦范畴，根本没有忠实函子到集合（Freyd 1970）。该定理在这里超出讨论范围，在本发展中既未证明、也未弱化或假设。它甚至尚不能以树形形式表述：库中没有同伦范畴。Riehl 在定义 1.6.18 的脚注中记录了同样的结果。

(2) Rel，即集合与关系的范畴（Instance/Rel.v），常与 Toph 一起被引用为“非具体的”。 那个引用太强烈了，而且这一发展并没有重复它。 什么是真实的，以及 Instance/Concrete.v 所证明的，是关于 EVIDENT 候选函子的陈述：没有一个函子 `U : Rel ⟶ Sets`，其在单元素集上的值是一个子单子集，可以是忠实的，因为 Rel 已经有单元素集的两个不同自关系。 明显的“基础集合”候选者恰好具有该属性，因此它不是忠实的。 Rel 仍然是可具体化的——实例/Concrete.v 通过直接像（幂集）函子展示了 `Rel_Concrete`，其在单元素集合上的值是一个两元素的集合等价类，恰好规避了这一障碍。 所以对麦克莱恩评论的诚实解读是“不是通过其明显的遗忘函子具体化”，这就是所证明的内容。 Rel 的不可具体化性并未被声称，实际上这是错误的。
*)

Section Concrete.

(*
A concrete category: a category `C` paired with a chosen faithful functor
   to `Sets`.  Mac Lane §I.7's `⟨C, U⟩`; Riehl §1.6, Definition 1.6.18.

--------
一个具体范畴：一个范畴 `C` 与一个选定的忠实函子配对到 `Sets`。Mac Lane §I.7 的 `⟨C, U⟩`；Riehl §1.6，第 1.6.18 定义。
*)
(*
   【Class Concrete 语法与字段展开】/ Syntax & field walkthrough

   1) 这是什么 / What this is
      具体范畴 = C + 到 Sets 的忠实函子 U（「忘却到集合」）。
      Concrete = C with a chosen faithful U : C ⟶ Sets.
      箭头因此可当作真正的函数（concrete_fun）；≈ 由 U 反映。
      Arrows act as actual functions; faithfulness reflects ≈.

   2) 字段 / Fields
      - underlying : C ⟶ Sets
      - underlying_faithful : Faithful underlying

   3) 邻近 / Nearby
      Separator / WellPointed —— 用全局元素分离箭头；Sets 自身是具体且良点的。

   阅读：Faithful → underlying → concrete_fun → Separator。
   Read: Faithful → underlying → concrete_fun → Separator.
*)

Class Concrete (C : Category) := {
  underlying : C ⟶ Sets;             (* the chosen underlying-set functor U / 所选择的底层集合函子 U *)
  underlying_faithful : Faithful underlying   (* arrows ARE actual functions / 箭头实际上是函数 *)
}.

#[export] Existing Instance underlying_faithful.

Context {C : Category}.
Context `{Con : @Concrete C}.

(*
The actual function carried by an arrow: the object part of [underlying]
   supplies the underlying set of each object, and [concrete_fun f] is `f`
   read as a setoid map between those sets.  (`SetoidMorphism` coerces to its
   carrier function, so `concrete_fun f a` is literally an application.)

--------
箭头实际承担的功能：[underlying] 的对象部分提供每个对象的底层集合，而 [concrete_fun f] 是 `f`，可被视为这些集合之间的集合态映射。（`SetoidMorphism` 强制转换为其载体函数，因此 `concrete_fun f a` 从字面上就是一个应用。）
*)
Definition concrete_fun {x y : C} (f : x ~> y) :
  underlying x ~{Sets}~> underlying y := fmap[underlying] f.

(*
An arrow determines its function.  This half is just functoriality
   ([fmap_respects]); it is recorded so the two halves sit together.

--------
一个箭头决定它的功能。这一半只是函子性（[fmap_respects]）；它被记录下来以便两半可以放在一起。
*)
Lemma concrete_fun_respects {x y : C} (f g : x ~> y) :
  f ≈ g → ∀ a : carrier (underlying x), concrete_fun f a ≈ concrete_fun g a.
Proof.
  intros Hfg a.
  exact (fmap_respects (Functor:=underlying) x y f g Hfg a).
Qed.

(*
The function determines the arrow: "arrows ARE actual functions", as the
   definitional unfolding of [underlying_faithful] at the level of elements.
   Note that the conclusion is `≈` in `C`'s hom-setoid and the hypothesis is
   `≈` in the codomain setoid — no `=` occurs on either side.

--------
该函数确定箭头：“箭头是实际函数”，作为 [underlying_faithful] 在元素层面的定义展开。注意，结论是 `≈` 在 `C` 的同类集合中，假设是 `≈` 在陪域集合中——两边都没有出现 `=`。
*)
Lemma concrete_arrow_eq {x y : C} (f g : x ~> y) :
  (∀ a : carrier (underlying x), concrete_fun f a ≈ concrete_fun g a) → f ≈ g.
Proof.
  intros Hfg.
  apply (fmap_inj (F:=underlying)).
  exact Hfg.
Qed.

(*
The two halves packaged as the biconditional Riehl states: parallel arrows
   are equal exactly when the functions they carry agree pointwise.

--------
Riehl 所说的双条件包装的两个部分：当它们所携带的函数在每一点上都相同时，平行箭头才相等。
*)
Corollary concrete_arrow_iff {x y : C} (f g : x ~> y) :
  f ≈ g ↔ (∀ a : carrier (underlying x), concrete_fun f a ≈ concrete_fun g a).
Proof.
  split.
  - apply concrete_fun_respects.
  - apply concrete_arrow_eq.
Qed.

End Concrete.

Arguments concrete_fun {C Con x y} f.

(** ** Awodey's refinement: separators and well-pointedness / ** Awodey的精炼：分隔符与良好指向性 *)

Section Separator.

Context {C : Category}.

(*
nLab: https://ncatlab.org/nlab/show/separator

   A separator (generator) is a test object `t` whose generalized elements
   `e : t ~> x` jointly detect equality of arrows out of `x`.  Awodey §1.5,
   Remark 1.7 introduces exactly this condition, as the repair of the naive
   notion of concreteness.  Compare Adjunction/SAFT.v's `Cogenerator`,
   which is the dual notion (arrows INTO a test object) packaged there for
   the special adjoint functor theorem.

--------
nLab: https://ncatlab.org/nlab/show/separator

一个分离子（生成器）是一个测试对象 `t`，其广义元素 `e : t ~> x` 共同检测来自 `x` 的箭头的相等性。Awodey §1.5，备注 1.7 正是引入了这种条件，作为天真的具体性概念的修正。比较 Adjunction/SAFT.v 中的 `Cogenerator`，它是对偶概念（箭头指向测试对象），在那里为特殊伴随定理进行了封装。
*)
Class Separator (t : C) := {
  separates {x y : C} (f g : x ~> y) :
    (∀ e : t ~> x, f ∘ e ≈ g ∘ e) → f ≈ g   (* generalized elements detect ≈ / 广义元素检测 ≈ *)
}.

(*
A separator concretizes: `Hom(t, −)` is faithful precisely when `t`
   separates, since `fmap[Hom(t,−)] f ≈ fmap[Hom(t,−)] g` unfolds to
   `∀ e : t ~> x, f ∘ e ≈ g ∘ e`.  This is the exact sense in which Awodey's
   refinement implies (his version of) concreteness.

--------
分离器具体化：`Hom(t, −)` 精确地忠实于 `t`
 分开，因为 `fmapXPROTECT0X f ≈ fmapXPROTECT1X g` 展开为
 `∀ e : t ~> x, f ∘ e ≈ g ∘ e`。 这正是 Awodey 的意义
 精致意味着（他的版本）具体。
*)
Program Definition Concrete_of_Separator (t : C) `{@Separator t} :
  Concrete C := {|
  underlying := fobj[Curried_Hom C] t
|}.
Next Obligation.
  constructor; simpl; intros x y f g Hfg.
  apply (separates (t:=t)).
  intro e.
  exact (Hfg e).
Qed.

(*
The converse reading: whenever `Hom(t, −)` is faithful, `t` separates.  So
   [Separator t] and faithfulness of the representable are interderivable, and
   neither direction is an extra assumption.

--------
相反的读法：每当 `Hom(t, −)` 忠诚时，`t` 就分离。因此 [Separator t] 与可表示对象的忠诚性是可相互推导的，并且两个方向都不是额外的假设。
*)
Definition Separator_of_Faithful (t : C)
  (H : Faithful (fobj[Curried_Hom C] t)) : Separator t.
Proof.
  constructor; intros x y f g Hfg.
  apply (fmap_inj (F:=fobj[Curried_Hom C] t)).
  simpl; intro e.
  exact (Hfg e).
Qed.

End Separator.

Arguments separates {C} t {Separator x y} f g _.

(*
Awodey's own case: the test object is terminal, so generalized elements are
   GLOBAL elements `1 ~> x` — the points of `x`.  A category in which the
   terminal object separates is well-pointed.

   This is a property of a CATEGORY equipped with a terminal object.  It has
   nothing to do with the [WellPointed] class of Instance/Fun.v, which is
   a coherence condition on a pointed endofunctor; the names are kept apart
   deliberately.

--------
Awodey 本人的例子：测试对象是终端对象，因此广义元素是全局元素 `1 ~> x` —— `x` 的点。一个终端对象能够分离的范畴是良点的。

这是一个配备了终端对象的范畴的性质。它与 Instance/Fun.v 中的 [WellPointed] 类无关，后者是一个关于有指向的自函子的相容性条件；这些名称是特意区分开的。
*)
Definition WellPointedCategory (C : Category) `{T : @Terminal C} : Type :=
  Separator (@terminal_obj C T).

(*
A well-pointed category is concrete, via its global-elements functor
   `Hom(1, −)`.  This is Awodey's refined notion of concreteness.

--------
一个良好指向的范畴是具体的，通过它的全局元函子 `Hom(1, −)`。这是 Awodey 提出的精炼具体性概念。
*)
Definition Concrete_of_WellPointed {C : Category} `{T : @Terminal C}
  (W : WellPointedCategory C) : Concrete C :=
  @Concrete_of_Separator C (@terminal_obj C T) W.

(** ** The category of setoids is concrete, and well-pointed / ** 集合类的范畴是具体的，并且是良点的 *)

(*
`Sets` is concrete by way of its identity functor: an object IS its
   underlying set and an arrow IS its function.  Faithfulness is then the
   identity implication.  This instance is the degenerate one, and it is NOT
   vacuous: `Sets` has parallel arrows that differ, as [Sets_two_arrows]
   below witnesses.

--------
`Sets` 是通过其恒等函子具体化的：一个对象就是它的底层集合，一条箭头就是它的函数。忠实性然后就是恒等的含义。这个实例是退化的，并且它不是空的：`Sets` 有平行的箭头，它们彼此不同，正如下面的 [Sets_two_arrows] 所证明的那样。
*)
#[export] Program Instance Sets_Concrete@{o so+} : Concrete Sets@{o so} := {|
  underlying := Id[Sets@{o so}]
|}.
Next Obligation.
  constructor; simpl; intros x y f g Hfg.
  exact Hfg.
Qed.

(*
The two-element setoid, used below to show the `Sets` instance has
   content.

--------
下面使用的二元集合，用于显示 `Sets` 实例具有内容。
*)
Definition bool_setoid_object@{t u+} : SetoidObject@{t u} :=
  {| carrier   := bool
   ; is_setoid := {| equiv := @eq bool ; setoid_equiv := eq_equivalence |} |}.

(*
Non-vacuity of [Sets_Concrete]: faithfulness is not free, because the
   hom-setoid it is injective on is not trivial.  The identity and negation
   maps on the two-element setoid are parallel arrows that are DISTINCT in
   the hom-setoid `bool_setoid_object ~{Sets}~> bool_setoid_object`, whose
   `≈` is pointwise equality of the underlying functions.

--------
[Sets_Concrete] 的非空性：忠诚不是免费的，因为它所注入的同态集合不是平凡的。两个元素集合上的恒等映射和取反映射是在同态集合 `bool_setoid_object ~{Sets}~> bool_setoid_object` 中平行但不同的箭头，其 `≈` 是底层函数的逐点相等。
*)
Program Definition Sets_negb@{o so+} :
  bool_setoid_object@{o o} ~{Sets@{o so}}~> bool_setoid_object@{o o} :=
  {| morphism := negb |}.

(*
Stated with an explicit `→ False` rather than `¬`: hom-equivalence in this
   library is a `crelation`, i.e. `Type`-valued, and `¬` is `Prop`-valued.

--------
用明确的 `→ False` 而不是 `¬` 陈述：在这个库中，同构等价性是 `crelation`，即 `Type` 值，而 `¬` 是 `Prop` 值。
*)
Lemma Sets_two_arrows@{o so+} :
  @id Sets@{o so} bool_setoid_object@{o o} ≈ Sets_negb@{o so} → False.
Proof.
  intro Heq.
  (*
`≈` in this hom-setoid is pointwise `=` on `bool`; instantiate at
     `true`.

--------
在这个同值域中，`≈` 在 `bool` 上是按点 `=` 的；在 `true` 上实例化。
*)
  specialize (Heq true).
  simpl in Heq.
  discriminate.
Qed.

(*
The point of a setoid `x` at an element `a`: the constant map out of the
   singleton terminal object.  This is the same probe Instance/Sets.v uses to
   characterize monos as injections.

--------
在元素 `a` 上的集合 `x` 的点：来自单元素终对象的恒等映射。这与 Instance/Sets.v 用来将单射表征为注入的探针相同。
*)
Program Definition Sets_point@{o so+} {x : Sets@{o so}} (a : carrier x) :
  @terminal_obj Sets Sets_Terminal ~{Sets}~> x := {| morphism := fun _ => a |}.

(*
`Sets` is well-pointed: a point of `x` is a map out of the singleton
   setoid, and the constant map at `a` is such a point picking out `a`.  So
   global elements detect equality of setoid maps.

--------
`Sets` 很明确：`x` 的一个点是单元素集合的集同态，而在 `a` 的常量映射就是这样一个指向 `a` 的点。因此，全局元素能够检测集同态映射的相等性。
*)
#[export] Instance Sets_Separator@{o so+} :
  @Separator Sets@{o so} (@terminal_obj Sets@{o so} Sets_Terminal@{so o}).
Proof.
  constructor.
  intros x y f g Hfg a.
  exact (Hfg (Sets_point a) ttt).
Qed.

Definition Sets_WellPointed@{o so+} : WellPointedCategory Sets@{o so} :=
  Sets_Separator@{o so}.

(*
[Separator] is a genuine condition on an object, not one every object
   satisfies: the EMPTY setoid is not a separator of `Sets`, because there is
   nothing to probe with — every hypothesis of the separator condition holds
   vacuously, so it would identify the two distinct arrows of
   [Sets_two_arrows].  Recording this keeps the class from being read as
   content-free.

--------
[Separator] 是对象上的一个真实条件，而不是每个对象都满足的条件：EMPTY 集合化对象不是 `Sets` 的分离器，因为没有什么可以进行探测 —— 分离器条件的每个假设都是空洞地成立的，因此它会识别 [Sets_two_arrows] 的两个不同箭头。记录这一点可以防止该类被解读为无内容。
*)
Definition empty_setoid_object@{t u+} : SetoidObject@{t u} :=
  {| carrier := False ; is_setoid := False_Setoid@{u} |}.

Lemma Sets_empty_not_Separator@{o so+} :
  @Separator Sets@{o so} empty_setoid_object@{o o} → False.
Proof.
  intro Hsep.
  destruct Hsep as [sep].
  apply Sets_two_arrows@{o so}.
  apply sep.
  intros e a.
  destruct a.
Qed.

(*
The global-elements concretization of `Sets` obtained from
   well-pointedness.  It is a SECOND concrete structure on the same category:
   its underlying-set functor is `Hom(1, −)` where [Sets_Concrete]'s is the
   identity.  The two are different data — which is why Mac Lane's definition
   pairs the functor with the category — and no claim is made here about how
   the two functors compare up to natural isomorphism.

--------
从良指性获得的 `Sets` 的全局元素具体化。它是在同一范畴上的第二个具体结构：它的基础集合函子是 `Hom(1, −)`，而 [Sets_Concrete] 的则是恒等函子。这两者是不同的数据——这也是为什么 Mac Lane 的定义将函子与范畴配对——并且这里没有对两个函子在自然同构意义下的比较作出任何声明。
*)
Definition Sets_Concrete_Points@{o so+} : Concrete Sets@{o so} :=
  Concrete_of_WellPointed Sets_WellPointed@{o so}.
