Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Internal.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(*
   * * The currying adjunction (- × S) ⊣ (-)^S, and evaluation as its counit 

   --------
   * * 柯里化伴随 (- × S) ⊣ (-)^S，以及作为其余单元的求值
*)

(*
 nLab: https://ncatlab.org/nlab/show/exponential+object
 nLab: https://ncatlab.org/nlab/show/adjoint+functor
 nLab: https://ncatlab.org/nlab/show/representable+functor
 Book: Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 Springer 1998; §I.4 (Natural Transformations) and Chapter IV
 (Adjoints), §6 (Cartesian Closed Categories)
 Book: Riehl, “Category Theory in Context”, Dover 2016; §2.1
 (Representable functors), Example 2.1.6(iv)

 Structure/Cartesian/Closed.v already carries the currying bijection: the
 field [exp_iso] of [Closed] is the setoid isomorphism

 (x × S ~> z)  ≊  (x ~> z^S),

 with [curry] its forward direction, [uncurry] its inverse, and
 [eval := uncurry id]. What that class does NOT do is exhibit the two sides
 as functors and the bijection as natural in x and z; the [Closed] class
 states the bijection objectwise and recovers the substitution laws
 ([curry_comp_l], [curry_comp], [uncurry_comp], [uncurry_comp_r]) as
 corollaries. This file assembles those corollaries into the structure they
 are the naturality squares of.

 Fixing an object S of a cartesian closed C, this file builds:

 - [Prod_Functor S] : C ⟶ C, the endofunctor (- × S), acting on arrows by
 [first];
 - [Exp_Functor S] : C ⟶ C, the endofunctor (-)^S, acting on arrows by
 f ↦ curry (f ∘ eval) — the internal-hom bifunctor of
 Functor/Hom/Internal.v with its contravariant argument held at S, as
 [Exp_Functor_InternalHom] records;
 - [eval_natural], the naturality of evaluation in its target (base)
 variable: f ∘ eval ≈ eval ∘ (curry (f ∘ eval) × id[S]);
 - [eval_Transform] : Prod_Functor S ◯ Exp_Functor S ⟹ Id[C], that same
 square bundled as a natural transformation with components [eval];
 - [Curry_Adjunction] : Prod_Functor S ⊣ Exp_Functor S, the adjunction in
 the hom-set form of Theory/Adjunction.v, whose transposes are [curry]
 and [uncurry] and whose counit is [eval] and unit [curry id] — both
 recorded below and both holding by [reflexivity], not merely up to ≈;
 - [Curry_Representable], an instance of [Representable] for the presheaf
 X ↦ C(X × S, B), with representing object B^S — the first inhabitant
 of that class in the tree, found by typeclass resolution
 ([Curry_Representable_resolves]) and read back through the class's
 own coercion ([Curry_repr_obj]).

 Note on the exponential's argument order: [exponent_obj x y] is displayed
 y ^ x, so the endofunctor (-)^S is [fun x => x ^ S], i.e.
 [fun x => exponent_obj S x], and [eval] at x is the arrow x^S × S ~> x.

 The header of Theory/Adjunction.v (in the paragraph beginning
 “For the functional programmer”) says in prose that “the function type
 arises from − × a ⊣ (−)^a with eval as counit”. [Curry_Adjunction] and
 [curry_adj_counit] are that sentence as a theorem. The Sets model — where
 the counit computes to e(h, s) = h s — is
 Instance/Sets/Cartesian/Closed/Adjunction.v. 

 --------
 nLab: https://ncatlab.org/nlab/show/exponential+object
 nLab: https://ncatlab.org/nlab/show/adjoint+functor
 nLab: https://ncatlab.org/nlab/show/representable+functor
 书籍: Mac Lane，《为从事数学研究的类论者》(Categories for the Working Mathematician)，第2版，施普林格 1998；§I.4（自然变换）和第IV章（伴随），§6（笛卡尔封闭类）
 书籍: Riehl，《语境中的类论》(Category Theory in Context)，多佛 2016；§2.1（可表示函子），例2.1.6(iv)

 Structure/Cartesian/Closed.v 已经包含了柯里化双射：[Closed] 的字段 [exp_iso] 是集合同构

 (x × S ~> z) ≊ (x ~> z^S)使用 [curry] 表示它的正向，[uncurry] 表示它的逆向，以及 [eval := uncurry id]。这个类**不**做的是将两个方面展示为函子，并且将双射展示为关于 x 和 z 自然的；[Closed] 类以对象的方式陈述双射，并恢复替换律（[curry_comp_l]、[curry_comp]、[uncurry_comp]、[uncurry_comp_r]）作为推论。此文件将这些推论组合成它们作为自然性方格的结构。

 固定笛卡尔封闭范畴 C 的一个对象 S，本文件构建：-  [Prod_Functor S]  : C ⟶ C，函子 (- × S)，在箭头上的作用为 [first] ；
 -  [Exp_Functor S]  : C ⟶ C，函子 (-)^S，在箭头上的作用为 f ↦ curry (f ∘ eval) — Functor/Hom/Internal.v 中的内部 Hom 双函子，其逆变参数固定为 S，如 [Exp_Functor_InternalHom] 所记录；
 -  [eval_natural]，评价映射在其目标（基）变量上的自然性：f ∘ eval ≈ eval ∘ (curry (f ∘ eval) × id [S])；
 -  [eval_Transform] : Prod_Functor S ◯ Exp_Functor S ⟹ Id [C]，同一个方形作为自然变换捆绑，其分量为 [eval]；
 -  [Curry_Adjunction] : Prod_Functor S ⊣ Exp_Functor S，Theory/Adjunction.v 中同态集形式的伴随，其转置为 [curry] 和 [uncurry]，余单位为 [eval]，单位为 [curry id] — 两者记录如下，并且都由 [reflexivity] 持有，而不仅仅是达到 ≈；
 -  [Curry_Representable]，[Representable] 的一个实例，用于预层 X ↦ C(X × S, B)，其表示对象为 B^S — 该类在树中的第一个成员，通过类型类解析（[Curry_Representable_resolves]）找到，并通过该类自身的强制转换（[Curry_repr_obj]）读取回来。关于指数的参数顺序的说明：[exponent_obj x y] 显示为 y ^ x，因此 endofunctor (-)^S 是 [fun x => x ^ S]，也就是 [fun x => exponent_obj S x]，而 [eval] 在 x 处是箭头 x^S × S ~> x。

 Theory/Adjunction.v 的标题（在以“对于函数式程序员”开头的段落中）用散文形式说明“函数类型来源于 − × a ⊣ (−)^a，评估（eval）作为余单位”。[Curry_Adjunction] 和 [curry_adj_counit] 是将该句子作为定理的表达。Sets 模型——其余单位计算为 e(h, s) = h s——在 Instance/Sets/Cartesian/Closed/Adjunction.v 中。
*)

(*
 Currying, naturality, and representability

 nLab: https://ncatlab.org/nlab/show/exponential+object
 nLab: https://ncatlab.org/nlab/show/cartesian+closed+category
 Book: Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 Springer 1998
 Book: Riehl, “Category Theory in Context”, Dover 2016
 Paper: Lawvere, “Adjointness in Foundations”, Dialectica 23(3/4), 1969;
 reprinted as TAC Reprints 16, 2006

 Mac Lane's Chapter I fixes the vocabulary this file is written in: §I.4
 defines a natural transformation as a family of arrows whose square
 commutes for every morphism of the source category, and the entire content
 of [eval_natural] is that [eval] is such a family once the two sides are
 read as functors of the base object. His Chapter IV, “Adjoints”, is where
 the exponential becomes one: its §6 is titled “Cartesian Closed
 Categories”, and the adjunction − × S ⊣ (−)^S with evaluation as counit is
 the shape this file instantiates.

 The nLab's page on exponential objects states the same content in two
 registers and both are realized here. Universally: the exponential is “an
 object X^Y equipped with an evaluation map ev : X^Y × Y → X” through which
 every e : Z × Y → X factors uniquely — this is [ump_exponents] in
 Structure/Cartesian/Closed.v. Representably: X^Y is “a representing object
 for the functor hom(− × Y, X)”, the currying isomorphism
 hom(Z, X^Y) ≅ hom(Z × Y, X) being “a natural isomorphism of sets”. The
 second reading is the one [Curry_Representable] formalizes.

 Riehl's Example 2.1.6(iv) is that reading verbatim: “The functor
 Hom(− × A, B) : Set^op → Set that sends a set X to the set of functions
 X × A → B is represented by the set B^A of functions from A to B. That is,
 there is a natural bijection between functions X × A → B and functions
 X → B^A. This natural isomorphism is referred to as currying in computer
 science”. Two adjustments are made in passing to that example here. First,
 the ambient category is a general cartesian closed C rather than Set, so
 the presheaf is the hom-functor C(− × S, B) : C^op ⟶ Sets and the
 representing object is B^S; Riehl's own statement is recovered by taking C
 to be [Sets], which Instance/Sets/Cartesian/Closed/Adjunction.v does.
 Second, “natural bijection” is here a genuine isomorphism in the functor
 category [C^op, Sets] of setoid-valued functors, since hom-sets in this
 library are setoids and equality of their elements is ≈, never =.

 Lawvere's “Adjointness in Foundations” is the source of the slogan that
 cartesian closed structure IS an adjunction — currying is − × a ⊣ (−)^a —
 quoted already in the essay that heads Theory/Adjunction.v; the [Adjunction]
 packaging below is what lets the general theory of that file apply, so
 that the triangle identities ([curry_adj_triangle_left] and
 [curry_adj_triangle_right]) arrive as instances of [counit_fmap_unit] and
 [fmap_counit_unit] rather than being re-proved.

 In-tree, this file sits between three neighbours. Structure/Cartesian/
 Closed.v supplies every exponential equation used below, so no new lemma
 about exponentials is needed: the four naturality fields of [Adjunction] are
 exactly [curry_comp_l], [curry_comp], [uncurry_comp] and [uncurry_comp_r].
 Functor/Hom/Internal.v supplies the internal-hom bifunctor
 [-,-] : C^op ∏ C ⟶ C, of which [Exp_Functor] is the partial application at
 a fixed exponent; the two agree up to ≈ ([Exp_Functor_InternalHom]) but not
 definitionally, because the bifunctor inserts a [second id] that the
 endofunctor does not. Adjunction/Diagonal/Product.v is the companion
 result one level down: the same hom-set packaging applied to the product's
 universal property, Δ ⊣ ×.

 Theory/Naturality.v is deliberately NOT used. That file is naturality
 infrastructure — a [Naturality] class computing, from the type of a family
 of arrows, the naturality statement appropriate to it, plus the [Mapping]
 class recording a morphism action without the functor laws. Its commented-
 out [PartialApply_Product_Left] / [PartialApply_Curried_Right] block is the
 only part that would bear on the present file, and it partially applies a
 bifunctor already presented as C ∏ C ⟶ C or C ⟶ [C, C]. The exponential in
 [Closed] is neither: it is a bare object operation [exponent_obj] plus the
 iso [exp_iso], with functoriality nowhere assumed. (The tree does build a
 bifunctor of the right mathematical content — [InternalHomFunctor] of
 Functor/Hom/Internal.v, cited above — but at shape C^op ∏ C ⟶ C, which is
 not one of the two shapes those instances accept.) The [Mapping]-based
 [ArityOne] instances would in any case give a naturality *statement* but
 no functor, and [Adjunction] needs functors.

 WHAT DEFINING [Exp_Functor] DIRECTLY ACTUALLY BUYS, stated precisely
 because the first commit of this file overstated it and an audit
 disproved the overstatement by construction. It does NOT buy the
 definitional counit: the counit is ⌈id⌉, which depends only on [adj]'s
 [from] field being [uncurry] and on eval := uncurry id, so it comes out
 [eval] by conversion for ANY right adjoint with the same transposes —
 the audit assembled the adjunction through [InternalHomFunctor] instead
 and all four corollaries below still closed by [reflexivity]. What the
 direct definition buys is that the four naturality fields discharge from
 the [Closed] corollaries VERBATIM: routed through the bifunctor, two of
 them additionally need [second_id] and [id_right] rewritten away, since
 that route inserts a [second (op id)]. That is a real but modest
 convenience, and it is the whole of it. 

 --------
 函数柯里化、自然性与可表示性

 nLab： https://ncatlab.org/nlab/show/exponential+object 
 nLab： https://ncatlab.org/nlab/show/cartesian+closed+category 
 书籍：Mac Lane，《为在职数学家而写的范畴论》，第2版，Springer 1998 
 书籍：Riehl，《情境中的范畴论》，Dover 2016 
 论文：Lawvere，《基础中的伴随性》，Dialectica 23(3/4), 1969；
 转载自 TAC Reprints 16, 2006麦克莱恩的第一章确定了本文件使用的词汇：§I.4 将自然变换定义为一个箭头族，其方形图在源范畴的每个态射下交换，整个 [eval_natural] 的内容是 [eval] 一旦将两边读作基对象的函子就是这样的一个族。他的第四章“伴随函子”是指数函子成为一个函子的地方：其 §6 标题为“笛卡尔封闭范畴”，伴随关系 − × S ⊣ (−)^S 以评估作为伴随的余单位，是本文件实例化的形式。nLab关于指数对象的页面以两种方式说明了相同的内容，这里都得到了体现。普遍性地：指数是“一个对象 X^Y，配有一个评估映射 ev : X^Y × Y → X”，通过它每个 e : Z × Y → X 都能唯一地分解——这在 Structure/Cartesian/Closed.v 中是 [ump_exponents]。可表示地：X^Y 是“函子 hom(− × Y, X) 的表示对象”，其柯里化同构 hom(Z, X^Y) ≅ hom(Z × Y, X) 是“一种集合的自然同构”。第二种理解是 [Curry_Representable] 所形式化的。Riehl 的示例 2.1.6(iv) 原文如下：“函子
 Hom(− × A, B) : Set^op → Set 将集合 X 发送到函数集合
 X × A → B，被集合 B^A 从 A 到 B 的函数所表征。也就是说，
 存在函数 X × A → B 和函数 X → B^A 之间的自然双射。这个自然同构在计算机科学中被称为柯里化。”在此处引用该示例时进行了两个调整。首先，环境范畴是一般的笛卡尔闭范畴 C 而不是 Set，因此该预上层是余函子 C(− × S, B) : C^op ⟶ Sets，而表征对象是 B^S；通过将 C 取为 [Sets]（Instance/Sets/Cartesian/Closed/Adjunction.v 中所做），可以恢复 Riehl 本人的陈述。其次，这里的“自然双射”在函子范畴 [C^op, Sets] 中是真正的同构，因为该库中的同态集合是集合同构体，其元素的等价关系是 ≈，而绝不是 =。

 Lawvere 的《基础中的伴随性》是“笛卡尔闭结构就是伴随性——柯里化是 − × a ⊣ (−)^a”这一口号的来源，该口号已经在开头的 Theory/Adjunction.v 文章中引用；下面的 [Adjunction] 封装使得该文件的一般理论能够应用，从而三角恒等式（[curry_adj_triangle_left] 和 [curry_adj_triangle_right]）作为 [counit_fmap_unit] 和 [fmap_counit_unit] 的实例出现，而无需重新证明。在树状结构中，这个文件位于三个邻居之间。Structure/Cartesian/Closed.v 提供了下面使用的每一个指数方程，所以不需要关于指数的新引理：[Adjunction] 的四个自然性域正好是 [curry_comp_l]、[curry_comp]、[uncurry_comp] 和 [uncurry_comp_r]。Functor/Hom/Internal.v 提供了内Hom双函子 [-,-] : C^op ∏ C ⟶ C，其中 [Exp_Functor] 是在固定指数下的部分应用；这两个在 ≈ ([Exp_Functor_InternalHom]) 下是一致的，但并不在定义上完全相同，因为该双函子插入了一个 [second id]，而该端函子没有。Adjunction/Diagonal/Product.v 是下一层的相关结果：同样的 Hom-集合封装应用于积的泛性质，Δ ⊣ ×。Theory/Naturality.v 特意没有使用。该文件是自然性基础设施——一个  [Naturality] 类，从箭头族的类型计算出适用于它的自然性陈述，以及记录没有函子律的态射作用的  [Mapping] 类。它被注释掉的  [PartialApply_Product_Left] / [PartialApply_Curried_Right] 块是唯一与当前文件相关的部分，并且它部分应用了已呈现为 C ∏ C ⟶ C 或 C ⟶ [C, C] 的双函子。[Closed] 中的指数也不是：它只是一个裸对象操作 [exponent_obj] 加上同构 [exp_iso]，且没有假定函子性。（这个树确实构建了一个具有正确数学内容的二函子——上文引用的 Functor/Hom/Internal.v 中的 [InternalHomFunctor]——但是它的形状是 C^op ∏ C ⟶ C，而这并不是那些实例接受的两种形状之一。）基于 [Mapping] 的 [ArityOne] 实例无论如何都会给出一个自然性*陈述*，但不会产生函子，而 [Adjunction] 需要函子。定义 [Exp_Functor] 直接实际买到的东西，精确说明 因为这个文件的第一次提交夸大了它，而审计通过构造证明了这种夸大。它并不买到定义上的余单位：余单位是 ⌈id⌉，它仅依赖于 [adj] 的 [from] 字段为 [uncurry]，以及 eval := uncurry id，因此对任何具有相同转置的右伴随，它通过转换得出 [eval] — 审计是通过 [InternalHomFunctor] 组装伴随的，并且下面的所有四个推论仍然通过 [reflexivity] 得到闭合。直接定义买到的是四个自然性字段可以完全按照 [Closed] 推论解除：通过双函子路由，其中两个还需要将 [second_id] 和 [id_right] 改写掉，因为该路径插入了一个 [second (op id)]。那确实是一种真实但简朴的便利，这就是全部。
*)

Section CurryAdjunction.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Closed C _}.

Context (S : C).

(*
 The left adjoint (- × S) : C ⟶ C. On arrows it is [first f] = f × id[S],
 so the functor laws are [first_id] and [first_comp]. 

 --------
 左伴随 (- × S) : C ⟶ C。在箭头上，它是 [first f] = f × id [S]，因此函子定律是 [first_id] 和 [first_comp]。
*)
Program Definition Prod_Functor : C ⟶ C := {|
  fobj := fun x => x × S;
  fmap := fun _ _ f => first f
|}.
Next Obligation. apply first_id. Qed.
Next Obligation. apply first_comp. Qed.

(*
 The right adjoint (-)^S : C ⟶ C, the endofunctor the issue calls (−)^S.
 On arrows it is post-composition inside the exponential, f ↦ curry (f ∘
 eval); [fmap] is this term definitionally, not merely up to ≈. Preservation
 of identities is [curry_eval] and of composition is [curry_comp]. 

 --------
 右伴随 (-)^S : C ⟶ C，是该问题称为 (−)^S 的自函子。在箭头上，它是在指数内部进行后组合，f ↦ curry (f ∘ eval)；[fmap] 从定义上而言就是这个项，而不仅仅是近似相等。恒等映射的保持是 [curry_eval]，复合的保持是 [curry_comp]。
*)
Program Definition Exp_Functor : C ⟶ C := {|
  fobj := fun x => x ^ S;
  fmap := fun _ _ f => curry (f ∘ eval)
|}.
Next Obligation. proper; rewrites; reflexivity. Qed.
Next Obligation. rewrite <- comp_assoc; apply curry_comp. Qed.

(*
 Naturality of [eval] in its target (base) variable: transporting along
 f : x ~> y after evaluating agrees with evaluating after transporting the
 function part along f. Reading [fmap[Prod_Functor] (fmap[Exp_Functor] f)]
 as curry (f ∘ eval) × id[S], the square is

 f ∘ eval ≈ eval ∘ (curry (f ∘ eval) × id[S]) : x^S × S ~> y,

 which is [ump_exponents] applied to f ∘ eval. Both sides are arrows of C
 compared with ≈; nothing here is an equality of morphisms. On vacuity:
 neither [Category] nor [Closed] forces hom-setoids to be trivial, so this
 is a genuine constraint — Instance/Sets/Cartesian/Closed/Adjunction.v
 exhibits a model in which the two sides are visibly non-trivial maps and
 the ambient hom-setoid separates arrows — and the proof consumes the
 exponential's universal property rather than a general categorical law. 

 --------
 [eval] 在其目标（基础）变量中的自然性：在评估之后沿 f : x ~> y 进行传输，与沿 f 传输函数部分之后再进行评估是一致的。将 [fmap[Prod_Functor] (fmap [Exp_Functor] f)] 读作 curry (f ∘ eval) × id [S]，方形是

 f ∘ eval ≈ eval ∘ (curry (f ∘ eval) × id [S]) : x^S × S ~> y,这是 [ump_exponents] 应用于 f ∘ eval。两边都是 C 的箭头，比对 ≈；这里没有任何形态是态射的等式。关于空性：[Category] 和 [Closed] 都不会强制同态集同构为平凡，因此这是一个真实的约束——Instance/Sets/Cartesian/Closed/Adjunction.v 展示了一个模型，其中两边显然是非平凡的映射，并且外部的同态集同构可以区分箭头——而证明使用了指数的普遍性属性，而不是一般的范畴定律。
*)
Lemma eval_natural {x y : C} (f : x ~> y) :
  f ∘ eval ≈ eval ∘ fmap[Prod_Functor] (fmap[Exp_Functor] f).
Proof. simpl; now rewrite ump_exponents. Qed.

(*
 The same square bundled: evaluation is a natural transformation from
 (-)^S × S to the identity functor. This is the counit of the adjunction
 below, exhibited before the adjunction so that the naturality content is
 visible on its own. 

 --------
 相同的平方束：评估是一个从 (-)^S × S 到恒等函子 的自然变换。这是下面伴随的一部分余单位，在伴随之前展示，以便自然性内容可以单独可见。
*)
Program Definition eval_Transform : Prod_Functor ◯ Exp_Functor ⟹ Id[C] := {|
  transform := fun _ => eval
|}.

(*
 The currying adjunction, in the hom-set form of Theory/Adjunction.v: the
 family of setoid isomorphisms (x × S ~> y) ≊ (x ~> y^S) is [exp_iso], with
 [curry] forward and [uncurry] back, and the four naturality fields are the
 substitution laws already proved in Structure/Cartesian/Closed.v. 

 --------
 在 Theory/Adjunction.v 的同态集形式中，柯里化伴随：集合族同构 (x × S ~> y) ≊ (x ~> y^S) 是 [exp_iso]，其中 [curry] 为正向，[uncurry] 为反向，四个自然性域是已经在 Structure/Cartesian/Closed.v 中证明的替换律。
*)
#[export] Program Instance Curry_Adjunction : Prod_Functor ⊣ Exp_Functor := {|
  adj := fun _ _ =>
    {| to   := {| morphism := curry |}
     ; from := {| morphism := uncurry |} |}
|}.
(*
 to_adj_nat_l: curry (f ∘ first g) ≈ curry f ∘ g 

 --------
 to_adj_nat_l：curry (f ∘ first g) ≈ curry f ∘ g
*)
Next Obligation. symmetry; apply curry_comp_l. Qed.
(*
 to_adj_nat_r: curry (f ∘ g) ≈ curry (f ∘ eval) ∘ curry g 

 --------
 to_adj_nat_r: curry (f ∘ g) ≈ curry (f ∘ eval) ∘ curry g
*)
Next Obligation. apply curry_comp. Qed.
(*
 from_adj_nat_l: uncurry (f ∘ g) ≈ uncurry f ∘ first g 

 --------
 from_adj_nat_l: uncurry (f ∘ g) ≈ uncurry f ∘ first g
*)
Next Obligation. apply uncurry_comp. Qed.
(*
 from_adj_nat_r: uncurry (curry (f ∘ eval) ∘ g) ≈ f ∘ uncurry g 

 --------
 from_adj_nat_r: 解开柯里化 (柯里化 (f ∘ eval) ∘ g) ≈ f ∘ 解开柯里化 g
*)
Next Obligation. symmetry; apply uncurry_comp_r. Qed.

(*
 The counit of the adjunction is evaluation. Both sides are arrows
 x^S × S ~> x and the comparison is ≈, as everywhere in this library; the
 [reflexivity] proof records the stronger fact that the two are convertible
 (the counit ⌈id⌉ unfolds to [uncurry id], which is the definition of
 [eval] in Structure/Cartesian/Closed.v). 

 --------
 伴随的余单位是求值。两边都是箭头
 x^S × S ~> x，比较是≈，就像在这个库中到处一样；
 [reflexivity]  证明记录了一个更强的事实，即两者是可转换的
 （余单位 ⌈id⌉ 展开为  [uncurry id] ，这就是 Structure/Cartesian/Closed.v 中
 [eval] 的定义）。
*)
Corollary curry_adj_counit {x : C} :
  @counit _ _ _ _ Curry_Adjunction x ≈ eval.
Proof. reflexivity. Qed.

(*
 Dually the unit is [curry id] : x ~> (x × S)^S, again convertible, not
 merely ≈-equal. 

 --------
 该单元的对偶是 [curry id]：x ~> (x × S)^S，同样是可转换的，而不仅仅是 ≈-相等。
*)
Corollary curry_adj_unit {x : C} :
  @unit _ _ _ _ Curry_Adjunction x ≈ curry id.
Proof. reflexivity. Qed.

(*
 The transposes of the adjunction are [curry] and [uncurry] on the nose:
 ⌊-⌋ = to adj is currying and ⌈-⌉ = from adj is uncurrying. Stated with ≈
 between arrows of C, as required; both hold by [reflexivity] because
 [Curry_Adjunction]'s [adj] field has [curry] and [uncurry] as its two
 directions. (Not because that field IS [exp_iso], as the first commit
 said: it is a freshly built [Isomorphism] wrapping the same two maps,
 and [reflexivity] does not identify the two records.) 

 --------
 伴随的转置是  [curry] 和 [uncurry] ，完全正确：
 ⌊-⌋ = 到伴随是柯里化，⌈-⌉ = 从伴随是反柯里化。在 C 的箭头之间用 ≈ 表示，如要求那样；两者都由 [reflexivity] 保证，因为 [Curry_Adjunction] 的 [adj] 字段有 [curry] 和 [uncurry] 作为它的两个方向。（不是因为该字段就是 [exp_iso] ，正如第一次提交所说：它是新建的 [Isomorphism] ，封装了相同的两个映射，而 [reflexivity] 不会识别这两个记录。）
*)
Corollary curry_adj_to {x y : C} (f : x × S ~> y) :
  to (@adj _ _ _ _ Curry_Adjunction x y) f ≈ curry f.
Proof. reflexivity. Qed.

Corollary curry_adj_from {x y : C} (g : x ~> y ^ S) :
  from (@adj _ _ _ _ Curry_Adjunction x y) g ≈ uncurry g.
Proof. reflexivity. Qed.

(*
 The two triangle identities, obtained from the general theory of
 Theory/Adjunction.v rather than re-proved. The first, ε ∘ F η ≈ id, reads
 eval ∘ (curry id × id[S]) ≈ id on x × S. 

 --------
 这两个三角恒等式，是从 Theory/Adjunction.v 的一般理论中获得的，而不是重新证明的。第一个，ε ∘ F η ≈ id，表示在 x × S 上 eval ∘ (curry id × id [S]) ≈ id。
*)
Corollary curry_adj_triangle_left {x : C} :
  eval ∘ first (curry (id[x × S])) ≈ id.
Proof. exact (@counit_fmap_unit _ _ _ _ Curry_Adjunction x). Qed.

(*
 The second, U ε ∘ η ≈ id, on x^S; here [curry (eval ∘ eval)] is
 [fmap[Exp_Functor]] applied to the counit [eval]. 

 --------
 第二个，U ε ∘ η ≈ id，作用在 x^S 上；这里 [curry (eval ∘ eval)] 是 [fmap[Exp_Functor] ] 作用于余单位 [eval] 上。
*)
Corollary curry_adj_triangle_right {x : C} :
  curry (eval ∘ eval) ∘ curry (id[x^S × S]) ≈ id.
Proof. exact (@fmap_counit_unit _ _ _ _ Curry_Adjunction x). Qed.

(*
 [Exp_Functor] is the internal-hom bifunctor of Functor/Hom/Internal.v held
 fixed in its contravariant argument. The agreement is up to ≈ and not
 definitional: the bifunctor's action inserts [second (op id)], which is
 [second id] and only ≈-equal to [id]. 

 --------
 [Exp_Functor] 是 Functor/Hom/Internal.v 的内部 Hom 双函子，在其逆变参数上保持固定。这个一致性是到 ≈ 的，而不是定义性的：双函子的作用插入了 [second (op id)]，而 [second (op id)] 是 [second id] 的，并且只与 [id] ≈ 相等。
*)
Lemma Exp_Functor_InternalHom {x y : C} (f : x ~> y) :
  fmap[Exp_Functor] f
    ≈ @fmap _ _ (InternalHomFunctor C) (S, x) (S, y) (id[S], f).
Proof. simpl; rewrite second_id, id_right; reflexivity. Qed.

End CurryAdjunction.

Arguments Prod_Functor {C _} S.
Arguments Exp_Functor {C _ _} S.

Section CurryRepresentable.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Closed C _}.

Context (S B : C).

(*
 The presheaf of Riehl's Example 2.1.6(iv), for a general cartesian closed
 C: X ↦ C(X × S, B), contravariant in X. It is assembled from pieces
 already in the tree — the contravariant hom [Hom ─, B] of Functor/Hom.v
 composed with the opposite of the left adjoint — so its functor laws are
 inherited and no new obligation arises. Unfolded, [Curry_Presheaf x] is the
 hom-setoid (x × S ~> B) and [fmap] sends g to g ∘ first f. 

 --------
 Riehl的例子2.1.6(iv)的前层，对于一般的笛卡尔闭范畴C：X ↦ C(X × S, B)，在X上是反变的。它由树中已有的部分拼装而成——Functor/Hom.v的反变Hom [Hom ─, B] 与左伴随的对偶组合——因此它的函子律是继承的，不产生新的义务。展开来看，[Curry_Presheaf x]是hom-集合Z（x × S ~> B），而[fmap]将g映射为g ∘ first f。
*)
Definition Curry_Presheaf : C^op ⟶ Sets := [Hom ─, B] ◯ (Prod_Functor S)^op.

(*
 The representation itself: the currying bijection, natural in X. The
 forward direction of a [Representable] is a transformation OUT of the
 represented functor, so [to] is [uncurry] : (x ~> B^S) → (x × S ~> B) and
 [from] is [curry]; naturality in x is [uncurry_comp] and [curry_comp_l],
 and the two round trips are [uncurry_curry] and [curry_uncurry]. Note that
 [Hom ─, B^S] is the covariant hom-functor of C^op at B^S, which is what
 the [Representable] class asks for when the base category is C^op. 

 --------
 表示本身：在 X 中自然的柯里化双射。[Representable] 的正向方向是表示函子的一种变换 OUT，因此 [to] 是 [uncurry] : (x ~> B^S) → (x × S ~> B)，而 [from] 是 [curry]；在 x 中的自然性是 [uncurry_comp] 和 [curry_comp_l]，两次往返是 [uncurry_curry] 和 [curry_uncurry]。请注意，[Hom ─, B^S] 是 C^op 在 B^S 处的协变同态函子，这正是 [Representable] 类在基类别为 C^op 时所要求的。
*)
Program Definition Curry_Representation : [Hom ─, B^S] ≅ Curry_Presheaf := {|
  to   := {| transform := fun _ => {| morphism := uncurry |} |};
  from := {| transform := fun _ => {| morphism := curry |} |}
|}.
Next Obligation. symmetry; apply uncurry_comp. Qed.
Next Obligation. apply uncurry_comp. Qed.
Next Obligation. apply curry_comp_l. Qed.
Next Obligation. symmetry; apply curry_comp_l. Qed.
Next Obligation. rewrite first_id, id_right; apply uncurry_curry. Qed.

(*
 The [Representable] witness. Before this instance the class of
 Functor/Representable.v had no inhabitants anywhere in the tree; this is
 the first, and it says exactly what Riehl's Example 2.1.6(iv) says: the
 functor C(− × S, B) is represented by B^S. The base category of the
 instance is C^op, since the functor is contravariant in C.

 Scope the claim correctly: it is THIS class that was uninhabited, and the
 claim is about the state of the tree when this instance was written — the
 tautological [Hom_Representable] has since been added beside the class
 itself, deliberately as a plain [Definition] rather than an [Instance] so
 that resolution below is unaffected. The tree does carry representability
 content elsewhere, under a different class — Structure/UniversalProperty.v's
 [IsUniversalProperty] also requires a natural iso out of a hom-functor, and
 it has three instances (cartesian products, limits, universal arrows); the
 passage between that class and this one is
 Functor/Representable/Functorial.v's [Representable_of_UnivProperty] and
 [UnivProperty_of_Representable]. 

 --------
 [Representable] 证据。在此实例之前，Functor/Representable.v 类在树中的任何地方都没有实例；这是第一个实例，它完全说明了 Riehl 的示例 2.1.6(iv) 所说的内容：函子 C(− × S, B) 由 B^S 表示。此实例的基类是 C^op，因为该函子在 C 中是逆变的。正确界定声明的范围：正是这个类没有实例，且声明是关于在编写此实例时树的状态——自那时起，重言式 [Hom_Representable] 已被添加到类本身旁边，有意作为一个普通的 [Definition] 而不是 [Instance]，这样下面的解析不会受到影响。该树在其他地方确实承载可表示性内容，在不同的类下——Structure/UniversalProperty.v 的 [IsUniversalProperty] 也要求从 Hom 函子出发的自然同构，并且它有三个实例（笛卡尔积、极限、通用箭头）；该类与这个类之间的过渡是 Functor/Representable/Functorial.v 的 [Representable_of_UnivProperty] 和 [UnivProperty_of_Representable]。
*)
#[export] Program Instance Curry_Representable : Representable Curry_Presheaf := {|
  repr_obj := B ^ S;
  represented := Curry_Representation
|}.

(*
 Identification of the universal element. The Yoneda lemma — in-tree as
 [Yoneda_Lemma] in Functor/Hom/Yoneda.v, not re-proved here — says a
 representation Φ : C(A, −) ≅ F is determined by the single element
 Φ_A(id[A]) of F A. For this representation A is B^S and that element is
 [eval] : B^S × S ~> B, so what is being represented is the exponential's
 own evaluation and not some unrelated family. The comparison is ≈ between
 arrows of C; the [reflexivity] proof shows the two sides convertible. 

 --------
 识别通用元件。Yoneda 引理——在树内作为 Functor/Hom/Yoneda.v 中的 [Yoneda_Lemma]，这里不再重新证明——指出，一个表示 Φ : C(A, −) ≅ F 由 F A 中的单一元素 Φ_A(id [A]) 决定。对于这个表示，A 是 B^S，而该元素是 [eval] : B^S × S ~> B，因此被表示的内容是指数本身的求值，而不是一些无关的族。比较是 C 的箭头之间的 ≈；[reflexivity] 证明表明两边是可转换的。
*)
Lemma Curry_repr_universal :
  to Curry_Representation (B ^ S) id ≈ eval.
Proof. reflexivity. Qed.

(*
 What the presheaf's action is, spelled out: restricting a map along
 f : y ~> x re-indexes by f in the first factor. This is a definitional
 unfolding — [reflexivity] closes it, and it carries no content beyond
 naming what [Curry_Presheaf]'s [fmap] computes to — but it is what makes
 the naturality obligations of [Curry_Representation] above legible. Stated
 as ≈ of arrows of C, as everywhere. 

 --------
 预层的作用是什么，详细说明：沿着 f : y ~> x 限制一个映射，在第一个因子上通过 f 重新索引。这是一个定义性的展开——[reflexivity] 封闭了它，而且它没有超出命名 [Curry_Presheaf] 的 [fmap] 计算结果的内容——但它使得上面 [Curry_Representation] 的自然性义务可读。用 C 的箭头的 ≈ 表示，就像到处一样。
*)
Lemma Curry_Presheaf_fmap {x y : C} (f : y ~> x) (g : x × S ~> B) :
  fmap[Curry_Presheaf] f g ≈ g ∘ first f.
Proof. reflexivity. Qed.

End CurryRepresentable.

Arguments Curry_Presheaf {C _} S B.
Arguments Curry_Representation {C _ _} S B.

(*
 The instance is usable, not merely declared: typeclass resolution finds it
 for the goal [Representable (Curry_Presheaf S B)] (the [_] below is solved
 by resolution alone), and the class's [Representable_to_obj] coercion —
 which had no callers in the tree either — reads the representing object
 back off it as B^S. The second statement is a Leibniz equality between two
 OBJECTS of C, which is the only sense available: this library has no ≈ on
 objects, only isomorphism, and objects are not morphisms. 

 --------
 该实例是可用的，而不仅仅是声明的：类型类解析为目标 [Representable (Curry_Presheaf S B)] 找到了它（下面的 [_] 仅通过解析就解决了），并且类的 [Representable_to_obj] 强制转换——在树中也没有调用者——将表示对象读回为 B^S。第二个陈述是在两个 C 的对象之间的莱布尼茨等式，这是唯一可用的意义：该库在对象上没有 ≈，只有同构，并且对象不是态射。
*)
Definition Curry_Representable_resolves
  {C : Category} `{@Cartesian C} `{@Closed C _} (S B : C) :
  Representable (Curry_Presheaf S B) := _.

Example Curry_repr_obj
  {C : Category} `{@Cartesian C} `{@Closed C _} (S B : C) :
  Representable_to_obj _ (Curry_Representable S B) = (B ^ S)%object.
Proof. reflexivity. Qed.
