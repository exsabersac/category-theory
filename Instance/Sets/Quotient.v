Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Universal.Element.

Generalizable All Variables.

(*
 The global obligation tactic ([cat_simpl], Lib/Tactics.v) introduces
 the obligations' binders under names of its own choosing, which makes the
 proof scripts below brittle; [idtac] hands each obligation over
 untouched, as Instance/Sets/Complete.v does. 

 --------
 全局义务策略（[cat_simpl]，Lib/Tactics.v）在自己选择的名称下引入义务的绑定器，这使得下面的证明脚本变得脆弱；[idtac] 则像 Instance/Sets/Complete.v 那样，保持每个义务原样传递。
*)
#[local] Obligation Tactic := idtac.

(* * * The quotient of a setoid by an equivalence relation / * * 通过等价关系的集合商 *)

(*
 nLab:      https://ncatlab.org/nlab/show/quotient+set
 nLab:      https://ncatlab.org/nlab/show/setoid
 Wikipedia: https://en.wikipedia.org/wiki/Equivalence_class
 Wikipedia: https://en.wikipedia.org/wiki/Quotient_set

 Mac Lane, "Categories for the Working Mathematician" 2nd ed., §III.1
 construction 4 (p. 57): for an equivalence relation E on a set S, the
 projection p : S -> S/E is universal among functions out of S that
 respect E.  Every h : S -> X with h x = h y whenever x E y factors
 through p by a unique u : S/E -> X.

 In a setoid library that construction is not a construction at all: a
 quotient IS another choice of `≈` on the same carrier.  The design is
 stated as such at Instance/Sets.v ("a quotient is just another
 choice of `≈` on the same carrier") and at Theory/Category.v, and
 it is what Construction/Quotient.v does one dimension up (a quotient
 of a CATEGORY by a hom-congruence, identity on objects).  This file
 supplies the missing element-level operator: given a [SetoidObject] A
 and an equivalence relation R on its carrier, [SetsQuotient A R] is A
 with `≈` replaced by R, and [sets_quot_proj] is the identity function
 read as a setoid map.

 Because carrier and function are untouched, Mac Lane's universal
 property becomes almost tautologous -- and that is the content, not a
 defect.  The mediator IS the given function; its respectfulness for
 the coarser relation IS the hypothesis that it respects E; and the
 defining triangle holds pointwise by [reflexivity].  What has to be
 built is only the ENVIRONMENT in which "universal" can be stated: the
 functor X |-> {E-respecting maps A -> X}, which is covariant by
 postcomposition, and against which ⟨A/R, p⟩ is a universal element in
 the sense of Theory/Universal/Element.v (Mac Lane's §III.1
 definition 2). 

 --------
 nLab:       https://ncatlab.org/nlab/show/quotient+set 
 nLab:       https://ncatlab.org/nlab/show/setoid 
 Wikipedia:  https://en.wikipedia.org/wiki/Equivalence_class 
 Wikipedia:  https://en.wikipedia.org/wiki/Quotient_set 

 Mac Lane，《泛函数学家的范畴论》第二版，第III.1节
 构造 4（第57页）：对于集合 S 上的等价关系 E，投射 p : S -> S/E 在尊重 E 的从 S 出发的函数中是通用的。每个 h : S -> X，若 x E y 时 h x = h y，则唯一地通过 u : S/E -> X 因子分解 p。在一个集合等价体（setoid）库中，这种构造根本不是一种构造：商集（quotient）只是对同一载体上的 `≈` 的另一种选择。该设计在 Instance/Sets.v 中已说明（“商集只是对同一载体上的 `≈` 的另一种选择”）以及在 Theory/Category.v 中说明，并且这也是 Construction/Quotient.v 在一个维度上所做的（通过同态同余关系对一个范畴 CATEGORY 取商集，保持对象身份）。此文件提供了缺失的元素级运算符：给定一个 [SetoidObject] A 及其载体上的等价关系 R，[SetsQuotient A R] 是用 R 替换 `≈` 的 A，而 [sets_quot_proj] 是被视为集合等价体映射的恒等函数。因为载体和函数保持不变，麦克莱恩的普遍性质几乎变成了同义反复——这就是内容，而不是缺陷。中介者就是给定的函数；它对较粗关系的尊重性就是它尊重 E 的假设；定义三角形按点成立，由 [reflexivity]。需要构建的只是一个可以陈述“普遍”的环境：函子 X |-> {尊重 E 的映射 A -> X}，通过后合成是协变的，而 ⟨A/R, p⟩ 是理论/普遍/元素.v 意义上的普遍元素（麦克莱恩 §III.1 定义 2）。
*)

(*
 Where this sits, and why the carrier does not move

 Text:  Bishop, "Foundations of Constructive Analysis", McGraw-Hill 1967
 Text:  Mac Lane, "Categories for the Working Mathematician", Springer
 1998, §III.1 (pp. 55-59) and §III.3 (pp. 64-68)
 Text:  Fong and Spivak, "Seven Sketches in Compositionality", CUP 2019,
 §1.2.1 (printed p. 10)
 Paper: Barthe, Capretta, Pons, "Setoids in type theory", JFP 13(2) 2003
 Thesis: Hofmann, "Extensional Concepts in Intensional Type Theory",
 LFCS report ECS-LFCS-95-327, University of Edinburgh, 1995

 Two presentations of a quotient have been current since Bishop.  The
 first, which the Seven Sketches definition (§1.2.1) gives, takes the
 quotient to BE the set of parts of the induced partition: an element
 of A/R is a subset of A.  The second, which Bishop's own development
 uses and which Hofmann's models of intensional type theory formalise,
 never separates a carrier from its equality: A/R is A again, under a
 coarser equality.  The two agree classically.  They do not agree
 constructively without care, and Instance/Sets/Quotient/Partition.v is
 where that care is spent -- it builds the class presentation, proves
 the comparison with this file's, and measures exactly what the
 comparison costs.

 This file takes the second presentation because the library does.  The
 choice buys three things.  Function extensionality is not needed, since
 no new function space is introduced.  No choice principle is needed,
 since no representative is ever selected -- Mac Lane's classical proof
 picks a representative of each class and checks independence, and here
 there is nothing to pick.  And the whole construction stays at the
 universe of the carrier, whereas a set of subsets does not
 (Instance/Sets/Powerset.v establishes exactly that, and the sequel file
 pins the consequence).

 The one thing the choice costs is that "quotient" no longer has a
 canonical meaning independent of the relation's proof content.  R is
 [crelation]-valued, so R x y is a TYPE, and two different derivations
 of R x y are two different elements.  That does not affect anything in
 this file -- `≈` in a [SetoidObject] is Type-valued for the same reason
 and the hom-setoid of [Sets] compares maps, not proofs -- but it does
 affect the class presentation, and again the sequel file is where it
 is measured. 

 --------
 这里所处的位置，以及载体为何不移动

 书籍: Bishop，《构造分析基础》，麦格劳-希尔，1967年
 书籍: Mac Lane，《为工作数学家准备的范畴论》，施普林格，1998年，§III.1（第55-59页）和§III.3（第64-68页）
 书籍: Fong 和 Spivak，《组合性中的七个草图》，剑桥大学出版社，2019年，§1.2.1（印刷第10页）
 论文: Barthe, Capretta, Pons，《类型理论中的集合同构》，《JFP》13(2)，2003年
 论文: Hofmann，《内涵类型理论中的外延概念》，LFCS报告 ECS-LFCS-95-327，爱丁堡大学，1995年自毕绍普以来，商的两种表示方法一直存在。第一种是《七个素描》的定义（§1.2.1）所给出的，它将商视为所诱导的划分的各部分的集合：A/R 的元素是 A 的子集。第二种是毕绍普自身的发展中使用的方法，也是霍夫曼的强类型理论模型所形式化的方法，它从不将载体与其相等性分开：A/R 仍然是 A，只是在较粗糙的相等性下。两者在经典逻辑下是一致的。在构造性逻辑中，如果不加注意，它们则不一致，而 Instance/Sets/Quotient/Partition.v 正是处理这一细节的文件——它构建类的表示，证明与本文件表示的比较，并精确衡量比较的代价。这个文件采用了库所使用的第二种表述。这个选择带来了三方面的好处。函数外延性不是必须的，因为没有引入新的函数空间。也不需要选择公理，因为从未选择过任何代表——Mac Lane 的经典证明会选择每个类的一个代表并检查独立性，而在这里根本没有什么可选的。而且整个构造保持在载体的宇宙中，而子集的集合则不保持（Instance/Sets/Powerset.v 正好阐明了这一点，后续文件则确定了其结果）。唯一的代价是，“商”不再具有独立于关系证明内容的规范含义。R 是 [crelation] 值的，因此 R x y 是一个 TYPE，而 R x y 的两个不同推导是两个不同的元素。这不会影响本文件中的任何内容——`≈` 中的 [SetoidObject] 由于同样的原因是 Type 值的，并且 [Sets] 的同态集准则比较的是映射而不是证明——但它确实会影响类的表示，并且同样，后续文件才是衡量这一点的地方。
*)

(*
 WHAT IS DELIVERED

 * [SetoidCoarser] and [SetoidRespectsRel], the two hypotheses the
 literature states, and [coarser_iff_respects] proving them EQUIVALENT
 for an equivalence relation.  This settles a question the source
 issue raises twice in different words: Mac Lane's §III.1 asks for a
 "setoid-respecting" E and Seven Sketches §1.2.1 for an R "coarser
 than `≈`", and these are the same hypothesis, not two.  Each
 direction consumes exactly one law of R -- transitivity forward,
 reflexivity back -- and both are recorded.

 * [SetsQuotient A R HR], the quotient setoid, and [sets_quot_proj], the
 projection.  Note WHICH hypothesis each needs: the OBJECT needs only
 that R is an equivalence, and [SetoidCoarser] enters exactly at the
 PROJECTION, where it is what makes the identity function respectful.

 * The functor [RespFunctor A R : Sets ⟶ Sets] sending X to the setoid
 of R-respecting maps A -> X, covariant by postcomposition.  It needs
 NOTHING of R -- neither that R is an equivalence nor that it is
 coarser than `≈` -- which is why it is defined before either.

 * [sets_quot_universal_element], Mac Lane §III.1 construction 4 as an
 [AUniversalElement] over #303's class, used DIRECTLY.  With the
 mediator calculus [sets_quot_med] / [_commutes] / [_unique], and
 [eq_refl] checks that the class's element IS the projection and the
 class's mediator IS [sets_quot_med].

 * A representation, by the YONEDA-FREE route.  [ue_representation] and
 [AUniversalElement_of_repr] (Theory/Universal/Element.v) build the
 natural isomorphism [Hom (A/R),─] ≅ RespFunctor without mentioning
 [Yoneda_Lemma]; [sets_quot_representation] and
 [sets_quot_Representable] are the results.  The Yoneda route is NOT
 available here and that is not a matter of taste: [Yoneda_Lemma] is
 stated over [C : Category@{u0 u0 u0}] -- object, hom and proof
 universes identified -- while [Sets@{o so} : Category@{so o o}] has
 its objects strictly above its homs.  Test/ProbeSetsQuotient.v pins
 the refusal against a positive control.

 * Non-vacuity, by proof rather than by assertion.  [nat_parity] is a
 concrete coarsening of the naturals under `=` in which the quotient
 identifies 0 with 2 and provably does not identify 0 with 1.  The two
 degenerate coarsenings are named and separated from it: the FINEST,
 R := `≈`, returns the object it started from ([sets_quot_finest_eq],
 by [eq_refl] on the whole record), and the COARSEST, R := the total
 relation, collapses everything ([sets_quot_total_collapses]) -- and
 [nat_parity] is proved to be neither ([nat_parity_not_finest],
 [nat_parity_not_coarsest]).

 WHAT IS NOT DELIVERED

 * NO CLASS PRESENTATION.  The quotient as the set of parts of the
 induced partition is Instance/Sets/Quotient/Partition.v, together
 with the comparison and the universe measurement.  Nothing here
 mentions a subset.

 * NO COEQUALIZERS.  [Sets_HasCoequalizers] and the identification of
 A/R with the coequalizer of the two projections of R are
 Instance/Sets/Coequalizer.v, which is this file's only in-tree
 consumer.

 * NO [Cocomplete Sets] IN THIS FILE.  It supplies one colimit shape's
 object, not the general construction; that is at
 Instance/Sets/Cocomplete.v, as Instance/Sets/Complete.v says.

 * NO FUNCTORIALITY IN THE RELATION.  A refinement R ⊆ R' induces a map
 A/R -> A/R', and that map is not built; nor is any comparison with
 Construction/Quotient.v's category-level quotient, which is a
 different construction on a different kind of object.

 STATUS: axiom-free.  45 named constants plus 6 [Program] obligations
 ([RespMap_Setoid_obligation_1], [RespFunctor_obligation_1] through
 [_4], [sets_quot_universal_element_obligation_1]), each measured
 separately, all reporting "Closed under the global context"; the
 Makefile's [print-assumptions] target audits thirteen of them. 

 --------
 交付的内容

 * [SetoidCoarser] 和 [SetoidRespectsRel]，文献中提出的两种假设，以及 [coarser_iff_respects]，证明它们在等价关系下是等价的。这解决了源问题两次以不同措辞提出的问题：Mac Lane 的 §III.1 要求一个“集合尊重”的 E，而 Seven Sketches §1.2.1 要求一个比 `≈` 更粗的 R，这实际上是相同的假设，而不是两个。每个方向恰好使用 R 的一条规律——正向使用传递性，反向使用自反性——并且两者都被记录。

 * [SetsQuotient A R HR]，商集合，以及 [sets_quot_proj]，投影。注意每个假设所需的内容：对象只需要 R 是等价关系，而 [SetoidCoarser] 恰好用于投影，这使得恒等函数符合要求。* 函子  [RespFunctor A R : Sets ⟶ Sets] 将 X 映射到 R-保持映射 A -> X 的等价类集合，通过后置组合协变。它不需要 R 的任何条件——既不要求 R 是等价关系，也不要求它比 `≈` 更粗——这也是它定义在任何一个之前的原因。

 *  [sets_quot_universal_element] ，Mac Lane §III.1 构造 4，作为 #303 类上的 [AUniversalElement] ，直接使用。借助中介者演算  [sets_quot_med] / [_commutes] / [_unique] ，并且 [eq_refl] 检查该类的元素确实是投影，该类的中介者确实是 [sets_quot_med] 。* 通过YONEDA-FREE路径表示。[ue_representation] 和 [AUniversalElement_of_repr]（Theory/Universal/Element.v）构建了自然同构 [Hom (A/R),─] ≅ RespFunctor，而没有提到 [Yoneda_Lemma]；[sets_quot_representation] 和 [sets_quot_Representable] 是结果。这里无法使用Yoneda路径，这不是个人喜好的问题：[Yoneda_Lemma] 是在 [C : Category@{u0 u0 u0}] 上陈述的——对象、同态和证明宇宙已被识别——而 [Sets@{o so} : Category@{so o o}] 的对象严格高于其同态。Test/ProbeSetsQuotient.v 将拒绝情况与阳性对照进行对比。* 非空性，通过证明而不是断言。[nat_parity] 是自然数在 `=` 下的一个具体粗化，其中商将 0 与 2 识别，并且可证明不将 0 与 1 识别。两个退化的粗化被命名并与之区分：最细的，R := `≈`，将对象返回到它开始的形式（[sets_quot_finest_eq]，通过 [eq_refl] 在整个记录上），最粗的，R := 总关系，将一切合并（[sets_quot_total_collapses]）——并且 [nat_parity] 被证明既不是（[nat_parity_not_finest]，[nat_parity_not_coarsest]）。

 未提供的内容

 * 无类呈现。作为诱导分区的各部分集合的商是 Instance/Sets/Quotient/Partition.v，同时包括比较和宇宙测量。这里没有提到任何子集。* 没有余等化器。[Sets_HasCoequalizers] 以及通过余等化器辨识 R 的两个投影的 A/R 在 Instance/Sets/Coequalizer.v 中，这是本文件中唯一的树内使用者。

 * 本文件中没有 [Cocomplete Sets]。它提供了一个余极限图形的对象，而不是一般的构造；那部分内容在 Instance/Sets/Cocomplete.v，如 Instance/Sets/Complete.v 所述。

 * 关系中没有函子性。一个细化 R ⊆ R' 会诱导一个映射 A/R -> A/R'，而该映射没有被构建；对 Construction/Quotient.v 的范畴级商的任何比较也没有构建，后者是在不同类型对象上的不同构造。状态：无公理。45 个已命名常量加上 6 个 [Program] 义务（[RespMap_Setoid_obligation_1]、[RespFunctor_obligation_1] 到 [_4]、[sets_quot_universal_element_obligation_1]），每个单独测量，全部报告“在全局上下文下关闭”；Makefile 的 [print-assumptions] 目标审核其中十三个。
*)

(* * ** The two forms of the hypothesis / * ** 假设的两种形式 *)

Section Hypotheses.

Context {A : SetoidObject}.
Context (R : crelation (carrier A)).

(*
 Seven Sketches' form: R is COARSER than the carrier's own equality,
 i.e. `≈` is contained in R. 

 --------
 七个素描的形式：R 比载体自身的等式更粗糙，即 `≈` 包含在 R 中。
*)
Definition SetoidCoarser : Type := ∀ x y : carrier A, x ≈ y → R x y.

(*
 Mac Lane's form: R RESPECTS the carrier's equality, i.e. R may be
 transported along `≈` in either argument.  Stated one-directionally;
 symmetry of `≈` gives the other direction. 

 --------
 Mac Lane 的形式：R 尊重载体的等同性，即 R 可以沿着 `≈` 在任一参数中传输。单向表述；`≈` 的对称性给出了另一方向。
*)
Definition SetoidRespectsRel : Type :=
  ∀ x x' y y' : carrier A, x ≈ x' → y ≈ y' → R x y → R x' y'.

(*
 Forward: coarseness gives respect, and the law of R it consumes is
 TRANSITIVITY. 

 --------
 前言：粗鲁带来尊重，而它所遵循的规律是传递性。
*)
Lemma coarser_respects (HR : Transitive R) : SetoidCoarser → SetoidRespectsRel.
Proof.
  intros Hc x x' y y' Hx Hy Hxy.
  transitivity y.
  - transitivity x; [ apply Hc; now symmetry | exact Hxy ].
  - now apply Hc.
Qed.

(*
 Back: respect gives coarseness, and the law of R it consumes is
 REFLEXIVITY.  Given x ≈ y, transport R x x along `≈` in the second
 argument. 

 --------
 背面：尊重带来粗糙，而它消耗的 R 法则是反身性。给定 x ≈ y，将 R x x 沿着第二个参数的 `≈` 传输。
*)
Lemma respects_coarser (HR : Reflexive R) : SetoidRespectsRel → SetoidCoarser.
Proof.
  intros Hr x y Hxy.
  exact (Hr x x x y (reflexivity x) Hxy (HR x)).
Qed.

(*
 ... hence for an equivalence relation the two hypotheses are one.  The
 source issue asks for a quotient by a "setoid-respecting" relation in
 its main body and for one by a relation "coarser than `≈`" in a
 trailing block harvested from a different book; this says that those
 two requests are the same request. 

 --------
 ... 因此对于一个等价关系，这两个假设是相同的。来源问题在其主体中要求对一个“尊重集体的”关系取商，而在从另一本书摘录的尾部块中要求对一个“比 `≈` 更粗”的关系取商；这表明这两个请求实际上是同一个请求。
*)
Theorem coarser_iff_respects (HR : Equivalence R) :
  SetoidCoarser ↔ SetoidRespectsRel.
Proof.
  split.
  - apply coarser_respects; apply HR.
  - apply respects_coarser; apply HR.
Qed.

End Hypotheses.

Arguments SetoidCoarser {A} R.
Arguments SetoidRespectsRel {A} R.

(* * ** The quotient object and its projection / * ** 商对象及其投射 *)

(*
 The quotient setoid: SAME CARRIER, coarser `≈`.  Note that
 [SetoidCoarser] does not appear -- an equivalence relation on the
 carrier is already enough to name a setoid.  It is the projection that
 needs the relation to be coarser. 

 --------
 商集合等式簇：相同的承载体，更粗的 `≈`。请注意 [SetoidCoarser] 并未出现——承载体上的等价关系已经足以命名一个集合等式簇。需要关系更粗的是投影。
*)
Definition SetsQuotient (A : SetoidObject) (R : crelation (carrier A))
  (HR : Equivalence R) : SetoidObject :=
  {| carrier := carrier A ; is_setoid := {| equiv := R ; setoid_equiv := HR |} |}.

(* The carrier is untouched, by conversion -- the [eq_refl] exception to the `≈` discipline, and the point of the construction. / 承运人未受转换影响——[eq_refl] 对 `≈` 规定的例外，以及构造的要点。 *)
Example sets_quot_carrier (A : SetoidObject) (R : crelation (carrier A))
  (HR : Equivalence R) : carrier (SetsQuotient A R HR) = carrier A.
Proof. reflexivity. Qed.

(*
 The projection is the identity function.  Its respectfulness clause,
 [Proper (equiv ==> equiv) (fun a => a)], is CONVERTIBLE with
 [SetoidCoarser R] and has no other content -- but writing
 [proper_morphism := HC] in the record literal is rejected, the
 elaborator not unfolding [SetoidCoarser] during unification, so the
 field is supplied by the one-step script below.  The same shape
 recurs at [sets_quot_med]. 

 --------
 投影是恒等函数。它的尊重条款 [Proper (equiv ==> equiv) (fun a => a)] 可以与 [SetoidCoarser R] 互换，并且没有其他内容——但在记录字面量中写入 [proper_morphism := HC] 会被拒绝，展开器在统一期间不展开 [SetoidCoarser]，因此该字段由下面的一步脚本提供。相同的形式在 [sets_quot_med] 处重复出现。
*)
Definition sets_quot_proj (A : SetoidObject) (R : crelation (carrier A))
  (HR : Equivalence R) (HC : SetoidCoarser R) :
  A ~{Sets}~> SetsQuotient A R HR.
Proof.
  unshelve refine {| morphism := fun a : carrier A => a |}.
  intros x y Hxy; exact (HC x y Hxy).
Defined.

(* ... and its action is the identity, by conversion. / ... 并且它的作用是通过转换实现恒等。 *)
Example sets_quot_proj_at (A : SetoidObject) (R : crelation (carrier A))
  (HR : Equivalence R) (HC : SetoidCoarser R) (a : carrier A) :
  sets_quot_proj A R HR HC a = a.
Proof. reflexivity. Qed.

(* Two elements are identified in the quotient exactly when R relates them -- again by conversion, so the quotient's `≈` is readable. / 当且仅当 R 关联它们时，商中会识别出两个元素——同样通过转换，因此商的 `≈` 是可读的。 *)
Example sets_quot_equiv (A : SetoidObject) (R : crelation (carrier A))
  (HR : Equivalence R) (x y : carrier A) :
  @equiv _ (SetsQuotient A R HR) x y = R x y.
Proof. reflexivity. Qed.

(* * ** The functor of R-respecting maps / * ** R-保持映射的函子 *)

Section RespFunctor.

Context {A : SetoidObject}.
Context (R : crelation (carrier A)).

(* h respects R when it cannot tell R-related elements apart. This is Mac Lane's condition on the functions that descend. / 当它无法区分与 R 相关的元素时，h 会尊重 R。这是 Mac Lane 对下降函数的条件。 *)
Definition SetsRespects (X : SetoidObject) (h : A ~{Sets}~> X) : Type :=
  ∀ x y : carrier A, R x y → h x ≈ h y.

Definition RespMap (X : SetoidObject) : Type :=
  { h : A ~{Sets}~> X & SetsRespects X h }.

(* Two respecting maps are compared by their underlying maps; the respectfulness witness carries no equational weight, exactly as in Instance/Grp/Quotient.v's [Kills_Setoid]. / 两个相关映射通过它们的基础映射进行比较；尊重性证据不带有任何方程权重，正如在 Instance/Grp/Quotient.v 的 [Kills_Setoid] 中一样。 *)
Program Definition RespMap_Setoid (X : SetoidObject) : Setoid (RespMap X) :=
  {| equiv := fun p q => `1 p ≈ `1 q |}.
Next Obligation.
  intros.
  constructor.
  - intros p x; reflexivity.
  - intros p q Hpq x; now symmetry.
  - intros p q r Hpq Hqr x; now transitivity (`1 q x).
Qed.

(* Postcomposition preserves respectfulness. / 后置组成保留了尊重。 *)
Lemma RespMap_post {X Y : SetoidObject} (k : X ~{Sets}~> Y) (p : RespMap X) :
  SetsRespects Y (k ∘ `1 p).
Proof.
  intros x y Hxy; simpl; unfold Basics.compose.
  apply proper_morphism.
  exact (`2 p x y Hxy).
Qed.

(*
 The functor.  It is COVARIANT -- postcomposition, not precomposition --
 which is what makes ⟨A/R, p⟩ a universal element in Mac Lane's sense
 rather than a representing object of a presheaf.  Nothing in this
 definition uses any law of R. 

 --------
 函子。它是协变的——后组合，而不是前组合——这正是使得 ⟨A/R, p⟩ 在 Mac Lane 意义上成为一个普遍元素，而不是一个预层的表示对象。在这个定义中没有使用 R 的任何定律。
*)
Program Definition RespFunctor : Sets ⟶ Sets := {|
  fobj := fun X => {| carrier := RespMap X ; is_setoid := RespMap_Setoid X |};
  fmap := fun X Y k =>
    {| morphism := fun p : RespMap X =>
         existT (SetsRespects Y) (k ∘ `1 p) (RespMap_post k p) |}
|}.
Next Obligation. intros X Y k p q Hpq a; simpl; now rewrite (Hpq a). Qed.
Next Obligation. intros X Y k k' Hk p a; simpl; exact (Hk _). Qed.
Next Obligation. intros X p a; simpl; reflexivity. Qed.
Next Obligation. intros X Y Z k k' p a; simpl; reflexivity. Qed.

End RespFunctor.

Arguments SetsRespects {A} R X h.
Arguments RespMap {A} R X.
Arguments RespFunctor {A} R.

(** ** The mediator / ** 调解员 *)

Section Mediator.

Context {A : SetoidObject}.
Context (R : crelation (carrier A)).
Context (HR : Equivalence R).

(*
 Descent.  In the group case (Instance/Grp/Quotient.v's
 [kills_descends]) this is a computation; here the mediator's
 respectfulness clause is CONVERTIBLE with the given map's
 [SetsRespects] witness, because the quotient's `≈` IS R and the
 mediator's underlying function IS the given one -- so the script is
 again one step, for the elaboration reason noted at
 [sets_quot_proj]. 

 --------
 下降。在群体情况（Instance/Grp/Quotient.v 的 [kills_descends]）中，这是一个计算；在这里，中介的尊重条款可以与给定映射的 [SetsRespects] 证据相互转换，因为商的 `≈` 是 R，并且中介的底层函数是给定的函数——因此该脚本同样是一步，出于 [sets_quot_proj] 处指出的详细化原因。
*)
Definition sets_quot_med {X : SetoidObject} (p : RespMap R X) :
  SetsQuotient A R HR ~{Sets}~> X.
Proof.
  unshelve refine
    {| morphism := fun a : carrier (SetsQuotient A R HR) => `1 p a |}.
  intros x y Hxy; exact (`2 p x y Hxy).
Defined.

(*
 The defining triangle, pointwise by [reflexivity]: the projection is
 the identity function, so there is nothing to compute. 

 --------
 由 [reflexivity] 点定义的三角形：投影是恒等函数，所以没有什么需要计算的。
*)
Lemma sets_quot_med_commutes (HC : SetoidCoarser R) {X : SetoidObject}
  (p : RespMap R X) : sets_quot_med p ∘ sets_quot_proj A R HR HC ≈ `1 p.
Proof. intro a; simpl; reflexivity. Qed.

Lemma sets_quot_med_unique (HC : SetoidCoarser R) {X : SetoidObject}
  (p : RespMap R X) (v : SetsQuotient A R HR ~{Sets}~> X)
  (Hv : v ∘ sets_quot_proj A R HR HC ≈ `1 p) : sets_quot_med p ≈ v.
Proof. intro a; simpl; symmetry; exact (Hv a). Qed.

End Mediator.

Arguments sets_quot_med {A} R HR {X} p.

(* * ** Mac Lane §III.1 construction 4: ⟨A/R, p⟩ is a universal element / * ** 麦克·莱恩 §III.1 构造 4：⟨A/R, p⟩ 是一个终元件 *)

Section Universal.

Context {A : SetoidObject}.
Context (R : crelation (carrier A)).
Context (HR : Equivalence R).
Context (HC : SetoidCoarser R).

(*
 The projection, packaged as an element of (RespFunctor R)(A/R).  Its
 respectfulness witness is the IDENTITY implication -- "R x y implies
 R x y" -- since the target's `≈` is R.

 The sigma's predicate is spelled out rather than left to inference,
 and that is a PORTABILITY fix, not decoration: on Coq 8.19/8.20 the
 elaborator resolves the [_] against the TYPE of the second component,
 here [∀ x y, R x y → R x y], instead of against the expected
 [RespMap], and rejects the definition.  Rocq 9.1 accepts either form,
 so the break is invisible on the default toolchain; it is the same
 trap Instance/Rng/Frac.v records for its fraction constructor, and
 every [existT] in these four files is written this way for it. 

 --------
 投影，被打包为 (RespFunctor R)(A/R) 的一个元素。它的尊重性证据是恒等蕴涵——“R x y 蕴含 R x y”——因为目标的 `≈` 是 R。

 sigma 的谓词被明确定义，而不是留给推理，这是一个可移植性修复，而不是装饰：在 Coq 8.19/8.20 上，展开器将 [_] 与第二个分量的类型 [∀ x y, R x y → R x y] 对比，而不是与期望的 [RespMap] 对比，因此拒绝定义。Rocq 9.1 接受任何一种形式，所以在默认工具链上这个问题不可见；这就是 Instance/Rng/Frac.v 为其分数构造器记录的陷阱，并且在这四个文件中的每个 [existT] 都是以这种方式编写的。
*)
Definition sets_quot_elem : RespMap R (SetsQuotient A R HR) :=
  existT (SetsRespects R (SetsQuotient A R HR))
    (sets_quot_proj A R HR HC) (fun x y (h : R x y) => h).

(*
 Mac Lane's construction 4.  Every R-respecting map out of A is
 (RespFunctor R u) applied to the projection, for a UNIQUE
 u : A/R -> X.  #303's [AUniversalElement] is used DIRECTLY, so neither
 of Theory/Universal/Element.v's routes to [Representable] is touched
 and no universe restriction is inherited at this point. 

 --------
 Mac Lane 的构造 4。每一个从 A 出发的 R-尊重映射都是 (RespFunctor R u) 应用于投影，对于唯一的 u : A/R -> X。#303 的 [AUniversalElement] 直接使用，因此 Theory/Universal/Element.v 的通往 [Representable] 的路径都未被触及，并且此时没有继承任何宇宙限制。
*)
Program Definition sets_quot_universal_element :
  AUniversalElement (RespFunctor R) (SetsQuotient A R HR) := {|
  aue_elem := sets_quot_elem
|}.
Next Obligation.
  intros X x.
  unshelve refine {| unique_obj := sets_quot_med R HR x |}.
  - exact (sets_quot_med_commutes R HR HC x).
  - intros v Hv; simpl in *.
    exact (sets_quot_med_unique R HR HC x v Hv).
Defined.

(* The class's element IS the projection, and the class's mediator IS [sets_quot_med] -- both by convertibility, the [eq_refl] exception, checking that the packaging rebuilt nothing. / 类的元素就是投影，类的中介者是 [sets_quot_med] —— 两者都可以转换，[eq_refl] 异常，检查包装没有重建任何东西。 *)
Example sets_quot_universal_elem_is_proj :
  `1 (@aue_elem _ (RespFunctor R) (SetsQuotient A R HR)
        sets_quot_universal_element)
    = sets_quot_proj A R HR HC.
Proof. reflexivity. Qed.

Example sets_quot_universal_med_is_med {X : SetoidObject} (x : RespMap R X) :
  unique_obj (@aue_universal _ (RespFunctor R) (SetsQuotient A R HR)
                sets_quot_universal_element X x)
    = sets_quot_med R HR x.
Proof. reflexivity. Qed.

(* * ** The representation, by the Yoneda-free route / * ** 通过 Yoneda 自由途径的表示 *)

(*
 [ue_representation] (Theory/Universal/Element.v) builds
 [Hom (A/R),─] ≅ RespFunctor R directly, mentioning no Yoneda lemma.
 The Yoneda-based [universal_element_yoneda] is NOT usable at [Sets]:
 its donor identifies object, hom and proof universes, and
 [Sets@{o so} : Category@{so o o}] does not.  Test/ProbeSetsQuotient.v
 pins that refusal, with a positive control at a category whose three
 universes can be identified. 

 --------
 [ue_representation]（Theory/Universal/Element.v）构建了
 [Hom (A/R),─] ≅ RespFunctor R 直接地，没有提到 Yoneda 引理。
 基于 Yoneda 的 [universal_element_yoneda] 在 [Sets] 处不可用：
 其捐赠者识别对象、hom 和证明宇宙，而
 [Sets@{o so} : Category@{so o o}] 不会。Test/ProbeSetsQuotient.v 确认了这一拒绝，同时在一个其三个位宇宙可识别的范畴上提供了阳性对照。
*)
(*
 [@Build_Representable] rather than the `{| ... |}` literal: for a Class,
 the literal sends the elaborator looking for an instance of the head
 before the ambient category is fixed -- the same trap
 Theory/Universal/Element.v records at [AUniversalElement_of_hom]. 

 --------
 [@Build_Representable] 而不是 `{| ... |}` 字面意思：对于一个类，字面意思会让展开器在环境类别确定之前寻找头的实例——同样的陷阱 Theory/Universal/Element.v 记录在 [AUniversalElement_of_hom] 。
*)
Definition sets_quot_Representable : Representable (RespFunctor R) :=
  @Build_Representable Sets (RespFunctor R) (SetsQuotient A R HR)
    (ue_representation (RespFunctor R) (SetsQuotient A R HR)
       sets_quot_universal_element).

(*
 The natural isomorphism itself, named.  Its type is
 [@Isomorphism (Fun Sets Sets) (fobj[Curried_Hom Sets] (A/R))
 (RespFunctor R)], i.e. [Hom (A/R),─] ≅ RespFunctor R in [Sets, Sets];
 it is left to be read off [represented] rather than ascribed, because
 spelling [@Curried_Hom _ (A/R)] in a type leaves the ambient category an
 unresolved evar (the object must be one of [C^op], and nothing in the
 annotation fixes [C]).  It is [ue_representation]'s value on the nose,
 the [represented] projection returning it by conversion. 

 --------
 自然同构本身，命名为。它的类型是
 [@Isomorphism (Fun Sets Sets) (fobj[Curried_Hom Sets]  (A/R))
 (RespFunctor R)]，即  [Hom (A/R),─]  ≅ RespFunctor R 在  [Sets, Sets] 中；
 它需要从  [represented] 中读取而不是指定，因为在类型中拼写  [@Curried_Hom _ (A/R)] 会使环境类别成为一个未解决的 evar（对象必须是  [C^op] 之一，而注释中没有任何内容能固定  [C]）。它正是  [ue_representation] 的值，
 [represented] 投影通过转换返回它。
*)
Definition sets_quot_representation :=
  @represented _ (RespFunctor R) sets_quot_Representable.

(* The representing object is the quotient on the nose. / 所表示的对象正是商。 *)
Example sets_quot_repr_obj :
  @repr_obj _ (RespFunctor R) sets_quot_Representable = SetsQuotient A R HR.
Proof. reflexivity. Qed.

End Universal.

Arguments sets_quot_elem {A} R HR HC.
Arguments sets_quot_universal_element {A} R HR HC.

(* * ** The two degenerate coarsenings, named / * ** 这两个退化的粗化，命名为 *)

(*
 THE FINEST: R := the carrier's own `≈`.  The quotient is the object it
 started from, and it is so ON THE NOSE -- Leibniz equality of the whole
 [SetoidObject] record, by [eq_refl].  Primitive projections give record
 eta, so [is_setoid A] and the rebuilt [{| equiv := ...; setoid_equiv :=
 ... |}] are the same term. 

 --------
 最精细的：R := 运营商自身的 `≈`。商是它开始的对象，并且它正好如此 —— [SetoidObject] 记录的整体莱布尼茨相等，由 [eq_refl]。原始投影给出记录 eta，因此 [is_setoid A] 和重建的 [{| equiv := ...; setoid_equiv := ... |}] 是同一个项。
*)
Example sets_quot_finest_eq (A : SetoidObject) :
  SetsQuotient A (@equiv _ A) (@setoid_equiv _ A) = A.
Proof. reflexivity. Qed.

Definition sets_quot_finest_coarser (A : SetoidObject) :
  SetoidCoarser (@equiv _ A) := fun _ _ h => h.

(* THE COARSEST: R := the total relation, which identifies everything. / 最粗略的：R := 总关系，识别一切。 *)
Definition TotalRelT (A : SetoidObject) : crelation (carrier A) :=
  fun _ _ => poly_unit.

Lemma TotalRelT_Equivalence (A : SetoidObject) : Equivalence (TotalRelT A).
Proof.
  constructor.
  - intro x; exact ttt.
  - intros x y _; exact ttt.
  - intros x y z _ _; exact ttt.
Qed.

Definition TotalRelT_coarser (A : SetoidObject) : SetoidCoarser (TotalRelT A) :=
  fun _ _ _ => ttt.

Lemma sets_quot_total_collapses (A : SetoidObject) (x y : carrier A) :
  @equiv _ (SetsQuotient A (TotalRelT A) (TotalRelT_Equivalence A)) x y.
Proof. exact ttt. Qed.

(* * ** Non-vacuity: a quotient that neither keeps everything apart nor collapses everything / * ** 非虚无性：一种既不将万物分隔开来，也不将万物融合在一起的商 *)

(*
 Parity on the naturals, as a coarsening of the DISCRETE setoid on
 [nat] -- so `≈` there is Leibniz equality and the coarsening is
 genuine.  [Nat.even] is a boolean, so the relation is a decidable
 equation of booleans; that is what lets the negative results below be
 proved rather than merely expected. 

 --------
 自然数上的奇偶性，作为对 [nat] 上离散集合体的粗化 —— 因此在 `≈` 上存在莱布尼茨相等性，并且这种粗化是实际存在的。[Nat.even] 是布尔类型，所以该关系是布尔值的可判定方程；这正是使下述负面结果能够被证明而不仅仅是预期的原因。
*)
Definition NatDiscrete : SetoidObject :=
  {| carrier := nat ; is_setoid := eq_Setoid nat |}.

Definition nat_parity : crelation (carrier NatDiscrete) :=
  fun m n => Nat.even m = Nat.even n.

Lemma nat_parity_Equivalence : Equivalence nat_parity.
Proof.
  constructor.
  - intro m; reflexivity.
  - intros m n H; now symmetry.
  - intros m n k H1 H2; now transitivity (Nat.even n).
Qed.

Definition nat_parity_coarser : SetoidCoarser nat_parity :=
  fun m n (H : m = n) => f_equal Nat.even H.

Definition NatParity : SetoidObject :=
  SetsQuotient NatDiscrete nat_parity nat_parity_Equivalence.

(* The quotient IDENTIFIES: 0 and 2 are equal in it, by computation. / 商识别：通过计算，0 和 2 在其中相等。 *)
Example nat_parity_merges : @equiv _ NatParity 0%nat 2%nat.
Proof. reflexivity. Qed.

(*
 The quotient SEPARATES: 0 and 1 are not.  This is where a decidable
 invariant earns its keep -- the relation unfolds to [true = false]. 

 --------
 商分开了：0 和 1 没有分开。这就是可判定不变量发挥作用的地方——关系展开为 [true = false]。
*)
Lemma nat_parity_separates : @equiv _ NatParity 0%nat 1%nat → False.
Proof. intro H; discriminate H. Qed.

(*
 ... so the parity quotient is neither degenerate case.  It is not the
 finest, since the finest keeps 0 and 2 apart; and it is not the
 coarsest, since the coarsest identifies 0 and 1.  Both are stated as
 refutations of the RELATIONS, which is the level at which the two
 degeneracies were defined. 

 --------
 ... 因此，奇偶商既不是退化情况。它不是最细的，因为最细的将 0 和 2 区分开来；它也不是最粗的，因为最粗的会将 0 和 1 视为相同。两者都被表述为对关系的反驳，这是定义这两种退化情况的层级。
*)
Lemma nat_parity_not_finest :
  (∀ m n : carrier NatDiscrete, nat_parity m n → @equiv _ NatDiscrete m n) → False.
Proof.
  intro H.
  pose proof (H 0%nat 2%nat eq_refl) as E; discriminate E.
Qed.

Lemma nat_parity_not_coarsest :
  (∀ m n : carrier NatDiscrete, TotalRelT NatDiscrete m n → nat_parity m n) → False.
Proof. intro H; exact (nat_parity_separates (H 0%nat 1%nat ttt)). Qed.

(*
 And the universal property is inhabited at it: the parity map itself
 is a respecting map, so the mediator out of the quotient exists and
 computes on closed input. 

 --------
 并且该泛性质在其上是可居的：奇偶映射本身是一个保持映射，因此从商出的中介是存在的，并且可以对封闭输入进行计算。
*)
Definition BoolSet : SetoidObject :=
  {| carrier := bool ; is_setoid := eq_Setoid bool |}.

(*
 [BoolSet] and [NatDiscrete] are discrete, so [proper_morphism] here is
 respect for Leibniz equality and instance resolution discharges it;
 both carriers are concrete ([nat], [bool]), so no universe
 polymorphism is at stake in leaving it to resolution. 

 --------
 [BoolSet] 和 [NatDiscrete] 是离散的，所以 [proper_morphism] 在这里是尊重莱布尼茨等式，并且实例解析会处理它；两个承载体都是具体的（[nat]，[bool]），所以在将其留给解析时，不涉及宇宙多态性。
*)
Definition nat_even_map : NatDiscrete ~{Sets}~> BoolSet.
Proof.
  unshelve refine {| morphism := Nat.even |}.
Defined.

Definition nat_even_resp : RespMap nat_parity BoolSet :=
  existT (SetsRespects nat_parity BoolSet)
    nat_even_map (fun m n (H : nat_parity m n) => H).

(* The descended map on the quotient, evaluated. / 在商上降下的映射，已被求值。 *)
Example nat_parity_med_at_4 :
  sets_quot_med nat_parity nat_parity_Equivalence nat_even_resp 4%nat = true.
Proof. reflexivity. Qed.

Example nat_parity_med_at_7 :
  sets_quot_med nat_parity nat_parity_Equivalence nat_even_resp 7%nat = false.
Proof. reflexivity. Qed.
