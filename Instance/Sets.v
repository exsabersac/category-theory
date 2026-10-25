Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(** The category of setoids / 集合等价类的范畴 *)

(*
 nLab: https://ncatlab.org/nlab/show/category+of+sets
 nLab: https://ncatlab.org/nlab/show/setoid
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_sets
 Wikipedia: https://en.wikipedia.org/wiki/Setoid

 This is the category [Sets], the constructive analogue of the classical
 category Set. To model "sets" without quotient types and without the
 function-extensionality axiom, objects are not bare types but setoids
 (Bishop sets): a carrier type together with an equivalence relation `≈`.
 Morphisms are setoid maps, i.e. functions that respect `≈` (proper
 functions), and the hom-setoid identifies two such maps when they agree
 pointwise up to the codomain's `≈` (extensional equality of setoid maps,
 realised without [funext]).

 objects: setoids        (carrier type + equivalence relation `≈`)
 arrows: setoid maps    (functions f with x ≈ y → f x ≈ f y)
 hom-setoid: f ≈ g  :=  ∀ x, f x ≈ g x   (pointwise, up to codomain `≈`)
 identity: the identity function
 composition: composition of functions, again respecting `≈`

 This file builds the category and its first structural instances:
 [Sets_Terminal] (singleton), [Sets_Initial] (empty), the cartesian
 [Sets_Product_Monoidal], and the characterizations of monos as injections
 and epis as surjections. The cartesian / closed structure proper lives in
 the companion files Instance/Sets/Cartesian.v and
 Instance/Sets/Cartesian/Closed.v. 

 --------
 nLab:  https://ncatlab.org/nlab/show/category+of+sets 
 nLab:  https://ncatlab.org/nlab/show/setoid 
 维基百科:  https://en.wikipedia.org/wiki/Category_of_sets 
 维基百科:  https://en.wikipedia.org/wiki/Setoid 

 这是类别  [Sets] ，古典类别 Set 的构造性类比。为了在没有商类型和函数外延公理的情况下建模“集合”，对象不是简单的类型，而是集合等价类（Bishop 集）：一个载体类型以及一个等价关系  `≈` 。
 态射是集合等价类映射，即尊重  `≈` 的函数（适当函数），同态集合等价类当两个映射在点上根据值域的  `≈` 一致时会被识别为相同（集合等价类映射的外延等价性，通过不使用  [funext] 实现）。对象：集合等价类（载体类型 + 等价关系  `≈` ）
 箭头：集合等价映射（函数 f 满足 x ≈ y → f x ≈ f y）
 同态集合等价：f ≈ g := 对所有 x, 有 f x ≈ g x（逐点比较，直到陪域 `≈` ）
 身份：恒等函数
 组成：函数的组合，同样遵守 `≈` 

 该文件构建了该范畴及其第一个结构实例：
 [Sets_Terminal]（单例），[Sets_Initial]（空集），笛卡尔范畴 [Sets_Product_Monoidal]，以及单射被描述为单入射、满射被描述为满射。
 笛卡尔 / 闭结构本身保存在伴随文件 Instance/Sets/Cartesian.v 和
 Instance/Sets/Cartesian/Closed.v 中。
*)

(*
 Bishop sets, the zero-axiom regime, and the universal codomain

 nLab:   https://ncatlab.org/nlab/show/Bishop+set
 nLab:   https://ncatlab.org/nlab/show/E-category
 nLab:   https://ncatlab.org/nlab/show/predicative+topos
 Book:   Bishop, "Foundations of Constructive Analysis", McGraw-Hill 1967
 Thesis: Hofmann, "Extensional Concepts in Intensional Type Theory",
 University of Edinburgh, LFCS report ECS-LFCS-95-327, 1995

 The two records below transcribe definitions Bishop set down in 1967.
 A set, for Bishop, is not an entity with an ideal existence: to define
 one is to prescribe what must be done to construct an element and what
 must be done to show two elements equal (Bishop 1967, chapter one, "A
 constructivist manifesto"); a function is a finite routine on elements
 that respects the two equalities.  [SetoidObject] and [SetoidMorphism]
 are those definitions as records — carrier plus equivalence, program
 plus congruence certificate.  The name "setoid" entered type theory
 with Hofmann's 1995 thesis (per the nLab), which also supplies the
 strategy's mathematical warrant: Hofmann built models of intensional
 type theory out of types with equivalence relations, models in which
 functional extensionality and quotients hold, so working with setoids
 is not a stopgap but a model construction.  The design space — total
 versus partial setoids, four notions of setoid map — is surveyed in
 (Barthe, Capretta, Pons, "Setoids in type theory", JFP 13(2) 2003);
 this file sits in the total-setoid column with a Type-valued relation.

 Two problems meet here.  First, Coq's intensional equality identifies
 only terms with the same definition: quotient types are absent, and
 pointwise-equal functions need not be provably equal.  Bishop's move
 is to never separate a carrier from its equality — a quotient is just
 another choice of `≈` on the same carrier (Construction/Quotient.v is
 the hom-level version) — and [SetoidMorphism_equiv] makes equality of
 maps extensional by definition rather than by axiom.  This is the
 decision Theory/Category.v credits with the library's zero-axiom
 regime.  Second, category theory needs a Set to land in.  The debt to
 Theory/Category.v runs both ways: a [Category] there is what the nLab
 calls an E-category — enriched in setoids, terminology in active use
 in Palmgren's school (Palmgren, Wilander, "Constructing categories
 and setoids of setoids in type theory", LMCS 10(3) 2014) — so its
 hom-functor can only land in a category whose objects are setoids.
 [Sets] is that category: the codomain of Functor/Hom.v and the Yoneda
 embedding (Functor/Hom/Yoneda.v), of presheaves, of the ends and
 coends of Instance/Sets/End.v and Instance/Sets/Coend.v, and of the
 weights of Structure/Limit/Weighted.v.  Instance/Coq.v is the
 contrast object: bare types under pointwise Leibniz equality, with no
 chosen `≈`.

 The cost has a name.  Altenkirch calls it setoid hell (Altenkirch,
 "From setoid hell to homotopy heaven? The role of extensionality in
 Type Theory", TYPES 2017): every type-level construction must be
 lifted to setoids by hand, the lifting is boilerplate, and the
 implementation is never actually hidden.  The Type-valued [Proper]
 machinery assembled in Lib/Foundation.v exists to make that
 discipline bearable; and the same talk concedes the other side of the
 ledger — most constructions need no higher dimensions, and setoids
 or groupoids suffice.  The successor programme is (Altenkirch,
 Boulier, Kaposi, Tabareau, "Setoid Type Theory — A Syntactic
 Translation", MPC 2019).

 How much of the classical Set survives?  In Martin-Löf type theory
 the category of setoids is a ΠW-pretopos, a locally cartesian closed
 pretopos with W-types and a predicative analogue of a topos (van den
 Berg, "Predicative toposes", arXiv:1207.0959 (2012), after Moerdijk
 and Palmgren 1999/2000).  Predicativity is visible in the subobject
 classifier: its characteristic maps must receive a [Type]-valued
 truth value, so the classifier for [Sets] lives one universe up and
 Instance/Sets/Classifier.v states it as cross-universe theorems
 rather than as an instance — a theorem-shaped fact about size, not a
 gap in the formalization.  A one-level instance does exist
 CONDITIONALLY, in Instance/Sets/Classifier/OneLevel.v, under a
 hypothesis this tree does not inhabit axiom-free (every impredicative
 truncation at level o inverts, or every mono's image membership is
 decidable — each implied by informative excluded middle at level o).
 That obstruction is genuinely about the
 classifier and does not spread: [surjectivity_is_epic] at the end of
 this file was long believed to inherit it, but the classical
 truth-value probe is not the only one available, and the cokernel
 pair used below stays at the universe of the carriers.  Because `≈`
 is Type-valued,
 its proofs carry data: [bijective_is_iso] turns a surjectivity
 witness into an honest inverse function with no appeal to choice,
 the choice having been data all along.  [Sets] is complete
 (Instance/Sets/Complete.v); its remaining structure is built piecewise
 under Instance/Sets/ — products and exponentials, small indexed
 (co)products, pushouts, and Cauchy completeness (Karoubi.v). 

 --------
 Bishop 集合、零公理体系与通用值域

 nLab:    https://ncatlab.org/nlab/show/Bishop+set 
 nLab:    https://ncatlab.org/nlab/show/E-category 
 nLab:    https://ncatlab.org/nlab/show/predicative+topos 
 书籍:   Bishop, 《构造分析的基础》，McGraw-Hill 1967
 论文: Hofmann, 《内涵类型理论中的外延概念》，
 爱丁堡大学, LFCS 报告 ECS-LFCS-95-327, 1995下面的两条记录转录了Bishop在1967年所制定的定义。对Bishop而言，一个集合并不是具有理想存在的实体：定义一个集合就是规定必须做些什么来构造一个元素，以及必须做些什么来证明两个元素相等（Bishop 1967，第1章，《建构主义宣言》）；函数是作用于元素的有限程序，并且遵守这两个相等关系。[SetoidObject] 和 [SetoidMorphism] 是那些定义作为记录的表示——承载者加等价关系，程序加一致性证明。“setoid” 这个名称随着 Hofmann 1995 年的论文进入了类型理论（根据 nLab 的说法），该论文也提供了该策略的数学依据：Hofmann 构建了由带有等价关系的类型组成的内涵类型理论模型，在这些模型中，函子外延性和商对象成立，因此使用 setoid 并不是权宜之计，而是一种模型构建。这一设计空间——总 setoid 与部分 setoid、四种 setoid 映射的概念——在 (Barthe, Capretta, Pons, 《类型理论中的 Setoids》，JFP 13(2) 2003) 中进行了概述；该文件属于总 setoid 列，使用一个取值为 Type 的关系。这里遇到两个问题。首先，Coq 的内涵等式只识别具有相同定义的项：商类型不存在，并且逐点相等的函数不一定可证明相等。Bishop 的做法是从不将载体与其等式分开——商只是同一载体上的另一种 `≈` 选择（Construction/Quotient.v 是同源层的版本）——而 [SetoidMorphism_equiv] 通过定义而非公理使映射的等式具有外延性。这个决定被 Theory/Category.v 归功于库的零公理机制。其次，范畴论需要一个集合作为落脚点。对 Theory/Category.v 的依赖是双向的：[Category] 那里存在 nLab 所称的 E-范畴——在 Palmgren 学派（Palmgren, Wilander, “Constructing categories and setoids of setoids in type theory”, LMCS 10(3) 2014）中广泛使用的术语——因此它的 Hom 函子只能落在对象为 setoid 的范畴中。[Sets] 就是那个范畴：Functor/Hom.v 和 Yoneda 嵌入（Functor/Hom/Yoneda.v）的余域，预层的余域，以及 Instance/Sets/End.v 和 Instance/Sets/Coend.v 的 end 和 coend 的余域，以及 Structure/Limit/Weighted.v 的加权余域。Instance/Coq.v 是对比对象：基于逐点 Leibniz 等式的裸类型，没有选定的 `≈`。代价有一个名字。Altenkirch称之为集合等价地狱（Altenkirch, "从集合等价地狱到同伦天堂？扩展性在类型理论中的作用", TYPES 2017）：每一个类型层的构造都必须手动提升到集合等价，提升过程是样板代码，而且实现实际上从未被隐藏。Lib/Foundation.v 中组装的类型值 [Proper] 机制存在的目的就是让这种方法学可以忍受；同一演讲也承认了账目的另一面——大多数构造不需要更高维度，集合等价或群oid就足够了。继任计划是（Altenkirch, Boulier, Kaposi, Tabareau, "集合等价类型理论——语法翻译", MPC 2019）。经典集合论还有多少存留？在Martin-Löf类型理论中，集合类(category of setoids)是一个ΠW-预拓扑(pretopos)，一个带有W型的局部笛卡尔闭预拓扑，以及一个公理化的拓扑类(topos)的可断言(predicative)类比（van den Berg，《Predicative toposes》，arXiv:1207.0959 (2012)，参照Moerdijk和Palmgren 1999/2000）。可断言性在子对象分类器(subobject classifier)中可见：它的特征映射必须接收[Type]值的真值，因此[Sets]的分类器存在于更高的宇宙中，而Instance/Sets/Classifier.v将其陈述为跨宇宙的定理，而不是一个实例——一个关于大小的定理形事实，而不是形式化中的一个空白。确实存在一个一层实例
 在 Instance/Sets/Classifier/OneLevel.v 中有条件地存在，在一个假设下，这棵树不属于无公理的情形（每个在级别 o 的蕴含截断都可逆，或者每个单射的像成员资格都是可判定的——每一个都由级别 o 的信息排中律推出）。这种障碍确实与分类器有关，但不会扩散：文件末尾的 [surjectivity_is_epic] 长期以来被认为继承了它，但经典真值探针并不是唯一可用的方法，下文使用的余核对仍然停留在载体的宇宙中。因为 `≈` 是类型值的，它的证明携带数据：[bijective_is_iso] 将满射的证据转化为一个真实的逆函数，而无需诉诸选择，因为选择从一开始就是数据。[Sets] 是完整的
 (Instance/Sets/Complete.v)；其剩余结构在 Instance/Sets/ 下逐步构建 — 乘积和指数，小索引的
 (co)乘积，推出，以及柯西完备性 (Karoubi.v)。
*)

Record SetoidObject@{o p} : Type@{max(o+1,p+1)} := {
  carrier :> Type@{o};               (* the underlying type (Bishop carrier) / 基础类型（主教载体） *)
  is_setoid :> Setoid@{o p} carrier   (* its equivalence relation `≈` / 它的等价关系 `≈` *)
}.
#[export] Existing Instance is_setoid.

(*
 A setoid map: a function on carriers together with a proof that it respects
 the two equivalences. This is the morphism part of [Sets]. 

 --------
 集合等价映射：载体上的一个函数，以及一个证明它尊重两个等价关系的证明。这是 [Sets] 的态射部分。
*)
Record SetoidMorphism@{o h p} `{Setoid@{o p} x} `{Setoid@{o p} y} := {
  morphism :> x → y;                  (* the underlying function on carriers / 承运人的基础功能 *)
  proper_morphism :>                  (* it sends `≈`-related inputs to `≈`-related outputs / 它将与 `≈` 相关的输入发送到与 `≈` 相关的输出 *)
    Proper@{h p} (respectful@{h p h p h p} equiv equiv) morphism
}.
#[export] Existing Instance proper_morphism.

Arguments SetoidMorphism {_} _ {_} _.
Arguments morphism {_ _ _ _ _} _.

(*
 Extensional equality of setoid maps: two maps are equivalent when they
 agree pointwise, judged up to the codomain's `≈`. This is the hom-setoid's
 underlying relation; [funext] is not needed because we compare up to `≈`. 

 --------
 集合范畴映射的外延相等：当两个映射在每一点上都相同时，它们是等价的，这里的比较是以值域的 `≈` 为准。这是同态集合范畴的基本关系；因为我们是按 `≈` 进行比较，所以不需要 [funext]。
*)
Definition SetoidMorphism_equiv@{o h p} {x y : SetoidObject@{o p}} :
  crelation@{h p} (SetoidMorphism@{o h p} x y) :=
  fun f g => ∀ x, @equiv@{o p} _ y (f x) (g x).

Arguments SetoidMorphism_equiv {x y} _ _ /.

#[export]
Program Instance SetoidMorphism_Setoid@{o h p} {x y : SetoidObject@{o p}} :
  Setoid@{h p} (SetoidMorphism@{o h p} x y) := {|
  equiv := SetoidMorphism_equiv@{o h p};
|}.
Next Obligation.
  constructor; repeat intro.
  - reflexivity.
  - symmetry.
    apply X.
  - transitivity (y0 x1).
    + apply X.
    + apply X0.
Qed.

(*
 The identity and the composite give their properness fields as terms
 (issue #1347).  Left to instance resolution, the identity's field was
 [subrelation_id_proper (subrelation_refl equiv)] and the composite's a
 chain of [Reflexive_partial_app_morphism], [compose_proper] and
 [proper_proper_proxy], each of them with an opaque part in the standard
 library (by [Print Opaque Dependencies]), so that in [Sets] the
 composite of h with the identity did not convert with h.  As terms, both
 unit laws and associativity hold of these two constants at [eq_refl]
 (Test/ProbeSetsTerms1347.v).  The universe blocks are unchanged by
 [About]: their caps come from [Datatypes.id] (ID.u0) and
 [Basics.compose] (compose.u0 to compose.u2), not from the fields. 

 --------
 恒等和复合给出了它们的适当域作为项（问题 #1347）。在实例解析中，恒等的域是 [subrelation_id_proper (subrelation_refl equiv)]，而复合的是一串 [Reflexive_partial_app_morphism]、[compose_proper] 和 [proper_proper_proxy]，它们每一个在标准库中都有一个不透明的部分（由 [Print Opaque Dependencies]），因此在 [Sets] 中，h 与恒等的复合没有随 h 转换。作为项，这两个常数在 [eq_refl] 上都满足单位律和结合律（Test/ProbeSetsTerms1347.v）。宇宙块没有被 [About] 改变：它们的上界来自 [Datatypes.id]（ID.u0）和 [Basics.compose]（compose.u0 到 compose.u2），而不是来自这些域。
*)
Definition setoid_morphism_id@{o h p} {x : SetoidObject@{o p}} :
  SetoidMorphism@{o h p} x x := {|
  morphism := Datatypes.id;
  proper_morphism := fun _ _ H => H
|}.

#[export] Hint Unfold setoid_morphism_id : core.

Definition setoid_morphism_compose@{o h p} {x y z : SetoidObject@{o p}}
        (g : SetoidMorphism@{o h p} y z)
        (f : SetoidMorphism@{o h p} x y) : SetoidMorphism@{o h p} x z := {|
  morphism := Basics.compose g f;
  proper_morphism := fun a b H =>
    proper_morphism g _ _ (proper_morphism f a b H)
|}.

#[export] Hint Unfold setoid_morphism_compose : core.

Program Definition setoid_morphism_compose_respects@{o h p}
  {x y z : SetoidObject@{o p}} :
  Proper@{h p} (equiv@{h p} ==> equiv@{h p} ==> equiv@{h p})
    (@setoid_morphism_compose x y z).
Proof.
  unfold Proper, respectful.
  simpl; intros.
  rewrite X.
  apply proper_morphism, X0.
Qed.

(*
 The category of setoids.

 objects: setoids
 arrows: setoid homomorphisms
 identity: typical identity of sets
 composition: composition of set maps, preserving equivalence

 --------
 集合类的范畴。

 对象：集合类
 箭头：集合类同态
 单位：集合的典型单位
 组合：保持等价关系的集合映射的组合
*)
Program Definition Sets@{o so} : Category@{so o o} := {|
  obj     := SetoidObject@{o o} : Type@{so};
  hom     := λ x y, SetoidMorphism@{o o o} x y : Type@{o};
  homset  := @SetoidMorphism_Setoid@{o o o};
  id      := @setoid_morphism_id@{o o o};
  compose := @setoid_morphism_compose@{o o o};

  compose_respects := @setoid_morphism_compose_respects@{o o o}
|}.

Require Import Category.Theory.Isomorphism.

(*
 An isomorphism between arrows in a category C is an isomorphism of objects
 in the category of set(oid)s, taking [hom] to the be the carrier type, and
 arrow equivalence to be the setoid. By using Sets in this way, we gain the
 fact that the arrows on both sides are respectful of C's notion of arrow
 equivalence. 

 --------
 范畴 C 中箭头之间的同构是集合(oid)范畴中对象的同构，将 [hom] 视为承载类型，并将箭头等价视为集合oid。通过以这种方式使用集合，我们获得了这样一个事实：两边的箭头都遵循 C 对箭头等价的概念。
*)
Notation "x ≊ y" := ({| carrier := x |} ≅[Sets] {| carrier := y |})
  (at level 99) : category_scope.

#[export]
Program Instance isomorphism_to_sets_respects
        `{Setoid x} `{Setoid y}
        (iso : @Isomorphism Sets {| carrier := x |} {| carrier := y |}) :
  Proper (equiv ==> equiv) (to iso).
Next Obligation.
  repeat intro.
  destruct iso; simpl in *.
  destruct to; simpl in *.
  rewrite X; reflexivity.
Qed.

#[export]
Program Instance isomorphism_from_sets_respects
        `{Setoid x} `{Setoid y}
        (iso : @Isomorphism Sets {| carrier := x |} {| carrier := y |}) :
  Proper (equiv ==> equiv) (from iso).
Next Obligation.
  repeat intro.
  destruct iso; simpl in *.
  destruct from; simpl in *.
  rewrite X; reflexivity.
Qed.

(* Build a [SetoidMorphism] by giving its underlying function and leaving the [proper_morphism] obligation as a fresh goal. / 通过给出其底层函数并将 [proper_morphism] 义务作为一个新的目标，来构建一个 [SetoidMorphism]。 *)
Ltac morphism :=
  unshelve (refine {| morphism := _ |}; simpl; intros).

Require Import Category.Structure.Terminal.

(* The singleton setoid: [poly_unit] under `=`, used as the terminal object. / 单例集合类：[poly_unit] 在 `=` 下，用作终端对象。 *)
#[export]
Program Instance Unit_Setoid@{u} : Setoid@{u u} poly_unit@{u} := {
  equiv := fun x y => x = y
}.

(*
 Terminal object: the singleton. There is exactly one map into it (every
 element maps to [ttt]), unique up to `≈`. 

 --------
 终端对象：单例。恰好有一个映射指向它（每个元素都映射到 [ttt]），在 `≈` 下唯一。
*)
#[export]
Program Instance Sets_Terminal : @Terminal Sets := {
  terminal_obj := {| carrier := poly_unit |};
  one := fun _ => {| morphism := fun _ => ttt |};
  one_unique := fun x f g => _
}.
Next Obligation. destruct (f x0), (g x0); reflexivity. Qed.

Require Import Category.Structure.Initial.

(* The empty setoid: [False] as carrier; equivalence is vacuous. / 空等价类：以 [False] 为承载；等价关系是空的。 *)
#[export]
Program Instance False_Setoid@{u} : Setoid@{u u} False.
Next Obligation. proper. Qed.

(*
 Initial object: the empty setoid. The unique map out of it is the empty
 function (by [False] elimination). 

 --------
 初始对象：空集合。同态映射出它的是空函数（依据 [False] 消去法）。
*)
#[export]
Program Instance Sets_Initial : @Initial Sets := {
  terminal_obj := {| carrier := False |};
  one := _
}.
Next Obligation.
  construct.
  - contradiction.
  - proper.
Qed.
Next Obligation. contradiction. Qed.

Require Import Category.Structure.Monoidal.

(*
 Cartesian monoidal structure on [Sets]: the tensor is the product of
 setoids (carrier = product of carriers, `≈` componentwise) and the unit is
 the singleton setoid. The unitor/associator obligations below supply the
 coherence isomorphisms. 

 --------
 [Sets] 上的笛卡尔单体结构：张量是集合同构的乘积（载体 = 载体的乘积，`≈` 按分量进行），单位是单元素集合同构。下面的单元器/结合器义务提供了相干同构。
*)
#[export]
Program Instance Sets_Product_Monoidal : @Monoidal Sets := {
  I      := {| carrier := poly_unit |};
  tensor := {|
    fobj := fun p =>
      {| carrier := carrier (fst p) * carrier (snd p)
       ; is_setoid := _
       |};
    fmap := fun x y f =>
      {| morphism := fun p => (fst f (fst p), snd f (snd p))
       ; proper_morphism := _ |}
  |}
}.
Next Obligation.
  construct.
  - repeat intro.
    destruct s, s0.
    try rename X into H.
    try rename X0 into H0.
    exact (fst H ≈ fst H0 ∧ snd H ≈ snd H0).
  - simpl.
    equivalence.
Defined.
Next Obligation.
  proper; simpl in *.
  - destruct s.
    now rewrites.
  - destruct s0.
    now rewrites.
Qed.
Next Obligation.
  construct.
  - construct.
    + try rename X into H.
      now destruct H.
    + proper.
  - construct.
    + split; [ exact ttt | assumption ].
    + proper.
  - simpl.
    reflexivity.
  - simpl.
    destruct x0.
    simpl.
    destruct p.
    split; reflexivity.
Defined.
Next Obligation.
  construct.
  - construct.
    + try rename X into H.
      now destruct H.
    + proper.
  - construct.
    + split; [ assumption | exact ttt ].
    + proper.
  - simpl.
    reflexivity.
  - simpl.
    destruct x0.
    simpl.
    destruct p.
    split; reflexivity.
Defined.
Next Obligation.
  construct.
  - construct.
    + simplify; auto.
    + proper.
  - construct.
    + simplify; auto.
    + proper.
  - simpl.
    simplify; simpl; cat.
  - simpl.
    simplify; simpl; cat.
Defined.

(*
 The singleton as a [SetoidObject], packaging [unit_setoid] for use as a
 probe object below (a map out of it picks an element up to `≈`). 

 --------
 单例作为 [SetoidObject]，将 [unit_setoid] 打包用于以下的探针对象（从中映射的元素最多为 `≈`）。
*)
Definition unit_setoid_object@{t u} : SetoidObject@{t u} :=
  {| carrier   := poly_unit@{t}
   ; is_setoid := unit_setoid@{t u} |}.

(*
 In [Sets] the monomorphisms are exactly the injections (up to `≈`). The
 non-trivial direction probes [f] with two constant maps out of the singleton
 [unit_setoid_object]. 

 --------
 在 [Sets] 中，单态正好是注入（在 `≈` 下）。非平凡方向用来自单例 [unit_setoid_object] 的两个常量映射探测 [f]。
*)
Lemma injectivity_is_monic {X Y : SetoidObject} (f : X ~{Sets}~> Y) :
  (∀ x y : X, f x ≈ f y → x ≈ y) ↔ Monic f.
Proof.
  split.
  - intros HA.
    constructor.
    autounfold in *; intros ??? HB.
    simpl in *; intros.
    apply HA, HB.
  - intros HA ?? HB.
    given (const_x : unit_setoid_object ~{ Sets }~> X). {
      construct.
      - apply x.
      - proper.
    }
    given (const_y : unit_setoid_object ~{ Sets }~> X). {
      construct.
      - apply y.
      - proper.
    }
    destruct HA.
    specialize (monic unit_setoid_object const_x const_y).
    unfold const_x in monic.
    unfold const_y in monic.
    simpl in *.
    eapply monic; eauto.
    constructor.
Qed.

(*
 In [Sets] a bijection (injective and split-surjective up to `≈`) is an
 isomorphism: the chosen preimage assembles a two-sided inverse. 

 --------
 在 [Sets] 中，双射（单射并且在 `≈` 意义下可分拆的满射）是一个同构：所选择的原像组装成一个双边逆元。
*)
Lemma bijective_is_iso {A B : SetoidObject} (h : A ~{Sets}~> B) :
  injective h -> surjective h -> IsIsomorphism h.
Proof.
  intros [i] [lift] ; unshelve econstructor.
  - exists (fun b => `1 (lift b)).
    abstract(intros a b eq; simpl;
    apply i; now rewrite `2 (lift a), `2 (lift b)).
  - abstract(intro x; now rewrite `2 (lift x)).
  - abstract(intro x; apply i; now rewrite `2 (lift (h x))).
Defined.


(*
 In Set the epimorphisms are exactly the surjections (see the Wikipedia and
 nLab pages cited in the file header).  This file used to state the
 biconditional and abandon the proof, so NEITHER direction entered the
 environment -- not even the forward one, whose script was complete but
 stranded inside the abandoned block.  Both directions are proved below, at
 the universe of A and B.

 The abandoned attempt (and the header note that went with it) reached for
 the classical probe: distinguish a point outside the image using the
 characteristic map of the image against a constant map into a truth-value
 object.  THAT probe genuinely does not fit here -- its object has carrier
 [Type] with `≈` taken to be `↔`, and no such object is an [obj[Sets]] at the
 universe of A and B, since Set's subobject classifier lives one level up
 (Instance/Sets/Classifier.v; a one-level instance exists only
 conditionally, in Instance/Sets/Classifier/OneLevel.v).

 But epis-are-surjections does not inherit that obstruction, because the
 truth-value object is not the only available probe.  The COKERNEL PAIR of h
 with itself does the same work and stays at the universe of B: take two
 copies of B glued exactly along the image of h, i.e. `carrier B + carrier B`
 under [ckrel] below.  The predicate [Im b := ∃ a, h a ≈ b] is
 [Type]-valued at the SAME level as the carriers -- `carrier A` is there
 already, and `equiv` on a [SetoidObject@{p p}] is a [crelation] at that
 level -- so nothing ever needs [Type@{p} : Type@{p}].  The two inclusions
 agree after h (each `h a` is in the image, witnessed by `a`), so right
 cancellation identifies them on all of B, and the [Im] component of the
 resulting equivalence at b IS the preimage.

 The argument is constructive: `∃` is [sigT] here (Lib/Foundation.v), so the
 preimage is genuinely extracted rather than merely asserted, and no choice
 principle is used. 

 --------
 在 Set 中，满射恰好是上同态（参见文件头引用的 Wikipedia 和 nLab 页面）。本文件过去曾声明双条件并放弃证明，因此两个方向都未进入环境——甚至连正向也没有，其脚本虽然完整，但被困在被放弃的块内。下面在 A 和 B 的宇宙中证明了两个方向。被放弃的尝试（以及随之而来的标题说明）尝试了经典的探针方法：使用图像的特征映射与一个常量映射到真值对象的映射来区分图像外的一个点。那个探针在这里确实不适用——它的对象的载体是 [Type]，其中 `≈` 被视为 `↔`，而在 A 和 B 的宇宙中，没有这样的对象是 [obj[Sets]，因为 Set 的子对象分类器存在于上一层（Instance/Sets/Classifier.v；一层实例仅在 Instance/Sets/Classifier/OneLevel.v 中有条件存在）。但是 epis-are-surjections 并不继承那个阻碍，因为真值对象并不是唯一可用的探针。h 与自身的余核对也完成相同的工作，并停留在 B 的宇宙中：取两个 B 的副本，沿着 h 的像精确地粘合，即下面的 `carrier B + carrier B` 在 [ckrel] 下。谓词 [Im b := ∃ a, h a ≈ b] 在与承载体相同的层级上是 [Type] 值 -- `carrier A` 已经在那里，并且在 [SetoidObject@{p p}] 上的 `equiv` 是该层级的 [crelation] -- 所以不需要 [Type@{p} : Type@{p}]。h 之后两个包含映射一致（每个 `h a` 都在像中，由 `a` 见证），因此右消去在整个 B 上将它们识别，并且在 b 处生成的等价关系的 [Im] 分量就是原像。这个论证是建设性的：`∃` 在这里是 [sigT]（Lib/Foundation.v），因此前像是实际提取的，而不仅仅是断言的，并且没有使用选择原理。
*)

Section CokernelPair.

Universes h p.
Context {A B : SetoidObject@{p p}}.
Context (f : A ~{Sets@{p h}}~> B).

(* Membership in the image of f, at the level of the carriers. / 在载体层次上的 f 的像的成员资格。 *)
Definition Im (b : carrier B) : Type@{p} := ∃ a : carrier A, f a ≈ b.

Lemma Im_resp (x y : carrier B) : x ≈ y → Im x → Im y.
Proof. intros E [a Ha]; exists a; transitivity x; assumption. Qed.

(* Two copies of B, identified across the copies exactly on the image. / B 的两个副本，在图像上能够在副本之间精确识别。 *)
Definition ckrel (u v : (carrier B + carrier B)%type) : Type@{p} :=
  match u, v with
  | inl x, inl y => x ≈ y
  | inr x, inr y => x ≈ y
  | inl x, inr y => prod (x ≈ y) (Im x)
  | inr x, inl y => prod (x ≈ y) (Im x)
  end.

Lemma ckrel_equiv : Equivalence ckrel.
Proof.
  constructor.
  - intro u; destruct u; simpl; reflexivity.
  - intros u v; destruct u, v; simpl; intro H;
      try (symmetry; assumption);
      destruct H as [E I]; split;
      [ symmetry; assumption | eapply Im_resp; eassumption
      | symmetry; assumption | eapply Im_resp; eassumption ].
  - intros u v w; destruct u, v, w; simpl; intros H1 H2;
      repeat match goal with [ X : prod _ _ |- _ ] => destruct X end;
      try (etransitivity; eassumption);
      split; try (etransitivity; eassumption); try assumption;
      try (eapply Im_resp; [ symmetry; eassumption | assumption ]).
Qed.

Definition CKSetoid : SetoidObject@{p p} :=
  {| carrier := (carrier B + carrier B)%type;
     is_setoid := {| equiv := ckrel; setoid_equiv := ckrel_equiv |} |}.

Definition ck_left : B ~{Sets@{p h}}~> CKSetoid.
Proof.
  refine {| morphism := fun b => inl b |}; repeat intro; simpl; assumption.
Defined.

Definition ck_right : B ~{Sets@{p h}}~> CKSetoid.
Proof.
  refine {| morphism := fun b => inr b |}; repeat intro; simpl; assumption.
Defined.

(* The two inclusions agree after f: every f a lies in the image, by a. / 在 f 之后这两个包含是一致的：每个 f a 都位于像中，由 a 给出。 *)
Lemma ck_agree : ck_left ∘[Sets@{p h}] f ≈ ck_right ∘[Sets@{p h}] f.
Proof.
  intro a; simpl; split; [ reflexivity | exists a; reflexivity ].
Qed.

End CokernelPair.

(* Mac Lane, CWM 2nd ed., §I.5, printed p. 19: in Set the epis are exactly the surjections. Both directions, at one universe. / Mac Lane, CWM 第二版，§I.5，印刷第 19 页：在 Set 中，正满射正好是满射。两条方向，都在一个宇宙中。 *)
Lemma surjectivity_is_epic@{h p} {A B : SetoidObject@{p p}}
  (h : A ~{Sets}~> B) :
  (∀ b, ∃ a, h a ≈ b)%type ↔ Epic@{h p} h.
Proof.
  split.
  - intros HA.
    constructor.
    autounfold in *; intros ??? HB.
    simpl in *; intros.
    specialize (HA x).
    destruct HA as [? HA].
    rewrite <- HA.
    apply HB.
  - intros E b.
    exact (snd (@epic _ _ _ _ E (CKSetoid h)
                  (ck_left h) (ck_right h) (ck_agree h) b)).
Defined.

(* The two halves under their own names, for callers that want just one. / 两个半部分以它们自己的名字出售，供只想要其中一部分的呼叫者使用。 *)
Definition surjective_implies_epic@{h p} {A B : SetoidObject@{p p}}
  (h : A ~{Sets}~> B) : (∀ b, ∃ a, h a ≈ b)%type → Epic@{h p} h :=
  fst (surjectivity_is_epic@{h p} h).

Definition epic_implies_surjective@{h p} {A B : SetoidObject@{p p}}
  (h : A ~{Sets}~> B) : Epic@{h p} h → (∀ b, ∃ a, h a ≈ b)%type :=
  snd (surjectivity_is_epic@{h p} h).

(*
 Sets is balanced: a map that is both monic and epic is an isomorphism.
 Monicity gives injectivity ([injectivity_is_monic]), epicness gives the
 preimages, and [bijective_is_iso] assembles a two-sided inverse -- with no
 appeal to choice, the preimages having been data all along. 

 --------
 集合是平衡的：一个既是单射又是满射的映射就是一个同构。
 单射性保证了注入性（[injectivity_is_monic]），满射性提供了原像，而[bijective_is_iso]组装了一个双侧逆——无需依赖选择原理，原像一直都是已知的数据。
*)
Definition Sets_balanced@{h p} {A B : SetoidObject@{p p}}
  (h : A ~{Sets@{p h}}~> B)
  (Hm : @Monic Sets@{p h} A B h) (He : @Epic@{h p} Sets@{p h} A B h) :
  @IsIsomorphism Sets@{p h} A B h :=
  bijective_is_iso h
    {| inj := λ x y, snd (injectivity_is_monic h) Hm x y |}
    {| surj := λ b, epic_implies_surjective@{h p} h He b |}.

(* ------------------------------------------------------------------------ *)
(* * ** The cancellation lemmas do not cancel the other factor / * ** 约简引理不会约掉其他因子 *)

(*
 Mac Lane, CWM 2nd ed., §I.5 Exercise 1 asks about BOTH factors, and
 Awodey §2.9 Exercise 2(d) asks for the counterexample outright.
 [monic_cancel] and [epic_cancel] (Theory/Morphisms.v) each cancel one
 factor; nothing follows about the other, and a single pair of setoid maps
 refutes both converses at once.

 Take the two-element setoid [bool_setoid_object], the map [pick_true] out
 of the singleton, and the map [collapse] back onto it.  Their composite is
 the identity of the singleton, hence monic and epic; but [collapse] is not
 monic (it identifies the two booleans) and [pick_true] is not epic (it
 misses [false]). 

 --------
 Mac Lane, CWM 第二版, §I.5 练习 1 问的是两个因子，而 Awodey §2.9 练习 2(d) 直接要求反例。[monic_cancel] 和 [epic_cancel]（Theory/Morphisms.v）各自消去一个因子；对另一个没有任何结论，而且一对集合等价映射就可以一次性反驳两者的逆命题。

 取二元集合等价 [bool_setoid_object]，从单元素集合到它的映射 [pick_true]，以及映射回单元素集合的 [collapse]。它们的复合是单元素集合的恒等映射，因此既是单射也是满射；但是 [collapse] 不是单射（它把两个布尔值认作相同），而 [pick_true] 不是满射（它漏掉了 [false]）。
*)

Definition bool_setoid_object@{t u} : SetoidObject@{t u} :=
  {| carrier   := bool
   ; is_setoid := {| equiv := eq ; setoid_equiv := eq_equivalence |} |}.

Program Definition pick_true : unit_setoid_object ~{Sets}~> bool_setoid_object :=
  {| morphism := fun _ => true |}.

Program Definition collapse : bool_setoid_object ~{Sets}~> unit_setoid_object :=
  {| morphism := fun _ => ttt |}.

Program Definition pick_false : unit_setoid_object ~{Sets}~> bool_setoid_object :=
  {| morphism := fun _ => false |}.

(* The composite is the identity on the singleton, up to `≈`. / 复合映射在单元素集上是恒等映射，直到 `≈` 。 *)
Lemma collapse_pick : collapse ∘[Sets] pick_true ≈ id{Sets}.
Proof. intro u; now destruct u. Qed.

(* Hence it is both monic and epic: everything into or out of the singleton is forced, the singleton being terminal. / 因此它既是幺模的也是史诗性的：进入或退出单元素的所有操作都是被迫的，因为单元素是终端的。 *)
Lemma collapse_pick_monic : Monic (collapse ∘[Sets] pick_true).
Proof. constructor; intros z g1 g2 _ u; now destruct (g1 u), (g2 u). Qed.

Lemma collapse_pick_epic : Epic (collapse ∘[Sets] pick_true).
Proof. constructor; intros z g1 g2 H u; destruct u; apply (H ttt). Qed.

(* ... while the OTHER factor need not be, in either case. [collapse] identifies the two booleans, so it is not monic: probe it with [pick_true] against [pick_false], which it cannot tell apart. / ...而另一个因素在任何情况下都不必如此。[collapse] 识别这两个布尔值，所以它不是单项的：用 [pick_true] 对 [pick_false] 进行探测，它无法区分它们。 *)
Lemma collapse_not_monic : Monic collapse → False.
Proof.
  intro M.
  assert (E : collapse ∘[Sets] pick_true ≈ collapse ∘[Sets] pick_false)
    by (intro u; now destruct u).
  exact (Bool.diff_true_false
           (@monic Sets _ _ collapse M unit_setoid_object
              pick_true pick_false E ttt)).
Qed.

(*
 And [pick_true] misses [false], so it is not epic: probe it with the
 identity against the constantly-true map, which agree on [true] alone. 

 --------
 而 [pick_true] 想念 [false]，所以它不是史诗：用恒真的映射的恒等映射探测它，只在 [true] 上一致。
*)
Lemma pick_true_not_epic : Epic pick_true → False.
Proof.
  intro E.
  assert (H : id{Sets} ∘[Sets] pick_true
                ≈ (pick_true ∘[Sets] collapse) ∘[Sets] pick_true)
    by (intro u; now destruct u).
  exact (Bool.diff_false_true
           (@epic Sets _ _ pick_true E bool_setoid_object
              id{Sets} (pick_true ∘[Sets] collapse) H false)).
Qed.

(* The two asymmetries, packaged under the names Theory/Morphisms.v cites. / 这两个不对称性，以 Theory/Morphisms.v 引用的名称打包。 *)
Definition sets_epic_left_factor_only :
  Epic (collapse ∘[Sets] pick_true) * (Epic pick_true → False) :=
  (collapse_pick_epic, pick_true_not_epic).

Definition sets_monic_right_factor_only :
  Monic (collapse ∘[Sets] pick_true) * (Monic collapse → False) :=
  (collapse_pick_monic, collapse_not_monic).

