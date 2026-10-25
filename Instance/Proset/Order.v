Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Thin.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Poset.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.

Generalizable All Variables.

(*
   * * Preorders as thin categories: the round trip, order reversal, total
   orders, and infima as limits 

   --------
   * * 作为稀疏范畴的前序：往返、顺序反转、全序，以及作为极限的下确界
*)

(*
 Book: Mac Lane, "Categories for the Working Mathematician",
 Springer GTM 5, 2nd ed. 1998, §I.2 (construction 7, definition 4)
 Book: Riehl, "Category Theory in Context", Dover 2016, §1.2
 Book: Fong and Spivak, "Seven Sketches in Compositionality",
 CUP 2019, §§1.2.2 and 1.3.1
 nLab: https://ncatlab.org/nlab/show/thin+category
 nLab: https://ncatlab.org/nlab/show/preorder
 nLab: https://ncatlab.org/nlab/show/total+order

 Instance/Proset.v builds the thin category of a preorder; this file
 closes the circle and works out the order theory the correspondence buys.

 MAC LANE §I.2 AND ITS ROUND TRIP.  That section lists among its examples
 of categories the one attached to a preordered set: objects the elements,
 one arrow x → y for each instance of x ≤ y.  (The internal numbering used
 in the citation above — construction 7, definition 4 — is as given by the
 issue this file answers, and has not been checked against the book here;
 the section reference is the reliable part.)  Read in reverse,
 a category determines a preorder on its objects — "x ≤ y when there is an
 arrow x ~> y" — and the two passages are meant to be mutually inverse on
 thin categories.  Both legs are proved below, and both are MEASURED rather
 than asserted:

 - [hom_preorder_Proset] recovers R from [Proset P] up to pointwise
 logical equivalence, not up to equality of relations.  The gap is
 exactly Coq's Prop/Type divide: Structure/Thin.v's [thin_preorder]
 squashes the hom into [inhabited], and [inhabited (R x y)] is not the
 same term as [R x y].  [hom_preorder_Proset_eq] then shows that
 propositional and functional extensionality — taken as explicit
 hypotheses, so that no axiom enters the development — close the gap
 to an honest equality.

 - [thin_Proset_iso] gives the other leg as an isomorphism in [Cat].
 Instance/Cat.v discloses that its [Functor_Setoid] identifies
 functors up to natural isomorphism, so an isomorphism there is only an
 EQUIVALENCE of categories.  More than that is proved, and recorded
 separately so the extra strength is checkable rather than asserted:
 [thin_Proset_iso_obj] shows both functors are the identity on objects
 definitionally, and [thin_Proset_roundtrip_hom] with
 [Proset_thin_roundtrip_hom] show their morphism actions invert each
 other up to `≈`.  That is an identity-on-objects isomorphism in the
 setoid sense the library uses everywhere.  It is NOT an equality of
 functors, and it is weaker than the [eq_refl]-level inverse pair the
 order-reversal isomorphism below achieves.

 - The backward functor needs [HomChoice] — an arrow produced from the
 bare fact that one exists.  It is taken as an explicit hypothesis
 (Structure/Thin.v), and it costs nothing where it is actually wanted:
 [proset_HomChoice] discharges it for every [Proset], whose homs are
 already Props, so [Proset_roundtrip] is hypothesis-free.  Separately,
 [hom_Proset_Faithful_iff_Thin] pins the role of thinness exactly: the
 forward functor is faithful precisely when the category is thin.

 ORDER REVERSAL (Riehl §1.2).  The opposite of the thin category of P is
 the thin category of the reversed order.  Here the two categories have
 CONVERTIBLE objects and homs, so [Proset_op_iso] is an isomorphism whose
 two morphism actions are mutually inverse by [eq_refl] — see
 [Proset_op_roundtrip] and [Proset_op_hom].  This is much stronger than the
 equivalence that `≅[Cat]` records, and stronger than the round trip above.
 The reversed preorder is stdlib's [Basics.flip] with stdlib's
 [flip_PreOrder] instance; nothing needed constructing.

 SEVEN SKETCHES §1.2.2.  Four items from that section are settled here.
 The axiom comparison — every [Equivalence] is a [PreOrder], and a
 symmetric [PreOrder] is an [Equivalence] — is [Equivalence_is_PreOrder]
 and [PreOrder_Symmetric_is_Equivalence].  The first direction already
 exists in stdlib as [Equivalence_PreOrder] and is re-derived here only so
 that both halves stand side by side over one carrier and one relation; for
 the second, a [Search] over the modules this file loads returns no stdlib
 lemma of that shape.  The discrete and codiscrete preorders on
 an arbitrary carrier are [discrete_rel] and [codiscrete_rel], with
 [codiscrete_terminal] and [discrete_initial] locating them as the top and
 the bottom of the preorder structures on a fixed carrier under refinement
 (the identity map being monotone), each characterized uniquely up to
 mutual refinement.  Comparability is [comparable], distinguished from
 decidability by three theorems rather than by a remark.  And a total order
 is a preorder in which every two elements are comparable
 ([TotalOrder_iff_all_comparable]).

 SEVEN SKETCHES §1.3.1.  Infimum and supremum are introduced under their
 order-theoretic names and identified with the limit and the colimit of the
 two-object discrete diagram: [infimum_iff_limit] and
 [supremum_iff_colimit], stated over Structure/Limit.v's [IsALimit] and
 Instance/Discrete.v's [DiscreteCat] on [bool].  Instance/Poset.v
 announces the dictionary entry as prose ("a product is a meet, and more
 generally the limit over a subset is its greatest lower bound"); these two
 theorems prove it at the two-object shape, for an ARBITRARY preorder.  The
 tree does already contain one instance of the identification — the
 cartesian structure on the walking arrow, whose product object is
 Instance/Two/Monoidal.v's [two_meet] fed to [Two_Cartesian] —
 but that is a single fixed two-element order presented as a [Cartesian]
 instance rather than as a limit over a discrete diagram.

 SCOPE NOTE on the general identification lemma.  The library contains no
 thin-category-wide "a limit is a meet" lemma: a case-insensitive search of
 every .v file for [infimum], [supremum], "greatest lower" and "least
 upper" returns exactly one hit, the prose comment at Instance/Poset.v.
 The general identification lemma belongs to issue #422 (MacLane V.2:
 products in a preorder are greatest lower bounds), whose suggested module
 is Instance/Proset/Limit.v -- this same directory.  The two theorems below
 ARE that dictionary at binary discrete shape, proved here because this
 issue's checkbox needs them; whoever takes #422 should consume and
 generalize them rather than restate them (issue #737, the poset adjoint
 functor theorem, consumes #422's lemma and explicitly forbids a second
 copy).  #223's own checkbox text attributed the lemma to #737; that
 attribution was wrong at the source.  The two theorems are accordingly
 proved DIRECTLY, at the two-object discrete shape, over an arbitrary
 preorder (totality is not needed for the identification — only for
 existence, which is [TotalOrder_meet] and [TotalOrder_join]).  When the
 general lemma lands, these become its specialization; until then they
 stand on their own and depend on nothing that does not exist.

 WHAT IS NOT CLAIMED.  The correspondence proved here is between preorders
 and thin categories one object-set at a time.  It is not lifted to an
 equivalence between a category of preorders and a category of thin
 categories, and no adjunction between [Proset] and [thin_preorder] is
 stated.  The morphism leg of the correspondence already exists in another
 guise: Construction/Enriched/Two.v identifies enriched functors
 between preorders enriched in the walking arrow with monotone maps. 

 --------
 书籍：Mac Lane，《工作数学家的范畴论分类》，Springer GTM 5，第2版 1998年，第I.2节（构造7，定义4）
 书籍：Riehl，《情境中的范畴论》，Dover 2016，第1.2节
 书籍：Fong 和 Spivak，《组合性的七个草图》，CUP 2019，第1.2.2节和第1.3.1节
 nLab：https://ncatlab.org/nlab/show/thin+category
 nLab：https://ncatlab.org/nlab/show/preorder
 nLab：https://ncatlab.org/nlab/show/total+order

 Instance/Proset.v 构建了一个前序集合的稀疏范畴；该文件闭合了这个循环，并推导了该对应关系带来的序理论。MAC LANE §I.2 及其循环往返。该部分在其类别例子中列出了附属于预序集合的那一类：对象是元素，每一对 x ≤ y 的实例有一条箭头 x → y。（上面引用中使用的内部编号——构造 7，定义 4——由该文件所回答的问题给出，尚未与书本核对；章节引用是可靠的部分。）反向阅读时，一个类别会在其对象上确定一个预序——“当存在箭头 x ~> y 时，x ≤ y”——这两段话在薄类别上被认为是互为逆的。下面证明了两条腿，且两者是经过衡量的，而非断言的。- [hom_preorder_Proset] 从 [Proset P] 中恢复 R，直到逐点逻辑等价，而不是关系的相等。这个差距正是 Coq 的 Prop/Type 分界：Structure/Thin.v 的 [thin_preorder] 将同态压缩到 [inhabited]，而 [inhabited (R x y)] 并不是 [R x y] 相同的项。然后 [hom_preorder_Proset_eq] 表明，命题外延性和函数外延性——作为显式假设引入，因此在发展中没有引入公理——弥补了差距，实现了真正的相等。- [thin_Proset_iso] 给出了在 [Cat] 中的另一条腿作为同构。  
 Instance/Cat.v 揭示其 [Functor_Setoid] 将函子识别为自然同构，因此其中的同构仅是范畴的一个等价。  
 除此之外，还证明了更多内容，并单独记录，以便额外的强度可以被检验而不是仅仅被声明：  
 [thin_Proset_iso_obj] 显示两个函子在对象上定义性地都是恒等的，[thin_Proset_roundtrip_hom] 和 [Proset_thin_roundtrip_hom] 显示它们的态射作用在 `≈` 范围内互相逆转。  
 这是在库中随处使用的集合体意义上的对象恒等同构。  
 它不是函子的等式，也比下面顺序反转同构达到的 [eq_refl] 级别逆元对要弱。- 后向函子需要 [HomChoice] —— 一个由某个存在的裸事实产生的箭头。它被作为一个显式假设（Structure/Thin.v），并且在真正需要的地方不产生任何代价：[proset_HomChoice] 为每个 [Proset] 解除它，其同态已经是命题，所以 [Proset_roundtrip] 是无假设的。另一个方面，[hom_Proset_Faithful_iff_Thin] 精确地确定了稀薄性的角色：前向函子当且仅当类别是稀薄的时才是忠实的。订单逆转（Riehl §1.2）。P 的薄范畴的对立面是逆序的薄范畴。在这里，这两个范畴具有可转换的对象和态射，因此 [Proset_op_iso] 是一个同构，其两个态射作用通过 [eq_refl] 互为逆——见 [Proset_op_roundtrip] 和 [Proset_op_hom]。这比 `≅ [Cat]ZZ ` 记录的等价强得多，也比上述往返更强。逆序的预序是 stdlib 的 [Basics.flip]，并且使用 stdlib 的 [flip_PreOrder] 实例；构造时不需要额外操作。七个草图 §1.2.2。本节的四个项目在此得到解决。公理比较——每个 [Equivalence] 都是一个 [PreOrder]，对称的 [PreOrder] 是 [Equivalence]——是 [Equivalence_is_PreOrder] 和 [PreOrder_Symmetric_is_Equivalence]。第一个方向已经存在于 stdlib 中作为 [Equivalence_PreOrder]，这里重新推导仅是为了使两个部分在一个载体和一个关系上并列；对于第二个方向，一个 [Search] 在本文件加载的模块上返回没有这种形状的 stdlib 引理。在任意载体上的离散和共离散预序是 [discrete_rel] 和 [codiscrete_rel]，[codiscrete_terminal] 和 [discrete_initial] 将它们定位为固定载体下在精炼过程中预序结构的顶部和底部（恒等映射是单调的），每个都唯一地由相互精炼特征化。可比性是 [comparable]，由三个定理而非一个备注将其与可判定性区分开来。全序是一种预序，其中每两个元素都是可比的（[TotalOrder_iff_all_comparable]）。七个素描 §1.3.1. 下确界和上确界以它们的序理论名称引入，并且与两个对象离散图的极限和余极限相对应：[infimum_iff_limit] 和 [supremum_iff_colimit]，声明于 Structure/Limit.v 的 [IsALimit] 和 Instance/Discrete.v 的 [DiscreteCat] 上 [bool]。Instance/Poset.v 以散文形式宣布词典条目（“积是交，更一般地，一个子集上的极限是它的最大下界”）；这两个定理在两个对象的形状下证明了它，对于任意的偏序关系都是成立的。该树已经包含了一个标识的实例——步行箭头上的笛卡尔结构，其积对象是 Instance/Two/Monoidal.v 的 [two_meet]，输入到 [Two_Cartesian]——但那只是一个固定的双元素顺序，作为 [Cartesian] 实例呈现，而不是作为离散图上的极限。关于一般识别引理的范围说明。库中没有薄范畴范围内的“极限是上确界”引理：对每个 .v 文件进行不区分大小写的搜索 [infimum]、[supremum]、“greatest lower”和“least upper”恰好返回一个结果，即 Instance/Poset.v 中的文字注释。一般识别引理属于问题 #422（MacLane V.2：前序下的乘积是下确界），建议的模块是 Instance/Proset/Limit.v——即同一目录。下面的两个定理确实是在二元离散形下的该字典，在这里证明是因为这个问题的复选框需要它们；负责 #422 的人应该使用并推广它们，而不是重新陈述（问题 #737，即偏序伴随函子定理，使用了 #422 的引理并明确禁止第二份复制）。#223自己勾选框中的文字将引理归因于#737；这一归因在源头上是错误的。因此，这两个定理是在任意预序（识别不需要全序——只需要存在性，即[TotalOrder_meet]和[TotalOrder_join]）下，直接在双对象离散图形上证明的。当一般引理出现时，这些定理就成为它的特例；在那之前，它们独立存在，并不依赖任何不存在的东西。未声明的内容。这里证明的对应关系是在每次处理一个对象集时的预序与稀疏范畴之间。它并没有提升到预序范畴与稀疏范畴之间的等价，也没有说明  [Proset]  与  [thin_preorder]  之间的伴随关系。对应关系中的态射部分已经以另一种形式存在：Construction/Enriched/Two.v 将在步进箭头中富集的预序之间的富集函子识别为单调映射。
*)

(* * ** Thinness of prosets and posets / * ** 伪序集和偏序集的稀疏性 *)

(*
 Instance/Proset.v declares the hom-setoid equivalence of a proset to be
 [True], so thinness holds by the unit constructor.  This is the bridge
 between Instance/Proset.v's construction and Structure/Thin.v's predicate,
 in the same relation as Instance/Discrete.v's [DiscreteCat_Discrete] to
 Structure/Discrete.v. 

 --------
 Instance/Proset.v 声明了一个 proset 的同态集合等价为 [True]，因此薄性由单位构造器成立。这是 Instance/Proset.v 的构造与 Structure/Thin.v 的谓词之间的桥梁，与 Instance/Discrete.v 的 [DiscreteCat_Discrete] 与 Structure/Discrete.v 的关系相同。
*)
Lemma proset_thin {A : Type} {R : relation A} (P : PreOrder R) :
  Thin (Proset P).
Proof. intros x y f g; exact I. Qed.

(*
 A poset is a proset with antisymmetry imposed, and Instance/Poset.v
 defines it as literally [Proset P], so the thin category is the same
 object; antisymmetry constrains the OBJECTS (making the category skeletal,
 Instance/Poset.v), not the homs. 

 --------
 偏序集是施加了反对称性的前序集，而 Instance/Poset.v 将其字面上定义为 [Proset P]，所以薄范畴是相同的对象；反对称性约束的是对象（使范畴成为骨架范畴，Instance/Poset.v），而不是态射。
*)
Lemma Poset_is_Proset {A : Type} {R : relation A} (P : PreOrder R)
      (H : @Antisymmetric A eq eq_equiv R) :
  @Poset A R P H = Proset P.
Proof. reflexivity. Qed.

Lemma poset_thin {A : Type} {R : relation A} (P : PreOrder R)
      (H : @Antisymmetric A eq eq_equiv R) :
  Thin (@Poset A R P H).
Proof. exact (proset_thin P). Qed.

(*
 Antisymmetry is exactly skeletality of the thin category: mutually related
 objects are isomorphic by [thin_iso], and antisymmetry forces them equal. 

 --------
 反对称性恰恰是薄范畴的骨架性：相互关联的对象通过 [thin_iso] 同构，反对称性强制它们相等。
*)
Lemma poset_skeletal {A : Type} {R : relation A} (P : PreOrder R)
      (H : @Antisymmetric A eq eq_equiv R) (x y : A) :
  x ≅[@Poset A R P H] y → x = y.
Proof. intro i; exact (H x y (to i) (from i)). Qed.

(* * ** Round trip, leg one: the preorder of the thin category of P is P / * ** 往返行程，第一程：P 的薄范畴的预排序是 P *)

(*
 Recovery up to pointwise logical equivalence.  Note this is [iffT] (the
 library rebinds `↔`, Lib/Foundation.v), so the two directions carry
 computational content: forward eliminates the [inhabited] witness (legal,
 since the goal [R x y] is itself a Prop), backward is [inhabits]. 

 --------
 恢复到逐点逻辑等价。注意这是 [iffT]（库重新绑定了 `↔`，Lib/Foundation.v），因此两个方向都携带计算内容：向前消除了 [inhabited] 的证据（合法，因为目标 [R x y] 本身是一个 Prop），向后是 [inhabits]。
*)
Theorem hom_preorder_Proset {A : Type} {R : relation A} (P : PreOrder R)
        (x y : A) :
  thin_preorder (Proset P) x y ↔ R x y.
Proof.
  split.
  - intro H; destruct H as [r]; exact r.
  - exact (fun r => inhabits r).
Qed.

(*
 Measuring the gap.  The recovery above is NOT an equality of relations:
 [thin_preorder (Proset P)] is the relation [fun x y => inhabited (R x y)],
 a different term from [R].  Under propositional and functional
 extensionality it becomes one, and both are taken here as explicit
 hypotheses of the lemma — nothing is assumed globally, and
 [Print Assumptions] on this constant stays clean. 

 --------
 测量差距。上述恢复并不是关系的等式：
 [thin_preorder (Proset P)] 是关系 [fun x y => inhabited (R x y)]，
 与 [R] 不同。在命题和函数外延性下，它们变为相同，这里两者都被作为该引理的明确假设——没有做全局假设，并且 [Print Assumptions] 在这个常量上保持干净。
*)
Theorem hom_preorder_Proset_eq {A : Type} {R : relation A} (P : PreOrder R)
        (prop_ext : ∀ p q : Prop, (p <-> q) → p = q)
        (fun_ext : ∀ f g : A → A → Prop, (∀ x y : A, f x y = g x y) → f = g) :
  thin_preorder (Proset P) = R.
Proof.
  apply fun_ext; intros x y.
  apply prop_ext; split.
  - intro H; destruct H as [r]; exact r.
  - exact (fun r => inhabits r).
Qed.

(* * ** Round trip, leg two: the thin category of the hom-preorder / * ** 往返行程，第二段：同序预排序的薄类别 *)

(*
 The comparison functor, defined for an ARBITRARY category: identity on
 objects, sending an arrow to the fact that it exists.  Every obligation is
 an equation in the target hom-setoid, which Instance/Proset.v declares
 to be [True]. 

 --------
 用于任意范畴的比较函子：在对象上是恒等的，将一个箭头映射到它存在的事实。每个义务都是目标同态集中的一个方程，Instance/Proset.v 声明它为 [True]。
*)
Program Definition thin_to_Proset_Functor (C : Category) :
  C ⟶ Proset (thin_PreOrder C) := {|
  fobj := fun x => x;
  fmap := fun x y f => inhabits f
|}.

(*
 Thinness is exactly the faithfulness of that comparison.  Forward: the
 hypothesis of [fmap_inj] is an equation in the trivial setoid, so it is
 free, and its conclusion is thinness.  Backward: immediate. 

 --------
 瘦弱正是那个比较的忠实性。前向：[fmap_inj] 的假设是在平凡集合同构中的一个等式，所以它是自由的，其结论是瘦弱。后向：立即。
*)
Theorem hom_Proset_Faithful_iff_Thin (C : Category) :
  Faithful (thin_to_Proset_Functor C) ↔ Thin C.
Proof.
  split.
  - intros F x y f g.
    destruct F as [inj].
    exact (inj x y f g I).
  - intro T.
    constructor; intros x y f g _; apply T.
Qed.

(*
 On a proset the choice hypothesis of Structure/Thin.v is discharged: the
 homs of [Proset P] are the Props [R x y], so eliminating [inhabited] lands
 back in Prop and is permitted. 

 --------
 在一个命题上，Structure/Thin.v 的选择假设被解除：[Proset P] 的同态是命题 [R x y]，因此消去 [inhabited] 会回到命题中，这是允许的。
*)
Definition proset_HomChoice {A : Type} {R : relation A} (P : PreOrder R) :
  HomChoice (Proset P) :=
  fun x y h => match h return R x y with inhabits r => r end.

(*
 The backward comparison functor, for a thin C with a choice of arrows.
 [fmap_respects] holds because any two chosen arrows are parallel, and the
 two functor laws because their two sides are parallel; all three are
 [Thin C]. 

 --------
 对于具有箭头选择的瘦 C，向后的比较函子。[fmap_respects] 成立，因为任意两个选定的箭头是平行的，并且两个函子律成立，因为它们的两边是平行的；三者都是 [Thin C]。
*)
Program Definition Proset_hom_Functor {C : Category}
        (T : Thin C) (ch : HomChoice C) :
  Proset (thin_PreOrder C) ⟶ C := {|
  fobj := fun x => x;
  fmap := fun x y h => ch x y h
|}.

(*
 The isomorphism in [Cat].  Both composites are the identity on objects, and
 every `≈` involved is an equation between parallel arrows of a thin
 category, so the natural-isomorphism data [Functor_Setoid]
 (Theory/Functor.v) asks for is discharged by the [cat_simpl] obligation
 tactic. 

 --------
 [Cat] 中的同构。两个复合都是对象上的恒等映射，并且每个涉及的 `≈` 都是在薄范畴中平行箭头之间的方程，因此自然同构数据 [Functor_Setoid]（Theory/Functor.v）所要求的内容可由 [cat_simpl] 义务策略来完成。
*)
Program Definition thin_Proset_iso {C : Category}
        (T : Thin C) (ch : HomChoice C) :
  C ≅[Cat] Proset (thin_PreOrder C) := {|
  to   := thin_to_Proset_Functor C;
  from := Proset_hom_Functor T ch
|}.

(*
   * *** Measuring the strength of that isomorphism

   Instance/Cat.v records that `≅[Cat]` means equivalence of
   categories, because [Functor_Setoid] compares functors up to natural
   isomorphism.  The first two facts below say more: the comparison is the
   identity on objects on the nose, and the C-side morphism round trip holds
   up to `≈` with real content (it is discharged by thinness of C).  The
   third is recorded for symmetry only and is VACUOUS: the Proset-side
   hom-setoid is Instance/Proset.v's constantly-[True] relation, so ANY
   two parallel morphisms there are `≈`, and the lemma would hold with both
   functors replaced by arbitrary maps. 

   --------
   * *** 测量该同构的强度

   Instance/Cat.v 记录了 `≅ [Cat]ZZ ` 意味着范畴等价，因为 [Functor_Setoid] 比较函子时采用自然同构。下面的前两个事实说明更多：比较在对象上严格等于恒等，并且 C 侧的态射往返仍然在 `≈` 下成立，并且具有实际内容（它通过 C 的稀薄性质解决）。第三个仅为对称性而记录且是空洞的：Proset 侧的态射集合是 Instance/Proset.v 的恒定 [True] 关系，所以那里任何两条平行态射都是 `≈`，并且引理在将两个函子都替换为任意映射时仍然成立。
*)

Lemma thin_Proset_iso_obj {C : Category} (T : Thin C) (ch : HomChoice C)
      (x : C) :
  (fobj[thin_to_Proset_Functor C] x = x) ∧
  (fobj[Proset_hom_Functor T ch] x = x).
Proof. split; reflexivity. Qed.

Lemma thin_Proset_roundtrip_hom {C : Category} (T : Thin C) (ch : HomChoice C)
      {x y : C} (f : x ~> y) :
  fmap[Proset_hom_Functor T ch] (fmap[thin_to_Proset_Functor C] f) ≈ f.
Proof. apply T. Qed.

(* Vacuous, per the note above -- kept only so both directions are named. / 空洞的，如上面的注释所示——保留仅仅是为了两种方向都有名称。 *)
Lemma Proset_thin_roundtrip_hom {C : Category} (T : Thin C) (ch : HomChoice C)
      {x y : C} (h : x ~{Proset (thin_PreOrder C)}~> y) :
  fmap[thin_to_Proset_Functor C] (fmap[Proset_hom_Functor T ch] h) ≈ h.
Proof. exact I. Qed.

(*
 The hypothesis-free corollary: a proset is recovered from its own
 hom-preorder, with [proset_HomChoice] supplying the only hypothesis and
 [proset_thin] the other. 

 --------
 无假设的推论：一个前置集合（proset）可以从它自身的同态预序（hom-preorder）中恢复，其中 [proset_HomChoice] 提供唯一的假设，[proset_thin] 提供另一个。
*)
Definition Proset_roundtrip {A : Type} {R : relation A} (P : PreOrder R) :
  Proset P ≅[Cat] Proset (thin_PreOrder (Proset P)) :=
  thin_Proset_iso (proset_thin P) (proset_HomChoice P).

(* * ** Order reversal: the opposite of a thin category (Riehl §1.2) / * ** 顺序反转：薄范畴的对立面（Riehl §1.2） *)

(*
 The reversed preorder is stdlib's [Basics.flip] with stdlib's
 [flip_PreOrder]; both already exist, so nothing is defined here.  The two
 categories below have convertible objects and convertible homs — the first
 because Construction/Opposite.v keeps [obj] and the second because it
 sets hom[C^op] x y := hom[C] y x, which for a proset is [R y x], which is
 [Basics.flip R x y] by delta. 

 --------
 反向先序是 stdlib 的 [Basics.flip] 与 stdlib 的 [flip_PreOrder]；两者都已存在，因此这里没有定义任何内容。下面的两个范畴具有可转换对象和可转换同态——第一个是因为 Construction/Opposite.v 保留了 [obj]，第二个是因为它设置同态 [C^op] x y := hom [C] y x，对于一个前序集合，这是 [R y x]，由 delta 得到 [Basics.flip R x y]。
*)

Lemma Proset_op_obj {A : Type} {R : relation A} (P : PreOrder R) :
  obj[(Proset P)^op] = obj[Proset (flip_PreOrder P)].
Proof. reflexivity. Qed.

Lemma Proset_op_hom {A : Type} {R : relation A} (P : PreOrder R) (x y : A) :
  (x ~{(Proset P)^op}~> y) = (x ~{Proset (flip_PreOrder P)}~> y).
Proof. reflexivity. Qed.

Program Definition Proset_op_to {A : Type} {R : relation A} (P : PreOrder R) :
  (Proset P)^op ⟶ Proset (flip_PreOrder P) := {|
  fobj := fun x => x;
  fmap := fun x y f => f
|}.

Program Definition Proset_op_from {A : Type} {R : relation A}
        (P : PreOrder R) :
  Proset (flip_PreOrder P) ⟶ (Proset P)^op := {|
  fobj := fun x => x;
  fmap := fun x y f => f
|}.

(*
 Both round trips on morphisms hold by [eq_refl] — not merely up to `≈`.
 Together with the identity object maps that makes [Proset_op_iso] below an
 isomorphism of categories in the textbook sense (a bijection on objects and
 on each hom), rather than only the equivalence that `≅[Cat]` on its own
 records (Instance/Cat.v).  What is NOT claimed is equality of the
 composite functors with [Id]: their [fobj] and [fmap] agree with [Id]'s by
 [eq_refl], but their law fields are the opaque obligation constants
 [Program] generated, which are not [eq_refl]-equal to [Id]'s. 

 --------
 在态射上的双程旅行由 [eq_refl] 成立——不仅仅是到 `≈` 为止。 结合使得下方的 [Proset_op_iso] 成为教材意义上的范畴同构（在对象上和每个 Hom 上都是双射）的恒等对象映射，而不仅仅是 `≅ [Cat]ZZ ` 单独记录的等价（Instance/Cat.v）。 未被声称的是复合函子与 [Id] 的相等性：它们的 [fobj] 和 [fmap] 根据 [eq_refl] 与 [Id] 一致，但它们的律域是生成的不可见义务常数 [Program]，这些常数与 [Id] 的 [eq_refl] 不相等。
*)

Lemma Proset_op_roundtrip {A : Type} {R : relation A} (P : PreOrder R)
      (x y : A) (f : x ~{(Proset P)^op}~> y) :
  fmap[Proset_op_from P] (fmap[Proset_op_to P] f) = f.
Proof. reflexivity. Qed.

Lemma Proset_op_roundtrip' {A : Type} {R : relation A} (P : PreOrder R)
      (x y : A) (f : x ~{Proset (flip_PreOrder P)}~> y) :
  fmap[Proset_op_to P] (fmap[Proset_op_from P] f) = f.
Proof. reflexivity. Qed.

Program Definition Proset_op_iso {A : Type} {R : relation A}
        (P : PreOrder R) :
  ((Proset P)^op)%category ≅[Cat] Proset (flip_PreOrder P) := {|
  to   := Proset_op_to P;
  from := Proset_op_from P
|}.

(* * ** Preorders versus equivalence relations (Seven Sketches §1.2.2) / * ** 预序与等价关系（七个概述 §1.2.2） *)

(*
 Dropping symmetry from an equivalence relation leaves a preorder; adding
 it back to a preorder restores an equivalence relation.  The first
 direction duplicates stdlib's [Equivalence_PreOrder]; it is restated so
 that the pair reads as one comparison over a fixed carrier and relation.
 For the second, [Search Symmetric PreOrder Equivalence] over the modules
 this file loads returns nothing from stdlib. 

 --------
 从等价关系中去掉对称性会得到一个预序；将它重新加回到预序中会恢复一个等价关系。第一个方向重复了标准库的 [Equivalence_PreOrder]；它被重新表述，以便该对可以作为固定载体和关系上的一次比较来阅读。对于第二个方向，该文件加载的模块上的 [Search Symmetric PreOrder Equivalence] 从标准库中不返回任何内容。
*)

Lemma Equivalence_is_PreOrder {A : Type} (R : relation A) :
  Equivalence R → PreOrder R.
Proof.
  intro E; constructor.
  - exact (@Equivalence_Reflexive A R E).
  - exact (@Equivalence_Transitive A R E).
Qed.

Lemma PreOrder_Symmetric_is_Equivalence {A : Type} (R : relation A) :
  PreOrder R → Symmetric R → Equivalence R.
Proof.
  intros P S; constructor.
  - exact (@PreOrder_Reflexive A R P).
  - exact S.
  - exact (@PreOrder_Transitive A R P).
Qed.

(* * ** The discrete and codiscrete preorders on a carrier (§1.2.2) / * ** 载体上的离散和余离散前序 (§1.2.2) *)

(*
 The two extreme preorder structures on an arbitrary [Type]: equality, and
 the relation that always holds.  [discrete_rel] is the order-theoretic
 shadow of Instance/Discrete.v's [DiscreteCat] (whose homs are exactly
 equality proofs); [codiscrete_rel] is the shadow of the codiscrete
 category, which Structure/Discrete.v's header mentions as the other
 adjoint. 

 --------
 在任意的 [Type] 上的两个极端预序结构：等式，以及总为真的关系。[discrete_rel] 是 Instance/Discrete.v 的 [DiscreteCat] 的序理论影子（其同态正是等式证明）；[codiscrete_rel] 是余离散范畴的影子，Structure/Discrete.v 的头部将其提到为另一个伴随。
*)

Definition discrete_rel (A : Type) : relation A := fun x y => x = y.

Definition codiscrete_rel (A : Type) : relation A := fun _ _ => True.

Definition discrete_PreOrder (A : Type) : PreOrder (discrete_rel A).
Proof.
  constructor.
  - intro x; reflexivity.
  - intros x y z Hxy Hyz; exact (eq_trans Hxy Hyz).
Defined.

Definition codiscrete_PreOrder (A : Type) : PreOrder (codiscrete_rel A).
Proof. constructor; [ intro x; exact I | intros x y z _ _; exact I ]. Defined.

(*
 "Terminal", made precise.  Preorder structures on a FIXED carrier are
 compared by refinement: R refines S when the identity map on the carrier
 is monotone from R to S, i.e. when every R-instance is an S-instance.
 [codiscrete_rel] is a top for this comparison, and any other top agrees
 with it; [discrete_rel] is a bottom among REFLEXIVE relations, and any
 other such bottom agrees with it.  This is deliberately a statement about
 preorder structures on ONE fixed carrier.  Whether the codiscrete category
 is also terminal in [Cat] is a different question and is left open here —
 Instance/Cat.v's `≅` compares functors up to natural isomorphism, and
 [codiscrete_all_iso] below shows every pair of objects of the codiscrete
 category is isomorphic, which makes that question subtler than it looks. 

 --------
 “终端”，精确表述。在一个固定载体上的预序结构通过精炼进行比较：当载体上的恒等映射从 R 到 S 是单调的，即每个 R 实例都是 S 实例时，R 精炼 S。[codiscrete_rel] 是这种比较的上界，任何其他上界都与它一致；[discrete_rel] 是自反关系中的下界，任何其他此类下界也与它一致。这明确地是关于在一个固定载体上的预序结构的陈述。余离散范畴是否也是 [Cat] 中的终端是另一个问题，这里保持开放——Instance/Cat.v 的 `≅` 将函子比较到自然同构，下面的 [codiscrete_all_iso] 显示余离散范畴的每一对对象都是同构的，这使得这个问题比看起来更微妙。
*)

Definition Refines {A : Type} (R S : relation A) : Prop :=
  ∀ x y : A, R x y → S x y.

Theorem codiscrete_terminal {A : Type} (R : relation A) :
  Refines R (codiscrete_rel A).
Proof. intros x y _; exact I. Qed.

Theorem codiscrete_terminal_unique {A : Type} (S : relation A) :
  (∀ R : relation A, Refines R S) → ∀ x y : A, S x y <-> codiscrete_rel A x y.
Proof.
  intros top x y; split.
  - intro; exact I.
  - exact (top (codiscrete_rel A) x y).
Qed.

Theorem discrete_initial {A : Type} (R : relation A) :
  Reflexive R → Refines (discrete_rel A) R.
Proof. intros refl x y e; destruct e; exact (refl x). Qed.

Theorem discrete_initial_unique {A : Type} (S : relation A) :
  Reflexive S →
  (∀ R : relation A, Reflexive R → Refines S R) →
  ∀ x y : A, S x y <-> discrete_rel A x y.
Proof.
  intros refl bot x y; split.
  - exact (bot (discrete_rel A) (fun z => eq_refl) x y).
  - exact (discrete_initial S refl x y).
Qed.

(*
 The categorical reading of the top: from every proset on A there is an
 identity-on-objects functor into the codiscrete one, because every arrow
 has somewhere to go. 

 --------
 顶部的范畴解读：从 A 上的每个前序集合都有一个在对象上是恒等的函子到余离散的前序集合，因为每个箭头都有去处。
*)
Program Definition to_codiscrete {A : Type} {R : relation A} (P : PreOrder R) :
  Proset P ⟶ Proset (codiscrete_PreOrder A) := {|
  fobj := fun x => x;
  fmap := fun _ _ _ => I
|}.

(*
 And why the codiscrete preorder is as far from a poset as possible: all
 its objects are isomorphic, so it is skeletal only when A is a
 subsingleton. 

 --------
 以及为什么余离散预序尽可能远离偏序集：它的所有对象都是同构的，因此只有当 A 是一个子单集时，它才是骨架的。
*)
Lemma codiscrete_all_iso {A : Type} (x y : A) :
  x ≅[Proset (codiscrete_PreOrder A)] y.
Proof. exact (thin_iso (proset_thin (codiscrete_PreOrder A)) I I). Qed.

(* * ** Comparability, and how it differs from decidability (§1.2.2) / * ** 可比较性，以及它与可判定性的区别 (§1.2.2) *)

(*
 Two elements are comparable when the order relates them one way or the
 other AND the witness records which way: `∨` is Lib/Foundation.v's
 notation for [sum], so [comparable] is Type-valued and can be matched on
 to compute.  That is the whole point — [TotalOrder_meet] below builds the
 binary infimum by dispatching on it.

 Comparability is NOT decidability.  Decidability of R at (x, y) settles
 [R x y] one way or the other; comparability settles which of [R x y] and
 [R y x] holds but says nothing about the negation of either, and the two
 are only related through extra data.  Three theorems below measure the
 distinction instead of describing it: [comparable_of_decidable_total]
 builds comparability from decidability plus Prop-valued totality (the
 [\/] can be eliminated because the goal it feeds is itself a Prop);
 [comparable_total] extracts Prop-valued totality back; and
 [decidable_of_comparable] exhibits a sufficient route from comparability to
 decidability, which needs reflexivity, antisymmetry AND a decision
 procedure for equality on the carrier — strictly more input than
 comparability alone.  (Those three are shown sufficient, not necessary.)
 Construction/Enriched/Two.v's [tpre_dec] is the
 decidability side of the same coin: that file needs to COMPUTE a truth
 value in the walking arrow for every pair, which comparability alone
 would not supply. 

 --------
 当两个元素的顺序以某种方式关联它们时，并且见证记录了具体方式，它们就是可比较的：`∨` 是 Lib/Foundation.v 中 [sum] 的表示，所以 [comparable] 是类型值的，可以进行匹配计算。重点就是这个 —— 下面的 [TotalOrder_meet] 通过对其进行分发来构建二元下确界。可比性不是可判定性。在(x, y)处R的可判定性能确定[R x y]的真伪；可比性则确定[R x y]和[R y x]中的哪一个成立，但对任意一个的否定则无从说明，而且两者只有通过额外的数据才相关。下面三个定理衡量这一区别，而不是描述它：[comparable_of_decidable_total]通过可判定性加上Prop值的全体性构建可比性（[\/]可以消除，因为它所提供的目标本身就是一个Prop）；[comparable_total]将Prop值的全体性提取回来；[decidable_of_comparable]展示了从可比性到可判定性的一个充分途径，这需要反身性、反对称性以及对载体上等式的判定程序——严格来说，这比单独的可比性要求的输入更多。（那三个被认为是充分的，而非必要的。）
 Construction/Enriched/Two.v 的 [tpre_dec] 是同一枚硬币的可判定性方面：该文件需要在行走箭头中为每对计算一个真值，而仅仅可比性无法提供这一点。
*)

Definition comparable {A : Type} (R : relation A) (x y : A) : Type :=
  R x y ∨ R y x.

Definition decidable_rel {A : Type} (R : relation A) : Type :=
  ∀ x y : A, R x y ∨ ¬ R x y.

Lemma comparable_of_decidable_total {A : Type} (R : relation A) :
  decidable_rel R → (∀ x y : A, R x y \/ R y x) →
  ∀ x y : A, comparable R x y.
Proof.
  intros dec tot x y.
  destruct (dec x y) as [h|n].
  - exact (inl h).
  - right.
    destruct (tot x y) as [h|h].
    + contradiction.
    + exact h.
Qed.

Lemma comparable_total {A : Type} (R : relation A) (x y : A) :
  comparable R x y → R x y \/ R y x.
Proof. intros [h|h]; [ left | right ]; exact h. Qed.

Lemma decidable_of_comparable {A : Type} (R : relation A) :
  Reflexive R →
  (∀ x y : A, R x y → R y x → x = y) →
  (∀ x y : A, (x = y) ∨ ¬ (x = y)) →
  (∀ x y : A, comparable R x y) →
  decidable_rel R.
Proof.
  intros refl anti eqdec cmp x y.
  destruct (cmp x y) as [h|h].
  - exact (inl h).
  - destruct (eqdec x y) as [e|ne].
    + destruct e; exact (inl (refl x)).
    + right; intro hxy; exact (ne (anti x y hxy h)).
Qed.

(* In a discrete preorder an element is comparable with itself and with nothing else (§1.2.2): the only arrows are the identities. / 在离散预序中，一个元素只能与它自身可比较，而与其他任何元素不可比较（第1.2.2节）：唯一的箭头是恒等箭头。 *)

Lemma discrete_comparable_self {A : Type} (x : A) :
  comparable (discrete_rel A) x x.
Proof. exact (inl eq_refl). Qed.

Lemma discrete_incomparable {A : Type} (x y : A) :
  x ≠ y → comparable (discrete_rel A) x y → False.
Proof. intros ne [e|e]; [ exact (ne e) | exact (ne (eq_sym e)) ]. Qed.

(* * ** Total (linear) orders, Mac Lane §I.2 definition 4 / * ** 全序（线性序），Mac Lane §I.2 定义 4 *)

(*
 A total order is a preorder that is antisymmetric and in which every two
 elements are comparable.  The class is [Type]-valued because
 [total_comparable] is: a Prop-valued totality would not let the meet below
 be computed.  Antisymmetry is stated in the elementary form and converted
 to Instance/Poset.v's [Antisymmetric] shape by [TotalOrder_Antisymmetric],
 so that the thin category is built by Instance/Poset.v's [Poset]
 rather than by a fresh construction. 

 --------
 全序是一个反对称的预序，并且其中的每两个元素都是可比较的。这个类是 [Type] 值的，因为 [total_comparable] 是：一个命题值的全体将不允许计算下面的交。反对称性以基本形式陈述，并通过 [TotalOrder_Antisymmetric] 转换为 Instance/Poset.v 的 [Antisymmetric] 形式，因此薄范畴是通过 Instance/Poset.v 的 [Poset] 构建的，而不是通过一个新的构造。
*)

Class TotalOrder {A : Type} (R : relation A) : Type := {
  total_preorder   : PreOrder R;
  total_antisym    : ∀ x y : A, R x y → R y x → x = y;
  total_comparable : ∀ x y : A, comparable R x y
}.

Definition TotalOrder_Antisymmetric {A : Type} {R : relation A}
           (T : TotalOrder R) : @Antisymmetric A eq eq_equiv R :=
  @total_antisym A R T.

Definition TotalOrder_Category {A : Type} {R : relation A}
           (T : TotalOrder R) : Category :=
  @Poset A R (@total_preorder A R T) (TotalOrder_Antisymmetric T).

Lemma TotalOrder_Category_thin {A : Type} {R : relation A} (T : TotalOrder R) :
  Thin (TotalOrder_Category T).
Proof. exact (proset_thin (@total_preorder A R T)). Qed.

(* The characterization asked for in §1.2.2: over a fixed antisymmetric preorder, being a total order IS "every two elements are comparable". / §1.2.2 中要求的表征：在固定的反对称前序上，作为全序就是“任意两个元素都是可比较的” *)
Theorem TotalOrder_iff_all_comparable {A : Type} (R : relation A)
        (P : PreOrder R) (anti : ∀ x y : A, R x y → R y x → x = y) :
  TotalOrder R ↔ (∀ x y : A, comparable R x y).
Proof.
  split.
  - exact (fun T => @total_comparable A R T).
  - intro cmp.
    exact {| total_preorder := P
           ; total_antisym := anti
           ; total_comparable := cmp |}.
Qed.

(* * *** (ℕ, ≤) as a total order, and its reverse / * *** (ℕ, ≤) 作为全序，以及它的逆序 *)

Definition nat_TotalOrder : TotalOrder PeanoNat.Nat.le := {|
  total_preorder   := PeanoNat.Nat.le_preorder;
  total_antisym    := partial_order_antisym PeanoNat.Nat.le_partialorder;
  total_comparable := fun x y =>
    match le_ge_dec x y with
    | left  h => inl h
    | right h => inr h
    end
|}.

(*
 The thin category of (ℕ, ≤).  Instance/Proset.v and Instance/Poset.v
 both already export a [LessThanEqualTo_Category] for this order (a clash
 Test/Poset.v documents), so no third name is introduced; this one is
 built through [TotalOrder_Category] to exercise the class. 

 --------
 （ℕ, ≤）的薄范畴。Instance/Proset.v 和 Instance/Poset.v 都已经为这个顺序导出了一个 [LessThanEqualTo_Category]（一个冲突 Test/Poset.v 有记录），因此没有引入第三个名称；这个是通过 [TotalOrder_Category] 构建的，用来测试该类。
*)
Definition Nat_TotalOrder_Category : Category :=
  TotalOrder_Category nat_TotalOrder.

(* The reverse of (ℕ, ≤) is (ℕ, ≥) on the nose: stdlib defines [ge n m] as [m <= n], and [Basics.flip le x y] reduces to [le y x], so the two relations are convertible. / (ℕ, ≤) 的逆就是 (ℕ, ≥)：stdlib 定义 [ge n m] 为 [m <= n]，而 [Basics.flip le x y] 简化为 [le y x]，所以这两个关系是可转换的。 *)
Lemma flip_le_is_ge (x y : nat) :
  Basics.flip PeanoNat.Nat.le x y = ge x y.
Proof. reflexivity. Qed.

(*
 Hence the opposite of the thin category of (ℕ, ≤) is the thin category of
 (ℕ, ≥), by the general order-reversal isomorphism above. 

 --------
 因此，（ℕ, ≤）的稀疏范畴的对偶是（ℕ, ≥）的稀疏范畴，根据上面的广义顺序反转同构。
*)
Definition Nat_op_iso :
  ((Proset PeanoNat.Nat.le_preorder)^op)%category
    ≅[Cat] Proset (flip_PreOrder PeanoNat.Nat.le_preorder) :=
  Proset_op_iso PeanoNat.Nat.le_preorder.

(*
 And the reversed order is itself a total order, so the opposite category
 is again the thin category of a total order. 

 --------
 而反转的顺序本身也是一个全序，因此对偶范畴再次是全序的瘦范畴。
*)
Definition flip_TotalOrder {A : Type} {R : relation A} (T : TotalOrder R) :
  TotalOrder (Basics.flip R) := {|
  total_preorder   := flip_PreOrder (@total_preorder A R T);
  total_antisym    := fun x y hxy hyx => @total_antisym A R T x y hyx hxy;
  total_comparable := fun x y =>
    match @total_comparable A R T x y with
    | inl h => inr h
    | inr h => inl h
    end
|}.

Definition nat_ge_TotalOrder : TotalOrder (Basics.flip PeanoNat.Nat.le) :=
  flip_TotalOrder nat_TotalOrder.

(* * ** Infima and suprema, and their categorical identification (§1.3.1) / * ** 下确界与上确界，以及它们的范畴识别 (§1.3.1) *)

(*
 Order-theoretic names first: m is an infimum (greatest lower bound) of x
 and y when it is a lower bound and dominates every lower bound.  The
 connectives are Lib/Foundation.v's, so these are [Type]-valued;
 nothing is eliminated from Prop into Type, the Prop components are only
 carried. 

 --------
 先从序理论的名称开始：当 m 是 x 和 y 的下界且支配每一个下界时，它是它们的下确界（最大下界）。连接词是 Lib/Foundation.v 的，所以它们取值于 [Type]；没有任何从 Prop 到 Type 被消除，Prop 组件只是被携带。
*)

Definition IsInfimum {A : Type} (R : relation A) (x y m : A) : Type :=
  (R m x ∧ R m y) ∧ (∀ n : A, R n x → R n y → R n m).

Definition IsSupremum {A : Type} (R : relation A) (x y m : A) : Type :=
  (R x m ∧ R y m) ∧ (∀ n : A, R x n → R y n → R m n).

(*
 The two notions are one notion read in two directions, and the identity is
 definitional, not merely provable. 

 --------
 这两个概念其实是同一个概念，只是从两个方向来理解，而这种同一性是定义上的，而不仅仅是可证明的。
*)
Lemma supremum_is_flipped_infimum {A : Type} (R : relation A) (x y m : A) :
  IsSupremum R x y m = IsInfimum (Basics.flip R) x y m.
Proof. reflexivity. Qed.

(*
 The two-object discrete diagram in the thin category of P, picking out x
 at [false] and y at [true].  Instance/Discrete.v's [DiscreteCat_Functor]
 turns any function out of a [Type] into a functor out of the discrete
 category on it. 

 --------
 在 P 的薄范畴中的双对象离散图，选出 x 位于 [false] 和 y 位于 [true]。Instance/Discrete.v 的 [DiscreteCat_Functor] 将任何来自 [Type] 的函数转换为来自其上的离散范畴的函子。
*)
Definition PairDiagram {A : Type} {R : relation A} (P : PreOrder R)
           (x y : A) : DiscreteCat bool ⟶ Proset P :=
  DiscreteCat_Functor (C:=Proset P) (fun b : bool => if b then y else x).

(*
 A lower bound of x and y IS a cone over the pair diagram (Structure/Cone.v
 declares the legs, and bundles them with an apex), and an upper bound IS a
 COCONE over it — which Structure/Cone.v defines as a cone over the
 opposed diagram, exactly the type written below.  These two constructors
 are separated out so that the mediating arrow supplied by [ump_limit] has
 an apex Coq can see is [n]. 

 --------
 x 和 y 的下界是该对偶图的一个锥（Structure/Cone.v 声明了底边，并将它们与顶点捆绑在一起），而上界是它的余锥——Structure/Cone.v 定义为对偶图上的锥，正是下文所写的类型。这两个构造函数被分开，以便 [ump_limit] 提供的中介箭头有一个顶点 Coq 可以看到的 [n]。
*)

Definition pair_cone {A : Type} {R : relation A} (P : PreOrder R)
           (x y n : A) (lx : R n x) (ly : R n y) : Cone (PairDiagram P x y).
Proof.
  unshelve econstructor.
  { exact n. }
  unshelve econstructor.
  - intro b; destruct b; [ exact ly | exact lx ].
  - intros b b' f; exact I.
Defined.

Definition pair_cocone {A : Type} {R : relation A} (P : PreOrder R)
           (x y n : A) (ux : R x n) (uy : R y n) :
  Cone ((PairDiagram P x y)^op).
Proof.
  unshelve econstructor.
  { exact n. }
  unshelve econstructor.
  - intro b; destruct b; [ exact uy | exact ux ].
  - intros b b' f; exact I.
Defined.

(*
 THE IDENTIFICATION.  Being an infimum of x and y is being a limit of that
 diagram, with the apex pinned (Structure/Limit.v's [IsALimit]).  Note
 what each half costs.  Building the limit needs: the two legs (the lower
 bound), cone coherence (an equation in the trivial hom-setoid, hence
 free), the mediating arrow (the greatest-lower-bound clause), and its
 uniqueness (again free, by thinness).  Reading the limit back needs only
 the legs and the mediator.  Totality is nowhere used — this holds over an
 arbitrary preorder. 

 --------
 识别。成为 x 和 y 的下确界就是成为该图的极限，顶点固定（Structure/Limit.v 的 [IsALimit]）。注意每一部分的代价。构造极限需要：两条边（下界）、圆锥一致性（在平凡同态集合中是一个方程，因此是免费的）、中介箭头（最大下界条款）及其唯一性（同样是免费的，由于稀薄性）。回读极限只需要边和中介箭头。整体性未被使用——这在任意预序上都成立。
*)
Theorem infimum_iff_limit {A : Type} {R : relation A} (P : PreOrder R)
        (x y m : A) :
  IsInfimum R x y m ↔ IsALimit (PairDiagram P x y) m.
Proof.
  split.
  - intros [[lx ly] med].
    unshelve refine {| limit_acone := _ |}.
    + unshelve refine {| vertex_map := _ |}.
      * intro b; destruct b; [ exact ly | exact lx ].
      * intros b b' f; exact I.
    + intro N.
      unshelve refine {| unique_obj := _ |}.
      * exact (med (vertex_obj[N])
                 (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) false)
                 (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) true)).
      * intro b; exact I.
      * intros v _; exact I.
  - intro L.
    split.
    + split.
      * exact (@vertex_map _ _ _ _ (@limit_acone _ _ _ _ L) false).
      * exact (@vertex_map _ _ _ _ (@limit_acone _ _ _ _ L) true).
    + intros n lx ly.
      exact (unique_obj (@ump_limit _ _ _ _ L (pair_cone P x y n lx ly))).
Qed.

(*
 The dual identification.  Structure/Limit.v defines a colimit of F as a
 limit of F^op, so the apex-pinned colimit of the pair diagram is
 [IsALimit ((PairDiagram P x y)^op) m]; unfolding, its legs are arrows
 x ~> m and y ~> m of [Proset P], i.e. upper bounds, and its mediator is
 the least-upper-bound clause. 

 --------
 双重识别。Structure/Limit.v 将 F 的余极限定义为 F^op 的极限，因此该对图的顶点固定余极限是 [IsALimit ((PairDiagram P x y)^op) m]；展开来看，它的腿是 [Proset P] 中的箭头 x ~> m 和 y ~> m，即上界，而它的中介则是最小上界条款。
*)
(*
 The apex-pinned colimit notion below is spelled out by hand; the library
 already names it -- Structure/Limit/Preservation.v's
 [IsAColimit F c := IsALimit (F^op) c] -- and [supremum_iff_IsAColimit]
 restates the theorem through that name. 

 --------
 下面的顶点固定余极限概念是手工写出的；库已经为它命名——Structure/Limit/Preservation.v 中的 [IsAColimit F c := IsALimit (F^op) c] ——而 [supremum_iff_IsAColimit] 则通过那个名称重述了该定理。
*)
Theorem supremum_iff_colimit {A : Type} {R : relation A} (P : PreOrder R)
        (x y m : A) :
  IsSupremum R x y m ↔ IsALimit ((PairDiagram P x y)^op) m.
Proof.
  split.
  - intros [[ux uy] med].
    unshelve refine {| limit_acone := _ |}.
    + unshelve refine {| vertex_map := _ |}.
      * intro b; destruct b; [ exact uy | exact ux ].
      * intros b b' f; exact I.
    + intro N.
      unshelve refine {| unique_obj := _ |}.
      * exact (med (vertex_obj[N])
                 (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) false)
                 (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) true)).
      * intro b; exact I.
      * intros v _; exact I.
  - intro L.
    split.
    + split.
      * exact (@vertex_map _ _ _ _ (@limit_acone _ _ _ _ L) false).
      * exact (@vertex_map _ _ _ _ (@limit_acone _ _ _ _ L) true).
    + intros n ux uy.
      exact (unique_obj (@ump_limit _ _ _ _ L (pair_cocone P x y n ux uy))).
Qed.

(*
   * *** Existence in a total order

   The identification above needs no totality; EXISTENCE does.  In a total
   order the meet of x and y is whichever of the two is below the other,
   which is exactly what the Type-valued [comparable] lets us compute. 

   --------
   * *** 在全序中的存在

   上述识别不需要全体性；存在需要。在全序中，x 和 y 的交是两者中位于另一者之下的那个，这正是类型值 [comparable] 让我们能够计算的。
*)

Definition tmeet {A : Type} {R : relation A} (T : TotalOrder R) (x y : A) : A :=
  match @total_comparable A R T x y with
  | inl _ => x
  | inr _ => y
  end.

Definition tjoin {A : Type} {R : relation A} (T : TotalOrder R) (x y : A) : A :=
  match @total_comparable A R T x y with
  | inl _ => y
  | inr _ => x
  end.

Theorem TotalOrder_meet {A : Type} {R : relation A} (T : TotalOrder R)
        (x y : A) : IsInfimum R x y (tmeet T x y).
Proof.
  unfold tmeet.
  destruct (@total_comparable A R T x y) as [h|h].
  - split; [ split | ].
    + exact (@PreOrder_Reflexive A R (@total_preorder A R T) x).
    + exact h.
    + intros n lx ly; exact lx.
  - split; [ split | ].
    + exact h.
    + exact (@PreOrder_Reflexive A R (@total_preorder A R T) y).
    + intros n lx ly; exact ly.
Qed.

Theorem TotalOrder_join {A : Type} {R : relation A} (T : TotalOrder R)
        (x y : A) : IsSupremum R x y (tjoin T x y).
Proof.
  unfold tjoin.
  destruct (@total_comparable A R T x y) as [h|h].
  - split; [ split | ].
    + exact h.
    + exact (@PreOrder_Reflexive A R (@total_preorder A R T) y).
    + intros n ux uy; exact uy.
  - split; [ split | ].
    + exact (@PreOrder_Reflexive A R (@total_preorder A R T) x).
    + exact h.
    + intros n ux uy; exact ux.
Qed.

(*
 Combining the two: the thin category of a total order has a limit and a
 colimit for every two-object discrete diagram. 

 --------
 结合两者：全序的薄范畴对于每个含两个对象的离散图都有极限和余极限。
*)

Definition TotalOrder_pair_limit {A : Type} {R : relation A}
           (T : TotalOrder R) (x y : A) :
  IsALimit (PairDiagram (@total_preorder A R T) x y) (tmeet T x y) :=
  fst (infimum_iff_limit (@total_preorder A R T) x y (tmeet T x y))
      (TotalOrder_meet T x y).

Definition TotalOrder_pair_colimit {A : Type} {R : relation A}
           (T : TotalOrder R) (x y : A) :
  IsALimit ((PairDiagram (@total_preorder A R T) x y)^op) (tjoin T x y) :=
  fst (supremum_iff_colimit (@total_preorder A R T) x y (tjoin T x y))
      (TotalOrder_join T x y).

(* * *** Worked instance: (ℕ, ≤), with min and max / * *** 已处理的实例: (ℕ, ≤)，具有最小值和最大值 *)

Theorem nat_min_infimum (x y : nat) :
  IsInfimum PeanoNat.Nat.le x y (PeanoNat.Nat.min x y).
Proof.
  split; [ split | ].
  - exact (PeanoNat.Nat.le_min_l x y).
  - exact (PeanoNat.Nat.le_min_r x y).
  - intros n lx ly; exact (PeanoNat.Nat.min_glb x y n lx ly).
Qed.

Theorem nat_max_supremum (x y : nat) :
  IsSupremum PeanoNat.Nat.le x y (PeanoNat.Nat.max x y).
Proof.
  split; [ split | ].
  - exact (PeanoNat.Nat.le_max_l x y).
  - exact (PeanoNat.Nat.le_max_r x y).
  - intros n ux uy; exact (PeanoNat.Nat.max_lub x y n ux uy).
Qed.

Definition nat_min_limit (x y : nat) :
  IsALimit (PairDiagram PeanoNat.Nat.le_preorder x y) (PeanoNat.Nat.min x y) :=
  fst (infimum_iff_limit PeanoNat.Nat.le_preorder x y (PeanoNat.Nat.min x y))
      (nat_min_infimum x y).

Definition nat_max_colimit (x y : nat) :
  IsALimit ((PairDiagram PeanoNat.Nat.le_preorder x y)^op)
           (PeanoNat.Nat.max x y) :=
  fst (supremum_iff_colimit PeanoNat.Nat.le_preorder x y
         (PeanoNat.Nat.max x y))
      (nat_max_supremum x y).

(* * *** Worked instance: the two-element order The smallest order in which the identification has content: [false] below [true], with conjunction the meet and disjunction the join. / * *** 示例实例：二元序 唯一具有内容的最小序：下面的 [false] [true] ，其合取为交，析取为并。 *)

Definition bool_le (x y : bool) : Prop := x = true → y = true.

Definition bool_PreOrder : PreOrder bool_le.
Proof.
  constructor.
  - intros x h; exact h.
  - intros x y z Hxy Hyz h; exact (Hyz (Hxy h)).
Defined.

Definition bool_TotalOrder : TotalOrder bool_le.
Proof.
  unshelve refine {| total_preorder := bool_PreOrder |}.
  - intros x y Hxy Hyx.
    destruct x, y; try reflexivity.
    + symmetry; exact (Hxy eq_refl).
    + exact (Hyx eq_refl).
  - intros x y.
    destruct x.
    + right; intro h; reflexivity.
    + left; intro h; discriminate h.
Defined.

Theorem bool_andb_infimum (x y : bool) :
  IsInfimum bool_le x y (andb x y).
Proof.
  split; [ split | ].
  - destruct x, y; simpl; intro h; try reflexivity; exact h.
  - destruct x, y; simpl; intro h; try reflexivity; exact h.
  - intros n lx ly h; destruct x, y; simpl;
      solve [ reflexivity | exact (lx h) | exact (ly h) ].
Qed.

Theorem bool_orb_supremum (x y : bool) :
  IsSupremum bool_le x y (orb x y).
Proof.
  split; [ split | ].
  - destruct x, y; simpl; intro h; try reflexivity; exact h.
  - destruct x, y; simpl; intro h; try reflexivity; exact h.
  - intros n ux uy h; destruct x, y; simpl in *;
      solve [ reflexivity | exact (ux h) | exact (uy h) | discriminate h ].
Qed.

Definition bool_andb_limit (x y : bool) :
  IsALimit (PairDiagram bool_PreOrder x y) (andb x y) :=
  fst (infimum_iff_limit bool_PreOrder x y (andb x y)) (bool_andb_infimum x y).

Definition bool_orb_colimit (x y : bool) :
  IsALimit ((PairDiagram bool_PreOrder x y)^op) (orb x y) :=
  fst (supremum_iff_colimit bool_PreOrder x y (orb x y))
      (bool_orb_supremum x y).

(*
 The two-element order is a poset, so its thin category is skeletal; and
 the meet computed by the class matches the boolean conjunction. 

 --------
 这个二元素序是一个偏序集，因此它的薄范畴是骨架的；并且该类计算的交与布尔合取一致。
*)

Example bool_tmeet_true_false : tmeet bool_TotalOrder true false = false.
Proof. reflexivity. Qed.

Example bool_tjoin_true_false : tjoin bool_TotalOrder true false = true.
Proof. reflexivity. Qed.

(*
   * ** Sanity: what the constructions reduce to

   Each of these holds by [eq_refl], so together they pin down that nothing
   above is stated at one remove from the concrete objects it is about.
   Numerals carry [%nat] because Lib/Foundation.v closes [nat_scope]. 

   --------
   * ** 理智：构造归结为何

   这些每一项都由 [eq_refl] 保持，因此它们一起确定了上面没有任何内容是以间接方式针对它所涉及的具体对象陈述的。
   数字携带 [%nat]，因为 Lib/Foundation.v 封闭了 [nat_scope]。
*)

(*
 The thin category of a total order has the carrier as its objects and the
 order itself as its homs. 

 --------
 全序的纤薄范畴以其承载对象为对象，以其序本身为态射。
*)
Example nat_order_obj : obj[Nat_TotalOrder_Category] = nat.
Proof. reflexivity. Qed.

Example nat_order_hom (x y : nat) :
  (x ~{Nat_TotalOrder_Category}~> y) = PeanoNat.Nat.le x y.
Proof. reflexivity. Qed.

(*
 Box: the reverse order, concretely.  Reading an arrow of the OPPOSITE thin
 category as a proposition gives [ge] on the nose — this is
 [flip_le_is_ge] seen through Construction/Opposite.v's hom reversal,
 and it is what [Nat_op_iso] packages as an isomorphism of categories. 

 --------
 盒子：以相反的顺序，具体地说。将相反细分类别的箭头作为命题来阅读，得到 [ge] —— 这是通过 Construction/Opposite.v 的同构反转看到的 [flip_le_is_ge]，并且它是 [Nat_op_iso] 所打包的类别同构。
*)
Example nat_op_hom_is_ge (x y : nat) :
  (x ~{((Proset PeanoNat.Nat.le_preorder)^op)%category}~> y) = ge x y.
Proof. reflexivity. Qed.

(* The meet of a total order computes. / 全序的上确界进行计算。 *)
Example nat_tmeet_3_5 : tmeet nat_TotalOrder 3%nat 5%nat = 3%nat.
Proof. reflexivity. Qed.

Example nat_tjoin_3_5 : tjoin nat_TotalOrder 3%nat 5%nat = 5%nat.
Proof. reflexivity. Qed.

(* [Thin] is inhabited on the two examples the tree already ships. The poset one is fully qualified because Instance/Proset.v and Instance/Poset.v both export the name (Test/Poset.v). / [Thin] 居住在两个示例上，树已经发送。这个 poset 是完全限定的，因为 Instance/Proset.v 和 Instance/Poset.v 都导出该名称 (Test/Poset.v)。 *)

Definition thin_proset_nat : Thin (Proset PeanoNat.Nat.le_preorder) :=
  proset_thin PeanoNat.Nat.le_preorder.

Definition thin_poset_nat :
  Thin Category.Instance.Poset.LessThanEqualTo_Category :=
  poset_thin PeanoNat.Nat.le_preorder
    (partial_order_antisym PeanoNat.Nat.le_partialorder).

(* The colimit half restated through the library's own apex-pinned name (Structure/Limit/Preservation.v), as promised above. / 通过库自身的顶点固定名称重新表述的余极半（Structure/Limit/Preservation.v），如上所承诺。 *)
Corollary supremum_iff_IsAColimit {A : Type} {R : relation A} (P : PreOrder R)
        (x y m : A) :
  IsSupremum R x y m ↔ IsAColimit (PairDiagram P x y) m.
Proof. exact (supremum_iff_colimit P x y m). Qed.

(*
 The "no third name" claim above, pinned rather than asserted: the
 TotalOrder route lands on the SAME category both existing files define. 

 --------
 上面提到的“没有第三个名字”的说法，是固定的而不是断言的：总顺序路线落在两个现有文件都定义的同一个类别上。
*)
Example Nat_TotalOrder_Category_is_Poset :
  Nat_TotalOrder_Category = Category.Instance.Poset.LessThanEqualTo_Category
  := eq_refl.

(*
 The discrete preorder really is the order-theoretic shadow of
 Instance/Discrete.v's DiscreteCat: the squashed ∃-a-morphism preorder of
 [DiscreteCat A] is exactly [discrete_rel A].  (An arrow of [DiscreteCat A]
 IS an equality proof, so inhabitation of the hom is equality.) 

 --------
 离散预序实际上是 Instance/Discrete.v 中 DiscreteCat 的序理论影子：[DiscreteCat A] 的压缩 ∃-a-态射预序正好是 [discrete_rel A]。（[DiscreteCat A] 的箭头就是一个等式证明，所以态射的存在性就是等式。）
*)
Lemma thin_preorder_DiscreteCat {A : Type} (x y : A) :
  thin_preorder (DiscreteCat A) x y ↔ discrete_rel A x y.
Proof.
  split.
  - intros [e]; exact e.
  - intro e; exact (inhabits e).
Qed.

