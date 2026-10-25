Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/Cat
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_small_categories

 Cat is the category of all small categories:

 objects               Categories
 arrows                Functors
 arrow equivalence     Natural Isomorphisms
 identity              Identity Functor
 composition           Horizontal composition of Functors

 isomorphisms          Equivalences of Categories (caused by the definition
 of [Functor_Setoid]).

 Size: Cat is a large category, and so cannot be an object of itself (there
 is no category of *all* categories). Here that constraint is enforced by
 universe polymorphism: [Category@{o h p | h <= p}] lives at a strictly
 higher universe than its objects, so the inner categories collected by
 [obj := Category] sit below the universe of [Cat] itself.

 Strict vs. weak: because the hom-setoid [Functor_Setoid] identifies functors
 whenever they are naturally isomorphic (not on-the-nose equal on objects and
 morphisms), an isomorphism in this [Cat] is an *equivalence* of categories.
 Identifying functors up to natural isomorphism makes this the homotopy
 category Ho(Cat) (the 1-truncation of the 2-category Cat), whose morphisms are
 natural-isomorphism classes of functors. It is therefore NOT the strict
 1-category of categories of the textbooks; and although it keeps the same
 objects, it is neither the *underlying* 1-category of the 2-category Cat
 (which keeps functor equality) nor its *core* (which keeps only the
 isomorphisms).

 This is deliberate, and consistent with the rest of the library: lacking
 function extensionality, the development compares morphisms up to a setoid
 equivalence [≈] rather than by Coq's intensional equality [=]. For [Cat] the
 morphisms are functors, and the corresponding [≈] is natural isomorphism —
 the equivalence-invariant notion of sameness for functors. So [Cat] applies
 the weaker notion of equivalence used everywhere else, lifted one level up, to
 suit Coq's metatheory.

 The reporter of issue #138 is right that the textbook bare-name "Cat" is the
 STRICT 1-category (functors compared by on-the-nose equality); that is
 [Category.Instance.StrictCat.StrictCat]. The choice here is not an error but a
 weaker, equivalence-invariant convention (cf. agda-categories' [Cats], whose
 functor equivalence is likewise natural isomorphism). The identity-on-objects
 comparison functor [StrictCat_to_Cat : StrictCat ⟶ Cat] of
 [Category.Instance.StrictCat.ToCat] sends each strict equality to the natural
 isomorphism it induces, exhibiting [StrictCat] as a strictification of this
 Ho(Cat). The weak hom-equivalence is moreover used substantively, not merely
 for phrasing: [Construction.Comma.Adjunction], for instance, builds an
 adjunction's unit and counit out of the *natural-isomorphism components* of a
 comma equivalence [≅[Cat]] — it takes the underlying morphism
 [from (`1 (iso_from_to lawvere_iso) x)] of such a component — which relies on
 [≅] in [Cat] being a natural isomorphism; a strict reformulation would be a
 genuinely different, transport-based construction rather than a rename.
 Conversely, the construction that cannot live over this
 [Cat] at all is the object-equality-dependent underlying-graph functor
 [Forgetful : StrictCat ⟶ Quiv] of issue #138, which does not respect natural
 isomorphism. 

 --------
 nLab:  https://ncatlab.org/nlab/show/Cat 
 维基百科:  https://en.wikipedia.org/wiki/Category_of_small_categories 

 Cat 是所有小范畴的范畴：

 对象               范畴
 箭头               函子
 箭头等价           自然同构
 恒等               恒等函子
 复合               函子的水平复合

 同构               范畴等价（由 [Functor_Setoid] 的定义引起）

 大小：Cat 是一个大范畴，因此不能成为它自身的对象（不存在包含*所有*范畴的范畴）。在这里，该约束通过宇宙多态性来实现：[Category@{o h p | h <= p}] 所在的宇宙严格高于其对象，因此由 [obj := Category] 收集的内部范畴位于 [Cat] 本身的宇宙之下。严格与宽松：由于同态集 [Functor_Setoid] 将函子在自然同构时（而非在对象和态射上完全相等时）视为相同，因此 [Cat] 中的同构是范畴的*等价*。将函子按自然同构进行识别，使其成为同伦范畴 Ho(Cat)（2-范畴 Cat 的 1 截断），其态射是函子的自然同构类。因此，它不是教科书中的严格 1-范畴；尽管它保留了相同的对象，但它既不是 2-范畴 Cat 的*底层* 1-范畴（保留函子的相等性），也不是其*核心*（只保留同构）。这是有意为之，并且与整个库保持一致：由于缺乏函数外延性，开发过程中是将态射按照 setoid 等价  [≈]  进行比较，而不是按照 Coq 的内在相等  [=]  。对于  [Cat] ，态射是函子，对应的  [≈]  是自然同构——这是函子的等价不变的相同概念。因此  [Cat]  将到处使用的较弱等价概念提升一级，以适应 Coq 的元理论。问题 #138 的记者是对的，教材中裸名 “Cat” 是严格的 1-范畴（函子通过完全相等进行比较）；也就是说 [Category.Instance.StrictCat.StrictCat]。这里的选择不是错误，而是一种较弱的、等价不变的约定（参见 agda-categories 的 [Cats]，其函子等价同样是自然同构）。对象恒等比较函子 [StrictCat_to_Cat : StrictCat ⟶ Cat] 将每个严格相等发送为它所引出的自然同构，从而将 [StrictCat] 展示为该 Ho(Cat) 的严格化。弱同值关系不仅仅用于措辞上，它还有实质性的用途：例如，[Construction.Comma.Adjunction] 构建了伴随的单位和余单位，它们是从逗号等价 [≅[Cat] 的*自然同构分量*中构建的——它采用了这样的一个分量的基础态射 [from (`1 (iso_from_to lawvere_iso) x)]——这依赖于 [Cat] 中的 [≅] 是自然同构；严格的重新表述将是一个真正不同的、基于传输的构造，而不是简单地更名。相反，无法在这个 [Cat] 上实现的构造是第 #138 号问题中的依赖于对象相等的基础图函子 [Forgetful : StrictCat ⟶ Quiv]，它不保持自然同构。
*)

(*
 Where Cat comes from, and what it is for

 SEP:   https://plato.stanford.edu/entries/category-theory/
 nLab:  https://ncatlab.org/nlab/show/2-category
 nLab:  https://ncatlab.org/nlab/show/ETCC

 Cat is category theory applied to itself.  Every ingredient of the
 instance below is already implicit in the founding paper of the subject
 (Eilenberg and Mac Lane, "General theory of natural equivalences",
 Trans. Amer. Math. Soc. 58, 1945), yet the concept of a category of
 categories is nowhere mentioned there; the authors regarded categories
 as scaffolding — "the whole concept of a category is essentially an
 auxiliary one", the basic concepts being functor and natural
 transformation, with "the categories are provided as the domains and
 ranges of functors" (quoted in Marquis, "Category Theory", Stanford
 Encyclopedia of Philosophy).  The instance below is the structure that
 finally makes categories themselves the objects, so that the machinery
 of the theory can be turned on the theory itself.

 The dimension this 1-categorical instance truncates away has its own
 history.  Vertical and horizontal composition of natural
 transformations, with whiskering, first appear in the appendix of
 Godement's "Topologie algébrique et théorie des faisceaux" (1958),
 invented for the standard resolution of abelian sheaves; the Godement
 product is this library's [nat_hcompose] in
 Theory/Natural/Transformation.v.  Strict 2-categories are due to
 Bénabou ("Catégories relatives", 1965) and Maranda ("Formal
 categories", 1965) — not to Ehresmann, whose 1963 double categories
 were the inspiration — and Cat is the archetypical 2-category (nLab,
 "2-category").  Here the higher cells live in
 Instance/Cat/Bicategory.v, where the hom-categories are definitionally
 the functor categories of Instance/Fun.v.

 Lawvere proposed to make the self-application foundational: the
 category of categories itself, axiomatized in first-order terms, would
 replace membership-based set theory ("The Category of Categories as a
 Foundation for Mathematics", La Jolla Proceedings, Springer 1966,
 following his 1963 dissertation).  J. R. Isbell's review (Mathematical
 Reviews, 1967) found an error in a core result, no repair achieved
 consensus, and the programme was largely eclipsed by topos theory,
 though it has recent successors (Hughes and Miranda, arXiv:2403.03647,
 2025).  The size question it wrestled with is the one the header above
 settles by typing: a category of all categories invites a Russell-style
 paradox, classically avoided by the small/large distinction or by
 Grothendieck universes.  Rather than adopt either device axiomatically,
 this library has a [Cat] at every universe level, each strictly above
 its own objects, so self-membership is a universe inconsistency caught
 by the elaborator rather than a paradox to be excluded by axiom.

 It follows that categorical algebra now applies to categories
 themselves.  Binary products in [Cat] are the product categories
 ([Cat_Cartesian] in Instance/Cat/Cartesian.v), coproducts the
 disjoint-union categories (Instance/Cat/Cocartesian.v), the terminal
 and initial objects the one-object and empty categories ([Cat_Terminal]
 in Instance/One.v, [Cat_Initial] in Instance/Zero.v), and the
 exponentials the functor categories: [Cat_Closed] in
 Instance/Cat/Cartesian/Closed.v exhibits cartesian closure (detailed in
 Awodey, "Category Theory", 2010), with the transposition [exp_iso]
 currying a bifunctor into a functor-valued functor and evaluation the
 uncurried identity.  Read computationally, the exponentials are
 function objects one universe up, the picture behind higher-order
 manipulation of functors in typed functional programming (Milewski,
 "Natural Transformations", 2015) — though Cat is not locally cartesian
 closed (Wikipedia, "Category of small categories").  Within this file
 the weak convention yields concrete theorems: both legs of an
 isomorphism in [Cat] are faithful unconditionally
 ([Cat_Iso_to_Faithful], [Cat_Iso_from_Faithful]) and full under an
 explicit compatibility hypothesis between the unit and counit
 components ([Cat_Iso_to_Full], [Cat_Iso_from_Full]), the four
 assembled into [Isomorphism_FullyFaithful] by [Cat_Iso_FullyFaithful];
 the definitional bridge to equivalence of categories is
 [Equivalence_to_Cat_Iso] and [Cat_Iso_to_Equivalence] in
 Theory/Equivalence.v. 

 --------
 猫的来源以及它的用途

 SEP:    https://plato.stanford.edu/entries/category-theory/ 
 nLab:   https://ncatlab.org/nlab/show/2-category 
 nLab:   https://ncatlab.org/nlab/show/ETCCCat 是将范畴论应用于自身。下面的例子中的每一个成分在该学科的创始论文中已经隐含存在（Eilenberg 和 Mac Lane，《自然等价的通用理论》，Trans. Amer. Math. Soc. 58, 1945），然而论文中并未提到范畴的范畴的概念；作者将范畴视为支架——“范畴的整体概念本质上是辅助性的”，基本概念是函子和自然变换，并且“范畴作为函子的定义域和值域提供”（引自 Marquis，《范畴论》，斯坦福哲学百科全书）。下面的例子是使范畴本身成为对象的结构，从而可以将该理论的机制应用到理论自身。这个一范畴实例截断掉的维度有它自己的历史。自然变换的垂直和水平组合，以及 whiskering，最早出现在 Godement 的《Topologie algébrique et théorie des faisceaux》（1958）的附录中，为阿贝尔层的标准解析而发明；Godement 乘积就是本库在 Theory/Natural/Transformation.v 中的 [nat_hcompose]。严格 2 范畴归功于 Bénabou（"Catégories relatives"，1965）和 Maranda（"Formal categories"，1965）——而不是 Ehresmann，他 1963 年提出的双范畴是其灵感来源——而 Cat 是典型的 2 范畴（nLab，"2-category"）。这里的高阶单元存在于 Instance/Cat/Bicategory.v，其中同态范畴在定义上是 Instance/Fun.v 的函子范畴。Lawvere 提出将自我应用作为基础：类别的类别本身，用一阶术语公理化，将取代基于成员关系的集合论（《作为数学基础的类别的类别》，La Jolla 论文集，Springer 1966，继他1963年的论文之后）。J. R. Isbell 的评论（《数学评论》，1967）发现了一个核心结果的错误，没有修正达成共识，这一方案在很大程度上被拓扑理论取代，尽管近年来有继承者（Hughes 和 Miranda，arXiv:2403.03647，2025）。它处理的规模问题正是上方标题通过类型来解决的：全类别的类别会引发类似拉塞尔的悖论，经典方法通过小/大类别的区分或通过格罗滕迪克宇宙来避免。这个库并没有按照公理化的方式采用任一装置，而是在每个宇宙层级都有一个 [Cat]，每个都严格高于其自身的对象，因此自我成员关系是一种由精化器捕捉到的宇宙不一致，而不是需要通过公理排除的悖论。由此可得，范畴代数现在适用于范畴本身。在 [Cat] 中的二元积是积范畴（Instance/Cat/Cartesian.v 中的 [Cat_Cartesian]），余积是析合并范畴（Instance/Cat/Cocartesian.v），终对象和初对象分别是一对象范畴和空范畴（Instance/One.v 中的 [Cat_Terminal]，Instance/Zero.v 中的 [Cat_Initial]），指数对象是函子范畴：Instance/Cat/Cartesian/Closed.v 中的 [Cat_Closed] 展示了笛卡尔闭性（详见 Awodey, "Category Theory", 2010），其中转置 [exp_iso] 将双函子柯里化为函子值函子，评估为非柯里化的恒等函子。从计算的角度来看，指数是位于一个宇宙之上的函数对象，是类型化函数式编程中函子高阶操作背后的图景（Milewski，《自然变换》，2015）——尽管 Cat 不是局部笛卡尔闭的（维基百科，《小类的范畴》）。在此文件中，弱约定产生了具体定理：[Cat] 中同构的两条腿无条件都是忠实的（[Cat_Iso_to_Faithful], [Cat_Iso_from_Faithful]），并且在单位和余单位分量之间存在明确兼容性假设时是满的（[Cat_Iso_to_Full], [Cat_Iso_from_Full]），这四者被 [Cat_Iso_FullyFaithful] 组装成 [Isomorphism_FullyFaithful]；到范畴等价的定义性桥梁是 Theory/Equivalence.v 中的 [Equivalence_to_Cat_Iso] 和 [Cat_Iso_to_Equivalence]。
*)

#[export]
Instance Cat : Category := {
  obj     := Category;
  hom     := @Functor;
  homset  := @Functor_Setoid;
  id      := @Id;
  compose := @Compose;

  compose_respects := @Compose_respects;
  id_left          := @fun_equiv_id_left;
  id_right         := @fun_equiv_id_right;
  comp_assoc       := @fun_equiv_comp_assoc;
  comp_assoc_sym   := fun a b c d f g h =>
    symmetry (@fun_equiv_comp_assoc a b c d f g h)
}.

Record Isomorphism_FullyFaithful `(iso : C ≅ D) := {
  to_full       : Full (to iso);
  to_faithful   : Faithful (to iso);
  from_full     : Full (from iso);
  from_faithful : Faithful (from iso)
}.

#[export]
Instance Cat_Iso_to_Faithful `(iso : C ≅ D) : Faithful (to iso).
Proof.
  construct.
  rewrite <- id_left.
  rewrite <- id_right.
  symmetry.
  rewrite <- id_left.
  rewrite <- id_right.
  symmetry.
  spose (`2 (iso_from_to iso) x y) as X2.
  transitivity (`1 (iso_from_to iso) y ∘ (`1 (iso_from_to iso) y)⁻¹ ∘ f
                 ∘ (`1 (iso_from_to iso) x ∘ (`1 (iso_from_to iso) x)⁻¹)).
  { repeat apply compose_respects.
    - symmetry. apply (iso_to_from (`1 (iso_from_to iso) y)).
    - reflexivity.
    - symmetry. apply (iso_to_from (`1 (iso_from_to iso) x)).
  }
  transitivity (`1 (iso_from_to iso) y ∘ (`1 (iso_from_to iso) y)⁻¹ ∘ g
                 ∘ (`1 (iso_from_to iso) x ∘ (`1 (iso_from_to iso) x)⁻¹)).
  2: {
    repeat apply compose_respects.
    - apply (iso_to_from (`1 (iso_from_to iso) y)).
    - reflexivity.
    - apply (iso_to_from (`1 (iso_from_to iso) x)).
  }
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ f _).
  rewrite (comp_assoc _ g _).
  rewrite (comp_assoc (_ ∘ _) _ _).
  rewrite (comp_assoc (_ ∘ _) _ _).
  rewrite <- (X2 f).
  rewrite <- (X2 g).
  comp_left.
  comp_right.
  now apply (@fmap_respects D C iso⁻¹).
Qed.

#[export]
Instance Cat_Iso_from_Faithful `(iso : C ≅ D) : Faithful (from iso).
Proof.
  apply (Cat_Iso_to_Faithful (iso_sym iso)).
Qed.

Section Cat_Iso_FullyFaithful.

#[local] Obligation Tactic := simpl; intros.

Program Definition Cat_Iso_to_Full `(iso : C ≅ D) :
  let φ := to iso in
  let η x := to (`1 (iso_from_to iso) x) in
  let μ x := to (`1 (iso_to_from iso) x) in
  (∀ x, fmap[φ] (η x) ≈ μ (φ x)) ->
  Full (to iso) :=
  let φ := to iso in
  let η x := to (`1 (iso_from_to iso) x) in
  let μ x := to (`1 (iso_to_from iso) x) in
  fun H0 =>
    {| prefmap x y g := to (`1 (iso_from_to iso) y)
                           ∘ fmap[from iso] g
                           ∘ from (`1 (iso_from_to iso) x)
    |}.
Next Obligation.
  rewrite !fmap_comp.
  srewrite H0.
  srewrite (`2 (iso_to_from iso)).
  rewrite !comp_assoc.
  rewrite iso_to_from, id_left.
  srewrite_r H0.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  transitivity (g ∘ id).
  - comp_left. rewrite iso_to_from. apply fmap_id.
  - apply id_right.
Qed.

End Cat_Iso_FullyFaithful.

Corollary Cat_Iso_from_Full `(iso : C ≅ D) :
  let ψ := from iso in
  let η x := to (`1 (iso_from_to iso) x) in
  let μ x := to (`1 (iso_to_from iso) x) in
  (∀ x, fmap[ψ] (μ x) ≈ η (ψ x)) ->
  Full (from iso).
Proof.
  apply (Cat_Iso_to_Full (iso_sym iso)).
Qed.

Definition Cat_Iso_FullyFaithful `(iso : C ≅ D) :
  let φ := to iso in
  let ψ := from iso in
  let η x := to (`1 (iso_from_to iso) x) in
  let μ x := to (`1 (iso_to_from iso) x) in
  (∀ x, fmap[φ] (η x) ≈ μ (φ x)) ->
  (∀ x, fmap[ψ] (μ x) ≈ η (ψ x)) ->
  Isomorphism_FullyFaithful iso :=
  fun H0 H1 =>
  {| to_full       := Cat_Iso_to_Full iso H0
   ; from_full     := Cat_Iso_from_Full iso H1
   ; to_faithful   := Cat_Iso_to_Faithful iso
   ; from_faithful := Cat_Iso_from_Faithful iso
   |}.
