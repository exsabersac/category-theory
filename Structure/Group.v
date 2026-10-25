Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Monoidal.Heunen_Vicary.
Require Import Category.Structure.Monoid.

Generalizable All Variables.

(* * * Group objects in a cartesian monoidal category / * * 在笛卡尔幺半范畴中对对象进行分组 *)

(*
 nLab:      https://ncatlab.org/nlab/show/group+object
 Wikipedia: https://en.wikipedia.org/wiki/Group_object

 A group object in a category with finite products (here packaged as a
 cartesian monoidal category, where ⨂ is the product × and I is the terminal
 object 1) is a monoid object (mappend, mempty) on an object [grp] together
 with an inversion morphism [inverse : grp ~> grp] satisfying the two-sided
 inverse law. Writing μ = mappend, η = mempty, ι = inverse, ∆ for the
 diagonal grp ~> grp ⨂ grp and [eliminate] for the discard grp ~> I, the law
 is, as an equation of endomorphisms grp ~> grp:

 μ ∘ (ι ⨂ id) ∘ ∆ ≈ η ∘ eliminate ≈ μ ∘ (id ⨂ ι) ∘ ∆.

 The right-hand side η ∘ eliminate is the constant-at-the-unit endomorphism
 (nLab/Wikipedia's e_G = e ∘ !), NOT the unit object I: both inversion
 composites collapse to "send everything to the identity element". The
 associativity and two-sided unit laws come from the underlying monoid object
 ([groupobject_is_monoid]). This matches nLab/Wikipedia exactly; equivalently,
 [grp] is a group object iff each hom Hom(X, grp) is a group naturally in X.

 See Structure/Group/Proofs.v for the derived facts (uniqueness of inverses,
 the antihomomorphism law μ ∘ (ι ⨂ ι) ≈ ι ∘ μ ∘ braid, etc.). 

 --------
 nLab:       https://ncatlab.org/nlab/show/group+object
 维基百科:  https://en.wikipedia.org/wiki/Group_object

 在具有有限积的范畴中的群对象（这里打包为笛卡尔幺半群范畴，其中 ⨂ 是积 ×，I 是终对象 1）是对象 [grp] 上的幺半群对象（mappend, mempty），以及一个满足双边逆律的逆运算态射 [inverse : grp ~> grp]。写作 μ = mappend，η = mempty，ι = inverse，∆ 表示对角线 grp ~> grp ⨂ grp，以及 [eliminate] 表示丢弃 grp ~> I，该律作为群自同态 grp ~> grp 的方程为：

 μ ∘ (ι ⨂ id) ∘ ∆ ≈ η ∘ eliminate ≈ μ ∘ (id ⨂ ι) ∘ ∆.右侧的 η ∘ eliminate 是单位端的常数自同态（nLab/Wikipedia 的 e_G = e ∘ !），而不是单位对象 I：两个取逆复合体都会坍缩为“将所有元素发送到单位元”。结合律和双边单位律来自底层的幺半群对象（[groupobject_is_monoid]）。这与 nLab/Wikipedia 完全一致；等价地，[grp] 是群对象当且仅当每个 Hom(X, grp) 自然地在 X 中是一个群。

 请参见 Structure/Group/Proofs.v 获得派生事实（逆元的唯一性、反同态律 μ ∘ (ι ⨂ ι) ≈ ι ∘ μ ∘ braiding 等）。
*)

(*
 Where group objects come from, and what they are for

 nLab:  https://ncatlab.org/nlab/show/Eckmann-Hilton+argument
 nLab:  https://ncatlab.org/nlab/show/Hopf+algebra
 Paper: Eckmann, Hilton, "Group-Like Structures in General Categories I:
 Multiplications and Comultiplications", Mathematische Annalen
 145, 1962

 A group object answers the question of what a group is when elements
 are unavailable.  The definition transcribes the group axioms as
 commuting diagrams — multiplication, unit, and inversion as morphisms,
 with no reference to underlying elements — and it follows that the same
 diagrams, interpreted in different ambient categories, yield
 topological groups in Top, Lie groups in smooth manifolds, group
 schemes in schemes over a base, simplicial groups in simplicial sets,
 and strict 2-groups in Cat (nLab and Wikipedia, as cited in the header
 above).

 The systematic notion is due to Eckmann and Hilton (1962), who called
 such structures G-objects and reached them from homotopy theory: the
 natural group structure of the cohomology H^n(X; G) is explained by a
 group-like multiplication on the Eilenberg–MacLane space K(G, n) in the
 homotopy category, with axioms "formulated entirely in terms of the
 maps of the category".  The same paper contains the functor-of-points
 reading — a G-object structure on A endows each hom-set H(X, A) with a
 group structure, naturally in X, and its Theorem 4.3 shows that every
 natural family of group structures on hom-sets arises this way —
 together with a footnote, added in proof, connecting the observation
 to Grothendieck's representable functors.  Algebraic geometry took
 that reading as primary at the same moment: group schemes as group
 objects, presented equivalently as representable functors into Grp,
 are the subject of SGA 3 (Demazure, Grothendieck, "Schémas en
 groupes", Springer LNM 151–153, 1970, from the 1962–64 séminaire).
 Mac Lane canonized the notion as "Groups in Categories" (Categories
 for the Working Mathematician, 2nd ed., 1998, Section III.6), and
 Awodey opens his chapter on groups and categories with it (Category
 Theory, 2nd ed., 2010, Chapter 4).

 The notion also sees structure that ordinary group theory cannot.  A
 group object in Grp itself is an abelian group: the two
 multiplications satisfy an interchange law, and the Eckmann–Hilton
 argument (Eckmann, Hilton, Theorem 1.12 in "Structure maps in group
 theory", Fundamenta Mathematicae 50, 1961) forces them to coincide and
 to commute — the same argument shows that the homotopy groups π_n are
 abelian for n ≥ 2.  nLab further records a recognition principle: a
 monoid object is a group object exactly when its associativity square
 is a pullback, so once stated through limits, invertibility is a
 property of a monoid rather than extra structure.

 The [CartesianMonoidal] hypothesis is load-bearing.  Both inverse laws
 [left_inverse] and [right_inverse] are written in copy/discard
 vocabulary — ∆ copies the value, [eliminate] discards it — and a
 general monoidal category supplies neither, which is why
 [MonoidObject] in Structure/Monoid.v asks for no such hypothesis
 (Monad/Monoid.v internalizes it in the endofunctor category under
 composition, a tensor that is not cartesian) while [GroupObject] must.
 Replacing the missing diagonal by a chosen compatible comonoid
 structure turns [inverse] into an antipode and the inverse laws into
 the antipode axioms; the result is a Hopf monoid, in Vect a Hopf
 algebra (nLab), the structure first observed by Hopf in the homology
 of Lie groups (Hopf, "Über die Topologie der
 Gruppen-Mannigfaltigkeiten und ihre Verallgemeinerungen", Annals of
 Mathematics 42(1), 1941).  A commutative Hopf algebra is in turn the
 same as a group object in the opposite category of algebras — that is,
 in affine schemes (nLab) — and every commutative Hopf algebra over a
 field arises so from an affine group scheme, an antiequivalence of
 categories (Wikipedia, "Hopf algebra").  The copy/discard vocabulary
 for monoidal categories with a comonoid supply is developed in
 Structure/Monoidal/CopyDiscard.v, and the library's concrete contact
 with the antipode is the Hopf law between Z- and X-spiders in
 Instance/ZX.v. 

 --------
 群对象的来源及其用途

 nLab:   https://ncatlab.org/nlab/show/Eckmann-Hilton+argument 
 nLab:   https://ncatlab.org/nlab/show/Hopf+algebra 
 论文: Eckmann, Hilton, "一般范畴中的类群结构 I: 乘法与余乘法", 数学年刊 145, 1962

 群对象回答了在没有元素可用时群是什么的问题。定义将群的公理转录为交换图——将乘法、单位元和逆元作为态射，没有涉及底层元素——因此，同样的图在不同的环境范畴中解释时，会产生 Top 中的拓扑群、光滑流形中的李群、基上丛范畴中的群示性、单纯集合中的单纯群，以及 Cat 中的严格 2-群（如上标题所引用的 nLab 和维基百科）。系统概念归功于 Eckmann 和 Hilton（1962），他们称这种结构为 G-对象，并从同伦理论中得出这一概念：通过在同伦范畴中对 Eilenberg–MacLane 空间 K(G, n) 定义类似群的乘法，可以解释上同调 H^n(X; G) 的自然群结构，该群的公理“完全用范畴中的映射来表述”。同一篇论文还包含了点函子（functor-of-points）的解读——在 A 上的 G-对象结构赋予每个同集 H(X, A) 一个群结构，并且在 X 中是自然的，其定理 4.3 表明，同集上的每个自然的群结构族都是以这种方式产生的——文章还附有一条校订中加入的脚注，将这一观察与 Grothendieck 的可表示函子联系起来。代数几何在同一时刻将这种理解作为主要观点：群方案作为群对象，可以等价地表示为可表示的函子到Grp，是SGA 3的研究对象（Demazure、Grothendieck，《Schémas en groupes》，Springer LNM 151–153，1970，来自1962–64年的研讨会）。Mac Lane 将这一概念作为“范畴中的群”确立下来（《为工作中的数学家讲解的范畴论》，第2版，1998年，第III.6节），Awodey 在他的关于群与范畴的一章中以此开篇（《范畴论》，第2版，2010年，第4章）。这个概念还看到了普通群论无法看到的结构。在 Grp 中的一个群对象本身是一个阿贝尔群：这两种乘法满足交换律，而 Eckmann–Hilton 论证（Eckmann, Hilton, "群论中的结构映射", Fundamenta Mathematicae 50, 1961 年，第 1.12 定理）迫使它们相同并且交换——同样的论证表明，当 n ≥ 2 时，同伦群 π_n 是阿贝尔群。nLab 进一步记录了一个识别原理：一个幺半群对象恰好是群对象，当且仅当它的结合律平方是一个拉回图，所以一旦通过极限来表达，可逆性是幺半群的一种性质，而不是额外结构。[CartesianMonoidal] 假设是承重的。两个逆律 [left_inverse] 和 [right_inverse] 使用复制/丢弃的词汇来书写——∆ 复制值，[eliminate] 丢弃它——而一般的幺半范畴既不提供这两者，这就是为什么 Structure/Monoid.v 中的 [MonoidObject] 不要求这样的假设（Monad/Monoid.v 最终在复合下的自函子范畴内将其内在化，这是一个非笛卡尔的张量），而 [GroupObject] 必须要求。通过用选定的兼容余单元结构替换缺失的对角线，将 [inverse] 变为一个对偶并将逆律变为对偶公理；结果是一个 Hopf 单子，在 Vect 中是一个 Hopf 代数（nLab），这一结构最早由 Hopf 在李群的同调中观察到（Hopf，“Über die Topologie der Gruppen-Mannigfaltigkeiten und ihre Verallgemeinerungen”，Annals of Mathematics 42(1), 1941）。交换 Hopf 代数反过来与代数的对偶范畴中的群对象相同——也就是说，在仿射簇中（nLab）——并且每个定义在域上的交换 Hopf 代数都由一个仿射群簇产生，这是一个范畴的反等价（Wikipedia，“Hopf algebra”）。带有余单子的单范畴的复制/丢弃词汇在 Structure/Monoidal/CopyDiscard.v 中进行了开发，并且该库与反子（antipode）的具体联系是在 Instance/ZX.v 中 Z- 和 X- 蜘蛛之间的 Hopf 定律。
*)

Section GroupObject.

Context `{@CartesianMonoidal C}.

Class GroupObject (grp : C) := {
  (*
 Underlying monoid object: supplies mappend (μ), mempty (η) and the
 associativity + two-sided unit laws. 

 --------
 底层幺半群对象：提供 mappend (μ)、mempty (η) 以及结合律 + 双边单位律。
*)
  groupobject_is_monoid : MonoidObject grp;
  (* Inversion / antipode ι : grp ~> grp. / 反演 / 对顶 ι：群 ~> 群。 *)
  inverse : grp ~> grp;

  (*
 Left inverse: μ ∘ (ι ⨂ id) ∘ ∆ ≈ η ∘ eliminate (the constant-identity
 endomorphism). Copy g with ∆, invert the left copy, then multiply. 

 --------
 左逆元：μ ∘ (ι ⨂ id) ∘ ∆ ≈ η ∘ 消去（常数恒等自同态）。用 ∆ 复制 g，反转左边的复制，然后相乘。
*)
  left_inverse : mappend ∘ inverse ⨂ id ∘ ∆ grp ≈ mempty ∘ eliminate;

  (*
 Right inverse: μ ∘ (id ⨂ ι) ∘ ∆ ≈ η ∘ eliminate, dually inverting the
 right copy. 

 --------
 右逆：μ ∘ (id ⨂ ι) ∘ ∆ ≈ η ∘ 消去，对应地逆转右复制。
*)
  right_inverse : mappend ∘ id ⨂ inverse ∘ ∆ grp ≈ mempty ∘ eliminate;
}.
#[export] Existing Instance groupobject_is_monoid.

Coercion groupobject_is_monoid : GroupObject >-> MonoidObject.

End GroupObject.

(* Projection to the inversion morphism ι of a given group object [G]. / 映射到给定群对象 [G] 的逆运算同态 ι。 *)
Notation "'inverse' [ G ]" := (@inverse _ _ G _)
  (at level 9, format "inverse [ G ]") : category_scope.
