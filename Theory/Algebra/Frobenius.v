Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Comonoid.

Generalizable All Variables.

(**
* Frobenius algebras in a monoidal category

    nLab:      https://ncatlab.org/nlab/show/Frobenius+algebra
    Wikipedia: https://en.wikipedia.org/wiki/Frobenius_algebra

    A Frobenius algebra on [X] is a monoid [(X, mu, eta)] and a comonoid
    [(X, delta, epsilon)] on the same object, satisfying the Frobenius
    compatibility law:

        (id ⨂ mu) ∘ (delta ⨂ id) ≈ delta ∘ mu ≈ (mu ⨂ id) ∘ (id ⨂ delta)

    (up to suitable insertions of the tensor associator).  Per nLab, the two
    equalities collapse into the single condition equating the outer
    composites, [(id ⨂ mu) ∘ (delta ⨂ id) ≈ (mu ⨂ id) ∘ (id ⨂ delta)], with
    the middle [delta ∘ mu] recovered using (co)unitality; together they
    encode that [delta] is a bimodule map.

    To keep the statement first-order in the tensor associator (rather than
    awkward two-sided compositions) we follow the standard nLab convention
    and rephrase as

        (mu ⨂ id) ∘ α⁻¹ ∘ (id ⨂ delta) ≈ delta ∘ mu

    and dually

        (id ⨂ mu) ∘ α ∘ (delta ⨂ id) ≈ delta ∘ mu.

    Together these two axioms recover the standard double Frobenius equation.

--------
* 单体范畴中的弗罗贝尼乌斯代数

nLab：https://ncatlab.org/nlab/show/Frobenius+algebra
维基百科：https://en.wikipedia.org/wiki/Frobenius_algebra

在 [X] 上的 Frobenius 代数是同一对象上的一个幺半群 [(X, mu, eta)] 和一个余半群 [(X, delta, epsilon)]，并满足 Frobenius 兼容律：

(id ⨂ mu) ∘ (delta ⨂ id) ≈ delta ∘ mu ≈ (mu ⨂ id) ∘ (id ⨂ delta)

(适当插入张量结合子)。根据 nLab，这两个等式合并为一个条件，即将外部复合 [(id ⨂ mu) ∘ (delta ⨂ id) ≈ (mu ⨂ id) ∘ (id ⨂ delta)] 与通过 (co) 单位性恢复的中间 [delta ∘ mu] 相等；它们共同编码了 [delta] 是一个双模态映射。

为了使该陈述保持在张量结合子的一阶（而不是笨拙的双边组合），我们遵循标准的 nLab 约定并重新表述为

(mu ⨂ id) ∘ α⁻¹ ∘ (id ⨂ delta) ≈ delta ∘ mu

并且双重地

(id ⨂ mu) ∘ α ∘ (delta ⨂ id) ≈ delta ∘ mu.

这两个公理一起恢复了标准的双弗罗贝尼乌斯方程。
*)

(*
Where Frobenius algebras come from, and what they are for

   Book:  Kock, "Frobenius Algebras and 2D Topological Quantum Field
          Theories", LMS Student Texts 59, CUP 2003;
          https://mat.uab.cat/~kock/TQFT.html
   Paper: Carboni, Walters, "Cartesian bicategories I", JPAA 49, 1987
   Paper: Lack, "Composing PROPs", Theory Appl. Categ. 13(9), 2004

   The classical objects predate the categorical definition by most of a
   century.  Frobenius studied finite-dimensional hypercomplex algebras in
   "Theorie der hyperkomplexen Größen" (1903); systematic study — and the
   name — came with Brauer and Nesbitt ("On the regular representations of
   algebras", Proc. Nat. Acad. Sci. USA 1937), and Nakayama opened the
   duality theory ("On Frobeniusean algebras I, II", Ann. of Math. 1939,
   1941).  Classically a Frobenius algebra is a finite-dimensional unital
   associative algebra with a nondegenerate bilinear pairing that
   associates with the multiplication; group algebras of finite groups
   are standard examples.  The diagrammatic form recorded in this file
   is younger.  Per Kock's account, Lawvere knew the categorical
   characterization by 1967 and published an equational version in
   "Ordinal sums and equational doctrines" (1969), yet the first explicit
   appearance of the Frobenius equation in print is the "discreteness
   axiom" of Carboni and Walters (1987), recognized only later as
   Lawvere's condition.  Over vector spaces the two definitions agree: a
   counit for which [epsilon ∘ mu] is a nondegenerate pairing identifies
   the algebra with its linear dual and thereby forces finite dimension
   (per the nLab page cited in the header above).

   The law is one of the two canonical, inequivalent ways a monoid and a
   comonoid on the same object can interact.  The bialgebra law makes
   [delta] a homomorphism of monoids; the Frobenius law instead makes the
   pairing [epsilon ∘ mu] and the copairing [delta ∘ eta] exhibit [X] as
   its own dual.  Composing the PROPs for commutative monoids and
   cocommutative comonoids by the two available distributive laws yields
   Cospan(FinSet) on the Frobenius side and Span(FinSet) on the bialgebra
   side (Lack 2004).  The self-duality reading is realized in-tree:
   Structure/Monoidal/CompactClosed.v equips every object of a hypergraph
   category with itself as dual, and the snake identities there follow
   from the Frobenius law alone, without appeal to specialness.

   Diagrammatically the law is a principle of topological invariance: both
   sides of the Frobenius equation are the same surface up to deformation.
   Pushed to its conclusion this becomes the classification of
   two-dimensional topological quantum field theories by commutative
   Frobenius algebras, stated as a folk theorem in Dijkgraaf's thesis ("A
   geometrical approach to two-dimensional Conformal Field Theory",
   Utrecht 1989) and proved by Abrams ("Two-dimensional topological
   quantum field theories and Frobenius algebras", J. Knot Theory
   Ramifications 1996); Kock's book is the standard treatment, and the
   commutative case where the correspondence lives is
   Theory/Algebra/CommutativeFrobenius.v.

   The computational readings are genuine.  In categorical quantum
   mechanics a commutative dagger-Frobenius monoid in finite-dimensional
   Hilbert spaces is exactly an orthogonal basis, orthonormal exactly when
   special: the comultiplication copies basis vectors and the counit
   deletes them, axiomatizing classical — copyable, deletable — data
   inside a quantum universe (Coecke, Pavlovic, Vicary, "A new description
   of orthogonal bases", arXiv:0810.0812, 2008).  In network theory
   Frobenius structure is the algebra of interconnection: Cospan(FinSet)
   is the PROP for special commutative Frobenius monoids (Lack 2004;
   Construction/Cospan/SCFA.v builds the canonical instance on cospans),
   corelations the PROP for extraspecial ones (Coya, Fong, "Corelations
   are the prop for extraspecial commutative Frobenius monoids", TAC 32,
   2017), and a hypergraph category carries the structure on every object
   (Structure/Monoidal/Hypergraph.v).  Both readings meet in the spider
   calculus: in the special commutative case a connected composite of
   [mu], [eta], [delta] and [epsilon] collapses to a canonical spider, the
   fusion rule of the ZX-calculus (Coecke, Duncan, "Interacting Quantum
   Observables", New J. Phys. 13, 2011; see Instance/ZX.v), and
   Structure/Monoidal/Hypergraph/Spider.v restates [frob_law_left] and
   [frob_law_right] as [spider_frobenius] and [spider_frobenius_sym].

   Downstream, Theory/Algebra/CommutativeFrobenius.v adds compatibility
   with the braiding and Theory/Algebra/SpecialCommutativeFrobenius.v the
   special law [mu_delta_id].  A no-go theorem delimits the whole subject:
   Structure/Monoidal/Collapse.v proves that a Frobenius object in a
   semicartesian monoidal category is isomorphic to the unit, so the
   notion trivializes over a cartesian tensor and carries content only
   where the tensor is resource-sensitive.

--------
弗罗贝尼乌斯代数的来源以及它们的用途

书籍：Kock，《Frobenius代数与二维拓扑量子场论》，LMS学生教材59，CUP 2003；
论文：Carboni, Walters，《笛卡尔双范畴 I》，JPAA 49, 1987
论文：Lack，《PROPs的组合》，Theory Appl. Categ. 13(9), 2004

经典对象早于范畴定义近一个世纪。Frobenius 在《超复数大小理论》(Theorie der hyperkomplexen Grössen, 1903) 中研究了有限维超复数代数；系统研究——以及名称——则出现在 Brauer 和 Nesbitt 的工作中（"论代数的正规表示"，美国国家科学院院刊, 1937），而 Nakayama 开启了对偶理论（"关于 Frobeniusean 代数 I, II"，数学年刊, 1939, 1941）。按经典定义，Frobenius 代数是有限维带单位元的结合代数，具有与乘法关联的非退化双线性配对；有限群的群代数是标准例子。本文件中记录的图示形式则较晚出现。
根据Coq的说法，Lawvere 在 1967 年就已经知道了该分类特征，并在《Ordinal sums and equational doctrines》（1969）中发表了一个方程版本，然而，Frobenius 方程首次明确出现在文献中是 Carboni 和 Walters（1987）的“离散性公理”，后来才被认识为 Lawvere 的条件。在向量空间上，这两个定义是一致的：对于 [epsilon ∘ mu] 是非退化配对的余单位，将该代数与其线性对偶相对应，从而强制其为有限维（根据上文标题中引用的 nLab 页面）。

法律是单子和余单子在同一对象上相互作用的两种规范但不等效的方式之一。双代数定律使 [delta] 成为单子的同态；而弗罗贝尼斯定律则使配对 [epsilon ∘ mu] 和共配对 [delta ∘ eta] 表现出 [X] 作为它自身的对偶。通过两种可用的分配律将交换单子和共交换余单子的 PROPs 组合起来，在弗罗贝尼斯方向上得到 Cospan(FinSet)，在双代数方向上得到 Span(FinSet)（Lack 2004）。自对偶的理解在树结构中得以实现：Structure/Monoidal/CompactClosed.v 为超图范畴的每个对象装备自己作为对偶，并且那里蛇形恒等式仅依赖弗罗贝尼斯定律即可推出，而无需调用特殊性。

从图示上看，该定律是拓扑不变性的一个原理：Frobenius方程的两边是相同的曲面，仅在形变上有所不同。 推到极致，这就变成了通过交换Frobenius代数对二维拓扑量子场论进行分类的问题，这在Dijkgraaf的论文（《二维共形场论的几何方法》，乌得勒支，1989）中被作为一个民间定理提出，并由Abrams（《二维拓扑量子场论与Frobenius代数》，《结理论及其分支》，1996）证明；Kock的书是标准的处理方法，而交换情形，即对应关系所存在的情形，则是Theory/Algebra/CommutativeFrobenius.v。

计算结果是真实的。在范畴量子力学中，有限维希尔伯特空间中的可交换匕首-弗罗贝尼乌斯幺半群正好是一个正交基，只有在特殊情况下才是标准正交基：余乘法复制基向量，余单位删除它们，从而在量子宇宙中公理化了经典——可复制、可删除——数据（Coecke, Pavlovic, Vicary, “A new description of orthogonal bases”, arXiv:0810.0812, 2008）。
在网络理论中，Frobenius 结构是互连的代数：Cospan(FinSet) 是特殊交换 Frobenius 单子的 PROP（Lack 2004；Construction/Cospan/SCFA.v 构建了 cospans 上的规范实例），corelations 是额外特殊单子的 PROP（Coya, Fong，“Corelations are the prop for extraspecial commutative Frobenius monoids”，TAC 32，2017），而一个超图范畴在每个对象上都承载该结构（Structure/Monoidal/Hypergraph.v）。这两种解释在蜘蛛演算中相遇：在特殊交换的情况下，[mu]、[eta]、[delta] 和 [epsilon] 的连通复合将收缩为一个规范蜘蛛，即 ZX 演算的融合规则（Coecke, Duncan，“Interacting Quantum Observables”，New J. Phys.）。
2011年13日；参见 Instance/ZX.v)，并且 Structure/Monoidal/Hypergraph/Spider.v 将 [frob_law_left] 和 [frob_law_right] 重述为 [spider_frobenius] 和 [spider_frobenius_sym]。

下游，Theory/Algebra/CommutativeFrobenius.v 增加了与编织的兼容性，Theory/Algebra/SpecialCommutativeFrobenius.v 增加了特殊法则 [mu_delta_id]。一个不可行定理界定了整个主题：Structure/Monoidal/Collapse.v 证明在半笛卡尔单范畴中的 Frobenius 对象同构于单位，所以这个概念在笛卡尔张量下变得平凡，并且只有在张量对资源敏感的地方才有实际内容。
*)

Section Frobenius.

Context {C : Category}.
Context `{M : @Monoidal C}.

Class Frobenius (X : C) : Type := {
  frob_monoid   : Monoid X;     (* the multiplication [mu] and unit [eta] / 乘法 [mu] 和单位 [eta] *)
  frob_comonoid : Comonoid X;   (* the comultiplication [delta] and counit [epsilon] / 余乘法 [delta] 和余单位 [epsilon] *)

  (* Frobenius law, left form: [(mu ⨂ id) ∘ α⁻¹ ∘ (id ⨂ delta) ≈ delta ∘ mu]. / 弗罗贝尼乌斯定律，左形式：[(mu ⨂ id) ∘ α⁻¹ ∘ (id ⨂ delta) ≈ delta ∘ mu]。 *)
  frob_law_left :
    bimap (@mu _ _ _ frob_monoid) id[X]
      ∘ from (@tensor_assoc C M X X X)
      ∘ bimap id[X] (@delta _ _ _ frob_comonoid)
    ≈ (@delta _ _ _ frob_comonoid) ∘ (@mu _ _ _ frob_monoid);

  (* Frobenius law, right form: [(id ⨂ mu) ∘ α ∘ (delta ⨂ id) ≈ delta ∘ mu]. / 弗罗贝尼乌斯定律，正确形式：[(id ⨂ mu) ∘ α ∘ (delta ⨂ id) ≈ delta ∘ mu]。 *)
  frob_law_right :
    bimap id[X] (@mu _ _ _ frob_monoid)
      ∘ to (@tensor_assoc C M X X X)
      ∘ bimap (@delta _ _ _ frob_comonoid) id[X]
    ≈ (@delta _ _ _ frob_comonoid) ∘ (@mu _ _ _ frob_monoid)
}.
#[export] Existing Instance frob_monoid.
#[export] Existing Instance frob_comonoid.

Coercion frob_monoid   : Frobenius >-> Monoid.
Coercion frob_comonoid : Frobenius >-> Comonoid.

End Frobenius.

Arguments frob_monoid   {C M X _}.
Arguments frob_comonoid {C M X _}.

(**
** Flat projections

    Convenience aliases paralleling [scfa_mu] / [scfa_eta] /
    [scfa_delta] / [scfa_epsilon] (in
    [Theory/Algebra/SpecialCommutativeFrobenius.v]) and [cfrob_*]
    (in [Theory/Algebra/CommutativeFrobenius.v]).  Project a
    [Frobenius X] to its underlying [mu] / [eta] / [delta] /
    [epsilon] without going through [frob_monoid] / [frob_comonoid]
    one-by-one.

    The instance arguments are explicit so downstream code can
    write e.g. [frob_mu F] unambiguously.

--------
** 平面投影

    便利别名，与 [scfa_mu] / [scfa_eta] / [scfa_delta] / [scfa_epsilon] （在 [Theory/Algebra/SpecialCommutativeFrobenius.v] 中）以及 [cfrob_*] （在 [Theory/Algebra/CommutativeFrobenius.v] 中）平行。将 [Frobenius X] 投影到其基础的 [mu] / [eta] / [delta] / [epsilon]，而无需逐一经过 [frob_monoid] / [frob_comonoid]。

    实例参数是显式的，因此下游代码可以明确无歧义地编写例如 [frob_mu F]。
*)

Section FrobeniusProjections.

Context {C : Category}.
Context `{M : @Monoidal C}.

Definition frob_mu {X : C} (F : Frobenius X) : (X ⨂ X)%object ~> X :=
  @mu _ _ _ (frob_monoid (X := X)).

Definition frob_eta {X : C} (F : Frobenius X) : @I _ _ ~> X :=
  @eta _ _ _ (frob_monoid (X := X)).

Definition frob_delta {X : C} (F : Frobenius X) : X ~> (X ⨂ X)%object :=
  @delta _ _ _ (frob_comonoid (X := X)).

Definition frob_epsilon {X : C} (F : Frobenius X) : X ~> @I _ _ :=
  @epsilon _ _ _ (frob_comonoid (X := X)).

End FrobeniusProjections.

Arguments frob_mu      {C M X} F.
Arguments frob_eta     {C M X} F.
Arguments frob_delta   {C M X} F.
Arguments frob_epsilon {C M X} F.
