Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Import Category.Functor.Bifunctor.
Require Export Category.Structure.Monoidal.
Require Export Category.Structure.Monoidal.Naturality.

Generalizable All Variables.

Section BraidedMonoidal.

Context {C : Category}.

(** Braided monoidal category. / 编织单体范畴。 *)

(*
 nLab: https://ncatlab.org/nlab/show/braided+monoidal+category
 Wikipedia: https://en.wikipedia.org/wiki/Braided_monoidal_category

 A braided monoidal category is a monoidal category equipped with a natural
 isomorphism, the braiding,

 beta : x ⊗ y ≅ y ⊗ x              ([braid]),

 that is compatible with the associator (alpha = [tensor_assoc]) by way of
 two hexagon identities. Writing the equations in this library's notation
 (composition reads right to left), they are

 alpha ∘ beta ∘ alpha
 = (id ⨂ beta) ∘ alpha ∘ (beta ⨂ id)
 ([hexagon_identity]),

 alpha⁻¹ ∘ beta ∘ alpha⁻¹
 = (beta ⨂ id) ∘ alpha⁻¹ ∘ (id ⨂ beta)
 ([hexagon_identity_sym]),

 where on the upper path the middle [braid] is the braiding of one object
 past a whole tensor product (B_{x, y⊗z} and B_{x⊗y, z} respectively). The
 first hexagon braids x past y ⊗ z; the second braids x ⊗ y past z, and uses
 the inverse associator throughout. Both follow the nLab orientation; the
 coherence consequence on triple tensors is the Yang-Baxter equation proved
 below. Adding the further axiom beta ∘ beta = id yields a symmetric
 monoidal category (see Structure/Monoidal/Symmetric.v).

 Only the braiding's naturality is asked for: the two hexagons are equations
 between fixed composites and so need no separate respectfulness. 

 --------
 nLab：https://ncatlab.org/nlab/show/braided+monoidal+category 
 维基百科：https://en.wikipedia.org/wiki/Braided_monoidal_category

 编织单数范畴（braided monoidal category）是一个单数范畴，配备了一个自然同构，即编织（braiding），

 beta : x ⊗ y ≅ y ⊗ x              ([braid])，

 它通过两个六边形恒等式与结合子（associator，alpha = [tensor_assoc]）兼容。在本库的符号表示法中（复合从右到左读），它们为：

 alpha ∘ beta ∘ alpha
 = (id ⨂ beta) ∘ alpha ∘ (beta ⨂ id)
 ([hexagon_identity])，

 alpha⁻¹ ∘ beta ∘ alpha⁻¹
 = (beta ⨂ id) ∘ alpha⁻¹ ∘ (id ⨂ beta)
 ([hexagon_identity_sym])，在上方路径中，中间的 [braid] 是将一个对象穿过整个张量积的编织（分别是 B_{x, y⊗z} 和 B_{x⊗y, z}）。第一个六边形将 x 穿过 y ⊗ z；第二个将 x ⊗ y 穿过 z，并在整个过程中使用逆结合子。两者都遵循 nLab 的方向；在三重张量上的相干性结果是下文证明的杨-巴克斯特方程。加入进一步公理 beta ∘ beta = id 可以得到一个对称单体范畴（参见 Structure/Monoidal/Symmetric.v）。

 这里只要求编织的自然性：两个六边形是固定复合之间的方程，因此不需要单独考虑守恒性。
*)

(*
 Where the braiding comes from, and what it is for

 nLab:  https://ncatlab.org/nlab/show/Yang-Baxter+equation
 nLab:  https://ncatlab.org/nlab/show/periodic+table
 Paper: Joyal, Street, "Braided tensor categories", Advances in
 Mathematics 102, 1993

 Braided monoidal categories were introduced by Joyal and Street in a
 pair of Macquarie Mathematics Reports (85-0067, 1985; 86-0081, 1986),
 revised as the paper above, and were arrived at independently by
 Lawrence Breen ("Une lettre à P. Deligne au sujet des 2-catégories
 tressées", 1988).  The name points to Artin's braid groups (Artin,
 "Theorie der Zöpfe", Abh. Math. Sem. Univ. Hamburg 4, 1925; "Theory of
 Braids", Annals of Mathematics 48, 1947): on n-fold tensor powers the
 coherence isomorphisms of a braided category act through the braid
 group B_n rather than the symmetric group S_n, and this is precisely
 what separates the notion from symmetry.  Coherence is accordingly
 conditional, unlike Mac Lane's for plain monoidal categories: a diagram
 built from associators, unitors and braidings commutes whenever both
 sides have the same underlying braid, and in the free braided monoidal
 category only then (Joyal-Street 1993).  Distinct braids can therefore
 name genuinely distinct morphisms — the double braiding
 [braid] ∘ [braid] need not be the identity, and requiring it to be so
 collapses B_n back onto S_n.

 The definition answers a precise question: what commutativity remains
 when the swap is an isomorphism that remembers how the swap was
 performed?  The hexagons are exactly compatibility with the associator
 — braiding one object past a whole tensor product agrees with braiding
 it past the two factors in adjacent steps — and from them together
 with [braid_natural] alone follows [Yang_Baxter_equation], the
 categorical form of Artin's braid relation on adjacent generators and
 of the third Reidemeister move.  That equation predates the
 categorical notion, arising twice in physics: in Yang's
 one-dimensional many-body problem (Physical Review Letters 19, 1967)
 and as the star-triangle relation of Baxter's eight-vertex model
 (Annals of Physics 70, 1972); the joint name is due to Faddeev in the
 late 1970s.  In the periodic table of k-tuply monoidal n-categories
 (Baez, Dolan, "Higher-dimensional algebra and topological quantum
 field theory", 1995), braided monoidal sits at k = 2, n = 1: two
 compatible monoidal structures on one category, merged by the
 Eckmann-Hilton argument into a single tensor carrying a braiding,
 while a third structure already stabilizes at symmetric.  Braided
 monoidal is thus the maximally noncommutative commutativity — the last
 stop before stabilization.

 The utility runs through algebra, topology and physics.  Modules over
 a quasitriangular Hopf algebra — Drinfeld's quantum groups (Drinfeld,
 "Quantum Groups", Proceedings of the ICM, Berkeley 1986) — form a
 braided category whose braiding is induced by the universal R-matrix;
 ribbon categories built on braidings yield the functorial
 Reshetikhin-Turaev invariants of links and 3-manifolds, the Jones
 polynomial among them (Shum, "Tortile tensor categories", J. Pure
 Appl. Algebra 93, 1994; Reshetikhin, Turaev, "Invariants of
 3-manifolds via link polynomials and quantum groups", Inventiones
 Mathematicae 103, 1991).  In topological quantum computation the
 exchange statistics of anyons are braid-group representations, so a
 braided fusion category models the physics — tensor as fusion, [braid]
 as particle exchange — and quantum gates are braids (Kitaev,
 "Fault-tolerant quantum computation by anyons", Annals of Physics 303,
 2003; Freedman, Kitaev, Larsen, Wang, "Topological quantum
 computation", Bulletin of the AMS 40, 2003).

 Within the library the reading is concrete.  The free PROP realizes
 the braiding as the literal block crossing [T_braid] of one wire
 bundle past another (Construction/PROP/Braided.v); the Drinfeld centre
 produces braided structure from any monoidal category
 ([Drinfeld_Braided] in Structure/Monoidal/Drinfeld.v); the cartesian
 swap gives the degenerate case ([CC_BraidedMonoidal] in
 Structure/Monoidal/Internal/Product.v); Structure/Monoidal/Symmetric.v
 adds the involution [braid_invol], under which either hexagon yields
 the other; Structure/Monoidal/Balanced.v adds a twist compatible with
 the double braiding — given duals that respect the twist, the ribbon
 notion behind Shum's theorem; for a monoidal functor, being braided is
 a property rather than structure ([BraidedMonoidalFunctor] in
 Functor/Structure/Monoidal/Braided.v); and Structure/Monoidal/Closed.v
 derives [flip] for internal homs from [BraidedMonoidal] alone, no
 symmetry required. 

 --------
 编织的来源及其用途

 nLab:   https://ncatlab.org/nlab/show/Yang-Baxter+equation 
 nLab:   https://ncatlab.org/nlab/show/periodic+table 
 论文: Joyal, Street, 《编织张量范畴》，《数学进展》102, 1993编织单体范畴由 Joyal 和 Street 在麦考瑞数学报告的一对文献中引入（85-0067, 1985；86-0081, 1986），后来修订为上述论文，并由 Lawrence Breen 独立提出（"Une lettre à P. Deligne au sujet des 2-catégories tressées", 1988）。其名称指向 Artin 的编织群（Artin, "Zöpfe 理论", Abh. Math. Sem. Univ. Hamburg 4, 1925; "编织理论", Annals of Mathematics 48, 1947）：在 n 次张量幂上，编织范畴的相干同构通过编织群 B_n 而非对称群 S_n 起作用，这正是它与对称性的概念区别所在。因此，连贯性是有条件的，不像麦克莱恩在普通单体范畴中的情况：由结合子、单位元子和编织子构建的图表，在双方具有相同的基础编织时才是可交换的，而在自由编织单体范畴中，只有这种情况下才是可交换的（Joyal-Street 1993）。因此，不同的编织可以表示真正不同的态射——双编织 [braid] ∘ [braid] 不一定是恒等映射，而要求它是恒等映射会将 B_n 重回压缩到 S_n。该定义回答了一个精确的问题：当交换是一个保持交换方式的同构时，还剩下什么可交换性？六边形方程正好对应于与结合子的兼容性——将一个对象在一个整体张量积中缠绕，与将它按相邻步骤穿过两个因子是相同的——从它们以及 [braid_natural] 本身，可以得出 [Yang_Baxter_equation]，即 Artin 关于相邻生成元的编织关系以及第三条 Reidemeister 变换的范畴形式。该方程早于范畴概念，在物理学中出现过两次：在杨的［一维多体问题］（Physical Review Letters 19, 1967）中，以及巴克斯特八顶点模型的星-三角关系中（Annals of Physics 70, 1972）；联合命名归功于 1970 年代末的 Faddeev。在 k-重单体 n-范畴的元素周期表中（Baez, Dolan, "高维代数与拓扑量子场论"，1995），编织单体位于 k = 2, n = 1：在一个范畴上有两个兼容的单体结构，通过 Eckmann-Hilton 论证合并为一个带编织的张量，而第三个结构已经在对称性上稳定。因此，编织单体是最大限度的非交换交换性——在稳定之前的最后一站。该工具涉及代数、拓扑学和物理学。准三角霍普夫代数上的模 — Drinfeld 的量子群（Drinfeld, “量子群”，ICM Berkeley 1986 论文集）— 构成一个编织范畴，其编织由普遍 R 矩阵引出；在编织基础上建立的缎带范畴产生链和三维流形的函子 Reshetikhin-Turaev 不变量，其中包括 Jones 多项式（Shum, “缠结张量范畴”, J. Pure Appl. Algebra 93, 1994；Reshetikhin, Turaev, “通过链多项式和量子群得到三维流形的不变量”, Inventiones Mathematicae 103, 1991）。在拓扑量子计算中，任意子的交换统计是编结群的表示，因此编结融合范畴可以模拟物理——将张量表示为融合，将[braid]表示为粒子交换——量子门则是编结（Kitaev，"任意子容错量子计算"，《物理年刊》303, 2003；Freedman, Kitaev, Larsen, Wang, "拓扑量子计算"，《美国数学学会公报》40, 2003）。在图书馆里，阅读是具体的。自由PROP实现了编织作为一个导线束越过另一个的字面块交叉 [T_braid]（Construction/PROP/Braided.v）；Drinfeld中心从任何单体范畴生成编织结构（ [Drinfeld_Braided] 在 Structure/Monoidal/Drinfeld.v）；笛卡尔交换给出了退化情况（ [CC_BraidedMonoidal] 在 Structure/Monoidal/Internal/Product.v）；Structure/Monoidal/Symmetric.v 添加了反演 [braid_invol]，在其下任意六边形定律都能得到另一条；Structure/Monoidal/Balanced.v 添加了与二重编织兼容的扭转——给定遵循扭转的对偶，体现了 Shum 定理背后的丝带概念；对于单体函子，成为编织是一个性质而非结构（ [BraidedMonoidalFunctor] 在 Functor/Structure/Monoidal/Braided.v）；Structure/Monoidal/Closed.v 对 inte 推导了 [flip]。仅来自 [BraidedMonoidal] 的 rnal 同源物，不需要对称性。
*)

Class BraidedMonoidal := {
  braided_is_monoidal : @Monoidal C;

  (* The braiding beta : x ⊗ y ≅ y ⊗ x, natural in both arguments. / 编织 β：x ⊗ y ≅ y ⊗ x，对两个参数都是自然的。 *)
  braid {x y} : x ⨂ y ~> y ⨂ x;
  braid_natural : natural (@braid);

  (* First hexagon: braiding x past the tensor product y ⊗ z. / 第一个六边形：将 x 编织到张量积 y ⊗ z 之前。 *)
  hexagon_identity {x y z} :
    tensor_assoc ∘ braid ∘ tensor_assoc
      << (x ⨂ y) ⨂ z ~~> y ⨂ (z ⨂ x) >>
    id ⨂ braid ∘ tensor_assoc ∘ braid ⨂ id;

  (* Second hexagon: braiding the tensor product x ⊗ y past z. / 第二个六边形：将张量积 x ⊗ y 编织经过 z。 *)
  hexagon_identity_sym {x y z} :
    tensor_assoc⁻¹ ∘ braid ∘ tensor_assoc⁻¹
      << x ⨂ (y ⨂ z) ~~> (z ⨂ x) ⨂ y >>
    braid ⨂ id ∘ tensor_assoc⁻¹ ∘ id ⨂ braid;
}.
#[export] Existing Instance braided_is_monoidal.

Coercion braided_is_monoidal : BraidedMonoidal >-> Monoidal.

Context `{BraidedMonoidal}.

(* The hexagons imply the Yang-Baxter equation on a triple tensor product: the two ways of fully reversing a ⊗ b ⊗ c by adjacent braidings agree. / 六边形暗示了三重张量积上的杨-巴克斯特方程：通过相邻的交错来完全反转 a ⊗ b ⊗ c 的两种方式是一致的。 *)
Theorem Yang_Baxter_equation {a b c : C} :
  braid ⨂ id[a] ∘ tensor_assoc⁻¹
    ∘ id[b] ⨂ braid ∘ tensor_assoc
    ∘ braid ⨂ id[c] ∘ tensor_assoc⁻¹
    ≈ tensor_assoc⁻¹ ∘ id[c] ⨂ braid
        ∘ tensor_assoc ∘ braid ⨂ id[b]
        ∘ tensor_assoc⁻¹ ∘ id[a] ⨂ braid.
Proof.
  rewrite <- !comp_assoc.
  rewrite (@comp_assoc _ _ _ _ _ (id ⨂ braid)).
  rewrite (@comp_assoc _ _ _ _ _ _ (braid ⨂ id)).
  rewrite <- hexagon_identity.
  rewrite <- !comp_assoc.
  rewrite (@comp_assoc _ _ _ _ _ tensor_assoc⁻¹ tensor_assoc).
  rewrite iso_from_to, id_left.
  rewrite iso_to_from, id_right.
  rewrite (@comp_assoc _ _ _ _ _ (id ⨂ braid)).
  rewrite (@comp_assoc _ _ _ _ _ _ (braid ⨂ id)).
  rewrite <- hexagon_identity.
  rewrite <- !comp_assoc.
  rewrite (@comp_assoc _ _ _ _ _ tensor_assoc⁻¹ tensor_assoc).
  rewrite iso_from_to, id_left.
  rewrite (@comp_assoc _ _ _ _ _ _ tensor_assoc⁻¹).
  rewrite iso_to_from, id_left.
  spose (braid_natural a _ id _ _ (@braid _ b c)) as X.
  rewrite bimap_id_id in X.
  rewrite id_right in X.
  rewrite X.
  rewrite bimap_id_id.
  rewrite id_right.
  reflexivity.
Qed.

End BraidedMonoidal.
