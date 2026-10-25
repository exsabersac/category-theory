Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.

Generalizable All Variables.

Section Monoidal.

Context {C : Category}.

(*
 nLab: https://ncatlab.org/nlab/show/monoidal+category
 Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category

 A monoidal category is a category equipped with a tensor product and a
 unit object that are associative and unital up to coherent isomorphism.
 The data are a unit object I, a tensor bifunctor ⊗ : C ∏ C ⟶ C, and three
 natural isomorphisms,

 lambda  : I ⊗ x ≅ x              ([unit_left]),
 rho     : x ⊗ I ≅ x              ([unit_right]),
 alpha   : (x ⊗ y) ⊗ z ≅ x ⊗ (y ⊗ z)   ([tensor_assoc]),

 the left unitor, the right unitor, and the associator respectively. The
 associator direction (x ⊗ y) ⊗ z ≅ x ⊗ (y ⊗ z) follows nLab; the opposite
 orientation appears in some sources and differs only by inverses.

 Naturality of each isomorphism is recorded explicitly, in both the forward
 (to) and inverse (from) directions, so rewriting and dualization work
 either way. For lambda this is the square g ∘ λ ≈ λ ∘ (id ⊗ g), and
 similarly for rho and alpha.

 Two coherence conditions govern the interaction of these isomorphisms:

 triangle:  (ρ ⊗ id) ≈ (id ⊗ λ) ∘ α   on   (x ⊗ I) ⊗ y
 pentagon:  (id ⊗ α) ∘ α ∘ (α ⊗ id) ≈ α ∘ α
 on  ((x ⊗ y) ⊗ z) ⊗ w

 The triangle identity relates the unitors to the associator across the
 unit; the pentagon identity makes the two reassociations of a fourfold
 tensor agree. By Mac Lane's coherence theorem these two laws force every
 formal diagram built from α, λ, ρ to commute. 

 --------
 nLab: https://ncatlab.org/nlab/show/monoidal+category
 Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category

 一个单象范畴是一个配备了张量积和单位对象的范畴，这些张量积和单位对象在相干同构下是结合的和单位的。数据包括一个单位对象 I、一个张量双函子 ⊗ : C ∏ C ⟶ C，以及三个自然同构：

 lambda  : I ⊗ x ≅ x              ([unit_left]),
 rho     : x ⊗ I ≅ x              ([unit_right]),
 alpha   : (x ⊗ y) ⊗ z ≅ x ⊗ (y ⊗ z)   ([tensor_assoc]),

 分别是左单位同构、右单位同构以及结合子。同构方向 (x ⊗ y) ⊗ z ≅ x ⊗ (y ⊗ z) 遵循 nLab；在一些资料中出现相反的方向，仅仅通过逆元不同。每个同构的自然性都被明确记录下来，包括正向（到）和逆向（从）两个方向，因此无论是哪种方式，重写和对偶化都可以工作。对于 λ，这个同构是方形 g ∘ λ ≈ λ ∘ (id ⊗ g)，ρ 和 α 也是类似的。

 两条一致性条件控制这些同构之间的相互作用：

 三角形：  (ρ ⊗ id) ≈ (id ⊗ λ) ∘ α   在   (x ⊗ I) ⊗ y 上
 五边形：  (id ⊗ α) ∘ α ∘ (α ⊗ id) ≈ α ∘ α
 在  ((x ⊗ y) ⊗ z) ⊗ w 上

 三角形恒等式将单位子与结合子在单位元处联系起来；五边形恒等式使四重张量的两种重新结合方式一致。根据 Mac Lane 的一致性定理，这两条定律强制由 α、λ、ρ 构成的每个形式图都交换。
*)

(*
 Origins, coherence, and the reach of the tensor

 nLab:  https://ncatlab.org/nlab/show/monoidal+category
 Paper: Bénabou, "Catégories avec multiplication", C. R. Acad. Sci.
 Paris 256, 1963
 Paper: Mac Lane, "Natural Associativity and Commutativity", Rice
 University Studies 49(4), 1963
 Paper: Kelly, "On MacLane's conditions for coherence of natural
 associativities, commutativities, etc.", J. Algebra 1(4), 1964
 Paper: Joyal, Street, "The geometry of tensor calculus, I", Advances
 in Mathematics 88(1), 1991
 Paper: Baez, Stay, "Physics, Topology, Logic and Computation: A
 Rosetta Stone", 2009 (arXiv:0903.0340)

 The notion entered the literature twice in 1963: Bénabou introduced
 categories with a multiplication in the Comptes Rendus, and Mac Lane
 isolated the coherence question and proved the first coherence
 theorem.  Mac Lane's original axiom list was longer than the one
 below; Kelly (1964) showed the surplus redundant, deriving the
 remaining unit laws — among them λ_{x⊗y} ∘ α ≈ λ_x ⊗ id and
 λ_I ≈ ρ_I — from the pentagon, one triangle, and naturality.  That
 reduction is why the [Monoidal] class carries exactly two coherence
 fields, [triangle_identity] and [pentagon_identity], and why
 Structure/Monoidal/Proofs.v can restate Kelly's derived equations as
 rewriting lemmas rather than axioms.  Coherence also has a modern
 repackaging: every monoidal category is monoidally equivalent to a
 strict one, in which α, λ, ρ are identities (the strict notion is
 Structure/Monoidal/Strict.v) — though not, nLab cautions, to a
 skeletal strict one, with (Set, ×) the standard counterexample.

 The definition answers a precise design problem.  Many categories
 carry a combining operation that is associative and unital only up
 to isomorphism — the tensor product of vector spaces reassociates
 canonically but not equally — so demanding equality would exclude
 nearly every example, while demanding bare isomorphism would let two
 different composites of structural maps join the same bracketings.
 Taking λ, ρ, α as structure and imposing the triangle and pentagon
 is the middle course: Mac Lane proved it sufficient, and Kelly
 trimmed the axioms required to exactly these two.

 Equally deliberate is what the definition omits: [tensor] need not
 be the categorical product.  A cartesian tensor comes with diagonals
 and projections, so every object can be copied and deleted; a
 general tensor supplies neither, which is precisely the situation of
 quantum systems (no-cloning) and of the multiplicative conjunction
 of resources consumed exactly once (Girard, "Linear logic",
 Theoretical Computer Science 50, 1987).  Monoidal categories are
 thus the home of resource-like combination, the cartesian case being
 characterized by Fox's theorem in-tree
 (Structure/Monoidal/Heunen_Vicary.v, Structure/Monoidal/Markov/Fox.v).
 Under the Baez–Stay reading, composition ∘ is process in series and
 ⊗ is process in parallel: given f : x ~> y and g : z ~> w, the map
 f ⊗ g does both jobs at once.  Joyal and Street (1991) made the
 accompanying string-diagram notation rigorous — a diagrammatic
 equality holds precisely when it follows from these axioms, so
 deforming the picture is a sound and complete proof method for
 structural equations.

 Within category theory the class is load-bearing infrastructure.
 Endofunctor categories are strict monoidal under composition, and
 monoids in them are monads; monoid objects (Theory/Algebra/Monoid.v),
 enriched categories (Construction/Enriched.v), and Day convolution
 (Construction/Day.v) all presuppose a monoidal base; and a monoidal
 category is exactly a one-object bicategory — every field of
 Theory/Bicategory.v mirrors a field here, with the delooping realized
 in Theory/Bicategory/OneObject.v.  The structure-preserving functors
 live in Functor/Structure/Monoidal.v, whose lax variant, given a
 strength on Coq's cartesian structure, is the programmer's
 applicative functor (Functor/Applicative.v,
 Theory/Coq/Applicative/Proofs.v, Instance/Coq/Applicative.v).  The
 braided and symmetric towers (Structure/Monoidal/Braided.v,
 Structure/Monoidal/Symmetric.v), the linear-logic superstructure
 (Structure/Monoidal/StarAutonomous.v, after Seely 1989), and the
 effectful weakening to premonoidal categories (Structure/Premonoidal.v,
 with the equivalence in Structure/Premonoidal/Monoidal.v) all take
 this file as their root. 

 --------
 张量的起源、一致性及其涵盖范围

 nLab: https://ncatlab.org/nlab/show/monoidal+category
 论文：Bénabou, 《具有乘法的范畴》, C. R. Acad. Sci. Paris 256, 1963
 论文：Mac Lane, 《自然的结合性与交换性》, Rice University Studies 49(4), 1963
 论文：Kelly, 《关于Mac Lane自然结合性、交换性等一致性条件的研究》, J. Algebra 1(4), 1964
 论文：Joyal, Street, 《张量演算的几何，I》, Advances in Mathematics 88(1), 1991
 论文：Baez, Stay, 《物理、拓扑学、逻辑与计算：一块罗塞塔石》, 2009 (arXiv:0903.0340)这一概念在1963年在文献中出现了两次：Bénabou在《Comptes Rendus》中引入了带有乘法的范畴，而Mac Lane则提出了相干性问题并证明了第一个相干性定理。Mac Lane最初的公理列表比下面的要长；Kelly（1964）证明了其中的冗余，通过五边形、一个三角形和自然性推导出了剩余的单位律——其中包括 λ_{x⊗y} ∘ α ≈ λ_x ⊗ id 和 λ_I ≈ ρ_I。这种简化正是为什么 [Monoidal] 类恰好有两个相干性域，[triangle_identity] 和 [pentagon_identity]，以及为什么 Structure/Monoidal/Proofs.v 可以将Kelly推导出的方程重述为重写引理而不是公理的原因。相干性也有一个现代的重新包装：每个单幺范畴在幺范畴意义下都等价于一个严格范畴，其中 α、λ、ρ 都是恒等映射（严格概念见 Structure/Monoidal/Strict.v）——尽管 nLab 警告说，并非与骨架严格范畴等价，标准的反例是 (Set, ×)。这个定义解决了一个精确的设计问题。许多范畴包含的组合运算只有在同构意义下才是结合的且具有单位——向量空间的张量积在范式上是可重新结合的，但不完全相等——因此要求相等几乎会排除所有例子，而仅要求同构又会使两个不同的结构映射组合对应到相同的括号结构。将 λ、ρ、α 作为结构，并施加三角形和五边形公理是一条中间路线：Mac Lane 证明这是足够的，而 Kelly 将所需的公理精简到正好这两个。同样值得注意的是定义中所省略的内容：[tensor] 不必是笛卡尔积。一个笛卡尔张量自带对角线和投影，因此每个对象都可以被复制和删除；而一个一般的张量既没有复制功能也没有删除功能，这正是量子系统（不可克隆性）以及资源仅被消耗一次的乘法合取情形（Girard，《线性逻辑》，理论计算机科学 50, 1987）的情况。因此，幺半范畴是资源类组合的归宿，笛卡尔情形则由 Fox 定理在树中加以刻画（Structure/Monoidal/Heunen_Vicary.v，Structure/Monoidal/Markov/Fox.v）。根据 Baez–Stay 的解释，组合 ∘ 表示串联过程，⊗ 表示并行过程：给定 f : x ~> y 和 g : z ~> w，映射 f ⊗ g 同时完成两个任务。Joyal 和 Street（1991）使随附的弦图符号系统变得严谨——当且仅当它可以从这些公理推导出来时，图形等式才成立，因此变形图形是一种对结构方程进行正确且完备的证明方法。在范畴论中，类是承重的基础设施。自函子范畴在复合下是严格的幺半群的，而其中的幺半群就是单子；幺半群对象（Theory/Algebra/Monoid.v）、丰富范畴（Construction/Enriched.v）以及 Day 卷积（Construction/Day.v）都假定了一个幺半群基底；而幺半群范畴正好是一个单对象双范畴——Theory/Bicategory.v 中的每个域在这里都有对应，解环在 Theory/Bicategory/OneObject.v 中实现。保持结构的函子位于 Functor/Structure/Monoidal.v，其松弛变体，在 Coq 的笛卡尔结构上给定一个强度时，就是程序员的抽象函子（Functor/Applicative.v, Theory/Coq/Applicative/Proofs.v, Instance/Coq/Applicative.v）。编织和对称的塔（Structure/Monoidal/Braided.v，Structure/Monoidal/Symmetric.v）、线性逻辑超结构（Structure/Monoidal/StarAutonomous.v，参照 Seely 1989），以及带效果的弱化到预单体范畴（Structure/Premonoidal.v，及 Structure/Premonoidal/Monoidal.v 中的等价）都以此文件为根。
*)

Reserved Infix "⨂" (at level 30, right associativity).

Class Monoidal := {
  I : C;                        (* unit_obj *)
  tensor : C ∏ C ⟶ C where "x ⨂ y" := (tensor (x, y));

  unit_left  {x} : I ⨂ x ≅ x;  (* lambda *)
  unit_right {x} : x ⨂ I ≅ x;  (* rho *)

  tensor_assoc {x y z} : (x ⨂ y) ⨂ z ≅ x ⨂ (y ⨂ z);  (* alpha *)

  (* alpha, lambda and rho are all natural isomorphisms. / alpha、lambda 和 rho 都是自然同构。 *)

  to_unit_left_natural {x y} (g : x ~> y) :
    g ∘ unit_left << I ⨂ x ~~> y >> unit_left ∘ bimap id g;
  from_unit_left_natural {x y} (g : x ~> y) :
    bimap id g ∘ unit_left⁻¹ << x ~~> I ⨂ y >> unit_left⁻¹ ∘ g;

  to_unit_right_natural {x y} (g : x ~> y) :
    g ∘ unit_right << x ⨂ I ~~> y >> unit_right ∘ bimap g id;
  from_unit_right_natural {x y} (g : x ~> y) :
    bimap g id ∘ unit_right⁻¹ << x ~~> y ⨂ I >> unit_right⁻¹ ∘ g;

  to_tensor_assoc_natural
    {x y z w v u} (g : x ~> y) (h : z ~> w) (i : v ~> u) :
    bimap g (bimap h i) ∘ tensor_assoc
      << (x ⨂ z) ⨂ v ~~> y ⨂ w ⨂ u >>
    tensor_assoc ∘ bimap (bimap g h) i;

  from_tensor_assoc_natural
    {x y z w v u} (g : x ~> y) (h : z ~> w) (i : v ~> u) :
    bimap (bimap g h) i ∘ tensor_assoc⁻¹
      << x ⨂ z ⨂ v ~~> (y ⨂ w) ⨂ u >>
    tensor_assoc⁻¹ ∘ bimap g (bimap h i);

  (*
 The above observe the following coherence conditions:
 the triangle identity (unitors vs. associator) and the pentagon
 identity (the two reassociations of a fourfold tensor agree). 

 --------
 上述遵循以下一致性条件：三角恒等式（单位子与结合子）和五边形恒等式（四重张量的两种重新结合方式相同）。
*)

  triangle_identity {x y} :
    bimap unit_right id
      << (x ⨂ I) ⨂ y ~~> x ⨂ y >>
    bimap id unit_left ∘ tensor_assoc;

  pentagon_identity {x y z w} :
    bimap id tensor_assoc ∘ tensor_assoc ∘ bimap tensor_assoc id
      << ((x ⨂ y) ⨂ z) ⨂ w ~~> x ⨂ (y ⨂ (z ⨂ w)) >>
    tensor_assoc ∘ tensor_assoc
}.

End Monoidal.

Notation "(⨂)" := (@tensor _ _) : functor_scope.
Notation "x ⨂ y" := (@tensor _ _ (x%object, y%object))
  (at level 30, right associativity) : object_scope.
Notation "x ⨂[ M ] y" := (fobj[@tensor _ M] (x, y))
  (at level 30, only parsing, right associativity) : object_scope.
Notation "f ⨂ g" := (bimap[(⨂)] f g)
  (at level 30, right associativity) : morphism_scope.
Notation "f ⨂[ M ] g" := (bimap[@tensor _ M] f g)
  (at level 30, only parsing, right associativity) : morphism_scope.
