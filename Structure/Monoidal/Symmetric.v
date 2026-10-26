Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Export Category.Structure.Monoidal.Braided.

Generalizable All Variables.

Section SymmetricMonoidal.

Context {C : Category}.

(*
 nLab: https://ncatlab.org/nlab/show/symmetric+monoidal+category
 Wikipedia: https://en.wikipedia.org/wiki/Symmetric_monoidal_category

 A symmetric monoidal category is a braided monoidal category whose braiding
 is its own inverse: the symmetry condition is

 braid ∘ braid ≈ id[x ⨂ y]

 i.e. β_{y,x} ∘ β_{x,y} = 1_{x ⨂ y}, “switching twice has no effect”. A
 braided monoidal category carries two hexagon identities; under symmetry
 either one implies the other, so a symmetric monoidal category is fully
 determined by its underlying braided structure together with braid_invol. 

 --------
 nLab:  https://ncatlab.org/nlab/show/symmetric+monoidal+category
 Wikipedia:  https://en.wikipedia.org/wiki/Symmetric_monoidal_category

 对称幺半范畴是一个编织幺半范畴，其编织是其自身的逆：对称性条件是

 braid ∘ braid ≈ id [x ⨂ y]

 即 β_{y,x} ∘ β_{x,y} = 1_{x ⨂ y}，“交换两次没有效果”。一个编织幺半范畴满足两个六边形恒等式；在对称性下，任意一个恒等式都能推导出另一个，因此一个对称幺半范畴完全由其底层的编织结构以及 braid_invol 决定。
*)

(*
 Where symmetric monoidal categories come from, and what they are for

 nLab:
 https://ncatlab.org/nlab/show/coherence+theorem+for+symmetric+monoidal+categories
 Paper: Mac Lane, “Natural Associativity and Commutativity”, Rice
 University Studies 49, 1963
 Paper: Mac Lane, “Categorical Algebra”, Bull. Amer. Math. Soc. 71, 1965

 The axioms answer a question Mac Lane posed and settled in 1963: how to
 say that a tensor product commutes when it commutes only up to
 isomorphism.  In vector spaces, V ⊗ W and W ⊗ V are isomorphic but not
 equal, and the chosen isomorphisms must cohere with the associator and
 unitors (Mac Lane 1963, above; the nLab records contemporaneous
 treatments by Bénabou, C. R. Acad. Sci. Paris 258, 1964, and by
 Eilenberg and Kelly, “Closed Categories”, in the La Jolla proceedings,
 1966).  The braided axioms alone do not settle the matter: they allow
 the double crossing x ⨂ y ~> y ⨂ x ~> x ⨂ y to be a nontrivial
 automorphism, as it genuinely is in categories of braids and ribbons
 (Joyal, Street, “Braided tensor categories”, Advances in Mathematics
 102, 1993).  The single law [braid_invol] removes exactly that freedom,
 and the reward is Mac Lane's coherence theorem for the symmetric case:
 every diagram built from associators, unitors, and symmetries commutes,
 provided its two sides induce the same permutation of the tensor
 factors.  It follows that one may reason as though an iterated tensor
 were a multiset of factors, and that every symmetric monoidal category
 is equivalent to a permutative one, strictly associative and strictly
 unital.  The lemmas [bimap_braid] and [braid_bimap_braid] below are
 small instances of this collapse, and [hexagon_rotated] shows one
 hexagon absorbing the other, as the header remarks.

 Read computationally, [braid] swaps two parallel wires, and
 [braid_invol] says the wires cross with no memory of the crossing —
 precisely where the symmetric case parts from the braided one, whose
 over- and under-crossings differ.  Coherence then licenses tracking
 only the permutation when replumbing a parallel composite, the
 soundness behind string-diagram calculi such as the signal-flow graphs
 of Fong and Spivak (“An Invitation to Applied Category Theory”, CUP
 2019, ch. 5).  Cartesian categories supply the everyday examples: Set,
 Cat, and any category with finite products, where the braiding is the
 argument swap, realized in-tree as [CC_SymmetricMonoidal] in
 Structure/Monoidal/Internal/Product.v.

 The definition organizes whole subjects downstream.  Mac Lane's PROPs
 (“Categorical Algebra”, 1965, from joint work with Adams) are strict
 symmetric monoidal categories whose objects are the natural numbers
 and whose tensor is addition; their models are symmetric monoidal
 functors ([SymmetricMonoidalFunctor] in
 Functor/Structure/Monoidal/Braided.v), and they present structures
 such as bialgebras that neither operads nor Lawvere theories reach —
 the library's free-PROP spine (Construction/PROP.v, whose class
 carries [prop_symmetric]) rests on this file.  In logic, closed
 symmetric monoidal categories model multiplicative intuitionistic
 linear logic (Girard 1987): the tensor is conjunction of resources,
 and the missing contraction rule means a consumed resource is gone;
 the classical case asks in addition for a dualizing object (Seely,
 “Linear logic, *-autonomous categories and cofree coalgebras”, 1989),
 which Structure/Monoidal/StarAutonomous.v adds atop its [SymMonClosed]
 base.  Resource theories in the sense of Coecke, Fritz, and Spekkens
 (“A mathematical theory of resources”, Information and Computation
 250, 2016) are symmetric monoidal categories outright — objects are
 resources, morphisms are the free transformations — a reading
 continued by the copy/discard and Markov developments
 (Structure/Monoidal/CopyDiscard.v, Structure/Monoidal/Markov.v), while
 Baez and Stay (“Physics, Topology, Logic and Computation: A Rosetta
 Stone”, 2009) take closed symmetric monoidal categories as the grammar
 shared by Hilbert spaces, cobordisms, proofs, and programs.  For the
 semantics of effects, Kock's theorem matches commutative monads with
 symmetric monoidal monads over a symmetric monoidal closed base (Kock,
 “Strong functors and monoidal monads”, Archiv der Mathematik 23,
 1972); in-tree, the Kleisli category of a commutative monad is again
 symmetric monoidal ([Kleisli_Symmetric] in
 Monad/Kleisli/Commutative.v), so independent effectful computations
 may be scheduled in either order.  Traced monoidal structure layers
 feedback on the same symmetric base (Structure/Monoidal/Traced.v, with
 [traced_is_symmetric] a coercion into this class). 

 --------
 对称单模范畴的来源及其用途

 nLab:
 https://ncatlab.org/nlab/show/coherence+theorem+for+symmetric+monoidal+categories 
 论文：Mac Lane，《自然的结合律与交换律》，赖斯大学研究，49，1963
 论文：Mac Lane，《范畴代数》，美国数学学会公报，71，1965这些公理回答了 Mac Lane 在 1963 年提出并解决的一个问题：当一个张量积仅在同构意义下交换时，如何说明它是交换的。在向量空间中，V ⊗ W 和 W ⊗ V 是同构的，但不相等，而所选择的同构必须与结合子和单位子一致（Mac Lane 1963，如上所述；nLab 记录了 Bénabou（C. R. Acad. Sci. Paris 258, 1964）以及 Eilenberg 和 Kelly 在 La Jolla 会议论文集（1966）中的同时期处理方法）。仅有编织公理并不能解决这个问题：它们允许双重交叉 x ⨂ y ~> y ⨂ x ~> x ⨂ y 成为一个非平凡的自同构，就像它在编织和丝带范畴中真实存在的一样（Joyal, Street, “Braided tensor categories”, Advances in Mathematics 102, 1993）。单一的定律 [braid_invol] 恰好消除了那种自由，而其回报是 Mac Lane 的对称情形的相干性定理：由结合子、单位子和对称子构成的每一个图都是可交换的，前提是其两边诱导的张量因子的排列相同。因此，可以像处理一个因子多重集合那样推理一个迭代张量，并且每个对称幺半范畴都与一个置换幺半范畴等价，该范畴严格结合并严格含有单位。下面的引理 [bimap_braid] 和 [braid_bimap_braid] 是这种坍塌的一些小例子，而 [hexagon_rotated] 展示了一个六边形吸收了另一个，如标题所述。从计算的角度来看，[braid] 交换两根平行的电线，而 [braid_invol] 表示电线交叉时没有交叉的记忆——这正是对称情况与编织情况的区别所在，后者的上下交叉不同。连贯性因此只允许在重新布线一个平行复合时跟踪置换，这是字符串图计算的合理性基础，例如 Fong 和 Spivak 的信号流图（“An Invitation to Applied Category Theory”, CUP 2019, 第5章）。笛卡尔范畴提供了日常的例子：Set、Cat，以及任何具有有限积的范畴，其中的编织是参数交换，在树中实现为 Structure/Monoidal/Internal/Product.v 中的 [CC_SymmetricMonoidal]。该定义将完整的学科向下组织。Mac Lane 的 PROPs（“Categorical Algebra”，1965年，与 Adams 的合作工作）是严格的对称单幺范畴，其对象是自然数，张量是加法；它们的模型是对称单幺函子（Functor/Structure/Monoidal/Braided.v 中的 [SymmetricMonoidalFunctor]），并且它们呈现了诸如双代数之类的结构，这是操作子或 Lawvere 理论无法涵盖的——库中的 free-PROP 主干（Construction/PROP.v，其类携带 [prop_symmetric]）依赖于此文件。在逻辑中，闭对称幺半范畴（closed symmetric monoidal categories）模拟乘法直觉线性逻辑（Girard 1987）：张量表示资源的合取，而缺失的合并规则意味着消耗的资源将消失；经典情形还要求一个对偶对象（Seely, “Linear logic, *-autonomous categories and cofree coalgebras”, 1989），这在 Structure/Monoidal/StarAutonomous.v 中在其 [SymMonClosed] 基础上进行了扩展。Coecke、Fritz 和 Spekkens 意义下的资源理论（“A mathematical theory of resources”，《Information and Computation》, 250, 2016）本质上是对称单体范畴——对象是资源，态射是自由变换——这一解读在复制/丢弃和马尔可夫的发展中得以延续（Structure/Monoidal/CopyDiscard.v, Structure/Monoidal/Markov.v），而 Baez 和 Stay（“Physics, Topology, Logic and Computation: A Rosetta Stone”, 2009）则将闭对称单体范畴视为希尔伯特空间、余流、证明和程序共用的语法。对于效应的语义，Kock 定理将交换单子与对称单闭基上的对称幺半群单子相对应（Kock，“强函子与幺半群单子”，Archiv der Mathematik 23，1972）；在树中，交换单子的 Kleisli 范畴再次是对称幺半群的（[Kleisli_Symmetric] 在 Monad/Kleisli/Commutative.v 中），因此独立的有副作用的计算可以按任意顺序调度。追踪幺半群结构在相同的对称基上叠加反馈（Structure/Monoidal/Traced.v，[traced_is_symmetric] 是进入该类的一种强制转换）。
*)

Class SymmetricMonoidal := {
  (* The underlying braided monoidal structure (braiding + hexagon laws). / 底层的编织单范畴结构（编织 + 六边形律）。 *)
  symmetric_is_braided : @BraidedMonoidal C;

  (* Symmetry: the braiding is its own inverse, β_{y,x} ∘ β_{x,y} = id. / 对称性：编织自身就是它的逆，β_{y,x} ∘ β_{x,y} = id。 *)
  braid_invol {x y} : braid ∘ braid ≈ id[x ⨂ y];
}.
#[export] Existing Instance symmetric_is_braided.

Coercion symmetric_is_braided : SymmetricMonoidal >-> BraidedMonoidal.

Context `{SymmetricMonoidal}.

(*
 A rotated form of the hexagon identity, available once the braiding is
 symmetric: the second hexagon is recovered from the first via braid_invol. 

 --------
 六边形恒等式的旋转形式，一旦交换对称就可以使用：第二个六边形通过 braid_invol 从第一个六边形恢复。
*)
Lemma hexagon_rotated {x y z} :
  tensor_assoc ∘ braid ⨂ id ∘ tensor_assoc ⁻¹
    << x ⨂ (y ⨂ z) ~~> y ⨂ (x ⨂ z) >>
  id ⨂ braid ∘ tensor_assoc ∘ braid.
Proof.
  rewrite <- (id_right (id ⨂ braid ∘ tensor_assoc ∘ braid)).
  rewrite <- (iso_to_from tensor_assoc).
  rewrite comp_assoc;
  rewrite <- (comp_assoc _ tensor_assoc braid);
  rewrite <- (comp_assoc _ (tensor_assoc ∘ braid) _).
  rewrite hexagon_identity.
  rewrite !comp_assoc.
  rewrite <- bimap_comp; rewrite id_left.
  rewrite braid_invol.
  cat.
Qed.

(*
 Naturality of the braiding, transposed: braid commutes a tensor of two
 morphisms past itself, swapping the order of the factors. 

 --------
 编织的自然性，转置：编织将两个态射的张量穿过自身，使因子的顺序交换。
*)
Lemma bimap_braid {x y z w} (f : x ~> z) (g : y ~> w) :
  g ⨂ f ∘ braid ≈ braid ∘ f ⨂ g.
Proof.
  spose (braid_natural _ _ f _ _ g) as X.
  normal.
  apply X.
Qed.

(* Conjugating a swapped tensor by the braiding on both sides recovers the original tensor; combines bimap_braid with the symmetry law braid_invol. / 通过在两侧用编织作用于交换的张量，可以恢复原始张量；将 bimap_braid 与对称律 braid_invol 结合。 *)
Lemma braid_bimap_braid {x y z w} (f : x ~> z) (g : y ~> w) :
  braid ∘ g ⨂ f ∘ braid ≈ f ⨂ g.
Proof.
  rewrite <- comp_assoc.
  rewrite bimap_braid.
  rewrite comp_assoc.
  rewrite braid_invol.
  cat.
Qed.

End SymmetricMonoidal.

Require Export Category.Structure.Monoidal.Balanced.

(*
 A balanced monoidal category whose twist is the identity is symmetric: the
 balancing axiom braid ∘ twist ⨂ twist ∘ braid ≈ twist then degenerates to
 the symmetry law braid ∘ braid ≈ id. 

 --------
 一个平衡单体范畴，其扭转是恒等映射，则是对称的：平衡公理 braid ∘ twist ⨂ twist ∘ braid ≈ twist 随后退化为对称律 braid ∘ braid ≈ id。
*)
Program Definition balanced_twist_id_is_symmetric
  `{@BalancedMonoidal C}
  (to_twist : ∀ x : C, to twist ≈[C] to (@iso_id _ x)) :
  @SymmetricMonoidal C := {|
  braid_invol := _;
|}.
Next Obligation.
  pose proof (@balanced_to_commutes _ _ x y).
  rewrite <- to_twist.
  rewrite <- X; clear X.
  comp_left.
  rewrite <- id_left at 1.
  comp_right.
  rewrite !to_twist.
  now rewrite bimap_id_id.
Qed.

(*
 ncatlab: “Every symmetric monoidal category is balanced in a canonical way;
 in fact, the identity natural transformation (on the identity functor of
 BB) is a balance on BB if and only if BB is symmetric. Thus balanced
 monoidal categories fall between braided monoidal categories and symmetric
 monoidal categories.” 

 --------
 ncatlab：“每一个对称单体范畴以一种典型的方式是平衡的；实际上，恒等自然变换（在 BB 的恒等函子上）是 BB 的一个平衡，当且仅当 BB 是对称的时候。因此，平衡单体范畴介于编织单体范畴和对称单体范畴之间。”
*)

Program Definition symmetric_is_balanced `{@SymmetricMonoidal C} :
  @BalancedMonoidal C := {|
  twist := @iso_id C
|}.
Next Obligation.
  rewrite bimap_id_id.
  rewrite id_right.
  apply braid_invol.
Qed.
Next Obligation.
  rewrite bimap_id_id.
  rewrite id_right.
  apply braid_invol.
Qed.
