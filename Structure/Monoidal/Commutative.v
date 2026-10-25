Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Export Category.Structure.Monoidal.Symmetric.

Generalizable All Variables.

Section CommutativeMonoidal.

Context {C : Category}.
Context `{@SymmetricMonoidal C}.

(** Commutative monoidal category (self-braiding triviality). / 交换幺半范畴（自缠绕平凡性）。 *)

(*
 nLab:      https://ncatlab.org/nlab/show/commutative+monoidal+category
 Wikipedia: https://en.wikipedia.org/wiki/Symmetric_monoidal_category

 A commutative monoidal category (nLab) is, strictly speaking, a commutative
 monoid object in (Cat, ×): a symmetric monoidal category whose associators,
 unitors AND braidings are all identity natural transformations, so that the
 braiding β_{x,y} ≈ id for every pair of objects and consequently x ⨂ y =
 y ⨂ x holds on the nose. That is the maximally strict notion of a
 "commutative" tensor product.

 This class does NOT impose that full strictness. It captures the weaker,
 purely self-referential condition that the braiding restricted to the
 DIAGONAL is trivial:

 braid ≈ id                       << x ⨂ x ~~> x ⨂ x >>

 i.e. β_{x,x} ≈ 1_{x ⨂ x} for every object x. Equivalently, swapping an
 object's two tensor copies of ITSELF does nothing. (In any symmetric
 monoidal category β_{x,x} is already an involution, β_{x,x} ∘ β_{x,x} ≈ id,
 by braid_invol; this axiom asks for the strictly stronger fact that β_{x,x}
 is the identity, not merely its own inverse — false in, e.g., super vector
 spaces, where swapping two odd vectors introduces a sign.)

 The two conditions are linked by a theorem of Kim (2016): a symmetric
 monoidal category is symmetric-monoidally EQUIVALENT to a commutative
 monoidal category iff all its self-braidings β_{x,x} are identities (proved
 assuming the objects can be totally ordered, e.g. under choice). The "only
 if" direction is immediate, since the property is equivalence-invariant.
 Hence this class names exactly the equivalence-invariant shadow of nLab's
 strict definition, without demanding strict equality of objects.

 Note the distinct meaning of "commutative" in
 Theory/Algebra/CommutativeMonoid.v: there it is a property of a MONOID
 OBJECT X in a symmetric monoidal category (mu ∘ braid ≈ mu), constraining a
 chosen multiplication. Here "commutative" is a property of the ambient
 MONOIDAL STRUCTURE itself (braid ≈ id on the diagonal), constraining no
 algebra. The two are independent. 

 --------
 nLab：       https://ncatlab.org/nlab/show/commutative+monoidal+category 
 Wikipedia：  https://en.wikipedia.org/wiki/Symmetric_monoidal_category 

 一个交换单体范畴（nLab）严格来说，是 (Cat, ×) 中的一个交换幺半群对象：一个对称单体范畴，其结合子、单位子和换位子都是恒等自然变换，因此对于每一对对象，换位 β_{x,y} ≈ id，从而 x ⨂ y = y ⨂ x 成立。这是“交换”张量积的最严格概念。

 这个类别并不要求完全严格性。它捕捉了一种较弱的、纯粹自指的条件，即在对角线上限制的换位是平凡的：

 braid ≈ id                       << x ⨂ x ~~> x ⨂ x >>即，对于每个对象 x，有 β_{x,x} ≈ 1_{x ⨂ x}。等价地，交换一个对象的两个自身的张量副本不会产生任何影响。（在任何对称单模范畴中，β_{x,x} 已经是一个自反元，即 β_{x,x} ∘ β_{x,x} ≈ id，由 braid_invol 给出；这个公理要求更严格的事实，即 β_{x,x} 是恒等映射，而不仅仅是它自身的逆——在例如超向量空间中，这并不成立，因为交换两个奇向量会引入一个符号。）这两个条件由 Kim (2016) 的一个定理联系起来：一个对称单体范畴当且仅当它的所有自交错 β_{x,x} 都是恒等映射时，与一个交换单体范畴在对称单体意义下是等价的（证明假设对象可以完全排序，例如在选择公理下）。“只有如果”方向是显而易见的，因为该性质在等价下不变。因此，这个类恰好命名了 nLab 严格定义的等价不变量的影子，而不要求对象严格相等。请注意在 Theory/Algebra/CommutativeMonoid.v 中“交换”的不同含义：在那里它是对对称幺半群范畴中的一个幺半群对象 X 的性质（mu ∘ braid ≈ mu），约束了选定的乘法。这里“交换”是对整体幺半群结构自身的性质（在对角线上 braid ≈ id），不约束任何代数。这两者是独立的。
*)

Class CommutativeMonoidal := {
  (* Self-braiding is trivial: β_{x,x} ≈ 1_{x ⨂ x} for every object x. / 自缠绕是平凡的：对于每个对象 x，β_{x,x} ≈ 1_{x ⨂ x}。 *)
  commutative {x} : @braid _ _ x x ≈ id
}.

End CommutativeMonoidal.
