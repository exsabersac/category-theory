Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Diagram.
Require Import Category.Structure.Cone.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(** * Witnesses for [Commutative]: concrete diagrams, and in-tree instances / * [Commutative] 的证人：具体图表和树内实例 *)

(*
Theory/Diagram.v proves [square_commutative_iff] and its triangle
   counterpart parametrically, over an arbitrary category and arbitrary
   morphisms.  This file supplies concrete inhabitants, because a
   universally quantified predicate can be true for two uninteresting
   reasons and both must be ruled out for [Commutative] to have been tested:

   1. VACUITY OF THE SHAPE.  If a quiver has no two distinct parallel paths,
      [Commutative] holds of every diagram over it for lack of anything to
      check.  [SquareQuiver] escapes this: [sq_via_B_neq_via_C]
      (Theory/Diagram.v) proves its two routes from [SqA] to [SqD] are
      DISTINCT morphisms of [FreeOnQuiver SquareQuiver], and
      [tri_via_Y_neq_direct] does the same for [TriangleQuiver].

   2. VACUITY OF THE TARGET.  If the target category is thin (a preorder --
      at most one morphism between any two objects) then all parallel
      composites agree and [Commutative] holds of every diagram into it.  The
      target used here is [Coq] (Instance/Coq.v: objects are types, morphisms
      are functions, [f ≈ g] is [∀ x, f x = g x]), and it is NOT thin: the
      examples below exhibit parallel morphisms that are provably not [≈]
      ([coq_parallel_not_equiv], [coq_sq_legs_differ],
      [coq_sq_sides_differ]).

   So the positive witnesses below are commuting diagrams over a shape that
   has a real parallel pair, into a category that has parallel morphisms it
   distinguishes; and the negative witnesses are diagrams over the SAME
   shapes, into the SAME category, for which [Commutative] is refuted.

   The category [Coq] is used rather than a setoid model because its category
   laws hold with no axioms (Instance/Coq.v, header) and disequality of
   functions here is decided by computation on [bool].

   The final section is of a different kind: it exhibits two of the tree's own
   shape-specific commutativity statements as instances of [Commutative], so
   that the claim in Theory/Diagram.v's header that the predicate generalizes
   them is a theorem here rather than an assertion.

--------
Theory/Diagram.v 在任意范畴和任意态射下参数化地证明了 [square_commutative_iff] 及其三角形对应物。该文件提供了具体的实例，因为一个全称量化的谓词可能由于两个无趣的原因而为真，并且为了测试 [Commutative]，必须排除这两种情况：

1. 形状的空虚。如果一个箭袋没有两条不同的平行路径，那么由于没有任何东西可供检查，[Commutative] 对其上的每个图表都成立。[SquareQuiver] 例外：[sq_via_B_neq_via_C]（Theory/Diagram.v）证明了从 [SqA] 到 [SqD] 的两条路径是 [FreeOnQuiver SquareQuiver] 的不同态射，而 [tri_via_Y_neq_direct] 对 [TriangleQuiver] 也是同样的处理。

2. 目标的空性。如果目标范畴是薄的（一个前序——在任意两个对象之间至多有一个态射），那么所有平行复合都是相同的，并且每个映入它的图都满足 [Commutative]。这里使用的目标是 [Coq]（Instance/Coq.v：对象是类型，态射是函数，[f ≈ g] 是 [∀ x, f x = g x]），它不是薄的：下面的例子展示了平行态射，它们被证明不是 [≈]（[coq_parallel_not_equiv]、[coq_sq_legs_differ]、[coq_sq_sides_differ]）。

因此，下面的正面证据是在一个具有实际平行对的形状上的交换图，进入一个具有它区分的平行态射的范畴；而负面证据则是在相同的形状上、进入相同的范畴的图，其中 [Commutative] 被否定。

范畴 [Coq] 被使用而不是集合模型，因为它的范畴定律在没有公理的情况下成立（Instance/Coq.v，头部），并且这里函数的不等性由对 [bool] 的计算决定。

最后一部分属于不同的类型：它展示了树自身两条特定形状的交换性陈述，作为 [Commutative] 的实例，因此 Theory/Diagram.v 头部中关于谓词推广它们的声明在此处是一个定理，而不是一个断言。
*)

(** ** A commuting square in [Coq] / ** [Coq] 中的一个换乘广场 *)

(*
unit --(fun _ => true)--> bool
          |                        |
    (fun _ => false)             negb
          |                        |
          v                        v
         bool --------id--------> bool

   Both routes send the unique element of [unit] to [false].

--------
unit --(fun _ => true)--> bool
          |                        |
    (fun _ => false)             negb
          |                        |
          v                        v
         bool --------id--------> bool

两个路径都将 [unit] 的唯一元素发送到 [false]。
*)

Definition coq_sq_u : (unit : Coq) ~{Coq}~> (bool : Coq) := fun _ => true.
Definition coq_sq_v : (bool : Coq) ~{Coq}~> (bool : Coq) := negb.
Definition coq_sq_h : (unit : Coq) ~{Coq}~> (bool : Coq) := fun _ => false.
Definition coq_sq_k : (bool : Coq) ~{Coq}~> (bool : Coq) := Datatypes.id.

Definition CoqCommutingSquare : Diagram SquareQuiver Coq :=
  SquareDiagram coq_sq_u coq_sq_v coq_sq_h coq_sq_k.

(* The square commutes, hence so does every pair of parallel paths over it. / 该方形是交换的，因此其上的每一对平行路径也都是交换的。 *)
Example coq_square_commutative : Commutative CoqCommutingSquare.
Proof.
  apply square_commutes.
  now intros [].
Qed.

(*
The commutation is not an artefact of the two legs coinciding: the top and
   left edges differ, and so do the right and bottom edges.

--------
交换并不是两条边重合的人工产物：上边和左边不同，右边和下边也不同。
*)
Example coq_sq_legs_differ : (coq_sq_u ≈[Coq] coq_sq_h) -> False.
Proof.
  intro Heq.
  specialize (Heq tt); simpl in Heq.
  discriminate Heq.
Qed.

Example coq_sq_sides_differ : (coq_sq_v ≈[Coq] coq_sq_k) -> False.
Proof.
  intro Heq.
  specialize (Heq true); simpl in Heq.
  discriminate Heq.
Qed.

(** ** A square over the same quiver that does NOT commute / ** 在同一个箭宿上的一个不交换的平方 *)

(*
unit ----id----> unit
          |                |
         id        (fun _ => true)
          |                |
          v                v
         unit --(fun _ => false)--> bool

   One route lands on [true], the other on [false].

--------
unit ----id----> unit
          |                |
         id        (fun _ => true)
          |                |
          v                v
         unit --(fun _ => false)--> bool

   一条路线到达 [true]，另一条到达 [false]。
*)

Definition coq_bad_u : (unit : Coq) ~{Coq}~> (unit : Coq) := Datatypes.id.
Definition coq_bad_v : (unit : Coq) ~{Coq}~> (bool : Coq) := fun _ => true.
Definition coq_bad_h : (unit : Coq) ~{Coq}~> (unit : Coq) := Datatypes.id.
Definition coq_bad_k : (unit : Coq) ~{Coq}~> (bool : Coq) := fun _ => false.

Definition CoqNonCommutingSquare : Diagram SquareQuiver Coq :=
  SquareDiagram coq_bad_u coq_bad_v coq_bad_h coq_bad_k.

(* [Coq] is not thin: these two parallel morphisms are not [≈]. / [Coq] 并不薄：这两个平行态射并不是 [≈]。 *)
Example coq_parallel_not_equiv : (coq_bad_v ≈[Coq] coq_bad_k) -> False.
Proof.
  intro Heq.
  specialize (Heq tt); simpl in Heq.
  discriminate Heq.
Qed.

(*
The negative witness: [Commutative] is refuted for this diagram, over the
   very same quiver that carries the commuting one above.  The refutation goes
   through [square_commutes_inv], which instantiates the predicate at the two
   genuinely distinct paths of [SquareQuiver].

--------
负见证：[Commutative] 在此图中被驳斥，使用的是与上方可交换图相同的箭袋。驳斥通过 [square_commutes_inv] 实现，该对象在 [SquareQuiver] 的两条真正不同的路径上实例化了该谓词。
*)
Example coq_square_not_commutative : Commutative CoqNonCommutingSquare -> False.
Proof.
  intro Hc.
  pose proof (square_commutes_inv coq_bad_u coq_bad_v coq_bad_h coq_bad_k Hc)
    as Hbad.
  specialize (Hbad tt); simpl in Hbad.
  discriminate Hbad.
Qed.

(** ** The same, for the triangle / ** 对于三角形也是一样 *)

(*   bool --negb--> bool --negb--> bool   versus   bool --id--> bool / bool --negb--> bool --negb--> bool   与   bool --id--> bool  *)

Definition coq_tri_u : (bool : Coq) ~{Coq}~> (bool : Coq) := negb.
Definition coq_tri_v : (bool : Coq) ~{Coq}~> (bool : Coq) := negb.
Definition coq_tri_w : (bool : Coq) ~{Coq}~> (bool : Coq) := Datatypes.id.

Definition CoqCommutingTriangle : Diagram TriangleQuiver Coq :=
  TriangleDiagram coq_tri_u coq_tri_v coq_tri_w.

Example coq_triangle_commutative : Commutative CoqCommutingTriangle.
Proof.
  apply triangle_commutes.
  now intros [].
Qed.

(* Replacing the direct edge by [negb] breaks it, over the same quiver. / 用 [negb] 替换直接边会破坏它，在同一个箭袋上。 *)
Definition CoqNonCommutingTriangle : Diagram TriangleQuiver Coq :=
  TriangleDiagram coq_tri_u coq_tri_v coq_tri_u.

Example coq_triangle_not_commutative :
  Commutative CoqNonCommutingTriangle -> False.
Proof.
  intro Hc.
  pose proof (triangle_commutes_inv coq_tri_u coq_tri_v coq_tri_u Hc) as Hbad.
  specialize (Hbad true); simpl in Hbad.
  discriminate Hbad.
Qed.

(** ** The tree's shape-specific commutativity statements are instances / ** 树的形状特定的交换性陈述是实例 *)

(*
Theory/Diagram.v's header claims that the reusable in-tree statements of
   commutativity each fix one figure, and that [Commutative] generalizes them.
   These four results discharge that claim for two of the three, by exhibiting
   each as a [Commutative] diagram of the corresponding walking shape.  (The
   third, Construction/Sq.v's [dsq], is the same square as
   [square_commutative_iff] after permuting its four arguments to [dsq]'s
   [(h, u, v, k)] AND applying [symmetry]: the permutation alone yields
   [v ∘ h ≈ k ∘ u], while [dsq] is stated as [k ∘ u ≈ v ∘ h].  It is not
   restated here, to avoid importing the double-category development.)

--------
Theory/Diagram.v 的头文件声称，可重用的树内交换律语句各修复一个图形，并且 [Commutative] 将它们概括。这四个结果通过将每一个展示为对应行走形状的 [Commutative] 图，否定了三个中的两个的该声明。（第三个，即 Construction/Sq.v 的 [dsq]，是与 [square_commutative_iff] 相同的方形，只是其四个参数置换为 [dsq] 的 [(h, u, v, k)] 并应用 [symmetry]：仅置换就得到 [v ∘ h ≈ k ∘ u]，而 [dsq] 被作为 [k ∘ u ≈ v ∘ h] 陈述。这里没有重新陈述，以避免引入双范畴的发展。）
*)

(*
A cone leg triangle: [Structure/Cone.v]'s [cone_coherence] is exactly
   the commutativity of the walking triangle on the two legs and the image
   morphism between them.

   Division of labour between the two results below, stated precisely because
   it is easy to misread.  The [_iff] is a SHAPE match: its [ACone] instance is
   used only to name [vertex_map], and the biconditional holds for any three
   morphisms of matching type, so it carries no more content than
   [triangle_commutative_iff] with the arguments instantiated.  The cone-ness is
   used by [cone_leg_commutes], which discharges the right-hand side from
   [cone_coherence].  Together they exhibit [cone_coherence] as an instance;
   neither alone does.  The same split applies to the pullback pair below.

--------
一个锥形腿三角形：[Structure/Cone.v] 的 [cone_coherence] 正是关于两条腿上的行走三角形的交换律，以及它们之间的图像态射。

下面的两个结果的分工说明得很精确，因为很容易被误读。[_iff] 是一个形状匹配：它的 [ACone] 实例仅用于命名 [vertex_map]，并且双条件对任意三个匹配类型的态射都成立，因此它承载的内容不比将参数实例化后的 [triangle_commutative_iff] 更多。锥形性质被 [cone_leg_commutes] 使用，它从 [cone_coherence] 中释放出右边部分。它们一起将 [cone_coherence] 展示为一个实例；单独没有一个能做到。下面的拉回对也适用相同的分工。
*)
Corollary cone_leg_commutative_iff {J C : Category} {F : J ⟶ C} {c : C}
          `{@ACone J C c F} {x y : J} (f : x ~{J}~> y) :
  Commutative (TriangleDiagram (vertex_map x) (fmap[F] f) (vertex_map y))
    ↔ fmap[F] f ∘ vertex_map x ≈ vertex_map y.
Proof. apply triangle_commutative_iff. Qed.

Corollary cone_leg_commutes {J C : Category} {F : J ⟶ C} {c : C}
          `{@ACone J C c F} {x y : J} (f : x ~{J}~> y) :
  Commutative (TriangleDiagram (vertex_map x) (fmap[F] f) (vertex_map y)).
Proof. apply triangle_commutes, cone_coherence. Qed.

(*
A pullback square: [Theory/Morphisms/Stability.v]'s
   [is_pullback_commutes] is exactly the commutativity of the walking square
   on the two projections and the two given morphisms.

--------
一个拉回方：[Theory/Morphisms/Stability.v] 的 [is_pullback_commutes] 恰好是步行方在两个投影和两个给定态射上的交换性。
*)
Corollary pullback_square_commutative_iff {C : Category} {x y z : C}
          (f : x ~> z) (g : y ~> z) {P : C} (p1 : P ~> x) (p2 : P ~> y) :
  Commutative (SquareDiagram p1 f p2 g) ↔ f ∘ p1 ≈ g ∘ p2.
Proof. apply square_commutative_iff. Qed.

Corollary pullback_square_commutes {C : Category} {x y z : C}
          {f : x ~> z} {g : y ~> z} {P : C} {p1 : P ~> x} {p2 : P ~> y}
          (Hpb : IsPullback f g P p1 p2) :
  Commutative (SquareDiagram p1 f p2 g).
Proof. apply square_commutes, (is_pullback_commutes Hpb). Qed.


(** ** The walking loop: a diagram that draws a non-identity endomorphism / ** 行走环：绘制非同一自同态的图表 *)

(*
Theory/Diagram.v's [loop_commutative_iff] proves that over the walking loop,
   [Commutative] is exactly "the drawn endomorphism is the identity".  That is
   the clause of the predicate driven by the EMPTY path, and it is the one no
   figure-fixing statement can express.  Here it is exercised concretely, in
   both directions, over the same category [Coq].

   [negb] is a non-identity endomorphism of [bool], so the diagram drawing it
   is not [Commutative] -- while the diagram drawing [Datatypes.id] is.

--------
Theory/Diagram.v 的 [loop_commutative_iff] 证明了在步行循环上，[Commutative] 恰好是“所绘制的自同态是恒等映射”。也就是说，它是由 EMPTY 路径驱动的谓词的子句，并且没有任何固定图形的语句可以表达它。在这里，它以具体方式在两个方向上应用于同一范畴 [Coq]。

[negb] 是 [bool] 的非恒等自同态，所以绘制它的图不是 [Commutative] —— 而绘制 [Datatypes.id] 的图是。
*)

Definition CoqLoopNegb : Diagram LoopQuiver Coq :=
  LoopDiagram (negb : (bool : Coq) ~{Coq}~> (bool : Coq)).

Definition CoqLoopId : Diagram LoopQuiver Coq :=
  LoopDiagram (Datatypes.id : (bool : Coq) ~{Coq}~> (bool : Coq)).

(*
The negative witness.  Note there is no parallel PAIR of nonempty paths at
   work: what refutes commutativity is the one-edge path against [tnil].

--------
负见证。注意这里没有一对平行的非空路径在起作用：否定交换性的，是针对 [tnil] 的单边路径。
*)
Example coq_loop_negb_not_commutative : Commutative CoqLoopNegb -> False.
Proof.
  intro Hc.
  pose proof (loop_commutes_inv _ Hc true) as H.
  discriminate H.
Qed.

(* The positive witness over the same shape and the same category. / 对同一形状和同一范畴的积极证据。 *)
Example coq_loop_id_commutative : Commutative CoqLoopId.
Proof.
  apply loop_commutes.
  now intro b.
Qed.
