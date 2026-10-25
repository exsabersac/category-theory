Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Free.Quiver.
From Coq Require Import Eqdep_dec.

Generalizable All Variables.

(*
   * * Two functors between free categories, agreeing on objects 

   --------
   * * 两个自由范畴之间的函子，在对象上相同
*)

(*
 Book: Fong, Spivak, "An Invitation to Applied Category Theory: Seven
 Sketches in Compositionality", Cambridge University Press, 2019,
 Section 3.3.2, Exercise 3.40, printed p. 92
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 Springer GTM 5, 1998, Section I.3 ("Functors"), printed p. 15
 nLab: https://ncatlab.org/nlab/show/free+category

 Exercise 3.40 asks for two functors that agree on objects and differ on
 morphisms, and supplies the cheapest possible witness: from the free
 category on a single arrow to the free category on two parallel arrows,
 send the generator to one parallel arrow or to the other.  The two
 functors have the SAME object function -- here literally [fun n => n],
 the identity -- and different arrow functions.  This is Mac Lane's
 Section I.3 question with the algebra removed; the group-theoretic
 reading is in Instance/Grp/TwoFunctors.v.

 Everything rests on Construction/Free/Quiver.v.  A quiver built by
 [Build_Quiver_Standard_Eq] compares edges by propositional equality, and
 [FreeOnQuiver] makes its morphisms the type-aligned paths of Lib/TList.v
 with [tlist_quiver_equiv] as the hom-setoid; a quiver homomorphism into
 the underlying quiver of a category induces a functor out of the free
 category ([InducedFunctor], which is also the mediating functor in the
 proof of the universal property [UniversalArrowQuiverCat]).  So both
 functors here are induced from a choice of image for the single
 generator.

 WHERE THE DIFFERENCE LIVES.  [fs_singleton_distinct] is the load-bearing
 lemma: the two one-edge paths are inequivalent IN THE HOM-SETOID of the
 target free category.  Unfolding [tlist_quiver_equiv] on two singletons
 leaves an equality of intermediate nodes and an equation between the two
 edges after transport along it; uniqueness of identity proofs on the
 two-element node type (Hedberg, via the stdlib's axiom-free [UIP_dec])
 discharges the first, and the second is then an equality of distinct
 constructors.  So the separation is a statement about the setoid, not
 about the shape of the terms.

 The distinctness is stated in [Functor_StrictEq_Setoid]
 (Theory/Functor.v), the hom-setoid of [StrictCat]
 (Instance/StrictCat.v).  No claim is made here about the weak setoid
 [Functor_Setoid] (Theory/Functor.v) of [Cat] (Instance/Cat.v),
 which identifies naturally isomorphic functors; the twisted pair of
 Functor/Twist.v and Instance/Grp/TwoFunctors.v is the one that
 deliberately exhibits a pair separated strictly and identified weakly. 

 --------
 书籍：Fong, Spivak，《应用范畴论邀请：组合性的七个草图》，剑桥大学出版社，2019年，第3.3.2节，练习3.40，第92页
 书籍：Mac Lane，《为工作中的数学家准备的范畴论》，第2版，Springer GTM 5，1998年，第I.3节（“函子”），第15页
 nLab: https://ncatlab.org/nlab/show/free+category练习 3.40 要求给出两个在对象上相同但在态射上不同的函子，并提供了最简单的示例：从单一箭头的自由范畴到两条平行箭头的自由范畴，将生成元映射到其中一条平行箭头或另一条。两个函子的对象函数相同 —— 在这里字面上是 [fun n => n]，即恒等函数 —— 而箭头函数不同。这是 Mac Lane 第 I.3 节的问题，只是移除了代数部分；群论的解读见 Instance/Grp/TwoFunctors.v。一切都基于 Construction/Free/Quiver.v。[Build_Quiver_Standard_Eq] 构建的箭袋通过命题等式比较边，[FreeOnQuiver] 将其态射设为 Lib/TList.v 的类型对齐路径，并以 [tlist_quiver_equiv] 作为 Hom-集合；进入某个范畴的底层箭袋的箭袋同态会诱导出自由范畴的函子（[InducedFunctor]，同时也是通用性质证明中的中介函子 [UniversalArrowQuiverCat]）。因此，这里的两个函子都是由单个生成元的像的选择所诱导的。差异所在。[fs_singleton_distinct] 是承重的引理：在目标自由范畴的 HOM-集合体中，两个单边路径是不等价的。在两个单元素上展开 [tlist_quiver_equiv] 会留下中间节点的等式，以及沿其传输后两个边之间的方程；在两元素节点类型上身份证明的唯一性（Hedberg，通过 stdlib 的无公理 [UIP_dec]）解决了第一个问题，而第二个则是不同构造子的等式。因此，这种分离是关于集合体的陈述，而不是关于项的形状。这种不同性在 [Functor_StrictEq_Setoid] (Theory/Functor.v) 中陈述，在 [StrictCat] (Instance/StrictCat.v) 的同态集合中体现。这里并未对 [Functor_Setoid] (Theory/Functor.v) 的弱同态集合 [Cat] (Instance/Cat.v) 作任何声明，该集合自然地识别同构的函子；而 Functor/Twist.v 与 Instance/Grp/TwoFunctors.v 的扭曲对则是故意展示一对在严格意义上分离、在弱意义上被识别的函子。
*)

(** ** The two quivers / ** 两个箭袋 *)

(* Two nodes, with decidable equality. / 两个节点，具有可判等性。 *)
Inductive fs_node : Type := fs_dom | fs_cod.

Definition fs_node_eq_dec (x y : fs_node) : {x = y} + {x <> y}.
Proof.
  destruct x, y.
  - now left.
  - now right.
  - now right.
  - now left.
Defined.

(* One arrow from [fs_dom] to [fs_cod] ... / 从 [fs_dom] 到 [fs_cod] 的一支箭... *)
Inductive fs_one_edge : fs_node → fs_node → Type :=
  | fs_gen : fs_one_edge fs_dom fs_cod.

(* ... and two parallel arrows between the same nodes. / ... 并且在相同的节点之间有两条平行箭头。 *)
Inductive fs_two_edges : fs_node → fs_node → Type :=
  | fs_left  : fs_two_edges fs_dom fs_cod
  | fs_right : fs_two_edges fs_dom fs_cod.

Definition WalkingArrowQuiver : Quiver :=
  Build_Quiver_Standard_Eq fs_node fs_one_edge.

Definition ParallelPairQuiver : Quiver :=
  Build_Quiver_Standard_Eq fs_node fs_two_edges.

Definition FreeWalkingArrow : Category := FreeOnQuiver WalkingArrowQuiver.

Definition FreeParallelPair : Category := FreeOnQuiver ParallelPairQuiver.

(** ** The two functors / ** 这两个函子 *)

(* The generator goes to the left parallel arrow ... / 发电机向左边的平行箭头移动... *)
Definition free_pick_left_hom :
  QuiverHomomorphism WalkingArrowQuiver (QuiverOfCat FreeParallelPair).
Proof.
  unshelve notypeclasses refine
    (Build_QuiverHomomorphism WalkingArrowQuiver (QuiverOfCat FreeParallelPair)
       (fun n => n)
       (fun _ _ e => match e with fs_gen => tlist_singleton fs_left end) _).
  intros x y e e' He.
  rewrite He.
  reflexivity.
Defined.

(* ... or to the right one. Nothing else changes. / ...或者向右边。其他什么都不变。 *)
Definition free_pick_right_hom :
  QuiverHomomorphism WalkingArrowQuiver (QuiverOfCat FreeParallelPair).
Proof.
  unshelve notypeclasses refine
    (Build_QuiverHomomorphism WalkingArrowQuiver (QuiverOfCat FreeParallelPair)
       (fun n => n)
       (fun _ _ e => match e with fs_gen => tlist_singleton fs_right end) _).
  intros x y e e' He.
  rewrite He.
  reflexivity.
Defined.

Definition FreePickLeft : FreeWalkingArrow ⟶ FreeParallelPair :=
  InducedFunctor WalkingArrowQuiver free_pick_left_hom.

Definition FreePickRight : FreeWalkingArrow ⟶ FreeParallelPair :=
  InducedFunctor WalkingArrowQuiver free_pick_right_hom.

(*
 The object functions are equal as FUNCTIONS, not merely pointwise: both
 are the identity function on the two nodes.  (This is an equality of
 object maps, which is what the exercise is about; morphisms are still
 compared with ≈ everywhere below.) 

 --------
 作为函数，对象函数是相等的，而不仅仅是在各点上相等：它们都是这两个节点上的恒等函数。（这是对象映射的相等性，这正是练习所涉及的；以下 morphism 仍然用 ≈ 进行比较。）
*)
Lemma free_two_functors_same_objects :
  fobj[FreePickLeft] = fobj[FreePickRight].
Proof. reflexivity. Qed.

(* * ** The generator, and where the two functors send it / * ** 生成器，以及两个函子将其发送到的位置 *)

(*
 A functor induced from a quiver homomorphism sends a one-edge path to
 the chosen image of that edge: the induction defining [InducedFunctor]
 contributes an identity on the empty tail. 

 --------
 由箭图同态引起的函子将一条单边路径发送到该边的选定像：定义 [InducedFunctor] 的归纳在空尾上贡献一个恒等映射。
*)
Lemma fmap_free_singleton {G : Quiver} {C : Category}
  (F : QuiverHomomorphism G (QuiverOfCat C)) {x y : G} (e : edges x y) :
  fmap[InducedFunctor G F] (tlist_singleton e) ≈ @fedgemap _ _ F x y e.
Proof.
  simpl.
  apply id_left.
Qed.

Example free_pick_left_generator :
  fmap[FreePickLeft] (tlist_singleton fs_gen) ≈ tlist_singleton fs_left.
Proof. apply (fmap_free_singleton free_pick_left_hom fs_gen). Qed.

Example free_pick_right_generator :
  fmap[FreePickRight] (tlist_singleton fs_gen) ≈ tlist_singleton fs_right.
Proof. apply (fmap_free_singleton free_pick_right_hom fs_gen). Qed.

(** ** The separation / ** 分离 *)

(*
 The hom-setoid of the target really does separate the two generating
 paths: it is not a setoid that identifies everything. 

 --------
 目标的同态集合确实把两个生成路径区分开：它不是一个把所有东西都识别为同一的集合。
*)
Lemma fs_singleton_distinct :
  @equiv _ (@homset FreeParallelPair fs_dom fs_cod)
    (tlist_singleton fs_left) (tlist_singleton fs_right) → False.
Proof.
  simpl.
  unfold tlist_quiver_equiv, tlist_singleton.
  simpl.
  intros [q Hedge _].
  rewrite (UIP_dec fs_node_eq_dec q eq_refl) in Hedge.
  assert (Hlr : fs_left = fs_right) by exact Hedge.
  discriminate.
Qed.

(*
 The concrete separating datum: the two arrow maps disagree on the
 generator, in the hom-setoid of the target. 

 --------
 具体的分离基准：在目标的同态集内，两张箭头图对生成元的看法不一致。
*)
Theorem free_two_functors_differ_on_generator :
  fmap[FreePickLeft] (tlist_singleton fs_gen)
    ≈ fmap[FreePickRight] (tlist_singleton fs_gen) → False.
Proof.
  intro H.
  apply fs_singleton_distinct.
  rewrite <- free_pick_left_generator.
  rewrite <- free_pick_right_generator.
  exact H.
Qed.

(*
 Two functors, the same object function, different arrow functions:
 distinct in the strict functor setoid.  The object components of a
 strict equality are loops at the two nodes, which uniqueness of identity
 proofs collapses to [eq_refl]; the arrow condition then says the two
 images of the generator agree in the hom-setoid, and they do not. 

 --------
 两个函子，相同的对象函数，不同的箭头函数：在严格函子集合等价类中是不同的。严格等式的对象分量是在两个节点的循环，身份证明的唯一性将其坍缩为 [eq_refl]；然后箭头条件说明生成元的两个像在同态集合等价类中一致，但它们不一致。
*)
Theorem free_two_functors_distinct :
  @equiv _ (@Functor_StrictEq_Setoid FreeWalkingArrow FreeParallelPair)
    FreePickLeft FreePickRight → False.
Proof.
  intros [eq_on_obj coherent].
  pose proof (coherent fs_dom fs_cod (tlist_singleton fs_gen)) as Hc.
  rewrite (UIP_dec fs_node_eq_dec (eq_on_obj fs_dom) eq_refl),
          (UIP_dec fs_node_eq_dec (eq_on_obj fs_cod) eq_refl) in Hc.
  (* both transports are along [eq_refl] and vanish / 两种运输方式都沿着 [eq_refl] 并消失 *)
  apply free_two_functors_differ_on_generator.
  exact Hc.
Qed.
