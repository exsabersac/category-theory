Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Shapes.
Require Import Category.Structure.Thin.
Require Import Category.Construction.Product.
Require Import Category.Construction.Cylinder.
Require Import Category.Instance.Two.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Ordinal.
Require Import Category.Instance.Square.Product.

Require Import Coq.Lists.List.

Generalizable All Variables.

(*
   * * The shape 2 × 3, and commutative rectangles

   Book: Riehl, Category Theory in Context, Dover 2016, §1.6,
   Example 1.6.9, printed p. 42
   Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,
   §II.8, Exercise 1, printed p. 52

   One step up from the walking commutative square.  A diagram of shape
   2 × 3 in [C] is a rectangle

   X0 --u--> X1 --v--> X2
   |         |         |
   p         q         r
   v         v         v
   Y0 --u'--> Y1 --v'--> Y2

   in which BOTH squares commute — and then, necessarily, so does the
   outer rectangle.  That last clause is the content of the example:
   two commuting squares paste to one, and the shape category forces
   the pasting rather than asking for it, because the composite
   [X0 → X2] and the composite [Y0 → Y2] are already arrows of 2 × 3
   and functoriality does the rest.

   WHAT IS DELIVERED.  (1) the shape [Rect := _2 ∏ _3] over
   [Instance/Ordinal.v]'s [_3], with its thinness; (2) the named
   generating arrows and, from any [F : Rect ⟶ C], the six objects and
   seven arrows of the rectangle together with the LEFT square, the
   RIGHT square, the OUTER rectangle and the two “short diagonals” —
   every one of them an equation [F] satisfies, not a hypothesis;
   (3) the pasting principle as a free-standing categorical lemma
   ([paste_squares]) and the observation that in a diagram of this
   shape the outer rectangle is forced twice over, once by pasting and
   once by thinness of the shape ([rect_outer_two_ways]); (4) the
   converse — a commutative rectangle, i.e. six objects, seven arrows
   and the TWO square equations, determines a functor
   ([RectFunctor]), with its action on all seven generators recovered;
   (5) the arrow count of the shape, 18 = 3 × 6, with 6 identities and
   12 others, cross-checked against [Instance/Ordinal.v]'s own count of
   the arrows of [_3].

   HOW THE CONVERSE IS BUILT, and why not by a presentation.
   [Instance/Square.v] builds its shape by generators and relations and
   reads the universal property off [presented_universal].  The same
   route is available here — six nodes, seven edges, two relations —
   but it would need a second path classification over a quiver with
   paths of length up to three, and the tree already contains every
   piece needed for the shorter route: [Theory/Shapes.v]'s
   [Functor_of_Pair] makes each ROW a functor [_3 ⟶ C],
   [Construction/Cylinder.v]'s [Cyl_functor] turns a natural
   transformation between two such into a functor on the cylinder
   [_3 ∏ _2], and [Construction/Product.v]'s [Swap] reorders the
   factors.  So the rectangle is assembled as “a natural
   transformation between two composable pairs”, which is what Riehl's
   example says it is.  The one piece the tree lacked is the
   naturality criterion for a PLAIN family of components (as against
   [Instance/Ordinal.v]'s [ord_naturality_from_steps], which is stated
   for a family of ISOMORPHISMS); it is supplied below as
   [ord_transform_naturality], and the donor's version is exhibited as
   its instance ([ord_naturality_from_steps_is_instance]) rather than
   the relationship being asserted.

   THE TWO SQUARE EQUATIONS ARE THE WHOLE HYPOTHESIS.  Nothing below
   asks for the outer rectangle to commute: it is derived, in
   [paste_squares] from the two squares alone and in
   [rect_outer_commutes] from functoriality alone.

   WHAT IS NOT DELIVERED.  No presentation of this shape by generators
   and relations (see above), hence no free-versus-presented arrow
   count for it — the count below is of [_2 ∏ _3] directly.  The
   CONVERSE half is pinned at [C : Category@{co Set Set}], inherited
   from [Functor_of_Pair] and [Cyl_functor]; the measurement and the
   reason are stated at the [Converse] section below, the forward half
   carries no pin, and Test/ProbeSquare.v guards both sides.  No
   uniqueness clause for [RectFunctor]: [Cyl_functor_unique]
   ([Construction/Cylinder.v]) supplies uniqueness on the cylinder, but
   transporting it across [Swap] and across the row-functor
   construction is not done here, and none of the statements below
   depend on it.  No identification of [Rect] with a presented
   category, and no [n × m] generalisation. 

   --------
   * * 形状 2 × 3 以及可交换矩形

   书籍：Riehl，《Category Theory in Context》，Dover 2016，§1.6，
   示例 1.6.9，第 42 页
   书籍：Mac Lane，《Categories for the Working Mathematician》，第 2 版，
   §II.8，练习 1，第 52 页

   比行走的可交换方形高一层。在  [C]  中形状为 2 × 3 的图是一个矩形

   X0 --u--> X1 --v--> X2
   |         |         |
   p         q         r
   v         v         v
   Y0 --u'--> Y1 --v'--> Y2在其中两个方格都可交换——那么，外部矩形也必然可交换。最后这一条就是例子的内容：两个可交换的方格粘合成一个，而形状范畴强制进行这种粘合，而不是要求它进行，因为复合箭头  [X0 → X2]  和复合箭头  [Y0 → Y2]  已经是 2 × 3 的箭头，函子性完成其余部分。交付内容。（1）形状 [Rect := _2 ∏ _3] 在 [Instance/Ordinal.v] 的 [_3] 上，以及其薄性；（2）命名的生成箭头，以及从任何 [F : Rect ⟶ C] 出发，矩形的六个对象和七个箭头，以及左方平方、右方平方、外部矩形和两个“短对角线”——它们每一个都是 [F] 满足的方程，而非假设；（3）作为独立范畴引理的粘贴原理（[paste_squares]）以及观察到在该形状的图示中，外部矩形被强制两次，一次通过粘贴，一次通过形状的薄性（[rect_outer_two_ways]）；（4）逆命题——一个交换矩形，即六个对象，七支箭头以及两个平方方程，确定了一个函子（[RectFunctor]），其对七个生成元的作用已恢复；（5）该形状的箭头计数为18 = 3 × 6，其中6个为恒等箭头，另外12个为其他箭头，并与[Instance/Ordinal.v]自身对[_3]箭头的计数进行了交叉验证。对偶是如何构建的，以及为什么不是通过演示来构建。[Instance/Square.v] 通过生成元和关系构建其形状，并从 [presented_universal] 中读取其普适性质。这里也可采用同样的路线——六个节点，七条边，两个关系——但这需要在一个箭图上进行第二次路径分类，该箭图的路径长度可达三，而树已经包含了更短路径所需的所有部分：[Theory/Shapes.v] 的 [Functor_of_Pair] 使每一行成为函子 [_3 ⟶ C]，[Construction/Cylinder.v] 的 [Cyl_functor] 将二者之间的自然变换转化为柱面 [_3 ∏ _2] 上的函子，[Construction/Product.v] 的 [Swap] 重新排列因子。因此，这个矩形被组装成“两个可组合对之间的自然变换”，这正是 Riehl 的例子所说明的。树缺少的一部分是 PLAIN 组件族的自然性准则（与 [Instance/Ordinal.v] 的 [ord_naturality_from_steps] 相对，后者是针对同构族陈述的）；它在下面作为 [ord_transform_naturality] 提供，并且给出了捐赠者版本作为其实例（[ord_naturality_from_steps_is_instance]），而不是断言的关系。

   这两个平方方程是整个假设。下面没有任何内容要求外部矩形交换：它在 [paste_squares] 中仅从两个平方导出，在 [rect_outer_commutes] 中仅从函子性导出。未交付的内容。没有通过生成器和关系（见上文）对该形态的表示，因此没有其自由与呈现箭头数量的对比——下面的计数是直接对 [_2 ∏ _3] 的计数。CONVERSE 部分固定在 [C : Category@{co Set Set}]，由 [Functor_of_Pair] 和 [Cyl_functor] 继承；测量和原因在下面 [Converse] 部分说明，正向部分没有固定，Test/ProbeSquare.v 保护两侧。[RectFunctor] 没有唯一性条款：[Cyl_functor_unique] ([Construction/Cylinder.v]) 在圆柱上提供唯一性，但在 [Swap] 以及跨行函子构造的传输在此未进行，以下陈述亦不依赖它。[Rect] 没有与呈现范畴的标识，也没有 [n × m] 的推广。
*)

(** ** The shape / ** 形状 *)

Definition Rect : Category := _2 ∏ _3.

Lemma Three_Thin : Thin _3.
Proof. intros x y f g; exact (ord_thin f g). Qed.

Lemma Rect_Thin : Thin Rect.
Proof. exact (Thin_Product Two_Thin Three_Thin). Qed.

(*
   * The generating arrows: horizontal ones live in the [_3] factor at a
   fixed row, vertical ones in the [_2] factor at a fixed column. 

   --------
   * 生成箭头：水平箭头存在于固定行的 [_3] 因子中，垂直箭头存在于固定列的 [_2] 因子中。
*)
Definition rect_horiz (i : TwoObj) {j j' : Ord_obj 3} (s : j ~{_3}~> j') :
  (i, j) ~{Rect}~> (i, j') := (id, s).

Definition rect_vert (j : Ord_obj 3) : (TwoX, j) ~{Rect}~> (TwoY, j) :=
  (TwoXY, id).

(*
   * ** Pasting, as a free-standing principle

   Riehl's “two commuting squares paste to one”, with no shape
   category in sight: it is three rewrites. 

   --------
   * ** 粘贴，作为一个独立的原则

   Riehl 的 “两个可交换的方格粘贴为一个”，没有任何形状类别的迹象：它是三个重写。
*)
Lemma paste_squares {C : Category} {a b c a' b' c' : C}
  (u : a ~> b) (v : b ~> c) (u' : a' ~> b') (v' : b' ~> c')
  (p : a ~> a') (q : b ~> b') (r : c ~> c') :
  q ∘ u ≈ u' ∘ p → r ∘ v ≈ v' ∘ q → r ∘ (v ∘ u) ≈ (v' ∘ u') ∘ p.
Proof.
  intros Hl Hr.
  rewrite comp_assoc, Hr.
  rewrite <- comp_assoc, Hl.
  now rewrite comp_assoc.
Qed.

(*
   * ** What a diagram of shape 2 × 3 is

   Every equation below holds of an ARBITRARY [F], with no hypothesis:
   the shape supplies them. 

   --------
   * ** 形状 2 × 3 的图示是什么

   下面的每个方程都适用于任意的 [F]，没有任何前提条件：
   形状本身提供它们。
*)

Section Diagram.

Context {C : Category}.
Context (F : Rect ⟶ C).

(** The six objects. / 六个物体。 *)
Definition rect_X0 : C := fobj[F] (TwoX, ord3_0).
Definition rect_X1 : C := fobj[F] (TwoX, ord3_1).
Definition rect_X2 : C := fobj[F] (TwoX, ord3_2).
Definition rect_Y0 : C := fobj[F] (TwoY, ord3_0).
Definition rect_Y1 : C := fobj[F] (TwoY, ord3_1).
Definition rect_Y2 : C := fobj[F] (TwoY, ord3_2).

(** The four horizontal arrows and the three vertical ones. / 四条水平箭头和三条垂直箭头。 *)
Definition rect_u : rect_X0 ~> rect_X1 := fmap[F] (rect_horiz TwoX three_01).
Definition rect_v : rect_X1 ~> rect_X2 := fmap[F] (rect_horiz TwoX three_12).
Definition rect_u' : rect_Y0 ~> rect_Y1 := fmap[F] (rect_horiz TwoY three_01).
Definition rect_v' : rect_Y1 ~> rect_Y2 := fmap[F] (rect_horiz TwoY three_12).
Definition rect_p : rect_X0 ~> rect_Y0 := fmap[F] (rect_vert ord3_0).
Definition rect_q : rect_X1 ~> rect_Y1 := fmap[F] (rect_vert ord3_1).
Definition rect_r : rect_X2 ~> rect_Y2 := fmap[F] (rect_vert ord3_2).

(*
   * The three “diagonal” arrows: the long one across the whole
   rectangle, and the two short ones, one per square.  Each is the
   image of a genuine arrow of the shape — which is why their
   well-definedness IS the rectangle's commutativity. 

   --------
   * 三个“对角线”箭头：一个长箭头贯穿整个矩形，两个短箭头，各在一个方格中。它们每一个都是该形状的真实箭头的像——这就是为什么它们的良定义性就是矩形的交换性。
*)
Definition rect_long_diagonal : rect_X0 ~> rect_Y2 :=
  fmap[F] (@compose Rect (TwoX, ord3_0) (TwoX, ord3_2) (TwoY, ord3_2)
             (rect_vert ord3_2) (rect_horiz TwoX three_02)).

Definition rect_diag_left : rect_X0 ~> rect_Y1 :=
  fmap[F] (@compose Rect (TwoX, ord3_0) (TwoX, ord3_1) (TwoY, ord3_1)
             (rect_vert ord3_1) (rect_horiz TwoX three_01)).

Definition rect_diag_right : rect_X1 ~> rect_Y2 :=
  fmap[F] (@compose Rect (TwoX, ord3_1) (TwoX, ord3_2) (TwoY, ord3_2)
             (rect_vert ord3_2) (rect_horiz TwoX three_12)).

(*
   * Each of the equations below is proved the same way: unfold the
   names, collapse the composites of images into images of composites,
   and observe that the two arrows of the shape being compared are
   parallel, hence equal, [Rect] being thin.  The OBJECT abbreviations
   must be unfolded too, not only the morphism ones: [fmap_comp]'s
   middle object has to be recognised as [fobj[F] _], and [rect_X1] is
   not syntactically of that form. 

   --------
   * 下面的每个方程都以相同的方式证明：展开名称，将像的合成折叠为合成的像，并观察被比较的形状的两条箭头是平行的，因此相等，因为 [Rect] 是薄的。对象缩写也必须展开，而不仅仅是态射的缩写：[fmap_comp] 的中间对象必须被识别为 [fobj[F] _]，并且 [rect_X1] 在语法上不是这种形式。
*)
Local Ltac rect_shape :=
  unfold rect_long_diagonal, rect_diag_left, rect_diag_right,
         rect_u, rect_v, rect_u', rect_v', rect_p, rect_q, rect_r,
         rect_X0, rect_X1, rect_X2, rect_Y0, rect_Y1, rect_Y2;
  rewrite <- !fmap_comp;
  apply fmap_respects;
  exact (Rect_Thin _ _ _ _).

(*
   * Each square commutes, because the two composites are already the
   same arrow of the shape. 

   --------
   * 每个方格都是交换的，因为两个复合已经是相同形状的箭头。
*)
Lemma rect_left_commutes : rect_q ∘ rect_u ≈ rect_u' ∘ rect_p.
Proof. rect_shape. Qed.

Lemma rect_right_commutes : rect_r ∘ rect_v ≈ rect_v' ∘ rect_q.
Proof. rect_shape. Qed.

(** The outer rectangle, likewise. / 外部矩形也是如此。 *)
Theorem rect_outer_commutes :
  rect_r ∘ (rect_v ∘ rect_u) ≈ (rect_v' ∘ rect_u') ∘ rect_p.
Proof. rect_shape. Qed.

(*
   * ...and it is forced twice over: the pasting principle derives the
   same equation from the two squares alone, with no reference to the
   shape at all. 

   --------
   * ……而且它被迫两次：拼贴原理仅从两个正方形得出相同的方程，完全不参考形状。
*)
Theorem rect_outer_two_ways :
  rect_r ∘ (rect_v ∘ rect_u) ≈ (rect_v' ∘ rect_u') ∘ rect_p.
Proof.
  exact (paste_squares rect_u rect_v rect_u' rect_v' rect_p rect_q rect_r
           rect_left_commutes rect_right_commutes).
Qed.

(*
   * The long diagonal is the common value of every path from X0 to
   Y2. 

   --------
   * 从 X0 到 Y2 的每条路径的公共值是长对角线。
*)
Theorem rect_long_via_top :
  rect_long_diagonal ≈ rect_r ∘ (rect_v ∘ rect_u).
Proof. rect_shape. Qed.

Theorem rect_long_via_bottom :
  rect_long_diagonal ≈ (rect_v' ∘ rect_u') ∘ rect_p.
Proof. rewrite rect_long_via_top; exact rect_outer_commutes. Qed.

(** The two short diagonals, likewise, one per square. / 两条短对角线，同样，每个方格一条。 *)
Theorem rect_diag_left_via_top : rect_diag_left ≈ rect_q ∘ rect_u.
Proof. rect_shape. Qed.

Theorem rect_diag_left_via_bottom : rect_diag_left ≈ rect_u' ∘ rect_p.
Proof. rewrite rect_diag_left_via_top; exact rect_left_commutes. Qed.

Theorem rect_diag_right_via_top : rect_diag_right ≈ rect_r ∘ rect_v.
Proof. rect_shape. Qed.

Theorem rect_diag_right_via_bottom : rect_diag_right ≈ rect_v' ∘ rect_q.
Proof. rewrite rect_diag_right_via_top; exact rect_right_commutes. Qed.

(*
   * The inner parallelogram: the long diagonal factors through either
   short one. 

   --------
   * 内部平行四边形：长对角线通过任意一条短对角线。
*)
Theorem rect_long_through_left : rect_long_diagonal ≈ rect_v' ∘ rect_diag_left.
Proof.
  rewrite rect_long_via_bottom, rect_diag_left_via_bottom.
  now rewrite comp_assoc.
Qed.

Theorem rect_long_through_right : rect_long_diagonal ≈ rect_diag_right ∘ rect_u.
Proof.
  rewrite rect_long_via_top, rect_diag_right_via_top.
  now rewrite <- comp_assoc.
Qed.

End Diagram.

(*
   * ** Naturality on the generating steps, for a plain family

   [Instance/Ordinal.v]'s [ord_naturality_from_steps] asks for a family
   of ISOMORPHISMS and concludes naturality of their forward legs.  Its
   proof never uses the inverses, so the same induction proves the same
   conclusion for an arbitrary family of morphisms; that is what a
   natural transformation out of an ordinal needs, and it is what the
   rectangle's converse consumes.  The donor is recovered as an
   instance below, so the claim “the same induction” is checked rather
   than asserted. 

   --------
   * ** 在生成步骤上的自然性，对于一个普通的族

   [Instance/Ordinal.v] 的 [ord_naturality_from_steps] 要求一个同构族，并得出它们前向部分的自然性。它的证明从未使用逆映射，因此相同的归纳法可以证明任意一个态射族得出同样的结论；这就是从一个序数中出发的自然变换所需要的，也是矩形的逆向所利用的。下文展示了捐赠者的一个实例，因此“相同归纳法”的说法是经过检验的，而不是仅仅声明。
*)
Theorem ord_transform_naturality@{o h p co ch cp}
  {C : Category@{co ch cp}} {n : nat}
  (F G : Ordinal@{o h p} (S n) ⟶ C)
  (η : ∀ x : Ord_obj@{o} (S n), F x ~> G x)
  (Hgen : ∀ k : Ord_obj@{o} n,
      η (ord_succ k) ∘ fmap[F] (ord_step k)
        ≈ fmap[G] (ord_step k) ∘ η (ord_incl k)) :
  ∀ (i j : nat) (f : le_t i j) (Hi : le_t (S i) (S n)) (Hj : le_t (S j) (S n)),
    η (ord_at j Hj) ∘ @fmap _ _ F (ord_at i Hi) (ord_at j Hj) f
      ≈ @fmap _ _ G (ord_at i Hi) (ord_at j Hj) f ∘ η (ord_at i Hi).
Proof.
  intros i j f; induction f as [| m f' IH]; intros Hi Hj.
  - rewrite (le_t_irr Hj Hi).
    assert (EF : @fmap _ _ F (ord_at i Hi) (ord_at i Hi) le_t_n ≈ id)
      by exact (@fmap_id _ _ F (ord_at i Hi)).
    assert (EG : @fmap _ _ G (ord_at i Hi) (ord_at i Hi) le_t_n ≈ id)
      by exact (@fmap_id _ _ G (ord_at i Hi)).
    rewrite EF, EG.
    now rewrite id_left, id_right.
  - pose (Hm := le_t_SS_inv Hj : le_t (S m) n).
    rewrite (le_t_irr Hj (le_t_SS Hm)).
    assert (Estep : @fmap _ _ F (ord_at i Hi) (ord_at (S m) (le_t_SS Hm)) (le_t_S f')
              ≈ fmap[F] (ord_step (ord_at m Hm))
                  ∘ @fmap _ _ F (ord_at i Hi) (ord_at m (le_t_S Hm)) f').
    { rewrite <- fmap_comp.
      apply fmap_respects, le_t_irr. }
    assert (Estep' : @fmap _ _ G (ord_at i Hi) (ord_at (S m) (le_t_SS Hm)) (le_t_S f')
              ≈ fmap[G] (ord_step (ord_at m Hm))
                  ∘ @fmap _ _ G (ord_at i Hi) (ord_at m (le_t_S Hm)) f').
    { rewrite <- fmap_comp.
      apply fmap_respects, le_t_irr. }
    rewrite Estep, Estep'.
    rewrite comp_assoc.
    rewrite (Hgen (ord_at m Hm)).
    rewrite <- comp_assoc.
    rewrite (IH Hi (le_t_S Hm)).
    now rewrite comp_assoc.
Qed.

(*
   * The donor is the special case at the forward legs of an isomorphism
   family — an [exact], with no proof of its own. 

   --------
   * 捐赠者是同构族前向分支中的特殊情况——一个 [exact]，本身没有证明。
*)
Corollary ord_naturality_from_steps_is_instance {C : Category} {n : nat}
  (F G : Ordinal (S n) ⟶ C) (θ : ∀ x : Ord_obj (S n), F x ≅ G x)
  (Hgen : ∀ k : Ord_obj n,
      to (θ (ord_succ k)) ∘ fmap[F] (ord_step k)
        ≈ fmap[G] (ord_step k) ∘ to (θ (ord_incl k))) :
  ∀ (i j : nat) (f : le_t i j) (Hi : le_t (S i) (S n)) (Hj : le_t (S j) (S n)),
    to (θ (ord_at j Hj)) ∘ @fmap _ _ F (ord_at i Hi) (ord_at j Hj) f
      ≈ @fmap _ _ G (ord_at i Hi) (ord_at j Hj) f ∘ to (θ (ord_at i Hi)).
Proof.
  exact (ord_transform_naturality F G (fun x => to (θ x)) Hgen).
Qed.

(*
   * The object-level form, which is what [Transform] wants.  The passage
   from the index-level statement is [ord_eta]: [ord_at (ord_val x)
   (ord_bound x)] IS [x], by record eta. 

   --------
   * 对象级形式，即 [Transform] 想要的形式。从索引级语句得到的段落是 [ord_eta] : [ord_at (ord_val x) (ord_bound x)] IS [x]，通过记录 eta。
*)
Corollary ord_transform_natural@{o h p co ch cp}
  {C : Category@{co ch cp}} {n : nat}
  (F G : Ordinal@{o h p} (S n) ⟶ C)
  (η : ∀ x : Ord_obj@{o} (S n), F x ~> G x)
  (Hgen : ∀ k : Ord_obj@{o} n,
      η (ord_succ k) ∘ fmap[F] (ord_step k)
        ≈ fmap[G] (ord_step k) ∘ η (ord_incl k)) :
  ∀ (x y : Ord_obj (S n)) (f : x ~{Ordinal (S n)}~> y),
    η y ∘ fmap[F] f ≈ fmap[G] f ∘ η x.
Proof.
  intros x y f.
  exact (ord_transform_naturality F G η Hgen
           (ord_val x) (ord_val y) f (ord_bound x) (ord_bound y)).
Qed.

(*
   * ** Commutative rectangles

   Six objects, seven arrows, and exactly TWO equations. 

   --------
   * ** 交换矩形

   六个对象，七个箭头，正好两个方程。
*)

Record CommutingRectangle (C : Category) : Type := {
  crc_x0 : C;  crc_x1 : C;  crc_x2 : C;
  crc_y0 : C;  crc_y1 : C;  crc_y2 : C;
  crc_u  : crc_x0 ~> crc_x1;
  crc_v  : crc_x1 ~> crc_x2;
  crc_u' : crc_y0 ~> crc_y1;
  crc_v' : crc_y1 ~> crc_y2;
  crc_p  : crc_x0 ~> crc_y0;
  crc_q  : crc_x1 ~> crc_y1;
  crc_r  : crc_x2 ~> crc_y2;
  crc_left  : crc_q ∘ crc_u ≈ crc_u' ∘ crc_p;
  crc_right : crc_r ∘ crc_v ≈ crc_v' ∘ crc_q
}.

Arguments crc_x0 {C} _.  Arguments crc_x1 {C} _.  Arguments crc_x2 {C} _.
Arguments crc_y0 {C} _.  Arguments crc_y1 {C} _.  Arguments crc_y2 {C} _.
Arguments crc_u  {C} _.  Arguments crc_v  {C} _.
Arguments crc_u' {C} _.  Arguments crc_v' {C} _.
Arguments crc_p  {C} _.  Arguments crc_q  {C} _.  Arguments crc_r {C} _.
Arguments crc_left  {C} _.
Arguments crc_right {C} _.

(*
   * The outer rectangle of a commutative rectangle commutes — the
   pasting principle, applied to the record's own two fields. 

   --------
   * 交换矩形的外部矩形是交换的 —— 粘贴原理，应用于记录自身的两个字段。
*)
Theorem crc_outer {C : Category} (R : CommutingRectangle C) :
  crc_r R ∘ (crc_v R ∘ crc_u R) ≈ (crc_v' R ∘ crc_u' R) ∘ crc_p R.
Proof.
  exact (paste_squares _ _ _ _ _ _ _ (crc_left R) (crc_right R)).
Qed.

(*
   * UNIVERSES, measured.  The construction below is pinned at
   [C : Category@{co Set Set}] — the target's hom and proof universes at
   [Set] — and the pin is inherited, not introduced here.
   [Theory/Shapes.v]'s [Functor_of_Pair] produces a functor out of
   [_3@{u Set Set}] (that file's header records the same profile for
   [Instance/Ordinal.v]'s own [Functor_of_Steps] and
   [Functor_of_Triple]), and [Construction/Cylinder.v]'s [Cyl_functor]
   identifies the hom and proof universes of its two categories, so
   [Set] propagates from the row functors to the target.  The FORWARD
   direction — the [Diagram] section above, which is where all the
   commutativity content lives — carries no such pin and is stated for
   an arbitrary [C].  Lifting this one would mean rebuilding the
   cylinder's classifying functor by hand over [_2 ∏ _3]; that is not
   done here, and nothing above depends on it. 

   --------
   * 宇宙，已测量。下面的构造固定在  
   [C : Category@{co Set Set}] — 目标的同构宇宙和证明宇宙在  
   [Set] — 并且该固定是继承而来的，而不是这里引入的。  
   [Theory/Shapes.v] 的 [Functor_of_Pair] 从  
   [_3@{u Set Set}] 产生了一个函子（该文件的头部记录了 [Instance/Ordinal.v] 自身 [Functor_of_Steps] 和  
   [Functor_of_Triple] 的相同配置文件），而 [Construction/Cylinder.v] 的 [Cyl_functor]  
   标识了其两个范畴的同构宇宙和证明宇宙，因此  
   [Set] 从行函子传播到目标。前向方向 — 上面的 [Diagram] 部分，这是所有交换性内容所在 — 不带有这种固定，并且是针对任意 [C] 说明的。提升这个将意味着在 [_2 ∏ _3] 上手动重建圆柱的分类函子；这里没有执行此操作，上述内容也不依赖它。
*)

Section Converse.

Universe co.

Context {C : Category@{co Set Set}}.
Context (R : CommutingRectangle C).

(*
   * The two rows, as functors out of [_3] — [Theory/Shapes.v]'s
   composable-pair construction. 

   --------
   * 这两行，作为从 [_3] 到 [Theory/Shapes.v] 的函子 — 可组合对的构造。
*)
Definition rect_top : _3 ⟶ C := Functor_of_Pair (crc_u R) (crc_v R).
Definition rect_bottom : _3 ⟶ C := Functor_of_Pair (crc_u' R) (crc_v' R).

(*
   * The three vertical arrows, as a family indexed by the objects of
   [_3].  The fourth branch is the out-of-range index, ruled out by the
   bound — the shape [pair_theta] ([Theory/Shapes.v]) uses. 

   --------
   * 三个垂直箭头，作为一个以 [_3] 的对象为索引的族。第四个分支是超出范围的索引，被界限排除了——形状 [pair_theta]（[Theory/Shapes.v]）使用。
*)
Definition rect_eta (w : Ord_obj 3) : rect_top w ~> rect_bottom w.
Proof.
  destruct w as [i H]; destruct i as [| [| [| i]]].
  - exact (crc_p R).
  - exact (crc_q R).
  - exact (crc_r R).
  - destruct (le_t_zero_absurd (le_t_SS_inv (le_t_SS_inv (le_t_SS_inv H)))).
Defined.

(*
   * Naturality on the two generating steps IS the two square
   equations. 

   --------
   * 两个生成步骤上的自然性就是两个平方方程。
*)
Lemma rect_eta_gen (k : Ord_obj 2) :
  rect_eta (ord_succ k) ∘ fmap[rect_top] (ord_step k)
    ≈ fmap[rect_bottom] (ord_step k) ∘ rect_eta (ord_incl k).
Proof.
  unfold rect_top, rect_bottom, Functor_of_Pair.
  destruct k as [i H]; destruct i as [| [| i]].
  - rewrite !Functor_of_Steps_step.
    exact (crc_left R).
  - rewrite !Functor_of_Steps_step.
    exact (crc_right R).
  - destruct (le_t_zero_absurd (le_t_SS_inv (le_t_SS_inv H))).
Qed.

Program Definition rect_transform : rect_top ⟹ rect_bottom := {|
  transform := rect_eta
|}.
Next Obligation.
  symmetry; exact (ord_transform_natural rect_top rect_bottom
                     rect_eta rect_eta_gen x y f).
Qed.
Next Obligation.
  exact (ord_transform_natural rect_top rect_bottom
           rect_eta rect_eta_gen x y f).
Qed.

(*
   * The functor a commutative rectangle names: the classifying functor
   of that transformation on the cylinder [_3 ∏ _2], read on
   [_2 ∏ _3] through [Swap]. 

   --------
   * 一个交换矩形所命名的函子：那个在圆柱体 [_3 ∏ _2] 上的变换的分类函子，通过 [_2 ∏ _3] 到 [Swap] 读取。
*)
Definition RectFunctor : Rect ⟶ C := Cyl_functor rect_transform ◯ Swap.

(** Its six objects, on the nose. / 它的六个物体，正好。 *)
Example RectFunctor_X0 : fobj[RectFunctor] (TwoX, ord3_0) = crc_x0 R := eq_refl.
Example RectFunctor_X1 : fobj[RectFunctor] (TwoX, ord3_1) = crc_x1 R := eq_refl.
Example RectFunctor_X2 : fobj[RectFunctor] (TwoX, ord3_2) = crc_x2 R := eq_refl.
Example RectFunctor_Y0 : fobj[RectFunctor] (TwoY, ord3_0) = crc_y0 R := eq_refl.
Example RectFunctor_Y1 : fobj[RectFunctor] (TwoY, ord3_1) = crc_y1 R := eq_refl.
Example RectFunctor_Y2 : fobj[RectFunctor] (TwoY, ord3_2) = crc_y2 R := eq_refl.

(** ...and all seven generating arrows, up to [≈]. / ...以及所有七个生成箭头，直到 [≈] 。 *)
Theorem RectFunctor_u : rect_u RectFunctor ≈ crc_u R.
Proof. exact (Functor_of_Pair_fst (crc_u R) (crc_v R)). Qed.

Theorem RectFunctor_v : rect_v RectFunctor ≈ crc_v R.
Proof. exact (Functor_of_Pair_snd (crc_u R) (crc_v R)). Qed.

Theorem RectFunctor_u' : rect_u' RectFunctor ≈ crc_u' R.
Proof. exact (Functor_of_Pair_fst (crc_u' R) (crc_v' R)). Qed.

Theorem RectFunctor_v' : rect_v' RectFunctor ≈ crc_v' R.
Proof. exact (Functor_of_Pair_snd (crc_u' R) (crc_v' R)). Qed.

Theorem RectFunctor_p : rect_p RectFunctor ≈ crc_p R.
Proof. exact (Cyl_functor_mu rect_transform ord3_0). Qed.

Theorem RectFunctor_q : rect_q RectFunctor ≈ crc_q R.
Proof. exact (Cyl_functor_mu rect_transform ord3_1). Qed.

Theorem RectFunctor_r : rect_r RectFunctor ≈ crc_r R.
Proof. exact (Cyl_functor_mu rect_transform ord3_2). Qed.

End Converse.

Arguments RectFunctor {C} _.

(*
   * ** The arrow count of the shape

   An arrow of [_2 ∏ _3] is a pair, so the count is 3 × 6.  The [_3]
   factor's own count is [Instance/Ordinal.v]'s, reused: [ord_pairs 3]
   enumerates the ordered pairs of indices carrying an arrow, and its
   length is 6. 

   --------
   * ** 形状的箭头数量

   [_2 ∏ _3] 的一个箭头是成对出现的，所以数量是 3 × 6。[_3] 因子的自身数量是 [Instance/Ordinal.v] 的，重用：[ord_pairs 3] 列举了携带箭头的索引的有序对，其长度为 6。
*)

Definition ord3_objs : list (Ord_obj 3) := ord3_0 :: ord3_1 :: ord3_2 :: nil.

Definition ord3_homcount (x y : Ord_obj 3) : nat :=
  if Nat.leb (ord_val x) (ord_val y) then 1 else 0.

Lemma ord3_hom_inhabited (x y : Ord_obj 3) :
  ord3_homcount x y = 1%nat → x ~{_3}~> y.
Proof.
  unfold ord3_homcount; intro H.
  destruct (Nat.leb (ord_val x) (ord_val y)) eqn:E; [ | discriminate ].
  exact (le_t_of_leb _ _ E).
Qed.

Lemma ord3_hom_empty (x y : Ord_obj 3) :
  ord3_homcount x y = 0%nat → (x ~{_3}~> y) → False.
Proof.
  unfold ord3_homcount; intros H f.
  destruct (Nat.leb (ord_val x) (ord_val y)) eqn:E; [ discriminate | ].
  apply PeanoNat.Nat.leb_nle in E.
  exact (E (le_t_to_le f)).
Qed.

Definition ord3_arrow_total : nat :=
  fold_right (fun q n => ord3_homcount (fst q) (snd q) + n)%nat 0%nat
    (list_prod ord3_objs ord3_objs).

Theorem ord3_arrow_total_6 : ord3_arrow_total = 6%nat.
Proof. reflexivity. Qed.

(*
   * The same 6, read off [Instance/Ordinal.v]'s enumeration, which is
   proved sound, complete and duplicate-free there. 

   --------
   * 相同的 6，从 [Instance/Ordinal.v] 的枚举中读出，该枚举在那里被证明是正确的、完整的且无重复的。
*)
Example ord3_count_agrees : ord3_arrow_total = length (ord_pairs 3).
Proof. reflexivity. Qed.

Definition rect_objs : list (TwoObj * Ord_obj 3) := list_prod two_objs ord3_objs.

Example rect_objs_6 : length rect_objs = 6%nat := eq_refl.

Definition rect_homcount (x y : TwoObj * Ord_obj 3) : nat :=
  (two_homcount (fst x) (fst y) * ord3_homcount (snd x) (snd y))%nat.

Definition rect_arrow_total : nat :=
  fold_right (fun q n => rect_homcount (fst q) (snd q) + n)%nat 0%nat
    (list_prod rect_objs rect_objs).

(** Riehl §1.6 Example 1.6.9: the shape has eighteen arrows. / Riehl §1.6 例 1.6.9：该形状有十八个箭头。 *)
Theorem rect_arrow_total_18 : rect_arrow_total = 18%nat.
Proof. reflexivity. Qed.

Definition rect_identity_total : nat :=
  fold_right (fun x n => rect_homcount x x + n)%nat 0%nat rect_objs.

Theorem rect_identity_total_6 : rect_identity_total = 6%nat.
Proof. reflexivity. Qed.

Definition rect_nonidentity_total : nat :=
  (rect_arrow_total - rect_identity_total)%nat.

Theorem rect_nonidentity_total_12 : rect_nonidentity_total = 12%nat.
Proof. reflexivity. Qed.

(*
   * 18 = 3 × 6: the walking arrow's three arrows against the ordinal 3's
   six. 

   --------
   * 18 = 3 × 6：行走箭头的三个箭头对着序数3的六个。
*)
Example rect_count_is_product :
  rect_arrow_total = (two_arrow_total * ord3_arrow_total)%nat := eq_refl.

(*
   * The counting function is correct: 0 exactly where the hom-set is
   empty, and where it is 1 the hom-set is inhabited.  (Thinness is
   [Rect_Thin] and holds everywhere.) 

   --------
   * 计数函数是正确的：在同态集为空的地方为 0， 在同态集有一个元素的地方为 1。（薄性是 [Rect_Thin] 并且在所有地方都成立。）
*)
Theorem rect_homcount_inhabited (x y : TwoObj * Ord_obj 3) :
  rect_homcount x y = 1%nat → x ~{Rect}~> y.
Proof.
  destruct x as [a i], y as [b j]; unfold rect_homcount; simpl; intro H.
  apply PeanoNat.Nat.eq_mul_1 in H; destruct H as [H1 H2].
  split; [ exact (two_hom_inhabited a b H1) | exact (ord3_hom_inhabited i j H2) ].
Qed.

Theorem rect_homcount_empty (x y : TwoObj * Ord_obj 3) :
  rect_homcount x y = 0%nat → (x ~{Rect}~> y) → False.
Proof.
  destruct x as [a i], y as [b j]; unfold rect_homcount; simpl; intros H [u w].
  apply PeanoNat.Nat.mul_eq_0 in H; destruct H as [H | H].
  - destruct a, b; simpl in H; try discriminate.
    exact (two_hom_empty u).
  - exact (ord3_hom_empty i j H w).
Qed.
