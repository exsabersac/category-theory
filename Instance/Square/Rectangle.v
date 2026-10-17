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
 Book: Riehl, Category Theory in Context, Dover 2016, §1.6,
 Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The shape *)

Definition Rect : Category := _2 ∏ _3.

Lemma Three_Thin : Thin _3.
Proof. intros x y f g; exact (ord_thin f g). Qed.

Lemma Rect_Thin : Thin Rect.
Proof. exact (Thin_Product Two_Thin Three_Thin). Qed.

(** 本节：The generating arrows: horizontal ones live [_3] factor at a
 fixed row, vertical ones [_2] factor at fixed column. （已译） *)
Definition rect_horiz (i : TwoObj) {j j' : Ord_obj 3} (s : j ~{_3}~> j') :
  (i, j) ~{Rect}~> (i, j') := (id, s).

Definition rect_vert (j : Ord_obj 3) : (TwoX, j) ~{Rect}~> (TwoY, j) :=
  (TwoXY, id).

(* * ** Pasting, free-standing principle

 Riehl's "two commuting squares paste one", no shape
 范畴 sight: it three rewrites. （已译） *)
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

(* * ** What diagram shape 2 × 3 is

 Every equation below holds ARBITRARY [F], no 假设:
 shape supplies them. （已译） *)

Section Diagram.

Context {C : Category}.
Context (F : Rect ⟶ C).

(** The six objects. *)
Definition rect_X0 : C := fobj[F] (TwoX, ord3_0).
Definition rect_X1 : C := fobj[F] (TwoX, ord3_1).
Definition rect_X2 : C := fobj[F] (TwoX, ord3_2).
Definition rect_Y0 : C := fobj[F] (TwoY, ord3_0).
Definition rect_Y1 : C := fobj[F] (TwoY, ord3_1).
Definition rect_Y2 : C := fobj[F] (TwoY, ord3_2).

(** 本节：The four horizontal arrows three vertical ones. （已译） *)
Definition rect_u : rect_X0 ~> rect_X1 := fmap[F] (rect_horiz TwoX three_01).
Definition rect_v : rect_X1 ~> rect_X2 := fmap[F] (rect_horiz TwoX three_12).
Definition rect_u' : rect_Y0 ~> rect_Y1 := fmap[F] (rect_horiz TwoY three_01).
Definition rect_v' : rect_Y1 ~> rect_Y2 := fmap[F] (rect_horiz TwoY three_12).
Definition rect_p : rect_X0 ~> rect_Y0 := fmap[F] (rect_vert ord3_0).
Definition rect_q : rect_X1 ~> rect_Y1 := fmap[F] (rect_vert ord3_1).
Definition rect_r : rect_X2 ~> rect_Y2 := fmap[F] (rect_vert ord3_2).

(*
   本节说明 Rectangle 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
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
   本节说明 Rectangle 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Local Ltac rect_shape :=
  unfold rect_long_diagonal, rect_diag_left, rect_diag_right,
         rect_u, rect_v, rect_u', rect_v', rect_p, rect_q, rect_r,
         rect_X0, rect_X1, rect_X2, rect_Y0, rect_Y1, rect_Y2;
  rewrite <- !fmap_comp;
  apply fmap_respects;
  exact (Rect_Thin _ _ _ _).

(** 本节：Each square commutes, because two composites already the
 same arrow shape. （已译） *)
Lemma rect_left_commutes : rect_q ∘ rect_u ≈ rect_u' ∘ rect_p.
Proof. rect_shape. Qed.

Lemma rect_right_commutes : rect_r ∘ rect_v ≈ rect_v' ∘ rect_q.
Proof. rect_shape. Qed.

(** The outer rectangle, likewise. *)
Theorem rect_outer_commutes :
  rect_r ∘ (rect_v ∘ rect_u) ≈ (rect_v' ∘ rect_u') ∘ rect_p.
Proof. rect_shape. Qed.

(** 本节：...and it forced twice over: pasting principle derives the
 same equation two squares alone, no reference the
 shape at all. （已译） *)
Theorem rect_outer_two_ways :
  rect_r ∘ (rect_v ∘ rect_u) ≈ (rect_v' ∘ rect_u') ∘ rect_p.
Proof.
  exact (paste_squares rect_u rect_v rect_u' rect_v' rect_p rect_q rect_r
           rect_left_commutes rect_right_commutes).
Qed.

(** 本节：The long diagonal common value every path X0 to
 Y2. （已译） *)
Theorem rect_long_via_top :
  rect_long_diagonal ≈ rect_r ∘ (rect_v ∘ rect_u).
Proof. rect_shape. Qed.

Theorem rect_long_via_bottom :
  rect_long_diagonal ≈ (rect_v' ∘ rect_u') ∘ rect_p.
Proof. rewrite rect_long_via_top; exact rect_outer_commutes. Qed.

(** The two short diagonals, likewise, one per square. *)
Theorem rect_diag_left_via_top : rect_diag_left ≈ rect_q ∘ rect_u.
Proof. rect_shape. Qed.

Theorem rect_diag_left_via_bottom : rect_diag_left ≈ rect_u' ∘ rect_p.
Proof. rewrite rect_diag_left_via_top; exact rect_left_commutes. Qed.

Theorem rect_diag_right_via_top : rect_diag_right ≈ rect_r ∘ rect_v.
Proof. rect_shape. Qed.

Theorem rect_diag_right_via_bottom : rect_diag_right ≈ rect_v' ∘ rect_q.
Proof. rewrite rect_diag_right_via_top; exact rect_right_commutes. Qed.

(** 本节：The inner parallelogram: long diagonal factors through either
 short one. （已译） *)
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
   本节说明自然变换、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
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

(** The donor special case at forward legs 同构
 family — [exact], no 证明 own. （已译） *)
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

(** The 对象-level form, what [Transform] wants. The passage
 index-level statement [ord_eta]: [ord_at (ord_val x)
 (ord_bound x)] IS [x], record eta. （已译） *)
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

(* * ** Commutative rectangles

 Six 对象, seven arrows, exactly TWO equations. （已译） *)

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

(** 本节：The outer rectangle commutative rectangle commutes — the
 pasting principle, applied record's own two fields. （已译） *)
Theorem crc_outer {C : Category} (R : CommutingRectangle C) :
  crc_r R ∘ (crc_v R ∘ crc_u R) ≈ (crc_v' R ∘ crc_u' R) ∘ crc_p R.
Proof.
  exact (paste_squares _ _ _ _ _ _ _ (crc_left R) (crc_right R)).
Qed.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Converse.

Universe co.

Context {C : Category@{co Set Set}}.
Context (R : CommutingRectangle C).

(** The two rows, as functors out of [_3] — [Theory/Shapes.v]'s
    composable-pair construction. *)
Definition rect_top : _3 ⟶ C := Functor_of_Pair (crc_u R) (crc_v R).
Definition rect_bottom : _3 ⟶ C := Functor_of_Pair (crc_u' R) (crc_v' R).

(*
   本节说明 Rectangle 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition rect_eta (w : Ord_obj 3) : rect_top w ~> rect_bottom w.
Proof.
  destruct w as [i H]; destruct i as [| [| [| i]]].
  - exact (crc_p R).
  - exact (crc_q R).
  - exact (crc_r R).
  - destruct (le_t_zero_absurd (le_t_SS_inv (le_t_SS_inv (le_t_SS_inv H)))).
Defined.

(** 本节：Naturality two generating steps IS two square
 equations. （已译） *)
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

(** The 函子 commutative rectangle names: classifying 函子
 transformation cylinder [_3 ∏ _2], read on
 [_2 ∏ _3] through [Swap]. （已译） *)
Definition RectFunctor : Rect ⟶ C := Cyl_functor rect_transform ◯ Swap.

(** Its six objects, on the nose. *)
Example RectFunctor_X0 : fobj[RectFunctor] (TwoX, ord3_0) = crc_x0 R := eq_refl.
Example RectFunctor_X1 : fobj[RectFunctor] (TwoX, ord3_1) = crc_x1 R := eq_refl.
Example RectFunctor_X2 : fobj[RectFunctor] (TwoX, ord3_2) = crc_x2 R := eq_refl.
Example RectFunctor_Y0 : fobj[RectFunctor] (TwoY, ord3_0) = crc_y0 R := eq_refl.
Example RectFunctor_Y1 : fobj[RectFunctor] (TwoY, ord3_1) = crc_y1 R := eq_refl.
Example RectFunctor_Y2 : fobj[RectFunctor] (TwoY, ord3_2) = crc_y2 R := eq_refl.

(** ...and all seven generating arrows, up to [≈]. *)
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
   本节说明 Rectangle 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
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

(** 本节：The same 6, read off [Instance/Ordinal.v]'s enumeration, is
 proved sound, complete duplicate-free there. （已译） *)
Example ord3_count_agrees : ord3_arrow_total = length (ord_pairs 3).
Proof. reflexivity. Qed.

Definition rect_objs : list (TwoObj * Ord_obj 3) := list_prod two_objs ord3_objs.

Example rect_objs_6 : length rect_objs = 6%nat := eq_refl.

Definition rect_homcount (x y : TwoObj * Ord_obj 3) : nat :=
  (two_homcount (fst x) (fst y) * ord3_homcount (snd x) (snd y))%nat.

Definition rect_arrow_total : nat :=
  fold_right (fun q n => rect_homcount (fst q) (snd q) + n)%nat 0%nat
    (list_prod rect_objs rect_objs).

(** Riehl §1.6 Example 1.6.9: the shape has eighteen arrows. *)
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

(** 本节：18 = 3 × 6: walking arrow's three arrows against ordinal 3's
 six. （已译） *)
Example rect_count_is_product :
  rect_arrow_total = (two_arrow_total * ord3_arrow_total)%nat := eq_refl.

(** 本节：The counting function correct: 0 exactly where hom-set is
 empty, where it 1 hom-set inhabited. (Thinness is
 [Rect_Thin] holds everywhere.) （已译） *)
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
