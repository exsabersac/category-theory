Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.
Require Import Coq.Reals.RIneq.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.

Generalizable All Variables.

Open Scope R_scope.

(*
   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Set Default Proof Using "All".

(** * The unit interval as an object of Top *)

(*
   nLab:      https://ncatlab.org/nlab/show/interval+object
   nLab:      https://ncatlab.org/nlab/show/metric+space
   Book:      Riehl, "Category Theory in Context", Epilogue §E.3 ("Freyd's
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,

   本节说明 Interval 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Case-splitting tactics for the real-number side arithmetic *)

(*
   本节说明 Interval 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Ltac Rcases :=
  unfold Rabs, Rmin, Rmax;
  repeat
    match goal with
    | [ |- context[Rcase_abs ?x] ]  => destruct (Rcase_abs x)
    | [ |- context[Rle_dec ?x ?y] ] => destruct (Rle_dec x y)
    end.

Ltac Rlin := Rcases; lra.

(** ** Ball spaces *)

(*
   本节说明 Interval 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record BallSpace@{o} := {
  ball_carrier :> SetoidObject@{o o};

  bdist : ball_carrier → ball_carrier → R;

  bdist_zero : ∀ x y : ball_carrier, x ≈ y → bdist x y = 0;
  bdist_sym : ∀ x y : ball_carrier, bdist x y = bdist y x;
  bdist_tri : ∀ x y z : ball_carrier, bdist x z <= bdist x y + bdist y z
}.

Arguments bdist {_} _ _.

Lemma bdist_nonneg (A : BallSpace) (x y : A) : 0 <= bdist x y.
Proof.
  pose proof (bdist_tri A x y x) as Htri.
  rewrite (bdist_sym A y x) in Htri.
  rewrite (bdist_zero A x x (reflexivity x)) in Htri.
  lra.
Qed.

(*
   本节说明 Interval 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma bdist_respects (A : BallSpace) (x x' y : A) :
  x ≈ x' → bdist x y = bdist x' y.
Proof.
  intro H.
  pose proof (bdist_tri A x x' y) as H1.
  pose proof (bdist_tri A x' x y) as H2.
  rewrite (bdist_zero A x x' H) in H1.
  rewrite (bdist_zero A x' x (symmetry H)) in H2.
  lra.
Qed.

(*
   本节说明 Interval 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma bdist_proper (A : BallSpace) :
  Proper (equiv ==> equiv ==> eq) (@bdist A).
Proof.
  intros x x' Hx y y' Hy.
  rewrite (bdist_respects A x x' y Hx).
  rewrite (bdist_sym A x' y), (bdist_respects A y y' x' Hy).
  exact (bdist_sym A y' x').
Qed.

(*
   本节说明 Interval 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ball_open (A : BallSpace) (U : A → Type) : Type :=
  ∀ x : A, U x → { d : R & ((0 < d) ∧ (∀ y : A, bdist x y < d → U y))%type }.

Lemma ball_respects (A : BallSpace) (U V : A → Type) :
  (∀ x, U x ↔ V x) → ball_open A U → ball_open A V.
Proof.
  intros HUV HU x Vx.
  destruct (HU x (snd (HUV x) Vx)) as [d [Hd Hball]].
  exists d; split.
  - exact Hd.
  - intros y Hy; exact (fst (HUV y) (Hball y Hy)).
Qed.

(* Opens respect the carrier's own equality: `≈`-equal points are at distance
   zero, hence inside every ball around one another. *)
Lemma ball_proper (A : BallSpace) (U : A → Type) :
  ball_open A U → ∀ x y : A, x ≈ y → U x → U y.
Proof.
  intros HU x y Hxy Ux.
  destruct (HU x Ux) as [d [Hd Hball]].
  apply Hball.
  rewrite (bdist_zero A x y Hxy).
  exact Hd.
Qed.

Lemma ball_union (A : BallSpace) (I : Type) (U : I → (A → Type)) :
  (∀ i, ball_open A (U i)) → ball_open A (fun x => { i : I & U i x }).
Proof.
  intros HU x w.
  destruct (HU (projT1 w) x (projT2 w)) as [d [Hd Hball]].
  exists d; split.
  - exact Hd.
  - intros y Hy; exact (projT1 w; Hball y Hy).
Qed.

Lemma ball_whole (A : BallSpace) : ball_open A (fun _ => poly_unit).
Proof.
  intros x _.
  exists 1; split.
  - lra.
  - intros y _; exact ttt.
Qed.

Lemma ball_inter (A : BallSpace) (U V : A → Type) :
  ball_open A U → ball_open A V → ball_open A (fun x => U x ∧ V x).
Proof.
  intros HU HV x w.
  destruct (HU x (fst w)) as [d1 [Hd1 Hb1]].
  destruct (HV x (snd w)) as [d2 [Hd2 Hb2]].
  exists (Rmin d1 d2); split.
  - Rlin.
  - intros y Hy; split.
    + apply Hb1; revert Hy; Rlin.
    + apply Hb2; revert Hy; Rlin.
Qed.

Definition BallTop (A : BallSpace) : TopSpace := {|
  top_carrier   := ball_carrier A;
  IsOpen        := ball_open A;
  open_respects := ball_respects A;
  open_proper   := ball_proper A;
  open_union    := ball_union A;
  open_whole    := ball_whole A;
  open_inter    := ball_inter A
|}.

(*
   本节说明 Interval 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma lipschitz_continuous (A B : BallSpace)
      (f : SetoidMorphism (ball_carrier A) (ball_carrier B)) (L : R) (HL : 0 < L)
      (Hf : ∀ x y : A, bdist (f x) (f y) <= L * bdist x y) :
  Continuous (BallTop A) (BallTop B) f.
Proof.
  intros U HU x Ufx.
  destruct (HU (f x) Ufx) as [d [Hd Hball]].
  assert (HL0 : L <> 0) by lra.
  exists (d / L); split.
  - unfold Rdiv.
    apply Rmult_lt_0_compat; [ exact Hd | now apply Rinv_0_lt_compat ].
  - intros y Hy.
    apply Hball.
    apply Rle_lt_trans with (r2 := L * bdist x y).
    + exact (Hf x y).
    + replace d with (L * (d / L)) by (field; exact HL0).
      now apply Rmult_lt_compat_l.
Qed.

(** ** The interval and the square *)

(*
   本节说明 Interval 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record Ipt := mkI {
  ival :> R;
  ipt_lo : 0 <= ival;
  ipt_hi : ival <= 1
}.

Definition Ipt_equiv (x y : Ipt) : Type := ival x = ival y.

Lemma Ipt_equiv_Equivalence : Equivalence Ipt_equiv.
Proof.
  constructor; unfold Ipt_equiv.
  - intro x; reflexivity.
  - intros x y H; now symmetry.
  - intros x y z H1 H2; now transitivity (ival y).
Qed.

Definition Ipt_Setoid : Setoid Ipt := {|
  equiv        := Ipt_equiv;
  setoid_equiv := Ipt_equiv_Equivalence
|}.

Definition Ipt_Object : SetoidObject := {|
  carrier   := Ipt;
  is_setoid := Ipt_Setoid
|}.

Lemma BS_I_zero (x y : Ipt_Object) : x ≈ y → Rabs (ival x - ival y) = 0.
Proof.
  intro H.
  assert (Heq : ival x = ival y) by exact H.
  Rlin.
Qed.

Lemma BS_I_sym (x y : Ipt_Object) :
  Rabs (ival x - ival y) = Rabs (ival y - ival x).
Proof. Rlin. Qed.

Lemma BS_I_tri (x y z : Ipt_Object) :
  Rabs (ival x - ival z) <= Rabs (ival x - ival y) + Rabs (ival y - ival z).
Proof. Rlin. Qed.

Definition BS_I : BallSpace := {|
  ball_carrier := Ipt_Object;
  bdist        := fun x y => Rabs (ival x - ival y);
  bdist_zero   := BS_I_zero;
  bdist_sym    := BS_I_sym;
  bdist_tri    := BS_I_tri
|}.

Definition I_Top : TopSpace := BallTop BS_I.

(* The two endpoints, as points of the interval. *)
Definition I_zero : Ipt := mkI 0 (Rle_refl 0) Rle_0_1.
Definition I_one : Ipt := mkI 1 Rle_0_1 (Rle_refl 1).

(* The product of two ball spaces, under the sup distance.  Only the square
   [0,1]² is needed downstream, but the construction costs nothing extra in
   general form. *)
Record BSprod_pt (A B : BallSpace) := mkP {
  bs_fst : A;
  bs_snd : B
}.

Arguments mkP {_ _} _ _.
Arguments bs_fst {_ _} _.
Arguments bs_snd {_ _} _.

Definition BSprod_equiv (A B : BallSpace) (x y : BSprod_pt A B) : Type :=
  (bs_fst x ≈ bs_fst y) ∧ (bs_snd x ≈ bs_snd y).

Lemma BSprod_equiv_Equivalence (A B : BallSpace) :
  Equivalence (BSprod_equiv A B).
Proof.
  constructor; unfold BSprod_equiv.
  - intro x; split; reflexivity.
  - intros x y H; split; symmetry; [ exact (fst H) | exact (snd H) ].
  - intros x y z H1 H2; split.
    + transitivity (bs_fst y); [ exact (fst H1) | exact (fst H2) ].
    + transitivity (bs_snd y); [ exact (snd H1) | exact (snd H2) ].
Qed.

Definition BSprod_Setoid (A B : BallSpace) : Setoid (BSprod_pt A B) := {|
  equiv        := BSprod_equiv A B;
  setoid_equiv := BSprod_equiv_Equivalence A B
|}.

Definition BSprod_Object (A B : BallSpace) : SetoidObject := {|
  carrier   := BSprod_pt A B;
  is_setoid := BSprod_Setoid A B
|}.

Definition BSprod_dist (A B : BallSpace) (x y : BSprod_Object A B) : R :=
  Rmax (bdist (bs_fst x) (bs_fst y)) (bdist (bs_snd x) (bs_snd y)).

Lemma BSprod_zero (A B : BallSpace) (x y : BSprod_Object A B) :
  x ≈ y → BSprod_dist A B x y = 0.
Proof.
  intro H.
  unfold BSprod_dist.
  rewrite (bdist_zero A _ _ (fst H)), (bdist_zero B _ _ (snd H)).
  Rlin.
Qed.

Lemma BSprod_sym (A B : BallSpace) (x y : BSprod_Object A B) :
  BSprod_dist A B x y = BSprod_dist A B y x.
Proof.
  unfold BSprod_dist.
  rewrite (bdist_sym A (bs_fst x)), (bdist_sym B (bs_snd x)).
  reflexivity.
Qed.

Lemma BSprod_tri (A B : BallSpace) (x y z : BSprod_Object A B) :
  BSprod_dist A B x z <= BSprod_dist A B x y + BSprod_dist A B y z.
Proof.
  unfold BSprod_dist.
  pose proof (bdist_tri A (bs_fst x) (bs_fst y) (bs_fst z)) as H1.
  pose proof (bdist_tri B (bs_snd x) (bs_snd y) (bs_snd z)) as H2.
  Rlin.
Qed.

Definition BS_prod (A B : BallSpace) : BallSpace := {|
  ball_carrier := BSprod_Object A B;
  bdist        := BSprod_dist A B;
  bdist_zero   := BSprod_zero A B;
  bdist_sym    := BSprod_sym A B;
  bdist_tri    := BSprod_tri A B
|}.

Definition BS_Sq : BallSpace := BS_prod BS_I BS_I.

Definition Sq_Top : TopSpace := BallTop BS_Sq.

(* The two coordinates of a point of the square, as reals. *)
Definition sq_t (z : BS_Sq) : R := ival (bs_fst z).
Definition sq_s (z : BS_Sq) : R := ival (bs_snd z).

(** ** A small Lipschitz calculus *)

(*
   本节说明 Interval 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition RLip (L : R) (k : R → R) : Prop :=
  ∀ a b, Rabs (k a - k b) <= L * Rabs (a - b).

Lemma Rabs_Rmin_le (a b a' b' : R) :
  Rabs (Rmin a b - Rmin a' b') <= Rmax (Rabs (a - a')) (Rabs (b - b')).
Proof. Rlin. Qed.

Lemma Rabs_Rmax_le (a b a' b' : R) :
  Rabs (Rmax a b - Rmax a' b') <= Rmax (Rabs (a - a')) (Rabs (b - b')).
Proof. Rlin. Qed.

Lemma RLip_min (L : R) (f g : R → R) :
  RLip L f → RLip L g → RLip L (fun t => Rmin (f t) (g t)).
Proof.
  intros Hf Hg a b.
  apply Rle_trans with
    (r2 := Rmax (Rabs (f a - f b)) (Rabs (g a - g b))).
  - apply Rabs_Rmin_le.
  - apply Rmax_lub; [ apply Hf | apply Hg ].
Qed.

Lemma RLip_max (L : R) (f g : R → R) :
  RLip L f → RLip L g → RLip L (fun t => Rmax (f t) (g t)).
Proof.
  intros Hf Hg a b.
  apply Rle_trans with
    (r2 := Rmax (Rabs (f a - f b)) (Rabs (g a - g b))).
  - apply Rabs_Rmax_le.
  - apply Rmax_lub; [ apply Hf | apply Hg ].
Qed.

Lemma RLip_ext (L : R) (f g : R → R) : (∀ t, f t = g t) → RLip L f → RLip L g.
Proof.
  intros Hfg Hf a b.
  rewrite <- (Hfg a), <- (Hfg b).
  apply Hf.
Qed.

Lemma RLip_affine (m q L : R) : Rabs m <= L → RLip L (fun t => m * t + q).
Proof.
  intros Hm a b.
  replace (m * a + q - (m * b + q)) with (m * (a - b)) by ring.
  rewrite Rabs_mult.
  apply Rmult_le_compat_r; [ apply Rabs_pos | exact Hm ].
Qed.

(* A convenient packaging of the two-factor product bound, used repeatedly in
   the square estimates below. *)
Lemma Rabs_mult_le (x y a b : R) :
  Rabs x <= a → Rabs y <= b → Rabs (x * y) <= a * b.
Proof.
  intros Hx Hy.
  rewrite Rabs_mult.
  apply Rmult_le_compat; solve [ apply Rabs_pos | assumption ].
Qed.

(** ** Arrows of Top out of the interval and the square *)

Section IArrow.

Context (k : R → R).
Context (L : R).
Context (HL : 0 < L).
Context (Hr0 : ∀ t, 0 <= t → t <= 1 → 0 <= k t).
Context (Hr1 : ∀ t, 0 <= t → t <= 1 → k t <= 1).
Context (Hlip : RLip L k).

Definition I_point (x : Ipt) : Ipt :=
  mkI (k (ival x)) (Hr0 _ (ipt_lo x) (ipt_hi x)) (Hr1 _ (ipt_lo x) (ipt_hi x)).

Definition I_setoid_map : SetoidMorphism Ipt_Object Ipt_Object.
Proof.
  refine {| morphism := I_point |}.
  intros x y Hxy.
  assert (Heq : ival x = ival y) by exact Hxy.
  exact (f_equal k Heq).
Defined.

Definition I_arrow : I_Top ~{Top}~> I_Top :=
  Build_ContinuousMorphism I_Top I_Top I_setoid_map
    (lipschitz_continuous BS_I BS_I I_setoid_map L HL
       (fun x y => Hlip (ival x) (ival y))).

Lemma I_arrow_eval (x : Ipt) : ival (I_arrow x) = k (ival x).
Proof. reflexivity. Qed.

End IArrow.

(* The componentwise map of the square, built from two interval formulas.  All
   five reindexings of a homotopy used downstream have this shape. *)
Section SqSqArrow.

Context (k1 k2 : R → R).
Context (L : R).
Context (HL : 0 < L).
Context (Hr0 : ∀ t, 0 <= t → t <= 1 → 0 <= k1 t).
Context (Hr1 : ∀ t, 0 <= t → t <= 1 → k1 t <= 1).
Context (Hs0 : ∀ t, 0 <= t → t <= 1 → 0 <= k2 t).
Context (Hs1 : ∀ t, 0 <= t → t <= 1 → k2 t <= 1).
Context (Hlip1 : RLip L k1).
Context (Hlip2 : RLip L k2).

Definition SqSq_point (z : BS_Sq) : BS_Sq :=
  @mkP BS_I BS_I (I_point k1 Hr0 Hr1 (bs_fst z)) (I_point k2 Hs0 Hs1 (bs_snd z)).

Definition SqSq_setoid_map :
  SetoidMorphism (ball_carrier BS_Sq) (ball_carrier BS_Sq).
Proof.
  refine {| morphism := SqSq_point |}.
  intros z w Hzw.
  assert (H1 : ival (bs_fst z) = ival (bs_fst w)) by exact (fst Hzw).
  assert (H2 : ival (bs_snd z) = ival (bs_snd w)) by exact (snd Hzw).
  exact (f_equal k1 H1, f_equal k2 H2).
Defined.

Lemma SqSq_lipschitz (z w : BS_Sq) :
  bdist (SqSq_point z) (SqSq_point w) <= L * bdist z w.
Proof.
  simpl; unfold BSprod_dist; simpl.
  apply Rmax_lub.
  - apply Rle_trans with (r2 := L * Rabs (ival (bs_fst z) - ival (bs_fst w))).
    + apply Hlip1.
    + apply Rmult_le_compat_l; [ lra | apply Rmax_l ].
  - apply Rle_trans with (r2 := L * Rabs (ival (bs_snd z) - ival (bs_snd w))).
    + apply Hlip2.
    + apply Rmult_le_compat_l; [ lra | apply Rmax_r ].
Qed.

Definition SqSq_arrow : Sq_Top ~{Top}~> Sq_Top :=
  Build_ContinuousMorphism Sq_Top Sq_Top SqSq_setoid_map
    (lipschitz_continuous BS_Sq BS_Sq SqSq_setoid_map L HL SqSq_lipschitz).

End SqSqArrow.

(*
   本节说明 Interval 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section SqArrow.

Context (k : R → R → R).
Context (L : R).
Context (HL : 0 < L).
Context (Hr0 : ∀ t s, 0 <= t → t <= 1 → 0 <= s → s <= 1 → 0 <= k t s).
Context (Hr1 : ∀ t s, 0 <= t → t <= 1 → 0 <= s → s <= 1 → k t s <= 1).
Context (Hlip : ∀ t s t' s',
            0 <= t → t <= 1 → 0 <= s → s <= 1 →
            0 <= t' → t' <= 1 → 0 <= s' → s' <= 1 →
            Rabs (k t s - k t' s') <= L * Rabs (t - t') + L * Rabs (s - s')).

Definition Sq_point (z : BS_Sq) : Ipt :=
  mkI (k (sq_t z) (sq_s z))
      (Hr0 _ _ (ipt_lo (bs_fst z)) (ipt_hi (bs_fst z))
             (ipt_lo (bs_snd z)) (ipt_hi (bs_snd z)))
      (Hr1 _ _ (ipt_lo (bs_fst z)) (ipt_hi (bs_fst z))
             (ipt_lo (bs_snd z)) (ipt_hi (bs_snd z))).

Definition Sq_setoid_map :
  SetoidMorphism (ball_carrier BS_Sq) (ball_carrier BS_I).
Proof.
  refine {| morphism := Sq_point |}.
  intros z w Hzw.
  assert (H1 : sq_t z = sq_t w) by exact (fst Hzw).
  assert (H2 : sq_s z = sq_s w) by exact (snd Hzw).
  assert (Hgoal : k (sq_t z) (sq_s z) = k (sq_t w) (sq_s w))
    by (rewrite H1, H2; reflexivity).
  exact Hgoal.
Defined.

Lemma Sq_lipschitz (z w : BS_Sq) :
  @bdist BS_I (Sq_point z) (Sq_point w) <= (2 * L) * @bdist BS_Sq z w.
Proof.
  simpl; unfold BSprod_dist; simpl.
  apply Rle_trans with
    (r2 := L * Rabs (sq_t z - sq_t w) + L * Rabs (sq_s z - sq_s w)).
  - apply Hlip;
      solve [ apply ipt_lo | apply ipt_hi ].
  - pose proof (Rmax_l (Rabs (ival (bs_fst z) - ival (bs_fst w)))
                       (Rabs (ival (bs_snd z) - ival (bs_snd w)))) as Hm1.
    pose proof (Rmax_r (Rabs (ival (bs_fst z) - ival (bs_fst w)))
                       (Rabs (ival (bs_snd z) - ival (bs_snd w)))) as Hm2.
    unfold sq_t, sq_s.
    nra.
Qed.

Definition Sq_arrow : Sq_Top ~{Top}~> I_Top :=
  Build_ContinuousMorphism Sq_Top I_Top Sq_setoid_map
    (lipschitz_continuous BS_Sq BS_I Sq_setoid_map (2 * L) ltac:(lra)
       Sq_lipschitz).

Lemma Sq_arrow_eval (z : BS_Sq) : ival (Sq_arrow z) = k (sq_t z) (sq_s z).
Proof. reflexivity. Qed.

End SqArrow.

(** ** Pasting two arrows along a level set of a coordinate *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Paste.

Context {A : BallSpace}.
Context {X : TopSpace}.
Context (u : A → R).
Context (Hu : ∀ x y : A, Rabs (u x - u y) <= bdist x y).
Context (c : R).
Context (f g : BallTop A ~{Top}~> X).
Context (Hfg : ∀ x : A, u x = c → f x ≈ g x).

Definition paste_fun (x : A) : X := if Rle_dec (u x) c then f x else g x.

Lemma paste_coord (x y : A) : x ≈ y → u x = u y.
Proof.
  intro Hxy.
  pose proof (Hu x y) as H.
  rewrite (bdist_zero A x y Hxy) in H.
  revert H; Rlin.
Qed.

Definition paste_setoid_map : SetoidMorphism (ball_carrier A) (top_carrier X).
Proof.
  refine {| morphism := paste_fun |}.
  intros x y Hxy.
  unfold paste_fun.
  rewrite (paste_coord x y Hxy).
  destruct (Rle_dec (u y) c).
  - now apply proper_morphism.
  - now apply proper_morphism.
Defined.

Lemma paste_open (U : X → Type) (HU : IsOpen X U) :
  ball_open A (fun z => U (paste_fun z)).
Proof.
  intros x Ux.
  destruct (total_order_T (u x) c) as [[Hlt | Heq] | Hgt].
  - (* strictly below the level: the paste agrees with f nearby *)
    assert (Hfx : U (f x)).
    { revert Ux; unfold paste_fun; destruct (Rle_dec (u x) c) as [Hle | Hnle].
      - exact (fun w => w).
      - intro w; exfalso; apply Hnle; lra. }
    destruct (continuity f U HU x Hfx) as [d1 [Hd1 Hb1]].
    exists (Rmin d1 (c - u x)); split.
    + Rlin.
    + intros y Hy.
      pose proof (Hu x y) as Habs.
      assert (Huy : u y < c) by (revert Hy Habs; Rlin).
      unfold paste_fun; destruct (Rle_dec (u y) c) as [Hle | Hnle].
      * apply Hb1; revert Hy; Rlin.
      * exfalso; apply Hnle; lra.
  - (* exactly at the level: both halves are available, and they agree *)
    assert (Hfx : U (f x)).
    { revert Ux; unfold paste_fun; destruct (Rle_dec (u x) c) as [Hle | Hnle].
      - exact (fun w => w).
      - intro w; exfalso; apply Hnle; lra. }
    assert (Hgx : U (g x)) by
      exact (open_proper X U HU (f x) (g x) (Hfg x Heq) Hfx).
    destruct (continuity f U HU x Hfx) as [d1 [Hd1 Hb1]].
    destruct (continuity g U HU x Hgx) as [d2 [Hd2 Hb2]].
    exists (Rmin d1 d2); split.
    + Rlin.
    + intros y Hy.
      unfold paste_fun; destruct (Rle_dec (u y) c) as [Hle | Hnle].
      * apply Hb1; revert Hy; Rlin.
      * apply Hb2; revert Hy; Rlin.
  - (* strictly above the level: the paste agrees with g nearby *)
    assert (Hgx : U (g x)).
    { revert Ux; unfold paste_fun; destruct (Rle_dec (u x) c) as [Hle | Hnle].
      - intro w; exfalso; lra.
      - exact (fun w => w). }
    destruct (continuity g U HU x Hgx) as [d2 [Hd2 Hb2]].
    exists (Rmin d2 (u x - c)); split.
    + Rlin.
    + intros y Hy.
      pose proof (Hu x y) as Habs.
      assert (Huy : c < u y) by (revert Hy Habs; Rlin).
      unfold paste_fun; destruct (Rle_dec (u y) c) as [Hle | Hnle].
      * exfalso; lra.
      * apply Hb2; revert Hy; Rlin.
Qed.

Definition paste_arrow : BallTop A ~{Top}~> X :=
  Build_ContinuousMorphism (BallTop A) X paste_setoid_map paste_open.

Lemma paste_left (x : A) : u x <= c → paste_arrow x ≈ f x.
Proof.
  intro H.
  unfold paste_arrow; simpl; unfold paste_fun.
  destruct (Rle_dec (u x) c) as [Hle | Hnle].
  - reflexivity.
  - exfalso; exact (Hnle H).
Qed.

Lemma paste_right (x : A) : c <= u x → paste_arrow x ≈ g x.
Proof.
  intro H.
  unfold paste_arrow; simpl; unfold paste_fun.
  destruct (Rle_dec (u x) c) as [Hle | Hnle].
  - apply Hfg; lra.
  - reflexivity.
Qed.

End Paste.

(** ** The reparametrizations *)

(*
   本节说明 Interval 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition rf_id (t : R) : R := t.
Definition rf_rev (t : R) : R := 1 - t.
Definition rf_dbl (t : R) : R := Rmin (2 * t) 1.
Definition rf_dbl' (t : R) : R := Rmax (2 * t - 1) 0.
Definition rf_assoc (t : R) : R := Rmin (2 * t) (Rmin (t + 1/4) (t / 2 + 1/2)).
Definition rf_tent (t : R) : R := Rmin (2 * t) (2 - 2 * t).
Definition rf_zero (t : R) : R := 0.

Lemma rf_id_lo (t : R) : 0 <= t → t <= 1 → 0 <= rf_id t.
Proof. unfold rf_id; Rlin. Qed.
Lemma rf_id_hi (t : R) : 0 <= t → t <= 1 → rf_id t <= 1.
Proof. unfold rf_id; Rlin. Qed.
Lemma rf_id_lip : RLip 2 rf_id.
Proof. intros a b; unfold rf_id; Rlin. Qed.

Lemma rf_rev_lo (t : R) : 0 <= t → t <= 1 → 0 <= rf_rev t.
Proof. unfold rf_rev; Rlin. Qed.
Lemma rf_rev_hi (t : R) : 0 <= t → t <= 1 → rf_rev t <= 1.
Proof. unfold rf_rev; Rlin. Qed.
Lemma rf_rev_lip : RLip 2 rf_rev.
Proof. intros a b; unfold rf_rev; Rlin. Qed.

Lemma rf_dbl_lo (t : R) : 0 <= t → t <= 1 → 0 <= rf_dbl t.
Proof. unfold rf_dbl; Rlin. Qed.
Lemma rf_dbl_hi (t : R) : 0 <= t → t <= 1 → rf_dbl t <= 1.
Proof. unfold rf_dbl; Rlin. Qed.
Lemma rf_dbl_lip : RLip 2 rf_dbl.
Proof. intros a b; unfold rf_dbl; Rlin. Qed.

Lemma rf_dbl'_lo (t : R) : 0 <= t → t <= 1 → 0 <= rf_dbl' t.
Proof. unfold rf_dbl'; Rlin. Qed.
Lemma rf_dbl'_hi (t : R) : 0 <= t → t <= 1 → rf_dbl' t <= 1.
Proof. unfold rf_dbl'; Rlin. Qed.
Lemma rf_dbl'_lip : RLip 2 rf_dbl'.
Proof. intros a b; unfold rf_dbl'; Rlin. Qed.

(*
   本节说明 Interval 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma rf_assoc_first (t : R) : 0 <= t → t <= 1/4 → rf_assoc t = 2 * t.
Proof.
  intros H1 H2; unfold rf_assoc.
  rewrite (Rmin_left (t + 1/4) (t / 2 + 1/2)) by lra.
  rewrite (Rmin_left (2 * t) (t + 1/4)) by lra.
  reflexivity.
Qed.

Lemma rf_assoc_middle (t : R) : 1/4 <= t → t <= 1/2 → rf_assoc t = t + 1/4.
Proof.
  intros H1 H2; unfold rf_assoc.
  rewrite (Rmin_left (t + 1/4) (t / 2 + 1/2)) by lra.
  rewrite (Rmin_right (2 * t) (t + 1/4)) by lra.
  reflexivity.
Qed.

Lemma rf_assoc_last (t : R) : 1/2 <= t → t <= 1 → rf_assoc t = t / 2 + 1/2.
Proof.
  intros H1 H2; unfold rf_assoc.
  rewrite (Rmin_right (t + 1/4) (t / 2 + 1/2)) by lra.
  rewrite (Rmin_right (2 * t) (t / 2 + 1/2)) by lra.
  reflexivity.
Qed.

Lemma rf_assoc_lo (t : R) : 0 <= t → t <= 1 → 0 <= rf_assoc t.
Proof.
  intros H1 H2; unfold rf_assoc.
  apply Rmin_glb; [ lra | apply Rmin_glb; lra ].
Qed.

Lemma rf_assoc_hi (t : R) : 0 <= t → t <= 1 → rf_assoc t <= 1.
Proof.
  intros H1 H2; unfold rf_assoc.
  apply Rle_trans with (r2 := t / 2 + 1/2); [ | lra ].
  apply Rle_trans with (r2 := Rmin (t + 1/4) (t / 2 + 1/2)).
  - apply Rmin_r.
  - apply Rmin_r.
Qed.

Lemma rf_assoc_lip : RLip 2 rf_assoc.
Proof.
  apply (RLip_ext 2
           (fun t => Rmin (2 * t + 0) (Rmin (1 * t + 1/4) ((1/2) * t + 1/2)))).
  - intro t; unfold rf_assoc.
    replace (2 * t + 0) with (2 * t) by ring.
    replace (1 * t + 1/4) with (t + 1/4) by ring.
    replace ((1/2) * t + 1/2) with (t / 2 + 1/2) by field.
    reflexivity.
  - apply RLip_min.
    + apply RLip_affine; Rlin.
    + apply RLip_min; apply RLip_affine; Rlin.
Qed.

Lemma rf_tent_lo (t : R) : 0 <= t → t <= 1 → 0 <= rf_tent t.
Proof. unfold rf_tent; Rlin. Qed.
Lemma rf_tent_hi (t : R) : 0 <= t → t <= 1 → rf_tent t <= 1.
Proof. unfold rf_tent; Rlin. Qed.
Lemma rf_tent_lip : RLip 2 rf_tent.
Proof. intros a b; unfold rf_tent; Rlin. Qed.

Lemma rf_zero_lo (t : R) : 0 <= t → t <= 1 → 0 <= rf_zero t.
Proof. unfold rf_zero; Rlin. Qed.
Lemma rf_zero_hi (t : R) : 0 <= t → t <= 1 → rf_zero t <= 1.
Proof. unfold rf_zero; Rlin. Qed.
Lemma rf_zero_lip : RLip 2 rf_zero.
Proof. intros a b; unfold rf_zero; Rlin. Qed.

Lemma two_pos : 0 < 2.
Proof. lra. Qed.

(** ** The reparametrization arrows *)

Definition I_rev : I_Top ~{Top}~> I_Top :=
  I_arrow rf_rev 2 two_pos rf_rev_lo rf_rev_hi rf_rev_lip.

Definition I_dbl : I_Top ~{Top}~> I_Top :=
  I_arrow rf_dbl 2 two_pos rf_dbl_lo rf_dbl_hi rf_dbl_lip.

Definition I_dbl' : I_Top ~{Top}~> I_Top :=
  I_arrow rf_dbl' 2 two_pos rf_dbl'_lo rf_dbl'_hi rf_dbl'_lip.

Definition I_assoc : I_Top ~{Top}~> I_Top :=
  I_arrow rf_assoc 2 two_pos rf_assoc_lo rf_assoc_hi rf_assoc_lip.

Definition I_tent : I_Top ~{Top}~> I_Top :=
  I_arrow rf_tent 2 two_pos rf_tent_lo rf_tent_hi rf_tent_lip.

Lemma I_rev_eval (x : Ipt) : ival (I_rev x) = 1 - ival x.
Proof. reflexivity. Qed.
Lemma I_dbl_eval (x : Ipt) : ival (I_dbl x) = Rmin (2 * ival x) 1.
Proof. reflexivity. Qed.
Lemma I_dbl'_eval (x : Ipt) : ival (I_dbl' x) = Rmax (2 * ival x - 1) 0.
Proof. reflexivity. Qed.
Lemma I_assoc_eval (x : Ipt) : ival (I_assoc x) = rf_assoc (ival x).
Proof. reflexivity. Qed.
Lemma I_tent_eval (x : Ipt) : ival (I_tent x) = Rmin (2 * ival x) (2 - 2 * ival x).
Proof. reflexivity. Qed.

(** ** The reindexings of the square *)

Definition Sq_flip : Sq_Top ~{Top}~> Sq_Top :=
  SqSq_arrow rf_id rf_rev 2 two_pos rf_id_lo rf_id_hi rf_rev_lo rf_rev_hi
             rf_id_lip rf_rev_lip.

Definition Sq_lower : Sq_Top ~{Top}~> Sq_Top :=
  SqSq_arrow rf_id rf_dbl 2 two_pos rf_id_lo rf_id_hi rf_dbl_lo rf_dbl_hi
             rf_id_lip rf_dbl_lip.

Definition Sq_upper : Sq_Top ~{Top}~> Sq_Top :=
  SqSq_arrow rf_id rf_dbl' 2 two_pos rf_id_lo rf_id_hi rf_dbl'_lo rf_dbl'_hi
             rf_id_lip rf_dbl'_lip.

Definition Sq_leftside : Sq_Top ~{Top}~> Sq_Top :=
  SqSq_arrow rf_dbl rf_id 2 two_pos rf_dbl_lo rf_dbl_hi rf_id_lo rf_id_hi
             rf_dbl_lip rf_id_lip.

Definition Sq_rightside : Sq_Top ~{Top}~> Sq_Top :=
  SqSq_arrow rf_dbl' rf_id 2 two_pos rf_dbl'_lo rf_dbl'_hi rf_id_lo rf_id_hi
             rf_dbl'_lip rf_id_lip.

(** ** The homotopy parameter maps *)

(*
   本节说明 Interval 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section HomotopyMap.

Context (phi psi : R → R).
Context (L : R).
Context (HL : 0 < L).
Context (Hphi0 : ∀ t, 0 <= t → t <= 1 → 0 <= phi t).
Context (Hphi1 : ∀ t, 0 <= t → t <= 1 → phi t <= 1).
Context (Hpsi0 : ∀ t, 0 <= t → t <= 1 → 0 <= psi t).
Context (Hpsi1 : ∀ t, 0 <= t → t <= 1 → psi t <= 1).
Context (Hphil : RLip L phi).
Context (Hpsil : RLip L psi).

Definition hfun (t s : R) : R := (1 - s) * phi t + s * psi t.

Lemma hfun_lo (t s : R) : 0 <= t → t <= 1 → 0 <= s → s <= 1 → 0 <= hfun t s.
Proof.
  intros Ht0 Ht1 Hs0 Hs1; unfold hfun.
  pose proof (Hphi0 t Ht0 Ht1).
  pose proof (Hpsi0 t Ht0 Ht1).
  nra.
Qed.

Lemma hfun_hi (t s : R) : 0 <= t → t <= 1 → 0 <= s → s <= 1 → hfun t s <= 1.
Proof.
  intros Ht0 Ht1 Hs0 Hs1; unfold hfun.
  pose proof (Hphi1 t Ht0 Ht1).
  pose proof (Hpsi1 t Ht0 Ht1).
  nra.
Qed.

Lemma hfun_lip (t s t' s' : R) :
  0 <= t → t <= 1 → 0 <= s → s <= 1 →
  0 <= t' → t' <= 1 → 0 <= s' → s' <= 1 →
  Rabs (hfun t s - hfun t' s')
    <= (2 * L + 1) * Rabs (t - t') + (2 * L + 1) * Rabs (s - s').
Proof.
  intros Ht0 Ht1 Hs0 Hs1 Ht'0 Ht'1 Hs'0 Hs'1.
  unfold hfun.
  replace ((1 - s) * phi t + s * psi t - ((1 - s') * phi t' + s' * psi t'))
    with ((1 - s) * (phi t - phi t') + s * (psi t - psi t')
            + (s - s') * (psi t' - phi t')) by ring.
  apply Rle_trans with
    (r2 := Rabs ((1 - s) * (phi t - phi t') + s * (psi t - psi t'))
             + Rabs ((s - s') * (psi t' - phi t'))).
  { apply Rabs_triang. }
  assert (H3 : Rabs ((s - s') * (psi t' - phi t')) <= Rabs (s - s') * 1).
  { apply Rabs_mult_le.
    - apply Rle_refl.
    - pose proof (Hphi0 t' Ht'0 Ht'1).
      pose proof (Hphi1 t' Ht'0 Ht'1).
      pose proof (Hpsi0 t' Ht'0 Ht'1).
      pose proof (Hpsi1 t' Ht'0 Ht'1).
      Rlin. }
  assert (H12 : Rabs ((1 - s) * (phi t - phi t') + s * (psi t - psi t'))
                  <= 2 * L * Rabs (t - t')).
  { apply Rle_trans with
      (r2 := Rabs ((1 - s) * (phi t - phi t'))
               + Rabs (s * (psi t - psi t'))).
    { apply Rabs_triang. }
    assert (H1 : Rabs ((1 - s) * (phi t - phi t')) <= 1 * (L * Rabs (t - t'))).
    { apply Rabs_mult_le; [ Rlin | apply Hphil ]. }
    assert (H2 : Rabs (s * (psi t - psi t')) <= 1 * (L * Rabs (t - t'))).
    { apply Rabs_mult_le; [ Rlin | apply Hpsil ]. }
    nra. }
  pose proof (Rabs_pos (t - t')).
  pose proof (Rabs_pos (s - s')).
  nra.
Qed.

Definition Sq_hmap : Sq_Top ~{Top}~> I_Top :=
  Sq_arrow hfun (2 * L + 1) ltac:(lra) hfun_lo hfun_hi hfun_lip.

Lemma Sq_hmap_eval (z : BS_Sq) :
  ival (Sq_hmap z) = (1 - sq_s z) * phi (sq_t z) + sq_s z * psi (sq_t z).
Proof. reflexivity. Qed.

End HomotopyMap.

(** ** Points of the square, and its first projection *)

Definition sq_pt (t s : Ipt) : BS_Sq := @mkP BS_I BS_I t s.

Lemma sq_pt_t (t s : Ipt) : sq_t (sq_pt t s) = ival t.
Proof. reflexivity. Qed.

Lemma sq_pt_s (t s : Ipt) : sq_s (sq_pt t s) = ival s.
Proof. reflexivity. Qed.

Lemma sq_first_lip (t s t' s' : R) :
  0 <= t → t <= 1 → 0 <= s → s <= 1 →
  0 <= t' → t' <= 1 → 0 <= s' → s' <= 1 →
  Rabs (t - t') <= 1 * Rabs (t - t') + 1 * Rabs (s - s').
Proof.
  intros; pose proof (Rabs_pos (s - s')); lra.
Qed.

Definition Sq_first : Sq_Top ~{Top}~> I_Top :=
  Sq_arrow (fun t _ => t) 1 Rlt_0_1
    (fun t s H0 _ _ _ => H0) (fun t s _ H1 _ _ => H1) sq_first_lip.

Lemma Sq_first_eval (z : BS_Sq) : ival (Sq_first z) = sq_t z.
Proof. reflexivity. Qed.

(** ** Applying an arrow to points that agree on coordinates *)

(*
   本节说明 Interval 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Iap {X : TopSpace} (f : I_Top ~{Top}~> X) (x y : Ipt) :
  ival x = ival y → f x ≈ f y.
Proof. intro H; now apply proper_morphism. Qed.

Lemma Sqap {X : TopSpace} (F : Sq_Top ~{Top}~> X) (z w : BS_Sq) :
  sq_t z = sq_t w → sq_s z = sq_s w → F z ≈ F w.
Proof. intros H1 H2; apply proper_morphism; exact (H1, H2). Qed.

(** ** Coordinate computations *)

(* Every reindexing above acts on coordinates by its defining formula, and each
   of these equations holds by conversion.  Downstream proofs rewrite with them
   rather than unfolding the arrow constructors. *)

Lemma ival_I_zero : ival I_zero = 0.
Proof. reflexivity. Qed.

Lemma ival_I_one : ival I_one = 1.
Proof. reflexivity. Qed.

Lemma Sq_flip_t (z : BS_Sq) : sq_t (Sq_flip z) = sq_t z.
Proof. reflexivity. Qed.
Lemma Sq_flip_s (z : BS_Sq) : sq_s (Sq_flip z) = 1 - sq_s z.
Proof. reflexivity. Qed.

Lemma Sq_lower_t (z : BS_Sq) : sq_t (Sq_lower z) = sq_t z.
Proof. reflexivity. Qed.
Lemma Sq_lower_s (z : BS_Sq) : sq_s (Sq_lower z) = Rmin (2 * sq_s z) 1.
Proof. reflexivity. Qed.

Lemma Sq_upper_t (z : BS_Sq) : sq_t (Sq_upper z) = sq_t z.
Proof. reflexivity. Qed.
Lemma Sq_upper_s (z : BS_Sq) : sq_s (Sq_upper z) = Rmax (2 * sq_s z - 1) 0.
Proof. reflexivity. Qed.

Lemma Sq_leftside_t (z : BS_Sq) : sq_t (Sq_leftside z) = Rmin (2 * sq_t z) 1.
Proof. reflexivity. Qed.
Lemma Sq_leftside_s (z : BS_Sq) : sq_s (Sq_leftside z) = sq_s z.
Proof. reflexivity. Qed.

Lemma Sq_rightside_t (z : BS_Sq) : sq_t (Sq_rightside z) = Rmax (2 * sq_t z - 1) 0.
Proof. reflexivity. Qed.
Lemma Sq_rightside_s (z : BS_Sq) : sq_s (Sq_rightside z) = sq_s z.
Proof. reflexivity. Qed.

(* The 1-Lipschitz coordinates that [paste_arrow] is applied along. *)
Lemma I_coord_lip (x y : BS_I) : Rabs (ival x - ival y) <= bdist x y.
Proof. apply Rle_refl. Qed.

Lemma Sq_t_lip (z w : BS_Sq) : Rabs (sq_t z - sq_t w) <= bdist z w.
Proof. apply Rmax_l. Qed.

Lemma Sq_s_lip (z w : BS_Sq) : Rabs (sq_s z - sq_s w) <= bdist z w.
Proof. apply Rmax_r. Qed.

(** ** Endpoint values of the reparametrizations *)

Lemma rf_dbl_zero : rf_dbl 0 = 0.
Proof. unfold rf_dbl; Rlin. Qed.
Lemma rf_dbl_one : rf_dbl 1 = 1.
Proof. unfold rf_dbl; Rlin. Qed.
Lemma rf_dbl'_zero : rf_dbl' 0 = 0.
Proof. unfold rf_dbl'; Rlin. Qed.
Lemma rf_dbl'_one : rf_dbl' 1 = 1.
Proof. unfold rf_dbl'; Rlin. Qed.
Lemma rf_tent_zero : rf_tent 0 = 0.
Proof. unfold rf_tent; Rlin. Qed.
Lemma rf_tent_one : rf_tent 1 = 0.
Proof. unfold rf_tent; Rlin. Qed.
Lemma rf_assoc_zero : rf_assoc 0 = 0.
Proof. rewrite rf_assoc_first; lra. Qed.
Lemma rf_assoc_one : rf_assoc 1 = 1.
Proof. rewrite rf_assoc_last; lra. Qed.
