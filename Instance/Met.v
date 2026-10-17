Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.
Require Import Coq.Reals.RIneq.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.Reals.Rfunctions.
Require Import Coq.Reals.Rseries.
Require Import Coq.Reals.SeqProp.
Require Import Coq.Reals.Rcomplete.
Require Import Coq.micromega.Lra.
Require Import Coq.ZArith.ZArith.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Sets.

Generalizable All Variables.

Open Scope R_scope.

(* 相关说明。 （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/complete+metric+space
 nLab:      https://ncatlab.org/nlab/show/Cauchy+sequence
 Wikipedia: https://en.wikipedia.org/wiki/Metric_space
 Wikipedia: https://en.wikipedia.org/wiki/Complete_metric_space
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 Book:      Fong & Spivak, "Seven Sketches in Compositionality",
 Book:      Bishop, "Foundations of Constructive Analysis", McGraw-Hill
 Paper:     Lawvere, "Metric spaces, generalized logic, and closed

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

(*
   本节说明 Met 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Rabs_zero_inv (r : R) : Rabs r = 0 → r = 0.
Proof.
  intro Hr.
  destruct (Req_dec r 0) as [Hz | Hnz]; [ exact Hz |].
  now apply Rabs_no_R0 in Hnz.
Qed.

(** ** The four axioms *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record MetricSpace@{o} := {
  met_carrier :> SetoidObject@{o o};      (* the setoid of points *)

  dist : met_carrier → met_carrier → R;   (* the distance *)

  (* 相关说明。 （已译） *)
  dist_proper : ∀ x x' y y', x ≈ x' → y ≈ y' → dist x y = dist x' y';

  (* (a) zero self-distance *)
  dist_refl : ∀ x, dist x x = 0;

  (* (b) separation *)
  dist_separates : ∀ x y, dist x y = 0 → x ≈ y;

  (* (c) symmetry *)
  dist_sym : ∀ x y, dist x y = dist y x;

  (* (d) the triangle inequality *)
  dist_triangle : ∀ x y z, dist x z <= dist x y + dist y z
}.

Arguments dist {X} _ _ : rename.
Arguments dist_proper {X} _ _ _ _ _ _ : rename.
Arguments dist_refl {X} _ : rename.
Arguments dist_separates {X} _ _ _ : rename.
Arguments dist_sym {X} _ _ : rename.
Arguments dist_triangle {X} _ _ _ : rename.

(* 相关说明。 （已译） *)

(* Non-negativity, Fong & Spivak build 进入 codomain: run the
 triangle inequality x x through y, then use symmetry the
 vanishing diagonal read 0 ≤ 2 d(x,y). （已译） *)
Lemma dist_nonneg {X : MetricSpace} (x y : X) : 0 <= dist x y.
Proof.
  pose proof (dist_triangle x y x) as H.
  rewrite (dist_refl x), (dist_sym y x) in H.
  lra.
Qed.

(* 相关说明。 （已译） *)
Lemma dist_eq_zero {X : MetricSpace} (x y : X) : x ≈ y → dist x y = 0.
Proof.
  intro Hxy.
  rewrite (dist_proper x x y x (reflexivity x) (symmetry Hxy)).
  apply dist_refl.
Qed.

(* 相关说明。 （已译） *)
Lemma dist_zero_iff {X : MetricSpace} (x y : X) : dist x y = 0 ↔ x ≈ y.
Proof.
  split.
  - apply dist_separates.
  - apply dist_eq_zero.
Qed.

(*
   本节说明 Met 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma dist_quadrilateral {X : MetricSpace} (x x' y y' : X) :
  Rabs (dist x y - dist x' y') <= dist x x' + dist y y'.
Proof.
  apply Rabs_le; split.
  - pose proof (dist_triangle x' x y') as H1.
    pose proof (dist_triangle x y y') as H2.
    rewrite (dist_sym x' x) in H1.
    lra.
  - pose proof (dist_triangle x x' y) as H1.
    pose proof (dist_triangle x' y' y) as H2.
    rewrite (dist_sym y' y) in H2.
    lra.
Qed.

(** ** Isometries *)

(*
   本节说明 Met 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record Isometry (X Y : MetricSpace) := {
  isometry_map :> SetoidMorphism (met_carrier X) (met_carrier Y);
  isometry_dist : ∀ x y : X, dist (isometry_map x) (isometry_map y) = dist x y
}.

Arguments isometry_map {X Y} _.
Arguments isometry_dist {X Y} _ _ _.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma isometry_injective {X Y : MetricSpace} (f : Isometry X Y) (x y : X) :
  isometry_map f x ≈ isometry_map f y → x ≈ y.
Proof.
  intro Hf.
  apply dist_separates.
  rewrite <- (isometry_dist f x y).
  now apply dist_eq_zero.
Qed.

(** ** The category Met *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Isometry_equiv {X Y : MetricSpace} : crelation (Isometry X Y) :=
  fun f g => ∀ x : X, isometry_map f x ≈ isometry_map g x.

Arguments Isometry_equiv {X Y} _ _ /.

#[export]
Program Instance Isometry_Setoid {X Y : MetricSpace} :
  Setoid (Isometry X Y) := {| equiv := Isometry_equiv |}.
Next Obligation.
  constructor.
  - intros f x; reflexivity.
  - intros f g Hfg x; symmetry; exact (Hfg x).
  - intros f g h Hfg Hgh x; transitivity (isometry_map g x).
    + exact (Hfg x).
    + exact (Hgh x).
Qed.

Definition met_id {X : MetricSpace} : Isometry X X := {|
  isometry_map  := setoid_morphism_id;
  isometry_dist := fun x y => eq_refl
|}.

Definition met_compose {X Y Z : MetricSpace}
           (g : Isometry Y Z) (f : Isometry X Y) : Isometry X Z := {|
  isometry_map  := setoid_morphism_compose g f;
  isometry_dist := fun x y =>
    eq_trans (isometry_dist g (f x) (f y)) (isometry_dist f x y)
|}.

Lemma met_compose_respects {X Y Z : MetricSpace} :
  Proper (equiv ==> equiv ==> equiv) (@met_compose X Y Z).
Proof.
  intros g1 g2 Hg f1 f2 Hf x; simpl.
  rewrite (Hg (isometry_map f1 x)).
  apply proper_morphism, Hf.
Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Met : Category := {|
  obj     := MetricSpace;
  hom     := Isometry;
  homset  := @Isometry_Setoid;
  id      := @met_id;
  compose := @met_compose;

  compose_respects := @met_compose_respects
|}.

(*
   本节说明 Met 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Met_all_Monic {X Y : Met} (f : X ~> Y) : Monic f.
Proof.
  constructor; intros z g1 g2 Hg x.
  exact (isometry_injective f (isometry_map g1 x) (isometry_map g2 x) (Hg x)).
Qed.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Met_Forget : Met ⟶ Sets := {|
  fobj := met_carrier;
  fmap := fun _ _ f => isometry_map f
|}.

Lemma Met_Forget_Faithful : Faithful Met_Forget.
Proof. constructor; intros x y f g H; exact H. Qed.

(** ** Building metric spaces *)

(*
   本节说明 Met 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section OfInjection.

(* 相关说明。 （已译） *)
Local Set Default Proof Using "All".

Context (A : SetoidObject).
Context (f : A → R).
Context (f_proper : ∀ x y : A, x ≈ y → f x = f y).
Context (f_injective : ∀ x y : A, f x = f y → x ≈ y).

Let inj_dist (x y : A) : R := Rabs (f x - f y).

Lemma inj_proper : ∀ x x' y y', x ≈ x' → y ≈ y' → inj_dist x y = inj_dist x' y'.
Proof.
  intros a b c d Hab Hcd; unfold inj_dist.
  now rewrite (f_proper _ _ Hab), (f_proper _ _ Hcd).
Qed.

Lemma inj_refl : ∀ x, inj_dist x x = 0.
Proof.
  intro a; unfold inj_dist.
  replace (f a - f a) with 0 by ring.
  exact Rabs_R0.
Qed.

Lemma inj_separates : ∀ x y, inj_dist x y = 0 → x ≈ y.
Proof.
  intros a b Hab; unfold inj_dist in Hab.
  apply f_injective, Rminus_diag_uniq.
  now apply Rabs_zero_inv.
Qed.

Lemma inj_sym : ∀ x y, inj_dist x y = inj_dist y x.
Proof. intros a b; apply Rabs_minus_sym. Qed.

Lemma inj_triangle : ∀ x y z, inj_dist x z <= inj_dist x y + inj_dist y z.
Proof.
  intros a b c; unfold inj_dist.
  replace (f a - f c) with ((f a - f b) + (f b - f c)) by ring.
  apply Rabs_triang.
Qed.

Definition Metric_of_injection : MetricSpace :=
  {| met_carrier    := A;
     dist           := inj_dist;
     dist_proper    := inj_proper;
     dist_refl      := inj_refl;
     dist_separates := inj_separates;
     dist_sym       := inj_sym;
     dist_triangle  := inj_triangle |}.

End OfInjection.

Arguments Metric_of_injection A f f_proper f_injective : clear implicits.

(* The real line.  Its carrier is [R] under Leibniz equality. *)
Definition R_Setoid : SetoidObject :=
  {| carrier := R; is_setoid := {| equiv := @eq R |} |}.

Definition R_Metric : MetricSpace :=
  Metric_of_injection R_Setoid (fun r => r)
    (fun x y H => H) (fun x y H => H).

(* 相关说明。 （已译） *)
Example R_Metric_dist (x y : R_Metric) : dist x y = Rabs (x - y) := eq_refl.

(* 相关说明。 （已译） *)
Definition Point_Metric : MetricSpace :=
  {| met_carrier    := unit_setoid_object;
     dist           := fun _ _ => 0;
     dist_proper    := fun _ _ _ _ _ _ => eq_refl;
     dist_refl      := fun _ => eq_refl;
     dist_separates := fun x y _ =>
       match x, y with ttt, ttt => reflexivity ttt end;
     dist_sym       := fun _ _ => eq_refl;
     dist_triangle  := fun _ _ _ => Rplus_le_le_0_compat 0 0 (Rle_refl 0) (Rle_refl 0) |}.

(** ** A concrete incomplete space *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition harm (n : nat) : R := / (INR n + 1).

Lemma harm_pos (n : nat) : 0 < harm n.
Proof.
  apply Rinv_0_lt_compat.
  pose proof (pos_INR n); lra.
Qed.

Lemma harm_injective (m n : nat) : harm m = harm n → m = n.
Proof.
  unfold harm; intro H.
  pose proof (pos_INR m); pose proof (pos_INR n).
  assert (INR m + 1 = INR n + 1) as H'.
  { rewrite <- (Rinv_inv (INR m + 1)), <- (Rinv_inv (INR n + 1)).
    now rewrite H. }
  apply INR_eq; lra.
Qed.

Definition Nat_Setoid : SetoidObject :=
  {| carrier := nat; is_setoid := {| equiv := @eq nat |} |}.

Definition Harmonic : MetricSpace :=
  Metric_of_injection Nat_Setoid harm
    (fun x y H => f_equal harm H)
    (fun x y H => harm_injective x y H).

(* 相关说明。 （已译） *)

(*
   本节说明 Met 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition MCauchy (X : MetricSpace) (u : nat → X) : Type :=
  ∀ eps : R, 0 < eps →
    ∃ N : nat, ∀ m n : nat, (N <= m)%nat → (N <= n)%nat → dist (u m) (u n) < eps.

Definition MConverges (X : MetricSpace) (u : nat → X) (l : X) : Type :=
  ∀ eps : R, 0 < eps →
    ∃ N : nat, ∀ n : nat, (N <= n)%nat → dist (u n) l < eps.

Definition MComplete (X : MetricSpace) : Type :=
  ∀ u : nat → X, MCauchy X u → ∃ l : X, MConverges X u l.

(* 相关说明。 （已译） *)
Lemma MConverges_unique {X : MetricSpace} (u : nat → X) (l l' : X) :
  MConverges X u l → MConverges X u l' → l ≈ l'.
Proof.
  intros Hl Hl'.
  apply dist_separates.
  (* 相关说明。 （已译） *)
  assert (∀ eps : R, 0 < eps → dist l l' < eps) as Hsmall.
  { intros eps Heps.
    destruct (Hl (eps / 2) ltac:(lra)) as [N1 HN1].
    destruct (Hl' (eps / 2) ltac:(lra)) as [N2 HN2].
    pose (n := Nat.max N1 N2).
    specialize (HN1 n (Nat.le_max_l N1 N2)).
    specialize (HN2 n (Nat.le_max_r N1 N2)).
    pose proof (dist_triangle l (u n) l') as Htri.
    rewrite (dist_sym l (u n)) in Htri.
    lra. }
  pose proof (dist_nonneg l l') as Hpos.
  destruct (Rle_lt_or_eq_dec 0 (dist l l') Hpos) as [Hlt | Heq].
  - exfalso. specialize (Hsmall (dist l l') Hlt). lra.
  - now symmetry.
Qed.

(* 相关说明。 （已译） *)
Lemma MConverges_MCauchy {X : MetricSpace} (u : nat → X) (l : X) :
  MConverges X u l → MCauchy X u.
Proof.
  intros Hl eps Heps.
  destruct (Hl (eps / 2) ltac:(lra)) as [N HN].
  exists N; intros m n Hm Hn.
  pose proof (dist_triangle (u m) l (u n)) as Htri.
  rewrite (dist_sym l (u n)) in Htri.
  pose proof (HN m Hm) as H1.
  pose proof (HN n Hn) as H2.
  lra.
Qed.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma isometry_MCauchy {X Y : MetricSpace} (f : Isometry X Y) (u : nat → X) :
  MCauchy X u → MCauchy Y (fun n => isometry_map f (u n)).
Proof.
  intros Hu eps Heps.
  destruct (Hu eps Heps) as [N HN].
  exists N; intros m n Hm Hn.
  rewrite (isometry_dist f (u m) (u n)).
  now apply HN.
Qed.

Lemma isometry_MConverges {X Y : MetricSpace} (f : Isometry X Y)
      (u : nat → X) (l : X) :
  MConverges X u l → MConverges Y (fun n => isometry_map f (u n)) (isometry_map f l).
Proof.
  intros Hu eps Heps.
  destruct (Hu eps Heps) as [N HN].
  exists N; intros n Hn.
  rewrite (isometry_dist f (u n) l).
  now apply HN.
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition CompleteSpaces : Subcategory Met :=
  @Build_Subcategory Met
    (fun X => MComplete X)              (* the complete spaces *)
    (fun _ _ _ _ _ => True)             (* full: every isometry is kept *)
    (fun _ _ _ _ _ _ _ _ _ _ => I)      (* closed under composition *)
    (fun _ _ => I).                     (* closed under identities *)

Definition CMet : Category := Sub Met CompleteSpaces.

Definition CMet_Incl : CMet ⟶ Met := Incl Met CompleteSpaces.

Definition CMet_Full : Construction.Subcategory.Full Met CompleteSpaces :=
  fun _ _ _ _ _ => I.

Definition CMet_Incl_Faithful : Faithful CMet_Incl :=
  Incl_Faithful Met CompleteSpaces.

Definition CMet_Incl_Full : Functor.Full CMet_Incl :=
  Full_Implies_Full_Functor Met CompleteSpaces CMet_Full.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition Point_Metric_MComplete : MComplete Point_Metric :=
  fun u _ => (ttt; fun eps Heps => (0%nat; fun n _ => Heps)).

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma R_Metric_MComplete : MComplete R_Metric.
Proof.
  intros u Hu.
  (* 相关说明。 （已译） *)
  assert (Cauchy_crit u) as Hcc.
  { intros eps Heps.
    destruct (Hu eps ltac:(lra)) as [N HN].
    exists N; intros n m Hn Hm.
    unfold R_dist.
    exact (HN n m Hn Hm). }
  destruct (R_complete u Hcc) as [l Hl].
  exists l; intros eps Heps.
  destruct (Hu (eps / 2) ltac:(lra)) as [N HN].
  exists N; intros n Hn.
  (* |u n - l| ≤ |u n - u m| + |u m - l| suitable m ≥ N chosen the
 Prop-level convergence; goal Prop, so 这是 legitimate. （已译） *)
  destruct (Hl (eps / 2) ltac:(lra)) as [M HM].
  pose (m := Nat.max N M).
  assert (R_dist (u m) l < eps / 2) as H1 by (apply HM; apply Nat.le_max_r).
  assert (dist (u n) (u m) < eps / 2) as H2
      by (apply HN; [ exact Hn | apply Nat.le_max_l ]).
  pose proof (dist_triangle (X:=R_Metric) (u n) (u m) l) as Htri.
  unfold R_dist in H1.
  change (dist (X:=R_Metric) (u m) l) with (Rabs (u m - l)) in *.
  lra.
Qed.

(* [CMet] is inhabited, twice over. *)
Definition R_CMet : CMet := (R_Metric; R_Metric_MComplete).
Definition Point_CMet : CMet := (Point_Metric; Point_Metric_MComplete).

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition harm_mod (eps : R) : nat := Z.to_nat (up (/ eps)).

Lemma harm_antitone (m n : nat) : (m <= n)%nat → harm n <= harm m.
Proof.
  intro Hmn; unfold harm.
  apply Rinv_le_contravar.
  - pose proof (pos_INR m); lra.
  - apply Rplus_le_compat_r, le_INR, Hmn.
Qed.

Lemma harm_mod_spec (eps : R) : 0 < eps → harm (harm_mod eps) < eps.
Proof.
  intro Heps.
  assert (0 < / eps) as Hinv by (apply Rinv_0_lt_compat, Heps).
  destruct (archimed (/ eps)) as [Hup _].
  assert (0 <= up (/ eps))%Z as Hnn.
  { apply le_IZR; simpl; lra. }
  assert (INR (harm_mod eps) = IZR (up (/ eps))) as Heq.
  { unfold harm_mod. rewrite INR_IZR_INZ, Z2Nat.id by exact Hnn. reflexivity. }
  unfold harm; rewrite Heq.
  (* / eps < IZR (up (/eps)) < IZR (up (/eps)) + 1, so the reciprocal is < eps. *)
  assert (/ eps < IZR (up (/ eps)) + 1) as Hlt by lra.
  apply (Rmult_lt_reg_l (IZR (up (/ eps)) + 1)); [ lra |].
  rewrite Rinv_r by lra.
  apply (Rmult_lt_reg_r (/ eps)); [ exact Hinv |].
  rewrite Rmult_1_l, Rmult_assoc, Rinv_r by lra.
  lra.
Qed.

(*
   本节说明 Met 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma harm_half (l n : nat) : (2 * l + 1 <= n)%nat → harm n <= harm l / 2.
Proof.
  intro Hn.
  transitivity (harm (2 * l + 1)); [ now apply harm_antitone |].
  unfold harm.
  rewrite plus_INR, mult_INR.
  replace (INR 2 * INR l + INR 1 + 1) with (2 * (INR l + 1)) by (simpl; lra).
  rewrite Rinv_mult.
  pose proof (pos_INR l); lra.
Qed.

(* The 恒等 sequence harmonic space Cauchy. （已译） *)
Lemma harm_seq_MCauchy : MCauchy Harmonic (fun n => n).
Proof.
  intros eps Heps.
  exists (harm_mod eps); intros m n Hm Hn.
  pose proof (harm_mod_spec eps Heps) as Hsmall.
  pose proof (harm_antitone _ _ Hm) as Hm'.
  pose proof (harm_antitone _ _ Hn) as Hn'.
  pose proof (harm_pos m); pose proof (harm_pos n).
  change (Rabs (harm m - harm n) < eps).
  apply Rabs_def1; lra.
Qed.

(* 相关说明。 （已译） *)
Lemma harm_seq_no_limit (l : Harmonic) :
  MConverges Harmonic (fun n => n) l → False.
Proof.
  intro Hl.
  pose proof (harm_pos l) as Hlpos.
  destruct (Hl (harm l / 2) ltac:(lra)) as [N HN].
  pose (n := Nat.max N (2 * l + 1)).
  assert (N <= n)%nat as Hn by apply Nat.le_max_l.
  specialize (HN n Hn).
  change (Rabs (harm n - harm l) < harm l / 2) in HN.
  pose proof (harm_half l n (Nat.le_max_r N (2 * l + 1))) as Hsmall.
  pose proof (harm_pos n).
  rewrite Rabs_left1 in HN by lra.
  lra.
Qed.

Lemma Harmonic_not_MComplete : MComplete Harmonic → False.
Proof.
  intro Hc.
  destruct (Hc (fun n => n) harm_seq_MCauchy) as [l Hl].
  exact (harm_seq_no_limit l Hl).
Qed.
