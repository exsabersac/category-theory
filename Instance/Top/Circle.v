Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lqa.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyReals.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyRealsMult.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyAbs.

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Subspace.
Require Import Category.Instance.Top.Subspace.TypeValued.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/solenoid
 nLab: https://ncatlab.org/nlab/show/Cauchy+real+number
 Wikipedia: https://en.wikipedia.org/wiki/Solenoid_(mathematics)

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

(* 相关说明。 （已译） *)

(* [inject_Q] reflects the order, so it is injective up to [Qeq]. *)
Lemma creal_inject_Q_injective@{} (q r : Q) :
  CRealEq (inject_Q q) (inject_Q r) → Qeq q r.
Proof.
  intros [H1 H2]. apply Qle_antisym; apply le_inject_Q; assumption.
Qed.

Lemma inject_Q_pos_le@{} (e : Q) :
  Qlt 0 e → CRealLe (inject_Q 0) (inject_Q e).
Proof. intro H; apply inject_Q_le; apply Qlt_le_weak; exact H. Qed.

Lemma creal_inject_Z_mult@{} (a b : Z) :
  CRealEq (inject_Z (a * b)) (CReal_mult (inject_Z a) (inject_Z b)).
Proof. unfold inject_Z. rewrite <- inject_Q_mult. reflexivity. Qed.

(* A positive integer as a real, and its nonnegativity. *)
Definition posR@{} (p : positive) : CReal := inject_Z (Zpos p).

Lemma posR_nonneg@{} (p : positive) : CRealLe (inject_Q 0) (posR p).
Proof. unfold posR, inject_Z. apply inject_Q_le. unfold Qle; simpl; lia. Qed.

(* 相关说明。 （已译） *)
Lemma creal_minus_self@{} (x y : CReal) :
  CRealEq x y → CRealEq (CReal_minus x y) (inject_Z 0).
Proof.
  intro H. rewrite H. unfold inject_Z, CReal_minus. apply CReal_plus_opp_r.
Qed.

(* A difference of rationals is an integer [k] as reals exactly when it is
   one as rationals. *)
Lemma inject_Q_minus@{} (a b : Q) :
  CRealEq (CReal_minus (inject_Q a) (inject_Q b)) (inject_Q (a - b)).
Proof.
  unfold CReal_minus, Qminus. rewrite inject_Q_plus, opp_inject_Q.
  reflexivity.
Qed.

Lemma inject_Q_minus_int@{} (a b : Q) (k : Z) :
  Qeq (a - b) (k # 1) →
  CRealEq (CReal_minus (inject_Q a) (inject_Q b)) (inject_Z k).
Proof.
  intro H. rewrite inject_Q_minus. unfold inject_Z.
  apply inject_Q_morph_T. exact H.
Qed.

Lemma inject_Q_minus_int_inv@{} (a b : Q) (k : Z) :
  CRealEq (CReal_minus (inject_Q a) (inject_Q b)) (inject_Z k) →
  Qeq (a - b) (k # 1).
Proof.
  intro H. rewrite inject_Q_minus in H. unfold inject_Z in H.
  exact (creal_inject_Q_injective _ _ H).
Qed.

Lemma creal_inject_Z_injective@{} (a b : Z) :
  CRealEq (inject_Z a) (inject_Z b) → a = b.
Proof.
  intro H. apply creal_inject_Q_injective in H. unfold Qeq in H; simpl in H.
  lia.
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明 Circle 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition cround@{} (d : CReal) : Z := Qfloor (seq d (-4) + (1 # 2)).

Lemma cround_between@{} (d : CReal) (k : Z) :
  CRealLe (inject_Q ((k # 1) - (1 # 4))) d →
  CRealLe d (inject_Q ((k # 1) + (1 # 4))) →
  cround d = k.
Proof.
  intros Hlo Hhi.
  pose proof (proj2 (CRealLe_not_lt _ _) Hlo (-4)%Z) as Lo.
  pose proof (proj2 (CRealLe_not_lt _ _) Hhi (-4)%Z) as Hi.
  clear Hlo Hhi.
  cbn [seq inject_Q] in Lo, Hi.
  assert (E : (2 * 2 ^ (-4) == 1 # 8)%Q) by reflexivity.
  rewrite E in Lo, Hi.
  unfold cround.
  set (q := (seq d (-4) + (1 # 2))%Q).
  pose proof (Qfloor_le q) as F1. pose proof (Qlt_floor q) as F2.
  rewrite QArith_base.inject_Z_plus in F2.
  change (QArith_base.inject_Z 1) with 1%Q in F2.
  change (k # 1) with (QArith_base.inject_Z k) in Lo, Hi.
  assert (Hq : (q == seq d (-4) + (1 # 2))%Q) by reflexivity.
  clearbody q.
  set (K := QArith_base.inject_Z k) in *.
  set (Fl := QArith_base.inject_Z (Qfloor q)) in *.
  set (S := seq d (-4)) in *.
  assert (A1 : (Fl < K + 1)%Q) by lra.
  assert (A2 : (K < Fl + 1)%Q) by lra.
  change 1%Q with (QArith_base.inject_Z 1) in A1, A2.
  unfold K, Fl in A1, A2.
  rewrite <- QArith_base.inject_Z_plus, <- Zlt_Qlt in A1, A2. lia.
Qed.

Lemma cround_spec@{} (d : CReal) (k : Z) :
  CRealEq d (inject_Z k) → cround d = k.
Proof.
  intros [H1 H2]. apply cround_between.
  - apply (CRealLe_proper_r _ _ _ (CRealEq_sym _ _ (conj H1 H2))).
    apply inject_Q_le. unfold Qle; simpl. lia.
  - apply (CRealLe_proper_l _ _ _ (CRealEq_sym _ _ (conj H1 H2))).
    apply inject_Q_le. unfold Qle; simpl. lia.
Qed.

Lemma cround_ball@{} (d : CReal) (j : Z) :
  CRealLe (CReal_abs (CReal_minus d (inject_Z j))) (inject_Q (1 # 4)) →
  cround d = j.
Proof.
  intro H. apply CReal_abs_def2 in H. destruct H as [H1 H2].
  assert (E : CRealEq d
                (CReal_plus (inject_Z j) (CReal_minus d (inject_Z j))))
    by (unfold CReal_minus; ring).
  apply cround_between.
  - unfold Qminus. rewrite inject_Q_plus, opp_inject_Q.
    change (inject_Q (j # 1)) with (inject_Z j).
    rewrite E. apply CReal_plus_le_compat_l. exact H2.
  - rewrite inject_Q_plus. change (inject_Q (j # 1)) with (inject_Z j).
    rewrite E at 1. apply CReal_plus_le_compat_l. exact H1.
Qed.

(* 相关说明。 （已译） *)

Program Definition creal_setoid@{o} : Setoid@{o o} CReal :=
  {| equiv := CRealEq |}.
Next Obligation.
  constructor.
  - intro x; exact (CRealEq_refl x).
  - intros x y H; exact (CRealEq_sym x y H).
  - intros x y z H1 H2; exact (CRealEq_trans x y z H1 H2).
Qed.

Definition RLine_setoid@{o} : SetoidObject@{o o} :=
  {| carrier := CReal; is_setoid := creal_setoid@{o} |}.

(* The closed ball of rational radius [e] about [x]: |y - x| <= e. *)
Definition rball@{} (x y : CReal) (e : Q) : Prop :=
  CRealLe (CReal_abs (CReal_minus y x)) (inject_Q e).

Lemma rball_center@{} (x y : CReal) (e : Q) :
  Qlt 0 e → CRealEq x y → rball x y e.
Proof.
  intros He Hxy. unfold rball.
  assert (H0 : CRealEq (CReal_minus y x) (inject_Q 0)).
  { rewrite Hxy. unfold CReal_minus. apply CReal_plus_opp_r. }
  rewrite H0, (CReal_abs_right (inject_Q 0) (CRealLe_refl _)).
  exact (inject_Q_pos_le e He).
Qed.

Lemma rball_mono@{} (x y : CReal) (e e' : Q) :
  Qle e e' → rball x y e → rball x y e'.
Proof.
  intros H b. unfold rball in *. apply (CReal_le_trans _ (inject_Q e)).
  - exact b.
  - apply inject_Q_le; exact H.
Qed.

(* Multiplication by [p] carries a ball of radius [e/p] into one of
   radius [e]. *)
Lemma rball_mul@{} (p : positive) (x y : CReal) (e : Q) :
  rball x y (e * (1 # p)) →
  rball (CReal_mult (posR p) x) (CReal_mult (posR p) y) e.
Proof.
  unfold rball; intro b.
  assert (E : CRealEq
    (CReal_minus (CReal_mult (posR p) y) (CReal_mult (posR p) x))
    (CReal_mult (posR p) (CReal_minus y x))).
  { unfold CReal_minus. ring. }
  rewrite E, CReal_abs_mult, (CReal_abs_right (posR p) (posR_nonneg p)).
  apply (CReal_le_trans _ (CReal_mult (posR p) (inject_Q (e * (1 # p))))).
  - apply CReal_mult_le_compat_l; [exact (posR_nonneg p)|exact b].
  - unfold posR, inject_Z. rewrite <- inject_Q_mult. apply inject_Q_le.
    destruct e as [n d]; cbv [Qle Qmult Qnum Qden].
    rewrite !Pos2Z.inj_mul; nia.
Qed.

Lemma q_half_pos@{} (d : Q) : Qlt 0 d → Qlt 0 (d * (1 # 2)).
Proof. intro H. apply Qmult_lt_0_compat; [exact H|reflexivity]. Qed.

Lemma q_half_half@{} (d : Q) : Qle (d * (1 # 2) + d * (1 # 2)) d.
Proof.
  destruct d as [n m]; cbv [Qle Qplus Qmult Qnum Qden].
  rewrite !Pos2Z.inj_mul; nia.
Qed.

Lemma q_scale_pos@{} (p : positive) (e : Q) : Qlt 0 e → Qlt 0 (e * (1 # p)).
Proof. intro H. apply Qmult_lt_0_compat; [exact H|reflexivity]. Qed.

(* 相关说明。 （已译） *)
Definition ropen@{o} (U : RLine_setoid@{o} → Type@{o}) : Type@{o} :=
  ∀ x, U x → { e : Q & (Qlt 0 e * ∀ y, rball x y e → U y)%type }.

Lemma ropen_respects@{o} (U V : RLine_setoid@{o} → Type@{o}) :
  (∀ x, U x ↔ V x) → ropen@{o} U → ropen@{o} V.
Proof.
  intros H HU x v. destruct (HU x (snd (H x) v)) as [e [He Hb]].
  exists e; split; [exact He|]. intros y b; exact (fst (H y) (Hb y b)).
Qed.

Lemma ropen_proper@{o} (U : RLine_setoid@{o} → Type@{o}) :
  ropen@{o} U → ∀ x y : RLine_setoid@{o}, x ≈ y → U x → U y.
Proof.
  intros HU x y Hxy u. destruct (HU x u) as [e [He Hb]].
  apply Hb, rball_center; [exact He|exact Hxy].
Qed.

Lemma ropen_union@{o} (I : Type@{o}) (U : I → (RLine_setoid@{o} → Type@{o})) :
  (∀ i, ropen@{o} (U i)) → ropen@{o} (fun x => { i : I & U i x }).
Proof.
  intros HU x [i u]. destruct (HU i x u) as [e [He Hb]].
  exists e; split; [exact He|]. intros y b. exact (i; Hb y b).
Qed.

Lemma ropen_whole@{o} : ropen@{o} (fun _ => poly_unit@{o}).
Proof. intros x _. exists 1%Q. split; [reflexivity|intros; exact ttt]. Qed.

Lemma ropen_inter@{o} (U V : RLine_setoid@{o} → Type@{o}) :
  ropen@{o} U → ropen@{o} V → ropen@{o} (fun x => U x ∧ V x).
Proof.
  intros HU HV x [u v].
  destruct (HU x u) as [e1 [He1 Hb1]], (HV x v) as [e2 [He2 Hb2]].
  destruct (Qlt_le_dec e1 e2) as [Hlt|Hle].
  - exists e1; split; [exact He1|]. intros y b; split.
    + exact (Hb1 y b).
    + apply Hb2, (rball_mono _ _ e1); [apply Qlt_le_weak; exact Hlt|exact b].
  - exists e2; split; [exact He2|]. intros y b; split.
    + apply Hb1, (rball_mono _ _ e2); [exact Hle|exact b].
    + exact (Hb2 y b).
Qed.

Definition RLine@{o} : TopSpace@{o} := {|
  top_carrier   := RLine_setoid@{o};
  IsOpen        := ropen@{o};
  open_respects := ropen_respects@{o};
  open_proper   := ropen_proper@{o};
  open_union    := ropen_union@{o};
  open_whole    := ropen_whole@{o};
  open_inter    := ropen_inter@{o}
|}.

(* 相关说明。 （已译） *)
Definition propen@{o} (U : RLine_setoid@{o} → Prop) : Prop :=
  ∀ x, U x → ex (fun e : Q => Qlt 0 e /\ ∀ y, rball x y e → U y).

Lemma propen_respects@{o} (U V : RLine_setoid@{o} → Prop) :
  (∀ x, U x <-> V x) → propen@{o} U → propen@{o} V.
Proof.
  intros H HU x v. destruct (HU x (proj2 (H x) v)) as [e [He Hb]].
  exists e; split; [exact He|]. intros y b; exact (proj1 (H y) (Hb y b)).
Qed.

Lemma propen_proper@{o} (U : RLine_setoid@{o} → Prop) :
  propen@{o} U → ∀ x y : RLine_setoid@{o}, x ≈ y → U x → U y.
Proof.
  intros HU x y Hxy u. destruct (HU x u) as [e [He Hb]].
  apply Hb, rball_center; [exact He|exact Hxy].
Qed.

Lemma propen_union@{o} (F : (RLine_setoid@{o} → Prop) → Prop) :
  (∀ U, F U → propen@{o} U) →
  propen@{o} (fun x => ex (fun U => F U /\ U x)).
Proof.
  intros HF x [U [FU u]]. destruct (HF U FU x u) as [e [He Hb]].
  exists e; split; [exact He|]. intros y b.
  exists U; split; [exact FU|exact (Hb y b)].
Qed.

Lemma propen_whole@{o} : propen@{o} (fun _ => True).
Proof. intros x _. exists 1%Q. split; [reflexivity|intros; exact I]. Qed.

Lemma propen_inter@{o} (U V : RLine_setoid@{o} → Prop) :
  propen@{o} U → propen@{o} V → propen@{o} (fun x => U x /\ V x).
Proof.
  intros HU HV x [u v].
  destruct (HU x u) as [e1 [He1 Hb1]], (HV x v) as [e2 [He2 Hb2]].
  destruct (Qlt_le_dec e1 e2) as [Hlt|Hle].
  - exists e1; split; [exact He1|]. intros y b; split.
    + exact (Hb1 y b).
    + apply Hb2, (rball_mono _ _ e1); [apply Qlt_le_weak; exact Hlt|exact b].
  - exists e2; split; [exact He2|]. intros y b; split.
    + apply Hb1, (rball_mono _ _ e2); [exact Hle|exact b].
    + exact (Hb2 y b).
Qed.

Definition PRLine@{o} : PTop@{o} := {|
  pt_carrier     := RLine_setoid@{o};
  POpen          := propen@{o};
  popen_respects := propen_respects@{o};
  popen_proper   := propen_proper@{o};
  popen_union    := propen_union@{o};
  popen_whole    := propen_whole@{o};
  popen_inter    := propen_inter@{o}
|}.

(* 相关说明。 （已译） *)

Program Definition line_mul@{o} (p : positive) :
  SetoidMorphism@{o o o} RLine_setoid@{o} RLine_setoid@{o} := {|
  morphism := fun x => CReal_mult (posR p) x
|}.
Next Obligation. intros p x y H; simpl in *. rewrite H. reflexivity. Qed.

Lemma line_mul_cont@{h o | o < h +} (p : positive) :
  Continuous@{h o} RLine@{o} RLine@{o} (line_mul@{o} p).
Proof.
  intros U HU x u. destruct (HU _ u) as [e [He Hb]].
  exists (e * (1 # p))%Q. split; [exact (q_scale_pos p e He)|].
  intros y b. apply Hb. exact (rball_mul p x y e b).
Qed.

Definition rline_mul@{h o | o < h +} (p : positive) :
  RLine@{o} ~{Top@{h o}}~> RLine@{o} :=
  @Build_ContinuousMorphism RLine RLine (line_mul p) (line_mul_cont p).

Lemma pline_mul_cont@{o} (p : positive) :
  @PCont PRLine@{o} PRLine@{o} (line_mul@{o} p).
Proof.
  intros U HU x u. destruct (HU _ u) as [e [He Hb]].
  exists (e * (1 # p))%Q. split; [exact (q_scale_pos p e He)|].
  intros y b. apply Hb. exact (rball_mul p x y e b).
Qed.

Definition prline_mul@{o} (p : positive) : PMor@{o} PRLine@{o} PRLine@{o} :=
  @Build_PMor PRLine PRLine (line_mul p) (pline_mul_cont p).

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition circ_eq@{u} (x y : CReal) : Type@{u} :=
  { k : Z & CRealEq (CReal_minus x y) (inject_Z k) }.

Lemma circ_eq_refl@{u} (x : CReal) : circ_eq@{u} x x.
Proof.
  exists 0%Z. apply creal_minus_self. apply CRealEq_refl.
Qed.

Lemma circ_eq_sym@{u} (x y : CReal) : circ_eq@{u} x y → circ_eq@{u} y x.
Proof.
  intros [k Hk]. exists (- k)%Z. rewrite opp_inject_Z, <- Hk.
  unfold CReal_minus. ring.
Qed.

Lemma circ_eq_trans@{u} (x y z : CReal) :
  circ_eq@{u} x y → circ_eq@{u} y z → circ_eq@{u} x z.
Proof.
  intros [k1 H1] [k2 H2]. exists (k1 + k2)%Z.
  rewrite inject_Z_plus, <- H1, <- H2. unfold CReal_minus. ring.
Qed.

Lemma circ_eq_of_creal@{u} (x y : CReal) : CRealEq x y → circ_eq@{u} x y.
Proof. intro H. exists 0%Z. exact (creal_minus_self x y H). Qed.

Program Definition circ_setoid@{o} : Setoid@{o o} CReal :=
  {| equiv := circ_eq@{o} |}.
Next Obligation.
  constructor.
  - exact circ_eq_refl.
  - exact circ_eq_sym.
  - exact circ_eq_trans.
Qed.

Definition Circle_setoid@{o} : SetoidObject@{o o} :=
  {| carrier := CReal; is_setoid := circ_setoid@{o} |}.

(* The quotient map: 恒等 representatives. （已译） *)
Program Definition circ_q@{o} :
  SetoidMorphism@{o o o} RLine_setoid@{o} Circle_setoid@{o} := {|
  morphism := fun x => x
|}.
Next Obligation. intros x y H. exact (circ_eq_of_creal x y H). Qed.

(* The p-fold map on points, shared by both circles below. *)
Program Definition circ_mul@{o} (p : positive) :
  SetoidMorphism@{o o o} Circle_setoid@{o} Circle_setoid@{o} := {|
  morphism := fun x => CReal_mult (posR p) x
|}.
Next Obligation.
  intros p x y [k Hk]. exists (Zpos p * k)%Z.
  rewrite creal_inject_Z_mult, <- Hk. unfold posR, CReal_minus. ring.
Qed.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Lemma circ_eq_witness_unique@{u} (x y : CReal) (a b : circ_eq@{u} x y) :
  projT1 a = projT1 b.
Proof.
  destruct a as [k Hk], b as [l Hl]. cbn [projT1].
  apply creal_inject_Z_injective. rewrite <- Hk, <- Hl. reflexivity.
Qed.

Definition circ_peq@{} (x y : CReal) : Prop :=
  ex (fun k : Z => CRealEq (CReal_minus x y) (inject_Z k)).

(* 相关说明。 （已译） *)
Lemma circ_eq_of_peq@{u} (x y : CReal) : circ_peq x y → circ_eq@{u} x y.
Proof.
  intro H. exists (cround (CReal_minus x y)).
  destruct H as [k Hk]. rewrite (cround_spec _ _ Hk). exact Hk.
Qed.

Lemma circ_peq_of_eq@{u} (x y : CReal) : circ_eq@{u} x y → circ_peq x y.
Proof. intros [k Hk]. exact (ex_intro _ k Hk). Qed.

Definition circ_PropEquiv@{o} :
  PropEquiv@{o o} (is_setoid Circle_setoid@{o}) :=
  @PropEquiv_of_relation _ (is_setoid Circle_setoid@{o}) circ_peq
    circ_eq_of_peq@{o} circ_peq_of_eq@{o}.

(* 相关说明。 （已译） *)
Definition cball@{u} (x y : CReal) (e : Q) : Type@{u} :=
  { k : Z & CRealLe
      (CReal_abs (CReal_plus (CReal_minus y x) (inject_Z k))) (inject_Q e) }.

Lemma cball_of_rball@{u} (x y : CReal) (e : Q) :
  rball x y e → cball@{u} x y e.
Proof.
  intro b. exists 0%Z. unfold rball in b.
  assert (E : CRealEq (CReal_plus (CReal_minus y x) (inject_Z 0))
                      (CReal_minus y x)).
  { unfold inject_Z. ring. }
  rewrite E. exact b.
Qed.

(* 相关说明。 （已译） *)
Lemma rball_of_cball@{} (x y : CReal) (e : Q) (k : Z) :
  CRealLe (CReal_abs (CReal_plus (CReal_minus y x) (inject_Z k)))
          (inject_Q e) →
  rball x (CReal_plus y (inject_Z k)) e.
Proof.
  intro b. unfold rball.
  assert (E : CRealEq (CReal_minus (CReal_plus y (inject_Z k)) x)
                      (CReal_plus (CReal_minus y x) (inject_Z k))).
  { unfold CReal_minus. ring. }
  rewrite E. exact b.
Qed.

Lemma circ_eq_translate@{u} (y : CReal) (k : Z) :
  circ_eq@{u} (CReal_plus y (inject_Z k)) y.
Proof.
  exists k. unfold CReal_minus. ring.
Qed.

Lemma cball_of_eq@{u} (x y : CReal) (e : Q) :
  Qlt 0 e → circ_eq@{u} x y → cball@{u} x y e.
Proof.
  intros He [k Hk]. exists k.
  assert (E : CRealEq (CReal_plus (CReal_minus y x) (inject_Z k))
                      (inject_Q 0)).
  { rewrite <- Hk. unfold CReal_minus. ring. }
  rewrite E, (CReal_abs_right (inject_Q 0) (CRealLe_refl _)).
  exact (inject_Q_pos_le e He).
Qed.

Lemma cball_mono@{u} (x y : CReal) (e e' : Q) :
  Qle e e' → cball@{u} x y e → cball@{u} x y e'.
Proof.
  intros H [k b]. exists k. apply (CReal_le_trans _ (inject_Q e)).
  - exact b.
  - apply inject_Q_le; exact H.
Qed.

Lemma cball_triang@{u} (x y z : CReal) (a b : Q) :
  cball@{u} x y a → cball@{u} y z b → cball@{u} x z (a + b).
Proof.
  intros [k1 H1] [k2 H2]. exists (k1 + k2)%Z.
  assert (E : CRealEq (CReal_plus (CReal_minus z x) (inject_Z (k1 + k2)))
    (CReal_plus (CReal_plus (CReal_minus y x) (inject_Z k1))
                (CReal_plus (CReal_minus z y) (inject_Z k2)))).
  { rewrite inject_Z_plus. unfold CReal_minus. ring. }
  rewrite E, inject_Q_plus.
  apply (CReal_le_trans _ _ _ (CReal_abs_triang _ _)).
  apply CReal_plus_le_compat; [exact H1|exact H2].
Qed.

Lemma cball_mul@{u} (p : positive) (x y : CReal) (e : Q) :
  cball@{u} x y (e * (1 # p)) →
  cball@{u} (CReal_mult (posR p) x) (CReal_mult (posR p) y) e.
Proof.
  intros [k b]. exists (Zpos p * k)%Z.
  assert (E : CRealEq
    (CReal_plus (CReal_minus (CReal_mult (posR p) y) (CReal_mult (posR p) x))
                (inject_Z (Zpos p * k)))
    (CReal_mult (posR p) (CReal_plus (CReal_minus y x) (inject_Z k)))).
  { rewrite creal_inject_Z_mult. unfold posR, CReal_minus. ring. }
  rewrite E, CReal_abs_mult, (CReal_abs_right (posR p) (posR_nonneg p)).
  apply (CReal_le_trans _ (CReal_mult (posR p) (inject_Q (e * (1 # p))))).
  - apply CReal_mult_le_compat_l; [exact (posR_nonneg p)|exact b].
  - unfold posR, inject_Z. rewrite <- inject_Q_mult. apply inject_Q_le.
    destruct e as [n d]; cbv [Qle Qmult Qnum Qden].
    rewrite !Pos2Z.inj_mul; nia.
Qed.

(* 相关说明。 （已译） *)

Definition Circle@{o} : TopSpace@{o} :=
  TQuot@{o} RLine@{o} Circle_setoid@{o} circ_q@{o}.

Example Circle_points@{o} : top_carrier Circle@{o} = Circle_setoid@{o} :=
  eq_refl.

(* 相关说明。 （已译） *)
Definition cball_open@{o} (V : Circle_setoid@{o} → Type@{o}) : Type@{o} :=
  ∀ x, V x → { e : Q & (Qlt 0 e * ∀ y, cball@{o} x y e → V y)%type }.

(* 相关说明。 （已译） *)
Lemma circle_open_balls@{o} (V : Circle_setoid@{o} → Type@{o}) :
  IsOpen Circle@{o} V ↔ cball_open@{o} V.
Proof.
  split.
  - intros [Hp Ho] x v. destruct (Ho x v) as [e [He Hb]].
    exists e; split; [exact He|]. intros y [k b].
    apply (Hp (CReal_plus y (inject_Z k)) y (circ_eq_translate y k)).
    exact (Hb _ (rball_of_cball x y e k b)).
  - intro HV; split.
    + intros t t' e v. destruct (HV t v) as [d [Hd Hb]].
      exact (Hb t' (cball_of_eq t t' d Hd e)).
    + intros x v. destruct (HV x v) as [e [He Hb]].
      exists e; split; [exact He|]. intros y b.
      exact (Hb y (cball_of_rball x y e b)).
Qed.

(*
   本节说明 Circle 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition cint@{o} (c : CReal) (e : Q) (y : Circle_setoid@{o}) : Type@{o} :=
  { d : Q & (Qlt 0 d * ∀ y', cball@{o} y y' d → cball@{o} c y' e)%type }.

Lemma cint_balls@{o} (c : CReal) (e : Q) : cball_open@{o} (cint@{o} c e).
Proof.
  intros y [d [Hd H]]. exists (d * (1 # 2))%Q.
  split; [exact (q_half_pos d Hd)|].
  intros y' b. exists (d * (1 # 2))%Q. split; [exact (q_half_pos d Hd)|].
  intros y'' b'. apply H. apply (cball_mono _ _ _ _ (q_half_half d)).
  exact (cball_triang _ _ _ _ _ b b').
Qed.

Lemma cint_open@{o} (c : CReal) (e : Q) : IsOpen Circle@{o} (cint@{o} c e).
Proof. exact (snd (circle_open_balls _) (cint_balls c e)). Qed.

Lemma cint_centre@{o} (c : CReal) (e : Q) : Qlt 0 e → cint@{o} c e c.
Proof. intro He. exists e. split; [exact He|]. intros y' b; exact b. Qed.

Lemma cint_sub@{o} (c : CReal) (e : Q) (y : CReal) :
  cint@{o} c e y → cball@{o} c y e.
Proof.
  intros [d [Hd H]]. apply H. exact (cball_of_eq y y d Hd (circ_eq_refl y)).
Qed.

(*
   本节说明 Circle 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition wrap@{h o | o < h +} (p : positive) :
  Circle@{o} ~{Top@{h o}}~> Circle@{o} :=
  tquot_desc RLine Circle_setoid circ_q Circle
    (top_compose (tquot_proj RLine Circle_setoid circ_q) (rline_mul p))
    (circ_mul p) (fun x => circ_eq_refl _).

Example wrap_map@{h o | o < h +} (p : positive) :
  continuous_map (wrap@{h o} p) = circ_mul@{o} p := eq_refl.

(* At p = 1 wrapping map 恒等. （已译） *)
Lemma wrap_one@{h o | o < h +} : wrap@{h o} 1 ≈ @id Top@{h o} Circle@{o}.
Proof. intro x. apply circ_eq_of_creal. exact (CReal_mult_1_l x). Qed.

(* 相关说明。 （已译） *)

Definition PCircle@{o} : PTop@{o} :=
  PQuot@{o} PRLine@{o} Circle_setoid@{o} circ_q@{o}.

Example PCircle_points@{o} : pt_carrier PCircle@{o} = Circle_setoid@{o} :=
  eq_refl.

Definition pcball_open@{o} (V : Circle_setoid@{o} → Prop) : Prop :=
  ∀ x, V x → ex (fun e : Q => Qlt 0 e /\ ∀ y, cball@{o} x y e → V y).

Lemma pcircle_open_balls@{o} (V : Circle_setoid@{o} → Prop) :
  POpen PCircle@{o} V <-> pcball_open@{o} V.
Proof.
  split.
  - intros [Hp Ho] x v. destruct (Ho x v) as [e [He Hb]].
    exists e; split; [exact He|]. intros y [k b].
    apply (Hp (CReal_plus y (inject_Z k)) y (circ_eq_translate y k)).
    exact (Hb _ (rball_of_cball x y e k b)).
  - intro HV; split.
    + intros t t' e v. destruct (HV t v) as [d [Hd Hb]].
      exact (Hb t' (cball_of_eq t t' d Hd e)).
    + intros x v. destruct (HV x v) as [e [He Hb]].
      exists e; split; [exact He|]. intros y b.
      exact (Hb y (cball_of_rball x y e b)).
Qed.

Definition pwrap@{o so | o < so +} (p : positive) :
  PCircle@{o} ~{PTopCat@{o so}}~> PCircle@{o} :=
  pquot_desc PRLine Circle_setoid circ_q PCircle
    (pcompose (pquot_proj PRLine Circle_setoid circ_q) (prline_mul p))
    (circ_mul p) (fun x => circ_eq_refl _).

Example pwrap_map@{o so | o < so +} (p : positive) :
  pmap (pwrap@{o so} p) = circ_mul@{o} p := eq_refl.

Lemma pwrap_one@{o so | o < so +} :
  pwrap@{o so} 1 ≈ @id PTopCat@{o so} PCircle@{o}.
Proof. intro x. apply circ_eq_of_creal. exact (CReal_mult_1_l x). Qed.

(* 相关说明。 （已译） *)

Lemma circle_half_not_zero@{o} :
  @equiv _ Circle_setoid@{o} (inject_Q (1 # 2)) (inject_Q 0) → False.
Proof.
  intros [k Hk]. apply inject_Q_minus_int_inv in Hk.
  unfold Qeq, Qminus, Qplus in Hk; simpl in Hk. lia.
Qed.

(** ** The circle's points, lifted *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition circle_lift_iso@{h o hs | o < h, h < hs +} :
  @Isomorphism Sets@{h hs} (Setoid_Lift@{o h} Circle_setoid@{o})
    Circle_setoid@{h} := {|
  to := {| morphism := fun x : CReal => x |};
  from := {| morphism := fun x : CReal => x |}
|}.
Next Obligation. intros x y [k Hk]. exact (k; Hk). Qed.
Next Obligation. intros x y [k Hk]. exact (k; Hk). Qed.
Next Obligation. intro x. apply circ_eq_refl. Qed.
Next Obligation. intro x. apply circ_eq_refl. Qed.
