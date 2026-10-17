Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Quotient.
Require Import Category.Instance.Rng.Algebras.Associative.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   本文件给出商相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** ℤ·E₁₁ as a left ideal of UT2 *)

Definition ut2_col1 (x : ut2) : Type := { a : Z & x = (a, 0, 0)%Z }.

Program Definition E11Left : LeftIdeal UT2 := {| lidl_mem := ut2_col1 |}.
Next Obligation.
  intros x y Hxy [a Ha]; unfold ut2_eqT in Hxy.
  exists a; now subst.
Qed.
Next Obligation. exists 0%Z; reflexivity. Qed.
Next Obligation.
  intros [[x1 x2] x3] [[y1 y2] y3] [a Ha] [b Hb].
  inversion Ha; inversion Hb; subst.
  exists (a + b)%Z.
  unfold rig_add, UT2, UT2_Rig, ut2_add; simpl.
  apply ut2_eq3; ring.
Qed.
Next Obligation.
  intros [[r1 r2] r3] [[x1 x2] x3] [a Ha].
  inversion Ha; subst.
  exists (r1 * a)%Z.
  unfold rig_mul, UT2, UT2_Rig, ut2_mul; simpl.
  apply ut2_eq3; ring.
Qed.

(* Non-vacuity of the left ideal itself: E₁₁ is in it and is not zero. *)
Theorem E11Left_nontrivial :
  lidl_mem E11Left ut2_e11 * (ut2_e11 = ut2_zero → False).
Proof.
  split.
  - exists 1%Z; reflexivity.
  - discriminate.
Qed.

(** ** It is NOT a right ideal *)

(* E₁₁ · E₁₂ = E₁₂, which has a nonzero entry off the first column. *)
Example ut2_e11_times_e12 : rig_mul UT2 ut2_e11 ut2_e12 = ut2_e12 := eq_refl.

Theorem ut2_e11_not_right_absorbing :
  lidl_mem E11Left (rig_mul UT2 ut2_e11 ut2_e12) → False.
Proof. intros [a Ha]; discriminate Ha. Qed.

(* So the fifth field of [Ideal] is not derivable from the other four:
   no [Ideal UT2] has [E11Left]'s membership predicate. *)
Theorem E11Left_is_not_an_Ideal :
  { I : Ideal UT2 & ∀ x, idl_mem I x ↔ lidl_mem E11Left x } → False.
Proof.
  intros [I HI].
  apply ut2_e11_not_right_absorbing.
  apply (fst (HI _)).
  apply idl_absorb_r.
  apply (snd (HI _)).
  exists 1%Z; reflexivity.
Qed.

(*
   本节说明 OneSided 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 OneSided 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma ut2_e11_rel_zero : lquot_rel E11Left ut2_e11 ut2_zero.
Proof. constructor; exists 1%Z; reflexivity. Qed.

Lemma ut2_e12_rel_self : lquot_rel E11Left ut2_e12 ut2_e12.
Proof. constructor; exists 0%Z; reflexivity. Qed.

Theorem ut2_left_ideal_not_mul_congruence :
  LeftIdealMulCongruence E11Left → False.
Proof.
  intro Hcong.
  pose proof (Hcong ut2_e11 ut2_zero ut2_e12 ut2_e12
                ut2_e11_rel_zero ut2_e12_rel_self) as H.
  destruct H as [[a Ha]].
  discriminate Ha.
Qed.

(*
   本节说明 OneSided 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition ut2_strict (x : ut2) : Type := { b : Z & x = (0, b, 0)%Z }.

Program Definition StrictUpper : Ideal UT2 := {| idl_mem := ut2_strict |}.
Next Obligation.
  intros x y Hxy [b Hb]; unfold ut2_eqT in Hxy.
  exists b; now subst.
Qed.
Next Obligation. exists 0%Z; reflexivity. Qed.
Next Obligation.
  intros [[x1 x2] x3] [[y1 y2] y3] [b Hb] [c Hc].
  inversion Hb; inversion Hc; subst.
  exists (b + c)%Z.
  unfold rig_add, UT2, UT2_Rig, ut2_add; simpl.
  apply ut2_eq3; ring.
Qed.
Next Obligation.
  intros [[r1 r2] r3] [[x1 x2] x3] [b Hb].
  inversion Hb; subst.
  exists (r1 * b)%Z.
  unfold rig_mul, UT2, UT2_Rig, ut2_mul; simpl.
  apply ut2_eq3; ring.
Qed.
Next Obligation.
  intros [[x1 x2] x3] [[r1 r2] r3] [b Hb].
  inversion Hb; subst.
  exists (b * r3)%Z.
  unfold rig_mul, UT2, UT2_Rig, ut2_mul; simpl.
  apply ut2_eq3; ring.
Qed.

Definition StrictUpper_congruence : IdealMulCongruence StrictUpper :=
  ideal_mul_congruence StrictUpper.

(* Proper: E₁₁ is not strictly upper triangular. *)
Theorem StrictUpper_proper : idl_mem StrictUpper ut2_e11 → False.
Proof. intros [b Hb]; discriminate Hb. Qed.

(* Nontrivial: E₁₂ is, and is not zero. *)
Theorem StrictUpper_nontrivial :
  idl_mem StrictUpper ut2_e12 * (ut2_e12 = ut2_zero → False).
Proof.
  split.
  - exists 1%Z; reflexivity.
  - discriminate.
Qed.

(*
   本节说明 OneSided 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem UT2_mod_strict_not_collapsed :
  rquot_rel StrictUpper ut2_e11 ut2_zero → False.
Proof. intros [[b Hb]]; discriminate Hb. Qed.

Theorem UT2_mod_strict_collapses_e12 :
  rig_map (rquot_proj StrictUpper) ut2_e12
    ≈ rig_map (rquot_proj StrictUpper) ut2_zero.
Proof. constructor; exists 1%Z; reflexivity. Qed.

(* The quotient ring UT2/StrictUpper is not the zero ring. *)
Theorem UT2_mod_strict_nonzero :
  rig_one (QuotientRing StrictUpper) ≈ rig_zero (QuotientRing StrictUpper)
    → False.
Proof. intros [[b Hb]]; discriminate Hb. Qed.

(*
   本节说明 OneSided 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem UT2_mod_strict_commutative :
  ∀ x y : carrier (rig_setoid (QuotientRing StrictUpper)),
    rig_mul (QuotientRing StrictUpper) x y
      ≈ rig_mul (QuotientRing StrictUpper) y x.
Proof.
  intros [[x1 x2] x3] [[y1 y2] y3].
  constructor.
  exists (x1 * y2 + x2 * y3 - (y1 * x2 + y2 * x3))%Z.
  unfold rig_mul, UT2, UT2_Rig, ut2_mul; simpl.
  apply ut2_eq3; ring.
Qed.
