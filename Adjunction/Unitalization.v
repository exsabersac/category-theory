Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Coproduct.
Require Import Category.Instance.Ab.Monoidal.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rg.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

(*
    nLab: https://ncatlab.org/nlab/show/rng
    nLab: https://ncatlab.org/nlab/show/unitalisation
    Wikipedia: https://en.wikipedia.org/wiki/Rng_(algebra)#Adjoining_an_identity

   本文件给出伴随相关构造与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Lemma rg_mul_neg_l (R : RgObject) (a b : carrier R) :
  rg_mul R (ab_neg R a) b ≈ ab_neg R (rg_mul R a b).
Proof.
  apply (ab_neg_unique (rg_ab R)).
  rewrite <- rg_distr_r.
  rewrite (ab_neg_left (rg_ab R)).
  apply rg_mul_zero_l.
Qed.

Lemma rg_mul_neg_r (R : RgObject) (a b : carrier R) :
  rg_mul R a (ab_neg R b) ≈ ab_neg R (rg_mul R a b).
Proof.
  apply (ab_neg_unique (rg_ab R)).
  rewrite <- rg_distr_l.
  rewrite (ab_neg_left (rg_ab R)).
  apply rg_mul_zero_r.
Qed.

Lemma ab_neg_involution (A : AbObject) (a : carrier A) :
  ab_neg A (ab_neg A a) ≈ a.
Proof.
  symmetry.
  apply (ab_neg_unique A).
  apply (ab_neg_right A).
Qed.

(* 相关说明。 （已译） *)

Lemma rg_nat_smul_mul_l (R : RgObject) (k : nat) (a b : carrier R) :
  nat_smul (rg_ab R) k (rg_mul R a b)
    ≈ rg_mul R (nat_smul (rg_ab R) k a) b.
Proof.
  induction k as [|j IH]; simpl.
  - symmetry; apply rg_mul_zero_l.
  - rewrite IH.
    symmetry; apply rg_distr_r.
Qed.

Lemma rg_nat_smul_mul_r (R : RgObject) (k : nat) (a b : carrier R) :
  nat_smul (rg_ab R) k (rg_mul R a b)
    ≈ rg_mul R a (nat_smul (rg_ab R) k b).
Proof.
  induction k as [|j IH]; simpl.
  - symmetry; apply rg_mul_zero_r.
  - rewrite IH.
    symmetry; apply rg_distr_l.
Qed.

Lemma rg_zsmul_mul_l (R : RgObject) (n : Z) (a b : carrier R) :
  zsmul (rg_ab R) n (rg_mul R a b)
    ≈ rg_mul R (zsmul (rg_ab R) n a) b.
Proof.
  destruct n as [|p|p].
  - rewrite zsmul_Z0.
    symmetry; apply rg_mul_zero_l.
  - rewrite !zsmul_Zpos.
    apply rg_nat_smul_mul_l.
  - rewrite !zsmul_Zneg.
    rewrite (rg_nat_smul_mul_l R (Pos.to_nat p) a b).
    symmetry; apply rg_mul_neg_l.
Qed.

Lemma rg_zsmul_mul_r (R : RgObject) (n : Z) (a b : carrier R) :
  zsmul (rg_ab R) n (rg_mul R a b)
    ≈ rg_mul R a (zsmul (rg_ab R) n b).
Proof.
  destruct n as [|p|p].
  - rewrite zsmul_Z0.
    symmetry; apply rg_mul_zero_r.
  - rewrite !zsmul_Zpos.
    apply rg_nat_smul_mul_r.
  - rewrite !zsmul_Zneg.
    rewrite (rg_nat_smul_mul_r R (Pos.to_nat p) a b).
    symmetry; apply rg_mul_neg_r.
Qed.

(* 相关说明。 （已译） *)

Lemma nat_smul_mul (A : AbObject) (j k : nat) (a : carrier A) :
  nat_smul A (j * k) a ≈ nat_smul A j (nat_smul A k a).
Proof.
  induction j as [|j IH]; simpl.
  - reflexivity.
  - rewrite nat_smul_add, IH.
    reflexivity.
Qed.

Lemma zsmul_mul (A : AbObject) (m n : Z) (a : carrier A) :
  zsmul A (m * n)%Z a ≈ zsmul A m (zsmul A n a).
Proof.
  destruct m as [|p|p]; destruct n as [|q|q]; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - symmetry; apply nat_smul_zero.
  - rewrite Pos2Nat.inj_mul.
    apply nat_smul_mul.
  - rewrite Pos2Nat.inj_mul.
    rewrite nat_smul_mul.
    symmetry; apply nat_smul_neg.
  - symmetry.
    rewrite nat_smul_zero.
    apply ab_neg_zero.
  - rewrite Pos2Nat.inj_mul.
    apply (ab_neg_respects A).
    apply nat_smul_mul.
  - rewrite Pos2Nat.inj_mul.
    rewrite nat_smul_mul.
    rewrite nat_smul_neg.
    symmetry; apply ab_neg_involution.
Qed.

Lemma cmon_swap_head (P : CMonObject) (a b r : carrier (cmon_setoid P)) :
  cmon_plus P a (cmon_plus P b r) ≈ cmon_plus P b (cmon_plus P a r).
Proof.
  rewrite <- !cmon_plus_assoc.
  now rewrite (cmon_plus_comm P a b).
Qed.

(** ** The Dorroh extension *)

Section Dorroh.

Context (R : RgObject).

Definition dorroh_ab : AbObject := Ab_product ZAb (rg_ab R).

Definition dorroh_mul (x y : carrier dorroh_ab) : carrier dorroh_ab :=
  (Z.mul (fst x) (fst y),
   cmon_plus (rg_ab R)
     (cmon_plus (rg_ab R)
        (zsmul (rg_ab R) (fst x) (snd y))
        (zsmul (rg_ab R) (fst y) (snd x)))
     (rg_mul R (snd x) (snd y))).

Definition dorroh_one : carrier dorroh_ab := (1%Z, cmon_zero (rg_ab R)).

Lemma dorroh_mul_respects :
  Proper (equiv ==> equiv ==> equiv) dorroh_mul.
Proof.
  intros x x' [Hx1 Hx2] y y' [Hy1 Hy2].
  split; simpl.
  - unfold Z_eqT in *; simpl in *; now rewrite Hx1, Hy1.
  - apply cmon_plus_respects.
    + apply cmon_plus_respects.
      * unfold Z_eqT in Hx1; simpl in Hx1; rewrite Hx1.
        now apply zsmul_respects.
      * unfold Z_eqT in Hy1; simpl in Hy1; rewrite Hy1.
        now apply zsmul_respects.
    + now apply rg_mul_respects.
Qed.

Lemma dorroh_mul_assoc (x y z : carrier dorroh_ab) :
  dorroh_mul (dorroh_mul x y) z ≈ dorroh_mul x (dorroh_mul y z).
Proof.
  destruct x as [m a], y as [n b], z as [p c].
  split; simpl.
  - assert (H : (m * n * p = m * (n * p))%Z) by ring; exact H.
  - rewrite !zsmul_plus, !rg_distr_r, !rg_distr_l.
    rewrite <- !(rg_zsmul_mul_l R), <- !(rg_zsmul_mul_r R).
    rewrite <- !zsmul_mul.
    rewrite (Z.mul_comm p m), (Z.mul_comm p n).
    rewrite (rg_mul_assoc R a b c).
    rewrite !cmon_plus_assoc.
    apply cmon_plus_respects; [ reflexivity | ].
    apply cmon_plus_respects; [ reflexivity | ].
    etransitivity.
    { apply cmon_plus_respects; [ reflexivity | apply cmon_swap_head ]. }
    etransitivity.
    { apply cmon_swap_head. }
    apply cmon_plus_respects; [ reflexivity | ].
    apply cmon_plus_respects; [ reflexivity | ].
    apply cmon_swap_head.
Qed.

Lemma dorroh_mul_one_l (x : carrier dorroh_ab) :
  dorroh_mul dorroh_one x ≈ x.
Proof.
  destruct x as [n b].
  split; simpl.
  - assert (H : (1 * n = n)%Z) by ring; exact H.
  - now rewrite zsmul_zero_r, rg_mul_zero_l, !cmon_plus_zero_r.
Qed.

Lemma dorroh_mul_one_r (x : carrier dorroh_ab) :
  dorroh_mul x dorroh_one ≈ x.
Proof.
  destruct x as [n b].
  split; simpl.
  - assert (H : (n * 1 = n)%Z) by ring; exact H.
  - now rewrite zsmul_zero_r, rg_mul_zero_r, !cmon_plus_zero_r,
      cmon_plus_zero_l.
Qed.

Lemma dorroh_distr_l (x y z : carrier dorroh_ab) :
  dorroh_mul x (cmon_plus dorroh_ab y z)
    ≈ cmon_plus dorroh_ab (dorroh_mul x y) (dorroh_mul x z).
Proof.
  destruct x as [m a], y as [n b], z as [p c].
  split; simpl.
  - assert (H : (m * (n + p) = m * n + m * p)%Z) by ring; exact H.
  - rewrite zsmul_plus, zsmul_add, rg_distr_l.
    rewrite (cmon_plus_interchange (rg_ab R)
               (zsmul (rg_ab R) m b) (zsmul (rg_ab R) m c)
               (zsmul (rg_ab R) n a) (zsmul (rg_ab R) p a)).
    apply cmon_plus_interchange.
Qed.

Lemma dorroh_distr_r (x y z : carrier dorroh_ab) :
  dorroh_mul (cmon_plus dorroh_ab x y) z
    ≈ cmon_plus dorroh_ab (dorroh_mul x z) (dorroh_mul y z).
Proof.
  destruct x as [m a], y as [n b], z as [p c].
  split; simpl.
  - assert (H : ((m + n) * p = m * p + n * p)%Z) by ring; exact H.
  - rewrite zsmul_add, zsmul_plus, rg_distr_r.
    rewrite (cmon_plus_interchange (rg_ab R)
               (zsmul (rg_ab R) m c) (zsmul (rg_ab R) n c)
               (zsmul (rg_ab R) p a) (zsmul (rg_ab R) p b)).
    apply cmon_plus_interchange.
Qed.

Lemma dorroh_mul_zero_l (x : carrier dorroh_ab) :
  dorroh_mul (cmon_zero dorroh_ab) x ≈ cmon_zero dorroh_ab.
Proof.
  destruct x as [n b].
  split; simpl.
  - assert (H : (0 * n = 0)%Z) by ring; exact H.
  - now rewrite zsmul_zero_r, rg_mul_zero_l, !cmon_plus_zero_r.
Qed.

Lemma dorroh_mul_zero_r (x : carrier dorroh_ab) :
  dorroh_mul x (cmon_zero dorroh_ab) ≈ cmon_zero dorroh_ab.
Proof.
  destruct x as [n b].
  split; simpl.
  - assert (H : (n * 0 = 0)%Z) by ring; exact H.
  - now rewrite zsmul_zero_r, rg_mul_zero_r, !cmon_plus_zero_r.
Qed.

(* 相关说明。 （已译） *)
Definition dorroh_rig : RigObject := {|
  rig_setoid := cmon_setoid dorroh_ab;
  rig_zero := cmon_zero dorroh_ab;
  rig_add := cmon_plus dorroh_ab;
  rig_one := dorroh_one;
  rig_mul := dorroh_mul;
  rig_add_respects := cmon_plus_respects dorroh_ab;
  rig_mul_respects := dorroh_mul_respects;
  rig_add_assoc := cmon_plus_assoc dorroh_ab;
  rig_add_comm := cmon_plus_comm dorroh_ab;
  rig_add_zero_l := cmon_plus_zero_l dorroh_ab;
  rig_mul_assoc := dorroh_mul_assoc;
  rig_mul_one_l := dorroh_mul_one_l;
  rig_mul_one_r := dorroh_mul_one_r;
  rig_distr_l := dorroh_distr_l;
  rig_distr_r := dorroh_distr_r;
  rig_mul_zero_l := dorroh_mul_zero_l;
  rig_mul_zero_r := dorroh_mul_zero_r
|}.

Definition Dorroh : RingObject := {|
  ring_rig := dorroh_rig;
  ring_neg := ab_neg dorroh_ab;
  ring_neg_respects := ab_neg_respects dorroh_ab;
  ring_neg_l := ab_neg_left dorroh_ab
|}.

End Dorroh.

(* * ** The unit: 嵌入 rng （已译） *)

#[local] Obligation Tactic := idtac.

Program Definition dorroh_insert (R : RgObject)
  : R ~{Rg}~> ring_rg (Dorroh R) := {|
  rg_hom_ab := {|
    cmon_map := {| morphism := fun a => (0%Z, a) |}
  |}
|}.
Next Obligation. intros R x y H; split; [ reflexivity | exact H ]. Qed.
Next Obligation. intros R; reflexivity. Qed.
Next Obligation. intros R a b; reflexivity. Qed.
Next Obligation.
  intros R a b; split; [ reflexivity | ].
  simpl; symmetry; now rewrite !cmon_plus_zero_l.
Qed.

(* 相关说明。 （已译） *)

Lemma rig_iter_is_nat_smul (S : RingObject) (k : nat) :
  rig_iter S k = nat_smul (ring_ab S) k (rig_one S).
Proof.
  induction k as [|j IH]; simpl.
  - reflexivity.
  - now rewrite IH.
Qed.

Lemma zring_is_zsmul_one (S : RingObject) (n : Z) :
  zring S n = zsmul (ring_ab S) n (rig_one S).
Proof.
  destruct n as [|p|p]; simpl.
  - reflexivity.
  - apply rig_iter_is_nat_smul.
  - now rewrite rig_iter_is_nat_smul.
Qed.

Lemma zring_mul_zsmul_l (S : RingObject) (n : Z)
  (x : carrier (rig_setoid S)) :
  rig_mul S (zring S n) x ≈ zsmul (ring_ab S) n x.
Proof.
  rewrite zring_is_zsmul_one.
  etransitivity.
  { symmetry; exact (rg_zsmul_mul_l (ring_rg S) n (rig_one S) x). }
  exact (zsmul_respects (ring_ab S) n _ _ (rig_mul_one_l S x)).
Qed.

Lemma zring_mul_zsmul_r (S : RingObject) (n : Z)
  (x : carrier (rig_setoid S)) :
  rig_mul S x (zring S n) ≈ zsmul (ring_ab S) n x.
Proof.
  rewrite zring_is_zsmul_one.
  etransitivity.
  { symmetry; exact (rg_zsmul_mul_r (ring_rg S) n x (rig_one S)). }
  exact (zsmul_respects (ring_ab S) n _ _ (rig_mul_one_r S x)).
Qed.

Corollary zring_is_central (S : RingObject) (n : Z)
  (x : carrier (rig_setoid S)) :
  rig_mul S (zring S n) x ≈ rig_mul S x (zring S n).
Proof.
  rewrite zring_mul_zsmul_l.
  symmetry; apply zring_mul_zsmul_r.
Qed.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Unitalization 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma rig_hom_preserves_zring (A B : RingObject) (h : RigHom A B) (n : Z) :
  rig_map h (zring A n) ≈ zring B n.
Proof.
  apply (Z_peano_rect (fun z => rig_map h (zring A z) ≈ zring B z)).
  - apply (rig_map_zero h).
  - intros z IH.
    rewrite (proper_morphism (rig_map h) _ _ (zring_succ A z)).
    rewrite (rig_map_add h).
    rewrite (rig_map_one h), IH.
    symmetry; apply zring_succ.
  - intros z IH.
    rewrite (proper_morphism (rig_map h) _ _ (zring_pred A z)).
    rewrite (rig_map_add h).
    rewrite (RigHom_neg A B h (rig_one A)).
    rewrite (rig_map_one h), IH.
    symmetry; apply zring_pred.
Qed.

Lemma dorroh_zring (R : RgObject) (n : Z) :
  zring (Dorroh R) n
    ≈ ((n, cmon_zero (rg_ab R)) : carrier (rig_setoid (Dorroh R))).
Proof.
  apply (Z_peano_rect
           (fun z : Z => zring (Dorroh R) z
              ≈ ((z, cmon_zero (rg_ab R))
                   : carrier (rig_setoid (Dorroh R))))).
  - reflexivity.
  - intros z IH.
    rewrite zring_succ, IH.
    split; simpl.
    + apply Z.add_1_l.
    + apply cmon_plus_zero_l.
  - intros z IH.
    rewrite zring_pred, IH.
    split; simpl.
    + assert (K : ((-1) + z = Z.pred z)%Z) by lia; exact K.
    + rewrite ab_neg_zero.
      apply cmon_plus_zero_l.
Qed.

(** ** The unique unital extension *)

Section Extend.

Context (R : RgObject) (S : RingObject).
Context (f : R ~{Rg}~> ring_rg S).

(*
   本节说明 Unitalization 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma dext_f_zero :
  cmon_map (rg_hom_ab f) (cmon_zero (rg_ab R)) ≈ rig_zero S.
Proof. apply (cmon_map_zero (rg_hom_ab f)). Qed.

Lemma dext_f_add (a b : carrier R) :
  cmon_map (rg_hom_ab f) (cmon_plus (rg_ab R) a b)
    ≈ rig_add S (cmon_map (rg_hom_ab f) a) (cmon_map (rg_hom_ab f) b).
Proof. apply (cmon_map_plus (rg_hom_ab f)). Qed.

Lemma dext_f_mul (a b : carrier R) :
  cmon_map (rg_hom_ab f) (rg_mul R a b)
    ≈ rig_mul S (cmon_map (rg_hom_ab f) a) (cmon_map (rg_hom_ab f) b).
Proof. apply (rg_map_mul f a b). Qed.

Lemma dext_f_zsmul (n : Z) (a : carrier R) :
  cmon_map (rg_hom_ab f) (zsmul (rg_ab R) n a)
    ≈ rig_mul S (zring S n) (cmon_map (rg_hom_ab f) a).
Proof.
  rewrite zring_mul_zsmul_l.
  apply (zsmul_hom (rg_hom_ab f) n a).
Qed.

Definition dorroh_ext_map (x : carrier (rig_setoid (Dorroh R)))
  : carrier (rig_setoid S) :=
  rig_add S (zring S (fst x)) (cmon_map (rg_hom_ab f) (snd x)).

Program Definition dorroh_extend : Dorroh R ~{Rng}~> S := {|
  rig_map := {| morphism := dorroh_ext_map |}
|}.
Next Obligation.
  intros x y [H1 H2]; unfold dorroh_ext_map.
  unfold Z_eqT in H1; simpl in H1, H2.
  now rewrite H1, H2.
Qed.
Next Obligation.
  unfold dorroh_ext_map; simpl.
  rewrite dext_f_zero.
  apply rig_add_zero_l.
Qed.
Next Obligation.
  intros x y; destruct x as [m a], y as [n b].
  unfold dorroh_ext_map; simpl.
  rewrite zring_add, dext_f_add.
  apply (cmon_plus_interchange (ring_ab S)).
Qed.
Next Obligation.
  unfold dorroh_ext_map; simpl.
  rewrite dext_f_zero, rig_add_zero_r.
  apply rig_add_zero_r.
Qed.
Next Obligation.
  intros x y; destruct x as [m a], y as [n b].
  unfold dorroh_ext_map; simpl.
  rewrite zring_mul.
  rewrite !dext_f_add, dext_f_mul, !dext_f_zsmul.
  rewrite !rig_distr_r, !rig_distr_l.
  rewrite (zring_is_central S n (cmon_map (rg_hom_ab f) a)).
  now rewrite !rig_add_assoc.
Qed.

Lemma dorroh_extend_commutes (a : carrier R) :
  rig_map dorroh_extend (0%Z, a) ≈ cmon_map (rg_hom_ab f) a.
Proof.
  unfold dorroh_ext_map; simpl.
  apply rig_add_zero_l.
Qed.

Lemma dorroh_extend_unique (h : Dorroh R ~{Rng}~> S)
  (Hh : ∀ a : carrier R,
          rig_map h (0%Z, a) ≈ cmon_map (rg_hom_ab f) a)
  (x : carrier (rig_setoid (Dorroh R))) :
  rig_map h x ≈ rig_map dorroh_extend x.
Proof.
  destruct x as [n a].
  (* (n, a) splits as (n, 0) + (0, a) *)
  assert (Hsplit : ((n : carrier ZAb), a)
            ≈ rig_add (Dorroh R) (n, cmon_zero (rg_ab R)) (0%Z, a)).
  { split; simpl.
    - symmetry; apply Z.add_0_r.
    - symmetry; apply cmon_plus_zero_l. }
  (* and h (n, 0) is forced to be zring S n *)
  assert (Hz : rig_map h ((n, cmon_zero (rg_ab R))
                            : carrier (rig_setoid (Dorroh R)))
                 ≈ zring S n).
  { etransitivity.
    - apply (proper_morphism (rig_map h)).
      symmetry; exact (dorroh_zring R n).
    - exact (rig_hom_preserves_zring (Dorroh R) S h n). }
  etransitivity.
  { apply (proper_morphism (rig_map h)); exact Hsplit. }
  rewrite (rig_map_add h).
  apply rig_add_respects; [ exact Hz | exact (Hh a) ].
Qed.

End Extend.

(* * ** The 普遍性质, both encodings （已译） *)

Program Definition dorroh_ump (R : RgObject) (S : RingObject)
  (f : R ~{Rg}~> ring_rg S)
  : ∃! g : Dorroh R ~{Rng}~> S,
      f ≈ fmap[Rng_Forget_Rg] g ∘ dorroh_insert R := {|
  unique_obj := dorroh_extend R S f
|}.
Next Obligation.
  intros R S f a; simpl.
  symmetry; apply (dorroh_extend_commutes R S f a).
Qed.
Next Obligation.
  intros R S f v Hv a; simpl.
  symmetry.
  apply (dorroh_extend_unique R S f v).
  intro b; symmetry; exact (Hv b).
Qed.

Definition dorroh_universal (R : RgObject)
  : @UniversalArrow Rg Rng R Rng_Forget_Rg :=
  @universal_arrow_from_UMP Rg Rng R Rng_Forget_Rg (Dorroh R)
    (dorroh_insert R) (fun S f => dorroh_ump R S f).

Program Definition dorroh_auniversal (R : RgObject)
  : @AUniversalArrow Rg Rng R Rng_Forget_Rg (Dorroh R) := {|
  universal_arrow := dorroh_insert R;
  universal_arrow_universal := fun S f => {|
    unique_obj := dorroh_extend R S f
  |}
|}.
Next Obligation.
  intros R S f a; simpl.
  apply (dorroh_extend_commutes R S f a).
Qed.
Next Obligation.
  intros R S f v Hv a; simpl.
  symmetry.
  apply (dorroh_extend_unique R S f v).
  intro b; exact (Hv b).
Qed.

(* * ** The unitalization 函子 伴随 （已译） *)

Definition DorrohFunctor : Rg ⟶ Rng :=
  LeftAdjointFunctorFromUniversalArrows Rng_Forget_Rg dorroh_universal.

Definition unitalization_adjunction : DorrohFunctor ⊣ Rng_Forget_Rg :=
  AdjunctionFromUniversalArrows Rng_Forget_Rg dorroh_universal.

(* * ** The unit monic; forgetful 函子 faithful （已译） *)

#[export] Program Instance dorroh_insert_Monic (R : RgObject)
  : Monic (dorroh_insert R).
Next Obligation.
  intros R Q g1 g2 H a.
  exact (snd (H a)).
Qed.

Lemma dorroh_insert_injective (R : RgObject) (a b : carrier R) :
  cmon_map (rg_hom_ab (dorroh_insert R)) a
    ≈ cmon_map (rg_hom_ab (dorroh_insert R)) b → a ≈ b.
Proof. intro H; exact (snd H). Qed.

Definition unitalization_forgetful_Faithful : Faithful Rng_Forget_Rg :=
  Rng_Forget_Rg_Faithful.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Example dorroh_carrier_strict (R : RgObject) :
  carrier (rig_setoid (Dorroh R))
    = (carrier ZAb * carrier (rg_ab R))%type := eq_refl.

Example dorroh_zero_strict (R : RgObject) :
  rig_zero (Dorroh R)
    = ((0%Z, cmon_zero (rg_ab R)) : carrier (rig_setoid (Dorroh R)))
  := eq_refl.

Example dorroh_one_strict (R : RgObject) :
  rig_one (Dorroh R)
    = ((1%Z, cmon_zero (rg_ab R)) : carrier (rig_setoid (Dorroh R)))
  := eq_refl.

Example dorroh_add_strict (R : RgObject) :
  rig_add (Dorroh R) = cmon_plus (dorroh_ab R) := eq_refl.

Example dorroh_neg_strict (R : RgObject) :
  ring_neg (Dorroh R) = ab_neg (dorroh_ab R) := eq_refl.

Example dorroh_mul_strict (R : RgObject) :
  rig_mul (Dorroh R) = dorroh_mul R := eq_refl.

(* 相关说明。 （已译） *)
Example dorroh_insert_strict (R : RgObject) (a : carrier R) :
  cmon_map (rg_hom_ab (dorroh_insert R)) a
    = ((0%Z, a) : carrier (rig_setoid (Dorroh R))) := eq_refl.

(* The 泛箭头 extracted comma-packaged class IS the
 嵌入, 左伴随's 对象 action IS [Dorroh]. （已译） *)
Example dorroh_arrow_strict (R : RgObject) :
  @arrow Rg Rng R Rng_Forget_Rg (dorroh_universal R) = dorroh_insert R
  := eq_refl.

Example dorroh_fobj_strict (R : RgObject) :
  fobj[DorrohFunctor] R = Dorroh R := eq_refl.

(* 相关说明。 （已译） *)
Example dorroh_auniversal_med_strict (R : RgObject) (S : RingObject)
  (f : R ~{Rg}~> ring_rg S) :
  unique_obj (@universal_arrow_universal Rg Rng R Rng_Forget_Rg (Dorroh R)
                (dorroh_auniversal R) S f) = dorroh_extend R S f := eq_refl.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example dorroh_unit_is_insert_strict (R : RgObject) :
  @unit Rng Rg DorrohFunctor Rng_Forget_Rg unitalization_adjunction R
    = dorroh_insert R := eq_refl.

Fail Example dorroh_ump_med_strict (R : RgObject) (S : RingObject)
  (f : R ~{Rg}~> ring_rg S) :
  unique_obj (@ump_universal_arrows Rg Rng R Rng_Forget_Rg
                (dorroh_universal R) S f) = dorroh_extend R S f := eq_refl.

(* * ** The unit counit produced 伴随 （已译） *)

Lemma unitalization_unit_is_insert (R : RgObject) :
  @unit Rng Rg DorrohFunctor Rng_Forget_Rg unitalization_adjunction R
    ≈ dorroh_insert R.
Proof. intro a; reflexivity. Qed.

Lemma unitalization_counit_insert (S : RingObject)
  (a : carrier (rig_setoid S)) :
  rig_map (@counit Rng Rg DorrohFunctor Rng_Forget_Rg
             unitalization_adjunction S) (0%Z, a) ≈ a.
Proof.
  symmetry.
  exact (unique_property
           (@ump_universal_arrows Rg Rng (ring_rg S) Rng_Forget_Rg
              (dorroh_universal (ring_rg S)) S (@id Rg (ring_rg S))) a).
Qed.

Lemma unitalization_counit_is_extend (S : RingObject)
  (x : carrier (rig_setoid (Dorroh (ring_rg S)))) :
  rig_map (@counit Rng Rg DorrohFunctor Rng_Forget_Rg
             unitalization_adjunction S) x
    ≈ rig_map (dorroh_extend (ring_rg S) S (@id Rg (ring_rg S))) x.
Proof.
  apply (dorroh_extend_unique (ring_rg S) S (@id Rg (ring_rg S))).
  intro a; exact (unitalization_counit_insert S a).
Qed.

(*
   本节说明 Unitalization 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition DorrohTwoZ : RingObject := Dorroh TwoZ_Rg.

Definition dtz (m a : Z) : carrier (rig_setoid DorrohTwoZ) := (m, a).

(* Adjoining an identity to a rng that provably had none: 1 ≉ 0. *)
Theorem dorroh_TwoZ_unital :
  rig_one DorrohTwoZ ≈ rig_zero DorrohTwoZ → False.
Proof. intros [H1 _]; discriminate H1. Qed.

(* Two provably distinct elements, both outside image the
 嵌入's ℤ coordinate. （已译） *)
Theorem dorroh_TwoZ_two_elements : dtz 1 0 ≈ dtz 2 0 → False.
Proof. intros [H1 _]; discriminate H1. Qed.

(* The 嵌入 not surjective: nothing lands 恒等. （已译） *)
Theorem dorroh_TwoZ_insert_not_surjective :
  ∀ a : carrier TwoZ_Rg,
    cmon_map (rg_hom_ab (dorroh_insert TwoZ_Rg)) a
      ≈ rig_one DorrohTwoZ → False.
Proof. intros a [H1 _]; discriminate H1. Qed.

(* The multiplication computes, it visibly 所消耗 ℤ-action:
 (1,0)·(0,5) (0,5), not componentwise (0,0). （已译） *)
Example dorroh_TwoZ_mul_computes :
  dorroh_mul TwoZ_Rg (dtz 1 3) (dtz 0 5) = dtz 0 35 := eq_refl.

Example dorroh_TwoZ_action_computes :
  dorroh_mul TwoZ_Rg (dtz 1 0) (dtz 0 5) = dtz 0 5 := eq_refl.

Theorem dorroh_TwoZ_mul_not_componentwise :
  dorroh_mul TwoZ_Rg (dtz 1 0) (dtz 0 5) ≈ dtz 0 0 → False.
Proof. intros [_ H2]; discriminate H2. Qed.

(* And universal extension computes. Instance/Rg.v's [TwoZ_incl] is
 doubling map 2ℤ ↪ ℤ; extending it along 嵌入 sends
 (3, 4) 3 + 2·4 = 11. （已译） *)
Example dorroh_TwoZ_extend_computes :
  rig_map (dorroh_extend TwoZ_Rg Int_Ring TwoZ_incl) (dtz 3 4) = 11%Z
  := eq_refl.

Example dorroh_TwoZ_extend_one :
  rig_map (dorroh_extend TwoZ_Rg Int_Ring TwoZ_incl) (dtz 1 0) = 1%Z
  := eq_refl.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Unitalization 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section ProbeRgObjects.
Universes ao ah ap.
Constraint ao < ah.

Check (RgObject@{ap ao ah} : Type).
Check (fun (R : RgObject@{ap ao ah}) (a b : carrier R) => rg_mul R a b).
Fail Check (fun R : RgObject@{ap ao ah} => (R : obj[Rg])).

End ProbeRgObjects.

Section ProbeDonorPin.
Universes bo bh bp.
Constraint Set < bh.

Check (fun R : RgObject@{bp bo bh} => Dorroh R).
Check (fun R : RgObject@{bp bo bh} => zring (Dorroh R)).
Fail Check (fun R : RgObject@{bp bo bh} => rng_from_Z (Dorroh R)).

End ProbeDonorPin.

(* 相关说明。 （已译） *)

Set Printing Universes.
About Dorroh.
About unitalization_adjunction.
Unset Printing Universes.
