Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Universal.Element.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(*
   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Obligation Tactic := idtac.

(*
   nLab:      https://ncatlab.org/nlab/show/tensor+product+of+modules
   nLab:      https://ncatlab.org/nlab/show/universal+element
   Wikipedia: https://en.wikipedia.org/wiki/Tensor_product_of_modules
   Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,
   Book: Riehl, Category Theory in Context, Dover 2016, §2.3, printed

   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Bilinear maps *)

Section Bilinear.

Context (R : RingObject).
Context (V V' : RModObject R).

(*
   本节说明 Tensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record RBilinear (W : RModObject R) := {
  rbl_map : carrier (cmon_setoid V) →
            carrier (cmon_setoid V') → carrier (cmon_setoid W);

  rbl_respects : Proper (equiv ==> equiv ==> equiv) rbl_map;

  (* (v + v') ⊗ w = v ⊗ w + v' ⊗ w *)
  rbl_add_l (v v' : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
    rbl_map (cmon_plus V v v') w
      ≈ cmon_plus W (rbl_map v w) (rbl_map v' w);
  (* v ⊗ (w + w') = v ⊗ w + v ⊗ w' *)
  rbl_add_r (v : carrier (cmon_setoid V)) (w w' : carrier (cmon_setoid V')) :
    rbl_map v (cmon_plus V' w w')
      ≈ cmon_plus W (rbl_map v w) (rbl_map v w');
  (* (r·v) ⊗ w = r·(v ⊗ w) *)
  rbl_smul_l (r : carrier (rig_setoid (ring_rig R)))
             (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
    rbl_map (rm_smul V r v) w ≈ rm_smul W r (rbl_map v w);
  (* v ⊗ (r·w) = r·(v ⊗ w) *)
  rbl_smul_r (r : carrier (rig_setoid (ring_rig R)))
             (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
    rbl_map v (rm_smul V' r w) ≈ rm_smul W r (rbl_map v w)
}.

End Bilinear.

Arguments RBilinear {R} V V' W.
Arguments rbl_map {R V V' W} _ _ _.
Arguments rbl_respects {R V V' W} _.
Arguments rbl_add_l {R V V' W} _ _ _ _.
Arguments rbl_add_r {R V V' W} _ _ _ _.
Arguments rbl_smul_l {R V V' W} _ _ _ _.
Arguments rbl_smul_r {R V V' W} _ _ _ _.

#[export] Existing Instance rbl_respects.

Section BilinearFacts.

Context {R : RingObject}.
Context {V V' W : RModObject R}.
Context (β : RBilinear V V' W).

(** 0 ⊗ w ≈ 0, by cancelling [0 ⊗ w] against itself — the argument of
    Instance/Mod.v's [rm_smul_zero_l], one level up. *)
Lemma rbl_zero_l (w : carrier (cmon_setoid V')) :
  rbl_map β (cmon_zero V) w ≈ cmon_zero W.
Proof.
  apply (ab_cancel_l W (rbl_map β (cmon_zero V) w)).
  rewrite <- (rbl_add_l β (cmon_zero V) (cmon_zero V) w).
  rewrite (cmon_plus_zero_l V (cmon_zero V)).
  symmetry.
  apply (cmon_plus_zero_r W (rbl_map β (cmon_zero V) w)).
Qed.

(** v ⊗ 0 ≈ 0, dually. *)
Lemma rbl_zero_r (v : carrier (cmon_setoid V)) :
  rbl_map β v (cmon_zero V') ≈ cmon_zero W.
Proof.
  apply (ab_cancel_l W (rbl_map β v (cmon_zero V'))).
  rewrite <- (rbl_add_r β v (cmon_zero V') (cmon_zero V')).
  rewrite (cmon_plus_zero_l V' (cmon_zero V')).
  symmetry.
  apply (cmon_plus_zero_r W (rbl_map β v (cmon_zero V'))).
Qed.

(** 本节：(−v) ⊗ w ≈ −(v ⊗ w): left-hand side IS additive inverse of
 v ⊗ w, Instance/Ab.v's [ab_neg_unique] says enough. （已译） *)
Lemma rbl_neg_l (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  rbl_map β (ab_neg V v) w ≈ ab_neg W (rbl_map β v w).
Proof.
  apply ab_neg_unique.
  rewrite <- (rbl_add_l β (ab_neg V v) v w).
  rewrite (ab_neg_left V v).
  apply rbl_zero_l.
Qed.

Lemma rbl_neg_r (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  rbl_map β v (ab_neg V' w) ≈ ab_neg W (rbl_map β v w).
Proof.
  apply ab_neg_unique.
  rewrite <- (rbl_add_r β v (ab_neg V' w) w).
  rewrite (ab_neg_left V' w).
  apply rbl_zero_r.
Qed.

(*
   本节说明 Tensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma rbl_commutator (r s : carrier (rig_setoid (ring_rig R)))
  (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  rm_smul W (rig_mul (ring_rig R) r s) (rbl_map β v w)
    ≈ rm_smul W (rig_mul (ring_rig R) s r) (rbl_map β v w).
Proof.
  transitivity (rbl_map β (rm_smul V r v) (rm_smul V' s w)).
  - rewrite (rm_smul_assoc W r s (rbl_map β v w)).
    rewrite <- (rbl_smul_r β s v w).
    symmetry; apply (rbl_smul_l β r v (rm_smul V' s w)).
  - rewrite (rm_smul_assoc W s r (rbl_map β v w)).
    rewrite <- (rbl_smul_l β r v w).
    apply (rbl_smul_r β s (rm_smul V r v) w).
Qed.

(*
   本节说明 Tensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma rbl_commutator_annihilates (r s : carrier (rig_setoid (ring_rig R)))
  (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  rm_smul W (rig_add (ring_rig R) (rig_mul (ring_rig R) r s)
               (ring_neg R (rig_mul (ring_rig R) s r)))
    (rbl_map β v w)
    ≈ cmon_zero W.
Proof.
  rewrite (rm_smul_distr_r W _ _ (rbl_map β v w)).
  rewrite (rm_smul_neg_l W (rig_mul (ring_rig R) s r) (rbl_map β v w)).
  rewrite (rbl_commutator r s v w).
  apply (ab_neg_right W).
Qed.

End BilinearFacts.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma rbl_commutator_from_commutativity {R : RingObject}
  (Rcomm : ∀ a b, rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a)
  (W : RModObject R) (r s : carrier (rig_setoid (ring_rig R)))
  (x : carrier (cmon_setoid W)) :
  rm_smul W (rig_mul (ring_rig R) r s) x
    ≈ rm_smul W (rig_mul (ring_rig R) s r) x.
Proof.
  now rewrite (Rcomm r s).
Qed.

(*
   本节说明 Tensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Tensor.

Context {R : RingObject}.
Context (V V' : RModObject R).

Inductive MTerm : Type :=
  | mt_gen  : carrier (cmon_setoid V) → carrier (cmon_setoid V') → MTerm
  | mt_zero : MTerm
  | mt_plus : MTerm → MTerm → MTerm
  | mt_neg  : MTerm → MTerm
  | mt_smul : carrier (rig_setoid (ring_rig R)) → MTerm → MTerm.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Inductive mt_eq : MTerm → MTerm → Prop :=
  (* congruence *)
  | mte_gen {v v' : carrier (cmon_setoid V)} {w w' : carrier (cmon_setoid V')} :
      v ≈ v' → w ≈ w' → mt_eq (mt_gen v w) (mt_gen v' w')
  | mte_plus {s s' t t'} :
      mt_eq s s' → mt_eq t t' → mt_eq (mt_plus s t) (mt_plus s' t')
  | mte_neg {s s'} : mt_eq s s' → mt_eq (mt_neg s) (mt_neg s')
  | mte_smul {r r' : carrier (rig_setoid (ring_rig R))} {s s'} :
      r ≈ r' → mt_eq s s' → mt_eq (mt_smul r s) (mt_smul r' s')

  (* abelian group *)
  | mte_assoc (s t u : MTerm) :
      mt_eq (mt_plus (mt_plus s t) u) (mt_plus s (mt_plus t u))
  | mte_comm (s t : MTerm) : mt_eq (mt_plus s t) (mt_plus t s)
  | mte_zero_l (s : MTerm) : mt_eq (mt_plus mt_zero s) s
  | mte_neg_l (s : MTerm) : mt_eq (mt_plus (mt_neg s) s) mt_zero

  (* module *)
  | mte_smul_distr_l (r : carrier (rig_setoid (ring_rig R))) (s t : MTerm) :
      mt_eq (mt_smul r (mt_plus s t)) (mt_plus (mt_smul r s) (mt_smul r t))
  | mte_smul_distr_r (r r' : carrier (rig_setoid (ring_rig R))) (s : MTerm) :
      mt_eq (mt_smul (rig_add (ring_rig R) r r') s)
            (mt_plus (mt_smul r s) (mt_smul r' s))
  | mte_smul_assoc (r r' : carrier (rig_setoid (ring_rig R))) (s : MTerm) :
      mt_eq (mt_smul (rig_mul (ring_rig R) r r') s)
            (mt_smul r (mt_smul r' s))
  | mte_smul_one (s : MTerm) :
      mt_eq (mt_smul (rig_one (ring_rig R)) s) s

  (* bilinearity: additivity in each variable *)
  | mte_add_l (v v' : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
      mt_eq (mt_gen (cmon_plus V v v') w)
            (mt_plus (mt_gen v w) (mt_gen v' w))
  | mte_add_r (v : carrier (cmon_setoid V)) (w w' : carrier (cmon_setoid V')) :
      mt_eq (mt_gen v (cmon_plus V' w w'))
            (mt_plus (mt_gen v w) (mt_gen v w'))

  (* bilinearity: the scalar action, on each variable *)
  | mte_act_l (r : carrier (rig_setoid (ring_rig R)))
              (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
      mt_eq (mt_smul r (mt_gen v w)) (mt_gen (rm_smul V r v) w)
  | mte_act_r (r : carrier (rig_setoid (ring_rig R)))
              (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
      mt_eq (mt_smul r (mt_gen v w)) (mt_gen v (rm_smul V' r w))

  | mte_sym {s t} : mt_eq s t → mt_eq t s
  | mte_trans {s t u} : mt_eq s t → mt_eq t u → mt_eq s u.

Lemma mt_refl (s : MTerm) : mt_eq s s.
Proof.
  induction s.
  - exact (mte_gen (reflexivity _) (reflexivity _)).
  - exact (mte_trans (mte_sym (mte_zero_l mt_zero)) (mte_zero_l mt_zero)).
  - exact (mte_plus IHs1 IHs2).
  - exact (mte_neg IHs).
  - exact (mte_smul (reflexivity _) IHs).
Qed.

Lemma mt_eq_Equivalence : Equivalence mt_eq.
Proof.
  constructor.
  - exact mt_refl.
  - exact (fun s t => mte_sym).
  - exact (fun s t u => mte_trans).
Qed.

Definition mt_Setoid : Setoid MTerm := {|
  equiv        := mt_eq;
  setoid_equiv := mt_eq_Equivalence
|}.

(*
   本节说明 Tensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition TensorMod : RModObject R := {|
  rm_ab := {|
    ab_cmon := {|
      cmon_setoid := {| carrier := MTerm; is_setoid := mt_Setoid |};
      cmon_zero := mt_zero;
      cmon_plus := mt_plus;
      cmon_plus_respects := fun _ _ Hs _ _ Ht => mte_plus Hs Ht;
      cmon_plus_assoc := mte_assoc;
      cmon_plus_comm := mte_comm;
      cmon_plus_zero_l := mte_zero_l;
      (* [mt_eq] IS a [Prop] relation, so it is its own [Prop] mirror. *)
      cmon_prop := @PropEquiv_of_relation _ mt_Setoid mt_eq
                     (fun _ _ h => h) (fun _ _ h => h)
    |};
    ab_neg := mt_neg;
    ab_neg_respects := fun _ _ Hs => mte_neg Hs;
    ab_neg_left := mte_neg_l
  |};
  rm_smul          := mt_smul;
  rm_smul_respects := fun _ _ Hr _ _ Hs => mte_smul Hr Hs;
  rm_smul_distr_l  := mte_smul_distr_l;
  rm_smul_distr_r  := mte_smul_distr_r;
  rm_smul_assoc    := mte_smul_assoc;
  rm_smul_one      := mte_smul_one
|}.

(*
   本节说明 Tensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition tensor_gen : RBilinear V V' TensorMod :=
  @Build_RBilinear R V V' TensorMod mt_gen
    (fun _ _ Hv _ _ Hw => mte_gen Hv Hw)
    mte_add_l
    mte_add_r
    (fun r v w => mte_sym (mte_act_l r v w))
    (fun r v w => mte_sym (mte_act_r r v w)).

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma tensor_balanced (r : carrier (rig_setoid (ring_rig R)))
  (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  mt_eq (mt_gen (rm_smul V r v) w) (mt_gen v (rm_smul V' r w)).
Proof.
  exact (mte_trans (mte_sym (mte_act_l r v w)) (mte_act_r r v w)).
Qed.

(** 本节：The elementary consequences bilinearity, at canonical map. （已译） *)
Lemma tensor_zero_l (w : carrier (cmon_setoid V')) :
  mt_eq (mt_gen (cmon_zero V) w) mt_zero.
Proof. exact (rbl_zero_l tensor_gen w). Qed.

Lemma tensor_zero_r (v : carrier (cmon_setoid V)) :
  mt_eq (mt_gen v (cmon_zero V')) mt_zero.
Proof. exact (rbl_zero_r tensor_gen v). Qed.

Lemma tensor_neg_l (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  mt_eq (mt_gen (ab_neg V v) w) (mt_neg (mt_gen v w)).
Proof. exact (rbl_neg_l tensor_gen v w). Qed.

Lemma tensor_neg_r (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  mt_eq (mt_gen v (ab_neg V' w)) (mt_neg (mt_gen v w)).
Proof. exact (rbl_neg_r tensor_gen v w). Qed.

(*
   本节说明 Tensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma tensor_commutator (r s : carrier (rig_setoid (ring_rig R)))
  (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  mt_eq (mt_smul (rig_mul (ring_rig R) r s) (mt_gen v w))
        (mt_smul (rig_mul (ring_rig R) s r) (mt_gen v w)).
Proof. exact (rbl_commutator tensor_gen r s v w). Qed.

End Tensor.

Arguments MTerm {R} V V'.
Arguments mt_gen {R V V'} v w.
Arguments mt_zero {R V V'}.
Arguments mt_plus {R V V'} s t.
Arguments mt_neg {R V V'} s.
Arguments mt_smul {R V V'} r s.
Arguments mt_eq {R V V'} s t.
Arguments mt_refl {R V V'} s.
Arguments mte_gen {R V V' v v' w w'} _ _.
Arguments mte_plus {R V V' s s' t t'} _ _.
Arguments mte_neg {R V V' s s'} _.
Arguments mte_smul {R V V' r r' s s'} _ _.
Arguments mte_assoc {R V V'} s t u.
Arguments mte_comm {R V V'} s t.
Arguments mte_zero_l {R V V'} s.
Arguments mte_neg_l {R V V'} s.
Arguments mte_smul_distr_l {R V V'} r s t.
Arguments mte_smul_distr_r {R V V'} r r' s.
Arguments mte_smul_assoc {R V V'} r r' s.
Arguments mte_smul_one {R V V'} s.
Arguments mte_add_l {R V V'} v v' w.
Arguments mte_add_r {R V V'} v w w'.
Arguments mte_act_l {R V V'} r v w.
Arguments mte_act_r {R V V'} r v w.
Arguments mte_sym {R V V' s t} _.
Arguments mte_trans {R V V' s t u} _ _.
Arguments TensorMod {R} V V'.
Arguments tensor_gen {R V V'}.
Arguments tensor_balanced {R V V'} r v w.
Arguments tensor_zero_l {R V V'} w.
Arguments tensor_zero_r {R V V'} v.
Arguments tensor_neg_l {R V V'} v w.
Arguments tensor_neg_r {R V V'} v w.
Arguments tensor_commutator {R V V'} r s v w.

(** ** The factorization *)

Section Mediator.

Context {R : RingObject}.
Context {V V' : RModObject R}.
Context {W : RModObject R}.
Context (β : RBilinear V V' W).

(*
   本节说明 Tensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fixpoint tensor_med_fun (t : MTerm V V') : carrier (cmon_setoid W) :=
  match t with
  | mt_gen v w  => rbl_map β v w
  | mt_zero     => cmon_zero W
  | mt_plus s t => cmon_plus W (tensor_med_fun s) (tensor_med_fun t)
  | mt_neg s    => ab_neg W (tensor_med_fun s)
  | mt_smul r s => rm_smul W r (tensor_med_fun s)
  end.

(*
   本节说明 Tensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma tensor_med_respects (s t : MTerm V V') :
  mt_eq s t → tensor_med_fun s ≈ tensor_med_fun t.
Proof.
  intro He.
  (*
   本节说明 Tensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  apply pequiv_to.
  induction He as
    [ v v' w w' Hv Hw
    | s s' t t' _ IH1 _ IH2
    | s s' _ IH
    | r r' s s' Hr _ IH
    | s t u | s t | s | s
    | r s t | r r' s | r r' s | s
    | v v' w | v w w'
    | r v w | r v w
    | s t _ IH
    | s t u _ IH1 _ IH2 ]; simpl.
  - apply pequiv_from; exact (rbl_respects β _ _ Hv _ _ Hw).
  - apply pequiv_from.
    exact (cmon_plus_respects W _ _ (pequiv_to _ _ IH1)
                                _ _ (pequiv_to _ _ IH2)).
  - apply pequiv_from.
    exact (ab_neg_respects W _ _ (pequiv_to _ _ IH)).
  - apply pequiv_from.
    exact (rm_smul_respects W _ _ Hr _ _ (pequiv_to _ _ IH)).
  - apply pequiv_from; exact (cmon_plus_assoc W _ _ _).
  - apply pequiv_from; exact (cmon_plus_comm W _ _).
  - apply pequiv_from; exact (cmon_plus_zero_l W _).
  - apply pequiv_from; exact (ab_neg_left W _).
  - apply pequiv_from; exact (rm_smul_distr_l W _ _ _).
  - apply pequiv_from; exact (rm_smul_distr_r W _ _ _).
  - apply pequiv_from; exact (rm_smul_assoc W _ _ _).
  - apply pequiv_from; exact (rm_smul_one W _).
  - apply pequiv_from; exact (rbl_add_l β _ _ _).
  - apply pequiv_from; exact (rbl_add_r β _ _ _).
  - apply pequiv_from; exact (symmetry (rbl_smul_l β _ _ _)).
  - apply pequiv_from; exact (symmetry (rbl_smul_r β _ _ _)).
  - exact (symmetry IH).
  - exact (transitivity IH1 IH2).
Qed.

(*
   本节说明 Tensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition tensor_med : TensorMod V V' ~{RMod R}~> W := {|
  rm_hom := {| cmon_map := {| morphism := tensor_med_fun |} |}
|}.
Next Obligation.
  first [ (intros s t He; exact (tensor_med_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (tensor_med_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (tensor_med_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (tensor_med_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.

(* It agrees with β on generators — definitionally, not up to [≈]. *)
Example tensor_med_gen (v : carrier (cmon_setoid V))
  (w : carrier (cmon_setoid V')) :
  cmon_map (rm_hom tensor_med) (mt_gen v w) = rbl_map β v w := eq_refl.

End Mediator.

Arguments tensor_med_fun {R V V' W} β t.
Arguments tensor_med {R V V' W} β.

(*
   本节说明 Tensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma tensor_hom_ext {R : RingObject} {V V' W : RModObject R}
  (f g : TensorMod V V' ~{RMod R}~> W) :
  (∀ (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')),
      cmon_map (rm_hom f) (mt_gen v w) ≈ cmon_map (rm_hom g) (mt_gen v w)) →
  ∀ t : MTerm V V', cmon_map (rm_hom f) t ≈ cmon_map (rm_hom g) t.
Proof.
  intros Hgen t; induction t.
  - exact (Hgen c c0).
  - exact (transitivity (cmon_map_zero (rm_hom f))
             (symmetry (cmon_map_zero (rm_hom g)))).
  - refine (transitivity (cmon_map_plus (rm_hom f) t1 t2) _).
    refine (transitivity _ (symmetry (cmon_map_plus (rm_hom g) t1 t2))).
    exact (cmon_plus_respects W _ _ IHt1 _ _ IHt2).
  - refine (transitivity (ab_map_neg (rm_hom f) t) _).
    refine (transitivity _ (symmetry (ab_map_neg (rm_hom g) t))).
    exact (ab_neg_respects W _ _ IHt).
  - refine (transitivity (rm_map_smul f c t) _).
    refine (transitivity _ (symmetry (rm_map_smul g c t))).
    exact (rm_smul_respects W _ _ (reflexivity c) _ _ IHt).
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section BilinFunctor.

Context {R : RingObject}.
Context (V V' : RModObject R).

Program Definition RBilinear_Setoid (W : RModObject R) :
  Setoid (RBilinear V V' W) := {|
  equiv := fun β γ => ∀ v w, rbl_map β v w ≈ rbl_map γ v w
|}.
Next Obligation.
  intros W.
  constructor.
  - intros β v w; reflexivity.
  - intros β γ Hβγ v w; symmetry; apply Hβγ.
  - intros β γ δ H1 H2 v w.
    transitivity (rbl_map γ v w); [ apply H1 | apply H2 ].
Qed.

Definition Bilin_obj (W : RModObject R) : SetoidObject := {|
  carrier   := RBilinear V V' W;
  is_setoid := RBilinear_Setoid W
|}.

(* Postcomposition with a module homomorphism. *)
Program Definition Bilin_post {W W' : RModObject R} (f : W ~{RMod R}~> W')
  (β : RBilinear V V' W) : RBilinear V V' W' := {|
  rbl_map := fun v w => cmon_map (rm_hom f) (rbl_map β v w)
|}.
Next Obligation.
  intros W W' f β v v0 Hv w w0 Hw; simpl.
  now rewrite Hv, Hw.
Qed.
Next Obligation.
  intros W W' f β v v0 w; simpl.
  rewrite (rbl_add_l β v v0 w).
  apply (cmon_map_plus (rm_hom f)).
Qed.
Next Obligation.
  intros W W' f β v w w0; simpl.
  rewrite (rbl_add_r β v w w0).
  apply (cmon_map_plus (rm_hom f)).
Qed.
Next Obligation.
  intros W W' f β r v w; simpl.
  rewrite (rbl_smul_l β r v w).
  apply (rm_map_smul f r (rbl_map β v w)).
Qed.
Next Obligation.
  intros W W' f β r v w; simpl.
  rewrite (rbl_smul_r β r v w).
  apply (rm_map_smul f r (rbl_map β v w)).
Qed.

Program Definition Bilin : RMod R ⟶ Sets := {|
  fobj := Bilin_obj;
  fmap := fun W W' f => {| morphism := Bilin_post f |}
|}.
Next Obligation.
  intros W W' f β γ Hβγ v w; simpl.
  now rewrite (Hβγ v w).
Qed.
Next Obligation.
  intros W W' f g Hfg β v w; simpl.
  exact (Hfg (rbl_map β v w)).
Qed.
Next Obligation.
  intros W β v w; simpl; reflexivity.
Qed.
Next Obligation.
  intros W W' W'' f g β v w; simpl; reflexivity.
Qed.

(*
   本节说明 Tensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition tensor_universal_element :
  AUniversalElement Bilin (TensorMod V V') := {|
  aue_elem      := tensor_gen;
  aue_universal := fun W β => {| unique_obj := tensor_med β |}
|}.
Next Obligation.
  intros W β v w; simpl; reflexivity.
Qed.
Next Obligation.
  intros W β k Hk t.
  apply (tensor_hom_ext (tensor_med β) k).
  intros v w.
  exact (symmetry (Hk v w)).
Qed.

(* Mac Lane's pair ⟨r, e⟩, same data 对象 field. （已译） *)
Definition tensor_UniversalElement : UniversalElement Bilin :=
  UniversalElement_of_AUniversalElement tensor_universal_element.

(* The 表示 对象 tensor, [eq_refl]. （已译） *)
Example tensor_UniversalElement_obj :
  @ue_obj (RMod R) Bilin tensor_UniversalElement = TensorMod V V' := eq_refl.

(*
   本节说明 Tensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition tensor_factor {W : RModObject R} (β : RBilinear V V' W) :
  TensorMod V V' ~{RMod R}~> W :=
  unique_obj (@aue_universal (RMod R) Bilin (TensorMod V V')
                tensor_universal_element W β).

Example tensor_factor_is_med {W : RModObject R} (β : RBilinear V V' W) :
  tensor_factor β = tensor_med β := eq_refl.

Lemma tensor_factor_commutes {W : RModObject R} (β : RBilinear V V' W)
  (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  cmon_map (rm_hom (tensor_factor β)) (mt_gen v w) ≈ rbl_map β v w.
Proof.
  exact (unique_property (@aue_universal (RMod R) Bilin (TensorMod V V')
                            tensor_universal_element W β) v w).
Qed.

Lemma tensor_factor_unique {W : RModObject R} (β : RBilinear V V' W)
  (k : TensorMod V V' ~{RMod R}~> W) :
  (∀ (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')),
      cmon_map (rm_hom k) (mt_gen v w) ≈ rbl_map β v w) →
  tensor_factor β ≈ k.
Proof.
  intro Hk.
  exact (uniqueness (@aue_universal (RMod R) Bilin (TensorMod V V')
                       tensor_universal_element W β) k Hk).
Qed.

End BilinFunctor.

Arguments RBilinear_Setoid {R} V V' W.
Arguments Bilin_obj {R} V V' W.
Arguments Bilin_post {R} V V' {W W'} f β.
Arguments Bilin {R} V V'.
Arguments tensor_universal_element {R} V V'.
Arguments tensor_UniversalElement {R} V V'.
Arguments tensor_factor {R V V' W} β.
Arguments tensor_factor_commutes {R V V' W} β v w.
Arguments tensor_factor_unique {R V V' W} β k _.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Tensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Int_mul_bilinear : RBilinear Int_RMod Int_RMod Int_RMod.
Proof.
  unshelve notypeclasses refine
    (@Build_RBilinear Int_Ring Int_RMod Int_RMod Int_RMod Z.mul _ _ _ _ _).
  - (* rbl_respects *)
    intros a b Hab c d Hcd; simpl in *; unfold Rig.Z_eqT in *; now subst.
  - (* rbl_add_l *)
    intros v v' w; simpl; unfold Rig.Z_eqT; ring.
  - (* rbl_add_r *)
    intros v w w'; simpl; unfold Rig.Z_eqT; ring.
  - (* rbl_smul_l *)
    intros r v w; simpl; unfold Rig.Z_eqT; ring.
  - (* 相关说明。 （已译） *)
    intros r v w; simpl; unfold Rig.Z_eqT; ring.
Defined.

(* 相关说明。 （已译） *)
Local Notation zgen  := (@mt_gen Int_Ring Int_RMod Int_RMod).
Local Notation zzero := (@mt_zero Int_Ring Int_RMod Int_RMod).
Local Notation zplus := (@mt_plus Int_Ring Int_RMod Int_RMod).
Local Notation zneg  := (@mt_neg Int_Ring Int_RMod Int_RMod).
Local Notation zsmul := (@mt_smul Int_Ring Int_RMod Int_RMod).

(* 相关说明。 （已译） *)
Example int_tensor_med_computes :
  cmon_map (rm_hom (tensor_med Int_mul_bilinear)) (zgen 2%Z 3%Z) = 6%Z
  := eq_refl.

Example int_tensor_factor_computes :
  cmon_map (rm_hom (tensor_factor Int_mul_bilinear)) (zgen 2%Z 3%Z) = 6%Z
  := eq_refl.

(* 相关说明。 （已译） *)
Example int_tensor_med_computes_sum :
  cmon_map (rm_hom (tensor_med Int_mul_bilinear))
    (zplus (zsmul 5%Z (zgen 2%Z 3%Z)) (zneg (zgen 4%Z 1%Z)))
  = 26%Z := eq_refl.

(* * The quotient does not collapse.  Both statements are proved by
    mapping OUT through [tensor_med_respects]: an inhabitant of [mt_eq]
    would give an equation in ℤ that [discriminate] refutes.（标题）（已译） *)
Lemma int_tensor_gen_nonzero : mt_eq (zgen 1%Z 1%Z) zzero → False.
Proof.
  intro He.
  pose proof (tensor_med_respects Int_mul_bilinear _ _ He) as Hz.
  simpl in Hz; unfold Rig.Z_eqT in Hz.
  discriminate Hz.
Qed.

Lemma int_tensor_gen_distinct :
  mt_eq (zgen 1%Z 1%Z) (zgen 2%Z 1%Z) → False.
Proof.
  intro He.
  pose proof (tensor_med_respects Int_mul_bilinear _ _ He) as Hz.
  simpl in Hz; unfold Rig.Z_eqT in Hz.
  discriminate Hz.
Qed.

(*
   本节说明 Tensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明 Tensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition int_tensor_unit :
  Int_RMod ~{RMod Int_Ring}~> TensorMod Int_RMod Int_RMod := {|
  rm_hom := {| cmon_map := {|
    morphism        := fun n => zgen n 1%Z;
    proper_morphism := fun a b Hab => mte_gen Hab (reflexivity 1%Z) |} |}
|}.
Next Obligation.
  exact (@tensor_zero_l Int_Ring Int_RMod Int_RMod 1%Z).
Qed.
Next Obligation.
  intros a b; exact (@mte_add_l Int_Ring Int_RMod Int_RMod a b 1%Z).
Qed.
Next Obligation.
  intros r n; exact (mte_sym (@mte_act_l Int_Ring Int_RMod Int_RMod r n 1%Z)).
Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Int_tensor_iso :
  @Isomorphism (RMod Int_Ring) (TensorMod Int_RMod Int_RMod) Int_RMod := {|
  to   := tensor_med Int_mul_bilinear;
  from := int_tensor_unit
|}.
Next Obligation.
  intro n; simpl; unfold Rig.Z_eqT; apply Z.mul_1_r.
Qed.
Next Obligation.
  refine (tensor_hom_ext
            (int_tensor_unit ∘ tensor_med Int_mul_bilinear)
            (@id (RMod Int_Ring) (TensorMod Int_RMod Int_RMod)) _).
  intros v w; simpl.
  (* 相关说明。 （已译） *)
  refine (mte_trans (@mte_gen Int_Ring Int_RMod Int_RMod _ _ _ _
                       (Z.mul_comm v w) (reflexivity 1%Z)) _).
  refine (mte_trans (mte_sym (@mte_act_l Int_Ring Int_RMod Int_RMod w v 1%Z)) _).
  refine (mte_trans (@mte_act_r Int_Ring Int_RMod Int_RMod w v 1%Z) _).
  exact (@mte_gen Int_Ring Int_RMod Int_RMod _ _ _ _
           (reflexivity v) (Z.mul_1_r w)).
Qed.
