Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Rng.
Require Import Category.Instance.FdVect.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/field
 Wikipedia: https://en.wikipedia.org/wiki/Field_(mathematics)

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

(** ** The category *)

(*
   本节说明hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Field : Category := {|
  obj     := FieldObject;
  hom     := fun F K => RigHom F K;
  homset  := fun F K => @RigHom_Setoid F K;
  id      := fun F => @rig_hom_id F;
  compose := fun _ _ _ f g => rig_hom_compose f g;

  compose_respects := fun _ _ _ => @rig_hom_compose_respects _ _ _
|}.
Next Obligation. intros x y f a; simpl; reflexivity. Qed.
Next Obligation. intros x y f a; simpl; reflexivity. Qed.
Next Obligation. intros x y z w f g h a; simpl; reflexivity. Qed.
Next Obligation. intros x y z w f g h a; simpl; reflexivity. Qed.

(* * ** The evident forgetful 函子 （已译） *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Field_Rng : Field ⟶ Rng := {|
  fobj := fun F : FieldObject => field_ring F;
  fmap := fun _ _ f => f
|}.
Next Obligation. intros F K f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros F a; simpl; reflexivity. Qed.
Next Obligation. intros F K T f g a; simpl; reflexivity. Qed.

#[export] Instance Field_Rng_Faithful : Faithful Field_Rng.
Proof. constructor; intros F K f g E; exact E. Qed.

(* To setoids: the underlying set, Mac Lane's roster column. *)
Program Definition Field_Forget : Field ⟶ Sets := {|
  fobj := fun F : FieldObject => rig_setoid F;
  fmap := fun F K f => rig_map f
|}.
Next Obligation. intros F K f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros F a; simpl; reflexivity. Qed.
Next Obligation. intros F K T f g a; simpl; reflexivity. Qed.

#[export] Instance Field_Forget_Faithful : Faithful Field_Forget.
Proof. constructor; intros F K f g E; exact E. Qed.

(* 相关说明。 （已译） *)

(*
   本节说明 Field 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma field_hom_nonzero {F K : FieldObject} (f : RigHom F K)
  (x : carrier (rig_setoid F)) :
  (x ≈ rig_zero F → False) → (rig_map f x ≈ rig_zero K → False).
Proof.
  intros Hx Hfx.
  apply (field_one_neq_zero K).
  transitivity (rig_map f (rig_one F)).
  - symmetry; apply (rig_map_one f).
  - transitivity (rig_map f (rig_mul F (finv F x) x)).
    + apply (proper_morphism (rig_map f)).
      symmetry; now apply finv_l.
    + rewrite (rig_map_mul f).
      rewrite Hfx.
      apply rig_mul_zero_r.
Qed.

(*
   本节说明 Field 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma field_hom_finv {F K : FieldObject} (f : RigHom F K)
  (x : carrier (rig_setoid F)) (Hx : x ≈ rig_zero F → False) :
  rig_map f (finv F x) ≈ finv K (rig_map f x).
Proof.
  apply (rig_inv_unique K (rig_map f x)).
  - rewrite <- (rig_map_mul f).
    transitivity (rig_map f (rig_one F)).
    + apply (proper_morphism (rig_map f)); now apply finv_l.
    + apply (rig_map_one f).
  - apply finv_r.
    now apply (field_hom_nonzero f x Hx).
Qed.

(* 相关说明。 （已译） *)

(* A difference vanishing forces two elements agree — pure ring
 arithmetic, isolated so field 论元 below reads cleanly. （已译） *)
Lemma ring_sub_zero (R : RingObject) (a b : carrier (rig_setoid R)) :
  rig_add R a (ring_neg R b) ≈ rig_zero R → a ≈ b.
Proof.
  intro H.
  transitivity (rig_add R (rig_add R a (ring_neg R b)) b).
  - rewrite rig_add_assoc.
    rewrite (ring_neg_l R b).
    symmetry; apply rig_add_zero_r.
  - rewrite H.
    apply rig_add_zero_l.
Qed.

(* 相关说明。 （已译） *)
Lemma ring_zero_sub (R : RingObject) (a b : carrier (rig_setoid R)) :
  a ≈ b → rig_add R a (ring_neg R b) ≈ rig_zero R.
Proof.
  intro H.
  rewrite H.
  rewrite rig_add_comm.
  apply ring_neg_l.
Qed.

(* 相关说明。 （已译） *)
Lemma field_hom_sub_zero {F K : FieldObject} (f : RigHom F K)
  (a b : carrier (rig_setoid F)) :
  rig_map f a ≈ rig_map f b →
  rig_map f (rig_add F a (ring_neg F b)) ≈ rig_zero K.
Proof.
  intro Hab.
  rewrite (rig_map_add f).
  rewrite (RigHom_neg F K f b).
  rewrite Hab.
  rewrite rig_add_comm.
  apply (ring_neg_l K (rig_map f b)).
Qed.

(*
   本节说明 Field 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem field_hom_distinct {F K : FieldObject} (f : RigHom F K)
  (a b : carrier (rig_setoid F)) :
  (a ≈ b → False) → (rig_map f a ≈ rig_map f b → False).
Proof.
  intros Hne Hab.
  (* the difference is nonzero, since a vanishing difference gives a ≈ b *)
  assert (Hd : rig_add F a (ring_neg F b) ≈ rig_zero F → False).
  { intro H; apply Hne; exact (ring_sub_zero F a b H). }
  (* yet its image vanishes *)
  exact (field_hom_nonzero f _ Hd (field_hom_sub_zero f a b Hab)).
Qed.

(* 相关说明。 （已译） *)
Corollary field_hom_injective_nn {F K : FieldObject} (f : RigHom F K)
  (a b : carrier (rig_setoid F)) :
  rig_map f a ≈ rig_map f b → ((a ≈ b → False) → False).
Proof.
  intros Hab Hne.
  exact (field_hom_distinct f a b Hne Hab).
Qed.

(* * ** The named 假设, it exactly missing step （已译） *)

(* 相关说明。 （已译） *)
Definition FieldStable (F : FieldObject) : Type :=
  ∀ a b : carrier (rig_setoid F), ((a ≈ b → False) → False) → a ≈ b.

Lemma field_dec_stable (F : FieldObject)
  (dec : ∀ a b : carrier (rig_setoid F), (a ≈ b) + (a ≈ b → False)) :
  FieldStable F.
Proof.
  intros a b Hnn.
  destruct (dec a b) as [H | H].
  - exact H.
  - destruct (Hnn H).
Qed.

(*
   本节说明 Field 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem stability_is_the_conclusion {F K : FieldObject} (f : RigHom F K)
  (a b : carrier (rig_setoid F)) (Hab : rig_map f a ≈ rig_map f b) :
  ((((a ≈ b → False) → False) → a ≈ b) → a ≈ b) *
  ((a ≈ b) → (((a ≈ b → False) → False) → a ≈ b)).
Proof.
  split.
  - intro Hstab.
    apply Hstab.
    exact (field_hom_injective_nn f a b Hab).
  - intros H _; exact H.
Qed.

(* * ** The 假设 ever used at zero （已译） *)

(*
   本节说明 Field 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition FieldStableAtZero (F : FieldObject) : Type :=
  ∀ a : carrier (rig_setoid F),
    ((a ≈ rig_zero F → False) → False) → a ≈ rig_zero F.

Definition field_stable_stable_at_zero (F : FieldObject) :
  FieldStable F → FieldStableAtZero F :=
  fun HF a => HF a (rig_zero F).

Lemma field_stable_at_zero_stable (F : FieldObject) :
  FieldStableAtZero F → FieldStable F.
Proof.
  intros HF a b Hnn.
  apply (ring_sub_zero F a b).
  apply HF.
  intro Hd.
  apply Hnn.
  intro Hab.
  exact (Hd (ring_zero_sub F a b Hab)).
Qed.

(* 相关说明。 （已译） *)
Theorem field_stable_at_zero_suffices {F K : FieldObject} (f : RigHom F K)
  (HF : FieldStableAtZero F) (a b : carrier (rig_setoid F)) :
  rig_map f a ≈ rig_map f b → a ≈ b.
Proof.
  intro Hab.
  apply (ring_sub_zero F a b).
  apply HF.
  intro Hd.
  exact (field_hom_nonzero f _ Hd (field_hom_sub_zero f a b Hab)).
Qed.

(* 相关说明。 （已译） *)

Theorem field_hom_injective {F K : FieldObject} (f : RigHom F K)
  (HF : FieldStable F) (a b : carrier (rig_setoid F)) :
  rig_map f a ≈ rig_map f b → a ≈ b.
Proof.
  intro Hab.
  apply HF.
  exact (field_hom_injective_nn f a b Hab).
Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem field_monic {F K : FieldObject} (f : F ~{Field}~> K)
  (HF : FieldStable F) : Monic f.
Proof.
  constructor; intros T g1 g2 Hg a.
  exact (field_hom_injective f HF (rig_map g1 a) (rig_map g2 a) (Hg a)).
Qed.

(* Riehl's blanket statement, with its hypothesis in view. *)
Theorem field_every_monic :
  (∀ F : FieldObject, FieldStable F) →
  ∀ (F K : FieldObject) (f : F ~{Field}~> K), Monic f.
Proof.
  intros Hstab F K f.
  exact (field_monic f (Hstab F)).
Qed.

(** ** ℚ: the witness *)

(* [Qeq] decidable, so ℚ's equality stable every homomorphism
 out ℚ monic no 假设 whatsoever. （已译） *)
Lemma Q_Field_dec (a b : carrier (rig_setoid Q_Field)) :
  (a ≈ b) + (a ≈ b → False).
Proof.
  destruct (Qeq_dec a b) as [H | H].
  - left; exact H.
  - right; exact H.
Qed.

Definition Q_Field_stable : FieldStable Q_Field :=
  field_dec_stable Q_Field Q_Field_dec.

Theorem Q_hom_monic (K : FieldObject) (f : Q_Field ~{Field}~> K) : Monic f.
Proof. exact (field_monic f Q_Field_stable). Qed.

(*
   本节说明 Field 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example Q_Field_object : obj[Field] := Q_Field.

Example Q_Field_id : Q_Field ~{Field}~> Q_Field := @id Field Q_Field.

Example Q_Field_id_monic : Monic (@id Field Q_Field) := Q_hom_monic _ _.

(** ** ℚ is rigid *)

(* 相关说明。 （已译） *)
Lemma Q_den_nonzero (q : Q) : ~ (inject_Z (Z.pos (Qden q)) == 0)%Q.
Proof. unfold Qeq, inject_Z; simpl; discriminate. Qed.

Lemma Q_cancel_r (x y b : Q) :
  ~ (b == 0)%Q → (x * b == y * b)%Q → (x == y)%Q.
Proof.
  intros Hb H.
  rewrite <- (Qmult_1_r x), <- (Qmult_1_r y).
  rewrite <- (Qmult_inv_r b Hb).
  rewrite (Qmult_assoc x b (/ b)), (Qmult_assoc y b (/ b)).
  now rewrite H.
Qed.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Q_endo_id (f : Q_Field ~{Field}~> Q_Field) (q : Q) :
  (rig_map f q == q)%Q.
Proof.
  (* f respects Qeq, and preserves products — both by conversion *)
  assert (Hresp : ∀ x y : Q, (x == y)%Q → (rig_map f x == rig_map f y)%Q).
  { intros x y H; exact (proper_morphism (rig_map f) x y H). }
  assert (Hmul : ∀ x y : Q,
             (rig_map f (x * y) == rig_map f x * rig_map f y)%Q).
  { intros x y; exact (rig_map_mul f x y). }
  (* f fixes every integer, by initiality of ℤ used on both sides *)
  assert (Hz : ∀ z : Z, (rig_map f (inject_Z z) == inject_Z z)%Q).
  { intro z.
    transitivity (zring Q_Ring z).
    - exact (rng_from_Z_unique Q_Ring (rig_hom_compose f ZtoQ) z).
    - symmetry; exact (rng_from_Z_unique Q_Ring ZtoQ z). }
  (* 相关说明。 （已译） *)
  apply (Q_cancel_r _ _ (inject_Z (Z.pos (Qden q))) (Q_den_nonzero q)).
  transitivity (rig_map f (q * inject_Z (Z.pos (Qden q)))%Q).
  - rewrite Hmul.
    now rewrite (Hz (Z.pos (Qden q))).
  - transitivity (inject_Z (Qnum q)).
    + transitivity (rig_map f (inject_Z (Qnum q))).
      * apply Hresp, Q_num_den.
      * apply Hz.
    + symmetry; apply Q_num_den.
Qed.

(* ...hence 恒等 endomorphism, hom-setoid. （已译） *)
Corollary Q_endo_unique (f : Q_Field ~{Field}~> Q_Field) :
  f ≈ @id Field Q_Field.
Proof. intro q; exact (Q_endo_id f q). Qed.

(* * ** F₂: second 对象, second characteristic （已译） *)

(*
   本节说明 Field 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition F2_Rig : RigObject := {|
  rig_setoid := bool_setoid_object;
  rig_zero := false;
  rig_add := xorb;
  rig_one := true;
  rig_mul := andb;

  (* [bool_setoid_object]'s `≈` IS [eq]: two 蕴含 the
 恒等. See Lib/Setoid/Propositional.v why 关系 must be
 named rather than ascribed. （已译） *)
  rig_prop := @PropEquiv_of_relation _ (is_setoid bool_setoid_object) (@eq bool)
                (fun _ _ h => h) (fun _ _ h => h)
|}.
Next Obligation. intros [|] [|] [|]; reflexivity. Qed.
Next Obligation. intros [|] [|]; reflexivity. Qed.
Next Obligation. intros [|]; reflexivity. Qed.
Next Obligation. intros [|] [|] [|]; reflexivity. Qed.
Next Obligation. intros [|]; reflexivity. Qed.
Next Obligation. intros [|]; reflexivity. Qed.
Next Obligation. intros [|] [|] [|]; reflexivity. Qed.
Next Obligation. intros [|] [|] [|]; reflexivity. Qed.
Next Obligation. intros [|]; reflexivity. Qed.
Next Obligation. intros [|]; reflexivity. Qed.

Program Definition F2_Ring : RingObject := {|
  ring_rig := F2_Rig;
  ring_neg := fun b => b
|}.
Next Obligation. intros [|]; reflexivity. Qed.

Program Definition F2_Field : FieldObject := {|
  field_ring := F2_Ring;
  finv := fun b => b
|}.
Next Obligation. intros [|] [|]; reflexivity. Qed.
Next Obligation. discriminate. Qed.
Next Obligation.
  (* 相关说明。 （已译） *)
  intros [|] Hx; [ reflexivity | destruct (Hx eq_refl) ].
Qed.

(* Leibniz equality [bool] decidable, so F₂ stable every
 homomorphism out it monic no 假设. （已译） *)
Lemma F2_Field_dec (a b : carrier (rig_setoid F2_Field)) :
  (a ≈ b) + (a ≈ b → False).
Proof.
  destruct a, b;
    solve [ left; reflexivity | right; discriminate ].
Qed.

Definition F2_Field_stable : FieldStable F2_Field :=
  field_dec_stable F2_Field F2_Field_dec.

Theorem F2_hom_monic (K : FieldObject) (f : F2_Field ~{Field}~> K) :
  Monic f.
Proof. exact (field_monic f F2_Field_stable). Qed.

(* 相关说明。 （已译） *)

(* 1 + 1 in an arbitrary field.  Named because both non-existence
   theorems below run through it: it is zero in F₂ and nonzero in ℚ,
   and a homomorphism must carry it to the corresponding element. *)
Definition ftwo (F : FieldObject) : carrier (rig_setoid F) :=
  rig_add F (rig_one F) (rig_one F).

Lemma ftwo_map {F K : FieldObject} (f : RigHom F K) :
  rig_map f (ftwo F) ≈ ftwo K.
Proof.
  unfold ftwo.
  rewrite (rig_map_add f).
  now rewrite (rig_map_one f).
Qed.

(* 相关说明。 （已译） *)
Lemma Q_ftwo_nonzero : ftwo Q_Field ≈ rig_zero Q_Field → False.
Proof.
  intro H.
  assert (Hq : (2 # 1 == 0)%Q) by exact H.
  unfold Qeq in Hq; simpl in Hq; discriminate Hq.
Qed.

(* In F₂, 2 ≈ 0 — and definitionally so, since [xorb true true] computes
   to [false]. *)
Lemma F2_ftwo_zero : ftwo F2_Field ≈ rig_zero F2_Field.
Proof. reflexivity. Qed.

(* 相关说明。 （已译） *)
Theorem no_hom_Q_F2 (f : Q_Field ~{Field}~> F2_Field) : False.
Proof.
  apply (field_hom_nonzero f (ftwo Q_Field) Q_ftwo_nonzero).
  rewrite (ftwo_map f).
  exact F2_ftwo_zero.
Qed.

(* 相关说明。 （已译） *)
Theorem no_hom_F2_Q (g : F2_Field ~{Field}~> Q_Field) : False.
Proof.
  apply Q_ftwo_nonzero.
  rewrite <- (ftwo_map g).
  (* [ftwo F2_Field] IS [rig_zero F2_Field], by computation *)
  apply (rig_map_zero g).
Qed.

(* * ** riehl:1.6:example15: fields have neither initial nor a
 终对象 （已译） *)

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Field_no_initial (I : @Initial Field) : False.
Proof.
  pose (f := @zero Field I Q_Field).
  pose (g := @zero Field I F2_Field).
  (* 1 + 1 is nonzero in the initial field, because its ℚ-image is 2 *)
  assert (Hnz : ftwo (@initial_obj Field I)
                  ≈ rig_zero (@initial_obj Field I) → False).
  { intro H.
    apply Q_ftwo_nonzero.
    transitivity (rig_map f (ftwo (@initial_obj Field I))).
    - symmetry; apply (ftwo_map f).
    - transitivity (rig_map f (rig_zero (@initial_obj Field I))).
      + apply (proper_morphism (rig_map f)); exact H.
      + apply (rig_map_zero f). }
  (* yet its F₂-image is zero *)
  apply (field_hom_nonzero g _ Hnz).
  rewrite (ftwo_map g).
  exact F2_ftwo_zero.
Qed.

(* 相关说明。 （已译） *)
Theorem Field_no_terminal (T : @Terminal Field) : False.
Proof.
  pose (f := @one Field T Q_Field).
  pose (g := @one Field T F2_Field).
  (* 相关说明。 （已译） *)
  assert (H0 : ftwo (@terminal_obj Field T)
                 ≈ rig_zero (@terminal_obj Field T)).
  { transitivity (rig_map g (ftwo F2_Field)).
    - symmetry; apply (ftwo_map g).
    - apply (rig_map_zero g). }
  (* 相关说明。 （已译） *)
  apply (field_hom_nonzero f (ftwo Q_Field) Q_ftwo_nonzero).
  rewrite (ftwo_map f).
  exact H0.
Qed.

(* The 对象-level readings, what "范畴 has no
 始对象" says without choosing one: NO 对象 [Field] is
 initial, none terminal. （已译） *)
Corollary Field_no_initial_obj (c : Field) (H : IsInitialObj c) : False.
Proof. exact (Field_no_initial (Initial_from_IsInitialObj H)). Qed.

Corollary Field_no_terminal_obj (c : Field) (H : IsTerminalObj c) : False.
Proof. exact (Field_no_terminal (Terminal_from_IsTerminalObj H)). Qed.

(** ** Acceptance tests *)

(* The forgetful 函子 return underlying data nose. （已译） *)
Example field_forget_carrier (F : FieldObject) :
  Field_Forget F = rig_setoid F := eq_refl.

Example field_rng_object (F : FieldObject) :
  Field_Rng F = field_ring F := eq_refl.

(* 相关说明。 （已译） *)
Example q_inv_three : finv Q_Field (3 # 1) = (1 # 3)%Q := eq_refl.

Example q_one_neq_zero : (1 # 1) == 0 → False := field_one_neq_zero Q_Field.
