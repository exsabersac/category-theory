Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Instance.Rng.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Theory.Universal.Element.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 nLab: https://ncatlab.org/nlab/show/quotient+ring
 Wikipedia: https://en.wikipedia.org/wiki/Quotient_ring

   本文件给出商相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Two-sided ideals *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Record Ideal (R : RingObject) := {
  idl_mem : carrier (rig_setoid R) → Type;

  (* (1) ≈-saturation *)
  idl_resp : ∀ a b : carrier (rig_setoid R),
    a ≈ b → idl_mem a → idl_mem b;
  (* (2) zero *)
  idl_zero : idl_mem (rig_zero R);
  (* (3) closure under addition *)
  idl_plus : ∀ a b : carrier (rig_setoid R),
    idl_mem a → idl_mem b → idl_mem (rig_add R a b);
  (* (4) absorption on the left *)
  idl_absorb_l : ∀ r a : carrier (rig_setoid R),
    idl_mem a → idl_mem (rig_mul R r a);
  (* (5) absorption on the RIGHT -- the field a one-sided ideal drops,
     and the one Instance/Rng/Quotient/OneSided.v proves indispensable *)
  idl_absorb_r : ∀ a r : carrier (rig_setoid R),
    idl_mem a → idl_mem (rig_mul R a r)
}.

Arguments idl_mem {R} _ _.
Arguments idl_resp {R} _ _ _ _ _.
Arguments idl_zero {R} _.
Arguments idl_plus {R} _ _ _ _ _.
Arguments idl_absorb_l {R} _ _ _ _.
Arguments idl_absorb_r {R} _ _ _ _.

(* A LEFT ideal: the same record with [idl_absorb_r] dropped.  It exists
   in order to be refuted. *)
Record LeftIdeal (R : RingObject) := {
  lidl_mem : carrier (rig_setoid R) → Type;

  lidl_resp : ∀ a b : carrier (rig_setoid R),
    a ≈ b → lidl_mem a → lidl_mem b;
  lidl_zero : lidl_mem (rig_zero R);
  lidl_plus : ∀ a b : carrier (rig_setoid R),
    lidl_mem a → lidl_mem b → lidl_mem (rig_add R a b);
  lidl_absorb_l : ∀ r a : carrier (rig_setoid R),
    lidl_mem a → lidl_mem (rig_mul R r a)
}.

Arguments lidl_mem {R} _ _.
Arguments lidl_resp {R} _ _ _ _ _.
Arguments lidl_zero {R} _.
Arguments lidl_plus {R} _ _ _ _ _.
Arguments lidl_absorb_l {R} _ _ _ _.

(* Every two-sided ideal is in particular a left ideal, so the refutation
   downstream is genuinely about the WEAKER notion. *)
Definition Ideal_LeftIdeal {R : RingObject} (I : Ideal R) : LeftIdeal R :=
  {| lidl_mem := idl_mem I
   ; lidl_resp := idl_resp I
   ; lidl_zero := idl_zero I
   ; lidl_plus := idl_plus I
   ; lidl_absorb_l := idl_absorb_l I |}.

(* Saturation in the argument-implicit shape the proofs below want. *)
Definition idl_at {R : RingObject} (I : Ideal R)
  {a b : carrier (rig_setoid R)} (Hab : a ≈ b) (Ha : idl_mem I a) :
  idl_mem I b := idl_resp I a b Hab Ha.

Definition lidl_at {R : RingObject} (L : LeftIdeal R)
  {a b : carrier (rig_setoid R)} (Hab : a ≈ b) (Ha : lidl_mem L a) :
  lidl_mem L b := lidl_resp L a b Hab Ha.

(* THE SIXTH FIELD THAT IS NOT A FIELD: closure under negation, because
   -a is (-1)·a.  Only LEFT absorption is spent. *)
Lemma idl_neg {R : RingObject} (I : Ideal R) (a : carrier (rig_setoid R)) :
  idl_mem I a → idl_mem I (ring_neg R a).
Proof.
  intro Ha.
  apply (idl_at I (a := rig_mul R (ring_neg R (rig_one R)) a)).
  - apply rig_mul_neg_one.
  - exact (idl_absorb_l I _ _ Ha).
Qed.

Lemma idl_sub {R : RingObject} (I : Ideal R)
  (a b : carrier (rig_setoid R)) :
  idl_mem I a → idl_mem I b → idl_mem I (ab_sub (ring_ab R) a b).
Proof.
  intros Ha Hb.
  exact (idl_plus I _ _ Ha (idl_neg I _ Hb)).
Qed.

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma rng_neg_mul_l (R : RingObject) (a b : carrier (rig_setoid R)) :
  rig_mul R (ring_neg R a) b ≈ ring_neg R (rig_mul R a b).
Proof.
  apply (ab_neg_unique (ring_ab R)); simpl.
  rewrite <- rig_distr_r.
  rewrite (ring_neg_l R a).
  apply rig_mul_zero_l.
Qed.

Lemma rng_neg_mul_r (R : RingObject) (a b : carrier (rig_setoid R)) :
  rig_mul R a (ring_neg R b) ≈ ring_neg R (rig_mul R a b).
Proof.
  apply (ab_neg_unique (ring_ab R)); simpl.
  rewrite <- rig_distr_l.
  rewrite (ring_neg_l R b).
  apply rig_mul_zero_r.
Qed.

Lemma rig_mul_sub_l (R : RingObject) (a b c : carrier (rig_setoid R)) :
  rig_mul R a (ab_sub (ring_ab R) b c)
    ≈ ab_sub (ring_ab R) (rig_mul R a b) (rig_mul R a c).
Proof.
  unfold ab_sub; simpl.
  rewrite rig_distr_l.
  now rewrite rng_neg_mul_r.
Qed.

Lemma rig_mul_sub_r (R : RingObject) (a b c : carrier (rig_setoid R)) :
  rig_mul R (ab_sub (ring_ab R) a b) c
    ≈ ab_sub (ring_ab R) (rig_mul R a c) (rig_mul R b c).
Proof.
  unfold ab_sub; simpl.
  rewrite rig_distr_r.
  now rewrite rng_neg_mul_l.
Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma rig_map_sub {R S : RingObject} (f : R ~{Rng}~> S)
  (x y : carrier (rig_setoid R)) :
  rig_map f (ab_sub (ring_ab R) x y)
    ≈ ab_sub (ring_ab S) (rig_map f x) (rig_map f y).
Proof.
  unfold ab_sub; simpl.
  rewrite (rig_map_add f).
  apply rig_add_respects; [ reflexivity |].
  apply (RigHom_neg R S f).
Qed.

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma rig_mul_sub_expand (R : RingObject)
  (x y x' y' : carrier (rig_setoid R)) :
  ab_sub (ring_ab R) (rig_mul R x y) (rig_mul R x' y')
    ≈ rig_add R (rig_mul R x (ab_sub (ring_ab R) y y'))
                (rig_mul R (ab_sub (ring_ab R) x x') y').
Proof.
  rewrite rig_mul_sub_l, rig_mul_sub_r.
  symmetry.
  exact (ab_sub_trans (ring_ab R) (rig_mul R x y) (rig_mul R x y')
                      (rig_mul R x' y')).
Qed.

(** ** The quotient relation *)

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition rquot_rel {R : RingObject} (I : Ideal R)
  (x y : carrier (rig_setoid R)) : Prop :=
  inhabited (idl_mem I (ab_sub (ring_ab R) x y)).

Section QuotientRelation.

Context {R : RingObject}.
Context (I : Ideal R).

Lemma rquot_rel_of_equiv (x y : carrier (rig_setoid R)) :
  x ≈ y → rquot_rel I x y.
Proof.
  intro Hxy; unfold rquot_rel.
  constructor.
  apply (idl_at I (a := rig_zero R)); [| exact (idl_zero I) ].
  change (rig_zero R) with (cmon_zero (ring_ab R)).
  rewrite <- Hxy.
  symmetry; apply (ab_sub_self (ring_ab R)).
Qed.

Lemma rquot_rel_refl (x : carrier (rig_setoid R)) : rquot_rel I x x.
Proof. apply rquot_rel_of_equiv; reflexivity. Qed.

Lemma rquot_rel_sym (x y : carrier (rig_setoid R)) :
  rquot_rel I x y → rquot_rel I y x.
Proof.
  unfold rquot_rel; intros [K].
  constructor.
  apply (idl_at I (a := ring_neg R (ab_sub (ring_ab R) x y))).
  - apply (ab_sub_neg (ring_ab R)).
  - exact (idl_neg I _ K).
Qed.

Lemma rquot_rel_trans (x y z : carrier (rig_setoid R)) :
  rquot_rel I x y → rquot_rel I y z → rquot_rel I x z.
Proof.
  unfold rquot_rel; intros [K1] [K2].
  constructor.
  apply (idl_at I (a := rig_add R (ab_sub (ring_ab R) x y)
                                 (ab_sub (ring_ab R) y z))).
  - apply (ab_sub_trans (ring_ab R)).
  - exact (idl_plus I _ _ K1 K2).
Qed.

Lemma rquot_rel_add (x x' y y' : carrier (rig_setoid R)) :
  rquot_rel I x x' → rquot_rel I y y' →
  rquot_rel I (rig_add R x y) (rig_add R x' y').
Proof.
  unfold rquot_rel; intros [K1] [K2].
  constructor.
  apply (idl_at I (a := rig_add R (ab_sub (ring_ab R) x x')
                                 (ab_sub (ring_ab R) y y'))).
  - apply (ab_sub_plus (ring_ab R)).
  - exact (idl_plus I _ _ K1 K2).
Qed.

Lemma rquot_rel_neg (x x' : carrier (rig_setoid R)) :
  rquot_rel I x x' → rquot_rel I (ring_neg R x) (ring_neg R x').
Proof.
  unfold rquot_rel; intros [K].
  constructor.
  apply (idl_at I (a := ring_neg R (ab_sub (ring_ab R) x x'))).
  - rewrite (ab_sub_neg (ring_ab R)).
    (*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
    symmetry; exact (ab_sub_neg_neg (ring_ab R) x x').
  - exact (idl_neg I _ K).
Qed.

(* THE PLACE BOTH ABSORPTION LAWS ARE SPENT, one apiece. *)
Lemma rquot_rel_mul (x x' y y' : carrier (rig_setoid R)) :
  rquot_rel I x x' → rquot_rel I y y' →
  rquot_rel I (rig_mul R x y) (rig_mul R x' y').
Proof.
  unfold rquot_rel; intros [K1] [K2].
  constructor.
  apply (idl_at I
           (a := rig_add R (rig_mul R x (ab_sub (ring_ab R) y y'))
                           (rig_mul R (ab_sub (ring_ab R) x x') y'))).
  - symmetry; apply rig_mul_sub_expand.
  - apply idl_plus.
    + exact (idl_absorb_l I x _ K2).
    + exact (idl_absorb_r I _ y' K1).
Qed.

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma rquot_rel_zero_iff (x : carrier (rig_setoid R)) :
  rquot_rel I x (rig_zero R) ↔ inhabited (idl_mem I x).
Proof.
  split; intros [K]; unfold rquot_rel in *; constructor.
  - exact (idl_at I (ab_sub_zero_r (ring_ab R) x) K).
  - exact (idl_at I (symmetry (ab_sub_zero_r (ring_ab R) x)) K).
Qed.

(* The half of the biconditional that keeps its [Type]-valued hypothesis:
   nothing is truncated on the way in. *)
Lemma rquot_rel_of_mem (x : carrier (rig_setoid R)) :
  idl_mem I x → rquot_rel I x (rig_zero R).
Proof.
  intro K; unfold rquot_rel; constructor.
  exact (idl_at I (symmetry (ab_sub_zero_r (ring_ab R) x)) K).
Qed.

Program Definition rquot_setoid : Setoid (carrier (rig_setoid R)) := {|
  equiv := rquot_rel I
|}.
Next Obligation.
  constructor.
  - exact rquot_rel_refl.
  - exact rquot_rel_sym.
  - exact rquot_rel_trans.
Qed.

End QuotientRelation.

Arguments rquot_setoid {R} I.

(* The property the two-sided condition buys, named so that
   Instance/Rng/Quotient/OneSided.v can refute it for the one-sided
   notion. *)
Definition IdealMulCongruence {R : RingObject} (I : Ideal R) : Type :=
  ∀ x x' y y' : carrier (rig_setoid R),
    rquot_rel I x x' → rquot_rel I y y' →
    rquot_rel I (rig_mul R x y) (rig_mul R x' y').

Definition ideal_mul_congruence {R : RingObject} (I : Ideal R) :
  IdealMulCongruence I := rquot_rel_mul I.

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition lquot_rel {R : RingObject} (L : LeftIdeal R)
  (x y : carrier (rig_setoid R)) : Prop :=
  inhabited (lidl_mem L (ab_sub (ring_ab R) x y)).

Definition LeftIdealMulCongruence {R : RingObject} (L : LeftIdeal R) : Type :=
  ∀ x x' y y' : carrier (rig_setoid R),
    lquot_rel L x x' → lquot_rel L y y' →
    lquot_rel L (rig_mul R x y) (rig_mul R x' y').

Example lquot_rel_is_rquot_rel {R : RingObject} (I : Ideal R)
  (x y : carrier (rig_setoid R)) :
  lquot_rel (Ideal_LeftIdeal I) x y = rquot_rel I x y.
Proof. reflexivity. Qed.

(** ** The quotient ring and its projection *)

Definition QuotientRing {R : RingObject} (I : Ideal R) : RingObject.
Proof.
  unshelve notypeclasses refine {|
    ring_rig := {| rig_setoid := {| carrier := carrier (rig_setoid R)
                                  ; is_setoid := rquot_setoid I |}
                 ; rig_zero := rig_zero R
                 ; rig_add := rig_add R
                 ; rig_one := rig_one R
                 ; rig_mul := rig_mul R |};
    ring_neg := ring_neg R
  |}.
  - (* rig_add_respects *)
    intros x x' Hx y y' Hy; now apply rquot_rel_add.
  - (* rig_mul_respects *)
    intros x x' Hx y y' Hy; now apply rquot_rel_mul.
  - (* rig_add_assoc *)
    intros a b c; apply rquot_rel_of_equiv, rig_add_assoc.
  - (* rig_add_comm *)
    intros a b; apply rquot_rel_of_equiv, rig_add_comm.
  - (* rig_add_zero_l *)
    intros a; apply rquot_rel_of_equiv, rig_add_zero_l.
  - (* rig_mul_assoc *)
    intros a b c; apply rquot_rel_of_equiv, rig_mul_assoc.
  - (* rig_mul_one_l *)
    intros a; apply rquot_rel_of_equiv, rig_mul_one_l.
  - (* rig_mul_one_r *)
    intros a; apply rquot_rel_of_equiv, rig_mul_one_r.
  - (* rig_distr_l *)
    intros a b c; apply rquot_rel_of_equiv, rig_distr_l.
  - (* rig_distr_r *)
    intros a b c; apply rquot_rel_of_equiv, rig_distr_r.
  - (* rig_mul_zero_l *)
    intros a; apply rquot_rel_of_equiv, rig_mul_zero_l.
  - (* rig_mul_zero_r *)
    intros a; apply rquot_rel_of_equiv, rig_mul_zero_r.
  - (*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
    exact (@PropEquiv_of_relation _ (rquot_setoid I) (rquot_rel I)
             (fun _ _ h => h) (fun _ _ h => h)).
  - (* ring_neg_respects *)
    intros x y Hxy; now apply rquot_rel_neg.
  - (* ring_neg_l *)
    intros a; apply rquot_rel_of_equiv, ring_neg_l.
Defined.

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition rquot_proj {R : RingObject} (I : Ideal R) :
  R ~{Rng}~> QuotientRing I := {|
  rig_map := {| morphism := fun x : carrier (rig_setoid R) => x |}
|}.
Next Obligation. intros R I x y Hxy; apply rquot_rel_of_equiv, Hxy. Qed.
Next Obligation. intros R I; simpl; apply rquot_rel_refl. Qed.
Next Obligation. intros R I x y; simpl; apply rquot_rel_refl. Qed.
Next Obligation. intros R I; simpl; apply rquot_rel_refl. Qed.
Next Obligation. intros R I x y; simpl; apply rquot_rel_refl. Qed.

Lemma rquot_proj_kills {R : RingObject} (I : Ideal R)
  (x : carrier (rig_setoid R)) :
  idl_mem I x → rig_map (rquot_proj I) x ≈ rig_zero (QuotientRing I).
Proof.
  intro Hx; simpl.
  (* The [Type]-valued direction: [rquot_rel_of_mem] rather than the
     truncated biconditional, so nothing is lost on the way in. *)
  exact (rquot_rel_of_mem I x Hx).
Qed.

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma rquot_proj_kernel {R : RingObject} (I : Ideal R)
  (x : carrier (rig_setoid R)) :
  rig_map (rquot_proj I) x ≈ rig_zero (QuotientRing I) ↔ inhabited (idl_mem I x).
Proof. exact (rquot_rel_zero_iff I x). Qed.

Lemma rquot_proj_surjective {R : RingObject} (I : Ideal R) :
  ∀ b : carrier (rig_setoid (QuotientRing I)),
    ∃ a, rig_map (rquot_proj I) a ≈ b.
Proof. intro x; exists x; simpl; apply rquot_rel_refl. Qed.

Lemma rquot_proj_epic {R : RingObject} (I : Ideal R) :
  Epic (rquot_proj I).
Proof. apply rng_surjective_epic, rquot_proj_surjective. Qed.

(** ** The functor of homomorphisms killing I *)

Definition RKills {R : RingObject} (I : Ideal R) (K : RingObject) : Type :=
  { h : R ~{Rng}~> K
  & ∀ a : carrier (rig_setoid R), idl_mem I a →
      rig_map h a ≈ rig_zero K }.

Program Definition RKills_Setoid {R : RingObject} (I : Ideal R)
  (K : RingObject) : Setoid (RKills I K) := {|
  equiv := fun p q => `1 p ≈ `1 q
|}.
Next Obligation.
  intros R I K.
  constructor.
  - intro p; reflexivity.
  - intros p q Hpq; now symmetry.
  - intros p q u Hpq Hqu; now transitivity (`1 q).
Qed.

Lemma RKills_post {R : RingObject} (I : Ideal R) {K K' : RingObject}
  (k : K ~{Rng}~> K') (p : RKills I K) (a : carrier (rig_setoid R)) :
  idl_mem I a → rig_map (k ∘ `1 p) a ≈ rig_zero K'.
Proof.
  intro Ha; simpl; unfold Basics.compose.
  rewrite (`2 p a Ha).
  apply (rig_map_zero k).
Qed.

Program Definition RKillsFunctor {R : RingObject} (I : Ideal R) :
  Rng ⟶ Sets := {|
  fobj := fun K => {| carrier := RKills I K
                    ; is_setoid := RKills_Setoid I K |};
  fmap := fun K K' k =>
    {| morphism := fun p : RKills I K =>
         existT _ (k ∘ `1 p) (RKills_post I k p) |}
|}.
Next Obligation.
  intros R I K K' k p q Hpq a; simpl in *.
  unfold Basics.compose.
  now rewrite (Hpq a).
Qed.
Next Obligation.
  intros R I K K' k k' Hk p a; simpl.
  unfold Basics.compose.
  exact (Hk _).
Qed.
Next Obligation. intros R I K p a; simpl; reflexivity. Qed.
Next Obligation. intros R I K K' K'' k k' p a; simpl; reflexivity. Qed.

(** ** The mediating homomorphism *)

Section Mediator.

Context {R : RingObject}.
Context (I : Ideal R).
Context {K : RingObject}.
Context (p : RKills I K).

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma rkills_descends (x y : carrier (rig_setoid R)) :
  rquot_rel I x y → rig_map (`1 p) x ≈ rig_map (`1 p) y.
Proof.
  intro Hxy.
  (*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  apply pequiv_to.
  destruct Hxy as [Hxy].
  apply pequiv_from.
  apply (fst (ab_sub_eq_zero_iff (ring_ab K) _ _)).
  rewrite <- (rig_map_sub (`1 p) x y).
  exact (`2 p _ Hxy).
Qed.

Program Definition rquot_med : QuotientRing I ~{Rng}~> K := {|
  rig_map := {| morphism := fun x : carrier (rig_setoid (QuotientRing I)) =>
                              rig_map (`1 p) x |}
|}.
Next Obligation. intros x y Hxy; exact (rkills_descends x y Hxy). Qed.
Next Obligation. simpl; apply (rig_map_zero (`1 p)). Qed.
Next Obligation. intros x y; simpl; apply (rig_map_add (`1 p)). Qed.
Next Obligation. simpl; apply (rig_map_one (`1 p)). Qed.
Next Obligation. intros x y; simpl; apply (rig_map_mul (`1 p)). Qed.

Lemma rquot_med_commutes : rquot_med ∘ rquot_proj I ≈ `1 p.
Proof. intro x; simpl; reflexivity. Qed.

Lemma rquot_med_unique (v : QuotientRing I ~{Rng}~> K)
  (Hv : v ∘ rquot_proj I ≈ `1 p) : rquot_med ≈ v.
Proof. intro x; simpl; symmetry; exact (Hv x). Qed.

End Mediator.

Arguments rquot_med {R} I {K} p.

(** ** Mac Lane §III.1 Exercise 6: ⟨R/I, p⟩ is a universal element *)

Definition rquot_elem {R : RingObject} (I : Ideal R) :
  RKills I (QuotientRing I) :=
  existT _ (rquot_proj I) (rquot_proj_kills I).

Program Definition rquot_universal_element {R : RingObject} (I : Ideal R) :
  AUniversalElement (RKillsFunctor I) (QuotientRing I) := {|
  aue_elem := rquot_elem I
|}.
Next Obligation.
  intros R I K x.
  unshelve refine {| unique_obj := rquot_med I x |}.
  - exact (rquot_med_commutes I x).
  - intros v Hv; simpl in *.
    exact (rquot_med_unique I x v Hv).
Defined.

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example rquot_universal_elem_is_proj {R : RingObject} (I : Ideal R) :
  `1 (@aue_elem _ (RKillsFunctor I) (QuotientRing I)
        (rquot_universal_element I)) = rquot_proj I.
Proof. reflexivity. Qed.

Example rquot_universal_med_is_rquot_med {R : RingObject} (I : Ideal R)
  {K : RingObject} (x : RKills I K) :
  unique_obj (@aue_universal _ (RKillsFunctor I) (QuotientRing I)
                (rquot_universal_element I) K x)
    = rquot_med I x.
Proof. reflexivity. Qed.

(** ** The homomorphism theorem, as a biconditional *)

Theorem ring_hom_theorem {R K : RingObject} (I : Ideal R)
  (h : R ~{Rng}~> K) :
  (∀ a : carrier (rig_setoid R), idl_mem I a → rig_map h a ≈ rig_zero K)
    ↔ (∃! u : QuotientRing I ~{Rng}~> K, u ∘ rquot_proj I ≈ h).
Proof.
  split.
  - intro Hkill.
    pose (x := existT (fun h : R ~{Rng}~> K =>
                         ∀ a : carrier (rig_setoid R), idl_mem I a →
                           rig_map h a ≈ rig_zero K) h Hkill).
    unshelve refine {| unique_obj := rquot_med I x |}.
    + exact (rquot_med_commutes I x).
    + intros v Hv.
      exact (rquot_med_unique I x v Hv).
  - intros [u Hu _] a Ha.
    transitivity (rig_map u (rig_map (rquot_proj I) a)).
    + symmetry; exact (Hu a).
    + transitivity (rig_map u (rig_zero (QuotientRing I))).
      * apply proper_morphism.
        exact (rquot_proj_kills I a Ha).
      * exact (rig_map_zero u).
Qed.

Definition ring_hom_theorem_factor {R K : RingObject} (I : Ideal R)
  (h : R ~{Rng}~> K)
  (Hkill : ∀ a : carrier (rig_setoid R), idl_mem I a →
             rig_map h a ≈ rig_zero K) :
  ∃! u : QuotientRing I ~{Rng}~> K, u ∘ rquot_proj I ≈ h :=
  fst (ring_hom_theorem I h) Hkill.

Definition ring_hom_theorem_kills {R K : RingObject} (I : Ideal R)
  (h : R ~{Rng}~> K)
  (Hfac : ∃! u : QuotientRing I ~{Rng}~> K, u ∘ rquot_proj I ≈ h) :
  ∀ a : carrier (rig_setoid R), idl_mem I a → rig_map h a ≈ rig_zero K :=
  snd (ring_hom_theorem I h) Hfac.

(*
   本节说明同构、核/余核、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition KernelIdeal {R S : RingObject} (f : R ~{Rng}~> S) :
  Ideal R := {|
  idl_mem := fun a : carrier (rig_setoid R) => rig_map f a ≈ rig_zero S
|}.
Next Obligation.
  intros R S f a b Hab Ha; simpl in *.
  now rewrite <- Hab.
Qed.
Next Obligation. intros R S f; simpl; apply (rig_map_zero f). Qed.
Next Obligation.
  intros R S f a b Ha Hb; simpl in *.
  rewrite (rig_map_add f), Ha, Hb.
  apply rig_add_zero_l.
Qed.
Next Obligation.
  intros R S f r a Ha; simpl in *.
  rewrite (rig_map_mul f), Ha.
  apply rig_mul_zero_r.
Qed.
Next Obligation.
  intros R S f a r Ha; simpl in *.
  rewrite (rig_map_mul f), Ha.
  apply rig_mul_zero_l.
Qed.

Example KernelIdeal_mem {R S : RingObject} (f : R ~{Rng}~> S)
  (a : carrier (rig_setoid R)) :
  idl_mem (KernelIdeal f) a = (rig_map f a ≈ rig_zero S).
Proof. reflexivity. Qed.

(** ** Quotients by coextensive ideals agree *)

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma rquot_rel_mono {R : RingObject} (I I' : Ideal R)
  (H : ∀ a : carrier (rig_setoid R), idl_mem I a → idl_mem I' a)
  (x y : carrier (rig_setoid R)) : rquot_rel I x y → rquot_rel I' x y.
Proof. intros [K]; constructor; exact (H _ K). Qed.

Program Definition rquot_congr {R : RingObject} (I I' : Ideal R)
  (H1 : ∀ a : carrier (rig_setoid R), idl_mem I a → idl_mem I' a)
  (H2 : ∀ a : carrier (rig_setoid R), idl_mem I' a → idl_mem I a) :
  QuotientRing I ≅[Rng] QuotientRing I' := {|
  to := {| rig_map := {| morphism :=
    fun x : carrier (rig_setoid (QuotientRing I)) => x |} |};
  from := {| rig_map := {| morphism :=
    fun x : carrier (rig_setoid (QuotientRing I')) => x |} |}
|}.
Next Obligation.
  intros R I I' H1 H2 x y Hxy; exact (rquot_rel_mono I I' H1 x y Hxy).
Qed.
Next Obligation. intros R I I' H1 H2; simpl; apply rquot_rel_refl. Qed.
Next Obligation. intros R I I' H1 H2 x y; simpl; apply rquot_rel_refl. Qed.
Next Obligation. intros R I I' H1 H2; simpl; apply rquot_rel_refl. Qed.
Next Obligation. intros R I I' H1 H2 x y; simpl; apply rquot_rel_refl. Qed.
Next Obligation.
  intros R I I' H1 H2 x y Hxy; exact (rquot_rel_mono I' I H2 x y Hxy).
Qed.
Next Obligation. intros R I I' H1 H2; simpl; apply rquot_rel_refl. Qed.
Next Obligation. intros R I I' H1 H2 x y; simpl; apply rquot_rel_refl. Qed.
Next Obligation. intros R I I' H1 H2; simpl; apply rquot_rel_refl. Qed.
Next Obligation. intros R I I' H1 H2 x y; simpl; apply rquot_rel_refl. Qed.
Next Obligation. intros R I I' H1 H2 x; simpl; apply rquot_rel_refl. Qed.
Next Obligation. intros R I I' H1 H2 x; simpl; apply rquot_rel_refl. Qed.

(** ** The degenerate ideals, named and separated *)

Program Definition TrivialIdeal (R : RingObject) : Ideal R := {|
  idl_mem := fun a : carrier (rig_setoid R) => a ≈ rig_zero R
|}.
Next Obligation.
  intros R a b Hab Ha; simpl in *; now rewrite <- Hab.
Qed.
Next Obligation. intros R; simpl; reflexivity. Qed.
Next Obligation.
  intros R a b Ha Hb; simpl in *.
  rewrite Ha, Hb; apply rig_add_zero_l.
Qed.
Next Obligation.
  intros R r a Ha; simpl in *.
  rewrite Ha; apply rig_mul_zero_r.
Qed.
Next Obligation.
  intros R a r Ha; simpl in *.
  rewrite Ha; apply rig_mul_zero_l.
Qed.

Program Definition TotalIdeal (R : RingObject) : Ideal R := {|
  idl_mem := fun _ : carrier (rig_setoid R) => poly_unit
|}.
Next Obligation. intros R a b Hab Ha; exact ttt. Qed.
Next Obligation. intros R; exact ttt. Qed.
Next Obligation. intros R a b Ha Hb; exact ttt. Qed.
Next Obligation. intros R r a Ha; exact ttt. Qed.
Next Obligation. intros R a r Ha; exact ttt. Qed.

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma rquot_trivial_iff (R : RingObject) (x y : carrier (rig_setoid R)) :
  rquot_rel (TrivialIdeal R) x y ↔ x ≈ y.
Proof.
  split.
  - intro K.
    apply (fst (ab_sub_eq_zero_iff (ring_ab R) x y)).
    exact (pequiv_elim_inhabited _ _ K).
  - intro Hxy.
    constructor.
    exact (snd (ab_sub_eq_zero_iff (ring_ab R) x y) Hxy).
Qed.

Lemma rquot_total_collapses (R : RingObject)
  (x y : carrier (rig_setoid R)) : rquot_rel (TotalIdeal R) x y.
Proof. constructor; exact ttt. Qed.

(* Quotienting by the whole ring gives a ring in which 1 ≈ 0, which is
   the zero ring up to the identification [rquot_total_collapses]
   supplies. *)
Lemma rquot_total_one_is_zero (R : RingObject) :
  rig_one (QuotientRing (TotalIdeal R))
    ≈ rig_zero (QuotientRing (TotalIdeal R)).
Proof. exact (rquot_total_collapses R _ _). Qed.

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ℤ's ring operations, pinned by convertibility -- what lets [ring] and
   [lia] see the goals below, neither tactic seeing through [carrier]. *)
Example zring_zero_is_0 : rig_zero Int_Ring = 0%Z := eq_refl.
Example zring_one_is_1 : rig_one Int_Ring = 1%Z := eq_refl.
Example zring_add_is_add (a b : Z) : rig_add Int_Ring a b = (a + b)%Z :=
  eq_refl.
Example zring_mul_is_mul (a b : Z) : rig_mul Int_Ring a b = (a * b)%Z :=
  eq_refl.
Example zring_neg_is_opp (a : Z) : ring_neg Int_Ring a = (- a)%Z := eq_refl.
Example zring_sub_is_minus (a b : Z) :
  ab_sub (ring_ab Int_Ring) a b = (a - b)%Z := eq_refl.

Definition ZEven (a : Z) : Type := { k : Z & a = (2 * k)%Z }.

Program Definition EvenIdeal : Ideal Int_Ring := {| idl_mem := ZEven |}.
Next Obligation.
  intros a b Hab [k Hk]; simpl in *.
  exists k; now subst.
Qed.
Next Obligation. exists 0%Z; reflexivity. Qed.
Next Obligation.
  intros a b [k Hk] [l Hl].
  rewrite zring_add_is_add, Hk, Hl.
  exists (k + l)%Z; ring.
Qed.
Next Obligation.
  intros r a [k Hk].
  rewrite zring_mul_is_mul, Hk.
  exists (r * k)%Z; ring.
Qed.
Next Obligation.
  intros a r [k Hk].
  rewrite zring_mul_is_mul, Hk.
  exists (k * r)%Z; ring.
Qed.

(* 2ℤ is PROPER: 1 is not even, so ℤ/2ℤ is not the zero ring. *)
Theorem EvenIdeal_proper : idl_mem EvenIdeal 1%Z → False.
Proof. intros [k Hk]; lia. Qed.

(* 2ℤ is NONTRIVIAL: it contains 2, which is not zero. *)
Theorem EvenIdeal_nontrivial :
  idl_mem EvenIdeal 2%Z
  * ((2%Z : carrier (rig_setoid Int_Ring)) ≈ rig_zero Int_Ring → False).
Proof.
  split.
  - exists 1%Z; reflexivity.
  - simpl; discriminate.
Qed.

(* THE QUOTIENT DOES NOT COLLAPSE: 1 stays apart from 0 in ℤ/2ℤ, i.e.
   ℤ/2ℤ is not the zero ring. *)
Theorem Z2_ring_not_collapsed : rquot_rel EvenIdeal 1%Z 0%Z → False.
Proof.
  (* One extra layer since the PR "algebraic carriers are sets"
     (2026-09-17): [rquot_rel] is the truncation of membership, and the
     goal [False] is a [Prop], so the elimination is allowed. *)
  intros [[k Hk]].
  assert (Hz : (1 - 0 = 2 * k)%Z) by exact Hk.
  lia.
Qed.

Theorem Z2_ring_nonzero :
  rig_one (QuotientRing EvenIdeal) ≈ rig_zero (QuotientRing EvenIdeal)
    → False.
Proof. exact Z2_ring_not_collapsed. Qed.

(* ...but it does collapse 2 into 0, so the projection is not injective
   and the quotient is a genuine quotient rather than a relabelling. *)
Theorem Z2_ring_collapses_two :
  rig_map (rquot_proj EvenIdeal) 2%Z ≈ rig_map (rquot_proj EvenIdeal) 0%Z.
Proof. constructor; exists 1%Z; reflexivity. Qed.

Theorem rquot_proj_EvenIdeal_not_injective :
  (∀ a b : carrier (rig_setoid Int_Ring),
     rig_map (rquot_proj EvenIdeal) a ≈ rig_map (rquot_proj EvenIdeal) b
       → a ≈ b) → False.
Proof.
  intro Hinj.
  pose proof (Hinj 2%Z 0%Z Z2_ring_collapses_two) as E.
  discriminate E.
Qed.

(* ℤ/2ℤ's ARITHMETIC, computed: 1 + 1 ≈ 0 and 1 · 1 ≈ 1, so the
   MULTIPLICATIVE structure survives the quotient nondegenerately and
   the ring is not merely an abelian group in disguise. *)
Theorem Z2_ring_one_plus_one :
  rig_add (QuotientRing EvenIdeal) 1%Z 1%Z
    ≈ rig_zero (QuotientRing EvenIdeal).
Proof. constructor; exists 1%Z; reflexivity. Qed.

Theorem Z2_ring_one_times_one :
  rig_mul (QuotientRing EvenIdeal) 1%Z 1%Z
    ≈ rig_one (QuotientRing EvenIdeal).
Proof. constructor; exists 0%Z; reflexivity. Qed.

Theorem Z2_ring_three_is_one :
  rig_map (rquot_proj EvenIdeal) 3%Z ≈ rig_one (QuotientRing EvenIdeal).
Proof. constructor; exists 1%Z; reflexivity. Qed.

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma EvenIdeal_is_kernel_of_proj (a : Z) :
  idl_mem (KernelIdeal (rquot_proj EvenIdeal)) a
    ↔ inhabited (idl_mem EvenIdeal a).
Proof. exact (rquot_proj_kernel EvenIdeal a). Qed.

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition ZSix (a : Z) : Type := { k : Z & a = (6 * k)%Z }.

Program Definition SixIdeal : Ideal Int_Ring := {| idl_mem := ZSix |}.
Next Obligation.
  intros a b Hab [k Hk]; simpl in *.
  exists k; now subst.
Qed.
Next Obligation. exists 0%Z; reflexivity. Qed.
Next Obligation.
  intros a b [k Hk] [l Hl].
  rewrite zring_add_is_add, Hk, Hl.
  exists (k + l)%Z; ring.
Qed.
Next Obligation.
  intros r a [k Hk].
  rewrite zring_mul_is_mul, Hk.
  exists (r * k)%Z; ring.
Qed.
Next Obligation.
  intros a r [k Hk].
  rewrite zring_mul_is_mul, Hk.
  exists (k * r)%Z; ring.
Qed.

Lemma six_kills_two (a : Z) :
  idl_mem SixIdeal a →
  rig_map (rquot_proj EvenIdeal) a ≈ rig_zero (QuotientRing EvenIdeal).
Proof.
  intros [k Hk].
  constructor.
  exists (3 * k)%Z.
  (* The membership equation is CONVERTIBLE to one about plain ℤ, and
     [exact] is what performs the conversion; [lia] and [ring] see
     through neither [carrier] nor [rig_zero]. *)
  assert (Hz : (a - 0 = 2 * (3 * k))%Z) by lia.
  exact Hz.
Qed.

Definition six_to_two : RKills SixIdeal (QuotientRing EvenIdeal) :=
  existT _ (rquot_proj EvenIdeal) six_kills_two.

Definition Z6_to_Z2 : QuotientRing SixIdeal ~{Rng}~> QuotientRing EvenIdeal :=
  rquot_med SixIdeal six_to_two.

(* The mediator is the one the CLASS produces, by convertibility. *)
Example Z6_to_Z2_is_the_mediator :
  unique_obj (@aue_universal _ (RKillsFunctor SixIdeal)
                (QuotientRing SixIdeal) (rquot_universal_element SixIdeal)
                (QuotientRing EvenIdeal) six_to_two)
    = Z6_to_Z2.
Proof. reflexivity. Qed.

(* Its triangle, and its value: the class of 5 in ℤ/6ℤ goes to the class
   of 1 in ℤ/2ℤ, and not to 0. *)
Lemma Z6_to_Z2_triangle : Z6_to_Z2 ∘ rquot_proj SixIdeal
    ≈ rquot_proj EvenIdeal.
Proof. exact (rquot_med_commutes SixIdeal six_to_two). Qed.

Theorem Z6_to_Z2_five_is_one :
  rig_map Z6_to_Z2 5%Z ≈ rig_one (QuotientRing EvenIdeal).
Proof. constructor; exists 2%Z; reflexivity. Qed.

Theorem Z6_to_Z2_five_not_zero :
  rig_map Z6_to_Z2 5%Z ≈ rig_zero (QuotientRing EvenIdeal) → False.
Proof.
  intros [[k Hk]].
  assert (Hz : (5 - 0 = 2 * k)%Z) by exact Hk.
  lia.
Qed.

(* And the mediator is NOT injective: 3 and 1 are apart in ℤ/6ℤ but
   agree in ℤ/2ℤ, so the factorization is genuinely a further
   quotient. *)
Theorem Z6_three_apart_from_one : rquot_rel SixIdeal 3%Z 1%Z → False.
Proof.
  intros [[k Hk]].
  assert (Hz : (3 - 1 = 6 * k)%Z) by exact Hk.
  lia.
Qed.

Theorem Z6_to_Z2_identifies_three_and_one :
  rig_map Z6_to_Z2 3%Z ≈ rig_map Z6_to_Z2 1%Z.
Proof. constructor; exists 1%Z; reflexivity. Qed.
