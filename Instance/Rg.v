Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Instance.Ab.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/rng
 nLab: https://ncatlab.org/nlab/show/nonunital+ring
 Wikipedia: https://en.wikipedia.org/wiki/Rng_(algebra)

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Rngs over a setoid carrier *)

(*
   本节说明分配律相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record RgObject := {
  rg_ab :> AbObject;

  rg_mul : carrier (cmon_setoid (ab_cmon rg_ab)) →
           carrier (cmon_setoid (ab_cmon rg_ab)) →
           carrier (cmon_setoid (ab_cmon rg_ab));

  rg_mul_respects : Proper (equiv ==> equiv ==> equiv) rg_mul;

  rg_mul_assoc : ∀ a b c,
    rg_mul (rg_mul a b) c ≈ rg_mul a (rg_mul b c);

  rg_distr_l : ∀ a b c,
    rg_mul a (cmon_plus (ab_cmon rg_ab) b c)
      ≈ cmon_plus (ab_cmon rg_ab) (rg_mul a b) (rg_mul a c);
  rg_distr_r : ∀ a b c,
    rg_mul (cmon_plus (ab_cmon rg_ab) a b) c
      ≈ cmon_plus (ab_cmon rg_ab) (rg_mul a c) (rg_mul b c)
}.

#[export] Existing Instance rg_mul_respects.

(** ** Annihilation, derived *)

(*
   本节说明 Rg 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma rg_cancel_idem (A : AbObject) (k : carrier (cmon_setoid A)) :
  cmon_plus A k k ≈ k → k ≈ cmon_zero A.
Proof.
  intro H.
  transitivity (cmon_plus A (ab_neg A k) (cmon_plus A k k)).
  - rewrite <- cmon_plus_assoc.
    rewrite ab_neg_left.
    now rewrite cmon_plus_zero_l.
  - rewrite H.
    apply ab_neg_left.
Qed.

(*
   本节说明 Rg 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma rg_mul_zero_l (R : RgObject) (a : carrier (cmon_setoid (rg_ab R))) :
  rg_mul R (cmon_zero (rg_ab R)) a ≈ cmon_zero (rg_ab R).
Proof.
  apply (rg_cancel_idem (rg_ab R)).
  rewrite <- rg_distr_r.
  now rewrite cmon_plus_zero_l.
Qed.

Lemma rg_mul_zero_r (R : RgObject) (a : carrier (cmon_setoid (rg_ab R))) :
  rg_mul R a (cmon_zero (rg_ab R)) ≈ cmon_zero (rg_ab R).
Proof.
  apply (rg_cancel_idem (rg_ab R)).
  rewrite <- rg_distr_l.
  now rewrite cmon_plus_zero_l.
Qed.

(** ** Homomorphisms *)

(*
   本节说明 Rg 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record RgHom (R S : RgObject) := {
  rg_hom_ab :> AbHom R S;

  rg_map_mul : ∀ a b,
    cmon_map rg_hom_ab (rg_mul R a b)
      ≈ rg_mul S (cmon_map rg_hom_ab a) (cmon_map rg_hom_ab b)
}.

Arguments rg_hom_ab {R S} _.
Arguments rg_map_mul {R S} _ _ _.

(* 相关说明。 （已译） *)
Corollary rg_map_neg {R S : RgObject} (f : RgHom R S)
  (a : carrier (cmon_setoid (rg_ab R))) :
  cmon_map (rg_hom_ab f) (ab_neg (rg_ab R) a)
    ≈ ab_neg (rg_ab S) (cmon_map (rg_hom_ab f) a).
Proof. exact (ab_map_neg (rg_hom_ab f) a). Qed.

#[local] Obligation Tactic := idtac.

(* Homomorphisms are compared by their underlying maps, pointwise —
   Theory/Algebra/Rig.v's [RigHom_Setoid] pattern. *)
#[export]
Program Instance RgHom_Setoid {R S : RgObject} : Setoid (RgHom R S) := {|
  equiv := fun f g => ∀ a, cmon_map (rg_hom_ab f) a
                             ≈ cmon_map (rg_hom_ab g) a
|}.
Next Obligation.
  intros R S.
  constructor.
  - intros f a; reflexivity.
  - intros f g Hfg a; symmetry; apply Hfg.
  - intros f g h Hfg Hgh a.
    transitivity (cmon_map (rg_hom_ab g) a); [ apply Hfg | apply Hgh ].
Qed.

Program Definition rg_hom_id {R : RgObject} : RgHom R R := {|
  rg_hom_ab := @cmon_hom_id (ab_cmon (rg_ab R))
|}.
Next Obligation. intros R a b; simpl; reflexivity. Qed.

Program Definition rg_hom_compose {R S T : RgObject}
  (f : RgHom S T) (g : RgHom R S) : RgHom R T := {|
  rg_hom_ab := cmon_hom_compose (rg_hom_ab f) (rg_hom_ab g)
|}.
Next Obligation.
  intros R S T f g a b; simpl.
  rewrite (proper_morphism (cmon_map (rg_hom_ab f)) _ _
             (rg_map_mul g a b)).
  apply rg_map_mul.
Qed.

Lemma rg_hom_compose_respects {R S T : RgObject} :
  Proper (equiv ==> equiv ==> equiv) (@rg_hom_compose R S T).
Proof.
  intros f1 f2 Hf g1 g2 Hg a; simpl.
  rewrite (Hf (cmon_map (rg_hom_ab g1) a)).
  apply (proper_morphism (cmon_map (rg_hom_ab f2))), Hg.
Qed.

(** ** The category *)

(*
   本节说明 Rg 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Rg@{u p} : Category@{u p p} := {|
  obj     := RgObject@{p p p};
  hom     := RgHom@{p};
  homset  := @RgHom_Setoid@{p};
  id      := @rg_hom_id@{p};
  compose := @rg_hom_compose@{u p};

  compose_respects := @rg_hom_compose_respects@{u p}
|}.
Next Obligation. intros x y f a; simpl; reflexivity. Qed.
Next Obligation. intros x y f a; simpl; reflexivity. Qed.
Next Obligation. intros x y z w f g h a; simpl; reflexivity. Qed.
Next Obligation. intros x y z w f g h a; simpl; reflexivity. Qed.

(** ** Forgetting from Rg *)

Program Definition Rg_Forget_Ab : Rg ⟶ Ab := {|
  fobj := rg_ab;
  fmap := fun R S f => rg_hom_ab f
|}.
Next Obligation. intros R S f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros R a; simpl; reflexivity. Qed.
Next Obligation. intros R S T f g a; simpl; reflexivity. Qed.

Program Definition Rg_Forget : Rg ⟶ Sets := {|
  fobj := fun R : RgObject => cmon_setoid (ab_cmon (rg_ab R));
  fmap := fun R S f => cmon_map (rg_hom_ab f)
|}.
Next Obligation. intros R S f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros R a; simpl; reflexivity. Qed.
Next Obligation. intros R S T f g a; simpl; reflexivity. Qed.

#[export] Program Instance Rg_Forget_Ab_Faithful : Faithful Rg_Forget_Ab.
Next Obligation. intros R S f g Hfg a; exact (Hfg a). Qed.

(* * ** The forgetful 函子 unital rings （已译） *)

(*
   本节说明 Rg 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ring_rg (R : RingObject) : RgObject := {|
  rg_ab := ring_ab R;
  rg_mul := rig_mul R;
  rg_mul_respects := rig_mul_respects R;
  rg_mul_assoc := rig_mul_assoc R;
  rg_distr_l := rig_distr_l R;
  rg_distr_r := rig_distr_r R
|}.

(* 相关说明。 （已译） *)
Program Definition Rng_Forget_Rg : Rng ⟶ Rg := {|
  fobj := ring_rg;
  fmap := fun R S f => {|
    rg_hom_ab := {|
      cmon_map := rig_map f;
      cmon_map_zero := rig_map_zero f;
      cmon_map_plus := rig_map_add f
    |};
    rg_map_mul := rig_map_mul f
  |}
|}.
Next Obligation. intros R S f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros R a; simpl; reflexivity. Qed.
Next Obligation. intros R S T f g a; simpl; reflexivity. Qed.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Program Instance Rng_Forget_Rg_Faithful : Faithful Rng_Forget_Rg.
Next Obligation. intros R S f g Hfg a; exact (Hfg a). Qed.

(** ** The functor is not full *)

(*
   本节说明 Rg 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition rg_zero_mor (R S : RgObject) : RgHom R S := {|
  rg_hom_ab := {|
    cmon_map := {| morphism := fun _ => cmon_zero (ab_cmon (rg_ab S)) |}
  |}
|}.
Next Obligation. intros R S x y Hxy; reflexivity. Qed.
Next Obligation. intros R S; simpl; reflexivity. Qed.
Next Obligation.
  intros R S a b; simpl; symmetry; apply cmon_plus_zero_l.
Qed.
Next Obligation.
  intros R S a b; simpl; symmetry; apply rg_mul_zero_l.
Qed.

(* 相关说明。 （已译） *)
Theorem Rng_Forget_Rg_not_Full : Full Rng_Forget_Rg → False.
Proof.
  intro F.
  pose (z := rg_zero_mor (ring_rg Int_Ring) (ring_rg Int_Ring)).
  pose (g := @prefmap _ _ _ F Int_Ring Int_Ring z).
  assert (H0 : rig_map g 1%Z = 0%Z)
    by exact (@fmap_sur _ _ _ F Int_Ring Int_Ring z 1%Z).
  assert (H1 : rig_map g 1%Z = 1%Z) by exact (rig_map_one g).
  rewrite H0 in H1.
  discriminate.
Qed.

(* * ** The trivial rng zero 对象 （已译） *)

(* Built on Instance/CMon/Biproduct.v's polymorphic [CMon_trivial],
   NOT on Instance/Ab.v's [Ab_trivial], which is measured to be
   [AbObject@{Set Set Set}] with no universe binders at all. *)
Definition rg_trivial_ab@{o} : AbObject@{o o o}.
Proof.
  unshelve notypeclasses refine {|
    ab_cmon := CMon_trivial@{o};
    ab_neg  := fun _ => ttt
  |}.
  - intros x y Hxy; reflexivity.
  - intros a; reflexivity.
Defined.

Definition Rg_trivial@{o} : RgObject@{o o o}.
Proof.
  unshelve notypeclasses refine {|
    rg_ab  := rg_trivial_ab@{o};
    rg_mul := fun _ _ => ttt
  |}.
  - intros x y Hxy u v Huv; reflexivity.
  - intros a b c; reflexivity.
  - intros a b c; reflexivity.
  - intros a b c; reflexivity.
Defined.

(* Terminal: everything to the point. *)
Program Definition Rg_one@{u o} (R : RgObject@{o o o})
  : R ~{Rg@{u o}}~> Rg_trivial@{o} := {|
  rg_hom_ab := {| cmon_map := {| morphism := fun _ => ttt |} |}
|}.
Next Obligation. intros R x y Hxy; reflexivity. Qed.
Next Obligation. intros R; reflexivity. Qed.
Next Obligation. intros R a b; reflexivity. Qed.
Next Obligation. intros R a b; reflexivity. Qed.

Lemma Rg_one_unique@{u o} (R : RgObject@{o o o})
  (f : R ~{Rg@{u o}}~> Rg_trivial@{o}) : f ≈ Rg_one@{u o} R.
Proof.
  intro a; simpl.
  destruct (cmon_map (rg_hom_ab f) a); reflexivity.
Qed.

#[export] Program Instance Rg_Terminal : @Terminal Rg := {|
  terminal_obj := Rg_trivial;
  one          := Rg_one
|}.
Next Obligation.
  intros R f g.
  now rewrite (Rg_one_unique R f), (Rg_one_unique R g).
Qed.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Rg_zero_hom@{u o} (R : RgObject@{o o o})
  : Rg_trivial@{o} ~{Rg@{u o}}~> R := {|
  rg_hom_ab := {|
    cmon_map := {| morphism := fun _ => cmon_zero (ab_cmon (rg_ab R)) |}
  |}
|}.
Next Obligation. intros R x y Hxy; reflexivity. Qed.
Next Obligation. intros R; simpl; reflexivity. Qed.
Next Obligation.
  intros R a b; simpl; symmetry; apply cmon_plus_zero_l.
Qed.
Next Obligation.
  intros R a b; simpl; symmetry; apply rg_mul_zero_l.
Qed.

Lemma Rg_zero_hom_unique@{u o} (R : RgObject@{o o o})
  (f : Rg_trivial@{o} ~{Rg@{u o}}~> R) : f ≈ Rg_zero_hom@{u o} R.
Proof.
  intro a; destruct a; simpl.
  exact (cmon_map_zero (rg_hom_ab f)).
Qed.

#[export] Program Instance Rg_Initial : @Initial Rg := {|
  terminal_obj := Rg_trivial : obj[Rg^op];
  one          := Rg_zero_hom
|}.
Next Obligation.
  intros R f g.
  now rewrite (Rg_zero_hom_unique R f), (Rg_zero_hom_unique R g).
Qed.

(* One record plays both roles, so coincidence 同构 the
 恒等 — Instance/CMon/Biproduct.v Instance/Ab.v do the
 same. （已译） *)
#[export] Instance Rg_Zero : ZeroObject Rg :=
  @Build_ZeroObject Rg Rg_Terminal Rg_Initial iso_id.

(* * ** The contrast unital 范畴 （已译） *)

(*
   本节说明始/终对象、核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Rng_terminal_not_initial :
  (Zero_Ring ~{Rng}~> Int_Ring) → False.
Proof.
  intro f.
  assert (H1 : rig_map f ttt = 1%Z) by exact (rig_map_one f).
  assert (H0 : rig_map f ttt = 0%Z) by exact (rig_map_zero f).
  rewrite H1 in H0.
  discriminate.
Qed.

(*
   本节说明始/终对象、核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Rng_Rg_zero_object_contrast :
  ZeroObject Rg * ((Zero_Ring ~{Rng}~> Int_Ring) → False) :=
  (Rg_Zero, Rng_terminal_not_initial).

(** ** Strict readbacks *)

Example rg_forget_ab_strict (R : RingObject) :
  rg_ab (ring_rg R) = ring_ab R := eq_refl.

Example rg_forget_mul_strict (R : RingObject) :
  rg_mul (ring_rg R) = rig_mul R := eq_refl.

Example rg_forget_carrier_strict (R : RingObject) :
  carrier (cmon_setoid (ab_cmon (rg_ab (ring_rg R))))
    = carrier (rig_setoid R) := eq_refl.

Example rg_forget_zero_strict (R : RingObject) :
  cmon_zero (ab_cmon (rg_ab (ring_rg R))) = rig_zero R := eq_refl.

Example rg_zero_obj_strict :
  @zero_obj Rg Rg_Zero = Rg_trivial := eq_refl.

Example rg_trivial_carrier_strict :
  carrier (cmon_setoid (ab_cmon (rg_ab Rg_trivial))) = poly_unit := eq_refl.

(* 相关说明。 （已译） *)

(*
   本节说明 Rg 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition probe_zero_ring_is_trivial :
  ring_rg Zero_Ring = Rg_trivial := eq_refl.

Example control_zero_ring_carrier :
  carrier (cmon_setoid (ab_cmon (rg_ab (ring_rg Zero_Ring))))
    = carrier (cmon_setoid (ab_cmon (rg_ab Rg_trivial))) := eq_refl.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition probe_forget_hom_record (R S : RingObject)
  (f : R ~{Rng}~> S) : fmap[Rng_Forget_Rg] f = f := eq_refl.

Example control_forget_underlying_map (R S : RingObject)
  (f : R ~{Rng}~> S) :
  cmon_map (rg_hom_ab (fmap[Rng_Forget_Rg] f)) = rig_map f := eq_refl.

(* 相关说明。 （已译） *)

(*
   本节说明 Rg 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition TwoZ_mul (a b : Z) : Z := 2 * a * b.

Lemma TwoZ_assoc_Z (a b c : Z) :
  TwoZ_mul (TwoZ_mul a b) c = TwoZ_mul a (TwoZ_mul b c).
Proof. unfold TwoZ_mul; ring. Qed.

Lemma TwoZ_distr_l_Z (a b c : Z) :
  TwoZ_mul a (Z.add b c) = Z.add (TwoZ_mul a b) (TwoZ_mul a c).
Proof. unfold TwoZ_mul; ring. Qed.

Lemma TwoZ_distr_r_Z (a b c : Z) :
  TwoZ_mul (Z.add a b) c = Z.add (TwoZ_mul a c) (TwoZ_mul b c).
Proof. unfold TwoZ_mul; ring. Qed.

(*
   本节说明 Rg 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition TwoZ_Rg : RgObject := {|
  rg_ab  := ring_ab Int_Ring;
  rg_mul := TwoZ_mul
|}.
Next Obligation. exact TwoZ_assoc_Z. Qed.
Next Obligation. exact TwoZ_distr_l_Z. Qed.
Next Obligation. exact TwoZ_distr_r_Z. Qed.

(* 相关说明。 （已译） *)
Theorem TwoZ_not_unital :
  ∀ e : carrier (cmon_setoid (ab_cmon (rg_ab TwoZ_Rg))),
    (∀ a, rg_mul TwoZ_Rg e a ≈ a) → False.
Proof.
  intros e H.
  assert (H1 : TwoZ_mul e 1%Z = 1%Z) by exact (H 1%Z).
  unfold TwoZ_mul in H1.
  lia.
Qed.

(* Not degenerate: the carrier has two distinct elements. *)
Theorem TwoZ_nondegenerate :
  (0%Z : carrier (cmon_setoid (ab_cmon (rg_ab TwoZ_Rg))))
    ≈ (1%Z : carrier (cmon_setoid (ab_cmon (rg_ab TwoZ_Rg)))) → False.
Proof. intro H; unfold Z_eqT in H; discriminate. Qed.

(*
   本节说明 Rg 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem TwoZ_mul_nonzero :
  rg_mul TwoZ_Rg 1%Z 1%Z
    ≈ cmon_zero (ab_cmon (rg_ab TwoZ_Rg)) → False.
Proof. intro H; unfold Z_eqT in H; discriminate. Qed.

(*
   本节说明 Rg 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition TwoZ_double (z : Z) : Z := 2 * z.

Lemma TwoZ_double_add (a b : Z) :
  TwoZ_double (Z.add a b) = Z.add (TwoZ_double a) (TwoZ_double b).
Proof. unfold TwoZ_double; ring. Qed.

Lemma TwoZ_double_mul (a b : Z) :
  TwoZ_double (TwoZ_mul a b) = Z.mul (TwoZ_double a) (TwoZ_double b).
Proof. unfold TwoZ_double, TwoZ_mul; ring. Qed.

Program Definition TwoZ_incl : RgHom TwoZ_Rg (ring_rg Int_Ring) := {|
  rg_hom_ab := {| cmon_map := {| morphism := TwoZ_double |} |}
|}.
Next Obligation. exact (@eq_refl Z 0%Z). Qed.
Next Obligation. exact TwoZ_double_add. Qed.
Next Obligation. exact TwoZ_double_mul. Qed.

Theorem TwoZ_incl_injective : ∀ a b,
  cmon_map (rg_hom_ab TwoZ_incl) a ≈ cmon_map (rg_hom_ab TwoZ_incl) b →
  a ≈ b.
Proof.
  intros a b H.
  assert (H2 : TwoZ_double a = TwoZ_double b) by exact H.
  unfold TwoZ_double in H2.
  assert (Hab : a = b) by lia.
  exact Hab.
Qed.

Theorem TwoZ_incl_image_even : ∀ a,
  { k : Z & cmon_map (rg_hom_ab TwoZ_incl) a = Z.mul 2 k }.
Proof. intro a; exists a; exact (@eq_refl Z (TwoZ_double a)). Qed.

(* 相关说明。 （已译） *)
Theorem TwoZ_incl_image_onto_even : ∀ k : Z,
  { a & cmon_map (rg_hom_ab TwoZ_incl) a = Z.mul 2 k }.
Proof. intro k; exists k; exact (@eq_refl Z (TwoZ_double k)). Qed.

(* 相关说明。 （已译） *)

Set Printing Universes.
About Rg_trivial.
About Rg_Zero.
Unset Printing Universes.
