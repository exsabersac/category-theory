Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Heunen_Vicary.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Structure.Monoid.
Require Import Category.Structure.Group.
Require Import Category.Theory.EckmannHilton.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Epi.

Generalizable All Variables.

(*
   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Local Set Default Proof Using "All".

(* * * Group 对象 Grp abelian groups （已译） *)

(*
   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   Paper: Eckmann, Hilton, "Structure maps in group theory", Fundamenta
   nLab:  https://ncatlab.org/nlab/show/Eckmann-Hilton+argument
   nLab:  https://ncatlab.org/nlab/show/group+object

   本节说明 EckmannHilton 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 EckmannHilton 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明幺半结构、hom、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 EckmannHilton 相关定义、性质与动机。

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

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明hom、始/终对象、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 EckmannHilton 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明函子、（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* * ** The ambient 范畴 cartesian monoidal structure （已译） *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Monomorphic Universe gu.

Definition GrpS : Category := Grp@{gu Set}.

Definition GrpCM : @CartesianMonoidal GrpS :=
  @CC_CartesianMonoidal GrpS Grp_Cartesian Grp_Terminal.

Definition GrpMon : @Monoidal GrpS := GrpCM.

Definition GrpTensor := @tensor GrpS GrpMon.

(* The tensor IS Instance/Grp.v's own direct product, tensor unit
 IS own trivial group -- [eq_refl], so no comparison 态射 is
 needed anywhere below. （已译） *)
Example grp_tensor_is_product (G H : GrpS) :
  @fobj _ _ GrpTensor (G, H) = Grp_product G H := eq_refl.

Example grp_tensor_unit_is_trivial :
  @Category.Structure.Monoidal.I GrpS GrpMon = Grp_trivial := eq_refl.

(** ** Abelian groups *)

Definition AbelianGrp (G : GrpS) : Type :=
  ∀ a b : carrier G, grp_mul G a b ≈ grp_mul G b a.

(* * ** Half (b): group 对象 Grp abelian （已译） *)

Section GroupObjectInGrp.

Context (G : GrpS).
Context (GO : @GroupObject GrpS GrpCM G).

Definition gob_monoid : @MonoidObject GrpS GrpMon G :=
  @groupobject_is_monoid GrpS GrpCM G GO.

(* The three structure 态射, read elementwise. [gmul2] SECOND
 multiplication -- internal one -- opposed [grp_mul G], which
 group's own. （已译） *)
Definition gmul2 (a b : carrier G) : carrier G :=
  grp_map (@mappend GrpS GrpMon G gob_monoid) (a, b).

Definition gunit2 : carrier G :=
  grp_map (@mempty GrpS GrpMon G gob_monoid) ttt.

Definition ginv2 (a : carrier G) : carrier G :=
  grp_map (@Category.Structure.Group.inverse GrpS GrpCM G GO) a.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma gmul2_respects : Proper (equiv ==> equiv ==> equiv) gmul2.
Proof.
  intros a a' Ha b b' Hb.
  unfold gmul2.
  apply proper_morphism.
  split; assumption.
Qed.

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma gmul2_unit_left (a : carrier G) : gmul2 gunit2 a ≈ a.
Proof. exact (@mempty_left GrpS GrpMon G gob_monoid (ttt, a)). Qed.

Lemma gmul2_unit_right (a : carrier G) : gmul2 a gunit2 ≈ a.
Proof. exact (@mempty_right GrpS GrpMon G gob_monoid (a, ttt)). Qed.

(*
   本节说明 EckmannHilton 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma gob_interchange (a b c d : carrier G) :
  gmul2 (grp_mul G a b) (grp_mul G c d)
    ≈ grp_mul G (gmul2 a c) (gmul2 b d).
Proof.
  exact (grp_map_mul (@mappend GrpS GrpMon G gob_monoid) (a, c) (b, d)).
Qed.

(* Input 5 is [grp_mul G]'s own unit and respectfulness data, which
   Instance/Grp.v already supplies: [grp_mul_respects] is a field,
   [grp_mul_unit_l] is a field, and [grp_mul_unit_r] is derived there. *)

(* Eckmann-Hilton, output 1: the two units coincide. *)
Theorem gob_units_agree : gunit2 ≈ grp_unit G.
Proof.
  exact (eh_units gmul2 (grp_mul G) gunit2 (grp_unit G)
           gmul2_respects (grp_mul_respects G)
           gmul2_unit_left gmul2_unit_right
           (grp_mul_unit_l G) (grp_mul_unit_r G)
           gob_interchange).
Qed.

(* Output 2: the two multiplications coincide. *)
Theorem gob_mul_agrees (a b : carrier G) : gmul2 a b ≈ grp_mul G a b.
Proof.
  exact (eh_ops gmul2 (grp_mul G) gunit2 (grp_unit G)
           gmul2_respects (grp_mul_respects G)
           gmul2_unit_left gmul2_unit_right
           (grp_mul_unit_l G) (grp_mul_unit_r G)
           gob_interchange a b).
Qed.

(* Output 3, the internal reading of commutativity. *)
Theorem gob_mul_comm (a b : carrier G) : gmul2 a b ≈ gmul2 b a.
Proof.
  exact (eh_comm gmul2 (grp_mul G) gunit2 (grp_unit G)
           gmul2_respects (grp_mul_respects G)
           gmul2_unit_left gmul2_unit_right
           (grp_mul_unit_l G) (grp_mul_unit_r G)
           gob_interchange a b).
Qed.

(* 相关说明。 （已译） *)
Theorem group_object_abelian : AbelianGrp G.
Proof.
  exact (eh_g_comm gmul2 (grp_mul G) gunit2 (grp_unit G)
           gmul2_respects (grp_mul_respects G)
           gmul2_unit_left gmul2_unit_right
           (grp_mul_unit_l G) (grp_mul_unit_r G)
           gob_interchange).
Qed.

(* 相关说明。 （已译） *)
Lemma gob_inv_left (a : carrier G) : gmul2 (ginv2 a) a ≈ gunit2.
Proof. exact (@left_inverse GrpS GrpCM G GO a). Qed.

Lemma gob_inv_right (a : carrier G) : gmul2 a (ginv2 a) ≈ gunit2.
Proof. exact (@right_inverse GrpS GrpCM G GO a). Qed.

(*
   本节说明 EckmannHilton 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem gob_inv_agrees (a : carrier G) : ginv2 a ≈ grp_inv G a.
Proof.
  apply grp_inv_unique_l.
  rewrite <- gob_mul_agrees.
  rewrite gob_inv_left.
  apply gob_units_agree.
Qed.

(* "Every group 对象 Grp arises way", packaged: all three
 structure 态射 group's own. （已译） *)
Definition group_object_structure_forced :
  (∀ a b : carrier G, gmul2 a b ≈ grp_mul G a b)
    ∧ (gunit2 ≈ grp_unit G)
    ∧ (∀ a : carrier G, ginv2 a ≈ grp_inv G a) :=
  (gob_mul_agrees, (gob_units_agree, gob_inv_agrees)).

End GroupObjectInGrp.

(* * ** Uniqueness group-对象 structure （已译） *)

(* Because every group-对象 structure [G] [G]'s own structure,
 any two them agree. This content "arises way" a
 bare biconditional does not carry. （已译） *)

Theorem group_object_mul_unique (G : GrpS)
        (GO GO' : @GroupObject GrpS GrpCM G) (a b : carrier G) :
  gmul2 G GO a b ≈ gmul2 G GO' a b.
Proof.
  rewrite gob_mul_agrees.
  symmetry.
  apply gob_mul_agrees.
Qed.

Theorem group_object_unit_unique (G : GrpS)
        (GO GO' : @GroupObject GrpS GrpCM G) :
  gunit2 G GO ≈ gunit2 G GO'.
Proof.
  rewrite gob_units_agree.
  symmetry.
  apply gob_units_agree.
Qed.

Theorem group_object_inverse_unique (G : GrpS)
        (GO GO' : @GroupObject GrpS GrpCM G) (a : carrier G) :
  ginv2 G GO a ≈ ginv2 G GO' a.
Proof.
  rewrite gob_inv_agrees.
  symmetry.
  apply gob_inv_agrees.
Qed.

(* * ** Half (a): abelian group group 对象 Grp （已译） *)

Section AbelianIsGroupObject.

Context (G : GrpS).
Context (HA : AbelianGrp G).

(*
   本节说明 EckmannHilton 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ab_mappend : Grp_product G G ~{GrpS}~> G.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom (Grp_product G G) G
       {| morphism := fun p => grp_mul G (fst p) (snd p) |} _ _).
  - intros p q Hpq.
    destruct Hpq as [H1 H2]; simpl in *.
    now rewrite H1, H2.
  - simpl.
    apply grp_mul_unit_l.
  - intros [a b] [c d]; simpl.
    rewrite !grp_mul_assoc.
    apply grp_mul_respects; [reflexivity |].
    rewrite <- !grp_mul_assoc.
    apply grp_mul_respects; [| reflexivity].
    apply HA.
Defined.

(*
   本节说明 EckmannHilton 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition grp_ab_inverse : G ~{GrpS}~> G.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom G G {| morphism := grp_inv G |} _ _).
  - intros a b Hab.
    now rewrite Hab.
  - apply grp_inv_unit.
  - intros a b; simpl.
    rewrite grp_inv_mul.
    apply HA.
Defined.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ab_MonoidObject : @MonoidObject GrpS GrpMon G.
Proof.
  unshelve notypeclasses refine
    (@Build_MonoidObject GrpS GrpMon G (Grp_zero_hom G) ab_mappend _ _ _).
  - intros [u a]; simpl.
    apply grp_mul_unit_l.
  - intros [a u]; simpl.
    apply grp_mul_unit_r.
  - intros [[a b] c]; simpl.
    apply grp_mul_assoc.
Defined.

(*
   本节说明 EckmannHilton 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition abelian_GroupObject : @GroupObject GrpS GrpCM G.
Proof.
  unshelve notypeclasses refine
    (@Build_GroupObject GrpS GrpCM G ab_MonoidObject grp_ab_inverse _ _).
  - intro a; simpl.
    apply grp_mul_inv_l.
  - intro a; simpl.
    apply grp_mul_inv_r.
Defined.

End AbelianIsGroupObject.

(** ** Mac Lane's Exercise 4 *)

(* 相关说明。 （已译） *)
Definition abelian_iff_group_object (G : GrpS) :
  AbelianGrp G ↔ @GroupObject GrpS GrpCM G :=
  (abelian_GroupObject G, group_object_abelian G).

(* 相关说明。 （已译） *)
Definition maclane_III_6_ex4 (G : GrpS) :
  (AbelianGrp G ↔ @GroupObject GrpS GrpCM G)
    ∧ (∀ GO : @GroupObject GrpS GrpCM G,
         (∀ a b : carrier G, gmul2 G GO a b ≈ grp_mul G a b)
           ∧ (gunit2 G GO ≈ grp_unit G)
           ∧ (∀ a : carrier G, ginv2 G GO a ≈ grp_inv G a)) :=
  (abelian_iff_group_object G, group_object_structure_forced G).

(* 相关说明。 （已译） *)

(*
   本节说明 EckmannHilton 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example abelian_roundtrip_mul (G : GrpS) (HA : AbelianGrp G)
        (a b : carrier G) :
  gmul2 G (abelian_GroupObject G HA) a b = grp_mul G a b := eq_refl.

Example abelian_roundtrip_unit (G : GrpS) (HA : AbelianGrp G) :
  gunit2 G (abelian_GroupObject G HA) = grp_unit G := eq_refl.

Example abelian_roundtrip_inv (G : GrpS) (HA : AbelianGrp G)
        (a : carrier G) :
  ginv2 G (abelian_GroupObject G HA) a = grp_inv G a := eq_refl.

(*
   本节说明 EckmannHilton 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem group_object_roundtrip_mul (G : GrpS)
        (GO : @GroupObject GrpS GrpCM G) (a b : carrier G) :
  gmul2 G (abelian_GroupObject G (group_object_abelian G GO)) a b
    ≈ gmul2 G GO a b.
Proof.
  symmetry.
  apply gob_mul_agrees.
Qed.

Theorem group_object_roundtrip_unit (G : GrpS)
        (GO : @GroupObject GrpS GrpCM G) :
  gunit2 G (abelian_GroupObject G (group_object_abelian G GO))
    ≈ gunit2 G GO.
Proof.
  symmetry.
  apply gob_units_agree.
Qed.

Theorem group_object_roundtrip_inv (G : GrpS)
        (GO : @GroupObject GrpS GrpCM G) (a : carrier G) :
  ginv2 G (abelian_GroupObject G (group_object_abelian G GO)) a
    ≈ ginv2 G GO a.
Proof.
  symmetry.
  apply gob_inv_agrees.
Qed.

(** ** Non-vacuity *)

(* The degenerate case first, and proved degenerate: the trivial group is
   abelian, so it carries a group-object structure, but every pair of its
   elements is identified, so nothing about it separates anything. *)

Lemma trivial_abelian : AbelianGrp Grp_trivial.
Proof.
  intros a b.
  reflexivity.
Qed.

Definition trivial_GroupObject : @GroupObject GrpS GrpCM Grp_trivial :=
  abelian_GroupObject Grp_trivial trivial_abelian.

Lemma trivial_GroupObject_degenerate (a b : carrier Grp_trivial) : a ≈ b.
Proof.
  destruct a, b.
  reflexivity.
Qed.

(* Z/2, Instance/Grp.v's own witness, reused rather than rebuilt. *)

Lemma Z2_abelian : AbelianGrp Z2.
Proof.
  intros a b; simpl.
  destruct a, b; reflexivity.
Qed.

Definition Z2_GroupObject : @GroupObject GrpS GrpCM Z2 :=
  abelian_GroupObject Z2 Z2_abelian.

(* The group-object structure on Z/2 COMPUTES. *)

Example Z2_gob_mul_tt : gmul2 Z2 Z2_GroupObject true true = false :=
  eq_refl.

Example Z2_gob_mul_tf : gmul2 Z2 Z2_GroupObject true false = true :=
  eq_refl.

Example Z2_gob_unit : gunit2 Z2 Z2_GroupObject = false := eq_refl.

Example Z2_gob_inv : ginv2 Z2 Z2_GroupObject true = true := eq_refl.

(* And it not degenerate: multiplication not 常值, the
 carrier has two provably distinct elements ([Z2_nontrivial] is
 Instance/Grp.v's). （已译） *)

Lemma Z2_gob_not_constant :
  gmul2 Z2 Z2_GroupObject true true ≈ gmul2 Z2 Z2_GroupObject true false
    → False.
Proof.
  simpl.
  discriminate.
Qed.

Lemma Z2_GroupObject_nondegenerate :
  (∀ a b : carrier Z2, a ≈ b) → False.
Proof.
  intro Hall.
  exact (Z2_nontrivial (Hall true false)).
Qed.

(*
   本节说明 EckmannHilton 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Sym3 : GrpS := GrpSym3.

Lemma Sym3_not_abelian : AbelianGrp Sym3 → False.
Proof.
  intro H.
  exact (H sym3_s sym3_a sym3_l0).
Qed.

Theorem Sym3_no_group_object : @GroupObject GrpS GrpCM Sym3 → False.
Proof.
  intro GO.
  exact (Sym3_not_abelian (group_object_abelian Sym3 GO)).
Qed.

(** ** Probes *)

(*
   本节说明 EckmannHilton 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ProbeUniversePin.

Universe pu ph.
Constraint Set < ph.

(*
   本节说明hom、笛卡尔、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ctrl_probe_category : Category := Grp@{pu ph}.

Definition ctrl_probe_cartesian : @Cartesian Grp@{pu ph} := Grp_Cartesian.

Definition ctrl_probe_terminal : @Terminal GrpS := Grp_Terminal.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (Grp_Terminal : @Terminal Grp@{pu ph}).

(* FORMABILITY (universe), 2 of 2, a CONTROL since #450.  The rejection
   used to propagate to the cartesian monoidal structure, reported at
   [Grp_Terminal]; since #450 the structure is formable at [Grp@{pu ph}]. *)
Check (@CC_CartesianMonoidal Grp@{pu ph} Grp_Cartesian Grp_Terminal
       : @CartesianMonoidal Grp@{pu ph}).

End ProbeUniversePin.

(* TYPING.  [GroupObject] wants a [CartesianMonoidal]; [GrpMon] is only a
   [Monoidal].  "The term GrpMon has type Monoidal while it is expected to
   have type CartesianMonoidal." *)
Definition ctrl_probe_groupobject : Type := @GroupObject GrpS GrpCM Z2.

Fail Definition probe_needs_cartesian : Type :=
  @GroupObject GrpS GrpMon Z2.

(*
   本节说明 EckmannHilton 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example ctrl_probe_mul_agrees (G : GrpS)
        (GO : @GroupObject GrpS GrpCM G) (a b : carrier G) :
  gmul2 G GO a b ≈ grp_mul G a b := gob_mul_agrees G GO a b.

Fail Example probe_mul_strict (G : GrpS)
        (GO : @GroupObject GrpS GrpCM G) (a b : carrier G) :
  gmul2 G GO a b = grp_mul G a b := eq_refl.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example probe_record_roundtrip (G : GrpS)
        (GO : @GroupObject GrpS GrpCM G) :
  abelian_GroupObject G (group_object_abelian G GO) = GO := eq_refl.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example probe_other_roundtrip (G : GrpS) (HA : AbelianGrp G) :
  group_object_abelian G (abelian_GroupObject G HA) = HA := eq_refl.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example eh_probe_instrument : true = true := eq_refl.

Fail Example probe_instrument_neg : true = false := eq_refl.
