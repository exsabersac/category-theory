Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Subobject.
Require Import Category.Structure.WellPowered.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.Epi.

Generalizable All Variables.

(** * Grp is well-powered one universe up *)

(*
 Wikipedia: https://en.wikipedia.org/wiki/Subgroup

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The image of a homomorphism as a [Subgroup]; its membership is
   Instance/Grp/Epi.v's [GrpImage], a [Type]-valued "has a preimage". *)
Definition grp_image_subgroup {G H : Grp} (f : G ~{Grp}~> H) : Subgroup H :=
  {| sub_mem  := GrpImage f ;
     sub_resp := GrpImage_respects f ;
     sub_unit := GrpImage_unit f ;
     sub_mul  := GrpImage_mul f ;
     sub_inv  := GrpImage_inv f |}.

(* The subobject a subgroup names: its inclusion. *)
Definition grp_sub_of_subgroup (G : Grp) (S : Subgroup G) : SubObj G :=
  @Build_SubObj Grp G (SubgroupGrp S) (sub_incl S) (sub_incl_monic S).

Section GrpToFrom.

Context (G : Grp) (u : SubObj G).

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition grp_image_fwd :
  SubgroupGrp (grp_image_subgroup (sub_mono u)) ~{Grp}~> sub_dom u := {|
  grp_map := {| morphism := fun p => `1 (`2 p) |}
|}.
Next Obligation.
  intros [b [a Ha]] [b' [a' Ha']] H; simpl in *.
  apply (snd (Grp_injectivity_is_monic (sub_mono u)) (sub_is_monic u)).
  rewrite Ha, Ha'. exact H.
Qed.
Next Obligation.
  apply (snd (Grp_injectivity_is_monic (sub_mono u)) (sub_is_monic u)).
  rewrite (projT2 (GrpImage_unit (sub_mono u))).
  symmetry. apply (grp_map_unit (sub_mono u)).
Qed.
Next Obligation.
  apply (snd (Grp_injectivity_is_monic (sub_mono u)) (sub_is_monic u)).
  rewrite (grp_map_mul (sub_mono u)).
  rewrite (projT2 (GrpImage_mul (sub_mono u) _ _ (projT2 a) (projT2 b))).
  destruct a as [b1 [x Hx]], b as [b2 [y Hy]]; simpl.
  rewrite Hx, Hy. reflexivity.
Qed.

Program Definition grp_image_bwd :
  sub_dom u ~{Grp}~> SubgroupGrp (grp_image_subgroup (sub_mono u)) := {|
  grp_map := {| morphism := fun a =>
      existT (fun b => GrpImage (sub_mono u) b) (sub_mono u a)
             (existT (fun a' => @equiv _ (is_setoid (grp_setoid G))
                                        (sub_mono u a') (sub_mono u a)) a
                     (@Equivalence_Reflexive _ _
                        (@setoid_equiv _ (is_setoid (grp_setoid G)))
                        (sub_mono u a))) |}
|}.
Next Obligation. intros a a' H; simpl. apply proper_morphism; exact H. Qed.
Next Obligation. apply (grp_map_unit (sub_mono u)). Qed.
Next Obligation. apply (grp_map_mul (sub_mono u)). Qed.

Definition grp_image_iso :
  @Isomorphism Grp (SubgroupGrp (grp_image_subgroup (sub_mono u))) (sub_dom u).
Proof.
  unshelve refine (@Build_Isomorphism Grp _ _ grp_image_fwd grp_image_bwd _ _).
  - intro a; simpl; reflexivity.
  - intros [b [a Ha]]; simpl. exact Ha.
Defined.

Definition grp_image_to_from :
  grp_sub_of_subgroup G (grp_image_subgroup (sub_mono u)) ≈ u.
Proof.
  exists grp_image_iso.
  intros [b [a Ha]]; simpl. exact Ha.
Defined.

End GrpToFrom.

Definition Grp_WellPoweredAt_up (G : Grp) : WellPoweredAt G :=
  {| wp_index   := Subgroup G ;
     wp_to      := grp_sub_of_subgroup G ;
     wp_from    := fun u => grp_image_subgroup (sub_mono u) ;
     wp_to_from := grp_image_to_from G |}.
