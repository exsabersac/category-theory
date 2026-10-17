Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.

Generalizable All Variables.

(*
    nLab: https://ncatlab.org/nlab/show/limit

   本文件给出极限相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Definition alimit_cone `{F : J ⟶ C} {c : C} (H : IsALimit F c) : Cone F :=
  {| vertex_obj := c; coneFrom := @limit_acone _ _ _ _ H |}.

(* 相关说明。 （已译） *)
Example alimit_cone_leg `{F : J ⟶ C} {c : C} (H : IsALimit F c) (x : J) :
  cone_leg (alimit_cone H) x = limit_leg H x := eq_refl.

Definition acolimit_cocone `{F : J ⟶ C} {c : C} (H : IsAColimit F c) :
  Cocone F :=
  @Build_Cone (J^op) (C^op) (F^op) c (@limit_acone _ _ _ _ H).

Example acolimit_cocone_inj `{F : J ⟶ C} {c : C} (H : IsAColimit F c)
  (x : J) : cocone_inj (acolimit_cocone H) x = colimit_inj H x := eq_refl.

(** ** Proposition 3.1.7, limits *)

Section LimitUnique.

Context {J : Category}.
Context {C : Category}.
Context {F : J ⟶ C}.
Context {c d : C}.
Context (Hc : IsALimit F c) (Hd : IsALimit F d).

Definition limit_unique_to : c ~{C}~> d := limit_med Hd (alimit_cone Hc).
Definition limit_unique_from : d ~{C}~> c := limit_med Hc (alimit_cone Hd).

Lemma limit_unique_to_legs (x : J) :
  limit_leg Hd x ∘ limit_unique_to ≈ limit_leg Hc x.
Proof. exact (limit_med_commutes Hd (alimit_cone Hc) x). Qed.

Lemma limit_unique_from_legs (x : J) :
  limit_leg Hc x ∘ limit_unique_from ≈ limit_leg Hd x.
Proof. exact (limit_med_commutes Hc (alimit_cone Hd) x). Qed.

Lemma limit_unique_from_to : limit_unique_from ∘ limit_unique_to ≈ id.
Proof.
  apply (limit_med_eq Hc (alimit_cone Hc)); intro x.
  - transitivity ((limit_leg Hc x ∘ limit_unique_from) ∘ limit_unique_to).
    { apply comp_assoc. }
    transitivity (limit_leg Hd x ∘ limit_unique_to).
    { now rewrite limit_unique_from_legs. }
    exact (limit_unique_to_legs x).
  - apply id_right.
Qed.

Lemma limit_unique_to_from : limit_unique_to ∘ limit_unique_from ≈ id.
Proof.
  apply (limit_med_eq Hd (alimit_cone Hd)); intro x.
  - transitivity ((limit_leg Hd x ∘ limit_unique_to) ∘ limit_unique_from).
    { apply comp_assoc. }
    transitivity (limit_leg Hc x ∘ limit_unique_from).
    { now rewrite limit_unique_to_legs. }
    exact (limit_unique_from_legs x).
  - apply id_right.
Qed.

(* The isomorphism of apexes... *)
Definition limit_unique_iso : c ≅ d := {|
  to := limit_unique_to;
  from := limit_unique_from;
  iso_to_from := limit_unique_to_from;
  iso_from_to := limit_unique_from_to
|}.

(* ...carrying leg-commutation equations both directions — the
 同构 "commutes legs two limit cones", not a
 bare ≅. （已译） *)
Definition limit_unique_iso_legs :
  (∀ x : J, limit_leg Hd x ∘ to limit_unique_iso ≈ limit_leg Hc x) *
  (∀ x : J, limit_leg Hc x ∘ from limit_unique_iso ≈ limit_leg Hd x) :=
  (limit_unique_to_legs, limit_unique_from_legs).

(* The uniqueness clause — Riehl's content: ANY 态射 commuting with
 two leg families 同构. （已译） *)
Theorem limit_unique_iso_unique (h : c ~{C}~> d) :
  (∀ x : J, limit_leg Hd x ∘ h ≈ limit_leg Hc x) →
  h ≈ to limit_unique_iso.
Proof.
  intro Hh; symmetry.
  exact (limit_med_unique Hd (alimit_cone Hc) h Hh).
Qed.

End LimitUnique.

(* The accompanying remark, at single witness: endomorphism
 apex commuting fixed limit cone 恒等. （已译） *)
Theorem limit_endo_id `{F : J ⟶ C} {c : C} (H : IsALimit F c)
  (e : c ~{C}~> c) :
  (∀ x : J, limit_leg H x ∘ e ≈ limit_leg H x) → e ≈ id.
Proof.
  intro He.
  apply (limit_med_eq H (alimit_cone H)); intro x.
  - exact (He x).
  - apply id_right.
Qed.

(* 相关说明。 （已译） *)

Section ColimitUnique.

Context {J : Category}.
Context {C : Category}.
Context {F : J ⟶ C}.
Context {c d : C}.
Context (Hc : IsAColimit F c) (Hd : IsAColimit F d).

Definition colimit_unique_to : c ~{C}~> d :=
  @limit_unique_from (J^op) (C^op) (F^op) c d Hc Hd.
Definition colimit_unique_from : d ~{C}~> c :=
  @limit_unique_to (J^op) (C^op) (F^op) c d Hc Hd.

(* The colimit mediator IS opposite limit mediator, definitionally
 — sense section adds no 证明 content. （已译） *)
Example colimit_unique_to_is_op :
  colimit_unique_to = @limit_unique_from (J^op) (C^op) (F^op) c d Hc Hd
  := eq_refl.

Lemma colimit_unique_to_injs (x : J) :
  colimit_unique_to ∘ colimit_inj Hc x ≈ colimit_inj Hd x.
Proof. exact (@limit_unique_from_legs (J^op) (C^op) (F^op) c d Hc Hd x). Qed.

Lemma colimit_unique_from_injs (x : J) :
  colimit_unique_from ∘ colimit_inj Hd x ≈ colimit_inj Hc x.
Proof. exact (@limit_unique_to_legs (J^op) (C^op) (F^op) c d Hc Hd x). Qed.

Lemma colimit_unique_from_to :
  colimit_unique_from ∘ colimit_unique_to ≈ id.
Proof. exact (@limit_unique_from_to (J^op) (C^op) (F^op) c d Hc Hd). Qed.

Lemma colimit_unique_to_from :
  colimit_unique_to ∘ colimit_unique_from ≈ id.
Proof. exact (@limit_unique_to_from (J^op) (C^op) (F^op) c d Hc Hd). Qed.

Definition colimit_unique_iso : c ≅ d := {|
  to := colimit_unique_to;
  from := colimit_unique_from;
  iso_to_from := colimit_unique_to_from;
  iso_from_to := colimit_unique_from_to
|}.

Definition colimit_unique_iso_injs :
  (∀ x : J, to colimit_unique_iso ∘ colimit_inj Hc x ≈ colimit_inj Hd x) *
  (∀ x : J, from colimit_unique_iso ∘ colimit_inj Hd x ≈ colimit_inj Hc x) :=
  (colimit_unique_to_injs, colimit_unique_from_injs).

Theorem colimit_unique_iso_unique (h : c ~{C}~> d) :
  (∀ x : J, h ∘ colimit_inj Hc x ≈ colimit_inj Hd x) →
  h ≈ to colimit_unique_iso.
Proof.
  exact (@limit_unique_iso_unique (J^op) (C^op) (F^op) d c Hd Hc h).
Qed.

End ColimitUnique.

Theorem colimit_endo_id `{F : J ⟶ C} {c : C} (H : IsAColimit F c)
  (e : c ~{C}~> c) :
  (∀ x : J, e ∘ colimit_inj H x ≈ colimit_inj H x) → e ≈ id.
Proof. exact (@limit_endo_id (J^op) (C^op) (F^op) c H e). Qed.
