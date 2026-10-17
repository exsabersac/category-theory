Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Eval.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.

Generalizable All Variables.

(* * * Pointwise limits 函子 范畴 （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/functor+category

   本文件给出极限实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Pointwise.

Context {J P X : Category}.
Context (D : J ⟶ [P, X]).

(* The 假设 Mac Lane's Theorem 1: each evaluation diagram
 has limit X. （已译） *)
Context (L : ∀ p : P, Limit (Eval p ◯ D)).

(** ** The pointwise data *)

Definition plim_obj (p : P) : X := vertex_obj[@limit_cone _ _ _ (L p)].

Definition plim_alimit (p : P) : IsALimit (Eval p ◯ D) (plim_obj p) :=
  limit_is_alimit (L p).

Definition plim_leg (p : P) (j : J) : plim_obj p ~{X}~> fobj[D j] p :=
  limit_leg (plim_alimit p) j.

Lemma plim_leg_coherence (p : P) {i j : J} (g : i ~{J}~> j) :
  transform[fmap[D] g] p ∘ plim_leg p i ≈ plim_leg p j.
Proof. exact (limit_leg_coherence (plim_alimit p) g). Qed.

(* 相关说明。 （已译） *)
Program Definition plim_probe_cone {q : P} {c : X} (u : c ~{X}~> plim_obj q) :
  Cone (Eval q ◯ D) := {|
  vertex_obj := c;
  coneFrom := {| vertex_map := fun j => plim_leg q j ∘ u |}
|}.
Next Obligation.
  rewrite comp_assoc.
  now rewrite plim_leg_coherence.
Qed.

Lemma plim_jointly_monic {q : P} {c : X} (u v : c ~{X}~> plim_obj q) :
  (∀ j : J, plim_leg q j ∘ u ≈ plim_leg q j ∘ v) → u ≈ v.
Proof.
  intro H.
  apply (limit_med_eq (plim_alimit q) (plim_probe_cone u) u v);
    intro x; [reflexivity | symmetry; apply H].
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition plim_cone_at {p q : P} (f : p ~{P}~> q) :
  Cone (Eval q ◯ D) := {|
  vertex_obj := plim_obj p;
  coneFrom := {| vertex_map := fun j => fmap[D j] f ∘ plim_leg p j |}
|}.
Next Obligation.
  rewrite comp_assoc.
  rewrite <- (naturality[fmap[D] f0] p q f).
  rewrite <- comp_assoc.
  now rewrite plim_leg_coherence.
Qed.

Definition plim_map {p q : P} (f : p ~{P}~> q) : plim_obj p ~{X}~> plim_obj q :=
  limit_med (plim_alimit q) (plim_cone_at f).

Lemma plim_map_commutes {p q : P} (f : p ~{P}~> q) (j : J) :
  plim_leg q j ∘ plim_map f ≈ fmap[D j] f ∘ plim_leg p j.
Proof. exact (limit_med_commutes (plim_alimit q) (plim_cone_at f) j). Qed.

(* Mac Lane's "unique": the arrow part is determined by its legs. *)
Lemma plim_map_unique {p q : P} (f : p ~{P}~> q)
  (u : plim_obj p ~{X}~> plim_obj q) :
  (∀ j : J, plim_leg q j ∘ u ≈ fmap[D j] f ∘ plim_leg p j) → plim_map f ≈ u.
Proof. exact (limit_med_unique (plim_alimit q) (plim_cone_at f) u). Qed.

(** ** The pointwise limit functor *)

Program Definition PointwiseLimit : P ⟶ X := {|
  fobj := plim_obj;
  fmap := fun _ _ f => plim_map f
|}.
Next Obligation.
  proper.
  apply plim_jointly_monic; intro j.
  rewrite !plim_map_commutes.
  now rewrite X0.
Qed.
Next Obligation.
  apply plim_jointly_monic; intro j.
  rewrite plim_map_commutes, id_right, fmap_id, id_left.
  reflexivity.
Qed.
Next Obligation.
  apply plim_jointly_monic; intro j.
  rewrite plim_map_commutes, comp_assoc, plim_map_commutes.
  rewrite <- comp_assoc, plim_map_commutes, comp_assoc.
  now rewrite fmap_comp.
Qed.

(** ** The limiting cone in [P, X] *)

Program Definition plim_nat (j : J) : PointwiseLimit ~{[P, X]}~> D j := {|
  transform := fun p => plim_leg p j
|}.
Next Obligation. symmetry; apply plim_map_commutes. Qed.
Next Obligation. apply plim_map_commutes. Qed.

Program Definition PointwiseLimitCone : Cone D := {|
  vertex_obj := PointwiseLimit;
  coneFrom := {| vertex_map := plim_nat |}
|}.
Next Obligation. apply plim_leg_coherence. Qed.

(* 相关说明。 （已译） *)

Section Universal.

Context (M : Cone D).

(* A cone over D in [P, X], evaluated at p, is a cone over the evaluated
   diagram. *)
Program Definition plim_comp_cone (p : P) : Cone (Eval p ◯ D) := {|
  vertex_obj := fobj[vertex_obj[M]] p;
  coneFrom := {| vertex_map := fun j => transform[cone_leg M j] p |}
|}.
Next Obligation.
  pose proof (@cone_coherence _ _ _ _ (@coneFrom _ _ _ M) x y f) as Hc.
  simpl in Hc. apply Hc.
Qed.

Definition plim_ump_map (p : P) :
  fobj[vertex_obj[M]] p ~{X}~> plim_obj p :=
  limit_med (plim_alimit p) (plim_comp_cone p).

Lemma plim_ump_commutes (p : P) (j : J) :
  plim_leg p j ∘ plim_ump_map p ≈ transform[cone_leg M j] p.
Proof. exact (limit_med_commutes (plim_alimit p) (plim_comp_cone p) j). Qed.

(* 相关说明。 （已译） *)
Program Definition plim_ump_nat :
  vertex_obj[M] ~{[P, X]}~> PointwiseLimit := {|
  transform := plim_ump_map
|}.
Next Obligation.
  apply plim_jointly_monic; intro j.
  rewrite comp_assoc, plim_map_commutes.
  rewrite <- comp_assoc, plim_ump_commutes.
  rewrite comp_assoc, plim_ump_commutes.
  apply (naturality[cone_leg M j]).
Qed.
Next Obligation.
  symmetry.
  apply plim_jointly_monic; intro j.
  rewrite comp_assoc, plim_map_commutes.
  rewrite <- comp_assoc, plim_ump_commutes.
  rewrite comp_assoc, plim_ump_commutes.
  apply (naturality[cone_leg M j]).
Qed.

End Universal.

(* Uniqueness in [P, X] is pointwise uniqueness: an equation of
   transformations reduces componentwise. *)
Definition PointwiseIsLimitCone : IsLimitCone PointwiseLimitCone.
Proof.
  intro M.
  unshelve refine {| unique_obj := plim_ump_nat M |}.
  - intros j p; simpl.
    apply plim_ump_commutes.
  - intros v Hv p.
    apply (limit_med_unique (plim_alimit p) (plim_comp_cone M p)).
    intro j.
    exact (Hv j p).
Defined.

(* 相关说明。 （已译） *)
Definition Functor_Category_pointwise_limit : Limit D :=
  limitcone_limit PointwiseLimitCone PointwiseIsLimitCone.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition Eval_pointwise_IsLimitCone (p : P) :
  IsLimitCone (FCone (Eval p) PointwiseLimitCone) :=
  limit_limitcone (L p).

(* 相关说明。 （已译） *)
Definition Eval_PreservesLimitCone (p : P) : PreservesLimitCone D (Eval p) :=
  fun N HN =>
    limitcone_transport
      (ConeIso_sym (FCone_iso (Eval p) (limitcone_iso HN PointwiseIsLimitCone)))
      (Eval_pointwise_IsLimitCone p).

Definition Eval_PreservesLimit (p : P) : PreservesLimit D (Eval p) :=
  PreservesLimitCone_PreservesLimit (Eval_PreservesLimitCone p).

End Pointwise.

(* 相关说明。 （已译） *)

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Fun_HasLimitsOfShape@{jo jh co ch io u u0 u1 u2 u3 +}
  {J : Category@{io ch ch}} {P : Category@{jo jh jh}} {X : Category@{co ch ch}}
  (LX : ∀ F : J ⟶ X, Limit@{u io ch co} F) :
  ∀ D : J ⟶ [P, X], Limit@{u io ch u3} D :=
  fun D => Functor_Category_pointwise_limit D (fun p => LX (Eval p ◯ D)).

(* The issue's pinned name. *)
Definition Functor_Category_Complete@{jo jh co ch u u0 u1 u2 u3 +}
  {P : Category@{jo jh jh}} {X : Category@{co ch ch}}
  (HX : @Complete@{u u2 ch co} X) : @Complete@{u u2 jh u3} ([P, X]) :=
  fun J D => Functor_Category_pointwise_limit D (fun p => HX J (Eval p ◯ D)).

(* 相关说明。 （已译） *)

(* Annotated at 定义 same reason corollaries:
 written bare, both minimize P one universe [Category@{u u u}]
 (measured). （已译） *)
Definition Eval_ContinuousFunctor@{jo jh co ch u u0 u1 u2 u3 +}
  {P : Category@{jo jh jh}} {X : Category@{co ch ch}}
  (HX : @Complete@{u u2 ch co} X) (p : P) : ContinuousFunctor (Eval p) :=
  fun J D => Eval_PreservesLimitCone D (fun q => HX J (Eval q ◯ D)) p.

Definition Eval_PreservesAllLimits@{jo jh co ch u u0 u1 u2 u3 +}
  {P : Category@{jo jh jh}} {X : Category@{co ch ch}}
  (HX : @Complete@{u u2 ch co} X) (p : P) : PreservesAllLimits (Eval p) :=
  Continuous_PreservesAllLimits (Eval_ContinuousFunctor HX p).

(* * ** Presheaves: concrete 推论 （已译） *)

(* Awodey §8.5's Corollary: every presheaf 范畴 is 完备, from
 Instance/Sets/Complete.v's [Sets_Complete]; evaluation at any 对象
 preserves all limits (Proposition 8.7's second clause). The covariant
 twin [Fun_Sets_Complete] is recorded too.（已译） *)
Definition Presheaf_Complete (C : Category) : @Complete ([C^op, Sets]) :=
  Functor_Category_Complete Sets_Complete.

Definition Presheaf_Eval_PreservesAllLimits (C : Category) (c : C) :
  PreservesAllLimits (@Eval (C^op) Sets c) :=
  @Eval_PreservesAllLimits (C^op) Sets Sets_Complete c.

Definition Fun_Sets_Complete (C : Category) : @Complete ([C, Sets]) :=
  Functor_Category_Complete Sets_Complete.
