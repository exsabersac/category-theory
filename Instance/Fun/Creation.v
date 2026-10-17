Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Kan.Extension.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Eval.
Require Import Category.Instance.Fun.Limit.

Generalizable All Variables.

(** * Pointwise limits as creation along the discrete inclusion *)

(*
 nLab: https://ncatlab.org/nlab/show/created+limit

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The object-discrete inclusion and the restriction functor *)

Section Restriction.

Universe jo jh co ch.

Context {P : Category@{jo jh jh}} {X : Category@{co ch ch}}.

(* |P|: the discrete category on the objects of P. *)
Definition ObjCat : Category@{jo jh jh} := DiscreteCat@{jo jh jh} (obj[P]).

(*
   本节说明函子、（余）极限、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition DiscInc : ObjCat ⟶ P := DiscreteCat_Functor' (fun p : P => p).

(* Restriction along the inclusion: precomposition, Theory/Kan/Extension.v's
   [Induced]. *)
Definition Res : [P, X] ⟶ [ObjCat, X] := @Induced ObjCat P DiscInc X.

End Restriction.

Section Readbacks.

Context {P X : Category}.

Definition res_obj (H : [P, X]) : fobj[@Res P X] H = H ◯ DiscInc := eq_refl.

Definition res_obj_at (H : [P, X]) (p : P) :
  fobj[fobj[@Res P X] H] p = fobj[H] p := eq_refl.

Definition res_map (H K : [P, X]) (s : H ~{[P, X]}~> K) (p : P) :
  transform[fmap[@Res P X] s] p = transform[s] p := eq_refl.

(* Evaluating after restricting IS evaluating, in both data fields. *)
Definition eval_res_obj (p : P) (H : [P, X]) :
  fobj[(@Eval ObjCat X p) ◯ (@Res P X)] H = fobj[@Eval P X p] H := eq_refl.

Definition eval_res_map (p : P) (H K : [P, X]) (s : H ~{[P, X]}~> K) :
  fmap[(@Eval ObjCat X p) ◯ (@Res P X)] s = fmap[@Eval P X p] s := eq_refl.

End Readbacks.

(** ** Reflection: a cone whose every evaluation is limiting is limiting *)

Section PointwiseReflect.

Context {J P X : Category}.
Context (D : J ⟶ [P, X]).

(* From a cone M in [P, X] all of whose evaluations are limiting, the
   pointwise limit data #425's construction consumes. *)
Definition ptw_of_cone (M : Cone D)
  (H : ∀ p : P, IsLimitCone (FCone (Eval p) M)) (p : P) : Limit (Eval p ◯ D) :=
  limitcone_limit (FCone (Eval p) M) (H p).

(* The assembled pointwise cone has M's apex and M's legs, objectwise on
   the nose. *)
Definition ptw_apex_readback (M : Cone D)
  (H : ∀ p : P, IsLimitCone (FCone (Eval p) M)) (p : P) :
  fobj[PointwiseLimit D (ptw_of_cone M H)] p = fobj[vertex_obj[M]] p := eq_refl.

Definition ptw_leg_readback (M : Cone D)
  (H : ∀ p : P, IsLimitCone (FCone (Eval p) M)) (p : P) (j : J) :
  transform[cone_leg (PointwiseLimitCone D (ptw_of_cone M H)) j] p
    = transform[cone_leg M j] p := eq_refl.

(* The mediator between adjacent pointwise limits IS M's own arrow action,
   by the uniqueness of the arrow part. *)
Lemma ptw_map_is_fmap (M : Cone D)
  (H : ∀ p : P, IsLimitCone (FCone (Eval p) M)) {x y : P} (f : x ~{P}~> y) :
  plim_map D (ptw_of_cone M H) f ≈ fmap[vertex_obj[M]] f.
Proof.
  apply (plim_map_unique D (ptw_of_cone M H) f).
  intro j.
  symmetry; exact (naturality[cone_leg M j] _ _ f).
Qed.

(* ... so the two cones are isomorphic with IDENTITY components. *)
Program Definition ptw_apex_iso (M : Cone D)
  (H : ∀ p : P, IsLimitCone (FCone (Eval p) M)) :
  @Isomorphism ([P, X]) (vertex_obj[M]) (PointwiseLimit D (ptw_of_cone M H)) := {|
  to   := {| transform := fun p => id |};
  from := {| transform := fun p => id |}
|}.
Next Obligation.
  rewrite id_left, id_right.
  now rewrite ptw_map_is_fmap.
Qed.
Next Obligation.
  rewrite id_left, id_right.
  now rewrite ptw_map_is_fmap.
Qed.
Next Obligation.
  rewrite id_left, id_right.
  now rewrite ptw_map_is_fmap.
Qed.
Next Obligation.
  rewrite id_left, id_right.
  now rewrite ptw_map_is_fmap.
Qed.
Next Obligation. rewrite ptw_map_is_fmap; cat. Qed.

Definition ptw_cone_iso (M : Cone D)
  (H : ∀ p : P, IsLimitCone (FCone (Eval p) M)) :
  ConeIso M (PointwiseLimitCone D (ptw_of_cone M H)).
Proof.
  exists (ptw_apex_iso M H).
  intros j p; simpl.
  apply id_right.
Defined.

(* THE REFLECTION — Theorem 1 reformulated: a transport of #425's
   [PointwiseIsLimitCone], not a parallel proof. *)
Definition Fun_pointwise_reflect (M : Cone D)
  (H : ∀ p : P, IsLimitCone (FCone (Eval p) M)) : IsLimitCone M :=
  limitcone_transport (ConeIso_sym (ptw_cone_iso M H))
    (PointwiseIsLimitCone D (ptw_of_cone M H)).

End PointwiseReflect.

(** ** The family of evaluations jointly creates limits (Riehl Ex 3.4.v) *)

Section JointCreation.

Context {J P X : Category}.
Context (D : J ⟶ [P, X]).

Definition ev_family (p : obj[P]) : [P, X] ⟶ X := (Eval p).

(* The lift is #425's pointwise cone, assembled from the given family. *)
Definition ev_lift (N : ∀ p : obj[P], Cone (Eval p ◯ D))
  (HN : ∀ p : obj[P], IsLimitCone (N p)) : Cone D :=
  PointwiseLimitCone D (fun p => limitcone_limit (N p) (HN p)).

(* The image of the lift under [Eval p] is the given cone in APEX and LEGS
   on the nose; the whole records do not convert (probe). *)
Definition ev_lift_apex (N : ∀ p : obj[P], Cone (Eval p ◯ D))
  (HN : ∀ p : obj[P], IsLimitCone (N p)) (p : obj[P]) :
  vertex_obj[FCone (Eval p) (ev_lift N HN)] = vertex_obj[N p] := eq_refl.

Definition ev_lift_leg (N : ∀ p : obj[P], Cone (Eval p ◯ D))
  (HN : ∀ p : obj[P], IsLimitCone (N p)) (p : obj[P]) (x : J) :
  cone_leg (FCone (Eval p) (ev_lift N HN)) x = cone_leg (N p) x := eq_refl.

Definition ev_lift_over (N : ∀ p : obj[P], Cone (Eval p ◯ D))
  (HN : ∀ p : obj[P], IsLimitCone (N p)) (p : obj[P]) :
  ConeIso (FCone (Eval p) (ev_lift N HN)) (N p).
Proof.
  exists iso_id.
  intro x; simpl; apply id_right.
Defined.

Definition Fun_Eval_JointlyCreateLimit : JointlyCreateLimit D ev_family.
Proof.
  unshelve refine {| jcreates_lift := ev_lift |}.
  - exact ev_lift_over.
  - exact (Fun_pointwise_reflect D).
Defined.

End JointCreation.

(** ** Creation along the restriction functor *)

Section ResCreation.

Context {J P X : Category}.
Context (D : J ⟶ [P, X]).

(* A cone over [Res ◯ D] in [|P|, X], evaluated at an object p. *)
Program Definition res_comp_cone (N : Cone (@Res P X ◯ D)) (p : P) :
  Cone (Eval p ◯ D) := {|
  vertex_obj := fobj[vertex_obj[N]] p;
  coneFrom := {| vertex_map := fun j => transform[cone_leg N j] p |}
|}.
Next Obligation.
  pose proof (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f) as Hc.
  simpl in Hc; apply Hc.
Qed.

(* The mediator into the restricted cone: componentwise the pointwise
   mediator; naturality over the discrete shape is free. *)
Program Definition res_ump_nat (M : Cone D)
  (H : ∀ p : P, IsLimitCone (FCone (Eval p) M)) (N : Cone (@Res P X ◯ D)) :
  vertex_obj[N] ~{[@ObjCat P, X]}~> fobj[@Res P X] (vertex_obj[M]) := {|
  transform := fun p => unique_obj (H p (res_comp_cone N p))
|}.

(* PRESERVATION: a cone all of whose evaluations are limiting has a limiting
   image under [Res]. *)
Definition Res_preserves (M : Cone D)
  (H : ∀ p : P, IsLimitCone (FCone (Eval p) M)) :
  IsLimitCone (FCone (@Res P X) M).
Proof.
  intro N.
  unshelve refine {| unique_obj := res_ump_nat M H N |}.
  - intros j p; simpl.
    exact (unique_property (H p (res_comp_cone N p)) j).
  - intros v Hv p; simpl.
    exact (uniqueness (H p (res_comp_cone N p)) (transform[v] p)
             (fun j => Hv j p)).
Defined.

(* An isomorphism of cones downstairs restricts to one at each object. *)
Definition res_coneiso_at (L : ∀ p : P, Limit (Eval p ◯ D)) (M : Cone D)
  (i : ConeIso (FCone (@Res P X) M) (FCone (@Res P X) (PointwiseLimitCone D L)))
  (p : P) :
  ConeIso (FCone (Eval p) M) (FCone (Eval p) (PointwiseLimitCone D L)).
Proof.
  exists (fobj_iso (@Eval (@ObjCat P) X p) _ _ (`1 i)).
  intro x.
  exact (`2 i x p).
Defined.

(* CREATION — Mac Lane §V.3 Theorem 2 — under the hypothesis that the
   pointwise limits exist (the header explains why the hypothesis stays). *)
Definition Res_CreatesLimit (L : ∀ p : P, Limit (Eval p ◯ D)) :
  CreatesLimit D (@Res P X).
Proof.
  unshelve refine {| creates_lift := fun N HN => PointwiseLimitCone D L |}.
  - intros N HN.
    exact (limitcone_iso
             (Res_preserves (PointwiseLimitCone D L)
                (fun p => Eval_pointwise_IsLimitCone D L p)) HN).
  - intros M HM.
    apply (Fun_pointwise_reflect D M).
    intro p.
    apply (limitcone_transport
             (ConeIso_sym
                (res_coneiso_at L M
                   (limitcone_iso HM
                      (Res_preserves (PointwiseLimitCone D L)
                         (fun q => Eval_pointwise_IsLimitCone D L q))) p))).
    exact (Eval_pointwise_IsLimitCone D L p).
Defined.

(* The limit downstairs that the pointwise limits give. *)
Definition res_limit (L : ∀ p : P, Limit (Eval p ◯ D)) : Limit (@Res P X ◯ D) :=
  limitcone_limit (FCone (@Res P X) (PointwiseLimitCone D L))
    (Res_preserves (PointwiseLimitCone D L)
       (fun p => Eval_pointwise_IsLimitCone D L p)).

(* The creation-derived limit IS #425's pointwise limit, apex and legs on
   the nose. *)
Definition creation_apex (L : ∀ p : P, Limit (Eval p ◯ D)) :
  vertex_obj[@limit_cone _ _ _ (creates_limit_lift (Res_CreatesLimit L) (res_limit L))]
  = vertex_obj[@limit_cone _ _ _ (Functor_Category_pointwise_limit D L)] := eq_refl.

Definition creation_leg (L : ∀ p : P, Limit (Eval p ◯ D)) (j : J) (p : P) :
  transform[cone_leg (@limit_cone _ _ _
    (creates_limit_lift (Res_CreatesLimit L) (res_limit L))) j] p
  = transform[cone_leg (@limit_cone _ _ _
    (Functor_Category_pointwise_limit D L)) j] p := eq_refl.

End ResCreation.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition discrete_inclusion_creates_limits@{io jo co h +}
  {J : Category@{io h h}} {P : Category@{jo h h}} {X : Category@{co h h}}
  (D : J ⟶ [P, X]) (L : ∀ p : P, Limit (Eval p ◯ D)) :
  CreatesLimit D (@Res P X) := Res_CreatesLimit D L.

(** ** Corollaries *)

Section Corollaries.

Context {P X : Category}.

Definition Res_CreatesAllLimits (HX : @Complete X) : CreatesAllLimits (@Res P X) :=
  fun J D => Res_CreatesLimit D (fun p => HX J (Eval p ◯ D)).

(* Completeness of [P, X] once more, now through Structure/Limit/Creation.v's
   general theorem (creation + a complete target). *)
Definition Res_Complete (HX : @Complete X) : @Complete ([P, X]) :=
  creates_limits_Complete (@Res P X) (Functor_Category_Complete HX)
    (Res_CreatesAllLimits HX).

Definition Res_continuous (HX : @Complete X) (J : Category) (D : J ⟶ [P, X]) :
  PreservesLimitCone D (@Res P X) :=
  creates_limits_continuous (@Res P X) (Functor_Category_Complete HX)
    (Res_CreatesAllLimits HX) J D.

End Corollaries.

(** ** Strictness: what converts and what does not *)

Section Strictness.

Context {P X : Category}.

(*
   本节说明函子、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition strict_self {J : Category} (D : J ⟶ [P, X]) (M : Cone D) :
  StrictLift D (@Res P X) (FCone (@Res P X) M) := self_lift M.

End Strictness.
