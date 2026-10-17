Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Grp.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/limit#limits_in_categories_of_algebras
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_groups

   本文件给出极限实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Section SetsExt.

Context {J : Category}.
Context {F : J ⟶ Sets}.
Context {c : Sets}.
Context (H : IsALimit F c).

Definition sets_pre {d : Sets} (u : d ~{Sets}~> c) : Cone F :=
  @Build_Cone J Sets F d
    (@Build_ACone J Sets d F (fun j => limit_leg H j ∘ u)
       (fun x y f =>
          transitivity (comp_assoc _ _ _)
            (@compose_respects Sets _ _ _ _ _ (limit_leg_coherence H f) _ _
               (reflexivity u)))).

Lemma sets_med_eq {d : Sets} (u v : d ~{Sets}~> c) :
  (∀ j : J, limit_leg H j ∘ u ≈ limit_leg H j ∘ v) → u ≈ v.
Proof.
  intro Huv.
  apply (limit_med_eq H (sets_pre u)).
  - intro j; reflexivity.
  - intro j; symmetry; apply Huv.
Qed.

Program Definition sets_const (x : carrier c) : c ~{Sets}~> c :=
  {| morphism := fun _ => x |}.

Lemma sets_limit_ext (x y : carrier c) :
  (∀ j : J, limit_leg H j x ≈ limit_leg H j y) → x ≈ y.
Proof.
  intro Hxy.
  exact (sets_med_eq (sets_const x) (sets_const y) (fun j a => Hxy j) x).
Qed.

End SetsExt.

(* 相关说明。 （已译） *)

Section GrpLift.

Context {J : Category}.
Context (K : J ⟶ Grp).
Context (L : Limit (Grp_Forget ◯ K)).

Definition glim_leg (j : J) : vertex_obj[L] ~{Sets}~> grp_setoid (K j) :=
  limit_leg (limit_is_alimit L) j.

Lemma glim_leg_coherence {x y : J} (f : x ~{J}~> y)
  (a : carrier vertex_obj[L]) :
  grp_map (fmap[K] f) (glim_leg x a) ≈ glim_leg y a.
Proof. exact (limit_leg_coherence (limit_is_alimit L) f a). Qed.

Lemma glim_ext (x y : carrier vertex_obj[L]) :
  (∀ j : J, glim_leg j x ≈ glim_leg j y) → x ≈ y.
Proof. exact (sets_limit_ext (limit_is_alimit L) x y). Qed.

(** ** The multiplication *)

Definition glim_pair : Sets :=
  {| carrier   := carrier vertex_obj[L] * carrier vertex_obj[L]
   ; is_setoid := prod_setoid |}.

Program Definition glim_mul_leg (j : J) :
  glim_pair ~{Sets}~> grp_setoid (K j) :=
  {| morphism := fun p =>
       grp_mul (K j) (glim_leg j (fst p)) (glim_leg j (snd p)) |}.
Next Obligation.
  intros p q Hpq.
  destruct Hpq as [H1 H2].
  now rewrite H1, H2.
Qed.

Lemma glim_mul_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Grp_Forget ◯ K] f ∘ glim_mul_leg x ≈ glim_mul_leg y.
Proof.
  intro p; simpl.
  rewrite grp_map_mul.
  now rewrite !glim_leg_coherence.
Qed.

Definition glim_mul_cone : Cone (Grp_Forget ◯ K) :=
  @Build_Cone J Sets (Grp_Forget ◯ K) glim_pair
    (@Build_ACone J Sets glim_pair (Grp_Forget ◯ K)
       glim_mul_leg (@glim_mul_coherence)).

Definition glim_mul_map : glim_pair ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) glim_mul_cone.

Definition glim_mul (a b : carrier vertex_obj[L]) : carrier vertex_obj[L] :=
  glim_mul_map (a, b).

Lemma glim_mul_triangle (j : J) (a b : carrier vertex_obj[L]) :
  glim_leg j (glim_mul a b) ≈ grp_mul (K j) (glim_leg j a) (glim_leg j b).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) glim_mul_cone j (a, b)).
Qed.

Lemma glim_mul_respects :
  Proper (equiv ==> equiv ==> equiv) glim_mul.
Proof.
  intros a a' Ha b b' Hb.
  exact (proper_morphism glim_mul_map (a, b) (a', b') (Ha, Hb)).
Qed.

(** ** The unit *)

Program Definition glim_unit_leg (j : J) :
  unit_setoid_object ~{Sets}~> grp_setoid (K j) :=
  {| morphism := fun _ => grp_unit (K j) |}.

Lemma glim_unit_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Grp_Forget ◯ K] f ∘ glim_unit_leg x ≈ glim_unit_leg y.
Proof. intro p; simpl; apply grp_map_unit. Qed.

Definition glim_unit_cone : Cone (Grp_Forget ◯ K) :=
  @Build_Cone J Sets (Grp_Forget ◯ K) unit_setoid_object
    (@Build_ACone J Sets unit_setoid_object (Grp_Forget ◯ K)
       glim_unit_leg (@glim_unit_coherence)).

Definition glim_unit_map : unit_setoid_object ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) glim_unit_cone.

Definition glim_unit : carrier vertex_obj[L] := glim_unit_map ttt.

Lemma glim_unit_triangle (j : J) :
  glim_leg j glim_unit ≈ grp_unit (K j).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) glim_unit_cone j ttt).
Qed.

(** ** The inversion *)

Program Definition glim_inv_leg (j : J) :
  vertex_obj[L] ~{Sets}~> grp_setoid (K j) :=
  {| morphism := fun a => grp_inv (K j) (glim_leg j a) |}.
Next Obligation. intros a b Hab; now rewrite Hab. Qed.

Lemma glim_inv_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Grp_Forget ◯ K] f ∘ glim_inv_leg x ≈ glim_inv_leg y.
Proof.
  intro a; simpl.
  rewrite grp_map_inv.
  now rewrite glim_leg_coherence.
Qed.

Definition glim_inv_cone : Cone (Grp_Forget ◯ K) :=
  @Build_Cone J Sets (Grp_Forget ◯ K) vertex_obj[L]
    (@Build_ACone J Sets vertex_obj[L] (Grp_Forget ◯ K)
       glim_inv_leg (@glim_inv_coherence)).

Definition glim_inv_map : vertex_obj[L] ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) glim_inv_cone.

Definition glim_inv (a : carrier vertex_obj[L]) : carrier vertex_obj[L] :=
  glim_inv_map a.

Lemma glim_inv_triangle (j : J) (a : carrier vertex_obj[L]) :
  glim_leg j (glim_inv a) ≈ grp_inv (K j) (glim_leg j a).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) glim_inv_cone j a).
Qed.


(* 相关说明。 （已译） *)

Lemma glim_assoc (a b c : carrier vertex_obj[L]) :
  glim_mul (glim_mul a b) c ≈ glim_mul a (glim_mul b c).
Proof.
  apply glim_ext; intro j.
  rewrite !glim_mul_triangle.
  apply grp_mul_assoc.
Qed.

Lemma glim_unit_l (a : carrier vertex_obj[L]) : glim_mul glim_unit a ≈ a.
Proof.
  apply glim_ext; intro j.
  rewrite glim_mul_triangle, glim_unit_triangle.
  apply grp_mul_unit_l.
Qed.

Lemma glim_inv_l (a : carrier vertex_obj[L]) :
  glim_mul (glim_inv a) a ≈ glim_unit.
Proof.
  apply glim_ext; intro j.
  rewrite glim_mul_triangle, glim_inv_triangle, glim_unit_triangle.
  apply grp_mul_inv_l.
Qed.

(** ** The lifted group *)

(*
   本节说明（余）极限、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition glim_prop : PropEquiv (is_setoid vertex_obj[L]) :=
  @PropEquiv_of_relation _ (is_setoid vertex_obj[L])
    (fun x y => forall j : J,
       @pequiv _ _ (grp_prop (K j)) (glim_leg j x) (glim_leg j y))
    (fun x y H => glim_ext x y (fun j => pequiv_to _ _ (H j)))
    (fun x y H j => pequiv_from _ _ (proper_morphism (glim_leg j) x y H)).

Definition LimitGroup : GrpObject :=
  {| grp_setoid       := vertex_obj[L]
   ; grp_unit         := glim_unit
   ; grp_mul          := glim_mul
   ; grp_inv          := glim_inv
   ; grp_mul_respects := glim_mul_respects
   ; grp_mul_assoc    := glim_assoc
   ; grp_mul_unit_l   := glim_unit_l
   ; grp_mul_inv_l    := glim_inv_l
   ; grp_prop         := glim_prop |}.

(** ** The legs are homomorphisms *)

Program Definition glim_hom (j : J) : GrpHom LimitGroup (K j) :=
  {| grp_map := glim_leg j |}.
Next Obligation. apply glim_unit_triangle. Qed.
Next Obligation. apply glim_mul_triangle. Qed.

Lemma glim_hom_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[K] f ∘ glim_hom x ≈ glim_hom y.
Proof. intro a; exact (glim_leg_coherence f a). Qed.

Definition glim_cone : Cone K :=
  @Build_Cone J Grp K LimitGroup
    (@Build_ACone J Grp LimitGroup K glim_hom (@glim_hom_coherence)).

(* 相关说明。 （已译） *)

Definition glim_over_obj : Grp_Forget LimitGroup = vertex_obj[L] := eq_refl.

Definition glim_over_legs (j : J) :
  fmap[Grp_Forget] (cone_leg glim_cone j) = glim_leg j := eq_refl.


(** ** The lifted cone is limiting *)

Definition gcar_med (N : Cone K) :
  grp_setoid vertex_obj[N] ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) (FCone Grp_Forget N).

Lemma gcar_med_commutes (N : Cone K) (j : J) (a : carrier vertex_obj[N]) :
  glim_leg j (gcar_med N a) ≈ grp_map (cone_leg N j) a.
Proof.
  exact (limit_med_commutes (limit_is_alimit L) (FCone Grp_Forget N) j a).
Qed.

Lemma gcar_med_unit (N : Cone K) :
  gcar_med N (grp_unit vertex_obj[N]) ≈ glim_unit.
Proof.
  apply glim_ext; intro j.
  rewrite gcar_med_commutes, glim_unit_triangle.
  apply grp_map_unit.
Qed.

Lemma gcar_med_mul (N : Cone K) (a b : carrier vertex_obj[N]) :
  gcar_med N (grp_mul vertex_obj[N] a b)
    ≈ glim_mul (gcar_med N a) (gcar_med N b).
Proof.
  apply glim_ext; intro j.
  rewrite gcar_med_commutes, glim_mul_triangle, !gcar_med_commutes.
  apply grp_map_mul.
Qed.

Program Definition glim_med (N : Cone K) : vertex_obj[N] ~{Grp}~> LimitGroup :=
  {| grp_map := gcar_med N |}.
Next Obligation. apply gcar_med_unit. Qed.
Next Obligation. apply gcar_med_mul. Qed.

Definition glim_created : IsALimit K LimitGroup.
Proof.
  unshelve refine {| limit_acone := @coneFrom _ _ _ glim_cone |}.
  intro N.
  unshelve refine {| unique_obj := glim_med N |}.
  - intros j a.
    exact (gcar_med_commutes N j a).
  - intros v Hv a.
    exact (limit_med_unique (limit_is_alimit L) (FCone Grp_Forget N)
             (grp_map v) Hv a).
Defined.


(* 相关说明。 （已译） *)

Lemma glim_unit_unique (e : carrier vertex_obj[L])
  (He : ∀ j : J, glim_leg j e ≈ grp_unit (K j)) : e ≈ glim_unit.
Proof.
  apply glim_ext; intro j.
  now rewrite He, glim_unit_triangle.
Qed.

Lemma glim_mul_unique
  (m : carrier vertex_obj[L] → carrier vertex_obj[L] → carrier vertex_obj[L])
  (Hm : ∀ (j : J) a b,
     glim_leg j (m a b) ≈ grp_mul (K j) (glim_leg j a) (glim_leg j b))
  (a b : carrier vertex_obj[L]) : m a b ≈ glim_mul a b.
Proof.
  apply glim_ext; intro j.
  now rewrite Hm, glim_mul_triangle.
Qed.

Lemma glim_inv_unique
  (i : carrier vertex_obj[L] → carrier vertex_obj[L])
  (Hi : ∀ (j : J) a, glim_leg j (i a) ≈ grp_inv (K j) (glim_leg j a))
  (a : carrier vertex_obj[L]) : i a ≈ glim_inv a.
Proof.
  apply glim_ext; intro j.
  now rewrite Hi, glim_inv_triangle.
Qed.


(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma glim_structure_unique
  (e : carrier vertex_obj[L])
  (m : carrier vertex_obj[L] → carrier vertex_obj[L] → carrier vertex_obj[L])
  (i : carrier vertex_obj[L] → carrier vertex_obj[L])
  (He : ∀ j : J, glim_leg j e ≈ grp_unit (K j))
  (Hm : ∀ (j : J) a b,
     glim_leg j (m a b) ≈ grp_mul (K j) (glim_leg j a) (glim_leg j b))
  (Hi : ∀ (j : J) a, glim_leg j (i a) ≈ grp_inv (K j) (glim_leg j a)) :
  (e ≈ glim_unit)
    * (∀ a b, m a b ≈ glim_mul a b)
    * (∀ a, i a ≈ glim_inv a).
Proof.
  split; [ split | ].
  - exact (glim_unit_unique e He).
  - exact (glim_mul_unique m Hm).
  - exact (glim_inv_unique i Hi).
Qed.

End GrpLift.

(* 相关说明。 （已译） *)

Section GrpReflect.

Context {J : Category}.
Context (K : J ⟶ Grp).
Context (M : Cone K).
Context (HM : IsLimitCone (FCone Grp_Forget M)).

Definition grefl_med (N : Cone K) :
  grp_setoid vertex_obj[N] ~{Sets}~> grp_setoid vertex_obj[M] :=
  limit_med (limitcone_isalimit HM) (FCone Grp_Forget N).

Lemma grefl_med_commutes (N : Cone K) (j : J) (a : carrier vertex_obj[N]) :
  grp_map (cone_leg M j) (grefl_med N a) ≈ grp_map (cone_leg N j) a.
Proof using All.
  exact (limit_med_commutes (limitcone_isalimit HM) (FCone Grp_Forget N) j a).
Qed.

Lemma grefl_ext (x y : carrier vertex_obj[M]) :
  (∀ j : J, grp_map (cone_leg M j) x ≈ grp_map (cone_leg M j) y) → x ≈ y.
Proof using All. exact (sets_limit_ext (limitcone_isalimit HM) x y). Qed.

Lemma grefl_med_unit (N : Cone K) :
  grefl_med N (grp_unit vertex_obj[N]) ≈ grp_unit vertex_obj[M].
Proof using All.
  apply grefl_ext; intro j.
  rewrite grefl_med_commutes, !grp_map_unit.
  reflexivity.
Qed.

Lemma grefl_med_mul (N : Cone K) (a b : carrier vertex_obj[N]) :
  grefl_med N (grp_mul vertex_obj[N] a b)
    ≈ grp_mul vertex_obj[M] (grefl_med N a) (grefl_med N b).
Proof using All.
  apply grefl_ext; intro j.
  rewrite grefl_med_commutes, !grp_map_mul, !grefl_med_commutes.
  reflexivity.
Qed.

Program Definition grefl_hom (N : Cone K) :
  vertex_obj[N] ~{Grp}~> vertex_obj[M] := {| grp_map := grefl_med N |}.
Next Obligation. apply grefl_med_unit. Qed.
Next Obligation. apply grefl_med_mul. Qed.

Definition grp_reflects : IsLimitCone M.
Proof using All.
  intro N.
  unshelve refine {| unique_obj := grefl_hom N |}.
  - intros j a.
    exact (grefl_med_commutes N j a).
  - intros v Hv a.
    exact (limit_med_unique (limitcone_isalimit HM) (FCone Grp_Forget N)
             (grp_map v) Hv a).
Defined.

End GrpReflect.

(* 相关说明。 （已译） *)

Section GrpStrictlyCreates.

Context {J : Category}.
Context (K : J ⟶ Grp).

Definition grp_strict_lift (N : Cone (Grp_Forget ◯ K)) (HN : IsLimitCone N) :
  StrictLift K Grp_Forget N :=
  @Build_StrictLift J Grp Sets K Grp_Forget N
    (glim_cone K (@Build_Limit J Sets (Grp_Forget ◯ K) N HN))
    eq_refl
    (fun x => reflexivity _).

Definition Grp_Forget_StrictlyCreatesLimit : StrictlyCreatesLimit K Grp_Forget.
Proof.
  unshelve refine {| screates := grp_strict_lift |}.
  - intros N HN.
    exact (@ump_limit _ _ _ _
             (glim_created K (@Build_Limit J Sets (Grp_Forget ◯ K) N HN))).
  - intros M HM.
    exact (grp_reflects K M HM).
Defined.

Definition Grp_Forget_CreatesLimit : CreatesLimit K Grp_Forget :=
  StrictlyCreatesLimit_CreatesLimit Grp_Forget_StrictlyCreatesLimit.

End GrpStrictlyCreates.

Definition Grp_Forget_StrictlyCreatesLimits :
  StrictlyCreatesLimits Grp_Forget :=
  fun J K => Grp_Forget_StrictlyCreatesLimit K.

Definition Grp_Forget_creates_limits : CreatesAllLimits Grp_Forget :=
  fun J K => Grp_Forget_CreatesLimit K.

Definition Grp_Forget_reflects_limits {J : Category} (K : J ⟶ Grp) :
  ReflectsLimitCone K Grp_Forget :=
  creates_reflects_limits (Grp_Forget_CreatesLimit K).

(*
   本节说明 Limit 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Grp_lift_cone_unique {J : Category} (K : J ⟶ Grp)
  (N : Cone (Grp_Forget ◯ K)) (HN : IsLimitCone N)
  (M : Cone K) (i : ConeIso (FCone Grp_Forget M) N) :
  ConeIso M (slift_cone (screates N HN)) :=
  screates_lift_unique (Grp_Forget_StrictlyCreatesLimit K) N HN M i.

(* 相关说明。 （已译） *)

Example grp_fcone_apex {J : Category} (K : J ⟶ Grp) (N : Cone K) :
  vertex_obj[FCone Grp_Forget N] = grp_setoid vertex_obj[N] := eq_refl.

Example grp_fcone_leg {J : Category} (K : J ⟶ Grp) (N : Cone K) (j : J) :
  cone_leg (FCone Grp_Forget N) j = grp_map (cone_leg N j) := eq_refl.

(* 相关说明。 （已译） *)

Definition Grp_Forget_lifts_limits {J : Category} (K : J ⟶ Grp)
  (L : Limit (Grp_Forget ◯ K)) : Limit K :=
  creates_limit_lift (Grp_Forget_CreatesLimit K) L.

Example grp_lift_apex {J : Category} (K : J ⟶ Grp)
  (L : Limit (Grp_Forget ◯ K)) :
  Grp_Forget (vertex_obj[Grp_Forget_lifts_limits K L]) = vertex_obj[L]
  := eq_refl.

Example grp_lift_legs {J : Category} (K : J ⟶ Grp)
  (L : Limit (Grp_Forget ◯ K)) (j : J) :
  fmap[Grp_Forget]
    (cone_leg (@limit_cone _ _ _ (Grp_Forget_lifts_limits K L)) j)
    = limit_leg (limit_is_alimit L) j
  := eq_refl.

(* 相关说明。 （已译） *)

Definition Grp_Complete : @Complete Grp :=
  creates_limits_Complete Grp_Forget Sets_Complete Grp_Forget_creates_limits.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Grp_Forget_continuous : ContinuousFunctor Grp_Forget :=
  creates_limits_continuous Grp_Forget Sets_Complete Grp_Forget_creates_limits.

Definition Grp_Forget_PreservesAllLimits : PreservesAllLimits Grp_Forget :=
  creates_limits_PreservesAllLimits Grp_Forget Sets_Complete
    Grp_Forget_creates_limits.

(* 相关说明。 （已译） *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section GrpComputed.

Context {J : Category}.
Context (K : J ⟶ Grp).

Example grp_complete_carrier :
  grp_setoid (vertex_obj[Grp_Complete J K]) = Sets_limit_obj (Grp_Forget ◯ K)
  := eq_refl.

Example grp_complete_mul
  (a b : carrier (Sets_limit_obj (Grp_Forget ◯ K))) (d : J) :
  `1 (grp_mul (vertex_obj[Grp_Complete J K]) a b) d
    = grp_mul (K d) (`1 a d) (`1 b d) := eq_refl.

Example grp_complete_unit (d : J) :
  `1 (grp_unit (vertex_obj[Grp_Complete J K])) d = grp_unit (K d) := eq_refl.

Example grp_complete_inv
  (a : carrier (Sets_limit_obj (Grp_Forget ◯ K))) (d : J) :
  `1 (grp_inv (vertex_obj[Grp_Complete J K]) a) d
    = grp_inv (K d) (`1 a d) := eq_refl.

Example grp_complete_leg (d : J) :
  grp_map (cone_leg (@limit_cone _ _ _ (Grp_Complete J K)) d)
    = Sets_limit_leg (Grp_Forget ◯ K) d := eq_refl.

End GrpComputed.
