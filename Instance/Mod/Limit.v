Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Mod.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(* * * Limits R-modules created forgetful 函子 [Ab] （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/created+limit
 nLab: https://ncatlab.org/nlab/show/limit#limits_in_categories_of_algebras
 nLab: https://ncatlab.org/nlab/show/Mod
 nLab: https://ncatlab.org/nlab/show/adjoint+functor+theorem
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_modules

   本文件给出极限实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ModLift.

Context {R : RingObject}.
Context {J : Category}.
Context (K : J ⟶ RMod R).
Context (L : Limit (RMod_Forget_Ab R ◯ K)).

Definition mlim_leg (j : J) : vertex_obj[L] ~{Ab}~> rm_ab (K j) :=
  limit_leg (limit_is_alimit L) j.

Lemma mlim_leg_coherence {x y : J} (f : x ~{J}~> y)
  (a : carrier (cmon_setoid (ab_cmon vertex_obj[L]))) :
  cmon_map (rm_hom (fmap[K] f)) (cmon_map (mlim_leg x) a)
    ≈ cmon_map (mlim_leg y) a.
Proof. exact (limit_leg_coherence (limit_is_alimit L) f a). Qed.

(*
   本节说明伴随、（余）极限、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition mlim_sets_limit :=
  limitcone_isalimit
    (Ab_Forget_creates_continuous J (RMod_Forget_Ab R ◯ K)
       (@limit_cone _ _ _ L) (limit_limitcone L)).

Lemma mlim_ext (x y : carrier (cmon_setoid (ab_cmon vertex_obj[L]))) :
  (∀ j : J, cmon_map (mlim_leg j) x ≈ cmon_map (mlim_leg j) y) → x ≈ y.
Proof. exact (absets_limit_ext mlim_sets_limit x y). Qed.

(** ** The scalar action *)

(*
   本节说明分配律相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition mlim_smul_fn (r : carrier (rig_setoid (ring_rig R)))
  (j : J) :
  cmon_setoid (ab_cmon vertex_obj[L]) ~{Sets}~> cmon_setoid (ab_cmon (K j)) :=
  {| morphism := fun a => rm_smul (K j) r (cmon_map (mlim_leg j) a) |}.
Next Obligation.
  intros r j a b Hab.
  now rewrite Hab.
Qed.

Program Definition mlim_smul_leg (r : carrier (rig_setoid (ring_rig R)))
  (j : J) : vertex_obj[L] ~{Ab}~> (RMod_Forget_Ab R ◯ K) j :=
  {| cmon_map := mlim_smul_fn r j |}.
Next Obligation.
  intros r j; simpl.
  rewrite cmon_map_zero.
  apply rm_smul_zero_r.
Qed.
Next Obligation.
  intros r j a b; simpl.
  rewrite cmon_map_plus.
  apply rm_smul_distr_l.
Qed.

Lemma mlim_smul_coherence (r : carrier (rig_setoid (ring_rig R)))
  {x y : J} (f : x ~{J}~> y) :
  fmap[RMod_Forget_Ab R ◯ K] f ∘ mlim_smul_leg r x ≈ mlim_smul_leg r y.
Proof.
  intro a; simpl.
  rewrite (rm_map_smul (fmap[K] f)).
  now rewrite mlim_leg_coherence.
Qed.

Definition mlim_smul_cone (r : carrier (rig_setoid (ring_rig R))) :
  Cone (RMod_Forget_Ab R ◯ K) :=
  @Build_Cone J Ab (RMod_Forget_Ab R ◯ K) vertex_obj[L]
    (@Build_ACone J Ab vertex_obj[L] (RMod_Forget_Ab R ◯ K)
       (mlim_smul_leg r) (@mlim_smul_coherence r)).

Definition mlim_smul_map (r : carrier (rig_setoid (ring_rig R))) :
  vertex_obj[L] ~{Ab}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) (mlim_smul_cone r).

Definition mlim_smul (r : carrier (rig_setoid (ring_rig R)))
  (a : carrier (cmon_setoid (ab_cmon vertex_obj[L]))) :
  carrier (cmon_setoid (ab_cmon vertex_obj[L])) :=
  cmon_map (mlim_smul_map r) a.

Lemma mlim_smul_triangle (r : carrier (rig_setoid (ring_rig R))) (j : J)
  (a : carrier (cmon_setoid (ab_cmon vertex_obj[L]))) :
  cmon_map (mlim_leg j) (mlim_smul r a)
    ≈ rm_smul (K j) r (cmon_map (mlim_leg j) a).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) (mlim_smul_cone r) j a).
Qed.

(* 相关说明。 （已译） *)

Lemma mlim_smul_respects : Proper (equiv ==> equiv ==> equiv) mlim_smul.
Proof.
  intros r r' Hr a a' Ha.
  apply mlim_ext; intro j.
  rewrite !mlim_smul_triangle.
  rewrite Hr.
  now rewrite (proper_morphism (cmon_map (mlim_leg j)) a a' Ha).
Qed.

Lemma mlim_smul_distr_l (r : carrier (rig_setoid (ring_rig R)))
  (a b : carrier (cmon_setoid (ab_cmon vertex_obj[L]))) :
  mlim_smul r (cmon_plus vertex_obj[L] a b)
    ≈ cmon_plus vertex_obj[L] (mlim_smul r a) (mlim_smul r b).
(* Not proved: mediator [Ab]-态射, so IS its
 [cmon_map_plus] clause. （已译） *)
Proof. exact (cmon_map_plus (mlim_smul_map r) a b). Qed.

Lemma mlim_smul_distr_r (r s : carrier (rig_setoid (ring_rig R)))
  (a : carrier (cmon_setoid (ab_cmon vertex_obj[L]))) :
  mlim_smul (rig_add (ring_rig R) r s) a
    ≈ cmon_plus vertex_obj[L] (mlim_smul r a) (mlim_smul s a).
Proof.
  apply mlim_ext; intro j.
  rewrite mlim_smul_triangle.
  rewrite (cmon_map_plus (mlim_leg j)).
  rewrite !mlim_smul_triangle.
  apply rm_smul_distr_r.
Qed.

Lemma mlim_smul_assoc (r s : carrier (rig_setoid (ring_rig R)))
  (a : carrier (cmon_setoid (ab_cmon vertex_obj[L]))) :
  mlim_smul (rig_mul (ring_rig R) r s) a ≈ mlim_smul r (mlim_smul s a).
Proof.
  apply mlim_ext; intro j.
  rewrite !mlim_smul_triangle.
  apply rm_smul_assoc.
Qed.

Lemma mlim_smul_one (a : carrier (cmon_setoid (ab_cmon vertex_obj[L]))) :
  mlim_smul (rig_one (ring_rig R)) a ≈ a.
Proof.
  apply mlim_ext; intro j.
  rewrite mlim_smul_triangle.
  apply rm_smul_one.
Qed.

(** ** The lifted module *)

(* 相关说明。 （已译） *)

Definition LimitMod : RModObject R :=
  {| rm_ab            := vertex_obj[L]
   ; rm_smul          := mlim_smul
   ; rm_smul_respects := mlim_smul_respects
   ; rm_smul_distr_l  := mlim_smul_distr_l
   ; rm_smul_distr_r  := mlim_smul_distr_r
   ; rm_smul_assoc    := mlim_smul_assoc
   ; rm_smul_one      := mlim_smul_one |}.

(* 相关说明。 （已译） *)

Program Definition mlim_hom (j : J) : RModHom LimitMod (K j) :=
  {| rm_hom := mlim_leg j |}.
Next Obligation. intros j r m; apply mlim_smul_triangle. Qed.

Lemma mlim_hom_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[K] f ∘ mlim_hom x ≈ mlim_hom y.
Proof. intro a; exact (mlim_leg_coherence f a). Qed.

Definition mlim_cone : Cone K :=
  @Build_Cone J (RMod R) K LimitMod
    (@Build_ACone J (RMod R) LimitMod K mlim_hom (@mlim_hom_coherence)).

(* 相关说明。 （已译） *)

Definition mlim_over_obj : RMod_Forget_Ab R LimitMod = vertex_obj[L] :=
  eq_refl.

Definition mlim_over_legs (j : J) :
  fmap[RMod_Forget_Ab R] (cone_leg mlim_cone j) = mlim_leg j := eq_refl.

(** ** The lifted cone is limiting *)

Definition mcar_med (N : Cone K) :
  rm_ab vertex_obj[N] ~{Ab}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) (FCone (RMod_Forget_Ab R) N).

Lemma mcar_med_commutes (N : Cone K) (j : J)
  (a : carrier (cmon_setoid (ab_cmon (rm_ab vertex_obj[N])))) :
  cmon_map (mlim_leg j) (cmon_map (mcar_med N) a)
    ≈ cmon_map (rm_hom (cone_leg N j)) a.
Proof.
  exact (limit_med_commutes (limit_is_alimit L)
           (FCone (RMod_Forget_Ab R) N) j a).
Qed.

Lemma mcar_med_smul (N : Cone K) (r : carrier (rig_setoid (ring_rig R)))
  (a : carrier (cmon_setoid (ab_cmon (rm_ab vertex_obj[N])))) :
  cmon_map (mcar_med N) (rm_smul vertex_obj[N] r a)
    ≈ mlim_smul r (cmon_map (mcar_med N) a).
Proof.
  apply mlim_ext; intro j.
  rewrite mcar_med_commutes, mlim_smul_triangle, mcar_med_commutes.
  apply (rm_map_smul (cone_leg N j)).
Qed.

Program Definition mlim_med (N : Cone K) :
  vertex_obj[N] ~{RMod R}~> LimitMod := {| rm_hom := mcar_med N |}.
Next Obligation. intros N r m; apply mcar_med_smul. Qed.

Definition mlim_created : IsALimit K LimitMod.
Proof.
  unshelve refine {| limit_acone := @coneFrom _ _ _ mlim_cone |}.
  intro N.
  unshelve refine {| unique_obj := mlim_med N |}.
  - intros j a.
    exact (mcar_med_commutes N j a).
  - intros v Hv a.
    exact (limit_med_unique (limit_is_alimit L)
             (FCone (RMod_Forget_Ab R) N) (rm_hom v) Hv a).
Defined.

(* 相关说明。 （已译） *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma mlim_smul_unique
  (s : carrier (rig_setoid (ring_rig R)) →
       carrier (cmon_setoid (ab_cmon vertex_obj[L])) →
       carrier (cmon_setoid (ab_cmon vertex_obj[L])))
  (Hs : ∀ (j : J) r a,
     cmon_map (mlim_leg j) (s r a)
       ≈ rm_smul (K j) r (cmon_map (mlim_leg j) a))
  (r : carrier (rig_setoid (ring_rig R)))
  (a : carrier (cmon_setoid (ab_cmon vertex_obj[L]))) :
  s r a ≈ mlim_smul r a.
Proof.
  apply mlim_ext; intro j.
  now rewrite Hs, mlim_smul_triangle.
Qed.

End ModLift.

(* 相关说明。 （已译） *)

Section ModReflect.

Context {R : RingObject}.
Context {J : Category}.
Context (K : J ⟶ RMod R).
Context (M : Cone K).
Context (HM : IsLimitCone (FCone (RMod_Forget_Ab R) M)).

Definition mrefl_med (N : Cone K) :
  rm_ab vertex_obj[N] ~{Ab}~> rm_ab vertex_obj[M] :=
  limit_med (limitcone_isalimit HM) (FCone (RMod_Forget_Ab R) N).

Lemma mrefl_med_commutes (N : Cone K) (j : J)
  (a : carrier (cmon_setoid (ab_cmon (rm_ab vertex_obj[N])))) :
  cmon_map (rm_hom (cone_leg M j)) (cmon_map (mrefl_med N) a)
    ≈ cmon_map (rm_hom (cone_leg N j)) a.
Proof using All.
  exact (limit_med_commutes (limitcone_isalimit HM)
           (FCone (RMod_Forget_Ab R) N) j a).
Qed.

Definition mrefl_sets_limit :=
  limitcone_isalimit
    (Ab_Forget_creates_continuous J (RMod_Forget_Ab R ◯ K)
       (FCone (RMod_Forget_Ab R) M) HM).

Lemma mrefl_ext (x y : carrier (cmon_setoid (ab_cmon (rm_ab vertex_obj[M])))) :
  (∀ j : J, cmon_map (rm_hom (cone_leg M j)) x
              ≈ cmon_map (rm_hom (cone_leg M j)) y) → x ≈ y.
Proof using All. exact (absets_limit_ext mrefl_sets_limit x y). Qed.

Lemma mrefl_med_smul (N : Cone K) (r : carrier (rig_setoid (ring_rig R)))
  (a : carrier (cmon_setoid (ab_cmon (rm_ab vertex_obj[N])))) :
  cmon_map (mrefl_med N) (rm_smul vertex_obj[N] r a)
    ≈ rm_smul vertex_obj[M] r (cmon_map (mrefl_med N) a).
Proof using All.
  apply mrefl_ext; intro j.
  rewrite mrefl_med_commutes.
  rewrite (rm_map_smul (cone_leg N j)).
  rewrite (rm_map_smul (cone_leg M j)).
  now rewrite mrefl_med_commutes.
Qed.

Program Definition mrefl_hom (N : Cone K) :
  vertex_obj[N] ~{RMod R}~> vertex_obj[M] := {| rm_hom := mrefl_med N |}.
Next Obligation. intros N r m; apply mrefl_med_smul. Qed.

Definition rmod_reflects : IsLimitCone M.
Proof using All.
  intro N.
  unshelve refine {| unique_obj := mrefl_hom N |}.
  - intros j a.
    exact (mrefl_med_commutes N j a).
  - intros v Hv a.
    exact (limit_med_unique (limitcone_isalimit HM)
             (FCone (RMod_Forget_Ab R) N) (rm_hom v) Hv a).
Defined.

End ModReflect.

(* 相关说明。 （已译） *)

Section ModStrictlyCreates.

Context {R : RingObject}.
Context {J : Category}.
Context (K : J ⟶ RMod R).

Definition rmod_strict_lift (N : Cone (RMod_Forget_Ab R ◯ K))
  (HN : IsLimitCone N) : StrictLift K (RMod_Forget_Ab R) N :=
  @Build_StrictLift J (RMod R) Ab K (RMod_Forget_Ab R) N
    (mlim_cone K (@Build_Limit J Ab (RMod_Forget_Ab R ◯ K) N HN))
    eq_refl
    (fun x => reflexivity _).

Definition RMod_Forget_Ab_StrictlyCreatesLimit :
  StrictlyCreatesLimit K (RMod_Forget_Ab R).
Proof.
  unshelve refine {| screates := rmod_strict_lift |}.
  - intros N HN.
    exact (@ump_limit _ _ _ _
             (mlim_created K (@Build_Limit J Ab (RMod_Forget_Ab R ◯ K) N HN))).
  - intros M HM.
    exact (rmod_reflects K M HM).
Defined.

Definition RMod_Forget_Ab_CreatesLimit : CreatesLimit K (RMod_Forget_Ab R) :=
  StrictlyCreatesLimit_CreatesLimit RMod_Forget_Ab_StrictlyCreatesLimit.

End ModStrictlyCreates.

Definition RMod_Forget_Ab_StrictlyCreatesLimits (R : RingObject) :
  StrictlyCreatesLimits (RMod_Forget_Ab R) :=
  fun J K => RMod_Forget_Ab_StrictlyCreatesLimit K.

Definition RMod_Forget_Ab_creates_limits (R : RingObject) :
  CreatesAllLimits (RMod_Forget_Ab R) :=
  fun J K => RMod_Forget_Ab_CreatesLimit K.

Definition RMod_Forget_Ab_reflects_limits {R : RingObject} {J : Category}
  (K : J ⟶ RMod R) : ReflectsLimitCone K (RMod_Forget_Ab R) :=
  creates_reflects_limits (RMod_Forget_Ab_CreatesLimit K).

Definition RMod_lift_cone_unique {R : RingObject} {J : Category}
  (K : J ⟶ RMod R) (N : Cone (RMod_Forget_Ab R ◯ K)) (HN : IsLimitCone N)
  (M : Cone K) (i : ConeIso (FCone (RMod_Forget_Ab R) M) N) :
  ConeIso M (slift_cone (screates N HN)) :=
  screates_lift_unique (RMod_Forget_Ab_StrictlyCreatesLimit K) N HN M i.

(* 相关说明。 （已译） *)

Example rmod_fcone_apex {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (N : Cone K) :
  vertex_obj[FCone (RMod_Forget_Ab R) N] = rm_ab vertex_obj[N] := eq_refl.

Example rmod_fcone_leg {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (N : Cone K) (j : J) :
  cone_leg (FCone (RMod_Forget_Ab R) N) j = rm_hom (cone_leg N j) := eq_refl.

(* 相关说明。 （已译） *)

Definition RMod_Forget_Ab_lifts_limits {R : RingObject} {J : Category}
  (K : J ⟶ RMod R) (L : Limit (RMod_Forget_Ab R ◯ K)) : Limit K :=
  creates_limit_lift (RMod_Forget_Ab_CreatesLimit K) L.

Example rmod_lift_apex {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (L : Limit (RMod_Forget_Ab R ◯ K)) :
  RMod_Forget_Ab R (vertex_obj[RMod_Forget_Ab_lifts_limits K L])
    = vertex_obj[L] := eq_refl.

Example rmod_lift_legs {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (L : Limit (RMod_Forget_Ab R ◯ K)) (j : J) :
  fmap[RMod_Forget_Ab R]
    (cone_leg (@limit_cone _ _ _ (RMod_Forget_Ab_lifts_limits K L)) j)
    = limit_leg (limit_is_alimit L) j := eq_refl.

(* * * Corollaries: [RMod R] complete, both forgetful 函子 are
 continuous （已译） *)

Definition RMod_Complete (R : RingObject) : @Complete (RMod R) :=
  creates_limits_Complete (RMod_Forget_Ab R) Ab_Complete
    (RMod_Forget_Ab_creates_limits R).

Definition RMod_Forget_Ab_creates_continuous (R : RingObject) :
  ContinuousFunctor (RMod_Forget_Ab R) :=
  creates_limits_continuous (RMod_Forget_Ab R) Ab_Complete
    (RMod_Forget_Ab_creates_limits R).

Definition RMod_Forget_Ab_PreservesAllLimits (R : RingObject) :
  PreservesAllLimits (RMod_Forget_Ab R) :=
  creates_limits_PreservesAllLimits (RMod_Forget_Ab R) Ab_Complete
    (RMod_Forget_Ab_creates_limits R).

Definition RMod_Forget_composite_continuous (R : RingObject) :
  ContinuousFunctor (Ab_Forget ◯ RMod_Forget_Ab R) :=
  continuous_compose (RMod_Forget_Ab_creates_continuous R)
    Ab_Forget_creates_continuous.

(*
   本节说明 Limit 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example rmod_forget_obj_agrees {R : RingObject} (M : RMod R) :
  RMod_Forget R M = (Ab_Forget ◯ RMod_Forget_Ab R) M := eq_refl.

Example rmod_forget_map_agrees {R : RingObject} {M N : RMod R}
  (f : M ~{RMod R}~> N) :
  fmap[RMod_Forget R] f = fmap[Ab_Forget ◯ RMod_Forget_Ab R] f := eq_refl.

Section ModForgetCone.

Context {R : RingObject}.
Context {J : Category}.
Context (K : J ⟶ RMod R).

(* The repackaging bridge: same apex, same legs, same coherence 证明, a
 different record type. Structure/Limit/Preservation.v's
 [cone_assoc] same move across 函子 associativity. （已译） *)

Definition rmod_abcone_of (N : Cone (RMod_Forget R ◯ K)) :
  Cone ((Ab_Forget ◯ RMod_Forget_Ab R) ◯ K) :=
  @Build_Cone J Sets ((Ab_Forget ◯ RMod_Forget_Ab R) ◯ K)
    (@vertex_obj _ _ _ N)
    (@Build_ACone J Sets (@vertex_obj _ _ _ N)
       ((Ab_Forget ◯ RMod_Forget_Ab R) ◯ K)
       (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x)
       (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)).

End ModForgetCone.

Definition RMod_Forget_creates_continuous (R : RingObject) :
  ContinuousFunctor (RMod_Forget R) :=
  fun J K N HN M =>
    RMod_Forget_composite_continuous R J K N HN (rmod_abcone_of K M).

Definition RMod_Forget_PreservesAllLimits (R : RingObject) :
  PreservesAllLimits (RMod_Forget R) :=
  Continuous_PreservesAllLimits (RMod_Forget_creates_continuous R).

(* 相关说明。 （已译） *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section RModComputed.

Context {R : RingObject}.
Context {J : Category}.
Context (K : J ⟶ RMod R).

Example rmod_complete_carrier :
  cmon_setoid (ab_cmon (rm_ab (vertex_obj[RMod_Complete R J K])))
    = Sets_limit_obj (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K)) := eq_refl.

Example rmod_complete_plus
  (a b : carrier (Sets_limit_obj (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K))))
  (d : J) :
  `1 (cmon_plus (rm_ab (vertex_obj[RMod_Complete R J K])) a b) d
    = cmon_plus (rm_ab (K d)) (`1 a d) (`1 b d) := eq_refl.

Example rmod_complete_zero (d : J) :
  `1 (cmon_zero (rm_ab (vertex_obj[RMod_Complete R J K]))) d
    = cmon_zero (rm_ab (K d)) := eq_refl.

Example rmod_complete_neg
  (a : carrier (Sets_limit_obj (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K))))
  (d : J) :
  `1 (ab_neg (rm_ab (vertex_obj[RMod_Complete R J K])) a) d
    = ab_neg (rm_ab (K d)) (`1 a d) := eq_refl.

Example rmod_complete_smul (r : carrier (rig_setoid (ring_rig R)))
  (a : carrier (Sets_limit_obj (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K))))
  (d : J) :
  `1 (rm_smul (vertex_obj[RMod_Complete R J K]) r a) d
    = rm_smul (K d) r (`1 a d) := eq_refl.

Example rmod_complete_leg (d : J) :
  cmon_map (rm_hom (cone_leg (@limit_cone _ _ _ (RMod_Complete R J K)) d))
    = Sets_limit_leg (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K)) d := eq_refl.

End RModComputed.
