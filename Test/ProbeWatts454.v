(*
   本文件为测试：ProbeWatts454。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Opposite.
Require Import Category.Adjunction.Continuity.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.Limit.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Limit.
Require Import Category.Functor.Hom.Continuous.
Require Import Category.Functor.Representable.
Require Import Category.Functor.Representable.Additive.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Structure.WellPowered.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.AbCategory.
Require Import Category.Structure.Projective.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Instance.Ab.Character.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Limit.
Require Import Category.Instance.Mod.Bimodule.
Require Import Category.Instance.Mod.Coextension.
Require Import Category.Instance.Mod.Representable.
Require Import Category.Instance.Mod.WellPowered.
Require Import Category.Instance.Mod.Colimit.
Require Import Category.Instance.Mod.HomTensor.
Require Import Category.Instance.Mod.Cogenerator.
Require Import Category.Adjunction.Additive.
Require Import Category.Adjunction.SAFT.
Require Import Category.Adjunction.SAFT.Characterization.
Require Import Category.Adjunction.SAFT.Characterization.Corollaries.
Require Import Category.Adjunction.Compose.
Require Import Category.Adjunction.Representability.Sets.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Ab.Free.
Require Import Category.Instance.Mod.Watts.Unconditional.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Subobject.Quotient.
Require Import Category.Structure.Generator.
Require Import Category.Structure.Generator.Dual.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Instance.Mod.Quotient.
Require Import Category.Instance.Mod.Spanning.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Limit.Finite.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Instance.Mod.Free.
Require Import Category.Instance.Mod.TensorAFT.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lia.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Instance.Ab.Monoidal.
Require Import Category.Adjunction.Unitalization.
Require Import Category.Structure.Cone.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Mod.Watts.

Generalizable All Variables.

(** ** Instrument: the refutation keyword is live *)

Fail Check probe454_absent_name.

(** ** N1 (INSTANCE): Functor/Representable/Additive.v *)

(* CONTROL: [LocallyPropositional_op_at], restated. *)
Example p454_lp_op_at@{o h +} {C : Category@{o h h}}
  (LP : LocallyPropositional C) (x y : C) :
  @locally_prop (C^op) (LocallyPropositional_op LP) x y
    = @locally_prop C LP y x := eq_refl.

(* CONTROL: [HomAb_fmap_at] and [CoHomAb_fmap_at], restated. *)
Example p454_homab_fmap_at@{o h a +} {C : Category@{o h h}}
  {LP : LocallyPropositional C} (AC : AbEnriched C) (A0 : C) {x y : C}
  (f : x ~{C}~> y) (g : A0 ~{C}~> x) :
  cmon_map (fmap[HomAb AC A0 : C ⟶ Ab@{a h}] f) g = f ∘ g := eq_refl.

Example p454_cohomab_fmap_at@{o h a +} {C : Category@{o h h}}
  {LP : LocallyPropositional C} (AC : AbEnriched C) (A0 : C) {x y : C}
  (f : y ~{C}~> x) (g : x ~{C}~> A0) :
  cmon_map (fmap[CoHomAb AC A0 : C^op ⟶ Ab@{a h}] f) g = g ∘ f := eq_refl.

(* CONTROL: the two components of [watt_ab_iso] ARE the representation's
   ([watt_ab_iso_to_at] and [watt_ab_iso_from_at], restated). *)
Example p454_watt_to_at@{o h a s +} {C : Category@{o h h}}
  {LP : LocallyPropositional C} (AC : AbEnriched C) (T : C ⟶ Ab@{a h})
  (AF : @AdditiveFunctor C Ab@{a h} AC Ab_AbEnriched T)
  (Rp : Representable (Ab_Forget@{a s h} ◯ T)) (x : C)
  (f : wab_obj Rp ~{C}~> x) :
  cmon_map (transform[to (watt_ab_iso AC T AF Rp)] x) f
    = transform[to (@represented _ _ Rp)] x f := eq_refl.

Example p454_watt_from_at@{o h a s +} {C : Category@{o h h}}
  {LP : LocallyPropositional C} (AC : AbEnriched C) (T : C ⟶ Ab@{a h})
  (AF : @AdditiveFunctor C Ab@{a h} AC Ab_AbEnriched T)
  (Rp : Representable (Ab_Forget@{a s h} ◯ T)) (x : C)
  (t : carrier (cmon_setoid (T x))) :
  cmon_map (transform[from (watt_ab_iso AC T AF Rp)] x) t
    = transform[from (@represented _ _ Rp)] x t := eq_refl.

(* CONTROL: at (RMod R)^op the local propositionality passed
   explicitly. *)
Definition p454_lp_explicit (R : RingObject) (T : (RMod R)^op ⟶ Ab)
  (AF : @AdditiveFunctor _ _ (AbEnriched_op (RMod_AbEnriched R))
          Ab_AbEnriched T)
  (Rp : Representable (Ab_Forget ◯ T)) :=
  @watt_ab_iso _ (LocallyPropositional_op _)
    (AbEnriched_op (RMod_AbEnriched R)) T AF Rp.

Fail Definition p454_n1_lp_by_resolution (R : RingObject)
  (T : (RMod R)^op ⟶ Ab)
  (AF : @AdditiveFunctor _ _ (AbEnriched_op (RMod_AbEnriched R))
          Ab_AbEnriched T)
  (Rp : Representable (Ab_Forget ◯ T)) :=
  watt_ab_iso (AbEnriched_op (RMod_AbEnriched R)) T AF Rp.

(* CONTROL: [HomAb_continuous] and [CoHomAb_continuous], restated; the
   second IS the first at the opposite category. *)
Definition p454_homab_cont@{o h a +} {C : Category@{o h h}}
  {LP : LocallyPropositional C} (AC : AbEnriched C) (A0 : C) :
  ContinuousFunctor (HomAb AC A0 : C ⟶ Ab@{a h}) :=
  HomAb_continuous AC A0.

Definition p454_cohomab_cont@{o h a +} {C : Category@{o h h}}
  {LP : LocallyPropositional C} (AC : AbEnriched C) (A0 : C) :
  ContinuousFunctor (CoHomAb AC A0 : C^op ⟶ Ab@{a h}) :=
  CoHomAb_continuous AC A0.

Example p454_cohomab_cont_is_op@{o h a +} {C : Category@{o h h}}
  {LP : LocallyPropositional C} (AC : AbEnriched C) (A0 : C) :
  (CoHomAb_continuous AC A0
     : ContinuousFunctor (CoHomAb AC A0 : C^op ⟶ Ab@{a h}))
    = @HomAb_continuous (C^op) (LocallyPropositional_op LP)
        (AbEnriched_op AC) A0 := eq_refl.

(** ** N2, N3 (CONVERSION, UNIVERSE): Instance/Mod/HomTensor.v *)

(* CONTROL: [homzl_ring_group] and [homzl_ring_act], restated. *)
Example p454_homzl_group@{ra +} (R : RingObject@{ra ra ra}) (G : AbObject) :
  rm_ab (HomZL (Ring_RMod (Ring_op R)) G) = rm_ab (CoextObj R G) :=
  eq_refl.

Example p454_homzl_act@{ra +} (R : RingObject@{ra ra ra}) (G : AbObject)
  r f s :
  cmon_map (rm_smul (HomZL (Ring_RMod (Ring_op R)) G) r f) s
    = cmon_map (rm_smul (CoextObj R G) r f) s := eq_refl.

(* CONTROL: the identity-map isomorphism [homzl_coext_iso]. *)
Definition p454_homzl_coext_iso@{r +} (R : RingObject@{r r r})
  (G : AbObject@{r r r}) :
  HomZL (Ring_RMod (Ring_op R)) G ≅[RMod R] CoextObj R G :=
  homzl_coext_iso G.

Fail Example p454_n2_homzl_is_coext@{ra +} (R : RingObject@{ra ra ra})
  (G : AbObject) :
  HomZL (Ring_RMod (Ring_op R)) G = CoextObj R G := eq_refl.

(* CONTROL: the first leg keeps the ring's three universes apart. *)
Definition p454_tensor_homZ_apart@{ra rc rp +| rc < ra, rp < ra +}
  {R : RingObject@{ra rc rp}} (B : RModObject (Ring_op R)) :=
  tensor_homZ_adjunction B.

(* CONTROL: [homzl_ring_adjunction] at [RingObject@{r r r}]. *)
Definition p454_homzl_ring_adj@{r +} {R : RingObject@{r r r}} :=
  @homzl_ring_adjunction R.

Fail Definition p454_n3_homzl_ring_apart@{ra rc rp +| rc < ra, rp < ra +}
  {R : RingObject@{ra rc rp}} :=
  @homzl_ring_adjunction R.

(** ** N4, N5 (UNIVERSE, BINDER): Instance/Mod/Cogenerator.v *)

(* CONTROL: [RMod_Cogenerator_large] is a cogenerator, indexed at the
   object universe. *)
Definition p454_large_cog@{a c p o x +|
    Set < o, c < o, c < x, p <= a, c <= a, a <= o +}
  (R : RingObject@{a c p}) : Cogenerator@{o o c} (RMod@{o x a p c} R) :=
  RMod_Cogenerator_large R.

(* CONTROL: [cogen_prod] at [RMod_Complete R] takes a cogenerator indexed
   at the carrier universe. *)
Definition p454_small_cog_prod@{a c p o x +|
    Set < o, c < o, c < x, p <= a, c <= a, a <= o +}
  (R : RingObject@{a c p}) (G : Cogenerator@{c o c} (RMod@{o x a p c} R)) :
  RMod@{o x a p c} R :=
  cogen_prod (RMod_Complete R) G.

(* CONTROL: [QZ_cogen_prod], restated. *)
Definition p454_qz_cogen_prod@{r a +} (R : RingObject@{r r r})
  (HC : QZ_family_cogenerates@{a r r _ _}) : RMod R :=
  cogen_prod (RMod_Complete R) (coext_cogenerator R (QZ_Cogenerator HC)).

Fail Definition p454_n4_large_cog_prod@{a c p o x +|
    Set < o, c < o, c < x, p <= a, c <= a, a <= o +}
  (R : RingObject@{a c p}) : RMod@{o x a p c} R :=
  cogen_prod (RMod_Complete R) (RMod_Cogenerator_large R).

(* CONTROL: an adjunction whose two categories share their hom
   universe. *)
Definition p454_adj_one_hom@{co do h +}
  (C : Category@{co h h}) (D : Category@{do h h})
  (F : D ⟶ C) (U : C ⟶ D) : Type :=
  F ⊣ U.

Fail Definition p454_n5_adj_two_homs@{co hc do hd +| hc < hd +}
  (C : Category@{co hc hc}) (D : Category@{do hd hd})
  (F : D ⟶ C) (U : C ⟶ D) : Type :=
  F ⊣ U.

(* CONTROL: the transferred cogenerator's member at [eq_refl]
   ([right_adjoint_cogenerator_obj] and [QZ_injective_cogenerator_member],
   restated). *)
Example p454_ra_cog_obj@{co do h c +}
  {C : Category@{co h h}} {D : Category@{do h h}} {F : D ⟶ C}
  {U : C ⟶ D} (A : F ⊣ U) (HF : Faithful F) (G : Cogenerator@{c co h} C)
  (j : cog_index G) :
  cog_obj (right_adjoint_cogenerator A HF G) j = fobj[U] (cog_obj G j) :=
  eq_refl.

Example p454_qz_member@{r a c +} (R : RingObject@{r r r})
  (HI : @Injective Ab@{a r} QZ) (HC : QZ_family_cogenerates@{a r c _ _})
  (u : poly_unit@{c}) :
  cog_obj (snd (QZ_injective_cogenerator R HI HC)) u = CoextObj R QZ :=
  eq_refl.

(* CONTROL: the metatheorems at their stated types. *)
Definition p454_qz_dne@{a h c +} (HC : QZ_family_cogenerates@{a h c _ _}) :
  ∀ P : Prop, ~~P → P :=
  QZ_cogenerates_Ab_DNE HC.

Definition p454_qz_wlem@{a h +} (HI : @Injective Ab@{a h} QZ) :
  ∀ P : Prop, (~ P) + (~~ P) :=
  QZ_injective_WLEM HI.

Definition p454_stable_dne@{c a h +} (G : Cogenerator@{c a h} Ab@{a h})
  (stable : ∀ j (a b : carrier (cmon_setoid (cog_obj G j))),
              ((a ≈ b → False) → False) → a ≈ b) :
  ∀ P : Prop, ~~P → P :=
  cogenerator_stable_DNE G stable.

Definition p454_stable_dne_Z@{c m h +}
  (G : Cogenerator@{c m h} (RMod Int_Ring))
  (stable : ∀ j (a b : carrier (cmon_setoid (rm_ab (cog_obj G j)))),
              ((a ≈ b → False) → False) → a ≈ b) :
  ∀ P : Prop, ~~P → P :=
  cogenerator_stable_DNE_Z G stable.

Definition p454_coext_dne@{r c +}
  (HC : ∀ (x y : RMod Int_Ring@{r r r}) (f g : x ~{RMod Int_Ring}~> y),
          (∀ (u : poly_unit@{c})
             (k : y ~{RMod Int_Ring}~> CoextObj Int_Ring@{r r r} QZ),
             k ∘ f ≈ k ∘ g) → f ≈ g) :
  ∀ P : Prop, ~~P → P :=
  coext_QZ_cogenerates_DNE HC.

Definition p454_coext_wlem@{r +}
  (HI : @Injective (RMod Int_Ring) (CoextObj Int_Ring@{r r r} QZ)) :
  ∀ P : Prop, (~ P) + (~~ P) :=
  coext_QZ_injective_WLEM HI.

(** ** N6-N13, N28 (UNIVERSE, TYPING, BINDER): Instance/Mod/WellPowered.v *)

(* CONTROL: (2) at the pin, under [U]. *)
Definition p454_wp_pin_U@{a c p o x +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} (U : Untruncate@{c}) :
  WellPowered@{o c c o x} (RMod@{o x a p c} R) :=
  fun W => RMod_WellPoweredAt_untruncate U W.

(* CONTROL: (1) one universe up, with nothing assumed; its fifth slot
   is x. *)
Definition p454_wp_up@{a c p o x w +|
    Set < o, c < o, c < x, p <= a, c <= a, a <= o, c < w +}
  {R : RingObject@{a c p}} (W : obj[RMod@{o x a p c} R]) :
  WellPoweredAt@{w o o c x} W :=
  RMod_WellPoweredAt_up W.

Fail Definition p454_n6_wp_up_at_pin@{a c p o x +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} :
  WellPowered@{o c c o x} (RMod@{o x a p c} R) :=
  fun W => RMod_WellPoweredAt_up W.

Fail Definition p454_n7_wp_up_fifth_slot@{a c p o x w +|
    Set < o, c < o, c < x, p <= a, c <= a, a <= o, c < w, x < w +}
  {R : RingObject@{a c p}} (W : obj[RMod@{o x a p c} R]) :
  WellPoweredAt@{w o o c w} W :=
  RMod_WellPoweredAt_up W.

Fail Definition p454_n28_wp_up_fifth_slot_below@{a c p o x w +|
    Set < o, c < o, c < x, p <= a, c <= a, a <= o, c < w, w < x +}
  {R : RingObject@{a c p}} (W : obj[RMod@{o x a p c} R]) :
  WellPoweredAt@{w o o c w} W :=
  RMod_WellPoweredAt_up W.

(* CONTROL: (3) at the pin, under [U]. *)
Definition p454_cwp_pin_U@{a c p o x +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} (U : Untruncate@{c}) :
  CoWellPowered@{o c c o x} (RMod@{o x a p c} R) :=
  fun W => RMod_CoWellPoweredAt_untruncate U W.

(* CONTROL: (5) one universe up, with nothing assumed, and at
   [RingObject@{c c c}] with [c < w] alone. *)
Definition p454_cwp_up@{a c p o x w +|
    Set < o, c < o, c < x, p <= a, c <= a, a <= o, c < w, a <= w +}
  {R : RingObject@{a c p}} :
  ∀ W : obj[RMod@{o x a p c} R],
    @WellPoweredAt@{w o o c x} ((RMod@{o x a p c} R)^op) W :=
  RMod_CoWellPowered_up.

Definition p454_cwp_up_ccc@{c o x w +| Set < o, c < o, c < x, c < w +}
  {R : RingObject@{c c c}} :
  ∀ W : obj[RMod@{o x c c c} R],
    @WellPoweredAt@{w o o c x} ((RMod@{o x c c c} R)^op) W :=
  fun W => RMod_CoWellPoweredAt_up W.

Fail Definition p454_n8_cwp_up_at_pin@{a c p o x +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} :
  CoWellPowered@{o c c o x} (RMod@{o x a p c} R) :=
  fun W => RMod_CoWellPoweredAt_up W.

(* CONTROL: [pim_fn]'s body, restated, spending [U]. *)
Definition p454_pim_fn_U@{a c p o x +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} (U : Untruncate@{c})
  {W : obj[RMod@{o x a p c} R]} (m : @SubObj (RMod@{o x a p c} R) W)
  (p : smod_carrier (psm_sub (pimage (Subobject.sub_mono m)))) :
  smod_carrier (subobj_smod m) :=
  existT (fun b => smod_mem (subobj_smod m) b) (`1 p) (U _ (`2 p)).

Fail Definition p454_n9_pim_fn_no_U@{a c p o x +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}}
  {W : obj[RMod@{o x a p c} R]} (m : @SubObj (RMod@{o x a p c} R) W)
  (p : smod_carrier (psm_sub (pimage (Subobject.sub_mono m)))) :
  smod_carrier (subobj_smod m) :=
  existT (fun b => smod_mem (subobj_smod m) b) (`1 p) ((`2 p) _ (fun x => x)).

(* CONTROL: [pre_fn]'s body, restated, spending [U]. *)
Definition p454_pre_fn_U@{a c p o x +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} (U : Untruncate@{c})
  {W : obj[RMod@{o x a p c} R]} (u : @QuotObj (RMod@{o x a p c} R) W)
  (q : carrier (cmon_setoid (quot_cod u))) : carrier (cmon_setoid W) :=
  `1 (U _ (squash_of_ex
             (rmod_epic_surjective (quot_epi u) (quot_is_epic u) q))).

Fail Definition p454_n10_pre_fn_match@{a c p o x +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}}
  {W : obj[RMod@{o x a p c} R]} (u : @QuotObj (RMod@{o x a p c} R) W)
  (q : carrier (cmon_setoid (quot_cod u))) : carrier (cmon_setoid W) :=
  match rmod_epic_surjective (quot_epi u) (quot_is_epic u) q with
  | ex_intro _ a _ => a
  end.

(* CONTROL: the ring as a module over itself at [RingObject@{c c c}]. *)
Definition p454_ring_obj_ccc@{c o x +| Set < o, c < o, c < x +}
  (R : RingObject@{c c c}) : obj[RMod@{o x c c c} R] :=
  Ring_RMod R.

Fail Definition p454_n11_ring_obj_apart@{a c p o x +|
    Set < o, c < o, c < x, p <= a, c < a, a <= o +}
  (R : RingObject@{a c p}) : obj[RMod@{o x a p c} R] :=
  Ring_RMod R.

(* CONTROL: (2)'s record under a CLOSED universe list: its universes
   are exactly the five named. *)
Definition p454_wp_record_closed@{a c p o x |
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} (U : Untruncate@{c})
  (W : obj[RMod@{o x a p c} R]) : WellPoweredAt@{c o o c x} W :=
  {| wp_index   := PSubmodule W;
     wp_to      := fun P => smod_subobj (psm_sub P);
     wp_from    := fun m => pimage (Subobject.sub_mono m);
     wp_to_from := pim_to_from U |}.

(* CONTROL: (3)'s record under an extensible universe list. *)
Definition p454_cwp_record@{a c p o x +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} (U : Untruncate@{c})
  (W : obj[RMod@{o x a p c} R]) :
  @WellPoweredAt@{c o o c x} ((RMod@{o x a p c} R)^op) W :=
  {| wp_index   := PSubmodule W;
     wp_to      := pquot;
     wp_from    := fun u => pker (quot_epi u);
     wp_to_from := cwp_to_from U |}.

Fail Definition p454_n12_cwp_record_closed@{a c p o x |
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} (U : Untruncate@{c})
  (W : obj[RMod@{o x a p c} R]) :
  @WellPoweredAt@{c o o c x} ((RMod@{o x a p c} R)^op) W :=
  {| wp_index   := PSubmodule W;
     wp_to      := pquot;
     wp_from    := fun u => pker (quot_epi u);
     wp_to_from := cwp_to_from U |}.

(* CONTROL: (5)'s construction with [RModPropSurjective] unfolded into
   its [Prop], as one term, under an extensible universe list. *)
Definition p454_cwp_up_unfolded@{a c p o x w +| c < w, a <= w +}
  {R : RingObject@{a c p}} (W : obj[RMod@{o x a p c} R]) :
  @WellPoweredAt@{w o o c x} ((RMod@{o x a p c} R)^op) W :=
  {| wp_index := { Q : RModObject@{c a c c c a c p} R
                 & { e : W ~{RMod@{o x a p c} R}~> Q &
                     ∀ b : carrier (cmon_setoid Q),
                       (exists a0 : carrier (cmon_setoid W),
                          @pequiv _ _ (cmon_prop Q)
                            (cmon_map (rm_hom e) a0) b)%type } };
     wp_to := fun i => @mk_quot (RMod@{o x a p c} R) W (`1 i) (`1 (`2 i))
                         (rmod_prop_surjective_epic _ (`2 (`2 i)));
     wp_from := fun u => existT _ (quot_cod u)
                  (existT _ (quot_epi u)
                     (rmod_epic_surjective _ (quot_is_epic u)));
     wp_to_from := ltac:(intro u; exists iso_id; simpl; cat) |}.

Fail Definition p454_n13_cwp_up_closed@{a c p o x w | c < w, a <= w +}
  {R : RingObject@{a c p}} (W : obj[RMod@{o x a p c} R]) :
  @WellPoweredAt@{w o o c x} ((RMod@{o x a p c} R)^op) W :=
  {| wp_index := { Q : RModObject@{c a c c c a c p} R
                 & { e : W ~{RMod@{o x a p c} R}~> Q &
                     ∀ b : carrier (cmon_setoid Q),
                       (exists a0 : carrier (cmon_setoid W),
                          @pequiv _ _ (cmon_prop Q)
                            (cmon_map (rm_hom e) a0) b)%type } };
     wp_to := fun i => @mk_quot (RMod@{o x a p c} R) W (`1 i) (`1 (`2 i))
                         (rmod_prop_surjective_epic _ (`2 (`2 i)));
     wp_from := fun u => existT _ (quot_cod u)
                  (existT _ (quot_epi u)
                     (rmod_epic_surjective _ (quot_is_epic u)));
     wp_to_from := ltac:(intro u; exists iso_id; simpl; cat) |}.

(** ** N14, N15 (UNIVERSE): Instance/Mod/Colimit.v *)

(* CONTROL: the solution set at a [Set] carrier. *)
Definition p454_sols_at_set@{go gx ga gp +|
    Set < go, Set < gx, gp <= ga, ga <= go +}
  (R : RingObject@{ga Set gp}) (J : Category@{Set Set Set})
  (D : J ⟶ RMod@{go gx ga gp Set} R) :=
  @Diagonal_RMod_solution_set R J D.

(* CONTROL: the colimit above [Set]. *)
Definition p454_colim_above_set@{a c p o x jo +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, jo <= c +}
  (R : RingObject@{a c p}) (J : Category@{jo c c}) :=
  RMod_colim_via_GAFT R J.

Fail Definition p454_n14_colim_at_set@{go gx ga gp +|
    Set < go, Set < gx, gp <= ga, ga <= go +}
  (R : RingObject@{ga Set gp}) (J : Category@{Set Set Set}) :=
  RMod_colim_via_GAFT R J.

(* CONTROL: each initial object alone, the adjoint functor theorem's and
   Instance/Mod.v's zero module, the latter at a [Set] carrier. *)
Definition p454_initial_via_gaft (R : RingObject) :=
  RMod_Initial_via_GAFT R.

Definition p454_zero_module@{a +} (R : RingObject@{a Set a}) :=
  RMod_Initial R.

(* CONTROL: [initial_unique] between two copies of the adjoint functor
   theorem's initial module. *)
Definition p454_initial_unique_gaft (R : RingObject) :=
  initial_unique (RMod_Initial_via_GAFT R) (RMod_Initial_via_GAFT R).

Fail Definition p454_n15_initial_vs_zero (R : RingObject) :=
  initial_unique (RMod_Initial_via_GAFT R) (RMod_Initial R).

(** ** N16-N23, N29-N34 (CONVERSION, UNIVERSE): Instance/Mod/Watts.v *)

(* CONTROL: [watts_ex3_forget_obj], restated: the representing object is
   the ring up to isomorphism. *)
Definition p454_ex3_forget_obj@{c o x b g +} (R : RingObject@{c c c})
  (G : Cogenerator@{g o c} (RMod@{o x c c c} R)) (U : Untruncate@{c}) :
  projT1 (watts_ex3_forget R G U
           : { A : RMod@{o x c c c} R &
               @Isomorphism (@Fun (RMod@{o x c c c} R) Ab@{b c})
                 (HomAb (RMod_AbEnriched R) A) (RMod_Forget_Ab R) })
    ≅[RMod@{o x c c c} R] Ring_RMod R :=
  watts_ex3_forget_obj R G U.

Fail Example p454_n16_ex3_forget_obj_refl@{c o x b g +}
  (R : RingObject@{c c c})
  (G : Cogenerator@{g o c} (RMod@{o x c c c} R)) (U : Untruncate@{c}) :
  projT1 (watts_ex3_forget R G U
           : { A : RMod@{o x c c c} R &
               @Isomorphism (@Fun (RMod@{o x c c c} R) Ab@{b c})
                 (HomAb (RMod_AbEnriched R) A) (RMod_Forget_Ab R) })
    = Ring_RMod R := eq_refl.

(* CONTROL: [watt_at_forget], restated: no hypothesis, and the
   representing object [Ring_RMod R] by conversion. *)
Definition p454_watt_at_forget@{c o x b +} (R : RingObject@{c c c}) :
  @Isomorphism (@Fun (RMod@{o x c c c} R) Ab@{b c})
    (HomAb (RMod_AbEnriched R) (Ring_RMod R)) (RMod_Forget_Ab R) :=
  watt_at_forget R.

(* CONTROL: [watts_theorem_sets]'s body at [RingObject@{c c c}]. *)
Definition p454_sets_ccc@{c o x a pk pa ra rt +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  Representable@{ra rt pa o c} (Ab_Forget ◯ T) :=
  continuous_Set_functor_representable (Ab_Forget ◯ T)
    (Complete_op_of_Cocomplete (RMod_Cocomplete_via_GAFT R))
    (Continuous_PreservesImageLimit
       (continuous_compose (PreservesImageLimit_Continuous contT)
          Ab_Forget_creates_continuous))
    (RModop_Cogenerator R) (RMod_CoWellPowered_untruncate U).

(* CONTROL: the same body with the ring's three universes named apart and
   no constraint among them. *)
Definition p454_sets_apart_free@{a c p o x b pk pa ra rt +}
  {R : RingObject@{a c p}} (T : (RMod@{o x a p c} R)^op ⟶ Ab@{b c})
  (contT : @PreservesImageLimit@{o c b c pk c pa c}
             ((RMod@{o x a p c} R)^op) Ab@{b c} T)
  (U : Untruncate@{c}) :
  Representable@{ra rt pa o c} (Ab_Forget@{b pa c} ◯ T) :=
  continuous_Set_functor_representable (Ab_Forget ◯ T)
    (Complete_op_of_Cocomplete (RMod_Cocomplete_via_GAFT R))
    (Continuous_PreservesImageLimit
       (continuous_compose (PreservesImageLimit_Continuous contT)
          Ab_Forget_creates_continuous))
    (RModop_Cogenerator R) (RMod_CoWellPowered_untruncate U).

(* CONTROL: Exercise 3's form keeps the ring's universes strictly
   apart. *)
Definition p454_ex3_apart@{a c p o x b g pk pa ra rt +| c < a, p < a +}
  {R : RingObject@{a c p}} (T : RMod@{o x a p c} R ⟶ Ab@{b c})
  (AF : @AdditiveFunctor (RMod@{o x a p c} R) Ab@{b c}
          (RMod_AbEnriched R) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o c b c pk c pa c}
             (RMod@{o x a p c} R) Ab@{b c} T)
  (G : Cogenerator@{g o c} (RMod@{o x a p c} R))
  (U : Untruncate@{c}) :=
  watts_ex3 T AF contT G U.

Fail Definition p454_n17_sets_apart@{a c p o x b pk pa ra rt +| c < a +}
  {R : RingObject@{a c p}} (T : (RMod@{o x a p c} R)^op ⟶ Ab@{b c})
  (contT : @PreservesImageLimit@{o c b c pk c pa c}
             ((RMod@{o x a p c} R)^op) Ab@{b c} T)
  (U : Untruncate@{c}) :
  Representable@{ra rt pa o c} (Ab_Forget@{b pa c} ◯ T) :=
  continuous_Set_functor_representable (Ab_Forget ◯ T)
    (Complete_op_of_Cocomplete (RMod_Cocomplete_via_GAFT R))
    (Continuous_PreservesImageLimit
       (continuous_compose (PreservesImageLimit_Continuous contT)
          Ab_Forget_creates_continuous))
    (RModop_Cogenerator R) (RMod_CoWellPowered_untruncate U).

(* CONTROL: R as a cogenerator of (RMod R)^op at [RingObject@{c c c}]. *)
Definition p454_rmodop_cog_ccc@{c o x +| Set < o, c < o, c < x +}
  (R : RingObject@{c c c}) : Cogenerator ((RMod@{o x c c c} R)^op) :=
  RModop_Cogenerator R.

Fail Definition p454_n18_rmodop_cog_apart@{a c p o x +|
    Set < o, c < o, c < x, p <= a, c < a, a <= o +}
  (R : RingObject@{a c p}) : Cogenerator ((RMod@{o x a p c} R)^op) :=
  RModop_Cogenerator R.

Fail Definition p454_n19_sets_level_above_pa@{c o x a s pk pa ra rt +|
    pa < s +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  Representable@{ra rt s o c} (Ab_Forget@{a s c} ◯ T) :=
  continuous_Set_functor_representable (Ab_Forget ◯ T)
    (Complete_op_of_Cocomplete (RMod_Cocomplete_via_GAFT R))
    (Continuous_PreservesImageLimit
       (continuous_compose (PreservesImageLimit_Continuous contT)
          Ab_Forget_creates_continuous))
    (RModop_Cogenerator R) (RMod_CoWellPowered_untruncate U).

Fail Definition p454_n29_sets_level_below_pa@{c o x a s pk pa ra rt +|
    s < pa +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  Representable@{ra rt s o c} (Ab_Forget@{a s c} ◯ T) :=
  continuous_Set_functor_representable (Ab_Forget ◯ T)
    (Complete_op_of_Cocomplete (RMod_Cocomplete_via_GAFT R))
    (Continuous_PreservesImageLimit
       (continuous_compose (PreservesImageLimit_Continuous contT)
          Ab_Forget_creates_continuous))
    (RModop_Cogenerator R) (RMod_CoWellPowered_untruncate U).

(* CONTROL: the opposite of the forgetful functor is continuous, a right
   adjoint by [coex_adjunction], with its [Ab] at RMod's object
   universe. *)
Definition p454_forget_op_cont@{c o x +| Set < o, c < o, c < x +}
  (R : RingObject@{c c c}) :
  ContinuousFunctor
    (Opposite_Functor (RMod_Forget_Ab R : RMod@{o x c c c} R ⟶ Ab@{o c})) :=
  right_adjoint_Continuous (Opposite_Adjunction _ _ (coex_adjunction R)).

Fail Definition p454_n20_forget_op_cont_above@{c o x m +|
    Set < o, c < o, c < x, o < m +}
  (R : RingObject@{c c c}) :
  ContinuousFunctor
    (Opposite_Functor (RMod_Forget_Ab R : RMod@{o x c c c} R ⟶ Ab@{m c})) :=
  right_adjoint_Continuous (Opposite_Adjunction _ _ (coex_adjunction R)).

Fail Definition p454_n30_forget_op_cont_below@{c o x m +|
    Set < o, c < o, c < x, m < o +}
  (R : RingObject@{c c c}) :
  ContinuousFunctor
    (Opposite_Functor (RMod_Forget_Ab R : RMod@{o x c c c} R ⟶ Ab@{m c})) :=
  right_adjoint_Continuous (Opposite_Adjunction _ _ (coex_adjunction R)).

(* CONTROL: [HomAbForget_continuous]'s body, the header's composite form,
   with the composite's intermediate [Ab] at RMod's object universe. *)
Definition p454_hafc_body_at_o@{c o x b +} (R : RingObject@{c c c})
  (A : AbObject@{c c c}) :
  ContinuousFunctor (@CoHomAb Ab@{o c} _ Ab_AbEnriched A
                       ◯ Opposite_Functor (RMod_Forget_Ab@{x o o c c c} R)
                     : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}) :=
  continuous_compose
    (right_adjoint_Continuous (Opposite_Adjunction _ _ (coex_adjunction R)))
    (CoHomAb_continuous Ab_AbEnriched A).

Fail Definition p454_n31_hafc_body_above_o@{c o x m b +| o < m +}
  (R : RingObject@{c c c}) (A : AbObject@{c c c}) :
  ContinuousFunctor (@CoHomAb Ab@{m c} _ Ab_AbEnriched A
                       ◯ Opposite_Functor (RMod_Forget_Ab@{x o m c c c} R)
                     : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}) :=
  continuous_compose
    (right_adjoint_Continuous (Opposite_Adjunction _ _ (coex_adjunction R)))
    (CoHomAb_continuous Ab_AbEnriched A).

Fail Definition p454_n32_hafc_body_below_o@{c o x m b +| m < o +}
  (R : RingObject@{c c c}) (A : AbObject@{c c c}) :
  ContinuousFunctor (@CoHomAb Ab@{m c} _ Ab_AbEnriched A
                       ◯ Opposite_Functor (RMod_Forget_Ab@{x o m c c c} R)
                     : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}) :=
  continuous_compose
    (right_adjoint_Continuous (Opposite_Adjunction _ _ (coex_adjunction R)))
    (CoHomAb_continuous Ab_AbEnriched A).

(* CONTROL: [HomAbForget_continuous] with its tenth slot at x. *)
Definition p454_hafc_at_x@{c o x b +} (R : RingObject@{c c c})
  (A : AbObject@{c c c}) :
  ContinuousFunctor@{_ _ _ _ _ _ _ _ _ x}
    (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}) :=
  HomAbForget_continuous R A.

Fail Definition p454_n21_hafc_above_x@{c o x b k6 +| x < k6 +}
  (R : RingObject@{c c c}) (A : AbObject@{c c c}) :
  ContinuousFunctor@{_ _ _ _ _ _ _ _ _ k6}
    (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}) :=
  HomAbForget_continuous R A.

Fail Definition p454_n22_hafc_below_x@{c o x b k6 +| k6 < x +}
  (R : RingObject@{c c c}) (A : AbObject@{c c c}) :
  ContinuousFunctor@{_ _ _ _ _ _ _ _ _ k6}
    (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}) :=
  HomAbForget_continuous R A.

(* CONTROL: [HomAbForget_continuous]'s body with its tenth slot at x. *)
Definition p454_hafc_body_at_x@{c o x b +} (R : RingObject@{c c c})
  (A : AbObject@{c c c}) :
  ContinuousFunctor@{_ _ _ _ _ _ _ _ _ x}
    (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}) :=
  continuous_compose
    (right_adjoint_Continuous (Opposite_Adjunction _ _ (coex_adjunction R)))
    (CoHomAb_continuous Ab_AbEnriched A).

Fail Definition p454_n33_hafc_body_above_x@{c o x b k6 +| x < k6 +}
  (R : RingObject@{c c c}) (A : AbObject@{c c c}) :
  ContinuousFunctor@{_ _ _ _ _ _ _ _ _ k6}
    (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}) :=
  continuous_compose
    (right_adjoint_Continuous (Opposite_Adjunction _ _ (coex_adjunction R)))
    (CoHomAb_continuous Ab_AbEnriched A).

Fail Definition p454_n34_hafc_body_below_x@{c o x b k6 +| k6 < x +}
  (R : RingObject@{c c c}) (A : AbObject@{c c c}) :
  ContinuousFunctor@{_ _ _ _ _ _ _ _ _ k6}
    (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}) :=
  continuous_compose
    (right_adjoint_Continuous (Opposite_Adjunction _ _ (coex_adjunction R)))
    (CoHomAb_continuous Ab_AbEnriched A).

(* CONTROL: a draft of [watts_ex3] that elaborates [watts_ex3_sets]
   twice, accepted with [s < x] declared. *)
Definition p454_ex3_twice@{a c p o x b s g +| s < x +}
  {R : RingObject@{a c p}} (T : RMod@{o x a p c} R ⟶ Ab@{b c})
  (AF : @AdditiveFunctor (RMod@{o x a p c} R) Ab@{b c}
          (RMod_AbEnriched R) Ab_AbEnriched T)
  (contT : ContinuousFunctor T)
  (G : Cogenerator@{g o c} (RMod@{o x a p c} R))
  (U : Untruncate@{c}) :
  { A : RMod@{o x a p c} R &
    @Isomorphism (@Fun (RMod@{o x a p c} R) Ab@{b c})
      (HomAb (RMod_AbEnriched R) A) T }.
Proof.
  exists (wab_obj (watts_ex3_sets T (Continuous_PreservesImageLimit contT) G U
                    : Representable (Ab_Forget@{b s c} ◯ T))).
  exact (watt_ab_iso (RMod_AbEnriched R) T AF
           (watts_ex3_sets T (Continuous_PreservesImageLimit contT) G U)).
Defined.

(* CONTROL: [watts_theorem_obj] and [watts_ex3_QZ_cogenerator],
   restated. *)
Example p454_watts_obj@{c o x a pk pa ra rt +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (AF : @AdditiveFunctor ((RMod@{o x c c c} R)^op) Ab@{a c}
          (AbEnriched_op (RMod_AbEnriched R)) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  projT1 (watts_theorem T AF contT U)
    = @repr_obj _ _ (watts_theorem_sets T contT U
                      : Representable@{ra rt pa o c} (Ab_Forget ◯ T)) :=
  eq_refl.

Example p454_ex3_qz_cog@{r o x +}
  {R : RingObject@{r r r}} (HI : @Injective Ab@{o r} QZ)
  (HC : QZ_family_cogenerates) :
  snd (QZ_injective_cogenerator R HI HC)
    = coext_cogenerator R (QZ_Cogenerator HC) := eq_refl.

(* CONTROL: [watts_theorem_Fz], restated: the representing object is F ℤ
   up to isomorphism. *)
Definition p454_watts_Fz@{c o x a pk pa ra rt +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (AF : @AdditiveFunctor ((RMod@{o x c c c} R)^op) Ab@{a c}
          (AbEnriched_op (RMod_AbEnriched R)) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  projT1 (watts_theorem T AF contT U)
    ≅[RMod@{o x c c c} R]
  fobj[projT1 (watts_theorem_adjoint T contT U)] (FreeAb SetsOne) :=
  watts_theorem_Fz T AF contT U.

Fail Example p454_n23_Fz_refl@{c o x a pk pa ra rt +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (AF : @AdditiveFunctor ((RMod@{o x c c c} R)^op) Ab@{a c}
          (AbEnriched_op (RMod_AbEnriched R)) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  projT1 (watts_theorem T AF contT U)
    = fobj[projT1 (watts_theorem_adjoint T contT U)] (FreeAb SetsOne) :=
  eq_refl.

(* CONTROL: [ab_hom_Z_iso], restated. *)
Definition p454_ab_hom_Z@{a c +} :
  @Isomorphism (@Fun Ab@{a c} Ab@{a c})
    (HomAb Ab_AbEnriched (FreeAb SetsOne)) Id[Ab@{a c}] :=
  ab_hom_Z_iso.

(* CONTROL: [watts_theorem_via_unconditional], restated, and its body at
   [eq_refl], which does not mention [U]. *)
Definition p454_via_unconditional@{c o x a pk pa +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (AF : @AdditiveFunctor ((RMod@{o x c c c} R)^op) Ab@{a c}
          (AbEnriched_op (RMod_AbEnriched R)) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  { A : RMod@{o x c c c} R &
    @Isomorphism (@Fun ((RMod@{o x c c c} R)^op) Ab@{a c})
      (CoHomAb (RMod_AbEnriched R) A) T } :=
  watts_theorem_via_unconditional T AF contT U.

Example p454_via_unconditional_body@{c o x a pk pa +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (AF : @AdditiveFunctor ((RMod@{o x c c c} R)^op) Ab@{a c}
          (AbEnriched_op (RMod_AbEnriched R)) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  watts_theorem_via_unconditional T AF contT U
    = watts_theorem_unconditional T AF (PreservesImageLimit_Continuous contT) :=
  eq_refl.

(* CONTROL: [watts_unconditional_coext] and its [_2a], restated: with no
   [Untruncate], the module the unconditional theorem returns at
   [HomAbForget R A] is the coextension, and hom_ℤ(R, A). *)
Definition p454_unc_coext@{c o x b +} (R : RingObject@{c c c})
  (A : AbObject@{c c c}) :
  projT1 (watts_theorem_unconditional
            (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c})
            (HomAbForget_additive R A) (HomAbForget_continuous R A))
    ≅[RMod@{o x c c c} R] CoextObj R A :=
  watts_unconditional_coext R A.

Definition p454_unc_coext_2a@{c o x b +} (R : RingObject@{c c c})
  (A : AbObject@{c c c}) :
  projT1 (watts_theorem_unconditional
            (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c})
            (HomAbForget_additive R A) (HomAbForget_continuous R A))
    ≅[RMod@{o x c c c} R] HomZL (Ring_RMod (Ring_op R)) A :=
  watts_unconditional_coext_2a R A.

(** ** N24-N27 (UNIVERSE, CONVERSION): Instance/Mod/Watts/Unconditional.v *)

(* CONTROL: the theorem at ℤ above [Set], the ring's universes collapsed
   and apart. *)
Definition p454_unc_Z_ccc@{c o x b +|
    Set < c, c < o, c < x, Set < b, c < b +}
  (A : RMod@{o x c c c} Int_Ring@{c c c}) :=
  watts_unconditional_at_Z A.

Definition p454_unc_Z_apart@{c p a o x b +|
    Set < c, c <= a, p <= a, a <= o, c < o, c < x, Set < b, c < b +}
  (A : RMod@{o x a p c} Int_Ring@{c p a}) :=
  watts_unconditional_at_Z A.

(* CONTROL: the category of ℤ-modules at a [Set] carrier is formed. *)
Definition p454_rmod_at_set@{o x +| Set < o, Set < x +} :=
  RMod@{o x Set Set Set} Int_Ring@{Set Set Set}.

Fail Definition p454_n24_unc_Z_at_set@{o x b +}
  (A : RMod@{o x Set Set Set} Int_Ring@{Set Set Set}) :=
  watts_unconditional_at_Z A.

(* CONTROL: the theorem with the ring's carrier above [Set] and its three
   universes strictly apart. *)
Definition p454_unc_apart@{a c p o x b s +|
    Set < c, c < o, c < x, p < a, c < a, a <= o, c < s, Set < b, c < b +}
  {R : RingObject@{a c p}} (T : (RMod@{o x a p c} R)^op ⟶ Ab@{b c})
  (AF : @AdditiveFunctor _ _ (AbEnriched_op (RMod_AbEnriched R))
          Ab_AbEnriched T)
  (contT : ContinuousFunctor@{_ _ _ _ _ _ _ _ _ s} T) :=
  watts_theorem_unconditional T AF contT.

Fail Definition p454_n25_unc_at_set@{o x b s +}
  (R : RingObject@{Set Set Set})
  (T : (RMod@{o x Set Set Set} R)^op ⟶ Ab@{b Set})
  (AF : @AdditiveFunctor _ _ (AbEnriched_op (RMod_AbEnriched R))
          Ab_AbEnriched T)
  (contT : ContinuousFunctor T) :=
  watts_theorem_unconditional T AF contT.

(* CONTROL: RMod's second universe x and the target's s apart, in both
   orders. *)
Definition p454_unc_x_below_s@{a c p o x b s +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, c < s, Set < b, c < b,
    x < s +}
  {R : RingObject@{a c p}} (T : (RMod@{o x a p c} R)^op ⟶ Ab@{b c})
  (AF : @AdditiveFunctor _ _ (AbEnriched_op (RMod_AbEnriched R))
          Ab_AbEnriched T)
  (contT : ContinuousFunctor@{_ _ _ _ _ _ _ _ _ s} T) :=
  watts_theorem_unconditional T AF contT.

Definition p454_unc_s_below_x@{a c p o x b s +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, c < s, Set < b, c < b,
    s < x +}
  {R : RingObject@{a c p}} (T : (RMod@{o x a p c} R)^op ⟶ Ab@{b c})
  (AF : @AdditiveFunctor _ _ (AbEnriched_op (RMod_AbEnriched R))
          Ab_AbEnriched T)
  (contT : ContinuousFunctor@{_ _ _ _ _ _ _ _ _ s} T) :=
  watts_theorem_unconditional T AF contT.

(* CONTROL: [ew_ev_g0] and [ew_t_at], restated. *)
Example p454_ev_g0@{a c p o x +|
    Set < o, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} {M : obj[RMod@{o x a p c} R]}
  (m : carrier (cmon_setoid M)) :
  cmon_map (rm_hom (ew_ev@{a c p o x} m)) ew_g0 = m := eq_refl.

Example p454_t_at@{a c p o x s +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, c < s +}
  {R : RingObject@{a c p}} (K : (RMod@{o x a p c} R)^op ⟶ Sets@{c s})
  (M : obj[RMod@{o x a p c} R]) (x0 : carrier (K M))
  (m : carrier (cmon_setoid M)) :
  cmon_map (rm_hom (ew_t K M x0)) m
    = cmon_map (rm_hom (ew_inj K (ew_am K M x0 m))) ew_g0 := eq_refl.

(* CONTROL: the value N26 compares with is an element of the fixed
   coproduct, and the object N27 compares with is a module. *)
Definition p454_cop_zero@{a c p o x s +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, c < s +}
  {R : RingObject@{a c p}} (K : (RMod@{o x a p c} R)^op ⟶ Sets@{c s}) :
  carrier (cmon_setoid (ew_Cop K)) :=
  cmon_zero (ew_Cop K).

Definition p454_cop_obj@{a c p o x b s +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, c < s, Set < b, c < b +}
  {R : RingObject@{a c p}} (T : (RMod@{o x a p c} R)^op ⟶ Ab@{b c}) :
  obj[RMod@{o x a p c} R] :=
  ew_Cop (Ab_Forget@{b s c} ◯ T).

Fail Example p454_n26_t_at_zero@{a c p o x s +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, c < s +}
  {R : RingObject@{a c p}} (K : (RMod@{o x a p c} R)^op ⟶ Sets@{c s})
  (M : obj[RMod@{o x a p c} R]) (x0 : carrier (K M))
  (m : carrier (cmon_setoid M)) :
  cmon_map (rm_hom (ew_t K M x0)) m = cmon_zero (ew_Cop K) := eq_refl.

(* CONTROL: [watts_theorem_unconditional_obj], restated. *)
Example p454_unc_obj@{a c p o x b s +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, c < s, Set < b, c < b +}
  {R : RingObject@{a c p}} (T : (RMod@{o x a p c} R)^op ⟶ Ab@{b c})
  (AF : @AdditiveFunctor _ _ (AbEnriched_op (RMod_AbEnriched R))
          Ab_AbEnriched T)
  (contT : ContinuousFunctor@{_ _ _ _ _ _ _ _ _ s} T) :
  projT1 (watts_theorem_unconditional T AF contT)
    = wab_obj (RModop_continuous_representable (Ab_Forget@{b s c} ◯ T)
                 (continuous_compose contT Ab_Forget_creates_continuous)) :=
  eq_refl.

Fail Example p454_n27_unc_obj_is_cop@{a c p o x b s +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, c < s, Set < b, c < b +}
  {R : RingObject@{a c p}} (T : (RMod@{o x a p c} R)^op ⟶ Ab@{b c})
  (AF : @AdditiveFunctor _ _ (AbEnriched_op (RMod_AbEnriched R))
          Ab_AbEnriched T)
  (contT : ContinuousFunctor@{_ _ _ _ _ _ _ _ _ s} T) :
  projT1 (watts_theorem_unconditional T AF contT)
    = ew_Cop (Ab_Forget@{b s c} ◯ T) :=
  eq_refl.

(** ** Guard block *)

(* Functor/Representable/Additive.v: 35 names *)
Check @LocallyPropositional_op.
Check @LocallyPropositional_op_at.
Check @HomAb_fmap.
Check @HomAb.
Check @HomAb_obj.
Check @HomAb_fmap_at.
Check @HomAb_additive.
Check @HomAb_forget_to.
Check @HomAb_forget_from.
Check @HomAb_forget_iso.
Check @HomAb_representable.
Check @CoHomAb.
Check @CoHomAb_fmap_at.
Check @wab_obj.
Check @wab_to.
Check @wab_from.
Check @wab_elem.
Check @wab_to_elem.
Check @wab_to_padd.
Check @wab_to_pzero.
Check @wab_to_from.
Check @wab_from_to.
Check @wab_to_hom.
Check @wab_from_hom.
Check @wab_to_nat.
Check @wab_from_nat.
Check @watt_ab_iso.
Check @watt_ab_iso_to_at.
Check @watt_ab_iso_from_at.
Check @watt_ab_repr.
Check @watt_ab_iso_HomAb.
Check @watt_ab_iso_HomAb_obj.
Check @watt_ab_iso_at_Ab.
Check @HomAb_continuous.
Check @CoHomAb_continuous.
(* Instance/Mod/HomTensor.v: 74 names *)
Check @hzl_group.
Check @hzl_act.
Check @hzl_act_respects.
Check @hzl_act_distr_l.
Check @hzl_act_distr_r.
Check @hzl_act_assoc.
Check @hzl_act_one.
Check @HomZL.
Check @hzl_map_ab.
Check @HomZLMap.
Check @HomZLF.
Check @tb_bal.
Check @TensorBF.
Check @ht_to_inner.
Check @ht_to_ab.
Check @ht_to.
Check @ht_bal.
Check @ht_from.
Check @ht_adj.
Check @tensor_homZ_adjunction.
Check @ht_to_at.
Check @hzr_group.
Check @hzr_act.
Check @hzr_act_respects.
Check @hzr_act_distr_l.
Check @hzr_act_distr_r.
Check @hzr_act_assoc.
Check @hzr_act_one.
Check @HomZR.
Check @hzr_map_ab.
Check @HomZRMap.
Check @HomZRF.
Check @ta_bal.
Check @TensorAF.
Check @th_to_inner.
Check @th_to_ab.
Check @th_to.
Check @th_bal.
Check @th_adj.
Check @homZ_tensor_adjunction.
Check @hom_hom_swap.
Check @hom_hom_swap_at.
Check @hom_hom_swap_iso.
Check @hom_hom_swap_iso_to.
Check @hom_hom_swap_iso_from_at.
Check @hom_hom_swap_natural.
Check @TensorBF_AFT_obj.
Check @TensorBF_AFT_fmap.
Check @TensorBF_AFT.
Check @TensorBF_AFT_iso.
Check @hom_tensor_adjunction.
Check @hom_tensor_adjunction_to_at.
Check @TensorAF_AFT_obj.
Check @TensorAF_AFT_fmap.
Check @TensorAF_AFT.
Check @TensorAF_AFT_iso.
Check @hom_tensor_adjunction_right.
Check @hom_tensor_adjunction_right_to_at.
Check @homzl_ring_group.
Check @homzl_ring_act.
Check @runit_bal.
Check @runit_to.
Check @runit_from.
Check @runit_gen.
Check @ring_unit_iso.
Check @ring_unit_iso_to_at.
Check @ring_unit_iso_from_at.
Check @ring_unit_nat.
Check @homzl_ring_adjunction.
Check @homzl_ring_adjunction_to_at.
Check @homzl_ring_adjunction_is_coex_at.
Check @homzl_coext_to.
Check @homzl_coext_from.
Check @homzl_coext_iso.
(* Instance/Mod/Cogenerator.v: 84 names *)
Check @right_adjoint_injective.
Check @right_adjoint_cogenerator.
Check @right_adjoint_cogenerator_obj.
Check @forget_ab_monic.
Check @forget_ab_faithful.
Check @coext_injective.
Check @coext_cogenerator.
Check @QZ_family_cogenerates.
Check @QZ_Cogenerator.
Check @QZ_injective_cogenerator.
Check @QZ_injective_cogenerator_member.
Check @QZ_injective_cogenerator_via_2a.
Check @QZ_injective_cogenerator_via_2a_member.
Check @ML_cogenerates.
Check @right_adjoint_ML.
Check @QZ_injective_cogenerator_ML.
Check @QZ_cogen_prod.
Check @RMod_Cogenerator_large.
Check @QZ_divisible.
Check @qz_sum_cong.
Check @q_add_mul.
Check @q_one_mul.
Check @q_zero_mul.
Check @q_succ_mul.
Check @q_neg_mul.
Check @zchar_pos.
Check @zchar_determined.
Check @q_baer_step.
Check @zchar.
Check @QZ_extends_along_mul.
Check @QZ_extends_along_mul_is_zchar.
Check @AbZMod.
Check @AbZModMap.
Check @Ab_to_ZMod.
Check @Ab_to_ZMod_group.
Check @Ab_to_ZMod_smul.
Check @Ab_to_ZMod_fmap.
Check @yp_eq.
Check @yp_equiv.
Check @yp_setoid.
Check @yp_prop.
Check @yp_plus_respects_prop.
Check @yp_plus_respects.
Check @YP.
Check @yp_zero.
Check @yp_true_false_prop.
Check @yp_true_false.
Check @bp_xor.
Check @bp_kill.
Check @bp_kill_xor.
Check @bp_eq.
Check @bp_xor_self.
Check @bp_xor_comm.
Check @bp_xor_trans.
Check @bp_equiv.
Check @bp_setoid.
Check @bp_prop.
Check @bp_plus_respects_prop.
Check @bp_eq_of_eq.
Check @bp_xor_assoc.
Check @bp_xor_zero_l.
Check @BP.
Check @bp_incl_respects_prop.
Check @bp_incl.
Check @bp_incl_injective_prop.
Check @bp_incl_monic.
Check @qz_half.
Check @qz_half_nonzero.
Check @z2_eq_bool.
Check @z2_half.
Check @cogenerator_stable_DNE.
Check @qz_stable.
Check @QZ_cogenerates_Ab_DNE.
Check @QZ_injective_WLEM.
Check @YPZ.
Check @BPZ.
Check @ypz_zero.
Check @bpz_incl.
Check @bpz_incl_monic.
Check @cogenerator_stable_DNE_Z.
Check @coext_QZ_stable.
Check @coext_QZ_cogenerates_DNE.
Check @z2_half_Z.
Check @coext_QZ_injective_WLEM.
(* Instance/Mod/WellPowered.v: 37 names *)
Check @RMod_WellPoweredAt_up.
Check @PSubmodule.
Check @Build_PSubmodule.
Check @psm_mem.
Check @psm_resp.
Check @psm_zero.
Check @psm_plus.
Check @psm_smul.
Check @psm_sub.
Check @pimage.
Check @pim_fn.
Check @tim_fn.
Check @pim_to_tim.
Check @tim_to_pim.
Check @pim_le.
Check @pim_ge.
Check @pim_to_from.
Check @RMod_WellPoweredAt_untruncate.
Check @RMod_WellPowered_untruncate.
Check @pker.
Check @pquot.
Check @squash_of_ex.
Check @pre_fn.
Check @pre_spec.
Check @rel_of_image.
Check @image_of_rel.
Check @pre_map.
Check @ev_map.
Check @pre_iso.
Check @cwp_to_from.
Check @RMod_CoWellPoweredAt_untruncate.
Check @RMod_CoWellPowered_untruncate.
Check @RMod_ring_separates.
Check @RMod_Generator.
Check @RModop_Cogenerator.
Check @RMod_CoWellPoweredAt_up.
Check @RMod_CoWellPowered_up.
(* Instance/Mod/Colimit.v: 41 names *)
Check @Colimit.MGen.
Check @mins.
Check @IsModCongruence.
Check @Build_IsModCongruence.
Check @mc_refl.
Check @mc_sym.
Check @mc_trans.
Check @mc_gen.
Check @mc_plus.
Check @mc_neg.
Check @mc_smul.
Check @IsModCoconeCong.
Check @Build_IsModCoconeCong.
Check @mcc_mod.
Check @mcc_resp.
Check @mcc_zero.
Check @mcc_plus.
Check @mcc_smul.
Check @mcc_nat.
Check @MDCongIdx.
Check @MDQ_Setoid.
Check @MDQ_smul_respects.
Check @MDQ.
Check @mdq_leg.
Check @mdq_arr.
Check @mflat.
Check @mker.
Check @mker_cocone.
Check @mker_idx.
Check @mker_med.
Check @Diagonal_RMod_solution_set.
Check @RMod_colim_via_GAFT.
Check @RMod_Cocomplete_via_GAFT.
Check @RMod_FinitelyCocomplete_via_GAFT.
Check @RMod_Cocartesian_via_GAFT.
Check @RMod_HasCoequalizers_via_GAFT.
Check @RMod_Initial_via_GAFT.
Check @RMod_initial_via_GAFT_trivial.
Check @RMod_inl_via_GAFT_retract.
Check @RMod_inl_via_GAFT_injective.
Check @RMod_coproduct_via_GAFT_nontrivial.
(* Instance/Mod/Watts.v: 27 names *)
Check @RMod_Forget_Ab_additive.
Check @watts_theorem_sets.
Check @watts_theorem_adjoint.
Check @watts_theorem.
Check @watts_theorem_obj.
Check @watts_theorem_to_at.
Check @watts_ex3_sets.
Check @watts_ex3.
Check @watts_ex3_QZ.
Check @watts_ex3_QZ_cogenerator.
Check @watts_ex3_forget.
Check @RMod_Forget_equiv.
Check @watt_at_forget.
Check @watts_ex3_forget_obj.
Check @HomAbForget.
Check @HomAbForget_additive.
Check @HomAbForget_continuous.
Check @watts_theorem_coext.
Check @coext_representable.
Check @watts_theorem_coext_obj.
Check @watts_theorem_coext_obj_2a.
Check @Ab_Forget_Id_equiv.
Check @ab_hom_Z_iso.
Check @watts_theorem_Fz.
Check @watts_theorem_via_unconditional.
Check @watts_unconditional_coext.
Check @watts_unconditional_coext_2a.
(* Instance/Mod/Watts/Unconditional.v: 61 names *)
Check @MSObj.
Check @ms_mod.
Check @ms_free.
Check @ms_gen.
Check @MSObj_rect.
Check @MSObj_ind.
Check @MSObj_rec.
Check @MSObj_sind.
Check @MSHom.
Check @ms_id.
Check @ms_comp.
Check @MultiSpan.
Check @ms_fobj.
Check @ms_fmap.
Check @ms_diagram.
Check @sets_limit_point.
Check @ew_Gen.
Check @ew_g0.
Check @ew_ev.
Check @ew_ev_g0.
Check @ew_Idx.
Check @ew_CopD.
Check @ew_CC.
Check @ew_CopL.
Check @ew_Cop.
Check @ew_inj.
Check @ew_y0_ex.
Check @ew_y0.
Check @ew_y0_leg.
Check @ew_am.
Check @ew_PD.
Check @ew_PL.
Check @ew_P.
Check @ew_pM.
Check @ew_pF.
Check @ew_pG.
Check @ew_pM_ev.
Check @ew_pF_inj.
Check @ew_key.
Check @ew_efam.
Check @ew_e_ex.
Check @ew_e.
Check @ew_e_leg.
Check @ew_N.
Check @ew_Q.
Check @ew_k.
Check @ew_qrel_of.
Check @ew_tfun.
Check @ew_t.
Check @ew_t_at.
Check @ew_k_t.
Check @ew_eQ.
Check @ew_t_covers.
Check @ew_WIdx.
Check @RModop_esols.
Check @RModop_continuous_representable.
Check @watts_theorem_unconditional.
Check @watts_theorem_unconditional_obj.
Check @watts_unconditional_CoHomAb_obj.
Check @RModop_hom_representable_obj.
Check @watts_unconditional_at_Z.
