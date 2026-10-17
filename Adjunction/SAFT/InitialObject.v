Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.WeaklyInitial.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Finite.
Require Import Category.Structure.Complete.
Require Import Category.Structure.WellPowered.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.SAFT.

Generalizable All Variables.

(* * * The special initial-对象 定理 （已译） *)

(*
   nLab:      https://ncatlab.org/nlab/show/adjoint+functor+theorem
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functor_theorem

   本文件给出特殊伴随函子定理相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Definition equalizer_sub@{o h +} {C : Category@{o h h}} {x : C} (w : SubObj x)
  {c q : C} {f g : Subobject.sub_dom w ~> c} {e : q ~> Subobject.sub_dom w}
  (E : IsEqualizer f g q e) : SubObj x :=
  @Build_SubObj C x q (Subobject.sub_mono w ∘ e)
    (monic_compose (Subobject.sub_is_monic w) (equalizer_monic f g E)).

Lemma least_sub_arrows_agree@{o h +} {C : Category@{o h h}}
  (HE : HasEqualizers C) {x : C}
  (w : SubObj x) (Hw : ∀ v : SubObj x, sub_le w v)
  {c : C} (f g : Subobject.sub_dom w ~> c) : f ≈ g.
Proof.
  destruct (@equalizer C HE _ _ f g) as [q [e E]].
  destruct (Hw (equalizer_sub w E)) as [s Hs]; simpl in Hs.
  assert (Hes : e ∘ s ≈ id).
  { apply (monic (Monic := Subobject.sub_is_monic w)).
    rewrite comp_assoc, Hs; cat. }
  rewrite <- (id_right f), <- (id_right g), <- Hes, !comp_assoc.
  now rewrite (fork_eq E).
Qed.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition cogen_prod_to_power@{o h so +| h <= so +} {C : Category@{o h h}}
  (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (c : C) :
  cogen_prod comp G ~> cogen_power comp G c :=
  unique_obj (iprod_ump (cogen_power_fam G c) (cogen_power_limit comp G c)
                (cogen_prod comp G)
                (fun p => iprod_proj (cog_obj G) (cogen_prod_limit comp G)
                            (projT1 p))).

(* [c] as a subobject of its power: the separation content. *)
Definition cogen_canonical_sub@{o h so +| h <= so +} {C : Category@{o h h}}
  (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (c : C) : SubObj (cogen_power comp G c) :=
  @Build_SubObj C (cogen_power comp G c) c (cogen_canonical comp G c)
    (cogenerator_canonical_monic comp G c).

Definition complete_pullbacks@{o h r so +| so <= r, h <= r +}
  {C : Category@{o h h}} (comp : @Complete@{r so h o} C) : HasPullbacks C :=
  FinitelyComplete_HasPullbacks (Complete_FinitelyComplete comp).

(* Its pullback along k: a subobject of the cogenerator product. *)
Definition cogen_pullback_sub@{o h so +| h <= so +} {C : Category@{o h h}}
  (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (c : C) : SubObj (cogen_prod comp G) :=
  @sub_reindex C (complete_pullbacks comp) _ _
    (cogen_prod_to_power comp G c) (cogen_canonical_sub comp G c).

Definition cogen_pullback_to@{o h so +| h <= so +} {C : Category@{o h h}}
  (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (c : C) :
  Subobject.sub_dom (cogen_pullback_sub comp G c) ~> c :=
  pullback_snd _ _ (@pullback C (complete_pullbacks comp) _ _ _
                      (cogen_prod_to_power comp G c)
                      (cogen_canonical comp G c)).

(* 相关说明。 （已译） *)
Definition special_initial_zero@{o h so +| h <= so +} {C : Category@{o h h}}
  (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (w : SubObj (cogen_prod comp G))
  (Hw : ∀ v : SubObj (cogen_prod comp G), sub_le w v) (c : C) :
  Subobject.sub_dom w ~> c :=
  cogen_pullback_to comp G c ∘ `1 (Hw (cogen_pullback_sub comp G c)).

(* * ** The 定理 over least subobject （已译） *)

Definition special_initial_object_least@{o h so +| h <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (w : SubObj (cogen_prod comp G))
  (Hw : ∀ v : SubObj (cogen_prod comp G), sub_le w v) : @Initial C.
Proof.
  unshelve refine (@Build_Terminal (C^op) (Subobject.sub_dom w) _ _).
  - intro c.
    exact (special_initial_zero comp G w Hw c).
  - intros c f g.
    exact (@least_sub_arrows_agree C (Complete_HasEqualizers comp) _ w Hw
             c f g).
Defined.

(* 相关说明。 （已译） *)

Definition least_of_intersection_all@{o h q +| o <= q, h <= q +}
  {C : Category@{o h h}} {x : C} (w : SubObj x)
  (Hw : IsIntersection@{o h q} (fun m : SubObj x => m) w) :
  ∀ v : SubObj x, sub_le w v :=
  inter_le _ _ Hw.

Definition intersection_all_of_least@{o h q +| o <= q, h <= q +}
  {C : Category@{o h h}} {x : C} (w : SubObj x)
  (Hw : ∀ v : SubObj x, sub_le w v) :
  IsIntersection@{o h q} (fun m : SubObj x => m) w :=
  @Build_IsIntersection C x (SubObj x) (fun m : SubObj x => m) w
    Hw (fun v Hv => Hv w).

(* * ** The 定理: intersection all subobjects product （已译） *)

Definition special_initial_object@{o h so q +| h <= so, o <= q, h <= q +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (w : SubObj (cogen_prod comp G))
  (Hw : IsIntersection@{o h q} (fun m : SubObj (cogen_prod comp G) => m) w) :
  @Initial C :=
  special_initial_object_least comp G w (least_of_intersection_all w Hw).

Example special_initial_object_obj@{o h so q +| h <= so, o <= q, h <= q +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (w : SubObj (cogen_prod comp G))
  (Hw : IsIntersection@{o h q} (fun m : SubObj (cogen_prod comp G) => m) w) :
  @initial_obj C (special_initial_object comp G w Hw) = Subobject.sub_dom w :=
  eq_refl.

Example special_initial_object_zero@{o h so q +| h <= so, o <= q, h <= q +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (w : SubObj (cogen_prod comp G))
  (Hw : IsIntersection@{o h q} (fun m : SubObj (cogen_prod comp G) => m) w)
  (c : C) :
  @zero C (special_initial_object comp G w Hw) c
    = cogen_pullback_to comp G c
        ∘ `1 (inter_le _ _ Hw (cogen_pullback_sub comp G c)) :=
  eq_refl.

(* 相关说明。 （已译） *)
Definition special_initial_IsInitialObj@{o h so q +|
    h <= so, o <= q, h <= q +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (w : SubObj (cogen_prod comp G))
  (Hw : IsIntersection@{o h q} (fun m : SubObj (cogen_prod comp G) => m) w) :
  IsInitialObj (Subobject.sub_dom w) :=
  IsInitialObj_from_Initial (special_initial_object comp G w Hw).

(* * ** Mac Lane's 假设: every class subobjects has intersection （已译） *)

Definition HasClassIntersections@{o h p q s t k |
    o <= s, h <= s, h < t, o <= q, h <= q, p <= q,
    p < k, o <= k, h <= k, q <= k +}
  (C : Category@{o h h}) : Type@{k} :=
  ∀ (x : C) (P : SubObj@{o h} x → Type@{p}),
    (∀ m m' : SubObj x, m ≈ m' → P m → P m') →
    { w : SubObj x &
      IsIntersection@{o h q} (fun k : { m : SubObj x & P m } => `1 k) w }.

(* 相关说明。 （已译） *)
Definition special_initial_object_book@{o h so p q s t k d +|
    h <= so, h < d +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (HI : HasClassIntersections@{o h p q s t k} C) :
  @Initial C.
Proof.
  refine (special_initial_object_least comp G
            (`1 (HI (cogen_prod@{so d so o h} comp G) (fun _ => unit)
                   (fun _ _ _ t => t)))
            _).
  intro v.
  exact (inter_le _ _
           (`2 (HI (cogen_prod@{so d so o h} comp G) (fun _ => unit)
                  (fun _ _ _ t => t)))
           (existT _ v tt)).
Defined.

Example special_initial_object_book_obj@{o h so p q s t k d +|
    h <= so, h < d +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (HI : HasClassIntersections@{o h p q s t k} C) :
  @initial_obj C (special_initial_object_book comp G HI)
    = Subobject.sub_dom
        (`1 (HI (cogen_prod@{so d so o h} comp G) (fun _ => unit)
               (fun _ _ _ t => t))) :=
  eq_refl.

(* * ** Well-powered 范畴: 假设 discharged （已译） *)

Definition wellpowered_class_intersections@{o h w s t so p q k +|
    w <= h, h < t, o <= s, h <= s, w <= so, p <= so,
    o <= q, h <= q, p <= q +}
  {C : Category@{o h h}} (WP : WellPowered@{o h w s t} C)
  (comp : @Complete@{so so h o} C) : HasClassIntersections@{o h p q s t k} C :=
  fun x P HP => wellpowered_complete_has_intersections WP comp x P HP.

(* Mac Lane's remark under §V.8 Definition 1. *)
Definition special_initial_object_wellpowered@{o h w s t so d +|
    w <= h, h < t, h < d, o <= s, h <= s, h <= so, w <= so +}
  {C : Category@{o h h}}
  (WP : WellPowered@{o h w s t} C) (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) : @Initial C :=
  special_initial_object comp G _
    (`2 (wellpowered_complete_intersection_all WP comp
          (cogen_prod@{so d so o h} comp G))).

Example special_initial_object_wellpowered_obj@{o h w s t so d +|
    w <= h, h < t, h < d, o <= s, h <= s, h <= so, w <= so +}
  {C : Category@{o h h}}
  (WP : WellPowered@{o h w s t} C) (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) :
  @initial_obj C (special_initial_object_wellpowered WP comp G)
    = Subobject.sub_dom
        (complete_intersection comp
           (wp_class_family (WP (cogen_prod@{so d so o h} comp G))
              (fun _ => True))) :=
  eq_refl.

(* Well-poweredness at the ONE object [cogen_prod comp G] suffices. *)
Definition special_initial_object_wellpowered_at@{o h w s t so d +|
    h < t, h < d, o <= s, h <= s, h <= so, w <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C)
  (W : WellPoweredAt@{w o s h t} (cogen_prod@{so d so o h} comp G)) :
  @Initial C.
Proof.
  refine (special_initial_object_least comp G
            (`1 (wp_complete_class_intersection comp W (fun _ => True)
                   (fun _ _ _ t => t))) _).
  intro v.
  exact (inter_le _ _
           (`2 (wp_complete_class_intersection comp W (fun _ => True)
                  (fun _ _ _ t => t)))
           (existT _ v I)).
Defined.

Example special_initial_object_wellpowered_at_obj@{o h w s t so d +|
    h < t, h < d, o <= s, h <= s, h <= so, w <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C)
  (W : WellPoweredAt@{w o s h t} (cogen_prod@{so d so o h} comp G)) :
  @initial_obj C (special_initial_object_wellpowered_at comp G W)
    = Subobject.sub_dom
        (complete_intersection comp (wp_class_family W (fun _ => True))) :=
  eq_refl.

(* * ** Small 对象: completeness alone intersects all subobjects （已译） *)

Definition special_initial_object_small@{o h so +| h <= so, o <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) : @Initial C :=
  special_initial_object comp G _
    (complete_intersection_IsIntersection comp
       (fun m : SubObj (cogen_prod comp G) => m)).

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition special_weakly_initial@{o h so +| h <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (w : SubObj (cogen_prod comp G))
  (Hw : ∀ v : SubObj (cogen_prod comp G), sub_le w v) :
  WeaklyInitial (Subobject.sub_dom w) :=
  special_initial_zero comp G w Hw.

(* Freyd's construction on that singleton family, at [so = h]. *)
Definition special_vs_freyd@{o h +} {C : Category@{o h h}}
  (comp : @Complete@{h h h o} C) (G : Cogenerator@{h o h} C)
  (w : SubObj (cogen_prod comp G))
  (Hw : ∀ v : SubObj (cogen_prod comp G), sub_le w v) :
  @initial_obj C (special_initial_object_least comp G w Hw)
  ≅ @initial_obj C
      (initial_from_weakly_initial_complete comp (Complete_HasEqualizers comp)
         (wif_of_weakly_initial (special_weakly_initial comp G w Hw))) :=
  initial_unique _ _.

(* The subobjects cogenerator product, indexed well-powered
 datum at one 对象, weakly initial family. （已译） *)
Definition wif_of_cogenerator@{o h w s t so d +|
    h < t, h < d, o <= s, h <= s, h <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C)
  (W : WellPoweredAt@{w o s h t} (cogen_prod@{so d so o h} comp G)) :
  WeaklyInitialFamily@{w o h} C.
Proof.
  refine (Build_WeaklyInitialFamily C (wp_index W)
            (fun i => Subobject.sub_dom (wp_to W i)) _).
  intro c.
  exists (wp_from W (cogen_pullback_sub comp G c)).
  exact (cogen_pullback_to comp G c
           ∘ `1 (sub_le_of_equiv _ _
                   (wp_to_from W (cogen_pullback_sub comp G c)))).
Defined.

Definition freyd_of_cogenerator@{o h s t d +|
    h < t, h < d, o <= s, h <= s +}
  {C : Category@{o h h}} (comp : @Complete@{h h h o} C)
  (G : Cogenerator@{h o h} C)
  (W : WellPoweredAt@{h o s h t} (cogen_prod@{h d h o h} comp G)) :
  @Initial C :=
  initial_from_weakly_initial_complete comp (Complete_HasEqualizers comp)
    (wif_of_cogenerator comp G W).

Definition special_vs_freyd_of_cogenerator@{o h s t d +|
    h < t, h < d, o <= s, h <= s +}
  {C : Category@{o h h}} (comp : @Complete@{h h h o} C)
  (G : Cogenerator@{h o h} C)
  (W : WellPoweredAt@{h o s h t} (cogen_prod@{h d h o h} comp G)) :
  @initial_obj C (special_initial_object_wellpowered_at comp G W)
  ≅ @initial_obj C (freyd_of_cogenerator comp G W) :=
  initial_unique _ _.
