Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Structure.Pullback.Wide.Complete.
Require Import Category.Structure.Complete.
Require Import Category.Structure.WellPowered.
Require Import Category.Instance.Sets.
Require Import Category.Adjunction.SAFT.
Require Import Category.Adjunction.SAFT.InitialObject.
Require Import Category.Adjunction.SpanningArrow.

Generalizable All Variables.

(* * * The special adjoint 函子 定理, characterization （已译） *)

(*
   nLab:      https://ncatlab.org/nlab/show/well-powered+category
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functor_theorem

   本文件给出特殊伴随函子定理相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The monos lemma *)

(* The easy half: arrow comma whose C-component monic is
 monic. No 假设. （已译） *)
Lemma comma_monic_of_underlying@{o hc dobj h +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  {X Y : =(d) ↓ U} (m : X ~{=(d) ↓ U}~> Y) :
  Monic (snd (`1 m)) → Monic m.
Proof.
  intros Hm; constructor; intros Z g1 g2 H.
  split.
  - destruct (fst (`1 g1)), (fst (`1 g2)); exact eq_refl.
  - apply (monic (Monic := Hm)).
    exact (snd H).
Qed.

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition kp_diag@{o hc dobj h +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  {X Y : =(d) ↓ U} (m : X ~{=(d) ↓ U}~> Y)
  (K : Pullback (snd (`1 m)) (snd (`1 m))) :
  snd (`1 X) ~{C}~> Pull _ _ K :=
  unique_obj (ump_pullbacks _ _ K (snd (`1 X)) id id (reflexivity _)).

Lemma kp_diag_fst@{o hc dobj h +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  {X Y : =(d) ↓ U} (m : X ~{=(d) ↓ U}~> Y)
  (K : Pullback (snd (`1 m)) (snd (`1 m))) :
  pullback_fst _ _ K ∘ kp_diag m K ≈ id.
Proof.
  exact (fst (unique_property (ump_pullbacks _ _ K _ id id (reflexivity _)))).
Qed.

Lemma kp_diag_snd@{o hc dobj h +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  {X Y : =(d) ↓ U} (m : X ~{=(d) ↓ U}~> Y)
  (K : Pullback (snd (`1 m)) (snd (`1 m))) :
  pullback_snd _ _ K ∘ kp_diag m K ≈ id.
Proof.
  exact (snd (unique_property (ump_pullbacks _ _ K _ id id (reflexivity _)))).
Qed.

Definition kp_obj@{o hc dobj h +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  {X Y : =(d) ↓ U} (m : X ~{=(d) ↓ U}~> Y)
  (K : Pullback (snd (`1 m)) (snd (`1 m))) : =(d) ↓ U :=
  ((ttt, Pull _ _ K); fmap[U] (kp_diag m K) ∘ `2 X).

Definition kp_fst@{o hc dobj h +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  {X Y : =(d) ↓ U} (m : X ~{=(d) ↓ U}~> Y)
  (K : Pullback (snd (`1 m)) (snd (`1 m))) :
  kp_obj m K ~{=(d) ↓ U}~> X.
Proof.
  unshelve refine ((ttt, pullback_fst _ _ K); _).
  change (`2 X ∘ id[d]
            ≈ fmap[U] (pullback_fst _ _ K) ∘ (fmap[U] (kp_diag m K) ∘ `2 X)).
  rewrite id_right, comp_assoc, <- fmap_comp, kp_diag_fst, fmap_id, id_left.
  reflexivity.
Defined.

Definition kp_snd@{o hc dobj h +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  {X Y : =(d) ↓ U} (m : X ~{=(d) ↓ U}~> Y)
  (K : Pullback (snd (`1 m)) (snd (`1 m))) :
  kp_obj m K ~{=(d) ↓ U}~> X.
Proof.
  unshelve refine ((ttt, pullback_snd _ _ K); _).
  change (`2 X ∘ id[d]
            ≈ fmap[U] (pullback_snd _ _ K) ∘ (fmap[U] (kp_diag m K) ∘ `2 X)).
  rewrite id_right, comp_assoc, <- fmap_comp, kp_diag_snd, fmap_id, id_left.
  reflexivity.
Defined.

Lemma underlying_monic_of_comma_monic@{o hc dobj h +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  {X Y : =(d) ↓ U} (m : X ~{=(d) ↓ U}~> Y)
  (K : Pullback (snd (`1 m)) (snd (`1 m))) :
  Monic m → Monic (snd (`1 m)).
Proof.
  intros Hm; constructor; intros z g1 g2 H.
  assert (Hp : kp_fst m K ≈ kp_snd m K).
  { apply (monic (Monic := Hm)).
    split.
    - destruct (fst (`1 m)); exact eq_refl.
    - exact (pullback_commutes _ _ K). }
  destruct (ump_pullbacks _ _ K z g1 g2 H) as [u [Hu1 Hu2] _].
  rewrite <- Hu1, <- Hu2.
  simpl in Hp.
  now rewrite (snd Hp).
Qed.

Definition comma_monic_iff_underlying_monic@{o hc dobj h +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  (HP : HasPullbacks C) {X Y : =(d) ↓ U} (m : X ~{=(d) ↓ U}~> Y) :
  Monic m ↔ Monic (snd (`1 m)) :=
  (underlying_monic_of_comma_monic m (pullback _ _),
   comma_monic_of_underlying m).

(* * ** The cogenerating family comma 范畴 （已译） *)

(* Mac Lane's Q': 对象 [(cog_obj G j, k)], one each arrow
 [k : d ~> U (cog_obj G j)]. The index universe [cc] free above the
 old index homs. （已译） *)
Definition comma_cogenerator@{o hc dobj h c cc +| hc <= h, c <= cc, h <= cc +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} (U : C ⟶ D) (d : D)
  (G : Cogenerator@{c o hc} C) : Cogenerator@{cc _ h} (=(d) ↓ U).
Proof.
  refine (@Build_Cogenerator (=(d) ↓ U)
            { j : cog_index G & d ~> U (cog_obj G j) }
            (fun p => ((ttt, cog_obj G (projT1 p)); projT2 p)) _).
  intros x y f g H.
  split.
  - destruct (fst `1 f), (fst `1 g); exact eq_refl.
  - apply (cog_separates G (snd `1 f) (snd `1 g)); intros j k.
    unshelve refine (snd (H (j; fmap[U] k ∘ `2 y) ((ttt, k); _))).
    simpl; cat.
Defined.

(* * ** Well-poweredness comma 范畴 （已译） *)

(*
   本节说明子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition underlying_sub@{o hc dobj h +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  (HP : HasPullbacks C) {X : =(d) ↓ U} (v : SubObj X) :
  SubObj (snd (`1 X)) :=
  @Build_SubObj C (snd (`1 X)) (snd (`1 (Subobject.sub_dom v)))
    (snd (`1 (Subobject.sub_mono v)))
    (underlying_monic_of_comma_monic (Subobject.sub_mono v) (pullback _ _)
       (Subobject.sub_is_monic v)).

(*
   本节说明 Characterization 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section CommaWellPowered.

Universes o hc dobj h w s t.
Constraint hc <= h.

Context {C : Category@{o hc hc}} {D : Category@{dobj h h}} (U : C ⟶ D) (d : D).
Context (HP : HasPullbacks C) (X : =(d) ↓ U).
Context (W : WellPoweredAt@{w o s hc t} (snd (`1 X))).

(* A subobject [X] comma: C-subobject underlying
 对象, named [W], factorization [X]'s structure arrow
 through [U] mono. （已译） *)
Definition comma_wp_index : Type :=
  { i : wp_index W &
    { s : d ~> U (Subobject.sub_dom (wp_to W i)) &
      fmap[U] (Subobject.sub_mono (wp_to W i)) ∘ s ≈ `2 X } }.

Definition comma_wp_dom (k : comma_wp_index) : =(d) ↓ U :=
  ((ttt, Subobject.sub_dom (wp_to W (`1 k))); `1 (`2 k)).

Definition comma_wp_mono (k : comma_wp_index) : comma_wp_dom k ~{=(d) ↓ U}~> X.
Proof.
  unshelve refine ((ttt, Subobject.sub_mono (wp_to W (`1 k))); _).
  change (`2 X ∘ id[d] ≈ fmap[U] (Subobject.sub_mono (wp_to W (`1 k)))
                            ∘ `1 (`2 k)).
  rewrite id_right; symmetry; exact (`2 (`2 k)).
Defined.

Definition comma_wp_to (k : comma_wp_index) : SubObj X :=
  @Build_SubObj (=(d) ↓ U) X (comma_wp_dom k) (comma_wp_mono k)
    (comma_monic_of_underlying (comma_wp_mono k)
       (Subobject.sub_is_monic (wp_to W (`1 k)))).

Definition comma_wp_from (v : SubObj X) : comma_wp_index.
Proof using HP.
  pose (e := wp_to_from W (underlying_sub HP v)).
  exists (wp_from W (underlying_sub HP v)).
  exists (fmap[U] (from (`1 e)) ∘ `2 (Subobject.sub_dom v)).
  rewrite comp_assoc, <- fmap_comp.
  assert (Hm : Subobject.sub_mono (wp_to W (wp_from W (underlying_sub HP v)))
                 ∘ from (`1 e) ≈ snd (`1 (Subobject.sub_mono v))).
  { rewrite <- (`2 e). simpl. rewrite <- comp_assoc, iso_to_from. cat. }
  rewrite Hm.
  symmetry.
  exact (comma_square (Subobject.sub_mono v)).
Defined.

Definition comma_wp_iso_to (v : SubObj X) :
  comma_wp_dom (comma_wp_from v) ~{=(d) ↓ U}~> Subobject.sub_dom v.
Proof using HP.
  unshelve refine ((ttt, to (`1 (wp_to_from W (underlying_sub HP v)))); _).
  simpl.
  rewrite id_right, comp_assoc, <- fmap_comp, iso_to_from, fmap_id.
  now rewrite id_left.
Defined.

Definition comma_wp_iso_from (v : SubObj X) :
  Subobject.sub_dom v ~{=(d) ↓ U}~> comma_wp_dom (comma_wp_from v).
Proof using HP.
  unshelve refine ((ttt, from (`1 (wp_to_from W (underlying_sub HP v)))); _).
  simpl. now rewrite id_right.
Defined.

Definition comma_wp_to_from@{sc tc +| h <= sc, h < tc +} (v : SubObj X) :
  @equiv _ (@SubObj_Setoid@{_ h h sc tc} (=(d) ↓ U) X)
    (comma_wp_to (comma_wp_from v)) v.
Proof using HP.
  unshelve eexists.
  - unshelve refine (@Build_Isomorphism (=(d) ↓ U) _ _
                       (comma_wp_iso_to v) (comma_wp_iso_from v) _ _).
    + split; [reflexivity|]. simpl.
      exact (iso_to_from (`1 (wp_to_from W (underlying_sub HP v)))).
    + split; [reflexivity|]. simpl.
      exact (iso_from_to (`1 (wp_to_from W (underlying_sub HP v)))).
  - split; [reflexivity|]. simpl.
    exact (`2 (wp_to_from W (underlying_sub HP v))).
Defined.

Definition comma_WellPoweredAt@{wc sc tc +| w <= wc, h <= wc, h <= sc, h < tc +} :
  @WellPoweredAt@{wc _ sc h tc} (=(d) ↓ U) X :=
  {| wp_index := comma_wp_index;
     wp_to := comma_wp_to;
     wp_from := comma_wp_from;
     wp_to_from := comma_wp_to_from |}.

End CommaWellPowered.

(* At every 对象. The comma [Let] section, so its
 universes fixed before result type names [sc] [tc]
 (collapse (d) header). （已译） *)
Section CommaWellPoweredAll.

Universes o hc dobj h w s t sc tc.
Constraint hc <= h, h <= sc, h < tc.

Context {C : Category@{o hc hc}} {D : Category@{dobj h h}} (U : C ⟶ D) (d : D).
Context (HP : HasPullbacks C) (WP : WellPowered@{o hc w s t} C).

Let K : Category := =(d) ↓ U.

Definition comma_WellPowered : @WellPowered@{_ h h sc tc} K :=
  fun X => comma_WellPoweredAt U d HP X (WP (snd (`1 X))).

End CommaWellPoweredAll.

(* 相关说明。 （已译） *)

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition SAFT_comma_initial@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) (d : D) :
  @Initial (=(d) ↓ U) :=
  special_initial_object_wellpowered_at (Comma_Complete cont comp)
    (comma_cogenerator U d G)
    (comma_WellPoweredAt U d (complete_pullbacks comp) _ (WP _)).

Definition SAFT_universal_arrow@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) (d : D) :
  UniversalArrow d U :=
  {| arrow_initial := SAFT_comma_initial U comp cont G WP d |}.

(* The left adjoint, transparent: Theory/Universal/Arrow.v's assembly,
   not Adjunction/GAFT.v's [Qed] [GAFT_from_initials]. *)
Definition SAFT_left@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) : D ⟶ C :=
  @LeftAdjointFunctorFromUniversalArrows D C U
    (SAFT_universal_arrow U comp cont G WP).

Definition SAFT_adjunction@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  SAFT_left U comp cont G WP ⊣ U :=
  @AdjunctionFromUniversalArrows D C U (SAFT_universal_arrow U comp cont G WP).

(* 相关说明。 （已译） *)
Definition SAFT_wellpowered@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  { F : D ⟶ C & F ⊣ U } :=
  existT _ (SAFT_left U comp cont G WP) (SAFT_adjunction U comp cont G WP).

(* READBACK, [eq_refl]: 左伴随 at [d] C-对象 under the
 intersection all subobjects comma's cogenerator product. （已译） *)
Example SAFT_left_obj@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) (d : D) :
  fobj[`1 (SAFT_wellpowered U comp cont G WP)] d
    = snd (`1 (Subobject.sub_dom
        (complete_intersection (Comma_Complete cont comp)
           (wp_class_family
              (comma_WellPoweredAt U d (complete_pullbacks comp)
                 (cogen_prod (Comma_Complete cont comp)
                    (comma_cogenerator U d G))
                 (WP _))
              (fun _ => True))))) :=
  eq_refl.

(* Mac Lane's Corollary, Awodey's Remark 9.35: over a complete,
   well-powered C with a small cogenerating family, [U] has a left
   adjoint iff it is continuous. *)
Definition SAFT_wellpowered_iff@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  { F : D ⟶ C & F ⊣ U }
    ↔ @PreservesImageLimit@{o h dobj h pk so pa so} C D U :=
  (fun H => right_adjoint_PreservesImageLimit (`2 H),
   fun cont => SAFT_wellpowered U comp cont G WP).

(* 相关说明。 （已译） *)

(* Mac Lane's "every set subobjects 对象 has pullback": a
 LIMIT, over index at universe [q] (the class reading). （已译） *)
Definition HasSubobjectWidePullbacks@{o h q r k +}
  (C : Category@{o h h}) : Type@{k} :=
  ∀ (x : C) (I : Type@{q}) (S : I → SubObj x),
    WidePullback@{q r o h} (fun i => Subobject.sub_mono (S i)).

(* Completeness supplies it at every index universe [q] at below its
 shape universe [so], whatever 对象' universe: Structure/
 Pullback/Wide/Complete.v's [complete_wide_pullback] at each family.
 Theorem 2 asks it at [q] at above 对象 (the header's
 paragraph IN TREE, THEOREM 2 IS APPLIED ONLY AT A THIN CATEGORY).（已译） *)
Definition Complete_HasSubobjectWidePullbacks@{o h so q r k +|
    h <= so, q <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C) :
  HasSubobjectWidePullbacks@{o h q r k} C :=
  fun x I S => complete_wide_pullback comp (fun i => Subobject.sub_mono (S i)).

(*
   本节说明拉回/推出、子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition least_index@{o hc dobj h lq +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} (U : C ⟶ D) (d : D)
  (X : =(d) ↓ U) : Type@{lq} :=
  { m : SubObj (snd (`1 X)) & SubFactorsThrough U (`2 X) m }.

Definition least_top@{o hc dobj h lq +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} (U : C ⟶ D) (d : D)
  (X : =(d) ↓ U) : least_index U d X :=
  (sub_top; factors_through_top U (`2 X)).

(* The D-arrow [U] intersection: mediator the
 factorizations, [HU]'s wide pullback supplies. Only this
 existence half 普遍性质 used. （已译） *)
Definition least_lift@{o hc dobj h lq r rd +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  {X : =(d) ↓ U}
  {W : WidePullback@{lq r o hc}
         (fun k : least_index U d X => Subobject.sub_mono (`1 k))}
  (HUW : IsWidePullback@{lq rd dobj h}
           (fun k : least_index U d X => fmap[U] (Subobject.sub_mono (`1 k)))
           (U (WPull W))
           (fun k => fmap[U] (wide_pullback_proj W k))) :
  d ~> U (WPull W).
Proof.
  refine (unique_obj (wpull_ump HUW (fun k => `1 (`2 k)) _)).
  intros i j. rewrite (`2 (`2 i)), (`2 (`2 j)). reflexivity.
Defined.

Lemma least_lift_commutes@{o hc dobj h lq r rd +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  {X : =(d) ↓ U}
  {W : WidePullback@{lq r o hc}
         (fun k : least_index U d X => Subobject.sub_mono (`1 k))}
  (HUW : IsWidePullback@{lq rd dobj h}
           (fun k : least_index U d X => fmap[U] (Subobject.sub_mono (`1 k)))
           (U (WPull W))
           (fun k => fmap[U] (wide_pullback_proj W k)))
  (k : least_index U d X) :
  fmap[U] (wide_pullback_proj W k) ∘ least_lift HUW ≈ `1 (`2 k).
Proof. exact (unique_property (wpull_ump HUW _ _) k). Qed.

Definition least_dom@{o hc dobj h lq r rd +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  {X : =(d) ↓ U}
  {W : WidePullback@{lq r o hc}
         (fun k : least_index U d X => Subobject.sub_mono (`1 k))}
  (HUW : IsWidePullback@{lq rd dobj h}
           (fun k : least_index U d X => fmap[U] (Subobject.sub_mono (`1 k)))
           (U (WPull W))
           (fun k => fmap[U] (wide_pullback_proj W k))) : =(d) ↓ U :=
  ((ttt, WPull W); least_lift HUW).

Definition least_mono@{o hc dobj h lq r rd +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  {X : =(d) ↓ U}
  {W : WidePullback@{lq r o hc}
         (fun k : least_index U d X => Subobject.sub_mono (`1 k))}
  (HUW : IsWidePullback@{lq rd dobj h}
           (fun k : least_index U d X => fmap[U] (Subobject.sub_mono (`1 k)))
           (U (WPull W))
           (fun k => fmap[U] (wide_pullback_proj W k))) :
  least_dom HUW ~{=(d) ↓ U}~> X.
Proof.
  unshelve refine ((ttt, Subobject.sub_mono
                           (sub_wide_intersection (fun k => `1 k)
                              (least_top U d X) W)); _).
  simpl. rewrite id_right, id_left.
  symmetry. exact (least_lift_commutes HUW (least_top U d X)).
Defined.

Definition least_sub@{o hc dobj h lq r rd +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  {X : =(d) ↓ U}
  {W : WidePullback@{lq r o hc}
         (fun k : least_index U d X => Subobject.sub_mono (`1 k))}
  (HUW : IsWidePullback@{lq rd dobj h}
           (fun k : least_index U d X => fmap[U] (Subobject.sub_mono (`1 k)))
           (U (WPull W))
           (fun k => fmap[U] (wide_pullback_proj W k))) : SubObj X :=
  @Build_SubObj (=(d) ↓ U) X (least_dom HUW) (least_mono HUW)
    (comma_monic_of_underlying (least_mono HUW)
       (Subobject.sub_is_monic
          (sub_wide_intersection (fun k => `1 k) (least_top U d X) W))).

(* A comma subobject [v] read as a member of the corresponding family. *)
Definition least_index_of@{o hc dobj h lq +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  (HP : HasPullbacks C) {X : =(d) ↓ U} (v : SubObj X) : least_index U d X.
Proof.
  exists (underlying_sub HP v).
  exists (`2 (Subobject.sub_dom v)).
  symmetry. exact (comma_square (Subobject.sub_mono v)).
Defined.

Definition least_le@{o hc dobj h lq r rd +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  (HP : HasPullbacks C) {X : =(d) ↓ U}
  {W : WidePullback@{lq r o hc}
         (fun k : least_index U d X => Subobject.sub_mono (`1 k))}
  (HUW : IsWidePullback@{lq rd dobj h}
           (fun k : least_index U d X => fmap[U] (Subobject.sub_mono (`1 k)))
           (U (WPull W))
           (fun k => fmap[U] (wide_pullback_proj W k)))
  (v : SubObj X) : sub_le (least_sub HUW) v.
Proof.
  unshelve eexists.
  - unshelve refine ((ttt, wide_pullback_proj W (least_index_of HP v)); _).
    simpl. rewrite id_right. symmetry.
    exact (least_lift_commutes HUW (least_index_of HP v)).
  - split; [reflexivity|]. simpl.
    rewrite id_left.
    exact (transitivity
             (wide_pullback_commutes W (least_index_of HP v) (least_top U d X))
             (id_left _)).
Defined.


(** ** Theorem 2, sufficiency *)

(* #452's 定理 over least subobject, comma, at least
 subobject built above; assembled transparently Corollary is. （已译） *)
Definition SAFT_thm2_initial@{o dobj h so c pk pa q r rd pw k +|
    h <= so, c <= so, o <= q, h <= q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) (d : D) :
  @Initial (=(d) ↓ U) :=
  special_initial_object_least (Comma_Complete cont comp)
    (comma_cogenerator U d G)
    (@least_sub C D U d
       (cogen_prod (Comma_Complete cont comp) (comma_cogenerator U d G))
       (HW _ _ (fun k => `1 k))
       (HU _ _ _ _ (fun k => Subobject.sub_is_monic (`1 k)) _ _
          (wide_pullback_is_pullback (HW _ _ (fun k => `1 k)))))
    (least_le (complete_pullbacks comp)
       (HU _ _ _ _ (fun k => Subobject.sub_is_monic (`1 k)) _ _
          (wide_pullback_is_pullback (HW _ _ (fun k => `1 k))))).

Definition SAFT_thm2_universal_arrow@{o dobj h so c pk pa q r rd pw k +|
    h <= so, c <= so, o <= q, h <= q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) (d : D) :
  UniversalArrow d U :=
  {| arrow_initial := SAFT_thm2_initial U comp cont G HW HU d |}.

Definition SAFT_thm2_left@{o dobj h so c pk pa q r rd pw k +|
    h <= so, c <= so, o <= q, h <= q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) : D ⟶ C :=
  @LeftAdjointFunctorFromUniversalArrows D C U
    (SAFT_thm2_universal_arrow U comp cont G HW HU).

Definition SAFT_thm2_adjunction@{o dobj h so c pk pa q r rd pw k +|
    h <= so, c <= so, o <= q, h <= q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) :
  SAFT_thm2_left U comp cont G HW HU ⊣ U :=
  @AdjunctionFromUniversalArrows D C U
    (SAFT_thm2_universal_arrow U comp cont G HW HU).

Definition SAFT_thm2@{o dobj h so c pk pa q r rd pw k +|
    h <= so, c <= so, o <= q, h <= q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) :
  { F : D ⟶ C & F ⊣ U } :=
  existT _ (SAFT_thm2_left U comp cont G HW HU)
    (SAFT_thm2_adjunction U comp cont G HW HU).

(* READBACK, [eq_refl]: 左伴随 at [d] C-wide pullback of
 corresponding family comma's cogenerator product. （已译） *)
Example SAFT_thm2_left_obj@{o dobj h so c pk pa q r rd pw k +|
    h <= so, c <= so, o <= q, h <= q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) (d : D) :
  fobj[`1 (SAFT_thm2 U comp cont G HW HU)] d
    = WPull (HW (snd (`1 (cogen_prod (Comma_Complete cont comp)
                              (comma_cogenerator U d G))))
                (least_index U d
                   (cogen_prod (Comma_Complete cont comp)
                      (comma_cogenerator U d G)))
                (fun k => `1 k)) :=
  eq_refl.

(* 相关说明。 （已译） *)

(* Every wide 拉回, monos not, at every index universe: the
 monicity clause [Hm] is accepted ignored. Elementary, by
 transposition along [adj], since wide 拉回 has no shape
 范畴 [rapl_ump].（已译） *)
Definition right_adjoint_PreservesWidePullbacks@{o dobj h pw q r rd +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} {F : D ⟶ C} {U : C ⟶ D}
  (A : F ⊣ U) : PreservesWidePullbacks@{o h dobj h pw q r rd} U.
Proof.
  intros I B z g _ P p HP.
  constructor.
  - intros i j. rewrite <- !fmap_comp. now rewrite (wpull_commutes HP i j).
  - intros Q q Hq.
    pose (qb := fun i => from (@adj _ _ _ _ A Q (B i)) (q i)).
    assert (Hq' : ∀ i j, g i ∘ qb i ≈ g j ∘ qb j).
    { intros i j; unfold qb.
      rewrite <- (@from_adj_nat_r C D F U A _ _ _ (g i) (q i)).
      rewrite <- (@from_adj_nat_r C D F U A _ _ _ (g j) (q j)).
      apply from_adj_respects. exact (Hq i j). }
    destruct (wpull_ump HP qb Hq') as [u Hu Huu].
    unshelve refine {| unique_obj := to (@adj _ _ _ _ A Q P) u |}.
    + intro i.
      rewrite <- (@to_adj_nat_r C D F U A _ _ _ (p i) u).
      etransitivity; [apply to_adj_respects; exact (Hu i)|].
      apply from_adj_comp_law.
    + intros v Hv.
      etransitivity; [|apply (from_adj_comp_law v)].
      apply to_adj_respects.
      apply Huu; intro i; unfold qb.
      rewrite <- (@from_adj_nat_r C D F U A _ _ _ (p i) v).
      apply from_adj_respects. exact (Hv i).
Defined.

(** ** Theorem 2, the biconditional *)

(* Mac Lane §V.8 Theorem 2: over 完备 C small cogenerating
 family which every family subobjects has wide 拉回, [U] has
 左伴随 iff it preserves small limits wide pullbacks of
 monos.（已译） *)
Definition SAFT_iff@{o dobj h so c pk pa q r rd pw k +|
    h <= so, c <= so, o <= q, h <= q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C) (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C) :
  { F : D ⟶ C & F ⊣ U }
    ↔ (@PreservesImageLimit@{o h dobj h pk so pa so} C D U
       * PreservesWidePullbacks@{o h dobj h pw q r rd} U) :=
  (fun H => (right_adjoint_PreservesImageLimit (`2 H),
             right_adjoint_PreservesWidePullbacks (`2 H)),
   fun H => SAFT_thm2 U comp (fst H) G HW (snd H)).
