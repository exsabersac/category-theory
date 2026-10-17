Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Span.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Complete.
Require Import Category.Structure.WellPowered.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Roof.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.SAFT.
Require Import Category.Adjunction.SAFT.InitialObject.

Generalizable All Variables.

(** * The covering step of the special adjoint functor theorem, derived *)

(*
   nLab:      https://ncatlab.org/nlab/show/well-powered+category

   本文件给出特殊伴随函子定理相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The product over arrows out of [d] *)

(* A cone over [U ◯ DiscreteCat_Functor f] from a plain family of legs. *)
Definition image_family_cone@{o dobj h a pc dq +| h < pc, h < dq +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  {A : Type@{a}} (f : A -> C) (x : D) (pi : ∀ i, x ~> U (f i)) :
  Cone (@Compose@{dobj a o pc h} _ _ _ U (DiscreteCat_Functor@{a h h o h h dq} f)).
Proof.
  unshelve econstructor.
  - exact x.
  - unshelve econstructor.
    + exact pi.
    + intros i j e; destruct e; simpl.
      rewrite fmap_id; apply id_left.
Defined.

(* One factor [cog_obj G j] per arrow [d ~> U (cog_obj G j)]. *)
Definition saft_index@{o dobj h so +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (G : Cogenerator@{so o h} C) (d : D) : Type@{so} :=
  { j : cog_index G & d ~> U (cog_obj G j) }.

Definition saft_fam@{o dobj h so +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (G : Cogenerator@{so o h} C) (d : D) : saft_index U G d -> C :=
  fun p => cog_obj G (projT1 p).

Definition saft_prod_limit@{o dobj h so dp +| h <= so, h < dp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C) (G : Cogenerator@{so o h} C) (d : D) :=
  comp _ (DiscreteCat_Functor@{so h h o h h dp} (saft_fam U G d)).

Definition saft_prod@{o dobj h so dp +| h <= so, h < dp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C) (G : Cogenerator@{so o h} C) (d : D) : C :=
  iprod (saft_fam U G d) (saft_prod_limit@{o dobj h so dp} U comp G d).

(* The canonical point [d ~> U (saft_prod …)], from preservation. *)
Definition saft_point@{o dobj h so dp pl pa +| h <= so, h < dp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D) :
  d ~> U (saft_prod@{o dobj h so dp} U comp G d) :=
  unique_obj (cont _ _ (saft_prod_limit@{o dobj h so dp} U comp G d)
                (image_family_cone@{o dobj h so pa dp} U (saft_fam U G d) d
                   (fun p => projT2 p))).

Lemma saft_point_commutes@{o dobj h so dp pl pa +| h <= so, h < dp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D) (p : saft_index U G d) :
  fmap[U] (iprod_proj (saft_fam U G d)
             (saft_prod_limit@{o dobj h so dp} U comp G d) p)
    ∘ saft_point@{o dobj h so dp pl pa} U comp cont G d ≈ projT2 p.
Proof.
  exact (unique_property
           (cont _ _ (saft_prod_limit@{o dobj h so dp} U comp G d)
              (image_family_cone@{o dobj h so pa dp} U (saft_fam U G d) d
                 (fun p => projT2 p))) p).
Qed.

(** ** Mac Lane's k, now depending on [h] *)

(* Component [(j, k)] is the projection at [(j, U k ∘ h)]. *)
Definition saft_kappa@{o dobj h so dp cp +| h <= so, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C) (G : Cogenerator@{so o h} C)
  (d : D) (c : C) (h : d ~> U c) :
  saft_prod@{o dobj h so dp} U comp G d ~> cogen_power@{cp so o h so} comp G c :=
  unique_obj (iprod_ump (cogen_power_fam G c)
                (cogen_power_limit@{o h cp so so} comp G c)
                (saft_prod@{o dobj h so dp} U comp G d)
                (fun p => iprod_proj (saft_fam U G d)
                            (saft_prod_limit@{o dobj h so dp} U comp G d)
                            (existT _ (projT1 p) (fmap[U] (projT2 p) ∘ h)))).

Lemma saft_square@{o dobj h so dp cp pl pa +| h <= so, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D) (c : C) (h : d ~> U c) :
  fmap[U] (saft_kappa@{o dobj h so dp cp} U comp G d c h)
    ∘ saft_point@{o dobj h so dp pl pa} U comp cont G d
    ≈ fmap[U] (cogen_canonical@{cp so h so o} comp G c) ∘ h.
Proof.
  pose (N := image_family_cone@{o dobj h so pa cp} U (cogen_power_fam G c) d
               (fun p => fmap[U] (projT2 p) ∘ h)).
  pose proof (uniqueness
                (cont _ _ (cogen_power_limit@{o h cp so so} comp G c) N)) as Hu.
  transitivity
    (unique_obj (cont _ _ (cogen_power_limit@{o h cp so so} comp G c) N)).
  - symmetry; apply Hu; intro p; unfold image_leg; simpl.
    rewrite comp_assoc, <- fmap_comp.
    pose proof (unique_property
                  (iprod_ump (cogen_power_fam G c)
                     (cogen_power_limit@{o h cp so so} comp G c)
                     (saft_prod@{o dobj h so dp} U comp G d)
                     (fun p => iprod_proj (saft_fam U G d)
                                 (saft_prod_limit@{o dobj h so dp} U comp G d)
                                 (existT _ (projT1 p) (fmap[U] (projT2 p) ∘ h))))
                  p) as Hk.
    unfold saft_kappa; simpl in Hk |- *.
    rewrite Hk.
    exact (saft_point_commutes@{o dobj h so dp pl pa} U comp cont G d
             (existT _ (projT1 p) (fmap[U] (projT2 p) ∘ h))).
  - apply Hu; intro p; unfold image_leg; simpl.
    rewrite comp_assoc, <- fmap_comp.
    destruct p as [j k].
    pose proof (cogen_canonical_commutes comp G c j k) as Hc.
    simpl in Hc |- *.
    rewrite Hc; reflexivity.
Qed.

(** ** The subobject: the pullback of the canonical mono along [k] *)

Definition saft_sub@{o dobj h so dp cp +| h <= so, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C) (G : Cogenerator@{so o h} C)
  (d : D) (c : C) (h : d ~> U c) :
  SubObj (saft_prod@{o dobj h so dp} U comp G d) :=
  @sub_reindex C (complete_pullbacks comp) _ _
    (saft_kappa@{o dobj h so dp cp} U comp G d c h)
    (cogen_canonical_sub@{o h so cp} comp G c).

Definition saft_sub_to@{o dobj h so dp cp +| h <= so, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C) (G : Cogenerator@{so o h} C)
  (d : D) (c : C) (h : d ~> U c) :
  Subobject.sub_dom (saft_sub@{o dobj h so dp cp _ _} U comp G d c h) ~> c :=
  pullback_snd _ _ (@pullback C (complete_pullbacks comp) _ _ _
                      (saft_kappa@{o dobj h so dp cp} U comp G d c h)
                      (cogen_canonical@{cp so h so o} comp G c)).

(* [U] carries that pullback to a limit: the cone over the image of the
   cospan, with vertex [d]. *)
Definition saft_pb_cone@{o dobj h so dp cp pl pa ro pc sa +|
    h <= so, h < dp, h < cp, h < pc, h < sa +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D) (c : C) (h : d ~> U c) :
  Cone (@Compose@{dobj ro o pc h} _ _ _ U
          (Opposite_Functor@{ro h o}
             (@ASpan@{ro o sa h} (C^op) _ _ _
                (saft_kappa@{o dobj h so dp cp} U comp G d c h)
                (cogen_canonical@{cp so h so o} comp G c)))).
Proof.
  unshelve econstructor.
  - exact d.
  - unshelve econstructor.
    + intro x; destruct x; simpl.
      * exact (saft_point@{o dobj h so dp pl pa} U comp cont G d).
      * exact (fmap[U] (saft_kappa@{o dobj h so dp cp} U comp G d c h)
                 ∘ saft_point@{o dobj h so dp pl pa} U comp cont G d).
      * exact h.
    + (* Nine pairs of objects of [Roof], in the order [destruct] gives;
         [f] is a [RoofHom] from the second to the first. *)
      intros x y f; destruct x, y; simpl in f |- *.
      * (* RNeg, RNeg: an identity *)
        rewrite fmap_id; cat.
      * (* RNeg, RZero: [ZeroNeg], the leg at [RZero] on both sides *)
        reflexivity.
      * (* RNeg, RPos: no arrow *)
        inversion f.
      * (* RZero, RNeg: no arrow *)
        inversion f.
      * (* RZero, RZero: an identity *)
        rewrite fmap_id; cat.
      * (* RZero, RPos: no arrow *)
        inversion f.
      * (* RPos, RNeg: no arrow *)
        inversion f.
      * (* RPos, RZero: [ZeroPos], the square [saft_square] *)
        symmetry; apply saft_square.
      * (* RPos, RPos: an identity *)
        rewrite fmap_id; cat.
Defined.

Definition saft_lift@{o dobj h so dp cp pl pa +| h <= so, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D) (c : C) (h : d ~> U c) :
  d ~> U (Subobject.sub_dom (saft_sub@{o dobj h so dp cp _ _} U comp G d c h)) :=
  unique_obj (cont _ _ _ (saft_pb_cone@{o dobj h so dp cp pl pa so pa _}
                            U comp cont G d c h)).

Lemma saft_lift_commutes@{o dobj h so dp cp pl pa +| h <= so, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D) (c : C) (h : d ~> U c) :
  fmap[U] (saft_sub_to@{o dobj h so dp cp _ _} U comp G d c h)
    ∘ saft_lift@{o dobj h so dp cp pl pa _ _} U comp cont G d c h ≈ h.
Proof.
  exact (unique_property (cont _ _ _ (saft_pb_cone U comp cont G d c h)) RPos).
Qed.

(** ** The covering datum at [d], and its derivation *)

Definition SubobjectCoverAt@{o dobj h so dp w s t +| h <= so, h < dp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C) (G : Cogenerator@{so o h} C) (d : D)
  (W : WellPoweredAt@{w o s h t} (saft_prod@{o dobj h so dp} U comp G d)) :
  Type :=
  ∀ (c : C) (h : d ~> U c),
    { i : wp_index W &
      { s : d ~> U (Subobject.sub_dom (wp_to W i)) &
        { t : Subobject.sub_dom (wp_to W i) ~> c & fmap[U] t ∘ s ≈ h } } }.

Definition saft_cover_at@{o dobj h so dp cp w s t pl pa +|
    h <= so, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D)
  (W : WellPoweredAt@{w o s h t} (saft_prod@{o dobj h so dp} U comp G d)) :
  SubobjectCoverAt@{o dobj h so dp w s t _} U comp G d W.
Proof.
  intros c h.
  exists (wp_from W (saft_sub@{o dobj h so dp cp _ _} U comp G d c h)).
  destruct (wp_to_from W (saft_sub@{o dobj h so dp cp _ _} U comp G d c h))
    as [iso _].
  exists (fmap[U] (from iso)
            ∘ saft_lift@{o dobj h so dp cp pl pa _ _} U comp cont G d c h).
  exists (saft_sub_to@{o dobj h so dp cp _ _} U comp G d c h ∘ to iso).
  rewrite fmap_comp, <- comp_assoc, (comp_assoc (fmap[U] (to iso))).
  rewrite <- fmap_comp, iso_to_from, fmap_id, id_left.
  apply saft_lift_commutes.
Defined.

(** ** The solution set at [d], and SAFT through [GAFT] *)

Definition saft_solution_set_at@{o dobj h so dp cp w s t pl pa i +|
    h <= so, h < dp, h < cp, w <= i, h <= i +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D)
  (W : WellPoweredAt@{w o s h t} (saft_prod@{o dobj h so dp} U comp G d)) :
  SolutionSet@{i dobj o h} U d.
Proof.
  unshelve refine
    {| sol_index := { i : wp_index W & d ~> U (Subobject.sub_dom (wp_to W i)) }
     ; sol_obj := fun p => Subobject.sub_dom (wp_to W (projT1 p))
     ; sol_arr := fun p => projT2 p |}.
  intros c h.
  destruct (saft_cover_at@{o dobj h so dp cp w s t pl pa _ _ _}
              U comp cont G d W c h) as [i [s [t e]]].
  exists (existT _ i s); simpl.
  exists t; exact e.
Defined.

Definition SAFT_cover_wp_at@{o dobj h dp cp w s t pl pa +|
    h < dp, h < cp, w <= h +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl h pa h} C D U)
  (G : Cogenerator@{h o h} C)
  (W : ∀ d : D, WellPoweredAt@{w o s h t} (saft_prod@{o dobj h h dp} U comp G d)) :
  { F : D ⟶ C & F ⊣ U } :=
  GAFT U comp cont
    (fun d => saft_solution_set_at@{o dobj h h dp cp w s t pl pa h _ _ _}
                U comp cont G d (W d)).

Definition SAFT_cover_wp@{o dobj h dp cp w s t pl pa +|
    h < dp, h < cp, w <= h +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl h pa h} C D U)
  (G : Cogenerator@{h o h} C) (WP : WellPowered@{o h w s t} C) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_cover_wp_at@{o dobj h dp cp w s t pl pa _ _ _} U comp cont G
    (fun d => WP (saft_prod@{o dobj h h dp} U comp G d)).

(** ** Readbacks *)

(* The cover's index at [h] IS the well-powering's name for the pullback
   subobject [saft_sub]. *)
Example saft_cover_at_index@{o dobj h so dp cp w s t pl pa +|
    h <= so, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D)
  (W : WellPoweredAt@{w o s h t} (saft_prod@{o dobj h so dp} U comp G d))
  (c : C) (h : d ~> U c) :
  projT1 (saft_cover_at@{o dobj h so dp cp w s t pl pa _ _ _}
            U comp cont G d W c h)
    = wp_from W (saft_sub@{o dobj h so dp cp _ _} U comp G d c h) := eq_refl.

(* The solution set's index is the well-powering's index paired with a
   [d]-arrow. *)
Example saft_solution_set_at_index@{o dobj h so dp cp w s t pl pa i +|
    h <= so, h < dp, h < cp, w <= i, h <= i +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D)
  (W : WellPoweredAt@{w o s h t} (saft_prod@{o dobj h so dp} U comp G d)) :
  sol_index (saft_solution_set_at@{o dobj h so dp cp w s t pl pa i _ _ _}
               U comp cont G d W)
    = { i : wp_index W & d ~> U (Subobject.sub_dom (wp_to W i)) } := eq_refl.

(* The theorem IS [GAFT] at those solution sets, whose [Qed] seals the
   left adjoint. *)
Example SAFT_cover_wp_is_GAFT@{o dobj h dp cp w s t pl pa +|
    h < dp, h < cp, w <= h +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl h pa h} C D U)
  (G : Cogenerator@{h o h} C) (WP : WellPowered@{o h w s t} C) :
  SAFT_cover_wp@{o dobj h dp cp w s t pl pa _ _ _} U comp cont G WP
    = GAFT U comp cont
        (fun d => saft_solution_set_at@{o dobj h h dp cp w s t pl pa h _ _ _}
                    U comp cont G d (WP (saft_prod@{o dobj h h dp} U comp G d)))
  := eq_refl.
