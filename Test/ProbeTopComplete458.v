(*
   本文件为测试：ProbeTopComplete458。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Structure.Cartesian.
Require Import Category.Adjunction.Continuity.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Subspace.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Eqdep_dec.
Require Import Category.Instance.Top.Complete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Instance.Cones.
Require Import Category.Instance.Cones.Limit.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.One.
Require Import Category.Instance.Roof.
Require Import Category.Instance.Top.Complete.ConeComma.
Require Import Category.Structure.Complete.Freyd.
Require Import Category.Construction.Quotient.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.CompHaus.
Require Import Category.Instance.Top.StoneCech.Refutations.
Require Import Category.Instance.Top.Complete.Refutations.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Coequalizer.
Require Import Category.Instance.Sets.Cocomplete.
Require Import Category.Instance.Sets.Coequalizer.
Require Import Category.Instance.Top.Cocomplete.
Require Import Category.Construction.Product.Limit.
Require Import Category.Instance.Top.Cocomplete.Refutations.
Require Import Category.Instance.Top.Subspace.TypeValued.
Require Import Category.Instance.Top.Cocomplete.TypeValued.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(* The instrument *)
Fail Check probe458_absent_name.

(* 相关说明。 （已译） *)

(* CONTROL: [PInit]'s index universe is free, under the CLOSED binder
   [@{o i}]; its opens read back at [eq_refl]. *)
Definition p458_pinit@{o i} (S : SetoidObject@{o o}) (I : Type@{i})
  (X : I → PTop@{o}) (t : ∀ k : I, SetoidMorphism@{o o o} S (X k)) :
  PTop@{o} := PInit S I X t.

Example p458_pinit_open@{o i} (S : SetoidObject@{o o}) (I : Type@{i})
  (X : I → PTop@{o}) (t : ∀ k : I, SetoidMorphism@{o o o} S (X k))
  (V : S → Prop) :
  POpen (PInit S I X t) V = pinit_open S I X t V := eq_refl.

(* CONTROL: 普遍性质 over ARBITRARY spaces 映射 in, and
 one-map case, subspace topology, restated. （已译） *)
Definition p458_pinit_universal@{o i +} (S : SetoidObject@{o o})
  (I : Type@{i}) (X : I → PTop@{o})
  (t : ∀ k : I, SetoidMorphism@{o o o} S (X k)) (Z : PTop@{o})
  (g : SetoidMorphism@{o o o} Z S) :
  @PCont Z (PInit S I X t) g <->
  (∀ k, @PCont Z (X k) (setoid_morphism_compose@{o o o} (t k) g)) :=
  pinit_universal S I X t Z g.

Definition p458_pinit_one_psub@{o +} (X : PTop@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S X)
  (V : S → Prop) :
  POpen (PInit S Datatypes.unit (fun _ => X) (fun _ => h)) V
  <-> POpen (PSub X S h) V :=
  PInit_one_PSub X S h V.

(* 相关说明。 （已译） *)
Definition p458_recipe_above@{j o so v v1 w w1 +| o < so, o < j +}
  {J : Category@{j o o}} (T : J ⟶ PTopCat@{o so})
  (N : Cone (PForget@{o so} ◯ T)) (HN : IsLimitCone@{v v1 j o so} N) :
  IsLimitCone@{w w1 j o so} (pinit_cone T N) :=
  pinit_cone_limiting T N HN.

Example p458_recipe_med_map@{j o so +| o < so +}
  {J : Category@{j o o}} (T : J ⟶ PTopCat@{o so})
  (N : Cone (PForget@{o so} ◯ T)) (HN : IsLimitCone N) (M : Cone T) :
  pmap (unique_obj (pinit_cone_limiting T N HN M))
    = unique_obj (HN (FCone PForget M)) := eq_refl.

(* 相关说明。 （已译） *)
Definition p458_topology_forced@{j o so +| o < so +}
  {J : Category@{j o o}} (T : J ⟶ PTopCat@{o so}) (L : Cone T)
  (HL : IsLimitCone L) (V : vertex_obj[L] → Prop) :
  POpen (vertex_obj[L]) V
  <-> POpen (vertex_obj[pinit_cone T (FCone PForget L)]) V :=
  PTop_limit_open_iff_initial T L HL V.

(* 相关说明。 （已译） *)
Definition p458_pforget_continuous@{o so +| o < so +} :
  ContinuousFunctor PForget@{o so} := PForget_Continuous.

Definition p458_pforget_preserves_above@{s o so +| o < so, o < s +}
  (J : Category@{s o o}) (T : J ⟶ PTopCat@{o so}) :
  PreservesLimitCone T PForget@{o so} := PForget_PreservesLimitCone J T.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition p458_iprod_at_points@{o so +| o < so +} :
  @HasIndexedProducts@{o o o o so o} PTopCat@{o so} :=
  PTop_HasIndexedProducts.

Definition p458_iprod_below@{i o so +| i < o, o < so +} :
  @HasIndexedProducts@{i i i o so o} PTopCat@{o so} :=
  PTop_HasIndexedProducts.

(* N1 *)
Fail Definition p458_iprod_above@{s o so +| o < so, o < s +} :
  @HasIndexedProducts@{s s s s so o} PTopCat@{o so} :=
  PTop_HasIndexedProducts.

(* 相关说明。 （已译） *)
Example p458_product_obj@{i o so +| i <= o, o < so +} (A : Type@{i})
  (X : A → PTop@{o}) :
  @indexed_product PTopCat@{o so} PTop_HasIndexedProducts A X
    = PProd A X := eq_refl.

Example p458_pprod_open@{i o +| i <= o +} (A : Type@{i})
  (X : A → PTop@{o}) (V : PProd_carrier A X → Prop) :
  POpen (PProd A X) V
    = pinit_open (PProd_carrier A X) A X (pprod_leg A X) V := eq_refl.

Definition p458_iprod_topology_forced@{i o so +| i <= o, o < so +}
  (A : Type@{i}) (X : A → PTop@{o}) (Y : PTop@{o})
  (p : ∀ a, Y ~{PTopCat@{o so}}~> X a)
  (H : @IsIndexedProduct PTopCat@{o so} A X Y p) (V : Y → Prop) :
  POpen Y V <-> POpen (PInit Y A X (fun a => pmap (p a))) V :=
  PTop_iprod_open_iff_initial A X Y p H V.

(* 相关说明。 （已译） *)
Definition p458_equalizer_topology_forced@{o so +| o < so +}
  {X Y : PTop@{o}} (f g : X ~{PTopCat@{o so}}~> Y) (E : PTop@{o})
  (e : E ~{PTopCat@{o so}}~> X)
  (H : @IsEqualizer PTopCat@{o so} X Y f g E e) (V : E → Prop) :
  POpen E V <-> POpen (PSub X E (pmap e)) V :=
  PTop_equalizer_open_iff_PSub f g E e H V.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition p458_complete_at_points@{o so +| o < so +} :
  @Complete@{o o o so} PTopCat@{o so} := PTop_Complete.

Definition p458_complete_below@{s o so +| s < o, o < so +} :
  @Complete@{o s o so} PTopCat@{o so} := PTop_Complete.

Definition p458_complete_at_set@{o so +| Set < o, o < so +} :
  @Complete@{o Set o so} PTopCat@{o so} := PTop_Complete.

Definition p458_complete_points_at_set@{so +| Set < so +} :
  @Complete@{Set Set Set so} PTopCat@{Set so} := PTop_Complete.

Definition p458_complete_record_above@{r o so +| o < r, o < so +} :
  @Complete@{r o o so} PTopCat@{o so} := PTop_Complete.

(* N2 *)
Fail Definition p458_complete_above@{r s o so +| o < s, o < so, s <= r +} :
  @Complete@{r s o so} PTopCat@{o so} := PTop_Complete.

(* 相关说明。 （已译） *)
Example p458_complete_apex@{s o so +| s <= o, o < so +}
  (J : Category@{s o o}) (T : J ⟶ PTopCat@{o so}) :
  vertex_obj[@limit_cone _ _ _ (@PTop_Complete@{o s o so _ _} J T)]
    = pinit_top T (Sets_limit_cone (PForget ◯ T)) := eq_refl.

(* CONTROL: book's route, at one instance [Complete@{o o o so}];
 it IS #416's 定理 at products #457's equalizers. （已译） *)
Definition p458_complete_via_products@{o so +| o < so +} :
  @Complete@{o o o so} PTopCat@{o so} := PTop_Complete_via_products.

Example p458_via_products_is_book_route@{o so +| o < so +} :
  @PTop_Complete_via_products@{o so _ _ _ _ _}
    = @Complete_from_products_equalizers PTopCat@{o so}
        PTop_HasIndexedProducts PTop_HasEqualizers := eq_refl.

(* N3 *)
Fail Definition p458_via_products_below@{s o so +| s < o, o < so +} :
  @Complete@{o s o so} PTopCat@{o so} := PTop_Complete_via_products.

(* N4 *)
Fail Definition p458_via_products_record_above@{r o so +| o < r, o < so +} :
  @Complete@{r o o so} PTopCat@{o so} := PTop_Complete_via_products.

(* 相关说明。 （已译） *)
Definition p458_via_products_apex@{o so +| o < so +}
  (J : Category@{o o o}) (T : J ⟶ PTopCat@{o so}) :
  ex (fun S => ex (fun h =>
    vertex_obj[@limit_cone _ _ _ (@PTop_Complete_via_products J T)]
      = PSub (PProd (obj[J]) (fun j => fobj[T] j)) S h)) :=
  PTop_Complete_via_products_apex J T.

Definition p458_complete_routes_iso@{o so +| o < so +}
  (J : Category@{o o o}) (T : J ⟶ PTopCat@{o so}) :
  vertex_obj[@limit_cone _ _ _ (@PTop_Complete J T)]
    ≅[PTopCat@{o so}]
  vertex_obj[@limit_cone _ _ _ (@PTop_Complete_via_products J T)] :=
  PTop_Complete_routes_iso J T.

(* N5 *)
Fail Example p458_complete_routes_carrier@{o so +| o < so +}
  (J : Category@{o o o}) (T : J ⟶ PTopCat@{o so}) :
  carrier (pt_carrier (vertex_obj[@limit_cone _ _ _ (PTop_Complete J T)]))
  = carrier (pt_carrier
      (vertex_obj[@limit_cone _ _ _ (PTop_Complete_via_products J T)])) :=
  eq_refl.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition p458_ppair_open_iff_box@{o +} (X1 X2 : PTop@{o})
  (W : PPair_carrier X1 X2 → Prop) :
  POpen (PPair X1 X2) W <-> pair_box_union X1 X2 W :=
  PPair_open_iff_box X1 X2 W.

Definition p458_cartesian@{o so +| o < so +} : @Cartesian PTopCat@{o so} :=
  PTop_Cartesian.

(* 相关说明。 （已译） *)
Definition p458_box_not_product@{o so +| o < so +} :
  @IsIndexedProduct PTopCat@{o so} nat (fun _ => PBool@{o})
    (PBoxTop nat (fun _ => PBool@{o}))
    (pbox_proj nat (fun _ => PBool@{o}) Nat.eq_dec)
  → False :=
  box_not_indexed_product.

Definition p458_box_mediator@{o +} :
  PMor@{o} PConv@{o} (PProd nat (fun _ => PBool@{o})) :=
  pconv_prod_mediator.

Definition p458_box_strictly_finer@{o +} :
  POpen (PProd nat (fun _ => PBool@{o})) pbox_all_false → False :=
  pbox_all_false_not_product_open.

(* 相关说明。 （已译） *)

(* CONTROL: G_*'s 对象 action, (a) RIGHT adjoint G_*,
 restated any [G], [T] shape. （已译） *)
Example p458_coneimage_obj@{oj oc od h +} {J : Category@{oj h h}}
  {C : Category@{oc h h}} {D : Category@{od h h}} (G : C ⟶ D)
  (T : J ⟶ C) (N : Cone T) : fobj[ConeImage G T] N = FCone G N :=
  eq_refl.

Definition p458_ex3a_right@{oj oc od h +} {J : Category@{oj h h}}
  {C : Category@{oc h h}} {D : Category@{od h h}} (G : C ⟶ D)
  (T : J ⟶ C) (W : Cones (G ◯ T) ⟶ Cones T) (A : ConeImage G T ⊣ W)
  (L : Limit (G ◯ T)) : Limit T :=
  limit_from_cone_right_adjoint G T W A L.

(* N6 *)
Fail Definition p458_ex3a_left@{oj oc od h +} {J : Category@{oj h h}}
  {C : Category@{oc h h}} {D : Category@{od h h}} (G : C ⟶ D)
  (T : J ⟶ C) (F : Cones (G ◯ T) ⟶ Cones T) (A : F ⊣ ConeImage G T)
  (L : Limit (G ◯ T)) : Limit T :=
  limit_from_cone_right_adjoint G T F A L.

(* CONTROL: at [PForget] 右伴随 weakest topology, and
 (a) at it IS [PTop_limit_via_cones]; 左伴随, discrete
 topology, exists too. （已译） *)
Example p458_pinitcone_obj@{j o so +| o < so +} {J : Category@{j o o}}
  (T : J ⟶ PTopCat@{o so}) (N : Cone (PForget@{o so} ◯ T)) :
  fobj[PInitCone T] N = pinit_cone T N := eq_refl.

Definition p458_limit_via_right@{j o so +| o < so +}
  {J : Category@{j o o}} (T : J ⟶ PTopCat@{o so})
  (L : Limit (PForget@{o so} ◯ T)) : Limit T :=
  limit_from_cone_right_adjoint PForget T (PInitCone T)
    (pcone_adjunction T) L.

Example p458_limit_via_right_is@{j o so +| o < so +} {J : Category@{j o o}}
  (T : J ⟶ PTopCat@{o so}) (L : Limit (PForget@{o so} ◯ T)) :
  p458_limit_via_right T L = PTop_limit_via_cones T L := eq_refl.

Definition p458_left_adjoint_at_pforget@{j o so +| o < so +}
  {J : Category@{j o o}} (T : J ⟶ PTopCat@{o so}) :
  PDiscCone T ⊣ ConeImage PForget@{o so} T :=
  pdisc_cone_adjunction T.

(* N7 *)
Fail Definition p458_limit_via_left@{j o so +| o < so +}
  {J : Category@{j o o}} (T : J ⟶ PTopCat@{o so})
  (L : Limit (PForget@{o so} ◯ T)) : Limit T :=
  limit_from_cone_right_adjoint PForget T (PDiscCone T)
    (pdisc_cone_adjunction T) L.

(* 相关说明。 （已译） *)
Definition p458_complete_via_cones_below@{s o so +| s < o, o < so +} :
  @Complete@{o s o so} PTopCat@{o so} := PTop_Complete_via_cones.

Definition p458_complete_via_cones_at_points@{o so +| o < so +} :
  @Complete@{o o o so} PTopCat@{o so} := PTop_Complete_via_cones.

(* N8 *)
Fail Definition p458_via_cones_record_above@{r o so +| o < r, o < so +} :
  @Complete@{r o o so} PTopCat@{o so} := PTop_Complete_via_cones.

(* N9 *)
Fail Definition p458_via_cones_above@{s o so +| o < s, o < so +} :
  @Complete@{s s o so} PTopCat@{o so} := PTop_Complete_via_cones.

Example p458_via_cones_cone@{s o so +| s <= o, o < so +}
  (J : Category@{s o o}) (T : J ⟶ PTopCat@{o so}) :
  @limit_cone _ _ _ (@PTop_Complete_via_cones@{o s o so _ _ _} J T)
    = @limit_cone _ _ _ (@PTop_Complete@{o s o so _ _} J T) := eq_refl.

Definition p458_via_cones_cone_is@{s o so +| s <= o, o < so +}
  (J : Category@{s o o}) (T : J ⟶ PTopCat@{o so}) :
  @limit_cone _ _ _ (@PTop_Complete_via_cones@{o s o so _ _ _} J T)
    = @limit_cone _ _ _ (@PTop_Complete@{o s o so _ _} J T) :=
  PTop_via_cones_cone J T.

Definition p458_products_via_cone_comma@{i o so +| i <= o, o < so +} :
  @HasIndexedProducts@{i i i o so o} PTopCat@{o so} :=
  PTop_products_via_cone_comma.

(* 相关说明。 （已译） *)

(* CONTROL: [PFinal]'s index universe is free, under the CLOSED binder
   [@{o i}]; its opens read back at [eq_refl]. *)
Definition p458_pfinal@{o i} (S : SetoidObject@{o o}) (Ix : Type@{i})
  (X : Ix → PTop@{o}) (f : ∀ k : Ix, SetoidMorphism@{o o o} (X k) S) :
  PTop@{o} := PFinal S Ix X f.

Example p458_pfinal_open@{o i} (S : SetoidObject@{o o}) (Ix : Type@{i})
  (X : Ix → PTop@{o}) (f : ∀ k : Ix, SetoidMorphism@{o o o} (X k) S)
  (V : S → Prop) :
  POpen (PFinal S Ix X f) V
  = ((∀ s t : S, s ≈ t → V s → V t) /\
     (∀ k : Ix, POpen (X k) (fun x => V (f k x)))) := eq_refl.

(* CONTROL: 普遍性质 over ARBITRARY spaces 映射 out,
 one-map case, quotient topology, restated. （已译） *)
Definition p458_pfinal_universal@{o i +} (S : SetoidObject@{o o})
  (Ix : Type@{i}) (X : Ix → PTop@{o})
  (f : ∀ k : Ix, SetoidMorphism@{o o o} (X k) S) (Z : PTop@{o})
  (g : SetoidMorphism@{o o o} S Z) :
  @PCont (PFinal S Ix X f) Z g <->
  (∀ k, @PCont (X k) Z (setoid_morphism_compose@{o o o} g (f k))) :=
  pfinal_universal S Ix X f Z g.

Definition p458_pfinal_one_pquot@{o +} (X : PTop@{o})
  (T : SetoidObject@{o o}) (q : SetoidMorphism@{o o o} X T)
  (V : T → Prop) :
  POpen (PQuot X T q) V
  <-> POpen (PFinal T Datatypes.unit (fun _ => X) (fun _ => q)) V :=
  pfinal_one_map_PQuot X T q V.

(* 相关说明。 （已译） *)
Definition p458_corecipe_above@{o so s r r' x x' +| o < so, o < s +}
  {D : Category@{s o o}} (F : D ⟶ PTopCat@{o so})
  (N : Cocone (PForget@{o so} ◯ F))
  (HN : IsColimitCocone@{x' x' r' s o so} N) :
  IsColimitCocone@{x x r s o so} (PFinalCocone F N) :=
  pfinal_cocone_colimiting F N HN.

Example p458_pcolimit_apex@{r s o so +| o < so, s <= o, o <= r +}
  {D : Category@{s o o}} (F : D ⟶ PTopCat@{o so}) :
  vertex_obj[@limit_cone _ _ _ (@PColimit@{r s o so _ _} D F)]
    = PFinal (Sets_colim_obj (PForget ◯ F)) (obj[D]) (fun d => F d)
        (fun d => Sets_colim_inj (PForget ◯ F) d) := eq_refl.

Example p458_pcolimit_med_at@{r s o so +| o < so, s <= o, o <= r +}
  {D : Category@{s o o}} (F : D ⟶ PTopCat@{o so}) (M : Cocone F) (d : D)
  (x : pt_carrier (F d)) :
  pmap (unique_obj (@ump_limits _ _ _ (@PColimit@{r s o so _ _} D F) M))
    (existT _ d x) = pmap (cocone_inj M d) x := eq_refl.

Definition p458_pcolimit_med_at_is@{r s o so +| o < so, s <= o, o <= r +}
  {D : Category@{s o o}} (F : D ⟶ PTopCat@{o so}) (M : Cocone F) (d : D)
  (x : pt_carrier (F d)) :
  pmap (unique_obj (@ump_limits _ _ _ (@PColimit@{r s o so _ _} D F) M))
    (existT _ d x) = pmap (cocone_inj M d) x :=
  PColimit_med_at F M d x.

Definition p458_colimit_open_iff_final@{o so s r +| o < so +}
  {D : Category@{s o o}} {F : D ⟶ PTopCat@{o so}}
  (L : Colimit@{r s o so} F) (V : pt_carrier (colimit_apex L) → Prop) :
  POpen (colimit_apex L) V
  <-> POpen (PFinal (pt_carrier (colimit_apex L)) (obj[D]) (fun d => F d)
               (fun d => pmap (colimit_inj (colimit_is_acolimit L) d))) V :=
  PTop_colimit_open_iff_final L V.

(* 相关说明。 （已译） *)
Definition p458_pforget_cocontinuous@{o so +| o < so +} :
  CocontinuousFunctor PForget@{o so} := PForget_Cocontinuous.

Definition p458_pforget_copreserves_above@{s o so +| o < so, o < s +}
  (J : Category@{s o o}) (K : J ⟶ PTopCat@{o so}) :
  PreservesColimitCocone K PForget@{o so} :=
  PForget_PreservesColimitCocone J K.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition p458_cocomplete_at_points@{o so +| o < so +} :
  @Cocomplete@{o o o so} PTopCat@{o so} := PTop_Cocomplete.

Definition p458_cocomplete_below@{s o so +| s < o, o < so +} :
  @Cocomplete@{o s o so} PTopCat@{o so} := PTop_Cocomplete.

Definition p458_cocomplete_points_at_set@{so +| Set < so +} :
  @Cocomplete@{Set Set Set so} PTopCat@{Set so} := PTop_Cocomplete.

Definition p458_cocomplete_record_above@{r o so +| o < r, o < so +} :
  @Cocomplete@{r o o so} PTopCat@{o so} := PTop_Cocomplete.

(* N10 *)
Fail Definition p458_cocomplete_above@{r s o so +| o < s, o < so, s <= r +} :
  @Cocomplete@{r s o so} PTopCat@{o so} := PTop_Cocomplete.

(* CONTROL: book's route, at one instance
 [Cocomplete@{o o o so}]; it IS #416's 定理 at coproducts and
 #457's coequalizers. （已译） *)
Definition p458_cocomplete_via_coeq@{o so +| o < so +} :
  @Cocomplete@{o o o so} PTopCat@{o so} := PTop_Cocomplete_via_coproducts.

Example p458_via_coeq_is_book_route@{o so +| o < so +} :
  @PTop_Cocomplete_via_coproducts@{o so _ _ _ _ _ _}
    = Cocomplete_from_coproducts_coequalizers PTop_HasIndexedCoproducts
        PTop_HasCoequalizers := eq_refl.

(* N11 *)
Fail Definition p458_via_coeq_below@{s o so +| s < o, o < so +} :
  @Cocomplete@{o s o so} PTopCat@{o so} := PTop_Cocomplete_via_coproducts.

(* N12 *)
Fail Definition p458_via_coeq_record_above@{r o so +| o < r, o < so +} :
  @Cocomplete@{r o o so} PTopCat@{o so} := PTop_Cocomplete_via_coproducts.

(* 相关说明。 （已译） *)
Definition p458_cocomplete_routes_iso@{o so +| o < so +}
  (D : Category@{o o o}) (F : D ⟶ PTopCat@{o so}) :
  colimit_apex (PTop_Cocomplete D F)
    ≅[PTopCat@{o so}] colimit_apex (PTop_Cocomplete_via_coproducts D F) :=
  PTop_Cocomplete_routes_iso D F.

Example p458_cocomplete_routes_carrier@{o so +| o < so +}
  (D : Category@{o o o}) (F : D ⟶ PTopCat@{o so}) :
  carrier (pt_carrier (colimit_apex (PTop_Cocomplete D F)))
  = carrier
      (pt_carrier (colimit_apex (PTop_Cocomplete_via_coproducts D F))) :=
  eq_refl.

(* N13 *)
Fail Example p458_cocomplete_routes_points@{o so +| o < so +}
  (D : Category@{o o o}) (F : D ⟶ PTopCat@{o so}) :
  pt_carrier (colimit_apex (PTop_Cocomplete D F))
  = pt_carrier (colimit_apex (PTop_Cocomplete_via_coproducts D F)) := eq_refl.

(* N14 *)
Fail Example p458_cocomplete_routes_spaces@{o so +| o < so +}
  (D : Category@{o o o}) (F : D ⟶ PTopCat@{o so}) :
  colimit_apex (PTop_Cocomplete D F)
  = colimit_apex (PTop_Cocomplete_via_coproducts D F) := eq_refl.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Example p458_psigma_open@{o i +| i <= o +} (Ix : Type@{i})
  (X : Ix → PTop@{o})
  (V : Sets_icoprod_obj (fun k => pt_carrier (X k)) → Prop) :
  POpen (PSigma Ix X) V
  = ((∀ p q : Sets_icoprod_obj (fun k => pt_carrier (X k)),
        p ≈ q → V p → V q) /\
     (∀ k : Ix, POpen (X k) (fun x => V (existT _ k x)))) := eq_refl.

Definition p458_icoprod_at_points@{o so u +| o < so, so <= u, o < u +} :
  @HasIndexedCoproducts@{u o o so o} PTopCat@{o so} :=
  PTop_HasIndexedCoproducts.

(* N15 *)
Fail Definition p458_icoprod_above@{s o so u +| o < so, o < s, so <= u,
  s < u +} :
  @HasIndexedCoproducts@{u s s so o} PTopCat@{o so} :=
  PTop_HasIndexedCoproducts.

Definition p458_sum_injections_differ@{o so u | o < so, o < u +} :
  psigma_inj@{o so o u} bool (fun _ => PTwoIndisc@{o}) true
    ≈[PTopCat@{o so}] psigma_inj@{o so o u} bool (fun _ => PTwoIndisc) false
  → False := PTwoIndiscSum_injections_differ.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition p458_top_coproducts_small@{o h u u0 +| o < h, u0 <= o, h < u +} :
  @HasIndexedCoproducts@{u u0 h h h} Top@{h o} :=
  Top_HasIndexedCoproducts_small.

Definition p458_top_coequalizers@{o h +| o < h +} :
  @HasCoequalizers Top@{h o} := Top_HasCoequalizers.

Example p458_top_coequalizer_obj@{o h +| o < h +} {x y : Top@{h o}}
  (f g : x ~{Top@{h o}}~> y) :
  `1 (@coeq _ Top_HasCoequalizers x y f g)
    = TQuot y (SetsCoeq (continuous_map f) (continuous_map g))
        (sets_coeq_proj (continuous_map f) (continuous_map g)) := eq_refl.

(* N16 *)
Fail Definition p458_top_book_route@{o h +| o < h +} :
  @Cocomplete Top@{h o} :=
  Cocomplete_from_coproducts_coequalizers Top_HasIndexedCoproducts_small
    Top_HasCoequalizers.

(* N17 *)
Fail Definition p458_top_book_route_free :=
  Cocomplete_from_coproducts_coequalizers Top_HasIndexedCoproducts_small
    Top_HasCoequalizers.

(* N18 *)
Fail Definition p458_top_coproducts_at_homs@{o h u +| o < h, h < u +} :
  @HasIndexedCoproducts@{u h h h h} Top@{h o} :=
  Top_HasIndexedCoproducts_small.

(* The points colimit [Top@{h o}] over shape at below the
 points: sigma over shape's 对象, at [o]. （已译） *)
Definition p458_tcarr@{o h s +| o < h, s <= o +} (D : Category@{s h h})
  (F : D ⟶ Top@{h o}) : Type@{o} :=
  { d : obj[D] & top_carrier (F d) }.

(* N19 *)
Fail Inductive p458_tcolim_rel@{o h s +| o < h, s <= o +}
  (D : Category@{s h h}) (F : D ⟶ Top@{h o}) :
  p458_tcarr D F → p458_tcarr D F → Type@{o} :=
  | p458_tcr_point : ∀ (d : D) (x y : top_carrier (F d)), x ≈ y →
      p458_tcolim_rel (existT _ d x) (existT _ d y)
  | p458_tcr_glue : ∀ (d d' : D) (f : d ~{D}~> d') (x : top_carrier (F d)),
      p458_tcolim_rel (existT _ d x)
        (existT _ d' (continuous_map (fmap[F] f) x))
  | p458_tcr_sym : ∀ p q, p458_tcolim_rel p q → p458_tcolim_rel q p
  | p458_tcr_trans : ∀ p q r, p458_tcolim_rel p q →
      p458_tcolim_rel q r → p458_tcolim_rel p r.

(* CONTROL: same 关系 valued at homs' universe [h]. （已译） *)
Inductive p458_tcolim_relH@{o h s +| o < h, s <= o +}
  (D : Category@{s h h}) (F : D ⟶ Top@{h o}) :
  p458_tcarr D F → p458_tcarr D F → Type@{h} :=
  | p458_tcrH_point : ∀ (d : D) (x y : top_carrier (F d)), x ≈ y →
      p458_tcolim_relH (existT _ d x) (existT _ d y)
  | p458_tcrH_glue : ∀ (d d' : D) (f : d ~{D}~> d') (x : top_carrier (F d)),
      p458_tcolim_relH (existT _ d x)
        (existT _ d' (continuous_map (fmap[F] f) x))
  | p458_tcrH_sym : ∀ p q, p458_tcolim_relH p q → p458_tcolim_relH q p
  | p458_tcrH_trans : ∀ p q r, p458_tcolim_relH p q →
      p458_tcolim_relH q r → p458_tcolim_relH p r.

(* N20 *)
Fail Definition p458_tcolim_relH_at_o@{o h s +| o < h, s <= o +}
  (D : Category@{s h h}) (F : D ⟶ Top@{h o}) :
  p458_tcarr D F → p458_tcarr D F → Type@{o} :=
  p458_tcolim_relH D F.

(* CONTROL: same 关系 valued [Prop] fits at [Type@{o}]; the
 mediator respects it up [inhabited]; squash eliminates a
 命题. （已译） *)
Inductive p458_tcolim_prel@{o h s +| o < h, s <= o +}
  (D : Category@{s h h}) (F : D ⟶ Top@{h o}) :
  p458_tcarr D F → p458_tcarr D F → Prop :=
  | p458_tcp_point : ∀ (d : D) (x y : top_carrier (F d)),
      inhabited (x ≈ y) → p458_tcolim_prel (existT _ d x) (existT _ d y)
  | p458_tcp_glue : ∀ (d d' : D) (f : d ~{D}~> d') (x : top_carrier (F d)),
      p458_tcolim_prel (existT _ d x)
        (existT _ d' (continuous_map (fmap[F] f) x))
  | p458_tcp_sym : ∀ p q, p458_tcolim_prel p q → p458_tcolim_prel q p
  | p458_tcp_trans : ∀ p q r, p458_tcolim_prel p q →
      p458_tcolim_prel q r → p458_tcolim_prel p r.

Definition p458_tcolim_prel_at_o@{o h s +| o < h, s <= o +}
  (D : Category@{s h h}) (F : D ⟶ Top@{h o}) :
  p458_tcarr D F → p458_tcarr D F → Type@{o} :=
  p458_tcolim_prel D F.

Lemma p458_tcolim_med_squashed@{o h s +| o < h, s <= o +}
  (D : Category@{s h h}) (F : D ⟶ Top@{h o}) (Z : TopSpace@{o})
  (m : p458_tcarr D F → top_carrier Z)
  (Hp : ∀ d (x y : top_carrier (F d)), x ≈ y →
          m (existT _ d x) ≈ m (existT _ d y))
  (Hm : ∀ d d' (f : d ~{D}~> d') x,
          m (existT _ d x) ≈ m (existT _ d' (continuous_map (fmap[F] f) x)))
  (p q : p458_tcarr D F) :
  p458_tcolim_prel D F p q → inhabited (m p ≈ m q).
Proof.
  induction 1 as [d x y [e]|d d' f x|p q _ [IH]|p q r _ [IH1] _ [IH2]].
  - constructor. exact (Hp d x y e).
  - constructor. exact (Hm d d' f x).
  - constructor. symmetry. exact IH.
  - constructor. transitivity (m q); assumption.
Qed.

Definition p458_squash_prop@{o +} (Z : TopSpace@{o}) (a b : top_carrier Z)
  (P : Prop) (k : a ≈ b → P) (w : inhabited (a ≈ b)) : P :=
  match w with inhabits e => k e end.

(* N21 *)
Fail Definition p458_tcolim_elim@{o h s +| o < h, s <= o +}
  (D : Category@{s h h}) (F : D ⟶ Top@{h o}) (Z : TopSpace@{o})
  (m : p458_tcarr D F → top_carrier Z) (p q : p458_tcarr D F)
  (H : p458_tcolim_prel D F p q) : m p ≈ m q :=
  match H with
  | p458_tcp_point _ _ _ _ _ _ => _
  | p458_tcp_glue _ _ _ _ _ _ => _
  | p458_tcp_sym _ _ _ _ _ => _
  | p458_tcp_trans _ _ _ _ _ _ _ => _
  end.

(* N22 *)
Fail Definition p458_squash_elim@{o +} (Z : TopSpace@{o})
  (a b : top_carrier Z) (w : inhabited (a ≈ b)) : a ≈ b :=
  match w with inhabits e => e end.

(* 相关说明。 （已译） *)

(* CONTROL: printed (a) refuted, refuting data, left
 伴随 limit [G ◯ T] it consists of, restated. （已译） *)
Definition p458_ex3a_literal_refuted :
  Ex3a_left_literal ex3_G1 ex3_T0 → False :=
  ex3a_left_adjoint_literal_refuted.

(* 相关说明。 （已译） *)
Definition p458_ex3a_literal_above_set@{u u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 |
  Set < u, Set < u0, Set < u1, Set < u2, Set < u3, Set < u4, Set < u5,
  Set < u6, Set < u7, Set < u8, Set < u9, u8 < u5, u9 < u2 +} :
  Ex3a_left_literal@{u u5 u0 u1 u2 u9 u3 u4 u6 u8 u7} ex3_G1@{u7 u4 u8}
    ex3_T0@{u6 u8 u7 u5} → False :=
  ex3a_left_adjoint_literal_refuted@{u u0 u1 u2 u3 u4 u5 u6 u7 u8 u9}.

Definition p458_ex3a_counterexample :
  Ex3a_left_refuting_data ex3_G1 ex3_T0 := ex3a_left_counterexample.

Definition p458_ex3_left_adj : ex3_LeftAdj ⊣ ConeImage ex3_G1 ex3_T0 :=
  ex3_left_adj.

Definition p458_ex3_point_limit : Limit (ex3_G1 ◯ ex3_T0) :=
  ex3_point_limit.

(* N23 *)
Fail Definition p458_ex3a_left_at_roof : Limit ex3_T0 :=
  limit_from_cone_right_adjoint ex3_G1 ex3_T0 ex3_LeftAdj ex3_left_adj
    ex3_point_limit.

(* CONTROL: completeness refuted above the points under [IEM]; no arrow
   index at or below them, constructively. *)
Definition p458_not_complete_above@{e r s o so +| o < so, o < s,
  s <= r +} :
  IEM@{e} → @Complete@{r s o so} PTopCat@{o so} → False :=
  PTop_not_complete_IEM.

(* N24 *)
Fail Definition p458_not_complete_at_points@{e r o so +| o < so, o <= r +} :
  IEM@{e} → @Complete@{r o o so} PTopCat@{o so} → False :=
  PTop_not_complete_IEM.

Definition p458_no_arrow_index_below@{s o so +| s <= o, o < so +} :
  ArrowIndex@{s so o} PTopCat@{o so} → False :=
  PTop_no_ArrowIndex_below.

(* CONTROL: products refuted above the points under [IEM]. *)
Definition p458_iprod_refuted_above@{e s o so +| o < so, o < s +} :
  IEM@{e} → @HasIndexedProducts@{s s s s so o} PTopCat@{o so} → False :=
  PTop_iprod_refuted_IEM.

(* N25 *)
Fail Definition p458_iprod_refuted_at_points@{e o so +| o < so +} :
  IEM@{e} → @HasIndexedProducts@{o o o o so o} PTopCat@{o so} → False :=
  PTop_iprod_refuted_IEM.

(* 相关说明。 （已译） *)
Definition p458_top_iprod_refuted@{e h o +| o < h +} :
  IEM@{e} → @HasIndexedProducts@{h h h h h h} Top@{h o} → False :=
  Top_iprod_refuted_IEM_canonical.

(* N26 *)
Fail Definition p458_top_iprod_refuted_at_points@{e h o +| o < h +} :
  IEM@{e} → @HasIndexedProducts@{o o o h h h} Top@{h o} → False :=
  Top_iprod_refuted_IEM_canonical.

(* 相关说明。 （已译） *)
Definition p458_not_cocomplete_above@{e r s o so +| o < so, o < s,
  s <= r +} :
  IEM@{e} → @Cocomplete@{r s o so} PTopCat@{o so} → False :=
  PTop_not_cocomplete_IEM.

Definition p458_not_cocomplete_points_at_set@{e r s so +| Set < so,
  Set < s, s <= r +} :
  IEM@{e} → @Cocomplete@{r s Set so} PTopCat@{Set so} → False :=
  PTop_not_cocomplete_IEM.

(* N27 *)
Fail Definition p458_not_cocomplete_at_points@{e r o so +| o < so,
  o <= r +} :
  IEM@{e} → @Cocomplete@{r o o so} PTopCat@{o so} → False :=
  PTop_not_cocomplete_IEM.

Definition p458_sets_not_cocomplete_above@{e r s o so +| o < so, o < s,
  s <= r +} :
  IEM@{e} → @Cocomplete@{r s o so} Sets@{o so} → False :=
  Sets_not_cocomplete_IEM.

Definition p458_top_not_cocomplete_above@{e r s o h +| o < h, o < s,
  s <= r, h <= r +} :
  IEM@{e} → @Cocomplete@{r s h h} Top@{h o} → False :=
  Top_not_cocomplete_IEM.

(* 相关说明。 （已译） *)

(*
   本节说明 ProbeTopComplete458 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition p458_not_cocomplete_objdeceq_at_set@{r s so +| Set < so,
  Set < s, s <= r +} :
  ObjDecEq PTopCat@{Set so} → @Cocomplete@{r s Set so} PTopCat@{Set so}
  → False :=
  PTop_not_cocomplete_ObjDecEq.

Definition p458_cantor_objdeceq_above_set@{r s o so +| Set < o, o < so,
  o < s, s <= r +} :
  ObjDecEq PTopCat@{o so} → @Cocomplete@{r s o so} PTopCat@{o so} → False :=
  PTop_not_cocomplete_Cantor_ObjDecEq.

(* N28 *)
Fail Definition p458_cantor_objdeceq_at_set@{r s so +| Set < so, Set < s,
  s <= r +} :
  ObjDecEq PTopCat@{Set so} → @Cocomplete@{r s Set so} PTopCat@{Set so}
  → False :=
  PTop_not_cocomplete_Cantor_ObjDecEq.

(*
   本节说明hom、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition p458_top_rebuild_up@{o h1 h2 | o < h1, h1 < h2 +}
  {X Y : TopSpace@{o}} (f : ContinuousMorphism@{h1 o} X Y) :
  ContinuousMorphism@{h2 o} X Y :=
  top_rebuild f.

Definition p458_top_rebuild_unexpanded_at_h@{o h | o < h +}
  {X Y : TopSpace@{o}} (f : ContinuousMorphism@{h o} X Y) :
  ContinuousMorphism@{h o} X Y :=
  {| continuous_map := continuous_map f; continuity := continuity f |}.

(* N29 *)
Fail Definition p458_top_rebuild_unexpanded@{o h1 h2 | o < h1, h1 < h2 +}
  {X Y : TopSpace@{o}} (f : ContinuousMorphism@{h1 o} X Y) :
  ContinuousMorphism@{h2 o} X Y :=
  {| continuous_map := continuous_map f; continuity := continuity f |}.

(* CONTROL: an arrow index of [Top] moves up and down between hom
   universes. *)
Definition p458_top_transport_up@{s o h1 h2 | o < h1, h1 < h2 +}
  (AI : ArrowIndex@{s h1 h1} Top@{h1 o}) : ArrowIndex@{s h2 h2} Top@{h2 o} :=
  Top_ArrowIndex_transport AI.

Definition p458_top_transport_down@{s o h1 h2 | o < h2, h2 < h1 +}
  (AI : ArrowIndex@{s h1 h1} Top@{h1 o}) : ArrowIndex@{s h2 h2} Top@{h2 o} :=
  Top_ArrowIndex_transport AI.

(*
   本节说明 ProbeTopComplete458 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition p458_top_not_complete_below@{e r s h o +| o < s, s < h,
  h <= r +} :
  IEM@{e} → @Complete@{r s h h} Top@{h o} → False :=
  Top_not_complete_below_IEM.

Definition p458_top_not_complete_below_at_set@{r s h +| Set < s, s < h,
  h <= r +} :
  ObjDecEq Top@{h Set} → @Complete@{r s h h} Top@{h Set} → False :=
  Top_not_complete_below_ObjDecEq.

Definition p458_top_not_complete_canonical@{e r s h o +| o < h, h <= s,
  s <= r +} :
  IEM@{e} → @Complete@{r s h h} Top@{h o} → False :=
  Top_not_complete_IEM.

(* N30 *)
Fail Definition p458_top_not_complete_at_points@{e r h o +| o < h,
  h <= r +} :
  IEM@{e} → @Complete@{r o h h} Top@{h o} → False :=
  Top_not_complete_below_IEM@{e r o h o}.

(* N31 *)
Fail Definition p458_top_not_complete_canonical_below@{e r s h o +| o < s,
  s < h, h <= r +} :
  IEM@{e} → @Complete@{r s h h} Top@{h o} → False :=
  Top_not_complete_IEM.

(* 相关说明。 （已译） *)
Definition p458_comphaus_not_complete_below@{e r s c h o +| o < s, s < h,
  h <= c, h <= r +} :
  IEM@{e} → @Complete@{r s h c} (CompHaus : Category@{c h h}) → False :=
  CompHaus_not_complete_below_IEM.

Definition p458_comphaus_not_complete_canonical@{e r s c h o +| o < h,
  h <= s, h <= c, s <= r +} :
  IEM@{e} → @Complete@{r s h c} (CompHaus : Category@{c h h}) → False :=
  CompHaus_not_complete_IEM_below.

(* N32 *)
Fail Definition p458_comphaus_canonical_below@{e r s c h o +| o < s, s < h,
  h <= c, h <= r +} :
  IEM@{e} → @Complete@{r s h c} (CompHaus : Category@{c h h}) → False :=
  CompHaus_not_complete_IEM_below.

(* 相关说明。 （已译） *)
Definition p458_top_iprod_refuted_below@{e s h o +| o < s, s < h +} :
  IEM@{e} → @HasIndexedProducts@{s s s h h h} Top@{h o} → False :=
  Top_iprod_refuted_below_IEM.

(* N33 *)
Fail Definition p458_top_iprod_below_at_points@{e h o +| o < h +} :
  IEM@{e} → @HasIndexedProducts@{o o o h h h} Top@{h o} → False :=
  Top_iprod_refuted_below_IEM@{e o h o}.

(*
   本节说明 ProbeTopComplete458 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition p458_top_not_cocomplete_between@{e r s h o +| o < s, s < h,
  h <= r +} :
  IEM@{e} → @Cocomplete@{r s h h} Top@{h o} → False :=
  Top_not_cocomplete_IEM.

Definition p458_top_not_cocomplete_at_set@{r s h +| Set < s, s < h,
  h <= r +} :
  ObjDecEq Top@{h Set} → @Cocomplete@{r s h h} Top@{h Set} → False :=
  Top_not_cocomplete_ObjDecEq.

Definition p458_top_not_cocomplete_cantor@{e r s h o +| o < s, s < h,
  h <= r +} :
  IEM@{e} → @Cocomplete@{r s h h} Top@{h o} → False :=
  Top_not_cocomplete_Cantor_IEM.

Definition p458_top_cantor_objdeceq_above_set@{r s h o +| Set < o, o < s,
  s < h, h <= r +} :
  ObjDecEq Top@{h o} → @Cocomplete@{r s h h} Top@{h o} → False :=
  Top_not_cocomplete_Cantor_ObjDecEq.

(* N34 *)
Fail Definition p458_top_not_cocomplete_at_points@{e r h o +| o < h,
  h <= r +} :
  IEM@{e} → @Cocomplete@{r o h h} Top@{h o} → False :=
  Top_not_cocomplete_IEM@{e r o h o}.

(* N35 *)
Fail Definition p458_top_cantor_objdeceq_at_set@{r s h +| Set < s, s < h,
  h <= r +} :
  ObjDecEq Top@{h Set} → @Cocomplete@{r s h h} Top@{h Set} → False :=
  Top_not_cocomplete_Cantor_ObjDecEq.

(* * ** Guard: every 常值 six targets （已译） *)

(* Instance/Top/Complete.v *)
Check PBoxTop.
Check PConv.
Check PDisc.
Check PDisc_PForget.
Check Complete.PDisc_obligation_1.
Check Complete.PDisc_obligation_2.
Check Complete.PDisc_obligation_3.
Check PForget_Continuous.
Check PForget_PreservesLimitCone.
Check PInit.
Check PInit_carrier.
Check PInit_one_PSub.
Check PInit_open.
Check PIsTopology.
Check PPair.
Check PPair_carrier.
Check PPair_open_iff_box.
Check PProd.
Check PProd_carrier.
Check PProd_open.
Check PTop_Cartesian.
Check PTop_Complete.
Check PTop_Complete_apex.
Check PTop_Complete_routes_iso.
Check PTop_Complete_routes_iso_legs.
Check PTop_Complete_via_products.
Check PTop_Complete_via_products_apex.
Check PTop_HasIndexedProducts.
Check PTop_IsIndexedProduct.
Check PTop_Limit_lift.
Check PTop_equalizer_open_iff_PSub.
Check PTop_iprod_open_iff_initial.
Check PTop_iprod_ump.
Check Complete.PTop_iprod_ump_obligation_1.
Check Complete.PTop_iprod_ump_obligation_2.
Check PTop_limit_open_iff_initial.
Check PTop_product_obj.
Check box_not_indexed_product.
Check equalizer_points_monic.
Check iprod_points_jointly_monic.
Check pair_box_union.
Check pair_box_union_topology.
Check pbox_all_false.
Check pbox_all_false_not_product_open.
Check pbox_all_false_open.
Check pbox_at.
Check pbox_no_mediator.
Check pbox_open.
Check pbox_open_inter.
Check pbox_open_proper.
Check pbox_open_respects.
Check pbox_open_union.
Check pbox_open_whole.
Check pbox_proj.
Check pbox_proj_cont.
Check pconv_ind.
Check pconv_ind_cont.
Check pconv_ind_map.
Check pconv_ind_mor.
Check pconv_limit_point_not_open.
Check pconv_open.
Check pconv_open_inter.
Check pconv_open_proper.
Check pconv_open_respects.
Check pconv_open_union.
Check pconv_open_whole.
Check pconv_prod_mediator.
Check pconv_setoid.
Check pdisc_forget_iso.
Check Complete.pdisc_forget_iso_obligation_1.
Check Complete.pdisc_forget_iso_obligation_2.
Check Complete.pdisc_forget_iso_obligation_3.
Check Complete.pdisc_forget_iso_obligation_4.
Check pinit_cone.
Check pinit_cone_leg.
Check pinit_cone_limiting.
Check pinit_cone_med_map.
Check pinit_cone_points.
Check pinit_leg.
Check pinit_leg_cont.
Check pinit_leg_map.
Check pinit_lift.
Check pinit_lift_map.
Check pinit_open.
Check pinit_open_inter.
Check pinit_open_proper.
Check pinit_open_respects.
Check pinit_open_union.
Check pinit_open_whole.
Check pinit_sub.
Check pinit_top.
Check pinit_universal.
Check pinit_weakest.
Check plimit_point.
Check plimit_point_cone.
Check plimit_points_jointly_monic.
Check popen_topology.
Check ppair_exl.
Check ppair_exr.
Check ppair_fam.
Check ppair_fork.
Check ppair_fork_map.
Check ppair_fst.
Check ppair_leg.
Check ppair_snd.
Check pprod_leg.
Check pprod_open_pbox_open.
Check pprod_tuple.
Check pproj.
Check pproper.
Check pproper_topology.
Check ptuple.

(* Instance/Top/Complete/ConeComma.v *)
Check ConeImage.
Check ConeImage_obj.
Check Ex3a_left_literal.
Check Ex3a_left_refuting_data.
Check PDiscCone.
Check PDiscCone_open.
Check PInitCone.
Check PInitCone_obj.
Check PTop_Complete_via_cones.
Check PTop_iprod_cone.
Check PTop_iprod_via_cones.
Check PTop_limit_via_cones.
Check PTop_products_via_cone_comma.
Check PTop_via_cones_apex.
Check PTop_via_cones_cone.
Check cone_adjoints_differ_at_empty_shape.
Check ex3_G1.
Check ex3_LeftAdj.
Check ConeComma.ex3_LeftAdj_obligation_1.
Check ConeComma.ex3_LeftAdj_obligation_2.
Check ConeComma.ex3_LeftAdj_obligation_3.
Check ConeComma.ex3_LeftAdj_obligation_4.
Check ex3_T0.
Check ex3_left_adj.
Check ex3_left_adj_iso.
Check ConeComma.ex3_left_adj_iso_obligation_1.
Check ConeComma.ex3_left_adj_iso_obligation_2.
Check ConeComma.ex3_left_adj_iso_obligation_3.
Check ConeComma.ex3_left_adj_iso_obligation_4.
Check ConeComma.ex3_left_adj_iso_obligation_5.
Check ConeComma.ex3_left_adj_iso_obligation_6.
Check ex3_point_cone.
Check ex3_point_limit.
Check ex3_point_terminal.
Check ConeComma.ex3_point_terminal_obligation_1.
Check ConeComma.ex3_point_terminal_obligation_2.
Check ex3_roof_cone.
Check ex3_roof_from_apex.
Check ex3_roof_no_limit.
Check ex3a_left_adjoint_literal_refuted.
Check ex3a_left_counterexample.
Check limit_from_cone_right_adjoint.
Check pbool_cone.
Check pcone_adj_iso.
Check ConeComma.pcone_adj_iso_obligation_1.
Check ConeComma.pcone_adj_iso_obligation_2.
Check ConeComma.pcone_adj_iso_obligation_3.
Check ConeComma.pcone_adj_iso_obligation_4.
Check ConeComma.pcone_adj_iso_obligation_5.
Check ConeComma.pcone_adj_iso_obligation_6.
Check ConeComma.pcone_adj_iso_obligation_7.
Check pcone_adjunction.
Check pdisc_cone.
Check pdisc_cone_adj_iso.
Check ConeComma.pdisc_cone_adj_iso_obligation_1.
Check ConeComma.pdisc_cone_adj_iso_obligation_2.
Check ConeComma.pdisc_cone_adj_iso_obligation_3.
Check ConeComma.pdisc_cone_adj_iso_obligation_4.
Check ConeComma.pdisc_cone_adj_iso_obligation_5.
Check ConeComma.pdisc_cone_adj_iso_obligation_6.
Check pdisc_cone_adjunction.
Check pempty_diagram.
Check puniform_topology.
Check terminal_of_right_adjoint.

(* Instance/Top/Complete/Refutations.v *)
Check CompHaus_not_complete_below_IEM.
Check PTop_ArrowIndex_transport.
Check PTop_iprod_refuted_IEM.
Check PTop_no_ArrowIndex_at_points.
Check PTop_no_ArrowIndex_below.
Check PTop_not_complete_Freyd.
Check PTop_not_complete_IEM.
Check PTop_not_complete_IEM_canonical.
Check PTop_not_complete_ObjDecEq.
Check Top_ArrowIndex_transport.
Check Top_iprod_refuted_IEM_canonical.
Check Top_iprod_refuted_below_IEM.
Check Top_not_complete_below_IEM.
Check Top_not_complete_below_ObjDecEq.
Check pbool_eval_pt.
Check pbool_eval_pt_resp.
Check top_rebuild.

(* Instance/Top/Cocomplete.v *)
Check PColimit.
Check PColimit_apex.
Check PColimit_inj.
Check PColimit_med_at.
Check PColimit_points.
Check PFinal.
Check PFinalCocone.
Check PFinalCocone_legs.
Check Cocomplete.PFinalCocone_obligation_1.
Check PFinalCocone_points.
Check PFinal_carrier.
Check PFinal_open.
Check PForget_Cocontinuous.
Check PForget_PIndisc.
Check PForget_PreservesColimitCocone.
Check PIndisc.
Check PIndisc_fobj.
Check Cocomplete.PIndisc_obligation_1.
Check Cocomplete.PIndisc_obligation_2.
Check Cocomplete.PIndisc_obligation_3.
Check PIndiscrete.
Check PIndiscrete_carrier.
Check PIndiscrete_open.
Check PSigma.
Check PSigma_open.
Check PSigma_points.
Check PTop_Cocomplete.
Check PTop_Cocomplete_routes_iso.
Check PTop_Cocomplete_routes_iso_injs.
Check PTop_Cocomplete_via_coproducts.
Check PTop_Cocomplete_via_coproducts_apex.
Check PTop_Colimit_lift.
Check PTop_Colimit_lift_apex.
Check PTop_HasIndexedCoproducts.
Check PTop_IsIndexedCoproduct.
Check PTop_colimit_open_iff_final.
Check PTwoIndisc.
Check PTwoIndiscSum.
Check PTwoIndiscSum_injections_differ.
Check PTwoIndiscSum_not_discrete.
Check PTwoIndiscSum_not_indiscrete.
Check PTwoIndiscSum_summand_open.
Check pfinal_cocone_colimiting.
Check pfinal_cocone_colimiting_reflect.
Check pfinal_cocone_inj.
Check pfinal_cocone_med_map.
Check pfinal_cocone_obj.
Check pfinal_desc.
Check pfinal_desc_map.
Check pfinal_finest.
Check pfinal_leg.
Check pfinal_leg_cont.
Check pfinal_leg_map.
Check pfinal_one_map_PQuot.
Check pfinal_open.
Check pfinal_open_inter.
Check pfinal_open_proper.
Check pfinal_open_respects.
Check pfinal_open_union.
Check pfinal_open_whole.
Check pfinal_universal.
Check pforget_indisc_iso.
Check Cocomplete.pforget_indisc_iso_obligation_1.
Check Cocomplete.pforget_indisc_iso_obligation_2.
Check Cocomplete.pforget_indisc_iso_obligation_3.
Check pindisc_cont.
Check pindisc_mor.
Check pindisc_mor_map.
Check pindisc_open.
Check pindisc_open_inter.
Check pindisc_open_proper.
Check pindisc_open_respects.
Check pindisc_open_union.
Check pindisc_open_whole.
Check psigma_case.
Check psigma_case_at.
Check psigma_desc.
Check psigma_inj.

(* Instance/Top/Cocomplete/Refutations.v *)
Check PTop_not_cocomplete_Cantor_IEM.
Check PTop_not_cocomplete_Cantor_ObjDecEq.
Check PTop_not_cocomplete_Freyd.
Check PTop_not_cocomplete_IEM.
Check PTop_not_cocomplete_ObjDecEq.
Check Sets_not_cocomplete_IEM.
Check Top_not_cocomplete_Cantor_IEM.
Check Top_not_cocomplete_Cantor_ObjDecEq.
Check Top_not_cocomplete_Freyd.
Check Top_not_cocomplete_IEM.
Check Top_not_cocomplete_ObjDecEq.
Check cocomp_cantor_diagonal.
Check pcc_Prop.
Check Refutations.pcc_Prop_obligation_1.
Check pcc_contradiction.
Check pcc_enc.
Check pcc_enc_inj.
Check pcc_index.
Check pcc_inj.
Check pcc_leg.
Check pcc_sep.
Check pcc_sep_at.
Check pcc_sum.
Check tcc_contradiction.
Check tcc_enc.
Check tcc_enc_inj.
Check tcc_index.
Check tcc_inj.
Check tcc_leg.
Check tcc_sep.
Check tcc_sep_at.
Check tcc_sum.

(* Instance/Top/Cocomplete/TypeValued.v *)
Check TSigma.
Check TSigma_carrier.
Check TSigma_open.
Check Top_HasCoequalizers.
Check Top_HasIndexedCoproducts_small.
Check Top_coequalizer_obj.
Check tcoeq_IsCoequalizer.
Check tcoeq_cofork.
Check tcoeq_desc.
Check tcoeq_med.
Check tcoeq_obj.
Check tcoeq_proj.
Check tsig_case.
Check tsig_case_cont.
Check tsig_desc.
Check tsig_inj.
Check tsig_open.
Check tsig_open_inter.
Check tsig_open_proper.
Check tsig_open_respects.
Check tsig_open_union.
Check tsig_open_whole.
Check tsig_setoid.
