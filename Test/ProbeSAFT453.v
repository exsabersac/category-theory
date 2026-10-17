(*
   本文件为测试：ProbeSAFT453。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

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
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Span.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Roof.
Require Import Category.Adjunction.GAFT.
Require Import Category.Functor.Representable.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Fun.
Require Import Category.Adjunction.Representability.Sets.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Functor.Hom.Limit.
Require Import Category.Instance.Discrete.Reconstruct.
Require Import Category.Instance.Adjoints.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Sets.WellPowered.
Require Import Category.Instance.Sets.Cogenerator.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Powerset.WellPowered.
Require Import Category.Adjunction.GAFT.Sets.
Require Import Category.Adjunction.SAFT.Sets.
Require Import Category.Adjunction.SAFT.WellPowered.
Require Import Category.Adjunction.SAFT.InitialObject.Examples.
Require Import Category.Adjunction.SAFT.Characterization.
Require Import Category.Adjunction.SAFT.Characterization.Cover.
Require Import Category.Adjunction.SAFT.Characterization.Corollaries.
Require Import Category.Adjunction.SAFT.Characterization.Examples.

Generalizable All Variables.

(* 相关说明。 （已译） *)

Fail Check probe453_absent_name.

(* 相关说明。 （已译） *)

(* CONTROL: [SAFT_left_obj], restated. *)
Example p453_left_obj@{o dobj h so c w s t pk pa +|
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

(* 相关说明。 （已译） *)
Example p453_iff_left_obj@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) (d : D) :
  fobj[`1 (snd (SAFT_wellpowered_iff U comp G WP) cont)] d
    = snd (`1 (Subobject.sub_dom
        (complete_intersection (Comma_Complete cont comp)
           (wp_class_family
              (comma_WellPoweredAt U d (complete_pullbacks comp)
                 (cogen_prod (Comma_Complete cont comp)
                    (comma_cogenerator U d G))
                 (WP _))
              (fun _ => True))))) :=
  eq_refl.

Fail Example p453_n1_obj_is_product@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) (d : D) :
  fobj[`1 (SAFT_wellpowered U comp cont G WP)] d
    = snd (`1 (cogen_prod (Comma_Complete cont comp)
                 (comma_cogenerator U d G))) :=
  eq_refl.

Fail Example p453_n2_obj_empty_class@{o dobj h so c w s t pk pa +|
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
              (fun _ => False))))) :=
  eq_refl.

(* CONTROL: [SAFT_thm2_left_obj], restated. *)
Example p453_thm2_left_obj@{o dobj h so c pk pa q r rd pw k +|
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
Example p453_iff_thm2_obj@{o dobj h so c pk pa q r rd pw k +|
    h <= so, c <= so, o <= q, h <= q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) (d : D) :
  fobj[`1 (snd (SAFT_iff U comp G HW) (cont, HU))] d
    = WPull (HW (snd (`1 (cogen_prod (Comma_Complete cont comp)
                              (comma_cogenerator U d G))))
                (least_index U d
                   (cogen_prod (Comma_Complete cont comp)
                      (comma_cogenerator U d G)))
                (fun k => `1 k)) :=
  eq_refl.

Fail Example p453_n3_thm2_obj_is_product@{o dobj h so c pk pa q r rd pw k +|
    h <= so, c <= so, o <= q, h <= q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) (d : D) :
  fobj[`1 (SAFT_thm2 U comp cont G HW HU)] d
    = snd (`1 (cogen_prod (Comma_Complete cont comp)
                 (comma_cogenerator U d G))) :=
  eq_refl.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition p453_gaft_route@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  { F : D ⟶ C & F ⊣ U } :=
  GAFT_from_initials U (SAFT_comma_initial U comp cont G WP).

(* ... and for Theorem 2. *)
Definition p453_thm2_gaft_route@{o dobj h so c pk pa q r rd pw k +|
    h <= so, c <= so, o <= q, h <= q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) :
  { F : D ⟶ C & F ⊣ U } :=
  GAFT_from_initials U (SAFT_thm2_initial U comp cont G HW HU).

Fail Example p453_n4_gaft_route_obj@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) (d : D) :
  fobj[`1 (p453_gaft_route U comp cont G WP)] d
    = snd (`1 (Subobject.sub_dom
        (complete_intersection (Comma_Complete cont comp)
           (wp_class_family
              (comma_WellPoweredAt U d (complete_pullbacks comp)
                 (cogen_prod (Comma_Complete cont comp)
                    (comma_cogenerator U d G))
                 (WP _))
              (fun _ => True))))) :=
  eq_refl.

Fail Example p453_n5_thm2_gaft_route_obj@{o dobj h so c pk pa q r rd pw k +|
    h <= so, c <= so, o <= q, h <= q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) (d : D) :
  fobj[`1 (p453_thm2_gaft_route U comp cont G HW HU)] d
    = WPull (HW (snd (`1 (cogen_prod (Comma_Complete cont comp)
                              (comma_cogenerator U d G))))
                (least_index U d
                   (cogen_prod (Comma_Complete cont comp)
                      (comma_cogenerator U d G)))
                (fun k => `1 k)) :=
  eq_refl.

(* 相关说明。 （已译） *)

(* CONTROL: [SAFT_cover_wp_is_GAFT], restated. *)
Example p453_cover_is_gaft@{o dobj h dp cp w s t pl pa +|
    h < dp, h < cp, w <= h +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl h pa h} C D U)
  (G : Cogenerator@{h o h} C) (WP : WellPowered@{o h w s t} C) :
  SAFT_cover_wp@{o dobj h dp cp w s t pl pa _ _ _} U comp cont G WP
    = GAFT U comp cont
        (fun d => saft_solution_set_at@{o dobj h h dp cp w s t pl pa h _ _ _}
                    U comp cont G d
                    (WP (saft_prod@{o dobj h h dp} U comp G d))) :=
  eq_refl.

(* 相关说明。 （已译） *)
Definition p453_cover_iso@{o dobj h dp cp w s t pl pa +|
    h < dp, h < cp, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl h pa h} C D U)
  (G : Cogenerator@{h o h} C) (WP : WellPowered@{o h w s t} C) :
  projT1 (SAFT_cover_wp@{o dobj h dp cp w s t pl pa _ _ _} U comp cont G WP)
    ≈ projT1 (SAFT_wellpowered U comp cont G WP) :=
  SAFT_cover_wp_iso U comp cont G WP.

Fail Example p453_n6_routes_convertible@{o dobj h dp cp w s t pl pa +|
    h < dp, h < cp, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl h pa h} C D U)
  (G : Cogenerator@{h o h} C) (WP : WellPowered@{o h w s t} C) :
  projT1 (SAFT_cover_wp@{o dobj h dp cp w s t pl pa _ _ _} U comp cont G WP)
    = projT1 (SAFT_wellpowered U comp cont G WP) :=
  eq_refl.

(* 相关说明。 （已译） *)
Example p453_same_index@{o dobj h so +| h <= so +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D) (d : D)
  (G : Cogenerator@{so o h} C) :
  cog_index (comma_cogenerator U d G) = saft_index U G d :=
  eq_refl.

Fail Example p453_n7_same_product@{o dobj h so dp pk pa +|
    h <= so, h < dp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D) (d : D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{so o h} C) :
  snd (`1 (cogen_prod (Comma_Complete cont comp) (comma_cogenerator U d G)))
    = saft_prod@{o dobj h so dp} U comp G d :=
  eq_refl.

(* 相关说明。 （已译） *)

(* CONTROL: Corollary homs strictly below shapes the
 shapes strictly below 对象. （已译） *)
Definition p453_small@{o dobj h so c w s t pk pa +|
    h < so, so < o, c < so, w < h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_wellpowered U comp cont G WP.

(* CONTROL: its biconditional at the same universes. *)
Definition p453_small_iff@{o dobj h so c w s t pk pa +|
    h < so, so < o, c < so, w < h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  { F : D ⟶ C & F ⊣ U }
    ↔ @PreservesImageLimit@{o h dobj h pk so pa so} C D U :=
  SAFT_wellpowered_iff U comp G WP.

(* CONTROL: [WellPowered]'s [t] and [PreservesImageLimit]'s auxiliary
   [pa] apart, in both orders. *)
Definition p453_t_below_pa@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, t < pa +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_wellpowered U comp cont G WP.

Definition p453_pa_below_t@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, pa < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_wellpowered U comp cont G WP.

(* INSTRUMENT: binder's constraints enforced. [Complete@{so so h
 o}] declares [h] at below first slot, so 这是 refused
 whatever body. （已译） *)
Fail Definition p453_n8_shapes_below_homs@{o dobj h so c w s t pk pa +|
    so < h, c < so, w < h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_wellpowered U comp cont G WP.

(* CONTROL: Theorem 2 at same regime, class index strictly above
 对象. （已译） *)
Definition p453_thm2_small@{o dobj h so c pk pa q r rd pw k +|
    h < so, so < o, c < so, o < q, h < q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_thm2 U comp cont G HW HU.

(* CONTROL: its biconditional at the same universes. *)
Definition p453_thm2_small_iff@{o dobj h so c pk pa q r rd pw k +|
    h < so, so < o, c < so, o < q, h < q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C) :
  { F : D ⟶ C & F ⊣ U }
    ↔ (@PreservesImageLimit@{o h dobj h pk so pa so} C D U
       * PreservesWidePullbacks@{o h dobj h pw q r rd} U) :=
  SAFT_iff U comp G HW.

(* 相关说明。 （已译） *)
Definition p453_thm2_q_below_r@{o dobj h so c pk pa q r rd pw k +|
    h <= so, c <= so, o <= q, h <= q, q < r, q < rd +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_thm2 U comp cont G HW HU.

Fail Definition p453_n9_class_index_small@{o dobj h so c pk pa q r rd pw k +|
    h < so, so < o, c < so, q < o, h < q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_thm2 U comp cont G HW HU.

(* CONTROL: [HU]'s C-side wide-pullback universe [r2] declared at or
   above [HW]'s [r]. *)
Definition p453_thm2_r_le@{o dobj h so c pk pa q r r2 rd pw k +|
    h <= so, c <= so, o <= q, h <= q, r <= r2 +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r2 rd} U) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_thm2 U comp cont G HW HU.

Fail Definition p453_n10_thm2_r_apart@{o dobj h so c pk pa q r r2 rd pw k +|
    h <= so, c <= so, o <= q, h <= q, r < r2 +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r2 rd} U) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_thm2 U comp cont G HW HU.

(* CONTROL: N26's term, [HW] applied corresponding family
 [least_index] comma's cogenerator product, class index at or
 above 对象. （已译） *)
Definition p453_least_index_at_objects@{o dobj h so c pk pa q r k +|
    h < so, so < o, c < so, o <= q, h < q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C) (d : D) :=
  HW (snd (`1 (cogen_prod (Comma_Complete cont comp)
                 (comma_cogenerator U d G))))
     (least_index U d (cogen_prod (Comma_Complete cont comp)
                         (comma_cogenerator U d G)))
     (fun k => `1 k).

Fail Definition p453_n26_least_index_small@{o dobj h so c pk pa q r k +|
    h < so, so < o, c < so, q < o, h < q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C) (d : D) :=
  HW (snd (`1 (cogen_prod (Comma_Complete cont comp)
                 (comma_cogenerator U d G))))
     (least_index U d (cogen_prod (Comma_Complete cont comp)
                         (comma_cogenerator U d G)))
     (fun k => `1 k).

(* CONTROL: [SAFT_thm2_initial]'s body, [HU]'s C-side wide-pullback
   universe [r2] declared at or above [HW]'s [r]. *)
Definition p453_thm2_initial_r_le@{o dobj h so c pk pa q r r2 rd pw k +|
    h <= so, c <= so, o <= q, h <= q, r <= r2 +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r2 rd} U) (d : D) :
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

Fail Definition p453_n27_initial_r_apart@{o dobj h so c pk pa q r r2 rd pw k +|
    h <= so, c <= so, o <= q, h <= q, r < r2 +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r2 rd} U) (d : D) :
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

(* 相关说明。 （已译） *)

(* CONTROL: at [Sets] unconditional well-powering one universe up
 small cogenerating family taken 假设, cover is
 accepted ... （已译） *)
Definition p453_cover_up@{o so +| o < so +} (d : Sets@{o so})
  (G : Cogenerator@{o so o} Sets@{o so}) :=
  saft_cover_at (@Id Sets@{o so}) Sets_Complete Sets_Id_PreservesImageLimit G d
    (Sets_WellPoweredAt_up _).

(* 相关说明。 （已译） *)
Definition p453_solution_set_up@{o so +| o < so +} (d : Sets@{o so})
  (G : Cogenerator@{o so o} Sets@{o so}) :=
  saft_solution_set_at (@Id Sets@{o so}) Sets_Complete
    Sets_Id_PreservesImageLimit G d (Sets_WellPoweredAt_up _).

(* CONTROL: other unconditional well-powering [Sets@{o so}],
 Structure/WellPowered.v's [wp_trivial], indexed at 对象' [so],
 strictly above homs [o] ... （已译） *)
Definition p453_sets_wp_trivial@{o so +| o < so +} (d : Sets@{o so}) :
  WellPoweredAt@{so so so o so} d :=
  wp_trivial d.

(* ... and the cover accepts it too. *)
Definition p453_sets_cover_trivial@{o so +| o < so +} (d : Sets@{o so})
  (G : Cogenerator@{o so o} Sets@{o so}) :=
  saft_cover_at (@Id Sets@{o so}) Sets_Complete Sets_Id_PreservesImageLimit G d
    (wp_trivial _).

Fail Definition p453_n11_cover_wp_at_up@{o so +| o < so +}
  (G : Cogenerator@{o so o} Sets@{o so}) :
  { F : Sets@{o so} ⟶ Sets@{o so} & F ⊣ Id } :=
  SAFT_cover_wp_at (@Id Sets@{o so}) Sets_Complete Sets_Id_PreservesImageLimit G
    (fun d => Sets_WellPoweredAt_up _).

Fail Definition p453_n12_gaft_at_up@{o so +| o < so +}
  (G : Cogenerator@{o so o} Sets@{o so}) :
  { F : Sets@{o so} ⟶ Sets@{o so} & F ⊣ Id } :=
  GAFT (@Id Sets@{o so}) Sets_Complete Sets_Id_PreservesImageLimit
    (fun d => saft_solution_set_at (@Id Sets@{o so}) Sets_Complete
                Sets_Id_PreservesImageLimit G d (Sets_WellPoweredAt_up _)).

(* CONTROL: the well-powering one universe up, per object. *)
Definition p453_wp_up_at@{o so +| o < so +} (x : Sets@{o so}) :=
  Sets_WellPoweredAt_up x.

Fail Definition p453_n13_wp_up@{o so +| o < so +} : WellPowered Sets@{o so} :=
  fun x => Sets_WellPoweredAt_up x.

(* 相关说明。 （已译） *)
Definition p453_sets_id@{o so +| Set < o, o < so +} (Un : Untruncate@{o}) :
  { F : Sets@{o so} ⟶ Sets@{o so} & F ⊣ @Id Sets@{o so} } :=
  SAFT_wellpowered (@Id Sets@{o so}) Sets_Complete Sets_Id_PreservesImageLimit
    (Sets_Cogenerator_untruncate Un) (Sets_WellPowered_untruncate Un).

Definition p453_sets_id_cover@{o so +| Set < o, o < so +}
  (Un : Untruncate@{o}) :
  { F : Sets@{o so} ⟶ Sets@{o so} & F ⊣ @Id Sets@{o so} } :=
  SAFT_cover_wp (@Id Sets@{o so}) Sets_Complete Sets_Id_PreservesImageLimit
    (Sets_Cogenerator_untruncate Un) (Sets_WellPowered_untruncate Un).

(*
   本节说明 ProbeSAFT453 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition p453_cover_trivial@{o dobj h so dp cp w s t pl pa +|
    h <= so, h < dp, h < cp, o <= w, h <= w, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D) :=
  saft_cover_at U comp cont G d
    (wp_trivial@{o h w s t} (saft_prod U comp G d)).

(* CONTROL: [GAFT]'s pin takes [wp_trivial] 对象 fit the
 homs. （已译） *)
Definition p453_cover_wp_trivial_small@{o dobj h dp cp s t pl pa +|
    o <= h, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl h pa h} C D U)
  (G : Cogenerator@{h o h} C) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_cover_wp_at U comp cont G (fun d => wp_trivial (saft_prod U comp G d)).

Fail Definition p453_n14_cover_wp_trivial_large@{o dobj h dp cp s t pl pa +|
    h < o, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl h pa h} C D U)
  (G : Cogenerator@{h o h} C) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_cover_wp_at U comp cont G (fun d => wp_trivial (saft_prod U comp G d)).

(* CONTROL: N28's term, [GAFT] applied directly solution sets built
 [wp_trivial], 对象 fit homs. （已译） *)
Definition p453_gaft_trivial_small@{o dobj h dp cp pl pa +|
    o <= h, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl h pa h} C D U)
  (G : Cogenerator@{h o h} C) :
  { F : D ⟶ C & F ⊣ U } :=
  GAFT U comp cont
    (fun d => saft_solution_set_at U comp cont G d
                (wp_trivial (saft_prod U comp G d))).

Fail Definition p453_n28_gaft_trivial_large@{o dobj h dp cp pl pa +|
    h < o, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl h pa h} C D U)
  (G : Cogenerator@{h o h} C) :
  { F : D ⟶ C & F ⊣ U } :=
  GAFT U comp cont
    (fun d => saft_solution_set_at U comp cont G d
                (wp_trivial (saft_prod U comp G d))).

(* 相关说明。 （已译） *)

(* CONTROL: the family itself. *)
Definition p453_large_cog@{c o so +| o < so, o < c +} :
  Cogenerator@{c so o} Sets@{o so} :=
  Sets_Cogenerator_large@{c o so}.

(* CONTROL: the Corollary takes it over a completeness datum whose shape
   universe is the family's index universe, a hypothetical datum taken as
   a variable ([Sets_Complete] is [Complete@{o o o so}]).（标题）（已译） *)
Definition p453_large_cog_abstract@{c o so w s t pk pa +|
    o < so, o < c, w <= o, so <= s, o <= s, o < t +}
  (comp : @Complete@{c c o so} Sets@{o so})
  (cont : @PreservesImageLimit@{so o so o pk c pa c} Sets@{o so} Sets@{o so}
            (@Id Sets@{o so}))
  (WP : WellPowered@{so o w s t} Sets@{o so}) :
  { F : Sets@{o so} ⟶ Sets@{o so} & F ⊣ @Id Sets@{o so} } :=
  SAFT_wellpowered (@Id Sets@{o so}) comp cont Sets_Cogenerator_large@{c o so}
    WP.

Fail Definition p453_n15_large_cog_cover@{o so +| Set < o, o < so +}
  (Un : Untruncate@{o}) :
  { F : Sets@{o so} ⟶ Sets@{o so} & F ⊣ Id } :=
  SAFT_cover_wp (@Id Sets@{o so}) Sets_Complete Sets_Id_PreservesImageLimit
    Sets_Cogenerator_large (Sets_WellPowered_untruncate Un).

Fail Definition p453_n16_large_cog_comma@{o so +| Set < o, o < so +}
  (Un : Untruncate@{o}) :
  { F : Sets@{o so} ⟶ Sets@{o so} & F ⊣ Id } :=
  SAFT_wellpowered (@Id Sets@{o so}) Sets_Complete Sets_Id_PreservesImageLimit
    Sets_Cogenerator_large (Sets_WellPowered_untruncate Un).

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition p453_unannotated {C D : Category} (U : C ⟶ D)
  (comp : @Complete C) (cont : @PreservesImageLimit C D U)
  (G : Cogenerator C) (WP : WellPowered C) : { F : D ⟶ C & F ⊣ U } :=
  SAFT_wellpowered U comp cont G WP.

(* CONTROL: library 常值 takes index at [Set], strictly below
 homs ([indiscrete_saft], restated). （已译） *)
Definition p453_indiscrete_set_index@{j o +| j < o +} :
  { F : Indiscrete@{o j j} Type@{j} ⟶ Indiscrete@{o j j} Type@{j}
    & F ⊣ @Id (Indiscrete@{o j j} Type@{j}) } :=
  SAFT_wellpowered (@Id (Indiscrete@{o j j} Type@{j}))
    (Indiscrete_Complete (Datatypes.unit : Type@{j}))
    (right_adjoint_PreservesImageLimit (@adj_id (Indiscrete@{o j j} Type@{j})))
    (Indiscrete_Cogenerator_empty Type@{j})
    (Indiscrete_WellPowered@{o j Set o _} Type@{j}).

(* 相关说明。 （已译） *)
Definition p453_unannotated_hom_index@{j o +| j < o +} :
  { F : Indiscrete@{o j j} Type@{j} ⟶ Indiscrete@{o j j} Type@{j}
    & F ⊣ @Id (Indiscrete@{o j j} Type@{j}) } :=
  p453_unannotated (@Id (Indiscrete@{o j j} Type@{j}))
    (Indiscrete_Complete (Datatypes.unit : Type@{j}))
    (right_adjoint_PreservesImageLimit (@adj_id (Indiscrete@{o j j} Type@{j})))
    (Indiscrete_Cogenerator_empty Type@{j})
    (Indiscrete_WellPowered@{o j j o _} Type@{j}).

Fail Definition p453_n17_unannotated_set_index@{j o +| j < o +} :
  { F : Indiscrete@{o j j} Type@{j} ⟶ Indiscrete@{o j j} Type@{j}
    & F ⊣ @Id (Indiscrete@{o j j} Type@{j}) } :=
  p453_unannotated (@Id (Indiscrete@{o j j} Type@{j}))
    (Indiscrete_Complete (Datatypes.unit : Type@{j}))
    (right_adjoint_PreservesImageLimit (@adj_id (Indiscrete@{o j j} Type@{j})))
    (Indiscrete_Cogenerator_empty Type@{j})
    (Indiscrete_WellPowered@{o j Set o _} Type@{j}).

(* 相关说明。 （已译） *)

(* CONTROL: [saft_lift]'s body, the cone at [pa]. *)
Definition p453_lift_at_pa@{o dobj h so dp cp pl pa +|
    h <= so, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D) (c : C) (h : d ~> U c) :
  d ~> U (Subobject.sub_dom
           (saft_sub@{o dobj h so dp cp _ _} U comp G d c h)) :=
  unique_obj (cont _ _ _ (saft_pb_cone@{o dobj h so dp cp pl pa so pa _}
                            U comp cont G d c h)).

Fail Definition p453_n18_lift_at_pc@{o dobj h so dp cp pl pa pc +|
    h <= so, h < dp, h < cp, h < pc, pa < pc +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D) (c : C) (h : d ~> U c) :
  d ~> U (Subobject.sub_dom
           (saft_sub@{o dobj h so dp cp _ _} U comp G d c h)) :=
  unique_obj (cont _ _ _ (saft_pb_cone@{o dobj h so dp cp pl pa so pc _}
                            U comp cont G d c h)).

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition p453_diag_small@{o h so c w s t jo +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, jo <= h +}
  (C : Category@{o h h}) (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C)
  (J : Category@{jo h h}) :=
  SAFT_wellpowered (@Diagonal C J) comp
    (Continuous_PreservesImageLimit Diagonal_continuous) G WP.

(* 相关说明。 （已译） *)
Definition p453_diag_alone@{o h jo +| h < jo +}
  (C : Category@{o h h}) (J : Category@{jo h h}) :=
  @Diagonal C J.

Fail Definition p453_n19_diag_large@{o h so c w s t jo +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, h < jo +}
  (C : Category@{o h h}) (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C)
  (J : Category@{jo h h}) :=
  SAFT_wellpowered (@Diagonal C J) comp
    (Continuous_PreservesImageLimit Diagonal_continuous) G WP.

(* 相关说明。 （已译） *)
Definition p453_cocomplete_cr_le@{o h so c w s t jo fo fa cr +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, jo <= h,
    o <= fo, h <= fo, h < fa, h <= cr, jo <= cr +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  @Cocomplete@{cr jo h o} C :=
  fun J F => Diagonal_left_adjoint_HasColimits
               (projT2 (saft_colim C comp G WP J
                        : { L : @Fun@{jo h o h fo h fa} J C ⟶ C
                          & L ⊣ @Diagonal@{fo h fa jo o h} C J })) F.

Fail Definition p453_n20_cocomplete_cr_above@{o h so c w s t jo fo fa cr +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, jo <= h,
    o <= fo, h <= fo, h < fa, h < cr, jo <= cr +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  @Cocomplete@{cr jo h o} C :=
  fun J F => Diagonal_left_adjoint_HasColimits
               (projT2 (saft_colim C comp G WP J
                        : { L : @Fun@{jo h o h fo h fa} J C ⟶ C
                          & L ⊣ @Diagonal@{fo h fa jo o h} C J })) F.

(* CONTROL: representability 推论 [PreservesImageLimit]'s
 auxiliary [pa] strictly below 对象 [su] [Sets@{h su}]. （已译） *)
Definition p453_repr_pa_below_su@{o h so c w s t su pl pa ra rt +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, h < su, pa < su +}
  {C : Category@{o h h}} (K : C ⟶ Sets@{h su})
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h su h pl so pa so} C Sets@{h su} K)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  Representable@{ra rt su o h} K :=
  continuous_Set_functor_representable K comp cont G WP.

(* CONTROL: its biconditional with [pa] declared at or below [su]. *)
Definition p453_repr_iff_pa_le_su@{o h so c w s t su pl pa ra rt +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, h < su, pa <= su +}
  {C : Category@{o h h}} (K : C ⟶ Sets@{h su})
  (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  Representable@{ra rt su o h} K
    ↔ @PreservesImageLimit@{o h su h pl so pa so} C Sets@{h su} K :=
  continuous_Set_functor_representable_iff K comp G WP.

Fail Definition p453_n21_repr_iff_pa_below_su@{o h so c w s t su pl pa ra rt +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, h < su, pa < su +}
  {C : Category@{o h h}} (K : C ⟶ Sets@{h su})
  (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  Representable@{ra rt su o h} K
    ↔ @PreservesImageLimit@{o h su h pl so pa so} C Sets@{h su} K :=
  continuous_Set_functor_representable_iff K comp G WP.

(* 相关说明。 （已译） *)

(* CONTROL: completeness supplies them index at shapes, the
 对象 at below shapes. （已译） *)
Definition p453_hw_at_shapes@{o h so k +| h <= so, o <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C) :
  HasSubobjectWidePullbacks@{o h so so k} C :=
  fun x I S => complete_wide_pullback comp (fun i => Subobject.sub_mono (S i)).

(* CONTROL: index at 对象, they fit. （已译） *)
Definition p453_hw_at_objects@{o h so k +| h <= so, o <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C) :
  HasSubobjectWidePullbacks@{o h o o k} C :=
  fun x I S => complete_wide_pullback comp (fun i => Subobject.sub_mono (S i)).

(* CONTROL: Adjunction/SAFT/Characterization.v's
 [Complete_HasSubobjectWidePullbacks], at index at 对象, IS
 term. （已译） *)
Example p453_hw_is_library@{o h so k +| h <= so, o <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C) :
  (Complete_HasSubobjectWidePullbacks comp
     : HasSubobjectWidePullbacks@{o h o o k} C)
    = p453_hw_at_objects comp :=
  eq_refl.

Fail Definition p453_n22_hw_large@{o h so k +| h <= so, so < o +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C) :
  HasSubobjectWidePullbacks@{o h o o k} C :=
  fun x I S => complete_wide_pullback comp (fun i => Subobject.sub_mono (S i)).

(* CONTROL: N23's term, family's index explicit, at 对象'
 universe, 对象 fit shapes. （已译） *)
Definition p453_hw_index_ok@{o h so +| h <= so, o <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C) (x : C)
  (I : Type@{o}) (S : I → SubObj x) :=
  @complete_wide_pullback C comp I (fun i => Subobject.sub_dom (S i)) x
    (fun i => Subobject.sub_mono (S i)).

Fail Definition p453_n23_hw_large_index@{o h so +| h <= so, so < o +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C) (x : C)
  (I : Type@{o}) (S : I → SubObj x) :=
  @complete_wide_pullback C comp I (fun i => Subobject.sub_dom (S i)) x
    (fun i => Subobject.sub_mono (S i)).

(* 相关说明。 （已译） *)
Definition p453_sets_hw_small@{o so k +| Set < o, o < so +} :
  HasSubobjectWidePullbacks@{so o o o k} Sets@{o so} :=
  fun x I S => complete_wide_pullback Sets_Complete
                 (fun i => Subobject.sub_mono (S i)).

(* CONTROL: library 常值 there, index at homs. （已译） *)
Definition p453_sets_hw_library@{o so k +| Set < o, o < so +} :
  HasSubobjectWidePullbacks@{so o o o k} Sets@{o so} :=
  Complete_HasSubobjectWidePullbacks Sets_Complete.

Fail Definition p453_n24_sets_hw_large@{o so k +| Set < o, o < so +} :
  HasSubobjectWidePullbacks@{so o so so k} Sets@{o so} :=
  fun x I S => complete_wide_pullback Sets_Complete
                 (fun i => Subobject.sub_mono (S i)).

(* 相关说明。 （已译） *)
Definition p453_thm2_subsets@{o u so k +| o <= u, u <= so, o <= so +}
  {X Y : SetoidObject@{o o}} (f : X ~{Sets}~> Y) :
  { F : Subsets@{o u} X ⟶ Subsets@{o u} Y & F ⊣ InverseImage f } :=
  SAFT_thm2 (InverseImage f) (Subsets_Complete_free Y)
    (right_adjoint_PreservesImageLimit (image_preimage_adjunction f))
    (Subsets_Cogenerator_empty Y)
    (p453_hw_at_shapes (Subsets_Complete_free Y))
    (right_adjoint_PreservesWidePullbacks (image_preimage_adjunction f)).

(* CONTROL: Adjunction/SAFT/Characterization/Examples.v's
   [subsets_inverse_image_thm2] IS that assembly. *)
Example p453_thm2_subsets_is_library@{o so u +| Set < o, o < so, o <= u +}
  {X Y : SetoidObject@{o o}} (f : X ~{Sets@{o so}}~> Y) :
  subsets_inverse_image_thm2 f
    = (p453_thm2_subsets f
       : { F : Subsets@{o u} X ⟶ Subsets@{o u} Y & F ⊣ InverseImage f }) :=
  eq_refl.

(* 相关说明。 （已译） *)

Require Import Category.Instance.Sets.SpecialInitial.

(* CONTROL: the cover is accepted there. *)
Definition p453_setsop_cover_up@{o so +| o < so +}
  (d : (Sets@{o so}^op)%category) :=
  saft_cover_at (@Id ((Sets@{o so}^op)%category)) setsop_comp
    (right_adjoint_PreservesImageLimit (@adj_id ((Sets@{o so}^op)%category)))
    setsop_cog d (Sets_CoWellPoweredAt_up _).

Fail Definition p453_n25_setsop_cover_wp_at_up@{o so +| o < so +} :
  { F : (Sets@{o so}^op)%category ⟶ (Sets@{o so}^op)%category & F ⊣ Id } :=
  SAFT_cover_wp_at (@Id ((Sets@{o so}^op)%category)) setsop_comp
    (right_adjoint_PreservesImageLimit (@adj_id ((Sets@{o so}^op)%category)))
    setsop_cog (fun d => Sets_CoWellPoweredAt_up _).

(* CONTROL: N29's solution set, not handed to [GAFT]. *)
Definition p453_setsop_solution_set_up@{o so +| o < so +}
  (d : (Sets@{o so}^op)%category) :=
  saft_solution_set_at (@Id ((Sets@{o so}^op)%category)) setsop_comp
    (right_adjoint_PreservesImageLimit (@adj_id ((Sets@{o so}^op)%category)))
    setsop_cog d (Sets_CoWellPoweredAt_up _).

Fail Definition p453_n29_setsop_gaft_up@{o so +| o < so +} :
  { F : (Sets@{o so}^op)%category ⟶ (Sets@{o so}^op)%category & F ⊣ Id } :=
  GAFT (@Id ((Sets@{o so}^op)%category)) setsop_comp
    (right_adjoint_PreservesImageLimit (@adj_id ((Sets@{o so}^op)%category)))
    (fun d =>
       saft_solution_set_at (@Id ((Sets@{o so}^op)%category)) setsop_comp
         (right_adjoint_PreservesImageLimit
            (@adj_id ((Sets@{o so}^op)%category)))
         setsop_cog d (Sets_CoWellPoweredAt_up _)).

(** ** Controls without a negative *)

(* The 表示 对象 左伴随 at singleton
 ([continuous_Set_functor_representable_obj], restated). （已译） *)
Example p453_repr_obj@{o h so c w s t su pl pa ra rt +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, h < su +}
  {C : Category@{o h h}} (K : C ⟶ Sets@{h su})
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h su h pl so pa so} C Sets@{h su} K)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  @repr_obj C K
    (continuous_Set_functor_representable K comp cont G WP
       : Representable@{ra rt su o h} K)
    = fobj[projT1 (SAFT_wellpowered K comp cont G WP)] SetsOne :=
  eq_refl.

(* 相关说明。 （已译） *)
Example p453_cover_index@{o dobj h so dp cp w s t pl pa +|
    h <= so, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D)
  (W : WellPoweredAt@{w o s h t} (saft_prod@{o dobj h so dp} U comp G d))
  (c : C) (h : d ~> U c) :
  projT1 (saft_cover_at@{o dobj h so dp cp w s t pl pa _ _ _}
            U comp cont G d W c h)
    = wp_from W (saft_sub@{o dobj h so dp cp _ _} U comp G d c h) :=
  eq_refl.

(* 相关说明。 （已译） *)
Definition p453_cover_t_below_pa@{o dobj h so dp cp w s t pl pa +|
    h <= so, h < dp, h < cp, o <= s, h <= s, h < t, t < pa +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D)
  (W : WellPoweredAt@{w o s h t} (saft_prod@{o dobj h so dp} U comp G d)) :=
  saft_cover_at@{o dobj h so dp cp w s t pl pa _ _ _} U comp cont G d W.

Definition p453_cover_pa_below_t@{o dobj h so dp cp w s t pl pa +|
    h <= so, h < dp, h < cp, o <= s, h <= s, h < t, pa < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D)
  (W : WellPoweredAt@{w o s h t} (saft_prod@{o dobj h so dp} U comp G d)) :=
  saft_cover_at@{o dobj h so dp cp w s t pl pa _ _ _} U comp cont G d W.

(* At one tuple at [Id[Sets]] under [Untruncate], reshaped covering
 datum holds at every 对象 old one refuted. （已译） *)
Definition p453_separation@{o so t +| Set < o, o < so, o < t +}
  (Un : Untruncate@{o}) :
  (∀ d : Sets@{o so},
     SubobjectCoverAt (@Id Sets@{o so}) Sets_Complete
       (Sets_Cogenerator_untruncate Un) d
       (Sets_WellPowered_untruncate@{o so t} Un _))
  * (SubobjectCover (@Id Sets@{o so}) Sets_Complete
       (Sets_Cogenerator_untruncate Un)
       (WellPowered_SubobjectIndex (Sets_WellPowered_untruncate@{o so t} Un))
     → False) :=
  sets_id_cover_separation Un.

(* The monos lemma over pullbacks in [C], at its stated type. *)
Definition p453_monos_lemma@{o hc dobj h +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  (HP : HasPullbacks C) {X Y : =(d) ↓ U} (m : X ~{=(d) ↓ U}~> Y) :
  Monic m ↔ Monic (snd (`1 m)) :=
  comma_monic_iff_underlying_monic HP m.

(** ** Guard block *)

Check @comma_monic_of_underlying.
Check @kp_diag.
Check @kp_diag_fst.
Check @kp_diag_snd.
Check @kp_obj.
Check @kp_fst.
Check @kp_snd.
Check @underlying_monic_of_comma_monic.
Check @comma_monic_iff_underlying_monic.
Check @comma_cogenerator.
Check @comma_wp_index.
Check @comma_wp_dom.
Check @comma_wp_mono.
Check @comma_wp_to.
Check @underlying_sub.
Check @comma_wp_from.
Check @comma_wp_iso_to.
Check @comma_wp_iso_from.
Check @comma_wp_to_from.
Check @comma_WellPoweredAt.
Check @comma_WellPowered.
Check @SAFT_comma_initial.
Check @SAFT_universal_arrow.
Check @SAFT_left.
Check @SAFT_adjunction.
Check @SAFT_wellpowered.
Check @SAFT_left_obj.
Check @SAFT_wellpowered_iff.
Check @HasSubobjectWidePullbacks.
Check @Complete_HasSubobjectWidePullbacks.
Check @least_index.
Check @least_top.
Check @least_lift.
Check @least_lift_commutes.
Check @least_dom.
Check @least_mono.
Check @least_sub.
Check @least_index_of.
Check @least_le.
Check @SAFT_thm2_initial.
Check @SAFT_thm2_universal_arrow.
Check @SAFT_thm2_left.
Check @SAFT_thm2_adjunction.
Check @SAFT_thm2.
Check @SAFT_thm2_left_obj.
Check @right_adjoint_PreservesWidePullbacks.
Check @SAFT_iff.
Check @image_family_cone.
Check @saft_index.
Check @saft_fam.
Check @saft_prod_limit.
Check @saft_prod.
Check @saft_point.
Check @saft_point_commutes.
Check @saft_kappa.
Check @saft_square.
Check @saft_sub.
Check @saft_sub_to.
Check @saft_pb_cone.
Check @saft_lift.
Check @saft_lift_commutes.
Check @SubobjectCoverAt.
Check @saft_cover_at.
Check @saft_solution_set_at.
Check @SAFT_cover_wp_at.
Check @SAFT_cover_wp.
Check @saft_cover_at_index.
Check @saft_solution_set_at_index.
Check @SAFT_cover_wp_is_GAFT.
Check @continuous_Set_functor_representable.
Check @continuous_Set_functor_representable_obj.
Check @continuous_Set_functor_representable_iff.
Check @continuous_Set_functor_representable_at.
Check @saft_colim.
Check @saft_cocomplete.
Check @SAFT_cover_wp_iso.
Check @comma_cogenerator_index.
Check @sets_id_saft.
Check @sets_id_saft_cover.
Check @sets_id_new_cover.
Check @sets_id_old_cover_refuted.
Check @sets_id_cover_separation.
Check @sets_hom_saft.
Check @sets_id_repr_saft.
Check @sets_hom_repr_saft.
Check @sets_saft_cocomplete.
Check @subsets_inverse_image_saft.
Check @subsets_inverse_image_thm2.
Check @subsets_saft_cocomplete.
Check @indiscrete_saft.
Check @indiscrete_saft_cocomplete.
Check @sets_id_saft_iso.
Check @subsets_inverse_image_saft_iso.
