(*
   本文件为测试：ProbeStoneCech455。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Complete.Freyd.
Require Import Category.Structure.WellPowered.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.CompHaus.
Require Import Category.Instance.Top.StoneCech.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.SAFT.
Require Import Category.Adjunction.SAFT.Characterization.
Require Import Coq.Lists.List.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Sets.Classifier.
Require Import Coq.Arith.PeanoNat.
Require Import Category.Instance.Top.StoneCech.Refutations.

Generalizable All Variables.

(* 相关说明。 （已译） *)

Fail Check probe455_absent_name.

(* 相关说明。 （已译） *)

(* CONTROL: [StoneCech_finite], restated at its stated type. *)
Definition p455_stonecech_finite@{o h +} (X : SetoidObject@{o o})
  (FX : FinEnum X) :
  UniversalArrow (C:=Sets) (Setoid_Lift@{o h} X) CompHaus_Forget :=
  StoneCech_finite X FX.

(* CONTROL: [StoneCech_finite_obj] and [StoneCech_finite_unit], restated. *)
Example p455_fin_obj_at@{o h +} (X : SetoidObject@{o o}) (FX : FinEnum X) :
  @arrow_obj Sets _ (Setoid_Lift@{o h} X) _ (StoneCech_finite X FX)
    = Discrete_CH X FX := eq_refl.

Example p455_fin_unit_at@{o h +} (X : SetoidObject@{o o}) (FX : FinEnum X) :
  @arrow Sets _ (Setoid_Lift@{o h} X) _ (StoneCech_finite X FX)
    = sc_fin_unit X FX := eq_refl.

(* CONTROL: at two-point set universal 对象 IS [Bool_CH], so
 [Bool_CH] not wrong value there; it [Discrete_CH] at the
 enumeration passed. （已译） *)
Example p455_fin_obj_bool@{o h +} :
  @arrow_obj Sets _ (Setoid_Lift@{o h} bool_setoid_object@{o o}) _
    (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum) = Bool_CH :=
  eq_refl.

Example p455_fin_obj_bool_enum@{o h +} :
  @arrow_obj Sets _ (Setoid_Lift@{o h} bool_setoid_object@{o o}) _
    (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum)
    = Discrete_CH bool_setoid_object@{o o} bool_FinEnum := eq_refl.

(* CONTROL: the one-point space is an object of [CompHaus] at every
   carrier universe. *)
Example p455_point_ch_above_set@{o +| Set < o +} :
  `1 Point_CH = Point_Top@{o} := eq_refl.

Fail Example p455_n1_fin_obj_bool_point@{o h +} :
  @arrow_obj Sets _ (Setoid_Lift@{o h} bool_setoid_object@{o o}) _
    (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum) = Point_CH :=
  eq_refl.

(* 相关说明。 （已译） *)
Lemma p455_n1_wrong_value@{o h +} :
  @arrow_obj Sets _ (Setoid_Lift@{o h} bool_setoid_object@{o o}) _
    (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum) = Point_CH →
  False.
Proof.
  intro H.
  assert (E : ∀ a b : top_carrier (`1 (@arrow_obj Sets _
                 (Setoid_Lift@{o h} bool_setoid_object@{o o}) _
                 (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum))),
              a = b).
  { rewrite H. intros [] []. reflexivity. }
  specialize (E true false). discriminate E.
Qed.

(* CONTROL: second enumeration two-point set, list reversed,
 对象 it gives. （已译） *)
Lemma p455_bool_FinEnum_rev@{o +} : FinEnum bool_setoid_object@{o o}.
Proof.
  exists (false :: true :: nil). intros [|].
  - exists true. split; [right; left; reflexivity | reflexivity].
  - exists false. split; [left; reflexivity | reflexivity].
Qed.

Definition p455_bool_ch_rev@{o +} : CompHaus :=
  Discrete_CH bool_setoid_object@{o o} p455_bool_FinEnum_rev.

Fail Example p455_n2_fin_obj_other_enum@{o h +} :
  @arrow_obj Sets _ (Setoid_Lift@{o h} bool_setoid_object@{o o}) _
    (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum)
    = Discrete_CH bool_setoid_object@{o o} p455_bool_FinEnum_rev := eq_refl.

(* CONTROL: N2's two 对象 have one space; they differ the
 compactness 证明 alone. （已译） *)
Example p455_n2_same_space@{o +} :
  `1 (Discrete_CH bool_setoid_object@{o o} bool_FinEnum)
  = `1 (Discrete_CH bool_setoid_object@{o o} p455_bool_FinEnum_rev) :=
  eq_refl.

(* CONTROL: unit does not see enumeration; at two-point set it
 IS 恒等 [Sets]. （已译） *)
Example p455_fin_unit_other_enum@{o h +} (X : SetoidObject@{o o})
  (FX FX' : FinEnum X) :
  @arrow Sets _ (Setoid_Lift@{o h} X) _ (StoneCech_finite X FX)
    = sc_fin_unit X FX' := eq_refl.

Example p455_fin_unit_bool_id@{o h +} :
  @arrow Sets _ (Setoid_Lift@{o h} bool_setoid_object@{o o}) _
    (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum)
    = @id Sets (Setoid_Lift@{o h} bool_setoid_object@{o o}) := eq_refl.

(* 相关说明。 （已译） *)
Definition p455_negb_lift@{o h +} :
  Setoid_Lift@{o h} bool_setoid_object@{o o} ~{Sets}~>
    CompHaus_Forget (Discrete_CH bool_setoid_object@{o o} bool_FinEnum).
Proof.
  unshelve refine {| morphism := negb |}.
  intros a b e. simpl in *. rewrite e. reflexivity.
Defined.

Lemma p455_negb_not_unit@{o h +} :
  p455_negb_lift
    ≈ @arrow Sets _ (Setoid_Lift@{o h} bool_setoid_object@{o o}) _
        (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum) → False.
Proof. intro H. specialize (H true). simpl in H. discriminate H. Qed.

Fail Example p455_n3_fin_unit_negb@{o h +} :
  @arrow Sets _ (Setoid_Lift@{o h} bool_setoid_object@{o o}) _
    (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum)
    = p455_negb_lift := eq_refl.

(* 相关说明。 （已译） *)
Example p455_incl_obj_at@{h o +} (K : CompHaus) :
  @arrow_obj Top@{h o} _ (CompHaus_Incl K) _ (CompHaus_Incl_universal K)
    = K := eq_refl.

Example p455_incl_obj_point@{h o +} :
  @arrow_obj Top@{h o} _ (CompHaus_Incl Point_CH) _
    (CompHaus_Incl_universal Point_CH) = Point_CH := eq_refl.

Fail Example p455_n4_incl_obj_point@{h o +} (K : CompHaus) :
  @arrow_obj Top@{h o} _ (CompHaus_Incl K) _ (CompHaus_Incl_universal K)
    = Point_CH := eq_refl.

(* CONTROL: type 泛箭头 范畴 named. （已译） *)
Definition p455_ua_with_C@{o h +} (X : SetoidObject@{o o}) : Type :=
  UniversalArrow (C:=Sets) (Setoid_Lift@{o h} X) CompHaus_Forget.

Fail Definition p455_n5_ua_without_C@{o h +} (X : SetoidObject@{o o}) :
  Type :=
  UniversalArrow (Setoid_Lift@{o h} X) CompHaus_Forget.

(* 相关说明。 （已译） *)

(*
   本节说明 ProbeStoneCech455 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record p455_TopP@{o} := {
  p455_tp_carrier :> SetoidObject@{o o};
  p455_POpen : (p455_tp_carrier → Prop) → Prop;
  p455_popen_union (I : Type@{o}) (U : I → p455_tp_carrier → Prop) :
    (∀ i, p455_POpen (U i)) → p455_POpen (fun x => exists i, U i x)%type
}.

Definition p455_ContHom@{o} (X Y : p455_TopP@{o}) : Type@{o} :=
  { f : SetoidMorphism@{o o o} X Y &
    ∀ U : Y → Prop, p455_POpen Y U → p455_POpen X (fun x => U (f x)) }.

(* CONTROL: the tree's continuous maps one universe up. *)
Definition p455_conthom_at_h@{h o +| o < h +} (X Y : TopSpace@{o}) :
  Type@{h} :=
  ContinuousMorphism X Y.

Fail Definition p455_n6_conthom_at_o@{o +} (X Y : TopSpace@{o}) :
  Type@{o} :=
  ContinuousMorphism X Y.

(* 相关说明。 （已译） *)
Definition p455_point_hausdorff_set : IsHausdorff Point_Top@{Set} :=
  Point_Hausdorff.

Definition p455_point_hausdorff_o@{h o +| o < h +} :
  IsHausdorff@{h o o o} Point_Top@{o} :=
  Discrete_Hausdorff _.

Definition p455_point_compact_o@{o +| Set < o +} :
  IsCompact Point_Top@{o} :=
  Point_Compact.

Fail Definition p455_n7_point_hausdorff_o@{h o +| o < h +} :
  IsHausdorff@{h o o o} Point_Top@{o} :=
  Point_Hausdorff.

(* CONTROL: [bool_FinEnum] stated without universe binder, its uses:
 at [Set], at [FinEnum] above [Set] conversion, 对象 of
 [CompHaus] above [Set] once its setoid is named at that universe.（已译） *)
Lemma p455_bool_FinEnum_bare : FinEnum bool_setoid_object.
Proof.
  exists (true :: false :: nil). intros [|].
  - exists true. split; [left; reflexivity | reflexivity].
  - exists false. split; [right; left; reflexivity | reflexivity].
Qed.

Definition p455_bare_at_set : FinEnum bool_setoid_object@{Set Set} :=
  p455_bool_FinEnum_bare.

Definition p455_bare_at_o@{o +| Set < o +} :
  FinEnum bool_setoid_object@{o o} :=
  p455_bool_FinEnum_bare.

Definition p455_bare_named_setoid@{o +| Set < o +} : CompHaus :=
  (Bool_Discrete@{o};
     (Discrete_Compact_of_FinEnum bool_setoid_object@{o o}
        p455_bool_FinEnum_bare, Discrete_Hausdorff _)).

(* CONTROL: [Bool_CH]'s body, and [Bool_CH] itself above [Set]. *)
Definition p455_bool_ch_body@{o +} : CompHaus :=
  (Bool_Discrete@{o};
     (Discrete_Compact_of_FinEnum _ bool_FinEnum, Discrete_Hausdorff _)).

Example p455_bool_ch_above_set@{o +| Set < o +} :
  `1 Bool_CH = Bool_Discrete@{o} := eq_refl.

(* CONTROL: N8's own body at [Set]. *)
Definition p455_bool_ch_bare_at_set : CompHaus :=
  (Bool_Discrete@{Set};
     (Discrete_Compact_of_FinEnum _ p455_bool_FinEnum_bare,
      Discrete_Hausdorff _)).

Fail Definition p455_n8_bool_ch_bare@{o +} : CompHaus :=
  (Bool_Discrete@{o};
     (Discrete_Compact_of_FinEnum _ p455_bool_FinEnum_bare,
      Discrete_Hausdorff _)).

(* 相关说明。 （已译） *)

(* CONTROL: the reduction of GAFT at [CompHaus_Forget] to completeness. *)
Definition p455_pres@{h s +} :
  @PreservesImageLimit CompHaus Sets@{h s} CompHaus_Forget :=
  CompHaus_Forget_PreservesImageLimit.

Definition p455_taut_sols@{h s +} (d : obj[Sets@{h s}]) :
  SolutionSet CompHaus_Forget d :=
  taut_sols d.

Definition p455_gaft_only_complete@{h s +}
  (comp : @Complete@{h h h h} CompHaus) :
  { F : Sets@{h s} ⟶ CompHaus & F ⊣ CompHaus_Forget } :=
  GAFT_CompHaus_only_complete comp.

(* CONTROL: [GAFT_CompHaus_only_complete]'s body, restated. *)
Definition p455_gaft_body@{h s +} (comp : @Complete@{h h h h} CompHaus) :
  { F : Sets@{h s} ⟶ CompHaus & F ⊣ CompHaus_Forget } :=
  GAFT CompHaus_Forget comp CompHaus_Forget_PreservesImageLimit taut_sols.

(* CONTROL: tautological solution set 对象 [CompHaus]
 above homs. （已译） *)
Definition p455_taut_sols_above@{h s c +| h < c +} (d : obj[Sets@{h s}]) :
  SolutionSet (CompHaus_Forget : (CompHaus : Category@{c h h}) ⟶ Sets@{h s})
    d :=
  taut_sols d.

Fail Definition p455_n9_gaft_taut_above@{h s c +| h < c +}
  (comp : @Complete@{h h h c} CompHaus) :
  { F : Sets@{h s} ⟶ CompHaus & F ⊣ CompHaus_Forget } :=
  GAFT CompHaus_Forget comp CompHaus_Forget_PreservesImageLimit taut_sols.

(* 相关说明。 （已译） *)

(* CONTROL: [Discrete_Hausdorff]; compactness of a discrete space iff
   finite enumerability, at one instance; discrete ℕ not compact. *)
Definition p455_discrete_hausdorff@{h o +| o < h +}
  (A : SetoidObject@{o o}) : IsHausdorff@{h o o o} (Discrete_Top@{o o} A) :=
  Discrete_Hausdorff A.

Definition p455_compact_iff@{o +} (A : SetoidObject@{o o}) :
  (FinEnum A → IsCompact (Discrete_Top@{o o} A))
  ∧ (IsCompact (Discrete_Top@{o o} A) → FinEnum A) :=
  (Discrete_Compact_of_FinEnum A, FinEnum_of_Discrete_Compact A).

Definition p455_nat_not_compact@{o +} :
  IsCompact (Discrete_Top@{o o} sc_nat_setoid) → False :=
  Discrete_nat_not_compact.

(* CONTROL: Exercise 4 over the underlying-set functor. *)
Definition p455_ex4_separated@{o h +} (X : SetoidObject@{o o})
  (UA : UniversalArrow (C:=Sets) (Setoid_Lift@{o h} X) CompHaus_Forget) :
  (∀ x y : X, (∀ (K : CompHaus)
                 (f : Setoid_Lift X ~{Sets}~> CompHaus_Forget K), f x ≈ f y)
              → x ≈ y) →
  ∀ x y : X, @arrow _ _ _ _ UA x ≈ @arrow _ _ _ _ UA y → x ≈ y :=
  unit_injective_of_separated X UA.

Definition p455_ex4_converse@{o h +} (X : SetoidObject@{o o})
  (UA : UniversalArrow (C:=Sets) (Setoid_Lift@{o h} X) CompHaus_Forget) :
  (∀ x y : X, @arrow _ _ _ _ UA x ≈ @arrow _ _ _ _ UA y → x ≈ y) →
  ∀ x y : X, (∀ (K : CompHaus)
                (f : Setoid_Lift X ~{Sets}~> CompHaus_Forget K), f x ≈ f y)
             → x ≈ y :=
  separated_of_unit_injective X UA.

Definition p455_ex4_dec@{o h +} (X : SetoidObject@{o o})
  (UA : UniversalArrow (C:=Sets) (Setoid_Lift@{o h} X) CompHaus_Forget)
  (dec : ∀ x y : X, (x ≈ y) + ((x ≈ y) → False)) :
  ∀ x y : X, @arrow _ _ _ _ UA x ≈ @arrow _ _ _ _ UA y → x ≈ y :=
  unit_injective_of_dec X UA dec.

Definition p455_ex4_bool@{o h +} :
  ∀ x y : bool_setoid_object@{o o},
    @arrow _ _ _ _ (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum
                    : UniversalArrow (C:=Sets)
                        (Setoid_Lift@{o h} bool_setoid_object@{o o})
                        CompHaus_Forget) x
    ≈ @arrow _ _ _ _ (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum
                      : UniversalArrow (C:=Sets)
                          (Setoid_Lift@{o h} bool_setoid_object@{o o})
                          CompHaus_Forget) y
    → x ≈ y :=
  StoneCech_finite_bool_injective.

(* CONTROL: Exercise 4 at a space, over the inclusion. *)
Definition p455_ex4_incl@{h o +} (K : CompHaus) (X : Top@{h o})
  (HX : KSeparated K X)
  (UA : UniversalArrow (C:=Top@{h o}) X CompHaus_Incl) :
  ∀ x y : top_carrier X,
    continuous_map (@arrow _ _ _ _ UA) x
      ≈ continuous_map (@arrow _ _ _ _ UA) y
    → x ≈ y :=
  StoneCech_unit_injective_completely_regular K X HX UA.

Definition p455_ex4_incl_converse@{h o +} (K : CompHaus)
  (sepK : ∀ (Y : CompHaus) (p q : top_carrier (`1 Y)),
            (∀ k : Y ~{CompHaus}~> K,
               continuous_map (`1 k) p ≈ continuous_map (`1 k) q) → p ≈ q)
  (X : Top@{h o}) (UA : UniversalArrow (C:=Top@{h o}) X CompHaus_Incl)
  (Hinj : ∀ x y : top_carrier X,
     continuous_map (@arrow _ _ _ _ UA) x
       ≈ continuous_map (@arrow _ _ _ _ UA) y
     → x ≈ y) :
  KSeparated K X :=
  KSeparated_of_unit_injective K sepK X UA Hinj.

Definition p455_ex4_at_CompHaus@{h o +} (K : CompHaus) :
  ∀ x y : top_carrier (CompHaus_Incl K : obj[Top@{h o}]),
    continuous_map (@arrow _ _ _ _ (CompHaus_Incl_universal K)) x
      ≈ continuous_map (@arrow _ _ _ _ (CompHaus_Incl_universal K)) y
    → x ≈ y :=
  StoneCech_unit_injective_at_CompHaus K.

Definition p455_ex4_incl_local@{h o +} (K : CompHaus) (X : Top@{h o})
  (UA : UniversalArrow (C:=Top@{h o}) X CompHaus_Incl)
  (sepK : ∀ p q : top_carrier (`1 (@arrow_obj _ _ _ _ UA)),
            (∀ k : @arrow_obj _ _ _ _ UA ~{CompHaus}~> K,
               continuous_map (`1 k) p ≈ continuous_map (`1 k) q) → p ≈ q)
  (Hinj : ∀ x y : top_carrier X,
     continuous_map (@arrow _ _ _ _ UA) x
       ≈ continuous_map (@arrow _ _ _ _ UA) y
     → x ≈ y) :
  KSeparated K X :=
  KSeparated_of_unit_injective_local K X UA sepK Hinj.

Definition p455_ex4_local_at_CompHaus@{h o +} (K : CompHaus) :
  KSeparated K (CompHaus_Incl K : obj[Top@{h o}]) :=
  KSeparated_of_unit_injective_local_at_CompHaus K.

(* 相关说明。 （已译） *)

(* CONTROL: completeness [CompHaus] refuted index at shape
 below 对象; [IEM] at [c <= s] [h <= s], at GAFT's
 instance. （已译） *)
Definition p455_not_complete_index@{r s c h +| s < c +}
  (AI : ArrowIndex@{s c h} CompHaus) (comp : @Complete@{r s h c} CompHaus) :
  False :=
  CompHaus_not_complete AI comp.

Definition p455_not_complete_IEM@{e r s c h +| c <= s, h <= s +}
  (E : IEM@{e}) (comp : @Complete@{r s h c} CompHaus) : False :=
  CompHaus_not_complete_IEM E comp.

Definition p455_not_complete_IEM_gaft@{e h +} (E : IEM@{e})
  (comp : @Complete@{h h h h} CompHaus) : False :=
  CompHaus_not_complete_IEM E comp.

(* CONTROL: arrow index [Top] transported [CompHaus]; through it,
 N10's statement [h <= s] refuted under [IEM], GAFT's shape
 对象 above homs. （已译） *)
Definition p455_sub_index@{s h o c +} (AIT : ArrowIndex@{s h h} Top@{h o}) :
  ArrowIndex@{s c h} (CompHaus : Category@{c h h}) :=
  CompHaus_ArrowIndex_of_Top AIT.

Definition p455_not_complete_IEM_below@{e r s c h +| s < c, h <= s +}
  (E : IEM@{e}) (comp : @Complete@{r s h c} CompHaus) : False :=
  CompHaus_not_complete_IEM_below E comp.

Definition p455_not_complete_IEM_above@{e h c +| h < c +} (E : IEM@{e})
  (comp : @Complete@{h h h c} (CompHaus : Category@{c h h})) : False :=
  CompHaus_not_complete_IEM_above E comp.

Fail Definition p455_n10_not_complete_IEM_below@{e r s c h +| s < c +}
  (E : IEM@{e}) (comp : @Complete@{r s h c} CompHaus) : False :=
  CompHaus_not_complete_IEM E comp.

(*
   本节说明 ProbeStoneCech455 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition p455_not_complete_below_slots@{e h c o +| h < c +}
  (E : IEM@{e})
  (comp : @Complete@{h h h c}
            (CompHaus@{c h h c _ _ o _ _ _ _ _ _ _ _} : Category@{c h h})) :
  False :=
  CompHaus_not_complete_IEM_below@{e h h c h o _ _ _ _ _ _ _} E comp.

Definition p455_not_complete_IEM_top_slot@{e h t o +| t < h +}
  (E : IEM@{e})
  (comp : @Complete@{h h h h}
            (CompHaus@{h h t h _ _ o _ _ _ _ _ _ _ _} : Category@{h h h})) :
  False :=
  CompHaus_not_complete_IEM E comp.

Fail Definition p455_n21_below_top_slot@{e h c t o +| t < h, h < c +}
  (E : IEM@{e})
  (comp : @Complete@{h h h c}
            (CompHaus@{c h t c _ _ o _ _ _ _ _ _ _ _} : Category@{c h h})) :
  False :=
  CompHaus_not_complete_IEM_below@{e h h c h o _ _ _ _ _ _ _} E comp.

(* CONTROL: the same for [Top]. *)
Definition p455_top_not_complete_index@{r s h o +| s < h +}
  (AI : ArrowIndex@{s h h} Top@{h o}) (comp : @Complete@{r s h h} Top@{h o}) :
  False :=
  Top_not_complete AI comp.

Definition p455_top_not_complete_IEM@{e r s h o +| h <= s +} (E : IEM@{e})
  (comp : @Complete@{r s h h} Top@{h o}) : False :=
  Top_not_complete_IEM E comp.

Fail Definition p455_n11_top_not_complete_IEM_below@{e r s h o +| s < h +}
  (E : IEM@{e}) (comp : @Complete@{r s h h} Top@{h o}) : False :=
  Top_not_complete_IEM E comp.

(* CONTROL: 伴随 refuted under [IEM], applied GAFT's own
 output; 泛箭头 at large set refuted index. （已译） *)
Definition p455_adj_refuted_IEM@{e h s +} (E : IEM@{e})
  (A : { F : Sets@{h s} ⟶ CompHaus & F ⊣ CompHaus_Forget }) : False :=
  StoneCech_adjunction_refuted_IEM E A.

Definition p455_refutes_gaft_output@{e h s +} (E : IEM@{e})
  (comp : @Complete@{h h h h} CompHaus) : False :=
  StoneCech_adjunction_refuted_IEM E
    (GAFT_CompHaus_only_complete@{h s _ _ _ _ _ _ _ _} comp).

Definition p455_large_ua_refuted@{c h +} (AI : ArrowIndex@{h c h} CompHaus)
  (UA : UniversalArrow (C:=Sets) (KSet AI) CompHaus_Forget) : False :=
  large_universal_arrow_refuted AI UA.

Definition p455_gaft_vacuous@{e h s +} (E : IEM@{e})
  (comp : @Complete@{h h h h} CompHaus) :
  ({ F : Sets@{h s} ⟶ CompHaus & F ⊣ CompHaus_Forget } * False)%type :=
  GAFT_CompHaus_IEM_vacuous E comp.

(* CONTROL: 对象 above homs, 伴随 refuted an
 arrow index at hom universe. （已译） *)
Definition p455_adj_refuted_index_above@{h s c +| h < c +}
  (AI : ArrowIndex@{h c h} (CompHaus : Category@{c h h}))
  (A : { F : Sets@{h s} ⟶ (CompHaus : Category@{c h h})
       & F ⊣ CompHaus_Forget }) : False :=
  large_universal_arrow_refuted AI
    (universal_arrow_of_adjunction (`2 A) (KSet AI)).

(* CONTROL: N12's statement, refuted under [IEM] through [Top]'s index. *)
Definition p455_adj_refuted_IEM_above@{e h s c +| h < c +} (E : IEM@{e})
  (A : { F : Sets@{h s} ⟶ (CompHaus : Category@{c h h})
       & F ⊣ CompHaus_Forget }) : False :=
  StoneCech_adjunction_refuted_IEM_above E A.

Fail Definition p455_n12_adj_refuted_above@{e h s c +| h < c +}
  (E : IEM@{e})
  (A : { F : Sets@{h s} ⟶ (CompHaus : Category@{c h h})
       & F ⊣ CompHaus_Forget }) : False :=
  StoneCech_adjunction_refuted_IEM E A.

(* CONTROL: same slot slot, 证明 slot at 对象; and
 GAFT's route 对象 above homs, any solution sets. （已译） *)
Definition p455_adj_above_slots@{e h s c o +| h < c +} (E : IEM@{e})
  (A : { F : Sets@{h s} ⟶ (CompHaus@{c h h c _ _ o _ _ _ _ _ _ _ _}
                             : Category@{c h h})
       & F ⊣ CompHaus_Forget }) : False :=
  StoneCech_adjunction_refuted_IEM_above@{e h s o c _ _ _ _ _ _ _} E A.

Definition p455_gaft_vacuous_above@{e h s c +| h < c +} (E : IEM@{e})
  (comp : @Complete@{h h h c} (CompHaus : Category@{c h h}))
  (sols : ∀ d : obj[Sets@{h s}], SolutionSet CompHaus_Forget d) :
  ({ F : Sets@{h s} ⟶ (CompHaus : Category@{c h h})
     & F ⊣ CompHaus_Forget } * False)%type :=
  GAFT_CompHaus_IEM_vacuous_above E comp sols.

Fail Definition p455_n20_adj_above_proof_slot@{e h s c o +| h < c +}
  (E : IEM@{e})
  (A : { F : Sets@{h s} ⟶ (CompHaus@{c h h h _ _ o _ _ _ _ _ _ _ _}
                             : Category@{c h h})
       & F ⊣ CompHaus_Forget }) : False :=
  StoneCech_adjunction_refuted_IEM_above@{e h s o c _ _ _ _ _ _ _} E A.

(* CONTROL: same fourteenth fifteenth slots, the
 universes separating opens Hausdorff 证明, written out
 at points' universe o. （已译） *)
Definition p455_adj_above_hausdorff_at_o@{e h s c o +| h < c +}
  (E : IEM@{e})
  (A : { F : Sets@{h s} ⟶ (CompHaus@{c h h c _ _ o _ _ _ _ _ _ o o}
                             : Category@{c h h})
       & F ⊣ CompHaus_Forget }) : False :=
  StoneCech_adjunction_refuted_IEM_above@{e h s o c _ _ _ _ _ _ _} E A.

Fail Definition p455_n22_hausdorff_opens_below@{e h s c o q +| h < c, q < o +}
  (E : IEM@{e})
  (A : { F : Sets@{h s} ⟶ (CompHaus@{c h h c _ _ o _ _ _ _ _ _ q q}
                             : Category@{c h h})
       & F ⊣ CompHaus_Forget }) : False :=
  StoneCech_adjunction_refuted_IEM_above@{e h s o c _ _ _ _ _ _ _} E A.

(* * ** N13-N17, N19 (UNIVERSE): Instance/Top/StoneCech/Refutations.v, SAFT
 at 含入 （已译） *)

(*
   本节说明 ProbeStoneCech455 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition p455_saft_incl@{s h +} (comp : @Complete@{s s h h} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl) (G : Cogenerator CompHaus) :
  { F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } :=
  SAFT_CompHaus_Incl comp cont G.

Definition p455_saft_incl_apart@{s c h +}
  (comp : @Complete@{s s h c} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl) (G : Cogenerator CompHaus) :
  { F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } :=
  SAFT_wellpowered CompHaus_Incl comp cont G CompHaus_WellPowered.

Definition p455_saft_wp_hyp_above@{s c h t +| h < c +}
  (comp : @Complete@{s s h c} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl) (G : Cogenerator CompHaus)
  (WP : WellPowered@{c h h c t} (CompHaus : Category@{c h h})) :
  { F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } :=
  SAFT_wellpowered CompHaus_Incl comp cont G WP.

(* CONTROL: the two vacuity pairs, restated. *)
Definition p455_saft_vacuous@{s c h +} (AI : ArrowIndex@{s c h} CompHaus)
  (comp : @Complete@{s s h c} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl)
  (G : Cogenerator CompHaus) (WP : WellPowered CompHaus) :
  ({ F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } * False)%type :=
  SAFT_Incl_vacuous AI comp cont G WP.

Definition p455_saft_iem_vacuous@{e s c h +} (E : IEM@{e})
  (comp : @Complete@{s s h c} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl)
  (G : Cogenerator CompHaus) (WP : WellPowered CompHaus) :
  ({ F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } * False)%type :=
  SAFT_Incl_IEM_vacuous E comp cont G WP.

Definition p455_saft_iem_vacuous_below@{e s c h +| h <= s, s < c +}
  (E : IEM@{e}) (comp : @Complete@{s s h c} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl)
  (G : Cogenerator CompHaus) (WP : WellPowered CompHaus) :
  ({ F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } * False)%type :=
  SAFT_Incl_IEM_vacuous_below E comp cont G WP.

Fail Definition p455_n13_saft_incl_above@{s c h +| h < c +}
  (comp : @Complete@{s s h c} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl) (G : Cogenerator CompHaus) :
  { F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } :=
  SAFT_wellpowered CompHaus_Incl comp cont G CompHaus_WellPowered.

Fail Definition p455_n14_saft_incl_below@{s c h +| c < h +}
  (comp : @Complete@{s s h c} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl) (G : Cogenerator CompHaus) :
  { F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } :=
  SAFT_wellpowered CompHaus_Incl comp cont G CompHaus_WellPowered.

Fail Definition p455_n19_saft_wp_below@{s c h +| c < h +}
  (comp : @Complete@{s s h c} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl) (G : Cogenerator CompHaus)
  (WP : WellPowered CompHaus) :
  { F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } :=
  SAFT_wellpowered CompHaus_Incl comp cont G WP.

(*
   本节说明 ProbeStoneCech455 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition p455_wellpowered@{c h t +} :
  WellPowered@{c h h h t} (CompHaus : Category@{c h h}) :=
  CompHaus_WellPowered.

Definition p455_trivial_small_below@{c h t +| c < h +} :
  WellPowered@{c h h h t} (CompHaus : Category@{c h h}) :=
  trivial_small CompHaus.

Definition p455_trivial_small_free@{c h t +} :
  WellPowered@{c h h c t} (CompHaus : Category@{c h h}) :=
  trivial_small CompHaus.

Definition p455_wp_type_at_c@{c h t +| h < c +} : Type :=
  WellPowered@{c h h c t} (CompHaus : Category@{c h h}).

Definition p455_incl_above@{c h +| h < c +} :=
  CompHaus_Incl : (CompHaus : Category@{c h h}) ⟶ Top.

Fail Definition p455_n15_wp_type_at_h@{c h t +| h < c +} : Type :=
  WellPowered@{c h h h t} (CompHaus : Category@{c h h}).

Fail Definition p455_n16_trivial_small_at_c@{c h t +| h < c +} :
  WellPowered@{c h h c t} (CompHaus : Category@{c h h}) :=
  trivial_small CompHaus.

Fail Definition p455_n17_incl_below@{c h +| c < h +} :=
  CompHaus_Incl : (CompHaus : Category@{c h h}) ⟶ Top.

(* 相关说明。 （已译） *)

(* CONTROL: [big_inj_injective], restated; [big_inj]'s body with
   [obj[CompHaus]] written in both places, at [s < c]. *)
Definition p455_big_inj_injective@{r s c h +}
  (C := CompHaus : Category@{c h h})
  (comp : @Complete@{r s h c} C) (phi psi : obj[C] → bool) :
  big_inj comp phi ≈ big_inj comp psi → ∀ j, phi j = psi j :=
  big_inj_injective comp phi psi.

Definition p455_big_inj_unsplit@{r s c h +| s < c +}
  (comp : @Complete@{r s h c} (CompHaus : Category@{c h h}))
  (phi : obj[CompHaus] → bool) :=
  continuous_map
    (`1 (unique_obj
           (iprod_desc
              (complete_iprod comp (fun _ : obj[CompHaus] => Bool_CH))
              (fun j => sc_pt_bool (phi j))))) ttt.

Fail Definition p455_n18_big_inj_below@{r s c h +| s < c +}
  (comp : @Complete@{r s h c} (CompHaus : Category@{c h h}))
  (phi : obj[CompHaus] → bool) :=
  big_inj comp phi.

(* 相关说明。 （已译） *)
Definition p455_cogen_dne@{k c h +} (G : Cogenerator@{k c h} CompHaus)
  (stable : ∀ j (a b : top_carrier (`1 (cog_obj G j))),
              ((a ≈ b → False) → False) → a ≈ b) :
  ∀ P : Prop, ~~P → P :=
  CompHaus_cogenerator_stable_DNE G stable.

(* 相关说明。 （已译） *)
Definition p455_point_sep_dne@{c h +} (K : (CompHaus : Category@{c h h}))
  (sepK : ∀ (Y : (CompHaus : Category@{c h h})) (p q : top_carrier (`1 Y)),
            (∀ k : Y ~{CompHaus}~> K,
               continuous_map (`1 k) p ≈ continuous_map (`1 k) q) → p ≈ q)
  (stable : ∀ a b : top_carrier (`1 K), ((a ≈ b → False) → False) → a ≈ b) :
  ∀ P : Prop, ~~P → P :=
  CompHaus_point_separator_stable_DNE K sepK stable.

(** ** Guard block *)

(* Instance/Top/StoneCech.v: 41 names *)
Check @Discrete_Hausdorff.
Check @FinEnum.
Check @Discrete_Compact_of_FinEnum.
Check @FinEnum_of_Discrete_Compact.
Check @sc_nat_setoid.
Check @sc_in_le_fold_max.
Check @nat_not_FinEnum.
Check @Discrete_nat_not_compact.
Check @bool_FinEnum.
Check @Bool_CH.
Check @Point_CH.
Check @Discrete_CH.
Check @sc_fin_unit.
Check @sc_unlift.
Check @sc_fin_ext.
Check @sc_fin_ump.
Check @StoneCech_finite.
Check @StoneCech_finite_obj.
Check @StoneCech_finite_unit.
Check @sc_pt_cone.
Check @sc_pres_pt.
Check @sc_pt_const_med.
Check @sc_pres_map.
Check @CompHaus_Forget_PreservesImageLimit.
Check @taut_sols.
Check @GAFT_CompHaus_only_complete.
Check @unit_injective_of_separated.
Check @separated_of_unit_injective.
Check @sc_chi.
Check @unit_injective_of_dec.
Check @sc_bool_dec.
Check @StoneCech_finite_bool_injective.
Check @KSeparated.
Check @StoneCech_unit_injective_completely_regular.
Check @KSeparated_of_unit_injective.
Check @KSeparated_of_unit_injective_local.
Check @CompHaus_Incl_universal.
Check @CompHaus_Incl_universal_obj.
Check @KSeparated_self.
Check @StoneCech_unit_injective_at_CompHaus.
Check @KSeparated_of_unit_injective_local_at_CompHaus.

(* Instance/Top/StoneCech/Refutations.v: 33 names *)
Check @sc_pt_bool.
Check @sc_eval_pt.
Check @sc_eval_pt_resp.
Check @CompHaus_not_complete.
Check @ObjDecEq_of_IEM.
Check @CompHaus_not_complete_IEM.
Check @Top_not_complete.
Check @Top_not_complete_IEM.
Check @CompHaus_ArrowIndex_of_Top.
Check @CompHaus_not_complete_IEM_below.
Check @CompHaus_not_complete_IEM_above.
Check @KSet.
Check @sc_phi_map.
Check @large_universal_arrow_refuted.
Check @StoneCech_adjunction_refuted_IEM.
Check @StoneCech_adjunction_refuted_IEM_above.
Check @GAFT_CompHaus_IEM_vacuous.
Check @GAFT_CompHaus_IEM_vacuous_above.
Check @CompHaus_WellPowered.
Check @SAFT_CompHaus_Incl.
Check @SAFT_Incl_vacuous.
Check @SAFT_Incl_IEM_vacuous.
Check @SAFT_Incl_IEM_vacuous_below.
Check @big_inj.
Check @big_inj_injective.
Check @sc_yp_equiv.
Check @sc_yp_equiv_Equivalence.
Check @sc_YP.
Check @sc_yp_FinEnum.
Check @YP_CH.
Check @sc_yp_const.
Check @CompHaus_cogenerator_stable_DNE.
Check @CompHaus_point_separator_stable_DNE.
