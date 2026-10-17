(*
   本文件为测试：ProbeKolmogorov372。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Kolmogorov.

(* 相关说明。 （已译） *)

Fail Check probe_372b_no_such_reference.

(*
   本节说明 ProbeKolmogorov372 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ProbeKolmogorovLevels.

Universes s o.
Constraint s < o.

Context (Xu : TopSpace@{o}).

Definition k372_probe_small_at_o (x y : Xu) : Type@{o} :=
  SameOpens@{s o} Xu x y.

Definition k372_probe_kq_setoid_at_o : SetoidObject@{o o} :=
  kq_setoid@{s o} Xu.

Fail Definition k372_probe_all_at_o (x y : Xu) : Type@{o} :=
  SameOpensAll Xu x y.

End ProbeKolmogorovLevels.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ProbeKolmogorovDonor.

Universes uo uh up.
Constraint uh < up.

Context (Cu : Category@{uo uh up}).
Context (xu yu : obj[Cu]).

Check (xu ~{Cu}~> yu).
Check (@id Cu xu).

Fail Check (@Subcategory Cu).

End ProbeKolmogorovDonor.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example k372_probe_unit_is_proj_strict (X : TopSpace) :
  t0_unit X = kolmogorov_proj X := eq_refl.

Example k372_probe_unit_is_proj_pointwise (X : TopSpace) (x : X) :
  continuous_map (t0_unit X) x
    = continuous_map (kolmogorov_proj X) x := eq_refl.

Lemma k372_probe_unit_is_proj_hom (X : TopSpace) :
  t0_unit X ≈ kolmogorov_proj X.
Proof. apply t0_unit_is_proj_hom. Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example k372_probe_kq_isopen_strict (X : TopSpace) (U : X → Type) :
  IsOpen (KolmogorovQuotient X) U = IsOpen X U := eq_refl.

Example k372_probe_kq_isopen_is_kq_open (X : TopSpace) (U : X → Type) :
  IsOpen (KolmogorovQuotient X) U = kq_open X U := eq_refl.

Example k372_probe_kq_carrier (X : TopSpace) :
  carrier (top_carrier (KolmogorovQuotient X))
    = carrier (top_carrier X) := eq_refl.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example k372_probe_quot_bool_strict :
  KolmogorovQuotient Bool_Discrete = Bool_Discrete := eq_refl.

Definition k372_probe_bool_iso :
  fobj[T0_reflector] (Incl Top T0_Subcategory Bool_Discrete_T0Space)
    ≅[T0Spaces] Bool_Discrete_T0Space := bool_reflect_iso.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Definition k372_probe_reflective_is_adjunction
  : T0_reflector ⊣ Incl Top T0_Subcategory :=
  T0_Reflective_in_Top.

Definition k372_probe_reflective_adj
  : T0_reflector ⊣ Incl Top T0_Subcategory :=
  reflective_adj T0_Reflective_in_Top.

Definition k372_probe_reflective_record : Reflective T0_Subcategory :=
  T0_Reflective_in_Top.

Definition k372_probe_reflective_full :
  Category.Construction.Subcategory.Full Top T0_Subcategory :=
  reflective_full T0_Reflective_in_Top.

(* * ** Controls naming every 常值 negatives mention （已译） *)

Check @SameOpens.
Check @SameOpensAll.
Check @SameOpensAll_SameOpens.
Check @IsT0.
Check @kq_setoid.
Check @kq_open.
Check @small_open_is_kq_open.
Check @KolmogorovQuotient.
Check @KolmogorovQuotient_T0.
Check @KolmogorovT0.
Check @kolmogorov_proj.
Check @kolmogorov_med.
Check @kolmogorov_universal.
Check @kolmogorov_universal_arrow.
Check @t0_unit.
Check @t0_unit_is_proj_hom.
Check @t0_reflect_iso.
Check @T0_reflector.
Check @T0_adj.
Check @T0_Subcategory.
Check @T0Spaces.
Check @T0_Full.
Check @T0_Incl_Full.
Check @T0_Incl_Faithful.
Check @T0_Reflective_in_Top.
Check @Bool_Discrete_T0.
Check @Bool_Discrete_T0Space.
Check @bool_reflect_iso.
Check @TwoPoint_Indiscrete_not_T0.
Check @Hausdorff_T0_nn.
Check @Tri_Top.
Check @Tri_Top_not_T0.
Check @tri_point_apart.
Check @tri_quot_keeps_point_apart.
Check @Tri_T0.
Check @Subcategory.
Check @Reflective.
Check @Sub.
Check @Incl.
Check @Top.
Check @TopSpace.
Check @IsOpen.
Check @Bool_Discrete.
Check @continuous_map.
Check @carrier.
Check @top_carrier.
Check @SetoidObject.
