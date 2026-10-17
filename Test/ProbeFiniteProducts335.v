(*
   本文件为测试：ProbeFiniteProducts335。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Coq.Vectors.Fin.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Instance.Coq.
Require Import Category.Structure.Limit.Product.Finite.

Generalizable All Variables.

(* 相关说明。 （已译） *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

Section Conversions.

Context {C : Category}.
Context (CP : @Cartesian C) (T : @Terminal C).
Context (x y z : C) (f1 : Fin.t 1 → C) (f2 : Fin.t 2 → C).

(* 相关说明。 （已译） *)

Fail Definition probe_fin_prod_one :
  @fin_prod C CP T 1 f1 = f1 Fin.F1 := eq_refl.

(* 相关说明。 （已译） *)

Fail Definition probe_fin_prod_two :
  @fin_prod C CP T 2 f2 = (f2 Fin.F1 × f2 (Fin.FS Fin.F1))%object := eq_refl.

(* 相关说明。 （已译） *)

Fail Definition probe_roundtrip_product_obj :
  @product_obj C (HasFiniteProducts_Cartesian
                    (Cartesian_Terminal_HasFiniteProducts CP T)) x y
  = (x × y)%object := eq_refl.

(* 相关说明。 （已译） *)

Fail Definition probe_roundtrip_cartesian :
  HasFiniteProducts_Cartesian (Cartesian_Terminal_HasFiniteProducts CP T)
  = CP := eq_refl.

(* 相关说明。 （已译） *)

Fail Definition probe_roundtrip_terminal :
  HasFiniteProducts_Terminal (Cartesian_Terminal_HasFiniteProducts CP T)
  = T := eq_refl.

(*
   本节说明 ProbeFiniteProducts335 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Definition probe_roundtrip_whole :
  Cartesian_Terminal_HasFiniteProducts
    (HasFiniteProducts_Cartesian
       (Cartesian_Terminal_HasFiniteProducts CP T))
    (HasFiniteProducts_Terminal
       (Cartesian_Terminal_HasFiniteProducts CP T))
  = Cartesian_Terminal_HasFiniteProducts CP T := eq_refl.

(* * ** Negative 7 (CONVERSION): right fold left fold differ

 This why [awodey_fold_iso] 同构 nothing stronger. （已译） *)

Fail Definition probe_right_vs_left_fold :
  @fin_prod C CP T 3 (fin3 x y z) = awodey_prod CP x y z := eq_refl.

End Conversions.

(* 相关说明。 （已译） *)

Check @fin_prod.
Check @fin_proj.
Check @fin3.
Check @awodey_prod.
Check @awodey_fold_iso.
Check @HasFiniteProducts.
Check @HasFiniteProducts_Cartesian.
Check @HasFiniteProducts_Terminal.
Check @Cartesian_Terminal_HasFiniteProducts.
Check @product_obj.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Positives.

Context {C : Category}.
Context (CP : @Cartesian C) (T : @Terminal C).
Context (x y : C) (n : nat) (f : Fin.t n → C).

Example probe_class_returns_the_fold :
  @finite_product C (Cartesian_Terminal_HasFiniteProducts CP T) n f
  = @fin_prod C CP T n f := eq_refl.

Example probe_class_returns_the_projections :
  @finite_product_proj C (Cartesian_Terminal_HasFiniteProducts CP T) n f
  = @fin_proj C CP T n f := eq_refl.

Example probe_terminal_obj_is_recovered :
  @terminal_obj C
    (HasFiniteProducts_Terminal (Cartesian_Terminal_HasFiniteProducts CP T))
  = @terminal_obj C T := eq_refl.

Example probe_padded_product_is_what_it_is :
  @product_obj C (HasFiniteProducts_Cartesian
                    (Cartesian_Terminal_HasFiniteProducts CP T)) x y
  = (x × (y × 1))%object := eq_refl.

End Positives.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section UniverseIdentification.

Universe uo uh up.
Constraint uh < up.

Context (C : Category@{uo uh up}).

(* 相关说明。 （已译） *)
Check (fun x y : C => x ~{C}~> y).

Fail Check (@Cartesian C).
Fail Check (@Terminal C).
(*
   本节说明 ProbeFiniteProducts335 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (fun (A : Type) (f : A → C) (p : C)
                (pr : ∀ a, p ~{C}~> f a) =>
              @IsIndexedProduct C A f p pr).

End UniverseIdentification.

(* 相关说明。 （已译） *)

Check @Cartesian.
Check @Terminal.
Check @IsIndexedProduct.

(* 相关说明。 （已译） *)

Check @fin_IsIndexedProduct.
Check @Cartesian_Terminal_HasFiniteProducts.
Check @HasFiniteProducts_iff.
Check @iprod_unique_iso.
Check @fin_prod_unique_iso.
Check @awodey_IsIndexedProduct.
Check @fin_zero_IsTerminalObj.
Check @fin_two_IsCartesianProduct.
Check @fin_coprod.
Check @HasFiniteCoproducts.
(*
   本节说明 ProbeFiniteProducts335 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check Cocartesian_Initial_HasFiniteCoproducts.

(*
   本节说明笛卡尔、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
