(*
   本文件为测试：ProbeMatrix336。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Coq.Vectors.Fin.
Require Import Coq.Logic.Eqdep_dec.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Bicartesian.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Biproduct.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.Semiadditive.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Limit.Product.Finite.
Require Import Category.Instance.Coq.
Require Import Category.Structure.Bicartesian.Matrix.

Generalizable All Variables.

(* 相关说明。 （已译） *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(*
   本节说明 ProbeMatrix336 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section KroneckerDiagonal.

Context {C : Category} (Z : @ZeroObject C) (fam : Fin.t 2 → C).

Fail Definition probe_kron_diag_computes :
  @kron C Z (Fin.t 2) fam Fin.eq_dec Fin.F1 Fin.F1 = id := eq_refl.

End KroneckerDiagonal.

(*
   本节说明 ProbeMatrix336 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section BinaryComparison.

Context {C : Category} (Z : @ZeroObject C).
Context (CP : @Cartesian C) (CC : @Cocartesian C).
Context (x y : C).

Fail Definition probe_binary_can_is_can_comparison :
  @binary_can C Z CP CC x y = can_comparison x y := eq_refl.

End BinaryComparison.

(* 相关说明。 （已译） *)

Check @kron.
Check @kron_diag.
Check @kron_off.
Check @binary_can.
Check @can_comparison.
Check @binary_can_is_can_comparison.
Check @Fin.eq_dec.

(*
   本节说明hom、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section UniverseMinimization.

Universe uo uh up.
Constraint uh < up.

Context (C : Category@{uo uh up}).

(* Controls: ambient vocabulary IS formable at these levels, so the
 rejection below about unannotated 定义 not about C. （已译） *)
Check (fun x y : C => x ~{C}~> y).
Check (fun (x y z : C) (f : x ~{C}~> y) (g : y ~{C}~> z) => g ∘ f).

(* Control: the SHIPPED, annotated [mat_entry] is formable here. *)
Check (fun (J K : Type) (g : J → C) (fm : K → C)
           (q p : C) (inj : ∀ j, g j ~{C}~> q)
           (proj : ∀ k, p ~{C}~> fm k) (u : q ~{C}~> p) (j : J) (k : K) =>
         @mat_entry C J K g fm q p inj proj u j k).

(*
   本节说明 ProbeMatrix336 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition mat_entry_unannotated {D : Category}
  {J K : Type} {g : J → D} {fm : K → D} {q p : D}
  (inj : ∀ j, g j ~{D}~> q) (proj : ∀ k, p ~{D}~> fm k)
  (u : q ~{D}~> p) (j : J) (k : K) : g j ~{D}~> fm k :=
  proj k ∘ u ∘ inj j.

Fail Check (fun (J K : Type) (g : J → C) (fm : K → C)
                (q p : C) (inj : ∀ j, g j ~{C}~> q)
                (proj : ∀ k, p ~{C}~> fm k) (u : q ~{C}~> p) (j : J) (k : K) =>
              @mat_entry_unannotated C J K g fm q p inj proj u j k).

End UniverseMinimization.

(* 相关说明。 （已译） *)

Check @mat_entry.
Check @mat_entry_unfold.

(* 相关说明。 （已译） *)

Check @matrix_ext.
Check @matrix_determined.
Check @matrix_mor.
Check @matrix_entry.
Check @matrix_ump.
Check @matrix_mor_entry.
Check @can_matrix.
Check @can_matrix_diag.
Check @can_matrix_off.
Check @can_matrix_unique.
Check @can_matrix_ump.
Check @indexed_inj_Section.
Check @indexed_inj_SplitMono.
Check @indexed_inj_Monic.
Check @inl_Section.
Check @inr_Section.
Check @inl_Monic.
Check @inr_Monic.
Check @fin_matrix.
Check @fin_matrix_entry.
Check @fin_matrix_ext.

(*
   本节说明 ProbeMatrix336 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Coproduct.

Example ab_inl_Section (x y : Ab) : Section (@inl Ab Ab_Cocartesian x y) :=
  inl_Section x y.

Example ab_inl_Monic (x y : Ab) : Monic (@inl Ab Ab_Cocartesian x y) :=
  inl_Monic x y.

Example ab_inr_Monic (x y : Ab) : Monic (@inr Ab Ab_Cocartesian x y) :=
  inr_Monic x y.

(*
   本节说明 ProbeMatrix336 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
