Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Coproduct.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Free.Quiver.Coproduct.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Mon.Coproduct.
Require Import Category.Instance.Roster.

Generalizable All Variables.
Local Open Scope category_scope.

(* 相关说明。 （已译） *)

(*
   本文件为测试：ProbeCoproduct328。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Instrument check *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(*
   本节说明 ProbeCoproduct328 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition probe_pos_mon_sets_is_the_same_term :
  Mon_Sets = @Mon Sets Sets_Product_Monoidal := eq_refl.

Check (_ : @Cocartesian Mon_Sets).

Check (Mon_Sets_Cocartesian).

Check (Mon_Sets_Initial).

(*
   本节说明 ProbeCoproduct328 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section MonNegatives.

Context (A B Q : @Mon Sets Sets_Product_Monoidal).
Context (f : A ~> Q) (g : B ~> Q).

Fail Definition probe_mon_beta_morphism :
  fp_merge A B Q f g ∘ fp_injl A B = f := eq_refl.

Fail Definition probe_mon_eta_morphism :
  fp_merge A B (FreeProd A B) (fp_injl A B) (fp_injr A B)
    = @id (@Mon Sets Sets_Product_Monoidal) (FreeProd A B) := eq_refl.

End MonNegatives.

(*
   本节说明 ProbeCoproduct328 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (fun (C : Category) (x : obj[C]) => @id C x).

(* Positive controls naming Instance/Mon/Coproduct.v's own constants. *)
Check fp_beta_l_fun.
Check fp_beta_l_strict.
Check fp_merge_inl.
Check coprod_is_FreeProd.
Check fp_injl.
Check fp_injr.
Check FreeProd.
Check fp_merge.

(* 相关说明。 （已译） *)
Check fp_injections_Monic.
Check fp_inl_injective.
Check fp_generators_do_not_commute.
Check fp_word_not_left.

(*
   本节说明函子、hom、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section QuiverNegatives.

Context (C D : Category).

Fail Definition probe_quiver_edges_strict :
  @edges (QuiverOfCat (C ∐ D))
    = @edges (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D)) := eq_refl.

Fail Definition probe_quiver_record_strict :
  QuiverOfCat (C ∐ D)
    = QuiverCoprod (QuiverOfCat C) (QuiverOfCat D) := eq_refl.

(* 相关说明。 （已译） *)
Fail Definition probe_quiver_edgeset_ll (a b : obj[C]) :
  @edgeset (QuiverOfCat (C ∐ D)) (Datatypes.inl a) (Datatypes.inl b)
    = @edgeset (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D))
        (Datatypes.inl a) (Datatypes.inl b) := eq_refl.

(* 相关说明。 （已译） *)
Check (fun (G : Quiver) (x y : nodes) => @edgeset G x y).

Definition probe_pos_quiver_edges_ll (a b : obj[C]) :
  @edges (QuiverOfCat (C ∐ D)) (Datatypes.inl a) (Datatypes.inl b)
    = @edges (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D))
        (Datatypes.inl a) (Datatypes.inl b) := eq_refl.

End QuiverNegatives.

(*
   本节说明同构、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明 ProbeCoproduct328 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (fun (G : Quiver) => @edges G).

Check QuiverOfCat_Coproduct_nodes.
Check QuiverOfCat_Coproduct_edges_ll.
Check QuiverOfCat_Coproduct_edges_lr.
Check QuiverOfCat_Coproduct_iso.
Check QuiverCoprod.
Check QuiverOfCat.

(* 相关说明。 （已译） *)
Check QuiverCopair_Inl.
Check QuiverCopair_Inr.

(* 相关说明。 （已译） *)
Check QuiverCopair_respects.
Check QuiverCopair_unique.

(* 相关说明。 （已译） *)
Check QuiverCategory_Cocartesian.
Check Coprod_is_QuiverCoprod.

(* 相关说明。 （已译） *)
Check coprod_no_cross_edge.
Check injections_not_equivalent.
Check quiver_coprod_no_edge_lr.
