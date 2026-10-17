Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Subobject.
Require Import Category.Structure.Complete.
Require Import Category.Structure.WellPowered.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Adjunction.SAFT.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   nLab:      https://ncatlab.org/nlab/show/adjoint+functor+theorem

   本文件给出特殊伴随函子定理相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition SubobjectIndex_of_WellPoweredAt {C : Category} {x : C}
  (W : WellPoweredAt x) : SubobjectIndex x :=
  {| sub_index := wp_index W ;
     SAFT.sub_dom   := fun i => Subobject.sub_dom (wp_to W i) ;
     SAFT.sub_mono  := fun i => Subobject.sub_mono (wp_to W i) ;
     sub_monic := fun i => Subobject.sub_is_monic (wp_to W i) |}.

Definition WellPowered_SubobjectIndex@{o h w s t}
  {C : Category@{o h h}} (W : WellPowered@{o h w s t} C) :
  ∀ x : C, SubobjectIndex x :=
  fun x => SubobjectIndex_of_WellPoweredAt (W x).

(* 相关说明。 （已译） *)
Definition SAFT_of_WellPowered@{cobj dobj h w s t u +}
  {C : Category@{cobj h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h cobj} C)
  (cont : @PreservesImageLimit@{cobj h dobj h _ h u h} C D U)
  (G : Cogenerator C) (W : WellPowered@{cobj h w s t} C)
  (cover : SubobjectCover@{_ w h u h dobj cobj h} U comp G
             (WellPowered_SubobjectIndex W)) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT U comp cont G (WellPowered_SubobjectIndex W) cover.
