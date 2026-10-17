Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cartesian.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Product.Indexed.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Product.Limit.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   本文件为测试：ProbeProductLimit418。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Instrument check *)

(* 相关说明。 （已译） *)

Fail Check probe418_no_such_constant.

(* * ** Guards: every 常值 negative names, named outside every [Fail] （已译） *)

Check @prod_cone.
Check @prod_cone_iso.
Check @FCone.
Check @Fst.
Check @Snd.
Check @Compose.
Check @Cone.
Check @cone_leg.
Check @vertex_obj.
Check @pi_cone.
Check @PiCat.
Check @PiCat_Proj.
Check @PiCat_Complete.
Check @Opposite.
Check @Product.
Check @Product_Opposite.
Check @PreservesLimitCone.
Check @Fst_PreservesLimitCone.
Check @Snd_PreservesLimitCone.

(* 相关说明。 （已译） *)

Section BinaryRecords.

Context {J C D : Category}.
Context (K : J ⟶ C ∏ D).

(* 相关说明。 （已译） *)
Example probe418_ctrl_fst_apex (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K)) :
  vertex_obj[FCone Fst (prod_cone K N1 N2)] = vertex_obj[N1] := eq_refl.

Example probe418_ctrl_fst_leg (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K))
  (x : J) :
  cone_leg (FCone Fst (prod_cone K N1 N2)) x = cone_leg N1 x := eq_refl.

(* N1: CONVERSION — the whole record is not. *)
Fail Example probe418_n1 (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K)) :
  FCone Fst (prod_cone K N1 N2) = N1 := eq_refl.

(* 相关说明。 （已译） *)
Fail Example probe418_n2 (N : Cone K) :
  vertex_obj[prod_cone K (FCone Fst N) (FCone Snd N)] = vertex_obj[N]
  := eq_refl.

(* Control: cone 同构 target uses instead, apex
 同构 [(id, id)]. （已译） *)
Example probe418_ctrl_prod_iso (N : Cone K) :
  to `1 (prod_cone_iso K N) = (id, id) := eq_refl.

End BinaryRecords.

(* 相关说明。 （已译） *)

Section FamilyRecords.

Context {I : Type} {D : I → Category} {J : Category}.
Context (K : J ⟶ PiCat D).

(* 相关说明。 （已译） *)
Example probe418_ctrl_pi_apex (N : Cone K) :
  vertex_obj[pi_cone K (fun i => FCone (PiCat_Proj D i) N)] = vertex_obj[N]
  := eq_refl.

Example probe418_ctrl_pi_leg (N : Cone K) (x : J) :
  cone_leg (pi_cone K (fun i => FCone (PiCat_Proj D i) N)) x = cone_leg N x
  := eq_refl.

(* 相关说明。 （已译） *)
Fail Example probe418_n3 (N : Cone K) :
  pi_cone K (fun i => FCone (PiCat_Proj D i) N) = N := eq_refl.

End FamilyRecords.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Example probe418_ctrl_binary_op (C D : Category) :
  Opposite (C ∏ D) = (Opposite C ∏ Opposite D) := eq_refl.

(* N4: CONVERSION. *)
Fail Example probe418_n4 {I : Type} (D : I → Category) :
  Opposite (PiCat D) = PiCat (fun i => Opposite (D i)) := eq_refl.

(* 相关说明。 （已译） *)

Section Handedness.

Context {J C D : Category}.
Context (K : J ⟶ C ∏ D).

(* Controls. *)
Check (Fst_PreservesLimitCone K : PreservesLimitCone K Fst).
Check (Snd_PreservesLimitCone K : PreservesLimitCone K Snd).

(* N5: CONVERSION. *)
Fail Check (Fst_PreservesLimitCone K : PreservesLimitCone K Snd).

End Handedness.

(* * ** N6: universe boundary, 函子 cone controls （已译） *)

Section UniverseBoundary.

Universes jo jh co ch do dh.
Constraint jh < ch.
Constraint jh < dh.

Context (Ju : Category@{jo jh jh}).
Context (Cu : Category@{co ch ch}).
Context (Du : Category@{do dh dh}).
Context (K : Ju ⟶ Cu ∏ Du).

(* 相关说明。 （已译） *)
Check K.
Check (@Cone Ju (Cu ∏ Du) K).
Check (@Fst Cu Du).

(* N6: UNIVERSE — donor: [Compose] wants one hom level all three
 范畴. （已译） *)
Fail Check (Fst ◯ K).

(* Inherited: [prod_cone] mentions that composite in its type. *)
Fail Check (prod_cone K).

End UniverseBoundary.

(* 相关说明。 （已译） *)

Section IndexBoundary.

Universes pi_i pi_h.
Constraint pi_h < pi_i.

Context (Iu : Type@{pi_i}).
Context (Du : Iu -> Category@{pi_i pi_h pi_h}).

(* 相关说明。 （已译） *)
Check (PiCat Du).

(* N7: UNIVERSE — donor: [PiCat_Proj]'s binder [C : I → Category@{u1 u u}]
 puts index at factors' hom-and-证明 level. （已译） *)
Fail Check (PiCat_Proj Du).

(* Inherited: [PiCat_Complete] reads [D : I → Category@{u5 u u}] its
 BINDER no block equation, refused at [Du] 论元. （已译） *)
Fail Check (@PiCat_Complete Iu Du).

End IndexBoundary.
