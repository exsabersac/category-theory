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

(** * Probe: the measured boundaries of Construction/Product/Limit.v *)

(*
   本文件为测试：ProbeProductLimit418。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Instrument check *)

(* A name that is not in scope: if the harness were reporting [Fail]
   successes as failures, or vice versa, this line would say so. *)

Fail Check probe418_no_such_constant.

(** ** Guards: every constant a negative names, named outside every [Fail] *)

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

(** ** N1, N2: the binary pairing against its projections *)

Section BinaryRecords.

Context {J C D : Category}.
Context (K : J ⟶ C ∏ D).

(* Controls: apex and legs of the projected pairing ARE the first cone's. *)
Example probe418_ctrl_fst_apex (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K)) :
  vertex_obj[FCone Fst (prod_cone K N1 N2)] = vertex_obj[N1] := eq_refl.

Example probe418_ctrl_fst_leg (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K))
  (x : J) :
  cone_leg (FCone Fst (prod_cone K N1 N2)) x = cone_leg N1 x := eq_refl.

(* N1: CONVERSION — the whole record is not. *)
Fail Example probe418_n1 (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K)) :
  FCone Fst (prod_cone K N1 N2) = N1 := eq_refl.

(* N2: CONVERSION — no eta for [prod] on the apex. *)
Fail Example probe418_n2 (N : Cone K) :
  vertex_obj[prod_cone K (FCone Fst N) (FCone Snd N)] = vertex_obj[N]
  := eq_refl.

(* Control: the cone isomorphism the target uses instead, with apex
   isomorphism [(id, id)]. *)
Example probe418_ctrl_prod_iso (N : Cone K) :
  to `1 (prod_cone_iso K N) = (id, id) := eq_refl.

End BinaryRecords.

(** ** N3: the family pairing against its projections *)

Section FamilyRecords.

Context {I : Type} {D : I → Category} {J : Category}.
Context (K : J ⟶ PiCat D).

(* Controls: apex AND legs agree on the nose, by function eta. *)
Example probe418_ctrl_pi_apex (N : Cone K) :
  vertex_obj[pi_cone K (fun i => FCone (PiCat_Proj D i) N)] = vertex_obj[N]
  := eq_refl.

Example probe418_ctrl_pi_leg (N : Cone K) (x : J) :
  cone_leg (pi_cone K (fun i => FCone (PiCat_Proj D i) N)) x = cone_leg N x
  := eq_refl.

(* N3: CONVERSION — the whole record is not; only the coherence differs. *)
Fail Example probe418_n3 (N : Cone K) :
  pi_cone K (fun i => FCone (PiCat_Proj D i) N) = N := eq_refl.

End FamilyRecords.

(** ** N4: the opposite of a set-indexed product is not a set-indexed product
       of opposites on the nose *)

(* Control: for the binary product it is — Construction/Product.v's
   [Product_Opposite], restated. *)
Example probe418_ctrl_binary_op (C D : Category) :
  Opposite (C ∏ D) = (Opposite C ∏ Opposite D) := eq_refl.

(* N4: CONVERSION. *)
Fail Example probe418_n4 {I : Type} (D : I → Category) :
  Opposite (PiCat D) = PiCat (fun i => Opposite (D i)) := eq_refl.

(** ** N5: the two projections' preservation witnesses are not interchangeable *)

Section Handedness.

Context {J C D : Category}.
Context (K : J ⟶ C ∏ D).

(* Controls. *)
Check (Fst_PreservesLimitCone K : PreservesLimitCone K Fst).
Check (Snd_PreservesLimitCone K : PreservesLimitCone K Snd).

(* N5: CONVERSION. *)
Fail Check (Fst_PreservesLimitCone K : PreservesLimitCone K Snd).

End Handedness.

(** ** N6: the universe boundary, with the functor and the cone as controls *)

Section UniverseBoundary.

Universes jo jh co ch do dh.
Constraint jh < ch.
Constraint jh < dh.

Context (Ju : Category@{jo jh jh}).
Context (Cu : Category@{co ch ch}).
Context (Du : Category@{do dh dh}).
Context (K : Ju ⟶ Cu ∏ Du).

(* Controls: the diagram, a cone over it, and the projection ALONE are all
   formable at these levels — so neither [K] nor [Fst] is the donor. *)
Check K.
Check (@Cone Ju (Cu ∏ Du) K).
Check (@Fst Cu Du).

(* N6: UNIVERSE — the donor: [Compose] wants one hom level for all three
   categories. *)
Fail Check (Fst ◯ K).

(* Inherited: [prod_cone] mentions that composite in its type. *)
Fail Check (prod_cone K).

End UniverseBoundary.

(** ** N7: the index boundary of the [PiCat] half, with [PiCat] itself as the
       control *)

Section IndexBoundary.

Universes pi_i pi_h.
Constraint pi_h < pi_i.

Context (Iu : Type@{pi_i}).
Context (Du : Iu -> Category@{pi_i pi_h pi_h}).

(* Control: the set-indexed product itself is formable at an index declared
   strictly above the factors' homs — its block carries bounds only. *)
Check (PiCat Du).

(* N7: UNIVERSE — the donor: [PiCat_Proj]'s binder [C : I → Category@{u1 u u}]
   puts the index at the factors' hom-and-proof level. *)
Fail Check (PiCat_Proj Du).

(* Inherited: [PiCat_Complete] reads [D : I → Category@{u5 u u}] in its
   BINDER with no block equation, and is refused at its [Du] argument. *)
Fail Check (@PiCat_Complete Iu Du).

End IndexBoundary.
