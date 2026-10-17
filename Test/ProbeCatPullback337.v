(*
   本文件为测试：ProbeCatPullback337。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Category.Monoid.
Require Import Category.Construction.Arrow.
Require Import Category.Construction.Comma.Diagram.
Require Import Category.Construction.Slice.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.One.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Structure.Pullback.
Require Import Category.Instance.Cat.Pullback.

Generalizable All Variables.

(* 相关说明。 （已译） *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section UniverseBoundary.

Universe ao bo co h.
Constraint ao < bo.
Constraint bo < co.

(* Control: construction formable three 对象 universes
 declared strictly apart. （已译） *)
Check (fun (A : Category@{ao h h}) (B : Category@{bo h h})
           (C : Category@{co h h}) (F : A ⟶ C) (G : B ⟶ C) =>
         FibreProduct F G).

(* 相关说明。 （已译） *)
Check (fun (A : Category@{ao h h}) (B : Category@{bo h h})
           (C : Category@{co h h}) (F : A ⟶ C) (G : B ⟶ C) =>
         (FP_fst F G, FP_snd F G)).

(* Control: so is the hypothesis. *)
Check (fun (C : Category@{co h h}) => ObjUIP C).

(* NEGATIVE 1. *)
Fail Check (fun (A : Category@{ao h h}) (B : Category@{bo h h})
                (C : Category@{co h h}) (F : A ⟶ C) (G : B ⟶ C)
                (uip : ObjUIP C) =>
              FibreProduct_IsPullback F G uip).

End UniverseBoundary.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section TriangleData.

Context {A B C Q : Category} (F : A ⟶ C) (G : B ⟶ C).
Context (q1 : Q ⟶ A) (q2 : Q ⟶ B).
Context (Hsq : F ∘[StrictCat] q1 ≈[StrictCat] G ∘[StrictCat] q2).

(* Control: 对象 action [q1]'s nose. （已译） *)
Definition probe_fp_obj (z : Q) :
  fobj[FP_fst F G ◯ FP_med F G q1 q2 Hsq] z = fobj[q1] z := eq_refl.

(* Control: so is the arrow action. *)
Definition probe_fp_map (z w : Q) (f : z ~> w) :
  fmap[FP_fst F G ◯ FP_med F G q1 q2 Hsq] f = fmap[q1] f := eq_refl.

(* Control: the second triangle's data likewise. *)
Definition probe_fp_obj_snd (z : Q) :
  fobj[FP_snd F G ◯ FP_med F G q1 q2 Hsq] z = fobj[q2] z := eq_refl.

(* NEGATIVE 2. *)
Fail Definition probe_fp_record :
  FP_fst F G ◯ FP_med F G q1 q2 Hsq = q1 := eq_refl.

(* Control: what IS available at that strength, in [StrictCat]'s own
   hom-setoid. *)
Check (FP_med_fst F G q1 q2 Hsq).
Check (FP_med_snd F G q1 q2 Hsq).

End TriangleData.

(*
   本节说明拉回/推出、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SliceApex.

Context {C : Category} (c : C).

(* Control: leg's 对象 action, nose. （已译） *)
Definition probe_slice_obj (x : Slice C c) :
  fobj[Slice_Arrow c] x = ((`1 x, c); `2 x) := eq_refl.

(* NEGATIVE 3. *)
Fail Definition probe_slice_apex :
  Slice C c = FibreProduct (@Arrow_cod C) (@Diagonal C _1 c) := eq_refl.

End SliceApex.

(*
   本节说明 ProbeCatPullback337 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* Control: at cospan whose two legs agree, pair [eq_refl] an
 对象. （已译） *)
Definition probe_ib_agree : obj[FibreProduct IBtrue IBtrue] :=
  ((ttt, ttt); eq_refl).

(* NEGATIVE 4. *)
Fail Definition probe_ib_empty : obj[FibreProduct IBtrue IBfalse] :=
  ((ttt, ttt); eq_refl).

(* Control: the same fact, proved rather than probed. *)
Check IB_FibreProduct_empty.
Check IB_iso.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Check FibreProduct.
Check FP_fst.
Check FP_snd.
Check FP_commutes_strict.
Check FP_commutes_cat.
Check FP_med.
Check FP_med_unique.
Check FibreProduct_IsPullback.
Check FibreProduct_Pullback.
Check ObjUIP_of_ObjDecEq.
Check FibreProduct_IsPullback_dec.
Check StrictCat_HasPullbacks.

(** 本节：The [Cat] side: candidate refuted, refutation narrow
 -- same cospan does have [Cat] pullback. （已译） *)

Check FibreProduct_not_Cat_pullback.
Check point_cospan_Cat_IsPullback.
Check point_cospan_square.
Check one_functors_equiv.

(** Necessity of the hypothesis. *)

Check FP_uniqueness_forces_UIP.
Check loop_functor.
Check loop_functor_fst.
Check loop_functor_snd.

(** The comma half. *)

Check Slice_Arrow.
Check Slice_commutes.
Check Slice_IsPullback.
Check Coslice_Arrow.
Check Coslice_commutes.
Check Coslice_IsPullback.
Check slice_arrow_reflect.
Check coslice_arrow_reflect.

(*
   本节说明 ProbeCatPullback337 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Check (fun (C : Category) (c : C) => (@Slice C c, @Arrow_cod C,
                                      @Diagonal C _1 c)).
Check IBtrue.
Check IBfalse.
Check IB.
