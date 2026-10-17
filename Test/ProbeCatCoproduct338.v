(*
   本文件为测试：ProbeCatCoproduct338。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Coproduct.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Instance.Cat.
Require Import Category.Construction.Coproduct.Indexed.
Require Import Category.Instance.Cat.Coproduct.

Generalizable All Variables.

(** ** Instrument check

    A [Fail] that never fails would make every negative below vacuous. *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section BinderBoundary.

Universe uo uh up.
Constraint uh < up.

(* Control: the ANNOTATED construction is formable with the summands' hom
   and proof universes declared strictly apart. *)
Check (fun (I : Type) (C : I -> Category@{uo uh up}) => SigmaCat C).

(* Control: so is its injection, at the same levels. *)
Check (fun (I : Type) (C : I -> Category@{uo uh up}) (i : I) =>
         SigmaCat_inj C i).

(* The unannotated body, re-declared here so the negative is about the
   ANNOTATION and not about anything else in the file. *)
Definition sigma_obj_unann {I : Type} (C : I -> Category) : Type :=
  ∃ i : I, C i.

(* NEGATIVE 1. *)
Fail Check (fun (I : Type) (C : I -> Category@{uo uh up}) =>
              sigma_obj_unann C).

End BinderBoundary.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SetoidBoundary.

Universe vo vh vp.
Constraint vh < vp.

(* Control: the functor TYPE elaborates at separated levels. *)
Check (fun (C D : Category@{vo vh vp}) => (C ⟶ D)).

(* Control: so does a `Unique` over a hom-setoid of such a category. *)
Check (fun (C : Category@{vo vh vp}) (x y : C)
           (P : (x ~> y) -> Type) => @Unique _ (@homset C x y) P).

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check @Functor_Setoid.

(* NEGATIVE 2. *)
Fail Check (fun (C D : Category@{vo vh vp}) => @Functor_Setoid C D).

End SetoidBoundary.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Check @SigmaCat_IsIndexedCoproduct.
Check Cat_HasIndexedCoproducts.

Definition probe_pkg_obj {I : Type} (C : I -> Cat) :
  @indexed_coproduct Cat Cat_HasIndexedCoproducts I C = SigmaCat C
  := eq_refl.

Definition probe_pkg_inj {I : Type} (C : I -> Cat) (i : I) :
  @indexed_coproduct_inj Cat Cat_HasIndexedCoproducts I C i
    = SigmaCat_inj C i := eq_refl.

Definition probe_pkg_ump {I : Type} (C : I -> Cat) :
  @indexed_coproduct_ump Cat Cat_HasIndexedCoproducts I C
    = SigmaCat_IsIndexedCoproduct C := eq_refl.

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* Control: the isomorphism that DOES hold. *)
Check @SigmaBool_strict_iso.
Check @SigmaBool_iso.
Check @BoolFam.

(* NEGATIVE 3. *)
Fail Definition probe_bool_obj (C D : Category) :
  obj[SigmaCat (BoolFam C D)] = (obj[C] + obj[D])%type := eq_refl.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition probe_forall_encoding_inhabited
  (C : bool -> Category) (x : C true) (y : C false) :
  ∀ e : true = false, ob_cast C e x ~> y :=
  fun e => match (eq_ind true (fun b : bool => if b then True else False)
                          I false e) with end.

(* Contrast, from the target: the encoding actually used makes that hom
   EMPTY, which is the point. *)
Check @sigma_hom_cross_empty.
Check @bool_cross_empty_lr.
Check @bool_cross_empty_rl.

(** ** Positive controls for the headline artifacts *)

Check @SigmaCat.
Check @SigmaCat_inj.
Check @SigmaCat_case.
Check @SigmaCat_case_inj.
Check @SigmaCat_case_unique.
Check @SigmaCat_ump.
Check @ob_cast.
Check @mor_cast.

(** The hypothesis-free/hypothesis-bearing split, and the necessity
    theorem that makes the split principled rather than convenient. *)

Check @SigmaCat_inj_Full.
Check @sigma_inj_Full_forces_UIP.
Check @inj_Full_forces_UIP_at_One.
Check @SigmaCat_const_inj_Faithful.
Check @SigmaCat_inj_Faithful.
Check @Faithful_cancel.
Check @IdxUIP.

(** Non-vacuity. *)

Check @SigmaCat_empty_no_obj.
Check @SigmaCat_unit_iso.
Check @bool_summands_not_isomorphic.
Check @case_separates_summands.
Check @sigma_poly_unit_dec.

(*
   本节说明 ProbeCatCoproduct338 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
