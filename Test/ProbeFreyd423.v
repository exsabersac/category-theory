(*
   本文件为测试：ProbeFreyd423。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Size.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Quotient.
Require Import Category.Structure.Thin.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Product.Limit.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Limit.
Require Import Coq.Logic.Eqdep_dec.
Require Import Category.Structure.Complete.Freyd.

Generalizable All Variables.

(* instrument: the refutation keyword is live *)
Fail Check probe423_absent_name.

(* 相关说明。 （已译） *)

Section SetPin.

Universe uo uh.
Constraint Set < uh.

Context {C : Category@{uo uh uh}} (comp : @Complete C) (fam : TotalMor C → C).

(*
   本节说明（余）极限、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (@limit_is_indexed_product C (TotalMor C) fam
         (comp _ (@DiscreteCat_Functor (TotalMor C) C fam))).

(* control: annotated route Freyd.v at same 范畴 （已译） *)
Check (complete_iprod comp fam).
Check (complete_iprod_obj comp fam).

End SetPin.

(** ** B: the dual's record literal *)

Section OpLiteral.

Context {C : Category} (AI : ArrowIndex C).

(* 相关说明。 （已译） *)
Fail Definition p423_op_literal : ArrowIndex (C^op) :=
  {| ai_index   := ai_index AI
   ; ai_enc     := fun x y h => ai_enc AI h
   ; ai_dec     := fun x y m d => ai_dec AI m d
   ; ai_dec_enc := fun x y h d => ai_dec_enc AI h d |}.

(* control: the explicit constructor at [C^op] *)
Check (ArrowIndex_op AI).

(* readback: the dual is an involution at [eq_refl] *)
Example p423_op_round : ArrowIndex_op (ArrowIndex_op AI) = AI := eq_refl.

End OpLiteral.

(* * ** C: positive controls — 假设 not vacuous, the
 constructive wall injection （已译） *)

(* every category with decidable object equality carries an [ArrowIndex] *)
Check (@canonical_ArrowIndex).

(* 相关说明。 （已译） *)
Check (@fr_inj_injective).

(* Theory/Size.v's [Small] products over 范畴's own arrows
 coexist: no universe wall （已译） *)
Definition p423_small_and_products {C : Category} `{@Small C}
  (HP : HasIndexedProducts C) (fam : TotalMor C → C) : C :=
  indexed_product fam.

(** ** D: the headline statements *)

Check (@freyd_no_separated_pair).
Check (@freyd_thin).
Check (@small_complete_is_thin).
Check (@small_cocomplete_is_thin).
Check (@complete_has_glbs).
Check (@complete_Proset_Complete).

(** ** Guard block *)

Check @ArrowIndex.
Check @ai_index.
Check @ai_enc.
Check @ai_dec.
Check @ai_dec_enc.
Check @ArrowIndex_op.
Check @ObjDecEq.
Check @canonical_ArrowIndex.
Check @DecHom.
Check @DecHom_op.
Check @freyd_thin_canonical.
Check @freyd_thin_dual.
Check @fr_inj.
Check @complete_iprod.
Check @complete_iprod_obj.
Check @complete_iprod_proj.
Check @limit_is_indexed_product.
Check @DiscreteCat_Functor.
Check @DiscreteCat_Functor'.
Check @Complete.
Check @TotalMor.
Check @Small.
Check @HasIndexedProducts.
Check @indexed_product.
