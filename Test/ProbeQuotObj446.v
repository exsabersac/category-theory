Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Subobject.Quotient.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.

Generalizable All Variables.

(*
   本文件为测试：ProbeQuotObj446。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Instrument check *)

Fail Check quot_obj_theory_446_no_such_constant.

(* * ** Positive controls: every 常值 negatives depend on （已译） *)

Check @QuotObj.
Check @SubObj.
Check @quot_cod.
Check @quot_epi.
Check @quot_le.
Check @quot_meet.
Check @quot_join.
Check @monic_op_iff_epic.
Check @Epic.
Check @Monic.
Check @Isomorphism.
Check @to.
Check @Cartesian.
Check @HasPushouts.
Check @HasImages.
Check @quot_equiv_iff_iso.
Check @quot_equiv_of_cod_iso.
Check @quot_le_unfold.
Check @quot_equiv_unfold.
Check @QuotObj_op_is_SubObj.

(* 相关说明。 （已译） *)

Section Readbacks.

Context {C : Category}.
Context {x : C}.

(* F1: quotient 对象 opposite 范畴 ARE subobjects, the
 nose, because C^op^op C reflexivity. （已译） *)
Example p446t_op_is_sub : @QuotObj (C^op) x = @SubObj C x := eq_refl.

(* 相关说明。 （已译） *)
Example p446t_le_unfold (q r : QuotObj x) :
  quot_le q r
  = { k : quot_cod r ~> quot_cod q & k ∘ quot_epi r ≈ quot_epi q }
  := eq_refl.

(* 相关说明。 （已译） *)
Check (fun q r : QuotObj x => quot_meet q r).

End Readbacks.

(** ** Negatives *)

Section Negatives.

Context {C : Category}.
Context {x y : C}.

(* N2 -- CONVERSION. Dropping ^op left F1: quotient 对象
 C NOT subobjects C. "cannot unify QuotObj x SubObj x". （已译） *)
Fail Definition n2 : @QuotObj C x = @SubObj C x := eq_refl.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition n3 (q r : QuotObj x) :
  (q ≈ r) = { i : quot_cod q ≅ quot_cod r & to i ∘ quot_epi q ≈ quot_epi r }
  := eq_refl.

(*
   本节说明 ProbeQuotObj446 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition n4 (q r : QuotObj x) :
  quot_le q r
  = { k : quot_cod q ~> quot_cod r & k ∘ quot_epi q ≈ quot_epi r }
  := eq_refl.

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition n5 (q r : QuotObj x) : QuotObj x := quot_meet q r.

(*
   本节说明 ProbeQuotObj446 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition n6 (f : x ~> y) : @Epic (C^op) y x f → @Monic C x y f :=
  fst (monic_op_iff_epic f).

End Negatives.

Section NoCoimages.

Context {C : Category}.
Context `{@Cartesian C}.
Context {x : C}.

(*
   本节说明 ProbeQuotObj446 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition n7 (q r : QuotObj x) : QuotObj x := quot_join q r.

End NoCoimages.
