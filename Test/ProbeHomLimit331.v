(*
   本文件为测试：ProbeHomLimit331。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Functor.Hom.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Limit.Cartesian.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Instance.Coq.
Require Import Category.Functor.Hom.Limit.

(* 相关说明。 （已译） *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(* * ** Negative 1 (TYPING): HomFrom's implicit 范畴 undeterminable （已译） *)

Fail Check (FCone (HomFrom unit) (coq_two_limit (Pick_Two bool nat))).

(* Positive controls naming negative's own constants. The EXPLICIT
 spelling what target ships, every 常值 rejected
 expression independently well-formed here. （已译） *)
Check coq_hom_bool_nat_limit.
Check (@FCone Two_Discrete Coq Sets (HomFrom unit)).
Check (HomFrom unit).
Check coq_two_limit.
Check (Pick_Two bool nat).
(* The repair, named: ascribing 对象 determines [HomFrom]'s implicit
 范畴, then FCone's own arguments may stay implicit. （已译） *)
Check (FCone (HomFrom (unit : obj[Coq])) (coq_two_limit (Pick_Two bool nat))).

(*
   本节说明 ProbeHomLimit331 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section AboveSet.

Universe uo uh.
Constraint Set < uh.

Context (C : Category@{uo uh uh}) (c : obj[C]) (fam : bool -> obj[C]).

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (@hom_IsIndexedProduct C c).
Check (@hom_IsCartesianProduct C c).

(* Control (b): discrete-diagram 函子 ALONE formable here. It
 always was; what used refused was COMBINATION below. （已译） *)
Check (@DiscreteCat_Functor bool C fam).

(* The repaired combination, kept as a positive control. *)
Check (fun N : Cone (@DiscreteCat_Functor bool C fam) => IsLimitCone N).

(* Control (c): [IsLimitCone] itself fine at ambient 范畴 when
 SHAPE not Set-pinned discrete one. （已译） *)
Check (fun (J : Category@{uo uh uh}) (K : J ⟶ C) (N : Cone K) =>
         IsLimitCone N).

End AboveSet.

(* 相关说明。 （已译） *)

Check hom_PreservesLimitCone.
Check hom_ContinuousFunctor.
Check hom_PreservesLimit.
Check hom_PreservesAllLimits.
Check hom_preserved_leg.
Check hom_preserved_mediator.
Check hom_med_commutes.
Check hom_med_unique.
Check hom_IsIndexedProduct.
Check hom_IsCartesianProduct.
Check HomFrom.
Check HomTo.
Check hom_to_is_op_hom_from.
Check cohom_ContinuousFunctor.
Check cohom_PreservesLimitCone.
Check cohom_colimit_to_limit.
Check cohom_IsIndexedProduct.
Check cohom_IsCartesianProduct.
Check cartesian_IsCartesianProduct.
Check coq_hom_product.
Check coq_hom_limit_cone.

(*
   本节说明 ProbeHomLimit331 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
