(*
   本文件为测试：ProbeAFTNecessity444。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Size.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Structure.UniversalProperty.
Require Import Category.Structure.UniversalProperty.Terminal.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.Representability.Sets.
Require Import Category.Structure.Thin.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Limit.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Category.Adjunction.GAFT.Necessity.
Require Import Category.Instance.Ordinal.Large.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Limit.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Instance.Powerset.

Generalizable All Variables.

(* 相关说明。 （已译） *)
Fail Check probe444_absent_name.

(* 相关说明。 （已译） *)

Check SmallOrd_op_Complete.
Check SmallOrd_self_limit.
Check SmallOrd_no_greatest.
Check SmallOrd_op_not_large_complete.

(* 相关说明。 （已译） *)

(*
   本节说明 ProbeAFTNecessity444 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (Complete_Initial SmallOrd_op_Complete).

(* 相关说明。 （已译） *)
Fail Check (Complete_Initial Sets_Complete).
Fail Check (Complete_Initial Grp_Complete).
Fail Check (Complete_Initial Ab_Complete).

(*
   本节说明 ProbeAFTNecessity444 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Definition p444_boom : False :=
  SmallOrd_op_not_large_complete SmallOrd_op_Complete.

(* 相关说明。 （已译） *)

Section ThinWitness.
Context (X : SetoidObject).
(* 相关说明。 （已译） *)
Check (Complete_Initial (Subsets_Complete (X:=X))).
End ThinWitness.

(** ** Guard block *)

Check @ConstOne.
Check @ConstOne_continuous.
Check @ConstOne_representable_iff_initial.
Check @ConstOne_not_representable.
Check @Complete_Initial.
(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check Category.Adjunction.GAFT.Necessity.Initial_of_limit_id.
Check @SmallShapeComplete.
Check @SmallOrd.
Check @ole.
Check @ojoin.
Check @SmallOrd_op_Proset.
Check @Subsets_Complete.
