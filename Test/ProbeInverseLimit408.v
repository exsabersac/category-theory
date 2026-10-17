Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Structure.Terminal.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Construction.Chain.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Cone.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Streams.
Require Import Category.Instance.Sets.InverseLimit.

Generalizable All Variables.
Open Scope category_scope.

(* 相关说明。 （已译） *)

(*
   本文件为测试：ProbeInverseLimit408。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Fail Check probe408_no_such_constant.

(* * ** Guard block: every 常值 negatives name, outside every Fail （已译） *)

Check @tower_obj.
Check @Sets_limit_obj.
Check @cone_apex.
Check @tower_iso.
Check @Sets_tower_limit.
Check @Sets_tower_limit_iso_cone_limit.
Check @inverse_limit.
Check @Cochain.
Check @Chain.
Check @Omega.
Check @Diagonal.
Check @cochain_inverse_limit.
Check @stream_to_tower.
Check @StreamTower.
Check @tower_compat.
Check @tower_compat_all.
Check @tower_proj.

(* * ** (1) CONVERSION: two presentations not one 对象 （已译） *)

(* The tower 对象 carries compatibility at STEPS; [Sets_limit_obj]
 carries it at every arrow. They isomorphic ([tower_iso]) not
 convertible. （已译） *)
Fail Definition neg_tower_is_limit_obj (F : Omega^op ⟶ Sets) :
  tower_obj F = Sets_limit_obj F := eq_refl.

(* The control: 同构 file actually delivers. （已译） *)
Check (fun F : Omega^op ⟶ Sets => tower_iso F).

(* * ** (2) CONVERSION: nor tower 对象 cone set （已译） *)

Fail Definition neg_tower_is_cone_apex (F : Omega^op ⟶ Sets) :
  tower_obj F = cone_apex F := eq_refl.

Check (fun F : Omega^op ⟶ Sets => Sets_tower_limit_iso_cone_limit F).

(* 相关说明。 （已译） *)

(* A plain has-type mismatch: no [cannot unify], no universe clause. *)
Fail Definition neg_wrong_variance (X : obj[Sets]) : obj[Sets] :=
  inverse_limit (Diagonal Omega X).

(* The control: OPPOSITE shape what [inverse_limit] 所消耗, and
 it exactly 常值 tower library file's section (G). （已译） *)
Check (fun X : obj[Sets] => inverse_limit (Diagonal (Omega^op) X)).

(* 相关说明。 （已译） *)

Section CochainPin.

Universes co ch.
Constraint Set < ch.

(* [Cochain@{u u0}] declared over [C : Category@{u0 Set Set}] -- hom AND
 证明 pinned literal [Set] -- so it refused at [Sets] whose
 hom-and-证明 level declared strictly above [Set]. （已译） *)
Fail Definition neg_cochain_above_Set
  (G : Sets@{ch co} ⟶ Sets@{ch co}) : Omega^op ⟶ Sets@{ch co} := Cochain G.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check Sets@{ch co}.
Check (Sets@{ch co} ⟶ Sets@{ch co}).
Check Omega@{ch co co}.
Check (fun (T : @Terminal (Opposite Sets@{ch co}))
           (G : Sets@{ch co} ⟶ Sets@{ch co}) => @Chain Sets@{ch co} T G).

End CochainPin.
