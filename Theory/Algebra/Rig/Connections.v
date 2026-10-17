Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Monad.Graded.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.

Generalizable All Variables.

(*
   本文件给出不同代数结构之间的联系与比较。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Example Bool_Rig_carrier_AndGrade : carrier (rig_setoid Bool_Rig) = grade AndGrade
  := eq_refl.
Example Bool_Rig_one_AndGrade : rig_one Bool_Rig = gunit AndGrade := eq_refl.
Example Bool_Rig_mul_AndGrade : rig_mul Bool_Rig = gmul AndGrade := eq_refl.

(* * ** Nat_Rig 对象-level shadow FinSet （已译） *)

(* The coproduct 对象 FinSet rig addition, nose. （已译） *)
Example Nat_Rig_add_FinSet_coproduct (m n : nat) :
  @product_obj _ FinSet_Cocartesian m n = rig_add Nat_Rig m n := eq_refl.

(* The product 对象 FinSet rig multiplication, nose. （已译） *)
Example Nat_Rig_mul_FinSet_product (m n : nat) :
  @product_obj _ FinSet_Cartesian m n = rig_mul Nat_Rig m n := eq_refl.

(* 相关说明。 （已译） *)
Example Nat_Rig_zero_FinSet : rig_zero Nat_Rig = 0%nat := eq_refl.
Example Nat_Rig_one_FinSet : rig_one Nat_Rig = 1%nat := eq_refl.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition CMon_EndRig (M : CMonObject) : RigObject :=
  EndRig CMon_Preadditive M.
