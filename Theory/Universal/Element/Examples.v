Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Terminal.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Coq.Nat.
Require Import Category.Theory.Universal.Element.
Require Import Category.Theory.Universal.Element.Elements.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   本文件给出例子。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)
Definition nat_UniversalElement : UniversalElement Endos_Forget :=
  UniversalElement_of_Representable nat_succ_Representable.

(* Its object is the representing object, by conversion. *)
Example nat_ue_obj : @ue_obj Endos Endos_Forget nat_UniversalElement = NatSucc.
Proof. reflexivity. Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example nat_ue_elem : @ue_elem Endos Endos_Forget nat_UniversalElement = O.
Proof. reflexivity. Qed.

(* The general equation Nat.v's check instance, at this
 representation: universal element image 恒等. （已译） *)
Example nat_ue_is_image_of_id :
  @ue_elem Endos Endos_Forget nat_UniversalElement
    = transform (to nat_succ_represents) NatSucc (id{Endos}).
Proof. reflexivity. Qed.

(* Mac Lane's unique-factorization clause, at this instance: every element n
   of every [Endos]-object is reached from [O] by a unique endomorphism-
   preserving map out of (nat, S) -- which is iteration.  The general class
   supplies it; nothing here is proved. *)
Definition nat_ue_factor (y : Endos) (n : Endos_Forget y)
  : NatSucc ~{Endos}~> y :=
  unique_obj (@ue_universal Endos Endos_Forget nat_UniversalElement y n).

Example nat_ue_factor_at_zero (y : Endos) (n : Endos_Forget y) :
  fmap[Endos_Forget] (nat_ue_factor y n) O ≈ n.
Proof. exact (unique_property (@ue_universal _ _ nat_UniversalElement y n)). Qed.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition nat_Elements_Initial : @Initial (Elements Endos_Forget) :=
  Elements_Initial Endos_Forget
    (AUniversalElement_of_UniversalElement nat_UniversalElement).

Example nat_Elements_Initial_obj :
  `1 (@initial_obj (Elements Endos_Forget) nat_Elements_Initial) = NatSucc.
Proof. reflexivity. Qed.

Example nat_Elements_Initial_elem :
  `2 (@initial_obj (Elements Endos_Forget) nat_Elements_Initial) = O.
Proof. reflexivity. Qed.
