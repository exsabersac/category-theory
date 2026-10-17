Require Import Category.Lib.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Opposite.
Require Import Category.Adjunction.Natural.Transformation.

Generalizable All Variables.

(* * * The opposite (dual) unit/counit 伴随. （已译） *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

   本文件给出反范畴、反函子或反自然变换（2-胞方向反转）。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Opposite_Adjunction_Transform
        `(F : D ⟶ C) `(U : C ⟶ D) (A : F ∹ U) :
  U^op ∹ F^op := {|
  unit := _;
  counit := _
|}.
Next Obligation.
  transform; simpl; intros.
  - apply counit.
  - apply (@naturality_sym _ _ _ _ counit).
  - apply (@naturality _ _ _ _ counit).
Defined.
Next Obligation.
  transform; simpl; intros.
  - apply unit.
  - apply (@naturality_sym _ _ _ _ unit).
  - apply (@naturality _ _ _ _ unit).
Defined.
Next Obligation.
  apply fmap_counit_unit.
Defined.
Next Obligation.
  apply counit_fmap_unit.
Defined.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Corollary Opposite_Adjunction_Transform_invol
          `(F : D ⟶ C) `(U : C ⟶ D) (A : F ∹ U) :
  Opposite_Adjunction_Transform
    (U^op) (F^op) (Opposite_Adjunction_Transform F U A) = A.
Proof. reflexivity. Qed.
