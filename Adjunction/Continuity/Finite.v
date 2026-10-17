Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Structure.Terminal.
Require Import Category.Functor.Structure.Cartesian.
Require Import Category.Adjunction.Continuity.
Require Import Category.Adjunction.Opposite.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(* * * Adjoints preserve 终对象 binary products, packaged （已译） *)

(*
   本文件给出有限情形。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section AdjointPreservation.

Context {C D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

(* A 右伴随 preserves 终对象: RAPL at empty
 discrete diagram, read through Structure/Limit/Comparison.v's bridge
 Functor/Structure/Terminal.v's class. （已译） *)
Definition right_adjoint_preserves_terminal `{@Terminal C} `{@Terminal D} :
  @TerminalFunctor C D U _ _ :=
  snd (terminal_functor_iff_preserves_terminal U)
      (right_adjoint_PreservesLimitCone A (DiscreteCat_Functor' nullary_fam)).

(* A 右伴随 preserves binary products: RAPL at two-对象
 discrete diagrams, through cartesian bridge. （已译） *)
Definition right_adjoint_preserves_binary_products
  `{@Cartesian C} `{@Cartesian D} : @CartesianFunctor C D U _ _ :=
  snd (cartesian_functor_iff_preserves_binary_products U)
      (fun x y => right_adjoint_PreservesLimitCone A
                    (DiscreteCat_Functor' (binary_fam x y))).

(*
   本节说明伴随、函子、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition left_adjoint_preserves_initial `{@Initial C} `{@Initial D} :
  @TerminalFunctor (D^op) (C^op) (F^op) _ _ :=
  snd (terminal_functor_iff_preserves_terminal (F^op))
      (right_adjoint_PreservesLimitCone (Opposite_Adjunction F U A)
         (DiscreteCat_Functor' nullary_fam)).

(* A left adjoint preserves binary coproducts: [CocartesianFunctor F],
   likewise spelled out (Functor/Structure/Cartesian.v). *)
Definition left_adjoint_preserves_binary_coproducts
  `{@Cocartesian C} `{@Cocartesian D} :
  @CartesianFunctor (D^op) (C^op) (F^op) _ _ :=
  snd (cartesian_functor_iff_preserves_binary_products (F^op))
      (fun x y => right_adjoint_PreservesLimitCone (Opposite_Adjunction F U A)
                    (DiscreteCat_Functor' (binary_fam x y))).

End AdjointPreservation.
