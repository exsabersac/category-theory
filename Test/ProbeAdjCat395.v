(*
   本文件为测试：ProbeAdjCat395。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Instance.Adj.
Require Import Category.Instance.Adj.Forgetful.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(* 相关说明。 （已译） *)
Fail Check p395_no_such_constant_anywhere.

Section Variance.

Context {C D : Category}.
Context {F : D ⟶ C} {U : C ⟶ D} (A  : F  ⊣ U).
Context {F' : D ⟶ C} {U' : C ⟶ D} (A' : F' ⊣ U').

(* 相关说明。 （已译） *)
Check @Conjugate.
Check A.
Check A'.
Check (fun (x : D) => F x).
Check (fun (a : C) => U a).

(* POSITIVE: 伴随 arguments SWAPPED, Mac Lane's labelling
 typechecks -- sigma forward left adjoints, tau backward the
 right adjoints. （已译） *)
Check (fun (s : F ⟹ F') (t : U' ⟹ U) => Conjugate A' A s t).

(*
   本节说明 ProbeAdjCat395 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (fun (s : F' ⟹ F) (t : U ⟹ U') => Conjugate A' A s t).

End Variance.

Section HomShape.

Context {C D : Category}.

(* 相关说明。 （已译） *)
Check @ConjPair.
Check @conj_left.
Check @conj_right.
Check @conj_pair_law.
Check @adjobj_adj.

(* 相关说明。 （已译） *)
Example adj_hom_is_conjpair (x y : AdjObj C D) :
  (x ~{Adj C D}~> y) = @ConjPair C D x y := eq_refl.

(* 相关说明。 （已译） *)
Example adj_law_is_swapped (x y : AdjObj C D) (f : x ~{Adj C D}~> y) :
  Conjugate (adjobj_adj y) (adjobj_adj x) (conj_left f) (conj_right f)
  := conj_pair_law f.

End HomShape.

Section ForgetfulShape.

(* CONTROLS. *)
Check @AdjForgetLeft.
Check @AdjForgetRight.

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example adj_forget_left_type (C D : Category) :
  AdjForgetLeft C D = AdjForgetLeft C D := eq_refl.

Check (fun C D : Category => AdjForgetLeft C D : Adj C D ⟶ [D, C]).
Check (fun C D : Category => AdjForgetRight C D : (Adj C D)^op ⟶ [C, D]).

(* NEGATIVE 2 (TYPING). The right forgetful 函子 NOT covariant on
 [Adj C D]; ascribing it there refused. This contravariance,
 pinned. （已译） *)
Fail Check (fun C D : Category => AdjForgetRight C D : Adj C D ⟶ [C, D]).

End ForgetfulShape.
