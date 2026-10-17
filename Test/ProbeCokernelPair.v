Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Morphisms.CokernelPair.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.CokernelPair.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   本文件为测试：ProbeCokernelPair。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Section Controls.

Context {C : Category}.
Context {x y z : C} (f : x ~> y) (g : x ~> z).

(* 相关说明。 （已译） *)
Definition ctl_roundtrip (P : IsPushout f g) :
  is_pushout_square_pushout (pushout_is_pushout_square f g P) = P := eq_refl.

(* [IsCokernelPair] IS [IsPushoutSquare] at a repeated leg. *)
Definition ctl_ckp_is_square (P : C) (u v : y ~> P) :
  IsCokernelPair f P u v = IsPushoutSquare f f P u v := eq_refl.

(*
   本节说明 ProbeCokernelPair 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ctl_epic_pushout_square (E : Epic f) := epic_pushout_square f E.
Definition ctl_pushout_square_epic (S : IsPushoutSquare f f y id id) :=
  pushout_square_epic f S.

(* 相关说明。 （已译） *)
Definition ctl_op_collapse :
  @IsPushoutSquare (C^op) y x x f f x id id
    = @IsPullback C x x y f f x id id := eq_refl.

(* 相关说明。 （已译） *)
Definition ctl_ckp_left `{H : @HasPushouts C} :
  ckp_left (cokernel_pair f) = pushout_in1 (pushout f f) := eq_refl.

(* 相关说明。 （已译） *)
Check (IsPushoutSquare f f y id id).
Check (IsPushout f f).

(* 相关说明。 （已译） *)
Check (@IsIsomorphism_of_op C x y).
Check (@op_IsIsomorphism_of C x y).

End Controls.

Section SetsControls.

Context {A B Q : SetoidObject}.
Context (f : A ~{Sets}~> B) (q1 q2 : B ~{Sets}~> Q).
Context (Hc : q1 ∘[Sets] f ≈ q2 ∘[Sets] f).

(*
   本节说明 ProbeCokernelPair 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ctl_sets_triangle_pointwise (b : carrier B) :
  (sets_ck_med f q1 q2 Hc ∘[Sets] ck_left f) b = q1 b := eq_refl.

Definition ctl_sets_triangle_pointwise_r (b : carrier B) :
  (sets_ck_med f q1 q2 Hc ∘[Sets] ck_right f) b = q2 b := eq_refl.

End SetsControls.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section SeparatedUniverseControl.

Universes uo uh up.
Constraint uh < up.

Context (C : Category@{uo uh up}).
Context (x y : C) (f : x ~> y).

Check (x ~> y).
Check f.

End SeparatedUniverseControl.

(** ** CONVERSION negatives *)

Section ConversionNegatives.

Context {C : Category}.
Context {x y : C} (f : x ~> y).
Context (a b : C) (h : b ~> a).

(*
   本节说明 ProbeCokernelPair 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition neg_iso_op :
  @IsIsomorphism (C^op) a b h = @IsIsomorphism C b a h := eq_refl.

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition neg_epi_roundtrip (E : Epic f) :
  pushout_square_epic f (epic_pushout_square f E) = E := eq_refl.

End ConversionNegatives.

Section SetsConversionNegatives.

Context {A B Q : SetoidObject}.
Context (f : A ~{Sets}~> B) (q1 q2 : B ~{Sets}~> Q).
Context (Hc : q1 ∘[Sets] f ≈ q2 ∘[Sets] f).

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition neg_sets_triangle :
  sets_ck_med f q1 q2 Hc ∘[Sets] ck_left f = q1 := eq_refl.

End SetsConversionNegatives.

(** ** FORMABILITY negatives *)

Section FormabilityNegatives.

Context {C : Category}.
Context {x y : C} (f : x ~> y).

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (IsPushout f f y id id).

End FormabilityNegatives.

(*
   本节说明拉回/推出、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section UniverseNegatives.

Universes vo vh vp.
Constraint vh < vp.

Context (C : Category@{vo vh vp}).
Context (x y : C) (f : x ~> y).

(* 5. the [Epic] donor, Theory/Morphisms.v *)
Fail Check (@Epic C x y f).

(* 6. the [Pullback] donor, Structure/Pullback.v *)
Fail Check (@Pullback C x x y f f).

(* 7. the [IsPullback] donor, Theory/Morphisms/Stability.v *)
Fail Check (@IsPullback C x x y f f x id id).

(* 8. the [IsPushout] donor, Structure/Pushout.v *)
Fail Check (@IsPushout C x y y f f).

(* 9. inherited by the pinned pushout square *)
Fail Check (@IsPushoutSquare C x y y f f y id id).

End UniverseNegatives.
