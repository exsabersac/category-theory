Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Elements.Kan.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   本文件为测试：ProbeCoyoneda。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Section RoundTripConversion.

Context {D : Category}.
Context (K : D ⟶ Sets).
Context {a : D}.
Context (tau : K ⟹ [Hom a,─]).
Context (psi : ACone a (Elements_proj K)).
Context (d : D) (x : K d).
Context (j : Elements K).

(* 相关说明。 （已译） *)
Definition control_instrument :
  kan_nat_of_cone K (kan_cone_of_nat K tau)
    = kan_nat_of_cone K (kan_cone_of_nat K tau) := eq_refl.

(*
   本节说明 ProbeCoyoneda 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition control_rt1_applied :
  @transform D Sets K ([Hom a,─])
     (kan_nat_of_cone K (kan_cone_of_nat K tau)) d x
  = @transform D Sets K ([Hom a,─]) tau d x := eq_refl.

(*
   本节说明 ProbeCoyoneda 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition neg_rt1_record :
  kan_nat_of_cone K (kan_cone_of_nat K tau) = tau := eq_refl.

(*
   本节说明 ProbeCoyoneda 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition neg_rt1_family :
  @transform D Sets K ([Hom a,─])
     (kan_nat_of_cone K (kan_cone_of_nat K tau))
  = @transform D Sets K ([Hom a,─]) tau := eq_refl.

(* 相关说明。 （已译） *)
Fail Definition neg_rt1_component :
  @transform D Sets K ([Hom a,─])
     (kan_nat_of_cone K (kan_cone_of_nat K tau)) d
  = @transform D Sets K ([Hom a,─]) tau d := eq_refl.

(* POSITIVE CONTROL 3. Round trip 2's LEG returns nose once the
 sigma 对象 literal pair. （已译） *)
Definition control_rt2_pair :
  @vertex_map (Elements K) D a (Elements_proj K)
     (kan_cone_of_nat K (kan_nat_of_cone K psi)) ((d; x) : Elements K)
  = @vertex_map (Elements K) D a (Elements_proj K) psi
     ((d; x) : Elements K) := eq_refl.

(*
   本节说明 ProbeCoyoneda 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition neg_rt2_leg :
  @vertex_map (Elements K) D a (Elements_proj K)
     (kan_cone_of_nat K (kan_nat_of_cone K psi)) j
  = @vertex_map (Elements K) D a (Elements_proj K) psi j := eq_refl.

(* 相关说明。 （已译） *)
Fail Definition neg_rt2_record :
  kan_cone_of_nat K (kan_nat_of_cone K psi) = psi := eq_refl.

End RoundTripConversion.

(* 相关说明。 （已译） *)

Section DeltaConversion.

Context {D : Category}.
Context (K : D ⟶ Sets).
Context {a : D}.
Context (psi : ACone a (Elements_proj K)).
Context (theta : Δ[Elements K](a) ⟹ Elements_proj K).
Context (j : Elements K).

(*
   本节说明 ProbeCoyoneda 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition control_delta_cone_leg :
  @vertex_map (Elements K) D a (Elements_proj K)
     (kan_cone_of_transform K (kan_transform_of_cone K psi)) j
  = @vertex_map (Elements K) D a (Elements_proj K) psi j := eq_refl.

Definition control_delta_transform_component :
  @transform (Elements K) D (Δ[Elements K](a)) (Elements_proj K)
     (kan_transform_of_cone K (kan_cone_of_transform K theta)) j
  = @transform (Elements K) D (Δ[Elements K](a)) (Elements_proj K) theta j
  := eq_refl.

(*
   本节说明 ProbeCoyoneda 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition neg_delta_cone_record :
  kan_cone_of_transform K (kan_transform_of_cone K psi) = psi := eq_refl.

(* 相关说明。 （已译） *)
Fail Definition neg_delta_transform_record :
  kan_transform_of_cone K (kan_cone_of_transform K theta) = theta := eq_refl.

End DeltaConversion.

(* * ** Group 3 (FORMABILITY): 对象 strictly above homs （已译） *)

(*
   本节说明hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ObjectsAboveHoms.

Universes uo uh us.
Constraint uh < uo.
Constraint uh < us.

(* NEGATIVE 8 (FORMABILITY).  The cone presheaf is not formable when D's
   objects sit strictly above its homs.  Stripped error: "universe
   inconsistency: Cannot enforce uh = _ because uh < uo <= _". *)
Fail Check (fun (D : Category@{uo uh uh}) (K : D ⟶ Sets@{uh us}) =>
              KanCone K).

(*
   本节说明自然变换、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (fun (D : Category@{uo uh uh}) (K : D ⟶ Sets@{uh us}) =>
              KanNat K).

(* NEGATIVE 10 (FORMABILITY).  Hence the natural isomorphism itself. *)
Fail Check (fun (D : Category@{uo uh uh}) (K : D ⟶ Sets@{uh us}) =>
              kan_coyoneda K).

(*
   本节说明 ProbeCoyoneda 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (fun (D : Category@{uo uh uh}) (K : D ⟶ Sets@{uh us}) (a : D)
           (tau : K ⟹ [Hom a,─]) => kan_cone_of_nat K tau).

Check (fun (D : Category@{uo uh uh}) (K : D ⟶ Sets@{uh us}) (a : D)
           (psi : ACone a (Elements_proj K)) => kan_nat_of_cone K psi).

End ObjectsAboveHoms.

Section ObjectsBelowHoms.

Universes vo vh vs.
Constraint vo <= vh.
Constraint vh < vs.

(*
   本节说明 ProbeCoyoneda 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (fun (D : Category@{vo vh vh}) (K : D ⟶ Sets@{vh vs}) => KanCone K).
Check (fun (D : Category@{vo vh vh}) (K : D ⟶ Sets@{vh vs}) => KanNat K).
Check (fun (D : Category@{vo vh vh}) (K : D ⟶ Sets@{vh vs}) =>
         kan_coyoneda K).

End ObjectsBelowHoms.

(* 相关说明。 （已译） *)

Section Delivered.

Context {D : Category}.
Context (K : D ⟶ Sets).

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition control_to_component (a : D) :
  transform[to (kan_coyoneda K)] a = to (kan_iso_at K a) := eq_refl.

Definition control_from_component (a : D) :
  transform[from (kan_coyoneda K)] a = from (kan_iso_at K a) := eq_refl.

End Delivered.
