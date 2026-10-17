Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Two.
Require Import Category.Instance.Fun.Morphisms.

Generalizable All Variables.

(** * Boundary probe for Instance/Fun/Morphisms.v (issue #369) *)

(*
   本文件为测试：ProbeMorphisms369。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* Instrument check: a [Fail] that must fire whatever else is true, so a
   silently vacuous [Fail] elsewhere is not mistaken for a measurement. *)
Fail Check probe369_no_such_reference.

(* ------------------------------------------------------------------ *)
(** ** CONVERSION negatives *)

Section Conversion.

Context {C : Category}.
Context {D : Category}.
Context {F : C ⟶ D}.
Context {G : C ⟶ D}.
Context (θ : F ⟹ G).
Context {P : C ⟶ Sets}.
Context {Q : C ⟶ Sets}.
Context (ψ : P ⟹ Q).
Context (x : C).

(*
   本节说明函子、核/余核、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example ker_fmap_id_strict :
  fmap[KerPair ψ] (id[x]) = id := eq_refl.

Example ker_fmap_id_equiv : fmap[KerPair ψ] (id[x]) ≈ id.
Proof. exact (@fmap_id _ _ (KerPair ψ) x). Qed.

(* Same for the cokernel-pair functor, whose [ck_fun] is a [match] on a
   [sum]. *)
Fail Example ck_fmap_id_strict :
  fmap[CokerPair ψ] (id[x]) = id := eq_refl.

Example ck_fmap_id_equiv : fmap[CokerPair ψ] (id[x]) ≈ id.
Proof. exact (@fmap_id _ _ (CokerPair ψ) x). Qed.

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example iso_records_strict
  (H : ∀ z : C, IsIsomorphism (transform[θ] z)) :
  equiv_iso (nat_iso_family θ H)
    = @IsIsoToIso ([C, D]) F G θ (componentwise_iso θ H) := eq_refl.

Example iso_to_agrees
  (H : ∀ z : C, IsIsomorphism (transform[θ] z)) (z : C) :
  transform[to (equiv_iso (nat_iso_family θ H))] z = transform[θ] z
  := eq_refl.

Example iso_from_agrees
  (H : ∀ z : C, IsIsomorphism (transform[θ] z)) (z : C) :
  transform[from (equiv_iso (nat_iso_family θ H))] z
    = transform[nat_inverse θ H] z := eq_refl.

(* The whole transform FUNCTIONS agree as well, not merely their values
   at each z. *)
Example iso_to_transform_agrees
  (H : ∀ z : C, IsIsomorphism (transform[θ] z)) :
  transform[to (equiv_iso (nat_iso_family θ H))] = transform[θ]
  := eq_refl.

Example iso_from_transform_agrees
  (H : ∀ z : C, IsIsomorphism (transform[θ] z)) :
  transform[from (equiv_iso (nat_iso_family θ H))]
    = transform[nat_inverse θ H] := eq_refl.

(* CONVERSION 3 and 4.  Neither whole LEG is ours on the nose: the data
   field agrees (the four controls above) and only the two naturality
   fields, `abstract`ed by the donor, differ. *)
Fail Example iso_to_leg_strict
  (H : ∀ z : C, IsIsomorphism (transform[θ] z)) :
  to (equiv_iso (nat_iso_family θ H)) = θ := eq_refl.

Fail Example iso_from_leg_strict
  (H : ∀ z : C, IsIsomorphism (transform[θ] z)) :
  from (equiv_iso (nat_iso_family θ H)) = nat_inverse θ H := eq_refl.

End Conversion.

(* ------------------------------------------------------------------ *)
(** ** CONVERSION 1, cause discriminated at the constant-functor witnesses *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example const_fmap_is_id : fmap[TwoOne] (@id _2 TwoX) = id := eq_refl.

Example const_fmap_id_refl :
  @fmap_id _ _ TwoOne TwoX = reflexivity _ := eq_refl.

Fail Example ker_fmap_id_const (u : carrier (KerPair two_pick_nat TwoX)) :
  fmap[KerPair two_pick_nat] (@id _2 TwoX) u = u := eq_refl.

Fail Example ck_fmap_id_const (u : carrier (CokerPair two_collapse TwoX)) :
  fmap[CokerPair two_collapse] (@id _2 TwoX) u = u := eq_refl.

Example ker_fmap_id_const_equiv :
  fmap[KerPair two_pick_nat] (@id _2 TwoX) ≈ id.
Proof. exact (@fmap_id _ _ (KerPair two_pick_nat) TwoX). Qed.

Example ck_fmap_id_const_equiv :
  fmap[CokerPair two_collapse] (@id _2 TwoX) ≈ id.
Proof. exact (@fmap_id _ _ (CokerPair two_collapse) TwoX). Qed.

(* ------------------------------------------------------------------ *)
(** ** TYPING negative *)

Section Typing.

Context {C : Category}.
Context {P : C ⟶ Sets}.
Context {Q : C ⟶ Sets}.
Context (ψ : P ⟹ Q).

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition monic_is_not_pointwise (Hm : @Monic ([C, Sets]) P Q ψ) :
  ∀ z : C, Monic (transform[ψ] z) := Hm.

Definition monic_gives_pointwise (Hm : @Monic ([C, Sets]) P Q ψ) :
  ∀ z : C, Monic (transform[ψ] z) := sets_functor_monic_pointwise ψ Hm.

Definition epic_gives_pointwise (He : @Epic ([C, Sets]) P Q ψ) :
  ∀ z : C, Epic (transform[ψ] z) := sets_functor_epic_pointwise ψ He.

End Typing.

(* ------------------------------------------------------------------ *)
(** ** FORMABILITY negatives *)

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section FormabilityFun.

Universes co ch cp dro dh dp.
Constraint ch < dh.

Context {Cu : Category@{co ch cp}}.
Context {Du : Category@{dro dh dp}}.
Context (x y : Cu) (a b : Du).

Check (x ~{Cu}~> y).
Check (a ~{Du}~> b).

Fail Check (@Fun Cu Du).

End FormabilityFun.

(* [Monic] and [Epic] take a category whose hom and proof levels
   coincide, which is the other identification the target's binders
   display. *)
Section FormabilityMonic.

Universes mo mh mp.
Constraint mh < mp.

Context {Du : Category@{mo mh mp}}.
Context (a b : Du) (g : a ~{Du}~> b).

Check (a ~{Du}~> b).
Check g.

Fail Check (@Monic Du a b g).
Fail Check (@Epic Du a b g).

End FormabilityMonic.

(* And the target's own general theorem inherits both, so it too is
   unformable over two categories whose hom levels are kept apart. *)
Section FormabilityTarget.

Universes to2 th tp uo uh up.
Constraint th < uh.

Context {Cu : Category@{to2 th tp}}.
Context {Du : Category@{uo uh up}}.
Context (x y : Cu) (a b : Du).

Check (x ~{Cu}~> y).
Check (a ~{Du}~> b).

Fail Check (@pointwise_monic_is_monic Cu Du).
Fail Check (@pointwise_epic_is_epic Cu Du).

End FormabilityTarget.

(* ------------------------------------------------------------------ *)
(** ** Rename guards *)

(*
   本节说明 ProbeMorphisms369 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Check @IsIsoToIso.
Check @Fun.
Check @pointwise_monic_is_monic.
Check @pointwise_epic_is_epic.
Check @theta_nat.
Check @ker_map_ok.
Check @ker_fun.
Check @ker_fun_proper.
Check @ker_map.
Check @KerPair.
Check @KerFst.
Check @KerSnd.
Check @ker_agree.
Check @sets_functor_monic_pointwise.
Check @sets_functor_monic_iff_pointwise.
Check @ck_Im_map.
Check @ck_fun.
Check @ck_fun_proper.
Check @ck_map.
Check @CokerPair.
Check @CkLeft.
Check @CkRight.
Check @ck_agree_nat.
Check @sets_functor_epic_pointwise.
Check @sets_functor_epic_iff_pointwise.
Check @nat_inv_natural.
Check @nat_inverse.
Check @componentwise_iso.
Check @nat_iso_pointwise.
Check @nat_iso_iff_pointwise.
Check @nat_iso_family.
Check @equiv_iso_to_is_theta.
Check @equiv_iso_from_is_nat_inverse.
Check @presheaf_monic_iff_pointwise.
Check @presheaf_epic_iff_pointwise.
Check @presheaf_monic_iff_injective.
Check @presheaf_epic_iff_surjective.
Check @const_fun.
Check TwoOne.
Check TwoBool.
Check two_pick_nat.
Check two_collapse.
Check @pick_true_Monic.
Check @collapse_Epic.
Check two_pick_Monic.
Check two_collapse_Epic.
Check @two_pick_component_not_surjective.
Check @two_pick_not_Epic.
Check @two_collapse_not_Monic.
Check TwoTwoX.
Check TwoTwoY.
Check two_arrow.
Check two_arrow_Monic.
Check two_arrow_Epic.
