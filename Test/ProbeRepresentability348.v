(*
   本文件为测试：ProbeRepresentability348。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Opposite.
Require Import Category.Functor.Representable.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Arrow.Dual.
Require Import Category.Theory.Universal.Element.
Require Import Category.Adjunction.Representability.

Generalizable All Variables.

Section ProbePackaging.

Context {C : Category}.
Context {D : Category}.
Context {c : C}.
Context {F : D ⟶ C}.

(* INSTRUMENT CHECK: scope-free, and it must fail. *)
Fail Definition instrument_check : True = False := eq_refl.

(* CONTROL: both derived projections DO return on the nose. *)
Example ctl_obj (W : UniversalArrow c F) :
  @arrow_obj C D c F (ua_of_aua (aua_of_ua W)) = @arrow_obj C D c F W
  := eq_refl.

Example ctl_arrow (W : UniversalArrow c F) :
  @arrow C D c F (ua_of_aua (aua_of_ua W)) = @arrow C D c F W := eq_refl.

(* 相关说明。 （已译） *)
Example ctl_aua_arrow {a : D} (W : AUniversalArrow c F a) :
  @universal_arrow C D c F a (aua_of_ua (ua_of_aua W))
    = @universal_arrow C D c F a W := eq_refl.

(* NEGATIVE 1 (CONVERSION). [ua_of_aua] rebuilds comma 范畴's
 [Initial] record UMP, so [arrow_initial] different term
 even though both projections above reduce. （已译） *)
Fail Definition neg_ua_round (W : UniversalArrow c F) :
  ua_of_aua (aua_of_ua W) = W := eq_refl.

End ProbePackaging.

Section ProbeResidue.

Context {C : Category}.
Context {D : Category}.
Context {F : C ⟶ D}.
Context {G : D ⟶ C}.
Context (A : F ⊣ G).

(* 相关说明。 （已译） *)
Example ctl_residue (c : C) :
  @arrow C D c G (universal_of_representable G (adj_representable A) c)
    = fmap[G] (id{D}) ∘ @unit D C F G A c := eq_refl.

(* 相关说明。 （已译） *)
Example ctl_residue_equiv (c : C) :
  @arrow C D c G (universal_of_representable G (adj_representable A) c)
    ≈ @unit D C F G A c := representable_roundtrip_arrow A c.

(* CONTROL: 对象 half same round trip DOES return. （已译） *)
Example ctl_roundtrip_obj (c : C) :
  fobj[left_adjoint_of_representable G (adj_representable A)] c = F c
  := eq_refl.

(* NEGATIVE 2 (CONVERSION): the arrow half does not. *)
Fail Definition neg_roundtrip_arrow (c : C) :
  @arrow C D c G (universal_of_representable G (adj_representable A) c)
    = @unit D C F G A c := eq_refl.

End ProbeResidue.

(* Names negatives depend must appear OUTSIDE [Fail], a
 rename would leave file 编译 guard vacuously green. （已译） *)
Check @ua_of_aua.
Check @aua_of_ua.
Check @universal_of_representable.
Check @adj_representable.
Check @left_adjoint_of_representable.
Check @adjunction_iff_pointwise_representable.
Check @coadjunction_iff_pointwise_representable.
