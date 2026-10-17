Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Theory.Skeleton.
Require Import Category.Adjunction.Compose.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.
Require Import Category.Theory.Shapes.
Require Import Category.Adjunction.LeftInverse.

Generalizable All Variables.

(*
   本文件为测试：ProbeLeftInverse376。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Instrument check: [Fail] itself must be able to fail. *)

Fail Check probe376_no_such_constant_anywhere.

(** ** Controls: the names the negatives below depend on. *)

Check @LeftAdjointLeftInverse.
Check @lali_characterization.
Check @LeftAdjointFFInjective.
Check @ReflectiveIsoPresentation.
Check @ri_lali_implies_lali.
Check @ri_sub.
Check @lali_implies_ri.
Check @lali_image_insertion.
Check @lali_cycle.
Check @lali_obj.
Check @lali_counit.
Check @LaliImageSub.
Check @ImageTo.
Check @ImageFrom.
Check @image_to_from_obj.
Check @lali_implies_ffi.
Check @ffi_left.
Check @lali_left.
Check @PointAt.
Check @terminal_LALI.
Check @Point.
Check @Incl.
Check @Reflective.
Check @reflective_adj.
Check @reflector.
Check @reflective_counit_iso.
Check @counit.
Check @id_cast.
Check @Functor_StrictEq_Setoid.
Check @lali_along_right_strict.
Check @ffi_implies_ri.
Check @Sub.
Check @Isomorphism.
Check StrictCat.

(*
   本节说明伴随、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CounitIsNotIdentity.

Context {A X : Category}.
Context {F : X ⟶ A}.
Context {G : A ⟶ X}.
Context (Adj : F ⊣ G).
Context (a : A).

Fail Check (@counit A X F G Adj a ≈ id[a]).

Context (P : LeftAdjointLeftInverse G).

Check (@counit A X (lali_left P) G (lali_adj P) a ≈ id_cast (lali_obj P a)).
Check (lali_counit P a).

End CounitIsNotIdentity.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ReflectionCounit.

Context {C : Category}.
Context {S : Subcategory C}.
Context (R : Reflective S).
Context (y : Sub C S).

Fail Check (@counit (Sub C S) C (reflector R) (Incl C S) (reflective_adj R) y
              ≈ id[y]).

Check (@counit (Sub C S) C (reflector R) (Incl C S) (reflective_adj R) y
         ≈ to (reflective_counit_iso R y)).

End ReflectionCounit.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ThirdLegIsConditional.

Context {A X : Category}.
Context {G : A ⟶ X}.
Context (Pres : ReflectiveIsoPresentation G).
Context (L : LeftAdjointLeftInverse (Incl X (ri_sub Pres))).

Fail Definition unconditional_third_leg : LeftAdjointLeftInverse G :=
  ri_lali_implies_lali Pres.

Definition conditional_third_leg : LeftAdjointLeftInverse G :=
  ri_lali_implies_lali Pres L.

End ThirdLegIsConditional.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CycleIsNotIdentity.

Context {A X : Category}.
Context {G : A ⟶ X}.
Context (P : LeftAdjointLeftInverse G).

Fail Example cycle_is_identity : lali_cycle P = P := eq_refl.

Example ffi_left_strict : ffi_left (lali_implies_ffi P) = lali_left P :=
  eq_refl.

Example ri_sub_strict : ri_sub (lali_implies_ri P) = @LaliImageSub A X G :=
  eq_refl.

End CycleIsNotIdentity.

(*
   本节说明 ProbeLeftInverse376 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ImageRoundTripObj.

Context {A X : Category}.
Context {G : A ⟶ X}.
Context (B : LeftAdjointFFInjective G).
Context (y : Sub X (@LaliImageSub A X G)).
Context (a : A).

Fail Example image_obj_refl : image_to_from_obj B y = eq_refl := eq_refl.

Example image_obj_refl_at_image :
  image_to_from_obj B (@ImageTo A X G a) = eq_refl := eq_refl.

End ImageRoundTripObj.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section UniverseProbe.

Universes ao ah xo xh.
Constraint ah < xh.

Context (Au : Category@{ao ah ah}).
Context (Xu : Category@{xo xh xh}).
Context (Gu : Au ⟶ Xu).

(* control: the functor type, and a functor, at levels declared apart *)
Check (Au ⟶ Xu).
Check Gu.
Check (InjectiveOnObjects Gu).

Fail Check (Xu ⟶ Au).
Fail Check (@Functor_StrictEq_Setoid Au Xu).
Fail Check (LeftAdjointLeftInverse Gu).
Fail Check (@lali_along_right_strict Au Xu Gu Gu).
Fail Check (@ffi_implies_ri Au Xu Gu).

End UniverseProbe.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section StrictCatObjectProbe.

Universes bo bh co.
Constraint bo < co.

Context (Bu : Category@{bo bh bh}).
Context (Cu2 : Category@{co bh bh}).
Context (Gu2 : Bu ⟶ Cu2).

(* controls: accepted at object levels declared apart *)
Check (Bu ⟶ Cu2).
Check (LeftAdjointLeftInverse Gu2).
Check (@LeftAdjointFFInjective Bu Cu2 Gu2).

Fail Check (@Isomorphism StrictCat Bu Cu2).
Fail Check (@ffi_implies_ri Bu Cu2 Gu2).

End StrictCatObjectProbe.

(*
   本节说明hom、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section PointProbe.

Universes po ph.
Constraint Set < ph.

Context (Cu : Category@{po ph ph}).
Context (c : Cu).

Check (_1@{po ph ph}).
Check (PointAt (C:=Cu) c : _1@{po ph ph} ⟶ Cu).
Check (@terminal_LALI).

Fail Check (Point (C:=Cu) c : _1@{po ph ph} ⟶ Cu).

End PointProbe.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Check @lali_ri_insertion.
Check @two_LALI.
Check @two_lali_moves_TwoX.
