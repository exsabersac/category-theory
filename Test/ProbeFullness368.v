Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Adjunction.Natural.Transformation.Universal.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Adjunction.Fullness.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   本文件为测试：ProbeFullness368。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Fail Check probe368_no_such_constant_anywhere.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section P_hom_proof.

Universes co ch cp.
Constraint ch < cp.

Context (Cu : Category@{co ch cp}).
Context (x y : Cu).
Context (f : x ~{Cu}~> y).

(* Controls: hom-set 恒等 ARE formable at these levels. （已译） *)
Check (@id Cu x).
Check f.

(* Negative 1 (FORMABILITY). *)
Fail Check (@Section Cu x y f).

(* Negative 2 (FORMABILITY). *)
Fail Check (@Monic Cu x y f).

(* Negative 3 (FORMABILITY): same cause, third donor. *)
Fail Check (@Retraction Cu x y f).

End P_hom_proof.

Section P_hom_proof_control.

Universes co ch cp do dh dp.
Constraint ch < cp.

Context (Cu : Category@{co ch cp}).
Context (Du : Category@{do dh dp}).

(* [Functor] does NOT force hom = 证明: 这是 accepted at exactly the
 levels where [Section], [Monic] [Retraction] rejected. （已译） *)
Check (Du ⟶ Cu).

End P_hom_proof_control.

Section P_hom_hom.

Universes co ch cp do dh dp.
Constraint dh < ch.

Context (Cu : Category@{co ch ch}).
Context (Du : Category@{do dh dh}).

(* Control: one direction is formable. *)
Check (Du ⟶ Cu).

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (Cu ⟶ Du).

End P_hom_hom.

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section P_whisker.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

Definition PT : F ∹ U := @Adjunction_to_Transform C D F U A.

(* Controls: both whiskered transformations exist, at own types,
 both target's hand-built transformations exist at type
 同构 needs. （已译） *)
Check (U ⊳ (@counit _ _ _ _ PT)).
Check ((@unit _ _ _ _ PT) ⊲ U).
Check (@whiskered_counit C D F U A : U ◯ F ◯ U ⟹ U).
Check (@whiskered_unit C D F U A : U ⟹ U ◯ F ◯ U).

(* Negative 5 (TYPING). *)
Fail Check ((U ⊳ (@counit _ _ _ _ PT)) : U ◯ F ◯ U ⟹ U).

(* Negative 6 (TYPING). *)
Fail Check (((@unit _ _ _ _ PT) ⊲ U) : U ⟹ U ◯ F ◯ U).

(*
   本节说明 ProbeFullness368 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (@whiskered_counit_is_whisker_left C D F U A).
Check (@whiskered_unit_is_whisker_right C D F U A).

End P_whisker.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section P_reflective.

Context {C : Category}.
Context {S : Subcategory C}.
Context (R : Reflective S).
Context (x : Sub C S).

(* Controls: both isomorphisms exist, target's inverse the
 unit component at [eq_refl] (这是 target's own [Example],
 restated here so rename breaks probe). （已译） *)
Check (reflective_counit_iso R x).
Check (reflective_fmap_counit_IsIsomorphism R x).
Check (@reflective_fmap_counit_inverse C S R x).
Check (fmap[Incl C S] (from (reflective_counit_iso R x))).

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition probe_reflective_inverse_strict :
  two_sided_inverse
    (IsIsomorphism := reflective_fmap_counit_IsIsomorphism R x)
  = fmap[Incl C S] (from (reflective_counit_iso R x)) := eq_refl.

End P_reflective.

Section P_equiv.

Context {C : Category}.
Context {D : Category}.
Context {F : C ⟶ D}.
Context (E : @EquivalenceOfCategories C D F).
Context (d : D).

(* Controls. *)
Check (equiv_adjunction E).
Check (equiv_adjunction_counit_iso E d).
Check (equiv_fmap_counit_IsIsomorphism E d).
Check (@equiv_fmap_counit_inverse C D F E d).
Check (@equiv_fmap_counit_inverse_agrees C D F E d).

(* 相关说明。 （已译） *)
Fail Definition probe_equiv_inverse_strict :
  two_sided_inverse (IsIsomorphism := equiv_fmap_counit_IsIsomorphism E d)
  = fmap[@quasi_inverse C D F E]
      (two_sided_inverse
         (IsIsomorphism := equiv_adjunction_counit_iso E d)) := eq_refl.

End P_equiv.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section P_padding.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.

(* 相关说明。 （已译） *)
Example probe_padding_assoc_fobj :
  fobj[U ◯ (F ◯ U)] = fobj[(U ◯ F) ◯ U] := eq_refl.
Example probe_padding_assoc_fmap :
  @fmap _ _ (U ◯ (F ◯ U)) = @fmap _ _ ((U ◯ F) ◯ U) := eq_refl.
Example probe_padding_unit_r_fobj : fobj[U ◯ Id[C]] = fobj[U] := eq_refl.
Example probe_padding_unit_r_fmap :
  @fmap _ _ (U ◯ Id[C]) = @fmap _ _ U := eq_refl.
Example probe_padding_unit_l_fobj : fobj[Id[D] ◯ U] = fobj[U] := eq_refl.
Example probe_padding_unit_l_fmap :
  @fmap _ _ (Id[D] ◯ U) = @fmap _ _ U := eq_refl.

(* Negative 9 (CONVERSION): the two parenthesizations. *)
Fail Definition probe_padding_assoc : U ◯ (F ◯ U) = (U ◯ F) ◯ U := eq_refl.

(* Negative 10 (CONVERSION): the right identity padding. *)
Fail Definition probe_padding_unit_r : U ◯ Id[C] = U := eq_refl.

(* Negative 11 (CONVERSION): the left identity padding. *)
Fail Definition probe_padding_unit_l : Id[D] ◯ U = U := eq_refl.

End P_padding.

(*
   本节说明 ProbeFullness368 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section P_names.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

Check (@counit_split_mono_of_full_right C D F U A).
Check (@unit_split_epi_of_full_left C D F U A).
Check (@counit_inv_of_full_right C D F U A).
Check (@unit_inv_of_full_left C D F U A).
Check (@unit_fmap_counit_of_full_right C D F U A).
Check (@unit_fmap_counit_of_full_left C D F U A).
Check (@unit_fmap_counit C D F U A).
Check (@fmap_counit_IsIsomorphism_of_full C D F U A).
Check (@fmap_unit_counit_of_full_left C D F U A).
Check (@fmap_unit_counit_of_full_right C D F U A).
Check (@fmap_unit_counit C D F U A).
Check (@counit_at_F_IsIsomorphism_of_full C D F U A).
Check (@whiskered_counit_iso_of_full C D F U A).
Check (@whiskered_counit_iso_of_full_left C D F U A).
Check (@whiskered_counit_iso_of_full_right C D F U A).
Check (@whiskered_unit_F C D F U A).
Check (@whiskered_counit_F C D F U A).
Check (@whiskered_unit_iso_of_full C D F U A).
Check (@whiskered_unit_iso_of_full_left C D F U A).
Check (@whiskered_unit_iso_of_full_right C D F U A).
Check (@unit_at_UF_of_full_right C D F U A).
Check (@unit_epic_of_full_monic C D F U A).
Check (@unit_epic_of_full_left C D F U A).
Check (@unit_iso_of_full_monic C D F U A).
Check (@unit_at_U_IsIsomorphism_of_full C D F U A).
Check (@split_inverses_agree C).

End P_names.

Require Import Category.Structure.ZeroObject.
Require Import Category.Instance.One.
Require Import Category.Instance.Sets.Pointed.

Check (@Full_Erase_of_ZeroObject).
Check (@zero_erase_adjunction).
Check (@zero_erase_fmap_counit_IsIsomorphism).
Check Erase_PointedSets_not_Faithful.
Check pointed_counit_not_IsIsomorphism.
