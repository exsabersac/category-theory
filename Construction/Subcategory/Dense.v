Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Theory.Skeleton.

Generalizable All Variables.

(* * * An 同构-dense full subcategory reflective （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/essentially+surjective+functor
   nLab: https://ncatlab.org/nlab/show/dense+subcategory

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Dense.

Context {C : Category}.
Context (S : Subcategory C).

(** ** The hypothesis *)

(* Mac Lane's "every c C isomorphic (in C) some 对象 A", with
 对象 chosen. The sigma Type-valued, so representative and
 同构 both DATA. （已译） *)

Definition IsoDense : Type :=
  ∀ c : C, { a : Sub C S & Incl C S a ≅ c }.

(* ... [EssentiallySurjective] 含入, field for
 field. A plain [Definition], raising no obligation. （已译） *)

Definition iso_dense_ESO (D : IsoDense) :
  EssentiallySurjective (Incl C S) :=
  {| eso_obj := fun c => `1 (D c)
   ; eso_iso := fun c => `2 (D c) |}.

Example iso_dense_ESO_obj (D : IsoDense) (c : C) :
  @eso_obj _ _ _ (iso_dense_ESO D) c = `1 (D c) := eq_refl.

(* ... and back. *)

Definition ESO_iso_dense (E : EssentiallySurjective (Incl C S)) :
  IsoDense :=
  fun c => (@eso_obj _ _ _ E c; @eso_iso _ _ _ E c).

Example ESO_iso_dense_obj (E : EssentiallySurjective (Incl C S)) (c : C) :
  `1 (ESO_iso_dense E c) = @eso_obj _ _ _ E c := eq_refl.

(* 相关说明。 （已译） *)

Example ESO_round_whole (E : EssentiallySurjective (Incl C S)) :
  iso_dense_ESO (ESO_iso_dense E) = E := eq_refl.

(* The other closes 对象 component: stdlib [sigT] has no eta,
 so [IsoDense] whole record does not return. Refuted pinned in
 Test/ProbeDense375.v. （已译） *)

Example iso_dense_round_obj (D : IsoDense) (c : C) :
  `1 (ESO_iso_dense (iso_dense_ESO D) c) = `1 (D c) := eq_refl.

Context (F : Subcategory.Full C S).

(* * ** (1) The 嵌入 等价 （已译） *)

(* [Incl_Faithful] appears here, [:=] no tactic; reviewer
 check issue generic 引理 consumed rather than
 bypassed. （已译） *)

Definition dense_incl_equivalence (D : IsoDense) :
  EquivalenceOfCategories (Incl C S) :=
  @FF_ESO_Equivalence _ _ (Incl C S)
    (Full_Implies_Full_Functor C S F)
    (Incl_Faithful C S)
    (iso_dense_ESO D).

(* The quasi-inverse acts 对象 chosen representative:
 [FF_ESO_Equivalence] [Defined] [ff_eso_inverse]'s [fobj] is
 [eso_obj], so reduces all way. （已译） *)

Example dense_incl_quasi_obj (D : IsoDense) (c : C) :
  fobj[@quasi_inverse _ _ _ (dense_incl_equivalence D)] c = `1 (D c)
  := eq_refl.

(* * ** (2) The adjoint 等价, both handednesses （已译） *)

(* Mac Lane's triple read 嵌入 LEFT. （已译） *)

Definition dense_incl_adjoint_equivalence (D : IsoDense) :
  AdjointEquivalence (Incl C S)
    (@quasi_inverse _ _ _ (dense_incl_equivalence D)) :=
  Equivalence_to_AdjointEquivalence (dense_incl_equivalence D).

(* Mac Lane's T. *)

Definition dense_reflector (D : IsoDense) : C ⟶ Sub C S :=
  @quasi_inverse _ _ _ (dense_incl_equivalence D).

Example dense_reflector_obj (D : IsoDense) (c : C) :
  fobj[dense_reflector D] c = `1 (D c) := eq_refl.

(* ... reflection 伴随 T -| K, handedness the
 [Reflective] record asks for. （已译） *)

Definition dense_adj (D : IsoDense) : dense_reflector D ⊣ Incl C S :=
  AdjointEquivalence_swap_adjunction (dense_incl_adjoint_equivalence D).

(** ** (4) Reflectivity *)

Definition dense_full_subcategory_reflective (D : IsoDense) : Reflective S :=
  @Build_Reflective C S F (dense_reflector D) (dense_adj D).

Example dense_reflective_reflector (D : IsoDense) :
  reflector (dense_full_subcategory_reflective D) = dense_reflector D
  := eq_refl.

Example dense_reflective_adj (D : IsoDense) :
  reflective_adj (dense_full_subcategory_reflective D) = dense_adj D
  := eq_refl.

Example dense_reflective_full (D : IsoDense) :
  reflective_full (dense_full_subcategory_reflective D) = F := eq_refl.

Example dense_reflective_obj (D : IsoDense) (c : C) :
  fobj[reflector (dense_full_subcategory_reflective D)] c = `1 (D c)
  := eq_refl.

(* * ** (3) The counit, 同构 （已译） *)

(* [:=] no tactic: swapped adjoint 等价 carries a
 field. （已译） *)

Definition dense_counit_iso (D : IsoDense) (a : Sub C S) :
  IsIsomorphism (@counit _ _ _ _ (dense_adj D) a) :=
  @adj_equiv_counit_iso _ _ _ _
    (AdjointEquivalence_swap (dense_incl_adjoint_equivalence D)) a.

(*
   本节说明 Dense 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition dense_counit_Isomorphism (D : IsoDense) (a : Sub C S) :
  dense_reflector D (Incl C S a) ≅[Sub C S] a :=
  @IsIsoToIso (Sub C S) _ _ _ (dense_counit_iso D a).

Example dense_counit_Isomorphism_to (D : IsoDense) (a : Sub C S) :
  to (dense_counit_Isomorphism D a)
    = @counit _ _ _ _ (dense_adj D) a := eq_refl.

End Dense.

Arguments IsoDense {C} S.

(** ** The skeleton rider *)

(*
   本节说明 Dense 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition skeleton_IsoDense {C : Category} (Sk : Skeleton C) :
  IsoDense (skel_sub Sk) :=
  fun c => (skel_rep Sk c; iso_sym (skel_iso Sk c)).

Definition skeleton_reflective {C : Category} (Sk : Skeleton C) :
  Reflective (skel_sub Sk) :=
  dense_full_subcategory_reflective (skel_sub Sk) (skel_full Sk)
    (skeleton_IsoDense Sk).

Example skeleton_reflector_obj {C : Category} (Sk : Skeleton C) (c : C) :
  fobj[reflector (skeleton_reflective Sk)] c = skel_rep Sk c := eq_refl.

(* The reflector produced general 定理 IS Theory/Skeleton.v's
 [skel_reflect], nose: two [EssentiallySurjective] records
 agree field field, class has eta. （已译） *)

Example skeleton_reflector_is_skel_reflect {C : Category} (Sk : Skeleton C) :
  reflector (skeleton_reflective Sk) = skel_reflect Sk := eq_refl.

Example skeleton_reflective_full {C : Category} (Sk : Skeleton C) :
  reflective_full (skeleton_reflective Sk) = skel_full Sk := eq_refl.
