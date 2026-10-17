Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Arrow.Dual.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Reflective.Coreflective.

Generalizable All Variables.

(** * Reflective subcategories from universal arrows *)

(*
   nLab:  https://ncatlab.org/nlab/show/universal+morphism
   Book:  Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   Book:  Riehl, "Category Theory in Context", Dover 2016, §4.6,

   本文件给出泛构造相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* Mac Lane §IV.3, printed p. 91: reflective when every object has a
   universal arrow to the inclusion. *)
Definition Reflective_of_UniversalArrows@{o h +} {C : Category@{o h h}}
  {S : Subcategory C}
  (full : Construction.Subcategory.Full C S)
  (UA : ∀ x : C, UniversalArrow x (Incl C S)) : Reflective S :=
  @Build_Reflective C S full
    (LeftAdjointFunctorFromUniversalArrows (Incl C S) UA)
    (AdjunctionFromUniversalArrows (Incl C S) UA).

(* The reflection of x is the universal object, on the nose. *)
Example Reflective_of_UniversalArrows_obj@{o h +} {C : Category@{o h h}}
  {S : Subcategory C}
  (full : Construction.Subcategory.Full C S)
  (UA : ∀ x : C, UniversalArrow x (Incl C S)) (x : C) :
  fobj[reflector (Reflective_of_UniversalArrows full UA)] x
    = @arrow_obj C (Sub C S) x (Incl C S) (UA x) := eq_refl.

(* The unit is the universal arrow, up to [≈]: it arrives as the
   transpose of the identity, [fmap[Incl C S] id ∘ arrow]. *)
Lemma Reflective_of_UniversalArrows_unit@{o h +} {C : Category@{o h h}}
  {S : Subcategory C}
  (full : Construction.Subcategory.Full C S)
  (UA : ∀ x : C, UniversalArrow x (Incl C S)) (x : C) :
  @unit _ _ _ _ (reflective_adj (Reflective_of_UniversalArrows full UA)) x
    ≈ @arrow C (Sub C S) x (Incl C S) (UA x).
Proof. simpl. apply id_left. Qed.

(** ** The dual: coreflective subcategories from couniversal arrows *)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Coreflective_of_CouniversalArrows@{o h +} {C : Category@{o h h}}
  {S : Subcategory C}
  (full : Construction.Subcategory.Full C S)
  (CA : ∀ x : C, CouniversalArrow x (Incl C S)) : Coreflective S :=
  Coreflective_of_adjunction full
    (RightAdjointFunctorFromCouniversalArrows (Incl C S) CA)
    (AdjunctionFromCouniversalArrows (Incl C S) CA).

(* The coreflection of x is the couniversal object, on the nose. *)
Example Coreflective_of_CouniversalArrows_obj@{o h +}
  {C : Category@{o h h}} {S : Subcategory C}
  (full : Construction.Subcategory.Full C S)
  (CA : ∀ x : C, CouniversalArrow x (Incl C S)) (x : C) :
  fobj[coreflector (Coreflective_of_CouniversalArrows full CA)] x
    = @coarrow_obj C (Sub C S) x (Incl C S) (CA x) := eq_refl.

(* The covariant counit is the couniversal arrow, up to [≈]: it arrives
   as [coarrow ∘ fmap[Incl C S] id], Dual.v's [counit_couniversal]. *)
Lemma Coreflective_of_CouniversalArrows_counit@{o h +}
  {C : Category@{o h h}} {S : Subcategory C}
  (full : Construction.Subcategory.Full C S)
  (CA : ∀ x : C, CouniversalArrow x (Incl C S)) (x : C) :
  @counit _ _ _ _
    (coreflective_adj (Coreflective_of_CouniversalArrows full CA)) x
    ≈ @coarrow C (Sub C S) x (Incl C S) (CA x).
Proof. exact (counit_couniversal (Incl C S) CA x). Qed.
