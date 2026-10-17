(*
    nLab: https://ncatlab.org/nlab/show/coreflective+subcategory

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.

Generalizable All Variables.

(** ** From covariant data to the record *)

(* A covariant functor into the subcategory, read as a functor between
   the opposites.  Every field is the donor's own, with the two object
   arguments exchanged. *)
Definition coreflector_op@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (G : C ⟶ Sub C S) :
  C^op ⟶ Sub (C^op) (op_subcategory S).
Proof.
  refine (@Build_Functor (C^op) (Sub (C^op) (op_subcategory S))
            (fun x => fobj[G] x)
            (fun x y f => @fmap _ _ G y x f) _ _ _).
  - intros x y f g E. exact (@fmap_respects _ _ G y x f g E).
  - intros x. exact (@fmap_id _ _ G x).
  - intros x y z f g. exact (@fmap_comp _ _ G z y x g f).
Defined.

(* The covariant adjunction [Incl ⊣ G] read as [G^op ⊣ Incl^op].  The
   hom-set isomorphism is the donor's with [to] and [from] exchanged, and
   each of the four naturality fields is one of the donor's four with its
   arguments permuted: nothing is re-proved. *)
Definition coreflector_op_adj@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (G : C ⟶ Sub C S) (A : Incl C S ⊣ G) :
  coreflector_op G ⊣ Incl (C^op) (op_subcategory S).
Proof.
  unshelve refine
    (@Build_Adjunction (Sub (C^op) (op_subcategory S)) (C^op)
       (coreflector_op G) (Incl (C^op) (op_subcategory S))
       (fun x y => _) _ _ _ _).
  - unshelve refine (@Build_Isomorphism Sets _ _ _ _ _ _).
    + refine (@Build_SetoidMorphism _ _ _ _
                (fun f => from (@adj _ _ _ _ A y x) f) _).
      intros f g E. exact (proper_morphism (from (@adj _ _ _ _ A y x)) f g E).
    + refine (@Build_SetoidMorphism _ _ _ _
                (fun f => to (@adj _ _ _ _ A y x) f) _).
      intros f g E. exact (proper_morphism (to (@adj _ _ _ _ A y x)) f g E).
    + intros f. exact (iso_from_to (@adj _ _ _ _ A y x) f).
    + intros f. exact (iso_to_from (@adj _ _ _ _ A y x) f).
  - intros x y z f g. exact (@from_adj_nat_r _ _ _ _ A z y x g f).
  - intros x y z f g. exact (@from_adj_nat_l _ _ _ _ A z y x g f).
  - intros x y z f g. exact (@to_adj_nat_r _ _ _ _ A z y x g f).
  - intros x y z f g. exact (@to_adj_nat_l _ _ _ _ A z y x g f).
Defined.

(* Mac Lane's dual definition, built from covariant data: a full
   subcategory together with a right adjoint of its inclusion. *)
Definition Coreflective_of_adjunction@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (full : Construction.Subcategory.Full C S)
  (G : C ⟶ Sub C S) (A : Incl C S ⊣ G) : Coreflective S :=
  @Build_Reflective (C^op) (op_subcategory S)
    (fun x y ox oy f => full y x oy ox f)
    (coreflector_op G) (coreflector_op_adj G A).

(** ** From the record back to covariant data *)

Definition coreflective_full@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Coreflective S) :
  Construction.Subcategory.Full C S :=
  fun x y ox oy f => reflective_full R y x oy ox f.

Definition coreflector@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Coreflective S) : C ⟶ Sub C S.
Proof.
  refine (@Build_Functor C (Sub C S)
            (fun x => fobj[reflector R] x)
            (fun x y f => @fmap _ _ (reflector R) y x f) _ _ _).
  - intros x y f g E. exact (@fmap_respects _ _ (reflector R) y x f g E).
  - intros x. exact (@fmap_id _ _ (reflector R) x).
  - intros x y z f g. exact (@fmap_comp _ _ (reflector R) z y x g f).
Defined.

Definition coreflective_adj@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Coreflective S) :
  Incl C S ⊣ coreflector R.
Proof.
  unshelve refine
    (@Build_Adjunction C (Sub C S) (Incl C S) (coreflector R)
       (fun x y => _) _ _ _ _).
  - unshelve refine (@Build_Isomorphism Sets _ _ _ _ _ _).
    + refine (@Build_SetoidMorphism _ _ _ _
                (fun f => from (@adj _ _ _ _ (reflective_adj R) y x) f) _).
      intros f g E.
      exact (proper_morphism (from (@adj _ _ _ _ (reflective_adj R) y x))
               f g E).
    + refine (@Build_SetoidMorphism _ _ _ _
                (fun f => to (@adj _ _ _ _ (reflective_adj R) y x) f) _).
      intros f g E.
      exact (proper_morphism (to (@adj _ _ _ _ (reflective_adj R) y x))
               f g E).
    + intros f. exact (iso_from_to (@adj _ _ _ _ (reflective_adj R) y x) f).
    + intros f. exact (iso_to_from (@adj _ _ _ _ (reflective_adj R) y x) f).
  - intros x y z f g.
    exact (@from_adj_nat_r _ _ _ _ (reflective_adj R) z y x g f).
  - intros x y z f g.
    exact (@from_adj_nat_l _ _ _ _ (reflective_adj R) z y x g f).
  - intros x y z f g.
    exact (@to_adj_nat_r _ _ _ _ (reflective_adj R) z y x g f).
  - intros x y z f g.
    exact (@to_adj_nat_l _ _ _ _ (reflective_adj R) z y x g f).
Defined.

(** ** Round trips *)

Example coreflector_obj_roundtrip@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (full : Construction.Subcategory.Full C S)
  (G : C ⟶ Sub C S) (A : Incl C S ⊣ G) (x : C) :
  fobj[coreflector (Coreflective_of_adjunction full G A)] x = fobj[G] x
  := eq_refl.

Example coreflector_fmap_roundtrip@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (full : Construction.Subcategory.Full C S)
  (G : C ⟶ Sub C S) (A : Incl C S ⊣ G) (x y : C) (f : x ~> y) :
  fmap[coreflector (Coreflective_of_adjunction full G A)] f = fmap[G] f
  := eq_refl.

(* The whole functor, the whole adjunction, the fullness witness and the
   whole record all return on the nose. *)
Example coreflector_roundtrip@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (full : Construction.Subcategory.Full C S)
  (G : C ⟶ Sub C S) (A : Incl C S ⊣ G) :
  coreflector (Coreflective_of_adjunction full G A) = G := eq_refl.

Example coreflective_adj_roundtrip@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (full : Construction.Subcategory.Full C S)
  (G : C ⟶ Sub C S) (A : Incl C S ⊣ G) :
  coreflective_adj (Coreflective_of_adjunction full G A) = A := eq_refl.

Example coreflective_full_roundtrip@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (full : Construction.Subcategory.Full C S)
  (G : C ⟶ Sub C S) (A : Incl C S ⊣ G) :
  coreflective_full (Coreflective_of_adjunction full G A) = full
  := eq_refl.

Example Coreflective_roundtrip@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Coreflective S) :
  Coreflective_of_adjunction (coreflective_full R) (coreflector R)
    (coreflective_adj R) = R := eq_refl.

(** ** Unit and counit, read across the bridge *)

(* The covariant counit at [x : C] IS the record's unit at [x], and the
   covariant unit at [s : Sub C S] IS the record's counit at [s]. *)
Example coreflective_counit_is_op_unit@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Coreflective S) (x : C) :
  @counit _ _ _ _ (coreflective_adj R) x
    = @Category.Theory.Adjunction.unit _ _ _ _ (reflective_adj R) x
  := eq_refl.

Example coreflective_unit_is_op_counit@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Coreflective S) (s : Sub C S) :
  @Category.Theory.Adjunction.unit _ _ _ _ (coreflective_adj R) s
    = @counit _ _ _ _ (reflective_adj R) s
  := eq_refl.

(* The dual of [reflective_counit_iso]: at an object of a coreflective
   subcategory the unit is invertible, [x ≅ coreflector (Incl x)].  The
   two morphisms are [reflective_counit_iso]'s, and its two inverse laws
   are exchanged. *)
Definition coreflective_unit_iso@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Coreflective S) (x : Sub C S) :
  x ≅[Sub C S] fobj[coreflector R] (fobj[Incl C S] x).
Proof.
  pose (i := reflective_counit_iso R x).
  unshelve refine (@Build_Isomorphism (Sub C S) _ _ (to i) (from i) _ _).
  - exact (iso_from_to i).
  - exact (iso_to_from i).
Defined.
