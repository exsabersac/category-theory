Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Construction.Slice.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Pointed.

Generalizable All Variables.

(** * Pointed sets as the coslice of Sets under the one-point set *)

(*
 nLab:      https://ncatlab.org/nlab/show/under+category
 Wikipedia: https://en.wikipedia.org/wiki/Comma_category
 Book:      Awodey, "Category Theory", 1st ed., OUP 2006, §7.9 Example 7.26

   本文件给出余切片范畴实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

(* The header of Construction/Slice.v records the standard reading of the
   coslice — "pointed sets are the coslice of Set under the one-point set".
   Here that sentence becomes a theorem.  A global element of A, i.e. a map
   1 ~> A out of the terminal setoid, is the same data as a basepoint of A,
   and the coslice triangle is pointwise exactly [preserves_pt]. *)
Definition SetsOne : SetoidObject := @terminal_obj Sets Sets_Terminal.

(* A basepoint, read as a global element.  The one-point pointed set has the
   terminal setoid underneath it, so the constant map at the basepoint already
   has the right type. *)
Definition pt_global (X : PointedSetoid) :
  SetsOne ~{Sets}~> pointed_setoid X := const_pt_map PointedOne X.

Program Definition Pointed_to_Coslice : PointedSets ⟶ Coslice Sets SetsOne := {|
  fobj := fun X => (pointed_setoid X; pt_global X);
  fmap := fun X Y f => (pointed_map f; _)
|}.
Next Obligation.
  intros X Y f u; simpl.
  symmetry.
  exact (preserves_pt f).
Qed.
Next Obligation.
  intros X Y f g Hfg u; simpl.
  exact (Hfg u).
Qed.
Next Obligation. intros X u; simpl; reflexivity. Qed.
Next Obligation. intros X Y Z f g u; simpl; reflexivity. Qed.

Program Definition Coslice_to_Pointed : Coslice Sets SetsOne ⟶ PointedSets := {|
  fobj := fun p => {| pointed_setoid := `1 p; pt := `2 p ttt |};
  fmap := fun x y h => Build_PointedMorphism _ _ (`1 h) _
|}.
Next Obligation.
  intros x y h; simpl.
  symmetry.
  exact (`2 h ttt).
Qed.
Next Obligation.
  intros x y h h' Hhh u; simpl.
  exact (Hhh u).
Qed.
Next Obligation. intros x u; simpl; reflexivity. Qed.
Next Obligation. intros x y z h k u; simpl; reflexivity. Qed.

(* Going Pointed → Coslice → Pointed returns the very same record, since the
   global element evaluated at the only point of 1 is the basepoint again; the
   comparison isomorphism is therefore the identity. *)
Lemma Coslice_Pointed_unit :
  Coslice_to_Pointed ◯ Pointed_to_Coslice ≈ Id[PointedSets].
Proof.
  exists (fun X => iso_id).
  intros X Y f u; simpl.
  reflexivity.
Qed.

(* Going Coslice → Pointed → Coslice replaces the structure map by the
   constant map at its value on the point.  These agree up to `≈` but not on
   the nose, so the comparison isomorphism is carried by the identity of the
   underlying setoid together with the triangle proofs.  The isomorphism is
   assembled through [Build_Isomorphism] rather than by record notation, so
   that it does not depend on the field names [to] and [from] being unshadowed
   at this point in the development. *)
Program Definition coslice_counit_iso (p : Coslice Sets SetsOne) :
  Pointed_to_Coslice (Coslice_to_Pointed p) ≅[Coslice Sets SetsOne] p :=
  @Build_Isomorphism (Coslice Sets SetsOne)
    (Pointed_to_Coslice (Coslice_to_Pointed p)) p
    (@id Sets (`1 p); _) (@id Sets (`1 p); _) _ _.
Next Obligation.
  intros p u; simpl.
  destruct u.
  reflexivity.
Qed.
Next Obligation.
  intros p u; simpl.
  destruct u.
  reflexivity.
Qed.
Next Obligation. intros p u; simpl; reflexivity. Qed.
Next Obligation. intros p u; simpl; reflexivity. Qed.

Lemma Coslice_Pointed_counit :
  Pointed_to_Coslice ◯ Coslice_to_Pointed ≈ Id[Coslice Sets SetsOne].
Proof.
  exists coslice_counit_iso.
  intros x y h u; simpl.
  reflexivity.
Qed.

(* Set_* IS the coslice of Sets under the one-point setoid — an isomorphism of
   categories, not merely an equivalence. *)
Definition Pointed_Coslice_iso : PointedSets ≅[Cat] Coslice Sets SetsOne :=
  @Build_Isomorphism Cat PointedSets (Coslice Sets SetsOne)
    Pointed_to_Coslice Coslice_to_Pointed
    Coslice_Pointed_counit Coslice_Pointed_unit.
