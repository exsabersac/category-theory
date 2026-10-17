Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(** * A category read at higher universe levels *)

(*
 nLab: https://ncatlab.org/nlab/show/universe+enlargement (the general

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition LiftCat@{co ch xo xh +} (C : Category@{co ch ch}) :
  Category@{xo xh xh}.
Proof.
  unshelve refine
    {| obj := @obj C;
       hom := fun x y => @hom C x y;
       homset := fun x y =>
         {| equiv := fun f g => @equiv _ (@homset C x y) f g;
            setoid_equiv := _ |};
       id := fun x => @id C x;
       compose := fun x y z f g => @compose C x y z f g |}.
  - constructor.
    + intro f.
      exact (@Equivalence_Reflexive _ _ (@setoid_equiv _ (@homset C x y)) f).
    + intros f g H.
      exact (@Equivalence_Symmetric _ _ (@setoid_equiv _ (@homset C x y))
               f g H).
    + intros f g h H1 H2.
      exact (@Equivalence_Transitive _ _ (@setoid_equiv _ (@homset C x y))
               f g h H1 H2).
  - intros x y z f f2 Hf g g2 Hg.
    exact (@compose_respects C x y z f f2 Hf g g2 Hg).
  - intros x y f. exact (@id_left C x y f).
  - intros x y f. exact (@id_right C x y f).
  - intros x y z w f g h. exact (@comp_assoc C x y z w f g h).
  - intros x y z w f g h. exact (@comp_assoc_sym C x y z w f g h).
Defined.

Definition Lift_in@{co ch xo xh +} (C : Category@{co ch ch}) :
  C ⟶ LiftCat@{co ch xo xh} C.
Proof.
  unshelve refine (@Build_Functor C (LiftCat C)
    (fun x : C => x) (fun (x y : C) (f : x ~{C}~> y) => f) _ _ _).
  - intros x y f g H. exact H.
  - intros x. simpl. reflexivity.
  - intros x y z f g. simpl. reflexivity.
Defined.

Example Lift_in_fobj@{co ch xo xh +} (C : Category@{co ch ch}) (x : C) :
  fobj[Lift_in@{co ch xo xh} C] x = x := eq_refl.

Example Lift_in_fmap@{co ch xo xh +} (C : Category@{co ch ch}) {x y : C}
  (f : x ~{C}~> y) : fmap[Lift_in@{co ch xo xh} C] f = f := eq_refl.

Definition Lift_after@{co ch xo xh yo yh +}
  {C : Category@{co ch ch}} {X : Category@{xo xh xh}} (T : C ⟶ X) :
  C ⟶ LiftCat@{xo xh yo yh} X.
Proof.
  unshelve refine (@Build_Functor C (LiftCat X)
    (fun x : C => T x) (fun (x y : C) (f : x ~{C}~> y) => fmap[T] f)
    _ _ _).
  - intros x y f g H. exact (@fmap_respects _ _ T x y f g H).
  - intros x. exact (@fmap_id _ _ T x).
  - intros x y z f g. exact (@fmap_comp _ _ T x y z f g).
Defined.

Example Lift_after_fobj@{co ch xo xh yo yh +}
  {C : Category@{co ch ch}} {X : Category@{xo xh xh}} (T : C ⟶ X) (x : C) :
  fobj[Lift_after@{co ch xo xh yo yh} T] x = T x := eq_refl.

Example Lift_after_fmap@{co ch xo xh yo yh +}
  {C : Category@{co ch ch}} {X : Category@{xo xh xh}} (T : C ⟶ X)
  {x y : C} (f : x ~{C}~> y) :
  fmap[Lift_after@{co ch xo xh yo yh} T] f = fmap[T] f := eq_refl.
