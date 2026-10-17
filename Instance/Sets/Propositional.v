Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cartesian.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Complete.

Generalizable All Variables.

(* * * Propositional equality 对象 homs [Sets] （已译） *)

(*
 nLab:    https://ncatlab.org/nlab/show/h-set
 Book:    The Univalent Foundations Program, "Homotopy Type Theory", IAS
 Book:    Mac Lane, "Categories for the Working Mathematician", 2nd ed.,

   本文件给出集合范畴相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* * ** The property, at level [Sets] 对象 （已译） *)

(*
   本节说明 Propositional 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition PropEquivObj (X : SetoidObject) : Type := PropEquiv (is_setoid X).

(** ** Hom-setoids *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance hom_PropEquiv {x y : SetoidObject} (Py : PropEquiv (is_setoid y)) :
  PropEquiv (@SetoidMorphism_Setoid x y).
Proof.
  unshelve refine
    {| pequiv := fun f g : SetoidMorphism x y =>
                   forall a : carrier x, @pequiv _ _ Py (f a) (g a) |}.
  - intros f g H a; exact (pequiv_to _ _ (H a)).
  - intros f g H a; exact (pequiv_from _ _ (H a)).
Defined.

(* 相关说明。 （已译） *)
Example hom_PropEquiv_is_Sets_homset (x y : SetoidObject) :
  @SetoidMorphism_Setoid x y = @homset Sets x y := eq_refl.

(* The 关系 it supplies pointwise one, read back at [eq_refl]. （已译） *)
Example hom_pequiv_is_pointwise {x y : SetoidObject}
  (Py : PropEquiv (is_setoid y)) (f g : x ~{Sets}~> y) :
  @pequiv _ _ (hom_PropEquiv Py) f g
    = (forall a : carrier x, @pequiv _ _ Py (f a) (g a)) := eq_refl.

(** ** Binary products *)

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance product_PropEquiv {x y : SetoidObject}
  (Px : PropEquiv (is_setoid x)) (Py : PropEquiv (is_setoid y)) :
  PropEquiv (is_setoid (@product_obj Sets Sets_Cartesian x y)).
Proof.
  unshelve refine
    {| pequiv := fun p q => @pequiv _ _ Px (fst p) (fst q)
                            /\ @pequiv _ _ Py (snd p) (snd q) |}.
  - intros p q [H1 H2]; exact (pequiv_to _ _ H1, pequiv_to _ _ H2).
  - intros p q H; split;
      [ exact (pequiv_from _ _ (fst H)) | exact (pequiv_from _ _ (snd H)) ].
Defined.

Example product_pequiv_is_componentwise {x y : SetoidObject}
  (Px : PropEquiv (is_setoid x)) (Py : PropEquiv (is_setoid y))
  (p q : carrier (@product_obj Sets Sets_Cartesian x y)) :
  @pequiv _ _ (product_PropEquiv Px Py) p q
    = (@pequiv _ _ Px (fst p) (fst q) /\ @pequiv _ _ Py (snd p) (snd q))
  := eq_refl.

(** ** Indexed products *)

(*
   本节说明 Propositional 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance iprod_PropEquiv {A : Type} (F : A -> SetoidObject)
  (H : forall i : A, PropEquiv (is_setoid (F i))) :
  PropEquiv (is_setoid (Sets_iprod_obj F)).
Proof.
  unshelve refine {| pequiv := fun g h => forall i : A, @pequiv _ _ (H i) (g i) (h i) |}.
  - intros g h Hgh i. exact (pequiv_to _ _ (Hgh i)).
  - intros g h Hgh i. exact (pequiv_from _ _ (Hgh i)).
Defined.

Example iprod_pequiv_is_pointwise {A : Type} (F : A -> SetoidObject)
  (H : forall i : A, PropEquiv (is_setoid (F i)))
  (g h : carrier (Sets_iprod_obj F)) :
  @pequiv _ _ (iprod_PropEquiv F H) g h
    = (forall i : A, @pequiv _ _ (H i) (g i) (h i)) := eq_refl.

(** ** Limits *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance limit_PropEquiv {D : Category} (F : D ⟶ Sets)
  (H : forall d : D, PropEquiv (is_setoid (F d))) :
  PropEquiv (is_setoid (Sets_limit_obj F)).
Proof.
  unshelve refine
    {| pequiv := fun p q : Sets_limit_carrier F =>
                   forall d : D, @pequiv _ _ (H d) (`1 p d) (`1 q d) |}.
  - intros p q Hpq d. exact (pequiv_to _ _ (Hpq d)).
  - intros p q Hpq d. exact (pequiv_from _ _ (Hpq d)).
Defined.

Example limit_pequiv_is_pointwise {D : Category} (F : D ⟶ Sets)
  (H : forall d : D, PropEquiv (is_setoid (F d)))
  (p q : Sets_limit_carrier F) :
  @pequiv _ _ (limit_PropEquiv F H) p q
    = (forall d : D, @pequiv _ _ (H d) (`1 p d) (`1 q d)) := eq_refl.

(* * ** Locally propositional 范畴 （已译） *)

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class LocallyPropositional (C : Category) := {
  locally_prop : forall x y : C, PropEquiv (@homset C x y)
}.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition LocallyPropositional_of_relation (C : Category)
  (R : forall x y : C, (x ~> y) -> (x ~> y) -> Prop)
  (to : forall (x y : C) (f g : x ~> y), R x y f g -> f ≈ g)
  (from : forall (x y : C) (f g : x ~> y), f ≈ g -> R x y f g) :
  LocallyPropositional C :=
  {| locally_prop := fun x y =>
       PropEquiv_of_relation (R x y) (to x y) (from x y) |}.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance Morphism_equality_PropEquiv {ob : Type}
  {hom : ob -> ob -> Type} (x y : ob) :
  PropEquiv (@Morphism_equality ob hom x y).
Proof.
  unshelve refine {| pequiv := @eq (hom x y) |}.
  - intros f g h; exact h.
  - intros f g h; exact h.
Defined.

(* The same statement for a whole category, as a transport rather than an
   instance: "C's hom-setoid IS strict equality" is not a property of an
   arbitrary [C] that instance resolution can check, so it is taken as a
   hypothesis. *)
Definition LocallyPropositional_of_eq (C : Category)
  (H : forall x y : C, @homset C x y = Morphism_equality x y) :
  LocallyPropositional C.
Proof.
  constructor.
  intros x y.
  rewrite (H x y).
  exact (Morphism_equality_PropEquiv x y).
Defined.
