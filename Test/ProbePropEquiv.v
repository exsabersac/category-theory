Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cartesian.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.Cat.

(*
   本文件为测试：ProbePropEquiv。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Instrument check *)

(* A refusal expected around a name that is not there.  If the instrument were
   inert this line would pass silently and so would everything below it. *)
Fail Check zzz_no_such_constant_propequiv.

(** ** Positive controls: every constant the negatives sit beside *)

Check @PropEquiv.
Check @pequiv.
Check @pequiv_to.
Check @pequiv_from.
Check @PropEquiv_of_relation.
Check @pequiv_Equivalence.
Check @pequiv_Equivalence_Prop.
Check @pequiv_Proper.
Check @pequiv_elim_inhabited.

Check @eq_PropEquiv.
Check @unit_PropEquiv.
Check @Fin_PropEquiv.
Check @funext_PropEquiv.
Check @fun_PropEquiv.
Check @prod_PropEquiv.
Check @sum_PropEquiv.
Check @option_PropEquiv.
Check @list_PropEquiv.
Check @nat_PropEquiv.

Check @PropEquivObj.
Check @hom_PropEquiv.
Check @product_PropEquiv.
Check @iprod_PropEquiv.
Check @limit_PropEquiv.
Check @LocallyPropositional.
Check @locally_prop.
Check @LocallyPropositional_of_relation.
Check @Morphism_equality_PropEquiv.
Check @LocallyPropositional_of_eq.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check @Functor_Setoid.

Definition cat_equiv_is_data {C D : Category} (F G : C ⟶ D)
  (H : F ≈ G) (x : C) : F x ≅ G x := `1 H x.

(* [eq_PropEquiv] is registered, so instance resolution closes a [pequiv] goal
   at a discrete setoid with no explicit instance argument. *)
Example c_resolution (A : Type) (x y : A) : Prop := @pequiv A (eq_Setoid A) _ x y.

(* ... and the relation it resolves to is Coq's [eq], on the nose. *)
Example c_resolution_is_eq (A : Type) (x y : A) :
  @pequiv A (eq_Setoid A) (eq_PropEquiv A) x y = (x = y) := eq_refl.

(* [pequiv_elim_inhabited] takes its [PropEquiv] implicitly, so the one
   elimination the class buys elaborates with instance resolution alone. *)
Example c_elim (A : Type) (x y : A)
  (h : inhabited (@equiv A (eq_Setoid A) x y)) : @equiv A (eq_Setoid A) x y :=
  pequiv_elim_inhabited x y h.

(*
   本节说明 ProbePropEquiv 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition parity_rel (x y : nat) : Prop := Nat.even x = Nat.even y.

Definition parity_Equivalence : Equivalence parity_rel.
Proof.
  unfold parity_rel.
  constructor.
  - intro x; reflexivity.
  - intros x y H; symmetry; exact H.
  - intros x y z H1 H2; transitivity (Nat.even y); assumption.
Defined.

Definition parity_Setoid : Setoid nat :=
  {| equiv := parity_rel ; setoid_equiv := parity_Equivalence |}.

Definition parity_PropEquiv : PropEquiv parity_Setoid.
Proof.
  unshelve refine (PropEquiv_of_relation parity_rel _ _).
  - intros x y h; exact h.
  - intros x y h; exact h.
Defined.

Example c_parity_pequiv (x y : nat) :
  @pequiv nat parity_Setoid parity_PropEquiv x y = parity_rel x y := eq_refl.

(** ** Controls: the pointwise and componentwise transports read back *)

(* The hom-setoid of [Sets]: pointwise into the target. *)
Example c_hom_pointwise {x y : SetoidObject} (Py : PropEquiv (is_setoid y))
  (f g : x ~{Sets}~> y) :
  @pequiv _ _ (hom_PropEquiv Py) f g
    = (forall a : carrier x, @pequiv _ _ Py (f a) (g a)) := eq_refl.

(* Indexed products: pointwise in the index. *)
Example c_iprod_pointwise {A : Type} (F : A -> SetoidObject)
  (H : forall i : A, PropEquiv (is_setoid (F i)))
  (g h : carrier (Sets_iprod_obj F)) :
  @pequiv _ _ (iprod_PropEquiv F H) g h
    = (forall i : A, @pequiv _ _ (H i) (g i) (h i)) := eq_refl.

(* Limits: pointwise in the shape, the compatibility witness playing no part. *)
Example c_limit_pointwise {D : Category} (F : D ⟶ Sets)
  (H : forall d : D, PropEquiv (is_setoid (F d)))
  (p q : Sets_limit_carrier F) :
  @pequiv _ _ (limit_PropEquiv F H) p q
    = (forall d : D, @pequiv _ _ (H d) (`1 p d) (`1 q d)) := eq_refl.

(* The dependent-function setoid of Lib/Setoid.v. *)
Example c_funext_pointwise {T : Type} (t : T -> Type) (a b : T)
  {Sb : Setoid (t b)} (Pb : PropEquiv Sb) (f g : t a -> t b) :
  @pequiv _ _ (funext_PropEquiv t a b Pb) f g
    = (forall x : t a, @pequiv _ _ Pb (f x) (g x)) := eq_refl.

(* A [SetoidObject] that DOES have the property, as the control for
   NEGATIVE 3: the blanket instance is refused, individual ones are not. *)
Definition eq_SetoidObject (A : Type) : SetoidObject :=
  {| carrier := A ; is_setoid := eq_Setoid A |}.

Definition eq_SetoidObject_PropEquiv (A : Type) :
  PropEquiv (is_setoid (eq_SetoidObject A)) := eq_PropEquiv A.

(*
   本节说明 ProbePropEquiv 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition PropRelSpace@{u} (A : Type@{u}) : Type@{u} := A -> A -> Prop.

Definition PropEquiv_at_carrier@{u} (A : Type@{u}) (S : Setoid@{u u} A) :
  Type@{u} := PropEquiv@{u u} S.

(* Control for NEGATIVE 4: one universe up, the [Type]-valued relation space
   is accepted. *)
Definition CRelSpace@{u v} (A : Type@{u}) : Type@{v} := A -> A -> Type@{u}.

(* Control for NEGATIVE 5: one universe up, [Setoid] is accepted. *)
Definition Setoid_above_carrier@{u v} (A : Type@{u}) : Type@{v} := Setoid@{u u} A.

(*
   本节说明 ProbePropEquiv 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Definition cat_equiv_prop {C D : Category} (F G : C ⟶ D)
  (H : inhabited (F ≈ G)) (x : C) : F x ≅ G x :=
  match H with inhabits p => `1 p x end.

(*
   本节说明 ProbePropEquiv 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Definition eq_equiv_ascribed (A : Type) (x y : A) : Prop :=
  (@equiv A (eq_Setoid A) x y : Prop).

(*
   本节说明 ProbePropEquiv 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Definition sets_PropEquiv_generic (X : SetoidObject) :
  PropEquiv (is_setoid X) :=
  {| pequiv := fun x y => inhabited (@equiv _ (is_setoid X) x y)
   ; pequiv_to := fun x y H => match H with inhabits h => h end
   ; pequiv_from := fun x y h => inhabits h |}.

(*
   本节说明 ProbePropEquiv 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Definition CRelSpace_small@{u} (A : Type@{u}) : Type@{u} :=
  A -> A -> Type@{u}.

(*
   本节说明 ProbePropEquiv 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Definition Setoid_at_carrier@{u} (A : Type@{u}) : Type@{u} :=
  Setoid@{u u} A.
