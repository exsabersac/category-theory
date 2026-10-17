Require Import Category.Lib.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
 nLab:    https://ncatlab.org/nlab/show/h-set
 nLab:    https://ncatlab.org/nlab/show/mere+proposition
 Book:    The Univalent Foundations Program, "Homotopy Type Theory:
 Book:    Bishop, "Foundations of Constructive Analysis", McGraw-Hill 1967,
 Book:    Mac Lane, "Categories for the Working Mathematician", 2nd ed.,

   本文件给出 Propositional 相关定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Propositional 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class PropEquiv@{u p} {A : Type@{u}} (S : Setoid@{u p} A) := {
  pequiv : A -> A -> Prop;                              (* the Prop equality *)
  pequiv_to : forall x y, pequiv x y -> @equiv A S x y;   (* it implies `≈` *)
  pequiv_from : forall x y, @equiv A S x y -> pequiv x y  (* and follows from it *)
}.

(** ** Derived structure *)

Section Derived.

Context {A : Type}.
Context {S : Setoid A}.
Context {P : PropEquiv S}.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance pequiv_Equivalence : Equivalence (@pequiv A S P).
Proof.
  constructor.
  - intro x; exact (pequiv_from x x (reflexivity x)).
  - intros x y H; exact (pequiv_from y x (symmetry (pequiv_to x y H))).
  - intros x y z H1 H2;
      exact (pequiv_from x z (transitivity (pequiv_to x y H1) (pequiv_to y z H2))).
Defined.

(*
   本节说明 Propositional 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance pequiv_Equivalence_Prop :
  RelationClasses.Equivalence (@pequiv A S P).
Proof.
  constructor.
  - intro x; exact (pequiv_from x x (reflexivity x)).
  - intros x y H; exact (pequiv_from y x (symmetry (pequiv_to x y H))).
  - intros x y z H1 H2;
      exact (pequiv_from x z (transitivity (pequiv_to x y H1) (pequiv_to y z H2))).
Defined.

(* 相关说明。 （已译） *)
#[export] Instance pequiv_Proper :
  Proper (equiv ==> equiv ==> iff) (@pequiv A S P).
Proof.
  intros x x' Hx y y' Hy; split; intro H.
  - apply pequiv_from.
    rewrite <- Hx, <- Hy.
    exact (pequiv_to _ _ H).
  - apply pequiv_from.
    rewrite Hx, Hy.
    exact (pequiv_to _ _ H).
Qed.

(*
   本节说明 Propositional 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma pequiv_elim_inhabited (x y : A) : inhabited (x ≈ y) -> x ≈ y.
Proof using A S P.
  intro H.
  apply (pequiv_to x y).
  destruct H as [h].
  exact (pequiv_from x y h).
Qed.

End Derived.

(*
   本节说明 Propositional 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Arguments pequiv_elim_inhabited {A S P} x y _.

(*
   本节说明 Propositional 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition PropEquiv_of_relation@{u p} {A : Type@{u}} {S : Setoid@{u p} A}
  (R : A -> A -> Prop)
  (to : forall x y, R x y -> @equiv A S x y)
  (from : forall x y, @equiv A S x y -> R x y) : PropEquiv@{u p} S :=
  {| pequiv := R ; pequiv_to := to ; pequiv_from := from |}.

(* 相关说明。 （已译） *)

(* The discrete setoid: `≈` is Coq's [eq], which is already in [Prop].

     eq_PropEquiv@{u} : ∀ A : Type@{u}, PropEquiv@{u u} (eq_Setoid@{u} A)
     (* u |= u <= Logic_lemmas.equality.u0 *) *)
#[export] Instance eq_PropEquiv@{u} (A : Type@{u}) :
  PropEquiv@{u u} (eq_Setoid@{u} A).
Proof.
  unshelve refine {| pequiv := @eq A |}.
  - intros x y h; exact h.
  - intros x y h; exact h.
Defined.

(* The terminal setoid [poly_unit] under [eq].

     unit_PropEquiv@{t u} : PropEquiv@{t u} unit_setoid@{t u}
     (* t u |= t <= Logic_lemmas.equality.u0 *) *)
#[export] Instance unit_PropEquiv@{t u} : PropEquiv@{t u} unit_setoid@{t u}.
Proof.
  unshelve refine {| pequiv := @eq poly_unit@{t} |}.
  - intros x y h; exact h.
  - intros x y h; exact h.
Defined.

(* The standard finite types under [eq].

     Fin_PropEquiv@{} : ∀ {n : nat}, PropEquiv@{Set Set} Fin_Setoid *)
#[export] Instance Fin_PropEquiv {n} : PropEquiv (@Fin_Setoid n).
Proof.
  unshelve refine {| pequiv := @eq (Fin.t n) |}.
  - intros x y h; exact h.
  - intros x y h; exact h.
Defined.

(* The pointwise setoid on a dependent function space: propositional
   pointwise, given that the codomain is propositional.

     funext_PropEquiv@{u u0 u1 u2 u3 u4} :
       ∀ {T : Type@{u}} (t : T → Type@{u0}) (a b : T)
         {Sb : Setoid@{u0 u4} (t b)},
       PropEquiv@{u0 u4} Sb → PropEquiv@{u0 u1} (funext_Setoid t a b)
     (* u4 < u2, u0 <= u1, u0 <= u3, u2 <= u3, u4 <= u1 *) *)
#[export] Instance funext_PropEquiv {T : Type} (t : T -> Type) (a b : T)
  {Sb : Setoid (t b)} (Pb : PropEquiv Sb) :
  PropEquiv (@funext_Setoid T t a b Sb).
Proof.
  unshelve refine {| pequiv := fun f g => forall x : t a, @pequiv _ _ Pb (f x) (g x) |}.
  - intros f g H x; exact (pequiv_to _ _ (H x)).
  - intros f g H x; exact (pequiv_from _ _ (H x)).
Defined.

(* 相关说明。 （已译） *)

(* The non-dependent function setoid.

     fun_PropEquiv@{u u0 u1 u2 u3 u4 u5 u6} :
       ∀ {A : Type@{u}} {B : Type@{u0}} {SB : Setoid@{u0 u6} B},
       PropEquiv@{u0 u6} SB → PropEquiv@{u1 u2} (fun_setoid A B)
     (* u6 < u3, u <= u1, u <= u2, u0 <= u1, u0 <= u4, u0 <= u5,
        u3 <= u4, u6 <= u2, u6 <= u5 *) *)
#[export] Instance fun_PropEquiv {A : Type} {B : Type} {SB : Setoid B}
  (PB : PropEquiv SB) : PropEquiv (@fun_setoid A B SB).
Proof.
  unshelve refine {| pequiv := fun f g => forall x : A, @pequiv _ _ PB (f x) (g x) |}.
  - intros f g H x; exact (pequiv_to _ _ (H x)).
  - intros f g H x; exact (pequiv_from _ _ (H x)).
Defined.

(*
   本节说明 Propositional 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance prod_PropEquiv {A B : Type} {SA : Setoid A} {SB : Setoid B}
  (PA : PropEquiv SA) (PB : PropEquiv SB) :
  PropEquiv (@prod_setoid A B SA SB).
Proof.
  unshelve refine
    {| pequiv := fun x y => @pequiv _ _ PA (fst x) (fst y)
                            /\ @pequiv _ _ PB (snd x) (snd y) |}.
  - intros x y [H1 H2]; exact (pequiv_to _ _ H1, pequiv_to _ _ H2).
  - intros x y H; split;
      [ exact (pequiv_from _ _ (fst H)) | exact (pequiv_from _ _ (snd H)) ].
Defined.

(* The coproduct setoid: same injection and equivalent contents.

     sum_PropEquiv@{u u0 u1 u2 u3 u4} :
       ∀ {A : Type@{u}} {B : Type@{u0}} {SA : Setoid@{u u3} A}
         {SB : Setoid@{u0 u4} B},
       PropEquiv@{u u3} SA → PropEquiv@{u0 u4} SB →
       PropEquiv@{u1 u2} sum_setoid
     (* u <= u1, u0 <= u1, u3 <= u2, u4 <= u2, plus the stdlib bounds
        u2 <= sum_rect.u0, u3 <= False_rect.u0, u4 <= False_rect.u0 *) *)
#[export] Instance sum_PropEquiv {A B : Type} {SA : Setoid A} {SB : Setoid B}
  (PA : PropEquiv SA) (PB : PropEquiv SB) :
  PropEquiv (@sum_setoid A B SA SB).
Proof.
  unshelve refine
    {| pequiv := fun x y =>
         match x, y with
         | inl x, inl y => @pequiv _ _ PA x y
         | inr x, inr y => @pequiv _ _ PB x y
         | _, _ => False
         end |}.
  - intros [x|x] [y|y] H; simpl in *; try contradiction;
      [ exact (@pequiv_to _ _ PA x y H) | exact (@pequiv_to _ _ PB x y H) ].
  - intros [x|x] [y|y] H; simpl in *; try contradiction;
      [ exact (@pequiv_from _ _ PA x y H) | exact (@pequiv_from _ _ PB x y H) ].
Defined.

(*
   本节说明 Propositional 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance option_PropEquiv {A : Type} {SA : Setoid A}
  (PA : PropEquiv SA) : PropEquiv (@option_setoid A SA).
Proof.
  unshelve refine
    {| pequiv := fun x y =>
         match x, y with
         | Some x, Some y => @pequiv _ _ PA x y
         | None, None => True
         | _, _ => False
         end |}.
  - intros [x|] [y|] H; simpl in *; try contradiction.
    + exact (@pequiv_to _ _ PA x y H).
    + exact I.
  - intros [x|] [y|] H; simpl in *; try contradiction.
    + exact (@pequiv_from _ _ PA x y H).
    + exact I.
Defined.

(* The list setoid. [list_equiv] (Lib/Datatypes.v) [Type]-valued
 fixpoint using `∧` = [prod]; [Prop] 镜像 below uses [and], two
 蕴含 structural inductions. （已译） *)
Fixpoint list_pequiv {A : Type} {SA : Setoid A} (PA : PropEquiv SA)
  (xs ys : list A) : Prop :=
  match xs, ys with
  | nil, nil => True
  | cons x xs, cons y ys => @pequiv _ _ PA x y /\ list_pequiv PA xs ys
  | _, _ => False
  end.

(*   list_PropEquiv@{u u0} :
       ∀ {A : Type@{u}} {SA : Setoid@{u u0} A},
       PropEquiv@{u u0} SA → PropEquiv@{u u0} list_setoid
     (* u u0 |= u <= list_rect.u0, u <= list_rect.u1, u <= list_ind.u0,
        u0 <= False_rect.u0, u0 <= projections.u0, u0 <= projections.u1,
        u0 <= list_rect.u0 *) *)
#[export] Instance list_PropEquiv {A : Type} {SA : Setoid A}
  (PA : PropEquiv SA) : PropEquiv (@list_setoid A SA).
Proof.
  unshelve refine {| pequiv := list_pequiv PA |}.
  - intro xs; induction xs as [|x xs IH]; intros [|y ys] H;
      simpl in *; try contradiction.
    + exact I.
    + exact (@pequiv_to _ _ PA x y (proj1 H), IH ys (proj2 H)).
  - intro xs; induction xs as [|x xs IH]; intros [|y ys] H;
      simpl in *; try contradiction.
    + exact I.
    + exact (conj (@pequiv_from _ _ PA x y (fst H)) (IH ys (snd H))).
Defined.

(*
   本节说明 Propositional 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance nat_PropEquiv : PropEquiv nat_setoid.
Proof.
  unshelve refine {| pequiv := @eq nat |}.
  - intros x y h; exact h.
  - intros x y h; exact h.
Defined.

(* 相关说明。 （已译） *)

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition dep_fun_PropEquiv {I : Type} {A : I -> Type}
  {SA : forall i : I, Setoid (A i)} (S : Setoid (forall i : I, A i))
  (to : forall f g : forall i : I, A i,
          (forall i : I, @equiv (A i) (SA i) (f i) (g i)) -> @equiv _ S f g)
  (from : forall f g : forall i : I, A i,
            @equiv _ S f g -> forall i : I, @equiv (A i) (SA i) (f i) (g i))
  (H : forall i : I, PropEquiv (SA i)) : PropEquiv S.
Proof.
  unshelve refine
    {| pequiv := fun f g => forall i : I, @pequiv _ _ (H i) (f i) (g i) |}.
  - intros f g Hfg.
    apply to; intro i; exact (pequiv_to _ _ (Hfg i)).
  - intros f g Hfg i.
    exact (pequiv_from _ _ (from _ _ Hfg i)).
Defined.

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sigma_first_PropEquiv {A : Type} {SA : Setoid A} {P : A -> Type}
  (S : Setoid (@sigT A P))
  (to : forall p q : @sigT A P,
          @equiv A SA (projT1 p) (projT1 q) -> @equiv _ S p q)
  (from : forall p q : @sigT A P,
            @equiv _ S p q -> @equiv A SA (projT1 p) (projT1 q))
  (PA : PropEquiv SA) : PropEquiv S.
Proof.
  unshelve refine
    {| pequiv := fun p q => @pequiv _ _ PA (projT1 p) (projT1 q) |}.
  - intros p q Hpq.
    apply to; exact (pequiv_to _ _ Hpq).
  - intros p q Hpq.
    exact (pequiv_from _ _ (from _ _ Hpq)).
Defined.
