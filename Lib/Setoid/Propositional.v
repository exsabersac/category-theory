Require Import Category.Lib.

Generalizable All Variables.

(** * Setoids whose equality is propositional *)

(*
 nLab:    https://ncatlab.org/nlab/show/h-set
 nLab:    https://ncatlab.org/nlab/show/mere+proposition
 Book:    The Univalent Foundations Program, "Homotopy Type Theory:
 Book:    Bishop, "Foundations of Constructive Analysis", McGraw-Hill 1967,
 Book:    Mac Lane, "Categories for the Working Mathematician", 2nd ed.,

   本文件给出 Propositional 相关定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* [PropEquiv S] says that the setoid [S] has a [Prop]-valued equality: a
   relation [pequiv] in [Prop] that holds exactly when `≈` does.

   MEASURED UNIVERSES (About under Set Printing Universes):

     PropEquiv@{u p} :
       ∀ {A : Type@{u}}, Setoid@{u p} A → Type@{max(Set+1,u,p)}

   -- so at the [Setoid@{u u}] used by [Sets] and by every concrete algebraic
   carrier the class itself lands at [Type@{u}], the CARRIER universe, provided
   [u] is above [Set].  The [Set+1] in the maximum is the sort of [Prop] and is
   not avoidable; it is also harmless, since [Unset Universe Minimization
   ToSet] (Lib.v) keeps carrier universes off [Set]. *)
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

(* [pequiv] inherits the equivalence laws by transporting each one across the
   two implications.  This is the ambient [Equivalence] of the library, i.e.
   the [Type]-valued one of Coq.Classes.CRelationClasses that Lib/Foundation.v
   exports; a [Prop]-valued relation inhabits a [crelation] by cumulativity. *)
#[export] Instance pequiv_Equivalence : Equivalence (@pequiv A S P).
Proof.
  constructor.
  - intro x; exact (pequiv_from x x (reflexivity x)).
  - intros x y H; exact (pequiv_from y x (symmetry (pequiv_to x y H))).
  - intros x y z H1 H2;
      exact (pequiv_from x z (transitivity (pequiv_to x y H1) (pequiv_to y z H2))).
Defined.

(* The same laws as an instance of the [Prop]-level class of
   Coq.Classes.RelationClasses, for callers whose rewriting machinery is the
   [Prop] one rather than the library's [Type]-valued [CMorphisms]. *)
#[export] Instance pequiv_Equivalence_Prop :
  RelationClasses.Equivalence (@pequiv A S P).
Proof.
  constructor.
  - intro x; exact (pequiv_from x x (reflexivity x)).
  - intros x y H; exact (pequiv_from y x (symmetry (pequiv_to x y H))).
  - intros x y z H1 H2;
      exact (pequiv_from x z (transitivity (pequiv_to x y H1) (pequiv_to y z H2))).
Defined.

(* [pequiv] respects `≈` in both arguments, up to [iff].  Note that [iff] here
   is Coq's [Prop]-valued biconditional, NOT the library's `↔`, which
   Lib/Foundation.v binds to [iffT]. *)
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

(* THE elimination [PropEquiv] buys.  [inhabited] is [Prop]-valued, so it
   eliminates only into [Prop]; the goal [x ≈ y] is in [Type] and is therefore
   out of reach directly.  Going through [pequiv] puts a [Prop] goal in front
   of the elimination, after which [pequiv_to] returns to `≈`.  Every
   truncation this library performs on an algebraic quotient is discharged by
   this one lemma. *)
Lemma pequiv_elim_inhabited (x y : A) : inhabited (x ≈ y) -> x ≈ y.
Proof using A S P.
  intro H.
  apply (pequiv_to x y).
  destruct H as [h].
  exact (pequiv_from x y h).
Qed.

End Derived.

(* [P] is left implicit so that the elimination above is usable with no
   instance argument: an implicit argument of class type is closed by instance
   resolution, which is what makes [pequiv_elim_inhabited x y h] elaborate
   wherever the setoid has a registered [PropEquiv]. *)
Arguments pequiv_elim_inhabited {A S P} x y _.

(* The constructor for a setoid whose `≈` already IS a [Prop]-valued relation.
   The relation has to be handed over by NAME: as the header says, writing
   [(x ≈ y : Prop)] is refused, since [equiv x y] is typed at [Type] whatever
   sits underneath.  Test/ProbePropEquiv.v pins that refusal. *)
Definition PropEquiv_of_relation@{u p} {A : Type@{u}} {S : Setoid@{u p} A}
  (R : A -> A -> Prop)
  (to : forall x y, R x y -> @equiv A S x y)
  (from : forall x y, @equiv A S x y -> R x y) : PropEquiv@{u p} S :=
  {| pequiv := R ; pequiv_to := to ; pequiv_from := from |}.

(** ** Instances for the setoid constructors of Lib/Setoid.v *)

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

(** ** Instances for the setoid constructors of Lib/Datatypes.v *)

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

(* The product setoid, componentwise.  The conjunction is Coq's [and] (written
   `/\`), not the library's `∧`, which Lib/Foundation.v binds to [prod] and
   which would put the relation back in [Type].

     prod_PropEquiv@{u u0 u1 u2 u3 u4} :
       ∀ {A : Type@{u}} {B : Type@{u0}} {SA : Setoid@{u u3} A}
         {SB : Setoid@{u0 u4} B},
       PropEquiv@{u u3} SA → PropEquiv@{u0 u4} SB →
       PropEquiv@{u1 u2} prod_setoid
     (* u <= u1, u0 <= u1, u3 <= u2, u4 <= u2, and the stdlib bounds
        u <= prod_rect.u1, u0 <= prod_rect.u2, u3 <= projections.u0,
        u4 <= projections.u1 *) *)
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

(* The option setoid.  [None ≈ None] is already the [Prop] [True], so the
   relation below agrees with `≈` on the nose at that clause.

     option_PropEquiv@{u u0} :
       ∀ {A : Type@{u}} {SA : Setoid@{u u0} A},
       PropEquiv@{u u0} SA → PropEquiv@{u u0} option_setoid
     (* u u0 |= u <= eq_ind.u0, u0 <= False_rect.u0 *) *)
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

(* The list setoid.  [list_equiv] (Lib/Datatypes.v) is a [Type]-valued
   fixpoint using `∧` = [prod]; the [Prop] mirror below uses [and], and the two
   implications are structural inductions. *)
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

(* [nat_setoid] (Lib/Datatypes.v) is declared as a bare [Program Instance]
   whose [equiv] field is left to instance resolution, which picks [eq].  The
   two implications below are therefore the identity, and the file's
   [Unset Transparent Obligations] does not stand in the way: the [equiv] field
   is resolved during elaboration rather than becoming an opaque obligation.

     nat_PropEquiv@{} : PropEquiv@{Set Set} nat_setoid *)
#[export] Instance nat_PropEquiv : PropEquiv nat_setoid.
Proof.
  unshelve refine {| pequiv := @eq nat |}.
  - intros x y h; exact h.
  - intros x y h; exact h.
Defined.

(** ** Transports for setoids built inline *)

(* The two shapes below are the ones the concrete algebraic categories reach
   for, and neither is one of the ten constructors above: a carrier that is a
   DEPENDENT FUNCTION SPACE compared pointwise (the product of a family of
   modules, Instance/Mod/Product.v; the standard vector space over a field,
   Instance/FdVect.v) and a carrier that is a SIGMA compared on its first
   projection (a kernel, Instance/Ab.v; a subgroup or submodule,
   Instance/Ab/DirectedColimit.v and Instance/Mod/Quotient.v; the centre
   of a group, Instance/Grp/Center.v).

   WHY BOTH TAKE THEIR TWO IMPLICATIONS AS ARGUMENTS.  Each of those sites
   writes the relation out inline inside a [Program Definition], so the setoid
   it produces is a NAMED constant whose [setoid_equiv] field is an opaque
   [Program] obligation.  A transport stated as [PropEquiv (canonical_setoid …)]
   would therefore have to unify that constant with a canonical one, and the two
   opaque obligation proofs are not convertible; the unification is refused even
   though the [equiv] fields agree on the nose.  Taking the two implications as
   explicit arguments sidesteps the record entirely: at every site above they
   are [fun _ _ h => h], since the relations ARE convertible, and the transport
   then applies to whichever setoid the site happens to have built.  This is a
   generalisation of the form these lemmas were first drafted in, which named
   the setoid.

   Measured (About under Set Printing Universes):

     dep_fun_PropEquiv@{u u0 u1 u2 u3} :
       ∀ {I : Type@{u}} {A : I → Type@{u0}} {SA : ∀ i : I, Setoid@{u0 u3} (A i)}
         (S : Setoid@{u1 u2} (∀ i : I, A i)),
       (∀ f g : ∀ i : I, A i,
          (∀ i : I, @equiv (A i) (SA i) (f i) (g i)) → @equiv _ S f g) →
       (∀ f g : ∀ i : I, A i,
          @equiv _ S f g → ∀ i : I, @equiv (A i) (SA i) (f i) (g i)) →
       (∀ i : I, PropEquiv@{u0 u3} (SA i)) → PropEquiv@{u1 u2} S
     (* u u0 u1 u2 u3 |= u <= u1, u0 <= u1 *)

   -- the target carrier universe [u1] is bounded below by the index and by the
   components and by nothing else, so a pointwise product of carrier-sized
   propositional setoids stays carrier-sized. *)
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

(* The sigma case.  Only the first projection is compared, so the second
   component's type [P] is arbitrary and no [Prop] mirror is asked of it: a
   kernel element's proof that it is killed, a subgroup element's proof of
   membership, are carried along and never inspected by `≈`.  That is why the
   membership predicates of the concrete algebra may stay [Type]-valued while
   their carriers become propositional.

   Measured:

     sigma_first_PropEquiv@{u u0 u1 u2 u3} :
       ∀ {A : Type@{u}} {SA : Setoid@{u u3} A} {P : A → Type@{u0}}
         (S : Setoid@{u1 u2} (@sigT A P)),
       (∀ p q : @sigT A P, @equiv A SA (projT1 p) (projT1 q) → @equiv _ S p q) →
       (∀ p q : @sigT A P, @equiv _ S p q → @equiv A SA (projT1 p) (projT1 q)) →
       PropEquiv@{u u3} SA → PropEquiv@{u1 u2} S
     (* u u0 u1 u2 u3 |= u <= u1, u0 <= u1, and the stdlib bounds
        u <= Projections.u0, u0 <= Projections.u1 *) *)
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
