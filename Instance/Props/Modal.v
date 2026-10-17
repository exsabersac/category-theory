Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Adjunction.
Require Import Category.Comonad.Core.
Require Import Category.Comonad.Coalgebra.
Require Import Category.Comonad.Duality.
Require Import Category.Structure.Thin.Monad.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cartesian.Closed.Adjunction.
Require Import Category.Instance.Props.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Monotone.
Require Import Category.Instance.Proset.Monad.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(** * The modal operator B ⇒ − on propositions *)

(*
 nLab: https://ncatlab.org/nlab/show/closure+operator
 Book: Fong and Spivak, "Seven Sketches in Compositionality", arXiv v3,
 Book: Awodey, "Category Theory" (1st ed., CMU pre-print, Sept 2005),

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The operator and its two axioms *)

(* j p := B → p, an endofunctor of the entailment preorder [Props]; its
   law fields are [I], the hom-setoid of [Props] being [True]. *)
Definition modal_functor@{u h} (B : Prop) : Props@{u h} ⟶ Props@{u h} :=
  @Build_Functor Props@{u h} Props@{u h} (fun p => B → p)
    (fun p q (f : Basics.impl p q) (g : B → p) (b : B) => f (g b))
    (fun _ _ _ _ _ => I) (fun _ => I) (fun _ _ _ _ _ => I).

(* Seven Sketches Example 1.123's two axioms: p ⇒ j(p), and
   j(j(p)) = j(p), read as mutual entailment. *)
Definition modal_ext@{} (B p : Prop) : p → (B → p) := fun x _ => x.

(* The multiplication, a transparent term: the assumption used twice. *)
Definition modal_mult@{} (B p : Prop) : (B → (B → p)) → (B → p) :=
  fun f b => f b b.

Definition modal_idem@{} (B p : Prop) : (B → (B → p)) <-> (B → p) :=
  conj (modal_mult B p) (modal_ext B (B → p)).

(* The book's equation itself, under propositional extensionality taken
   as a hypothesis. *)
Lemma modal_idem_ext@{} (propext : ∀ P Q : Prop, (P <-> Q) → P = Q)
  (B p : Prop) : (B → (B → p)) = (B → p).
Proof. exact (propext _ _ (modal_idem B p)). Qed.

(* The monad: unit the first axiom, multiplication the forward half of
   the second, every law [I]. *)
Definition modal_monad@{u h} (B : Prop) :
  @Monad Props@{u h} (modal_functor@{u h} B) :=
  @Build_Monad Props@{u h} (modal_functor@{u h} B)
    (modal_ext B) (modal_mult B)
    (fun _ _ _ => I) (fun _ => I) (fun _ => I) (fun _ => I)
    (fun _ _ _ => I).

(* Its join computes: it is the term f ↦ (b ↦ f b b). *)
Example modal_monad_join@{u h} (B p : Prop) (f : B → (B → p)) (b : B) :
  @join _ _ (modal_monad@{u h} B) p f b = f b b := eq_refl.

(* It IS Structure/Thin/Monad.v's [thin_monad] at [Props] with the
   witness [fun _ _ _ _ => I], on the WHOLE record: that constructor's
   law fields reduce to [I] by beta. *)
Example modal_monad_is_thin@{u h t} (B : Prop) :
  modal_monad@{u h} B
    = @thin_monad@{t u h} Props@{u h} (fun _ _ _ _ => I)
        (modal_functor@{u h} B) (modal_ext B) (modal_mult B) := eq_refl.

(* Its algebras are the j-closed propositions, (B → p) → p. *)
Definition modal_talgebra_iff@{u h +} (B p : Prop) :
  @TAlgebra Props@{u h} (modal_functor B) (modal_monad B) p
    ↔ ((B → p) → p) :=
  (fun a => @t_alg Props@{u h} (modal_functor B) (modal_monad B) p a,
   fun h => @Build_TAlgebra Props@{u h} (modal_functor B) (modal_monad B) p
              h I I).

Example modal_talgebra_round@{u h p} (B p : Prop) (h : (B → p) → p) :
  match modal_talgebra_iff@{u h p} B p with
  | (to_closed, of_closed) => to_closed (of_closed h)
  end = h := eq_refl.

(* Non-vacuity: at B := False the proposition False is not closed. *)
Lemma modal_false_not_closed@{u h} :
  @TAlgebra Props@{u h} (modal_functor False) (modal_monad False) False
    → False.
Proof.
  intro a. destruct (modal_talgebra_iff False False) as [to_closed _].
  exact (to_closed a (fun x => x)).
Qed.

(** ** The monad of the currying adjunction (− ∧ B) ⊣ (B ⇒ −) *)

(* The two composites of Structure/Cartesian/Closed/Adjunction.v's
   [Prod_Functor B] and [Exp_Functor B] at [Props], for a closed
   structure [CL] (in use, always [Props_Closed]).  Taking [CL] as an
   argument keeps its exponential level e in the type: [Exp_Functor] and
   [Prod_Functor] each carry a level absent from their own types, pinned
   here to e. *)
Definition curry_functor@{u h e | h < e +}
  (CL : @Closed@{u h e} Props@{u h} Props_Cartesian@{u h}) (B : Prop) :
  Props@{u h} ⟶ Props@{u h} :=
  @Compose@{u u u e h} Props@{u h} Props@{u h} Props@{u h}
    (@Exp_Functor@{u h e e} Props@{u h} _ CL B)
    (@Prod_Functor@{u h e e} Props@{u h} _ B).

Definition curry_cofunctor@{u h e | h < e +}
  (CL : @Closed@{u h e} Props@{u h} Props_Cartesian@{u h}) (B : Prop) :
  Props@{u h} ⟶ Props@{u h} :=
  @Compose@{u u u e h} Props@{u h} Props@{u h} Props@{u h}
    (@Prod_Functor@{u h e e} Props@{u h} _ B)
    (@Exp_Functor@{u h e e} Props@{u h} _ CL B).

(* The monad of [Curry_Adjunction B].  The adjunction's last level is
   free in its block and is pinned to h. *)
Definition curry_monad@{u h e | h < e +} (B : Prop) :
  @Monad Props@{u h} (curry_functor@{u h e} Props_Closed B) :=
  @Adjunction_Monad@{u h u h e h} Props@{u h} Props@{u h} _ _
    (@Curry_Adjunction@{u h e e h} Props@{u h} _ _ B).

(* Its functor is B ⇒ (− ∧ B), on the nose. *)
Example curry_monad_fobj@{u h e | h < e +} (B p : Prop) :
  fobj[curry_functor@{u h e} Props_Closed B] p = (B → p /\ B) := eq_refl.

(* It is not B ⇒ − by conversion (the equation of objects is refused),
   but the two functors are naturally isomorphic. *)
Lemma curry_modal_iso@{u h e + | h < e +} (B : Prop) :
  curry_functor@{u h e} Props_Closed B ≈ modal_functor@{u h} B.
Proof.
  unshelve eexists.
  - intro p. unshelve refine (@Build_Isomorphism Props _ _ _ _ I I).
    + exact (fun f b => proj1 (f b)).
    + exact (fun f b => conj (f b) b).
  - intros; exact I.
Qed.

(* Under propositional extensionality, taken as a hypothesis, the two
   object maps agree, so no proof of their difference can exist unless
   that axiom is refuted. *)
Lemma curry_modal_fobj_ext@{u h e | h < e +}
  (propext : ∀ P Q : Prop, (P <-> Q) → P = Q) (B p : Prop) :
  fobj[curry_functor@{u h e} Props_Closed B] p = fobj[modal_functor@{u h} B] p.
Proof.
  apply propext. split.
  - exact (fun f b => proj1 (f b)).
  - exact (fun f b => conj (f b) b).
Qed.

Definition curry_talgebra_iff@{u h e + | h < e +} (B p : Prop) :
  @TAlgebra Props@{u h} _ (curry_monad@{u h e} B) p
    ↔ ((B → p /\ B) → p) :=
  (fun a => @t_alg Props@{u h} _ (curry_monad@{u h e} B) p a,
   fun h => @Build_TAlgebra Props@{u h} _ (curry_monad@{u h e} B) p
              h I I).

(* The two monads have the same closed elements. *)
Definition curry_modal_closed_iff@{} (B p : Prop) :
  ((B → p /\ B) → p) <-> ((B → p) → p) :=
  conj (fun h f => h (fun b => conj (f b) b))
       (fun h f => h (fun b => proj1 (f b))).

(** ** The dual: the comonad of the same adjunction, B ∧ − *)

(* [Adjunction_Comonad]'s level u4 (sixth in its binder) occurs in neither
   its type nor its block; it is pinned to h, as is the adjunction's last
   level. *)
Definition curry_comonad@{u h e | h < e +} (B : Prop) :
  @Comonad Props@{u h} (curry_cofunctor@{u h e} Props_Closed B) :=
  @Adjunction_Comonad@{u h u h e h h} Props@{u h} Props@{u h} _ _
    (@Curry_Adjunction@{u h e e h} Props@{u h} _ _ B).

Example curry_comonad_fobj@{u h e | h < e +} (B p : Prop) :
  fobj[curry_cofunctor@{u h e} Props_Closed B] p = ((B → p) /\ B) := eq_refl.

(* The interior operator it defines is B ∧ −, up to mutual entailment. *)
Definition curry_comonad_is_and@{} (B p : Prop) :
  ((B → p) /\ B) <-> (B /\ p) :=
  conj (fun '(conj f b) => conj b (f b))
       (fun '(conj b x) => conj (fun _ => x) b).

Definition curry_wcoalgebra_iff@{u h e + | h < e +} (B p : Prop) :
  @WCoalgebra Props@{u h} _ (curry_comonad@{u h e} B) p
    ↔ (p → (B → p) /\ B) :=
  (fun c => @w_coalg Props@{u h} _ (curry_comonad@{u h e} B) p c,
   fun h => @Build_WCoalgebra Props@{u h} _ (curry_comonad@{u h e} B) p
              h I I).

(* Its open elements are the propositions that entail B. *)
Definition curry_open_iff_entails@{} (B p : Prop) :
  (p → (B → p) /\ B) <-> (p → B) :=
  conj (fun h x => proj2 (h x)) (fun h x => conj (fun _ => x) (h x)).

(** ** The same operator on the preorder of propositions *)

Definition impl_PreOrder@{} : PreOrder Basics.impl :=
  {| PreOrder_Reflexive := fun _ x => x
   ; PreOrder_Transitive := fun _ _ _ f g x => g (f x) |}.

Definition modal_mono@{u} (B : Prop) :
  @MonotoneFun@{u u} Prop Basics.impl Prop Basics.impl :=
  {| mono_map := fun p => B → p
   ; mono_pres := fun p q (f : Basics.impl p q) =>
       (fun g b => f (g b)) : Basics.impl (B → p) (B → q) |}.

Definition modal_closure@{u} (B : Prop) : ClosureOperator@{u} impl_PreOrder :=
  {| cl_fun  := modal_mono B
   ; cl_ext  := modal_ext B
   ; cl_mult := modal_mult B |}.

(* [Props] is not [Proset impl_PreOrder] by conversion, so the two
   presentations are distinct terms; their functors agree on objects. *)
Example modal_closure_fobj@{u h} (B p : Prop) :
  fobj[closure_functor@{u h} (modal_closure@{u} B)] p
    = fobj[modal_functor@{u h} B] p := eq_refl.

(* And the two monads have the same unit and multiplication. *)
Example modal_closure_ret@{u h} (B p : Prop) :
  @ret _ _ (closure_monad@{u h} (modal_closure@{u} B)) p
    = @ret _ _ (modal_monad@{u h} B) p := eq_refl.

Example modal_closure_join@{u h} (B p : Prop) :
  @join _ _ (closure_monad@{u h} (modal_closure@{u} B)) p
    = @join _ _ (modal_monad@{u h} B) p := eq_refl.
