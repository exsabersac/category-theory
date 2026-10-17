Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Reflective.Idempotent.
Require Import Category.Structure.Thin.
Require Import Category.Structure.Thin.Monad.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Poset.
Require Import Category.Instance.Proset.Order.
Require Import Category.Instance.Proset.Monotone.
Require Import Category.Instance.Proset.Galois.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Arith.PeanoNat.
From Coq Require Import Lia.

Generalizable All Variables.

(** * Monads on a preorder are closure operators *)

(*
 nLab: https://ncatlab.org/nlab/show/idempotent+monad
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 Book: Awodey, "Category Theory" (1st ed., CMU pre-print, Sept 2005),
 Book: Fong and Spivak, "Seven Sketches in Compositionality", arXiv v3,
 Book: Riehl, "Category Theory in Context", 2nd ed., SS 5.1,

   本文件给出单子相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Closure operators: Mac Lane's display (3) *)

(* Mac Lane's display (3) as the fields: a monotone map, extensivity
   (the unit) and the multiplication inequality. *)
Record ClosureOperator@{u} {A : Type@{u}} {R : relation A}
  (P : PreOrder R) := {
  cl_fun  : @MonotoneFun A R A R;
  cl_ext  : ∀ x, R x (cl_fun x);
  cl_mult : ∀ x, R (cl_fun (cl_fun x)) (cl_fun x)
}.

Arguments cl_fun {A R P} _.
Arguments cl_ext {A R P} _ _.
Arguments cl_mult {A R P} _ _.

(* Seven Sketches Definition 1.120 (b), derived: the inverse of the
   multiplication is extensivity at cl x. *)
Definition cl_idem@{u h} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (c : ClosureOperator@{u} P) (x : A) :
  cl_fun c (cl_fun c x) ≅[Proset@{u h} P] cl_fun c x :=
  @Build_Isomorphism (Proset@{u h} P) _ _
    (cl_mult c x) (cl_ext c (cl_fun c x)) I I.

(* The smart constructor from Definition 1.120's form. *)
Definition closure_of_iso@{u h} {A : Type@{u}} {R : relation A}
  (P : PreOrder R) (f : @MonotoneFun A R A R) (ext : ∀ x, R x (f x))
  (idem : ∀ x, f (f x) ≅[Proset@{u h} P] f x) : ClosureOperator@{u} P :=
  {| cl_fun  := f
   ; cl_ext  := ext
   ; cl_mult := fun x => to (idem x) |}.

Example closure_of_iso_to@{u h} {A : Type@{u}} {R : relation A}
  (P : PreOrder R) (f : @MonotoneFun A R A R) (ext : ∀ x, R x (f x))
  (idem : ∀ x, f (f x) ≅[Proset@{u h} P] f x) (x : A) :
  to (cl_idem@{u h} (closure_of_iso P f ext idem) x) = to (idem x)
  := eq_refl.

(** ** The correspondence *)

(* The endofunctor of the thin category, through Monotone.v. *)
Definition closure_functor@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) :
  Proset@{u h} P ⟶ Proset@{u h} P :=
  Functor_of_monotone P P (cl_fun c).

(* Closure → monad: every law is [I], the hom-setoid being [True]. *)
Definition closure_monad@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) :
  @Monad (Proset@{u h} P) (closure_functor c) :=
  @Build_Monad (Proset@{u h} P) (closure_functor c)
    (fun x => cl_ext c x) (fun x => cl_mult c x)
    (fun _ _ _ => I) (fun _ => I) (fun _ => I) (fun _ => I)
    (fun _ _ _ => I).

(* Monad → closure: the two inequalities are ret and join. *)
Definition closure_of_monad@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} : ClosureOperator@{u} P :=
  {| cl_fun  := monotone_of_Functor P P M
   ; cl_ext  := fun x => @ret _ M MM x
   ; cl_mult := fun x => @join _ M MM x |}.

(* The correspondence.  The pair is built with its family explicit, the
   8.19/8.20 idiom recorded in Monotone.v. *)
Definition monad_closure_iff@{u h +} {A : Type@{u}} {R : relation A}
  (P : PreOrder R) :
  { M : Proset@{u h} P ⟶ Proset@{u h} P & @Monad (Proset@{u h} P) M }
    ↔ ClosureOperator@{u} P :=
  (fun p => match p with existT _ M MM => closure_of_monad M (MM := MM) end,
   fun c => existT (fun M : Proset@{u h} P ⟶ Proset@{u h} P =>
                      @Monad (Proset@{u h} P) M)
              (closure_functor c) (closure_monad c)).

(** ** Round trips *)

(* [closure_monad] is Structure/Thin/Monad.v's [thin_monad], on the WHOLE
   record. *)
Example closure_monad_is_thin@{u h t} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) :
  closure_monad@{u h} c
    = @thin_monad@{t u h} (Proset@{u h} P) (fun _ _ _ _ => I)
        (closure_functor@{u h} c) (cl_ext c) (cl_mult c) := eq_refl.

(* closure → monad → closure is the identity on the WHOLE record. *)
Example closure_round_trip@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) :
  closure_of_monad@{u h} (closure_functor@{u h} c) (MM := closure_monad c)
    = c := eq_refl.

(* monad → closure → monad is the identity up to ≈ of functors; [=] is
   refused by conversion. *)
Definition monad_round_trip@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} :
  closure_functor (closure_of_monad M (MM := MM)) ≈ M :=
  Functor_of_monotone_of_Functor P P M.

(* ...but its object and arrow maps are M's on the nose. *)
Example monad_round_trip_fobj@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x : A) :
  fobj[closure_functor (closure_of_monad M (MM := MM))] x = fobj[M] x
  := eq_refl.

Example monad_round_trip_fmap@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x y : A) (f : R x y) :
  fmap[closure_functor (closure_of_monad M (MM := MM))] f = fmap[M] f
  := eq_refl.

(* ...and the monad it rebuilds has M's unit and multiplication. *)
Example monad_round_trip_ret@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x : A) :
  @ret _ _ (closure_monad (closure_of_monad M (MM := MM))) x = @ret _ M MM x
  := eq_refl.

Example monad_round_trip_join@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x : A) :
  @join _ _ (closure_monad (closure_of_monad M (MM := MM))) x
    = @join _ M MM x := eq_refl.

(** ** Algebras are the closed elements *)

(* Mac Lane p. 141: an algebra is exactly an x with Tx ≤ x. *)
Definition talgebra_iff_closed@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x : A) :
  @TAlgebra (Proset@{u h} P) M MM x ↔ R (M x) x :=
  (fun alg => @t_alg (Proset@{u h} P) M MM x alg,
   fun h => @Build_TAlgebra (Proset@{u h} P) M MM x h I I).

Example talgebra_round@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x : A) (h : R (M x) x) :
  match talgebra_iff_closed M x with
  | (to_closed, of_closed) => to_closed (of_closed h)
  end = h := eq_refl.

(* "x ≤ Tx ≤ x": closed means Tx ≅ x. *)
Definition closed_iff_fixed@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x : A) :
  R (M x) x ↔ (M x ≅[Proset@{u h} P] x) :=
  (fun h => @Build_Isomorphism (Proset@{u h} P) _ _ h (@ret _ M MM x) I I,
   fun i => to i).

(* Idempotent.v's M-local objects (ret x invertible) are the closed ones. *)
Definition mlocal_iff_closed@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x : A) :
  sobj (Proset@{u h} P) (@MLocal_Subcategory (Proset@{u h} P) M MM) x
    ↔ R (M x) x :=
  (fun H => @two_sided_inverse _ _ _ _ H,
   fun h => @Build_IsIsomorphism (Proset@{u h} P) x (M x)
              (@ret _ M MM x) h I I).

(* The same, by instantiating Idempotent.v at the thin witness.  [Qed]
   keeps four body-only universe levels private (see the header). *)
Lemma talgebra_iff_closed_via_idem@{u h +} {A : Type@{u}}
  {R : relation A} {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x : A) :
  @TAlgebra (Proset@{u h} P) M MM x ↔ R (M x) x.
Proof.
  exact (let IM := thin_IdempotentMonad (Order.proset_thin P) (MM := MM) in
         let (to_closed, of_closed) := mlocal_iff_closed M x in
         (fun alg => to_closed (@algebra_ret_iso _ M MM IM x alg),
          fun h => @local_algebra _ M MM IM x (of_closed h))).
Qed.

(** ** The Eilenberg-Moore category and the reflection, instantiated *)

(* The Eilenberg-Moore category is equivalent to the closed elements. *)
Definition proset_EM_equivalence@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} :=
  @Idempotent_EM_Equivalence (Proset@{u h} P) M MM
    (thin_IdempotentMonad (Order.proset_thin P)).

(* The reflection onto the closed elements, t ⊣ i. *)
Definition proset_fixed_adj@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} :=
  @idem_reflective_adj (Proset@{u h} P) M MM
    (thin_IdempotentMonad (Order.proset_thin P)).

(* T = i ∘ t on objects, on the nose. *)
Example proset_factorisation_obj@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x : A) :
  fobj[Incl (Proset@{u h} P) (@MLocal_Subcategory (Proset@{u h} P) M MM)
         ◯ @idem_reflector (Proset@{u h} P) M MM
             (thin_IdempotentMonad (Order.proset_thin P))] x = M x
  := eq_refl.

(* ...and on arrows. *)
Example proset_factorisation_fmap@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x y : A) (f : R x y) :
  fmap[Incl (Proset@{u h} P) (@MLocal_Subcategory (Proset@{u h} P) M MM)
         ◯ @idem_reflector (Proset@{u h} P) M MM
             (thin_IdempotentMonad (Order.proset_thin P))] f = fmap[M] f
  := eq_refl.

(** ** Partial orders: antisymmetry turns ≅ into = *)

(* Mac Lane p. 141: in a partial order an algebra is a fixed point. *)
Lemma closed_eq@{u h} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (AS : @Antisymmetric A eq eq_equiv R)
  (M : Proset@{u h} P ⟶ Proset@{u h} P) {MM : @Monad (Proset@{u h} P) M}
  (x : A) : @TAlgebra (Proset@{u h} P) M MM x → M x = x.
Proof. intro alg. exact (AS _ _ (@t_alg _ _ _ _ alg) (@ret _ M MM x)). Qed.

(* Mac Lane p. 139: in a partial order T(Tx) = Tx. *)
Lemma closure_idem_eq@{u} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (AS : @Antisymmetric A eq eq_equiv R) (c : ClosureOperator@{u} P)
  (x : A) : cl_fun c (cl_fun c x) = cl_fun c x.
Proof. exact (AS _ _ (cl_mult c x) (cl_ext c (cl_fun c x))). Qed.

(* A monad on a [Poset] is accepted as it stands. *)
Example poset_closure_of_monad@{u h} {A : Type@{u}} {R : relation A}
  (P : PreOrder R) (AS : @Antisymmetric A eq eq_equiv R)
  (M : @Poset A R P AS ⟶ @Poset A R P AS)
  {MM : @Monad (@Poset A R P AS) M} : ClosureOperator@{u} P :=
  closure_of_monad@{u h} M (MM := MM).

(** ** Witnesses *)

(* Monotone and extensive, yet not a monad: join at 0 would be 2 ≤ 1. *)
Theorem succ_not_monad@{u h} :
  @Monad (Proset@{u h} Nat.le_preorder) NatSucc@{u h u} → False.
Proof.
  intro MM.
  pose proof (@join _ NatSucc MM 0%nat) as H.
  simpl in H.
  lia.
Qed.

(* n ↦ max k n, a closure operator on (ℕ, ≤)... *)
Definition max_mono@{u} (k : nat) : @MonotoneFun@{u u} nat Nat.le nat Nat.le :=
  {| mono_map := Nat.max k
   ; mono_pres := fun x y H => Nat.max_le_compat_l x y k H |}.

Lemma max_mult@{} (k n : nat) : (Nat.max k (Nat.max k n) <= Nat.max k n)%nat.
Proof. lia. Qed.

Definition max_closure@{u} (k : nat) : ClosureOperator@{u} Nat.le_preorder :=
  {| cl_fun  := max_mono k
   ; cl_ext  := fun n => Nat.le_max_r k n
   ; cl_mult := fun n => max_mult k n |}.

(* ...whose algebras are exactly the n above k. *)
Lemma max_closed_iff@{u h +} (k n : nat) :
  @TAlgebra (Proset@{u h} Nat.le_preorder)
    (closure_functor@{u h} (max_closure@{u} k))
    (closure_monad@{u h} (max_closure@{u} k)) n ↔ (k <= n)%nat.
Proof.
  destruct (talgebra_iff_closed (closure_functor (max_closure k))
              (MM := closure_monad (max_closure k)) n) as [to_closed of_closed].
  split.
  - intro alg. pose proof (to_closed alg) as H. simpl in H. lia.
  - intro H. apply of_closed. simpl. lia.
Qed.
