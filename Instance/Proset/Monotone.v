Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Two.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   本文件给出预序集相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Monotone maps, and the correspondence *)

Section Monotone.

Context {A : Type} {R : relation A} (P : PreOrder R).
Context {B : Type} {S : relation B} (Q : PreOrder S).

(* A monotone map between the underlying preorders: no decidability, no
   packaging — just the order-preserving function. *)
Record MonotoneFun := {
  mono_map :> A → B;
  mono_pres : ∀ x y, R x y → S (mono_map x) (mono_map y)
}.

(* The thin-category smart constructor: BECAUSE the target is a proset —
   every hom-setoid a subsingleton with the all-True equivalence — the
   functor laws cost nothing.  This is Seven Sketches §3.3.2's "the
   functor laws are automatic in a thin category", operationalized.
   The file sets [Obligation Tactic := idtac] (Pos.v's idiom), so the
   three laws are discharged explicitly: each is an equation between
   parallel morphisms in a thin target, hence [I]. *)
Program Definition Functor_of_monotone (f : MonotoneFun) :
  Proset P ⟶ Proset Q := {|
  fobj := mono_map f;
  fmap := fun x y (h : R x y) => mono_pres f x y h
|}.
Next Obligation. intros f x y g h Hgh; exact I. Qed.
Next Obligation. intros f x; exact I. Qed.
Next Obligation. intros f x y z g h; exact I. Qed.

(* The forward leg: a functor restricts to a monotone map on objects,
   monotonicity being the action on (unique) arrows. *)
Definition monotone_of_Functor (F : Proset P ⟶ Proset Q) : MonotoneFun := {|
  mono_map := fobj[F];
  mono_pres := fun x y h => fmap[F] h
|}.

(* Round trip on the monotone side: the same map, on the nose. *)
Lemma monotone_of_Functor_of_monotone (f : MonotoneFun) :
  mono_map (monotone_of_Functor (Functor_of_monotone f)) = mono_map f.
Proof. reflexivity. Qed.

(* Round trip on the functor side: the same functor up to the thin
   identification — a [Functor_Setoid] natural isomorphism whose
   components are identity arrows. *)
Lemma Functor_of_monotone_of_Functor (F : Proset P ⟶ Proset Q) :
  Functor_of_monotone (monotone_of_Functor F) ≈ F.
Proof.
  exists (fun x => iso_id).
  intros x y h; simpl.
  constructor.
Qed.

End Monotone.

(** ** Example 60: the 17/24 monotone map *)

(* The two-element order as a preorder on [bool]: false ≤ true. *)
Definition bool_le (a b : bool) : Prop := a = true → b = true.

#[export] Instance bool_le_preorder : PreOrder bool_le.
Proof.
  constructor.
  - intros a H; exact H.
  - intros a b c Hab Hbc H; exact (Hbc (Hab H)).
Qed.

(* The monotone map itself — the notion's first concrete inhabitant. *)
Program Definition seventeen_twentyfour :
  @MonotoneFun bool bool_le nat Nat.le := {|
  mono_map := fun b : bool => if b then 24%nat else 17%nat
|}.
Next Obligation.
  intros x y H; destruct x, y.
  - exact (le_n 24).
  - discriminate (H eq_refl).
  - repeat constructor.
  - exact (le_n 17).
Qed.

(* ...and its functor, through the smart constructor. *)
Definition Seventeen_TwentyFour_Proset :
  Proset bool_le_preorder ⟶ LessThanEqualTo_Category :=
  Functor_of_monotone bool_le_preorder Nat.le_preorder
    seventeen_twentyfour.

Example Seventeen_TwentyFour_Proset_bot :
  Seventeen_TwentyFour_Proset false = 17%nat := eq_refl.
Example Seventeen_TwentyFour_Proset_top :
  Seventeen_TwentyFour_Proset true = 24%nat := eq_refl.

(* The same map read out of the library's walking arrow [_2] —
   hand-built, since [_2] is not presented as a [Proset] (its homs are
   an inductive type compared by strict equality), so it sits outside
   the correspondence's domain. *)
Program Definition Seventeen_TwentyFour : _2 ⟶ LessThanEqualTo_Category := {|
  fobj := fun x => match x with TwoX => 17%nat | TwoY => 24%nat end;
  fmap := fun x y f => _
|}.
Next Obligation.
  intros x y f; destruct x, y.
  - exact (le_n 17).
  - repeat constructor.
  - inversion f.
  - exact (le_n 24).
Defined.
(* [_2]'s homset is strict equality, so the [Proper] law is inferred
   during elaboration; only the two remaining laws obligate, each an
   equation between parallel morphisms in a thin target. *)
Next Obligation. intros x; exact I. Qed.
Next Obligation. intros x y z f g; exact I. Qed.

Example Seventeen_TwentyFour_bot : Seventeen_TwentyFour TwoX = 17%nat
  := eq_refl.
Example Seventeen_TwentyFour_top : Seventeen_TwentyFour TwoY = 24%nat
  := eq_refl.

(** ** Example 3.42's payload: endofunctors of (ℕ, ≤) are the
    non-decreasing sequences *)

Definition nondecreasing (f : nat → nat) : Type :=
  ∀ m n : nat, (m <= n)%nat → (f m <= f n)%nat.

(* The pair is built with the family and both component types
   explicit: [x ~> y] in [LessThanEqualTo_Category] IS [x <= y] and
   its objects ARE [nat], but Coq 8.19/8.20's unifier declines to
   unfold the [hom] and [obj] projections inside the evar problems
   that infer a sigma pair's parts, while ascriptions route the same
   identifications through ordinary conversion, which every supported
   version performs. *)
Definition nondecreasing_of_endo
  (F : LessThanEqualTo_Category ⟶ LessThanEqualTo_Category) :
  { f : nat → nat & nondecreasing f } :=
  existT nondecreasing (fobj[F] : nat → nat)
    (fun m n (h : (m <= n)%nat) =>
       (fmap[F] h : (fobj[F] m <= fobj[F] n)%nat)).

Definition endo_of_nondecreasing
  (f : { f : nat → nat & nondecreasing f }) :
  LessThanEqualTo_Category ⟶ LessThanEqualTo_Category :=
  Functor_of_monotone Nat.le_preorder Nat.le_preorder
    {| mono_map := `1 f ; mono_pres := `2 f |}.

Example nondecreasing_round (f : { f : nat → nat & nondecreasing f }) :
  `1 (nondecreasing_of_endo (endo_of_nondecreasing f)) = `1 f := eq_refl.

(** ** Example 61: the tree of life, by generators *)

(* Five classification terms: a tiny fragment of the tree of life.
   The GENERATING edges point from the more specific to the more
   general term; the preorder is their reflexive-transitive closure. *)
Inductive Taxon : Set := Life | Animal | Plant | Mammal | Bird.

Inductive taxon_edge : Taxon → Taxon → Prop :=
  | edge_animal : taxon_edge Animal Life
  | edge_plant  : taxon_edge Plant Life
  | edge_mammal : taxon_edge Mammal Animal
  | edge_bird   : taxon_edge Bird Animal.

Definition taxon_le : relation Taxon := clos_refl_trans _ taxon_edge.

#[export] Instance taxon_le_preorder : PreOrder taxon_le.
Proof.
  constructor.
  - intro x; apply rt_refl.
  - intros x y z Hxy Hyz; exact (rt_trans _ _ _ _ _ Hxy Hyz).
Qed.

(* The three-element chain of ranks: species-level < kingdom-level <
   root, encoded as 0 < 1 < 2 under ≤. *)
Definition rank (t : Taxon) : nat :=
  match t with
  | Life => 2
  | Animal | Plant => 1
  | Mammal | Bird => 0
  end.

(* Monotonicity from the GENERATING relation: one case per edge — each
   generator raises the rank — and the two closure rules; the closure is
   never enumerated. *)
Lemma rank_monotone : ∀ s t, taxon_le s t → (rank s <= rank t)%nat.
Proof.
  intros s t H.
  induction H as [x y Hxy | x | x y z Hxy IH1 Hyz IH2].
  - destruct Hxy; simpl; repeat constructor.
  - reflexivity.
  - exact (Nat.le_trans _ _ _ IH1 IH2).
Qed.

Definition Taxonomy : Category := Proset taxon_le_preorder.

Definition taxonomy_rank : Taxonomy ⟶ LessThanEqualTo_Category :=
  Functor_of_monotone taxon_le_preorder Nat.le_preorder
    {| mono_map := rank ; mono_pres := rank_monotone |}.

Example taxonomy_rank_mammal : taxonomy_rank Mammal = 0%nat := eq_refl.
Example taxonomy_rank_life : taxonomy_rank Life = 2%nat := eq_refl.
