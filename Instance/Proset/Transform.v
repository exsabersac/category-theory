Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Proset.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(** * Natural transformations into a preorder *)

(*
 nLab:  https://ncatlab.org/nlab/show/thin+category
 Book:  Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 Book:  Fong and Spivak, "Seven Sketches in Compositionality", Cambridge
 Book:  Riehl, "Category Theory in Context", Dover 2016, §1.4,

   本文件给出预序集相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab:  https://ncatlab.org/nlab/show/thin+category
   nLab:  https://ncatlab.org/nlab/show/functor+category
   Book:  Fong and Spivak, "Seven Sketches in Compositionality", Cambridge
   Book:  Riehl, "Category Theory in Context", Dover 2016, §1.4

   本节说明函子、hom、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Mac Lane §I.4, exercise 4: existence and uniqueness *)

Section ProsetTransform.

Context {C : Category}.
Context {A : Type}.
Context {R : relation A}.
Context {P : PreOrder R}.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition proset_pointwise (S T : C ⟶ Proset P) : Prop :=
  ∀ c : C, R (S c) (T c).

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition proset_transform {S T : C ⟶ Proset P}
           (H : proset_pointwise S T) : S ⟹ T :=
  @Build_Transform C (Proset P) S T (fun c => H c)
                   (fun _ _ _ => I) (fun _ _ _ => I).

(* Left to right: read the pointwise witnesses off the components. *)

Definition proset_pointwise_of {S T : C ⟶ Proset P}
           (N : S ⟹ T) : proset_pointwise S T :=
  fun c => transform N c.

(*
   本节说明 Transform 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem proset_transform_iff (S T : C ⟶ Proset P) :
  (S ⟹ T) ↔ proset_pointwise S T.
Proof. exact (@proset_pointwise_of S T, @proset_transform S T). Qed.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem proset_pointwise_of_transform {S T : C ⟶ Proset P}
        (H : proset_pointwise S T) :
  proset_pointwise_of (proset_transform H) = H.
Proof. reflexivity. Qed.

Theorem proset_transform_of_pointwise {S T : C ⟶ Proset P} (N : S ⟹ T) :
  proset_transform (proset_pointwise_of N) ≈ N.
Proof. exact (fun _ => I). Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem proset_transform_unique {S T : C ⟶ Proset P} (α β : S ⟹ T) : α ≈ β.
Proof. exact (fun _ => I). Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem proset_transform_subsingleton (S T : C ⟶ Proset P) :
  ((S ⟹ T) ↔ proset_pointwise S T) ∧ (∀ α β : S ⟹ T, α ≈ β).
Proof. exact (proset_transform_iff S T, @proset_transform_unique S T). Qed.

(** ** Seven Sketches Example 3.57: the functor category is thin *)

(*
   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem Fun_Proset_thin (S T : [C, Proset P])
        (α β : S ~{[C, Proset P]}~> T) : α ≈ β.
Proof. exact (fun _ => I). Qed.

(* Hence a preorder.  The pointwise order on functors is reflexive and
   transitive because [R] is, so it presents [[C, Proset P]] as a proset. *)

(*
   本节说明 Transform 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Fun_Proset_PreOrder : PreOrder proset_pointwise.
Proof.
  constructor.
  - intros S c.
    exact (@PreOrder_Reflexive A R P (S c)).
  - intros S T U H1 H2 c.
    exact (@PreOrder_Transitive A R P (S c) (T c) (U c) (H1 c) (H2 c)).
Defined.

Definition Fun_Proset : Category := Proset Fun_Proset_PreOrder.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Fun_Proset_forward : [C, Proset P] ⟶ Fun_Proset := {|
  fobj := fun S => S;
  fmap := fun S T N => proset_pointwise_of N
|}.

Program Definition Fun_Proset_backward : Fun_Proset ⟶ [C, Proset P] := {|
  fobj := fun S => S;
  fmap := fun S T H => proset_transform H
|}.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem Fun_Proset_iso : [C, Proset P] ≅[Cat] Fun_Proset.
Proof.
  unshelve econstructor.
  - exact Fun_Proset_forward.
  - exact Fun_Proset_backward.
  - exists (fun x => @iso_id Fun_Proset x).
    intros; exact I.
  - exists (fun x => @iso_id ([C, Proset P]) x).
    intros; exact (fun _ => I).
Defined.

(*
   本节说明函子、hom、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem Fun_Proset_strict_iso : [C, Proset P] ≅[StrictCat] Fun_Proset.
Proof.
  unshelve econstructor.
  - exact Fun_Proset_forward.
  - exact Fun_Proset_backward.
  - exists (fun x => eq_refl).
    intros; exact I.
  - exists (fun x => eq_refl).
    intros; exact (fun _ => I).
Defined.

End ProsetTransform.

(** ** Riehl Exercise 1.4.iii: the preorder-to-preorder case *)

(*
   本节说明 Transform 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Corollary proset_to_proset_transform_iff
          {B : Type} {Rb : relation B} (Q : PreOrder Rb)
          {A : Type} {R : relation A} (P : PreOrder R)
          (S T : Proset Q ⟶ Proset P) :
  (S ⟹ T) ↔ (∀ b : B, R (S b) (T b)).
Proof. exact (proset_transform_iff S T). Qed.

Corollary proset_to_proset_transform_unique
          {B : Type} {Rb : relation B} (Q : PreOrder Rb)
          {A : Type} {R : relation A} (P : PreOrder R)
          {S T : Proset Q ⟶ Proset P} (α β : S ⟹ T) : α ≈ β.
Proof. exact (proset_transform_unique α β). Qed.

(** ** Seven Sketches Example 3.57 at the naturals: monotone maps *)

(* [Nat_Proset] is the preorder [(ℕ, ≤)] as a category: the example
   [LessThanEqualTo_Category] of Instance/Proset.v.  Instance/Poset.v exports a
   same-named example, so the reference below is fully qualified. *)

Definition Nat_Proset : Category :=
  Category.Instance.Proset.LessThanEqualTo_Category.

(* Monotone maps [ℕ → ℕ], ordered pointwise. *)

Definition Monotone : Type :=
  ∃ m : nat → nat,
    ∀ x y : nat, PeanoNat.Nat.le x y → PeanoNat.Nat.le (m x) (m y).

Definition monotone_le : relation Monotone :=
  fun m m' => ∀ n : nat, PeanoNat.Nat.le (`1 m n) (`1 m' n).

Definition monotone_le_PreOrder : PreOrder monotone_le.
Proof.
  constructor.
  - intros m n.
    exact (PeanoNat.Nat.le_refl (`1 m n)).
  - intros m m' m'' H1 H2 n.
    exact (PeanoNat.Nat.le_trans _ _ _ (H1 n) (H2 n)).
Defined.

Definition MonotoneProset : Category := Proset monotone_le_PreOrder.

(*
   本节说明 Transform 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition monotone_of_endo (F : Nat_Proset ⟶ Nat_Proset) : Monotone.
Proof.
  exists (fobj[F]).
  intros x y h.
  exact (fmap[F] h).
Defined.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition endo_of_monotone (m : Monotone) : Nat_Proset ⟶ Nat_Proset := {|
  fobj := `1 m;
  fmap := fun x y h => `2 m x y h
|}.

(* One round trip holds on the nose: rebuilding a monotone map through its
   endofunctor returns it up to eta of the sigma pair. *)

Theorem monotone_of_endo_of_monotone (m : Monotone) :
  monotone_of_endo (endo_of_monotone m) = m.
Proof. destruct m; reflexivity. Qed.

(*
   本节说明函子、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example endo_of_monotone_of_endo_fobj (F : Nat_Proset ⟶ Nat_Proset) :
  fobj[endo_of_monotone (monotone_of_endo F)] = fobj[F] := eq_refl.

Example endo_of_monotone_of_endo_fmap (F : Nat_Proset ⟶ Nat_Proset)
        (x y : nat) (h : PeanoNat.Nat.le x y) :
  fmap[endo_of_monotone (monotone_of_endo F)] h = fmap[F] h := eq_refl.

Theorem endo_of_monotone_of_endo (F : Nat_Proset ⟶ Nat_Proset) :
  endo_of_monotone (monotone_of_endo F) ≈[StrictCat] F.
Proof.
  exists (fun x => eq_refl).
  intros; exact I.
Qed.

(* The comparison functors. *)

Program Definition Endo_Monotone_forward :
  [Nat_Proset, Nat_Proset] ⟶ MonotoneProset := {|
  fobj := monotone_of_endo;
  fmap := fun F G N n => transform N n
|}.

Program Definition Endo_Monotone_backward :
  MonotoneProset ⟶ [Nat_Proset, Nat_Proset] := {|
  fobj := endo_of_monotone;
  fmap := fun m m' H =>
    @Build_Transform Nat_Proset Nat_Proset
      (endo_of_monotone m) (endo_of_monotone m')
      (fun n => H n) (fun _ _ _ => I) (fun _ _ _ => I)
|}.

(*
   本节说明函子、等价、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem endo_nat_monotone_iso :
  [Nat_Proset, Nat_Proset] ≅[Cat] MonotoneProset.
Proof.
  unshelve econstructor.
  - exact Endo_Monotone_forward.
  - exact Endo_Monotone_backward.
  - unshelve refine (_; _).
    + intro m.
      unshelve econstructor.
      * intro n; exact (PeanoNat.Nat.le_refl (`1 m n)).
      * intro n; exact (PeanoNat.Nat.le_refl (`1 m n)).
      * exact I.
      * exact I.
    + intros; exact I.
  - unshelve refine (_; _).
    + intro F.
      unshelve econstructor.
      * exact (@Build_Transform Nat_Proset Nat_Proset
                 (endo_of_monotone (monotone_of_endo F)) F
                 (fun n => PeanoNat.Nat.le_refl (F n))
                 (fun _ _ _ => I) (fun _ _ _ => I)).
      * exact (@Build_Transform Nat_Proset Nat_Proset
                 F (endo_of_monotone (monotone_of_endo F))
                 (fun n => PeanoNat.Nat.le_refl (F n))
                 (fun _ _ _ => I) (fun _ _ _ => I)).
      * exact (fun _ => I).
      * exact (fun _ => I).
    + intros; exact (fun _ => I).
Defined.

(** ** The criterion has teeth: existence and non-existence *)

(*
   本节说明自然变换相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition monotone_zero : Monotone.
Proof.
  exists (fun _ : nat => 0%nat).
  intros x y h.
  exact (PeanoNat.Nat.le_refl 0%nat).
Defined.

Definition monotone_id : Monotone.
Proof.
  exists (fun n : nat => n).
  intros x y h.
  exact h.
Defined.

Definition Endo_zero : Nat_Proset ⟶ Nat_Proset := endo_of_monotone monotone_zero.
Definition Endo_id : Nat_Proset ⟶ Nat_Proset := endo_of_monotone monotone_id.

(* [0 ≤ n] holds pointwise, so a transformation exists (and by
   [proset_transform_unique] it is the only one up to [≈]). *)

Definition zero_le_id : proset_pointwise Endo_zero Endo_id.
Proof.
  intro n.
  exact (PeanoNat.Nat.le_0_l n).
Defined.

Definition transform_zero_to_id : Endo_zero ⟹ Endo_id :=
  proset_transform zero_le_id.

(* The converse pointwise order breaks down at [1], so by the criterion there
   is no transformation in the other direction. *)

Theorem not_id_le_zero : ¬ proset_pointwise Endo_id Endo_zero.
Proof.
  intro H.
  specialize (H 1%nat).
  simpl in H.
  inversion H.
Qed.

Theorem no_transform_id_to_zero : ¬ (Endo_id ⟹ Endo_zero).
Proof.
  intro N.
  exact (not_id_le_zero (proset_pointwise_of N)).
Qed.

(** ** Seven Sketches Exercise 3.58, clause 2: the dual is refuted *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition par_one : ParX ~{Parallel}~> ParY := (true; ParOne).
Definition par_two : ParX ~{Parallel}~> ParY := (false; ParTwo).

Definition ConstParX : Nat_Proset ⟶ Parallel :=
  @Diagonal Parallel Nat_Proset ParX.
Definition ConstParY : Nat_Proset ⟶ Parallel :=
  @Diagonal Parallel Nat_Proset ParY.

Definition proset_out_one : ConstParX ⟹ ConstParY :=
  fmap[@Diagonal Parallel Nat_Proset] par_one.
Definition proset_out_two : ConstParX ⟹ ConstParY :=
  fmap[@Diagonal Parallel Nat_Proset] par_two.

(*
   本节说明 Transform 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem proset_out_not_unique : ¬ (proset_out_one ≈ proset_out_two).
Proof.
  intro H.
  specialize (H 0%nat).
  simpl in H.
  discriminate.
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Corollary proset_in_unique {A : Type} {R : relation A} (P : PreOrder R)
          {S T : Parallel ⟶ Proset P} (α β : S ⟹ T) : α ≈ β.
Proof. exact (proset_transform_unique α β). Qed.
