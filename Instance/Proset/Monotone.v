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

(* 相关说明。 （已译） *)

Section Monotone.

Context {A : Type} {R : relation A} (P : PreOrder R).
Context {B : Type} {S : relation B} (Q : PreOrder S).

(* 相关说明。 （已译） *)
Record MonotoneFun := {
  mono_map :> A → B;
  mono_pres : ∀ x y, R x y → S (mono_map x) (mono_map y)
}.

(*
   本节说明函子、hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Functor_of_monotone (f : MonotoneFun) :
  Proset P ⟶ Proset Q := {|
  fobj := mono_map f;
  fmap := fun x y (h : R x y) => mono_pres f x y h
|}.
Next Obligation. intros f x y g h Hgh; exact I. Qed.
Next Obligation. intros f x; exact I. Qed.
Next Obligation. intros f x y z g h; exact I. Qed.

(* The forward leg: 函子 restricts monotone map 对象,
 monotonicity being action (unique) arrows. （已译） *)
Definition monotone_of_Functor (F : Proset P ⟶ Proset Q) : MonotoneFun := {|
  mono_map := fobj[F];
  mono_pres := fun x y h => fmap[F] h
|}.

(* 相关说明。 （已译） *)
Lemma monotone_of_Functor_of_monotone (f : MonotoneFun) :
  mono_map (monotone_of_Functor (Functor_of_monotone f)) = mono_map f.
Proof. reflexivity. Qed.

(* Round trip 函子 side: same 函子 up thin
 identification — [Functor_Setoid] natural 同构 whose
 components 恒等 arrows. （已译） *)
Lemma Functor_of_monotone_of_Functor (F : Proset P ⟶ Proset Q) :
  Functor_of_monotone (monotone_of_Functor F) ≈ F.
Proof.
  exists (fun x => iso_id).
  intros x y h; simpl.
  constructor.
Qed.

End Monotone.

(* 相关说明。 （已译） *)

(* The two-element order as a preorder on [bool]: false ≤ true. *)
Definition bool_le (a b : bool) : Prop := a = true → b = true.

#[export] Instance bool_le_preorder : PreOrder bool_le.
Proof.
  constructor.
  - intros a H; exact H.
  - intros a b c Hab Hbc H; exact (Hbc (Hab H)).
Qed.

(* 相关说明。 （已译） *)
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

(* ...and 函子, through smart constructor. （已译） *)
Definition Seventeen_TwentyFour_Proset :
  Proset bool_le_preorder ⟶ LessThanEqualTo_Category :=
  Functor_of_monotone bool_le_preorder Nat.le_preorder
    seventeen_twentyfour.

Example Seventeen_TwentyFour_Proset_bot :
  Seventeen_TwentyFour_Proset false = 17%nat := eq_refl.
Example Seventeen_TwentyFour_Proset_top :
  Seventeen_TwentyFour_Proset true = 24%nat := eq_refl.

(*
   本节说明 Monotone 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
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
(* [_2]'s homset strict equality, so [Proper] law inferred
 during elaboration; two remaining laws obligate, each an
 equation between parallel 态射 thin target. （已译） *)
Next Obligation. intros x; exact I. Qed.
Next Obligation. intros x y z f g; exact I. Qed.

Example Seventeen_TwentyFour_bot : Seventeen_TwentyFour TwoX = 17%nat
  := eq_refl.
Example Seventeen_TwentyFour_top : Seventeen_TwentyFour TwoY = 24%nat
  := eq_refl.

(* 相关说明。 （已译） *)

Definition nondecreasing (f : nat → nat) : Type :=
  ∀ m n : nat, (m <= n)%nat → (f m <= f n)%nat.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
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

(* 相关说明。 （已译） *)

(*
   本节说明 Monotone 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
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

(* Monotonicity GENERATING 关系: one case per edge — each
 generator raises rank — two closure rules; closure is
 never enumerated. （已译） *)
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
