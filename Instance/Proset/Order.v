Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Thin.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Poset.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.

Generalizable All Variables.

(** * Preorders as thin categories: the round trip, order reversal, total
      orders, and infima as limits *)

(*
 Book: Riehl, "Category Theory in Context", Dover 2016, §1.2
 Book: Fong and Spivak, "Seven Sketches in Compositionality",
 nLab: https://ncatlab.org/nlab/show/thin+category
 nLab: https://ncatlab.org/nlab/show/preorder
 nLab: https://ncatlab.org/nlab/show/total+order

   本文件给出预序集相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Thinness of prosets and posets *)

(*
   本节说明hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma proset_thin {A : Type} {R : relation A} (P : PreOrder R) :
  Thin (Proset P).
Proof. intros x y f g; exact I. Qed.

(*
   本节说明 Order 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Poset_is_Proset {A : Type} {R : relation A} (P : PreOrder R)
      (H : @Antisymmetric A eq eq_equiv R) :
  @Poset A R P H = Proset P.
Proof. reflexivity. Qed.

Lemma poset_thin {A : Type} {R : relation A} (P : PreOrder R)
      (H : @Antisymmetric A eq eq_equiv R) :
  Thin (@Poset A R P H).
Proof. exact (proset_thin P). Qed.

(* Antisymmetry is exactly skeletality of the thin category: mutually related
   objects are isomorphic by [thin_iso], and antisymmetry forces them equal. *)
Lemma poset_skeletal {A : Type} {R : relation A} (P : PreOrder R)
      (H : @Antisymmetric A eq eq_equiv R) (x y : A) :
  x ≅[@Poset A R P H] y → x = y.
Proof. intro i; exact (H x y (to i) (from i)). Qed.

(** ** Round trip, leg one: the preorder of the thin category of P is P *)

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem hom_preorder_Proset {A : Type} {R : relation A} (P : PreOrder R)
        (x y : A) :
  thin_preorder (Proset P) x y ↔ R x y.
Proof.
  split.
  - intro H; destruct H as [r]; exact r.
  - exact (fun r => inhabits r).
Qed.

(*
   本节说明 Order 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem hom_preorder_Proset_eq {A : Type} {R : relation A} (P : PreOrder R)
        (prop_ext : ∀ p q : Prop, (p <-> q) → p = q)
        (fun_ext : ∀ f g : A → A → Prop, (∀ x y : A, f x y = g x y) → f = g) :
  thin_preorder (Proset P) = R.
Proof.
  apply fun_ext; intros x y.
  apply prop_ext; split.
  - intro H; destruct H as [r]; exact r.
  - exact (fun r => inhabits r).
Qed.

(** ** Round trip, leg two: the thin category of the hom-preorder *)

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition thin_to_Proset_Functor (C : Category) :
  C ⟶ Proset (thin_PreOrder C) := {|
  fobj := fun x => x;
  fmap := fun x y f => inhabits f
|}.

(*
   本节说明 Order 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem hom_Proset_Faithful_iff_Thin (C : Category) :
  Faithful (thin_to_Proset_Functor C) ↔ Thin C.
Proof.
  split.
  - intros F x y f g.
    destruct F as [inj].
    exact (inj x y f g I).
  - intro T.
    constructor; intros x y f g _; apply T.
Qed.

(* On a proset the choice hypothesis of Structure/Thin.v is discharged: the
   homs of [Proset P] are the Props [R x y], so eliminating [inhabited] lands
   back in Prop and is permitted. *)
Definition proset_HomChoice {A : Type} {R : relation A} (P : PreOrder R) :
  HomChoice (Proset P) :=
  fun x y h => match h return R x y with inhabits r => r end.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Proset_hom_Functor {C : Category}
        (T : Thin C) (ch : HomChoice C) :
  Proset (thin_PreOrder C) ⟶ C := {|
  fobj := fun x => x;
  fmap := fun x y h => ch x y h
|}.

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition thin_Proset_iso {C : Category}
        (T : Thin C) (ch : HomChoice C) :
  C ≅[Cat] Proset (thin_PreOrder C) := {|
  to   := thin_to_Proset_Functor C;
  from := Proset_hom_Functor T ch
|}.

(*
   本节说明函子、等价、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma thin_Proset_iso_obj {C : Category} (T : Thin C) (ch : HomChoice C)
      (x : C) :
  (fobj[thin_to_Proset_Functor C] x = x) ∧
  (fobj[Proset_hom_Functor T ch] x = x).
Proof. split; reflexivity. Qed.

Lemma thin_Proset_roundtrip_hom {C : Category} (T : Thin C) (ch : HomChoice C)
      {x y : C} (f : x ~> y) :
  fmap[Proset_hom_Functor T ch] (fmap[thin_to_Proset_Functor C] f) ≈ f.
Proof. apply T. Qed.

(* Vacuous, per the note above -- kept only so both directions are named. *)
Lemma Proset_thin_roundtrip_hom {C : Category} (T : Thin C) (ch : HomChoice C)
      {x y : C} (h : x ~{Proset (thin_PreOrder C)}~> y) :
  fmap[thin_to_Proset_Functor C] (fmap[Proset_hom_Functor T ch] h) ≈ h.
Proof. exact I. Qed.

(* The hypothesis-free corollary: a proset is recovered from its own
   hom-preorder, with [proset_HomChoice] supplying the only hypothesis and
   [proset_thin] the other. *)
Definition Proset_roundtrip {A : Type} {R : relation A} (P : PreOrder R) :
  Proset P ≅[Cat] Proset (thin_PreOrder (Proset P)) :=
  thin_Proset_iso (proset_thin P) (proset_HomChoice P).

(** ** Order reversal: the opposite of a thin category (Riehl §1.2) *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma Proset_op_obj {A : Type} {R : relation A} (P : PreOrder R) :
  obj[(Proset P)^op] = obj[Proset (flip_PreOrder P)].
Proof. reflexivity. Qed.

Lemma Proset_op_hom {A : Type} {R : relation A} (P : PreOrder R) (x y : A) :
  (x ~{(Proset P)^op}~> y) = (x ~{Proset (flip_PreOrder P)}~> y).
Proof. reflexivity. Qed.

Program Definition Proset_op_to {A : Type} {R : relation A} (P : PreOrder R) :
  (Proset P)^op ⟶ Proset (flip_PreOrder P) := {|
  fobj := fun x => x;
  fmap := fun x y f => f
|}.

Program Definition Proset_op_from {A : Type} {R : relation A}
        (P : PreOrder R) :
  Proset (flip_PreOrder P) ⟶ (Proset P)^op := {|
  fobj := fun x => x;
  fmap := fun x y f => f
|}.

(*
   本节说明函子、hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma Proset_op_roundtrip {A : Type} {R : relation A} (P : PreOrder R)
      (x y : A) (f : x ~{(Proset P)^op}~> y) :
  fmap[Proset_op_from P] (fmap[Proset_op_to P] f) = f.
Proof. reflexivity. Qed.

Lemma Proset_op_roundtrip' {A : Type} {R : relation A} (P : PreOrder R)
      (x y : A) (f : x ~{Proset (flip_PreOrder P)}~> y) :
  fmap[Proset_op_to P] (fmap[Proset_op_from P] f) = f.
Proof. reflexivity. Qed.

Program Definition Proset_op_iso {A : Type} {R : relation A}
        (P : PreOrder R) :
  ((Proset P)^op)%category ≅[Cat] Proset (flip_PreOrder P) := {|
  to   := Proset_op_to P;
  from := Proset_op_from P
|}.

(** ** Preorders versus equivalence relations (Seven Sketches §1.2.2) *)

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma Equivalence_is_PreOrder {A : Type} (R : relation A) :
  Equivalence R → PreOrder R.
Proof.
  intro E; constructor.
  - exact (@Equivalence_Reflexive A R E).
  - exact (@Equivalence_Transitive A R E).
Qed.

Lemma PreOrder_Symmetric_is_Equivalence {A : Type} (R : relation A) :
  PreOrder R → Symmetric R → Equivalence R.
Proof.
  intros P S; constructor.
  - exact (@PreOrder_Reflexive A R P).
  - exact S.
  - exact (@PreOrder_Transitive A R P).
Qed.

(** ** The discrete and codiscrete preorders on a carrier (§1.2.2) *)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition discrete_rel (A : Type) : relation A := fun x y => x = y.

Definition codiscrete_rel (A : Type) : relation A := fun _ _ => True.

Definition discrete_PreOrder (A : Type) : PreOrder (discrete_rel A).
Proof.
  constructor.
  - intro x; reflexivity.
  - intros x y z Hxy Hyz; exact (eq_trans Hxy Hyz).
Defined.

Definition codiscrete_PreOrder (A : Type) : PreOrder (codiscrete_rel A).
Proof. constructor; [ intro x; exact I | intros x y z _ _; exact I ]. Defined.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Refines {A : Type} (R S : relation A) : Prop :=
  ∀ x y : A, R x y → S x y.

Theorem codiscrete_terminal {A : Type} (R : relation A) :
  Refines R (codiscrete_rel A).
Proof. intros x y _; exact I. Qed.

Theorem codiscrete_terminal_unique {A : Type} (S : relation A) :
  (∀ R : relation A, Refines R S) → ∀ x y : A, S x y <-> codiscrete_rel A x y.
Proof.
  intros top x y; split.
  - intro; exact I.
  - exact (top (codiscrete_rel A) x y).
Qed.

Theorem discrete_initial {A : Type} (R : relation A) :
  Reflexive R → Refines (discrete_rel A) R.
Proof. intros refl x y e; destruct e; exact (refl x). Qed.

Theorem discrete_initial_unique {A : Type} (S : relation A) :
  Reflexive S →
  (∀ R : relation A, Reflexive R → Refines S R) →
  ∀ x y : A, S x y <-> discrete_rel A x y.
Proof.
  intros refl bot x y; split.
  - exact (bot (discrete_rel A) (fun z => eq_refl) x y).
  - exact (discrete_initial S refl x y).
Qed.

(* The categorical reading of the top: from every proset on A there is an
   identity-on-objects functor into the codiscrete one, because every arrow
   has somewhere to go. *)
Program Definition to_codiscrete {A : Type} {R : relation A} (P : PreOrder R) :
  Proset P ⟶ Proset (codiscrete_PreOrder A) := {|
  fobj := fun x => x;
  fmap := fun _ _ _ => I
|}.

(* And why the codiscrete preorder is as far from a poset as possible: all
   its objects are isomorphic, so it is skeletal only when A is a
   subsingleton. *)
Lemma codiscrete_all_iso {A : Type} (x y : A) :
  x ≅[Proset (codiscrete_PreOrder A)] y.
Proof. exact (thin_iso (proset_thin (codiscrete_PreOrder A)) I I). Qed.

(** ** Comparability, and how it differs from decidability (§1.2.2) *)

(*
   本节说明 Order 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition comparable {A : Type} (R : relation A) (x y : A) : Type :=
  R x y ∨ R y x.

Definition decidable_rel {A : Type} (R : relation A) : Type :=
  ∀ x y : A, R x y ∨ ¬ R x y.

Lemma comparable_of_decidable_total {A : Type} (R : relation A) :
  decidable_rel R → (∀ x y : A, R x y \/ R y x) →
  ∀ x y : A, comparable R x y.
Proof.
  intros dec tot x y.
  destruct (dec x y) as [h|n].
  - exact (inl h).
  - right.
    destruct (tot x y) as [h|h].
    + contradiction.
    + exact h.
Qed.

Lemma comparable_total {A : Type} (R : relation A) (x y : A) :
  comparable R x y → R x y \/ R y x.
Proof. intros [h|h]; [ left | right ]; exact h. Qed.

Lemma decidable_of_comparable {A : Type} (R : relation A) :
  Reflexive R →
  (∀ x y : A, R x y → R y x → x = y) →
  (∀ x y : A, (x = y) ∨ ¬ (x = y)) →
  (∀ x y : A, comparable R x y) →
  decidable_rel R.
Proof.
  intros refl anti eqdec cmp x y.
  destruct (cmp x y) as [h|h].
  - exact (inl h).
  - destruct (eqdec x y) as [e|ne].
    + destruct e; exact (inl (refl x)).
    + right; intro hxy; exact (ne (anti x y hxy h)).
Qed.

(* In a discrete preorder an element is comparable with itself and with
   nothing else (§1.2.2): the only arrows are the identities. *)

Lemma discrete_comparable_self {A : Type} (x : A) :
  comparable (discrete_rel A) x x.
Proof. exact (inl eq_refl). Qed.

Lemma discrete_incomparable {A : Type} (x y : A) :
  x ≠ y → comparable (discrete_rel A) x y → False.
Proof. intros ne [e|e]; [ exact (ne e) | exact (ne (eq_sym e)) ]. Qed.

(** ** Total (linear) orders, Mac Lane §I.2 definition 4 *)

(*
   本节说明 Order 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class TotalOrder {A : Type} (R : relation A) : Type := {
  total_preorder   : PreOrder R;
  total_antisym    : ∀ x y : A, R x y → R y x → x = y;
  total_comparable : ∀ x y : A, comparable R x y
}.

Definition TotalOrder_Antisymmetric {A : Type} {R : relation A}
           (T : TotalOrder R) : @Antisymmetric A eq eq_equiv R :=
  @total_antisym A R T.

Definition TotalOrder_Category {A : Type} {R : relation A}
           (T : TotalOrder R) : Category :=
  @Poset A R (@total_preorder A R T) (TotalOrder_Antisymmetric T).

Lemma TotalOrder_Category_thin {A : Type} {R : relation A} (T : TotalOrder R) :
  Thin (TotalOrder_Category T).
Proof. exact (proset_thin (@total_preorder A R T)). Qed.

(* The characterization asked for in §1.2.2: over a fixed antisymmetric
   preorder, being a total order IS "every two elements are comparable". *)
Theorem TotalOrder_iff_all_comparable {A : Type} (R : relation A)
        (P : PreOrder R) (anti : ∀ x y : A, R x y → R y x → x = y) :
  TotalOrder R ↔ (∀ x y : A, comparable R x y).
Proof.
  split.
  - exact (fun T => @total_comparable A R T).
  - intro cmp.
    exact {| total_preorder := P
           ; total_antisym := anti
           ; total_comparable := cmp |}.
Qed.

(** *** (ℕ, ≤) as a total order, and its reverse *)

Definition nat_TotalOrder : TotalOrder PeanoNat.Nat.le := {|
  total_preorder   := PeanoNat.Nat.le_preorder;
  total_antisym    := partial_order_antisym PeanoNat.Nat.le_partialorder;
  total_comparable := fun x y =>
    match le_ge_dec x y with
    | left  h => inl h
    | right h => inr h
    end
|}.

(*
   本节说明 Order 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Nat_TotalOrder_Category : Category :=
  TotalOrder_Category nat_TotalOrder.

(* The reverse of (ℕ, ≤) is (ℕ, ≥) on the nose: stdlib defines [ge n m] as
   [m <= n], and [Basics.flip le x y] reduces to [le y x], so the two
   relations are convertible. *)
Lemma flip_le_is_ge (x y : nat) :
  Basics.flip PeanoNat.Nat.le x y = ge x y.
Proof. reflexivity. Qed.

(* Hence the opposite of the thin category of (ℕ, ≤) is the thin category of
   (ℕ, ≥), by the general order-reversal isomorphism above. *)
Definition Nat_op_iso :
  ((Proset PeanoNat.Nat.le_preorder)^op)%category
    ≅[Cat] Proset (flip_PreOrder PeanoNat.Nat.le_preorder) :=
  Proset_op_iso PeanoNat.Nat.le_preorder.

(* And the reversed order is itself a total order, so the opposite category
   is again the thin category of a total order. *)
Definition flip_TotalOrder {A : Type} {R : relation A} (T : TotalOrder R) :
  TotalOrder (Basics.flip R) := {|
  total_preorder   := flip_PreOrder (@total_preorder A R T);
  total_antisym    := fun x y hxy hyx => @total_antisym A R T x y hyx hxy;
  total_comparable := fun x y =>
    match @total_comparable A R T x y with
    | inl h => inr h
    | inr h => inl h
    end
|}.

Definition nat_ge_TotalOrder : TotalOrder (Basics.flip PeanoNat.Nat.le) :=
  flip_TotalOrder nat_TotalOrder.

(** ** Infima and suprema, and their categorical identification (§1.3.1) *)

(*
   本节说明 Order 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition IsInfimum {A : Type} (R : relation A) (x y m : A) : Type :=
  (R m x ∧ R m y) ∧ (∀ n : A, R n x → R n y → R n m).

Definition IsSupremum {A : Type} (R : relation A) (x y m : A) : Type :=
  (R x m ∧ R y m) ∧ (∀ n : A, R x n → R y n → R m n).

(* The two notions are one notion read in two directions, and the identity is
   definitional, not merely provable. *)
Lemma supremum_is_flipped_infimum {A : Type} (R : relation A) (x y m : A) :
  IsSupremum R x y m = IsInfimum (Basics.flip R) x y m.
Proof. reflexivity. Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition PairDiagram {A : Type} {R : relation A} (P : PreOrder R)
           (x y : A) : DiscreteCat bool ⟶ Proset P :=
  DiscreteCat_Functor (C:=Proset P) (fun b : bool => if b then y else x).

(*
   本节说明 Order 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition pair_cone {A : Type} {R : relation A} (P : PreOrder R)
           (x y n : A) (lx : R n x) (ly : R n y) : Cone (PairDiagram P x y).
Proof.
  unshelve econstructor.
  { exact n. }
  unshelve econstructor.
  - intro b; destruct b; [ exact ly | exact lx ].
  - intros b b' f; exact I.
Defined.

Definition pair_cocone {A : Type} {R : relation A} (P : PreOrder R)
           (x y n : A) (ux : R x n) (uy : R y n) :
  Cone ((PairDiagram P x y)^op).
Proof.
  unshelve econstructor.
  { exact n. }
  unshelve econstructor.
  - intro b; destruct b; [ exact uy | exact ux ].
  - intros b b' f; exact I.
Defined.

(*
   本节说明（余）极限、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem infimum_iff_limit {A : Type} {R : relation A} (P : PreOrder R)
        (x y m : A) :
  IsInfimum R x y m ↔ IsALimit (PairDiagram P x y) m.
Proof.
  split.
  - intros [[lx ly] med].
    unshelve refine {| limit_acone := _ |}.
    + unshelve refine {| vertex_map := _ |}.
      * intro b; destruct b; [ exact ly | exact lx ].
      * intros b b' f; exact I.
    + intro N.
      unshelve refine {| unique_obj := _ |}.
      * exact (med (vertex_obj[N])
                 (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) false)
                 (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) true)).
      * intro b; exact I.
      * intros v _; exact I.
  - intro L.
    split.
    + split.
      * exact (@vertex_map _ _ _ _ (@limit_acone _ _ _ _ L) false).
      * exact (@vertex_map _ _ _ _ (@limit_acone _ _ _ _ L) true).
    + intros n lx ly.
      exact (unique_obj (@ump_limit _ _ _ _ L (pair_cone P x y n lx ly))).
Qed.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem supremum_iff_colimit {A : Type} {R : relation A} (P : PreOrder R)
        (x y m : A) :
  IsSupremum R x y m ↔ IsALimit ((PairDiagram P x y)^op) m.
Proof.
  split.
  - intros [[ux uy] med].
    unshelve refine {| limit_acone := _ |}.
    + unshelve refine {| vertex_map := _ |}.
      * intro b; destruct b; [ exact uy | exact ux ].
      * intros b b' f; exact I.
    + intro N.
      unshelve refine {| unique_obj := _ |}.
      * exact (med (vertex_obj[N])
                 (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) false)
                 (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) true)).
      * intro b; exact I.
      * intros v _; exact I.
  - intro L.
    split.
    + split.
      * exact (@vertex_map _ _ _ _ (@limit_acone _ _ _ _ L) false).
      * exact (@vertex_map _ _ _ _ (@limit_acone _ _ _ _ L) true).
    + intros n ux uy.
      exact (unique_obj (@ump_limit _ _ _ _ L (pair_cocone P x y n ux uy))).
Qed.

(*
   本节说明 Order 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition tmeet {A : Type} {R : relation A} (T : TotalOrder R) (x y : A) : A :=
  match @total_comparable A R T x y with
  | inl _ => x
  | inr _ => y
  end.

Definition tjoin {A : Type} {R : relation A} (T : TotalOrder R) (x y : A) : A :=
  match @total_comparable A R T x y with
  | inl _ => y
  | inr _ => x
  end.

Theorem TotalOrder_meet {A : Type} {R : relation A} (T : TotalOrder R)
        (x y : A) : IsInfimum R x y (tmeet T x y).
Proof.
  unfold tmeet.
  destruct (@total_comparable A R T x y) as [h|h].
  - split; [ split | ].
    + exact (@PreOrder_Reflexive A R (@total_preorder A R T) x).
    + exact h.
    + intros n lx ly; exact lx.
  - split; [ split | ].
    + exact h.
    + exact (@PreOrder_Reflexive A R (@total_preorder A R T) y).
    + intros n lx ly; exact ly.
Qed.

Theorem TotalOrder_join {A : Type} {R : relation A} (T : TotalOrder R)
        (x y : A) : IsSupremum R x y (tjoin T x y).
Proof.
  unfold tjoin.
  destruct (@total_comparable A R T x y) as [h|h].
  - split; [ split | ].
    + exact h.
    + exact (@PreOrder_Reflexive A R (@total_preorder A R T) y).
    + intros n ux uy; exact uy.
  - split; [ split | ].
    + exact (@PreOrder_Reflexive A R (@total_preorder A R T) x).
    + exact h.
    + intros n ux uy; exact ux.
Qed.

(* Combining the two: the thin category of a total order has a limit and a
   colimit for every two-object discrete diagram. *)

Definition TotalOrder_pair_limit {A : Type} {R : relation A}
           (T : TotalOrder R) (x y : A) :
  IsALimit (PairDiagram (@total_preorder A R T) x y) (tmeet T x y) :=
  fst (infimum_iff_limit (@total_preorder A R T) x y (tmeet T x y))
      (TotalOrder_meet T x y).

Definition TotalOrder_pair_colimit {A : Type} {R : relation A}
           (T : TotalOrder R) (x y : A) :
  IsALimit ((PairDiagram (@total_preorder A R T) x y)^op) (tjoin T x y) :=
  fst (supremum_iff_colimit (@total_preorder A R T) x y (tjoin T x y))
      (TotalOrder_join T x y).

(** *** Worked instance: (ℕ, ≤), with min and max *)

Theorem nat_min_infimum (x y : nat) :
  IsInfimum PeanoNat.Nat.le x y (PeanoNat.Nat.min x y).
Proof.
  split; [ split | ].
  - exact (PeanoNat.Nat.le_min_l x y).
  - exact (PeanoNat.Nat.le_min_r x y).
  - intros n lx ly; exact (PeanoNat.Nat.min_glb x y n lx ly).
Qed.

Theorem nat_max_supremum (x y : nat) :
  IsSupremum PeanoNat.Nat.le x y (PeanoNat.Nat.max x y).
Proof.
  split; [ split | ].
  - exact (PeanoNat.Nat.le_max_l x y).
  - exact (PeanoNat.Nat.le_max_r x y).
  - intros n ux uy; exact (PeanoNat.Nat.max_lub x y n ux uy).
Qed.

Definition nat_min_limit (x y : nat) :
  IsALimit (PairDiagram PeanoNat.Nat.le_preorder x y) (PeanoNat.Nat.min x y) :=
  fst (infimum_iff_limit PeanoNat.Nat.le_preorder x y (PeanoNat.Nat.min x y))
      (nat_min_infimum x y).

Definition nat_max_colimit (x y : nat) :
  IsALimit ((PairDiagram PeanoNat.Nat.le_preorder x y)^op)
           (PeanoNat.Nat.max x y) :=
  fst (supremum_iff_colimit PeanoNat.Nat.le_preorder x y
         (PeanoNat.Nat.max x y))
      (nat_max_supremum x y).

(** *** Worked instance: the two-element order

    The smallest order in which the identification has content: [false] below
    [true], with conjunction the meet and disjunction the join. *)

Definition bool_le (x y : bool) : Prop := x = true → y = true.

Definition bool_PreOrder : PreOrder bool_le.
Proof.
  constructor.
  - intros x h; exact h.
  - intros x y z Hxy Hyz h; exact (Hyz (Hxy h)).
Defined.

Definition bool_TotalOrder : TotalOrder bool_le.
Proof.
  unshelve refine {| total_preorder := bool_PreOrder |}.
  - intros x y Hxy Hyx.
    destruct x, y; try reflexivity.
    + symmetry; exact (Hxy eq_refl).
    + exact (Hyx eq_refl).
  - intros x y.
    destruct x.
    + right; intro h; reflexivity.
    + left; intro h; discriminate h.
Defined.

Theorem bool_andb_infimum (x y : bool) :
  IsInfimum bool_le x y (andb x y).
Proof.
  split; [ split | ].
  - destruct x, y; simpl; intro h; try reflexivity; exact h.
  - destruct x, y; simpl; intro h; try reflexivity; exact h.
  - intros n lx ly h; destruct x, y; simpl;
      solve [ reflexivity | exact (lx h) | exact (ly h) ].
Qed.

Theorem bool_orb_supremum (x y : bool) :
  IsSupremum bool_le x y (orb x y).
Proof.
  split; [ split | ].
  - destruct x, y; simpl; intro h; try reflexivity; exact h.
  - destruct x, y; simpl; intro h; try reflexivity; exact h.
  - intros n ux uy h; destruct x, y; simpl in *;
      solve [ reflexivity | exact (ux h) | exact (uy h) | discriminate h ].
Qed.

Definition bool_andb_limit (x y : bool) :
  IsALimit (PairDiagram bool_PreOrder x y) (andb x y) :=
  fst (infimum_iff_limit bool_PreOrder x y (andb x y)) (bool_andb_infimum x y).

Definition bool_orb_colimit (x y : bool) :
  IsALimit ((PairDiagram bool_PreOrder x y)^op) (orb x y) :=
  fst (supremum_iff_colimit bool_PreOrder x y (orb x y))
      (bool_orb_supremum x y).

(* The two-element order is a poset, so its thin category is skeletal; and
   the meet computed by the class matches the boolean conjunction. *)

Example bool_tmeet_true_false : tmeet bool_TotalOrder true false = false.
Proof. reflexivity. Qed.

Example bool_tjoin_true_false : tjoin bool_TotalOrder true false = true.
Proof. reflexivity. Qed.

(*
   本节说明 Order 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The thin category of a total order has the carrier as its objects and the
   order itself as its homs. *)
Example nat_order_obj : obj[Nat_TotalOrder_Category] = nat.
Proof. reflexivity. Qed.

Example nat_order_hom (x y : nat) :
  (x ~{Nat_TotalOrder_Category}~> y) = PeanoNat.Nat.le x y.
Proof. reflexivity. Qed.

(*
   本节说明hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example nat_op_hom_is_ge (x y : nat) :
  (x ~{((Proset PeanoNat.Nat.le_preorder)^op)%category}~> y) = ge x y.
Proof. reflexivity. Qed.

(* The meet of a total order computes. *)
Example nat_tmeet_3_5 : tmeet nat_TotalOrder 3%nat 5%nat = 3%nat.
Proof. reflexivity. Qed.

Example nat_tjoin_3_5 : tjoin nat_TotalOrder 3%nat 5%nat = 5%nat.
Proof. reflexivity. Qed.

(* [Thin] is inhabited on the two examples the tree already ships.  The poset
   one is fully qualified because Instance/Proset.v and Instance/Poset.v
   both export the name (Test/Poset.v). *)

Definition thin_proset_nat : Thin (Proset PeanoNat.Nat.le_preorder) :=
  proset_thin PeanoNat.Nat.le_preorder.

Definition thin_poset_nat :
  Thin Category.Instance.Poset.LessThanEqualTo_Category :=
  poset_thin PeanoNat.Nat.le_preorder
    (partial_order_antisym PeanoNat.Nat.le_partialorder).

(* The colimit half restated through the library's own apex-pinned name
   (Structure/Limit/Preservation.v), as promised above. *)
Corollary supremum_iff_IsAColimit {A : Type} {R : relation A} (P : PreOrder R)
        (x y m : A) :
  IsSupremum R x y m ↔ IsAColimit (PairDiagram P x y) m.
Proof. exact (supremum_iff_colimit P x y m). Qed.

(* The "no third name" claim above, pinned rather than asserted: the
   TotalOrder route lands on the SAME category both existing files define. *)
Example Nat_TotalOrder_Category_is_Poset :
  Nat_TotalOrder_Category = Category.Instance.Poset.LessThanEqualTo_Category
  := eq_refl.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma thin_preorder_DiscreteCat {A : Type} (x y : A) :
  thin_preorder (DiscreteCat A) x y ↔ discrete_rel A x y.
Proof.
  split.
  - intros [e]; exact e.
  - intro e; exact (inhabits e).
Qed.

