Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(** * Thin categories, and the hom-preorder of a category *)

(*
   nLab:      https://ncatlab.org/nlab/show/preorder
   Wikipedia: https://en.wikipedia.org/wiki/Preorder
   Book:      Mac Lane, "Categories for the Working Mathematician",
   Book:      Riehl, "Category Theory in Context", Dover 2016, §1.2
   Book:      Fong and Spivak, "Seven Sketches in Compositionality",

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明hom、等价、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Thin (C : Category) : Type :=
  ∀ (x y : C) (f g : x ~{C}~> y), f ≈ g.

(* Thinness is self-dual: reversing arrows neither creates nor merges parallel
   pairs.  Both directions hold on the nose because Construction/Opposite.v
   defines hom[C^op] x y as hom[C] y x and reuses the same hom-setoid. *)

Lemma Thin_Opposite {C : Category} : Thin C → Thin (C^op).
Proof. intros T x y f g; exact (T y x f g). Qed.

Lemma Opposite_Thin {C : Category} : Thin (C^op) → Thin C.
Proof. intros T x y f g; exact (T y x f g). Qed.

(* In a thin category every morphism is both monic and epic (the classes at
   Theory/Morphisms.v), because both cancellation laws conclude
   an equation between parallel morphisms.  The converse does not hold: being
   a bimorphism everywhere is far weaker than thinness. *)

Lemma thin_Monic {C : Category} (T : Thin C) {x y : C} (f : x ~> y) : Monic f.
Proof. constructor; intros z g1 g2 _; apply T. Qed.

Lemma thin_Epic {C : Category} (T : Thin C) {x y : C} (f : x ~> y) : Epic f.
Proof. constructor; intros z g1 g2 _; apply T. Qed.

(*
   本节说明同构、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition thin_iso {C : Category} (T : Thin C) {x y : C}
  (f : x ~> y) (g : y ~> x) : x ≅ y :=
  {| to          := f
   ; from        := g
   ; iso_to_from := T y y (f ∘ g) id
   ; iso_from_to := T x x (g ∘ f) id |}.

(** ** The hom-preorder of a category *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition thin_preorder (C : Category) : relation (obj[C]) :=
  fun x y => inhabited (x ~{C}~> y).

(* It is a preorder: reflexivity is the identity arrow, transitivity is
   composition.  The [inhabited] witnesses may be eliminated here because the
   goal is itself a Prop. *)
Definition thin_PreOrder (C : Category) : PreOrder (thin_preorder C).
Proof.
  constructor.
  - intro x; exact (inhabits (@id C x)).
  - intros x y z Hxy Hyz.
    destruct Hxy as [f], Hyz as [g].
    exact (inhabits (g ∘ f)).
Defined.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma hom_preorder_op (C : Category) (x y : obj[C]) :
  thin_preorder (C^op) x y = Basics.flip (thin_preorder C) x y.
Proof. reflexivity. Qed.

(*
   本节说明 Thin 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition HomChoice (C : Category) : Type :=
  ∀ (x y : obj[C]), thin_preorder C x y → x ~{C}~> y.

(** ** Closure of thinness (Mac Lane §II.3 Ex. 2 / §II.4 Ex. 4, structural halves) *)

#[local] Obligation Tactic := idtac.

(* Products of thin categories are thin: parallel pairs are componentwise
   parallel.  Instance/Proset/Closure.v instantiates this at preorders. *)
Lemma Thin_Product {C D : Category} :
  Thin C → Thin D → Thin (C ∏ D).
Proof.
  intros TC TD [a b] [c d] [f g] [f' g']; split.
  - exact (TC a c f f').
  - exact (TD b d g g').
Qed.

(* Into a thin target, any component family is natural — both naturality
   squares are equations between parallel morphisms.  Functors into thin
   categories are therefore compared by their object actions alone. *)
Program Definition thin_natural {C D : Category} (TD : Thin D)
  (F G : C ⟶ D) (η : ∀ x : C, F x ~> G x) : F ⟹ G := {|
  transform := η
|}.
Next Obligation.
  intros C D TD F G η x y f.
  exact (TD _ _ _ _).
Qed.
Next Obligation.
  intros C D TD F G η x y f.
  exact (TD _ _ _ _).
Qed.

(* Parallel natural transformations into a thin target agree pointwise:
   their components are parallel.  (The functor-category packaging of
   this — a functor category into a thin target is thin — lives in
   Instance/Proset/Closure.v, where [Fun] is available.) *)
Lemma Thin_Transform {C D : Category} (TD : Thin D)
  (F G : C ⟶ D) (σ τ : F ⟹ G) :
  ∀ x : C, transform σ x ≈ transform τ x.
Proof.
  intro x.
  exact (TD _ _ _ _).
Qed.
