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

(* A category is thin when parallel morphisms are identified by the hom-setoid
   equivalence.  Note that this is `≈`, not `=`: on the library's setoid
   hom-sets that is the right notion, and it is what Instance/Proset.v
   supplies for a proset by declaring the equivalence to be [True]. *)
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

(* A pair of opposing morphisms in a thin category is automatically an
   isomorphism: the two composites are endomorphisms, hence equal to the
   identity.  This is the categorical reading of "x ≤ y and y ≤ x", and it is
   exactly what antisymmetry rules out in Instance/Poset.v — a poset is a
   SKELETAL thin category (Instance/Poset.v), the isomorphic objects being
   forced equal.

   Both inverse laws are supplied directly rather than through [Program], so
   that the two appeals to thinness are visible in the term instead of being
   found by the [cat_simpl] obligation tactic (Lib/Tactics.v), whose [auto]
   would pick [T] out of the context. *)
Definition thin_iso {C : Category} (T : Thin C) {x y : C}
  (f : x ~> y) (g : y ~> x) : x ≅ y :=
  {| to          := f
   ; from        := g
   ; iso_to_from := T y y (f ∘ g) id
   ; iso_from_to := T x x (g ∘ f) id |}.

(** ** The hom-preorder of a category *)

(* The ∃-a-morphism preorder on objects, squashed to Prop.

   The library ALREADY carries a preorder of this shape at the Type level:
   Theory/Category.v's exported instance [hom_preorder : PreOrder hom[C]]
   over CRelationClasses, whose "proofs" are the morphisms themselves.  That
   instance is deliberately NOT reused here, and the reason is the honest
   version of this file's choice story: fed to a Type-valued preorder, the
   reconstruction below would need no [HomChoice] at all -- the witness IS the
   morphism.  What forces the squash is Instance/Proset.v's [Proset], which
   is hard-wired to [Relation_Definitions.relation], i.e. Prop-valued; a
   Prop-squashed relation is the only thing it accepts, and recovering a
   morphism from the squash is then a genuine choice.  (Instance/Omega.v
   documents the same Prop-vs-Type obstruction and routes around it with a
   bespoke Type-valued order; here the point is precisely to meet [Proset]
   where it is.)  The new name [thin_preorder] avoids shadowing the exported
   instance. *)
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

(* Opposition on categories is order reversal on hom-preorders, and the two
   relations are not merely pointwise equivalent but CONVERTIBLE: both sides
   reduce to [inhabited (y ~{C}~> x)].  [Basics.flip] is the stdlib operation
   [flip R x y = R y x]. *)
Lemma hom_preorder_op (C : Category) (x y : obj[C]) :
  thin_preorder (C^op) x y = Basics.flip (thin_preorder C) x y.
Proof. reflexivity. Qed.

(* Choosing an arrow from the bare knowledge that one exists.  This is
   elimination of the Prop [inhabited (x ~> y)] into [Type], which Coq's
   elimination rules do not grant: [inhabited] has a [Type]-valued argument in
   its constructor, so its eliminator is restricted to Prop targets, and no
   [match] on the witness can produce a morphism.  The hypothesis is therefore
   taken explicitly wherever it is needed, never assumed.  It is free of charge
   whenever the homs of C are themselves Props — in particular on every
   [Proset], where [proset_HomChoice] discharges it (Instance/Proset/Order.v).

   What is claimed here is only that the obvious definition does not
   typecheck; no impossibility theorem is being asserted. *)
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
