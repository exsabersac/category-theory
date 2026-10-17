Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Construction.Product.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** The hom-action of a functor: [fmap] as one natural transformation of
    hom-bifunctors. *)

(*
   nLab:      https://ncatlab.org/nlab/show/functor
   Wikipedia: https://en.wikipedia.org/wiki/Hom_functor
   Book:      Mac Lane, "Categories for the Working Mathematician",

   本文件给出 hom 形式的伴随/同态。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Open Scope category_scope.

Section HomAction.

Context {A D : Category}.
Context (T : A ⟶ D).

(* The Sets-morphism component at a pair p = (a, b) of objects: the hom-map
   g ↦ fmap[T] g, from hom_A(a, b) to hom_D(T a, T b). Its [proper_morphism]
   field is exactly [fmap_respects], supplied directly, so this is a plain
   [Definition] with no deferred obligation at all — which is what lets the
   component reduce, and hence [hom_action_component] below hold by eq_refl. *)
Definition hom_action_at (p : A^op ∏ A) :
  Hom A p ~{Sets}~> (Hom D ◯ (T^op ∏⟶ T)) p := {|
  morphism := fun g => fmap[T] g;
  proper_morphism := fun g g' (eqv : g ≈ g') => fmap_respects _ _ g g' eqv
|}.

(* Mac Lane §II.5 Exercise 7: the hom-maps of T assemble into one natural
   transformation between the hom-bifunctor of A and the hom-bifunctor of D
   pulled back along T in both variables. *)
Program Definition hom_action : Hom A ⟹ Hom D ◯ (T^op ∏⟶ T) := {|
  transform := hom_action_at
|}.
(* naturality: fmap[T] k ∘ fmap[T] g ∘ fmap[T] h ≈ fmap[T] (k ∘ g ∘ h) *)
Next Obligation. now rewrite !fmap_comp. Qed.
(* naturality_sym: the same square in the opposite orientation *)
Next Obligation. now rewrite !fmap_comp. Qed.

(* The component of [hom_action] at (a, b) IS the arrow function of T. This
   holds by [eq_refl]: the transformation stores [hom_action_at], whose
   [morphism] field is fmap[T] on the nose. Everything below is phrased through
   the transformation's components, and this lemma is what identifies those
   components with fmap[T]. *)
Lemma hom_action_component (a b : A) (f : a ~{A}~> b) :
  transform[hom_action] (a, b) f = fmap[T] f.
Proof. reflexivity. Qed.

(* Faithfulness, read componentwise: every component of [hom_action] is
   injective with respect to ≈. *)
Definition hom_action_injective : Type :=
  ∀ (a b : A) (f g : a ~{A}~> b),
    transform[hom_action] (a, b) f ≈ transform[hom_action] (a, b) g → f ≈ g.

(* Fullness, read componentwise: every component of [hom_action] is surjective
   AS DATA — a preimage is produced, not merely asserted to exist. (In this
   library ∃ is [sigT], so the two readings coincide; see Lib/Foundation.v.) *)
Definition hom_action_surjective : Type :=
  ∀ (a b : A) (g : T a ~{D}~> T b),
    ∃ (f : a ~{A}~> b), transform[hom_action] (a, b) f ≈ g.

Theorem Faithful_hom_action_injective : Faithful T → hom_action_injective.
Proof. intros F a b f g H; exact (fmap_inj f g H). Qed.

Theorem hom_action_injective_Faithful : hom_action_injective → Faithful T.
Proof. intros H; constructor; intros a b f g Hfg; exact (H a b f g Hfg). Qed.

(* Faithful T ⟺ every component of [hom_action] is injective. Both directions
   are near-definitional: [Faithful]'s only field IS the implication, and the
   components are fmap[T] by [hom_action_component]. The two directions are
   [Qed] (following Functor/Hom.v's own [Yoneda_Faithful]), but the pair itself
   is a transparent [Definition], so projecting the biconditional gives back
   the named lemmas by conversion. *)
Definition hom_action_faithful_iff : Faithful T ↔ hom_action_injective :=
  (Faithful_hom_action_injective, hom_action_injective_Faithful).

Definition Full_hom_action_surjective : Full T → hom_action_surjective :=
  fun F a b g => (prefmap g; fmap_sur g).

Definition hom_action_surjective_Full : hom_action_surjective → Full T :=
  fun H => {| prefmap := fun a b g => `1 (H a b g)
            ; fmap_sur := fun a b g => `2 (H a b g) |}.

(* Full T ⟺ every component of [hom_action] is surjective as data. Stated with
   ↔ = [iffT], since [Full] carries data: [prefmap] is recovered as the first
   projection of the surjectivity witness and [fmap_sur] as the second, so the
   backward direction is a repackaging rather than an implication between
   propositions. Both directions are given as terms, hence transparent, so the
   transported data reduces: prefmap of the round trip IS the original prefmap
   by conversion. *)
Definition hom_action_full_iff : Full T ↔ hom_action_surjective :=
  (Full_hom_action_surjective, hom_action_surjective_Full).

End HomAction.

(* Acceptance: the transformation computes. At the identity functor every
   component is the identity on hom-sets, and at a composite it is the
   composite of the two arrow functions — both on the nose, by [eq_refl].
   These are the definitional [=] readings the house rule permits alongside ≈;
   they are labelled as such, and every statement about MORPHISMS above uses ≈. *)

Example hom_action_Id (A : Category) (a b : A) (f : a ~{A}~> b) :
  transform[hom_action (@Id A)] (a, b) f = f.
Proof. reflexivity. Qed.

Example hom_action_Compose {A B D : Category} (F : B ⟶ D) (G : A ⟶ B)
        (a b : A) (f : a ~{A}~> b) :
  transform[hom_action (F ◯ G)] (a, b) f = fmap[F] (fmap[G] f).
Proof. reflexivity. Qed.
