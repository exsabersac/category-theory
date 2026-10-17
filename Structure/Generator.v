Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(*
   nLab:  https://ncatlab.org/nlab/show/separator
   nLab:  https://ncatlab.org/nlab/show/generator

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Generating (separating) families and objects *)

(* Mac Lane §V.7 p. 127 / Riehl 4.7.7 / Awodey §7.2: a family of objects
   SEPARATES (generates) C when parallel arrows agreeing after every arrow
   OUT of a member are equal.  Stated positively as a cancellation law,
   the constructively correct reading, exactly as [Cogenerator] states its
   dual. *)
Record Generator {C : Category} := {
  gen_index : Type;
  gen_obj : gen_index -> C;
  gen_separates : forall (x y : C) (f g : x ~> y),
    (forall (j : gen_index) (k : gen_obj j ~> x), f ∘ k ≈ g ∘ k) -> f ≈ g
}.

Arguments Generator : clear implicits.
Arguments gen_index {C} _.
Arguments gen_obj {C} _ _.
Arguments gen_separates {C} _ {x y} f g _.

(* Awodey's single-object form: one object whose generalized elements
   distinguish parallel arrows. *)
Definition IsSeparator {C : Category} (c : C) : Type :=
  forall (x y : C) (f g : x ~> y),
    (forall k : c ~> x, f ∘ k ≈ g ∘ k) -> f ≈ g.

Definition Generator_of_separator {C : Category} (c : C) (H : IsSeparator c) :
  Generator C := {|
  gen_index := unit;
  gen_obj := fun _ => c;
  gen_separates := fun x y f g Hk => H x y f g (fun k => Hk tt k)
|}.

(* Joint faithfulness of a family of functors: the arrows are told apart
   by SOME member.  For the representables [Hom (gen_obj j), ─] this is
   the separation condition read through [fmap]. *)
Definition JointlyFaithful {C D : Category} {J : Type}
  (F : J -> C ⟶ D) : Type :=
  forall (x y : C) (f g : x ~> y),
    (forall j : J, fmap[F j] f ≈ fmap[F j] g) -> f ≈ g.

(** ** Awodey §7.2: separation IS faithfulness of the representable *)

Section Characterizations.

Context {C : Category}.

(* Forward.  The hypothesis of [Faithful [Hom c,─]] at f, g is
   [fmap[[Hom c,─]] f ≈ fmap[[Hom c,─]] g], which unfolds -- through
   Instance/Sets.v's pointwise hom-setoid and Functor/Hom.v's
   post-composition [fmap] -- to [∀ k : c ~> x, f ∘ k ≈ g ∘ k], the
   hypothesis of [IsSeparator c].  Only the packaging moves: [Faithful]
   is a class, so the term is built with its constructor. *)
Definition separator_faithful (c : C) (H : IsSeparator c) :
  Faithful [Hom c,─] :=
  @Build_Faithful C Sets [Hom c,─] (fun x y f g E => H x y f g (fun k => E k)).

(* Backward, by the same unfolding read the other way: [fmap_inj] is the
   field of [Faithful], and its hypothesis is already the separation
   hypothesis. *)
Definition faithful_separator (c : C) (F : Faithful [Hom c,─]) :
  IsSeparator c :=
  fun x y f g H => @fmap_inj _ _ [Hom c,─] F x y f g (fun k => H k).

(** ** Mac Lane §V.7 / Riehl §E.4: the family form is joint faithfulness *)

(* The family of covariant representables on the members of a generating
   family is jointly faithful, and conversely.  The index of the functor
   family is the generator's own index, so the two statements quantify
   over the same [Type]. *)
Definition generator_jointly_faithful (G : Generator C) :
  JointlyFaithful (fun j : gen_index G => [Hom gen_obj G j,─]) :=
  fun x y f g H => gen_separates G f g (fun j k => H j k).

Definition jointly_faithful_generator {J : Type} (F : J -> C)
  (H : JointlyFaithful (fun j : J => [Hom F j,─])) : Generator C :=
  @Build_Generator C J F (fun x y f g Hk => H x y f g (fun j k => Hk j k)).

(** ** The single-object / family bridge *)

(* [Generator_of_separator] above is one direction.  This is its converse,
   for a family whose index has only the one element named: the object at
   that index separates by itself.  The transport is on the INDEX, by
   [rewrite] on a Leibniz equation between indices (data, not morphisms),
   after reverting the test arrow whose type mentions it. *)
Definition separator_of_generator (G : Generator C) (j0 : gen_index G)
  (Hsing : forall j : gen_index G, j = j0) : IsSeparator (gen_obj G j0).
Proof.
  intros x y f g H.
  apply (gen_separates G f g); intros j k.
  revert k; rewrite (Hsing j); intros k; apply H.
Defined.

(* The round trip on a separator: packaging it as a [unit]-indexed family
   and reading the object back off gives the separator one started with
   ON THE NOSE -- the composite is [H] at [eq_refl], the index singleton
   condition on [unit] being [eq_refl] at [tt].  This equation is what
   makes the [Defined] above load-bearing: with [separator_of_generator]
   closed by [Qed] the same [eq_refl] is refused (measured).  A first
   draft stated only the TYPE [IsSeparator c], which [H] itself inhabits;
   an audit caught the vacuity and the equation replaced it. *)
Example separator_generator_roundtrip (c : C) (H : IsSeparator c) :
  separator_of_generator (Generator_of_separator c H) tt
    (fun j => match j with tt => eq_refl end) = H := eq_refl.

(* The issue's pinned name, as the biconditional it names, for an
   UNBUNDLED family [F : J -> C]: [Separates F] is the separation clause
   of [Generator] with the family held fixed, and the two directions are
   the two terms above read at that family.  Type-valued, so the "iff" is
   a pair. *)
Definition Separates {J : Type} (F : J -> C) : Type :=
  forall (x y : C) (f g : x ~> y),
    (forall (j : J) (k : F j ~> x), f ∘ k ≈ g ∘ k) -> f ≈ g.

Definition generator_iff_jointly_faithful {J : Type} (F : J -> C) :
  (Separates F -> JointlyFaithful (fun j : J => [Hom F j,─])) *
  (JointlyFaithful (fun j : J => [Hom F j,─]) -> Separates F) :=
  (fun H x y f g E => H x y f g (fun j k => E j k),
   fun H x y f g E => H x y f g (fun j k => E j k)).

(* The same bridge one level up, between the two faithfulness notions:
   [JointlyFaithful] over a [unit] index is [Faithful]. *)
Definition jointly_faithful_faithful {D : Category} (F : C ⟶ D)
  (H : Faithful F) : JointlyFaithful (fun _ : unit => F) :=
  fun x y f g E => @fmap_inj _ _ F H x y f g (E tt).

Definition faithful_jointly_faithful {D : Category} (F : C ⟶ D)
  (H : JointlyFaithful (fun _ : unit => F)) : Faithful F :=
  @Build_Faithful C D F (fun x y f g E => H x y f g (fun _ => E)).

End Characterizations.

(** ** Transport along isomorphisms and along maps of index types *)

Section Transport.

Context {C : Category}.

(* The shared step of all three transports below.  If the arrows out of d
   already separate the pair (f, g), so do the arrows out of an isomorphic
   c: test with k ∘ from i and cancel [to i] on the right.  Stated for a
   FIXED pair, because that is what every consumer has in hand. *)
Lemma hom_test_iso {x y : C} (f g : x ~> y) {c d : C} (i : c ≅ d)
  (H : forall k : d ~> x, f ∘ k ≈ g ∘ k) (k : c ~> x) : f ∘ k ≈ g ∘ k.
Proof.
  specialize (H (k ∘ from i)).
  rewrite !comp_assoc in H.
  rewrite <- (id_right (f ∘ k)), <- (id_right (g ∘ k)).
  rewrite <- (iso_from_to i).
  rewrite !comp_assoc.
  now rewrite H.
Qed.

(* Separation is an isomorphism-invariant property of an object.  This is
   what moves a witness between two presentations of the same object --
   see the header on the terminal object of [Sets] and the singleton. *)
Definition separator_iso {c d : C} (H : IsSeparator c) (i : c ≅ d) :
  IsSeparator d :=
  fun x y f g Hk => H x y f g (hom_test_iso f g i Hk).

(* Monotonicity along a map of index types: a family that CONTAINS a
   separating family, each member up to isomorphism, separates.  The new
   family is indexed by K and the old index is carried into it by u. *)
Definition gen_family_mono (G : Generator C) {K : Type} (ob : K -> C)
  (u : gen_index G -> K) (i : forall j, gen_obj G j ≅ ob (u j)) :
  Generator C :=
  @Build_Generator C K ob
    (fun x y f g H =>
       gen_separates G f g (fun j => hom_test_iso f g (i j) (H (u j)))).

(* Replacing each member by an isomorphic object, the index kept. *)
Definition gen_iso (G : Generator C) (d : gen_index G -> C)
  (i : forall j, gen_obj G j ≅ d j) : Generator C :=
  gen_family_mono G d (fun j => j) i.

(* Adding objects to a separating family keeps it separating.  The
   isomorphisms are [iso_id]: on the [inl] summand the two families are
   convertible, so this is the definitional case of [gen_family_mono]. *)
Definition gen_extend (G : Generator C) {K : Type} (ob : K -> C) :
  Generator C :=
  gen_family_mono G (fun jk => match jk with
                               | inl j => gen_obj G j
                               | inr k => ob k
                               end) inl (fun _ => iso_id).

End Transport.

(** ** Riehl's contrapositive reading, as far as it is free *)

Section Contrapositive.

Context {C : Category}.

(* Riehl 4.7.7 states separation as: f ≉ g yields a member and an arrow
   out of it that the two arrows treat differently.  Constructively only
   this much comes back -- the tests cannot ALL agree -- and the step
   from there to an explicit witnessing pair is the one this library
   cannot take without a decider (see the header). *)
Definition gen_separates_contra (G : Generator C) {x y : C} (f g : x ~> y)
  (Hne : f ≈ g -> False) :
  (forall (j : gen_index G) (k : gen_obj G j ~> x), f ∘ k ≈ g ∘ k) -> False :=
  fun H => Hne (gen_separates G f g H).

Definition separator_contra {c : C} (H : IsSeparator c) {x y : C}
  (f g : x ~> y) (Hne : f ≈ g -> False) :
  (forall k : c ~> x, f ∘ k ≈ g ∘ k) -> False :=
  fun Hk => Hne (H x y f g Hk).

End Contrapositive.
