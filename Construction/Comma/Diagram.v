Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Arrow.
Require Import Category.Construction.Quotient.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Equations.Prop.Logic.

Generalizable All Variables.

(** * The comma diagram over the arrow category, and its universal property *)

(*
   nLab:      https://ncatlab.org/nlab/show/comma+category
   nLab:      https://ncatlab.org/nlab/show/arrow+category
   nLab:      https://ncatlab.org/nlab/show/comma+object
   Wikipedia: https://en.wikipedia.org/wiki/Comma_category

   本文件给出图示例子。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Transport and [hom_cast]: the two spellings of strict functor equality *)

Section StrictCastKit.

Context {D : Category}.

Lemma hom_cast_of_transports {a a' b b' : D}
      (ea : a = a') (eb : b = b') (f : a ~{D}~> b) (g : a' ~{D}~> b') :
  transport (fun z => a ~{D}~> z) eb f
    ≈ transport_r (fun z => z ~{D}~> b') ea g
  → hom_cast ea eb f ≈ g.
Proof. destruct ea, eb; simpl; unfold transport_r; simpl; auto. Qed.

Lemma transports_of_hom_cast {a a' b b' : D}
      (ea : a = a') (eb : b = b') (f : a ~{D}~> b) (g : a' ~{D}~> b') :
  hom_cast ea eb f ≈ g
  → transport (fun z => a ~{D}~> z) eb f
      ≈ transport_r (fun z => z ~{D}~> b') ea g.
Proof. destruct ea, eb; simpl; unfold transport_r; simpl; auto. Qed.

End StrictCastKit.

Definition strict_fmap_cast {C D : Category} {F G : C ⟶ D}
           (H : @equiv _ (@Functor_StrictEq_Setoid C D) F G)
           {x y : C} (f : x ~> y) :
  hom_cast (`1 H x) (`1 H y) (fmap[F] f) ≈ fmap[G] f :=
  hom_cast_of_transports _ _ _ _ (`2 H x y f).

Definition Build_strict_eq {C D : Category} {F G : C ⟶ D}
           (eo : ∀ x : C, F x = G x)
           (em : ∀ (x y : C) (f : x ~> y),
                   hom_cast (eo x) (eo y) (fmap[F] f) ≈ fmap[G] f) :
  @equiv _ (@Functor_StrictEq_Setoid C D) F G :=
  (eo; fun x y f => transports_of_hom_cast _ _ _ _ (em x y f)).

(** ** The domain and codomain functors of the arrow category *)

Definition Arrow_dom {C : Category} : @Arrow C ⟶ C := @comma_proj1 C C C Id[C] Id[C].
Definition Arrow_cod {C : Category} : @Arrow C ⟶ C := @comma_proj2 C C C Id[C] Id[C].

Example Arrow_dom_is_comma_proj1 {C : Category} :
  @Arrow_dom C = @comma_proj1 C C C Id[C] Id[C] := eq_refl.

Example Arrow_cod_is_comma_proj2 {C : Category} :
  @Arrow_cod C = @comma_proj2 C C C Id[C] Id[C] := eq_refl.

Example Arrow_dom_fobj {C : Category} (x : @Arrow C) :
  Arrow_dom x = fst ``x := eq_refl.

Example Arrow_cod_fobj {C : Category} (x : @Arrow C) :
  Arrow_cod x = snd ``x := eq_refl.

Example Arrow_dom_fmap {C : Category} (x y : @Arrow C) (f : x ~> y) :
  fmap[Arrow_dom] f = fst ``f := eq_refl.

Example Arrow_cod_fmap {C : Category} (x y : @Arrow C) (f : x ~> y) :
  fmap[Arrow_cod] f = snd ``f := eq_refl.

Lemma Arrow_square {C : Category} (x y : @Arrow C) (f : x ~> y) :
  `2 y ∘ fmap[Arrow_dom] f ≈ fmap[Arrow_cod] f ∘ `2 x.
Proof. exact (`2 f). Qed.

(** ** Mac Lane's functor [R] : the comma category over the arrow category *)

Section CommaToArrow.

Context {A B C : Category}.
Context {S : A ⟶ C}.
Context {T : B ⟶ C}.

#[local] Set Transparent Obligations.
#[local] Obligation Tactic := idtac.

Program Definition Comma_to_Arrow : (S ↓ T) ⟶ @Arrow C := {|
  fobj := fun x => ((S (fst ``x), T (snd ``x)); `2 x);
  fmap := fun _ _ f => ((fmap[S] (fst ``f), fmap[T] (snd ``f)); _)
|}.
Next Obligation. intros x y f; exact (`2 f). Defined.
Next Obligation.
  intros x y f g [e0 e1]; split; simpl.
  - now rewrite e0.
  - now rewrite e1.
Qed.
Next Obligation. intros x; split; simpl; apply fmap_id. Qed.
Next Obligation. intros x y z f g; split; simpl; apply fmap_comp. Qed.

Example Comma_to_Arrow_fobj (x : S ↓ T) :
  Comma_to_Arrow x = ((S (fst ``x), T (snd ``x)); `2 x) := eq_refl.

Example Comma_to_Arrow_mediating (x : S ↓ T) :
  `2 (Comma_to_Arrow x) = `2 x := eq_refl.

Example Comma_to_Arrow_dom_leg (x y : S ↓ T) (f : x ~> y) :
  fmap[Arrow_dom] (fmap[Comma_to_Arrow] f) = fmap[S] (fst ``f) := eq_refl.

Example Comma_to_Arrow_cod_leg (x y : S ↓ T) (f : x ~> y) :
  fmap[Arrow_cod] (fmap[Comma_to_Arrow] f) = fmap[T] (snd ``f) := eq_refl.

(* Exercise 3 for [P] and [Q] as well: both projections act on a comma
   morphism -- a commuting square -- by returning its leg in the relevant
   factor, definitionally. *)
Example comma_proj1_fmap (x y : S ↓ T) (f : x ~> y) :
  fmap[comma_proj1] f = fst ``f := eq_refl.

Example comma_proj2_fmap (x y : S ↓ T) (f : x ~> y) :
  fmap[comma_proj2] f = snd ``f := eq_refl.

Lemma Comma_to_Arrow_is_proj_nat (x : S ↓ T) :
  `2 (Comma_to_Arrow x) = comma_proj_nat x.
Proof. destruct x as [[a b] h]; reflexivity. Qed.

Lemma Comma_to_Arrow_naturality (x y : S ↓ T) (f : x ~> y) :
  comma_proj_nat y ∘ fmap[S ◯ comma_proj1] f
    ≈ fmap[T ◯ comma_proj2] f ∘ comma_proj_nat x.
Proof. apply naturality_sym. Qed.

(** ** The commuting diagram, Mac Lane's displays (5)-(6) *)

(* [Defined], not [Qed], for the same reason as [comma_mediator_proj1] below:
   [comma_diagram_self] feeds these two back in as the hypotheses of the
   universal property and needs their object components to reduce. *)
Theorem comma_diagram_dom :
  @equiv _ (@Functor_StrictEq_Setoid (S ↓ T) C)
         (Arrow_dom ◯ Comma_to_Arrow) (S ◯ comma_proj1).
Proof. exists (fun _ => eq_refl); intros; reflexivity. Defined.

Theorem comma_diagram_cod :
  @equiv _ (@Functor_StrictEq_Setoid (S ↓ T) C)
         (Arrow_cod ◯ Comma_to_Arrow) (T ◯ comma_proj2).
Proof. exists (fun _ => eq_refl); intros; reflexivity. Defined.

Example comma_diagram_dom_obj (x : S ↓ T) : `1 comma_diagram_dom x = eq_refl
  := eq_refl.

Example comma_diagram_cod_obj (x : S ↓ T) : `1 comma_diagram_cod x = eq_refl
  := eq_refl.

Corollary comma_diagram_dom_Cat :
  Arrow_dom ◯ Comma_to_Arrow ≈[Cat] S ◯ comma_proj1.
Proof. apply strict_equiv_implies_fun_equiv, comma_diagram_dom. Qed.

Corollary comma_diagram_cod_Cat :
  Arrow_cod ◯ Comma_to_Arrow ≈[Cat] T ◯ comma_proj2.
Proof. apply strict_equiv_implies_fun_equiv, comma_diagram_cod. Qed.

End CommaToArrow.

(** ** Rebuilding a comma / arrow object from its cast components *)

Lemma arrow_eta_cast {C : Category} (z : @Arrow C) {d0 d1 : C}
      (p : Arrow_dom z = d0) (q : Arrow_cod z = d1) :
  (((d0, d1); hom_cast p q (`2 z)) : @Arrow C) = z.
Proof. destruct z as [[c0 c1] h]; simpl in *; destruct p, q; reflexivity. Defined.

(* A [hom_cast] between two arrow objects presented through [arrow_eta_cast]
   is settled by its two legs, which is all the hom-setoid of the arrow
   category records.  Every endpoint here is a variable, so the whole proof is
   a [destruct] of the four object equalities; the lemma is then applied — not
   rewritten with — so that unification may unfold [Arrow] to [Id ↓ Id]. *)
Lemma arrow_eta_cast_legs {C : Category} (z w : @Arrow C) {d0 d1 e0 e1 : C}
      (p : Arrow_dom z = d0) (q : Arrow_cod z = d1)
      (p' : Arrow_dom w = e0) (q' : Arrow_cod w = e1)
      (u : (((d0, d1); hom_cast p q (`2 z)) : @Arrow C)
             ~> (((e0, e1); hom_cast p' q' (`2 w)) : @Arrow C))
      (v : z ~{@Arrow C}~> w) :
  hom_cast p p' (fmap[Arrow_dom] v) ≈ fmap[Arrow_dom] u
  → hom_cast q q' (fmap[Arrow_cod] v) ≈ fmap[Arrow_cod] u
  → hom_cast (arrow_eta_cast z p q) (arrow_eta_cast w p' q') u ≈ v.
Proof.
  destruct z as [[c0 c1] h], w as [[c0' c1'] h']; simpl in *.
  destruct p, q, p', q'; simpl.
  intros H0 H1; split; [ now symmetry | now symmetry ].
Qed.

(** ** Mac Lane §II.6 Exercise 5: the universal property *)

Section UMP.

Context {A B C : Category}.
Context {S : A ⟶ C}.
Context {T : B ⟶ C}.
Context {X : Category}.
Context {P' : X ⟶ A}.
Context {Q' : X ⟶ B}.
Context {R' : X ⟶ @Arrow C}.

Context (Hdom : @equiv _ (@Functor_StrictEq_Setoid X C)
                       (Arrow_dom ◯ R') (S ◯ P')).
Context (Hcod : @equiv _ (@Functor_StrictEq_Setoid X C)
                       (Arrow_cod ◯ R') (T ◯ Q')).

Definition ump_dom_obj (x : X) : Arrow_dom (R' x) = S (P' x) := `1 Hdom x.
Definition ump_cod_obj (x : X) : Arrow_cod (R' x) = T (Q' x) := `1 Hcod x.

#[local] Set Transparent Obligations.
#[local] Obligation Tactic := idtac.

Program Definition comma_mediator : X ⟶ (S ↓ T) := {|
  fobj := fun x => ((P' x, Q' x);
                    hom_cast (ump_dom_obj x) (ump_cod_obj x) (`2 (R' x)));
  fmap := fun _ _ g => ((fmap[P'] g, fmap[Q'] g); _)
|}.
Next Obligation.
  intros x y g; simpl.
  rewrite <- (strict_fmap_cast Hdom g), <- (strict_fmap_cast Hcod g).
  rewrite !hom_cast_comp.
  apply hom_cast_respects.
  exact (`2 (fmap[R'] g)).
Qed.
Next Obligation.
  intros x y f g e; split; simpl; now rewrite e.
Qed.
Next Obligation. intros x; split; simpl; apply fmap_id. Qed.
Next Obligation. intros x y z f g; split; simpl; apply fmap_comp. Qed.

(* [Defined], not [Qed]: [comma_mediator_mediates] below projects out the
   object-equality component and needs it to reduce to [eq_refl]. *)
Theorem comma_mediator_proj1 :
  @equiv _ (@Functor_StrictEq_Setoid X A) (comma_proj1 ◯ comma_mediator) P'.
Proof. exists (fun _ => eq_refl); intros; reflexivity. Defined.

Theorem comma_mediator_proj2 :
  @equiv _ (@Functor_StrictEq_Setoid X B) (comma_proj2 ◯ comma_mediator) Q'.
Proof. exists (fun _ => eq_refl); intros; reflexivity. Defined.

Example comma_mediator_proj1_obj (x : X) : `1 comma_mediator_proj1 x = eq_refl
  := eq_refl.

Example comma_mediator_proj2_obj (x : X) : `1 comma_mediator_proj2 x = eq_refl
  := eq_refl.

Theorem comma_mediator_arrow :
  @equiv _ (@Functor_StrictEq_Setoid X (@Arrow C))
         (Comma_to_Arrow ◯ comma_mediator) R'.
Proof.
  apply (Build_strict_eq (F := Comma_to_Arrow ◯ comma_mediator) (G := R')
           (fun x => arrow_eta_cast (R' x) (ump_dom_obj x) (ump_cod_obj x))).
  intros x y g.
  apply arrow_eta_cast_legs.
  - exact (strict_fmap_cast Hdom g).
  - exact (strict_fmap_cast Hcod g).
Qed.

(** The three commuting equations for a competing mediator. *)
Definition MediatesDiagram (L : X ⟶ (S ↓ T)) : Type :=
  { k1 : @equiv _ (@Functor_StrictEq_Setoid X A) (comma_proj1 ◯ L) P' &
  { k2 : @equiv _ (@Functor_StrictEq_Setoid X B) (comma_proj2 ◯ L) Q' &
    ∀ x : X,
      hom_cast (f_equal S (`1 k1 x)) (f_equal T (`1 k2 x)) (`2 (L x))
        ≈ hom_cast (ump_dom_obj x) (ump_cod_obj x) (`2 (R' x)) }}.

Lemma comma_mediator_mediates : MediatesDiagram comma_mediator.
Proof.
  exists comma_mediator_proj1, comma_mediator_proj2.
  intro x; reflexivity.
Qed.

Theorem comma_mediator_unique (L : X ⟶ (S ↓ T)) :
  MediatesDiagram L → L ≈[Cat] comma_mediator.
Proof.
  intros [k1 [k2 k3]].
  unshelve eexists.
  - intro x.
    unshelve refine
      (@Build_Isomorphism (S ↓ T) (L x) (comma_mediator x)
         ((id_cast (`1 k1 x), id_cast (`1 k2 x)); _)
         ((id_cast (eq_sym (`1 k1 x)), id_cast (eq_sym (`1 k2 x))); _)
         _ _).
    + simpl.
      rewrite !fmap_id_cast.
      rewrite <- (k3 x), hom_cast_decompose.
      rewrite <- !comp_assoc, id_cast_inv_l.
      now rewrite id_right.
    + simpl.
      rewrite !fmap_id_cast, <- !eq_sym_map_distr.
      rewrite <- (k3 x), hom_cast_decompose.
      rewrite !comp_assoc, id_cast_inv_l.
      now rewrite id_left.
    + split; simpl; apply id_cast_inv_r.
    + split; simpl; apply id_cast_inv_l.
  - intros x y g; split; simpl.
    + rewrite <- (strict_fmap_cast k1 g), hom_cast_decompose.
      rewrite !comp_assoc, id_cast_inv_l, id_left.
      rewrite <- !comp_assoc, id_cast_inv_l.
      now rewrite id_right.
    + rewrite <- (strict_fmap_cast k2 g), hom_cast_decompose.
      rewrite !comp_assoc, id_cast_inv_l, id_left.
      rewrite <- !comp_assoc, id_cast_inv_l.
      now rewrite id_right.
Qed.

Theorem comma_diagram_ump :
  { L : X ⟶ (S ↓ T)
  & (MediatesDiagram L * (∀ L' : X ⟶ (S ↓ T), MediatesDiagram L' → L' ≈[Cat] L))%type }.
Proof.
  exists comma_mediator.
  split.
  - exact comma_mediator_mediates.
  - exact comma_mediator_unique.
Defined.

End UMP.

(** ** Non-vacuity: the comma category is its own mediator *)

(* The hypotheses of the universal property are inhabited -- by the diagram
   the comma category itself carries, where they are literally
   [comma_diagram_dom] and [comma_diagram_cod] -- and at that competitor the
   mediator produced is [≈[Cat]] the identity functor (strictly so, in fact:
   [comma_diagram_self_strict]).  The identity moreover satisfies
   [MediatesDiagram] outright ([comma_id_mediates], three reflexivities), so
   [comma_mediator_unique] can be EXERCISED at it
   ([comma_diagram_self_via_ump]) -- with that, both halves of Exercise 5 are
   checked against the one case whose answer is forced. *)
Section SelfMediation.

Context {A B C : Category}.
Context {S : A ⟶ C}.
Context {T : B ⟶ C}.

Definition comma_self_mediator : (S ↓ T) ⟶ (S ↓ T) :=
  comma_mediator (P' := comma_proj1) (Q' := comma_proj2) (R' := Comma_to_Arrow)
                 comma_diagram_dom comma_diagram_cod.

Example comma_self_mediator_fobj (x : S ↓ T) :
  comma_self_mediator x = ((fst ``x, snd ``x); `2 x) := eq_refl.

Theorem comma_diagram_self : comma_self_mediator ≈[Cat] Id[S ↓ T].
Proof.
  unshelve eexists.
  - intro x.
    unshelve refine
      (@Build_Isomorphism (S ↓ T) (comma_self_mediator x) x
         ((id, id); _) ((id, id); _) _ _).
    + abstract (simpl; rewrite !fmap_id, id_left; now rewrite id_right).
    + abstract (simpl; rewrite !fmap_id, id_left; now rewrite id_right).
    + split; simpl; apply id_left.
    + split; simpl; apply id_left.
  - intros x y g; split; simpl; now rewrite id_left, id_right.
Qed.

(* The strict form is also available: the self-mediator and the identity
   have literally the same object map, and their fmaps agree by the
   category laws. *)
Theorem comma_diagram_self_strict :
  @equiv _ Functor_StrictEq_Setoid comma_self_mediator Id[S ↓ T].
Proof.
  unshelve eexists.
  - intro x; destruct x as [[a b] h]; reflexivity.
  - intros [[a b] h] [[a' b'] h'] f; split; simpl; cat.
Qed.

(* The identity functor satisfies [MediatesDiagram] at the comma's own
   diagram by three reflexivities -- which lets the UNIQUENESS half of the
   universal property be exercised, not merely stated: [comma_mediator_unique]
   at this competitor re-derives [comma_diagram_self] from the other side.
   (Adapted from the adversarial audit's probe, with thanks.) *)
Lemma comma_id_mediates :
  MediatesDiagram (P' := comma_proj1) (Q' := comma_proj2) (R' := Comma_to_Arrow)
                  comma_diagram_dom comma_diagram_cod (Id[S ↓ T]).
Proof.
  unshelve eexists.
  - exists (fun _ => eq_refl); intros; reflexivity.
  - unshelve eexists.
    + exists (fun _ => eq_refl); intros; reflexivity.
    + intro x; reflexivity.
Qed.

Theorem comma_diagram_self_via_ump : Id[S ↓ T] ≈[Cat] comma_self_mediator.
Proof. exact (comma_mediator_unique _ _ _ comma_id_mediates). Qed.

End SelfMediation.
