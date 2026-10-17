Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Natural.Transformation.Opposite.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Two.

Generalizable All Variables.

(** * Transport of colimits, and the induced map between (co)limits *)

(*
 nLab: https://ncatlab.org/nlab/show/colimit
 nLab: https://ncatlab.org/nlab/show/opposite+functor

   本文件给出余极限相关等价/构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** (A) Oppositization respects the functor setoid *)

(* Given e : G ≈ G' — which, for [Functor_Setoid], is a natural
   isomorphism bundled with its coherence — the opposite functors are
   equivalent, by taking each component's INVERSE.  This is the 2-cell
   reversal tamed by invertibility: [Isomorphism_Opposite] swaps [to] and
   [from], and the coherence square is the original one read at the
   flipped arrow, so only a reassociation separates the two statements
   (composition in the opposite category unfolds to reversed
   composition). *)

Definition Opposite_Functor_respects {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') : Opposite_Functor G ≈ Opposite_Functor G'.
Proof.
  exists (fun x => Isomorphism_Opposite (`1 e x)).
  intros x y f; simpl.
  rewrite comp_assoc.
  exact (`2 e y x f).
Defined.

(* The same fact registered for setoid rewriting, which is what a
   consumer dualizing a limit result actually reaches for. *)

#[export]
Instance Opposite_Functor_Proper {J C : Category} :
  Proper (equiv ==> equiv) (@Opposite_Functor J C) :=
  fun _ _ e => Opposite_Functor_respects e.

(* The inverse passage costs nothing, and the reason is the tree's own
   [Opposite_Functor_invol] (Functor/Opposite.v): oppositization is a
   DEFINITIONAL involution on functors, so [Opposite_Functor_respects]
   applied to an equivalence of opposites lands at
   [(G^op)^op ≈ (G'^op)^op], which IS [G ≈ G'].  A [:=] with no tactic,
   no transport and no coercion. *)

Definition Opposite_Functor_reflects {J C : Category} {G G' : J ⟶ C}
  (e : Opposite_Functor G ≈ Opposite_Functor G') : G ≈ G' :=
  Opposite_Functor_respects e.

(* The two passages return the ISOMORPHISM FAMILY on the nose, in both
   composition orders — [Isomorphism] has primitive projections with eta,
   so [Isomorphism_Opposite] applied twice is the identity definitionally.

   MEASURED REJECTION, with its cause DISCRIMINATED rather than guessed:
   the round trip does NOT hold at the whole record, and there are TWO
   independent obstructions, each with its own control.
     (i) The COHERENCE component is rejected on its own.  Its proof is
         built by [rewrite comp_assoc], so applying the passage twice
         wraps the term in two [eq_ind]s that do not cancel; the
         first-component Examples below are the control showing the data
         half is unaffected.
     (ii) Independently, stdlib [sigT] has no definitional eta:
         [existT _ (`1 e) (`2 e) = e] is rejected for an ARBITRARY [e],
         so the pair would fail to close even had (i) not.
   Nothing weaker than (i) is claimed: no [≈]-level round trip is stated,
   there being no setoid on [Functor_Setoid]'s coherence field. *)

Example Opposite_Functor_reflects_respects {J C : Category}
  {G G' : J ⟶ C} (e : G ≈ G') (x : J) :
  `1 (Opposite_Functor_reflects (Opposite_Functor_respects e)) x
  = `1 e x := eq_refl.

Example Opposite_Functor_respects_reflects {J C : Category}
  {G G' : J ⟶ C} (e : Opposite_Functor G ≈ Opposite_Functor G') (x : J) :
  `1 (Opposite_Functor_respects (Opposite_Functor_reflects e)) x
  = `1 e x := eq_refl.

(** ** (B) Transport of colimits along a natural isomorphism *)

(* The duals of Theory/Equivalence/Limit.v's [cone_transport],
   [cone_transport_inv], [isalimit_transport] and [limit_transport],
   obtained by riding (A) rather than by a second proof.  Every statement
   below is COVARIANT: no opposite category appears in any type AS
   WRITTEN — the covariant names [Cocone], [IsAColimit], [Colimit] and
   [colimit_inj] carry it — even though every proof goes through one.

   All four are supplied by [:=] with no tactic — the passage costs
   exactly the (A) lemma and nothing else. *)

Definition cocone_transport {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') (N : Cocone G) : Cocone G' :=
  cone_transport (Opposite_Functor_respects e) N.

Definition cocone_transport_inv {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') (N : Cocone G') : Cocone G :=
  cone_transport_inv (Opposite_Functor_respects e) N.

Definition isacolimit_transport {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') {c : C} (H : IsAColimit G c) : IsAColimit G' c :=
  isalimit_transport (Opposite_Functor_respects e) H.

Definition colimit_transport {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') (L : Colimit G) : Colimit G' :=
  limit_transport (Opposite_Functor_respects e) L.

(* Covariant readbacks.  A cocone's injections run INTO the apex, so
   pushing one across e postcomposes with the forward component while the
   colimit's own injections PREcompose with the backward one — the
   opposite handedness from the limit side, and the reason these are
   worth stating rather than leaving the reader to unfold.

   All four hold at Leibniz equality, recorded as [eq_refl] Examples
   below; the [≈] forms are the rewriting-friendly ones. *)

Lemma cocone_transport_inj {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') (N : Cocone G) (x : J) :
  cocone_inj (cocone_transport e N) x ≈ cocone_inj N x ∘ from (`1 e x).
Proof. reflexivity. Qed.

Lemma cocone_transport_inv_inj {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') (N : Cocone G') (x : J) :
  cocone_inj (cocone_transport_inv e N) x ≈ cocone_inj N x ∘ to (`1 e x).
Proof. reflexivity. Qed.

Lemma isacolimit_transport_inj {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') {c : C} (H : IsAColimit G c) (x : J) :
  colimit_inj (isacolimit_transport e H) x
    ≈ colimit_inj H x ∘ from (`1 e x).
Proof. reflexivity. Qed.

Lemma isacolimit_transport_med {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') {c : C} (H : IsAColimit G c) (N : Cocone G') :
  colimit_med (isacolimit_transport e H) N
    ≈ colimit_med H (cocone_transport_inv e N).
Proof. reflexivity. Qed.

(* The strict forms.  Each names the constant it is about on one side and
   a genuinely different expression — built from the donor accessors — on
   the other, so none is a tautology. *)

Example cocone_transport_inj_strict {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') (N : Cocone G) (x : J) :
  cocone_inj (cocone_transport e N) x = cocone_inj N x ∘ from (`1 e x)
  := eq_refl.

Example cocone_transport_inv_inj_strict {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') (N : Cocone G') (x : J) :
  cocone_inj (cocone_transport_inv e N) x = cocone_inj N x ∘ to (`1 e x)
  := eq_refl.

Example isacolimit_transport_inj_strict {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') {c : C} (H : IsAColimit G c) (x : J) :
  colimit_inj (isacolimit_transport e H) x
  = colimit_inj H x ∘ from (`1 e x) := eq_refl.

Example isacolimit_transport_med_strict {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') {c : C} (H : IsAColimit G c) (N : Cocone G') :
  colimit_med (isacolimit_transport e H) N
  = colimit_med H (cocone_transport_inv e N) := eq_refl.

(* The apex is untouched: transport moves the injections, never the
   object they land in.  This is the clause the induced-map statement of
   section (C) below cannot make. *)

Example colimit_transport_apex {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') (L : Colimit G) :
  colimit_apex (colimit_transport e L) = colimit_apex L := eq_refl.

(** ** (C) The induced map, without invertibility *)

(* A bundled limit witness, read as a cone.  (Theory/Equivalence/Limit.v
   has [isalimit_to_limit] for the [Limit] packaging; the [Cone]-level
   repackaging is not in tree, and the two constructions below need it.) *)

Definition isalimit_cone {J C : Category} {G : J ⟶ C} {c : C}
  (H : IsALimit G c) : Cone G :=
  @Build_Cone J C G c (@limit_acone _ _ _ _ H).

Section Induced.

Context {J : Category}.
Context {C : Category}.
Context {G G' : J ⟶ C}.
Context (a : G ⟹ G').

(* Push a cone over G along α: postcompose each leg with the component.
   This generalizes Theory/Equivalence/Limit.v's [cone_transport], which
   is this construction at the forward components of an isomorphism (see
   [cone_along_is_cone_transport] below); the coherence needs only
   NATURALITY of α, never invertibility. *)

Definition cone_along_leg (N : Cone G) (x : J) :
  vertex_obj[N] ~{C}~> G' x :=
  transform[a] x ∘ cone_leg N x.

Lemma cone_along_coherence (N : Cone G) {x y : J} (f : x ~{J}~> y) :
  fmap[G'] f ∘ cone_along_leg N x ≈ cone_along_leg N y.
Proof using a.
  unfold cone_along_leg.
  rewrite comp_assoc.
  rewrite (@naturality _ _ _ _ a x y f).
  rewrite <- comp_assoc.
  now rewrite (cone_leg_coherence N f).
Qed.

Definition cone_along (N : Cone G) : Cone G' :=
  @Build_Cone J C G' (vertex_obj[N])
    (@Build_ACone J C (vertex_obj[N]) G' (cone_along_leg N)
       (fun x y f => cone_along_coherence N f)).

Section AtWitnesses.

Context {c c' : C}.
Context (HL : IsALimit G c).
Context (HL' : IsALimit G' c').

(* The comparison: push the limit cone of G along α and mediate through
   the limit of G'.  NOTE the hypotheses — two limits, handed in
   explicitly; nothing says C has all J-shaped limits, and α is an
   arbitrary transformation. *)

Definition limit_induced : c ~{C}~> c' :=
  limit_med HL' (cone_along (isalimit_cone HL)).

Lemma limit_induced_commutes (x : J) :
  limit_leg HL' x ∘ limit_induced ≈ transform[a] x ∘ limit_leg HL x.
Proof using a HL HL'.
  exact (limit_med_commutes HL' (cone_along (isalimit_cone HL)) x).
Qed.

Lemma limit_induced_unique (v : c ~{C}~> c') :
  (∀ x : J, limit_leg HL' x ∘ v ≈ transform[a] x ∘ limit_leg HL x) →
  limit_induced ≈ v.
Proof using a HL HL'.
  intro Hv.
  exact (limit_med_unique HL' (cone_along (isalimit_cone HL)) v Hv).
Qed.

End AtWitnesses.

End Induced.

Arguments limit_induced {J C G G'} a {c c'} HL HL'.
Arguments limit_induced_commutes {J C G G'} a {c c'} HL HL' x.
Arguments limit_induced_unique {J C G G'} a {c c'} HL HL' v _.

(* The comparison at the identity transformation is the identity, and it
   composes.  These are the object-level shadows of functoriality of
   [lim]; no limit FUNCTOR is built here.  [nat_id]'s component is
   [fmap[G] id] rather than [id] (Theory/Natural/Transformation.v),
   which is why [fmap_id] appears. *)

Lemma limit_induced_id {J C : Category} {G : J ⟶ C} {c : C}
  (HL : IsALimit G c) : limit_induced nat_id HL HL ≈ id.
Proof.
  apply limit_induced_unique.
  intro x; simpl.
  rewrite fmap_id, id_left, id_right.
  reflexivity.
Qed.

Lemma limit_induced_comp {J C : Category} {G G' G'' : J ⟶ C}
  (a : G ⟹ G') (b : G' ⟹ G'') {c c' c'' : C}
  (HL : IsALimit G c) (HL' : IsALimit G' c') (HL'' : IsALimit G'' c'') :
  limit_induced (b ∙ a) HL HL''
    ≈ limit_induced b HL' HL'' ∘ limit_induced a HL HL'.
Proof.
  apply limit_induced_unique.
  intro x; simpl.
  rewrite comp_assoc.
  rewrite (limit_induced_commutes b HL' HL'' x).
  rewrite <- comp_assoc.
  rewrite (limit_induced_commutes a HL HL' x).
  now rewrite comp_assoc.
Qed.

(** *** The colimit dual, covariantly *)

(* [Opposite_Transform] sends α : G ⟹ G' to G'^op ⟹ G^op, so the roles of
   the two colimit witnesses are exchanged when the limit statement is
   instantiated — which is exactly what makes the induced arrow run from
   the colimit of G to the colimit of G'.  Every constant below is
   supplied by [:=] or by a bare [exact]; the dual costs nothing, and no
   opposite category appears in any of the types. *)

Definition colimit_induced {J C : Category} {G G' : J ⟶ C} (a : G ⟹ G')
  {c c' : C} (HC : IsAColimit G c) (HC' : IsAColimit G' c') :
  c ~{C}~> c' :=
  limit_induced (Opposite_Transform a) HC' HC.

Lemma colimit_induced_commutes {J C : Category} {G G' : J ⟶ C}
  (a : G ⟹ G') {c c' : C}
  (HC : IsAColimit G c) (HC' : IsAColimit G' c') (x : J) :
  colimit_induced a HC HC' ∘ colimit_inj HC x
    ≈ colimit_inj HC' x ∘ transform[a] x.
Proof. exact (limit_induced_commutes (Opposite_Transform a) HC' HC x). Qed.

Lemma colimit_induced_unique {J C : Category} {G G' : J ⟶ C}
  (a : G ⟹ G') {c c' : C}
  (HC : IsAColimit G c) (HC' : IsAColimit G' c') (v : c ~{C}~> c') :
  (∀ x : J, v ∘ colimit_inj HC x ≈ colimit_inj HC' x ∘ transform[a] x) →
  colimit_induced a HC HC' ≈ v.
Proof.
  intro Hv.
  exact (limit_induced_unique (Opposite_Transform a) HC' HC v Hv).
Qed.

Lemma colimit_induced_id {J C : Category} {G : J ⟶ C} {c : C}
  (HC : IsAColimit G c) : colimit_induced nat_id HC HC ≈ id.
Proof.
  apply colimit_induced_unique.
  intro x; simpl.
  rewrite fmap_id, id_left, id_right.
  reflexivity.
Qed.

Lemma colimit_induced_comp {J C : Category} {G G' G'' : J ⟶ C}
  (a : G ⟹ G') (b : G' ⟹ G'') {c c' c'' : C}
  (HC : IsAColimit G c) (HC' : IsAColimit G' c')
  (HC'' : IsAColimit G'' c'') :
  colimit_induced (b ∙ a) HC HC''
    ≈ colimit_induced b HC' HC'' ∘ colimit_induced a HC HC'.
Proof.
  apply colimit_induced_unique.
  intro x; simpl.
  rewrite <- comp_assoc.
  rewrite (colimit_induced_commutes a HC HC' x).
  rewrite comp_assoc.
  rewrite (colimit_induced_commutes b HC' HC'' x).
  now rewrite comp_assoc.
Qed.

(** ** How (B) and (C) fit together *)

(* The forward components of a [Functor_Setoid] equivalence form a
   natural transformation: the coherence field of [Functor_Setoid] is a
   naturality square in disguise, and [fun_equiv_to_fmap]
   (Theory/Functor.v) is exactly the square, in the other
   orientation.  The tree appears to have no such passage — a sweep of
   every [.v] for a declaration whose type mentions both [≈] and [⟹]
   returns only one hit, a prose comment (Instance/Cat/TwoCategory.v)
   — so this is a search over the SHAPE of the statement and does not
   rule out an equivalent phrased another way.  Without it (C) could not
   be applied to the data (B) consumes. *)

Definition fun_equiv_transform {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') : G ⟹ G'.
Proof.
  apply (Build_Transform' (fun x => to (`1 e x))).
  intros x y f.
  symmetry.
  exact (fun_equiv_to_fmap e x y f).
Defined.

Example fun_equiv_transform_component {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') (x : J) :
  transform[fun_equiv_transform e] x = to (`1 e x) := eq_refl.

(* Theory/Equivalence/Limit.v's [cone_transport] IS [cone_along] at those
   components, LEG BY LEG and on the nose, so the invertible case of (C)
   and the cone half of (B) are one construction.

   MEASURED REJECTION, and it is a fact about proof fields rather than
   about the construction: the WHOLE-RECORD form
   [cone_along (fun_equiv_transform e) N = cone_transport e N] does NOT
   close by [eq_refl].  [ACone] carries its coherence as a field, and the
   two coherences are different opaque constants
   ([cone_along_coherence] here, [cone_transport_coherence] in Limit.v),
   so what the leg-level Example below establishes is the strongest form
   available. *)

Example cone_along_is_cone_transport {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') (N : Cone G) (x : J) :
  cone_leg (cone_along (fun_equiv_transform e) N) x
  = cone_leg (cone_transport e N) x := eq_refl.

(* And the comparison induced between a limit and its OWN transport is
   the identity.  This is what (1) adds to (2): the apex is pinned, so
   the comparison has nowhere to go.  Note the statement names both a (B)
   constant and a (C) constant, and neither side reduces to the other. *)

Lemma limit_induced_of_transport {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') {c : C} (HL : IsALimit G c) :
  limit_induced (fun_equiv_transform e) HL (isalimit_transport e HL) ≈ id.
Proof.
  apply limit_induced_unique.
  intro x.
  now rewrite id_right.
Qed.

(* The colimit reading of the same fact.  The transformation is the
   BACKWARD family here: transporting a colimit precomposes its
   injections with [from], so the comparison that comes out as the
   identity is the one induced by the inverse components. *)

Definition fun_equiv_transform_inv {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') : G' ⟹ G.
Proof.
  apply (Build_Transform' (fun x => from (`1 e x))).
  intros x y f.
  exact (fun_equiv_fmap_from e x y f).
Defined.

Lemma colimit_induced_of_transport {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') {c : C} (H : IsAColimit G c) :
  colimit_induced (fun_equiv_transform_inv e) (isacolimit_transport e H) H
    ≈ id.
Proof.
  apply colimit_induced_unique.
  intro x.
  now rewrite id_left.
Qed.

(** ** Witnesses over the walking arrow *)

(* Non-vacuity.  The cheapest index shape with a non-identity arrow is
   [_2] (Instance/Two.v), and over it both a limit and a colimit of every
   diagram exist for free: the limit is the SOURCE object with legs [id]
   and the diagram's arrow, the colimit the TARGET object with
   injections the arrow and [id].

   These two lemmas are general (any ambient C, any diagram) and are
   proved here because the tree has no limit over [_2].  That absence is
   a search over the SPELLING, not over the meaning:
   [rg -E '(IsALimit|IsAColimit|Limit|Colimit)[^a-zA-Z_][^\n]*_2\b']
   over every [.v] returns nothing outside this file, which does not rule
   out an equivalent statement phrased another way.  They are used only
   by the witnesses below. *)

Definition two_limit_leg {C : Category} (D : _2 ⟶ C) (x : _2) :
  D TwoX ~{C}~> D x :=
  match x with
  | TwoX => id
  | TwoY => fmap[D] TwoXY
  end.

Lemma two_limit_coherence {C : Category} (D : _2 ⟶ C) {x y : _2}
  (f : x ~{_2}~> y) :
  fmap[D] f ∘ two_limit_leg D x ≈ two_limit_leg D y.
Proof.
  destruct f; simpl.
  - rewrite id_right.
    exact (@fmap_id _ _ D TwoX).
  - rewrite (@fmap_id _ _ D TwoY).
    now rewrite id_left.
  - now rewrite id_right.
Qed.

Program Definition two_IsALimit {C : Category} (D : _2 ⟶ C) :
  IsALimit D (D TwoX) := {|
  limit_acone :=
    @Build_ACone _2 C (D TwoX) D (two_limit_leg D)
      (fun x y f => two_limit_coherence D f)
|}.
Next Obligation.
  unshelve refine (Build_Unique _ _ _ (cone_leg N TwoX) _ _).
  - intro x; destruct x; simpl.
    + now rewrite id_left.
    + exact (cone_leg_coherence N TwoXY).
  - intros v Hv.
    specialize (Hv TwoX); simpl in Hv.
    rewrite id_left in Hv.
    now symmetry.
Defined.

Definition two_colimit_inj {C : Category} (D : _2 ⟶ C) (x : _2) :
  D x ~{C}~> D TwoY :=
  match x with
  | TwoX => fmap[D] TwoXY
  | TwoY => id
  end.

Program Definition two_IsAColimit {C : Category} (D : _2 ⟶ C) :
  IsAColimit D (D TwoY) := {|
  limit_acone :=
    @Build_ACone (Opposite _2) (Opposite C) (D TwoY) (Opposite_Functor D)
      (two_colimit_inj D) _
|}.
Next Obligation.
  destruct f; simpl.
  - rewrite (@fmap_id _ _ D TwoX).
    now rewrite id_right.
  - rewrite id_left.
    exact (@fmap_id _ _ D TwoY).
  - now rewrite id_left.
Qed.
Next Obligation.
  unshelve refine (Build_Unique _ _ _ (cocone_inj N TwoY) _ _).
  - intro x; destruct x; simpl.
    + exact (cocone_inj_coherence N TwoXY).
    + now rewrite id_right.
  - intros v Hv.
    specialize (Hv TwoY); simpl in Hv.
    rewrite id_right in Hv.
    now symmetry.
Defined.

(** *** A non-invertible transformation with a non-invertible comparison *)

(* Ambient [_2] as well as index [_2].  The diagram [Id[_2]] has colimit
   apex TwoY; the constant diagram at TwoY has colimit apex TwoY too, so
   for the sharp witness we take the LIMITS instead, whose apexes are
   TwoX and TwoY — genuinely different objects.

   [_2] is thin (Instance/Two.v's [Two_thin]), so every morphism
   obligation below closes with that one lemma. *)

Program Definition two_const : _2 ⟶ _2 := {|
  fobj := fun _ => TwoY;
  fmap := fun _ _ _ => id
|}.

Program Definition two_shift : Id[_2] ⟹ two_const := {|
  transform := fun x => match x with
                        | TwoX => TwoXY
                        | TwoY => TwoIdY
                        end
|}.
Solve Obligations with (intros; apply Two_thin).

(* The two diagrams are NOT naturally isomorphic, so section (B) does not
   apply to this pair at all: an isomorphism would supply an arrow
   TwoY ~> TwoX, and [_2] has none.  This is what makes the witness a
   separation of (C) from (B) rather than an instance of both. *)

Lemma two_shift_diagrams_not_isomorphic : Id[_2] ≈ two_const → False.
Proof.
  intro e.
  exact (TwoHom_Y_X_absurd (from (`1 e TwoX))).
Qed.

(* The transformation itself is not invertible at TwoX ... *)

Lemma two_shift_not_invertible :
  @IsIsomorphism _2 TwoX TwoY (transform[two_shift] TwoX) → False.
Proof. exact TwoXY_not_iso. Qed.

(* ... the two diagrams take TwoX to genuinely different objects, which
   is what makes the two limit apexes different: [two_IsALimit] pins the
   apex of a diagram [D] as [D TwoX], so the two object actions read off
   below ARE the two apexes.  DISPLAY HAZARD: [Check] suppresses the
   functor argument of [fobj], so the left-hand pair prints with the same
   head twice. *)

Example two_shift_fobj_at_TwoX :
  (fobj[Id[_2]] TwoX, fobj[two_const] TwoX) = (TwoX, TwoY) := eq_refl.

Lemma two_shift_apexes_distinct : TwoX = TwoY → False.
Proof. discriminate. Qed.

(* ... and the induced comparison, which exists by (C), is not an
   isomorphism.  It cannot be: it is an arrow TwoX ~> TwoY, and [_2] has
   no arrow back. *)

Definition two_shift_induced : TwoX ~{_2}~> TwoY :=
  limit_induced two_shift (two_IsALimit Id[_2]) (two_IsALimit two_const).

(* It COMPUTES to the transformation's component at TwoX.  This is why
   the two universal properties above are closed with [Defined]: with
   [Qed] the mediator is opaque and only the [≈] form below survives,
   which over a thin ambient says nothing. *)

Example two_shift_induced_computes : two_shift_induced = TwoXY := eq_refl.

Theorem two_shift_induced_not_iso :
  @IsIsomorphism _2 TwoX TwoY two_shift_induced → False.
Proof. intros [g _ _]; exact (TwoHom_Y_X_absurd g). Qed.

(* The comparison does satisfy its defining triangle, so the witness
   exercises the universal property and not merely the existence of an
   arrow.  Over a thin ambient this is automatic, which is exactly why
   the separation above (no natural isomorphism, distinct apexes) is
   what carries the content. *)

Lemma two_shift_induced_commutes (x : _2) :
  limit_leg (two_IsALimit two_const) x ∘ two_shift_induced
    ≈ transform[two_shift] x ∘ limit_leg (two_IsALimit Id[_2]) x.
Proof.
  exact (limit_induced_commutes two_shift (two_IsALimit Id[_2])
           (two_IsALimit two_const) x).
Qed.

(** *** Colimit transport, exercised: distinct diagrams, moved legs *)

(* WHAT THIS COSTS, MEASURED.  A sharp (B) witness needs two diagrams
   that are naturally isomorphic and genuinely different, and constant
   diagrams cannot be different (their arrow action is forced to [id]),
   so the diagram must act non-trivially on [TwoXY].  The obvious route
   is Theory/Shapes.v's [Walk], but requiring that module was
   measured to add NINE modules to this file's 32 — Construction/Arrow,
   Construction/Comma, Instance/One, Instance/Zero, Instance/Omega,
   Instance/Ordinal, Instance/StrictCat and its ToCat satellite — plus
   the Equations plugin, and rebuilding [Walk] here would duplicate a
   donor.

   NEITHER IS NEEDED, and the reason is worth carrying: [Walk] varies its
   OBJECT action, which is what forces its [match] to carry a dependent
   return annotation.  Hold the object action CONSTANT and the arrow
   action has codomain [X ~> X] independently of the endpoints, so the
   [match] is ordinary.  [two_endo] below is therefore not a special case
   of [Walk] dressed up — it is the case [Walk]'s annotation exists to
   avoid — and it costs zero extra modules.

   ENGINEERING FINDING, second sighting of a hazard the tree already
   records (Functor/Construction/Postcompose.v): written INLINE in the
   [Program Definition], even this non-dependent match is compiled
   through the dependent eliminator, and the obligations arrive carrying
   [eq]/[JMeq] hypotheses no ordinary case analysis discharges.
   Elaborating the arrow action as a plain [Definition] first
   ([two_endo_map]) avoids that entirely.  A THIRD hazard, also already
   recorded (Instance/Fun/Group.v): [_2]'s composition is itself
   [Program]-generated, so [destruct f, g] in the [fmap_comp] obligation
   yields an ill-typed application of [Two._2_obligation_1] — destruct
   the OBJECTS first, which is what the proof below does. *)

Definition two_endo_map {C : Category} {X : C} (u : X ~> X)
  (x y : _2) (f : x ~{_2}~> y) : X ~{C}~> X :=
  match f with
  | TwoIdX => id
  | TwoIdY => id
  | TwoXY  => u
  end.

Program Definition two_endo {C : Category} (X : C) (u : X ~> X) :
  _2 ⟶ C := {|
  fobj := fun _ => X;
  fmap := two_endo_map u
|}.
Next Obligation. destruct x; reflexivity. Qed.
Next Obligation.
  pose proof (TwoHom_inv _ _ f) as Hf.
  pose proof (TwoHom_inv _ _ g) as Hg.
  destruct x, y, z; simpl in *; try contradiction; subst; simpl;
    first [ now rewrite id_left | now rewrite id_right ].
Qed.

Example two_endo_arrow {C : Category} (X : C) (u : X ~> X) :
  fmap[two_endo X u] TwoXY = u := eq_refl.

(* The ambient: [bool] as a discrete setoid, with negation as a
   non-identity self-isomorphism of it. *)

Definition two_bool_set : SetoidObject :=
  {| carrier := bool ; is_setoid := eq_Setoid bool |}.

Program Definition two_negb_map :
  two_bool_set ~{Sets}~> two_bool_set := {| morphism := negb |}.

Program Definition two_negb_iso :
  @Isomorphism Sets two_bool_set two_bool_set :=
  {| to := two_negb_map ; from := two_negb_map |}.
Next Obligation. destruct x; reflexivity. Qed.
Next Obligation. destruct x; reflexivity. Qed.

(* Two diagrams over the walking arrow, sending [TwoXY] to [id] and to
   negation respectively. *)

Definition two_id_diagram : _2 ⟶ Sets := @two_endo Sets two_bool_set id.

Definition two_negb_diagram : _2 ⟶ Sets :=
  @two_endo Sets two_bool_set two_negb_map.

(* They are naturally isomorphic — identity at TwoX, negation at TwoY,
   the square closing because negation is its own inverse ... *)

Definition two_diagrams_equiv : two_id_diagram ≈ two_negb_diagram.
Proof.
  exists (fun x => match x with
                   | TwoX => iso_id
                   | TwoY => two_negb_iso
                   end).
  intros x y f; destruct f; simpl; intro b; destruct b; reflexivity.
Defined.

(* ... and they are genuinely different diagrams: their arrow actions at
   [TwoXY] are not even [≈]-equal, which is strictly stronger than
   refuting a Leibniz equality of the two functor records.

   NOT DELIVERED, and measured rather than overlooked: the Leibniz form
   [two_id_diagram = two_negb_diagram → False] is not stated.  The two
   are universe-POLYMORPHIC constants that receive different universe
   instances, so [rewrite] cannot abstract over one of them — it reports
   that abstracting leads to an ill-typed term.  Nothing is lost: two
   functors that were Leibniz equal would have [≈]-equal arrow actions,
   so the statement below refutes the Leibniz form a fortiori. *)

Lemma two_diagrams_differ :
  fmap[two_id_diagram] TwoXY ≈ fmap[two_negb_diagram] TwoXY → False.
Proof. intro K; specialize (K true); simpl in K; discriminate. Qed.

(* The colimit of the first diagram, and the transport of it along the
   isomorphism.  THE TRANSPORT VISIBLY MOVES A LEG: the injection at
   TwoY goes from the identity to negation, and the two are provably
   not [≈]-equal.  This is what makes the (B) witness a demonstration
   rather than a restatement — the transport genuinely consumes [e] and
   is not a projection. *)

Definition two_id_colimit : IsAColimit two_id_diagram two_bool_set :=
  two_IsAColimit two_id_diagram.

(* MEASURED REJECTION: the strict form of the next statement,
   [... TwoY = two_negb_map], is rejected.  The transported leg is
   [id ∘ two_negb_map], and composition in [Sets] rebuilds a
   [SetoidMorphism] record rather than reducing, so the [id ∘ _] residue
   survives.  The control is the line after it, where the ORIGINAL leg
   IS [id] strictly. *)

Lemma two_transport_inj_computes :
  colimit_inj (isacolimit_transport two_diagrams_equiv two_id_colimit)
    TwoY ≈ two_negb_map.
Proof. intro b; destruct b; reflexivity. Qed.

Example two_id_colimit_inj_Y :
  colimit_inj two_id_colimit TwoY = id := eq_refl.

Theorem two_transport_moves_inj :
  colimit_inj (isacolimit_transport two_diagrams_equiv two_id_colimit) TwoY
    ≈ colimit_inj two_id_colimit TwoY → False.
Proof. intro K; specialize (K true); simpl in K; discriminate. Qed.

(* The walking arrow's own (co)limit legs compute, at the identity
   diagram, which is what the two Examples above are read against. *)

Example two_colimit_inj_X :
  colimit_inj (two_IsAColimit Id[_2]) TwoX = TwoXY := eq_refl.

Example two_colimit_inj_Y :
  colimit_inj (two_IsAColimit Id[_2]) TwoY = TwoIdY := eq_refl.

Example two_limit_leg_Y :
  limit_leg (two_IsALimit Id[_2]) TwoY = TwoXY := eq_refl.
