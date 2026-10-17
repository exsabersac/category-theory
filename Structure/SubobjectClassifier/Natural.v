Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * The subobject classifier classifies NATURALLY *)

(*
   nLab: https://ncatlab.org/nlab/show/representable+functor

   本文件给出自然变换相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ClassifierNatural.

Context {C : Category}.
Context `{HT : @Terminal C}.
Context `{HP : @HasPullbacks C}.
Context `{HS : @SubobjectClassifier C HT}.

(* ------------------------------------------------------------------------ *)
(** ** The substitution law *)

(* The characteristic morphism of a subobject, with the mono and its
   monicity read off the record rather than passed separately.  This is the
   [to] leg of [classifier_classifies] as a plain function; the [eq_refl]
   below records that naming it changed nothing. *)
Definition char_sub {x : C} (s : SubObj x) : x ~> Ω :=
  char (sub_mono s) (sub_is_monic s).

Example char_sub_is_classifier_to {x : C} (s : SubObj x) :
  char_sub s = to (classifier_classifies x) s := eq_refl.

(* [char_respects] is stated on the three components; a subobject is its
   own triple, so the passage is a [destruct]. *)
Lemma char_sub_respects {x : C} (s s' : SubObj x) :
  s ≈ s' → char_sub s ≈ char_sub s'.
Proof. destruct s, s'; apply char_respects. Qed.

(* THE NATURALITY SQUARE.  Pulling a subobject back along f and then
   classifying is classifying and then precomposing with f.

   The proof is the round trip in both directions.  Reindexing truth along
   [char_sub s ∘ f] is, by the pasting lemma [sub_reindex_comp], reindexing
   along [char_sub s] and then along f; the first of those recovers s by
   [classifier_pullback_roundtrip], so the whole thing is [sub_reindex f s].
   Classifying both sides and using [classifier_char_roundtrip] on the
   right-hand one concludes. *)
Lemma char_reindex {x y : C} (f : y ~> x) (s : SubObj x) :
  char_sub (sub_reindex f s) ≈ char_sub s ∘ f.
Proof.
  transitivity (char_sub (sub_reindex (char_sub s ∘ f) truth_subobject)).
  - apply char_sub_respects.
    symmetry.
    transitivity (sub_reindex f (sub_reindex (char_sub s) truth_subobject)).
    + apply sub_reindex_comp.
    + apply sub_reindex_respects, classifier_pullback_roundtrip.
  - apply classifier_char_roundtrip.
Qed.

(* The companion square for the inverse leg: reindexing along f the
   pullback of truth along h is the pullback of truth along h ∘ f.  This is
   [sub_reindex_comp] read backwards, and it is stated separately only
   because the transformation below needs it in this orientation. *)
Lemma reindex_char {x y : C} (f : y ~> x) (h : x ~> Ω) :
  sub_reindex f (sub_reindex h truth_subobject)
    ≈ sub_reindex (h ∘ f) truth_subobject.
Proof. symmetry; apply sub_reindex_comp. Qed.

(* TWO MORE ORIENTATIONS, STATED AS LEMMAS FOR A MECHANICAL REASON worth
   recording once here rather than at each use.  By the time a [Program]
   obligation of the isomorphism below is reached, its [simpl] has unfolded
   the subobject equivalence into the underlying sigma, so the [symmetry]
   and [transitivity] TACTICS have no relation left to turn — they report
   "Cannot find a relation to rewrite".  Stated as lemmas, where the goal
   is still the folded [≈], both go through in one line, and the
   obligations then close by [apply], which converts. *)

Lemma sub_reindex_id_sym {x : C} (s : SubObj x) : s ≈ sub_reindex id s.
Proof. symmetry; apply sub_reindex_id. Qed.

Lemma classifier_pullback_roundtrip_id {x : C} (s : SubObj x) :
  sub_reindex (char_sub s) truth_subobject ≈ sub_reindex id s.
Proof.
  transitivity s.
  - apply classifier_pullback_roundtrip.
  - apply sub_reindex_id_sym.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** The two natural transformations *)

(* Both components are taken verbatim from [classifier_classifies], so what
   the two definitions add is precisely the naturality field. *)

(* The [@]-spellings below are forced and worth a note: [classifier_classifies]
   takes its category as an IMPLICIT argument inferred from the type of its
   object, and the objects here arrive as [obj[C^op]].  Left to itself the
   elaborator instantiates the donor at [C^op] and then cannot match
   [@SubObj (C^op) x] against [carrier (fobj[Sub] x)].  Pinning C is the
   whole fix; nothing about the mathematics changes. *)

Program Definition classifier_char_transform :
  @Transform (C^op) Sets (@Sub C HP) (@Curried_CoHom C Ω) := {|
  transform := fun x : C => to (@classifier_classifies C HT HP HS x)
|}.
Next Obligation. simpl; intros; symmetry; apply (@char_reindex x y f). Qed.
Next Obligation. simpl; intros; apply (@char_reindex x y f). Qed.

Program Definition classifier_pullback_transform :
  @Transform (C^op) Sets (@Curried_CoHom C Ω) (@Sub C HP) := {|
  transform := fun x : C => from (@classifier_classifies C HT HP HS x)
|}.
Next Obligation. simpl; intros; apply (@reindex_char x y f). Qed.
(* The symmetric orientation, applied in [sub_reindex_comp]'s own
   direction for the reason given above. *)
Next Obligation.
  simpl; intros; rename x0 into h.
  exact (sub_reindex_comp h f truth_subobject).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Awodey's clause: the correspondence is natural *)

Program Definition Sub_classifier_natural :
  @Isomorphism ([(C^op), Sets]) (@Sub C HP) (@Curried_CoHom C Ω) := {|
  to   := classifier_char_transform ;
  from := classifier_pullback_transform
|}.
Next Obligation.
  simpl; intros.
  transitivity x0.
  - apply classifier_char_roundtrip.
  - symmetry; apply id_right.
Qed.
Next Obligation. simpl; intros; apply classifier_pullback_roundtrip_id. Qed.

(* THE UPGRADE IS THE PRE-EXISTING BIJECTION, machine-checked.  Both legs
   are the corresponding legs of [classifier_classifies] at Leibniz [=] —
   the convertibility exception, flagged as such — so no reader has to take
   on trust that this is the same correspondence rather than a second one
   that happens to agree. *)
Example classifier_natural_component_to (x : C) :
  transform (to Sub_classifier_natural) x = to (classifier_classifies x)
  := eq_refl.

Example classifier_natural_component_from (x : C) :
  transform (from Sub_classifier_natural) x = from (classifier_classifies x)
  := eq_refl.

Example classifier_natural_to_computes (x : C) (s : SubObj x) :
  transform (to Sub_classifier_natural) x s = char_sub s := eq_refl.

Example classifier_natural_from_computes (x : C) (h : x ~> Ω) :
  transform (from Sub_classifier_natural) x h
    = sub_reindex h truth_subobject := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** The Yoneda reading *)

(* Naturality is exactly what turns the family of bijections into a
   representation, so the upgrade has an immediate payoff: [Sub] is a
   representable presheaf and Ω is a representing object.  [Representable]
   is Functor/Representable.v's class, whose [represented] field is a
   natural isomorphism [Hom(A, ─) ≅ F] — read here at [C^op], where
   [Hom ─,Ω] is that hom-functor. *)
(* [Representable]'s [represented] field is spelled with the COVARIANT
   [Curried_Hom] of the index category, here [@Curried_Hom (C^op) Ω]; the
   contravariant spelling used above is that same term by [Definition]
   ([Curried_CoHom C := Curried_Hom C^op]), recorded here by [eq_refl].
   The isomorphism is nevertheless built by [exact] rather than supplied as
   a record field, because the elaborator does not unfold [Curried_CoHom]
   while unifying a field's expected type. *)
Example CoHom_is_Hom_op : @Curried_CoHom C Ω = @Curried_Hom (C^op) Ω := eq_refl.

Definition Sub_Representable : Representable (@Sub C HP) :=
  @Build_Representable (C^op) (@Sub C HP) (@Ω C HT HS)
    (iso_sym Sub_classifier_natural).

Example Sub_repr_obj :
  @repr_obj (C^op) (@Sub C HP) Sub_Representable = @Ω C HT HS := eq_refl.

End ClassifierNatural.
