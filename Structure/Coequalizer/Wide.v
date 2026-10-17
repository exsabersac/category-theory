Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Equalizer.Wide.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Parallel.Wide.
Require Import Category.Instance.Two.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

Generalizable All Variables.

(** * Wide coequalizers, elementarily: wide coforks and descent *)

(*
   nLab:      https://ncatlab.org/nlab/show/wide+pullback
   Wikipedia: https://en.wikipedia.org/wiki/Coequaliser

   本文件给出 wide 相关构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The wide coequalizer of a diagram of shape [WideParallel I]: a colimit,
   exactly as [Structure/Equalizer.v]'s [Coequalizer] is over the two-arrow
   shape. *)
Definition WideCoequalizer {C : Category} {I : Type} (F : WideParallel I ⟶ C) :=
  Colimit F.

(* The elementary universal property: [e] coequalizes the whole family at q,
   and every map h out of y that absorbs the family descends uniquely
   across e. *)
Record IsWideCoequalizer {C : Category} {I : Type} {x y : C}
  (fs : I → x ~> y) (q : C) (e : y ~> q) := {
  (* the coequalizing map absorbs every member in the same way *)
  wcofork : ∀ i j : I, e ∘ fs i ≈ e ∘ fs j;

  (* universal property: every jointly coforking map descends uniquely *)
  wcoeq_desc {z} (h : y ~> z) (Hh : ∀ i j : I, h ∘ fs i ≈ h ∘ fs j) :
    ∃! u : q ~> z, u ∘ e ≈ h
}.

Arguments wcofork {_ _ _ _ _ _ _} _ _ _.
Arguments wcoeq_desc {_ _ _ _ _ _ _} _ {_} _ _.

(* A category has all wide coequalizers when every family of parallel
   arrows carries an elementary wide coequalizer. *)
Class HasWideCoequalizers (C : Category) := {
  wide_coeq {I : Type} {x y : C} (fs : I → x ~> y) :
    ∃ (q : C) (e : y ~> q), IsWideCoequalizer fs q e
}.

Section WideCoequalizerColimit.

Context {C : Category}.
Context {I : Type}.
Context {x y : C}.
Context (fs : I → x ~> y).

(* Abbreviations for the diagram and its shape; these are notations, so the
   statements below are literally about [AWide fs] and [WideParallel I]. *)
Local Notation WFam := (AWide fs).
Local Notation WShape := (WideParallel I).

(** ** Wide coequalizing maps are epimorphisms *)

Lemma wide_coequalizer_epic {q : C} {e : y ~> q}
  (E : IsWideCoequalizer fs q e) : Epic e.
Proof.
  constructor.
  intros z g1 g2 Hg.
  assert (Hcofork : ∀ i j : I, (g1 ∘ e) ∘ fs i ≈ (g1 ∘ e) ∘ fs j).
  { intros i j.
    rewrite <- !comp_assoc.
    rewrite (wcofork E i j).
    reflexivity. }
  transitivity (unique_obj (wcoeq_desc E (g1 ∘ e) Hcofork)).
  - symmetry.
    apply (uniqueness (wcoeq_desc E (g1 ∘ e) Hcofork)).
    reflexivity.
  - apply (uniqueness (wcoeq_desc E (g1 ∘ e) Hcofork)).
    symmetry.
    exact Hg.
Qed.

(** ** Wide coequalizers are unique up to isomorphism *)

Lemma wide_coequalizer_unique {q1 q2 : C} {e1 : y ~> q1} {e2 : y ~> q2}
  (E1 : IsWideCoequalizer fs q1 e1) (E2 : IsWideCoequalizer fs q2 e2) :
  q1 ≅ q2.
Proof.
  pose proof (wcoeq_desc E1 e2 (wcofork E2)) as D12.
  pose proof (wcoeq_desc E2 e1 (wcofork E1)) as D21.
  pose proof (wcoeq_desc E1 e1 (wcofork E1)) as D11.
  pose proof (wcoeq_desc E2 e2 (wcofork E2)) as D22.
  unshelve refine {| to := unique_obj D12; from := unique_obj D21 |}.
  - transitivity (unique_obj D22).
    + symmetry.
      apply (uniqueness D22).
      rewrite <- comp_assoc.
      rewrite (unique_property D21).
      exact (unique_property D12).
    + apply (uniqueness D22).
      apply id_left.
  - transitivity (unique_obj D11).
    + symmetry.
      apply (uniqueness D11).
      rewrite <- comp_assoc.
      rewrite (unique_property D12).
      exact (unique_property D21).
    + apply (uniqueness D11).
      apply id_left.
Defined.

(** ** From the colimit presentation to the cofork equations *)

(* The colimit injection over [ParY] absorbs the whole family: every member
   pushes it to the injection over [ParX], by injection coherence at that
   member.  No inhabitant of I is needed. *)
Lemma wide_colimit_coequalizes (L : WideCoequalizer WFam) :
  ∀ i j : I,
    colimit_inj (colimit_is_acolimit L) ParY ∘ fs i
      ≈ colimit_inj (colimit_is_acolimit L) ParY ∘ fs j.
Proof.
  intros i j.
  transitivity (colimit_inj (colimit_is_acolimit L) ParX).
  - exact (colimit_inj_coherence (colimit_is_acolimit L)
             (i : ParX ~{WShape}~> ParY)).
  - symmetry.
    exact (colimit_inj_coherence (colimit_is_acolimit L)
             (j : ParX ~{WShape}~> ParY)).
Qed.

(** ** The round trips, over a chosen member of the family *)

Section Pointed.

(* A chosen index; the section is exactly the scope of that hypothesis. *)
Context (i0 : I).

(* The injections of the cocone induced by a jointly coforking map h: the
   injection out of [ParX] is the common composite through the chosen
   member, the one out of [ParY] is h itself. *)
Definition wcofork_legs {z : C} (h : y ~> z) (p : ParObj) :
  WFam p ~{C}~> z :=
  match p return (WFam p ~{C}~> z) with
  | ParX => h ∘ fs i0
  | ParY => h
  end.

(* Injection coherence, phrased covariantly in C: precomposing the leg at
   the codomain of a shape arrow with its image recovers the leg at the
   domain.  This statement is definitionally the [cone_coherence] field of
   an [ACone] over [WFam^op]. *)
Lemma wcofork_legs_coherence {z : C} (h : y ~> z)
  (Hh : ∀ i j : I, h ∘ fs i ≈ h ∘ fs j) :
  ∀ (a b : ParObj) (k : b ~{WShape}~> a),
    wcofork_legs h a ∘ fmap[WFam] k ≈ wcofork_legs h b.
Proof.
  intros a b k.
  destruct a, b; simpl in *.
  - (* the identity arrow on ParX *)
    apply id_right.
  - (* an arrow ParY ~> ParX: refuted by the empty hom-set *)
    destruct k.
  - (* the arrow k : I, sent to fs k *)
    exact (Hh k i0).
  - (* the identity arrow on ParY *)
    apply id_right.
Qed.

Definition wcofork_cocone {z : C} (h : y ~> z)
  (Hh : ∀ i j : I, h ∘ fs i ≈ h ∘ fs j) : Cocone WFam :=
  @Build_Cone (WShape^op) (C^op) (WFam^op) z
    (@Build_ACone (WShape^op) (C^op) z (WFam^op)
       (wcofork_legs h) (wcofork_legs_coherence h Hh)).

(* Descent through the colimit apex. *)
Lemma wide_colimit_coequalizer_desc (L : WideCoequalizer WFam)
  {z : C} (h : y ~> z) (Hh : ∀ i j : I, h ∘ fs i ≈ h ∘ fs j) :
  ∃! u : colimit_apex L ~> z,
    u ∘ colimit_inj (colimit_is_acolimit L) ParY ≈ h.
(* Lib.v sets [Default Proof Using "Type"], which keeps only the section
   variables occurring in the STATEMENT.  This is the ONE proof in the
   section that reaches for [i0] without its statement mentioning it — the
   others go through [wcofork_legs], whose body carries the dependency. *)
Proof using All.
  unshelve eapply Build_Unique.
  - exact (colimit_med (colimit_is_acolimit L) (wcofork_cocone h Hh)).
  - exact (colimit_med_commutes
             (colimit_is_acolimit L) (wcofork_cocone h Hh) ParY).
  - intros v Hv.
    refine (colimit_med_unique
              (colimit_is_acolimit L) (wcofork_cocone h Hh) v _).
    intros p.
    destruct p.
    + (* the ParX injection follows from the ParY one via coherence at i0 *)
      rewrite <- (colimit_inj_coherence (colimit_is_acolimit L)
                    (i0 : ParX ~{WShape}~> ParY)).
      rewrite comp_assoc.
      rewrite Hv.
      reflexivity.
    + exact Hv.
Qed.

(* A colimit of [AWide fs] is an elementary wide coequalizer at its apex. *)
Definition wide_coequalizer_is_coequalizer (L : WideCoequalizer WFam) :
  IsWideCoequalizer fs (colimit_apex L)
    (colimit_inj (colimit_is_acolimit L) ParY) :=
  {| wcofork     := wide_colimit_coequalizes L
   ; wcoeq_desc  := fun z h Hh => wide_colimit_coequalizer_desc L h Hh |}.

(** ** From the elementary presentation back to the colimit *)

Definition is_wide_coequalizer_cocone {q : C} {e : y ~> q}
  (E : IsWideCoequalizer fs q e) : Cocone WFam :=
  wcofork_cocone e (wcofork E).

(* The universal property of that cocone, phrased covariantly in C; this
   statement is definitionally the [ump_limits] field of the colimit whose
   limit cone is [is_wide_coequalizer_cocone]. *)
Lemma is_wide_coequalizer_cocone_ump {q : C} {e : y ~> q}
  (E : IsWideCoequalizer fs q e) (N : Cocone WFam) :
  ∃! u : q ~> vertex_obj[N],
    ∀ p : ParObj, u ∘ wcofork_legs e p ≈ cocone_inj N p.
Proof.
  assert (HX : ∀ i : I, cocone_inj N ParY ∘ fs i ≈ cocone_inj N ParX).
  { intro i.
    exact (cocone_inj_coherence N (i : ParX ~{WShape}~> ParY)). }
  assert (Hfs : ∀ i j : I,
                  cocone_inj N ParY ∘ fs i ≈ cocone_inj N ParY ∘ fs j).
  { intros i j.
    rewrite (HX i).
    rewrite (HX j).
    reflexivity. }
  unshelve eapply Build_Unique.
  - exact (unique_obj (wcoeq_desc E (cocone_inj N ParY) Hfs)).
  - intros p.
    destruct p.
    + (* the injection out of ParX: u ∘ (e ∘ fs i0) ≈ nX via the ParY
         triangle *)
      simpl.
      rewrite comp_assoc.
      rewrite (unique_property (wcoeq_desc E (cocone_inj N ParY) Hfs)).
      exact (HX i0).
    + exact (unique_property (wcoeq_desc E (cocone_inj N ParY) Hfs)).
  - intros v Hv.
    apply (uniqueness (wcoeq_desc E (cocone_inj N ParY) Hfs)).
    exact (Hv ParY).
Qed.

(* An elementary wide coequalizer yields the bundled colimit over the wide
   shape. *)
Definition is_wide_coequalizer_colimit {q : C} {e : y ~> q}
  (E : IsWideCoequalizer fs q e) : WideCoequalizer WFam :=
  {| limit_cone := is_wide_coequalizer_cocone E
   ; ump_limits := fun N => is_wide_coequalizer_cocone_ump E N |}.

End Pointed.

(** ** The inhabitant is necessary, not merely convenient *)

(* Over an empty index the cofork condition is vacuous, so the identity of y
   satisfies the elementary record. *)
Lemma wide_empty_id_IsWideCoequalizer (Hempty : I → False) :
  IsWideCoequalizer fs y id[y].
Proof.
  unshelve refine {| wcofork := _ |}.
  - intros i j; destruct (Hempty i).
  - intros z h Hh.
    unshelve eapply Build_Unique.
    + exact h.
    + apply id_right.
    + intros v Hv.
      rewrite <- Hv.
      apply id_right.
Defined.

End WideCoequalizerColimit.

(* An UNPOINTED round trip on the colimit side would likewise manufacture an
   arrow x ~> y out of nothing: apply it to the identity above and read off
   the colimit injection over [ParX]. *)
Definition wide_unpointed_coround_trip_gives_hom
  {C : Category} {I : Type} {x y : C} (fs : I → x ~> y)
  (Hempty : I → False)
  (RT : ∀ (q : C) (e : y ~> q),
          IsWideCoequalizer fs q e → IsAColimit (AWide fs) q) :
  x ~{C}~> y :=
  colimit_inj (RT y id[y] (wide_empty_id_IsWideCoequalizer fs Hempty)) ParX.

(* And that is refutable at the walking arrow, whose hom-set
   [TwoY ~> TwoX] is empty. *)
Theorem wide_coround_trip_needs_point :
  (∀ (q : _2) (e : TwoX ~{_2}~> q),
     IsWideCoequalizer two_empty_family q e
     → IsAColimit (AWide two_empty_family) q) → False.
Proof.
  intro RT.
  exact (TwoHom_Y_X_absurd
           (wide_unpointed_coround_trip_gives_hom two_empty_family
              (fun i => match i with end) RT)).
Qed.
