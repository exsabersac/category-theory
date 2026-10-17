Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Parallel.Wide.
Require Import Category.Instance.Two.

Generalizable All Variables.

(** * Wide equalizers, elementarily: wide forks and descent *)

(*
   nLab:      https://ncatlab.org/nlab/show/wide+pullback
   Wikipedia: https://en.wikipedia.org/wiki/Equaliser_(mathematics)

   本文件给出 wide 相关构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The wide equalizer of a diagram of shape [WideParallel I]: a terminal
   cone, exactly as [Structure/Equalizer.v]'s [Equalizer] is over the
   two-arrow shape. *)
Definition WideEqualizer {C : Category} {I : Type} (F : WideParallel I ⟶ C) :=
  Limit F.

(* The elementary universal property: [e] equalizes the whole family at q,
   and every map h into x that the family agrees on factors uniquely
   through e. *)
Record IsWideEqualizer {C : Category} {I : Type} {x y : C}
  (fs : I → x ~> y) (q : C) (e : q ~> x) := {
  (* every member of the family absorbs e in the same way *)
  wfork_eq : ∀ i j : I, fs i ∘ e ≈ fs j ∘ e;

  (* universal property: every jointly forking map h factors uniquely *)
  weq_desc {z} (h : z ~> x) (Hh : ∀ i j : I, fs i ∘ h ≈ fs j ∘ h) :
    ∃! u : z ~> q, e ∘ u ≈ h
}.

Arguments wfork_eq {_ _ _ _ _ _ _} _ _ _.
Arguments weq_desc {_ _ _ _ _ _ _} _ {_} _ _.

(* A category has all wide equalizers when every family of parallel arrows
   carries an elementary wide equalizer.  The index [Type] is a universe
   PARAMETER of the class, not a quantifier over every universe, exactly as
   for [Structure/Limit/Product.v]'s indexed products; a consumer whose
   index is a hom-type instantiates it there. *)
Class HasWideEqualizers (C : Category) := {
  wide_equalizer {I : Type} {x y : C} (fs : I → x ~> y) :
    ∃ (q : C) (e : q ~> x), IsWideEqualizer fs q e
}.

Section WideEqualizerLimit.

Context {C : Category}.
Context {I : Type}.
Context {x y : C}.
Context (fs : I → x ~> y).

(* Abbreviations for the diagram and its shape; these are notations, so the
   statements below are literally about [AWide fs] and [WideParallel I]. *)
Local Notation WFam := (AWide fs).
Local Notation WShape := (WideParallel I).

(** ** Wide equalizing maps are monomorphisms *)

(*
   本节说明 Wide 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma wide_equalizer_monic {q : C} {e : q ~> x}
  (E : IsWideEqualizer fs q e) : Monic e.
Proof.
  constructor.
  intros z g1 g2 Hg.
  assert (Hfork : ∀ i j : I, fs i ∘ (e ∘ g1) ≈ fs j ∘ (e ∘ g1)).
  { intros i j.
    rewrite !comp_assoc.
    rewrite (wfork_eq E i j).
    reflexivity. }
  transitivity (unique_obj (weq_desc E (e ∘ g1) Hfork)).
  - symmetry.
    apply (uniqueness (weq_desc E (e ∘ g1) Hfork)).
    reflexivity.
  - apply (uniqueness (weq_desc E (e ∘ g1) Hfork)).
    symmetry.
    exact Hg.
Qed.

(** ** Wide equalizers are unique up to isomorphism *)

Lemma wide_equalizer_unique {q1 q2 : C} {e1 : q1 ~> x} {e2 : q2 ~> x}
  (E1 : IsWideEqualizer fs q1 e1) (E2 : IsWideEqualizer fs q2 e2) :
  q1 ≅ q2.
Proof.
  pose proof (weq_desc E2 e1 (wfork_eq E1)) as D12.
  pose proof (weq_desc E1 e2 (wfork_eq E2)) as D21.
  pose proof (weq_desc E1 e1 (wfork_eq E1)) as D11.
  pose proof (weq_desc E2 e2 (wfork_eq E2)) as D22.
  unshelve refine {| to := unique_obj D12; from := unique_obj D21 |}.
  - transitivity (unique_obj D22).
    + symmetry.
      apply (uniqueness D22).
      rewrite comp_assoc.
      rewrite (unique_property D12).
      exact (unique_property D21).
    + apply (uniqueness D22).
      apply id_right.
  - transitivity (unique_obj D11).
    + symmetry.
      apply (uniqueness D11).
      rewrite comp_assoc.
      rewrite (unique_property D21).
      exact (unique_property D12).
    + apply (uniqueness D11).
      apply id_right.
Defined.

(** ** From the limit presentation to the fork equations *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma wide_limit_equalizes (L : WideEqualizer WFam) :
  ∀ i j : I,
    fs i ∘ limit_leg (limit_is_alimit L) ParX
      ≈ fs j ∘ limit_leg (limit_is_alimit L) ParX.
Proof.
  intros i j.
  transitivity (limit_leg (limit_is_alimit L) ParY).
  - exact (limit_leg_coherence (limit_is_alimit L)
             (i : ParX ~{WShape}~> ParY)).
  - symmetry.
    exact (limit_leg_coherence (limit_is_alimit L)
             (j : ParX ~{WShape}~> ParY)).
Qed.

(** ** The round trips, over a chosen member of the family *)

Section Pointed.

(*
   本节说明 Wide 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Context (i0 : I).

(* The legs of the cone induced by a jointly forking map h: the leg over
   [ParX] is h itself, the leg over [ParY] the common composite through the
   chosen member. *)
Definition wfork_legs {z : C} (h : z ~> x) (p : ParObj) :
  z ~{C}~> WFam p :=
  match p return (z ~{C}~> WFam p) with
  | ParX => h
  | ParY => fs i0 ∘ h
  end.

(* Leg coherence.  This statement is definitionally the [cone_coherence]
   field of an [ACone] over [AWide fs]. *)
Lemma wfork_legs_coherence {z : C} (h : z ~> x)
  (Hh : ∀ i j : I, fs i ∘ h ≈ fs j ∘ h) :
  ∀ (a b : ParObj) (k : a ~{WShape}~> b),
    fmap[WFam] k ∘ wfork_legs h a ≈ wfork_legs h b.
Proof.
  intros a b k.
  destruct a, b; simpl in *.
  - (* the identity arrow on ParX *)
    apply id_left.
  - (* the arrow k : I, sent to fs k *)
    exact (Hh k i0).
  - (* an arrow ParY ~> ParX: refuted by the empty hom-set *)
    destruct k.
  - (* the identity arrow on ParY *)
    apply id_left.
Qed.

Definition wfork_cone {z : C} (h : z ~> x)
  (Hh : ∀ i j : I, fs i ∘ h ≈ fs j ∘ h) : Cone WFam :=
  @Build_Cone WShape C WFam z
    (@Build_ACone WShape C z WFam
       (wfork_legs h) (wfork_legs_coherence h Hh)).

(* Descent through the limit apex. *)
Lemma wide_limit_equalizer_desc (L : WideEqualizer WFam)
  {z : C} (h : z ~> x) (Hh : ∀ i j : I, fs i ∘ h ≈ fs j ∘ h) :
  ∃! u : z ~> L, limit_leg (limit_is_alimit L) ParX ∘ u ≈ h.
(*
   本节说明 Wide 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Proof using All.
  unshelve eapply Build_Unique.
  - exact (limit_med (limit_is_alimit L) (wfork_cone h Hh)).
  - exact (limit_med_commutes
             (limit_is_alimit L) (wfork_cone h Hh) ParX).
  - intros v Hv.
    refine (limit_med_unique
              (limit_is_alimit L) (wfork_cone h Hh) v _).
    intros p.
    destruct p.
    + exact Hv.
    + (* the ParY leg follows from the ParX leg via coherence at i0 *)
      rewrite <- (limit_leg_coherence (limit_is_alimit L)
                    (i0 : ParX ~{WShape}~> ParY)).
      rewrite <- comp_assoc.
      rewrite Hv.
      reflexivity.
Qed.

(* A limit of [AWide fs] is an elementary wide equalizer at its apex. *)
Definition wide_equalizer_is_equalizer (L : WideEqualizer WFam) :
  IsWideEqualizer fs L (limit_leg (limit_is_alimit L) ParX) :=
  {| wfork_eq  := wide_limit_equalizes L
   ; weq_desc  := fun z h Hh => wide_limit_equalizer_desc L h Hh |}.

(** ** From the elementary presentation back to the limit *)

Definition is_wide_equalizer_cone {q : C} {e : q ~> x}
  (E : IsWideEqualizer fs q e) : Cone WFam :=
  wfork_cone e (wfork_eq E).

(* The universal property of that cone; definitionally the [ump_limits]
   field of the limit whose limit cone is [is_wide_equalizer_cone]. *)
Lemma is_wide_equalizer_cone_ump {q : C} {e : q ~> x}
  (E : IsWideEqualizer fs q e) (N : Cone WFam) :
  ∃! u : vertex_obj[N] ~> q,
    ∀ p : ParObj, wfork_legs e p ∘ u ≈ cone_leg N p.
Proof.
  assert (HX : ∀ i : I, fs i ∘ cone_leg N ParX ≈ cone_leg N ParY).
  { intro i.
    exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) _ _
             (i : ParX ~{WShape}~> ParY)). }
  assert (Hfs : ∀ i j : I, fs i ∘ cone_leg N ParX ≈ fs j ∘ cone_leg N ParX).
  { intros i j.
    rewrite (HX i).
    rewrite (HX j).
    reflexivity. }
  unshelve eapply Build_Unique.
  - exact (unique_obj (weq_desc E (cone_leg N ParX) Hfs)).
  - intros p.
    destruct p.
    + exact (unique_property (weq_desc E (cone_leg N ParX) Hfs)).
    + (* the leg over ParY: (fs i0 ∘ e) ∘ u ≈ nY via the ParX triangle *)
      simpl.
      rewrite <- comp_assoc.
      rewrite (unique_property (weq_desc E (cone_leg N ParX) Hfs)).
      exact (HX i0).
  - intros v Hv.
    apply (uniqueness (weq_desc E (cone_leg N ParX) Hfs)).
    exact (Hv ParX).
Qed.

(* An elementary wide equalizer yields the bundled limit over the wide
   shape. *)
Definition is_wide_equalizer_limit {q : C} {e : q ~> x}
  (E : IsWideEqualizer fs q e) : WideEqualizer WFam :=
  {| limit_cone := is_wide_equalizer_cone E
   ; ump_limits := fun N => is_wide_equalizer_cone_ump E N |}.

End Pointed.

(** ** The inhabitant is necessary, not merely convenient *)

(* Over an empty index the fork condition is vacuous, so the identity of x
   satisfies the elementary record — descent is then just [id_left], and
   needs no emptiness at all. *)
Lemma wide_empty_id_IsWideEqualizer (Hempty : I → False) :
  IsWideEqualizer fs x id[x].
Proof.
  unshelve refine {| wfork_eq := _ |}.
  - intros i j; destruct (Hempty i).
  - intros z h Hh.
    unshelve eapply Build_Unique.
    + exact h.
    + apply id_left.
    + intros v Hv.
      rewrite <- Hv.
      apply id_left.
Defined.

End WideEqualizerLimit.

(*
   本节说明（余）极限、等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition wide_unpointed_round_trip_gives_hom
  {C : Category} {I : Type} {x y : C} (fs : I → x ~> y)
  (Hempty : I → False)
  (RT : ∀ (q : C) (e : q ~> x),
          IsWideEqualizer fs q e → IsALimit (AWide fs) q) :
  x ~{C}~> y :=
  limit_leg (RT x id[x] (wide_empty_id_IsWideEqualizer fs Hempty)) ParY.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition two_empty_family : Empty_set → (TwoY ~{_2}~> TwoX) :=
  fun i => match i with end.

Theorem wide_round_trip_needs_point :
  (∀ (q : _2) (e : q ~{_2}~> TwoY),
     IsWideEqualizer two_empty_family q e
     → IsALimit (AWide two_empty_family) q) → False.
Proof.
  intro RT.
  exact (TwoHom_Y_X_absurd
           (wide_unpointed_round_trip_gives_hom two_empty_family
              (fun i => match i with end) RT)).
Qed.
