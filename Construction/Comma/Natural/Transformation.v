Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Deloop.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** Huq's correspondence: natural transformations as sections of the comma
    projections. *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Comma_category
   Wikipedia: "If the domains of S, T are equal, then the diagram which

   本文件给出自然变换变体。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明自然变换、函子、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* natural transformation S ⟹ T  ↦  section functor D ⟶ (S ↓ T) *)
Program Definition Comma_Functor {C D : Category} {S T : D ⟶ C}
        (F : S ⟹ T) : D ⟶ (S ↓ T) := {|
  fobj := fun X : D => ((X, X); F X);
  fmap := fun _ _ f => ((f, f); _)
|}.
Next Obligation. apply naturality_sym. Qed.

#[local] Obligation Tactic := simpl; intros.

(* section functor D ⟶ (S ↓ T) of both projections  ↦  natural transformation
   S ⟹ T (the inverse direction of Huq's bijection) *)
Program Definition Comma_Transform {C D : Category} {S T : D ⟶ C}
        (F : D ⟶ (S ↓ T))
        (proj1 : comma_proj1 ◯ F ≈[Cat] Id)
        (proj2 : comma_proj2 ◯ F ≈[Cat] Id) : S ⟹ T := {|
  transform := fun X =>
    fmap (to (`1 proj2 X)) ∘ `2 (F X) ∘ fmap (from (`1 proj1 X))
|}.
Next Obligation.
  rewrite !comp_assoc.
  rewrite <- fmap_comp.
  rewrite <- !comp_assoc.
  rewrite <- fmap_comp.

  spose (`2 proj1 _ _ f) as X0.
  spose (`2 proj2 _ _ f) as X1.

  rewrite <- (id_left f) at 1.
  rewrite <- (iso_to_from (`1 proj2 y)).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ f).
  rewrites.
  rewrite fmap_comp.
  comp_left.

  symmetry.
  rewrite <- (id_right f) at 1.
  rewrite <- (iso_to_from (`1 proj1 x)).
  rewrite !comp_assoc.
  rewrites.
  rewrite fmap_comp.
  comp_right.

  exact (`2 (fmap[F] f)).
Qed.
Next Obligation.
  symmetry.
  apply Comma_Transform_obligation_1.
Qed.

Section HuqBijection.

Context {C D : Category}.
Context {S T : D ⟶ C}.

(** ** The canonical section witnesses *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Comma_Functor_proj1_strict (tau : S ⟹ T) :
  comma_proj1 ◯ Comma_Functor tau ≈[StrictCat] Id := (fun _ => eq_refl; _).
Next Obligation. reflexivity. Qed.

Program Definition Comma_Functor_proj2_strict (tau : S ⟹ T) :
  comma_proj2 ◯ Comma_Functor tau ≈[StrictCat] Id := (fun _ => eq_refl; _).
Next Obligation. reflexivity. Qed.

(*
   本节说明函子、hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Comma_Functor_proj1 (tau : S ⟹ T) :
  comma_proj1 ◯ Comma_Functor tau ≈[Cat] Id := (fun _ => iso_id; _).
Next Obligation. rewrite id_left, id_right; reflexivity. Qed.

Program Definition Comma_Functor_proj2 (tau : S ⟹ T) :
  comma_proj2 ◯ Comma_Functor tau ≈[Cat] Id := (fun _ => iso_id; _).
Next Obligation. rewrite id_left, id_right; reflexivity. Qed.

(** ** Round trip 1: recovering a natural transformation *)

(* At the canonical witnesses the conjugation of [Comma_Transform] collapses:
   both isomorphism components are the identity, so the recovered component is
   [fmap id ∘ tau X ∘ fmap id]. *)

Theorem Comma_Transform_Comma_Functor (tau : S ⟹ T) :
  Comma_Transform (Comma_Functor tau)
    (Comma_Functor_proj1 tau) (Comma_Functor_proj2 tau) ≈ tau.
Proof.
  intro X; simpl.
  rewrite !fmap_id.
  rewrite id_left, id_right.
  reflexivity.
Qed.

(** ** Witness dependence *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem Comma_Transform_witness_shift
        (F : D ⟶ (S ↓ T))
        (p p' : comma_proj1 ◯ F ≈[Cat] Id)
        (q q' : comma_proj2 ◯ F ≈[Cat] Id) (d : D) :
  Comma_Transform F p' q' d
    ≈ fmap[T] (to (`1 q' d) ∘ from (`1 q d))
        ∘ Comma_Transform F p q d
        ∘ fmap[S] (to (`1 p d) ∘ from (`1 p' d)).
Proof.
  assert (Hq : fmap[T] (to (`1 q' d) ∘ from (`1 q d)) ∘ fmap[T] (to (`1 q d))
                 ≈ fmap[T] (to (`1 q' d))).
  { rewrite <- fmap_comp, <- comp_assoc, iso_from_to, id_right.
    reflexivity. }
  assert (Hp : fmap[S] (from (`1 p d)) ∘ fmap[S] (to (`1 p d) ∘ from (`1 p' d))
                 ≈ fmap[S] (from (`1 p' d))).
  { rewrite <- fmap_comp, comp_assoc, iso_from_to, id_left.
    reflexivity. }
  simpl.
  rewrite !comp_assoc, Hq.
  rewrite <- !comp_assoc, Hp.
  reflexivity.
Qed.

(*
   本节说明 Transformation 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Corollary Comma_Transform_witness_irrelevant
        (F : D ⟶ (S ↓ T))
        (p p' : comma_proj1 ◯ F ≈[Cat] Id)
        (q q' : comma_proj2 ◯ F ≈[Cat] Id) :
  (∀ d, to (`1 p d) ≈ to (`1 p' d)) →
  (∀ d, to (`1 q d) ≈ to (`1 q' d)) →
  Comma_Transform F p' q' ≈ Comma_Transform F p q.
Proof.
  intros Hp Hq d.
  rewrite (Comma_Transform_witness_shift F p p' q q' d).
  rewrite <- (Hq d), (Hp d), !iso_to_from, !fmap_id, id_left, id_right.
  reflexivity.
Qed.

(** ** Round trip 2: recovering the section functor *)

(* The comparison isomorphism between [Comma_Functor (Comma_Transform F p q) d]
   — that is, ((d, d); the recovered component) — and [F d]; its legs are the
   two section witnesses at d. *)

Program Definition Comma_Functor_Comma_Transform_iso
        (F : D ⟶ (S ↓ T))
        (p : comma_proj1 ◯ F ≈[Cat] Id)
        (q : comma_proj2 ◯ F ≈[Cat] Id) (d : D) :
  Comma_Functor (Comma_Transform F p q) d ≅ F d := {|
  to   := ((from (`1 p d), from (`1 q d)); _);
  from := ((to   (`1 p d), to   (`1 q d)); _)
|}.
Next Obligation.
  rewrite !comp_assoc.
  rewrite <- fmap_comp, iso_from_to, fmap_id, id_left.
  reflexivity.
Qed.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp, iso_from_to, fmap_id, id_right.
  reflexivity.
Qed.
Next Obligation. split; apply iso_from_to. Qed.
Next Obligation. split; apply iso_to_from. Qed.

(* Naturality of that comparison. Note it uses only the coherence fields of
   the two witnesses; no property of [Comma_Transform] is needed. *)

Lemma Comma_Functor_Comma_Transform_natural
        (F : D ⟶ (S ↓ T))
        (p : comma_proj1 ◯ F ≈[Cat] Id)
        (q : comma_proj2 ◯ F ≈[Cat] Id) (x y : D) (f : x ~> y) :
  fmap[Comma_Functor (Comma_Transform F p q)] f
    ≈ from (Comma_Functor_Comma_Transform_iso F p q y)
        ∘ fmap[F] f
        ∘ to (Comma_Functor_Comma_Transform_iso F p q x).
Proof.
  spose (`2 p x y f) as Hp.
  spose (`2 q x y f) as Hq.
  split; simpl.
  - rewrite Hp.
    rewrite !comp_assoc, iso_to_from, id_left.
    rewrite <- comp_assoc, iso_to_from, id_right.
    reflexivity.
  - rewrite Hq.
    rewrite !comp_assoc, iso_to_from, id_left.
    rewrite <- comp_assoc, iso_to_from, id_right.
    reflexivity.
Qed.

(* Packaged transparently (not by [exists ...; Qed]) so that the components of
   the natural isomorphism remain observable downstream — [huq_section_
   compatible] below reads them. *)

Definition Comma_Functor_Comma_Transform
        (F : D ⟶ (S ↓ T))
        (p : comma_proj1 ◯ F ≈[Cat] Id)
        (q : comma_proj2 ◯ F ≈[Cat] Id) :
  Comma_Functor (Comma_Transform F p q) ≈[Cat] F :=
  (Comma_Functor_Comma_Transform_iso F p q;
   Comma_Functor_Comma_Transform_natural F p q).

(** ** The bijection *)

(* Two isomorphism-cancellation lemmas, used to compare two sections of the
   projections through their witnesses. *)

Lemma iso_conj_cancel {E : Category} {a b c : E} (i : a ≅ c) (j : b ≅ c) :
  (from j ∘ to i) ∘ (from i ∘ to j) ≈ id.
Proof.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (to i)).
  rewrite iso_to_from, id_left.
  apply iso_from_to.
Qed.

Lemma iso_conj_recompose {E : Category} {p q m p' q' m' : E}
      (u : p ≅ m) (v : q ≅ m) (u' : p' ≅ m') (v' : q' ≅ m') (g : m' ~> m) :
  (from u ∘ to v) ∘ (from v ∘ g ∘ to v') ∘ (from v' ∘ to u')
    ≈ from u ∘ g ∘ to u'.
Proof.
  rewrite !comp_assoc.
  rewrite <- (comp_assoc (from u) (to v) (from v)).
  rewrite iso_to_from, id_right.
  rewrite <- (comp_assoc (from u ∘ g) (to v') (from v')).
  rewrite iso_to_from, id_right.
  reflexivity.
Qed.

(* A section of both projections, packaged with its two witnesses. The
   witnesses are DATA, not a property: [Comma_Transform] genuinely depends on
   them ([Comma_Transform_witness_shift] above), so they cannot be discarded. *)

Record HuqSection : Type := {
  huq_functor : D ⟶ (S ↓ T);
  huq_sec1    : comma_proj1 ◯ huq_functor ≈[Cat] Id;
  huq_sec2    : comma_proj2 ◯ huq_functor ≈[Cat] Id
}.

Definition huq_transform (X : HuqSection) : S ⟹ T :=
  Comma_Transform (huq_functor X) (huq_sec1 X) (huq_sec2 X).

Definition huq_section (tau : S ⟹ T) : HuqSection :=
  {| huq_functor := Comma_Functor tau;
     huq_sec1    := Comma_Functor_proj1 tau;
     huq_sec2    := Comma_Functor_proj2 tau |}.

Lemma huq_transform_apply (X : HuqSection) (d : D) :
  huq_transform X d
    ≈ fmap[T] (to (`1 (huq_sec2 X) d))
        ∘ `2 (huq_functor X d)
        ∘ fmap[S] (from (`1 (huq_sec1 X) d)).
Proof. reflexivity. Qed.

Theorem huq_transform_section (tau : S ⟹ T) : huq_transform (huq_section tau) ≈ tau.
Proof. apply Comma_Transform_Comma_Functor. Qed.

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition HuqCompatible (X Y : HuqSection) : Type :=
  ∃ theta : huq_functor X ≈[Cat] huq_functor Y,
      (∀ d, to (`1 (huq_sec1 X) d)
              ≈ to (`1 (huq_sec1 Y) d) ∘ fst `1 (to (`1 theta d)))
    * (∀ d, to (`1 (huq_sec2 X) d)
              ≈ to (`1 (huq_sec2 Y) d) ∘ snd `1 (to (`1 theta d))).

(* Well-definedness of the backward map on the quotient. *)

Theorem huq_compatible_transform (X Y : HuqSection) :
  HuqCompatible X Y → huq_transform X ≈ huq_transform Y.
Proof.
  intros [theta [H1 H2]] d.
  spose (`2 (to (`1 theta d))) as Hsq.
  assert (Hu0 : fst `1 (to (`1 theta d))
                  ≈ from (`1 (huq_sec1 Y) d) ∘ to (`1 (huq_sec1 X) d)).
  { rewrite (H1 d), comp_assoc, iso_from_to, id_left; reflexivity. }
  assert (Hu : fst `1 (to (`1 theta d)) ∘ from (`1 (huq_sec1 X) d)
                 ≈ from (`1 (huq_sec1 Y) d)).
  { rewrite Hu0, <- comp_assoc, iso_to_from, id_right; reflexivity. }
  unfold huq_transform; simpl.
  rewrite <- Hu, (H2 d), !fmap_comp.
  rewrite !comp_assoc.
  comp_right.
  rewrite <- !comp_assoc.
  comp_left.
  symmetry; exact Hsq.
Qed.

(*
   本节说明等价、同构、核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* Undoing the conjugation on the [S] side: the recovered transformation,
   precomposed with the first witness, is the comma component of F d
   postcomposed with the second. *)
Lemma huq_transform_unconj (X : HuqSection) (d : D) :
  huq_transform X d ∘ fmap[S] (to (`1 (huq_sec1 X) d))
    ≈ fmap[T] (to (`1 (huq_sec2 X) d)) ∘ `2 (huq_functor X d).
Proof.
  rewrite (huq_transform_apply X d).
  rewrite <- (comp_assoc (fmap[T] (to (`1 (huq_sec2 X) d))
                            ∘ `2 (huq_functor X d))).
  rewrite <- fmap_comp, iso_from_to, fmap_id, id_right.
  reflexivity.
Qed.

(*
   本节说明 Transformation 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma huq_transform_shift (X Y : HuqSection)
      (H : huq_transform X ≈ huq_transform Y) (d : D) :
  fmap[T] (to (`1 (huq_sec2 X) d)) ∘ `2 (huq_functor X d)
    ≈ fmap[T] (to (`1 (huq_sec2 Y) d)) ∘ `2 (huq_functor Y d)
        ∘ fmap[S] (from (`1 (huq_sec1 Y) d))
        ∘ fmap[S] (to (`1 (huq_sec1 X) d)).
Proof.
  rewrite <- (huq_transform_apply Y d).
  rewrite <- (H d).
  symmetry; apply huq_transform_unconj.
Qed.

Program Definition huq_compare (X Y : HuqSection)
        (H : huq_transform X ≈ huq_transform Y) (d : D) :
  huq_functor X d ~{S ↓ T}~> huq_functor Y d :=
  ((from (`1 (huq_sec1 Y) d) ∘ to (`1 (huq_sec1 X) d),
    from (`1 (huq_sec2 Y) d) ∘ to (`1 (huq_sec2 X) d)); _).
Next Obligation.
  rewrite !fmap_comp.
  rewrite <- (comp_assoc (fmap[T] (from (`1 (huq_sec2 Y) d)))).
  rewrite (huq_transform_shift X Y H d).
  rewrite !comp_assoc, <- fmap_comp, iso_from_to, fmap_id, id_left.
  reflexivity.
Qed.

Program Definition huq_compare_iso (X Y : HuqSection)
        (H : huq_transform X ≈ huq_transform Y) (d : D) :
  huq_functor X d ≅ huq_functor Y d := {|
  to   := huq_compare X Y H d;
  from := huq_compare Y X (symmetry H) d
|}.
Next Obligation. split; apply iso_conj_cancel. Qed.
Next Obligation. split; apply iso_conj_cancel. Qed.

Lemma huq_compare_natural (X Y : HuqSection)
      (H : huq_transform X ≈ huq_transform Y) (x y : D) (f : x ~> y) :
  fmap[huq_functor X] f
    ≈ from (huq_compare_iso X Y H y)
        ∘ fmap[huq_functor Y] f
        ∘ to (huq_compare_iso X Y H x).
Proof.
  spose (`2 (huq_sec1 X) x y f) as H1X.
  spose (`2 (huq_sec1 Y) x y f) as H1Y.
  spose (`2 (huq_sec2 X) x y f) as H2X.
  spose (`2 (huq_sec2 Y) x y f) as H2Y.
  split; simpl.
  - rewrite H1X, H1Y.
    symmetry; apply iso_conj_recompose.
  - rewrite H2X, H2Y.
    symmetry; apply iso_conj_recompose.
Qed.

Definition huq_compare_equiv (X Y : HuqSection)
           (H : huq_transform X ≈ huq_transform Y) :
  huq_functor X ≈[Cat] huq_functor Y :=
  (huq_compare_iso X Y H; huq_compare_natural X Y H).

Theorem huq_transform_compatible (X Y : HuqSection) :
  huq_transform X ≈ huq_transform Y → HuqCompatible X Y.
Proof.
  intro H.
  exists (huq_compare_equiv X Y H).
  split; intro d; simpl;
  rewrite comp_assoc, iso_to_from, id_left; reflexivity.
Qed.

Theorem huq_compatible_iff (X Y : HuqSection) :
  HuqCompatible X Y ↔ huq_transform X ≈ huq_transform Y.
Proof.
  split.
  - apply huq_compatible_transform.
  - apply huq_transform_compatible.
Qed.

(*
   本节说明等价、同构、核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem huq_section_compatible (X : HuqSection) :
  HuqCompatible (huq_section (huq_transform X)) X.
Proof.
  exists (Comma_Functor_Comma_Transform (huq_functor X) (huq_sec1 X) (huq_sec2 X)).
  split; intro d; simpl; symmetry; apply iso_to_from.
Qed.

Program Definition HuqSection_Setoid : Setoid HuqSection := {|
  equiv := HuqCompatible
|}.
Next Obligation.
  constructor.
  - intro X.
    apply huq_transform_compatible; reflexivity.
  - intros X Y HXY.
    apply huq_transform_compatible.
    symmetry; now apply huq_compatible_transform.
  - intros X Y Z HXY HYZ.
    apply huq_transform_compatible.
    transitivity (huq_transform Y); now apply huq_compatible_transform.
Qed.

Definition huq_dom : SetoidObject := {| carrier := S ⟹ T |}.
Definition huq_cod : SetoidObject :=
  {| carrier := HuqSection; is_setoid := HuqSection_Setoid |}.

Program Definition Huq_roundtrip : @Isomorphism Sets huq_dom huq_cod := {|
  to   := {| morphism := huq_section |};
  from := {| morphism := huq_transform |}
|}.
Next Obligation.
  proper.
  apply huq_transform_compatible.
  rewrite !huq_transform_section.
  assumption.
Qed.
Next Obligation.
  proper.
  now apply huq_compatible_transform.
Qed.
Next Obligation. apply huq_section_compatible. Qed.
Next Obligation. apply huq_transform_section. Qed.

End HuqBijection.

(** ** Witness dependence is not merely formal *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Local Notation BZ2 := (Deloop Bool_Xor).

Definition huq_sep_tau : Id[BZ2] ⟹ Id[BZ2] := nat_id.

Definition huq_sep_F : BZ2 ⟶ (Id[BZ2] ↓ Id[BZ2]) := Comma_Functor huq_sep_tau.

(* The twisted witness: the component is [true], self-inverse in Z/2, and the
   coherence condition holds because conjugating by [true] on both sides is the
   identity. *)
Program Definition huq_sep_twist :
  comma_proj1 ◯ huq_sep_F ≈[Cat] Id := (fun _ => {| to := true; from := true |}; _).
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. now destruct f. Qed.

Definition huq_sep_canonical : HuqSection :=
  {| huq_functor := huq_sep_F;
     huq_sec1    := Comma_Functor_proj1 huq_sep_tau;
     huq_sec2    := Comma_Functor_proj2 huq_sep_tau |}.

Definition huq_sep_twisted : HuqSection :=
  {| huq_functor := huq_sep_F;
     huq_sec1    := huq_sep_twist;
     huq_sec2    := Comma_Functor_proj2 huq_sep_tau |}.

Example huq_sep_canonical_value : huq_transform huq_sep_canonical ttt = false :=
  eq_refl.

Example huq_sep_twisted_value : huq_transform huq_sep_twisted ttt = true :=
  eq_refl.

Theorem huq_witness_separates :
  huq_transform huq_sep_canonical ≈ huq_transform huq_sep_twisted → False.
Proof.
  intro H.
  specialize (H ttt).
  discriminate.
Qed.

(* The quotient of [Huq_roundtrip] therefore distinguishes two packaged
   sections with the SAME underlying functor: [HuqCompatible] is strictly
   finer than equality of section functors. *)

Corollary huq_witness_sections_incompatible :
  HuqCompatible huq_sep_canonical huq_sep_twisted → False.
Proof.
  intro HC.
  now apply huq_witness_separates, huq_compatible_transform.
Qed.
