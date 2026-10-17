Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Span.
Require Import Category.Instance.Roof.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(*
   本文件给出骨架分离相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** A coherence helper for the two-object discrete shape *)

Lemma two_discrete_cone_coherence {C : Category} (H : Two_Discrete ⟶ C)
  (c : C) (leg : ∀ x : Two_Discrete, c ~{C}~> H x)
  {x y : Two_Discrete} (f : x ~{Two_Discrete}~> y) :
  fmap[H] f ∘ leg x ≈ leg y.
Proof.
  destruct f;
  [ change (fmap[H] (@id Two_Discrete TwoDX) ∘ leg TwoDX ≈ leg TwoDX)
  | change (fmap[H] (@id Two_Discrete TwoDY) ∘ leg TwoDY ≈ leg TwoDY) ];
  rewrite fmap_id; apply id_left.
Qed.

(** ** The diagram: the two feet of the walking span *)

Definition SepK : Two_Discrete ⟶ Roof := @Pick_Two Roof RNeg RPos.

Definition sep_cone : Cone SepK :=
  @Build_Cone Two_Discrete Roof SepK RZero
    (@Build_ACone Two_Discrete Roof RZero SepK
       (fun x => match x return RZero ~{Roof}~> SepK x with
                 | TwoDX => ZeroNeg
                 | TwoDY => ZeroPos
                 end)
       (fun x y f => I)).

(* Only the apex of the span carries legs into both feet. *)

Lemma sep_apex (v : Roof) (f : v ~{Roof}~> RNeg) (g : v ~{Roof}~> RPos) :
  RZero = v.
Proof.
  destruct v.
  - exact (False_rect _ (RNeg_RPos_absurd g)).
  - reflexivity.
  - exact (False_rect _ (RPos_RNeg_absurd f)).
Qed.

Definition sep_med (v : Roof) (f : v ~{Roof}~> RNeg) (g : v ~{Roof}~> RPos) :
  v ~{Roof}~> RZero.
Proof.
  destruct v.
  - exact (False_rect _ (RNeg_RPos_absurd g)).
  - exact IdZero.
  - exact (False_rect _ (RPos_RNeg_absurd f)).
Defined.

Definition sep_IsLimitCone : IsLimitCone sep_cone.
Proof.
  intro M.
  unshelve refine
    {| unique_obj := sep_med _ (cone_leg M TwoDX) (cone_leg M TwoDY) |}.
  - intro x; exact I.
  - intros v _; exact I.
Defined.

(** ** The functor: both legs of the span go to the first projection *)

Definition SepF : Roof ⟶ Coq :=
  @ASpan Coq (prod bool bool) bool bool (@fst bool bool) (@fst bool bool).

(** ** [bool × bool] with its genuine projections is the limit downstairs *)

Definition sep_prod_cone : Cone (SepF ◯ SepK) :=
  @Build_Cone Two_Discrete Coq (SepF ◯ SepK) (prod bool bool)
    (@Build_ACone Two_Discrete Coq (prod bool bool) (SepF ◯ SepK)
       (fun x => match x return
                   prod bool bool ~{Coq}~> (SepF ◯ SepK) x with
                 | TwoDX => @fst bool bool
                 | TwoDY => @snd bool bool
                 end)
       (fun x y f => two_discrete_cone_coherence (SepF ◯ SepK) _ _ f)).

Definition sep_prod_IsLimitCone : IsLimitCone sep_prod_cone.
Proof.
  intro M.
  unshelve refine
    {| unique_obj := fun w => (cone_leg M TwoDX w, cone_leg M TwoDY w) |}.
  - intros x w; destruct x; reflexivity.
  - intros v Hv w.
    pose proof (Hv TwoDX w) as H1.
    pose proof (Hv TwoDY w) as H2.
    destruct (v w) as [a b] eqn:Hw.
    assert (Ha : a = cone_leg M TwoDX w)
      by (rewrite <- H1; change (a = fst (v w)); rewrite Hw; reflexivity).
    assert (Hb : b = cone_leg M TwoDY w)
      by (rewrite <- H2; change (b = snd (v w)); rewrite Hw; reflexivity).
    subst; reflexivity.
Defined.

(** ** The image cone is NOT limiting, though its apex carries a limit *)

Definition sep_image_isalimit : IsALimit (SepF ◯ SepK) (SepF RZero) :=
  limitcone_isalimit sep_prod_IsLimitCone.

Definition sep_bad_cone : Cone (SepF ◯ SepK) :=
  @Build_Cone Two_Discrete Coq (SepF ◯ SepK) bool
    (@Build_ACone Two_Discrete Coq bool (SepF ◯ SepK)
       (fun x => match x return bool ~{Coq}~> (SepF ◯ SepK) x with
                 | TwoDX => fun b : bool => b
                 | TwoDY => negb
                 end)
       (fun x y f => two_discrete_cone_coherence (SepF ◯ SepK) _ _ f)).

Theorem sep_image_not_limiting : IsLimitCone (FCone SepF sep_cone) → False.
Proof.
  intro H.
  destruct (H sep_bad_cone) as [u Hu _].
  pose proof (Hu TwoDX true) as H1.
  pose proof (Hu TwoDY true) as H2.
  change (fst (u true) = true) in H1.
  change (fst (u true) = false) in H2.
  rewrite H1 in H2; discriminate.
Qed.

(* Statement (A): the apex carries a limit of the composite diagram, and the
   image cone at that very apex is not universal. *)

Definition apex_limit_without_limit_cone :
  IsALimit (SepF ◯ SepK) vertex_obj[FCone SepF sep_cone]
    * (IsLimitCone (FCone SepF sep_cone) → False) :=
  (sep_image_isalimit, sep_image_not_limiting).

(** ** Statement (B): the class-level separation *)

Definition sep_PreservesLimit : PreservesLimit SepK SepF :=
  @Build_PreservesLimit Two_Discrete Roof SepK Coq SepF
    (fun L =>
       match sep_apex _ (cone_leg (@limit_cone _ _ _ L) TwoDX)
                        (cone_leg (@limit_cone _ _ _ L) TwoDY)
         in _ = z return IsALimit (SepF ◯ SepK) (SepF z)
       with eq_refl => sep_image_isalimit end).

Definition sep_not_PreservesLimitCone : PreservesLimitCone SepK SepF → False :=
  fun P => sep_image_not_limiting (P sep_cone sep_IsLimitCone).

Theorem PreservesLimit_not_PreservesLimitCone :
  (∀ (J C D : Category) (K : J ⟶ C) (F : C ⟶ D),
     PreservesLimit K F → PreservesLimitCone K F) → False.
Proof.
  intro H.
  exact (sep_not_PreservesLimitCone (H _ _ _ SepK SepF sep_PreservesLimit)).
Qed.

(** ** The documented non-invertible endomorphism, exhibited *)

Definition sep_dup : prod bool bool ~{Coq}~> prod bool bool :=
  fun p => (fst p, fst p).

Lemma sep_image_reindexes (x : Two_Discrete) :
  cone_leg sep_prod_cone x ∘ sep_dup ≈ cone_leg (FCone SepF sep_cone) x.
Proof. destruct x; intro w; reflexivity. Qed.

Lemma sep_dup_not_iso : IsIsomorphism sep_dup → False.
Proof.
  intros [g Hr _].
  pose proof (f_equal fst (Hr (true, false))) as E1.
  pose proof (f_equal snd (Hr (true, false))) as E2.
  change (fst (g (true, false)) = true) in E1.
  change (fst (g (true, false)) = false) in E2.
  rewrite E1 in E2; discriminate.
Qed.

Lemma sep_comparison_is_dup :
  cone_comparison SepF sep_cone sep_prod_IsLimitCone ≈ sep_dup.
Proof.
  apply cone_comparison_unique.
  exact sep_image_reindexes.
Qed.

Theorem sep_comparison_not_iso :
  IsIsomorphism (cone_comparison SepF sep_cone sep_prod_IsLimitCone) → False.
Proof.
  intros [g Hr Hl].
  apply sep_dup_not_iso.
  unshelve refine {| two_sided_inverse := g |}.
  - rewrite <- sep_comparison_is_dup; exact Hr.
  - rewrite <- sep_comparison_is_dup; exact Hl.
Qed.

(* And yet the apex-only witness produces an isomorphism between the same two
   objects — just not the canonical one. *)

Definition sep_apex_iso (L : Limit SepK) :
  SepF (vertex_obj[L]) ≅ vertex_obj[sep_prod_cone] :=
  apex_iso_of_PreservesLimit SepF sep_PreservesLimit L sep_prod_IsLimitCone.
