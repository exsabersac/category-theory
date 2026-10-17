Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Adjunction.Map.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Morphism.
Require Import Category.Monad.Morphism.Algebra.
Require Import Category.Monad.Monadicity.BeckObjects.
Require Import Category.Monad.Monadicity.Crude.
Require Import Category.Monad.Monadicity.Beck.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.

Generalizable All Variables.

(* * * Comparisons two resolutions one 单子 （已译） *)

(*
   Book: Awodey, "Category Theory", 1st ed. (Carnegie Mellon pre-print,
   Book: Riehl, "Category Theory in Context", §5.2, the category Adj_T,
   nLab: https://ncatlab.org/nlab/show/monadic+adjunction

   本文件给出比较函子/分解相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(* * ** Definition: comparison over identification 单子 （已译） *)

Section ComparisonDef.

(* The 对象 hom levels [Monads X], kept apart (see UNIVERSES). （已译） *)
Universes m1 m2.

Context {X : Category}.
Context {A : Category} {F : X ⟶ A} {G : A ⟶ X} (Adj : F ⊣ G).
Context {A' : Category} {F' : X ⟶ A'} {G' : A' ⟶ X} (Adj' : F' ⊣ G').
Context (θ : @Isomorphism (Monads@{_ _ m1 m2} X)
               (G' ◯ F'; Adjunction_Induced_Monad Adj')
               (G ◯ F; Adjunction_Induced_Monad Adj)).

(* Mac Lane's M F' = F G M = G', each up natural 同构, and
 identification two 单子 they induce, G' F' ≅ G M F' ≅ G F,
 given one. （已译） *)
Record Comparison : Type := {
  cmp_functor : A' ⟶ A;
  cmp_left : cmp_functor ◯ F' ≈ F;
  cmp_right : G ◯ cmp_functor ≈ G';
  cmp_monad (x : X) :
    fmap[G] (to (`1 cmp_left x)) ∘ from (`1 cmp_right (F' x))
      ≈ transform[mh_transform (to θ)] x
}.

Lemma cmp_theta_to_from (x : X) :
  transform[mh_transform (to θ)] x ∘ transform[mh_transform (from θ)] x
    ≈ id.
Proof. exact (iso_to_from θ x). Qed.

Lemma cmp_theta_from_to (x : X) :
  transform[mh_transform (from θ)] x ∘ transform[mh_transform (to θ)] x
    ≈ id.
Proof. exact (iso_from_to θ x). Qed.

(* ------------------------------------------------------------------------ *)
(* * ** A comparison map 伴随 (Adjunction/Map.v) （已译） *)

Section Squares.

Context (P : Comparison).

Local Notation M := (cmp_functor P).
Local Notation al x := (`1 (cmp_left P) x).
Local Notation be a := (`1 (cmp_right P) a).

(* The coherence read backwards: β ∘ G α⁻¹ is θ⁻¹. *)
Lemma cmp_monad_inv (x : X) :
  to (be (F' x)) ∘ fmap[G] (from (al x))
    ≈ transform[mh_transform (from θ)] x.
Proof.
  transitivity (to (be (F' x)) ∘ fmap[G] (from (al x))
                  ∘ (transform[mh_transform (to θ)] x
                       ∘ transform[mh_transform (from θ)] x)).
  { rewrite cmp_theta_to_from. symmetry. apply id_right. }
  rewrite <- (cmp_monad P x).
  rewrite !comp_assoc.
  rewrite <- (comp_assoc (to (be (F' x)))).
  simpl.
  rewrite <- (@fmap_comp _ _ G).
  rewrite iso_from_to, fmap_id, id_right.
  rewrite iso_to_from.
  apply id_left.
Qed.

(* 相关说明。 （已译） *)
Definition Comparison_squares : @WeakAdjSquares A' X F' G' A X F G.
Proof using P.
  unshelve refine {| wsq_K := M; wsq_L := Id[X] |}.
  - exists (fun x => al x).
    intros x y f.
    exact (`2 (cmp_left P) x y f).
  - exists (fun a => iso_sym (be a)).
    intros a b f; simpl.
    rewrite (`2 (cmp_right P) a b f).
    rewrite !comp_assoc.
    rewrite iso_to_from, id_left.
    rewrite <- comp_assoc.
    rewrite iso_to_from.
    symmetry. apply id_right.
Defined.

(* 相关说明。 （已译） *)
Lemma Comparison_unit : WeakSquaresUnit Adj' Adj Comparison_squares.
Proof.
  intros x; simpl.
  transitivity (fmap[G] (from (al x)) ∘ (fmap[G] (to (al x))
                  ∘ from (be (F' x))) ∘ @unit _ _ _ _ Adj' x).
  { rewrite !comp_assoc.
    rewrite <- (@fmap_comp _ _ G).
    rewrite iso_from_to, fmap_id, id_left.
    reflexivity. }
  rewrite (cmp_monad P x).
  rewrite <- comp_assoc.
  apply compose_respects; [ reflexivity | ].
  exact (@mh_ret _ _ _ _ _ (to θ) x).
Qed.

(* "Such a comparison is a morphism of adjunctions". *)
Definition Comparison_map : WeakMapOfAdjunctions Adj' Adj :=
  {| wmap_squares := Comparison_squares;
     wmap_hom := snd (weak_hom_iff_unit Adj' Adj Comparison_squares)
                   Comparison_unit |}.

Example Comparison_map_K :
  wsq_K (wmap_squares Adj' Adj Comparison_map) = M := eq_refl.

Example Comparison_map_L :
  wsq_L (wmap_squares Adj' Adj Comparison_map) = Id[X] := eq_refl.

(* "... and hence satisfies M ε' = ε M": Map.v's counit condition. *)
Theorem Comparison_counit : WeakSquaresCounit Adj' Adj Comparison_squares.
Proof.
  exact (fst (weak_hom_iff_counit Adj' Adj Comparison_squares)
           (wmap_hom Adj' Adj Comparison_map)).
Qed.

(* 相关说明。 （已译） *)
Theorem Comparison_counit_fused (a : A') :
  fmap[M] (@counit _ _ _ _ Adj' a)
    ≈ @counit _ _ _ _ Adj (M a) ∘ fmap[F] (from (be a)) ∘ to (al (G' a)).
Proof.
  pose proof (Comparison_counit a) as H; simpl in H.
  rewrite <- H.
  rewrite <- comp_assoc.
  rewrite iso_from_to.
  symmetry. apply id_right.
Qed.

(* 相关说明。 （已译） *)
Theorem Comparison_transpose (x : X) (a : A') (g : x ~> G' a) :
  fmap[M] (from (@adj _ _ _ _ Adj' x a) g) ∘ from (al x)
    ≈ from (@adj _ _ _ _ Adj x (M a)) (from (be a) ∘ g).
Proof.
  pose proof (wmap_hom Adj' Adj Comparison_map x a
                (from (@adj _ _ _ _ Adj' x a) g)) as H; simpl in H.
  apply (snd (adj_univ (H:=Adj) _ _)).
  rewrite H.
  apply compose_respects; [ reflexivity | ].
  apply (from_adj_comp_law (H:=Adj')).
Qed.

End Squares.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section Existence.

Context (CR : CreatesUSplitCoequalizers G).

Local Notation T := (Adjunction_Induced_Monad Adj).
Local Notation EMT := (@EilenbergMoore X (G ◯ F) T).
Local Notation th x := (transform[mh_transform (to θ)] x).
Local Notation ph x := (transform[mh_transform (from θ)] x).

(* 相关说明。 （已译） *)
Definition Comparison_alg : A' ⟶ EMT := mh_EM (from θ) ◯ EM_Comparison Adj'.

Example Comparison_alg_carrier (a : A') : `1 (Comparison_alg a) = G' a
  := eq_refl.

Example Comparison_alg_action (a : A') :
  t_alg[`2 (Comparison_alg a)] = fmap[G'] (@counit _ _ _ _ Adj' a) ∘ ph (G' a)
  := eq_refl.

(* 相关说明。 （已译） *)
Definition Comparison_functor : A' ⟶ A :=
  Beck_Inverse Adj CR ◯ Comparison_alg.

Example Comparison_functor_obj (a : A') :
  fobj[Comparison_functor] a = beck_G_obj Adj CR (Comparison_alg a) := eq_refl.

Definition Comparison_right_iso (a : A') : G (Comparison_functor a) ≅ G' a :=
  @Build_Isomorphism X (G (Comparison_functor a)) (G' a)
    (beck_to Adj CR (Comparison_alg a)) (beck_from Adj CR (Comparison_alg a))
    (beck_to_from Adj CR (Comparison_alg a))
    (beck_from_to Adj CR (Comparison_alg a)).

Definition Comparison_right : G ◯ Comparison_functor ≈ G'.
Proof.
  exists Comparison_right_iso.
  intros a b f.
  exact (beck_counit_coherence Adj CR (fmap[Comparison_alg] f)).
Defined.

Example Comparison_right_to (a : A') :
  to (`1 Comparison_right a) = beck_to Adj CR (Comparison_alg a) := eq_refl.

Example Comparison_right_from (a : A') :
  from (`1 Comparison_right a)
    = fmap[G] (beck_e Adj CR (Comparison_alg a)) ∘ @unit _ _ _ _ Adj (G' a)
  := eq_refl.

(* θ carries μ' to μ along T θ: θ_x ∘ μ'_x ∘ φ_{T' x} ≈ μ_x ∘ T θ_x. *)
Lemma cmp_theta_join (x : X) :
  th x ∘ (fmap[G'] (@counit _ _ _ _ Adj' (F' x)) ∘ ph (G' (F' x)))
    ≈ fmap[G] (@counit _ _ _ _ Adj (F x)) ∘ fmap[G] (fmap[F] (th x)).
Proof.
  rewrite comp_assoc.
  pose proof (@mh_join _ _ _ _ _ (to θ) x) as Hj; simpl in Hj.
  rewrite Hj; clear Hj.
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  pose proof (naturality (mh_transform (from θ)) _ _ (th x)) as Hn;
    simpl in Hn.
  rewrite Hn; clear Hn.
  rewrite comp_assoc.
  rewrite (cmp_theta_to_from (G (F x))).
  apply id_left.
Qed.

(* The arrow exhibits F x created 对象 at F' x. （已译） *)
Definition cmp_free_e (x : X) : F (G' (F' x)) ~> F x :=
  @counit _ _ _ _ Adj (F x) ∘ fmap[F] (th x).

Lemma cmp_free_e_cofork (x : X) :
  cmp_free_e x ∘ crude_pair_l Adj (Comparison_alg (F' x))
    ≈ cmp_free_e x ∘ crude_pair_r Adj (Comparison_alg (F' x)).
Proof.
  unfold cmp_free_e, crude_pair_l, crude_pair_r; simpl.
  rewrite <- !comp_assoc.
  rewrite <- (adj_counit_natural Adj (fmap[F] (th x))).
  rewrite <- (@fmap_comp _ _ F).
  pose proof (cmp_theta_join x) as Hj; simpl in Hj.
  rewrite Hj; clear Hj.
  rewrite (@fmap_comp _ _ F).
  rewrite !comp_assoc.
  apply compose_respects; [ | reflexivity ].
  rewrite (adj_counit_natural Adj (@counit _ _ _ _ Adj (F x))).
  reflexivity.
Qed.

Definition cmp_free_iso (x : X) : G (F x) ≅ G' (F' x) :=
  @Build_Isomorphism X (G (F x)) (G' (F' x)) (ph x) (th x)
    (cmp_theta_from_to x) (cmp_theta_to_from x).

Lemma cmp_free_iso_e (x : X) :
  to (cmp_free_iso x) ∘ fmap[G] (cmp_free_e x)
    ≈ scoeq_e (beck_split Adj (Comparison_alg (F' x))).
Proof.
  unfold cmp_free_e; simpl.
  rewrite (@fmap_comp _ _ G).
  pose proof (cmp_theta_join x) as Hj; simpl in Hj.
  rewrite <- Hj; clear Hj.
  rewrite comp_assoc.
  pose proof (cmp_theta_from_to x) as Hi; simpl in Hi.
  rewrite Hi; clear Hi.
  apply id_left.
Qed.

(* 相关说明。 （已译） *)
Definition Comparison_left_data (x : X) :=
  create_coeq_unique CR
    (crude_pair_l Adj (Comparison_alg (F' x)))
    (crude_pair_r Adj (Comparison_alg (F' x)))
    (beck_split Adj (Comparison_alg (F' x)))
    (beck_e Adj CR (Comparison_alg (F' x))) (cmp_free_e x)
    (beck_cofork Adj CR (Comparison_alg (F' x))) (cmp_free_e_cofork x)
    (beck_iso Adj CR (Comparison_alg (F' x)))
    (beck_iso_e Adj CR (Comparison_alg (F' x)))
    (cmp_free_iso x) (cmp_free_iso_e x).

Definition Comparison_left_iso (x : X) : Comparison_functor (F' x) ≅ F x :=
  `1 (Comparison_left_data x).

Lemma Comparison_left_iso_e (x : X) :
  to (Comparison_left_iso x) ∘ beck_e Adj CR (Comparison_alg (F' x))
    ≈ cmp_free_e x.
Proof. exact (`2 (Comparison_left_data x)). Qed.

Definition Comparison_left : Comparison_functor ◯ F' ≈ F.
Proof.
  exists Comparison_left_iso.
  intros x y f.
  apply (@epic _ _ _ _ (beck_e_epic Adj CR (Comparison_alg (F' x)))).
  change (beck_G_map Adj CR (fmap[Comparison_alg] (fmap[F'] f))
            ∘ beck_e Adj CR (Comparison_alg (F' x))
          ≈ from (Comparison_left_iso y) ∘ fmap[F] f
              ∘ to (Comparison_left_iso x)
              ∘ beck_e Adj CR (Comparison_alg (F' x))).
  rewrite (beck_G_map_commutes Adj CR
             (fmap[Comparison_alg] (fmap[F'] f))).
  rewrite <- (comp_assoc _ (to (Comparison_left_iso x))).
  rewrite Comparison_left_iso_e.
  unfold cmp_free_e.
  rewrite (comp_assoc _ (@counit _ _ _ _ Adj (F x))).
  rewrite <- (comp_assoc _ (fmap[F] f) (@counit _ _ _ _ Adj (F x))).
  rewrite <- (adj_counit_natural Adj (fmap[F] f)).
  rewrite !comp_assoc.
  rewrite <- (comp_assoc _ (fmap[F] (fmap[G] (fmap[F] f)))).
  rewrite <- (@fmap_comp _ _ F).
  pose proof (naturality (mh_transform (to θ)) _ _ f) as Hn; simpl in Hn.
  rewrite Hn; clear Hn.
  rewrite (@fmap_comp _ _ F).
  rewrite !comp_assoc.
  rewrite <- (comp_assoc _ (@counit _ _ _ _ Adj (F y))).
  change (@counit _ _ _ _ Adj (F y) ∘ fmap[F] (th y)) with (cmp_free_e y).
  rewrite <- Comparison_left_iso_e.
  rewrite !comp_assoc.
  rewrite iso_from_to, id_left.
  reflexivity.
Defined.

Lemma Comparison_coherence (x : X) :
  fmap[G] (to (`1 Comparison_left x)) ∘ from (`1 Comparison_right (F' x))
    ≈ th x.
Proof.
  change (fmap[G] (to (Comparison_left_iso x))
            ∘ (fmap[G] (beck_e Adj CR (Comparison_alg (F' x)))
                 ∘ @unit _ _ _ _ Adj (G' (F' x)))
          ≈ th x).
  rewrite comp_assoc.
  rewrite <- (@fmap_comp _ _ G).
  rewrite Comparison_left_iso_e.
  unfold cmp_free_e.
  rewrite (@fmap_comp _ _ G).
  rewrite <- comp_assoc.
  rewrite <- (adj_unit_natural Adj (th x)).
  rewrite comp_assoc.
  rewrite (@fmap_counit_unit _ _ _ _ Adj (F x)).
  apply id_left.
Qed.

Definition Comparison_exists : Comparison :=
  {| cmp_functor := Comparison_functor;
     cmp_left := Comparison_left;
     cmp_right := Comparison_right;
     cmp_monad := Comparison_coherence |}.

End Existence.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section Uniqueness.

Context (CR : CreatesUSplitCoequalizers G).
Context (P : Comparison).

Local Notation M0 := (cmp_functor P).
Local Notation al x := (`1 (cmp_left P) x).
Local Notation be a := (`1 (cmp_right P) a).
Local Notation th x := (transform[mh_transform (to θ)] x).
Local Notation ph x := (transform[mh_transform (from θ)] x).

(* Mac Lane's k = M ε'_a, read through α. *)
Definition cmp_e (a : A') : F (G' a) ~> M0 a :=
  fmap[M0] (@counit _ _ _ _ Adj' a) ∘ from (al (G' a)).

(* "... k must be M ε'_a = ε_{M a}", read through β. *)
Lemma cmp_e_counit (a : A') :
  cmp_e a ≈ @counit _ _ _ _ Adj (M0 a) ∘ fmap[F] (from (be a)).
Proof.
  unfold cmp_e.
  rewrite (Comparison_counit_fused P a).
  rewrite <- !comp_assoc.
  simpl.
  rewrite iso_to_from.
  rewrite id_right.
  reflexivity.
Qed.

Lemma cmp_e_G (a : A') :
  fmap[G] (cmp_e a)
    ≈ from (be a) ∘ (fmap[G'] (@counit _ _ _ _ Adj' a) ∘ ph (G' a)).
Proof.
  unfold cmp_e.
  rewrite (@fmap_comp _ _ G).
  pose proof (`2 (cmp_right P) _ _ (@counit _ _ _ _ Adj' a)) as Hn;
    simpl in Hn.
  simpl.
  rewrite Hn; clear Hn.
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  apply compose_respects; [ reflexivity | ].
  pose proof (cmp_monad_inv P (G' a)) as Hm; simpl in Hm.
  exact Hm.
Qed.

Lemma cmp_e_cofork (a : A') :
  cmp_e a ∘ crude_pair_l Adj (Comparison_alg a)
    ≈ cmp_e a ∘ crude_pair_r Adj (Comparison_alg a).
Proof.
  change (cmp_e a ∘ @counit _ _ _ _ Adj (F (G' a))
          ≈ cmp_e a ∘ fmap[F] (fmap[G'] (@counit _ _ _ _ Adj' a)
                                 ∘ ph (G' a))).
  rewrite !(cmp_e_counit a).
  rewrite <- !comp_assoc.
  rewrite <- (adj_counit_natural Adj (fmap[F] (from (be a)))).
  rewrite !comp_assoc.
  rewrite <- (adj_counit_natural Adj (@counit _ _ _ _ Adj (M0 a))).
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  rewrite <- !(@fmap_comp _ _ F).
  apply fmap_respects.
  rewrite <- (@fmap_comp _ _ G).
  rewrite <- (cmp_e_counit a).
  apply cmp_e_G.
Qed.

Lemma cmp_e_iso (a : A') :
  to (be a) ∘ fmap[G] (cmp_e a)
    ≈ scoeq_e (beck_split Adj (Comparison_alg a)).
Proof.
  rewrite (cmp_e_G a).
  rewrite !comp_assoc.
  simpl.
  rewrite iso_to_from.
  rewrite id_left.
  reflexivity.
Qed.

(* 相关说明。 （已译） *)
Definition cmp_e_coeq (a : A') :
  IsCoequalizer (crude_pair_l Adj (Comparison_alg a))
    (crude_pair_r Adj (Comparison_alg a)) (M0 a) (cmp_e a) :=
  @create_coeq_reflects A X G CR _ _
    (crude_pair_l Adj (Comparison_alg a))
    (crude_pair_r Adj (Comparison_alg a))
    (beck_split Adj (Comparison_alg a)) (M0 a) (cmp_e a)
    (cmp_e_cofork a) (be a) (cmp_e_iso a).

Definition cmp_unique_data (a : A') :=
  create_coeq_unique CR
    (crude_pair_l Adj (Comparison_alg a))
    (crude_pair_r Adj (Comparison_alg a))
    (beck_split Adj (Comparison_alg a))
    (cmp_e a) (beck_e Adj CR (Comparison_alg a))
    (cmp_e_cofork a) (beck_cofork Adj CR (Comparison_alg a))
    (be a) (cmp_e_iso a)
    (beck_iso Adj CR (Comparison_alg a))
    (beck_iso_e Adj CR (Comparison_alg a)).

Definition cmp_unique_iso (a : A') : M0 a ≅ Comparison_functor CR a :=
  `1 (cmp_unique_data a).

Lemma cmp_unique_iso_e (a : A') :
  to (cmp_unique_iso a) ∘ cmp_e a ≈ beck_e Adj CR (Comparison_alg a).
Proof. exact (`2 (cmp_unique_data a)). Qed.

Lemma cmp_e_natural {a b : A'} (f : a ~> b) :
  fmap[M0] f ∘ cmp_e a ≈ cmp_e b ∘ fmap[F] (fmap[G'] f).
Proof.
  unfold cmp_e.
  rewrite !comp_assoc.
  rewrite <- (@fmap_comp _ _ M0).
  rewrite <- (adj_counit_natural Adj' f).
  rewrite (@fmap_comp _ _ M0).
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  pose proof (`2 (cmp_left P) _ _ (fmap[G'] f)) as Hn; simpl in Hn.
  simpl.
  rewrite Hn; clear Hn.
  rewrite <- !comp_assoc.
  rewrite iso_to_from.
  rewrite id_right.
  reflexivity.
Qed.

(* The isomorphisms natural, 自然性 Mac Lane's k. （已译） *)
Lemma cmp_unique_iso_natural {a b : A'} (f : a ~> b) :
  fmap[M0] f
    ≈ from (cmp_unique_iso b) ∘ fmap[Comparison_functor CR] f
        ∘ to (cmp_unique_iso a).
Proof.
  apply (@epic _ _ _ _ (coequalizer_epic _ _ (cmp_e_coeq a))).
  rewrite (cmp_e_natural f).
  change (cmp_e b ∘ fmap[F] (fmap[G'] f)
          ≈ from (cmp_unique_iso b)
              ∘ beck_G_map Adj CR (fmap[Comparison_alg] f)
              ∘ to (cmp_unique_iso a) ∘ cmp_e a).
  rewrite <- (comp_assoc _ (to (cmp_unique_iso a))).
  rewrite cmp_unique_iso_e.
  rewrite <- comp_assoc.
  rewrite (beck_G_map_commutes Adj CR (fmap[Comparison_alg] f)).
  rewrite comp_assoc.
  rewrite <- cmp_unique_iso_e.
  rewrite !comp_assoc.
  rewrite iso_from_to, id_left.
  reflexivity.
Qed.

Theorem Comparison_unique_to : M0 ≈ Comparison_functor CR.
Proof.
  exists cmp_unique_iso.
  intros a b f.
  exact (cmp_unique_iso_natural f).
Qed.

End Uniqueness.

(* ------------------------------------------------------------------------ *)
(* * ** The 同构 态射 comparisons, one （已译） *)

Section Cell.

Context (CR : CreatesUSplitCoequalizers G).
Context (P : Comparison).

Local Notation M0 := (cmp_functor P).
Local Notation al x := (`1 (cmp_left P) x).
Local Notation be a := (`1 (cmp_right P) a).
Local Notation ph x := (transform[mh_transform (from θ)] x).

(* The algebra's unit law makes G (cmp_e a) a split epimorphism. *)
Lemma cmp_e_G_split (a : A') :
  fmap[G] (cmp_e P a) ∘ (@unit _ _ _ _ Adj (G' a) ∘ to (be a)) ≈ id.
Proof.
  rewrite (cmp_e_G P a).
  transitivity (from (be a)
                  ∘ ((fmap[G'] (@counit _ _ _ _ Adj' a) ∘ ph (G' a))
                       ∘ @unit _ _ _ _ Adj (G' a)) ∘ to (be a)).
  { rewrite !comp_assoc. reflexivity. }
  pose proof (@t_id X (G ◯ F) (Adjunction_Induced_Monad Adj) (G' a)
                (`2 (Comparison_alg a))) as Hu; simpl in Hu.
  simpl.
  rewrite Hu; clear Hu.
  rewrite id_right.
  apply iso_from_to.
Qed.

Lemma Comparison_unique_to_right (a : A') :
  to (`1 (Comparison_right CR) a) ∘ fmap[G] (to (cmp_unique_iso CR P a))
    ≈ to (be a).
Proof.
  rewrite <- (id_right (to (`1 (Comparison_right CR) a)
                          ∘ fmap[G] (to (cmp_unique_iso CR P a)))).
  rewrite <- (cmp_e_G_split a).
  rewrite !comp_assoc.
  rewrite <- (comp_assoc _ (fmap[G] (to (cmp_unique_iso CR P a)))).
  rewrite <- (@fmap_comp _ _ G).
  rewrite (cmp_unique_iso_e CR P a).
  change (beck_to Adj CR (Comparison_alg a)
            ∘ fmap[G] (beck_e Adj CR (Comparison_alg a))
            ∘ @unit _ _ _ _ Adj (G' a) ∘ to (be a) ≈ to (be a)).
  rewrite (beck_to_e Adj CR (Comparison_alg a)).
  pose proof (@t_id X (G ◯ F) (Adjunction_Induced_Monad Adj) (G' a)
                (`2 (Comparison_alg a))) as Hu; simpl in Hu.
  simpl.
  rewrite Hu; clear Hu.
  apply id_left.
Qed.

Lemma Comparison_unique_to_left (x : X) :
  to (`1 (Comparison_left CR) x) ∘ to (cmp_unique_iso CR P (F' x))
    ≈ to (al x).
Proof.
  apply (@epic _ _ _ _ (coequalizer_epic _ _ (cmp_e_coeq CR P (F' x)))).
  rewrite <- comp_assoc.
  rewrite (cmp_unique_iso_e CR P (F' x)).
  rewrite (Comparison_left_iso_e CR x).
  rewrite (cmp_e_counit P (F' x)).
  rewrite comp_assoc.
  simpl.
  rewrite <- (adj_counit_natural Adj (to (al x))).
  rewrite <- comp_assoc.
  rewrite <- (@fmap_comp _ _ F).
  unfold cmp_free_e.
  apply compose_respects; [ reflexivity | ].
  apply fmap_respects.
  symmetry.
  pose proof (cmp_monad P x) as Hm; simpl in Hm.
  exact Hm.
Qed.

(* 相关说明。 （已译） *)
Lemma Comparison_exists_e (a : A') :
  cmp_e (Comparison_exists CR) a ≈ beck_e Adj CR (Comparison_alg a).
Proof.
  rewrite (cmp_e_counit (Comparison_exists CR) a).
  change (@counit _ _ _ _ Adj (Comparison_functor CR a)
            ∘ fmap[F] (fmap[G] (beck_e Adj CR (Comparison_alg a))
                         ∘ @unit _ _ _ _ Adj (G' a))
          ≈ beck_e Adj CR (Comparison_alg a)).
  rewrite (@fmap_comp _ _ F).
  rewrite comp_assoc.
  rewrite (adj_counit_natural Adj (beck_e Adj CR (Comparison_alg a))).
  rewrite <- comp_assoc.
  rewrite (@counit_fmap_unit _ _ _ _ Adj (G' a)).
  apply id_right.
Qed.

Theorem Comparison_unique_cell
  (k : ∀ a : A', M0 a ~> Comparison_functor CR a)
  (Hk : ∀ (a b : A') (f : a ~> b),
     fmap[Comparison_functor CR] f ∘ k a ≈ k b ∘ fmap[M0] f)
  (Hl : ∀ x : X, to (`1 (Comparison_left CR) x) ∘ k (F' x) ≈ to (al x))
  (a : A') : k a ≈ to (cmp_unique_iso CR P a).
Proof.
  apply (@epic _ _ _ _ (coequalizer_epic _ _ (cmp_e_coeq CR P a))).
  rewrite (cmp_unique_iso_e CR P a).
  rewrite <- (Comparison_exists_e a).
  unfold cmp_e.
  transitivity ((k a ∘ fmap[M0] (@counit _ _ _ _ Adj' a))
                  ∘ from (al (G' a))).
  { apply comp_assoc. }
  transitivity ((fmap[Comparison_functor CR] (@counit _ _ _ _ Adj' a)
                   ∘ k (F' (G' a))) ∘ from (al (G' a))).
  { apply compose_respects; [ symmetry; apply Hk | reflexivity ]. }
  transitivity (fmap[Comparison_functor CR] (@counit _ _ _ _ Adj' a)
                  ∘ (k (F' (G' a)) ∘ from (al (G' a)))).
  { apply comp_assoc_sym. }
  apply compose_respects; [ reflexivity | ].
  transitivity ((from (Comparison_left_iso CR (G' a))
                   ∘ (to (Comparison_left_iso CR (G' a)) ∘ k (F' (G' a))))
                  ∘ from (al (G' a))).
  { apply compose_respects; [ | reflexivity ].
    rewrite comp_assoc, iso_from_to, id_left. reflexivity. }
  transitivity ((from (Comparison_left_iso CR (G' a)) ∘ to (al (G' a)))
                  ∘ from (al (G' a))).
  { apply compose_respects; [ | reflexivity ].
    apply compose_respects; [ reflexivity | apply Hl ]. }
  rewrite <- comp_assoc.
  simpl.
  rewrite iso_to_from.
  apply id_right.
Qed.

End Cell.

(* 相关说明。 （已译） *)
Theorem Comparison_unique (CR : CreatesUSplitCoequalizers G)
  (P Q : Comparison) : cmp_functor P ≈ cmp_functor Q.
Proof.
  transitivity (Comparison_functor CR).
  - apply Comparison_unique_to.
  - symmetry. apply Comparison_unique_to.
Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Comparison_unique_pair_left (CR : CreatesUSplitCoequalizers G)
  (P Q : Comparison) (x : X) :
  to (`1 (cmp_left Q) x)
    ∘ (from (cmp_unique_iso CR Q (F' x)) ∘ to (cmp_unique_iso CR P (F' x)))
    ≈ to (`1 (cmp_left P) x).
Proof.
  rewrite <- (Comparison_unique_to_left CR Q x).
  rewrite <- (Comparison_unique_to_left CR P x).
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  rewrite comp_assoc.
  rewrite iso_to_from, id_left.
  reflexivity.
Qed.

(* 相关说明。 （已译） *)
Theorem Comparison_unique_pair_cell (CR : CreatesUSplitCoequalizers G)
  (P Q : Comparison)
  (k : ∀ a : A', cmp_functor P a ~> cmp_functor Q a)
  (Hk : ∀ (a b : A') (f : a ~> b),
     fmap[cmp_functor Q] f ∘ k a ≈ k b ∘ fmap[cmp_functor P] f)
  (Hl : ∀ x : X,
     to (`1 (cmp_left Q) x) ∘ k (F' x) ≈ to (`1 (cmp_left P) x))
  (a : A') :
  k a ≈ from (cmp_unique_iso CR Q a) ∘ to (cmp_unique_iso CR P a).
Proof.
  enough (H : to (cmp_unique_iso CR Q a) ∘ k a
                ≈ to (cmp_unique_iso CR P a)).
  { rewrite <- H. rewrite comp_assoc, iso_from_to, id_left. reflexivity. }
  apply (@epic _ _ _ _ (coequalizer_epic _ _ (cmp_e_coeq CR P a))).
  rewrite (cmp_unique_iso_e CR P a).
  rewrite <- (cmp_unique_iso_e CR Q a).
  unfold cmp_e.
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  rewrite comp_assoc.
  rewrite <- (Hk _ _ (@counit _ _ _ _ Adj' a)).
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  rewrite <- (id_left (k (F' (G' a)))).
  rewrite <- (iso_from_to (`1 (cmp_left Q) (G' a))).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (to (`1 (cmp_left Q) (G' a)))).
  rewrite (Hl (G' a)).
  rewrite iso_to_from, id_right.
  reflexivity.
Qed.

End ComparisonDef.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section EMResolution.

Universes m1 m2.

Context {X : Category} (T : X ⟶ X) `{H : @Monad X T}.

Local Notation TE := (Adjunction_Induced_Monad (@EM_Adjunction X T H)).

(* F^T ⊣ G^T defines T: unit id ∘ η multiplication
 μ ∘ T id, so 恒等 components 态射 单子 each
 way. （已译） *)

Definition EM_Monad_to : MonadHom TE H.
Proof.
  unshelve refine
    {| mh_transform :=
         Build_Transform' (F:=EM_Forget T ◯ EM_Free T) (G:=T)
           (fun x => id) _ |}.
  - intros x y f; simpl. rewrite id_left, id_right. reflexivity.
  - intros x; simpl. rewrite id_left. exact (@EM_unit_agrees X T H x).
  - intros x; simpl.
    rewrite id_left.
    rewrite (@EM_join_agrees X T H x).
    rewrite fmap_id, !id_right.
    reflexivity.
Defined.

Definition EM_Monad_from : MonadHom H TE.
Proof.
  unshelve refine
    {| mh_transform :=
         Build_Transform' (F:=T) (G:=EM_Forget T ◯ EM_Free T)
           (fun x => id) _ |}.
  - intros x y f; simpl. rewrite id_left, id_right. reflexivity.
  - intros x; simpl. rewrite id_left. symmetry.
    exact (@EM_unit_agrees X T H x).
  - intros x; simpl.
    rewrite id_left.
    rewrite (@EM_join_agrees X T H x).
    rewrite fmap_id, !id_right.
    reflexivity.
Defined.

Definition EM_Monad_iso :
  @Isomorphism (Monads@{_ _ m1 m2} X) (EM_Forget T ◯ EM_Free T; TE) (T; H).
Proof.
  unshelve refine (@Build_Isomorphism (Monads@{_ _ m1 m2} X)
                     (EM_Forget T ◯ EM_Free T; TE) (T; H)
                     EM_Monad_to EM_Monad_from _ _).
  - intros x; simpl. apply id_left.
  - intros x; simpl. apply id_left.
Defined.

Example EM_Monad_iso_to (x : X) :
  transform[mh_transform (to EM_Monad_iso)] x = id := eq_refl.

Example EM_Monad_iso_from (x : X) :
  transform[mh_transform (from EM_Monad_iso)] x = id := eq_refl.

Section Terminal.

Context {A' : Category} {F' : X ⟶ A'} {G' : A' ⟶ X} (Adj' : F' ⊣ G').
Context (θ' : @Isomorphism (Monads@{_ _ m1 m2} X)
                (G' ◯ F'; Adjunction_Induced_Monad Adj') (T; H)).

Definition EM_terminal_theta :
  @Isomorphism (Monads@{_ _ m1 m2} X)
    (G' ◯ F'; Adjunction_Induced_Monad Adj')
    (EM_Forget T ◯ EM_Free T; TE) :=
  iso_compose (iso_sym EM_Monad_iso) θ'.

Definition EM_terminal :
  Comparison (@EM_Adjunction X T H) Adj' EM_terminal_theta :=
  Comparison_exists (@EM_Adjunction X T H) Adj' EM_terminal_theta
    (@monadic_creates X T H).

Theorem EM_terminal_unique
  (P Q : Comparison (@EM_Adjunction X T H) Adj' EM_terminal_theta) :
  cmp_functor _ _ _ P ≈ cmp_functor _ _ _ Q.
Proof.
  exact (Comparison_unique (@EM_Adjunction X T H) Adj' EM_terminal_theta
           (@monadic_creates X T H) P Q).
Qed.

End Terminal.

End EMResolution.

(* ------------------------------------------------------------------------ *)
(*
   本节说明单子、同构、Eilenberg–Moore相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section EMComparison.

Universes m1 m2.

Context {X A : Category} {F : X ⟶ A} {G : A ⟶ X} (Adj : F ⊣ G).

Local Notation T := (Adjunction_Induced_Monad Adj).
Local Notation EMAdj := (@EM_Adjunction X (G ◯ F) T).

Definition EM_Comparison_theta :
  @Isomorphism (Monads@{_ _ m1 m2} X) (G ◯ F; T)
    (EM_Forget (G ◯ F) ◯ EM_Free (G ◯ F); Adjunction_Induced_Monad EMAdj) :=
  iso_sym (@EM_Monad_iso X (G ◯ F) T).

Example EM_Comparison_theta_to (x : X) :
  transform[mh_transform (to EM_Comparison_theta)] x = id := eq_refl.

(* 相关说明。 （已译） *)
Example EM_Comparison_Forget_components (a : A) :
  `1 (EM_Comparison_Forget Adj) a = iso_id := eq_refl.

Example EM_Comparison_Free_components (x : X) :
  `1 (EM_Comparison_Free Adj) x = EM_Comparison_Free_iso Adj x := eq_refl.

Lemma EM_Comparison_coherence (x : X) :
  fmap[EM_Forget (G ◯ F)] (to (`1 (EM_Comparison_Free Adj) x))
    ∘ from (`1 (EM_Comparison_Forget Adj) (F x))
    ≈ transform[mh_transform (to EM_Comparison_theta)] x.
Proof. simpl. apply id_left. Qed.

Definition EM_Comparison_Comparison :
  Comparison EMAdj Adj EM_Comparison_theta :=
  {| cmp_functor := EM_Comparison Adj;
     cmp_left := EM_Comparison_Free Adj;
     cmp_right := EM_Comparison_Forget Adj;
     cmp_monad := EM_Comparison_coherence |}.

(*
   本节说明函子、单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem EM_Comparison_unique
  (P : Comparison EMAdj Adj EM_Comparison_theta) :
  cmp_functor _ _ _ P ≈ EM_Comparison Adj.
Proof.
  exact (Comparison_unique EMAdj Adj EM_Comparison_theta
           (@monadic_creates X (G ◯ F) T) P EM_Comparison_Comparison).
Qed.

(* ... up unique compatible 同构: 复合 two
 isomorphisms constructed comparison natural family
 commuting left triangles. （已译） *)
Theorem EM_Comparison_unique_cell
  (P : Comparison EMAdj Adj EM_Comparison_theta)
  (k : ∀ a : A, cmp_functor _ _ _ P a ~> EM_Comparison Adj a)
  (Hk : ∀ (a b : A) (f : a ~> b),
     fmap[EM_Comparison Adj] f ∘ k a ≈ k b ∘ fmap[cmp_functor _ _ _ P] f)
  (Hl : ∀ x : X,
     to (`1 (EM_Comparison_Free Adj) x) ∘ k (F x)
       ≈ to (`1 (cmp_left _ _ _ P) x))
  (a : A) :
  k a ≈ from (cmp_unique_iso EMAdj Adj EM_Comparison_theta
                (@monadic_creates X (G ◯ F) T) EM_Comparison_Comparison a)
          ∘ to (cmp_unique_iso EMAdj Adj EM_Comparison_theta
                  (@monadic_creates X (G ◯ F) T) P a).
Proof.
  exact (Comparison_unique_pair_cell EMAdj Adj EM_Comparison_theta
           (@monadic_creates X (G ◯ F) T) P EM_Comparison_Comparison
           k Hk Hl a).
Qed.

(* Mac Lane: Lemma at Eilenberg–Moore resolution "will incidentally
 provide new 证明 comparison 定理". （已译） *)
Definition EM_Comparison_via_Lemma : A ⟶ @EilenbergMoore X (G ◯ F) T :=
  Comparison_functor EMAdj Adj EM_Comparison_theta
    (@monadic_creates X (G ◯ F) T).

Theorem EM_Comparison_via_Lemma_agrees :
  EM_Comparison Adj ≈ EM_Comparison_via_Lemma.
Proof.
  exact (Comparison_unique_to EMAdj Adj EM_Comparison_theta
           (@monadic_creates X (G ◯ F) T) EM_Comparison_Comparison).
Qed.

End EMComparison.
