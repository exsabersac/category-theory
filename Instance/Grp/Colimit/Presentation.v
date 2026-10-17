Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Product.
Require Import Category.Functor.Diagonal.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Coequalizer.
Require Import Category.Adjunction.Diagonal.Coproduct.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cocartesian.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.
Require Import Category.Instance.Grp.Pushout.
Require Import Category.Instance.Grp.Colimit.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/monadic+adjunction
 nLab:      https://ncatlab.org/nlab/show/coequalizer
 Wikipedia: https://en.wikipedia.org/wiki/Free_product

   本文件给出余极限实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Lemma Grp_free_hom_ext {X : Sets} {K : Grp} (g1 g2 : FreeGrp X ~{Grp}~> K) :
  (∀ a, g1 (fg_insert X a) ≈ g2 (fg_insert X a)) → g1 ≈ g2.
Proof.
  intros Hg w.
  transitivity (free_grp_extend (fmap[Grp_Forget] g2 ∘ fg_insert X) w).
  - exact (free_grp_extend_unique X K
             (fmap[Grp_Forget] g2 ∘ fg_insert X) g1 Hg w).
  - symmetry.
    apply (free_grp_extend_unique X K _ g2).
    intro a; reflexivity.
Qed.

(* 相关说明。 （已译） *)

Section Canonical.

Context (G : Grp).

Lemma Grp_canonical_cofork :
  free_group_counit G ∘ free_group_counit (FreeGrp (Grp_Forget G))
    ≈ free_group_counit G
        ∘ fmap[FreeGrp] (fmap[Grp_Forget] (free_group_counit G)).
Proof.
  symmetry.
  exact (@counit_comp _ _ _ _ free_group_adjunction _ _ (free_group_counit G)).
Qed.

Context {c : Grp} (k : FreeGrp (Grp_Forget G) ~{Grp}~> c).
Context (Hk : k ∘ free_group_counit (FreeGrp (Grp_Forget G))
                ≈ k ∘ fmap[FreeGrp] (fmap[Grp_Forget] (free_group_counit G))).

Definition Grp_canonical_desc : G ~{Grp}~> c.
Proof using Hk.
  unshelve refine (@Build_GrpHom' G c
                     (fmap[Grp_Forget] k ∘ fg_insert (Grp_Forget G)) _).
  intros g g'; simpl.
  set (w := grp_mul (FreeGrpObject (Grp_Forget G))
              (fg_insert (Grp_Forget G) g) (fg_insert (Grp_Forget G) g')).
  rewrite <- (grp_map_mul k).
  fold w.
  transitivity (grp_map k (free_group_counit (FreeGrp (Grp_Forget G))
                  (fg_insert (Grp_Forget (FreeGrp (Grp_Forget G))) w))).
  2: { apply (proper_morphism (grp_map k)).
       exact (free_group_counit_generator (FreeGrp (Grp_Forget G)) w). }
  transitivity (grp_map k
                  (fmap[FreeGrp] (fmap[Grp_Forget] (free_group_counit G))
                     (fg_insert (Grp_Forget (FreeGrp (Grp_Forget G))) w))).
  2: { symmetry. exact (Hk _). }
  apply (proper_morphism (grp_map k)).
  rewrite free_group_fmap_generators.
  apply (proper_morphism (fg_insert (Grp_Forget G))).
  simpl.
  unfold w.
  rewrite (grp_map_mul (free_group_counit G)).
  rewrite !free_group_counit_generator.
  reflexivity.
Defined.

Lemma Grp_canonical_desc_commutes :
  Grp_canonical_desc ∘ free_group_counit G ≈ k.
Proof.
  apply Grp_free_hom_ext; intro a; simpl.
  apply (proper_morphism (grp_map k)).
  apply (proper_morphism (fg_insert (Grp_Forget G))).
  exact (free_group_counit_generator G a).
Qed.

Lemma Grp_canonical_desc_unique (v : G ~{Grp}~> c) :
  v ∘ free_group_counit G ≈ k → Grp_canonical_desc ≈ v.
Proof.
  intros Hv g; simpl.
  rewrite <- (Hv (fg_insert (Grp_Forget G) g)); simpl.
  apply (proper_morphism (grp_map v)).
  exact (free_group_counit_generator G g).
Qed.

End Canonical.

Definition Grp_canonical_presentation (G : Grp) :
  IsCoequalizer (free_group_counit (FreeGrp (Grp_Forget G)))
                (fmap[FreeGrp] (fmap[Grp_Forget] (free_group_counit G)))
                G (free_group_counit G).
Proof.
  unshelve econstructor.
  - exact (Grp_canonical_cofork G).
  - intros c k Hk.
    exact {| unique_obj      := Grp_canonical_desc G k Hk;
             unique_property := Grp_canonical_desc_commutes G k Hk;
             uniqueness      := Grp_canonical_desc_unique G k Hk |}.
Defined.

(** ** Riehl's parallel pair *)

Section RiehlPair.

Universes u p.
Context (G H : Grp@{u p}).

Local Notation UGH :=
  (@Coprod Sets Sets_Cocartesian (Grp_Forget G) (Grp_Forget H)).
Local Notation UFUGH :=
  (@Coprod Sets Sets_Cocartesian (Grp_Forget (FreeGrp (Grp_Forget G)))
                                 (Grp_Forget (FreeGrp (Grp_Forget H)))).
Local Notation inlS :=
  (@inl Sets Sets_Cocartesian (Grp_Forget G) (Grp_Forget H)).
Local Notation inrS :=
  (@inr Sets Sets_Cocartesian (Grp_Forget G) (Grp_Forget H)).

(* 相关说明。 （已译） *)
Definition Grp_riehl_comparison :
  UFUGH ~{Sets}~> Grp_Forget (FreeGrp UGH) :=
  @merge Sets Sets_Cocartesian _ _ _
    (fmap[Grp_Forget] (fmap[FreeGrp] inlS))
    (fmap[Grp_Forget] (fmap[FreeGrp] inrS)).

(* The leg F(Uε_G + Uε_H). *)
Definition Grp_riehl_l : FreeGrp UFUGH ~{Grp@{u p}}~> FreeGrp UGH :=
  fmap[FreeGrp] (@cover Sets Sets_Cocartesian _ _ _ _
                   (fmap[Grp_Forget] (free_group_counit G))
                   (fmap[Grp_Forget] (free_group_counit H))).

(* The leg ε_{F(UG+UH)} ∘ F[UF inl, UF inr]. *)
Definition Grp_riehl_r : FreeGrp UFUGH ~{Grp@{u p}}~> FreeGrp UGH :=
  free_group_counit (FreeGrp UGH) ∘ fmap[FreeGrp] Grp_riehl_comparison.

(* The transpose, across free-forgetful 伴随, copairing in
 [Sets] underlying maps two homomorphisms out G H. （已译） *)
Definition Grp_riehl_transpose {z : Grp@{u p}}
  (f1 : G ~{Grp@{u p}}~> z) (f2 : H ~{Grp@{u p}}~> z) :
  FreeGrp UGH ~{Grp@{u p}}~> z :=
  from (@adj _ _ _ _ free_group_adjunction _ _)
    (@merge Sets Sets_Cocartesian _ _ _ (fmap[Grp_Forget] f1)
                                        (fmap[Grp_Forget] f2)).

(* 相关说明。 （已译） *)
Definition Grp_riehl_e (CC : @Cocartesian Grp@{u p}) :
  FreeGrp UGH ~{Grp@{u p}}~> @Coprod Grp@{u p} CC G H :=
  Grp_riehl_transpose (@inl Grp@{u p} CC G H) (@inr Grp@{u p} CC G H).

(** *** What the maps do to a letter *)

Lemma Grp_riehl_transpose_generator {z : Grp@{u p}}
  (f1 : G ~{Grp@{u p}}~> z) (f2 : H ~{Grp@{u p}}~> z) (s : UGH) :
  Grp_riehl_transpose f1 f2 (fg_insert UGH s)
    ≈ @merge Sets Sets_Cocartesian _ _ _ (fmap[Grp_Forget] f1)
                                         (fmap[Grp_Forget] f2) s.
Proof.
  pose proof (@from_adj_comp_law _ _ _ _ free_group_adjunction _ _
                (@merge Sets Sets_Cocartesian _ _ _ (fmap[Grp_Forget] f1)
                                                    (fmap[Grp_Forget] f2)))
    as Hc.
  rewrite (@to_adj_unit _ _ _ _ free_group_adjunction) in Hc.
  exact (Hc s).
Qed.

Lemma Grp_riehl_l_inl (w : FGWord (Grp_Forget G)) :
  Grp_riehl_l (fg_insert UFUGH (Datatypes.inl w))
    ≈ fg_insert UGH (Datatypes.inl (free_group_counit G w)).
Proof. exact (@free_group_fmap_generators UFUGH UGH _ (Datatypes.inl w)). Qed.

Lemma Grp_riehl_l_inr (w : FGWord (Grp_Forget H)) :
  Grp_riehl_l (fg_insert UFUGH (Datatypes.inr w))
    ≈ fg_insert UGH (Datatypes.inr (free_group_counit H w)).
Proof. exact (@free_group_fmap_generators UFUGH UGH _ (Datatypes.inr w)). Qed.

Lemma Grp_riehl_r_inl (w : FGWord (Grp_Forget G)) :
  Grp_riehl_r (fg_insert UFUGH (Datatypes.inl w)) ≈ fmap[FreeGrp] inlS w.
Proof.
  transitivity (free_group_counit (FreeGrp UGH)
                  (fg_insert _ (Grp_riehl_comparison (Datatypes.inl w)))).
  - apply (proper_morphism (grp_map (free_group_counit (FreeGrp UGH)))).
    exact (@free_group_fmap_generators UFUGH _ Grp_riehl_comparison
             (Datatypes.inl w)).
  - exact (free_group_counit_generator (FreeGrp UGH) _).
Qed.

Lemma Grp_riehl_r_inr (w : FGWord (Grp_Forget H)) :
  Grp_riehl_r (fg_insert UFUGH (Datatypes.inr w)) ≈ fmap[FreeGrp] inrS w.
Proof.
  transitivity (free_group_counit (FreeGrp UGH)
                  (fg_insert _ (Grp_riehl_comparison (Datatypes.inr w)))).
  - apply (proper_morphism (grp_map (free_group_counit (FreeGrp UGH)))).
    exact (@free_group_fmap_generators UFUGH _ Grp_riehl_comparison
             (Datatypes.inr w)).
  - exact (free_group_counit_generator (FreeGrp UGH) _).
Qed.

(* 相关说明。 （已译） *)

Section Transpose.

Context {z : Grp@{u p}} (f1 : G ~{Grp@{u p}}~> z) (f2 : H ~{Grp@{u p}}~> z).

Lemma Grp_riehl_transpose_inl :
  Grp_riehl_transpose f1 f2 ∘ fmap[FreeGrp] inlS ≈ f1 ∘ free_group_counit G.
Proof.
  apply Grp_free_hom_ext; intro g.
  transitivity (Grp_riehl_transpose f1 f2 (fg_insert UGH (Datatypes.inl g))).
  - apply (proper_morphism (grp_map (Grp_riehl_transpose f1 f2))).
    exact (@free_group_fmap_generators _ UGH _ g).
  - rewrite (Grp_riehl_transpose_generator f1 f2 (Datatypes.inl g)).
    symmetry.
    apply (proper_morphism (grp_map f1)).
    exact (free_group_counit_generator G g).
Qed.

Lemma Grp_riehl_transpose_inr :
  Grp_riehl_transpose f1 f2 ∘ fmap[FreeGrp] inrS ≈ f2 ∘ free_group_counit H.
Proof.
  apply Grp_free_hom_ext; intro g.
  transitivity (Grp_riehl_transpose f1 f2 (fg_insert UGH (Datatypes.inr g))).
  - apply (proper_morphism (grp_map (Grp_riehl_transpose f1 f2))).
    exact (@free_group_fmap_generators _ UGH _ g).
  - rewrite (Grp_riehl_transpose_generator f1 f2 (Datatypes.inr g)).
    symmetry.
    apply (proper_morphism (grp_map f2)).
    exact (free_group_counit_generator H g).
Qed.

(* 相关说明。 （已译） *)
Lemma Grp_riehl_transpose_cofork :
  Grp_riehl_transpose f1 f2 ∘ Grp_riehl_l
    ≈ Grp_riehl_transpose f1 f2 ∘ Grp_riehl_r.
Proof.
  apply Grp_free_hom_ext; intros [w|w].
  - transitivity (Grp_riehl_transpose f1 f2
                    (fg_insert UGH (Datatypes.inl (free_group_counit G w)))).
    { apply (proper_morphism (grp_map (Grp_riehl_transpose f1 f2))).
      exact (Grp_riehl_l_inl w). }
    rewrite (Grp_riehl_transpose_generator f1 f2).
    transitivity (Grp_riehl_transpose f1 f2 (fmap[FreeGrp] inlS w)).
    { symmetry. exact (Grp_riehl_transpose_inl w). }
    apply (proper_morphism (grp_map (Grp_riehl_transpose f1 f2))).
    symmetry. exact (Grp_riehl_r_inl w).
  - transitivity (Grp_riehl_transpose f1 f2
                    (fg_insert UGH (Datatypes.inr (free_group_counit H w)))).
    { apply (proper_morphism (grp_map (Grp_riehl_transpose f1 f2))).
      exact (Grp_riehl_l_inr w). }
    rewrite (Grp_riehl_transpose_generator f1 f2).
    transitivity (Grp_riehl_transpose f1 f2 (fmap[FreeGrp] inrS w)).
    { symmetry. exact (Grp_riehl_transpose_inr w). }
    apply (proper_morphism (grp_map (Grp_riehl_transpose f1 f2))).
    symmetry. exact (Grp_riehl_r_inr w).
Qed.

End Transpose.

(* 相关说明。 （已译） *)

Section Factors.

Context {c : Grp@{u p}} (k : FreeGrp UGH ~{Grp@{u p}}~> c).
Context (Hk : k ∘ Grp_riehl_l ≈ k ∘ Grp_riehl_r).

(* 相关说明。 （已译） *)
Definition Grp_riehl_kG : FreeGrp (Grp_Forget G) ~{Grp@{u p}}~> c :=
  k ∘ fmap[FreeGrp] inlS.

Definition Grp_riehl_kH : FreeGrp (Grp_Forget H) ~{Grp@{u p}}~> c :=
  k ∘ fmap[FreeGrp] inrS.

(* Each restriction coforks that factor's canonical presentation. *)
Lemma Grp_riehl_kG_cofork :
  Grp_riehl_kG ∘ free_group_counit (FreeGrp (Grp_Forget G))
    ≈ Grp_riehl_kG ∘ fmap[FreeGrp] (fmap[Grp_Forget] (free_group_counit G)).
Proof using Hk.
  apply Grp_free_hom_ext; intro w.
  transitivity (k (fmap[FreeGrp] inlS w)).
  { apply (proper_morphism (grp_map Grp_riehl_kG)).
    exact (free_group_counit_generator (FreeGrp (Grp_Forget G)) w). }
  transitivity (k (Grp_riehl_r (fg_insert UFUGH (Datatypes.inl w)))).
  { apply (proper_morphism (grp_map k)).
    symmetry. exact (Grp_riehl_r_inl w). }
  transitivity (k (Grp_riehl_l (fg_insert UFUGH (Datatypes.inl w)))).
  { symmetry. exact (Hk _). }
  transitivity (k (fg_insert UGH (Datatypes.inl (free_group_counit G w)))).
  { apply (proper_morphism (grp_map k)).
    exact (Grp_riehl_l_inl w). }
  transitivity (Grp_riehl_kG
                  (fg_insert (Grp_Forget G) (free_group_counit G w))).
  { apply (proper_morphism (grp_map k)).
    symmetry. exact (@free_group_fmap_generators _ UGH _ _). }
  apply (proper_morphism (grp_map Grp_riehl_kG)).
  symmetry.
  exact (@free_group_fmap_generators _ _
           (fmap[Grp_Forget] (free_group_counit G)) w).
Qed.

Lemma Grp_riehl_kH_cofork :
  Grp_riehl_kH ∘ free_group_counit (FreeGrp (Grp_Forget H))
    ≈ Grp_riehl_kH ∘ fmap[FreeGrp] (fmap[Grp_Forget] (free_group_counit H)).
Proof using Hk.
  apply Grp_free_hom_ext; intro w.
  transitivity (k (fmap[FreeGrp] inrS w)).
  { apply (proper_morphism (grp_map Grp_riehl_kH)).
    exact (free_group_counit_generator (FreeGrp (Grp_Forget H)) w). }
  transitivity (k (Grp_riehl_r (fg_insert UFUGH (Datatypes.inr w)))).
  { apply (proper_morphism (grp_map k)).
    symmetry. exact (Grp_riehl_r_inr w). }
  transitivity (k (Grp_riehl_l (fg_insert UFUGH (Datatypes.inr w)))).
  { symmetry. exact (Hk _). }
  transitivity (k (fg_insert UGH (Datatypes.inr (free_group_counit H w)))).
  { apply (proper_morphism (grp_map k)).
    exact (Grp_riehl_l_inr w). }
  transitivity (Grp_riehl_kH
                  (fg_insert (Grp_Forget H) (free_group_counit H w))).
  { apply (proper_morphism (grp_map k)).
    symmetry. exact (@free_group_fmap_generators _ UGH _ _). }
  apply (proper_morphism (grp_map Grp_riehl_kH)).
  symmetry.
  exact (@free_group_fmap_generators _ _
           (fmap[Grp_Forget] (free_group_counit H)) w).
Qed.

(* 相关说明。 （已译） *)
Definition Grp_riehl_uG : G ~{Grp@{u p}}~> c :=
  unique_obj (coeq_desc (Grp_canonical_presentation G)
                Grp_riehl_kG Grp_riehl_kG_cofork).

Definition Grp_riehl_uH : H ~{Grp@{u p}}~> c :=
  unique_obj (coeq_desc (Grp_canonical_presentation H)
                Grp_riehl_kH Grp_riehl_kH_cofork).

Lemma Grp_riehl_uG_counit :
  Grp_riehl_uG ∘ free_group_counit G ≈ Grp_riehl_kG.
Proof using Hk.
  exact (unique_property (coeq_desc (Grp_canonical_presentation G)
                            Grp_riehl_kG Grp_riehl_kG_cofork)).
Qed.

Lemma Grp_riehl_uH_counit :
  Grp_riehl_uH ∘ free_group_counit H ≈ Grp_riehl_kH.
Proof using Hk.
  exact (unique_property (coeq_desc (Grp_canonical_presentation H)
                            Grp_riehl_kH Grp_riehl_kH_cofork)).
Qed.

End Factors.

(* 相关说明。 （已译） *)

Section Descent.

Context (CC : @Cocartesian Grp@{u p}).
Context {c : Grp@{u p}} (k : FreeGrp UGH ~{Grp@{u p}}~> c).
Context (Hk : k ∘ Grp_riehl_l ≈ k ∘ Grp_riehl_r).

Definition Grp_riehl_desc : @Coprod Grp@{u p} CC G H ~{Grp@{u p}}~> c :=
  @merge Grp@{u p} CC _ _ _ (Grp_riehl_uG k Hk) (Grp_riehl_uH k Hk).

Lemma Grp_riehl_desc_commutes : Grp_riehl_desc ∘ Grp_riehl_e CC ≈ k.
Proof.
  apply Grp_free_hom_ext; intros [g|g].
  - transitivity (Grp_riehl_desc (@inl Grp@{u p} CC G H g)).
    { apply (proper_morphism (grp_map Grp_riehl_desc)).
      exact (Grp_riehl_transpose_generator _ _ (Datatypes.inl g)). }
    transitivity (Grp_riehl_uG k Hk g).
    { exact (@inl_merge Grp@{u p} CC _ _ _ _ _ g). }
    transitivity (Grp_riehl_uG k Hk (free_group_counit G (fg_insert _ g))).
    { apply (proper_morphism (grp_map (Grp_riehl_uG k Hk))).
      symmetry. exact (free_group_counit_generator G g). }
    transitivity (Grp_riehl_kG k (fg_insert _ g)).
    { exact (Grp_riehl_uG_counit k Hk (fg_insert _ g)). }
    apply (proper_morphism (grp_map k)).
    exact (@free_group_fmap_generators _ UGH _ g).
  - transitivity (Grp_riehl_desc (@inr Grp@{u p} CC G H g)).
    { apply (proper_morphism (grp_map Grp_riehl_desc)).
      exact (Grp_riehl_transpose_generator _ _ (Datatypes.inr g)). }
    transitivity (Grp_riehl_uH k Hk g).
    { exact (@inr_merge Grp@{u p} CC _ _ _ _ _ g). }
    transitivity (Grp_riehl_uH k Hk (free_group_counit H (fg_insert _ g))).
    { apply (proper_morphism (grp_map (Grp_riehl_uH k Hk))).
      symmetry. exact (free_group_counit_generator H g). }
    transitivity (Grp_riehl_kH k (fg_insert _ g)).
    { exact (Grp_riehl_uH_counit k Hk (fg_insert _ g)). }
    apply (proper_morphism (grp_map k)).
    exact (@free_group_fmap_generators _ UGH _ g).
Qed.

Lemma Grp_riehl_desc_unique (v : @Coprod Grp@{u p} CC G H ~{Grp@{u p}}~> c) :
  v ∘ Grp_riehl_e CC ≈ k → Grp_riehl_desc ≈ v.
Proof.
  intro Hv.
  assert (HG : Grp_riehl_uG k Hk ≈ v ∘ @inl Grp@{u p} CC G H).
  { apply (uniqueness (coeq_desc (Grp_canonical_presentation G)
                         (Grp_riehl_kG k) (Grp_riehl_kG_cofork k Hk))).
    unfold Grp_riehl_kG.
    rewrite <- Hv.
    rewrite <- !comp_assoc.
    rewrite (Grp_riehl_transpose_inl (@inl Grp@{u p} CC G H)
                                     (@inr Grp@{u p} CC G H)).
    reflexivity. }
  assert (HH : Grp_riehl_uH k Hk ≈ v ∘ @inr Grp@{u p} CC G H).
  { apply (uniqueness (coeq_desc (Grp_canonical_presentation H)
                         (Grp_riehl_kH k) (Grp_riehl_kH_cofork k Hk))).
    unfold Grp_riehl_kH.
    rewrite <- Hv.
    rewrite <- !comp_assoc.
    rewrite (Grp_riehl_transpose_inr (@inl Grp@{u p} CC G H)
                                     (@inr Grp@{u p} CC G H)).
    reflexivity. }
  unfold Grp_riehl_desc.
  rewrite HG, HH.
  rewrite (@merge_comp Grp@{u p} CC).
  rewrite (@merge_inl_inr Grp@{u p} CC).
  exact (@id_right Grp@{u p} _ _ v).
Qed.

End Descent.

Definition Grp_coproduct_is_coequalizer (CC : @Cocartesian Grp@{u p}) :
  IsCoequalizer Grp_riehl_l Grp_riehl_r (@Coprod Grp@{u p} CC G H)
    (Grp_riehl_e CC).
Proof.
  unshelve econstructor.
  - exact (Grp_riehl_transpose_cofork _ _).
  - intros c k Hk.
    exact {| unique_obj      := Grp_riehl_desc CC k Hk;
             unique_property := Grp_riehl_desc_commutes CC k Hk;
             uniqueness      := Grp_riehl_desc_unique CC k Hk |}.
Defined.

(* 相关说明。 （已译） *)

Section Construction.

Context {q : Grp@{u p}} {e : FreeGrp UGH ~{Grp@{u p}}~> q}.
Context (E : IsCoequalizer Grp_riehl_l Grp_riehl_r q e).

(* 相关说明。 （已译） *)
Definition Grp_riehl_inl : G ~{Grp@{u p}}~> q := Grp_riehl_uG e (cofork E).
Definition Grp_riehl_inr : H ~{Grp@{u p}}~> q := Grp_riehl_uH e (cofork E).

(* 相关说明。 （已译） *)
Example Grp_riehl_inl_is_restriction (g : carrier (grp_setoid G)) :
  Grp_riehl_inl g = e (fmap[FreeGrp] inlS (fg_insert (Grp_Forget G) g))
  := eq_refl.

(* 相关说明。 （已译） *)
Definition Grp_riehl_merge {z : Grp@{u p}}
  (f1 : G ~{Grp@{u p}}~> z) (f2 : H ~{Grp@{u p}}~> z) : q ~{Grp@{u p}}~> z :=
  unique_obj (coeq_desc E (Grp_riehl_transpose f1 f2)
                (Grp_riehl_transpose_cofork f1 f2)).

Lemma Grp_riehl_merge_inl {z : Grp@{u p}}
  (f1 : G ~{Grp@{u p}}~> z) (f2 : H ~{Grp@{u p}}~> z) :
  Grp_riehl_merge f1 f2 ∘ Grp_riehl_inl ≈ f1.
Proof.
  apply (@epic _ _ _ _ (coequalizer_epic _ _ (Grp_canonical_presentation G))).
  rewrite <- comp_assoc.
  rewrite (Grp_riehl_uG_counit e (cofork E)).
  unfold Grp_riehl_kG.
  rewrite comp_assoc.
  rewrite (unique_property (coeq_desc E (Grp_riehl_transpose f1 f2)
                              (Grp_riehl_transpose_cofork f1 f2))).
  exact (Grp_riehl_transpose_inl f1 f2).
Qed.

Lemma Grp_riehl_merge_inr {z : Grp@{u p}}
  (f1 : G ~{Grp@{u p}}~> z) (f2 : H ~{Grp@{u p}}~> z) :
  Grp_riehl_merge f1 f2 ∘ Grp_riehl_inr ≈ f2.
Proof.
  apply (@epic _ _ _ _ (coequalizer_epic _ _ (Grp_canonical_presentation H))).
  rewrite <- comp_assoc.
  rewrite (Grp_riehl_uH_counit e (cofork E)).
  unfold Grp_riehl_kH.
  rewrite comp_assoc.
  rewrite (unique_property (coeq_desc E (Grp_riehl_transpose f1 f2)
                              (Grp_riehl_transpose_cofork f1 f2))).
  exact (Grp_riehl_transpose_inr f1 f2).
Qed.

Lemma Grp_riehl_merge_unique {z : Grp@{u p}}
  (f1 : G ~{Grp@{u p}}~> z) (f2 : H ~{Grp@{u p}}~> z)
  (h : q ~{Grp@{u p}}~> z) :
  h ∘ Grp_riehl_inl ≈ f1 → h ∘ Grp_riehl_inr ≈ f2 →
  h ≈ Grp_riehl_merge f1 f2.
Proof.
  intros H1 H2.
  symmetry.
  apply (uniqueness (coeq_desc E (Grp_riehl_transpose f1 f2)
                       (Grp_riehl_transpose_cofork f1 f2))).
  apply Grp_free_hom_ext; intros [g|g].
  - transitivity (h (Grp_riehl_inl g)).
    { apply (proper_morphism (grp_map h)).
      transitivity (e (fmap[FreeGrp] inlS (fg_insert _ g))).
      { apply (proper_morphism (grp_map e)).
        symmetry. exact (@free_group_fmap_generators _ UGH _ g). }
      transitivity (Grp_riehl_inl (free_group_counit G (fg_insert _ g))).
      { symmetry.
        exact (Grp_riehl_uG_counit e (cofork E) (fg_insert _ g)). }
      apply (proper_morphism (grp_map Grp_riehl_inl)).
      exact (free_group_counit_generator G g). }
    rewrite (H1 g).
    symmetry.
    exact (Grp_riehl_transpose_generator f1 f2 (Datatypes.inl g)).
  - transitivity (h (Grp_riehl_inr g)).
    { apply (proper_morphism (grp_map h)).
      transitivity (e (fmap[FreeGrp] inrS (fg_insert _ g))).
      { apply (proper_morphism (grp_map e)).
        symmetry. exact (@free_group_fmap_generators _ UGH _ g). }
      transitivity (Grp_riehl_inr (free_group_counit H (fg_insert _ g))).
      { symmetry.
        exact (Grp_riehl_uH_counit e (cofork E) (fg_insert _ g)). }
      apply (proper_morphism (grp_map Grp_riehl_inr)).
      exact (free_group_counit_generator H g). }
    rewrite (H2 g).
    symmetry.
    exact (Grp_riehl_transpose_generator f1 f2 (Datatypes.inr g)).
Qed.

(* 相关说明。 （已译） *)
Lemma Grp_riehl_inl_along {z : Grp@{u p}}
  (f1 : G ~{Grp@{u p}}~> z) (f2 : H ~{Grp@{u p}}~> z)
  (φ : q ~{Grp@{u p}}~> z) :
  φ ∘ e ≈ Grp_riehl_transpose f1 f2 → φ ∘ Grp_riehl_inl ≈ f1.
Proof.
  intro Hφ.
  rewrite <- (uniqueness (coeq_desc E (Grp_riehl_transpose f1 f2)
                            (Grp_riehl_transpose_cofork f1 f2)) φ Hφ).
  exact (Grp_riehl_merge_inl f1 f2).
Qed.

Lemma Grp_riehl_inr_along {z : Grp@{u p}}
  (f1 : G ~{Grp@{u p}}~> z) (f2 : H ~{Grp@{u p}}~> z)
  (φ : q ~{Grp@{u p}}~> z) :
  φ ∘ e ≈ Grp_riehl_transpose f1 f2 → φ ∘ Grp_riehl_inr ≈ f2.
Proof.
  intro Hφ.
  rewrite <- (uniqueness (coeq_desc E (Grp_riehl_transpose f1 f2)
                            (Grp_riehl_transpose_cofork f1 f2)) φ Hφ).
  exact (Grp_riehl_merge_inr f1 f2).
Qed.

End Construction.

(* Postcomposition moves inside the transpose. *)
Lemma Grp_riehl_transpose_post {z z' : Grp@{u p}}
  (f1 : G ~{Grp@{u p}}~> z) (f2 : H ~{Grp@{u p}}~> z)
  (f1' : G ~{Grp@{u p}}~> z') (f2' : H ~{Grp@{u p}}~> z')
  (φ : z ~{Grp@{u p}}~> z') :
  φ ∘ f1 ≈ f1' → φ ∘ f2 ≈ f2' →
  φ ∘ Grp_riehl_transpose f1 f2 ≈ Grp_riehl_transpose f1' f2'.
Proof.
  intros H1 H2.
  apply Grp_free_hom_ext; intros [g|g].
  - transitivity (φ (f1 g)).
    { apply (proper_morphism (grp_map φ)).
      exact (Grp_riehl_transpose_generator f1 f2 (Datatypes.inl g)). }
    rewrite (H1 g).
    symmetry.
    exact (Grp_riehl_transpose_generator f1' f2' (Datatypes.inl g)).
  - transitivity (φ (f2 g)).
    { apply (proper_morphism (grp_map φ)).
      exact (Grp_riehl_transpose_generator f1 f2 (Datatypes.inr g)). }
    rewrite (H2 g).
    symmetry.
    exact (Grp_riehl_transpose_generator f1' f2' (Datatypes.inr g)).
Qed.

End RiehlPair.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition Grp_Cocartesian_of_coequalizers@{u p +}
  (HC : HasCoequalizers Grp@{u p}) : @Cocartesian Grp@{u p}.
Proof.
  unshelve refine (@Build_Cartesian (Grp^op)
    (fun G H => `1 (@coeq Grp HC _ _ (Grp_riehl_l G H) (Grp_riehl_r G H)))
    (fun x G H f1 f2 =>
       @Grp_riehl_merge G H _ _
         (`2 (`2 (@coeq Grp HC _ _ (Grp_riehl_l G H) (Grp_riehl_r G H))))
         x f1 f2)
    (fun G H =>
       @Grp_riehl_inl G H _ _
         (`2 (`2 (@coeq Grp HC _ _ (Grp_riehl_l G H) (Grp_riehl_r G H)))))
    (fun G H =>
       @Grp_riehl_inr G H _ _
         (`2 (`2 (@coeq Grp HC _ _ (Grp_riehl_l G H) (Grp_riehl_r G H)))))
    _ _).
  - intros x G H f1 f1' Hf1 f2 f2' Hf2.
    apply Grp_riehl_merge_unique.
    + rewrite (Grp_riehl_merge_inl _ _ _ f1 f2); exact Hf1.
    + rewrite (Grp_riehl_merge_inr _ _ _ f1 f2); exact Hf2.
  - intros x G H f1 f2 h; split.
    + intro Hh; split.
      * rewrite Hh. exact (Grp_riehl_merge_inl _ _ _ f1 f2).
      * rewrite Hh. exact (Grp_riehl_merge_inr _ _ _ f1 f2).
    + intros [H1 H2].
      exact (Grp_riehl_merge_unique _ _ _ f1 f2 h H1 H2).
Defined.

(* * ** At adjoint 函子 定理's coproduct coequalizers （已译） *)

(* Riehl's statement at coproduct Instance/Grp/Colimit.v obtains from
 adjoint 函子 定理, passed explicitly. （已译） *)
Definition Grp_free_product_is_coequalizer@{u p +} (G H : Grp@{u p}) :
  IsCoequalizer (Grp_riehl_l G H) (Grp_riehl_r G H)
    (@Coprod Grp Grp_Cocartesian_via_GAFT G H)
    (Grp_riehl_e G H Grp_Cocartesian_via_GAFT) :=
  Grp_coproduct_is_coequalizer G H Grp_Cocartesian_via_GAFT.

(* The same at Instance/Grp/Pushout.v's words-based free product. *)
Definition Grp_free_product_words_is_coequalizer@{u p +} (G H : Grp@{u p}) :
  IsCoequalizer (Grp_riehl_l G H) (Grp_riehl_r G H)
    (@Coprod Grp Grp_Cocartesian G H)
    (Grp_riehl_e G H Grp_Cocartesian) :=
  Grp_coproduct_is_coequalizer G H Grp_Cocartesian.

(* Riehl's construction run on the adjoint functor theorem's coequalizers. *)
Definition Grp_Cocartesian_via_riehl@{u p +} : @Cocartesian Grp@{u p} :=
  Grp_Cocartesian_of_coequalizers Grp_HasCoequalizers_via_GAFT.

Example Grp_Cocartesian_via_riehl_obj@{u p +} (G H : Grp@{u p}) :
  @Coprod Grp Grp_Cocartesian_via_riehl G H
    = `1 (@coeq Grp Grp_HasCoequalizers_via_GAFT _ _
            (Grp_riehl_l G H) (Grp_riehl_r G H)) := eq_refl.

(** ** Agreement *)

(* 相关说明。 （已译） *)
Section CoequalizerAlong.

Context {C : Category} {x y : C} {f g : x ~> y}.
Context {q1 q2 : C} {e1 : y ~> q1} {e2 : y ~> q2}.
Context (E1 : IsCoequalizer f g q1 e1) (E2 : IsCoequalizer f g q2 e2).

Definition coequalizer_unique_along : q1 ≅ q2.
Proof using E1 E2.
  pose proof (coeq_desc E1 e2 (cofork E2)) as D12.
  pose proof (coeq_desc E2 e1 (cofork E1)) as D21.
  pose proof (coeq_desc E1 e1 (cofork E1)) as D11.
  pose proof (coeq_desc E2 e2 (cofork E2)) as D22.
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

Lemma coequalizer_unique_along_e : to coequalizer_unique_along ∘ e1 ≈ e2.
Proof using E1 E2. exact (unique_property (coeq_desc E1 e2 (cofork E2))). Qed.

End CoequalizerAlong.

(* The coequalizer Instance/Grp/Colimit.v's [Grp_HasCoequalizers_via_GAFT]
 returns Riehl's pair adjoint 函子 定理's coproduct... （已译） *)
Definition Grp_free_product_coequalizer_agrees@{u p +} (G H : Grp@{u p}) :
  `1 (@coeq Grp Grp_HasCoequalizers_via_GAFT _ _
        (Grp_riehl_l G H) (Grp_riehl_r G H))
    ≅ @Coprod Grp Grp_Cocartesian_via_GAFT G H :=
  coequalizer_unique_along
    (`2 (`2 (@coeq Grp Grp_HasCoequalizers_via_GAFT _ _
               (Grp_riehl_l G H) (Grp_riehl_r G H))))
    (Grp_free_product_is_coequalizer G H).

(* 相关说明。 （已译） *)
Lemma Grp_free_product_coequalizer_agrees_e@{u p +} (G H : Grp@{u p}) :
  to (Grp_free_product_coequalizer_agrees G H)
    ∘ `1 (`2 (@coeq Grp Grp_HasCoequalizers_via_GAFT _ _
                (Grp_riehl_l G H) (Grp_riehl_r G H)))
    ≈ Grp_riehl_e G H Grp_Cocartesian_via_GAFT.
Proof.
  exact (coequalizer_unique_along_e
           (`2 (`2 (@coeq Grp Grp_HasCoequalizers_via_GAFT _ _
                      (Grp_riehl_l G H) (Grp_riehl_r G H))))
           (Grp_free_product_is_coequalizer G H)).
Qed.

(* ...and injections: Riehl's left, 定理's the
 right. （已译） *)
Lemma Grp_free_product_coequalizer_agrees_inl@{u p +} (G H : Grp@{u p}) :
  to (Grp_free_product_coequalizer_agrees G H)
    ∘ @inl Grp Grp_Cocartesian_via_riehl G H
    ≈ @inl Grp Grp_Cocartesian_via_GAFT G H.
Proof.
  exact (Grp_riehl_inl_along G H _
           (@inl Grp Grp_Cocartesian_via_GAFT G H)
           (@inr Grp Grp_Cocartesian_via_GAFT G H) _
           (Grp_free_product_coequalizer_agrees_e G H)).
Qed.

Lemma Grp_free_product_coequalizer_agrees_inr@{u p +} (G H : Grp@{u p}) :
  to (Grp_free_product_coequalizer_agrees G H)
    ∘ @inr Grp Grp_Cocartesian_via_riehl G H
    ≈ @inr Grp Grp_Cocartesian_via_GAFT G H.
Proof.
  exact (Grp_riehl_inr_along G H _
           (@inl Grp Grp_Cocartesian_via_GAFT G H)
           (@inr Grp Grp_Cocartesian_via_GAFT G H) _
           (Grp_free_product_coequalizer_agrees_e G H)).
Qed.

(* The two coproduct bifunctors agree up natural 同构, both being
 左伴随 diagonal. （已译） *)
Definition Grp_riehl_coproduct_agrees@{u p +} :
  @InternalCoproductFunctor Grp@{u p} Grp_Cocartesian_via_riehl
    ≈ @InternalCoproductFunctor Grp@{u p} Grp_Cocartesian_via_GAFT :=
  left_adjoint_iso (Diagonal_Product Grp@{u p}) _ _
    (@Diagonal_Coproduct_Adjunction Grp@{u p} Grp_Cocartesian_via_riehl)
    (@Diagonal_Coproduct_Adjunction Grp@{u p} Grp_Cocartesian_via_GAFT).

(* Through Instance/Grp/Colimit.v's [Grp_free_product_iso], the same
   coequalizer is Instance/Grp/Pushout.v's words-based free product. *)
Definition Grp_free_product_coequalizer_agrees_words@{u p +}
  (G H : Grp@{u p}) :
  `1 (@coeq Grp Grp_HasCoequalizers_via_GAFT _ _
        (Grp_riehl_l G H) (Grp_riehl_r G H))
    ≅ @Coprod Grp Grp_Cocartesian G H :=
  iso_compose (Grp_free_product_iso G H)
              (Grp_free_product_coequalizer_agrees G H).

Lemma Grp_free_product_coequalizer_agrees_words_e@{u p +}
  (G H : Grp@{u p}) :
  to (Grp_free_product_coequalizer_agrees_words G H)
    ∘ `1 (`2 (@coeq Grp Grp_HasCoequalizers_via_GAFT _ _
                (Grp_riehl_l G H) (Grp_riehl_r G H)))
    ≈ Grp_riehl_e G H Grp_Cocartesian.
Proof.
  unfold Grp_free_product_coequalizer_agrees_words; simpl to.
  rewrite <- comp_assoc.
  rewrite (Grp_free_product_coequalizer_agrees_e G H).
  apply Grp_riehl_transpose_post.
  - exact (Grp_free_product_iso_inl G H).
  - exact (Grp_free_product_iso_inr G H).
Qed.

Lemma Grp_free_product_coequalizer_agrees_words_inl@{u p +}
  (G H : Grp@{u p}) :
  to (Grp_free_product_coequalizer_agrees_words G H)
    ∘ @inl Grp Grp_Cocartesian_via_riehl G H
    ≈ @inl Grp Grp_Cocartesian G H.
Proof.
  exact (Grp_riehl_inl_along G H _
           (@inl Grp Grp_Cocartesian G H) (@inr Grp Grp_Cocartesian G H) _
           (Grp_free_product_coequalizer_agrees_words_e G H)).
Qed.

Lemma Grp_free_product_coequalizer_agrees_words_inr@{u p +}
  (G H : Grp@{u p}) :
  to (Grp_free_product_coequalizer_agrees_words G H)
    ∘ @inr Grp Grp_Cocartesian_via_riehl G H
    ≈ @inr Grp Grp_Cocartesian G H.
Proof.
  exact (Grp_riehl_inr_along G H _
           (@inl Grp Grp_Cocartesian G H) (@inr Grp Grp_Cocartesian G H) _
           (Grp_free_product_coequalizer_agrees_words_e G H)).
Qed.

(** ** Non-vacuity *)

(*
   本节说明 Presentation 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section NonVacuity.

Universes u p.

Local Notation Z2 := Z2@{p}.
Local Notation Z2S :=
  (@Coprod Sets Sets_Cocartesian (Grp_Forget Z2) (Grp_Forget Z2)).
Local Notation Z2FS :=
  (@Coprod Sets Sets_Cocartesian (Grp_Forget (FreeGrp (Grp_Forget Z2)))
                                 (Grp_Forget (FreeGrp (Grp_Forget Z2)))).

Lemma Grp_riehl_pair_nontrivial :
  (Grp_riehl_l Z2 Z2 : _ ~{Grp@{u p}}~> _) ≈ Grp_riehl_r Z2 Z2 → False.
Proof.
  intro Hlr.
  pose (w := grp_mul (FreeGrpObject (Grp_Forget Z2))
               (fg_insert (Grp_Forget Z2) true)
               (fg_insert (Grp_Forget Z2) true)).
  unshelve epose (t := {| morphism := fun _ : Z2S => true |}
                         : Z2S ~{Sets}~> Grp_Forget Z2).
  { intros ? ? ?; reflexivity. }
  pose (k := free_grp_extend t).
  assert (HA : k (Grp_riehl_l Z2 Z2 (fg_insert Z2FS (Datatypes.inl w)))
                 ≈ true).
  { transitivity (k (fg_insert Z2S
                       (Datatypes.inl (free_group_counit Z2 w)))).
    - apply (proper_morphism (grp_map k)).
      exact (Grp_riehl_l_inl Z2 Z2 w).
    - exact (free_grp_extend_generators Z2S Z2 t _). }
  assert (HB : k (Grp_riehl_r Z2 Z2 (fg_insert Z2FS (Datatypes.inl w)))
                 ≈ false).
  { transitivity (k (fmap[FreeGrp]
                       (@inl Sets Sets_Cocartesian
                          (Grp_Forget Z2) (Grp_Forget Z2)) w)).
    - apply (proper_morphism (grp_map k)).
      exact (Grp_riehl_r_inl Z2 Z2 w).
    - unfold w.
      rewrite (proper_morphism (grp_map k) _ _
                 (grp_map_mul (fmap[FreeGrp]
                    (@inl Sets Sets_Cocartesian
                       (Grp_Forget Z2) (Grp_Forget Z2))) _ _)).
      rewrite (grp_map_mul k).
      rewrite (proper_morphism (grp_map k) _ _
                 (@free_group_fmap_generators (Grp_Forget Z2) Z2S _ true)).
      rewrite (free_grp_extend_generators Z2S Z2 t).
      reflexivity. }
  apply Z2_nontrivial.
  transitivity (k (Grp_riehl_l Z2 Z2 (fg_insert Z2FS (Datatypes.inl w)))).
  { symmetry; exact HA. }
  transitivity (k (Grp_riehl_r Z2 Z2 (fg_insert Z2FS (Datatypes.inl w)))).
  { apply (proper_morphism (grp_map k)); exact (Hlr _). }
  exact HB.
Qed.

(* 相关说明。 （已译） *)
Corollary Grp_riehl_e_not_monic (CC : @Cocartesian Grp@{u p}) :
  Monic (Grp_riehl_e Z2 Z2 CC) → False.
Proof.
  intro Hm.
  apply Grp_riehl_pair_nontrivial.
  apply (@monic _ _ _ _ Hm).
  exact (cofork (Grp_coproduct_is_coequalizer Z2 Z2 CC)).
Qed.

End NonVacuity.

(* The same at adjoint 函子 定理's coproduct, exists only
 above [Set] carriers. （已译） *)
Example Grp_free_product_coequalizer_nontrivial@{u p +} :
  Monic (Grp_riehl_e Z2@{p} Z2@{p}
           (Grp_Cocartesian_via_GAFT : @Cocartesian Grp@{u p})) → False :=
  Grp_riehl_e_not_monic _.
