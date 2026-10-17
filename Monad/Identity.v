Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.

Generalizable All Variables.

(** * The identity monad *)

(*
   nLab: https://ncatlab.org/nlab/show/monad
   nLab: https://ncatlab.org/nlab/show/Eilenberg-Moore+category

   本文件给出单子相关定义或实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The monad ⟨I, 1, 1⟩ *)

Definition IdMonad@{o h | } (C : Category@{o h h}) : @Monad C Id[C].
Proof.
  unshelve refine (@Build_Monad C Id[C] (fun x => id) (fun x => id)
                     _ _ _ _ _); intros; simpl.
  - transitivity f; [ apply id_left | symmetry; apply id_right ].
  - reflexivity.
  - apply id_left.
  - apply id_left.
  - transitivity f; [ apply id_left | symmetry; apply id_right ].
Defined.

Example IdMonad_fobj@{o h | +} (C : Category@{o h h}) (x : C) :
  fobj[Id[C]] x = x := eq_refl.

Example IdMonad_fmap@{o h | +} (C : Category@{o h h}) (x y : C)
  (f : x ~> y) : fmap[Id[C]] f = f := eq_refl.

Example IdMonad_ret@{o h | +} (C : Category@{o h h}) (x : C) :
  @ret C Id[C] (IdMonad@{o h} C) x = id := eq_refl.

Example IdMonad_join@{o h | +} (C : Category@{o h h}) (x : C) :
  @join C Id[C] (IdMonad@{o h} C) x = id := eq_refl.

(** ** Its algebras are the objects *)

Lemma IdMonad_alg_id@{o h | } (C : Category@{o h h}) (a : C)
  (A : @TAlgebra C Id[C] (IdMonad@{o h} C) a) : t_alg[A] ≈ id.
Proof.
  transitivity (t_alg[A] ∘ id); [ symmetry; apply id_right | ].
  exact (@t_id C Id[C] (IdMonad@{o h} C) a A).
Qed.

Definition IdMonad_EM_counit@{o h s e | h < s, o <= e, h <= e +}
  (C : Category@{o h h}) :
  @EM_Forget@{o h s e} C Id[C] (IdMonad@{o h} C)
    ◯ @EM_Free@{o h s e} C Id[C] (IdMonad@{o h} C) ≈ Id[C].
Proof.
  exists (fun x => iso_id).
  intros x y f; simpl.
  transitivity (id ∘ f); [ symmetry; apply id_left | ].
  symmetry; apply id_right.
Defined.

Definition IdMonad_EM_unit_iso@{o h s e | h < s, o <= e, h <= e +}
  (C : Category@{o h h})
  (X : @EilenbergMoore@{e o s h} C Id[C] (IdMonad@{o h} C)) :
  @Isomorphism (@EilenbergMoore@{e o s h} C Id[C] (IdMonad@{o h} C))
    X (fobj[@EM_Free@{o h s e} C Id[C] (IdMonad@{o h} C)
             ◯ @EM_Forget@{o h s e} C Id[C] (IdMonad@{o h} C)] X).
Proof.
  unshelve econstructor.
  - unshelve refine (@Build_TAlgebraHom C Id[C] (IdMonad@{o h} C)
                       (`1 X) (`1 X) (`2 X) _ id _); simpl.
    transitivity (t_alg[`2 X]); [ apply id_left | ].
    transitivity (@id C (`1 X)); [ exact (IdMonad_alg_id C _ (`2 X)) | ].
    symmetry; apply id_left.
  - unshelve refine (@Build_TAlgebraHom C Id[C] (IdMonad@{o h} C)
                       (`1 X) (`1 X) _ (`2 X) id _); simpl.
    transitivity (@id C (`1 X)); [ apply id_left | ].
    transitivity (t_alg[`2 X]);
      [ symmetry; exact (IdMonad_alg_id C _ (`2 X)) | ].
    symmetry; apply id_right.
  - simpl; apply id_left.
  - simpl; apply id_left.
Defined.

Example IdMonad_EM_unit_iso_id@{o h s e | h < s, o <= e, h <= e +}
  (C : Category@{o h h})
  (X : @EilenbergMoore@{e o s h} C Id[C] (IdMonad@{o h} C)) :
  (t_alg_hom[to (IdMonad_EM_unit_iso@{o h s e} C X)],
   t_alg_hom[from (IdMonad_EM_unit_iso@{o h s e} C X)]) = (id, id)
  := eq_refl.

Definition IdMonad_EM_unit@{o h s e | h < s, o <= e, h <= e +}
  (C : Category@{o h h}) :
  Id[@EilenbergMoore@{e o s h} C Id[C] (IdMonad@{o h} C)]
    ≈ @EM_Free@{o h s e} C Id[C] (IdMonad@{o h} C)
        ◯ @EM_Forget@{o h s e} C Id[C] (IdMonad@{o h} C).
Proof.
  exists (IdMonad_EM_unit_iso C).
  intros X Y f; simpl.
  transitivity (id ∘ t_alg_hom[f]); [ symmetry; apply id_left | ].
  symmetry; apply id_right.
Defined.

Definition IdMonad_EM_equivalence@{o h s e | h < s, o <= e, h <= e +}
  (C : Category@{o h h}) :
  EquivalenceOfCategories (@EM_Forget@{o h s e} C Id[C] (IdMonad@{o h} C)) :=
  @Build_EquivalenceOfCategories _ _ _ _
    (IdMonad_EM_counit@{o h s e} C) (IdMonad_EM_unit@{o h s e} C).
