Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Morphism.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(* * * θ*: 函子 algebras induced 态射 单子 （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/monad (section "The 2-category of
   nLab: https://ncatlab.org/nlab/show/Eilenberg-Moore+category

   本文件给出代数结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* * ** θ* 对象: (a, h') ↦ (a, h' ∘ θ_a) （已译） *)

Definition mh_algebra@{o h | } {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M') {a : C}
  (A : @TAlgebra C T' M' a) : @TAlgebra C T M a.
Proof.
  unshelve refine
    (@Build_TAlgebra C T M a (t_alg[A] ∘ mh_transform θ a) _ _).
  - etransitivity; [ apply comp_assoc_sym | ].
    etransitivity;
      [ apply compose_respects; [ reflexivity | apply (mh_ret θ) ] | ].
    apply (@t_id C T' M' a A).
  - symmetry.
    etransitivity; [ apply comp_assoc_sym | ].
    etransitivity;
      [ apply compose_respects; [ reflexivity | apply (mh_join θ) ] | ].
    etransitivity; [ apply comp_assoc | ].
    etransitivity;
      [ apply compose_respects;
          [ symmetry; apply (@t_action C T' M' a A) | reflexivity ] | ].
    etransitivity; [ apply comp_assoc_sym | ].
    etransitivity;
      [ apply compose_respects; [ reflexivity | apply comp_assoc ] | ].
    etransitivity;
      [ apply compose_respects;
          [ reflexivity
          | apply compose_respects;
              [ apply (naturality (mh_transform θ)) | reflexivity ] ] | ].
    etransitivity;
      [ apply compose_respects; [ reflexivity | apply comp_assoc_sym ] | ].
    etransitivity; [ apply comp_assoc | ].
    apply compose_respects; [ reflexivity | ].
    symmetry. apply fmap_comp.
Defined.

(** ** θ* : X^{T'} ⟶ X^T *)

Definition mh_EM@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M') :
  @EilenbergMoore@{e o s h} C T' M' ⟶ @EilenbergMoore@{e o s h} C T M.
Proof.
  unshelve refine
    (@Build_Functor
       (@EilenbergMoore@{e o s h} C T' M') (@EilenbergMoore@{e o s h} C T M)
       (fun X => (`1 X; mh_algebra θ (`2 X)))
       (fun X Y f =>
          @Build_TAlgebraHom C T M (`1 X) (`1 Y)
            (mh_algebra θ (`2 X)) (mh_algebra θ (`2 Y))
            (t_alg_hom[f]) _) _ _ _).
  - etransitivity; [ apply comp_assoc | ].
    etransitivity;
      [ apply compose_respects;
          [ apply (@t_alg_hom_commutes _ _ _ _ _ _ _ f) | reflexivity ] | ].
    etransitivity; [ apply comp_assoc_sym | ].
    etransitivity;
      [ apply compose_respects;
          [ reflexivity | apply (naturality (mh_transform θ)) ] | ].
    apply comp_assoc.
  - intros X Y f g E. exact E.
  - intros X. simpl. reflexivity.
  - intros X Y Z f g. simpl. reflexivity.
Defined.

Example mh_EM_carrier@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M')
  (X : @EilenbergMoore@{e o s h} C T' M') :
  `1 (fobj[mh_EM@{o h e s} θ] X) = `1 X := eq_refl.

Example mh_EM_alg@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M')
  (X : @EilenbergMoore@{e o s h} C T' M') :
  @t_alg _ _ _ _ (`2 (fobj[mh_EM@{o h e s} θ] X))
    = @t_alg _ _ _ _ (`2 X) ∘ mh_transform θ (`1 X) := eq_refl.

Example mh_EM_hom@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M')
  (X Y : @EilenbergMoore@{e o s h} C T' M') (f : X ~> Y) :
  t_alg_hom[fmap[mh_EM@{o h e s} θ] f] = t_alg_hom[f] := eq_refl.

(** ** G^T ∘ θ* = G^{T'} *)

(* On objects and on arrows, by [eq_refl]. *)

Example mh_EM_forget_obj@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M')
  (X : @EilenbergMoore@{e o s h} C T' M') :
  fobj[@EM_Forget@{o h s e} C T M ◯ mh_EM@{o h e s} θ] X
    = fobj[@EM_Forget@{o h s e} C T' M'] X := eq_refl.

Example mh_EM_forget_obj_fun@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M') :
  (fun X => fobj[@EM_Forget@{o h s e} C T M ◯ mh_EM@{o h e s} θ] X)
    = (fun X => fobj[@EM_Forget@{o h s e} C T' M'] X) := eq_refl.

Example mh_EM_forget_map@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M')
  (X Y : @EilenbergMoore@{e o s h} C T' M') (f : X ~> Y) :
  fmap[@EM_Forget@{o h s e} C T M ◯ mh_EM@{o h e s} θ] f
    = fmap[@EM_Forget@{o h s e} C T' M'] f := eq_refl.

(* At Cat's ≈, with identity isomorphisms. *)

Theorem mh_EM_forget@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M') :
  @EM_Forget@{o h s e} C T M ◯ mh_EM@{o h e s} θ
    ≈ @EM_Forget@{o h s e} C T' M'.
Proof.
  exists (fun X => iso_id).
  intros X Y f; cbn.
  symmetry.
  etransitivity; [ apply id_right | ].
  apply id_left.
Defined.

(* 相关说明。 （已译） *)

Example mh_EM_forget_iso_id@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M')
  (X : @EilenbergMoore@{e o s h} C T' M') :
  (to (projT1 (mh_EM_forget@{o h e s} θ) X),
   from (projT1 (mh_EM_forget@{o h e s} θ) X)) = (id, id) := eq_refl.

(* In the strict setoid of functors: objects equal by [eq_refl]. *)

Definition mh_EM_forget_strict@{o h e s a b |
  h < s, o <= e, h <= e, o <= a, h <= a, e <= a, h <= b, e <= b +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M') :
  @equiv _ (@Functor_StrictEq_Setoid@{a b e o s h} _ C)
    (@EM_Forget@{o h s e} C T M ◯ mh_EM@{o h e s} θ)
    (@EM_Forget@{o h s e} C T' M').
Proof.
  exists (fun X => eq_refl).
  intros X Y f. reflexivity.
Defined.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)

Definition mh_free_component@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M') (x : C) :
  fobj[@EM_Free@{o h s e} C T M] x
    ~{ @EilenbergMoore@{e o s h} C T M }~>
  fobj[mh_EM@{o h e s} θ ◯ @EM_Free@{o h s e} C T' M'] x.
Proof.
  unshelve refine (@Build_TAlgebraHom C T M (T x) (T' x) _ _
                     (mh_transform θ x) _).
  etransitivity; [ apply (mh_join θ) | ].
  apply comp_assoc.
Defined.

Definition mh_EM_free@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M') :
  @EM_Free@{o h s e} C T M
    ⟹ mh_EM@{o h e s} θ ◯ @EM_Free@{o h s e} C T' M'.
Proof.
  unshelve refine (Build_Transform' (mh_free_component θ) _).
  intros x y f. simpl.
  apply (naturality (mh_transform θ)).
Defined.

(* Its image under G^T is θ itself. *)

Example mh_EM_free_forget@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M') (x : C) :
  fmap[@EM_Forget@{o h s e} C T M] (transform[mh_EM_free@{o h e s} θ] x)
    = mh_transform θ x := eq_refl.

(* 相关说明。 （已译） *)

Lemma mh_EM_free_transpose@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M') (x : C) :
  t_alg_hom[@EM_extend@{o h e s} C T M x
                 (fobj[mh_EM@{o h e s} θ ◯ @EM_Free@{o h s e} C T' M'] x)
                 (@ret C T' M' x)]
    ≈ mh_transform θ x.
Proof.
  simpl.
  etransitivity; [ apply comp_assoc_sym | ].
  etransitivity;
    [ apply compose_respects;
        [ reflexivity | symmetry; apply (naturality (mh_transform θ)) ] | ].
  etransitivity; [ apply comp_assoc | ].
  etransitivity;
    [ apply compose_respects; [ apply join_fmap_ret | reflexivity ] | ].
  apply id_left.
Qed.

(** ** Functoriality in θ *)

(* The 恒等箭头 between two structures one carrier whose
 structure maps ≈. （已译） *)

Definition talg_same@{o h | } {C : Category@{o h h}} {T : C ⟶ C}
  {M : @Monad C T} {a : C} (A B : @TAlgebra C T M a)
  (E : @t_alg C T M a A ≈ @t_alg C T M a B) : @TAlgebraHom C T M a a A B.
Proof.
  unshelve refine (@Build_TAlgebraHom C T M a a A B id _).
  etransitivity; [ apply id_left | ].
  etransitivity; [ exact E | ].
  symmetry.
  etransitivity;
    [ apply compose_respects; [ reflexivity | apply fmap_id ] | ].
  apply id_right.
Defined.

Lemma mh_EM_respects@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ θ' : MonadHom@{o h} M M')
  (E : ∀ x, mh_transform θ x ≈ mh_transform θ' x) :
  mh_EM@{o h e s} θ ≈ mh_EM@{o h e s} θ'.
Proof.
  unshelve eexists.
  - intros X.
    unshelve refine (@Build_Isomorphism _ _ _ _ _ _ _).
    + apply talg_same. simpl.
      apply compose_respects; [ reflexivity | apply E ].
    + apply talg_same. simpl.
      apply compose_respects; [ reflexivity | symmetry; apply E ].
    + simpl. apply id_left.
    + simpl. apply id_left.
  - intros X Y f. simpl.
    symmetry. etransitivity; [ apply id_right | ]. apply id_left.
Defined.

Lemma mh_EM_id@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T : C ⟶ C} {M : @Monad C T} :
  mh_EM@{o h e s} (mh_id M) ≈ @Id (@EilenbergMoore@{e o s h} C T M).
Proof.
  unshelve eexists.
  - intros X.
    unshelve refine (@Build_Isomorphism _ _ _ _ _ _ _).
    + apply talg_same. simpl. apply id_right.
    + apply talg_same. simpl. symmetry. apply id_right.
    + simpl. apply id_left.
    + simpl. apply id_left.
  - intros X Y f. simpl.
    symmetry. etransitivity; [ apply id_right | ]. apply id_left.
Defined.

Lemma mh_EM_compose@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' T'' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} {M'' : @Monad C T''}
  (φ : MonadHom@{o h} M' M'') (θ : MonadHom@{o h} M M') :
  mh_EM@{o h e s} (mh_compose φ θ)
    ≈ mh_EM@{o h e s} θ ◯ mh_EM@{o h e s} φ.
Proof.
  unshelve eexists.
  - intros X.
    unshelve refine (@Build_Isomorphism _ _ _ _ _ _ _).
    + apply talg_same. simpl. apply comp_assoc.
    + apply talg_same. simpl. apply comp_assoc_sym.
    + simpl. apply id_left.
    + simpl. apply id_left.
  - intros X Y f. simpl.
    symmetry. etransitivity; [ apply id_right | ]. apply id_left.
Defined.

(* 相关说明。 （已译） *)

Example mh_EM_respects_iso_id@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ θ' : MonadHom@{o h} M M')
  (E : ∀ x, mh_transform θ x ≈ mh_transform θ' x)
  (X : @EilenbergMoore@{e o s h} C T' M') :
  (t_alg_hom[to (projT1 (mh_EM_respects@{o h e s} θ θ' E) X)],
   t_alg_hom[from (projT1 (mh_EM_respects@{o h e s} θ θ' E) X)])
    = (id, id) := eq_refl.

Example mh_EM_id_iso_id@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T : C ⟶ C} {M : @Monad C T}
  (X : @EilenbergMoore@{e o s h} C T M) :
  (t_alg_hom[to (projT1 (@mh_EM_id@{o h e s} C T M) X)],
   t_alg_hom[from (projT1 (@mh_EM_id@{o h e s} C T M) X)]) = (id, id)
  := eq_refl.

Example mh_EM_compose_iso_id@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' T'' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} {M'' : @Monad C T''}
  (φ : MonadHom@{o h} M' M'') (θ : MonadHom@{o h} M M')
  (X : @EilenbergMoore@{e o s h} C T'' M'') :
  (t_alg_hom[to (projT1 (mh_EM_compose@{o h e s} φ θ) X)],
   t_alg_hom[from (projT1 (mh_EM_compose@{o h e s} φ θ) X)]) = (id, id)
  := eq_refl.

(* * ** The contravariant 函子 (Monads C)^op ⟶ Cat （已译） *)

Definition Monads_EM@{o h m1 m2 e s u |
  h < s, h < u, e < u, o <= m1, h <= m1, o <= m2, h <= m2, m2 <= e,
  o <= e, h <= e +} (C : Category@{o h h}) :
  (Monads@{o h m1 m2} C)^op ⟶ Cat@{u e s e h}.
Proof.
  unshelve refine
    (@Build_Functor ((Monads@{o h m1 m2} C)^op) Cat@{u e s e h}
       (fun N : { T : C ⟶ C & @Monad C T } =>
          @EilenbergMoore@{e o s h} C (projT1 N) (projT2 N))
       (fun N N' (θ : MonadHom@{o h} (projT2 N') (projT2 N)) =>
          mh_EM@{o h e s} θ) _ _ _).
  - intros N N' θ θ' E. exact (mh_EM_respects θ θ' E).
  - intros N. exact mh_EM_id.
  - intros N N' N'' φ θ. exact (mh_EM_compose θ φ).
Defined.

Example Monads_EM_obj@{o h m1 m2 e s u |
  h < s, h < u, e < u, o <= m1, h <= m1, o <= m2, h <= m2, m2 <= e,
  o <= e, h <= e +} (C : Category@{o h h}) (N : Monads@{o h m1 m2} C) :
  fobj[Monads_EM@{o h m1 m2 e s u} C] N
    = @EilenbergMoore@{e o s h} C (projT1 N) (projT2 N) := eq_refl.

Example Monads_EM_map@{o h m1 m2 e s u |
  h < s, h < u, e < u, o <= m1, h <= m1, o <= m2, h <= m2, m2 <= e,
  o <= e, h <= e +} (C : Category@{o h h}) (N N' : Monads@{o h m1 m2} C)
  (θ : N' ~{Monads@{o h m1 m2} C}~> N) :
  fmap[Monads_EM@{o h m1 m2 e s u} C] θ = mh_EM@{o h e s} θ := eq_refl.
