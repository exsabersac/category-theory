(** * The free complete semilattice, and the monadicity of [SupLat] *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Comparison.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Monad.
Require Import Category.Instance.SupLat.

Generalizable All Variables.

(*
 Book: Awodey, "Category Theory", Carnegie Mellon pre-print, September
 Book: Riehl, "Category Theory in Context", 2nd ed., §5.1, Example
 nLab: https://ncatlab.org/nlab/show/suplattice
 nLab: https://ncatlab.org/nlab/show/monadic+functor

   本文件给出自由构造相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(** ** The free complete semilattice P X *)

(* P X ordered by inclusion, with sup = union. *)
Definition FreeSL@{o} (X : SetoidObject@{o o}) : SupLatObject@{o}.
Proof.
  unshelve refine
    (@Build_SupLatObject@{o} (Powerset_Prop_obj@{o} X)
       (λ S T, ∀ z, S z → T z) _ _ _ _ (@Powerset_union@{o} X) _ _).
  - intros S z Hz; exact Hz.
  - intros S T U H1 H2 z Hz; exact (H2 z (H1 z Hz)).
  - intros S S' T T' ES ET H z Hz.
    exact (proj1 (ET z) (H z (proj2 (ES z) Hz))).
  - intros S T H1 H2 z; split; [ apply H1 | apply H2 ].
  - intros SS S HS z Hz. exists S; split; assumption.
  - intros SS T H z [S [HS Hz]]. exact (H S HS z Hz).
Defined.

(* F : Sets ⟶ SupLat.  Its action on maps is #227's direct image, and a
   direct image preserves unions by the naturality of μ. *)
Definition SL_Free@{o so} : Sets@{o so} ⟶ SupLat@{o so}.
Proof.
  unshelve refine
    (@Build_Functor Sets@{o so} SupLat@{o so} FreeSL@{o}
       (fun X Y f => @Build_SupLatHom@{o} (FreeSL@{o} X) (FreeSL@{o} Y)
                       (fmap[Powerset_Prop@{o so}] f) _)
       _ _ _).
  - intro SS. symmetry. exact (Powerset_union_natural@{o} f SS).
  - intros X Y f g H.
    exact (@fmap_respects _ _ Powerset_Prop@{o so} X Y f g H).
  - intros X. exact (@fmap_id _ _ Powerset_Prop@{o so} X).
  - intros X Y Z f g. exact (@fmap_comp _ _ Powerset_Prop@{o so} X Y Z f g).
Defined.

(* U : SupLat ⟶ Sets forgets the order and the sup. *)
Definition SL_Forget@{o so} : SupLat@{o so} ⟶ Sets@{o so}.
Proof.
  unshelve refine
    (@Build_Functor SupLat@{o so} Sets@{o so} sl_set
       (fun A B f => slh_map f) _ _ _).
  - intros A B f g H. exact H.
  - intros A a. reflexivity.
  - intros A B C f g a. reflexivity.
Defined.

(* ------------------------------------------------------------------------ *)
(** ** The free/forgetful adjunction *)

(* A map ψ : X → U A extends to the sup-preserving S ↦ sup (ψ S). *)
Definition SL_extend@{o so} {X : SetoidObject@{o o}} {A : SupLatObject@{o}}
  (ψ : X ~{Sets@{o so}}~> fobj[SL_Forget@{o so}] A) :
  fobj[SL_Free@{o so}] X ~{SupLat@{o so}}~> A.
Proof.
  unshelve refine
    (@Build_SupLatHom@{o} (FreeSL@{o} X) A
       (@setoid_morphism_compose@{o o o} _ _ _
          (sl_sup A) (Powerset_Prop_map@{o} ψ)) _).
  intro SS.
  transitivity (sl_sup A (Powerset_union_pred@{o}
                  (Powerset_Prop_image@{o} (Powerset_Prop_map@{o} ψ) SS))).
  { apply (proper_morphism (sl_sup A)). symmetry.
    exact (Powerset_union_natural@{o} ψ SS). }
  transitivity (sl_sup A (Powerset_Prop_image@{o} (sl_sup A)
                  (Powerset_Prop_image@{o} (Powerset_Prop_map@{o} ψ) SS))).
  { symmetry.
    exact (@t_action _ _ _ _ (SupLat_TAlgebra@{o so} A)
             (Powerset_Prop_image@{o} (Powerset_Prop_map@{o} ψ) SS)). }
  apply (proper_morphism (sl_sup A)). symmetry.
  exact (@Powerset_Prop_map_comp@{o} _ _ _
           (sl_sup A) (Powerset_Prop_map@{o} ψ) SS).
Defined.

(* A sup-preserving φ : F X → A restricts to x ↦ φ {x}. *)
Definition SL_restrict@{o so} {X : SetoidObject@{o o}} {A : SupLatObject@{o}}
  (φ : fobj[SL_Free@{o so}] X ~{SupLat@{o so}}~> A) :
  X ~{Sets@{o so}}~> fobj[SL_Forget@{o so}] A :=
  @setoid_morphism_compose@{o o o} _ _ _
    (slh_map φ) (@Powerset_Prop_singleton_map@{o} X).

Definition SL_adj_iso@{o so} (X : SetoidObject@{o o}) (A : SupLatObject@{o}) :
  @Isomorphism Sets@{o so}
    (@Build_SetoidObject
       (@hom SupLat@{o so} (fobj[SL_Free@{o so}] X) A)
       (@homset SupLat@{o so} (fobj[SL_Free@{o so}] X) A))
    (@Build_SetoidObject
       (@hom Sets@{o so} X (fobj[SL_Forget@{o so}] A))
       (@homset Sets@{o so} X (fobj[SL_Forget@{o so}] A))).
Proof.
  unshelve refine
    (@Build_Isomorphism Sets@{o so}
       (@Build_SetoidObject
          (@hom SupLat@{o so} (fobj[SL_Free@{o so}] X) A)
          (@homset SupLat@{o so} (fobj[SL_Free@{o so}] X) A))
       (@Build_SetoidObject
          (@hom Sets@{o so} X (fobj[SL_Forget@{o so}] A))
          (@homset Sets@{o so} X (fobj[SL_Forget@{o so}] A)))
       (@Build_SetoidMorphism
          (@hom SupLat@{o so} (fobj[SL_Free@{o so}] X) A)
          (@homset SupLat@{o so} (fobj[SL_Free@{o so}] X) A)
          (@hom Sets@{o so} X (fobj[SL_Forget@{o so}] A))
          (@homset Sets@{o so} X (fobj[SL_Forget@{o so}] A))
          (fun φ => @SL_restrict@{o so} X A φ) _)
       (@Build_SetoidMorphism
          (@hom Sets@{o so} X (fobj[SL_Forget@{o so}] A))
          (@homset Sets@{o so} X (fobj[SL_Forget@{o so}] A))
          (@hom SupLat@{o so} (fobj[SL_Free@{o so}] X) A)
          (@homset SupLat@{o so} (fobj[SL_Free@{o so}] X) A)
          (fun ψ => @SL_extend@{o so} X A ψ) _) _ _).
  - intros φ φ' H x. exact (H _).
  - intros ψ ψ' H S. apply (proper_morphism (sl_sup A)).
    exact (@Powerset_Prop_map_respects@{o} _ _ ψ ψ' H S).
  - intros ψ x.
    transitivity (sl_sup A (Powerset_Prop_singleton_pred@{o} (ψ x))).
    + apply (proper_morphism (sl_sup A)).
      exact (@Powerset_Prop_image_singleton@{o} _ _ ψ x).
    + exact (@t_id _ _ _ _ (SupLat_TAlgebra@{o so} A) (ψ x)).
  - intros φ S.
    transitivity (slh_map φ (Powerset_union_pred@{o}
                    (Powerset_Prop_image@{o}
                       (@Powerset_Prop_singleton_map@{o} X) S))).
    + transitivity (sl_sup A (Powerset_Prop_image@{o} (slh_map φ)
                      (Powerset_Prop_image@{o}
                         (@Powerset_Prop_singleton_map@{o} X) S))).
      * apply (proper_morphism (sl_sup A)).
        exact (@Powerset_Prop_map_comp@{o} _ _ _ (slh_map φ)
                 (@Powerset_Prop_singleton_map@{o} X) S).
      * symmetry. exact (slh_sup φ _).
    + apply (proper_morphism (slh_map φ)).
      exact (Powerset_union_image_singleton@{o} S).
Defined.

(* The free complete semilattice: F ⊣ U, in the hom-set form. *)
Definition SL_adj@{o so} :
  @Adjunction@{so o o so o o o o so o so} SupLat@{o so} Sets@{o so}
    SL_Free@{o so} SL_Forget@{o so}.
Proof.
  unshelve refine
    (@Build_Adjunction' SupLat@{o so} Sets@{o so}
       SL_Free@{o so} SL_Forget@{o so}
       (fun X A => SL_adj_iso@{o so} X A) _ _).
  - intros X Y A φ g x.
    apply (proper_morphism (slh_map φ)).
    exact (@Powerset_Prop_image_singleton@{o} _ _ g x).
  - intros X A B f φ x. reflexivity.
Defined.

(* ------------------------------------------------------------------------ *)
(** ** The monad of the adjunction, against [Powerset_Monad] *)

Definition SL_induced@{o so} :
  @Monad Sets@{o so} (SL_Forget@{o so} ◯ SL_Free@{o so}) :=
  Adjunction_Induced_Monad SL_adj@{o so}.

Example SL_induced_obj@{o so} (X : SetoidObject@{o o}) :
  fobj[SL_Forget@{o so} ◯ SL_Free@{o so}] X = fobj[Powerset_Prop@{o so}] X
  := eq_refl.

Example SL_induced_map@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) :
  fmap[SL_Forget@{o so} ◯ SL_Free@{o so}] f = fmap[Powerset_Prop@{o so}] f
  := eq_refl.

Example SL_induced_ret_fun@{o so} (X : SetoidObject@{o o}) :
  (fun x => @ret _ _ SL_induced@{o so} X x)
    = (fun x => @ret _ _ Powerset_Monad@{o so} X x) := eq_refl.

(* The induced join is U ε F, that is ⋃ ∘ P id: the union of the direct
   image of SS under the identity, not the union of SS. *)
Example SL_induced_join_fun@{o so} (X : SetoidObject@{o o}) :
  (fun SS => @join _ _ SL_induced@{o so} X SS)
    = (fun SS => Powerset_union_pred@{o}
                   (Powerset_Prop_image@{o}
                      (@setoid_morphism_id@{o o o} (Powerset_Prop_obj@{o} X))
                      SS)) := eq_refl.

Lemma SL_induced_ret_equiv@{o so} (X : SetoidObject@{o o}) :
  @ret _ _ SL_induced@{o so} X ≈ @ret _ _ Powerset_Monad@{o so} X.
Proof. intros x. reflexivity. Qed.

Lemma SL_induced_join_equiv@{o so} (X : SetoidObject@{o o}) :
  @join _ _ SL_induced@{o so} X ≈ @join _ _ Powerset_Monad@{o so} X.
Proof.
  intros SS.
  exact (@Powerset_union_respects@{o} X _ SS
           (@Powerset_Prop_map_id@{o} (Powerset_Prop_obj@{o} X) SS)).
Qed.

(* Transparent, so that its components read back below. *)
Definition SL_induced_functor_equiv@{o so} :
  SL_Forget@{o so} ◯ SL_Free@{o so} ≈ Powerset_Prop@{o so}.
Proof.
  exists (fun X => @iso_id Sets@{o so} (fobj[Powerset_Prop@{o so}] X)).
  intros X Y f S. reflexivity.
Defined.

(* Its component at X is the identity isomorphism. *)
Example SL_induced_functor_component@{o so} (X : SetoidObject@{o o}) :
  projT1 SL_induced_functor_equiv@{o so} X
    = @iso_id Sets@{o so} (fobj[Powerset_Prop@{o so}] X) := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Monadicity of the forgetful functor *)

(* An algebra of the induced monad is, with its data unchanged, an algebra
   of [Powerset_Monad]: only the action law is proved again, since the
   induced join is ⋃ ∘ P id rather than ⋃. *)
Definition SL_induced_repack@{o so} {X : SetoidObject@{o o}}
  (β : @TAlgebra Sets@{o so} (SL_Forget@{o so} ◯ SL_Free@{o so})
         SL_induced@{o so} X) :
  @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X.
Proof.
  unshelve refine
    (@Build_TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so}
       X (@t_alg _ _ _ _ β) (@t_id _ _ _ _ β) _).
  intro SS.
  transitivity (@t_alg _ _ _ _ β (@join _ _ SL_induced@{o so} X SS)).
  - exact (@t_action _ _ _ _ β SS).
  - apply (proper_morphism (@t_alg _ _ _ _ β)).
    exact (@Powerset_union_respects@{o} X _ SS
             (@Powerset_Prop_map_id@{o} (Powerset_Prop_obj@{o} X) SS)).
Defined.

Definition EM_induced_to_SupLat@{o so} :
  @EilenbergMoore@{so so so o} Sets@{o so}
    (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}
    ⟶ SupLat@{o so}.
Proof.
  unshelve refine
    (@Build_Functor
       (@EilenbergMoore@{so so so o} Sets@{o so}
          (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so})
       SupLat@{o so}
       (fun x => TAlgebra_SupLat@{o so} (SL_induced_repack@{o so} (projT2 x)))
       (fun x y f =>
          @Build_SupLatHom@{o}
            (TAlgebra_SupLat@{o so} (SL_induced_repack@{o so} (projT2 x)))
            (TAlgebra_SupLat@{o so} (SL_induced_repack@{o so} (projT2 y)))
            (@t_alg_hom _ _ _ _ _ _ _ f)
            (fun S => @t_alg_hom_commutes _ _ _ _ _ _ _ f S))
       _ _ _).
  - intros x y f g H a. exact (H a).
  - intros x a. reflexivity.
  - intros x y z f g a. reflexivity.
Defined.

(* The algebra round trip through the comparison, with the identity as its
   component. *)
Definition SL_comparison_counit_iso@{o so}
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}) :
  @Isomorphism
    (@EilenbergMoore@{so so so o} Sets@{o so}
       (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so})
    (fobj[EM_Comparison SL_adj@{o so} ◯ EM_induced_to_SupLat@{o so}] x) x.
Proof.
  unshelve refine
    (@Build_Isomorphism
       (@EilenbergMoore@{so so so o} Sets@{o so}
          (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so})
       (fobj[EM_Comparison SL_adj@{o so} ◯ EM_induced_to_SupLat@{o so}] x) x
       (@Build_TAlgebraHom Sets@{o so} (SL_Forget@{o so} ◯ SL_Free@{o so})
          SL_induced@{o so} (projT1 x) (projT1 x)
          (projT2 (fobj[EM_Comparison SL_adj@{o so}
                        ◯ EM_induced_to_SupLat@{o so}] x))
          (projT2 x)
          (@setoid_morphism_id@{o o o} (projT1 x)) _)
       (@Build_TAlgebraHom Sets@{o so} (SL_Forget@{o so} ◯ SL_Free@{o so})
          SL_induced@{o so} (projT1 x) (projT1 x)
          (projT2 x)
          (projT2 (fobj[EM_Comparison SL_adj@{o so}
                        ◯ EM_induced_to_SupLat@{o so}] x))
          (@setoid_morphism_id@{o o o} (projT1 x)) _) _ _).
  - intro S. reflexivity.
  - intro S. apply (proper_morphism (@t_alg _ _ _ _ (projT2 x))).
    symmetry.
    transitivity (Powerset_Prop_map@{o}
                    (@setoid_morphism_id@{o o o} (projT1 x)) S).
    + exact (@Powerset_Prop_map_id@{o} (projT1 x) _).
    + exact (@Powerset_Prop_map_id@{o} (projT1 x) S).
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(* The semilattice round trip through the comparison, with the identity as
   its component. *)
Definition SL_comparison_unit_iso@{o so} (A : SupLatObject@{o}) :
  @Isomorphism SupLat@{o so}
    (fobj[EM_induced_to_SupLat@{o so} ◯ EM_Comparison SL_adj@{o so}] A) A.
Proof.
  unshelve refine
    (@Build_Isomorphism SupLat@{o so}
       (fobj[EM_induced_to_SupLat@{o so} ◯ EM_Comparison SL_adj@{o so}] A) A
       (@Build_SupLatHom@{o}
          (fobj[EM_induced_to_SupLat@{o so} ◯ EM_Comparison SL_adj@{o so}] A)
          A (@setoid_morphism_id@{o o o} (sl_set A)) _)
       (@Build_SupLatHom@{o} A
          (fobj[EM_induced_to_SupLat@{o so} ◯ EM_Comparison SL_adj@{o so}] A)
          (@setoid_morphism_id@{o o o} (sl_set A)) _) _ _).
  - intro S. reflexivity.
  - intro S. apply (proper_morphism (sl_sup A)). symmetry.
    transitivity (Powerset_Prop_map@{o}
                    (@setoid_morphism_id@{o o o} (sl_set A)) S).
    + exact (@Powerset_Prop_map_id@{o} (sl_set A) _).
    + exact (@Powerset_Prop_map_id@{o} (sl_set A) S).
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(* The comparison functor is an equivalence, with identity components both
   ways. *)
Definition SL_comparison_equivalence@{o so} :
  @EquivalenceOfCategories@{so so so so so o} SupLat@{o so}
    (@EilenbergMoore@{so so so o} Sets@{o so}
       (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so})
    (EM_Comparison SL_adj@{o so}).
Proof.
  unshelve refine
    (@Build_EquivalenceOfCategories _ _ (EM_Comparison SL_adj@{o so})
       EM_induced_to_SupLat@{o so} _ _).
  - exists (fun x => SL_comparison_counit_iso@{o so} x).
    intros x y f a. reflexivity.
  - exists (fun A => iso_sym (SL_comparison_unit_iso@{o so} A)).
    intros A B f a. reflexivity.
Defined.

Definition SL_Forget_Monadic@{o so} :
  @Monadic@{so so so so so o so so} SupLat@{o so} Sets@{o so}
    SL_Forget@{o so}.
Proof.
  exists SL_Free@{o so}.
  exists SL_adj@{o so}.
  exact SL_comparison_equivalence@{o so}.
Defined.

(* The components of both natural isomorphisms are identities, at a
   variable object. *)
Example SL_comparison_counit_component@{o so}
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}) :
  t_alg_hom[to (projT1 (@equivalence_counit _ _ _
                           SL_comparison_equivalence@{o so}) x)]
    = @setoid_morphism_id@{o o o} (projT1 x) := eq_refl.

Example SL_comparison_counit_component_from@{o so}
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}) :
  t_alg_hom[from (projT1 (@equivalence_counit _ _ _
                             SL_comparison_equivalence@{o so}) x)]
    = @setoid_morphism_id@{o o o} (projT1 x) := eq_refl.

Example SL_comparison_unit_component@{o so} (A : SupLatObject@{o}) :
  slh_map (to (projT1 (@equivalence_unit _ _ _
                         SL_comparison_equivalence@{o so}) A))
    = @setoid_morphism_id@{o o o} (sl_set A) := eq_refl.

Example SL_comparison_unit_component_from@{o so} (A : SupLatObject@{o}) :
  slh_map (from (projT1 (@equivalence_unit _ _ _
                           SL_comparison_equivalence@{o so}) A))
    = @setoid_morphism_id@{o o o} (sl_set A) := eq_refl.
