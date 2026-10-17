(** * The group-action monad G × (−) and its algebras, the G-sets *)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Monadicity.Beck.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Group.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Deloop.Functors.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Action.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.

Generalizable All Variables.

(*
 Book: Riehl, "Category Theory in Context", 2nd ed., Exercise
 nLab: https://ncatlab.org/nlab/show/action
 nLab: https://ncatlab.org/nlab/show/monadicity+theorem

   本文件给出单子相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The product M × X *)

(* The carrier of G × X, compared componentwise (Lib/Datatypes.v's
   [prod_setoid], the relation of Instance/Sets/Cartesian.v's product). *)
Definition act_prod@{o} (M : MonObject@{o o o}) (X : SetoidObject@{o o}) :
  SetoidObject@{o o} :=
  @Build_SetoidObject (carrier M * carrier X)%type prod_setoid.

(* G × f : G × X → G × Y, the identity on the first factor. *)
Definition act_prod_map@{o so} (M : MonObject@{o o o})
  {X Y : SetoidObject@{o o}} (f : X ~{Sets@{o so}}~> Y) :
  act_prod M X ~{Sets@{o so}}~> act_prod M Y.
Proof.
  unshelve refine
    (@Build_SetoidMorphism (carrier M * carrier X) prod_setoid
       (carrier M * carrier Y) prod_setoid (fun p => (fst p, f (snd p))) _).
  intros p q [Hg Hx].
  split; [ exact Hg | exact (proper_morphism f _ _ Hx) ].
Defined.

(** ** The free M-set and the forgetful functor *)

(* The free M-set on X: M × X with M acting on the left factor,
   g · (h, x) = (g h, x). *)
Definition FreeAct@{o} {M : MonObject@{o o o}} (X : SetoidObject@{o o}) :
  MSetoidAction@{o o o o o o o o} M.
Proof.
  unshelve refine
    (@Build_MSetoidAction M (act_prod M X)
       (fun g p => (mon_op g (fst p), snd p)) _ _ _).
  - intros g g' Hg p q [H1 H2].
    split; simpl;
      [ exact (mon_op_respects M g g' Hg (fst p) (fst q) H1) | exact H2 ].
  - intros [g x].
    split; simpl; [ exact (mon_op_unit_l g) | reflexivity ].
  - intros g h [k x].
    split; simpl; [ exact (mon_op_assoc_sym M g h k) | reflexivity ].
Defined.

(* U : MSet M ⟶ Sets forgets the action. *)
Definition MSet_Forget@{o so} (M : MonObject@{o o o}) :
  MSet@{so so o o o o o o} M ⟶ Sets@{o so}.
Proof.
  unshelve refine
    (@Build_Functor (MSet@{so so o o o o o o} M) Sets@{o so}
       (fun A => act_setoid A) (fun A B h => equiv_map h) _ _ _).
  - intros A B h h' Hh. exact Hh.
  - intros A a. reflexivity.
  - intros A B C f g a. reflexivity.
Defined.

(* F : Sets ⟶ MSet M sends X to the free M-set M × X. *)
Definition MSet_Free@{o so} (M : MonObject@{o o o}) :
  Sets@{o so} ⟶ MSet@{so so o o o o o o} M.
Proof.
  unshelve refine
    (@Build_Functor Sets@{o so} (MSet@{so so o o o o o o} M)
       (fun X => @FreeAct M X)
       (fun X Y f => @Build_Equivariant M (@FreeAct M X) (@FreeAct M Y)
                       (act_prod_map@{o so} M f) _)
       _ _ _).
  - intros g p. split; reflexivity.
  - intros X Y f f' Hf p. split; [ reflexivity | exact (Hf (snd p)) ].
  - intros X p. split; reflexivity.
  - intros X Y Z f g p. split; reflexivity.
Defined.

(** ** The free/forgetful adjunction *)

(* A map ψ : X → U A extends to the equivariant (g, x) ↦ g · ψ x. *)
Definition MSet_extend@{o so} {M : MonObject@{o o o}}
  {X : SetoidObject@{o o}} {A : MSetoidAction@{o o o o o o o o} M}
  (ψ : X ~{Sets@{o so}}~> act_setoid A) :
  fobj[MSet_Free@{o so} M] X ~{MSet@{so so o o o o o o} M}~> A.
Proof.
  unshelve refine
    (@Build_Equivariant M (@FreeAct M X) A
       (@Build_SetoidMorphism (carrier M * carrier X) prod_setoid
          (carrier (act_setoid A)) _
          (fun p => act A (fst p) (ψ (snd p))) _) _).
  - intros p q [Hg Hx].
    exact (act_respects A _ _ Hg _ _ (proper_morphism ψ _ _ Hx)).
  - intros g [h x]; simpl. apply act_op.
Defined.

(* An equivariant φ : F X → A restricts to x ↦ φ (e, x). *)
Definition MSet_restrict@{o so} {M : MonObject@{o o o}}
  {X : SetoidObject@{o o}} {A : MSetoidAction@{o o o o o o o o} M}
  (φ : fobj[MSet_Free@{o so} M] X ~{MSet@{so so o o o o o o} M}~> A) :
  X ~{Sets@{o so}}~> fobj[MSet_Forget@{o so} M] A.
Proof.
  unshelve refine
    (@Build_SetoidMorphism X _ (act_setoid A) _
       (fun x => equiv_map φ (mon_unit, x)) _).
  intros x y Hxy. apply (proper_morphism (equiv_map φ)).
  split; [ reflexivity | exact Hxy ].
Defined.

Definition MSet_adj_iso@{o so} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) (A : MSetoidAction@{o o o o o o o o} M) :
  @Isomorphism Sets@{o so}
    (@Build_SetoidObject
       (@hom (MSet@{so so o o o o o o} M) (fobj[MSet_Free@{o so} M] X) A)
       (@homset (MSet@{so so o o o o o o} M) (fobj[MSet_Free@{o so} M] X) A))
    (@Build_SetoidObject
       (@hom Sets@{o so} X (fobj[MSet_Forget@{o so} M] A))
       (@homset Sets@{o so} X (fobj[MSet_Forget@{o so} M] A))).
Proof.
  unshelve refine
    (@Build_Isomorphism Sets@{o so}
       (@Build_SetoidObject
          (@hom (MSet@{so so o o o o o o} M) (fobj[MSet_Free@{o so} M] X) A)
          (@homset (MSet@{so so o o o o o o} M)
             (fobj[MSet_Free@{o so} M] X) A))
       (@Build_SetoidObject
          (@hom Sets@{o so} X (fobj[MSet_Forget@{o so} M] A))
          (@homset Sets@{o so} X (fobj[MSet_Forget@{o so} M] A)))
       (@Build_SetoidMorphism
          (@hom (MSet@{so so o o o o o o} M) (fobj[MSet_Free@{o so} M] X) A)
          (@homset (MSet@{so so o o o o o o} M)
             (fobj[MSet_Free@{o so} M] X) A)
          (@hom Sets@{o so} X (fobj[MSet_Forget@{o so} M] A))
          (@homset Sets@{o so} X (fobj[MSet_Forget@{o so} M] A))
          (fun φ => @MSet_restrict M X A φ) _)
       (@Build_SetoidMorphism
          (@hom Sets@{o so} X (fobj[MSet_Forget@{o so} M] A))
          (@homset Sets@{o so} X (fobj[MSet_Forget@{o so} M] A))
          (@hom (MSet@{so so o o o o o o} M) (fobj[MSet_Free@{o so} M] X) A)
          (@homset (MSet@{so so o o o o o o} M)
             (fobj[MSet_Free@{o so} M] X) A)
          (fun ψ => @MSet_extend M X A ψ) _) _ _).
  - intros φ φ' Hφ x. exact (Hφ (mon_unit, x)).
  - intros ψ ψ' Hψ [g x]; simpl.
    apply act_respects; [ reflexivity | exact (Hψ x) ].
  - intros ψ x; simpl. apply act_unit.
  - intros φ [g x]; simpl.
    transitivity (equiv_map φ (act (@FreeAct M X) g (mon_unit, x))).
    + symmetry. exact (equivar φ g (mon_unit, x)).
    + apply (proper_morphism (equiv_map φ)).
      split; [ exact (mon_op_unit_r g) | reflexivity ].
Defined.

(* Riehl's left adjoint X ↦ G × X, over any monoid. *)
Definition MSet_adj@{o so} (M : MonObject@{o o o}) :
  @Adjunction@{so o o so o o o o so o so} (MSet@{so so o o o o o o} M)
    Sets@{o so} (MSet_Free@{o so} M) (MSet_Forget@{o so} M).
Proof.
  unshelve refine
    (@Build_Adjunction' (MSet@{so so o o o o o o} M) Sets@{o so}
       (MSet_Free@{o so} M) (MSet_Forget@{o so} M)
       (fun X A => MSet_adj_iso M X A) _ _).
  - intros X Y A f g x; simpl. reflexivity.
  - intros X A B f g x; simpl. reflexivity.
Defined.

(** ** Mac Lane's monad G × (−) *)

Definition ActF@{o so} (M : MonObject@{o o o}) :
  Sets@{o so} ⟶ Sets@{o so} :=
  MSet_Forget@{o so} M ◯ MSet_Free@{o so} M.

Definition ActMonad@{o so} (M : MonObject@{o o o}) :
  @Monad Sets@{o so} (ActF@{o so} M) :=
  Adjunction_Induced_Monad (MSet_adj@{o so} M).

(* Mac Lane's formulas, read back on the nose: T X = G × X, η x = (u, x)
   and μ (g₁, (g₂, x)) = (g₁ g₂, x). *)
Example ActF_obj@{o so} (M : MonObject@{o o o}) (X : SetoidObject@{o o}) :
  fobj[ActF@{o so} M] X = act_prod M X := eq_refl.

Example ActF_map@{o so} (M : MonObject@{o o o}) (X Y : SetoidObject@{o o})
  (f : X ~{Sets@{o so}}~> Y) :
  fmap[ActF@{o so} M] f = act_prod_map M f := eq_refl.

Example ActMonad_ret@{o so} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) (x : carrier X) :
  (@ret _ _ (ActMonad@{o so} M) X) x = (mon_unit, x) := eq_refl.

Example ActMonad_join@{o so} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) (g1 g2 : carrier M) (x : carrier X) :
  (@join _ _ (ActMonad@{o so} M) X) (g1, (g2, x)) = (mon_op g1 g2, x) :=
  eq_refl.

(* The point and the triple above are Mac Lane's notation.  η holds as a
   function too, and so does μ, which is stronger than the triple, since
   Coq's [prod] has no eta. *)
Example ActMonad_ret_fun@{o so} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) :
  (fun x : carrier X => (@ret _ _ (ActMonad@{o so} M) X) x)
  = (fun x => (mon_unit, x)) := eq_refl.

Example ActMonad_join_fun@{o so} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) :
  (fun p => (@join _ _ (ActMonad@{o so} M) X) p)
  = (fun p : carrier M * (carrier M * carrier X) =>
       (mon_op (fst p) (fst (snd p)), snd (snd p))) := eq_refl.

(** ** Algebras are actions *)

(* Mac Lane: a T-algebra h : G × X → X is an action, g · x := h (g, x). *)
Definition EM_act@{o so} {M : MonObject@{o o o}}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
         (ActMonad@{o so} M)) :
  MSetoidAction@{o o o o o o o o} M.
Proof.
  unshelve refine
    (@Build_MSetoidAction M (`1 x) (fun g a => t_alg[`2 x] (g, a)) _ _ _).
  - intros g g' Hg a a' Ha.
    apply (proper_morphism (t_alg[`2 x])). split; assumption.
  - intros a. exact (@t_id _ _ _ _ (`2 x) a).
  - intros g h a. symmetry. exact (@t_action _ _ _ _ (`2 x) (g, (h, a))).
Defined.

Definition EM_to_MSet@{o so} (M : MonObject@{o o o}) :
  @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M) (ActMonad@{o so} M)
    ⟶ MSet@{so so o o o o o o} M.
Proof.
  unshelve refine
    (@Build_Functor
       (@EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
          (ActMonad@{o so} M))
       (MSet@{so so o o o o o o} M)
       (fun x => @EM_act M x)
       (fun x y f => @Build_Equivariant M (@EM_act M x) (@EM_act M y)
                       t_alg_hom[f]
                       (fun g a => @t_alg_hom_commutes _ _ _ _ _ _ _ f (g, a)))
       _ _ _).
  - intros x y f f' Hf a. exact (Hf a).
  - intros x a. reflexivity.
  - intros x y z f g a. reflexivity.
Defined.

Definition MSet_counit_iso@{o so} {M : MonObject@{o o o}}
  (B : MSetoidAction@{o o o o o o o o} M) :
  @Isomorphism (MSet@{so so o o o o o o} M)
    (fobj[EM_to_MSet@{o so} M ◯ EM_Comparison (MSet_adj@{o so} M)] B) B.
Proof.
  unshelve refine
    (@Build_Isomorphism (MSet@{so so o o o o o o} M) _ _
       (@Build_Equivariant M
          (fobj[EM_to_MSet@{o so} M ◯ EM_Comparison (MSet_adj@{o so} M)] B) B
          (@setoid_morphism_id (act_setoid B)) _)
       (@Build_Equivariant M B
          (fobj[EM_to_MSet@{o so} M ◯ EM_Comparison (MSet_adj@{o so} M)] B)
          (@setoid_morphism_id (act_setoid B)) _) _ _).
  - intros g a. reflexivity.
  - intros g a. reflexivity.
  - intros a. reflexivity.
  - intros a. reflexivity.
Defined.

Definition MSet_unit_iso@{o so} {M : MonObject@{o o o}}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
         (ActMonad@{o so} M)) :
  @Isomorphism
    (@EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
       (ActMonad@{o so} M))
    (fobj[EM_Comparison (MSet_adj@{o so} M) ◯ EM_to_MSet@{o so} M] x) x.
Proof.
  destruct x as [X α].
  unshelve refine
    (@Build_Isomorphism
       (@EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
          (ActMonad@{o so} M))
       (fobj[EM_Comparison (MSet_adj@{o so} M) ◯ EM_to_MSet@{o so} M] (X; α))
       (X; α)
       (@Build_TAlgebraHom Sets@{o so} (ActF@{o so} M) (ActMonad@{o so} M) X X
          (`2 (fobj[EM_Comparison (MSet_adj@{o so} M)
                    ◯ EM_to_MSet@{o so} M] (X; α))) α
          (@setoid_morphism_id X) _)
       (@Build_TAlgebraHom Sets@{o so} (ActF@{o so} M) (ActMonad@{o so} M) X X
          α (`2 (fobj[EM_Comparison (MSet_adj@{o so} M)
                      ◯ EM_to_MSet@{o so} M] (X; α)))
          (@setoid_morphism_id X) _) _ _).
  - intros [g a]. reflexivity.
  - intros [g a]. reflexivity.
  - intros a. reflexivity.
  - intros a. reflexivity.
Defined.

(* The direct route: [EM_to_MSet] is a quasi-inverse of the comparison
   functor, with identity components both ways. *)
Definition MSet_comparison_equivalence@{o so} (M : MonObject@{o o o}) :
  EquivalenceOfCategories (EM_Comparison (MSet_adj@{o so} M)).
Proof.
  unshelve refine
    (@Build_EquivalenceOfCategories _ _ (EM_Comparison (MSet_adj@{o so} M))
       (EM_to_MSet@{o so} M) _ _).
  - exists (fun x => MSet_unit_iso x).
    intros [X α] [Y β] f a; simpl. reflexivity.
  - exists (fun B => iso_sym (MSet_counit_iso B)).
    intros B C h a; simpl. reflexivity.
Defined.

Definition MSet_Forget_Monadic_direct@{o so} (M : MonObject@{o o o}) :
  @Monadic@{so so so so so o so so} (MSet@{so so o o o o o o} M) Sets@{o so}
    (MSet_Forget@{o so} M).
Proof.
  exists (MSet_Free@{o so} M).
  exists (MSet_adj@{o so} M).
  exact (MSet_comparison_equivalence@{o so} M).
Defined.

(* G-sets ARE the algebras: an isomorphism in Cat whose [to] leg is the
   comparison functor itself. *)
Definition EM_MSet_iso@{o so c} (M : MonObject@{o o o}) :
  @Isomorphism Cat@{c so so so o}
    (MSet@{so so o o o o o o} M)
    (@EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
       (ActMonad@{o so} M)) :=
  Equivalence_to_Cat_Iso (MSet_comparison_equivalence@{o so} M).

Example EM_MSet_iso_to@{o so c} (M : MonObject@{o o o}) :
  to (EM_MSet_iso@{o so c} M) = EM_Comparison (MSet_adj@{o so} M) := eq_refl.

(* Its [from] leg is the direct quasi-inverse itself. *)
Example EM_MSet_iso_from@{o so c} (M : MonObject@{o o o}) :
  from (EM_MSet_iso@{o so c} M) = EM_to_MSet@{o so} M := eq_refl.

Example EM_act_is_action@{o so} {M : MonObject@{o o o}}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
         (ActMonad@{o so} M)) (g : carrier M) (a : carrier (`1 x)) :
  act (EM_act@{o so} x) g a = t_alg[`2 x] (g, a) := eq_refl.

Example comparison_alg_is_action@{o so} {M : MonObject@{o o o}}
  (A : MSetoidAction@{o o o o o o o o} M) (g : carrier M)
  (a : carrier (act_setoid A)) :
  t_alg[`2 (fobj[EM_Comparison (MSet_adj@{o so} M)] A)] (g, a) = act A g a :=
  eq_refl.

(* The same, as a function of the pair. *)
Example comparison_alg_fun@{o so} {M : MonObject@{o o o}}
  (A : MSetoidAction@{o o o o o o o o} M) :
  (fun p => t_alg[`2 (fobj[EM_Comparison (MSet_adj@{o so} M)] A)] p)
  = (fun p : carrier M * carrier (act_setoid A) => act A (fst p) (snd p)) :=
  eq_refl.

(** ** Riehl's route: the forgetful functor creates U-split coequalizers *)

(* Absorption through a split coequalizer: a map h out of B that
   coforks the pair satisfies h (s (e y)) ≈ h y. *)
Lemma split_absorb@{o so} {M : MonObject@{o o o}}
  {A B : MSetoidAction@{o o o o o o o o} M}
  (p q : A ~{MSet@{so so o o o o o o} M}~> B)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[MSet_Forget@{o so} M] p) (fmap[MSet_Forget@{o so} M] q))
  {W : SetoidObject@{o o}} (h : act_setoid B ~{Sets@{o so}}~> W)
  (Hh : ∀ x, h (equiv_map p x) ≈ h (equiv_map q x))
  (y : carrier (act_setoid B)) :
  h (scoeq_s S (scoeq_e S y)) ≈ h y.
Proof.
  pose proof (scoeq_law4 S y) as L4; simpl in L4.
  pose proof (scoeq_law3 S y) as L3; simpl in L3.
  transitivity (h (equiv_map q (scoeq_t S y))).
  - apply (proper_morphism h). symmetry. exact L4.
  - transitivity (h (equiv_map p (scoeq_t S y))).
    + symmetry. apply Hh.
    + apply (proper_morphism h). exact L3.
Qed.

(* The created action on the split quotient Z: g · z := e (g · s z). *)
Definition created_act@{o so} {M : MonObject@{o o o}}
  {A B : MSetoidAction@{o o o o o o o o} M}
  (p q : A ~{MSet@{so so o o o o o o} M}~> B)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[MSet_Forget@{o so} M] p) (fmap[MSet_Forget@{o so} M] q)) :
  carrier M → carrier (scoeq_obj S) → carrier (scoeq_obj S) :=
  fun g z => scoeq_e S (act B g (scoeq_s S z)).

(* e ∘ (g · −) coforks the pair, so it absorbs s ∘ e. *)
Lemma created_absorb@{o so} {M : MonObject@{o o o}}
  {A B : MSetoidAction@{o o o o o o o o} M}
  (p q : A ~{MSet@{so so o o o o o o} M}~> B)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[MSet_Forget@{o so} M] p) (fmap[MSet_Forget@{o so} M] q))
  (g : carrier M) (y : carrier (act_setoid B)) :
  scoeq_e S (act B g (scoeq_s S (scoeq_e S y))) ≈ scoeq_e S (act B g y).
Proof.
  pose proof (scoeq_law4 S y) as L4; simpl in L4.
  pose proof (scoeq_law3 S y) as L3; simpl in L3.
  pose proof (scoeq_law1 S (act A g (scoeq_t S y))) as L1; simpl in L1.
  transitivity (scoeq_e S (act B g (equiv_map q (scoeq_t S y)))).
  - apply (proper_morphism (scoeq_e S)).
    apply act_respects; [ reflexivity | symmetry; exact L4 ].
  - transitivity (scoeq_e S (equiv_map q (act A g (scoeq_t S y)))).
    + apply (proper_morphism (scoeq_e S)). symmetry. apply equivar.
    + transitivity (scoeq_e S (equiv_map p (act A g (scoeq_t S y)))).
      * symmetry. exact L1.
      * transitivity (scoeq_e S (act B g (equiv_map p (scoeq_t S y)))).
        -- apply (proper_morphism (scoeq_e S)). apply equivar.
        -- apply (proper_morphism (scoeq_e S)).
           apply act_respects; [ reflexivity | exact L3 ].
Qed.

Definition CreatedAct@{o so} {M : MonObject@{o o o}}
  {A B : MSetoidAction@{o o o o o o o o} M}
  (p q : A ~{MSet@{so so o o o o o o} M}~> B)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[MSet_Forget@{o so} M] p) (fmap[MSet_Forget@{o so} M] q)) :
  MSetoidAction@{o o o o o o o o} M.
Proof.
  unshelve refine
    (@Build_MSetoidAction M (scoeq_obj S) (created_act@{o so} p q S) _ _ _).
  - intros g g' Hg z z' Hz. unfold created_act.
    apply (proper_morphism (scoeq_e S)).
    apply act_respects;
      [ exact Hg | apply (proper_morphism (scoeq_s S)); exact Hz ].
  - intros z. unfold created_act.
    pose proof (scoeq_law2 S z) as L2; simpl in L2.
    transitivity (scoeq_e S (scoeq_s S z)); [ | exact L2 ].
    apply (proper_morphism (scoeq_e S)). apply act_unit.
  - intros g h z. unfold created_act.
    transitivity (scoeq_e S (act B g (act B h (scoeq_s S z)))).
    + apply (proper_morphism (scoeq_e S)). apply act_op.
    + symmetry. apply created_absorb.
Defined.

Definition CreatedE@{o so} {M : MonObject@{o o o}}
  {A B : MSetoidAction@{o o o o o o o o} M}
  (p q : A ~{MSet@{so so o o o o o o} M}~> B)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[MSet_Forget@{o so} M] p) (fmap[MSet_Forget@{o so} M] q)) :
  B ~{MSet@{so so o o o o o o} M}~> CreatedAct@{o so} p q S.
Proof.
  unshelve refine
    (@Build_Equivariant M B (CreatedAct@{o so} p q S) (scoeq_e S) _).
  intros g y. simpl. unfold created_act. symmetry. apply created_absorb.
Defined.

Definition CreatedE_is_coeq@{o so} {M : MonObject@{o o o}}
  {A B : MSetoidAction@{o o o o o o o o} M}
  (p q : A ~{MSet@{so so o o o o o o} M}~> B)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[MSet_Forget@{o so} M] p) (fmap[MSet_Forget@{o so} M] q)) :
  @IsCoequalizer (MSet@{so so o o o o o o} M) A B p q
    (CreatedAct@{o so} p q S) (CreatedE@{o so} p q S).
Proof.
  unshelve refine (@Build_IsCoequalizer _ _ _ _ _ _ _ _ _).
  - intros x. exact (scoeq_law1 S x).
  - intros W h Hh.
    unshelve eapply Build_Unique.
    + unshelve refine
        (@Build_Equivariant M (CreatedAct@{o so} p q S) W
           (@setoid_morphism_compose _ _ _ (equiv_map h) (scoeq_s S)) _).
      intros g z; simpl. unfold created_act.
      transitivity (equiv_map h (act B g (scoeq_s S z))).
      * apply (split_absorb p q S (equiv_map h) Hh).
      * apply equivar.
    + intros y; simpl. apply (split_absorb p q S (equiv_map h) Hh).
    + intros v Hv z; simpl.
      pose proof (scoeq_law2 S z) as L2; simpl in L2.
      transitivity (equiv_map v (scoeq_e S (scoeq_s S z))).
      * symmetry. exact (Hv (scoeq_s S z)).
      * apply (proper_morphism (equiv_map v)). exact L2.
Defined.

(* The reflection clause: a cofork lying over the splitting up to a
   compatible isomorphism downstairs is a coequalizer upstairs. *)
Definition Reflected_is_coeq@{o so} {M : MonObject@{o o o}}
  {A B : MSetoidAction@{o o o o o o o o} M}
  (p q : A ~{MSet@{so so o o o o o o} M}~> B)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[MSet_Forget@{o so} M] p) (fmap[MSet_Forget@{o so} M] q))
  (Q : MSetoidAction@{o o o o o o o o} M)
  (e : B ~{MSet@{so so o o o o o o} M}~> Q)
  (He : e ∘ p ≈ e ∘ q)
  (i : @Isomorphism Sets@{o so} (fobj[MSet_Forget@{o so} M] Q) (scoeq_obj S))
  (Hi : to i ∘ fmap[MSet_Forget@{o so} M] e ≈ scoeq_e S) :
  @IsCoequalizer (MSet@{so so o o o o o o} M) A B p q Q e.
Proof.
  (* w ≈ e (s (i w)) *)
  assert (L0 : ∀ w, w ≈ equiv_map e (scoeq_s S (to i w))).
  { intros w.
    pose proof (Hi (scoeq_s S (to i w))) as H1; simpl in H1.
    pose proof (scoeq_law2 S (to i w)) as L2; simpl in L2.
    pose proof (iso_from_to i w) as FT; simpl in FT.
    pose proof (iso_from_to i (equiv_map e (scoeq_s S (to i w)))) as FT';
      simpl in FT'.
    transitivity (from i (to i w)); [ symmetry; exact FT | ].
    transitivity (from i (to i (equiv_map e (scoeq_s S (to i w)))));
      [ | exact FT' ].
    apply (proper_morphism (from i)).
    symmetry.
    transitivity (scoeq_e S (scoeq_s S (to i w))); [ exact H1 | exact L2 ]. }
  unshelve refine (@Build_IsCoequalizer _ _ _ _ _ _ _ _ _).
  - exact He.
  - intros W h Hh.
    unshelve eapply Build_Unique.
    + unshelve refine
        (@Build_Equivariant M Q W
           (@setoid_morphism_compose _ _ _
              (@setoid_morphism_compose _ _ _ (equiv_map h) (scoeq_s S))
              (to i)) _).
      intros g w; simpl.
      transitivity
        (equiv_map h (scoeq_s S (to i (act Q g
           (equiv_map e (scoeq_s S (to i w))))))).
      * apply (proper_morphism (equiv_map h)).
        apply (proper_morphism (scoeq_s S)).
        apply (proper_morphism (to i)).
        apply act_respects; [ reflexivity | exact (L0 w) ].
      * transitivity
          (equiv_map h (scoeq_s S (to i (equiv_map e
             (act B g (scoeq_s S (to i w))))))).
        -- apply (proper_morphism (equiv_map h)).
           apply (proper_morphism (scoeq_s S)).
           apply (proper_morphism (to i)). symmetry. apply equivar.
        -- transitivity
             (equiv_map h (scoeq_s S (scoeq_e S
                (act B g (scoeq_s S (to i w)))))).
           ++ apply (proper_morphism (equiv_map h)).
              apply (proper_morphism (scoeq_s S)).
              exact (Hi _).
           ++ transitivity (equiv_map h (act B g (scoeq_s S (to i w)))).
              ** apply (split_absorb p q S (equiv_map h) Hh).
              ** apply equivar.
    + intros y; simpl.
      transitivity (equiv_map h (scoeq_s S (scoeq_e S y))).
      * apply (proper_morphism (equiv_map h)).
        apply (proper_morphism (scoeq_s S)).
        exact (Hi y).
      * apply (split_absorb p q S (equiv_map h) Hh).
    + intros v Hv w; simpl.
      transitivity (equiv_map v (equiv_map e (scoeq_s S (to i w)))).
      * symmetry. exact (Hv (scoeq_s S (to i w))).
      * apply (proper_morphism (equiv_map v)). symmetry. exact (L0 w).
Defined.

Definition MSet_Forget_creates@{o so} (M : MonObject@{o o o}) :
  CreatesUSplitCoequalizers (MSet_Forget@{o so} M).
Proof.
  unshelve refine (@Build_CreatesUSplitCoequalizers _ _ _ _ _).
  - intros A B p q S.
    exists (CreatedAct@{o so} p q S).
    exists (CreatedE@{o so} p q S).
    split.
    + exact (CreatedE_is_coeq@{o so} p q S).
    + exists (@iso_id Sets@{o so} (scoeq_obj S)).
      intros y; simpl. reflexivity.
  - intros A B p q S Q e He i Hi.
    exact (Reflected_is_coeq@{o so} p q S Q e He i Hi).
Defined.

(* The lift chosen is on the nose: the created M-set has carrier Z and
   action g · z = e (g · s z), its coequalizing arrow is e, and the
   comparison isomorphism is the identity. *)
Example mset_created_carrier@{o so} {M : MonObject@{o o o}}
  {A B : MSetoidAction@{o o o o o o o o} M}
  (p q : A ~{MSet@{so so o o o o o o} M}~> B)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[MSet_Forget@{o so} M] p) (fmap[MSet_Forget@{o so} M] q)) :
  act_setoid
    (`1 (@create_coeq _ _ _ (MSet_Forget_creates@{o so} M) A B p q S))
  = scoeq_obj S := eq_refl.

Example mset_created_action@{o so} {M : MonObject@{o o o}}
  {A B : MSetoidAction@{o o o o o o o o} M}
  (p q : A ~{MSet@{so so o o o o o o} M}~> B)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[MSet_Forget@{o so} M] p) (fmap[MSet_Forget@{o so} M] q))
  (g : carrier M) (z : carrier (scoeq_obj S)) :
  act (`1 (@create_coeq _ _ _ (MSet_Forget_creates@{o so} M) A B p q S)) g z
  = scoeq_e S (act B g (scoeq_s S z)) := eq_refl.

Example mset_created_arrow@{o so} {M : MonObject@{o o o}}
  {A B : MSetoidAction@{o o o o o o o o} M}
  (p q : A ~{MSet@{so so o o o o o o} M}~> B)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[MSet_Forget@{o so} M] p) (fmap[MSet_Forget@{o so} M] q)) :
  equiv_map
    (`1 (`2 (@create_coeq _ _ _ (MSet_Forget_creates@{o so} M) A B p q S)))
  = scoeq_e S := eq_refl.

Example mset_created_iso@{o so} {M : MonObject@{o o o}}
  {A B : MSetoidAction@{o o o o o o o o} M}
  (p q : A ~{MSet@{so so o o o o o o} M}~> B)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[MSet_Forget@{o so} M] p) (fmap[MSet_Forget@{o so} M] q)) :
  `1 (snd (`2 (`2 (@create_coeq _ _ _ (MSet_Forget_creates@{o so} M)
                     A B p q S))))
  = @iso_id Sets@{o so} (scoeq_obj S) := eq_refl.

(** ** Riehl's Exercise 5.5.iv by the monadicity theorem *)

Definition MSet_beck_equivalence@{o so} (M : MonObject@{o o o}) :
  EquivalenceOfCategories (EM_Comparison (MSet_adj@{o so} M)) :=
  beck_monadicity (MSet_adj@{o so} M) (MSet_Forget_creates@{o so} M).

Definition MSet_Forget_Monadic@{o so} (M : MonObject@{o o o}) :
  @Monadic@{so so so so so o so so} (MSet@{so so o o o o o o} M) Sets@{o so}
    (MSet_Forget@{o so} M).
Proof.
  exists (MSet_Free@{o so} M).
  exists (MSet_adj@{o so} M).
  exact (MSet_beck_equivalence@{o so} M).
Defined.

(* A bijective equivariant map is an isomorphism of M-sets. *)
Definition MSet_Forget_reflects@{o so} (M : MonObject@{o o o}) :
  ReflectsIsos (MSet_Forget@{o so} M) :=
  creates_split_reflects_isos _ (MSet_Forget_creates@{o so} M).

(** ** The two routes are equivalences of the same functor *)

Definition EM_MSet_iso_beck@{o so c} (M : MonObject@{o o o}) :
  @Isomorphism Cat@{c so so so o}
    (MSet@{so so o o o o o o} M)
    (@EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
       (ActMonad@{o so} M)) :=
  Equivalence_to_Cat_Iso (MSet_beck_equivalence@{o so} M).

Example EM_MSet_iso_beck_to@{o so c} (M : MonObject@{o o o}) :
  to (EM_MSet_iso_beck@{o so c} M) = EM_Comparison (MSet_adj@{o so} M) :=
  eq_refl.

Example beck_direct_to@{o so c} (M : MonObject@{o o o}) :
  to (EM_MSet_iso_beck@{o so c} M) = to (EM_MSet_iso@{o so c} M) := eq_refl.

(* Beck's quasi-inverse keeps the carrier and acts through η: its action
   at g is the structure map at (g u, z). *)
Example beck_carrier@{o so} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
         (ActMonad@{o so} M)) :
  act_setoid (fobj[@quasi_inverse _ _ _ (MSet_beck_equivalence@{o so} M)] x)
  = `1 x := eq_refl.

Example beck_act@{o so} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
         (ActMonad@{o so} M)) (g : carrier M) (z : carrier (`1 x)) :
  act (fobj[@quasi_inverse _ _ _ (MSet_beck_equivalence@{o so} M)] x) g z
  = t_alg[`2 x] (mon_op g mon_unit, z) := eq_refl.

Definition beck_vs_direct_iso@{o so} {M : MonObject@{o o o}}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
         (ActMonad@{o so} M)) :
  @Isomorphism (MSet@{so so o o o o o o} M)
    (fobj[@quasi_inverse _ _ _ (MSet_beck_equivalence@{o so} M)] x)
    (fobj[EM_to_MSet@{o so} M] x).
Proof.
  unshelve refine
    (@Build_Isomorphism (MSet@{so so o o o o o o} M) _ _
       (@Build_Equivariant M
          (fobj[@quasi_inverse _ _ _ (MSet_beck_equivalence@{o so} M)] x)
          (fobj[EM_to_MSet@{o so} M] x) (@setoid_morphism_id (`1 x)) _)
       (@Build_Equivariant M (fobj[EM_to_MSet@{o so} M] x)
          (fobj[@quasi_inverse _ _ _ (MSet_beck_equivalence@{o so} M)] x)
          (@setoid_morphism_id (`1 x)) _) _ _).
  - intros g z; simpl. apply (proper_morphism (t_alg[`2 x])).
    split; [ exact (mon_op_unit_r g) | reflexivity ].
  - intros g z; simpl. apply (proper_morphism (t_alg[`2 x])).
    split; [ symmetry; exact (mon_op_unit_r g) | reflexivity ].
  - intros z. reflexivity.
  - intros z. reflexivity.
Defined.

Definition beck_vs_direct@{o so} (M : MonObject@{o o o}) :
  @quasi_inverse _ _ _ (MSet_beck_equivalence@{o so} M) ≈ EM_to_MSet@{o so} M.
Proof.
  exists (fun x => beck_vs_direct_iso x).
  intros x y f z; simpl.
  exact (@t_id _ _ _ _ (`2 y) (t_alg_hom[f] z)).
Defined.

(** ** Riehl's Set^{BG} *)

(* Instance/Fun/Action.v's [MSet_Fun_equiv] followed by [EM_MSet_iso]:
   the functor category [Deloop M, Sets] is isomorphic in Cat to the
   Eilenberg–Moore category of G × (−). *)
Definition Fun_EM_iso@{o so c} (M : MonObject@{o o o}) :
  @Isomorphism Cat@{c so so so o}
    ([Deloop@{o o} M, Sets@{o so}])
    (@EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
       (ActMonad@{o so} M)) :=
  @iso_compose@{c so so c} Cat@{c so so so o} _ _ _
    (EM_MSet_iso@{o so c} M) (MSet_Fun_equiv@{so c o} M).

(** ** Groups *)

(* A group of Construction/Deloop.v reaches [MonObject] by coercion. *)
Definition GAct_Monad@{o so}
  (G : Category.Construction.Deloop.GrpObject@{o o o}) :
  @Monad Sets@{o so} (ActF@{o so} G) := ActMonad@{o so} G.

Definition GSet_Forget_Monadic@{o so}
  (G : Category.Construction.Deloop.GrpObject@{o o o}) :
  @Monadic@{so so so so so o so so} (MSet@{so so o o o o o o} G) Sets@{o so}
    (MSet_Forget@{o so} G) :=
  MSet_Forget_Monadic@{o so} G.

(* A group of Instance/Grp.v reaches it through Instance/Grp/Free.v's
   [grp_deloop_monoid]. *)
Definition GAct_Monad_Grp@{o so}
  (G : Category.Instance.Grp.GrpObject@{o o o}) :
  @Monad Sets@{o so} (ActF@{o so} (grp_deloop_monoid@{o o o} G)) :=
  ActMonad@{o so} (grp_deloop_monoid@{o o o} G).

Definition GSet_Forget_Monadic_Grp@{o so}
  (G : Category.Instance.Grp.GrpObject@{o o o}) :
  @Monadic@{so so so so so o so so}
    (MSet@{so so o o o o o o} (grp_deloop_monoid@{o o o} G)) Sets@{o so}
    (MSet_Forget@{o so} (grp_deloop_monoid@{o o o} G)) :=
  MSet_Forget_Monadic@{o so} (grp_deloop_monoid@{o o o} G).

(* A group of Structure/Group.v, internal to (Sets, ×), reaches it
   through Instance/Grp.v's [GroupObject_GrpObject], which asks that the
   carrier's ≈ be a proposition. *)
Definition GAct_Monad_GroupObject@{o so} (X : Sets@{o so})
  (PX : PropEquiv@{o o} X)
  (GO : @GroupObject@{so o so} Sets@{o so} Sets_CartesianMonoidal X) :
  @Monad Sets@{o so}
    (ActF@{o so} (grp_deloop_monoid@{o o o} (GroupObject_GrpObject X PX GO))) :=
  ActMonad@{o so} (grp_deloop_monoid@{o o o} (GroupObject_GrpObject X PX GO)).

Definition GSet_Forget_Monadic_GroupObject@{o so} (X : Sets@{o so})
  (PX : PropEquiv@{o o} X)
  (GO : @GroupObject@{so o so} Sets@{o so} Sets_CartesianMonoidal X) :
  @Monadic@{so so so so so o so so}
    (MSet@{so so o o o o o o}
       (grp_deloop_monoid@{o o o} (GroupObject_GrpObject X PX GO)))
    Sets@{o so}
    (MSet_Forget@{o so}
       (grp_deloop_monoid@{o o o} (GroupObject_GrpObject X PX GO))) :=
  MSet_Forget_Monadic@{o so}
    (grp_deloop_monoid@{o o o} (GroupObject_GrpObject X PX GO)).
