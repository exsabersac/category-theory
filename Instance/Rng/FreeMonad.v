Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Free.

Generalizable All Variables.

(** * The tensor-algebra monad T on Ab, and rings as its algebras *)

(*
 Book: Riehl, "Category Theory in Context", Example 5.5.7(ii), printed
 nLab: https://ncatlab.org/nlab/show/tensor+algebra
 nLab: https://ncatlab.org/nlab/show/algebra+over+a+monad
 nLab: https://ncatlab.org/nlab/show/monadic+functor

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section TensorAlgebraMonad.

Universes u p.

(* ------------------------------------------------------------------------ *)
(** ** T, the monad of the adjunction Ab ⇀ Rng *)

Definition TF@{+} : Ab@{u p} ⟶ Ab@{u p} := Rng_Forget_Ab ◯ FreeRngAb.

Definition TM@{+} : @Monad Ab@{u p} TF :=
  Adjunction_Induced_Monad free_rng_ab_adjunction_hom.

(* T A is the abelian group of formal ring expressions over A. *)
Example T_obj@{+} (A : Ab@{u p}) :
  fobj[TF] A = Rng_Forget_Ab (FreeRngAbObject A) := eq_refl.

Example T_carrier@{+} (A : Ab@{u p}) :
  carrier (cmon_setoid (fobj[TF] A)) = FRTerm A := eq_refl.

Example T_equiv@{+} (A : Ab@{u p}) (s t : FRTerm A) :
  @equiv _ (is_setoid (cmon_setoid (fobj[TF] A))) s t = fr_eq s t
  := eq_refl.

(* η_A is the insertion, as a map of carriers: a ↦ ⟨a⟩. *)
Example T_ret@{+} (A : Ab@{u p}) :
  cmon_map (@ret _ _ TM A) = cmon_map (free_rng_ab_insert A) := eq_refl.

Example T_ret_fun@{+} (A : Ab@{u p}) (a : carrier (cmon_setoid A)) :
  cmon_map (@ret _ _ TM A) a = fr_gen a := eq_refl.

(* μ = U ε F, the evaluation of a formal expression of formal expressions:
   it removes the outer brackets. *)
Example T_join_counit@{+} (A : Ab@{u p}) :
  @join _ _ TM A
    = fmap[Rng_Forget_Ab]
        (@counit _ _ _ _ free_rng_ab_adjunction_hom (FreeRngAb A))
  := eq_refl.

Example T_join_fun@{+} (A : Ab@{u p}) (t : FRTerm (fobj[TF] A)) :
  cmon_map (@join _ _ TM A) t = fr_eval (@id Ab@{u p} (fobj[TF] A)) t
  := eq_refl.

Example T_join_gen@{+} (A : Ab@{u p}) (t : FRTerm A) :
  cmon_map (@join _ _ TM A) (@fr_gen (fobj[TF] A) t) = t := eq_refl.

Example T_join_mul@{+} (A : Ab@{u p}) (s t : FRTerm A) :
  cmon_map (@join _ _ TM A)
    (fr_mul (@fr_gen (fobj[TF] A) s) (@fr_gen (fobj[TF] A) t))
    = fr_mul s t := eq_refl.

Example T_join_plus@{+} (A : Ab@{u p}) (s t : FRTerm A) :
  cmon_map (@join _ _ TM A)
    (fr_plus (@fr_gen (fobj[TF] A) s) (@fr_gen (fobj[TF] A) t))
    = fr_plus s t := eq_refl.

Example T_join_one@{+} (A : Ab@{u p}) :
  cmon_map (@join _ _ TM A) (@fr_one (fobj[TF] A)) = @fr_one A := eq_refl.

(* T f relabels the generators, up to ≈: the action on arrows is
   [FreeRngAb]'s, read through the universal arrows. *)
Lemma T_map_relabel@{+} {A B : Ab@{u p}} (f : A ~{Ab@{u p}}~> B)
  (t : FRTerm A) :
  cmon_map (fmap[TF] f) t ≈ fr_eval (free_rng_ab_insert B ∘[Ab@{u p}] f) t.
Proof.
  apply (free_rng_ab_extend_unique (FreeRngAb B)
           (free_rng_ab_insert B ∘[Ab@{u p}] f) (fmap[FreeRngAb] f)).
  intro a. exact (free_rng_ab_fmap_generators f a).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** An algebra is a ring *)

Definition RngAlg@{+} : Category@{u p p} :=
  @EilenbergMoore@{u u u p} Ab@{u p} TF TM.

Section Alg.

Context {A : Ab@{u p}} (α : @TAlgebra Ab@{u p} TF TM A).

Local Notation h := (cmon_map (t_alg[α])).

Lemma ralg_unit@{+} (a : carrier (cmon_setoid A)) : h (fr_gen a) ≈ a.
Proof. exact (@t_id _ _ _ _ α a). Qed.

(* The action law, with T h read as the relabelling. *)
Lemma ralg_action@{+} (t : FRTerm (fobj[TF] A)) :
  h (fr_eval (free_rng_ab_insert A ∘[Ab@{u p}] t_alg[α]) t)
    ≈ h (fr_eval (@id Ab@{u p} (fobj[TF] A)) t).
Proof.
  transitivity (h (cmon_map (fmap[TF] (t_alg[α])) t)).
  - apply (proper_morphism (cmon_map (t_alg[α]))). symmetry.
    apply T_map_relabel.
  - exact (@t_action _ _ _ _ α t).
Qed.

(* The unit h⟨⟩ = h 1 and the product a ⋆ b = h(⟨a⟩·⟨b⟩). *)
Definition ralg_one@{+} : carrier (cmon_setoid A) := h fr_one.

Definition ralg_mul@{+} (a b : carrier (cmon_setoid A)) :
  carrier (cmon_setoid A) := h (fr_mul (fr_gen a) (fr_gen b)).

(* h(s·t) ≈ h s ⋆ h t: the action law at the expression ⟨s⟩·⟨t⟩ of T T A. *)
Lemma ralg_mul_eval@{+} (s t : FRTerm A) :
  ralg_mul (h s) (h t) ≈ h (fr_mul s t).
Proof.
  exact (ralg_action (fr_mul (@fr_gen (fobj[TF] A) s)
                             (@fr_gen (fobj[TF] A) t))).
Qed.

Lemma ralg_mul_respects@{+} : Proper (equiv ==> equiv ==> equiv) ralg_mul.
Proof.
  intros a a' Ha b b' Hb. unfold ralg_mul.
  apply (proper_morphism (cmon_map (t_alg[α]))).
  exact (fre_mul (fre_gen Ha) (fre_gen Hb)).
Qed.

Lemma ralg_mul_assoc@{+} a b c :
  ralg_mul (ralg_mul a b) c ≈ ralg_mul a (ralg_mul b c).
Proof.
  transitivity (ralg_mul (ralg_mul a b) (h (fr_gen c))).
  { apply ralg_mul_respects; [ reflexivity | symmetry; apply ralg_unit ]. }
  transitivity (h (fr_mul (fr_mul (fr_gen a) (fr_gen b)) (fr_gen c))).
  { exact (ralg_mul_eval (fr_mul (fr_gen a) (fr_gen b)) (fr_gen c)). }
  transitivity (h (fr_mul (fr_gen a) (fr_mul (fr_gen b) (fr_gen c)))).
  { apply (proper_morphism (cmon_map (t_alg[α]))). apply fre_mul_assoc. }
  transitivity (ralg_mul (h (fr_gen a)) (h (fr_mul (fr_gen b) (fr_gen c)))).
  { symmetry. exact (ralg_mul_eval (fr_gen a) (fr_mul (fr_gen b) (fr_gen c))). }
  apply ralg_mul_respects; [ apply ralg_unit | reflexivity ].
Qed.

Lemma ralg_one_l@{+} a : ralg_mul ralg_one a ≈ a.
Proof.
  transitivity (ralg_mul ralg_one (h (fr_gen a))).
  { apply ralg_mul_respects; [ reflexivity | symmetry; apply ralg_unit ]. }
  transitivity (h (fr_mul fr_one (fr_gen a))).
  { exact (ralg_mul_eval fr_one (fr_gen a)). }
  transitivity (h (fr_gen a)).
  { apply (proper_morphism (cmon_map (t_alg[α]))). apply fre_mul_one_l. }
  apply ralg_unit.
Qed.

Lemma ralg_one_r@{+} a : ralg_mul a ralg_one ≈ a.
Proof.
  transitivity (ralg_mul (h (fr_gen a)) ralg_one).
  { apply ralg_mul_respects; [ symmetry; apply ralg_unit | reflexivity ]. }
  transitivity (h (fr_mul (fr_gen a) fr_one)).
  { exact (ralg_mul_eval (fr_gen a) fr_one). }
  transitivity (h (fr_gen a)).
  { apply (proper_morphism (cmon_map (t_alg[α]))). apply fre_mul_one_r. }
  apply ralg_unit.
Qed.

Lemma ralg_distr_l@{+} a b c :
  ralg_mul a (cmon_plus A b c) ≈ cmon_plus A (ralg_mul a b) (ralg_mul a c).
Proof.
  unfold ralg_mul. rewrite <- cmon_map_plus.
  apply (proper_morphism (cmon_map (t_alg[α]))).
  refine (fre_trans (fre_mul (fr_refl _) (fre_gen_plus b c)) _).
  apply fre_distr_l.
Qed.

Lemma ralg_distr_r@{+} a b c :
  ralg_mul (cmon_plus A a b) c ≈ cmon_plus A (ralg_mul a c) (ralg_mul b c).
Proof.
  unfold ralg_mul. rewrite <- cmon_map_plus.
  apply (proper_morphism (cmon_map (t_alg[α]))).
  refine (fre_trans (fre_mul (fre_gen_plus a b) (fr_refl _)) _).
  apply fre_distr_r.
Qed.

Lemma ralg_mul_zero_l@{+} a : ralg_mul (cmon_zero A) a ≈ cmon_zero A.
Proof.
  unfold ralg_mul.
  transitivity (h fr_zero); [ | exact (cmon_map_zero (t_alg[α])) ].
  apply (proper_morphism (cmon_map (t_alg[α]))).
  refine (fre_trans (fre_mul fre_gen_zero (fr_refl _)) _).
  apply fr_mul_zero_l.
Qed.

Lemma ralg_mul_zero_r@{+} a : ralg_mul a (cmon_zero A) ≈ cmon_zero A.
Proof.
  unfold ralg_mul.
  transitivity (h fr_zero); [ | exact (cmon_map_zero (t_alg[α])) ].
  apply (proper_morphism (cmon_map (t_alg[α]))).
  refine (fre_trans (fre_mul (fr_refl _) fre_gen_zero) _).
  apply fr_mul_zero_r.
Qed.

(* The ring of the algebra: A's own 0, + and −, with 1 and ⋆ above.  Its
   carrier is a set because A's is. *)
Definition ralg_rig@{+} : RigObject := {|
  rig_setoid := cmon_setoid A;
  rig_zero := cmon_zero A;
  rig_add := cmon_plus A;
  rig_one := ralg_one;
  rig_mul := ralg_mul;
  rig_add_respects := cmon_plus_respects A;
  rig_mul_respects := ralg_mul_respects;
  rig_add_assoc := cmon_plus_assoc A;
  rig_add_comm := cmon_plus_comm A;
  rig_add_zero_l := cmon_plus_zero_l A;
  rig_mul_assoc := ralg_mul_assoc;
  rig_mul_one_l := ralg_one_l;
  rig_mul_one_r := ralg_one_r;
  rig_distr_l := ralg_distr_l;
  rig_distr_r := ralg_distr_r;
  rig_mul_zero_l := ralg_mul_zero_l;
  rig_mul_zero_r := ralg_mul_zero_r;
  rig_prop := cmon_prop A
|}.

Definition ralg_ring@{+} : RingObject := {|
  ring_rig := ralg_rig;
  ring_neg := ab_neg A;
  ring_neg_respects := ab_neg_respects A;
  ring_neg_l := ab_neg_left A
|}.

(* The structure map IS the evaluation of formal expressions in the ring
   of the algebra, up to ≈: "the sum of the products". *)
Lemma ralg_fold@{+} (t : FRTerm A) :
  fr_eval (R := ralg_ring) (@id Ab@{u p} A) t ≈ h t.
Proof.
  induction t as [ a | | | t1 IH1 t2 IH2 | t IH | t1 IH1 t2 IH2 ]; simpl.
  - symmetry. apply ralg_unit.
  - symmetry. exact (cmon_map_zero (t_alg[α])).
  - reflexivity.
  - rewrite IH1, IH2. symmetry. exact (cmon_map_plus (t_alg[α]) _ _).
  - rewrite IH. symmetry. exact (ab_map_neg (t_alg[α]) _).
  - transitivity (ralg_mul (h t1) (h t2)).
    + apply ralg_mul_respects; assumption.
    + apply ralg_mul_eval.
Qed.

End Alg.

Arguments ralg_one {A} α.
Arguments ralg_mul {A} α a b.
Arguments ralg_rig {A} α.
Arguments ralg_ring {A} α.

(* ------------------------------------------------------------------------ *)
(** ** The comparison functor K and the isomorphism Rng ≅ Ab^T *)

Definition EM_rng_map@{+} {x y : RngAlg} (f : x ~{RngAlg}~> y) :
  ralg_ring (projT2 x) ~{Rng@{u p}}~> ralg_ring (projT2 y).
Proof.
  unshelve refine (@Build_RigHom (ralg_ring (projT2 x)) (ralg_ring (projT2 y))
                    (cmon_map (t_alg_hom[f])) _ _ _ _).
  - exact (cmon_map_zero (t_alg_hom[f])).
  - exact (cmon_map_plus (t_alg_hom[f])).
  - simpl. unfold ralg_one.
    transitivity (cmon_map (t_alg[projT2 y])
                    (cmon_map (fmap[TF] (t_alg_hom[f])) fr_one)).
    + exact (@t_alg_hom_commutes _ _ _ _ _ _ _ f fr_one).
    + apply (proper_morphism (cmon_map (t_alg[projT2 y]))).
      exact (rig_map_one (fmap[FreeRngAb] (t_alg_hom[f]))).
  - intros a b. simpl. unfold ralg_mul.
    transitivity (cmon_map (t_alg[projT2 y])
                    (cmon_map (fmap[TF] (t_alg_hom[f]))
                       (fr_mul (fr_gen a) (fr_gen b)))).
    + exact (@t_alg_hom_commutes _ _ _ _ _ _ _ f
               (fr_mul (fr_gen a) (fr_gen b))).
    + apply (proper_morphism (cmon_map (t_alg[projT2 y]))).
      exact (T_map_relabel (t_alg_hom[f]) (fr_mul (fr_gen a) (fr_gen b))).
Defined.

Definition EM_to_Rng@{+} : RngAlg ⟶ Rng@{u p}.
Proof.
  unshelve refine
    (@Build_Functor RngAlg Rng@{u p} (fun x => ralg_ring (projT2 x))
       (fun x y f => EM_rng_map f) _ _ _).
  - intros x y f g H. exact H.
  - intros x a. reflexivity.
  - intros x y z f g a. reflexivity.
Defined.

(* The comparison functor K : Rng → Ab^T, K R = ⟨U R, U ε_R⟩. *)
Definition Rng_K@{+} : Rng@{u p} ⟶ RngAlg :=
  EM_Comparison free_rng_ab_adjunction_hom.

(* The algebra round trip, with the identity as its component. *)
Definition Rng_EM_counit_iso@{+} (x : RngAlg) :
  @Isomorphism RngAlg (fobj[Rng_K ◯ EM_to_Rng] x) x.
Proof.
  unshelve refine
    (@Build_Isomorphism RngAlg (fobj[Rng_K ◯ EM_to_Rng] x) x
       (@Build_TAlgebraHom Ab@{u p} TF TM (projT1 x) (projT1 x)
          (projT2 (fobj[Rng_K ◯ EM_to_Rng] x)) (projT2 x)
          (@id Ab@{u p} (projT1 x)) _)
       (@Build_TAlgebraHom Ab@{u p} TF TM (projT1 x) (projT1 x)
          (projT2 x) (projT2 (fobj[Rng_K ◯ EM_to_Rng] x))
          (@id Ab@{u p} (projT1 x)) _) _ _).
  - intro t. simpl.
    transitivity (cmon_map (t_alg[projT2 x]) t);
      [ exact (ralg_fold (projT2 x) t) | ].
    apply (proper_morphism (cmon_map (t_alg[projT2 x]))).
    symmetry. exact (@fmap_id _ _ TF (projT1 x) t).
  - intro t. simpl.
    transitivity (cmon_map (t_alg[projT2 x]) (cmon_map (fmap[TF] id) t)).
    + apply (proper_morphism (cmon_map (t_alg[projT2 x]))).
      symmetry. exact (@fmap_id _ _ TF (projT1 x) t).
    + symmetry. exact (ralg_fold (projT2 x) _).
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(* The ring round trip, with the identity as its component: every
   operation comes back on the nose. *)
Definition Rng_EM_unit_iso@{+} (R : Rng@{u p}) :
  @Isomorphism Rng@{u p} (fobj[EM_to_Rng ◯ Rng_K] R) R.
Proof.
  unshelve refine
    (@Build_Isomorphism Rng@{u p} (fobj[EM_to_Rng ◯ Rng_K] R) R
       (@Build_RigHom (fobj[EM_to_Rng ◯ Rng_K] R) R
          (@setoid_morphism_id (rig_setoid R)) _ _ _ _)
       (@Build_RigHom R (fobj[EM_to_Rng ◯ Rng_K] R)
          (@setoid_morphism_id (rig_setoid R)) _ _ _ _) _ _);
    simpl; intros; reflexivity.
Defined.

(* K is an equivalence, with identity components both ways. *)
Definition Rng_EM_equivalence@{+} :
  @EquivalenceOfCategories@{u u u u u p} Rng@{u p} RngAlg Rng_K.
Proof.
  unshelve refine (@Build_EquivalenceOfCategories _ _ Rng_K EM_to_Rng _ _).
  - exists (fun x => Rng_EM_counit_iso x).
    intros x y f a. reflexivity.
  - exists (fun R => iso_sym (Rng_EM_unit_iso R)).
    intros R S f a. reflexivity.
Defined.

(* Riehl, Example 5.5.7(ii): the forgetful functor Rng → Ab is monadic. *)
Definition Rng_Forget_Ab_Monadic@{+} :
  @Monadic@{u u u u u p u u} Rng@{u p} Ab@{u p} Rng_Forget_Ab.
Proof.
  exists FreeRngAb.
  exists free_rng_ab_adjunction_hom.
  exact Rng_EM_equivalence.
Defined.

(* Mac Lane's "the comparison functor from rings to T-algebras is an
   isomorphism": Rng ≅ Ab^T in Cat, from the two component isomorphisms. *)
Definition Rng_EM_iso@{c +} :
  @Isomorphism Cat@{c u u u p} Rng@{u p} RngAlg.
Proof.
  unshelve refine
    (@Build_Isomorphism Cat@{c u u u p} Rng@{u p} RngAlg Rng_K EM_to_Rng _ _).
  - exists (fun x => Rng_EM_counit_iso x).
    intros x y f a. reflexivity.
  - exists (fun R => Rng_EM_unit_iso R).
    intros R S f a. reflexivity.
Defined.

(* ------------------------------------------------------------------------ *)
(** ** Commuting with the forgetful functors *)

Definition RngAlg_Forget@{+} : RngAlg ⟶ Ab@{u p} :=
  @EM_Forget Ab@{u p} TF TM.

Theorem Rng_K_Forget@{+} : RngAlg_Forget ◯ Rng_K ≈ Rng_Forget_Ab.
Proof. exact (EM_Comparison_Forget free_rng_ab_adjunction_hom). Qed.

Theorem EM_to_Rng_Forget@{+} : Rng_Forget_Ab ◯ EM_to_Rng ≈ RngAlg_Forget.
Proof.
  exists (fun x => iso_id).
  intros x y f a. reflexivity.
Qed.

Example Rng_K_Forget_obj@{+} (R : Rng@{u p}) :
  fobj[RngAlg_Forget] (fobj[Rng_K] R) = fobj[Rng_Forget_Ab] R := eq_refl.

Example Rng_K_Forget_map@{+} {R S : Rng@{u p}} (f : R ~{Rng@{u p}}~> S) :
  fmap[RngAlg_Forget] (fmap[Rng_K] f) = fmap[Rng_Forget_Ab] f := eq_refl.

Example EM_to_Rng_Forget_obj@{+} (x : RngAlg) :
  fobj[Rng_Forget_Ab] (fobj[EM_to_Rng] x) = fobj[RngAlg_Forget] x
  := eq_refl.

Example EM_to_Rng_Forget_map@{+} {x y : RngAlg} (f : x ~{RngAlg}~> y) :
  fmap[Rng_Forget_Ab] (fmap[EM_to_Rng] f) = fmap[RngAlg_Forget] f
  := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Readbacks *)

(* The two legs of the isomorphism in Cat are the two functors. *)
Example Rng_EM_iso_to@{+} : to Rng_EM_iso = Rng_K := eq_refl.

Example Rng_EM_iso_from@{+} : from Rng_EM_iso = EM_to_Rng := eq_refl.

(* K R = ⟨U R, U ε_R⟩: the structure map evaluates formal expressions in
   R, and so sends 1, ⟨a⟩, ⟨a⟩·⟨b⟩ and ⟨a⟩ + ⟨b⟩ to 1, a, a·b and a + b. *)
Example Rng_K_carrier@{+} (R : Rng@{u p}) :
  projT1 (fobj[Rng_K] R) = Rng_Forget_Ab R := eq_refl.

Example Rng_K_alg@{+} (R : Rng@{u p}) :
  t_alg[projT2 (fobj[Rng_K] R)]
    = fmap[Rng_Forget_Ab] (@counit _ _ _ _ free_rng_ab_adjunction_hom R)
  := eq_refl.

Example Rng_K_alg_fun@{+} (R : Rng@{u p}) (t : FRTerm (Rng_Forget_Ab R)) :
  cmon_map (t_alg[projT2 (fobj[Rng_K] R)]) t
    = fr_eval (@id Ab@{u p} (Rng_Forget_Ab R)) t := eq_refl.

Example Rng_K_alg_one@{+} (R : Rng@{u p}) :
  cmon_map (t_alg[projT2 (fobj[Rng_K] R)]) (@fr_one (Rng_Forget_Ab R))
    = rig_one R := eq_refl.

Example Rng_K_alg_gen@{+} (R : Rng@{u p}) (a : carrier (rig_setoid R)) :
  cmon_map (t_alg[projT2 (fobj[Rng_K] R)]) (@fr_gen (Rng_Forget_Ab R) a) = a
  := eq_refl.

Example Rng_K_alg_mul@{+} (R : Rng@{u p}) (a b : carrier (rig_setoid R)) :
  cmon_map (t_alg[projT2 (fobj[Rng_K] R)])
    (fr_mul (@fr_gen (Rng_Forget_Ab R) a) (@fr_gen (Rng_Forget_Ab R) b))
    = rig_mul R a b := eq_refl.

Example Rng_K_alg_plus@{+} (R : Rng@{u p}) (a b : carrier (rig_setoid R)) :
  cmon_map (t_alg[projT2 (fobj[Rng_K] R)])
    (fr_plus (@fr_gen (Rng_Forget_Ab R) a) (@fr_gen (Rng_Forget_Ab R) b))
    = rig_add R a b := eq_refl.

Example Rng_K_map@{+} {R S : Rng@{u p}} (f : R ~{Rng@{u p}}~> S) :
  t_alg_hom[fmap[Rng_K] f] = fmap[Rng_Forget_Ab] f := eq_refl.

(* The ring of an algebra: 1 = h 1, a·b = h(⟨a⟩·⟨b⟩), and A's own +. *)
Example EM_to_Rng_one@{+} (x : RngAlg) :
  rig_one (fobj[EM_to_Rng] x) = cmon_map (t_alg[projT2 x]) fr_one
  := eq_refl.

Example EM_to_Rng_mul@{+} (x : RngAlg)
  (a b : carrier (cmon_setoid (projT1 x))) :
  rig_mul (fobj[EM_to_Rng] x) a b
    = cmon_map (t_alg[projT2 x]) (fr_mul (fr_gen a) (fr_gen b)) := eq_refl.

Example EM_to_Rng_add@{+} (x : RngAlg) :
  rig_add (fobj[EM_to_Rng] x) = cmon_plus (projT1 x) := eq_refl.

Example EM_to_Rng_map@{+} {x y : RngAlg} (f : x ~{RngAlg}~> y) :
  rig_map (fmap[EM_to_Rng] f) = cmon_map (t_alg_hom[f]) := eq_refl.

(* The ring round trip returns every operation and every map on the
   nose. *)
Example Rng_rt_setoid@{+} (R : Rng@{u p}) :
  rig_setoid (fobj[EM_to_Rng ◯ Rng_K] R) = rig_setoid R := eq_refl.

Example Rng_rt_zero@{+} (R : Rng@{u p}) :
  rig_zero (fobj[EM_to_Rng ◯ Rng_K] R) = rig_zero R := eq_refl.

Example Rng_rt_add@{+} (R : Rng@{u p}) :
  rig_add (fobj[EM_to_Rng ◯ Rng_K] R) = rig_add R := eq_refl.

Example Rng_rt_one@{+} (R : Rng@{u p}) :
  rig_one (fobj[EM_to_Rng ◯ Rng_K] R) = rig_one R := eq_refl.

Example Rng_rt_mul@{+} (R : Rng@{u p}) (a b : carrier (rig_setoid R)) :
  rig_mul (fobj[EM_to_Rng ◯ Rng_K] R) a b = rig_mul R a b := eq_refl.

Example Rng_rt_neg@{+} (R : Rng@{u p}) :
  ring_neg (fobj[EM_to_Rng ◯ Rng_K] R) = ring_neg R := eq_refl.

Example Rng_rt_hom@{+} {R S : Rng@{u p}} (f : R ~{Rng@{u p}}~> S) :
  rig_map (fmap[EM_to_Rng ◯ Rng_K] f) = rig_map f := eq_refl.

(* The algebra round trip keeps the group and the maps on the nose, and
   returns the structure map as the evaluation in the algebra's ring. *)
Example EM_Rng_rt_carrier@{+} (x : RngAlg) :
  projT1 (fobj[Rng_K ◯ EM_to_Rng] x) = projT1 x := eq_refl.

Example EM_Rng_rt_alg_fun@{+} (x : RngAlg) (t : FRTerm (projT1 x)) :
  cmon_map (t_alg[projT2 (fobj[Rng_K ◯ EM_to_Rng] x)]) t
    = fr_eval (R := ralg_ring (projT2 x)) (@id Ab@{u p} (projT1 x)) t
  := eq_refl.

Example EM_Rng_rt_alg_hom@{+} {x y : RngAlg} (f : x ~{RngAlg}~> y) :
  t_alg_hom[fmap[Rng_K ◯ EM_to_Rng] f] = t_alg_hom[f] := eq_refl.

(* Every component of the two natural isomorphisms is the identity, at a
   variable object, to and from. *)
Example Rng_EM_iso_to_from_component@{+} (x : RngAlg) :
  (t_alg_hom[to (projT1 (iso_to_from Rng_EM_iso) x)],
   t_alg_hom[from (projT1 (iso_to_from Rng_EM_iso) x)])
    = (@id Ab@{u p} (projT1 x), @id Ab@{u p} (projT1 x)) := eq_refl.

Example Rng_EM_iso_from_to_component@{+} (R : Rng@{u p}) :
  (rig_map (to (projT1 (iso_from_to Rng_EM_iso) R)),
   rig_map (from (projT1 (iso_from_to Rng_EM_iso) R)))
    = (@setoid_morphism_id (rig_setoid R),
       @setoid_morphism_id (rig_setoid R)) := eq_refl.

Example Rng_EM_counit_component@{+} (x : RngAlg) :
  (t_alg_hom[to (projT1 (@equivalence_counit _ _ _ Rng_EM_equivalence) x)],
   t_alg_hom[from (projT1 (@equivalence_counit _ _ _
                             Rng_EM_equivalence) x)])
    = (@id Ab@{u p} (projT1 x), @id Ab@{u p} (projT1 x)) := eq_refl.

Example Rng_EM_unit_component@{+} (R : Rng@{u p}) :
  (rig_map (to (projT1 (@equivalence_unit _ _ _ Rng_EM_equivalence) R)),
   rig_map (from (projT1 (@equivalence_unit _ _ _ Rng_EM_equivalence) R)))
    = (@setoid_morphism_id (rig_setoid R),
       @setoid_morphism_id (rig_setoid R)) := eq_refl.

End TensorAlgebraMonad.
