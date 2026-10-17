(** * The monad R ⊗ (−) on Ab and its algebras, the left R-modules *)

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
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Tensor.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.BaseChange.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(*
 Book: Riehl, "Category Theory in Context", 2nd ed., Example
 nLab: https://ncatlab.org/nlab/show/module
 nLab: https://ncatlab.org/nlab/show/algebra+over+a+monad
 nLab: https://ncatlab.org/nlab/show/monadicity+theorem

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The monad R ⊗ (−) on Ab *)

(* T is the composite U ◯ F of the free/forgetful adjunction; the monad is
   Monad/Comparison.v's, whose ret is η and whose join is U ε F. *)
Definition TensorF@{a c p o x} (R : RingObject@{a c p}) :
  Ab@{o c} ⟶ Ab@{o c} :=
  RMod_Forget_Ab@{x o o a p c} R ◯ ZExt@{a c p x o a o c} R.

Definition TensorMonad@{a c p o x} (R : RingObject@{a c p}) :
  @Monad Ab@{o c} (TensorF@{a c p o x} R) :=
  Adjunction_Induced_Monad (zext_adjunction@{a c p o o x a a} R).

(* Mac Lane's formulas, read back on the nose: TA = R ⊗ A, T f = 1 ⊗ f
   (BaseChange.v's [zext_map_ab]), η a = 1 ⊗ a, and
   μ (r₁ ⊗ (r₂ ⊗ a)) = r₁r₂ ⊗ a. *)
Example TensorF_obj@{a c p o x} (R : RingObject@{a c p}) (A : obj[Ab@{o c}]) :
  fobj[TensorF@{a c p o x} R] A = AbTensor (ring_ab R) A := eq_refl.

Example TensorF_map@{a c p o x} (R : RingObject@{a c p})
  (A B : obj[Ab@{o c}]) (f : A ~{Ab@{o c}}~> B) :
  fmap[TensorF@{a c p o x} R] f = zext_map_ab R f := eq_refl.

Example TensorMonad_ret@{a c p o x} (R : RingObject@{a c p})
  (A : obj[Ab@{o c}]) (a : carrier A) :
  cmon_map (@ret _ _ (TensorMonad@{a c p o x} R) A) a
  = @ts_gen (ring_ab R) A (rig_one (ring_rig R)) a := eq_refl.

Example TensorMonad_join@{a c p o x} (R : RingObject@{a c p})
  (A : obj[Ab@{o c}]) (r1 r2 : carrier (rig_setoid (ring_rig R)))
  (a : carrier A) :
  cmon_map (@join _ _ (TensorMonad@{a c p o x} R) A)
    (@ts_gen (ring_ab R) (AbTensor (ring_ab R) A) r1
       (@ts_gen (ring_ab R) A r2 a))
  = @ts_gen (ring_ab R) A (rig_mul (ring_rig R) r1 r2) a := eq_refl.

(* μ IS the adjunction's counit at the free module R ⊗ A, as a
   homomorphism of abelian groups, and on each generator r ⊗ y it is the
   free module's own action r · y. *)
Example TensorMonad_join_counit@{a c p o x} (R : RingObject@{a c p})
  (A : obj[Ab@{o c}]) :
  @join _ _ (TensorMonad@{a c p o x} R) A
  = rm_hom (zext_counit@{a c p o x a o a} R (ZExtObj R A)) := eq_refl.

Example TensorMonad_join_gen@{a c p o x} (R : RingObject@{a c p})
  (A : obj[Ab@{o c}]) (r : carrier (rig_setoid (ring_rig R)))
  (y : carrier (AbTensor (ring_ab R) A)) :
  cmon_map (@join _ _ (TensorMonad@{a c p o x} R) A)
    (@ts_gen (ring_ab R) (AbTensor (ring_ab R) A) r y)
  = zext_act R A r y := eq_refl.

(* A computing witness over ℤ: μ (3 ⊗ (4 ⊗ a)) = 12 ⊗ a. *)
Example TensorMonad_join_Z@{o x} (a : Z) :
  cmon_map (@join _ _ (TensorMonad@{Set Set Set o x} Int_Ring)
              (ring_ab Int_Ring))
    (@ts_gen (ring_ab Int_Ring) (AbTensor (ring_ab Int_Ring) (ring_ab Int_Ring))
       3%Z (@ts_gen (ring_ab Int_Ring) (ring_ab Int_Ring) 4%Z a))
  = @ts_gen (ring_ab Int_Ring) (ring_ab Int_Ring) 12%Z a := eq_refl.

(** ** Algebras are left modules *)

(* An algebra (A, h) acts by r · m := h (r ⊗ m).  Riehl's "ℤ-bilinear
   map (r, a) ↦ r·a" is h composed with the universal bilinear map. *)
Definition em_smul@{a c p o x} {R : RingObject@{a c p}}
  (X : @EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
         (TensorMonad@{a c p o x} R))
  (r : carrier (rig_setoid (ring_rig R))) (m : carrier (`1 X)) :
  carrier (`1 X) :=
  cmon_map (t_alg[`2 X]) (@ts_gen (ring_ab R) (`1 X) r m).

Lemma em_smul_respects@{a c p o x} {R : RingObject@{a c p}}
  (X : @EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
         (TensorMonad@{a c p o x} R)) :
  Proper (equiv ==> equiv ==> equiv) (em_smul@{a c p o x} X).
Proof.
  intros r r' Hr m m' Hm.
  exact (proper_morphism (cmon_map (t_alg[`2 X])) _ _
           (@te_gen (ring_ab R) (`1 X) _ _ _ _ Hr Hm)).
Qed.

(* Additivity in m and in r: h is additive and ⊗ is bilinear. *)
Lemma em_smul_distr_l@{a c p o x} {R : RingObject@{a c p}}
  (X : @EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
         (TensorMonad@{a c p o x} R))
  (r : carrier (rig_setoid (ring_rig R))) (m n : carrier (`1 X)) :
  em_smul X r (cmon_plus (`1 X) m n)
    ≈ cmon_plus (`1 X) (em_smul X r m) (em_smul X r n).
Proof.
  unfold em_smul.
  transitivity (cmon_map (t_alg[`2 X])
                  (cmon_plus (AbTensor (ring_ab R) (`1 X))
                     (@ts_gen (ring_ab R) (`1 X) r m)
                     (@ts_gen (ring_ab R) (`1 X) r n))).
  - exact (proper_morphism (cmon_map (t_alg[`2 X])) _ _
             (@te_bilin_r (ring_ab R) (`1 X) r m n)).
  - exact (cmon_map_plus (t_alg[`2 X]) _ _).
Qed.

Lemma em_smul_distr_r@{a c p o x} {R : RingObject@{a c p}}
  (X : @EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
         (TensorMonad@{a c p o x} R))
  (r s : carrier (rig_setoid (ring_rig R))) (m : carrier (`1 X)) :
  em_smul X (rig_add (ring_rig R) r s) m
    ≈ cmon_plus (`1 X) (em_smul X r m) (em_smul X s m).
Proof.
  unfold em_smul.
  transitivity (cmon_map (t_alg[`2 X])
                  (cmon_plus (AbTensor (ring_ab R) (`1 X))
                     (@ts_gen (ring_ab R) (`1 X) r m)
                     (@ts_gen (ring_ab R) (`1 X) s m))).
  - exact (proper_morphism (cmon_map (t_alg[`2 X])) _ _
             (@te_bilin_l (ring_ab R) (`1 X) r s m)).
  - exact (cmon_map_plus (t_alg[`2 X]) _ _).
Qed.

(* Mac Lane's μ-law of the algebra, read at r ⊗ (s ⊗ m), is associativity
   of the action; [t_action] states it with the two sides exchanged. *)
Lemma em_smul_assoc@{a c p o x} {R : RingObject@{a c p}}
  (X : @EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
         (TensorMonad@{a c p o x} R))
  (r s : carrier (rig_setoid (ring_rig R))) (m : carrier (`1 X)) :
  em_smul X (rig_mul (ring_rig R) r s) m ≈ em_smul X r (em_smul X s m).
Proof.
  symmetry.
  exact (@t_action _ _ _ _ (`2 X)
           (@ts_gen (ring_ab R) (AbTensor (ring_ab R) (`1 X)) r
              (@ts_gen (ring_ab R) (`1 X) s m))).
Qed.

(* The η-law of the algebra is 1 · m ≈ m. *)
Lemma em_smul_one@{a c p o x} {R : RingObject@{a c p}}
  (X : @EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
         (TensorMonad@{a c p o x} R))
  (m : carrier (`1 X)) :
  em_smul X (rig_one (ring_rig R)) m ≈ m.
Proof. exact (@t_id _ _ _ _ (`2 X) m). Qed.

Definition EM_mod@{a c p o x} {R : RingObject@{a c p}}
  (X : @EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
         (TensorMonad@{a c p o x} R)) :
  obj[RMod@{o x a p c} R] :=
  @Build_RModObject R (`1 X) (em_smul X) (em_smul_respects X)
    (em_smul_distr_l X) (em_smul_distr_r X) (em_smul_assoc X)
    (em_smul_one X).

Definition EM_mod_hom@{a c p o x} {R : RingObject@{a c p}}
  {X Y : @EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
           (TensorMonad@{a c p o x} R)}
  (f : X ~{@EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
             (TensorMonad@{a c p o x} R)}~> Y) :
  EM_mod X ~{RMod@{o x a p c} R}~> EM_mod Y :=
  @Build_RModHom R (EM_mod X) (EM_mod Y) t_alg_hom[f]
    (fun r m => @t_alg_hom_commutes _ _ _ _ _ _ _ f
                  (@ts_gen (ring_ab R) (`1 X) r m)).

Definition EM_to_RMod@{a c p o x} (R : RingObject@{a c p}) :
  @EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
    (TensorMonad@{a c p o x} R) ⟶ RMod@{o x a p c} R.
Proof.
  unshelve refine
    (@Build_Functor
       (@EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
          (TensorMonad@{a c p o x} R))
       (RMod@{o x a p c} R) (fun X => EM_mod X) (fun X Y f => EM_mod_hom f)
       _ _ _).
  - intros X Y f f' Hf m. exact (Hf m).
  - intros X m. reflexivity.
  - intros X Y Z f g m. reflexivity.
Defined.

(* The action of [EM_mod X] IS h on generators, by definition. *)
Example EM_mod_smul@{a c p o x} {R : RingObject@{a c p}}
  (X : @EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
         (TensorMonad@{a c p o x} R))
  (r : carrier (rig_setoid (ring_rig R))) (m : carrier (`1 X)) :
  rm_smul (EM_mod X) r m
  = cmon_map (t_alg[`2 X]) (@ts_gen (ring_ab R) (`1 X) r m) := eq_refl.

(** ** The comparison functor is an equivalence *)

(* Module round trip: identity components, both laws by reflexivity. *)
Definition RMod_counit_iso@{a c p o x} {R : RingObject@{a c p}}
  (M : obj[RMod@{o x a p c} R]) :
  @Isomorphism (RMod@{o x a p c} R)
    (fobj[EM_to_RMod@{a c p o x} R
          ◯ EM_Comparison (zext_adjunction@{a c p o o x a a} R)] M) M.
Proof.
  unshelve refine
    (@Build_Isomorphism (RMod@{o x a p c} R) _ _
       (@Build_RModHom R
          (fobj[EM_to_RMod@{a c p o x} R
                ◯ EM_Comparison (zext_adjunction@{a c p o o x a a} R)] M) M
          (@cmon_hom_id (rm_ab M)) _)
       (@Build_RModHom R M
          (fobj[EM_to_RMod@{a c p o x} R
                ◯ EM_Comparison (zext_adjunction@{a c p o o x a a} R)] M)
          (@cmon_hom_id (rm_ab M)) _) _ _).
  - intros r m. reflexivity.
  - intros r m. reflexivity.
  - intros m. reflexivity.
  - intros m. reflexivity.
Defined.

(* Algebra round trip: identity components; the structure maps agree on
   each generator r ⊗ m by [reflexivity] and on every formal sum by
   [tensor_hom_ext], the uniqueness half of the tensor's universal
   property. *)
Definition RMod_unit_iso@{a c p o x} {R : RingObject@{a c p}}
  (X : @EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
         (TensorMonad@{a c p o x} R)) :
  @Isomorphism
    (@EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
       (TensorMonad@{a c p o x} R))
    (fobj[EM_Comparison (zext_adjunction@{a c p o o x a a} R)
          ◯ EM_to_RMod@{a c p o x} R] X) X.
Proof.
  unshelve refine
    (@Build_Isomorphism
       (@EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
          (TensorMonad@{a c p o x} R))
       (fobj[EM_Comparison (zext_adjunction@{a c p o o x a a} R)
             ◯ EM_to_RMod@{a c p o x} R] X) X
       (@Build_TAlgebraHom Ab@{o c} (TensorF@{a c p o x} R)
          (TensorMonad@{a c p o x} R) (`1 X) (`1 X)
          (`2 (fobj[EM_Comparison (zext_adjunction@{a c p o o x a a} R)
                    ◯ EM_to_RMod@{a c p o x} R] X)) (`2 X)
          (@cmon_hom_id (`1 X)) _)
       (@Build_TAlgebraHom Ab@{o c} (TensorF@{a c p o x} R)
          (TensorMonad@{a c p o x} R) (`1 X) (`1 X)
          (`2 X) (`2 (fobj[EM_Comparison (zext_adjunction@{a c p o o x a a} R)
                        ◯ EM_to_RMod@{a c p o x} R] X))
          (@cmon_hom_id (`1 X)) _) _ _).
  - intros s.
    refine (tensor_hom_ext _ _ _ s).
    intros r m. reflexivity.
  - intros s.
    refine (tensor_hom_ext _ _ _ s).
    intros r m. reflexivity.
  - intros m. reflexivity.
  - intros m. reflexivity.
Defined.

Definition RMod_comparison_equivalence@{a c p o x} (R : RingObject@{a c p}) :
  EquivalenceOfCategories (EM_Comparison (zext_adjunction@{a c p o o x a a} R)).
Proof.
  unshelve refine
    (@Build_EquivalenceOfCategories _ _
       (EM_Comparison (zext_adjunction@{a c p o o x a a} R))
       (EM_to_RMod@{a c p o x} R) _ _).
  - exists (fun X => RMod_unit_iso X).
    intros [A α] [B β] f m; simpl. reflexivity.
  - exists (fun M => iso_sym (RMod_counit_iso M)).
    intros M N h m; simpl. reflexivity.
Defined.

(* Riehl's Example 5.5.7(i): the forgetful functor is monadic, and the
   equivalence is the canonical comparison functor of [zext_adjunction]
   itself (her Definition 5.3.1), not some other equivalence. *)
Definition RMod_Forget_Ab_Monadic@{a c p o x} (R : RingObject@{a c p}) :
  @Monadic@{o x o o o c o a} (RMod@{o x a p c} R) Ab@{o c}
    (RMod_Forget_Ab@{x o o a p c} R).
Proof.
  exists (ZExt@{a c p x o a o c} R).
  exists (zext_adjunction@{a c p o o x a a} R).
  exact (RMod_comparison_equivalence@{a c p o x} R).
Defined.

Definition EM_RMod_iso@{a c p o x k} (R : RingObject@{a c p}) :
  @Isomorphism Cat@{k o x o c}
    (RMod@{o x a p c} R)
    (@EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
       (TensorMonad@{a c p o x} R)) :=
  Equivalence_to_Cat_Iso (RMod_comparison_equivalence@{a c p o x} R).

Example EM_RMod_iso_to@{a c p o x k} (R : RingObject@{a c p}) :
  to (EM_RMod_iso@{a c p o x k} R)
  = EM_Comparison (zext_adjunction@{a c p o o x a a} R) := eq_refl.

Example EM_RMod_iso_from@{a c p o x k} (R : RingObject@{a c p}) :
  from (EM_RMod_iso@{a c p o x k} R) = EM_to_RMod@{a c p o x} R := eq_refl.

(* The comparison algebra on a module M is U ε_M: on r ⊗ m it is r · m,
   and as a homomorphism it IS the counit at M. *)
Example comparison_alg_is_smul@{a c p o x} {R : RingObject@{a c p}}
  (M : obj[RMod@{o x a p c} R]) (r : carrier (rig_setoid (ring_rig R)))
  (m : carrier (rm_ab M)) :
  cmon_map (t_alg[`2 (fobj[EM_Comparison
                              (zext_adjunction@{a c p o o x a a} R)] M)])
    (@ts_gen (ring_ab R) (rm_ab M) r m)
  = rm_smul M r m := eq_refl.

Example comparison_alg_counit@{a c p o x} {R : RingObject@{a c p}}
  (M : obj[RMod@{o x a p c} R]) :
  t_alg[`2 (fobj[EM_Comparison (zext_adjunction@{a c p o o x a a} R)] M)]
  = rm_hom (zext_counit@{a c p o x a o a} R M) := eq_refl.

(** ** Riehl's Theorem 5.5.1: the creation of U-split coequalizers *)

(* Absorption: a map h out of U B coforking the pair satisfies
   h (s (e y)) ≈ h y. *)
Lemma rmod_split_absorb@{a c p o x} {R : RingObject@{a c p}}
  {A B : obj[RMod@{o x a p c} R]} (f g : A ~{RMod@{o x a p c} R}~> B)
  (S : @SplitCoequalizer Ab@{o c} _ _
         (fmap[RMod_Forget_Ab@{x o o a p c} R] f)
         (fmap[RMod_Forget_Ab@{x o o a p c} R] g))
  {W : obj[Ab@{o c}]} (h : rm_ab B ~{Ab@{o c}}~> W)
  (Hh : ∀ y, cmon_map h (cmon_map (rm_hom f) y)
             ≈ cmon_map h (cmon_map (rm_hom g) y))
  (y : carrier (rm_ab B)) :
  cmon_map h (cmon_map (scoeq_s S) (cmon_map (scoeq_e S) y)) ≈ cmon_map h y.
Proof.
  pose proof (scoeq_law4 S y) as L4; simpl in L4.
  pose proof (scoeq_law3 S y) as L3; simpl in L3.
  transitivity (cmon_map h (cmon_map (rm_hom g) (cmon_map (scoeq_t S) y))).
  - apply (proper_morphism (cmon_map h)). symmetry. exact L4.
  - transitivity (cmon_map h (cmon_map (rm_hom f) (cmon_map (scoeq_t S) y))).
    + symmetry. apply Hh.
    + apply (proper_morphism (cmon_map h)). exact L3.
Qed.

(* The created action on the split coequalizer Z: r · z := e (r · s z). *)
Definition rmod_created_smul@{a c p o x} {R : RingObject@{a c p}}
  {A B : obj[RMod@{o x a p c} R]} (f g : A ~{RMod@{o x a p c} R}~> B)
  (S : @SplitCoequalizer Ab@{o c} _ _
         (fmap[RMod_Forget_Ab@{x o o a p c} R] f)
         (fmap[RMod_Forget_Ab@{x o o a p c} R] g))
  (r : carrier (rig_setoid (ring_rig R))) (z : carrier (scoeq_obj S)) :
  carrier (scoeq_obj S) :=
  cmon_map (scoeq_e S) (rm_smul B r (cmon_map (scoeq_s S) z)).

Lemma rmod_created_absorb@{a c p o x} {R : RingObject@{a c p}}
  {A B : obj[RMod@{o x a p c} R]} (f g : A ~{RMod@{o x a p c} R}~> B)
  (S : @SplitCoequalizer Ab@{o c} _ _
         (fmap[RMod_Forget_Ab@{x o o a p c} R] f)
         (fmap[RMod_Forget_Ab@{x o o a p c} R] g))
  (r : carrier (rig_setoid (ring_rig R))) (y : carrier (rm_ab B)) :
  cmon_map (scoeq_e S) (rm_smul B r (cmon_map (scoeq_s S)
                                       (cmon_map (scoeq_e S) y)))
  ≈ cmon_map (scoeq_e S) (rm_smul B r y).
Proof.
  pose proof (scoeq_law4 S y) as L4; simpl in L4.
  pose proof (scoeq_law3 S y) as L3; simpl in L3.
  pose proof (scoeq_law1 S (rm_smul A r (cmon_map (scoeq_t S) y))) as L1;
    simpl in L1.
  transitivity (cmon_map (scoeq_e S)
                  (rm_smul B r (cmon_map (rm_hom g) (cmon_map (scoeq_t S) y)))).
  - apply (proper_morphism (cmon_map (scoeq_e S))).
    apply rm_smul_respects; [ reflexivity | symmetry; exact L4 ].
  - transitivity (cmon_map (scoeq_e S)
                    (cmon_map (rm_hom g)
                       (rm_smul A r (cmon_map (scoeq_t S) y)))).
    + apply (proper_morphism (cmon_map (scoeq_e S))).
      symmetry. apply rm_map_smul.
    + transitivity (cmon_map (scoeq_e S)
                      (cmon_map (rm_hom f)
                         (rm_smul A r (cmon_map (scoeq_t S) y)))).
      * symmetry. exact L1.
      * transitivity (cmon_map (scoeq_e S)
                        (rm_smul B r
                           (cmon_map (rm_hom f) (cmon_map (scoeq_t S) y)))).
        -- apply (proper_morphism (cmon_map (scoeq_e S))). apply rm_map_smul.
        -- apply (proper_morphism (cmon_map (scoeq_e S))).
           apply rm_smul_respects; [ reflexivity | exact L3 ].
Qed.

Definition RModCreated@{a c p o x} {R : RingObject@{a c p}}
  {A B : obj[RMod@{o x a p c} R]} (f g : A ~{RMod@{o x a p c} R}~> B)
  (S : @SplitCoequalizer Ab@{o c} _ _
         (fmap[RMod_Forget_Ab@{x o o a p c} R] f)
         (fmap[RMod_Forget_Ab@{x o o a p c} R] g)) :
  obj[RMod@{o x a p c} R].
Proof.
  unshelve refine (@Build_RModObject R (scoeq_obj S)
                     (rmod_created_smul f g S) _ _ _ _ _).
  - intros r r' Hr z z' Hz. unfold rmod_created_smul.
    apply (proper_morphism (cmon_map (scoeq_e S))).
    apply rm_smul_respects;
      [ exact Hr | apply (proper_morphism (cmon_map (scoeq_s S))); exact Hz ].
  - intros r z w. unfold rmod_created_smul.
    transitivity (cmon_map (scoeq_e S)
                    (rm_smul B r (cmon_plus (rm_ab B) (cmon_map (scoeq_s S) z)
                                              (cmon_map (scoeq_s S) w)))).
    + apply (proper_morphism (cmon_map (scoeq_e S))).
      apply rm_smul_respects; [ reflexivity | apply cmon_map_plus ].
    + transitivity (cmon_map (scoeq_e S)
                      (cmon_plus (rm_ab B)
                         (rm_smul B r (cmon_map (scoeq_s S) z))
                         (rm_smul B r (cmon_map (scoeq_s S) w)))).
      * apply (proper_morphism (cmon_map (scoeq_e S))). apply rm_smul_distr_l.
      * apply cmon_map_plus.
  - intros r r' z. unfold rmod_created_smul.
    transitivity (cmon_map (scoeq_e S)
                    (cmon_plus (rm_ab B)
                       (rm_smul B r (cmon_map (scoeq_s S) z))
                       (rm_smul B r' (cmon_map (scoeq_s S) z)))).
    + apply (proper_morphism (cmon_map (scoeq_e S))). apply rm_smul_distr_r.
    + apply cmon_map_plus.
  - intros r r' z. unfold rmod_created_smul.
    transitivity (cmon_map (scoeq_e S)
                    (rm_smul B r (rm_smul B r' (cmon_map (scoeq_s S) z)))).
    + apply (proper_morphism (cmon_map (scoeq_e S))). apply rm_smul_assoc.
    + symmetry. apply rmod_created_absorb.
  - intros z. unfold rmod_created_smul.
    pose proof (scoeq_law2 S z) as L2; simpl in L2.
    transitivity (cmon_map (scoeq_e S) (cmon_map (scoeq_s S) z));
      [ | exact L2 ].
    apply (proper_morphism (cmon_map (scoeq_e S))). apply rm_smul_one.
Defined.

Definition RModCreatedE@{a c p o x} {R : RingObject@{a c p}}
  {A B : obj[RMod@{o x a p c} R]} (f g : A ~{RMod@{o x a p c} R}~> B)
  (S : @SplitCoequalizer Ab@{o c} _ _
         (fmap[RMod_Forget_Ab@{x o o a p c} R] f)
         (fmap[RMod_Forget_Ab@{x o o a p c} R] g)) :
  B ~{RMod@{o x a p c} R}~> RModCreated f g S.
Proof.
  unshelve refine (@Build_RModHom R B (RModCreated f g S) (scoeq_e S) _).
  intros r y. simpl. unfold rmod_created_smul. symmetry.
  apply rmod_created_absorb.
Defined.

Definition RModCreatedE_is_coeq@{a c p o x} {R : RingObject@{a c p}}
  {A B : obj[RMod@{o x a p c} R]} (f g : A ~{RMod@{o x a p c} R}~> B)
  (S : @SplitCoequalizer Ab@{o c} _ _
         (fmap[RMod_Forget_Ab@{x o o a p c} R] f)
         (fmap[RMod_Forget_Ab@{x o o a p c} R] g)) :
  @IsCoequalizer (RMod@{o x a p c} R) A B f g
    (RModCreated f g S) (RModCreatedE f g S).
Proof.
  unshelve refine (@Build_IsCoequalizer _ _ _ _ _ _ _ _ _).
  - intros y. exact (scoeq_law1 S y).
  - intros W h Hh.
    unshelve eapply Build_Unique.
    + unshelve refine
        (@Build_RModHom R (RModCreated f g S) W
           (cmon_hom_compose (rm_hom h) (scoeq_s S)) _).
      intros r z; simpl. unfold rmod_created_smul.
      transitivity (cmon_map (rm_hom h) (rm_smul B r (cmon_map (scoeq_s S) z))).
      * exact (rmod_split_absorb f g S (rm_hom h) Hh _).
      * apply rm_map_smul.
    + intros y; simpl. exact (rmod_split_absorb f g S (rm_hom h) Hh y).
    + intros v Hv z; simpl.
      pose proof (scoeq_law2 S z) as L2; simpl in L2.
      transitivity (cmon_map (rm_hom v)
                      (cmon_map (scoeq_e S) (cmon_map (scoeq_s S) z))).
      * symmetry. exact (Hv (cmon_map (scoeq_s S) z)).
      * apply (proper_morphism (cmon_map (rm_hom v))). exact L2.
Defined.

Definition RModReflected_is_coeq@{a c p o x} {R : RingObject@{a c p}}
  {A B : obj[RMod@{o x a p c} R]} (f g : A ~{RMod@{o x a p c} R}~> B)
  (S : @SplitCoequalizer Ab@{o c} _ _
         (fmap[RMod_Forget_Ab@{x o o a p c} R] f)
         (fmap[RMod_Forget_Ab@{x o o a p c} R] g))
  (Q : obj[RMod@{o x a p c} R]) (e : B ~{RMod@{o x a p c} R}~> Q)
  (He : e ∘ f ≈ e ∘ g)
  (i : @Isomorphism Ab@{o c} (fobj[RMod_Forget_Ab@{x o o a p c} R] Q)
         (scoeq_obj S))
  (Hi : to i ∘ fmap[RMod_Forget_Ab@{x o o a p c} R] e ≈ scoeq_e S) :
  @IsCoequalizer (RMod@{o x a p c} R) A B f g Q e.
Proof.
  assert (L0 : ∀ w, w ≈ cmon_map (rm_hom e)
                          (cmon_map (scoeq_s S) (cmon_map (to i) w))).
  { intros w.
    pose proof (Hi (cmon_map (scoeq_s S) (cmon_map (to i) w))) as H1;
      simpl in H1.
    pose proof (scoeq_law2 S (cmon_map (to i) w)) as L2; simpl in L2.
    pose proof (iso_from_to i w) as FT; simpl in FT.
    pose proof (iso_from_to i (cmon_map (rm_hom e)
                  (cmon_map (scoeq_s S) (cmon_map (to i) w)))) as FT';
      simpl in FT'.
    transitivity (cmon_map (from i) (cmon_map (to i) w));
      [ symmetry; exact FT | ].
    transitivity (cmon_map (from i) (cmon_map (to i) (cmon_map (rm_hom e)
                    (cmon_map (scoeq_s S) (cmon_map (to i) w)))));
      [ | exact FT' ].
    apply (proper_morphism (cmon_map (from i))).
    symmetry.
    transitivity (cmon_map (scoeq_e S)
                    (cmon_map (scoeq_s S) (cmon_map (to i) w)));
      [ exact H1 | exact L2 ]. }
  unshelve refine (@Build_IsCoequalizer _ _ _ _ _ _ _ _ _).
  - exact He.
  - intros W h Hh.
    unshelve eapply Build_Unique.
    + unshelve refine
        (@Build_RModHom R Q W
           (cmon_hom_compose (cmon_hom_compose (rm_hom h) (scoeq_s S))
              (to i)) _).
      intros r w; simpl.
      transitivity
        (cmon_map (rm_hom h) (cmon_map (scoeq_s S) (cmon_map (to i)
           (rm_smul Q r (cmon_map (rm_hom e)
              (cmon_map (scoeq_s S) (cmon_map (to i) w))))))).
      * apply (proper_morphism (cmon_map (rm_hom h))).
        apply (proper_morphism (cmon_map (scoeq_s S))).
        apply (proper_morphism (cmon_map (to i))).
        apply rm_smul_respects; [ reflexivity | exact (L0 w) ].
      * transitivity
          (cmon_map (rm_hom h) (cmon_map (scoeq_s S) (cmon_map (to i)
             (cmon_map (rm_hom e)
                (rm_smul B r (cmon_map (scoeq_s S) (cmon_map (to i) w))))))).
        -- apply (proper_morphism (cmon_map (rm_hom h))).
           apply (proper_morphism (cmon_map (scoeq_s S))).
           apply (proper_morphism (cmon_map (to i))).
           symmetry. apply rm_map_smul.
        -- transitivity
             (cmon_map (rm_hom h) (cmon_map (scoeq_s S) (cmon_map (scoeq_e S)
                (rm_smul B r (cmon_map (scoeq_s S) (cmon_map (to i) w)))))).
           ++ apply (proper_morphism (cmon_map (rm_hom h))).
              apply (proper_morphism (cmon_map (scoeq_s S))).
              exact (Hi _).
           ++ transitivity (cmon_map (rm_hom h)
                 (rm_smul B r (cmon_map (scoeq_s S) (cmon_map (to i) w)))).
              ** exact (rmod_split_absorb f g S (rm_hom h) Hh _).
              ** apply rm_map_smul.
    + intros y; simpl.
      transitivity (cmon_map (rm_hom h)
                      (cmon_map (scoeq_s S) (cmon_map (scoeq_e S) y))).
      * apply (proper_morphism (cmon_map (rm_hom h))).
        apply (proper_morphism (cmon_map (scoeq_s S))).
        exact (Hi y).
      * exact (rmod_split_absorb f g S (rm_hom h) Hh y).
    + intros v Hv w; simpl.
      transitivity (cmon_map (rm_hom v) (cmon_map (rm_hom e)
                      (cmon_map (scoeq_s S) (cmon_map (to i) w)))).
      * symmetry. exact (Hv (cmon_map (scoeq_s S) (cmon_map (to i) w))).
      * apply (proper_morphism (cmon_map (rm_hom v))). symmetry. exact (L0 w).
Defined.

Definition RMod_Forget_Ab_creates_split@{a c p o x} (R : RingObject@{a c p}) :
  CreatesUSplitCoequalizers (RMod_Forget_Ab@{x o o a p c} R).
Proof.
  unshelve refine (@Build_CreatesUSplitCoequalizers _ _ _ _ _).
  - intros A B f g S.
    exists (RModCreated f g S).
    exists (RModCreatedE f g S).
    split.
    + exact (RModCreatedE_is_coeq f g S).
    + exists (@iso_id Ab@{o c} (scoeq_obj S)).
      intros y; simpl. reflexivity.
  - intros A B f g S Q e He i Hi.
    exact (RModReflected_is_coeq f g S Q e He i Hi).
Defined.

(* The lift chosen is on the nose: its group IS Z, its action IS
   e (r · s z), its coequalizing arrow IS e and its comparison isomorphism
   IS the identity. *)
Example rmod_created_carrier@{a c p o x} {R : RingObject@{a c p}}
  {A B : obj[RMod@{o x a p c} R]} (f g : A ~{RMod@{o x a p c} R}~> B)
  (S : @SplitCoequalizer Ab@{o c} _ _
         (fmap[RMod_Forget_Ab@{x o o a p c} R] f)
         (fmap[RMod_Forget_Ab@{x o o a p c} R] g)) :
  rm_ab (`1 (@create_coeq _ _ _ (RMod_Forget_Ab_creates_split@{a c p o x} R)
               A B f g S)) = scoeq_obj S := eq_refl.

Example rmod_created_action@{a c p o x} {R : RingObject@{a c p}}
  {A B : obj[RMod@{o x a p c} R]} (f g : A ~{RMod@{o x a p c} R}~> B)
  (S : @SplitCoequalizer Ab@{o c} _ _
         (fmap[RMod_Forget_Ab@{x o o a p c} R] f)
         (fmap[RMod_Forget_Ab@{x o o a p c} R] g))
  (r : carrier (rig_setoid (ring_rig R))) (z : carrier (scoeq_obj S)) :
  rm_smul (`1 (@create_coeq _ _ _ (RMod_Forget_Ab_creates_split@{a c p o x} R)
                 A B f g S)) r z
  = cmon_map (scoeq_e S) (rm_smul B r (cmon_map (scoeq_s S) z)) := eq_refl.

Example rmod_created_arrow@{a c p o x} {R : RingObject@{a c p}}
  {A B : obj[RMod@{o x a p c} R]} (f g : A ~{RMod@{o x a p c} R}~> B)
  (S : @SplitCoequalizer Ab@{o c} _ _
         (fmap[RMod_Forget_Ab@{x o o a p c} R] f)
         (fmap[RMod_Forget_Ab@{x o o a p c} R] g)) :
  rm_hom (`1 (`2 (@create_coeq _ _ _
                   (RMod_Forget_Ab_creates_split@{a c p o x} R) A B f g S)))
  = scoeq_e S := eq_refl.

Example rmod_created_iso@{a c p o x} {R : RingObject@{a c p}}
  {A B : obj[RMod@{o x a p c} R]} (f g : A ~{RMod@{o x a p c} R}~> B)
  (S : @SplitCoequalizer Ab@{o c} _ _
         (fmap[RMod_Forget_Ab@{x o o a p c} R] f)
         (fmap[RMod_Forget_Ab@{x o o a p c} R] g)) :
  `1 (snd (`2 (`2 (@create_coeq _ _ _
                     (RMod_Forget_Ab_creates_split@{a c p o x} R)
                     A B f g S))))
  = @iso_id Ab@{o c} (scoeq_obj S) := eq_refl.

(* An R-linear map invertible as a group homomorphism is invertible as a
   module map. *)
Definition RMod_Forget_Ab_reflects@{a c p o x} (R : RingObject@{a c p}) :
  ReflectsIsos (RMod_Forget_Ab@{x o o a p c} R) :=
  creates_split_reflects_isos _ (RMod_Forget_Ab_creates_split@{a c p o x} R).

(** ** Beck's route to monadicity *)

Definition RMod_beck_equivalence@{a c p o x} (R : RingObject@{a c p}) :
  EquivalenceOfCategories
    (EM_Comparison (zext_adjunction@{a c p o o x a a} R)) :=
  beck_monadicity (zext_adjunction@{a c p o o x a a} R)
    (RMod_Forget_Ab_creates_split@{a c p o x} R).

Definition RMod_Forget_Ab_Monadic_beck@{a c p o x} (R : RingObject@{a c p}) :
  @Monadic@{o x o o o c o a} (RMod@{o x a p c} R) Ab@{o c}
    (RMod_Forget_Ab@{x o o a p c} R).
Proof.
  exists (ZExt@{a c p x o a o c} R).
  exists (zext_adjunction@{a c p o o x a a} R).
  exact (RMod_beck_equivalence@{a c p o x} R).
Defined.

Definition EM_RMod_iso_beck@{a c p o x k} (R : RingObject@{a c p}) :
  @Isomorphism Cat@{k o x o c}
    (RMod@{o x a p c} R)
    (@EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
       (TensorMonad@{a c p o x} R)) :=
  Equivalence_to_Cat_Iso (RMod_beck_equivalence@{a c p o x} R).

(* The Beck Cat iso's [to] leg IS the comparison functor. *)
Example EM_RMod_iso_beck_to@{a c p o x k} (R : RingObject@{a c p}) :
  to (EM_RMod_iso_beck@{a c p o x k} R)
  = EM_Comparison (zext_adjunction@{a c p o o x a a} R) := eq_refl.

(* The two routes' [to] legs are one term. *)
Example rmod_beck_direct_to@{a c p o x k} (R : RingObject@{a c p}) :
  to (EM_RMod_iso_beck@{a c p o x k} R) = to (EM_RMod_iso@{a c p o x k} R)
  := eq_refl.

(* Beck's quasi-inverse keeps the carrier and acts through η:
   r · m = h ((r · 1) ⊗ m).  It is ≈ to [EM_to_RMod], by [rig_mul_one_r]
   in the scalar slot. *)
Example rmod_beck_carrier@{a c p o x} {R : RingObject@{a c p}}
  (X : @EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
         (TensorMonad@{a c p o x} R)) :
  rm_ab (fobj[@quasi_inverse _ _ _ (RMod_beck_equivalence@{a c p o x} R)] X)
  = `1 X := eq_refl.

Example rmod_beck_act@{a c p o x} {R : RingObject@{a c p}}
  (X : @EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
         (TensorMonad@{a c p o x} R))
  (r : carrier (rig_setoid (ring_rig R))) (m : carrier (`1 X)) :
  rm_smul (fobj[@quasi_inverse _ _ _ (RMod_beck_equivalence@{a c p o x} R)] X)
    r m
  = cmon_map (t_alg[`2 X])
      (@ts_gen (ring_ab R) (`1 X)
         (rig_mul (ring_rig R) r (rig_one (ring_rig R))) m) := eq_refl.

Definition rmod_beck_vs_direct_iso@{a c p o x} {R : RingObject@{a c p}}
  (X : @EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
         (TensorMonad@{a c p o x} R)) :
  @Isomorphism (RMod@{o x a p c} R)
    (fobj[@quasi_inverse _ _ _ (RMod_beck_equivalence@{a c p o x} R)] X)
    (fobj[EM_to_RMod@{a c p o x} R] X).
Proof.
  unshelve refine
    (@Build_Isomorphism (RMod@{o x a p c} R) _ _
       (@Build_RModHom R
          (fobj[@quasi_inverse _ _ _ (RMod_beck_equivalence@{a c p o x} R)] X)
          (fobj[EM_to_RMod@{a c p o x} R] X) (@cmon_hom_id (`1 X)) _)
       (@Build_RModHom R (fobj[EM_to_RMod@{a c p o x} R] X)
          (fobj[@quasi_inverse _ _ _ (RMod_beck_equivalence@{a c p o x} R)] X)
          (@cmon_hom_id (`1 X)) _) _ _).
  - intros r m; simpl. apply (proper_morphism (cmon_map (t_alg[`2 X]))).
    apply te_gen; [ exact (rig_mul_one_r (ring_rig R) r) | reflexivity ].
  - intros r m; simpl. apply (proper_morphism (cmon_map (t_alg[`2 X]))).
    apply te_gen; [ symmetry; exact (rig_mul_one_r (ring_rig R) r)
                  | reflexivity ].
  - intros m. reflexivity.
  - intros m. reflexivity.
Defined.

Definition rmod_beck_vs_direct@{a c p o x} (R : RingObject@{a c p}) :
  @quasi_inverse _ _ _ (RMod_beck_equivalence@{a c p o x} R)
  ≈ EM_to_RMod@{a c p o x} R.
Proof.
  exists (fun X => rmod_beck_vs_direct_iso X).
  intros X Y f m; simpl.
  exact (@t_id _ _ _ _ (`2 Y) (cmon_map t_alg_hom[f] m)).
Defined.
