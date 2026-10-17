Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Strict.
Require Import Category.Theory.Skeleton.
Require Import Category.Theory.Skeleton.Separation.
Require Import Category.Construction.Subcategory.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Instance.One.
Require Import Category.Instance.StrictCat.
Require Import Category.Adjunction.LeftInverse.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Kleisli.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Kleisli.Comparison.

Generalizable All Variables.

(* * * The one-point 单子 Sets: Exercise 3, every algebra free （已译） *)

(*
   Book: Riehl, "Category Theory in Context", the paragraph after Lemma
   nLab: https://ncatlab.org/nlab/show/Kleisli+category

   本文件给出例子。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* Mac Lane's FX in 1, all of it: a full subcategory on every object, its
   membership a proposition.  It does not mention Sets. *)
Definition kleisli_point_FX : Subcategory _1 :=
  @Build_Subcategory _1 (fun _ => True) (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I) (fun _ _ => I).

Definition kleisli_point_FX_full :
  Construction.Subcategory.Full _1 kleisli_point_FX := fun _ _ _ _ _ => I.

Lemma kleisli_point_FX_skeletal : Skeletal (Sub _1 kleisli_point_FX).
Proof. intros [a p] [b q] _. destruct a, b, p, q. reflexivity. Qed.

Section PointMonad.

Universes o so.

Notation SetsC := Sets@{o so}.

Definition kleisli_point_adj :
  Erase SetsC ⊣ PointAt (@terminal_obj SetsC Sets_Terminal) :=
  point_adj Sets_Terminal.

Notation T1 := (Adjunction_Induced_Monad kleisli_point_adj).
Notation XT1 := (@Kleisli SetsC (PointAt _ ◯ Erase SetsC) T1).

(* S ↦ T(S) = the one-point set. *)
Example kleisli_point_monad_obj (S : SetsC) :
  fobj[PointAt (@terminal_obj SetsC Sets_Terminal) ◯ Erase SetsC] S
    = @terminal_obj SetsC _ := eq_refl.

Definition kleisli_point_empty : SetsC := @initial_obj SetsC Sets_Initial.
Definition kleisli_point_one : SetsC := @terminal_obj SetsC Sets_Terminal.

Lemma kleisli_point_distinct : kleisli_point_empty = kleisli_point_one → False.
Proof.
  intro e.
  pose proof (f_equal carrier e) as e1.
  simpl in e1.
  exact (match eq_sym e1 in _ = P return P with eq_refl => ttt end).
Qed.

(* F is not injective on objects, so not a bijection on objects. *)
Lemma kleisli_point_F_not_injective :
  InjectiveOnObjects (Erase SetsC) → False.
Proof.
  intro H. apply kleisli_point_distinct. apply H. reflexivity.
Qed.

(* Neither is the comparison L. *)
Lemma kleisli_point_L_not_injective :
  InjectiveOnObjects (Kleisli_Comparison kleisli_point_adj) → False.
Proof.
  intro H. apply kleisli_point_distinct. apply H. reflexivity.
Qed.

(* FX is all of 1: its one object is F x; L is surjective on objects. *)
Definition kleisli_point_surjective :
  SurjectiveOnObjects (Kleisli_Comparison kleisli_point_adj).
Proof.
  intros c. exists kleisli_point_one. destruct c. reflexivity.
Defined.

Definition kleisli_point_equivalence :
  EquivalenceOfCategories (Kleisli_Comparison kleisli_point_adj) :=
  @ff_surj_eso_equivalence XT1 _ (Kleisli_Comparison kleisli_point_adj)
    _ _ kleisli_point_surjective.

(* ... but X_T is not isomorphic to 1 = FX. *)
Lemma kleisli_point_not_skeletal : Skeletal XT1 → False.
Proof.
  intro SK.
  apply kleisli_point_distinct.
  apply SK.
  unshelve eapply Build_Isomorphism.
  - exact (@one SetsC Sets_Terminal _).
  - exact (@one SetsC Sets_Terminal _).
  - apply (@one_unique SetsC Sets_Terminal).
  - apply (@one_unique SetsC Sets_Terminal).
Qed.

Theorem kleisli_point_not_iso : @Isomorphism StrictCat XT1 _1 → False.
Proof.
  intro i.
  apply kleisli_point_not_skeletal.
  exact (Skeletal_StrictCat_invariant (iso_sym i) One_Skeletal).
Qed.

(* Its chooser: one 对象 1 F one-point setoid. （已译） *)
Definition kleisli_point_FX_pick (a : _1) (m : sobj _1 kleisli_point_FX a) :
  { x : SetsC & Erase SetsC x ≅ a }.
Proof. exists kleisli_point_one. destruct a. apply iso_id. Defined.

(* Exercise 2's 等价 X_T → FX, general 定理 at FX... （已译） *)
Definition kleisli_point_FX_equivalence :
  EquivalenceOfCategories
    (Kleisli_Comparison_Restrict kleisli_point_adj kleisli_point_FX
       kleisli_point_FX_full (fun _ => I)) :=
  Kleisli_Comparison_Restrict_Equivalence kleisli_point_adj kleisli_point_FX
    kleisli_point_FX_full (fun _ => I) kleisli_point_FX_pick.

(* ... is not an isomorphism. *)
Theorem kleisli_point_FX_not_iso :
  @Isomorphism StrictCat XT1 (Sub _1 kleisli_point_FX) → False.
Proof.
  intro i.
  apply kleisli_point_not_skeletal.
  exact (Skeletal_StrictCat_invariant (iso_sym i) kleisli_point_FX_skeletal).
Qed.

(* Every algebra one-point 单子 free: structure map
 h : T A = 1 ~> A 唯一箭头 A ~> 1 inverse. （已译） *)
Definition kleisli_point_every_algebra_free : @EveryAlgebraFree SetsC _ T1.
Proof.
  intros [A alg].
  exists A.
  unshelve eapply Build_Isomorphism.
  - unshelve econstructor.
    + exact (@t_alg _ _ _ _ alg).
    + symmetry. exact (@t_action _ _ _ _ alg).
  - unshelve econstructor.
    + exact (@one SetsC Sets_Terminal A).
    + apply (@one_unique SetsC Sets_Terminal).
  - assert (E : @t_alg _ _ _ _ alg ∘ @one SetsC Sets_Terminal A ≈ id[A]).
    { rewrite (@one_unique SetsC Sets_Terminal A (@one SetsC Sets_Terminal A)
                 (@ret SetsC _ T1 A)).
      apply (@t_id _ _ _ _ alg). }
    exact E.
  - exact (@one_unique SetsC Sets_Terminal _
             (@one SetsC Sets_Terminal _ ∘ @t_alg _ _ _ _ alg) id).
Defined.

(* Hence K : C_T ⟶ C^T is an equivalence here, by the biconditional. *)
Definition kleisli_point_K_equivalence :
  EquivalenceOfCategories (@Kleisli_EM SetsC _ T1) :=
  snd (Kleisli_EM_equivalence_iff _) kleisli_point_every_algebra_free.

End PointMonad.
