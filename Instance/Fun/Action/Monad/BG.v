(* * * Riehl's Set^BG: evaluation monadic, monadicity 定理 （已译） *)

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
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
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
Require Import Category.Instance.Fun.Eval.
Require Import Category.Instance.Fun.Action.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.
Require Import Category.Instance.Fun.Action.Monad.

Generalizable All Variables.

(*
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 nLab: https://ncatlab.org/nlab/show/monadicity+theorem
 nLab: https://ncatlab.org/nlab/show/action

   本文件给出单子相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* * ** Riehl's Set^BG forgetful 函子 （已译） *)

(* The functor category [Deloop M, Sets], hom level o (see UNIVERSES). *)
Definition SetBG@{o so} (M : MonObject@{o o o}) : Category@{so o o} :=
  @Fun@{o o so o so o so} (Deloop@{o o} M) Sets@{o so}.

(* Riehl's U: evaluation at the one object of BM. *)
Definition U_BG@{o so} (M : MonObject@{o o o}) :
  SetBG@{o so} M ⟶ Sets@{o so} :=
  @Eval@{o o so o so so} (Deloop@{o o} M) Sets@{o so} ttt.

(* Riehl's 左伴随: X goes 函子 whose value free
 M-set M × X. （已译） *)
Definition F_BG@{o so} (M : MonObject@{o o o}) :
  Sets@{o so} ⟶ SetBG@{o so} M :=
  MSet_from@{so o o so o} M ◯ MSet_Free@{o so} M.

(* Evaluation is [MSet_to] followed by forgetting the action, in both data
   fields. *)
Example U_BG_obj@{o so} (M : MonObject@{o o o}) (P : SetBG@{o so} M) :
  fobj[U_BG@{o so} M] P = fobj[MSet_Forget@{o so} M ◯ MSet_to@{so o} M] P :=
  eq_refl.

Example U_BG_map@{o so} (M : MonObject@{o o o}) (P Q : SetBG@{o so} M)
  (η : P ~{SetBG@{o so} M}~> Q) :
  fmap[U_BG@{o so} M] η = fmap[MSet_Forget@{o so} M ◯ MSet_to@{so o} M] η :=
  eq_refl.

(** ** The free/forgetful adjunction *)

(* A transformation φ : F X ⟹ P restricts to x ↦ φ (u, x). *)
Definition BG_restrict@{o so} {M : MonObject@{o o o}}
  {X : SetoidObject@{o o}} {P : SetBG@{o so} M}
  (φ : fobj[F_BG@{o so} M] X ~{SetBG@{o so} M}~> P) :
  X ~{Sets@{o so}}~> fobj[U_BG@{o so} M] P.
Proof.
  unshelve refine
    (@Build_SetoidMorphism X _ (fobj[P] ttt) _
       (fun x => transform[φ] ttt (mon_unit, x)) _).
  intros x y Hxy. apply (proper_morphism (transform[φ] ttt)).
  split; [ reflexivity | exact Hxy ].
Defined.

(* 相关说明。 （已译） *)
Definition BG_extend@{o so} {M : MonObject@{o o o}}
  {X : SetoidObject@{o o}} {P : SetBG@{o so} M}
  (ψ : X ~{Sets@{o so}}~> fobj[U_BG@{o so} M] P) :
  fobj[F_BG@{o so} M] X ~{SetBG@{o so} M}~> P :=
  to (MSet_round_iso@{so o o so o} P)
    ∘ fmap[MSet_from@{so o o so o} M]
        (@MSet_extend@{o so} M X (action_of_functor@{o o o so o} P) ψ).

Definition BG_adj_iso@{o so} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) (P : SetBG@{o so} M) :
  @Isomorphism Sets@{o so}
    (@Build_SetoidObject
       (@hom (SetBG@{o so} M) (fobj[F_BG@{o so} M] X) P)
       (@homset (SetBG@{o so} M) (fobj[F_BG@{o so} M] X) P))
    (@Build_SetoidObject
       (@hom Sets@{o so} X (fobj[U_BG@{o so} M] P))
       (@homset Sets@{o so} X (fobj[U_BG@{o so} M] P))).
Proof.
  unshelve refine
    (@Build_Isomorphism Sets@{o so}
       (@Build_SetoidObject
          (@hom (SetBG@{o so} M) (fobj[F_BG@{o so} M] X) P)
          (@homset (SetBG@{o so} M) (fobj[F_BG@{o so} M] X) P))
       (@Build_SetoidObject
          (@hom Sets@{o so} X (fobj[U_BG@{o so} M] P))
          (@homset Sets@{o so} X (fobj[U_BG@{o so} M] P)))
       (@Build_SetoidMorphism
          (@hom (SetBG@{o so} M) (fobj[F_BG@{o so} M] X) P)
          (@homset (SetBG@{o so} M) (fobj[F_BG@{o so} M] X) P)
          (@hom Sets@{o so} X (fobj[U_BG@{o so} M] P))
          (@homset Sets@{o so} X (fobj[U_BG@{o so} M] P))
          (fun φ => @BG_restrict M X P φ) _)
       (@Build_SetoidMorphism
          (@hom Sets@{o so} X (fobj[U_BG@{o so} M] P))
          (@homset Sets@{o so} X (fobj[U_BG@{o so} M] P))
          (@hom (SetBG@{o so} M) (fobj[F_BG@{o so} M] X) P)
          (@homset (SetBG@{o so} M) (fobj[F_BG@{o so} M] X) P)
          (fun ψ => @BG_extend M X P ψ) _) _ _).
  - intros φ φ' Hφ x. exact (Hφ ttt (mon_unit, x)).
  - intros ψ ψ' Hψ [] [g x]; simpl.
    apply (proper_morphism (@fmap _ _ P ttt ttt g)). exact (Hψ x).
  - intros ψ x; simpl. exact (@fmap_id _ _ P ttt (ψ x)).
  - intros φ [] [g x]; simpl.
    transitivity
      (transform[φ] ttt
         (@fmap _ _ (fobj[F_BG@{o so} M] X) ttt ttt g (mon_unit, x))).
    + exact (@naturality _ _ _ _ φ ttt ttt g (mon_unit, x)).
    + apply (proper_morphism (transform[φ] ttt)).
      split; [ exact (mon_op_unit_r g) | reflexivity ].
Defined.

(* Riehl's adjunction, literally: F ⊣ U on Set^BM. *)
Definition BG_adj@{o so} (M : MonObject@{o o o}) :
  @Adjunction@{so o o so o o o o so o so} (SetBG@{o so} M) Sets@{o so}
    (F_BG@{o so} M) (U_BG@{o so} M).
Proof.
  unshelve refine
    (@Build_Adjunction' (SetBG@{o so} M) Sets@{o so}
       (F_BG@{o so} M) (U_BG@{o so} M) (fun X P => BG_adj_iso M X P) _ _).
  - intros X Y P f g x; simpl. reflexivity.
  - intros X P Q f g x; simpl. reflexivity.
Defined.

(* 相关说明。 （已译） *)

(* A cofork of transformations whose [MSet_to]-image is a coequalizer of
   M-sets is a coequalizer of functors: the descended equivariant map is
   the one component of the descended transformation. *)
Definition MSet_to_reflects_coeq@{o so} {M : MonObject@{o o o}}
  {P Q R : SetBG@{o so} M}
  (p q : P ~{SetBG@{o so} M}~> Q) (e : Q ~{SetBG@{o so} M}~> R)
  (E : @IsCoequalizer (MSet@{so so o o o o o o} M) _ _
         (fmap[MSet_to@{so o} M] p) (fmap[MSet_to@{so o} M] q)
         (fobj[MSet_to@{so o} M] R) (fmap[MSet_to@{so o} M] e)) :
  @IsCoequalizer (SetBG@{o so} M) P Q p q R e.
Proof.
  unshelve refine (@Build_IsCoequalizer _ _ _ _ _ _ _ _ _).
  - intros [] y. exact (cofork E y).
  - intros W h Hh.
    pose (D := coeq_desc E (fmap[MSet_to@{so o} M] h) (fun y => Hh ttt y)).
    unshelve eapply Build_Unique.
    + unshelve refine (@Build_Transform _ _ _ _ _ _ _).
      * intros []. exact (equiv_map (unique_obj D)).
      * intros [] [] g z; simpl. symmetry. exact (equivar (unique_obj D) g z).
      * intros [] [] g z; simpl. exact (equivar (unique_obj D) g z).
    + intros [] y. exact (unique_property D y).
    + intros v Hv [] z.
      exact (uniqueness D (fmap[MSet_to@{so o} M] v) (fun y => Hv ttt y) z).
Defined.

(* The coequalizing transformation onto created 函子: component e,
 自然性 equivariance Instance/Fun/Action/Monad.v's
 [CreatedE]. （已译） *)
Definition BGCreatedE@{o so} {M : MonObject@{o o o}} {P Q : SetBG@{o so} M}
  (p q : P ~{SetBG@{o so} M}~> Q)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[U_BG@{o so} M] p) (fmap[U_BG@{o so} M] q)) :
  Q ~{SetBG@{o so} M}~>
    fobj[MSet_from@{so o o so o} M]
      (CreatedAct@{o so} (fmap[MSet_to@{so o} M] p)
         (fmap[MSet_to@{so o} M] q) S).
Proof.
  unshelve refine (@Build_Transform _ _ _ _ _ _ _).
  - intros []. exact (scoeq_e S).
  - intros [] [] g y; simpl. symmetry.
    exact (equivar (CreatedE@{o so} (fmap[MSet_to@{so o} M] p)
                      (fmap[MSet_to@{so o} M] q) S) g y).
  - intros [] [] g y; simpl.
    exact (equivar (CreatedE@{o so} (fmap[MSet_to@{so o} M] p)
                      (fmap[MSet_to@{so o} M] q) S) g y).
Defined.

(* [CreatedE_is_coeq], moved along [MSet_action_round_iso] and read back
   through [MSet_to]. *)
Definition BGCreatedE_is_coeq@{o so} {M : MonObject@{o o o}}
  {P Q : SetBG@{o so} M} (p q : P ~{SetBG@{o so} M}~> Q)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[U_BG@{o so} M] p) (fmap[U_BG@{o so} M] q)) :
  @IsCoequalizer (SetBG@{o so} M) P Q p q
    (fobj[MSet_from@{so o o so o} M]
       (CreatedAct@{o so} (fmap[MSet_to@{so o} M] p)
          (fmap[MSet_to@{so o} M] q) S))
    (BGCreatedE@{o so} p q S).
Proof.
  apply MSet_to_reflects_coeq.
  refine (coequalizer_along_iso _ _ _
            (CreatedE_is_coeq@{o so} (fmap[MSet_to@{so o} M] p)
               (fmap[MSet_to@{so o} M] q) S)
            (MSet_action_round_iso
               (CreatedAct@{o so} (fmap[MSet_to@{so o} M] p)
                  (fmap[MSet_to@{so o} M] q) S))
            (fmap[MSet_to@{so o} M] (BGCreatedE@{o so} p q S)) _).
  intros y. reflexivity.
Defined.

Definition U_BG_creates@{o so} (M : MonObject@{o o o}) :
  CreatesUSplitCoequalizers (U_BG@{o so} M).
Proof.
  unshelve refine (@Build_CreatesUSplitCoequalizers _ _ _ _ _).
  - intros P Q p q S.
    exists (fobj[MSet_from@{so o o so o} M]
              (CreatedAct@{o so} (fmap[MSet_to@{so o} M] p)
                 (fmap[MSet_to@{so o} M] q) S)).
    exists (BGCreatedE@{o so} p q S).
    split.
    + exact (BGCreatedE_is_coeq@{o so} p q S).
    + exists (@iso_id Sets@{o so} (scoeq_obj S)).
      intros y; simpl. reflexivity.
  - intros P Q p q S R e He i Hi.
    apply MSet_to_reflects_coeq.
    refine (Reflected_is_coeq@{o so} (fmap[MSet_to@{so o} M] p)
              (fmap[MSet_to@{so o} M] q) S (fobj[MSet_to@{so o} M] R)
              (fmap[MSet_to@{so o} M] e) _ i Hi).
    intros y. exact (He ttt y).
Defined.

(* The lift nose: value Z, action e (g · s z), arrow e the
 恒等 comparison 同构. （已译） *)
Example bg_created_carrier@{o so} {M : MonObject@{o o o}}
  {P Q : SetBG@{o so} M} (p q : P ~{SetBG@{o so} M}~> Q)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[U_BG@{o so} M] p) (fmap[U_BG@{o so} M] q)) :
  fobj[`1 (@create_coeq _ _ _ (U_BG_creates@{o so} M) P Q p q S)] ttt
  = scoeq_obj S := eq_refl.

Example bg_created_action@{o so} {M : MonObject@{o o o}}
  {P Q : SetBG@{o so} M} (p q : P ~{SetBG@{o so} M}~> Q)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[U_BG@{o so} M] p) (fmap[U_BG@{o so} M] q))
  (g : carrier M) (z : carrier (scoeq_obj S)) :
  @fmap _ _ (`1 (@create_coeq _ _ _ (U_BG_creates@{o so} M) P Q p q S))
    ttt ttt g z
  = scoeq_e S (@fmap _ _ Q ttt ttt g (scoeq_s S z)) := eq_refl.

Example bg_created_arrow@{o so} {M : MonObject@{o o o}}
  {P Q : SetBG@{o so} M} (p q : P ~{SetBG@{o so} M}~> Q)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[U_BG@{o so} M] p) (fmap[U_BG@{o so} M] q)) :
  transform[`1 (`2 (@create_coeq _ _ _ (U_BG_creates@{o so} M) P Q p q S))]
    ttt
  = scoeq_e S := eq_refl.

Example bg_created_iso@{o so} {M : MonObject@{o o o}}
  {P Q : SetBG@{o so} M} (p q : P ~{SetBG@{o so} M}~> Q)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[U_BG@{o so} M] p) (fmap[U_BG@{o so} M] q)) :
  `1 (snd (`2 (`2 (@create_coeq _ _ _ (U_BG_creates@{o so} M) P Q p q S))))
  = @iso_id Sets@{o so} (scoeq_obj S) := eq_refl.

(* * ** Riehl's Exercise 5.5.iv, literally, monadicity 定理 （已译） *)

Definition BG_beck_equivalence@{o so} (M : MonObject@{o o o}) :
  EquivalenceOfCategories (EM_Comparison (BG_adj@{o so} M)) :=
  beck_monadicity (BG_adj@{o so} M) (U_BG_creates@{o so} M).

Definition U_BG_Monadic@{o so} (M : MonObject@{o o o}) :
  @Monadic@{so so so so so o so so} (SetBG@{o so} M) Sets@{o so}
    (U_BG@{o so} M).
Proof.
  exists (F_BG@{o so} M).
  exists (BG_adj@{o so} M).
  exact (BG_beck_equivalence@{o so} M).
Defined.

(* A transformation invertible at the one object is invertible. *)
Definition U_BG_reflects@{o so} (M : MonObject@{o o o}) :
  ReflectsIsos (U_BG@{o so} M) :=
  creates_split_reflects_isos _ (U_BG_creates@{o so} M).

(** ** The induced monad *)

Definition BGMonad@{o so} (M : MonObject@{o o o}) :
  @Monad Sets@{o so} (U_BG@{o so} M ◯ F_BG@{o so} M) :=
  Adjunction_Induced_Monad (BG_adj@{o so} M).

(* Set^BM isomorphic Cat algebras 单子, the
 comparison 函子 itself. （已译） *)
Definition BG_EM_iso@{o so c} (M : MonObject@{o o o}) :
  @Isomorphism Cat@{c so so so o} (SetBG@{o so} M)
    (@EilenbergMoore@{so so so o} Sets@{o so}
       (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M)) :=
  Equivalence_to_Cat_Iso (BG_beck_equivalence@{o so} M).

Example BG_EM_iso_to@{o so c} (M : MonObject@{o o o}) :
  to (BG_EM_iso@{o so c} M) = EM_Comparison (BG_adj@{o so} M) := eq_refl.

(* The 单子 read back: T X = M × X, T f = M × f, η x = (u u, x) and
 μ (g₁, (g₂, x)) = (g₁ g₂, x). （已译） *)
Example BG_T_obj@{o so} (M : MonObject@{o o o}) (X : SetoidObject@{o o}) :
  fobj[U_BG@{o so} M ◯ F_BG@{o so} M] X = act_prod M X := eq_refl.

Example BG_T_map@{o so} (M : MonObject@{o o o}) (X Y : SetoidObject@{o o})
  (f : X ~{Sets@{o so}}~> Y) :
  fmap[U_BG@{o so} M ◯ F_BG@{o so} M] f = act_prod_map M f := eq_refl.

Example BG_ret@{o so} (M : MonObject@{o o o}) (X : SetoidObject@{o o})
  (x : carrier X) :
  (@ret _ _ (BGMonad@{o so} M) X) x = (mon_op mon_unit mon_unit, x) :=
  eq_refl.

Example BG_join@{o so} (M : MonObject@{o o o}) (X : SetoidObject@{o o})
  (g1 g2 : carrier M) (x : carrier X) :
  (@join _ _ (BGMonad@{o so} M) X) (g1, (g2, x)) = (mon_op g1 g2, x) :=
  eq_refl.

(* The same two readbacks as functions, which is stronger, since Coq's
   [prod] has no eta. *)
Example BG_ret_fun@{o so} (M : MonObject@{o o o}) (X : SetoidObject@{o o}) :
  (fun x : carrier X => (@ret _ _ (BGMonad@{o so} M) X) x)
  = (fun x => (mon_op mon_unit mon_unit, x)) := eq_refl.

Example BG_join_fun@{o so} (M : MonObject@{o o o}) (X : SetoidObject@{o o}) :
  (fun p => (@join _ _ (BGMonad@{o so} M) X) p)
  = (fun p : carrier M * (carrier M * carrier X) =>
       (mon_op (fst p) (fst (snd p)), snd (snd p))) := eq_refl.

(* * ** Against 单子 Instance/Fun/Action/Monad.v （已译） *)

(* The two 函子, 恒等 components. （已译） *)
Definition BG_T_ActF@{o so} (M : MonObject@{o o o}) :
  U_BG@{o so} M ◯ F_BG@{o so} M ≈ ActF@{o so} M.
Proof.
  exists (fun X => @iso_id Sets@{o so} (act_prod M X)).
  intros X Y f p. simpl. split; reflexivity.
Defined.

(* 相关说明。 （已译） *)
Definition BG_ret_ActMonad@{o so} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) (x : carrier X) :
  (@ret _ _ (BGMonad@{o so} M) X) x ≈ (@ret _ _ (ActMonad@{o so} M) X) x.
Proof.
  split; [ exact (mon_op_unit_l mon_unit) | reflexivity ].
Defined.

(* 相关说明。 （已译） *)
Example BG_join_ActMonad@{o so} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) (p : carrier M * (carrier M * carrier X)) :
  (@join _ _ (BGMonad@{o so} M) X) p = (@join _ _ (ActMonad@{o so} M) X) p :=
  eq_refl.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition BG_Act_alg@{o so} (M : MonObject@{o o o}) (a : SetoidObject@{o o})
  (h : @TAlgebra Sets@{o so} (U_BG@{o so} M ◯ F_BG@{o so} M)
         (BGMonad@{o so} M) a) :
  @TAlgebra Sets@{o so} (ActF@{o so} M) (ActMonad@{o so} M) a.
Proof.
  unshelve refine
    (@Build_TAlgebra Sets@{o so} (ActF@{o so} M) (ActMonad@{o so} M) a
       (@t_alg _ _ _ _ h) _ _).
  - intros x. simpl.
    transitivity (@t_alg _ _ _ _ h (mon_op mon_unit mon_unit, x)).
    + apply (proper_morphism (@t_alg _ _ _ _ h)).
      split; [ symmetry; exact (mon_op_unit_l mon_unit) | reflexivity ].
    + exact (@t_id _ _ _ _ h x).
  - intros p. exact (@t_action _ _ _ _ h p).
Defined.

(* The same reading other way; it not assembled 函子. （已译） *)
Definition Act_BG_alg@{o so} (M : MonObject@{o o o}) (a : SetoidObject@{o o})
  (h : @TAlgebra Sets@{o so} (ActF@{o so} M) (ActMonad@{o so} M) a) :
  @TAlgebra Sets@{o so} (U_BG@{o so} M ◯ F_BG@{o so} M)
    (BGMonad@{o so} M) a.
Proof.
  unshelve refine
    (@Build_TAlgebra Sets@{o so} (U_BG@{o so} M ◯ F_BG@{o so} M)
       (BGMonad@{o so} M) a (@t_alg _ _ _ _ h) _ _).
  - intros x. simpl.
    transitivity (@t_alg _ _ _ _ h (mon_unit, x)).
    + apply (proper_morphism (@t_alg _ _ _ _ h)).
      split; [ exact (mon_op_unit_l mon_unit) | reflexivity ].
    + exact (@t_id _ _ _ _ h x).
  - intros p. exact (@t_action _ _ _ _ h p).
Defined.

(* Mac Lane's θ*, 恒等-component 同构 [BG_T_ActF]:
 恒等 carriers, structure maps arrows. （已译） *)
Definition BG_Act_EM@{o so} (M : MonObject@{o o o}) :
  @EilenbergMoore@{so so so o} Sets@{o so} (U_BG@{o so} M ◯ F_BG@{o so} M)
    (BGMonad@{o so} M)
  ⟶ @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
      (ActMonad@{o so} M).
Proof.
  unshelve refine
    (@Build_Functor
       (@EilenbergMoore@{so so so o} Sets@{o so}
          (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M))
       (@EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
          (ActMonad@{o so} M))
       (fun x => (`1 x; BG_Act_alg M (`1 x) (`2 x)))
       (fun x y f =>
          @Build_TAlgebraHom Sets@{o so} (ActF@{o so} M) (ActMonad@{o so} M)
            (`1 x) (`1 y) (BG_Act_alg M (`1 x) (`2 x))
            (BG_Act_alg M (`1 y) (`2 y)) (@t_alg_hom _ _ _ _ _ _ _ f)
            (@t_alg_hom_commutes _ _ _ _ _ _ _ f)) _ _ _).
  - intros x y f g E. exact E.
  - intros x z. reflexivity.
  - intros x y z f g w. reflexivity.
Defined.

Example BG_Act_EM_carrier@{o so} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M)) :
  `1 (fobj[BG_Act_EM@{o so} M] x) = `1 x := eq_refl.

Example BG_Act_EM_alg@{o so} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M)) :
  @t_alg _ _ _ _ (`2 (fobj[BG_Act_EM@{o so} M] x)) = @t_alg _ _ _ _ (`2 x) :=
  eq_refl.

(* Mac Lane's G^T ∘ θ* = G^T', on the nose in both data fields. *)
Example BG_Act_EM_forget_obj@{o so} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M)) :
  fobj[@EM_Forget _ _ (ActMonad@{o so} M) ◯ BG_Act_EM@{o so} M] x
  = fobj[@EM_Forget _ _ (BGMonad@{o so} M)] x := eq_refl.

Example BG_Act_EM_forget_map@{o so} (M : MonObject@{o o o})
  (x y : @EilenbergMoore@{so so so o} Sets@{o so}
           (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M))
  (f : x ~> y) :
  fmap[@EM_Forget _ _ (ActMonad@{o so} M) ◯ BG_Act_EM@{o so} M] f
  = fmap[@EM_Forget _ _ (BGMonad@{o so} M)] f := eq_refl.

(* The tie 对象: θ* after file's comparison 函子, against
 comparison 函子 [MSet_adj] after [MSet_to], [to] leg of
 [Fun_EM_iso]. （已译） *)
Example tie_carrier@{o so} (M : MonObject@{o o o}) (P : SetBG@{o so} M) :
  `1 (fobj[BG_Act_EM@{o so} M ◯ EM_Comparison (BG_adj@{o so} M)] P)
  = `1 (fobj[EM_Comparison (MSet_adj@{o so} M) ◯ MSet_to@{so o} M] P) :=
  eq_refl.

Example tie_alg@{o so} (M : MonObject@{o o o}) (P : SetBG@{o so} M)
  (g : carrier M) (z : carrier (fobj[P] ttt)) :
  @t_alg _ _ _ _
    (`2 (fobj[BG_Act_EM@{o so} M ◯ EM_Comparison (BG_adj@{o so} M)] P))
    (g, z)
  = @t_alg _ _ _ _
      (`2 (fobj[EM_Comparison (MSet_adj@{o so} M) ◯ MSet_to@{so o} M] P))
      (g, z) := eq_refl.

(* 相关说明。 （已译） *)
Example tie_alg_fun@{o so} (M : MonObject@{o o o}) (P : SetBG@{o so} M) :
  (fun p => @t_alg _ _ _ _
     (`2 (fobj[BG_Act_EM@{o so} M ◯ EM_Comparison (BG_adj@{o so} M)] P)) p)
  = (fun p => @t_alg _ _ _ _
       (`2 (fobj[EM_Comparison (MSet_adj@{o so} M) ◯ MSet_to@{so o} M] P))
       p) := eq_refl.

(* The tie 函子, Cat, 恒等 components. （已译） *)
Definition tie@{o so c} (M : MonObject@{o o o}) :
  @equiv _
    (@homset Cat@{c so so so o} (SetBG@{o so} M)
       (@EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
          (ActMonad@{o so} M)))
    (BG_Act_EM@{o so} M ◯ EM_Comparison (BG_adj@{o so} M))
    (to (Fun_EM_iso@{o so c} M)).
Proof.
  unshelve eexists.
  - intros P.
    unshelve refine (@Build_Isomorphism _ _ _ _ _ _ _).
    + unshelve refine
        (@Build_TAlgebraHom _ _ _ _ _ _ _ (@id Sets@{o so} _) _).
      intros [g z]. simpl. reflexivity.
    + unshelve refine
        (@Build_TAlgebraHom _ _ _ _ _ _ _ (@id Sets@{o so} _) _).
      intros [g z]. simpl. reflexivity.
    + intros z. simpl. reflexivity.
    + intros z. simpl. reflexivity.
  - intros P Q f z. simpl. reflexivity.
Defined.

(** ** Groups *)

(* Riehl's statement for a group G, at Construction/Deloop.v's groups. *)
Definition GSet_BG_Monadic@{o so}
  (G : Category.Construction.Deloop.GrpObject@{o o o}) :
  @Monadic@{so so so so so o so so} (SetBG@{o so} G) Sets@{o so}
    (U_BG@{o so} G) :=
  U_BG_Monadic@{o so} G.

(* At Instance/Grp.v's groups, through Instance/Grp/Free.v's
   [grp_deloop_monoid]. *)
Definition GSet_BG_Monadic_Grp@{o so}
  (G : Category.Instance.Grp.GrpObject@{o o o}) :
  @Monadic@{so so so so so o so so}
    (SetBG@{o so} (grp_deloop_monoid@{o o o} G)) Sets@{o so}
    (U_BG@{o so} (grp_deloop_monoid@{o o o} G)) :=
  U_BG_Monadic@{o so} (grp_deloop_monoid@{o o o} G).

(* At Structure/Group.v's groups internal (Sets, ×), through
 Instance/Grp.v's [GroupObject_GrpObject], asks the
 carrier's ≈ 命题. （已译） *)
Definition GSet_BG_Monadic_GroupObject@{o so} (X : Sets@{o so})
  (PX : PropEquiv@{o o} X)
  (GO : @GroupObject@{so o so} Sets@{o so} Sets_CartesianMonoidal X) :
  @Monadic@{so so so so so o so so}
    (SetBG@{o so}
       (grp_deloop_monoid@{o o o} (GroupObject_GrpObject X PX GO)))
    Sets@{o so}
    (U_BG@{o so}
       (grp_deloop_monoid@{o o o} (GroupObject_GrpObject X PX GO))) :=
  U_BG_Monadic@{o so}
    (grp_deloop_monoid@{o o o} (GroupObject_GrpObject X PX GO)).
