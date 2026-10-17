Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Theory.Equivalence.Strict.
Require Import Category.Theory.Skeleton.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Sets.
Require Import Category.Instance.StrictCat.
Require Import Category.Adjunction.Map.
Require Import Category.Adjunction.LeftInverse.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Morphism.
Require Import Category.Monad.Kleisli.
Require Import Category.Monad.Kleisli.Adjunction.

Generalizable All Variables.

(** * Free algebras for a monad: restricted adjunctions and the Kleisli
      comparison functor *)

(*
   Book: Riehl, "Category Theory in Context", Lemma 5.2.14 and the
   nLab: https://ncatlab.org/nlab/show/Kleisli+category
   nLab: https://ncatlab.org/nlab/show/Eilenberg-Moore+category

   本文件给出比较函子相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(** ** Construction 1: restricting an adjunction to a full subcategory *)

Section Restrict.

#[local] Obligation Tactic := idtac.

Context {X A : Category}.
Context {F : X ⟶ A} {G : A ⟶ X}.
Context (Adj : F ⊣ G).
Context (S : Subcategory A) (full : Full A S).
Context (mem : ∀ x : X, sobj A S (F x)).

(* F_B: F with its codomain restricted to B. *)
Program Definition Restricted_Left : X ⟶ Sub A S := {|
  fobj := fun x => (F x; mem x);
  fmap := fun x y f => (fmap[F] f; full _ _ _ _ (fmap[F] f))
|}.
Next Obligation. intros x y f g Hfg; simpl; now rewrite Hfg. Qed.
Next Obligation. intros x; simpl; apply fmap_id. Qed.
Next Obligation. intros x y z f g; simpl; apply fmap_comp. Qed.

(* G_B: G with its domain restricted to B. *)
Definition Restricted_Right : Sub A S ⟶ X := G ◯ Incl A S.

(* φ_B: hom_B(F_B x, b) = hom_A(F x, b) ≅ hom_X(x, G b) = hom_X(x, G_B b). *)
Program Definition Restricted_adj_iso (x : X) (b : Sub A S) :
  @Isomorphism Sets
    {| carrier := @hom (Sub A S) (Restricted_Left x) b
     ; is_setoid := @homset (Sub A S) (Restricted_Left x) b |}
    {| carrier := @hom X x (Restricted_Right b)
     ; is_setoid := @homset X x (Restricted_Right b) |} := {|
  to   := {| morphism := fun f => to (@adj _ _ _ _ Adj x (`1 b)) (`1 f) |};
  from := {| morphism := fun g =>
               (from (@adj _ _ _ _ Adj x (`1 b)) g;
                full _ _ (mem x) (`2 b) (from (@adj _ _ _ _ Adj x (`1 b)) g)) |}
|}.
Next Obligation. intros x b f g Hfg; simpl in *; now rewrite Hfg. Qed.
Next Obligation. intros x b f g Hfg; simpl in *; now rewrite Hfg. Qed.
Next Obligation. intros x b g; simpl; apply from_adj_comp_law. Qed.
Next Obligation. intros x b f; simpl; apply to_adj_comp_law. Qed.

Definition Restricted_Adjunction : Restricted_Left ⊣ Restricted_Right.
Proof using Adj full mem.
  unshelve eapply (@Build_Adjunction' (Sub A S) X Restricted_Left
                     Restricted_Right Restricted_adj_iso).
  - intros x y z f g; simpl. apply to_adj_nat_l.
  - intros x y z f g; simpl. apply to_adj_nat_r.
Defined.

(* "This second adjunction defines in X the same monad as did the first":
   the endofunctors agree on both actions, and so do η and μ = G ε F. *)

Example Restricted_monad_obj (x : X) :
  fobj[Restricted_Right ◯ Restricted_Left] x = fobj[G ◯ F] x := eq_refl.

Example Restricted_monad_map (x y : X) (f : x ~> y) :
  fmap[Restricted_Right ◯ Restricted_Left] f = fmap[G ◯ F] f := eq_refl.

Example Restricted_unit_agrees (x : X) :
  @ret X (Restricted_Right ◯ Restricted_Left)
       (Adjunction_Induced_Monad Restricted_Adjunction) x
    = @ret X (G ◯ F) (Adjunction_Induced_Monad Adj) x := eq_refl.

Example Restricted_join_agrees (x : X) :
  @join X (Restricted_Right ◯ Restricted_Left)
        (Adjunction_Induced_Monad Restricted_Adjunction) x
    = @join X (G ◯ F) (Adjunction_Induced_Monad Adj) x := eq_refl.

Theorem Restricted_Monad_agrees :
  Restricted_Right ◯ Restricted_Left ≈ G ◯ F.
Proof.
  exists (fun x => iso_id).
  intros x y f; simpl. now rewrite id_left, id_right.
Defined.

Example Restricted_Monad_agrees_iso (x : X) :
  `1 Restricted_Monad_agrees x = iso_id := eq_refl.

(* The two monads as objects of Monad/Morphism.v's [Monads X]: isomorphic,
   with identity components both ways. *)

Definition Restricted_Monad_to :
  MonadHom (Adjunction_Induced_Monad Restricted_Adjunction)
           (Adjunction_Induced_Monad Adj).
Proof.
  unshelve refine
    {| mh_transform :=
         Build_Transform' (F:=Restricted_Right ◯ Restricted_Left) (G:=G ◯ F)
           (fun x => id) _ |}.
  - intros x y f; simpl. rewrite id_left, id_right. reflexivity.
  - intros x; simpl. apply id_left.
  - intros x; simpl. rewrite !id_left, !fmap_id, id_right. reflexivity.
Defined.

Definition Restricted_Monad_from :
  MonadHom (Adjunction_Induced_Monad Adj)
           (Adjunction_Induced_Monad Restricted_Adjunction).
Proof.
  unshelve refine
    {| mh_transform :=
         Build_Transform' (F:=G ◯ F) (G:=Restricted_Right ◯ Restricted_Left)
           (fun x => id) _ |}.
  - intros x y f; simpl. rewrite id_left, id_right. reflexivity.
  - intros x; simpl. apply id_left.
  - intros x; simpl. rewrite !id_left, !fmap_id, id_right. reflexivity.
Defined.

Definition Restricted_Monad_iso :
  @Isomorphism (Monads X)
    (Restricted_Right ◯ Restricted_Left;
     Adjunction_Induced_Monad Restricted_Adjunction)
    (G ◯ F; Adjunction_Induced_Monad Adj).
Proof.
  unshelve refine (@Build_Isomorphism (Monads X)
                     (Restricted_Right ◯ Restricted_Left;
                      Adjunction_Induced_Monad Restricted_Adjunction)
                     (G ◯ F; Adjunction_Induced_Monad Adj)
                     Restricted_Monad_to Restricted_Monad_from _ _).
  - intros x; simpl. apply id_left.
  - intros x; simpl. apply id_left.
Defined.

Example Restricted_Monad_iso_to (x : X) :
  transform[mh_transform (to Restricted_Monad_iso)] x = id := eq_refl.

Example Restricted_Monad_iso_from (x : X) :
  transform[mh_transform (from Restricted_Monad_iso)] x = id := eq_refl.

End Restrict.

Arguments Restricted_Right {X A} G S.

(* ------------------------------------------------------------------------ *)
(** ** Theorem 2: the comparison functor L : X_T ⟶ A *)

Section KleisliComparison.

#[local] Obligation Tactic := idtac.

Context {X A : Category}.
Context {F : X ⟶ A} {G : A ⟶ X}.
Context (Adj : F ⊣ G).

Notation T := (@Adjunction_Induced_Monad A X F G Adj).
Notation XT := (@Kleisli X (G ◯ F) T).

Lemma Kleisli_Comparison_fmap_id (x : X) :
  from (@adj _ _ _ _ Adj x (F x)) (@unit _ _ _ _ Adj x) ≈ id[F x].
Proof. apply from_adj_unit. Qed.

Lemma Kleisli_Comparison_fmap_comp (x y z : X)
  (f : y ~{XT}~> z) (g : x ~{XT}~> y) :
  from (@adj _ _ _ _ Adj x (F z)) (f ∘[XT] g)
    ≈ from (@adj _ _ _ _ Adj y (F z)) f ∘ from (@adj _ _ _ _ Adj x (F y)) g.
Proof.
  rewrite !(from_adj_counit (H:=Adj)).
  simpl.
  rewrite !fmap_comp.
  rewrite !comp_assoc.
  rewrite <- (adj_counit_natural Adj (@counit _ _ _ _ Adj (F z) ∘ fmap[F] f)).
  rewrite !fmap_comp.
  rewrite !comp_assoc.
  reflexivity.
Qed.

(* L x = F x, and L f is the transpose ⌈f⌉ of f : x ~> G F y. *)
Program Definition Kleisli_Comparison : XT ⟶ A := {|
  fobj := fun x => F x;
  fmap := fun x y f => from (@adj _ _ _ _ Adj x (F y)) f
|}.
Next Obligation. intros x y f g Hfg; simpl; now rewrite Hfg. Qed.
Next Obligation. intros x; apply Kleisli_Comparison_fmap_id. Qed.
Next Obligation. intros x y z f g; apply Kleisli_Comparison_fmap_comp. Qed.

Example Kleisli_Comparison_obj (x : X) : fobj[Kleisli_Comparison] x = F x
  := eq_refl.

Example Kleisli_Comparison_map (x y : X) (f : x ~{XT}~> y) :
  fmap[Kleisli_Comparison] f = from (@adj _ _ _ _ Adj x (F y)) f := eq_refl.

Lemma Kleisli_Comparison_map_counit (x y : X) (f : x ~{XT}~> y) :
  fmap[Kleisli_Comparison] f ≈ @counit _ _ _ _ Adj (F y) ∘ fmap[F] f.
Proof. exact (from_adj_counit (H:=Adj) f). Qed.

(* G L = G_T *)
Theorem Kleisli_Comparison_Forget :
  G ◯ Kleisli_Comparison ≈ @Kleisli_Forget X (G ◯ F) T.
Proof.
  exists (fun x => iso_id).
  intros x y f; simpl.
  rewrite id_left, id_right.
  rewrite (from_adj_counit (H:=Adj) f).
  now rewrite fmap_comp.
Defined.

Example Kleisli_Comparison_Forget_iso (x : X) :
  `1 Kleisli_Comparison_Forget x = iso_id := eq_refl.

(* L F_T = F *)
Theorem Kleisli_Comparison_Free :
  Kleisli_Comparison ◯ @Kleisli_Free X (G ◯ F) T ≈ F.
Proof.
  exists (fun x => iso_id).
  intros x y f; simpl.
  rewrite id_left, id_right.
  symmetry. apply fmap_from_adj_unit.
Defined.

Example Kleisli_Comparison_Free_iso (x : X) :
  `1 Kleisli_Comparison_Free x = iso_id := eq_refl.

(* Mac Lane's G L = G_T and L F_T = F as strict functor equalities. *)
Definition Kleisli_Comparison_Forget_strict :
  @equiv _ (@Functor_StrictEq_Setoid XT X)
    (G ◯ Kleisli_Comparison) (@Kleisli_Forget X (G ◯ F) T).
Proof.
  refine (strict_equiv_of_id_cast_nat (G ◯ Kleisli_Comparison)
            (@Kleisli_Forget X (G ◯ F) T) (fun x => eq_refl) _).
  intros x y f; cbv beta; rewrite !id_cast_refl, id_left, id_right; simpl.
  rewrite (from_adj_counit (H:=Adj) f).
  now rewrite fmap_comp.
Defined.

Example Kleisli_Comparison_Forget_strict_obj (x : X) :
  `1 Kleisli_Comparison_Forget_strict x = eq_refl := eq_refl.

Definition Kleisli_Comparison_Free_strict :
  @equiv _ (@Functor_StrictEq_Setoid X A)
    (Kleisli_Comparison ◯ @Kleisli_Free X (G ◯ F) T) F.
Proof.
  refine (strict_equiv_of_id_cast_nat
            (Kleisli_Comparison ◯ @Kleisli_Free X (G ◯ F) T) F
            (fun x => eq_refl) _).
  intros x y f; cbv beta; rewrite !id_cast_refl, id_left, id_right; simpl.
  symmetry. apply fmap_from_adj_unit.
Defined.

Example Kleisli_Comparison_Free_strict_obj (x : X) :
  `1 Kleisli_Comparison_Free_strict x = eq_refl := eq_refl.

(* Full and faithful: the arrow action is the transposition bijection. *)
#[export] Program Instance Kleisli_Comparison_Full :
  Category.Theory.Functor.Full Kleisli_Comparison := {|
  prefmap := fun x y g => to (@adj _ _ _ _ Adj x (F y)) g
|}.
Next Obligation. intros x y g; simpl; apply to_adj_comp_law. Qed.

#[export] Program Instance Kleisli_Comparison_Faithful :
  Faithful Kleisli_Comparison.
Next Obligation.
  intros x y f g Hfg; simpl in *.
  rewrite <- (from_adj_comp_law (H:=Adj) f).
  rewrite <- (from_adj_comp_law (H:=Adj) g).
  now rewrite Hfg.
Qed.

(* Uniqueness: a functor agreeing with F on objects (Leibniz) and whose
   G-image agrees with G_T on arrows is L.  The arrow half of L F_T = F is
   not used. *)
Section Unique.

Context (L0 : XT ⟶ A) (Hobj : ∀ x, fobj[L0] x = F x).
Context (Hmap : ∀ (x y : X) (f : x ~{XT}~> y),
  fmap[G] (id_cast (Hobj y) ∘ fmap[L0] f ∘ id_cast (eq_sym (Hobj x)))
    ≈ fmap[@Kleisli_Forget X (G ◯ F) T] f).

Lemma Kleisli_Comparison_unique_map (x y : X) (f : x ~{XT}~> y) :
  id_cast (Hobj y) ∘ fmap[L0] f ∘ id_cast (eq_sym (Hobj x))
    ≈ fmap[Kleisli_Comparison] f.
Proof using Hmap.
  apply (snd (adj_univ (H:=Adj) _ _)).
  rewrite (to_adj_unit (H:=Adj)).
  rewrite (Hmap x y f); simpl.
  rewrite <- comp_assoc.
  rewrite <- (adj_unit_natural Adj f).
  rewrite comp_assoc.
  rewrite (@fmap_counit_unit _ _ _ _ Adj (F y)).
  apply id_left.
Qed.

Theorem Kleisli_Comparison_unique : L0 ≈ Kleisli_Comparison.
Proof using Hmap.
  exists (fun x => id_cast_iso (Hobj x)).
  intros x y f; simpl.
  rewrite <- (Kleisli_Comparison_unique_map x y f).
  rewrite !comp_assoc.
  rewrite id_cast_inv_l, id_left.
  rewrite <- comp_assoc.
  rewrite id_cast_inv_l.
  now rewrite id_right.
Qed.

(* ... and equal to L as a functor, strictly. *)
Theorem Kleisli_Comparison_unique_strict :
  @equiv _ (@Functor_StrictEq_Setoid XT A) L0 Kleisli_Comparison.
Proof using Hmap.
  refine (strict_equiv_of_id_cast_nat L0 Kleisli_Comparison Hobj _).
  intros x y f.
  rewrite <- (Kleisli_Comparison_unique_map x y f).
  rewrite <- !comp_assoc.
  rewrite id_cast_inv_l.
  now rewrite id_right.
Qed.

End Unique.

(* Mac Lane's hypotheses in the form existence delivers them: G L0 = G_T
   and L0 F_T = F as strict functor equalities, with the object equation of
   the first the G-image of that of the second ([coh]).  They give the
   hypotheses of the section above. *)
Theorem Kleisli_Comparison_unique_of_strict (L0 : XT ⟶ A)
  (E1 : @equiv _ (@Functor_StrictEq_Setoid X A)
          (L0 ◯ @Kleisli_Free X (G ◯ F) T) F)
  (E2 : @equiv _ (@Functor_StrictEq_Setoid XT X)
          (G ◯ L0) (@Kleisli_Forget X (G ◯ F) T))
  (coh : ∀ x, `1 E2 x = f_equal (fobj[G]) (`1 E1 x)) :
  @equiv _ (@Functor_StrictEq_Setoid XT A) L0 Kleisli_Comparison.
Proof.
  apply (Kleisli_Comparison_unique_strict L0 (`1 E1)).
  intros x y f.
  pose proof (fst (transport_square (`1 E2 x) (`1 E2 y) _ _) (`2 E2 x y f))
    as Hs.
  rewrite !fmap_comp, !fmap_id_cast.
  rewrite <- eq_sym_map_distr.
  rewrite <- !coh.
  simpl in Hs.
  rewrite Hs.
  rewrite <- comp_assoc, id_cast_inv_r.
  apply id_right.
Qed.

(* Theorem 2 as Mac Lane's map of adjunctions (§IV.7): K := L, L := Id. *)
Program Definition Kleisli_Comparison_Squares :
  @AdjSquares XT X (@Kleisli_Free X (G ◯ F) T) (@Kleisli_Forget X (G ◯ F) T)
              A X F G := {|
  sq_K := Kleisli_Comparison;
  sq_L := Id[X];
  sq_left := fun x => eq_refl;
  sq_right := fun a => eq_refl
|}.
Next Obligation.
  intros; simpl; rewrite id_left, id_right.
  symmetry. apply fmap_from_adj_unit.
Qed.
Next Obligation.
  intros; simpl; rewrite id_left, id_right.
  rewrite (from_adj_counit (H:=Adj) f).
  now rewrite fmap_comp.
Qed.

Lemma Kleisli_Comparison_Squares_unit :
  SquaresUnit (@Kleisli_Adjunction X (G ◯ F) T) Adj Kleisli_Comparison_Squares.
Proof.
  intros x; simpl.
  rewrite id_left, fmap_id, id_left.
  reflexivity.
Qed.

Definition Kleisli_Comparison_Map :
  MapOfAdjunctions (@Kleisli_Adjunction X (G ◯ F) T) Adj :=
  MapOfAdjunctions_of_unit _ _ Kleisli_Comparison_Squares
    Kleisli_Comparison_Squares_unit.

End KleisliComparison.

(* ------------------------------------------------------------------------ *)
(** ** Uniqueness by Mac Lane's route, Proposition IV.7.1 *)

Section UniqueViaMap.

Context {X A : Category}.
Context {F : X ⟶ A} {G : A ⟶ X}.
Context (Adj : F ⊣ G).

Notation T := (@Adjunction_Induced_Monad A X F G Adj).
Notation XT := (@Kleisli X (G ◯ F) T).

Context (L0 : XT ⟶ A) (Hobj : ∀ x, fobj[L0] x = F x).
Context (Hleft : ∀ (x y : X) (f : x ~> y),
   id_cast (Hobj y) ∘ fmap[L0] (fmap[@Kleisli_Free X (G ◯ F) T] f)
     ≈ fmap[F] f ∘ id_cast (Hobj x)).
Context (Hright : ∀ (a b : XT) (f : a ~{XT}~> b),
   id_cast (f_equal (fobj[G]) (eq_sym (Hobj b)))
       ∘ fmap[@Kleisli_Forget X (G ◯ F) T] f
     ≈ fmap[G] (fmap[L0] f) ∘ id_cast (f_equal (fobj[G]) (eq_sym (Hobj a)))).

(* The right square's object equation is the G-image of the left one. *)
Definition Kleisli_Comparison_Squares_of :
  @AdjSquares XT X (@Kleisli_Free X (G ◯ F) T) (@Kleisli_Forget X (G ◯ F) T)
              A X F G :=
  @Build_AdjSquares XT X (@Kleisli_Free X (G ◯ F) T)
    (@Kleisli_Forget X (G ◯ F) T) A X F G L0 Id[X] Hobj Hleft
    (fun a => f_equal (fobj[G]) (eq_sym (Hobj a))) Hright.

Lemma Kleisli_Comparison_Squares_of_unit :
  SquaresUnit (@Kleisli_Adjunction X (G ◯ F) T) Adj
    Kleisli_Comparison_Squares_of.
Proof using All.
  intros x; simpl.
  rewrite fmap_id_cast.
  reflexivity.
Qed.

Theorem Kleisli_Comparison_unique_via_map : L0 ≈ Kleisli_Comparison Adj.
Proof using Adj Hobj Hleft Hright.
  pose proof (snd (squares_hom_iff_unit _ _ Kleisli_Comparison_Squares_of)
                Kleisli_Comparison_Squares_of_unit) as Hh.
  exists (fun x => id_cast_iso (Hobj x)).
  intros x y f; simpl.
  specialize (Hh x y f); simpl in Hh.
  apply (snd (adj_univ (H:=Adj) _ _)) in Hh.
  rewrite <- (fmap_id_cast G (eq_sym (Hobj y))) in Hh.
  rewrite (@from_adj_nat_r _ _ _ _ Adj) in Hh.
  rewrite <- Hh.
  rewrite <- comp_assoc.
  rewrite id_cast_inv_l.
  now rewrite id_right.
Qed.

End UniqueViaMap.

(* ------------------------------------------------------------------------ *)
(** ** Exercise 2, in general: any full subcategory containing every F x,
       with a chosen free preimage for each of its objects *)

Section Restrict2.

#[local] Obligation Tactic := idtac.

Context {X A : Category}.
Context {F : X ⟶ A} {G : A ⟶ X}.
Context (Adj : F ⊣ G).
Context (S : Subcategory A) (full : Full A S).
Context (mem : ∀ x : X, sobj A S (F x)).
Context (pick : ∀ (a : A), sobj A S a → { x : X & F x ≅ a }).

Notation T := (@Adjunction_Induced_Monad A X F G Adj).
Notation XT := (@Kleisli X (G ◯ F) T).

Program Definition Kleisli_Comparison_Restrict : XT ⟶ Sub A S := {|
  fobj := fun x => (F x; mem x);
  fmap := fun x y f =>
    (fmap[Kleisli_Comparison Adj] f;
     full _ _ _ _ (fmap[Kleisli_Comparison Adj] f))
|}.
Next Obligation. intros x y f g Hfg; simpl; now rewrite Hfg. Qed.
Next Obligation. intros x; simpl; apply Kleisli_Comparison_fmap_id. Qed.
Next Obligation.
  intros x y z f g; simpl; apply Kleisli_Comparison_fmap_comp.
Qed.

#[export] Program Instance Kleisli_Comparison_Restrict_Full :
  Category.Theory.Functor.Full Kleisli_Comparison_Restrict := {|
  prefmap := fun x y g => to (@adj _ _ _ _ Adj x (F y)) (`1 g)
|}.
Next Obligation. intros x y g; simpl; apply to_adj_comp_law. Qed.

#[export] Program Instance Kleisli_Comparison_Restrict_Faithful :
  Faithful Kleisli_Comparison_Restrict.
Next Obligation.
  intros x y f g Hfg; simpl in *.
  exact (@fmap_inj _ _ _ (Kleisli_Comparison_Faithful Adj) x y f g Hfg).
Qed.

Definition Kleisli_Comparison_Restrict_ESO :
  EssentiallySurjective Kleisli_Comparison_Restrict.
Proof using Adj full mem pick.
  unshelve eapply Build_EssentiallySurjective.
  - exact (fun b => `1 (pick (`1 b) (`2 b))).
  - intros [a m]; simpl.
    exact (Full_sub_iso A S full (mem (`1 (pick a m))) m (`2 (pick a m))).
Defined.

Definition Kleisli_Comparison_Restrict_Equivalence :
  EquivalenceOfCategories Kleisli_Comparison_Restrict :=
  @FF_ESO_Equivalence _ _ Kleisli_Comparison_Restrict
    Kleisli_Comparison_Restrict_Full Kleisli_Comparison_Restrict_Faithful
    Kleisli_Comparison_Restrict_ESO.

End Restrict2.

(* ------------------------------------------------------------------------ *)
(** ** Exercise 1's image and Exercise 2 at FX *)

Section Image.

Context {X A : Category}.
Context {F : X ⟶ A} {G : A ⟶ X}.
Context (Adj : F ⊣ G).

Notation T := (@Adjunction_Induced_Monad A X F G Adj).
Notation XT := (@Kleisli X (G ◯ F) T).

(* Mac Lane's FX, read as Adjunction/LeftInverse.v's proof-relevant image:
   an object is an a : A with a chosen x and F x = a. *)
Notation FXS := (@LaliImageSub X A F).
Notation FX := (Sub A FXS).

(* Construction 1 at B = FX is LeftInverse.v's [ImageTo], on both actions. *)
Example Restricted_Left_Image_obj (x : X) :
  fobj[Restricted_Left FXS image_full (fun x => (x; eq_refl))] x
    = fobj[@ImageTo X A F] x := eq_refl.

Example Restricted_Left_Image_map (x y : X) (f : x ~> y) :
  fmap[Restricted_Left FXS image_full (fun x => (x; eq_refl))] f
    = fmap[@ImageTo X A F] f := eq_refl.

(* The corestriction L' : X_T ⟶ FX, the general functor at FX. *)
Definition Kleisli_Comparison_Image : XT ⟶ FX :=
  Kleisli_Comparison_Restrict Adj FXS image_full (fun x => (x; eq_refl)).

(* L' is LeftInverse.v's [ImageTo] of L, on both actions. *)
Example Kleisli_Comparison_Image_is_ImageTo_obj (x : X) :
  fobj[Kleisli_Comparison_Image] x
    = fobj[@ImageTo XT A (Kleisli_Comparison Adj)] x := eq_refl.

Example Kleisli_Comparison_Image_is_ImageTo_map (x y : X)
  (f : x ~{XT}~> y) :
  fmap[Kleisli_Comparison_Image] f
    = fmap[@ImageTo XT A (Kleisli_Comparison Adj)] f := eq_refl.

(* L = Incl ◯ L', both actions at eq_refl. *)
Example Kleisli_Comparison_Image_incl_obj (x : X) :
  fobj[Incl A FXS ◯ Kleisli_Comparison_Image] x
    = fobj[Kleisli_Comparison Adj] x := eq_refl.

Example Kleisli_Comparison_Image_incl_map (x y : X) (f : x ~{XT}~> y) :
  fmap[Incl A FXS ◯ Kleisli_Comparison_Image] f
    = fmap[Kleisli_Comparison Adj] f := eq_refl.

Definition Kleisli_Comparison_Image_surjective :
  SurjectiveOnObjects Kleisli_Comparison_Image.
Proof.
  intros [a [x e]].
  exists x.
  destruct e; reflexivity.
Defined.

Example Kleisli_Comparison_Image_surjective_obj (y : FX) :
  `1 (Kleisli_Comparison_Image_surjective y) = `1 (`2 y).
Proof. destruct y as [a [x e]]; reflexivity. Qed.

(* Exercise 2 at FX: the chooser is the projection. *)
Definition Kleisli_Comparison_Image_pick (a : A) (m : sobj A FXS a) :
  { x : X & F x ≅ a } := (`1 m; id_cast_iso (`2 m)).

Definition Kleisli_Comparison_Image_Equivalence :
  EquivalenceOfCategories Kleisli_Comparison_Image :=
  Kleisli_Comparison_Restrict_Equivalence Adj FXS image_full
    (fun x => (x; eq_refl)) Kleisli_Comparison_Image_pick.

Definition Kleisli_Comparison_Image_AdjointEquivalence :
  AdjointEquivalence
    (@ff_surjective_left XT FX Kleisli_Comparison_Image
       (Kleisli_Comparison_Restrict_Full Adj FXS image_full _)
       (Kleisli_Comparison_Restrict_Faithful Adj FXS image_full _)
       Kleisli_Comparison_Image_surjective)
    Kleisli_Comparison_Image :=
  @ff_surjective_adjoint_equivalence XT FX Kleisli_Comparison_Image
    (Kleisli_Comparison_Restrict_Full Adj FXS image_full _)
    (Kleisli_Comparison_Restrict_Faithful Adj FXS image_full _)
    Kleisli_Comparison_Image_surjective.

(* ... and, in this proof-relevant representation, an isomorphism of
   categories: L' is injective on objects. *)
Lemma Kleisli_Comparison_Image_injective :
  InjectiveOnObjects Kleisli_Comparison_Image.
Proof.
  intros x x' H.
  exact (f_equal (fun y : FX => `1 (`2 y)) H).
Qed.

Notation Linv :=
  (@ff_surjective_left XT FX Kleisli_Comparison_Image
     (Kleisli_Comparison_Restrict_Full Adj FXS image_full _)
     (Kleisli_Comparison_Restrict_Faithful Adj FXS image_full _)
     Kleisli_Comparison_Image_surjective).

Lemma Kleisli_Comparison_Image_inv_left :
  @equiv _ (@Functor_StrictEq_Setoid XT XT)
    (Linv ◯ Kleisli_Comparison_Image) Id[XT].
Proof.
  refine (strict_equiv_of_id_cast_nat
            (Linv ◯ Kleisli_Comparison_Image) Id[XT] (fun x => eq_refl) _).
  intros x y f; cbv beta.
  rewrite !id_cast_refl.
  rewrite (@id_left XT), (@id_right XT).
  simpl.
  rewrite id_left, id_right.
  apply (from_adj_comp_law (H:=Adj)).
Qed.

Lemma Kleisli_Comparison_Image_inv_right_obj (y : FX) :
  fobj[Kleisli_Comparison_Image ◯ Linv] y = y.
Proof. destruct y as [a [x e]]; destruct e; reflexivity. Defined.

Lemma Kleisli_Comparison_Image_inv_right :
  @equiv _ (@Functor_StrictEq_Setoid FX FX)
    (Kleisli_Comparison_Image ◯ Linv) Id[FX].
Proof.
  refine (strict_equiv_of_id_cast_nat
            (Kleisli_Comparison_Image ◯ Linv) Id[FX]
            Kleisli_Comparison_Image_inv_right_obj _).
  intros [a [x e]] [b [y e']] [f I']; destruct e, e'; simpl.
  rewrite !id_left, !id_right.
  apply (to_adj_comp_law (H:=Adj)).
Qed.

Definition Kleisli_Comparison_Image_StrictIso :
  @Isomorphism StrictCat XT FX :=
  @Build_Isomorphism StrictCat XT FX Kleisli_Comparison_Image Linv
    Kleisli_Comparison_Image_inv_right Kleisli_Comparison_Image_inv_left.

End Image.

(* ------------------------------------------------------------------------ *)
(** ** Riehl, Lemma 5.2.14: K : C_T ⟶ C^T, full and faithful onto the free
       algebras; and when it is an equivalence *)

Section Riehl.

#[local] Obligation Tactic := idtac.

Context {C : Category}.
Context (T : C ⟶ C).
Context `{H : @Monad C T}.

Program Definition Kleisli_EM : @Kleisli C T H ⟶ EilenbergMoore T := {|
  fobj := fun c => EM_Free T c;
  fmap := fun x y f => @EM_extend C T H x (EM_Free T y) f
|}.
Next Obligation. intros x y f g Hfg; simpl; now rewrite Hfg. Qed.
Next Obligation. intros; simpl; apply join_fmap_ret. Qed.
Next Obligation.
  intros; simpl.
  exact (@fmap_comp _ _ (@Kleisli_Forget C T H) _ _ _ _ _).
Qed.

Example Kleisli_EM_obj (c : C) :
  fobj[Kleisli_EM] c = (T c; {| t_alg := @join C T H c |}) := eq_refl.

Example Kleisli_EM_obj_free (c : C) :
  fobj[Kleisli_EM] c = fobj[EM_Free T] c := eq_refl.

Example Kleisli_EM_map (x y : C) (f : x ~{@Kleisli C T H}~> y) :
  t_alg_hom[fmap[Kleisli_EM] f] = join ∘ fmap[T] f := eq_refl.

Example Kleisli_EM_Forget_map (x y : C) (f : x ~{@Kleisli C T H}~> y) :
  fmap[EM_Forget T ◯ Kleisli_EM] f = fmap[@Kleisli_Forget C T H] f
  := eq_refl.

(* K is the transpose under F^T ⊣ U^T, Riehl's description, at eq_refl. *)
Example Kleisli_EM_is_transpose (x y : C) (f : x ~{@Kleisli C T H}~> y) :
  fmap[Kleisli_EM] f = from (@adj _ _ _ _ (EM_Adjunction T) x (EM_Free T y)) f
  := eq_refl.

#[export] Program Instance Kleisli_EM_Full :
  Category.Theory.Functor.Full Kleisli_EM := {|
  prefmap := fun x y g => t_alg_hom[g] ∘ ret
|}.
Next Obligation.
  intros x y g; simpl; exact (@EM_restrict_extend C T H x (EM_Free T y) g).
Qed.

#[export] Program Instance Kleisli_EM_Faithful : Faithful Kleisli_EM.
Next Obligation.
  intros x y f g Hfg; simpl in *.
  rewrite <- (EM_extend_ret T (`2 (EM_Free T y)) f).
  rewrite <- (EM_extend_ret T (`2 (EM_Free T y)) g).
  now rewrite Hfg.
Qed.

(* The corestriction to the free algebras, LeftInverse.v's [ImageTo]. *)
Notation FreeAlgs := (@LaliImageSub C (EilenbergMoore T) (EM_Free T)).

Definition Kleisli_EM_Image :
  @Kleisli C T H ⟶ Sub (EilenbergMoore T) FreeAlgs :=
  @ImageTo (@Kleisli C T H) (EilenbergMoore T) Kleisli_EM.

#[export] Program Instance Kleisli_EM_Image_Full :
  Category.Theory.Functor.Full Kleisli_EM_Image := {|
  prefmap := fun x y g => t_alg_hom[`1 g] ∘ ret
|}.
Next Obligation.
  intros x y g; simpl.
  exact (@EM_restrict_extend C T H x (EM_Free T y) (`1 g)).
Qed.

#[export] Program Instance Kleisli_EM_Image_Faithful :
  Faithful Kleisli_EM_Image.
Next Obligation.
  intros x y f g Hfg; simpl in *.
  exact (@fmap_inj _ _ _ Kleisli_EM_Faithful x y f g Hfg).
Qed.

Definition Kleisli_EM_Image_surjective :
  SurjectiveOnObjects Kleisli_EM_Image.
Proof. intros [a [c e]]. exists c. destruct e; reflexivity. Defined.

Definition Kleisli_EM_Image_Equivalence :
  EquivalenceOfCategories Kleisli_EM_Image :=
  @ff_surj_eso_equivalence _ _ Kleisli_EM_Image _ _
    Kleisli_EM_Image_surjective.

(* "Free" is "isomorphic in C^T to a free algebra", with the free algebra
   chosen; "equivalent" is "K is an equivalence". *)
Definition EveryAlgebraFree : Type :=
  ∀ a : EilenbergMoore T, { c : C & EM_Free T c ≅ a }.

Theorem Kleisli_EM_equivalence_iff :
  EquivalenceOfCategories Kleisli_EM ↔ EveryAlgebraFree.
Proof.
  split.
  - intros E a.
    exists (@quasi_inverse _ _ _ E a).
    exact (@equivalence_counit_at _ _ _ E a).
  - intros Hfree.
    exact (@FF_ESO_Equivalence _ _ Kleisli_EM Kleisli_EM_Full
             Kleisli_EM_Faithful
             (@Build_EssentiallySurjective _ _ Kleisli_EM
                (fun a => `1 (Hfree a)) (fun a => `2 (Hfree a)))).
Defined.

End Riehl.

(* K and L at the Eilenberg–Moore resolution agree on both actions. *)

Section RiehlIsL.

Context {C : Category} (T : C ⟶ C) `{H : @Monad C T}.

Example Kleisli_EM_is_comparison_obj (c : C) :
  fobj[@Kleisli_EM C T H] c = fobj[Kleisli_Comparison (EM_Adjunction T)] c
  := eq_refl.

Example Kleisli_EM_is_comparison_map (x y : C)
  (f : x ~{@Kleisli C T H}~> y) :
  fmap[@Kleisli_EM C T H] f = fmap[Kleisli_Comparison (EM_Adjunction T)] f
  := eq_refl.

End RiehlIsL.

(* Riehl's K as her proof builds it, her Proposition 5.2.13's functor at
   the Kleisli adjunction: Monad/Comparison.v's [EM_Comparison] at
   [Kleisli_Adjunction].  It forgets to the functor of [Kleisli_EM] on both
   actions, and lands in the algebras of the monad the Kleisli adjunction
   induces, with structure map μ ∘ T id at c. *)

Section RiehlEMComparison.

Context {C : Category} (T : C ⟶ C) `{H : @Monad C T}.

Example EM_Comparison_Kleisli_obj (c : C) :
  fobj[EM_Forget _ ◯ EM_Comparison (@Kleisli_Adjunction C T H)] c
    = fobj[EM_Forget T ◯ @Kleisli_EM C T H] c := eq_refl.

Example EM_Comparison_Kleisli_map (x y : C) (f : x ~{@Kleisli C T H}~> y) :
  fmap[EM_Forget _ ◯ EM_Comparison (@Kleisli_Adjunction C T H)] f
    = fmap[EM_Forget T ◯ @Kleisli_EM C T H] f := eq_refl.

Example EM_Comparison_Kleisli_alg (c : C) :
  t_alg[`2 (fobj[EM_Comparison (@Kleisli_Adjunction C T H)] c)]
    = @join C T H c ∘ fmap[T] (@id C (T c)) := eq_refl.

Lemma EM_Comparison_Kleisli_alg_join (c : C) :
  t_alg[`2 (fobj[EM_Comparison (@Kleisli_Adjunction C T H)] c)]
    ≈ @join C T H c.
Proof. simpl. rewrite fmap_id. apply id_right. Qed.

End RiehlEMComparison.
