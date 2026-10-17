Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Adjunction.Compose.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Adjunction.Map.

Generalizable All Variables.

(** * Adjoint squares (Kelly) and Palmquist's bijection *)

(*
   nLab: https://ncatlab.org/nlab/show/adjoint+functor

   本文件给出伴随相关构造与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ====================================================================== *)
(* (A) The condition, over BARE component families.                       *)
(* ====================================================================== *)

Section AdjointSquareCompare.

Context {C D : Category}.
Context {F : D ⟶ C} {U : C ⟶ D}.
Context (A : F ⊣ U).
Context {C' D' : Category}.
Context {F' : D' ⟶ C'} {U' : C' ⟶ D'}.
Context (A' : F' ⊣ U').
Context (K : C ⟶ C') (L : D ⟶ D').

Notation "⌊ f ⌋"  := (to   (@adj _ _ _ _ A  _ _) f).
Notation "⌈ f ⌉"  := (from (@adj _ _ _ _ A  _ _) f).
Notation "⌊ f ⌋²" := (to   (@adj _ _ _ _ A' _ _) f) (at level 0).
Notation "⌈ f ⌉²" := (from (@adj _ _ _ _ A' _ _) f) (at level 0).
Notation "'η' x"  := (@unit   _ _ _ _ A  x) (at level 9).
Notation "'ε' a"  := (@counit _ _ _ _ A  a) (at level 9).
Notation "'η²' x" := (@unit   _ _ _ _ A' x) (at level 9).
Notation "'ε²' a" := (@counit _ _ _ _ A' a) (at level 9).

(* The two comparison families of Mac Lane's array. *)

Definition SqSigma : Type := ∀ x : D, F' (L x) ~> K (F x).
Definition SqTau   : Type := ∀ a : C, L (U a) ~> U' (K a).

(* Naturality, stated on the bare families.  Neither predicate mentions an
   adjunction, exactly as Map.v's [CompareLeftNat]/[CompareRightNat] do not. *)

Definition SigmaNat (sigma : SqSigma) : Type :=
  ∀ (x y : D) (f : x ~> y),
    sigma y ∘ fmap[F'] (fmap[L] f) ≈ fmap[K] (fmap[F] f) ∘ sigma x.

Definition TauNat (tau : SqTau) : Type :=
  ∀ (a b : C) (f : a ~> b),
    tau b ∘ fmap[L] (fmap[U] f) ≈ fmap[U'] (fmap[K] f) ∘ tau a.

(* Mac Lane's commuting square of hom-sets, quantified over every
   transposable arrow rather than evaluated at one distinguished argument. *)

Definition AdjointSquare (sigma : SqSigma) (tau : SqTau) : Type :=
  ∀ (x : D) (a : C) (k : F x ~> a),
    ⌊ fmap[K] k ∘ sigma x ⌋² ≈ tau a ∘ fmap[L] ⌊ k ⌋.

(* The same square read through the inverse transposes. *)

Definition AdjointSquareFrom (sigma : SqSigma) (tau : SqTau) : Type :=
  ∀ (x : D) (a : C) (g : x ~> U a),
    ⌈ tau a ∘ fmap[L] g ⌉² ≈ fmap[K] ⌈ g ⌉ ∘ sigma x.

(* Mac Lane's Lη = η'L and Kε = ε'K, with the comparison families split
   across the two sides in Map.v's orientation. *)

Definition AdjointSquareUnit (sigma : SqSigma) (tau : SqTau) : Type :=
  ∀ x : D, tau (F x) ∘ fmap[L] (η x) ≈ fmap[U'] (sigma x) ∘ η² (L x).

Definition AdjointSquareCounit (sigma : SqSigma) (tau : SqTau) : Type :=
  ∀ a : C, fmap[K] (ε a) ∘ sigma (U a) ≈ ε² (K a) ∘ fmap[F'] (tau a).

(* ---- the two mate operators, defined BY THE TRANSPOSE ---- *)

Definition sq_mate (sigma : SqSigma) : SqTau :=
  λ a, ⌊ fmap[K] (ε a) ∘ sigma (U a) ⌋².

Definition sq_mate_inv (tau : SqTau) : SqSigma :=
  λ x, ⌈ tau (F x) ∘ fmap[L] (η x) ⌉².

(* The whiskered pasting spellings, up to ≈. *)

Lemma sq_mate_pasting (sigma : SqSigma) (a : C) :
  sq_mate sigma a
    ≈ fmap[U'] (fmap[K] (ε a) ∘ sigma (U a)) ∘ η² (L (U a)).
Proof. unfold sq_mate; now rewrite (to_adj_unit (H:=A')). Qed.

Lemma sq_mate_inv_pasting (tau : SqTau) (x : D) :
  sq_mate_inv tau x
    ≈ ε² (K (F x)) ∘ fmap[F'] (tau (F x) ∘ fmap[L] (η x)).
Proof. unfold sq_mate_inv; now rewrite (from_adj_counit (H:=A')). Qed.

(* ---- the ledger; every hypothesis is an explicit argument ---- *)

Lemma sq_hom_to_unit (sigma : SqSigma) (tau : SqTau) :
  AdjointSquare sigma tau → AdjointSquareUnit sigma tau.
Proof.
  intros H x.
  pose proof (H x (F x) id) as Hx.
  rewrite fmap_id, id_left in Hx.
  rewrite (to_adj_unit (H:=A')) in Hx.
  now rewrite <- Hx.
Qed.

Lemma sq_unit_to_hom (sigma : SqSigma) (tau : SqTau) :
  TauNat tau → AdjointSquareUnit sigma tau → AdjointSquare sigma tau.
Proof.
  intros Ht H x a k.
  rewrite (to_adj_unit (H:=A')).
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  rewrite <- (H x : _ ≈ _).
  rewrite comp_assoc.
  rewrite <- (Ht (F x) a k).
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  now rewrite <- (to_adj_unit (H:=A)).
Qed.

Lemma sq_hom_to_counit (sigma : SqSigma) (tau : SqTau) :
  AdjointSquare sigma tau → AdjointSquareCounit sigma tau.
Proof.
  intros H a.
  pose proof (H (U a) a (ε a)) as Ha.
  rewrite (to_adj_counit (H:=A)) in Ha.
  rewrite fmap_id, id_right in Ha.
  apply (snd (adj_univ (H:=A') _ _)) in Ha.
  rewrite Ha.
  now rewrite (from_adj_counit (H:=A')).
Qed.

Lemma sq_counit_to_hom (sigma : SqSigma) (tau : SqTau) :
  SigmaNat sigma → AdjointSquareCounit sigma tau → AdjointSquare sigma tau.
Proof.
  intros Hs H x a k.
  apply (fst (adj_univ (H:=A') _ _)).
  rewrite (from_adj_counit (H:=A')).
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite <- (H a : _ ≈ _).
  rewrite <- comp_assoc.
  rewrite (Hs _ _ ⌊ k ⌋).
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite <- (from_adj_counit (H:=A)).
  now rewrite (to_adj_comp_law (H:=A)).
Qed.

Theorem sq_hom_iff_unit (sigma : SqSigma) (tau : SqTau) :
  TauNat tau → (AdjointSquare sigma tau ↔ AdjointSquareUnit sigma tau).
Proof.
  intros Ht; split; [ exact (sq_hom_to_unit sigma tau)
                    | exact (sq_unit_to_hom sigma tau Ht) ].
Qed.

Theorem sq_hom_iff_counit (sigma : SqSigma) (tau : SqTau) :
  SigmaNat sigma → (AdjointSquare sigma tau ↔ AdjointSquareCounit sigma tau).
Proof.
  intros Hs; split; [ exact (sq_hom_to_counit sigma tau)
                    | exact (sq_counit_to_hom sigma tau Hs) ].
Qed.

Theorem sq_unit_iff_counit (sigma : SqSigma) (tau : SqTau) :
  SigmaNat sigma → TauNat tau →
  (AdjointSquareUnit sigma tau ↔ AdjointSquareCounit sigma tau).
Proof.
  intros Hs Ht; split; intro H.
  - exact (sq_hom_to_counit sigma tau (sq_unit_to_hom sigma tau Ht H)).
  - exact (sq_hom_to_unit sigma tau (sq_counit_to_hom sigma tau Hs H)).
Qed.

Theorem sq_hom_iff_from (sigma : SqSigma) (tau : SqTau) :
  AdjointSquare sigma tau ↔ AdjointSquareFrom sigma tau.
Proof.
  split.
  - intros H x a g.
    pose proof (H x a ⌈ g ⌉) as Hg.
    rewrite (from_adj_comp_law (H:=A)) in Hg.
    rewrite <- Hg.
    now rewrite (to_adj_comp_law (H:=A')).
  - intros H x a k.
    pose proof (H x a ⌊ k ⌋) as Hk.
    rewrite (to_adj_comp_law (H:=A)) in Hk.
    rewrite <- Hk.
    now rewrite (from_adj_comp_law (H:=A')).
Qed.

(* ---- each of sigma, tau determines the other ---- *)

Theorem sq_hom_to_mate (sigma : SqSigma) (tau : SqTau) :
  AdjointSquare sigma tau → ∀ a, tau a ≈ sq_mate sigma a.
Proof.
  intros H a.
  unfold sq_mate.
  rewrite (H (U a) a (ε a)).
  rewrite (to_adj_counit (H:=A)).
  now rewrite fmap_id, id_right.
Qed.

Theorem sq_mate_to_hom (sigma : SqSigma) (tau : SqTau) :
  SigmaNat sigma → (∀ a, tau a ≈ sq_mate sigma a) → AdjointSquare sigma tau.
Proof.
  intros Hs H.
  apply (sq_counit_to_hom sigma tau Hs).
  intros a.
  rewrite (H a).
  unfold sq_mate.
  rewrite <- (from_adj_counit (H:=A')).
  now rewrite (to_adj_comp_law (H:=A')).
Qed.

Theorem adjoint_square_iff_mate (sigma : SqSigma) (tau : SqTau) :
  SigmaNat sigma →
  (AdjointSquare sigma tau ↔ (∀ a, tau a ≈ sq_mate sigma a)).
Proof.
  intros Hs; split; [ exact (sq_hom_to_mate sigma tau)
                    | exact (sq_mate_to_hom sigma tau Hs) ].
Qed.

Theorem sq_hom_to_mate_inv (sigma : SqSigma) (tau : SqTau) :
  AdjointSquare sigma tau → ∀ x, sigma x ≈ sq_mate_inv tau x.
Proof.
  intros H x.
  unfold sq_mate_inv.
  rewrite (sq_hom_to_unit sigma tau H x).
  rewrite <- (to_adj_unit (H:=A')).
  now rewrite (to_adj_comp_law (H:=A')).
Qed.

Theorem sq_mate_inv_to_hom (sigma : SqSigma) (tau : SqTau) :
  TauNat tau → (∀ x, sigma x ≈ sq_mate_inv tau x) → AdjointSquare sigma tau.
Proof.
  intros Ht H.
  apply (sq_unit_to_hom sigma tau Ht).
  intros x.
  rewrite (H x).
  unfold sq_mate_inv.
  rewrite <- (to_adj_unit (H:=A')).
  now rewrite (from_adj_comp_law (H:=A')).
Qed.

Theorem adjoint_square_iff_mate_inv (sigma : SqSigma) (tau : SqTau) :
  TauNat tau →
  (AdjointSquare sigma tau ↔ (∀ x, sigma x ≈ sq_mate_inv tau x)).
Proof.
  intros Ht; split; [ exact (sq_hom_to_mate_inv sigma tau)
                    | exact (sq_mate_inv_to_hom sigma tau Ht) ].
Qed.

(* ---- naturality of the two mates ---- *)

Lemma sq_mate_nat (sigma : SqSigma) : SigmaNat sigma → TauNat (sq_mate sigma).
Proof.
  intros Hs a b f.
  unfold sq_mate.
  rewrite <- (to_adj_nat_r (Adjunction:=A')).
  rewrite <- (to_adj_nat_l (Adjunction:=A')).
  apply (to_adj_respects (H:=A')).
  rewrite <- !comp_assoc.
  rewrite (Hs _ _ (fmap[U] f)).
  rewrite !comp_assoc.
  rewrite <- !fmap_comp.
  apply compose_respects; [| reflexivity ].
  apply fmap_respects.
  now rewrite (conj_counit_nat A f).
Qed.

Lemma sq_mate_inv_nat (tau : SqTau) : TauNat tau → SigmaNat (sq_mate_inv tau).
Proof.
  intros Ht x y f.
  unfold sq_mate_inv.
  rewrite <- (from_adj_nat_r (Adjunction:=A')).
  rewrite <- (from_adj_nat_l (Adjunction:=A')).
  apply (from_adj_respects (H:=A')).
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite <- (conj_unit_nat A f).
  rewrite fmap_comp.
  rewrite !comp_assoc.
  now rewrite (Ht _ _ (fmap[F] f)).
Qed.

(* ---- existence, and the two round trips ---- *)

Theorem adjoint_square_sq_mate (sigma : SqSigma) :
  SigmaNat sigma → AdjointSquare sigma (sq_mate sigma).
Proof.
  intros Hs; apply (sq_mate_to_hom sigma (sq_mate sigma) Hs).
  intro a; reflexivity.
Qed.

Theorem adjoint_square_sq_mate_inv (tau : SqTau) :
  TauNat tau → AdjointSquare (sq_mate_inv tau) tau.
Proof.
  intros Ht; apply (sq_mate_inv_to_hom (sq_mate_inv tau) tau Ht).
  intro x; reflexivity.
Qed.

Corollary sq_mate_inv_mate (sigma : SqSigma) :
  SigmaNat sigma → ∀ x, sq_mate_inv (sq_mate sigma) x ≈ sigma x.
Proof.
  intros Hs x; symmetry.
  exact (sq_hom_to_mate_inv sigma (sq_mate sigma)
           (adjoint_square_sq_mate sigma Hs) x).
Qed.

Corollary sq_mate_mate_inv (tau : SqTau) :
  TauNat tau → ∀ a, sq_mate (sq_mate_inv tau) a ≈ tau a.
Proof.
  intros Ht a; symmetry.
  exact (sq_hom_to_mate (sq_mate_inv tau) tau
           (adjoint_square_sq_mate_inv tau Ht) a).
Qed.

End AdjointSquareCompare.

(* ====================================================================== *)
(* (B) The condition SUBSUMES its two in-tree special cases, at Leibniz   *)
(*     equality of TYPES.                                                 *)
(* ====================================================================== *)

Section SquareIdCase.

Context {C D : Category}.
Context {F : D ⟶ C} {U : C ⟶ D}.
Context {F' : D ⟶ C} {U' : C ⟶ D}.
Context (A : F ⊣ U) (A' : F' ⊣ U').

Example square_is_conjugate (s : F' ⟹ F) (t : U ⟹ U') :
  AdjointSquare A A' Id[C] Id[D] (transform[s]) (transform[t])
    = Conjugate A A' s t := eq_refl.

Example square_unit_is_conjugate_unit (s : F' ⟹ F) (t : U ⟹ U') :
  AdjointSquareUnit A A' Id[C] Id[D] (transform[s]) (transform[t])
    = ConjugateUnit A A' s t := eq_refl.

Example square_counit_is_conjugate_counit (s : F' ⟹ F) (t : U ⟹ U') :
  AdjointSquareCounit A A' Id[C] Id[D] (transform[s]) (transform[t])
    = ConjugateCounit A A' s t := eq_refl.

Example sq_mate_is_conj_mate (s : F' ⟹ F) (a : C) :
  sq_mate A A' Id[C] Id[D] (transform[s]) a = conj_mate A A' s a := eq_refl.

Example sq_mate_inv_is_conj_mate_inv (t : U ⟹ U') (x : D) :
  sq_mate_inv A A' Id[C] Id[D] (transform[t]) x
    = conj_mate_inv A A' t x := eq_refl.

End SquareIdCase.

Section SquareMapCase.

Context {C D : Category}.
Context {F : D ⟶ C} {U : C ⟶ D}.
Context (A : F ⊣ U).
Context {C' D' : Category}.
Context {F' : D' ⟶ C'} {U' : C' ⟶ D'}.
Context (A' : F' ⊣ U').
Context (K : C ⟶ C') (L : D ⟶ D').
Context (al : ∀ x : D, K (F x) ≅ F' (L x)).
Context (be : ∀ a : C, L (U a) ≅ U' (K a)).

Example square_is_map_adj_hom :
  AdjointSquare A A' K L (fun x => from (al x)) (fun a => to (be a))
    = MapAdjHom A A' K L al be := eq_refl.

Example square_unit_is_map_adj_unit :
  AdjointSquareUnit A A' K L (fun x => from (al x)) (fun a => to (be a))
    = MapAdjUnit A A' K L al be := eq_refl.

Example square_counit_is_map_adj_counit :
  AdjointSquareCounit A A' K L (fun x => from (al x)) (fun a => to (be a))
    = MapAdjCounit A A' K L al be := eq_refl.

Example tau_nat_is_compare_right :
  TauNat K L (fun a => to (be a)) = CompareRightNat K L be := eq_refl.

Example sigma_nat_is_compare_left_from :
  SigmaNat K L (fun x => from (al x))
    = (∀ (x y : D) (f : x ~> y),
         from (al y) ∘ fmap[F'] (fmap[L] f)
           ≈ fmap[K] (fmap[F] f) ∘ from (al x)) := eq_refl.

End SquareMapCase.

(* ====================================================================== *)
(* (C) Transform-typed wrappers and the bijection in Sets.                *)
(* ====================================================================== *)

Section SquareBijection.

Context {C D : Category}.
Context {F : D ⟶ C} {U : C ⟶ D}.
Context (A : F ⊣ U).
Context {C' D' : Category}.
Context {F' : D' ⟶ C'} {U' : C' ⟶ D'}.
Context (A' : F' ⊣ U').
Context (K : C ⟶ C') (L : D ⟶ D').

Definition AdjointSquareT
  (sg : F' ◯ L ⟹ K ◯ F) (ta : L ◯ U ⟹ U' ◯ K) : Type :=
  AdjointSquare A A' K L (fun x => sg x) (fun a => ta a).

Example adjoint_square_T_is_bare
  (sg : F' ◯ L ⟹ K ◯ F) (ta : L ◯ U ⟹ U' ◯ K) :
  AdjointSquareT sg ta
    = AdjointSquare A A' K L (fun x => sg x) (fun a => ta a) := eq_refl.

(* A component family of a Transform meets the bare engine with no
   transport, and [naturality_sym] IS the naturality predicate. *)

Lemma transform_SigmaNat (s : F' ◯ L ⟹ K ◯ F) : SigmaNat K L (transform[s]).
Proof. intros x y f; exact (naturality_sym s x y f). Qed.

Lemma transform_TauNat (t : L ◯ U ⟹ U' ◯ K) : TauNat K L (transform[t]).
Proof. intros a b f; exact (naturality_sym t a b f). Qed.

Program Definition SqMate (sg : F' ◯ L ⟹ K ◯ F) : L ◯ U ⟹ U' ◯ K := {|
  transform := sq_mate A A' K L (transform[sg])
|}.
Next Obligation.
  symmetry; exact (sq_mate_nat A A' K L _ (transform_SigmaNat sg) _ _ f).
Qed.
Next Obligation.
  exact (sq_mate_nat A A' K L _ (transform_SigmaNat sg) _ _ f).
Qed.

Program Definition SqMateInv (ta : L ◯ U ⟹ U' ◯ K) : F' ◯ L ⟹ K ◯ F := {|
  transform := sq_mate_inv A A' K L (transform[ta])
|}.
Next Obligation.
  symmetry; exact (sq_mate_inv_nat A A' K L _ (transform_TauNat ta) _ _ f).
Qed.
Next Obligation.
  exact (sq_mate_inv_nat A A' K L _ (transform_TauNat ta) _ _ f).
Qed.

Example SqMate_component (sg : F' ◯ L ⟹ K ◯ F) (a : C) :
  SqMate sg a = sq_mate A A' K L (transform[sg]) a := eq_refl.

Example SqMateInv_component (ta : L ◯ U ⟹ U' ◯ K) (x : D) :
  SqMateInv ta x = sq_mate_inv A A' K L (transform[ta]) x := eq_refl.

Theorem AdjointSquareT_SqMate (sg : F' ◯ L ⟹ K ◯ F) :
  AdjointSquareT sg (SqMate sg).
Proof. exact (adjoint_square_sq_mate A A' K L _ (transform_SigmaNat sg)). Qed.

Theorem SqMate_uniq (sg : F' ◯ L ⟹ K ◯ F) (ta : L ◯ U ⟹ U' ◯ K) :
  AdjointSquareT sg ta → ta ≈ SqMate sg.
Proof. intros H a; exact (sq_hom_to_mate A A' K L _ _ H a). Qed.

Theorem AdjointSquareT_SqMateInv (ta : L ◯ U ⟹ U' ◯ K) :
  AdjointSquareT (SqMateInv ta) ta.
Proof.
  exact (adjoint_square_sq_mate_inv A A' K L _ (transform_TauNat ta)).
Qed.

Theorem SqMateInv_uniq (sg : F' ◯ L ⟹ K ◯ F) (ta : L ◯ U ⟹ U' ◯ K) :
  AdjointSquareT sg ta → sg ≈ SqMateInv ta.
Proof. intros H x; exact (sq_hom_to_mate_inv A A' K L _ _ H x). Qed.

Definition sq_dom : SetoidObject := {| carrier := F' ◯ L ⟹ K ◯ F |}.
Definition sq_cod : SetoidObject := {| carrier := L ◯ U ⟹ U' ◯ K |}.

Example sq_dom_setoid :
  is_setoid sq_dom = @Transform_Setoid D C' (F' ◯ L) (K ◯ F) := eq_refl.
Example sq_cod_setoid :
  is_setoid sq_cod = @Transform_Setoid C D' (L ◯ U) (U' ◯ K) := eq_refl.

#[local] Obligation Tactic := idtac.

Program Definition square_bijection : @Isomorphism Sets sq_dom sq_cod := {|
  to   := {| morphism := SqMate |};
  from := {| morphism := SqMateInv |}
|}.
Next Obligation.
  intros s s' Hs a; simpl; unfold sq_mate.
  now rewrite (Hs (U a)).
Qed.
Next Obligation.
  intros t t' Ht x; simpl; unfold sq_mate_inv.
  now rewrite (Ht (F x)).
Qed.
Next Obligation.
  intros t a; simpl.
  exact (sq_mate_mate_inv A A' K L (transform[t]) (transform_TauNat t) a).
Qed.
Next Obligation.
  intros s x; simpl.
  exact (sq_mate_inv_mate A A' K L (transform[s]) (transform_SigmaNat s) x).
Qed.

Definition square_nat_bijection :
  (F' ◯ L ⟹ K ◯ F) ≊ (L ◯ U ⟹ U' ◯ K) := square_bijection.

End SquareBijection.

(* ====================================================================== *)
(* (D) Palmquist's bijection, and its two factorisations.                 *)
(* ====================================================================== *)

Section PrecompFactor.

Context {C D : Category}.
Context {F : D ⟶ C} {U : C ⟶ D}.
Context (A : F ⊣ U).
Context {X : Category}.

Notation "'η' x"  := (@unit   _ _ _ _ A  x) (at level 9).
Notation "'ε' a"  := (@counit _ _ _ _ A  a) (at level 9).

#[local] Obligation Tactic := idtac.

Program Definition pre_to {Y : D ⟶ X} {Z : C ⟶ X} (th : Y ◯ U ⟹ Z)
  : Y ⟹ Z ◯ F := {| transform := fun x => th (F x) ∘ fmap[Y] (η x) |}.
Next Obligation.
  intros Y Z th x y g; simpl.
  rewrite comp_assoc.
  rewrite (naturality th _ _ (fmap[F] g)); simpl.
  rewrite <- !comp_assoc, <- !fmap_comp.
  apply compose_respects; [ reflexivity | ].
  apply fmap_respects; now rewrite (conj_unit_nat A g).
Qed.
Next Obligation. symmetry; now apply pre_to_obligation_1. Qed.

Program Definition pre_from {Y : D ⟶ X} {Z : C ⟶ X} (ps : Y ⟹ Z ◯ F)
  : Y ◯ U ⟹ Z := {| transform := fun a => fmap[Z] (ε a) ∘ ps (U a) |}.
Next Obligation.
  intros Y Z ps a b f; simpl.
  rewrite comp_assoc, <- fmap_comp.
  rewrite (conj_counit_nat A f), fmap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  now rewrite (naturality ps _ _ (fmap[U] f)).
Qed.
Next Obligation. symmetry; now apply pre_from_obligation_1. Qed.

Theorem pre_from_to {Y : D ⟶ X} {Z : C ⟶ X} (th : Y ◯ U ⟹ Z) :
  pre_from (pre_to th) ≈ th.
Proof.
  intros a; simpl.
  rewrite comp_assoc.
  rewrite (naturality th _ _ (ε a)); simpl.
  rewrite <- comp_assoc, <- fmap_comp.
  rewrite (fmap_counit_unit (H:=A)).
  now rewrite fmap_id, id_right.
Qed.

Theorem pre_to_from {Y : D ⟶ X} {Z : C ⟶ X} (ps : Y ⟹ Z ◯ F) :
  pre_to (pre_from ps) ≈ ps.
Proof.
  intros x; simpl.
  rewrite <- comp_assoc.
  rewrite <- (naturality ps _ _ (η x)); simpl.
  rewrite comp_assoc, <- fmap_comp.
  rewrite (counit_fmap_unit (H:=A)).
  now rewrite fmap_id, id_left.
Qed.

Lemma pre_to_respects {Y : D ⟶ X} {Z : C ⟶ X} (t t' : Y ◯ U ⟹ Z) :
  t ≈ t' → pre_to t ≈ pre_to t'.
Proof. intros H x; simpl; now rewrite (H (F x)). Qed.

Lemma pre_from_respects {Y : D ⟶ X} {Z : C ⟶ X} (t t' : Y ⟹ Z ◯ F) :
  t ≈ t' → pre_from t ≈ pre_from t'.
Proof. intros H a; simpl; now rewrite (H (U a)). Qed.

Definition precomp_dom (Y : D ⟶ X) (Z : C ⟶ X) : SetoidObject :=
  {| carrier := Y ◯ U ⟹ Z |}.
Definition precomp_cod (Y : D ⟶ X) (Z : C ⟶ X) : SetoidObject :=
  {| carrier := Y ⟹ Z ◯ F |}.

Program Definition precomp_bijection (Y : D ⟶ X) (Z : C ⟶ X) :
  @Isomorphism Sets (precomp_dom Y Z) (precomp_cod Y Z) := {|
  to   := {| morphism := @pre_to Y Z |};
  from := {| morphism := @pre_from Y Z |}
|}.
Next Obligation. repeat intro; now apply pre_to_respects. Qed.
Next Obligation. repeat intro; now apply pre_from_respects. Qed.
Next Obligation. repeat intro; simpl; now apply pre_to_from. Qed.
Next Obligation. repeat intro; simpl; now apply pre_from_to. Qed.

End PrecompFactor.

Section PostcompFactor.

Context {C' D' : Category}.
Context {F' : D' ⟶ C'} {U' : C' ⟶ D'}.
Context (A' : F' ⊣ U').
Context {X : Category}.

Notation "⌊ f ⌋²" := (to   (@adj _ _ _ _ A' _ _) f) (at level 0).
Notation "⌈ f ⌉²" := (from (@adj _ _ _ _ A' _ _) f) (at level 0).

#[local] Obligation Tactic := idtac.

Program Definition post_to {Y : X ⟶ D'} {Z : X ⟶ C'} (th : F' ◯ Y ⟹ Z)
  : Y ⟹ U' ◯ Z := {| transform := fun x => ⌊ th x ⌋² |}.
Next Obligation.
  intros Y Z th x y g; simpl.
  rewrite <- (to_adj_nat_r (Adjunction:=A')).
  rewrite (naturality th _ _ g); simpl.
  now rewrite (to_adj_nat_l (Adjunction:=A')).
Qed.
Next Obligation. symmetry; now apply post_to_obligation_1. Qed.

Program Definition post_from {Y : X ⟶ D'} {Z : X ⟶ C'} (ps : Y ⟹ U' ◯ Z)
  : F' ◯ Y ⟹ Z := {| transform := fun x => ⌈ ps x ⌉² |}.
Next Obligation.
  intros Y Z ps x y g; simpl.
  rewrite <- (from_adj_nat_r (Adjunction:=A')).
  rewrite (naturality ps _ _ g); simpl.
  now rewrite (from_adj_nat_l (Adjunction:=A')).
Qed.
Next Obligation. symmetry; now apply post_from_obligation_1. Qed.

Theorem post_from_to {Y : X ⟶ D'} {Z : X ⟶ C'} (th : F' ◯ Y ⟹ Z) :
  post_from (post_to th) ≈ th.
Proof. intros x; simpl; apply (to_adj_comp_law (H:=A')). Qed.

Theorem post_to_from {Y : X ⟶ D'} {Z : X ⟶ C'} (ps : Y ⟹ U' ◯ Z) :
  post_to (post_from ps) ≈ ps.
Proof. intros x; simpl; apply (from_adj_comp_law (H:=A')). Qed.

Lemma post_to_respects {Y : X ⟶ D'} {Z : X ⟶ C'} (t t' : F' ◯ Y ⟹ Z) :
  t ≈ t' → post_to t ≈ post_to t'.
Proof. intros H x; simpl; now rewrite (H x). Qed.

Lemma post_from_respects {Y : X ⟶ D'} {Z : X ⟶ C'} (t t' : Y ⟹ U' ◯ Z) :
  t ≈ t' → post_from t ≈ post_from t'.
Proof. intros H x; simpl; now rewrite (H x). Qed.

Definition postcomp_dom (Y : X ⟶ D') (Z : X ⟶ C') : SetoidObject :=
  {| carrier := F' ◯ Y ⟹ Z |}.
Definition postcomp_cod (Y : X ⟶ D') (Z : X ⟶ C') : SetoidObject :=
  {| carrier := Y ⟹ U' ◯ Z |}.

Program Definition postcomp_bijection (Y : X ⟶ D') (Z : X ⟶ C') :
  @Isomorphism Sets (postcomp_dom Y Z) (postcomp_cod Y Z) := {|
  to   := {| morphism := @post_to Y Z |};
  from := {| morphism := @post_from Y Z |}
|}.
Next Obligation. repeat intro; now apply post_to_respects. Qed.
Next Obligation. repeat intro; now apply post_from_respects. Qed.
Next Obligation. repeat intro; simpl; now apply post_to_from. Qed.
Next Obligation. repeat intro; simpl; now apply post_from_to. Qed.

End PostcompFactor.

Section Palmquist.

Context {C D : Category}.
Context {F : D ⟶ C} {U : C ⟶ D}.
Context (A : F ⊣ U).
Context {C' D' : Category}.
Context {F' : D' ⟶ C'} {U' : C' ⟶ D'}.
Context (A' : F' ⊣ U').
Context (K : C ⟶ C') (L : D ⟶ D').

Notation "⌊ f ⌋²" := (to   (@adj _ _ _ _ A' _ _) f) (at level 0).
Notation "⌈ f ⌉²" := (from (@adj _ _ _ _ A' _ _) f) (at level 0).
Notation "'η' x"  := (@unit   _ _ _ _ A  x) (at level 9).
Notation "'ε' a"  := (@counit _ _ _ _ A  a) (at level 9).

(* [◯] is left associative, so [F' ◯ L ◯ U] is [(F' ◯ L) ◯ U].  The two
   bracketings agree on objects and arrows but not as functor records. *)

Example bracket_fobj_left (a : C) :
  fobj[F' ◯ L ◯ U] a = fobj[F' ◯ (L ◯ U)] a := eq_refl.

Example bracket_fmap_left (a b : C) (f : a ~> b) :
  fmap[F' ◯ L ◯ U] f = fmap[F' ◯ (L ◯ U)] f := eq_refl.

Example comp_type_left (a : C) :
  (fobj[F' ◯ L ◯ U] a ~> fobj[K] a) = (F' (L (U a)) ~> K a) := eq_refl.

Example comp_type_right (x : D) :
  (fobj[L] x ~> fobj[U' ◯ K ◯ F] x) = (L x ~> U' (K (F x))) := eq_refl.

Example bracket_transform_type_right :
  (L ⟹ U' ◯ K ◯ F) = (L ⟹ (U' ◯ K) ◯ F) := eq_refl.

#[local] Obligation Tactic := idtac.

Program Definition palm_to (al : F' ◯ L ◯ U ⟹ K) : L ⟹ U' ◯ K ◯ F := {|
  transform := fun x => ⌊ al (F x) ⌋² ∘ fmap[L] (η x)
|}.
Next Obligation.
  intros al x y f; simpl.
  rewrite comp_assoc.
  rewrite <- (to_adj_nat_r (Adjunction:=A')).
  rewrite (naturality al _ _ (fmap[F] f)); simpl.
  rewrite (to_adj_nat_l (Adjunction:=A')).
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  rewrite <- !fmap_comp.
  apply fmap_respects.
  now rewrite (conj_unit_nat A f).
Qed.
Next Obligation. symmetry; now apply palm_to_obligation_1. Qed.

Program Definition palm_from (be : L ⟹ U' ◯ K ◯ F) : F' ◯ L ◯ U ⟹ K := {|
  transform := fun a => fmap[K] (ε a) ∘ ⌈ be (U a) ⌉²
|}.
Next Obligation.
  intros be a b f; simpl.
  rewrite comp_assoc, <- fmap_comp.
  rewrite (conj_counit_nat A f), fmap_comp, <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  rewrite <- (from_adj_nat_r (Adjunction:=A')).
  rewrite (naturality be _ _ (fmap[U] f)); simpl.
  now rewrite (from_adj_nat_l (Adjunction:=A')).
Qed.
Next Obligation. symmetry; now apply palm_from_obligation_1. Qed.

Theorem palm_from_to (al : F' ◯ L ◯ U ⟹ K) : palm_from (palm_to al) ≈ al.
Proof.
  intros a; simpl.
  rewrite (from_adj_nat_l (Adjunction:=A')).
  rewrite (to_adj_comp_law (H:=A')).
  rewrite comp_assoc.
  rewrite (naturality al _ _ (ε a)); simpl.
  rewrite <- !comp_assoc, <- !fmap_comp.
  rewrite (fmap_counit_unit (H:=A)).
  now rewrite !fmap_id, id_right.
Qed.

Theorem palm_to_from (be : L ⟹ U' ◯ K ◯ F) : palm_to (palm_from be) ≈ be.
Proof.
  intros x; simpl.
  rewrite (to_adj_nat_r (Adjunction:=A')).
  rewrite (from_adj_comp_law (H:=A')).
  rewrite <- comp_assoc.
  rewrite <- (naturality be _ _ (η x)); simpl.
  rewrite comp_assoc, <- !fmap_comp.
  rewrite (counit_fmap_unit (H:=A)).
  now rewrite !fmap_id, id_left.
Qed.

Lemma palm_to_respects (al al' : F' ◯ L ◯ U ⟹ K) :
  al ≈ al' → palm_to al ≈ palm_to al'.
Proof. intros H x; simpl; now rewrite (H (F x)). Qed.

Lemma palm_from_respects (be be' : L ⟹ U' ◯ K ◯ F) :
  be ≈ be' → palm_from be ≈ palm_from be'.
Proof. intros H a; simpl; now rewrite (H (U a)). Qed.

Definition palm_dom : SetoidObject := {| carrier := F' ◯ L ◯ U ⟹ K |}.
Definition palm_cod : SetoidObject := {| carrier := L ⟹ U' ◯ K ◯ F |}.

Example palm_dom_setoid :
  is_setoid palm_dom = @Transform_Setoid C C' (F' ◯ L ◯ U) K := eq_refl.
Example palm_cod_setoid :
  is_setoid palm_cod = @Transform_Setoid D D' L (U' ◯ K ◯ F) := eq_refl.

Program Definition palmquist_bijection :
  @Isomorphism Sets palm_dom palm_cod := {|
  to   := {| morphism := palm_to |};
  from := {| morphism := palm_from |}
|}.
Next Obligation. exact palm_to_respects. Qed.
Next Obligation. exact palm_from_respects. Qed.
Next Obligation. exact palm_to_from. Qed.
Next Obligation. exact palm_from_to. Qed.

Definition palmquist_nat_bijection :
  (F' ◯ L ◯ U ⟹ K) ≊ (L ⟹ U' ◯ K ◯ F) := palmquist_bijection.

(* ---- the mate absorbs one pre/post pair ON THE NOSE ---- *)

Example sq_mate_is_post_of_pre (sg : F' ◯ L ⟹ K ◯ F) (a : C) :
  sq_mate A A' K L (transform[sg]) a
    = ⌊ pre_from A (Y:=F' ◯ L) (Z:=K) sg a ⌋² := eq_refl.

Example sq_mate_inv_is_pre_of_post (ta : L ◯ U ⟹ U' ◯ K) (x : D) :
  sq_mate_inv A A' K L (transform[ta]) x
    = ⌈ pre_to A (Y:=L) (Z:=U' ◯ K) ta x ⌉² := eq_refl.

(* ---- Palmquist factors through the mate, with NO associator ---- *)

Definition palm_via_mate (al : F' ◯ L ◯ U ⟹ K) : L ⟹ U' ◯ K ◯ F :=
  pre_to A (Y:=L) (Z:=U' ◯ K)
    (SqMate A A' K L (pre_to A (Y:=F' ◯ L) (Z:=K) al)).

Theorem palm_to_via_mate (al : F' ◯ L ◯ U ⟹ K) :
  palm_via_mate al ≈ palm_to al.
Proof.
  intros x; simpl.
  apply compose_respects; [ | reflexivity ].
  apply (to_adj_respects (H:=A')).
  rewrite comp_assoc.
  rewrite (naturality al _ _ (ε (F x))); simpl.
  rewrite <- comp_assoc, <- !fmap_comp.
  rewrite (fmap_counit_unit (H:=A)).
  now rewrite !fmap_id, id_right.
Qed.

(* ---- the two-factor route, which DOES meet the associator ---- *)

Definition palm_two_factor (al : F' ◯ L ◯ U ⟹ K) : L ⟹ U' ◯ (K ◯ F) :=
  post_to A' (Y:=L) (Z:=K ◯ F) (pre_to A (Y:=F' ◯ L) (Z:=K) al).

Theorem palm_two_factor_agrees (al : F' ◯ L ◯ U ⟹ K) (x : D) :
  palm_to al x ≈ palm_two_factor al x.
Proof.
  simpl.
  rewrite <- (to_adj_nat_l (Adjunction:=A')).
  reflexivity.
Qed.

Theorem palm_two_factor_spliced (al : F' ◯ L ◯ U ⟹ K) :
  palm_to al ≈ fun_comp_assoc (F:=U') (G:=K) (H:=F) ∙ palm_two_factor al.
Proof.
  intros x; simpl.
  rewrite (to_adj_nat_l (Adjunction:=A')).
  rewrite fmap_id, id_left.
  reflexivity.
Qed.

Example fun_comp_assoc_component (x : D) :
  transform[fun_comp_assoc (F:=U') (G:=K) (H:=F)] x = fmap[U'] id := eq_refl.

Theorem fun_comp_assoc_is_id (x : D) :
  transform[fun_comp_assoc (F:=U') (G:=K) (H:=F)] x ≈ id.
Proof. simpl; now rewrite !fmap_id. Qed.

End Palmquist.

(* ====================================================================== *)
(* (E) Riehl 4.3.v: horizontal and vertical pasting.                      *)
(* ====================================================================== *)

Section HorizontalPaste.

Context {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U).
Context {C' D' : Category} {F' : D' ⟶ C'} {U' : C' ⟶ D'} (A' : F' ⊣ U').
Context {C'' D'' : Category} {F'' : D'' ⟶ C''} {U'' : C'' ⟶ D''}.
Context (A'' : F'' ⊣ U'').
Context (K : C ⟶ C') (L : D ⟶ D').
Context (K' : C' ⟶ C'') (L' : D' ⟶ D'').

#[local] Obligation Tactic := idtac.

Program Definition paste_h_sigma
  (sg1 : F' ◯ L ⟹ K ◯ F) (sg2 : F'' ◯ L' ⟹ K' ◯ F')
  : F'' ◯ (L' ◯ L) ⟹ (K' ◯ K) ◯ F :=
  {| transform := fun x => fmap[K'] (sg1 x) ∘ sg2 (L x) |}.
Next Obligation.
  intros sg1 sg2 x y f; simpl.
  rewrite comp_assoc, <- !fmap_comp.
  rewrite (naturality sg1 _ _ f); simpl.
  rewrite fmap_comp, <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  now rewrite (naturality sg2 _ _ (fmap[L] f)).
Qed.
Next Obligation. symmetry; now apply paste_h_sigma_obligation_1. Qed.

Program Definition paste_h_tau
  (ta1 : L ◯ U ⟹ U' ◯ K) (ta2 : L' ◯ U' ⟹ U'' ◯ K')
  : (L' ◯ L) ◯ U ⟹ U'' ◯ (K' ◯ K) :=
  {| transform := fun a => ta2 (K a) ∘ fmap[L'] (ta1 a) |}.
Next Obligation.
  intros ta1 ta2 a b f; simpl.
  rewrite comp_assoc.
  rewrite (naturality ta2 _ _ (fmap[K] f)); simpl.
  rewrite <- !comp_assoc, <- !fmap_comp.
  apply compose_respects; [ reflexivity | ].
  apply fmap_respects.
  now rewrite (naturality ta1 _ _ f).
Qed.
Next Obligation. symmetry; now apply paste_h_tau_obligation_1. Qed.

Theorem adjoint_square_paste_h
  (sg1 : F' ◯ L ⟹ K ◯ F) (ta1 : L ◯ U ⟹ U' ◯ K)
  (sg2 : F'' ◯ L' ⟹ K' ◯ F') (ta2 : L' ◯ U' ⟹ U'' ◯ K') :
  AdjointSquareT A A' K L sg1 ta1 →
  AdjointSquareT A' A'' K' L' sg2 ta2 →
  AdjointSquareT A A'' (K' ◯ K) (L' ◯ L)
    (paste_h_sigma sg1 sg2) (paste_h_tau ta1 ta2).
Proof.
  intros H1 H2 x a k; simpl.
  rewrite comp_assoc, <- fmap_comp.
  rewrite (H2 (L x) (K a) (fmap[K] k ∘ sg1 x)).
  rewrite (H1 x a k).
  rewrite fmap_comp.
  now rewrite comp_assoc.
Qed.

Corollary sq_mate_paste_h
  (sg1 : F' ◯ L ⟹ K ◯ F) (sg2 : F'' ◯ L' ⟹ K' ◯ F') :
  SqMate A A'' (K' ◯ K) (L' ◯ L) (paste_h_sigma sg1 sg2)
    ≈ paste_h_tau (SqMate A A' K L sg1) (SqMate A' A'' K' L' sg2).
Proof.
  symmetry.
  apply (SqMate_uniq A A'').
  apply adjoint_square_paste_h; apply AdjointSquareT_SqMate.
Qed.

End HorizontalPaste.

Section VerticalPaste.

Context {D C E : Category}.
Context {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U).
Context {G : C ⟶ E} {V : E ⟶ C} (B : G ⊣ V).
Context {D' C' E' : Category}.
Context {F' : D' ⟶ C'} {U' : C' ⟶ D'} (A' : F' ⊣ U').
Context {G' : C' ⟶ E'} {V' : E' ⟶ C'} (B' : G' ⊣ V').
Context (L : D ⟶ D') (K : C ⟶ C') (M : E ⟶ E').

#[local] Obligation Tactic := idtac.

Program Definition paste_v_sigma
  (sg1 : F' ◯ L ⟹ K ◯ F) (sg2 : G' ◯ K ⟹ M ◯ G)
  : (G' ◯ F') ◯ L ⟹ M ◯ (G ◯ F) :=
  {| transform := fun x => sg2 (F x) ∘ fmap[G'] (sg1 x) |}.
Next Obligation.
  intros sg1 sg2 x y f; simpl.
  rewrite comp_assoc.
  rewrite (naturality sg2 _ _ (fmap[F] f)); simpl.
  rewrite <- !comp_assoc, <- !fmap_comp.
  apply compose_respects; [ reflexivity | ].
  apply fmap_respects.
  now rewrite (naturality sg1 _ _ f).
Qed.
Next Obligation. symmetry; now apply paste_v_sigma_obligation_1. Qed.

Program Definition paste_v_tau
  (ta1 : L ◯ U ⟹ U' ◯ K) (ta2 : K ◯ V ⟹ V' ◯ M)
  : L ◯ (U ◯ V) ⟹ (U' ◯ V') ◯ M :=
  {| transform := fun e => fmap[U'] (ta2 e) ∘ ta1 (V e) |}.
Next Obligation.
  intros ta1 ta2 e e2 f; simpl.
  rewrite comp_assoc, <- !fmap_comp.
  rewrite (naturality ta2 _ _ f); simpl.
  rewrite fmap_comp, <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  now rewrite (naturality ta1 _ _ (fmap[V] f)).
Qed.
Next Obligation. symmetry; now apply paste_v_tau_obligation_1. Qed.

Definition AB  : (G ◯ F) ⊣ (U ◯ V)     := Adjunction_Compose A B.
Definition AB' : (G' ◯ F') ⊣ (U' ◯ V') := Adjunction_Compose A' B'.

(* The composite's transposes are definitional; its unit is not. *)

Example AB_to_strict (x : D) (e : E) (k : G (F x) ~> e) :
  to (@adj _ _ _ _ AB x e) k
    = to (@adj _ _ _ _ A x (V e)) (to (@adj _ _ _ _ B (F x) e) k) := eq_refl.

Theorem AB_unit_upto (x : D) :
  @unit _ _ _ _ AB x
    ≈ fmap[U] (@unit _ _ _ _ B (F x)) ∘ @unit _ _ _ _ A x.
Proof. apply Adjunction_Compose_unit. Qed.

Theorem adjoint_square_paste_v
  (sg1 : F' ◯ L ⟹ K ◯ F) (ta1 : L ◯ U ⟹ U' ◯ K)
  (sg2 : G' ◯ K ⟹ M ◯ G) (ta2 : K ◯ V ⟹ V' ◯ M) :
  AdjointSquareT A A' K L sg1 ta1 →
  AdjointSquareT B B' M K sg2 ta2 →
  AdjointSquareT AB AB' M L (paste_v_sigma sg1 sg2) (paste_v_tau ta1 ta2).
Proof.
  intros H1 H2 x e k; simpl.
  rewrite comp_assoc.
  rewrite (to_adj_nat_l (Adjunction:=B')).
  rewrite (H2 (F x) e k).
  rewrite <- (comp_assoc (ta2 e)
                (fmap[K] (to (@adj _ _ _ _ B (F x) e) k)) (sg1 x)).
  rewrite (to_adj_nat_r (Adjunction:=A')).
  rewrite (H1 x (V e) (to (@adj _ _ _ _ B (F x) e) k)).
  now rewrite comp_assoc.
Qed.

Corollary sq_mate_paste_v
  (sg1 : F' ◯ L ⟹ K ◯ F) (sg2 : G' ◯ K ⟹ M ◯ G) :
  SqMate AB AB' M L (paste_v_sigma sg1 sg2)
    ≈ paste_v_tau (SqMate A A' K L sg1) (SqMate B B' M K sg2).
Proof.
  symmetry.
  apply (SqMate_uniq AB AB').
  apply adjoint_square_paste_v; apply AdjointSquareT_SqMate.
Qed.

End VerticalPaste.
