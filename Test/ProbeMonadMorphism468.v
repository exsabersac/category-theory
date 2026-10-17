(*
   本文件为测试：ProbeMonadMorphism468。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Monad.
Require Import Category.Instance.Fun.
Require Import Category.Monad.Morphism.
Require Import Category.Theory.Isomorphism.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Cat.
Require Import Category.Monad.Morphism.Algebra.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Compose.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Monad.Morphism.Monoid.
Require Import Category.Monad.Transformer.
Require Import Category.Monad.Morphism.Transformer.
Require Import Category.Construction.Deloop.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.Action.Monad.
Require Import Category.Instance.Fun.Action.Monad.BG.
Require Import Category.Instance.Fun.Action.Monad.BG.Morphism.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Monad.
Require Import Category.Instance.SupLat.
Require Import Category.Instance.SupLat.Free.
Require Import Category.Instance.SupLat.Free.Morphism.

Generalizable All Variables.

(* ------------------------------------------------------------------------ *)
(** ** Part (a): Monad/Morphism.v *)

(* C1: the right factor of [mh_join] is [nat_hcompose θ θ] at x. *)
Example p468_c1_hcompose@{o h s | h < s +} {C : Category@{o h h}}
  {T T2 : C ⟶ C} {M : @Monad C T} {M2 : @Monad C T2}
  (θ : MonadHom@{o h} M M2) (x : C) :
  transform[nat_hcompose@{s o o o h} (mh_transform θ) (mh_transform θ)] x
    = mh_transform θ (T2 x) ∘ fmap[T] (mh_transform θ x) := eq_refl.

(* C2: the ≈ of [Monads C] is the ≈ of [C, C] on [mh_transform]. *)
Example p468_c2_equiv@{o h m1 m2 u |
  h < u, o <= m1, h <= m1, o <= m2, h <= m2 +}
  (C : Category@{o h h}) (N N2 : Monads@{o h m1 m2} C)
  (θ φ : N ~{Monads@{o h m1 m2} C}~> N2) :
  @equiv _ (@homset (Monads@{o h m1 m2} C) N N2) θ φ
    = @equiv _ (@homset (@Fun@{o h o h m1 m2 u} C C) (projT1 N) (projT1 N2))
        (mh_transform θ) (mh_transform φ) := eq_refl.

(* C3: the identity of [Monads C] has components [id]. *)
Example p468_c3_id_components@{o h m1 m2 |
  o <= m1, h <= m1, o <= m2, h <= m2 +}
  (C : Category@{o h h}) (N : Monads@{o h m1 m2} C) (x : C) :
  mh_transform (@id (Monads@{o h m1 m2} C) N) x = id := eq_refl.

(* C4: the identity of [C, C] has components [fmap[T] id]. *)
Example p468_c4_fun_id@{o h m1 m2 u |
  h < u, o <= m1, h <= m1, o <= m2, h <= m2 +}
  (C : Category@{o h h}) (T : C ⟶ C) (x : C) :
  transform[@id (@Fun@{o h o h m1 m2 u} C C) T] x = fmap[T] id := eq_refl.

(* C46: [Monads_Forget] is the first projection on objects. *)
Example p468_c46_mforget_obj@{o h m1 m2 u |
  h < u, o <= m1, h <= m1, o <= m2, h <= m2 +} (C : Category@{o h h})
  (N : Monads@{o h m1 m2} C) :
  fobj[Monads_Forget@{o h m1 m2 u} C] N = projT1 N := eq_refl.

(* C47: and [mh_transform] on arrows. *)
Example p468_c47_mforget_map@{o h m1 m2 u |
  h < u, o <= m1, h <= m1, o <= m2, h <= m2 +} (C : Category@{o h h})
  (N N2 : Monads@{o h m1 m2} C) (θ : N ~{Monads@{o h m1 m2} C}~> N2) :
  fmap[Monads_Forget@{o h m1 m2 u} C] θ = mh_transform θ := eq_refl.

(* R6 *)
Fail Example p468_r6_forget_id@{o h m1 m2 u |
  h < u, o <= m1, h <= m1, o <= m2, h <= m2 +}
  (C : Category@{o h h}) (N : Monads@{o h m1 m2} C) (x : C) :
  transform[fmap[Monads_Forget@{o h m1 m2 u} C]
              (@id (Monads@{o h m1 m2} C) N)] x
    = transform[@id (@Fun@{o h o h m1 m2 u} C C) (projT1 N)] x := eq_refl.

(* C37: the composition law of [Monads_Forget] at a component. *)
Example p468_c37_forget_comp@{o h m1 m2 u |
  h < u, o <= m1, h <= m1, o <= m2, h <= m2 +}
  (C : Category@{o h h}) (N N2 N3 : Monads@{o h m1 m2} C)
  (φ : N2 ~{Monads@{o h m1 m2} C}~> N3)
  (θ : N ~{Monads@{o h m1 m2} C}~> N2) (x : C) :
  transform[fmap[Monads_Forget@{o h m1 m2 u} C] (φ ∘ θ)] x
    = transform[fmap[Monads_Forget@{o h m1 m2 u} C] φ
                ∘ fmap[Monads_Forget@{o h m1 m2 u} C] θ] x := eq_refl.

(* R18 *)
Fail Example p468_r18_forget_comp@{o h m1 m2 u |
  h < u, o <= m1, h <= m1, o <= m2, h <= m2 +}
  (C : Category@{o h h}) (N N2 N3 : Monads@{o h m1 m2} C)
  (φ : N2 ~{Monads@{o h m1 m2} C}~> N3)
  (θ : N ~{Monads@{o h m1 m2} C}~> N2) :
  fmap[Monads_Forget@{o h m1 m2 u} C] (φ ∘ θ)
    = fmap[Monads_Forget@{o h m1 m2 u} C] φ
      ∘ fmap[Monads_Forget@{o h m1 m2 u} C] θ := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Part (b): the direction of F^T ⇝ θ* ∘ F^{T'} *)

(* C5: the page's direction is a well-formed type. *)
Definition p468_c5_book_type@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T2 : C ⟶ C}
  {M : @Monad C T} {M2 : @Monad C T2} (θ : MonadHom@{o h} M M2) :=
  @EM_Free@{o h s e} C T M ⟹ mh_EM@{o h e s} θ ◯ @EM_Free@{o h s e} C T2 M2.

(* C6: [mh_EM_free θ] inhabits it. *)
Definition p468_c6_free_type@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T2 : C ⟶ C}
  {M : @Monad C T} {M2 : @Monad C T2} (θ : MonadHom@{o h} M M2) :
  p468_c5_book_type@{o h e s} θ := mh_EM_free@{o h e s} θ.

(* R1 *)
Fail Definition p468_r1_issue_direction@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T2 : C ⟶ C}
  {M : @Monad C T} {M2 : @Monad C T2} (θ : MonadHom@{o h} M M2) :=
  @EM_Free@{o h s e} C T2 M2 ⟹ mh_EM@{o h e s} θ ◯ @EM_Free@{o h s e} C T M.

(* ------------------------------------------------------------------------ *)
(** ** Part (b): G^T ∘ θ* = G^{T'} *)

(* C7: on objects. *)
Example p468_c7_forget_obj@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T2 : C ⟶ C}
  {M : @Monad C T} {M2 : @Monad C T2} (θ : MonadHom@{o h} M M2)
  (X : @EilenbergMoore@{e o s h} C T2 M2) :
  fobj[@EM_Forget@{o h s e} C T M ◯ mh_EM@{o h e s} θ] X
    = fobj[@EM_Forget@{o h s e} C T2 M2] X := eq_refl.

(* C8: on objects, as a function. *)
Example p468_c8_forget_obj_fun@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T2 : C ⟶ C}
  {M : @Monad C T} {M2 : @Monad C T2} (θ : MonadHom@{o h} M M2) :
  (fun X => fobj[@EM_Forget@{o h s e} C T M ◯ mh_EM@{o h e s} θ] X)
    = (fun X => fobj[@EM_Forget@{o h s e} C T2 M2] X) := eq_refl.

(* C9: on arrows. *)
Example p468_c9_forget_map@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T2 : C ⟶ C}
  {M : @Monad C T} {M2 : @Monad C T2} (θ : MonadHom@{o h} M M2)
  (X Y : @EilenbergMoore@{e o s h} C T2 M2) (f : X ~> Y) :
  fmap[@EM_Forget@{o h s e} C T M ◯ mh_EM@{o h e s} θ] f
    = fmap[@EM_Forget@{o h s e} C T2 M2] f := eq_refl.

(* C10: the [fobj] fields of the two functors. *)
Example p468_c10_fobj_field@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T2 : C ⟶ C}
  {M : @Monad C T} {M2 : @Monad C T2} (θ : MonadHom@{o h} M M2) :
  @fobj _ _ (@EM_Forget@{o h s e} C T M ◯ mh_EM@{o h e s} θ)
    = @fobj _ _ (@EM_Forget@{o h s e} C T2 M2) := eq_refl.

(* C11: the [fmap] fields of the two functors. *)
Example p468_c11_fmap_field@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T2 : C ⟶ C}
  {M : @Monad C T} {M2 : @Monad C T2} (θ : MonadHom@{o h} M M2) :
  @fmap _ _ (@EM_Forget@{o h s e} C T M ◯ mh_EM@{o h e s} θ)
    = @fmap _ _ (@EM_Forget@{o h s e} C T2 M2) := eq_refl.

(* C12: the object equation of [mh_EM_forget_strict] IS [eq_refl]. *)
Example p468_c12_strict_obj@{o h e s a b |
  h < s, o <= e, h <= e, o <= a, h <= a, e <= a, h <= b, e <= b +}
  {C : Category@{o h h}} {T T2 : C ⟶ C}
  {M : @Monad C T} {M2 : @Monad C T2} (θ : MonadHom@{o h} M M2)
  (X : @EilenbergMoore@{e o s h} C T2 M2) :
  projT1 (mh_EM_forget_strict@{o h e s a b} θ) X = eq_refl := eq_refl.

(* C41: both legs of the isomorphisms of [mh_EM_forget] are identities. *)
Example p468_c41_forget_iso@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T2 : C ⟶ C}
  {M : @Monad C T} {M2 : @Monad C T2} (θ : MonadHom@{o h} M M2)
  (X : @EilenbergMoore@{e o s h} C T2 M2) :
  (to (projT1 (mh_EM_forget@{o h e s} θ) X),
   from (projT1 (mh_EM_forget@{o h e s} θ) X))
    = (@id C (`1 X), @id C (`1 X)) := eq_refl.

(* R2 *)
Fail Example p468_r2_forget_eq@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T2 : C ⟶ C}
  {M : @Monad C T} {M2 : @Monad C T2} (θ : MonadHom@{o h} M M2) :
  @EM_Forget@{o h s e} C T M ◯ mh_EM@{o h e s} θ
    = @EM_Forget@{o h s e} C T2 M2 := eq_refl.

(* R2a *)
Fail Example p468_r2a_fmap_respects@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T2 : C ⟶ C}
  {M : @Monad C T} {M2 : @Monad C T2} (θ : MonadHom@{o h} M M2) :
  @fmap_respects _ _ (@EM_Forget@{o h s e} C T M ◯ mh_EM@{o h e s} θ)
    = @fmap_respects _ _ (@EM_Forget@{o h s e} C T2 M2) := eq_refl.

(* R2b *)
Fail Example p468_r2b_fmap_id@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T2 : C ⟶ C}
  {M : @Monad C T} {M2 : @Monad C T2} (θ : MonadHom@{o h} M M2) :
  @fmap_id _ _ (@EM_Forget@{o h s e} C T M ◯ mh_EM@{o h e s} θ)
    = @fmap_id _ _ (@EM_Forget@{o h s e} C T2 M2) := eq_refl.

(* R2c *)
Fail Example p468_r2c_fmap_comp@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T2 : C ⟶ C}
  {M : @Monad C T} {M2 : @Monad C T2} (θ : MonadHom@{o h} M M2) :
  @fmap_comp _ _ (@EM_Forget@{o h s e} C T M ◯ mh_EM@{o h e s} θ)
    = @fmap_comp _ _ (@EM_Forget@{o h s e} C T2 M2) := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Part (b): F^T ⇝ θ* ∘ F^{T'} *)

(* C13: each component is θ_x under G^T. *)
Example p468_c13_free_forget@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T2 : C ⟶ C}
  {M : @Monad C T} {M2 : @Monad C T2} (θ : MonadHom@{o h} M M2) (x : C) :
  t_alg_hom[transform[mh_EM_free@{o h e s} θ] x] = mh_transform θ x
  := eq_refl.

(* C18: the underlying arrow of the transpose of η'_x. *)
Example p468_c18_transpose_arrow@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T2 : C ⟶ C}
  {M : @Monad C T} {M2 : @Monad C T2} (θ : MonadHom@{o h} M M2) (x : C) :
  t_alg_hom[@EM_extend@{o h e s} C T M x
                 (fobj[mh_EM@{o h e s} θ ◯ @EM_Free@{o h s e} C T2 M2] x)
                 (@ret C T2 M2 x)]
    = (@join C T2 M2 x ∘ mh_transform θ (T2 x)) ∘ fmap[T] (@ret C T2 M2 x)
  := eq_refl.

(* R5 *)
Fail Example p468_r5_transpose@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T2 : C ⟶ C}
  {M : @Monad C T} {M2 : @Monad C T2} (θ : MonadHom@{o h} M M2) (x : C) :
  t_alg_hom[@EM_extend@{o h e s} C T M x
                 (fobj[mh_EM@{o h e s} θ ◯ @EM_Free@{o h s e} C T2 M2] x)
                 (@ret C T2 M2 x)]
    = mh_transform θ x := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Part (b): functoriality in θ *)

(* C63: θ* writes the structure map h' as h' ∘ θ_a. *)
Example p468_c63_alg@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T2 : C ⟶ C}
  {M : @Monad C T} {M2 : @Monad C T2} (θ : MonadHom@{o h} M M2)
  (X : @EilenbergMoore@{e o s h} C T2 M2) :
  @t_alg _ _ _ _ (`2 (fobj[mh_EM@{o h e s} θ] X))
    = @t_alg _ _ _ _ (`2 X) ∘ mh_transform θ (`1 X) := eq_refl.

(* C14: (id)* keeps the carrier. *)
Example p468_c14_id_carrier@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T : C ⟶ C} {M : @Monad C T}
  (X : @EilenbergMoore@{e o s h} C T M) :
  `1 (fobj[mh_EM@{o h e s} (mh_id M)] X) = `1 X := eq_refl.

(* C15: (id)* writes h ∘ id. *)
Example p468_c15_id_alg@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T : C ⟶ C} {M : @Monad C T}
  (X : @EilenbergMoore@{e o s h} C T M) :
  @t_alg _ _ _ _ (`2 (fobj[mh_EM@{o h e s} (mh_id M)] X))
    = @t_alg _ _ _ _ (`2 X) ∘ id := eq_refl.

(* R3 *)
Fail Example p468_r3_id_obj@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T : C ⟶ C} {M : @Monad C T}
  (X : @EilenbergMoore@{e o s h} C T M) :
  fobj[mh_EM@{o h e s} (mh_id M)] X = X := eq_refl.

(* C16: (φ ∘ θ)* writes h ∘ (φ ∘ θ). *)
Example p468_c16_comp_alg@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T2 T3 : C ⟶ C}
  {M : @Monad C T} {M2 : @Monad C T2} {M3 : @Monad C T3}
  (φ : MonadHom@{o h} M2 M3) (θ : MonadHom@{o h} M M2)
  (X : @EilenbergMoore@{e o s h} C T3 M3) :
  @t_alg _ _ _ _ (`2 (fobj[mh_EM@{o h e s} (mh_compose φ θ)] X))
    = @t_alg _ _ _ _ (`2 X) ∘ (mh_transform φ (`1 X) ∘ mh_transform θ (`1 X))
  := eq_refl.

(* C17: (φ ∘ θ)* and θ* ◯ φ* keep the same underlying arrows. *)
Example p468_c17_comp_hom@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T2 T3 : C ⟶ C}
  {M : @Monad C T} {M2 : @Monad C T2} {M3 : @Monad C T3}
  (φ : MonadHom@{o h} M2 M3) (θ : MonadHom@{o h} M M2)
  (X Y : @EilenbergMoore@{e o s h} C T3 M3) (f : X ~> Y) :
  t_alg_hom[fmap[mh_EM@{o h e s} (mh_compose φ θ)] f]
    = t_alg_hom[fmap[mh_EM@{o h e s} θ ◯ mh_EM@{o h e s} φ] f] := eq_refl.

(* R4 *)
Fail Example p468_r4_comp_obj@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T2 T3 : C ⟶ C}
  {M : @Monad C T} {M2 : @Monad C T2} {M3 : @Monad C T3}
  (φ : MonadHom@{o h} M2 M3) (θ : MonadHom@{o h} M M2)
  (X : @EilenbergMoore@{e o s h} C T3 M3) :
  fobj[mh_EM@{o h e s} (mh_compose φ θ)] X
    = fobj[mh_EM@{o h e s} θ ◯ mh_EM@{o h e s} φ] X := eq_refl.

(* C42: both legs of the isomorphism of (id)* ≈ Id have underlying arrow
   [id]. *)
Example p468_c42_id_iso@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T : C ⟶ C} {M : @Monad C T}
  (X : @EilenbergMoore@{e o s h} C T M) :
  (t_alg_hom[to (projT1 (@mh_EM_id@{o h e s} C T M) X)],
   t_alg_hom[from (projT1 (@mh_EM_id@{o h e s} C T M) X)])
    = (@id C (`1 X), @id C (`1 X)) := eq_refl.

(* C43: so have those of (φ ∘ θ)* ≈ θ* ◯ φ*. *)
Example p468_c43_comp_iso@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T2 T3 : C ⟶ C}
  {M : @Monad C T} {M2 : @Monad C T2} {M3 : @Monad C T3}
  (φ : MonadHom@{o h} M2 M3) (θ : MonadHom@{o h} M M2)
  (X : @EilenbergMoore@{e o s h} C T3 M3) :
  (t_alg_hom[to (projT1 (mh_EM_compose@{o h e s} φ θ) X)],
   t_alg_hom[from (projT1 (mh_EM_compose@{o h e s} φ θ) X)])
    = (@id C (`1 X), @id C (`1 X)) := eq_refl.

(* C44: and those of θ* ≈ θ2*, for θ ≈ θ2. *)
Example p468_c44_respects_iso@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T2 : C ⟶ C}
  {M : @Monad C T} {M2 : @Monad C T2} (θ θ2 : MonadHom@{o h} M M2)
  (E : ∀ x, mh_transform θ x ≈ mh_transform θ2 x)
  (X : @EilenbergMoore@{e o s h} C T2 M2) :
  (t_alg_hom[to (projT1 (mh_EM_respects@{o h e s} θ θ2 E) X)],
   t_alg_hom[from (projT1 (mh_EM_respects@{o h e s} θ θ2 E) X)])
    = (@id C (`1 X), @id C (`1 X)) := eq_refl.

(* C48: [Monads_EM] sends a monad to its Eilenberg–Moore category. *)
Example p468_c48_em_obj@{o h m1 m2 e s u |
  h < s, h < u, e < u, o <= m1, h <= m1, o <= m2, h <= m2, m2 <= e,
  o <= e, h <= e +} (C : Category@{o h h}) (N : Monads@{o h m1 m2} C) :
  fobj[Monads_EM@{o h m1 m2 e s u} C] N
    = @EilenbergMoore@{e o s h} C (projT1 N) (projT2 N) := eq_refl.

(* C49: and a morphism θ to θ*. *)
Example p468_c49_em_map@{o h m1 m2 e s u |
  h < s, h < u, e < u, o <= m1, h <= m1, o <= m2, h <= m2, m2 <= e,
  o <= e, h <= e +} (C : Category@{o h h}) (N N2 : Monads@{o h m1 m2} C)
  (θ : N2 ~{Monads@{o h m1 m2} C}~> N) :
  fmap[Monads_EM@{o h m1 m2 e s u} C] θ = mh_EM@{o h e s} θ := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Monad/Morphism/Monoid.v *)

(* C19: the tensor of [Compose_Monoidal] on (θ, θ), at x. *)
Example p468_c19_bimap@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T T2 : C ⟶ C}
  {M : @Monad C T} {M2 : @Monad C T2} (θ : MonadHom@{o h} M M2) (x : C) :
  transform[@bimap _ _ _ (@tensor _ (@Compose_Monoidal@{s f o h} C))
              _ _ _ _ (mh_transform θ) (mh_transform θ)] x
    = mh_transform θ (T2 x) ∘ fmap[T] (mh_transform θ x) := eq_refl.

(* C20: the type of [mh_join] is the multiplication square's. *)
Example p468_c20_hom_mu_type@{o h f s q |
  h < s, o <= f, h <= f, o < q, h < q +}
  {C : Category@{o h h}} {T T2 : C ⟶ C}
  {M : @Monad C T} {M2 : @Monad C T2} (θ : MonadHom@{o h} M M2) :
  @eq Type@{q}
    (∀ x : C, mh_transform θ x ∘ @join C T M x
                ≈ @join C T2 M2 x
                    ∘ (mh_transform θ (T2 x) ∘ fmap[T] (mh_transform θ x)))
    (@compose (@Fun@{o h o h f f s} C C) _ _ _
       (mh_transform θ) (@mu _ _ _ (monad_monoid@{o h f s} M))
     ≈ @compose (@Fun@{o h o h f f s} C C) _ _ _
         (@mu _ _ _ (monad_monoid@{o h f s} M2))
         (@bimap _ _ _ (@tensor _ (@Compose_Monoidal@{s f o h} C))
            _ _ _ _ (mh_transform θ) (mh_transform θ)))
  := eq_refl.

(* C52: the type of [mh_ret] is the unit triangle's. *)
Example p468_c52_hom_eta_type@{o h f s q |
  h < s, o <= f, h <= f, o < q, h < q +}
  {C : Category@{o h h}} {T T2 : C ⟶ C}
  {M : @Monad C T} {M2 : @Monad C T2} (θ : MonadHom@{o h} M M2) :
  @eq Type@{q} (∀ x : C, mh_transform θ x ∘ @ret C T M x ≈ @ret C T2 M2 x)
  (@compose (@Fun@{o h o h f f s} C C) _ _ _
       (mh_transform θ) (@eta _ _ _ (monad_monoid@{o h f s} M))
     ≈ @eta _ _ _ (monad_monoid@{o h f s} M2)) := eq_refl.

(* C38: the square of [mh_monoidhom θ] at x IS [mh_join θ] at x. *)
Example p468_c38_hom_mu_term@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T T2 : C ⟶ C}
  {M : @Monad C T} {M2 : @Monad C T2} (θ : MonadHom@{o h} M M2) (x : C) :
  @hom_mu _ _ _ _ _ _ _ (mh_monoidhom@{o h f s} θ) x = @mh_join _ _ _ _ _ θ x
  := eq_refl.

(* C39: the [mh_join] of [monoidhom_mh θ H] IS the square of H. *)
Example p468_c39_mh_join_term@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T T2 : C ⟶ C}
  {M : @Monad C T} {M2 : @Monad C T2} (θ : T ⟹ T2)
  (H : @MonoidHom (@Fun@{o h o h f f s} C C) (@Compose_Monoidal@{s f o h} C)
         T T2 (monad_monoid@{o h f s} M) (monad_monoid@{o h f s} M2) θ)
  (x : C) :
  @mh_join _ _ _ _ _ (monoidhom_mh@{o h f s} θ H) x
    = @hom_mu _ _ _ _ _ _ _ H x := eq_refl.

(* C53: [monoidhom_mh θ H] has the transformation θ itself. *)
Example p468_c53_mh_transform@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T T2 : C ⟶ C}
  {M : @Monad C T} {M2 : @Monad C T2} (θ : T ⟹ T2)
  (H : @MonoidHom (@Fun@{o h o h f f s} C C) (@Compose_Monoidal@{s f o h} C)
         T T2 (monad_monoid@{o h f s} M) (monad_monoid@{o h f s} M2) θ) :
  mh_transform (monoidhom_mh@{o h f s} θ H) = θ := eq_refl.

(* C54: [Monads_Mon] on objects. *)
Example p468_c54_mon_obj@{o h m1 m2 f s mo t |
  h < s, f < t, o <= m1, h <= m1, o <= m2, h <= m2, m2 <= f,
  o <= f, h <= f, f <= mo +}
  (C : Category@{o h h}) (N : Monads@{o h m1 m2} C) :
  fobj[Monads_Mon@{o h m1 m2 f s mo t} C] N
    = (projT1 N; monad_monoid@{o h f s} (projT2 N)) := eq_refl.

(* C55: [Monads_Mon] on arrows. *)
Example p468_c55_mon_map@{o h m1 m2 f s mo t |
  h < s, f < t, o <= m1, h <= m1, o <= m2, h <= m2, m2 <= f,
  o <= f, h <= f, f <= mo +}
  (C : Category@{o h h}) (N N2 : Monads@{o h m1 m2} C)
  (θ : N ~{Monads@{o h m1 m2} C}~> N2) :
  fmap[Monads_Mon@{o h m1 m2 f s mo t} C] θ
    = (mh_transform θ; mh_monoidhom@{o h f s} θ) := eq_refl.

(* C21: [Monads_Mon] on an identity has components [id]. *)
Example p468_c21_mon_id_left@{o h m1 f s mo t |
  h < s, f < t, o <= m1, h <= m1, o <= f, h <= f, f <= mo +}
  (C : Category@{o h h}) (N : Monads@{o h m1 f} C) (x : C) :
  transform[projT1 (fmap[Monads_Mon@{o h m1 f f s mo t} C]
                       (@id (Monads@{o h m1 f} C) N))] x
    = @id C (projT1 N x) := eq_refl.

(* C22: the identity of [Mon [C, C]] has components fmap[T] id. *)
Example p468_c22_mon_id_right@{o h m1 f s mo t |
  h < s, f < t, o <= m1, h <= m1, o <= f, h <= f, f <= mo +}
  (C : Category@{o h h}) (N : Monads@{o h m1 f} C) (x : C) :
  transform[projT1 (@id (@Mon@{f f mo t} (@Fun@{o h o h f f s} C C)
                          (@Compose_Monoidal@{s f o h} C))
                       (fobj[Monads_Mon@{o h m1 f f s mo t} C] N))] x
    = fmap[projT1 N] (@id C x) := eq_refl.

(* R7 *)
Fail Example p468_r7_mon_id@{o h m1 f s mo t |
  h < s, f < t, o <= m1, h <= m1, o <= f, h <= f, f <= mo +}
  (C : Category@{o h h}) (N : Monads@{o h m1 f} C) (x : C) :
  transform[projT1 (fmap[Monads_Mon@{o h m1 f f s mo t} C]
                       (@id (Monads@{o h m1 f} C) N))] x
    = transform[projT1 (@id (@Mon@{f f mo t} (@Fun@{o h o h f f s} C C)
                               (@Compose_Monoidal@{s f o h} C))
                          (fobj[Monads_Mon@{o h m1 f f s mo t} C] N))] x
  := eq_refl.

(* C23: [Monads_Mon] on a composite, at a component. *)
Example p468_c23_mon_comp@{o h m1 f s mo t |
  h < s, f < t, o <= m1, h <= m1, o <= f, h <= f, f <= mo +}
  (C : Category@{o h h}) (N N2 N3 : Monads@{o h m1 f} C)
  (φ : N2 ~{Monads@{o h m1 f} C}~> N3) (θ : N ~{Monads@{o h m1 f} C}~> N2)
  (x : C) :
  transform[projT1 (fmap[Monads_Mon@{o h m1 f f s mo t} C] (φ ∘ θ))] x
    = transform[projT1 (fmap[Monads_Mon@{o h m1 f f s mo t} C] φ
                        ∘ fmap[Monads_Mon@{o h m1 f f s mo t} C] θ)] x
  := eq_refl.

(* C50: μ of [monad_monoid M] is [join], at x. *)
Example p468_c50_monoid_mu@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T : C ⟶ C} (M : @Monad C T) (x : C) :
  transform[@mu _ _ _ (monad_monoid@{o h f s} M)] x = @join C T M x
  := eq_refl.

(* C51: η of [monad_monoid M] is [ret], at x. *)
Example p468_c51_monoid_eta@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T : C ⟶ C} (M : @Monad C T) (x : C) :
  transform[@eta _ _ _ (monad_monoid@{o h f s} M)] x = @ret C T M x
  := eq_refl.

(* C24: the unit and multiplication of the monad round trip are M's. *)
Example p468_c24_monad_round@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T : C ⟶ C} (M : @Monad C T) (x : C) :
  (@ret C T (monoid_monad@{o h f s} (monad_monoid@{o h f s} M)) x,
   @join C T (monoid_monad@{o h f s} (monad_monoid@{o h f s} M)) x)
    = (@ret C T M x, @join C T M x) := eq_refl.

(* R8 *)
Fail Example p468_r8_monad_round@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T : C ⟶ C} (M : @Monad C T) :
  monoid_monad@{o h f s} (monad_monoid@{o h f s} M) = M := eq_refl.

(* C25: μ and η of the monoid round trip are N's, at x. *)
Example p468_c25_monoid_round@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T : C ⟶ C}
  (N : @Monoid (@Fun@{o h o h f f s} C C) (@Compose_Monoidal@{s f o h} C) T)
  (x : C) :
  (transform[@mu _ _ _ (monad_monoid@{o h f s} (monoid_monad@{o h f s} N))] x,
   transform[@eta _ _ _ (monad_monoid@{o h f s} (monoid_monad@{o h f s} N))] x)
    = (transform[@mu _ _ _ N] x, transform[@eta _ _ _ N] x) := eq_refl.

(* R9 *)
Fail Example p468_r9_monoid_round@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T : C ⟶ C}
  (N : @Monoid (@Fun@{o h o h f f s} C C) (@Compose_Monoidal@{s f o h} C) T) :
  monad_monoid@{o h f s} (monoid_monad@{o h f s} N) = N := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Monad/Morphism/Transformer.v *)

(* C56: the components of [transformer_hom L] are L's lift. *)
Example p468_c56_trans_lift@{o h | +} {C : Category@{o h h}} {M : C ⟶ C}
  {HM : @Monad C M} {T : (C ⟶ C) → (C ⟶ C)} {HT : @Monad C (T M)}
  (L : @MonadTransformer C M HM T HT) (x : C) :
  mh_transform (transformer_hom@{o h} L) x = @lift C M HM T HT L x
  := eq_refl.

(* C57: the lift of [hom_transformer θ] has the components of θ. *)
Example p468_c57_hom_lift@{o h | +} {C : Category@{o h h}} {M : C ⟶ C}
  {HM : @Monad C M} {T : (C ⟶ C) → (C ⟶ C)} {HT : @Monad C (T M)}
  (θ : MonadHom@{o h} HM HT) (x : C) :
  @lift C M HM T HT (hom_transformer@{o h} θ) x = mh_transform θ x
  := eq_refl.

(* C26: the lift of the transformer round trip is L's. *)
Example p468_c26_trans_round@{o h | +} {C : Category@{o h h}}
  {M : C ⟶ C} {HM : @Monad C M} {T : (C ⟶ C) → (C ⟶ C)}
  {HT : @Monad C (T M)} (L : @MonadTransformer C M HM T HT) (x : C) :
  @lift C M HM T HT (hom_transformer@{o h} (transformer_hom@{o h} L)) x
    = @lift C M HM T HT L x := eq_refl.

(* R10 *)
Fail Example p468_r10_trans_round@{o h | +} {C : Category@{o h h}}
  {M : C ⟶ C} {HM : @Monad C M} {T : (C ⟶ C) → (C ⟶ C)}
  {HT : @Monad C (T M)} (L : @MonadTransformer C M HM T HT) :
  hom_transformer@{o h} (transformer_hom@{o h} L) = L := eq_refl.

(* C27: the components of the hom round trip are θ's. *)
Example p468_c27_hom_round@{o h | +} {C : Category@{o h h}}
  {M : C ⟶ C} {HM : @Monad C M} {T : (C ⟶ C) → (C ⟶ C)}
  {HT : @Monad C (T M)} (θ : MonadHom@{o h} HM HT) (x : C) :
  mh_transform (transformer_hom@{o h} (hom_transformer@{o h} θ)) x
    = mh_transform θ x := eq_refl.

(* R11 *)
Fail Example p468_r11_hom_round@{o h | +} {C : Category@{o h h}}
  {M : C ⟶ C} {HM : @Monad C M} {T : (C ⟶ C) → (C ⟶ C)}
  {HT : @Monad C (T M)} (θ : MonadHom@{o h} HM HT) :
  transformer_hom@{o h} (hom_transformer@{o h} θ) = θ := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Instance/Fun/Action/Monad/BG/Morphism.v *)

(* C58: [BG_theta M] has identity components. *)
Example p468_c58_bg_component@{o so | o < so +} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) :
  mh_transform (BG_theta@{o so} M) X = @id Sets@{o so} (act_prod M X)
  := eq_refl.

(* C59: so has [BG_theta_inv M]. *)
Example p468_c59_bg_inv_component@{o so | o < so +} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) :
  mh_transform (BG_theta_inv@{o so} M) X = @id Sets@{o so} (act_prod M X)
  := eq_refl.

(* C28: θ* keeps the carrier. *)
Example p468_c28_bg_carrier@{o so | o < so +} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M)) :
  `1 (fobj[mh_EM@{so o so so} (BG_theta@{o so} M)] x) = `1 x := eq_refl.

(* C29: θ* keeps the structure map as a function. *)
Example p468_c29_bg_alg_fun@{o so | o < so +} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M)) :
  (fun p => @t_alg _ _ _ _
              (`2 (fobj[mh_EM@{so o so so} (BG_theta@{o so} M)] x)) p)
    = (fun p => @t_alg _ _ _ _ (`2 x) p) := eq_refl.

(* C30: θ* keeps underlying arrows. *)
Example p468_c30_bg_hom@{o so | o < so +} (M : MonObject@{o o o})
  (x y : @EilenbergMoore@{so so so o} Sets@{o so}
           (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M))
  (f : x ~> y) :
  t_alg_hom[fmap[mh_EM@{so o so so} (BG_theta@{o so} M)] f]
    = t_alg_hom[f] := eq_refl.

(* C31: BG.v's [BG_Act_EM] keeps the structure map as a setoid morphism. *)
Example p468_c31_bg_orig_alg@{o so | o < so +} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M)) :
  @t_alg _ _ _ _ (`2 (fobj[BG_Act_EM@{o so} M] x)) = @t_alg _ _ _ _ (`2 x)
  := eq_refl.

(* C32: θ*'s structure map IS h ∘ id in Sets. *)
Example p468_c32_bg_alg_compose@{o so | o < so +} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M)) :
  @t_alg _ _ _ _ (`2 (fobj[mh_EM@{so o so so} (BG_theta@{o so} M)] x))
    = @compose Sets@{o so} _ _ _ (@t_alg _ _ _ _ (`2 x))
        (@id Sets@{o so} (act_prod M (`1 x))) := eq_refl.

(* R12 *)
Example p468_r12_bg_alg@{o so | o < so +} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M)) :
  @t_alg _ _ _ _ (`2 (fobj[mh_EM@{so o so so} (BG_theta@{o so} M)] x))
    = @t_alg _ _ _ _ (`2 x) := eq_refl.

(* R13 *)
Fail Example p468_r13_bg_obj@{o so | o < so +} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M)) :
  fobj[mh_EM@{so o so so} (BG_theta@{o so} M)] x = fobj[BG_Act_EM@{o so} M] x
  := eq_refl.

(* C33: [Act_BG_EM] against BG.v's [Act_BG_alg], as functions. *)
Example p468_c33_actbg_alg_fun@{o so | o < so +} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
         (ActMonad@{o so} M)) :
  (fun p => @t_alg _ _ _ _ (`2 (fobj[Act_BG_EM@{o so} M] x)) p)
    = (fun p => @t_alg _ _ _ _ (Act_BG_alg@{o so} M (`1 x) (`2 x)) p)
  := eq_refl.

(* C60: [Act_BG_EM] keeps the carrier. *)
Example p468_c60_actbg_carrier@{o so | o < so +} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
         (ActMonad@{o so} M)) :
  `1 (fobj[Act_BG_EM@{o so} M] x) = `1 x := eq_refl.

(* R14 *)
Example p468_r14_actbg_alg@{o so | o < so +} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
         (ActMonad@{o so} M)) :
  @t_alg _ _ _ _ (`2 (fobj[Act_BG_EM@{o so} M] x))
    = @t_alg _ _ _ _ (Act_BG_alg@{o so} M (`1 x) (`2 x)) := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Instance/SupLat/Free/Morphism.v *)

(* C61: [SL_theta] has identity components. *)
Example p468_c61_sl_component@{o so | Set < o, o < so +}
  (X : SetoidObject@{o o}) :
  mh_transform SL_theta@{o so} X
    = @id Sets@{o so} (fobj[Powerset_Prop@{o so}] X) := eq_refl.

(* C45: [SL_theta_inv] has identity components. *)
Example p468_c45_sl_inv_component@{o so | Set < o, o < so +}
  (X : SetoidObject@{o o}) :
  mh_transform SL_theta_inv@{o so} X
    = @id Sets@{o so} (fobj[Powerset_Prop@{o so}] X) := eq_refl.

(* C34: θ*'s structure map against [SL_induced_repack]'s, as functions. *)
Example p468_c34_sl_alg_fun@{o so | Set < o, o < so +}
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}) :
  (fun S => @t_alg _ _ _ _ (`2 (fobj[SL_EM_theta@{o so}] x)) S)
    = (fun S => @t_alg _ _ _ _ (SL_induced_repack@{o so} (`2 x)) S)
  := eq_refl.

(* R15 *)
Example p468_r15_sl_alg@{o so | Set < o, o < so +}
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}) :
  @t_alg _ _ _ _ (`2 (fobj[SL_EM_theta@{o so}] x))
    = @t_alg _ _ _ _ (SL_induced_repack@{o so} (`2 x)) := eq_refl.

(* C62: θ* keeps the carrier. *)
Example p468_c62_sl_carrier@{o so | Set < o, o < so +}
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}) :
  `1 (fobj[SL_EM_theta@{o so}] x) = `1 x := eq_refl.

(* C35: the carrier, the order and the supremum as a function. *)
Example p468_c35_sl_parts@{o so | Set < o, o < so +}
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}) :
  (sl_set (fobj[EM_to_SupLat@{o so} ◯ SL_EM_theta@{o so}] x),
   sl_le (fobj[EM_to_SupLat@{o so} ◯ SL_EM_theta@{o so}] x),
   fun S => sl_sup (fobj[EM_to_SupLat@{o so} ◯ SL_EM_theta@{o so}] x) S)
    = (sl_set (fobj[EM_induced_to_SupLat@{o so}] x),
       sl_le (fobj[EM_induced_to_SupLat@{o so}] x),
       fun S => sl_sup (fobj[EM_induced_to_SupLat@{o so}] x) S) := eq_refl.

(* C36: the underlying map of arrows. *)
Example p468_c36_sl_map@{o so | Set < o, o < so +}
  (x y : @EilenbergMoore@{so so so o} Sets@{o so}
           (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so})
  (f : x ~> y) :
  slh_map (fmap[EM_to_SupLat@{o so} ◯ SL_EM_theta@{o so}] f)
    = slh_map (fmap[EM_induced_to_SupLat@{o so}] f) := eq_refl.

(* R16 *)
Example p468_r16_sl_sup@{o so | Set < o, o < so +}
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}) :
  sl_sup (fobj[EM_to_SupLat@{o so} ◯ SL_EM_theta@{o so}] x)
    = sl_sup (fobj[EM_induced_to_SupLat@{o so}] x) := eq_refl.

(* R17 *)
Fail Example p468_r17_sl_obj@{o so | Set < o, o < so +}
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}) :
  fobj[EM_to_SupLat@{o so} ◯ SL_EM_theta@{o so}] x
    = fobj[EM_induced_to_SupLat@{o so}] x := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Guard: every constant of the six targets, by its full name *)

Check @Category.Monad.Morphism.MonadHom.
Check @Category.Monad.Morphism.Build_MonadHom.
Check @Category.Monad.Morphism.mh_transform.
Check @Category.Monad.Morphism.mh_ret.
Check @Category.Monad.Morphism.mh_join.
Check @Category.Monad.Morphism.mh_join_hcompose.
Check @Category.Monad.Morphism.mh_join_nat.
Check @Category.Monad.Morphism.mh_id.
Check @Category.Monad.Morphism.mh_id_component.
Check @Category.Monad.Morphism.mh_compose.
Check @Category.Monad.Morphism.mh_compose_component.
Check @Category.Monad.Morphism.Monads.
Check @Category.Monad.Morphism.Monads_equiv_is_Fun_equiv.
Check @Category.Monad.Morphism.Monads_Forget.
Check @Category.Monad.Morphism.Monads_Forget_obj.
Check @Category.Monad.Morphism.Monads_Forget_map.
Check @Category.Monad.Morphism.Monads_Forget_comp_component.
Check @Category.Monad.Morphism.Monads_Forget_Faithful.
Check @Category.Monad.Morphism.Algebra.mh_algebra.
Check @Category.Monad.Morphism.Algebra.mh_EM.
Check @Category.Monad.Morphism.Algebra.mh_EM_carrier.
Check @Category.Monad.Morphism.Algebra.mh_EM_alg.
Check @Category.Monad.Morphism.Algebra.mh_EM_hom.
Check @Category.Monad.Morphism.Algebra.mh_EM_forget_obj.
Check @Category.Monad.Morphism.Algebra.mh_EM_forget_obj_fun.
Check @Category.Monad.Morphism.Algebra.mh_EM_forget_map.
Check @Category.Monad.Morphism.Algebra.mh_EM_forget.
Check @Category.Monad.Morphism.Algebra.mh_EM_forget_iso_id.
Check @Category.Monad.Morphism.Algebra.mh_EM_forget_strict.
Check @Category.Monad.Morphism.Algebra.mh_free_component.
Check @Category.Monad.Morphism.Algebra.mh_EM_free.
Check @Category.Monad.Morphism.Algebra.mh_EM_free_forget.
Check @Category.Monad.Morphism.Algebra.mh_EM_free_transpose.
Check @Category.Monad.Morphism.Algebra.talg_same.
Check @Category.Monad.Morphism.Algebra.mh_EM_respects.
Check @Category.Monad.Morphism.Algebra.mh_EM_id.
Check @Category.Monad.Morphism.Algebra.mh_EM_compose.
Check @Category.Monad.Morphism.Algebra.mh_EM_respects_iso_id.
Check @Category.Monad.Morphism.Algebra.mh_EM_id_iso_id.
Check @Category.Monad.Morphism.Algebra.mh_EM_compose_iso_id.
Check @Category.Monad.Morphism.Algebra.Monads_EM.
Check @Category.Monad.Morphism.Algebra.Monads_EM_obj.
Check @Category.Monad.Morphism.Algebra.Monads_EM_map.
Check @Category.Monad.Morphism.Monoid.monad_monoid.
Check @Category.Monad.Morphism.Monoid.monad_monoid_mu.
Check @Category.Monad.Morphism.Monoid.monad_monoid_eta.
Check @Category.Monad.Morphism.Monoid.monoid_monad.
Check @Category.Monad.Morphism.Monoid.monoid_monad_ret.
Check @Category.Monad.Morphism.Monoid.monoid_monad_join.
Check @Category.Monad.Morphism.Monoid.monad_monoid_mu_round.
Check @Category.Monad.Morphism.Monoid.monad_monoid_eta_round.
Check @Category.Monad.Morphism.Monoid.mh_bimap_component.
Check @Category.Monad.Morphism.Monoid.mh_join_is_hom_mu.
Check @Category.Monad.Morphism.Monoid.mh_ret_is_hom_eta.
Check @Category.Monad.Morphism.Monoid.mh_monoidhom.
Check @Category.Monad.Morphism.Monoid.monoidhom_mh.
Check @Category.Monad.Morphism.Monoid.monoidhom_mh_transform.
Check @Category.Monad.Morphism.Monoid.Monads_Mon.
Check @Category.Monad.Morphism.Monoid.Monads_Mon_obj.
Check @Category.Monad.Morphism.Monoid.Monads_Mon_map.
Check @Category.Monad.Morphism.Monoid.Monads_Mon_Faithful.
Check @Category.Monad.Morphism.Monoid.Monads_Mon_Full.
Check @Category.Monad.Morphism.Monoid.Monads_Mon_ESO.
Check @Category.Monad.Morphism.Monoid.Monads_Mon_Equivalence.
Check @Category.Monad.Morphism.Transformer.lift_natural.
Check @Category.Monad.Morphism.Transformer.transformer_hom.
Check @Category.Monad.Morphism.Transformer.transformer_hom_lift.
Check @Category.Monad.Morphism.Transformer.hom_transformer.
Check @Category.Monad.Morphism.Transformer.hom_transformer_lift.
Check @Category.Monad.Morphism.Transformer.transformer_round_trip.
Check @Category.Monad.Morphism.Transformer.hom_round_trip.
Check @Category.Instance.Fun.Action.Monad.BG.Morphism.BG_theta.
Check @Category.Instance.Fun.Action.Monad.BG.Morphism.BG_theta_component.
Check @Category.Instance.Fun.Action.Monad.BG.Morphism.BG_theta_inv.
Check @Category.Instance.Fun.Action.Monad.BG.Morphism.BG_theta_inv_component.
Check @Category.Instance.Fun.Action.Monad.BG.Morphism.BG_theta_iso.
Check @Category.Instance.Fun.Action.Monad.BG.Morphism.BG_theta_EM_carrier.
Check @Category.Instance.Fun.Action.Monad.BG.Morphism.BG_theta_EM_alg_fun.
Check @Category.Instance.Fun.Action.Monad.BG.Morphism.BG_theta_EM_hom.
Check @Category.Instance.Fun.Action.Monad.BG.Morphism.BG_theta_EM.
Check @Category.Instance.Fun.Action.Monad.BG.Morphism.Act_BG_EM.
Check @Category.Instance.Fun.Action.Monad.BG.Morphism.Act_BG_EM_carrier.
Check @Category.Instance.Fun.Action.Monad.BG.Morphism.Act_BG_EM_alg_fun.
Check @Category.Instance.SupLat.Free.Morphism.SL_theta.
Check @Category.Instance.SupLat.Free.Morphism.SL_theta_component.
Check @Category.Instance.SupLat.Free.Morphism.SL_theta_alg_fun.
Check @Category.Instance.SupLat.Free.Morphism.SL_theta_inv.
Check @Category.Instance.SupLat.Free.Morphism.SL_theta_inv_component.
Check @Category.Instance.SupLat.Free.Morphism.SL_theta_iso.
Check @Category.Instance.SupLat.Free.Morphism.SL_EM_theta.
Check @Category.Instance.SupLat.Free.Morphism.SL_EM_theta_carrier.
Check @Category.Instance.SupLat.Free.Morphism.SL_EM_theta_alg_fun.
Check @Category.Instance.SupLat.Free.Morphism.SL_factor_set.
Check @Category.Instance.SupLat.Free.Morphism.SL_factor_le.
Check @Category.Instance.SupLat.Free.Morphism.SL_factor_sup_fun.
Check @Category.Instance.SupLat.Free.Morphism.SL_factor_map.
Check @Category.Instance.SupLat.Free.Morphism.SL_factor.

(* ------------------------------------------------------------------------ *)
(** ** The route through Monad/Monoid.v, measured and not taken *)

(* CORRECTION (#1348): taken since #1348; C40 now restates [monad_monoid]'s
   own body. *)

(* Loaded here, after every other command, so that the two modules below
   change the environment of this control alone. *)
Require Import Category.Monad.Monoid.
Require Import Category.Theory.Algebra.Monoid.Product.

(* C40: that route's μ and η are [monad_monoid]'s, and its round trip
   keeps [ret]. *)
Example p468_c40_monoid_route@{o h f s + | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T : C ⟶ C} (M : @Monad C T) (x : C) :
  (transform[@mu _ _ _
     (@Monoid_of_MonoidObject _ (@Compose_Monoidal@{s f o h} C) T
        (snd (@Monoid_Monad C T) M))] x,
   transform[@eta _ _ _
     (@Monoid_of_MonoidObject _ (@Compose_Monoidal@{s f o h} C) T
        (snd (@Monoid_Monad C T) M))] x,
   @ret C T (fst (@Monoid_Monad C T)
     (@MonoidObject_of_Monoid _ (@Compose_Monoidal@{s f o h} C) T
        (@Monoid_of_MonoidObject _ (@Compose_Monoidal@{s f o h} C) T
           (snd (@Monoid_Monad C T) M)))) x)
    = (transform[@mu _ _ _ (monad_monoid@{o h f s} M)] x,
       transform[@eta _ _ _ (monad_monoid@{o h f s} M)] x,
       @ret C T M x) := eq_refl.
