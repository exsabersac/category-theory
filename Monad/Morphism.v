Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Monad.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(** * Morphisms of monads, and the category of monads on C *)

(*
   nLab: https://ncatlab.org/nlab/show/monad (section "The 2-category of
   Paper: Eilenberg, Moore, "Adjoint functors and triples", Illinois
   Paper: Street, "The formal theory of monads", Journal of Pure and

   本文件给出单子相关定义或实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Morphisms of monads *)

(* A transformation T ⟹ T' preserving the unit (Mac Lane's fη = η') and
   the multiplication (his fμ = μ'(f □ f)), the horizontal composite
   f □ f written in [nat_hcompose]'s form at x. *)

Class MonadHom@{o h | } {C : Category@{o h h}} {T T' : C ⟶ C}
      (M : @Monad C T) (M' : @Monad C T') := {
  mh_transform : T ⟹ T';
  mh_ret {x : C} : mh_transform x ∘ @ret C T M x ≈ @ret C T' M' x;
  mh_join {x : C} :
    mh_transform x ∘ @join C T M x
      ≈ @join C T' M' x ∘ (mh_transform (T' x) ∘ fmap[T] (mh_transform x))
}.

Arguments mh_transform {C T T' M M'} _.
Arguments mh_ret {C T T' M M'} _ {x}.
Arguments mh_join {C T T' M M'} _ {x}.

(* The right factor of [mh_join] is the horizontal composite θθ. *)

Example mh_join_hcompose@{o h s | h < s +} {C : Category@{o h h}}
  {T T' : C ⟶ C} {M : @Monad C T} {M' : @Monad C T'}
  (θ : MonadHom@{o h} M M') (x : C) :
  transform[nat_hcompose@{s o o o h} (mh_transform θ) (mh_transform θ)] x
    = mh_transform θ (T' x) ∘ fmap[T] (mh_transform θ x) := eq_refl.

(* The other form of θθ, T'(θ_x) ∘ θ_{Tx}, by naturality of θ. *)

Lemma mh_join_nat@{o h | } {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M') (x : C) :
  mh_transform θ x ∘ @join C T M x
    ≈ @join C T' M' x ∘ (fmap[T'] (mh_transform θ x) ∘ mh_transform θ (T x)).
Proof.
  etransitivity; [ apply (mh_join θ) | ].
  apply compose_respects; [ reflexivity | ].
  symmetry. apply (naturality (mh_transform θ)).
Qed.

(* Identity and composite.  The proofs are chains of [etransitivity],
   [compose_respects] and the associativity laws, with no setoid
   [rewrite], which would add a universe (see UNIVERSES above). *)

Definition mh_id@{o h | } {C : Category@{o h h}} {T : C ⟶ C}
  (M : @Monad C T) : MonadHom@{o h} M M.
Proof.
  unshelve refine {| mh_transform := Build_Transform'@{o h h o h h}
                       (F:=T) (G:=T) (fun x => id) _ |}.
  - intros x y f.
    transitivity (fmap[T] f); [ apply id_right | symmetry; apply id_left ].
  - intros x; cbn. apply id_left.
  - intros x; cbn.
    transitivity (@join C T M x); [ apply id_left | ].
    symmetry.
    transitivity (@join C T M x ∘ id); [ | apply id_right ].
    apply compose_respects; [ reflexivity | ].
    transitivity (fmap[T] (@id C (T x))); [ apply id_left | apply fmap_id ].
Defined.

Example mh_id_component@{o h | +} {C : Category@{o h h}} {T : C ⟶ C}
  (M : @Monad C T) (x : C) :
  mh_transform (mh_id@{o h} M) x = id := eq_refl.

Definition mh_compose@{o h | } {C : Category@{o h h}} {T T' T'' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} {M'' : @Monad C T''}
  (φ : MonadHom@{o h} M' M'') (θ : MonadHom@{o h} M M') :
  MonadHom@{o h} M M''.
Proof.
  unshelve refine {| mh_transform := Build_Transform'@{o h h o h h}
                       (F:=T) (G:=T'')
                       (fun x => mh_transform φ x ∘ mh_transform θ x) _ |}.
  - intros x y f; cbn.
    etransitivity; [ apply comp_assoc | ].
    etransitivity;
      [ apply compose_respects;
          [ apply (naturality (mh_transform φ)) | reflexivity ] | ].
    etransitivity; [ apply comp_assoc_sym | ].
    etransitivity;
      [ apply compose_respects;
          [ reflexivity | apply (naturality (mh_transform θ)) ] | ].
    apply comp_assoc.
  - intros x; cbn.
    etransitivity; [ apply comp_assoc_sym | ].
    etransitivity;
      [ apply compose_respects; [ reflexivity | apply (mh_ret θ) ] | ].
    apply (mh_ret φ).
  - intros x; cbn.
    etransitivity; [ apply comp_assoc_sym | ].
    etransitivity;
      [ apply compose_respects; [ reflexivity | apply (mh_join θ) ] | ].
    etransitivity; [ apply comp_assoc | ].
    etransitivity;
      [ apply compose_respects; [ apply (mh_join φ) | reflexivity ] | ].
    etransitivity; [ apply comp_assoc_sym | ].
    apply compose_respects; [ reflexivity | ].
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
    etransitivity;
      [ apply compose_respects;
          [ reflexivity
          | apply compose_respects;
              [ reflexivity | symmetry; apply fmap_comp ] ] | ].
    apply comp_assoc.
Defined.

Example mh_compose_component@{o h | +} {C : Category@{o h h}}
  {T T' T'' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} {M'' : @Monad C T''}
  (φ : MonadHom@{o h} M' M'') (θ : MonadHom@{o h} M M') (x : C) :
  mh_transform (mh_compose@{o h} φ θ) x
    = mh_transform φ x ∘ mh_transform θ x := eq_refl.

(** ** The category of monads on C *)

(* Objects are monads, arrows are morphisms of monads, and ≈ compares
   components, as the ≈ of [C, C] does. *)

Definition Monads@{o h m1 m2 | o <= m1, h <= m1, o <= m2, h <= m2 +}
  (C : Category@{o h h}) : Category@{m1 m2 m2}.
Proof.
  unshelve refine
    {| obj := { T : C ⟶ C & @Monad C T }
     ; hom := fun M N => MonadHom@{o h} (projT2 M) (projT2 N)
     ; homset := fun M N =>
         {| equiv := fun θ φ => ∀ x : C,
              @equiv _ (@homset C _ _) (mh_transform θ x) (mh_transform φ x) |}
     ; id := fun M => mh_id (projT2 M)
     ; compose := fun M N P φ θ => mh_compose φ θ |}.
  - constructor.
    + intros θ x. reflexivity.
    + intros θ φ E x. symmetry. apply E.
    + intros θ φ ψ E F x.
      transitivity (mh_transform φ x); [ apply E | apply F ].
  - intros M N P φ φ' Eφ θ θ' Eθ x; cbn.
    apply compose_respects; [ exact (Eφ x) | exact (Eθ x) ].
  - intros M N θ x; cbn. apply id_left.
  - intros M N θ x; cbn. apply id_right.
  - intros M N P Q f g k x; cbn. apply comp_assoc.
  - intros M N P Q f g k x; cbn. apply comp_assoc_sym.
Defined.

Example Monads_equiv_is_Fun_equiv@{o h m1 m2 u |
  h < u, o <= m1, h <= m1, o <= m2, h <= m2 +}
  (C : Category@{o h h}) (N N' : Monads@{o h m1 m2} C)
  (θ φ : N ~{Monads@{o h m1 m2} C}~> N') :
  @equiv _ (@homset (Monads@{o h m1 m2} C) N N') θ φ
    = @equiv _ (@homset (@Fun@{o h o h m1 m2 u} C C) (projT1 N) (projT1 N'))
        (mh_transform θ) (mh_transform φ) := eq_refl.

(** ** The forgetful functor into [C, C] *)

Definition Monads_Forget@{o h m1 m2 u |
  h < u, o <= m1, h <= m1, o <= m2, h <= m2 +} (C : Category@{o h h}) :
  Monads@{o h m1 m2} C ⟶ @Fun@{o h o h m1 m2 u} C C.
Proof.
  unshelve refine
    (@Build_Functor (Monads@{o h m1 m2} C) (@Fun@{o h o h m1 m2 u} C C)
       (fun N : { T : C ⟶ C & @Monad C T } => projT1 N)
       (fun N N' θ => mh_transform θ) _ _ _).
  - intros N N' θ θ' E. exact E.
  - intros N x. simpl. symmetry. apply fmap_id.
  - intros N N' N'' φ θ x. simpl. reflexivity.
Defined.

Example Monads_Forget_obj@{o h m1 m2 u |
  h < u, o <= m1, h <= m1, o <= m2, h <= m2 +} (C : Category@{o h h})
  (N : Monads@{o h m1 m2} C) :
  fobj[Monads_Forget@{o h m1 m2 u} C] N = projT1 N := eq_refl.

Example Monads_Forget_map@{o h m1 m2 u |
  h < u, o <= m1, h <= m1, o <= m2, h <= m2 +} (C : Category@{o h h})
  (N N' : Monads@{o h m1 m2} C) (θ : N ~{Monads@{o h m1 m2} C}~> N') :
  fmap[Monads_Forget@{o h m1 m2 u} C] θ = mh_transform θ := eq_refl.

(* The composition law at a component: both sides are φ_x ∘ θ_x. *)

Example Monads_Forget_comp_component@{o h m1 m2 u |
  h < u, o <= m1, h <= m1, o <= m2, h <= m2 +} (C : Category@{o h h})
  (N N' N'' : Monads@{o h m1 m2} C)
  (φ : N' ~{Monads@{o h m1 m2} C}~> N'')
  (θ : N ~{Monads@{o h m1 m2} C}~> N') (x : C) :
  transform[fmap[Monads_Forget@{o h m1 m2 u} C] (φ ∘ θ)] x
    = transform[fmap[Monads_Forget@{o h m1 m2 u} C] φ
                ∘ fmap[Monads_Forget@{o h m1 m2 u} C] θ] x := eq_refl.

(* Faithful by conversion: the hypothesis is already the conclusion. *)

Definition Monads_Forget_Faithful@{o h m1 m2 u |
  h < u, o <= m1, h <= m1, o <= m2, h <= m2 +} (C : Category@{o h h}) :
  Faithful (Monads_Forget@{o h m1 m2 u} C).
Proof. constructor. intros N N' θ θ' E. exact E. Defined.
