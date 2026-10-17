Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Monad.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Compose.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Instance.Fun.
Require Category.Theory.Algebra.Monoid.Product.
Require Category.Monad.Monoid.
Require Import Category.Monad.Morphism.

Generalizable All Variables.

(* * * The 范畴 单子 Mac Lane's Mon_{C^C} （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/monoid+in+a+monoidal+category
   nLab: https://ncatlab.org/nlab/show/monad (section "The 2-category of

   本文件给出幺半范畴中的幺半群对象：乘法 μ、单位 η，以及结合律与左右单位律（插入结合子/单位子使态射可复合）。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* * ** Objects: 单子 幺半群 ⟨[C, C], ◯, Id⟩ （已译） *)

Definition monad_monoid@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T : C ⟶ C} (M : @Monad C T) :
  @Monoid (@Fun@{o h o h f f s} C C) (@Compose_Monoidal@{s f o h} C) T :=
  Category.Theory.Algebra.Monoid.Product.Monoid_of_MonoidObject
    (snd (@Category.Monad.Monoid.Monoid_Monad@{o h s f} C T) M).

Example monad_monoid_mu@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T : C ⟶ C} (M : @Monad C T) (x : C) :
  transform[@mu _ _ _ (monad_monoid@{o h f s} M)] x = @join C T M x
  := eq_refl.

Example monad_monoid_eta@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T : C ⟶ C} (M : @Monad C T) (x : C) :
  transform[@eta _ _ _ (monad_monoid@{o h f s} M)] x = @ret C T M x
  := eq_refl.

Definition monoid_monad@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T : C ⟶ C}
  (N : @Monoid (@Fun@{o h o h f f s} C C) (@Compose_Monoidal@{s f o h} C) T) :
  @Monad C T :=
  fst (@Category.Monad.Monoid.Monoid_Monad@{o h s f} C T)
    (Category.Theory.Algebra.Monoid.Product.MonoidObject_of_Monoid N).

(* 相关说明。 （已译） *)

Example monoid_monad_ret@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T : C ⟶ C} (M : @Monad C T) (x : C) :
  @ret C T (monoid_monad@{o h f s} (monad_monoid@{o h f s} M)) x
    = @ret C T M x := eq_refl.

Example monoid_monad_join@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T : C ⟶ C} (M : @Monad C T) (x : C) :
  @join C T (monoid_monad@{o h f s} (monad_monoid@{o h f s} M)) x
    = @join C T M x := eq_refl.

Example monad_monoid_mu_round@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T : C ⟶ C}
  (N : @Monoid (@Fun@{o h o h f f s} C C) (@Compose_Monoidal@{s f o h} C) T)
  (x : C) :
  transform[@mu _ _ _ (monad_monoid@{o h f s} (monoid_monad@{o h f s} N))] x
    = transform[@mu _ _ _ N] x := eq_refl.

Example monad_monoid_eta_round@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T : C ⟶ C}
  (N : @Monoid (@Fun@{o h o h f f s} C C) (@Compose_Monoidal@{s f o h} C) T)
  (x : C) :
  transform[@eta _ _ _ (monad_monoid@{o h f s} (monoid_monad@{o h f s} N))] x
    = transform[@eta _ _ _ N] x := eq_refl.

(* 相关说明。 （已译） *)

(* The tensor of Compose_Monoidal on (θ, θ), at x. *)

Example mh_bimap_component@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M') (x : C) :
  transform[@bimap _ _ _ (@tensor _ (@Compose_Monoidal@{s f o h} C))
              _ _ _ _ (mh_transform θ) (mh_transform θ)] x
    = mh_transform θ (T' x) ∘ fmap[T] (mh_transform θ x) := eq_refl.

(* The type [mh_join], quantified over x, IS type the
 multiplication square 幺半群 homomorphism. （已译） *)

Example mh_join_is_hom_mu@{o h f s q |
  h < s, o <= f, h <= f, o < q, h < q, f <= q +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M') :
  @eq Type@{q}
    (∀ x : C, mh_transform θ x ∘ @join C T M x
                ≈ @join C T' M' x
                    ∘ (mh_transform θ (T' x) ∘ fmap[T] (mh_transform θ x)))
    (@compose (@Fun@{o h o h f f s} C C) _ _ _
       (mh_transform θ) (@mu _ _ _ (monad_monoid@{o h f s} M))
     ≈ @compose (@Fun@{o h o h f f s} C C) _ _ _
         (@mu _ _ _ (monad_monoid@{o h f s} M'))
         (@bimap _ _ _ (@tensor _ (@Compose_Monoidal@{s f o h} C))
            _ _ _ _ (mh_transform θ) (mh_transform θ))) := eq_refl.

Example mh_ret_is_hom_eta@{o h f s q |
  h < s, o <= f, h <= f, o < q, h < q, f <= q +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M') :
  @eq Type@{q} (∀ x : C, mh_transform θ x ∘ @ret C T M x ≈ @ret C T' M' x)
  (@compose (@Fun@{o h o h f f s} C C) _ _ _
       (mh_transform θ) (@eta _ _ _ (monad_monoid@{o h f s} M))
     ≈ @eta _ _ _ (monad_monoid@{o h f s} M')) := eq_refl.

Definition mh_monoidhom@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M') :
  @MonoidHom (@Fun@{o h o h f f s} C C) (@Compose_Monoidal@{s f o h} C)
    T T' (monad_monoid@{o h f s} M) (monad_monoid@{o h f s} M')
    (mh_transform θ).
Proof.
  constructor.
  - intros x. exact (mh_join θ).
  - intros x. exact (mh_ret θ).
Defined.

Definition monoidhom_mh@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : T ⟹ T')
  (H : @MonoidHom (@Fun@{o h o h f f s} C C) (@Compose_Monoidal@{s f o h} C)
         T T' (monad_monoid@{o h f s} M) (monad_monoid@{o h f s} M') θ) :
  MonadHom@{o h} M M'.
Proof.
  unshelve refine (@Build_MonadHom C T T' M M' θ _ _).
  - intros x. exact (@hom_eta _ _ _ _ _ _ _ H x).
  - intros x. exact (@hom_mu _ _ _ _ _ _ _ H x).
Defined.

Example monoidhom_mh_transform@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : T ⟹ T')
  (H : @MonoidHom (@Fun@{o h o h f f s} C C) (@Compose_Monoidal@{s f o h} C)
         T T' (monad_monoid@{o h f s} M) (monad_monoid@{o h f s} M') θ) :
  mh_transform (monoidhom_mh@{o h f s} θ H) = θ := eq_refl.

(* * ** The 函子 Monads C ⟶ Mon [C, C] （已译） *)

Definition Monads_Mon@{o h m1 m2 f s mo t |
  h < s, f < t, o <= m1, h <= m1, o <= m2, h <= m2, m2 <= f,
  o <= f, h <= f, f <= mo +}
  (C : Category@{o h h}) :
  Monads@{o h m1 m2} C
    ⟶ @Mon@{f f mo t} (@Fun@{o h o h f f s} C C)
        (@Compose_Monoidal@{s f o h} C).
Proof.
  unshelve refine
    (@Build_Functor (Monads@{o h m1 m2} C)
       (@Mon@{f f mo t} (@Fun@{o h o h f f s} C C)
          (@Compose_Monoidal@{s f o h} C))
       (fun N : { T : C ⟶ C & @Monad C T } =>
          (projT1 N; monad_monoid@{o h f s} (projT2 N)))
       (fun N N' (θ : MonadHom@{o h} (projT2 N) (projT2 N')) =>
          (mh_transform θ; mh_monoidhom@{o h f s} θ)) _ _ _).
  - intros N N' θ θ' E. exact E.
  - intros N x. simpl. symmetry. apply fmap_id.
  - intros N N' N'' φ θ x. simpl. reflexivity.
Defined.

Example Monads_Mon_obj@{o h m1 m2 f s mo t |
  h < s, f < t, o <= m1, h <= m1, o <= m2, h <= m2, m2 <= f,
  o <= f, h <= f, f <= mo +}
  (C : Category@{o h h}) (N : Monads@{o h m1 m2} C) :
  fobj[Monads_Mon@{o h m1 m2 f s mo t} C] N
    = (projT1 N; monad_monoid@{o h f s} (projT2 N)) := eq_refl.

Example Monads_Mon_map@{o h m1 m2 f s mo t |
  h < s, f < t, o <= m1, h <= m1, o <= m2, h <= m2, m2 <= f,
  o <= f, h <= f, f <= mo +}
  (C : Category@{o h h}) (N N' : Monads@{o h m1 m2} C)
  (θ : N ~{Monads@{o h m1 m2} C}~> N') :
  fmap[Monads_Mon@{o h m1 m2 f s mo t} C] θ
    = (mh_transform θ; mh_monoidhom@{o h f s} θ) := eq_refl.

Definition Monads_Mon_Faithful@{o h m1 f s mo t |
  h < s, f < t, o <= m1, h <= m1, o <= f, h <= f, f <= mo +}
  (C : Category@{o h h}) :
  Faithful (Monads_Mon@{o h m1 f f s mo t} C).
Proof. constructor. intros N N' θ θ' E. exact E. Defined.

Definition Monads_Mon_Full@{o h m1 f s mo t |
  h < s, f < t, o <= m1, h <= m1, o <= f, h <= f, f <= mo +}
  (C : Category@{o h h}) :
  Full (Monads_Mon@{o h m1 f f s mo t} C).
Proof.
  unshelve refine (@Build_Full _ _ (Monads_Mon@{o h m1 f f s mo t} C) _ _).
  - intros N N' g. exact (monoidhom_mh@{o h f s} (projT1 g) (projT2 g)).
  - intros N N' g x. simpl. reflexivity.
Defined.

(* Every 幺半群 ⟨[C, C], ◯, Id⟩ is, up 同构 with
 恒等 components, image 单子 it defines. （已译） *)

Definition Monads_Mon_ESO@{o h m1 f s mo t |
  h < s, f < t, o <= m1, h <= m1, o <= f, h <= f, f <= mo +}
  (C : Category@{o h h}) :
  EssentiallySurjective (Monads_Mon@{o h m1 f f s mo t} C).
Proof.
  unshelve refine
    (@Build_EssentiallySurjective _ _ (Monads_Mon@{o h m1 f f s mo t} C)
       (fun P => (projT1 P; monoid_monad@{o h f s} (projT2 P))) _).
  intros P.
  unshelve refine (@Build_Isomorphism _ _ _ _ _ _ _).
  - exists (mh_transform (mh_id (monoid_monad@{o h f s} (projT2 P)))).
    constructor.
    + intros x; simpl.
      etransitivity; [ apply id_left | ].
      symmetry.
      etransitivity; [ | apply id_right ].
      apply compose_respects; [ reflexivity | ].
      etransitivity; [ apply id_left | apply fmap_id ].
    + intros x; simpl. apply id_left.
  - exists (mh_transform (mh_id (monoid_monad@{o h f s} (projT2 P)))).
    constructor.
    + intros x; simpl.
      etransitivity; [ apply id_left | ].
      symmetry.
      etransitivity; [ | apply id_right ].
      apply compose_respects; [ reflexivity | ].
      etransitivity; [ apply id_left | apply fmap_id ].
    + intros x; simpl. apply id_left.
  - intros x; simpl.
    etransitivity; [ apply id_left | ].
    symmetry. apply fmap_id.
  - intros x; simpl.
    etransitivity; [ apply id_left | ].
    symmetry. apply fmap_id.
Defined.

Definition Monads_Mon_Equivalence@{o h m1 f s mo t e |
  h < s, f < t, o <= m1, h <= m1, o <= f, h <= f, f <= mo,
  m1 <= e, f <= e +}
  (C : Category@{o h h}) :
  EquivalenceOfCategories@{mo t e m1 mo f}
    (Monads_Mon@{o h m1 f f s mo t} C) :=
  @FF_ESO_Equivalence@{mo t e m1 mo f} _ _ (Monads_Mon@{o h m1 f f s mo t} C)
    (Monads_Mon_Full@{o h m1 f s mo t} C)
    (Monads_Mon_Faithful@{o h m1 f s mo t} C)
    (Monads_Mon_ESO@{o h m1 f s mo t} C).
