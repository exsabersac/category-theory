Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Instance.Adjoints.
Require Import Category.Adjunction.Compose.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.

Generalizable All Variables.

(*
    nLab:      https://ncatlab.org/nlab/show/monadic+adjunction
    Wikipedia: https://en.wikipedia.org/wiki/Beck%27s_monadicity_theorem

   本文件给出例子。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section IdentityMonadic.

Context {C : Category}.

Local Notation A  := (@Adjunction_Id C).
Local Notation T  := (Id[C] ◯ Id[C]).
Local Notation HM := (Adjunction_Induced_Monad A).
Local Notation EM := (@EilenbergMoore C T HM).
Local Notation K  := (EM_Comparison A).
Local Notation UT := (@EM_Forget C T HM).

(** Every algebra for the identity monad has identity structure map: the
    unit of the induced monad is the unit of [Adjunction_Id], which is the
    identity ([adj_id_unit]), so the algebra unit law ν ∘ η ≈ id collapses
    to ν ≈ id. *)

Lemma identity_alg_id {a : C} (ν : @TAlgebra C T HM a) :
  t_alg[ν] ≈ id[a].
Proof.
  assert (Hret : @ret C T HM a ≈ id[a]) by reflexivity.
  rewrite <- (@t_id C T HM a ν), Hret.
  now rewrite id_right.
Qed.

(** Consequently every C-arrow intertwines any two identity-monad algebra
    structures: both structure maps are identities, and fmap[T] is the
    identity on morphisms. *)

Lemma identity_alg_hom_commutes {a b : C}
  (ν : @TAlgebra C T HM a) (ρ : @TAlgebra C T HM b) (f : a ~{C}~> b) :
  f ∘ t_alg[ν] ≈ t_alg[ρ] ∘ fmap[T] f.
Proof.
  rewrite (identity_alg_id ν), (identity_alg_id ρ).
  rewrite id_left, id_right.
  reflexivity.
Qed.

(** The counit isomorphism K (U^T (a, ν)) ≅ (a, ν) of the equivalence: in
    both directions the underlying arrow is the identity of the carrier,
    which is a homomorphism by the previous lemma. *)

Definition identity_counit_to (X : EM) :
  fobj[K ◯ UT] X ~{EM}~> X :=
  @Build_TAlgebraHom C T HM (Id[C] (`1 X)) (`1 X)
    (EM_Comparison_Algebra A (`1 X)) (`2 X)
    id
    (identity_alg_hom_commutes (EM_Comparison_Algebra A (`1 X)) (`2 X) id).

Definition identity_counit_from (X : EM) :
  X ~{EM}~> fobj[K ◯ UT] X :=
  @Build_TAlgebraHom C T HM (`1 X) (Id[C] (`1 X))
    (`2 X) (EM_Comparison_Algebra A (`1 X))
    id
    (identity_alg_hom_commutes (`2 X) (EM_Comparison_Algebra A (`1 X)) id).

Lemma identity_counit_to_from (X : EM) :
  identity_counit_to X ∘ identity_counit_from X ≈ id.
Proof.
  cbn.
  now rewrite id_left.
Qed.

Lemma identity_counit_from_to (X : EM) :
  identity_counit_from X ∘ identity_counit_to X ≈ id.
Proof.
  cbn.
  now rewrite id_left.
Qed.

Definition identity_counit_iso (X : EM) :
  @Isomorphism EM (fobj[K ◯ UT] X) X :=
  @Build_Isomorphism EM (fobj[K ◯ UT] X) X
    (identity_counit_to X) (identity_counit_from X)
    (identity_counit_to_from X) (identity_counit_from_to X).

(** The counit cell of the equivalence: comparing after forgetting is the
    identity of C^T.  Naturality holds on underlying arrows, where all the
    iso components are identities. *)

Theorem identity_equivalence_counit : K ◯ UT ≈ Id[EM].
Proof.
  exists identity_counit_iso.
  intros X Y f; cbn.
  cat.
Qed.

(** The unit cell: forgetting after comparing is U = Id[C] on the nose —
    this is [EM_Comparison_Forget] at the identity adjunction, read
    backwards. *)

Theorem identity_equivalence_unit : Id[C] ≈ UT ◯ K.
Proof.
  symmetry.
  exact (EM_Comparison_Forget A).
Qed.

(** The identity-monad witness: the Eilenberg–Moore comparison functor of
    the identity adjunction is an equivalence of categories, quasi-inverse
    the forgetful functor. *)

Definition identity_monadic : EquivalenceOfCategories K :=
  @Build_EquivalenceOfCategories C EM K UT
    identity_equivalence_counit
    identity_equivalence_unit.

End IdentityMonadic.

(** Packaged in the vocabulary of Monad/Comparison.v: the identity functor
    is monadic. *)

Definition Identity_Monadic {C : Category} : Monadic Id[C] :=
  (Id[C]; (Adjunction_Id; identity_monadic)).
