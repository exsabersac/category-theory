Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Construction.Product.
Require Import Category.Functor.Construction.Product.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(** Monoidal functors. *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_functor

   本文件给出幺半相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section MonoidalFunctor.

Context {C : Category}.
Context {D : Category}.
Context `{@Monoidal C}.
Context `{@Monoidal D}.
Context {F : C ⟶ D}.

Lemma ap_iso_to_from
      (ap_functor_iso : (⨂) ◯ F ∏⟶ F ≅[[C ∏ C, D]] F ◯ (⨂)) {x y} :
  transform (to ap_functor_iso) (x, y)
    ∘ transform (from ap_functor_iso) (x, y) ≈ id[F (x ⨂ y)].
Proof.
  spose (iso_to_from ap_functor_iso (x, y)) as X.
  rewrite !fmap_id in X.
  apply X.
Qed.

Lemma ap_iso_from_to
      (ap_functor_iso : (⨂) ◯ F ∏⟶ F ≅[[C ∏ C, D]] F ◯ (⨂)) {x y} :
  transform (from ap_functor_iso) (x, y) ∘ transform (to ap_functor_iso) (x, y)
    ≈ id[((⨂) ◯ F ∏⟶ F) (x, y)].
Proof.
  spose (iso_from_to ap_functor_iso (x, y)) as X.
  rewrite !fmap_id in X.
  apply X.
Qed.

Class MonoidalFunctor := {
  pure_iso : I ≅ F I;             (* unit comparison η, invertible *)

  (* tensor comparison μ as a natural isomorphism (⨂) ◯ F ∏⟶ F ≅ F ◯ (⨂) *)
  ap_functor_iso : (⨂) ◯ F ∏⟶ F ≅[[C ∏ C, D]] F ◯ (⨂);

  (* the component F x ⨂ F y ≅ F (x ⨂ y) of the tensor comparison *)
  ap_iso {x y} : F x ⨂ F y ≅ F (x ⨂ y) := {|
    to   := transform[to ap_functor_iso] (x, y);
    from := transform[from ap_functor_iso] (x, y);
    iso_to_from := @ap_iso_to_from ap_functor_iso x y;
    iso_from_to := @ap_iso_from_to ap_functor_iso x y
  |};

  pure_iso_left {x}  : I ⨂ F x ≅ F (I ⨂ x);  (* derived iso for left unitality *)
  pure_iso_right {x} : F x ⨂ I ≅ F (x ⨂ I);  (* derived iso for right unitality *)

  (* derived iso for the associativity coherence square *)
  ap_iso_assoc {x y z} : (F x ⨂ F y) ⨂ F z ≅ F (x ⨂ (y ⨂ z));

  monoidal_unit_left {x} :         (* left unitality: λ vs. μ and η *)
    to unit_left
       ≈ fmap[F] (to unit_left) ∘ to ap_iso ∘ bimap (to pure_iso) (id[F x]);

  monoidal_unit_right {x} :        (* right unitality: ρ vs. μ and η *)
    to unit_right
       ≈ fmap[F] (to unit_right) ∘ to ap_iso ∘ bimap (id[F x]) (to pure_iso);

  monoidal_assoc {x y z} :         (* associativity: α vs. two μ's *)
    fmap[F] (to (@tensor_assoc _ _ x y z)) ∘ to ap_iso ∘ bimap (to ap_iso) id
      ≈ to ap_iso ∘ bimap id (to ap_iso) ∘ to tensor_assoc
}.

Class LaxMonoidalFunctor := {
  lax_pure : I ~> F I;             (* unit comparison η : I → F I *)

  (* tensor comparison μ as a natural transformation (⨂) ◯ F ∏⟶ F ⟹ F ◯ (⨂) *)
  ap_functor_nat : ((⨂) ◯ F ∏⟶ F) ~{[C ∏ C, D]}~> (F ◯ (⨂));

  (* the component μ_{x,y} : F x ⨂ F y → F (x ⨂ y) of the tensor comparison *)
  lax_ap {x y} : F x ⨂ F y ~> F (x ⨂ y) := transform[ap_functor_nat] (x, y);

  pure_left {x}  : I ⨂ F x ≅ F (I ⨂ x);  (* derived iso for left unitality *)
  pure_right {x} : F x ⨂ I ≅ F (x ⨂ I);  (* derived iso for right unitality *)

  (* derived iso for the associativity coherence square *)
  ap_assoc {x y z} : (F x ⨂ F y) ⨂ F z ≅ F (x ⨂ (y ⨂ z));

  lax_monoidal_unit_left {x} :     (* left unitality: λ vs. μ and η *)
    to unit_left
       ≈ fmap[F] (to unit_left) ∘ lax_ap ∘ bimap lax_pure (id[F x]);

  lax_monoidal_unit_right {x} :    (* right unitality: ρ vs. μ and η *)
    to unit_right
       ≈ fmap[F] (to unit_right) ∘ lax_ap ∘ bimap (id[F x]) lax_pure;

  lax_monoidal_assoc {x y z} :     (* associativity: α vs. two μ's *)
    fmap[F] (to (@tensor_assoc _ _ x y z)) ∘ lax_ap ∘ bimap lax_ap id
      ≈ lax_ap ∘ bimap id lax_ap ∘ to tensor_assoc
}.

Program Definition MonoidalFunctor_Is_Lax (S : MonoidalFunctor) :
  LaxMonoidalFunctor := {|
  lax_pure := to (@pure_iso S);
  ap_functor_nat := to (@ap_functor_iso S)
|}.
Next Obligation. apply pure_iso_left. Qed.
Next Obligation. apply pure_iso_right. Qed.
Next Obligation. apply ap_iso_assoc. Qed.
Next Obligation. apply monoidal_unit_left. Qed.
Next Obligation. apply monoidal_unit_right. Qed.
Next Obligation. apply monoidal_assoc. Qed.

End MonoidalFunctor.

Notation "ap_iso[ F ]" := (@ap_iso _ _ _ _ F%functor _ _ _)
  (at level 9, format "ap_iso[ F ]").
Notation "ap_functor_iso[ F ]" := (@ap_functor_iso _ _ _ _ _ F%functor)
  (at level 9, format "ap_functor_iso[ F ]") : morphism_scope.

Notation "lax_pure[ F ]" := (@lax_pure _ _ _ _ F%functor _)
  (at level 9, format "lax_pure[ F ]") : morphism_scope.
Notation "lax_ap[ F ]" := (@lax_ap _ _ _ _ F%functor _ _ _)
  (at level 9, format "lax_ap[ F ]").
Notation "ap_functor_nat[ F ]" := (@ap_functor_nat _ _ _ _ _ F%functor)
  (at level 9, format "ap_functor_nat[ F ]") : morphism_scope.

Arguments LaxMonoidalFunctor {C D _ _} F.
Arguments MonoidalFunctor {C D _ _} F.
