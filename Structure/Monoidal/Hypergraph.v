Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Braided.Proofs.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.Frobenius.
Require Import Category.Theory.Algebra.CommutativeFrobenius.
Require Import Category.Theory.Algebra.SpecialCommutativeFrobenius.

Generalizable All Variables.

(*
    nLab:      https://ncatlab.org/nlab/show/hypergraph+category
    Wikipedia: no dedicated article (the underlying special commutative
    Reference: Fong & Spivak, "Hypergraph Categories",

   本文件给出幺半相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Hypergraph.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

(* * The "middle two factors" swap [(X⨂Y) ⨂ (X⨂Y) ≅ (X⨂X) ⨂ (Y⨂Y)],
    built by re-associating, braiding the middle pair, then re-associating
    back.  Concretely, the chain is

      (X⨂Y) ⨂ (X⨂Y)
        =α=> X ⨂ (Y ⨂ (X⨂Y))
        =id⨂α⁻¹=> X ⨂ ((Y⨂X) ⨂ Y)
        =id⨂(braid⨂id)=> X ⨂ ((X⨂Y) ⨂ Y)
        =id⨂α=> X ⨂ (X ⨂ (Y⨂Y))
        =α⁻¹=> (X⨂X) ⨂ (Y⨂Y).（标题）（已译） *)
Definition mid_swap (X Y : C) :
  (X ⨂ Y) ⨂ (X ⨂ Y) ~> (X ⨂ X) ⨂ (Y ⨂ Y) :=
  (@tensor_assoc C _ X X (Y ⨂ Y))⁻¹
    ∘ bimap id[X] (to (@tensor_assoc C _ X Y Y))
    ∘ bimap id[X] (bimap (@braid C _ Y X) id[Y])
    ∘ bimap id[X] ((@tensor_assoc C _ Y X Y)⁻¹)
    ∘ to (@tensor_assoc C _ X Y (X ⨂ Y)).

(** Inverse direction, used in the canonical [delta]. *)
Definition mid_swap_inv (X Y : C) :
  (X ⨂ X) ⨂ (Y ⨂ Y) ~> (X ⨂ Y) ⨂ (X ⨂ Y) :=
  (@tensor_assoc C _ X Y (X ⨂ Y))⁻¹
    ∘ bimap id[X] (to (@tensor_assoc C _ Y X Y))
    ∘ bimap id[X] (bimap (@braid C _ X Y) id[Y])
    ∘ bimap id[X] ((@tensor_assoc C _ X Y Y)⁻¹)
    ∘ to (@tensor_assoc C _ X X (Y ⨂ Y)).

(*
   本节说明幺半结构、幺半群、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma mid_swap_iso (X Y : C) :
  mid_swap X Y ∘ mid_swap_inv X Y ≈ id[(X ⨂ X) ⨂ (Y ⨂ Y)].
Proof. exact (@swap_inner_invol C S X X Y Y). Qed.

Lemma mid_swap_iso_sym (X Y : C) :
  mid_swap_inv X Y ∘ mid_swap X Y ≈ id[(X ⨂ Y) ⨂ (X ⨂ Y)].
Proof. exact (@swap_inner_invol C S X Y X Y). Qed.

(** 本节：Canonical [mu] [X ⨂ Y] those [X] [Y]. （已译） *)
Definition canonical_tensor_mu {X Y : C}
           (MX : Monoid X) (MY : Monoid Y) :
  (X ⨂ Y) ⨂ (X ⨂ Y) ~> X ⨂ Y :=
  bimap (@mu _ _ _ MX) (@mu _ _ _ MY) ∘ mid_swap X Y.

(** Canonical [eta] on [X ⨂ Y]. *)
Definition canonical_tensor_eta {X Y : C}
           (MX : Monoid X) (MY : Monoid Y) :
  I ~> X ⨂ Y :=
  bimap (@eta _ _ _ MX) (@eta _ _ _ MY) ∘ from (@unit_left C _ I).

(** Canonical [delta] on [X ⨂ Y]. *)
Definition canonical_tensor_delta {X Y : C}
           (CX : Comonoid X) (CY : Comonoid Y) :
  X ⨂ Y ~> (X ⨂ Y) ⨂ (X ⨂ Y) :=
  mid_swap_inv X Y ∘ bimap (@delta _ _ _ CX) (@delta _ _ _ CY).

(** Canonical [epsilon] on [X ⨂ Y]. *)
Definition canonical_tensor_epsilon {X Y : C}
           (CX : Comonoid X) (CY : Comonoid Y) :
  X ⨂ Y ~> I :=
  to (@unit_left C _ I) ∘ bimap (@epsilon _ _ _ CX) (@epsilon _ _ _ CY).

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class Hypergraph : Type := {
  scfa : forall (X : C), SpecialCommutativeFrobenius X;

  scfa_tensor_mu : forall (X Y : C),
    scfa_mu (scfa (X ⨂ Y)) ≈ canonical_tensor_mu (scfa X) (scfa Y);

  scfa_tensor_eta : forall (X Y : C),
    scfa_eta (scfa (X ⨂ Y)) ≈ canonical_tensor_eta (scfa X) (scfa Y);

  scfa_tensor_delta : forall (X Y : C),
    scfa_delta (scfa (X ⨂ Y)) ≈ canonical_tensor_delta (scfa X) (scfa Y);

  scfa_tensor_epsilon : forall (X Y : C),
    scfa_epsilon (scfa (X ⨂ Y)) ≈ canonical_tensor_epsilon (scfa X) (scfa Y);

  (** Unit-对象 coherence — closes CRIT-1. The canonical SCFA [I]
 trivial one: [μ_I ≈ unit_left], [η_I ≈ id], etc. （已译） *)

  scfa_unit_mu :
    scfa_mu (scfa I) ≈ to (@unit_left C _ I);

  scfa_unit_eta :
    scfa_eta (scfa I) ≈ id[I];

  scfa_unit_delta :
    scfa_delta (scfa I) ≈ from (@unit_left C _ I);

  scfa_unit_epsilon :
    scfa_epsilon (scfa I) ≈ id[I]
}.

End Hypergraph.

Arguments scfa {C S _} X.
Arguments Hypergraph C {S}.
