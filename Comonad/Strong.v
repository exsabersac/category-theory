Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Import Category.Theory.Monad.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Functor.Strong.
Require Import Category.Monad.Strong.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.Monoidal.
Require Import Category.Comonad.Core.

Generalizable All Variables.

(** * Costrong comonads *)

(*
   nLab:      https://ncatlab.org/nlab/show/tensorial+strength
   Wikipedia: https://en.wikipedia.org/wiki/Strong_monad

   本文件给出（余）强度/强（余）单子相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab:  https://ncatlab.org/nlab/show/tensorial+costrength
   Paper: Blute, Cockett, Seely, J. Pure Appl. Algebra 116(1-3), 1997,
   Paper: Kock, Arch. Math. 23, 1972, pp. 113-120 (tensorial strength)

   本节说明函子、单子、余单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition CostrongComonad {C : Category} (M : @Monoidal C) (W : C ⟶ C) : Type :=
  @StrongMonad (C^op) (@Monoidal_op C M) (W^op).

(*
   本节说明余单子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Existing Class CostrongComonad.

(* ================================================================== *)
(** ** The covariant API: definitional op-reads of the bundled fields  *)
(* ================================================================== *)

Section CostrongComonadAPI.

Context {C : Category}.
Context {M : @Monoidal C}.
Context {W : C ⟶ C}.
Context {CS : CostrongComonad M W}.

(** The underlying comonad: the op-read of [strongmonad_is_monad]. *)
Definition costrong_is_comonad : @Comonad C W :=
  @strongmonad_is_monad (C^op) (@Monoidal_op C M) (W^op) CS.

(*
   本节说明余单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Existing Instance costrong_is_comonad.

(** The underlying strong endofunctor over (C^op, Monoidal_op M): the
    op-read of [strongmonad_is_strong]. *)
Definition costrong_is_strong :
  @StrongFunctor (C^op) (@Monoidal_op C M) (W^op) :=
  @strongmonad_is_strong (C^op) (@Monoidal_op C M) (W^op) CS.

(** The costrength W (x ⨂ y) ~> x ⨂ W y: the covariant reading of
    [strength] at (C^op, Monoidal_op M, W^op). *)
Definition costrength {x y : C} : W (x ⨂ y) ~> x ⨂ W y :=
  @strength (C^op) (@Monoidal_op C M) (W^op) costrong_is_strong x y.

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma costrength_natural {x y z w : C} (f : x ~> y) (k : z ~> w) :
  costrength ∘ fmap[W] (f ⨂ k) ≈ (f ⨂ fmap[W] k) ∘ costrength.
Proof.
  pose proof (@strength_natural (C^op) (@Monoidal_op C M) (W^op)
                costrong_is_strong y x f w z k) as SN.
  simpl in SN.
  rewrite <- fmap_comp in SN.
  rewrite bimap_id_right_left in SN.
  rewrite comp_assoc in SN.
  rewrite bimap_id_right_left in SN.
  exact SN.
Qed.

(** Left-unitor coherence: the op-read of [strength_id_left].  Dualization
    inverts the unitor, so in C the law reads against λ⁻¹: precomposing the
    costrength with W (λ⁻¹) is λ⁻¹ at W x. *)
Lemma costrength_id_left {x : C} :
  costrength ∘ fmap[W] (from (@unit_left C M x))
    ≈ from (@unit_left C M (W x)).
Proof.
  exact (@strength_id_left (C^op) (@Monoidal_op C M) (W^op)
           costrong_is_strong x).
Qed.

(** Associator coherence: the op-read of [strength_assoc], with α likewise
    arriving in its inverse orientation. *)
Lemma costrength_assoc {x y z : C} :
  costrength ∘ fmap[W] (from (@tensor_assoc C M x y z))
    ≈ from (@tensor_assoc C M x y (W z)) ∘ (id[x] ⨂ costrength) ∘ costrength.
Proof.
  rewrite <- comp_assoc.
  exact (@strength_assoc (C^op) (@Monoidal_op C M) (W^op)
           costrong_is_strong x y z).
Qed.

(*
   本节说明余单子、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma costrength_extract {x y : C} :
  (id[x] ⨂ extract) ∘ costrength ≈ (extract : W (x ⨂ y) ~> x ⨂ y).
Proof.
  exact (@strength_ret (C^op) (@Monoidal_op C M) (W^op) CS x y).
Qed.

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma costrength_duplicate {x y : C} :
  (id[x] ⨂ duplicate (x:=y)) ∘ costrength
    ≈ costrength ∘ fmap[W] costrength ∘ duplicate.
Proof.
  rewrite <- comp_assoc.
  exact (@strength_join (C^op) (@Monoidal_op C M) (W^op) CS x y).
Qed.

End CostrongComonadAPI.

(* [costrength[W]] names the costrength of a given costrong comonad on W at
   implicit arguments, mirroring the [strength[F]] convention. *)
Notation "costrength[ W ]" := (@costrength _ _ W%functor _ _ _)
  (at level 9, format "costrength[ W ]") : morphism_scope.

(* ================================================================== *)
(** ** Building the bundled structure from covariant data              *)
(* ================================================================== *)

Section BuildCostrongComonad.

Context {C : Category}.
Context {M : @Monoidal C}.
Context {W : C ⟶ C}.

(*
   本节说明单子、Kleisli相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Obligation Tactic := program_simpl.

(*
   本节说明余单子、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Build_CostrongComonad
  (H : @Comonad C W)
  (sigma : forall x y : C, W (x ⨂ y) ~> x ⨂ W y)
  (sigma_natural : forall (x y z w : C) (f : x ~> y) (k : z ~> w),
    sigma y w ∘ fmap[W] (f ⨂ k) ≈ (f ⨂ fmap[W] k) ∘ sigma x z)
  (sigma_id_left : forall x : C,
    sigma I x ∘ fmap[W] (from (@unit_left C M x))
      ≈ from (@unit_left C M (W x)))
  (sigma_assoc : forall x y z : C,
    sigma ((x ⨂ y)%object) z ∘ fmap[W] (from (@tensor_assoc C M x y z))
      ≈ from (@tensor_assoc C M x y (W z)) ∘ (id[x] ⨂ sigma y z)
          ∘ sigma x ((y ⨂ z)%object))
  (sigma_extract : forall x y : C,
    (id[x] ⨂ extract) ∘ sigma x y ≈ (extract : W (x ⨂ y) ~> x ⨂ y))
  (sigma_duplicate : forall x y : C,
    (id[x] ⨂ duplicate (x:=y)) ∘ sigma x y
      ≈ sigma x (W y) ∘ fmap[W] (sigma x y) ∘ duplicate)
  : CostrongComonad M W :=
  @Build_StrongMonad (C^op) (@Monoidal_op C M) (W^op) H
    (@Build_StrongFunctor (C^op) (@Monoidal_op C M) (W^op)
       (fun x y => sigma x y) _ _ _)
    _ _.
Next Obligation.
  (* strength_natural in C^op: merge the separated actions and apply the
     covariant naturality. *)
  rewrite <- fmap_comp.
  rewrite bimap_id_right_left.
  rewrite comp_assoc.
  rewrite bimap_id_right_left.
  apply sigma_natural.
Qed.
Next Obligation.
  (* strength_assoc in C^op: the op-read arrives right-bracketed. *)
  rewrite comp_assoc.
  apply sigma_assoc.
Qed.
Next Obligation.
  (* strength_join in C^op: likewise a re-bracketing of δ-compat. *)
  rewrite comp_assoc.
  apply sigma_duplicate.
Qed.

End BuildCostrongComonad.

Section BuildCostrongComonadAgreement.

Context {C : Category}.
Context {M : @Monoidal C}.
Context {W : C ⟶ C}.
Context (H : @Comonad C W).
Context (sigma : forall x y : C, W (x ⨂ y) ~> x ⨂ W y).
Context (sigma_natural : forall (x y z w : C) (f : x ~> y) (k : z ~> w),
  sigma y w ∘ fmap[W] (f ⨂ k) ≈ (f ⨂ fmap[W] k) ∘ sigma x z).
Context (sigma_id_left : forall x : C,
  sigma I x ∘ fmap[W] (from (@unit_left C M x))
    ≈ from (@unit_left C M (W x))).
Context (sigma_assoc : forall x y z : C,
  sigma ((x ⨂ y)%object) z ∘ fmap[W] (from (@tensor_assoc C M x y z))
    ≈ from (@tensor_assoc C M x y (W z)) ∘ (id[x] ⨂ sigma y z)
        ∘ sigma x ((y ⨂ z)%object)).
Context (sigma_extract : forall x y : C,
  (id[x] ⨂ extract) ∘ sigma x y ≈ (extract : W (x ⨂ y) ~> x ⨂ y)).
Context (sigma_duplicate : forall x y : C,
  (id[x] ⨂ duplicate (x:=y)) ∘ sigma x y
    ≈ sigma x (W y) ∘ fmap[W] (sigma x y) ∘ duplicate).

(** Reading the costrength back off the assembled structure returns the
    supplied family on the nose. *)
Lemma Build_CostrongComonad_costrength {x y : C} :
  @costrength C M W
    (Build_CostrongComonad H sigma sigma_natural sigma_id_left
       sigma_assoc sigma_extract sigma_duplicate) x y
    ≈ sigma x y.
Proof. reflexivity. Qed.

(** The underlying comonad passes through the assembly unchanged. *)
Lemma Build_CostrongComonad_comonad :
  @costrong_is_comonad C M W
    (Build_CostrongComonad H sigma sigma_natural sigma_id_left
       sigma_assoc sigma_extract sigma_duplicate) = H.
Proof. reflexivity. Qed.

End BuildCostrongComonadAgreement.

(* ================================================================== *)
(** ** Transfers: costrong comonads are strong monads on the opposite  *)
(* ================================================================== *)

(*
   本节说明幺半结构、单子、余单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition CostrongComonad_to_op_StrongMonad
  {C : Category} {M : @Monoidal C} {W : C ⟶ C}
  (CS : CostrongComonad M W) :
  @StrongMonad (C^op) (@Monoidal_op C M) (W^op) := CS.

Definition op_StrongMonad_to_CostrongComonad
  {C : Category} {M : @Monoidal C} {W : C ⟶ C}
  (S : @StrongMonad (C^op) (@Monoidal_op C M) (W^op)) :
  CostrongComonad M W := S.

Lemma CostrongComonad_op_roundtrip
  {C : Category} {M : @Monoidal C} {W : C ⟶ C} (CS : CostrongComonad M W) :
  op_StrongMonad_to_CostrongComonad (CostrongComonad_to_op_StrongMonad CS)
    = CS.
Proof. reflexivity. Qed.

Lemma op_StrongMonad_roundtrip
  {C : Category} {M : @Monoidal C} {W : C ⟶ C}
  (S : @StrongMonad (C^op) (@Monoidal_op C M) (W^op)) :
  CostrongComonad_to_op_StrongMonad (op_StrongMonad_to_CostrongComonad S)
    = S.
Proof. reflexivity. Qed.

Section StrongMonadOpposite.

Context {C : Category}.
Context {M : @Monoidal C}.
Context {T : C ⟶ C}.

(*
   本节说明幺半结构、单子、余单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition StrongMonad_to_op_CostrongComonad (S : @StrongMonad C M T) :
  @CostrongComonad (C^op) (@Monoidal_op C M) (T^op) :=
  @Build_StrongMonad ((C^op)^op)
    (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op)
    (@strongmonad_is_monad C M T S)
    (@Build_StrongFunctor ((C^op)^op)
       (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op)
       (fun x y => @strength C M T (@strongmonad_is_strong C M T S) x y)
       (@strength_natural C M T (@strongmonad_is_strong C M T S))
       (@strength_id_left C M T (@strongmonad_is_strong C M T S))
       (@strength_assoc C M T (@strongmonad_is_strong C M T S)))
    (@strength_ret C M T S)
    (@strength_join C M T S).

Definition op_CostrongComonad_to_StrongMonad
  (S : @CostrongComonad (C^op) (@Monoidal_op C M) (T^op)) :
  @StrongMonad C M T :=
  @Build_StrongMonad C M T
    (@strongmonad_is_monad ((C^op)^op)
       (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op) S)
    (@Build_StrongFunctor C M T
       (fun x y => @strength ((C^op)^op)
          (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op)
          (@strongmonad_is_strong ((C^op)^op)
             (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op) S) x y)
       (@strength_natural ((C^op)^op)
          (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op)
          (@strongmonad_is_strong ((C^op)^op)
             (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op) S))
       (@strength_id_left ((C^op)^op)
          (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op)
          (@strongmonad_is_strong ((C^op)^op)
             (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op) S))
       (@strength_assoc ((C^op)^op)
          (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op)
          (@strongmonad_is_strong ((C^op)^op)
             (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op) S)))
    (@strength_ret ((C^op)^op)
       (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op) S)
    (@strength_join ((C^op)^op)
       (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op) S).

(** Covariantly read, the costrength of the opposite costrong comonad IS
    the strength of the strong monad it came from. *)
Lemma op_costrength_strength (S : @StrongMonad C M T) {x y : C} :
  @costrength (C^op) (@Monoidal_op C M) (T^op)
    (StrongMonad_to_op_CostrongComonad S) x y
    ≈ @strength C M T (@strongmonad_is_strong C M T S) x y.
Proof. reflexivity. Qed.

(*
   本节说明单子、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma StrongMonad_op_roundtrip_strength (S : @StrongMonad C M T) {x y : C} :
  @strength C M T
    (@strongmonad_is_strong C M T
       (op_CostrongComonad_to_StrongMonad
          (StrongMonad_to_op_CostrongComonad S))) x y
    ≈ @strength C M T (@strongmonad_is_strong C M T S) x y.
Proof. reflexivity. Qed.

Lemma StrongMonad_op_roundtrip_monad (S : @StrongMonad C M T) :
  @strongmonad_is_monad C M T
    (op_CostrongComonad_to_StrongMonad (StrongMonad_to_op_CostrongComonad S))
    = @strongmonad_is_monad C M T S.
Proof. reflexivity. Qed.

Lemma op_CostrongComonad_roundtrip_costrength
  (S : @CostrongComonad (C^op) (@Monoidal_op C M) (T^op)) {x y : C} :
  @costrength (C^op) (@Monoidal_op C M) (T^op)
    (StrongMonad_to_op_CostrongComonad (op_CostrongComonad_to_StrongMonad S))
    x y
    ≈ @costrength (C^op) (@Monoidal_op C M) (T^op) S x y.
Proof. reflexivity. Qed.

Lemma op_CostrongComonad_roundtrip_comonad
  (S : @CostrongComonad (C^op) (@Monoidal_op C M) (T^op)) :
  @costrong_is_comonad (C^op) (@Monoidal_op C M) (T^op)
    (StrongMonad_to_op_CostrongComonad (op_CostrongComonad_to_StrongMonad S))
    = @costrong_is_comonad (C^op) (@Monoidal_op C M) (T^op) S.
Proof. reflexivity. Qed.

End StrongMonadOpposite.
