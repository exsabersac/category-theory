Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Structure.Monoidal.Hypergraph.

Generalizable All Variables.

(** * PROPs (PROducts and Permutations) *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

   本文件给出 PROP 相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明幺半结构、hom、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class PROP : Type := {
  prop_cat : Category;

  prop_strict : @StrictMonoidal prop_cat;
  prop_symmetric : @SymmetricMonoidal prop_cat;

  (*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  prop_monoidal_coherence :
    (@strict_is_monoidal prop_cat prop_strict)
    = (@braided_is_monoidal prop_cat
         (@symmetric_is_braided prop_cat prop_symmetric));

  (** The canonical object correspondence: every natural number names an
      object of [prop_cat], with [0] the monoidal unit and addition
      reflecting tensor. *)
  prop_of_nat : nat -> @obj prop_cat;

  prop_unit_zero :
    @I prop_cat (@strict_is_monoidal prop_cat prop_strict)
    = prop_of_nat 0;

  prop_tensor_plus : forall (m n : nat),
    ((prop_of_nat m) ⨂[@strict_is_monoidal prop_cat prop_strict]
     (prop_of_nat n))%object
    = prop_of_nat (m + n)
}.

#[export] Existing Instance prop_strict.
#[export] Existing Instance prop_symmetric.

Coercion prop_cat : PROP >-> Category.

(*
   本节说明 PROP 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section PROPLemmas.

Context (P : PROP).

(** The PROP-object [⟦n⟧] is the canonical object indexed by [n : nat]. *)
Notation "⟦ n ⟧" := (@prop_of_nat P n) (at level 0, format "⟦ n ⟧").

(** Sanity: the unit object of [P] is [⟦0⟧]. *)
Lemma prop_I_eq_zero : @I P _ = ⟦0⟧.
Proof. exact prop_unit_zero. Qed.

(** Sanity: tensor on objects is addition. *)
Lemma prop_tensor_eq_plus (m n : nat) :
  (⟦m⟧ ⨂ ⟦n⟧)%object = ⟦m + n⟧.
Proof. exact (prop_tensor_plus m n). Qed.

(** Tensor of three PROP-objects collapses to the sum. *)
Lemma prop_tensor_triple (m n p : nat) :
  ((⟦m⟧ ⨂ ⟦n⟧) ⨂ ⟦p⟧)%object = ⟦m + n + p⟧.
Proof.
  rewrite prop_tensor_plus.
  apply prop_tensor_plus.
Qed.

(** The unit object on the left of a tensor is absorbed. *)
Lemma prop_tensor_unit_left_obj (n : nat) :
  (⟦0⟧ ⨂ ⟦n⟧)%object = ⟦n⟧.
Proof.
  rewrite prop_tensor_plus.
  reflexivity.
Qed.

(** The unit object on the right of a tensor is absorbed, modulo [n + 0 = n]. *)
Lemma prop_tensor_unit_right_obj (n : nat) :
  (⟦n⟧ ⨂ ⟦0⟧)%object = ⟦n + 0⟧.
Proof. apply prop_tensor_plus. Qed.

(*
   本节说明 PROP 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Open Scope nat_scope.

(** Iterated tensor of [n] copies of [⟦1⟧], starting from [I]. *)
Fixpoint iter_tensor (n : nat) : @obj P :=
  match n with
  | O    => @I P _
  | S n' => (@prop_of_nat P 1 ⨂ iter_tensor n')%object
  end.

(** Every PROP object [⟦n⟧] is Leibniz-equal to [iter_tensor n].

    Base: [⟦0⟧ = I] by [prop_unit_zero].
    Step: [⟦S n⟧ = ⟦1 + n⟧ = ⟦1⟧ ⨂ ⟦n⟧ = ⟦1⟧ ⨂ iter_tensor n] by IH. *)
Lemma prop_of_nat_iter : forall n, @prop_of_nat P n = iter_tensor n.
Proof.
  induction n; cbn.
  - exact (eq_sym (@prop_unit_zero P)).
  - rewrite <- IHn.
    exact (eq_sym (@prop_tensor_plus P 1 n)).
Qed.

(** The successor decomposition: [⟦S n⟧ = ⟦1⟧ ⨂ ⟦n⟧]. *)
Lemma prop_of_nat_S :
  forall n, @prop_of_nat P (S n)
            = (@prop_of_nat P 1 ⨂ @prop_of_nat P n)%object.
Proof. intro n. exact (eq_sym (@prop_tensor_plus P 1 n)). Qed.

Close Scope nat_scope.

End PROPLemmas.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class HypergraphPROP : Type := {
  hpprop : PROP;

  hpprop_hyper : @Hypergraph
                   (@prop_cat hpprop)
                   (@prop_symmetric hpprop)
}.

#[export] Existing Instance hpprop_hyper.

Coercion hpprop : HypergraphPROP >-> PROP.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
