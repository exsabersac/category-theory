Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.Frobenius.
Require Import Category.Theory.Algebra.CommutativeFrobenius.
Require Import Category.Theory.Algebra.SpecialCommutativeFrobenius.
Require Import Category.Structure.Monoidal.Hypergraph.

Generalizable All Variables.

(*
      nLab:      https://ncatlab.org/nlab/show/Frobenius+algebra
      nLab:      https://ncatlab.org/nlab/show/classical+structure
      Wikipedia: https://en.wikipedia.org/wiki/ZX-calculus
      Wikipedia: https://en.wikipedia.org/wiki/Frobenius_algebra

   本文件给出幺半相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Spider.

Context {C : Category}.
Context `{Sym : @SymmetricMonoidal C}.
Context `{H : @Hypergraph C Sym}.

(** 本节：The Frobenius law at user-friendly [scfa_*] level. （已译） *)
Lemma spider_frobenius (X : C) :
  scfa_delta (scfa X) ∘ scfa_mu (scfa X)
  ≈ bimap (scfa_mu (scfa X)) id[X]
      ∘ from (@tensor_assoc C _ X X X)
      ∘ bimap id[X] (scfa_delta (scfa X)).
Proof.
  unfold scfa_mu, scfa_delta.
  symmetry.
  apply (frob_law_left (Frobenius := scfa X)).
Qed.

(** Symmetric form: the right Frobenius law. *)
Lemma spider_frobenius_sym (X : C) :
  scfa_delta (scfa X) ∘ scfa_mu (scfa X)
  ≈ bimap id[X] (scfa_mu (scfa X))
      ∘ to (@tensor_assoc C _ X X X)
      ∘ bimap (scfa_delta (scfa X)) id[X].
Proof.
  unfold scfa_mu, scfa_delta.
  symmetry.
  apply (frob_law_right (Frobenius := scfa X)).
Qed.

(** Specialness, the collapse axiom: [μ ∘ δ ≈ id]. *)
Lemma spider_collapse (X : C) :
  scfa_mu (scfa X) ∘ scfa_delta (scfa X) ≈ id[X].
Proof.
  unfold scfa_mu, scfa_delta.
  apply (mu_delta_id (SpecialCommutativeFrobenius := scfa X)).
Qed.

(** Monoid associativity at the [scfa_*] level. *)
Lemma spider_mu_assoc (X : C) :
  scfa_mu (scfa X) ∘ bimap (scfa_mu (scfa X)) id[X]
  ≈ scfa_mu (scfa X) ∘ bimap id[X] (scfa_mu (scfa X))
      ∘ to (@tensor_assoc C _ X X X).
Proof.
  unfold scfa_mu.
  apply (mu_assoc (Monoid := scfa X)).
Qed.

(** Comonoid coassociativity at the [scfa_*] level. *)
Lemma spider_delta_coassoc (X : C) :
  bimap (scfa_delta (scfa X)) id[X] ∘ scfa_delta (scfa X)
  ≈ from (@tensor_assoc C _ X X X)
      ∘ bimap id[X] (scfa_delta (scfa X))
      ∘ scfa_delta (scfa X).
Proof.
  unfold scfa_delta.
  apply (delta_coassoc (Comonoid := scfa X)).
Qed.

(** Monoid unit laws at the [scfa_*] level. *)
Lemma spider_mu_unit_left (X : C) :
  scfa_mu (scfa X) ∘ bimap (scfa_eta (scfa X)) id[X]
  ≈ to (@unit_left C _ X).
Proof.
  unfold scfa_mu, scfa_eta.
  apply (mu_unit_left (Monoid := scfa X)).
Qed.

Lemma spider_mu_unit_right (X : C) :
  scfa_mu (scfa X) ∘ bimap id[X] (scfa_eta (scfa X))
  ≈ to (@unit_right C _ X).
Proof.
  unfold scfa_mu, scfa_eta.
  apply (mu_unit_right (Monoid := scfa X)).
Qed.

(** Comonoid counit laws at the [scfa_*] level. *)
Lemma spider_delta_counit_left (X : C) :
  bimap (scfa_epsilon (scfa X)) id[X] ∘ scfa_delta (scfa X)
  ≈ from (@unit_left C _ X).
Proof.
  unfold scfa_delta, scfa_epsilon.
  apply (delta_counit_left (Comonoid := scfa X)).
Qed.

Lemma spider_delta_counit_right (X : C) :
  bimap id[X] (scfa_epsilon (scfa X)) ∘ scfa_delta (scfa X)
  ≈ from (@unit_right C _ X).
Proof.
  unfold scfa_delta, scfa_epsilon.
  apply (delta_counit_right (Comonoid := scfa X)).
Qed.

(** Commutativity of [scfa_mu] under the braid. *)
Lemma spider_mu_commutative (X : C) :
  scfa_mu (scfa X) ∘ braid ≈ scfa_mu (scfa X).
Proof.
  unfold scfa_mu.
  apply (mu_commutative (CommutativeFrobenius := scfa X)).
Qed.

(** Cocommutativity of [scfa_delta] under the braid. *)
Lemma spider_delta_cocommutative (X : C) :
  braid ∘ scfa_delta (scfa X) ≈ scfa_delta (scfa X).
Proof.
  unfold scfa_delta.
  apply (delta_cocommutative (CommutativeFrobenius := scfa X)).
Qed.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma spider_3_to_1 (X : C) :
  scfa_mu (scfa X) ∘ bimap (scfa_mu (scfa X)) id[X]
  ≈ scfa_mu (scfa X) ∘ bimap id[X] (scfa_mu (scfa X))
      ∘ to (@tensor_assoc C _ X X X).
Proof.
  apply spider_mu_assoc.
Qed.

(** Dually, the 1-into-3 spider. *)
Lemma spider_1_to_3 (X : C) :
  bimap (scfa_delta (scfa X)) id[X] ∘ scfa_delta (scfa X)
  ≈ from (@tensor_assoc C _ X X X)
      ∘ bimap id[X] (scfa_delta (scfa X)) ∘ scfa_delta (scfa X).
Proof.
  apply spider_delta_coassoc.
Qed.

(** 本节：The 2-into-2 spider: heart Frobenius equation. （已译） *)
Lemma spider_2_to_2 (X : C) :
  scfa_delta (scfa X) ∘ scfa_mu (scfa X)
  ≈ bimap (scfa_mu (scfa X)) id[X]
      ∘ from (@tensor_assoc C _ X X X)
      ∘ bimap id[X] (scfa_delta (scfa X)).
Proof.
  apply spider_frobenius.
Qed.

End Spider.

(*
   本节说明 Spider 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section TPower.
Context {C : Category}.
Context `{M : @Monoidal C}.

Fixpoint tpower (X : C) (n : nat) : C :=
  match n with
  | O   => I
  | S k => X ⨂ tpower X k
  end.

End TPower.

Notation "X '^⨂' n" := (tpower X n) (at level 30, no associativity) : object_scope.

Section SpiderConstructions.
Context {C : Category}.
Context `{Sym : @SymmetricMonoidal C}.
Context `{H : @Hypergraph C Sym}.

(** Fold n+1 copies of X into one using μ.

    Concretely, [fold_mu X 0] is just [unit_right⁻¹]-style: X^⨂1 = X⨂I ~> X.
    [fold_mu X (S k)] = μ ∘ (id ⨂ fold_mu X k) : X⨂X^⨂(S k) ~> X. *)
Fixpoint fold_mu (X : C) (n : nat) : tpower X (S n) ~> X :=
  match n with
  | O   => to (@unit_right C _ X)
  | S k => scfa_mu (scfa X) ∘ bimap id[X] (fold_mu X k)
  end.

Fixpoint unfold_delta (X : C) (n : nat) : X ~> tpower X (S n) :=
  match n with
  | O   => from (@unit_right C _ X)
  | S k => bimap id[X] (unfold_delta X k) ∘ scfa_delta (scfa X)
  end.

(** [fold_eta X n : I ~> X^⨂n] sends I into X^⨂n via repeated η.

    Concretely, [fold_eta X 0] = id_I, and [fold_eta X (S n)] uses
    [bimap η (fold_eta X n) ∘ unit_left⁻¹]. *)
Fixpoint fold_eta (X : C) (n : nat) : I ~> tpower X n :=
  match n with
  | O   => id[I]
  | S k => bimap (scfa_eta (scfa X)) (fold_eta X k) ∘ from (@unit_left C _ I)
  end.

(** Dual: [fold_eps X n : X^⨂n ~> I] sends X^⨂n into I via repeated ε. *)
Fixpoint fold_eps (X : C) (n : nat) : tpower X n ~> I :=
  match n with
  | O   => id[I]
  | S k => to (@unit_left C _ I) ∘ bimap (scfa_epsilon (scfa X)) (fold_eps X k)
  end.

(** The canonical spider [canonical_spider X m n : X^⨂m ~> X^⨂n].

    Defined by case-analysis on whether each side is zero:
      - m = 0, n = 0:   id_I
      - m = 0, S n':    fold_eta : I ~> X^⨂(S n')
      - S m', n = 0:    fold_eps : X^⨂(S m') ~> I
      - S m', S n':    unfold_delta ∘ fold_mu :
                        X^⨂(S m') -- fold_mu --> X -- unfold_delta --> X^⨂(S n')
*)
Definition canonical_spider (X : C) (m n : nat) : tpower X m ~> tpower X n :=
  match m, n with
  | O,    O    => id[I]
  | O,    S n' => fold_eta X (S n')
  | S m', O    => fold_eps X (S m')
  | S m', S n' => unfold_delta X n' ∘ fold_mu X m'
  end.

(* 相关说明。 （已译） *)

Lemma canonical_spider_0_0 (X : C) :
  canonical_spider X 0 0 = id[I].
Proof. reflexivity. Qed.

Lemma canonical_spider_0_1 (X : C) :
  canonical_spider X 0 1
  = bimap (scfa_eta (scfa X)) id[I] ∘ from (@unit_left C _ I).
Proof. reflexivity. Qed.

Lemma canonical_spider_1_0 (X : C) :
  canonical_spider X 1 0
  = to (@unit_left C _ I) ∘ bimap (scfa_epsilon (scfa X)) id[I].
Proof. reflexivity. Qed.

Lemma canonical_spider_1_1 (X : C) :
  canonical_spider X 1 1
  = from (@unit_right C _ X) ∘ to (@unit_right C _ X).
Proof. reflexivity. Qed.

(** The 1-1 spider 恒等 (a special case un-bracketed
 1-1 spider law, here verified direct cancellation [unit_right]
 inverse). （已译） *)
Lemma canonical_spider_1_1_id (X : C) :
  canonical_spider X 1 1 ≈ id[X ⨂ I].
Proof.
  rewrite canonical_spider_1_1.
  apply iso_from_to.
Qed.

Lemma canonical_spider_2_1 (X : C) :
  canonical_spider X 2 1
  = from (@unit_right C _ X)
      ∘ (scfa_mu (scfa X) ∘ bimap id[X] (to (@unit_right C _ X))).
Proof. reflexivity. Qed.

Lemma canonical_spider_1_2 (X : C) :
  canonical_spider X 1 2
  = (bimap id[X] (from (@unit_right C _ X)) ∘ scfa_delta (scfa X))
      ∘ to (@unit_right C _ X).
Proof. reflexivity. Qed.

Lemma canonical_spider_2_2 (X : C) :
  canonical_spider X 2 2
  = (bimap id[X] (from (@unit_right C _ X)) ∘ scfa_delta (scfa X))
      ∘ (scfa_mu (scfa X) ∘ bimap id[X] (to (@unit_right C _ X))).
Proof. reflexivity. Qed.

(*
   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** The 1→1 spider just 恒等 (modulo [unit_right] cast
 introduced [tpower X 1 = X ⨂ I]). （已译） *)
Lemma fold_mu_unfold_delta_1 (X : C) :
  unfold_delta X 0 ∘ fold_mu X 0
  ≈ from (@unit_right C _ X) ∘ to (@unit_right C _ X).
Proof. simpl; reflexivity. Qed.

(*
   本节说明 Spider 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma spider_2_to_1_then_1_to_2 (X : C) :
  unfold_delta X 0 ∘ fold_mu X 1
  ≈ from (@unit_right C _ X)
      ∘ (scfa_mu (scfa X) ∘ bimap id[X] (fold_mu X 0)).
Proof. simpl; reflexivity. Qed.

(** The 0→0 spider 恒等 I. （已译） *)
Lemma canonical_spider_0_0_id (X : C) :
  canonical_spider X 0 0 ≈ id[I].
Proof. simpl; reflexivity. Qed.

(*
   本节说明 Spider 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma fold_eps_eta_I (n : nat) :
  fold_eps (I (C := C)) n ∘ fold_eta (I (C := C)) n ≈ id[I].
Proof.
  induction n as [|k IH]; simpl.
  - apply id_left.
  - (* (unit_left ∘ bimap ε (fold_eps I k))
       ∘ (bimap η (fold_eta I k) ∘ unit_left⁻¹) ≈ id *)
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (bimap (scfa_epsilon _) (fold_eps I k))).
    rewrite <- bimap_comp.
    rewrite scfa_unit_epsilon.
    rewrite scfa_unit_eta.
    rewrite IH.
    rewrite id_left.
    rewrite bimap_id_id.
    rewrite id_left.
    rewrite iso_to_from.
    reflexivity.
Qed.

End SpiderConstructions.

Arguments tpower {C M} X n.
Arguments fold_mu {C Sym H} X n.
Arguments unfold_delta {C Sym H} X n.
Arguments fold_eta {C Sym H} X n.
Arguments fold_eps {C Sym H} X n.
Arguments canonical_spider {C Sym H} X m n.

(*
   本节说明 Spider 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* * ** Syntactic spider expressions Lack's normal-form 定理 （已译） *)

Section SpiderExpr.

Context {C : Category}.
Context `{Sym : @SymmetricMonoidal C}.
Context `{Hyp : @Hypergraph C Sym}.

(*
   本节说明 Spider 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Open Scope nat_scope.

(*
   本节说明 Spider 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Inductive SpiderExpr (X : C) : nat -> nat -> Type :=
  | SE_id_X    : SpiderExpr 1 1
  | SE_mu_X    : SpiderExpr 2 1
  | SE_eta_X   : SpiderExpr 0 1
  | SE_delta_X : SpiderExpr 1 2
  | SE_eps_X   : SpiderExpr 1 0
  | SE_braid_X : SpiderExpr 2 2
  | SE_seq_X   : forall {m k n},
      SpiderExpr m k -> SpiderExpr k n -> SpiderExpr m n
  | SE_par_X   : forall {m1 n1 m2 n2},
      SpiderExpr m1 n1 -> SpiderExpr m2 n2
      -> SpiderExpr (m1 + m2) (n1 + n2).

Arguments SE_id_X    {X}.
Arguments SE_mu_X    {X}.
Arguments SE_eta_X   {X}.
Arguments SE_delta_X {X}.
Arguments SE_eps_X   {X}.
Arguments SE_braid_X {X}.
Arguments SE_seq_X   {X m k n} _ _.
Arguments SE_par_X   {X m1 n1 m2 n2} _ _.

Close Scope nat_scope.

(*
   本节说明 Spider 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Fixpoint tpower_add_iso (X : C) (m1 m2 : nat) {struct m1} :
  (tpower X m1 ⨂ tpower X m2)%object ≅ tpower X (m1 + m2) :=
  match m1
        return (tpower X m1 ⨂ tpower X m2)%object ≅ tpower X (m1 + m2)
  with
  | O      => @unit_left C _ (tpower X m2)
  | S m1'  =>
      iso_compose
        (@bifunctor_respects _ _ _ (@tensor C _)
           (X, (tpower X m1' ⨂ tpower X m2)%object)
           (X, tpower X (m1' + m2))
           (@iso_id C X, tpower_add_iso X m1' m2))
        (@tensor_assoc C _ X (tpower X m1') (tpower X m2))
  end.

(* 相关说明。 （已译） *)
Fixpoint denote_spider {X : C} {m n : nat}
  (e : SpiderExpr X m n) : tpower X m ~> tpower X n :=
  match e with
  | SE_id_X        => id
  | SE_mu_X        =>
      from (@unit_right C _ X)
        ∘ scfa_mu (scfa X)
        ∘ bimap id[X] (to (@unit_right C _ X))
  | SE_eta_X       =>
      from (@unit_right C _ X) ∘ scfa_eta (scfa X)
  | SE_delta_X     =>
      bimap id[X] (from (@unit_right C _ X))
        ∘ scfa_delta (scfa X)
        ∘ to (@unit_right C _ X)
  | SE_eps_X       =>
      scfa_epsilon (scfa X) ∘ to (@unit_right C _ X)
  | SE_braid_X     =>
      bimap id[X] (from (@unit_right C _ X))
        ∘ braid
        ∘ bimap id[X] (to (@unit_right C _ X))
  | SE_seq_X e1 e2 => denote_spider e2 ∘ denote_spider e1
  | SE_par_X e1 e2 =>
      to (tpower_add_iso X _ _)
      ∘ bimap (denote_spider e1) (denote_spider e2)
      ∘ from (tpower_add_iso X _ _)
  end.

(*
   本节说明 Spider 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Spider 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma fold_mu_unfold_delta_id (X : C) (k : nat) :
  fold_mu X k ∘ unfold_delta X k ≈ id[X].
Proof.
  induction k as [|k IH]; simpl.
  - (* k = 0:  to unit_right ∘ from unit_right ≈ id *)
    apply iso_to_from.
  - rewrite <- comp_assoc.
    (* Goal: μ ∘ (bimap id (fold_mu k) ∘ (bimap id (unfold_delta k) ∘ δ)) *)
    setoid_rewrite (comp_assoc (bimap id[X] (fold_mu X k))).
    rewrite <- bimap_comp.
    rewrite id_left.
    rewrite IH.
    rewrite bimap_id_id.
    rewrite id_left.
    apply spider_collapse.
Qed.

(*
   本节说明 Spider 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* * ** Smoke-test corollaries [denote_spider] 恒等 sequences

 Direct consequences [SE_seq_X] / [SE_par_X] reduction rules.
 These exercise semantic interpretation without requiring the
 full normal-form 定理. （已译） *)

(** A sequence of two identity wires denotes the identity. *)
Lemma denote_spider_id_seq_id (X : C) :
  denote_spider (SE_seq_X (X := X) SE_id_X SE_id_X) ≈ id.
Proof. simpl; apply id_left. Qed.

(** A 3-fold identity sequence still denotes the identity. *)
Lemma denote_spider_id_seq_3 (X : C) :
  denote_spider
    (SE_seq_X (X := X) SE_id_X (SE_seq_X SE_id_X SE_id_X))
  ≈ id.
Proof. simpl; rewrite id_left; apply id_left. Qed.

(** μ followed by ε denotes [ε_X ∘ μ_X] (modulo the unit_right cast).
    Direct unfolding of [denote_spider]. *)
Lemma denote_spider_mu_seq_eps (X : C) :
  denote_spider (SE_seq_X (X := X) SE_mu_X SE_eps_X)
  ≈ scfa_epsilon (scfa X) ∘ to (@unit_right C _ X)
      ∘ (from (@unit_right C _ X)
           ∘ scfa_mu (scfa X)
           ∘ bimap id[X] (to (@unit_right C _ X))).
Proof. simpl; reflexivity. Qed.

End SpiderExpr.

Arguments SpiderExpr {C} X.
Arguments denote_spider {C Sym Hyp X m n} e.

(*
   本节说明 Spider 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
