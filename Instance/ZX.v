Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Monoidal.
Require Import Category.Construction.PROP.

Generalizable All Variables.

(*
 Reference: Coecke–Duncan, "Interacting Quantum Observables: Categorical

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   关于the ZX-calculus的来源与用途

   Wikipedia: https://en.wikipedia.org/wiki/ZX-calculus
   Paper:     Abramsky, Coecke, "A categorical semantics of quantum
   Paper:     Coecke, Duncan, "Interacting Quantum Observables",

   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明幺半群、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Parameter Phase : Type.
Parameter phase_zero : Phase.
Parameter phase_add  : Phase -> Phase -> Phase.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Inductive ZX : nat -> nat -> Type :=
  | zx_id     : forall n : nat, ZX n n
  | zx_swap   : ZX 2 2                          (* wire crossing 2 → 2 *)
  | zx_compose: forall m n p, ZX n p -> ZX m n -> ZX m p
  | zx_tensor : forall m n m' n', ZX m n -> ZX m' n' -> ZX (m + m') (n + n')
  | zx_z      : forall m n : nat, Phase -> ZX m n   (* Z-spider Z_m^n(α) *)
  | zx_x      : forall m n : nat, Phase -> ZX m n   (* X-spider X_m^n(α) *)
  | zx_h      : ZX 1 1.                              (* Hadamard *)

Arguments zx_id n : assert.
Arguments zx_compose {m n p} _ _.
Arguments zx_tensor {m n m' n'} _ _.
Arguments zx_z m n _ : assert.
Arguments zx_x m n _ : assert.

(** 本节：Notation ZX wires. Composition diagrams written
 [f ⊙ g], tensor [f ⊕ g] (to avoid clashing [⨂]). （已译） *)

Declare Scope zx_scope.
Delimit Scope zx_scope with zx.

Notation "f ⊙ g" := (zx_compose f g) (at level 40, left associativity) : zx_scope.
Notation "f ⊕ g" := (zx_tensor f g) (at level 30, right associativity) : zx_scope.
Open Scope zx_scope.

(*
   本节说明 ZX 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Inductive zx_eq : forall {m n}, ZX m n -> ZX m n -> Prop :=
  (** Congruence: zx_eq reflexive, symmetric, transitive, and
 preserved tensor 复合. （已译） *)
  | zx_eq_refl  : forall {m n} (f : ZX m n), zx_eq f f
  | zx_eq_sym   : forall {m n} (f g : ZX m n), zx_eq f g -> zx_eq g f
  | zx_eq_trans : forall {m n} (f g h : ZX m n),
                    zx_eq f g -> zx_eq g h -> zx_eq f h
  | zx_eq_compose :
      forall {m n p} (f f' : ZX n p) (g g' : ZX m n),
        zx_eq f f' -> zx_eq g g' -> zx_eq (f ⊙ g) (f' ⊙ g')
  | zx_eq_tensor :
      forall {m n m' n'} (f f' : ZX m n) (g g' : ZX m' n'),
        zx_eq f f' -> zx_eq g g' -> zx_eq (f ⊕ g) (f' ⊕ g')
  (** Category laws (strict on the nose). *)
  | zx_eq_id_left :
      forall {m n} (f : ZX m n), zx_eq (zx_id n ⊙ f) f
  | zx_eq_id_right :
      forall {m n} (f : ZX m n), zx_eq (f ⊙ zx_id m) f
  | zx_eq_assoc :
      forall {m n p q} (f : ZX p q) (g : ZX n p) (h : ZX m n),
        zx_eq ((f ⊙ g) ⊙ h) (f ⊙ (g ⊙ h))
  (** Identity-spider axiom [S2]: Z_1^1(0) = X_1^1(0) = id_1. *)
  | zx_eq_z_id : zx_eq (zx_z 1 1 phase_zero) (zx_id 1)
  | zx_eq_x_id : zx_eq (zx_x 1 1 phase_zero) (zx_id 1)
  (*
   本节说明 ZX 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  | zx_eq_z_fusion :
      forall (m n : nat) (alpha beta : Phase),
        zx_eq (zx_z 1 n alpha ⊙ zx_z m 1 beta)
              (zx_z m n (phase_add alpha beta))
  | zx_eq_x_fusion :
      forall (m n : nat) (alpha beta : Phase),
        zx_eq (zx_x 1 n alpha ⊙ zx_x m 1 beta)
              (zx_x m n (phase_add alpha beta))
  (** Hadamard self-inverse: H ⊙ H = id_1. *)
  | zx_eq_h_invol :
      zx_eq (zx_h ⊙ zx_h) (zx_id 1)
  (*
   本节说明 ZX 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  | zx_eq_colour_change_1 :
      forall (alpha : Phase),
        zx_eq (zx_h ⊙ zx_z 1 1 alpha ⊙ zx_h)
              (zx_x 1 1 alpha)
  (** Swap involutivity: σ ⊙ σ = id_2. *)
  | zx_eq_swap_invol :
      zx_eq (zx_swap ⊙ zx_swap) (zx_id 2)
  (*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  | zx_eq_tensor_id :
      forall (m n : nat), zx_eq (zx_id m ⊕ zx_id n) (zx_id (m + n))
  (*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  | zx_eq_tensor_compose :
      forall {m n p m' n' p' : nat}
             (f : ZX n p) (h : ZX m n)
             (g : ZX n' p') (k : ZX m' n'),
        zx_eq ((f ⊕ g) ⊙ (h ⊕ k))%zx ((f ⊙ h) ⊕ (g ⊙ k))%zx.

(** Setoid wrapper. *)
#[export] Program Instance ZX_Setoid {m n : nat} : Setoid (ZX m n) := {|
  equiv := @zx_eq m n
|}.
Next Obligation.
  constructor.
  - intros f; apply zx_eq_refl.
  - intros f g; apply zx_eq_sym.
  - intros f g h; apply zx_eq_trans.
Defined.

(*
   本节说明 ZX 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[export] Program Instance zx_compose_respects {m n p : nat} :
  Proper (equiv ==> equiv ==> equiv) (@zx_compose m n p).
Next Obligation.
  proper.
  apply zx_eq_compose; assumption.
Qed.

Program Definition ZX_Cat : Category := {|
  obj      := nat;
  hom      := ZX;
  homset   := @ZX_Setoid;
  id       := zx_id;
  compose  := @zx_compose;
  compose_respects := @zx_compose_respects;
  id_left  := fun m n f => zx_eq_id_left f;
  id_right := fun m n f => zx_eq_id_right f;
  comp_assoc := fun m n p q f g h => zx_eq_sym _ _ (zx_eq_assoc f g h);
  comp_assoc_sym := fun m n p q f g h => zx_eq_assoc f g h
|}.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[export] Program Instance zx_tensor_respects {m n m' n' : nat} :
  Proper (equiv ==> equiv ==> equiv) (@zx_tensor m n m' n').
Next Obligation.
  proper.
  apply zx_eq_tensor; assumption.
Qed.

Program Definition ZX_Bifunctor
  : (ZX_Cat ∏ ZX_Cat) ⟶ ZX_Cat := {|
  fobj := fun mn => Nat.add (fst mn) (snd mn);
  fmap := fun mn pq fg => zx_tensor (fst fg) (snd fg)
|}.
Next Obligation.
  proper; simpl in *.
  apply zx_eq_tensor; assumption.
Defined.
Next Obligation.
  apply zx_eq_tensor_id.
Defined.
Next Obligation.
  apply zx_eq_sym, zx_eq_tensor_compose.
Defined.

(* * ** Sanity check: 恒等 wire [n] composed itself itself. （已译） *)

Lemma zx_id_compose_id (n : nat) :
  zx_eq (zx_id n ⊙ zx_id n) (zx_id n).
Proof. apply zx_eq_id_left. Qed.

(* 相关说明。 （已译） *)

Lemma zx_z_self_fuse (m n : nat) :
  zx_eq (zx_z 1 n phase_zero ⊙ zx_z m 1 phase_zero)
        (zx_z m n (phase_add phase_zero phase_zero)).
Proof. apply (zx_eq_z_fusion m n). Qed.

(* 相关说明。 （已译） *)

Lemma zx_x_self_fuse (m n : nat) :
  zx_eq (zx_x 1 n phase_zero ⊙ zx_x m 1 phase_zero)
        (zx_x m n (phase_add phase_zero phase_zero)).
Proof. apply (zx_eq_x_fusion m n). Qed.

(* 相关说明。 （已译） *)

Lemma zx_h_triple :
  zx_eq (zx_h ⊙ zx_h ⊙ zx_h) zx_h.
Proof.
  eapply zx_eq_trans.
  - apply zx_eq_compose; [ apply zx_eq_h_invol | apply zx_eq_refl ].
  - apply zx_eq_id_left.
Qed.

(* * ** Double swap 恒等 wire pair. （已译） *)

Lemma zx_swap_double :
  zx_eq (zx_swap ⊙ zx_swap) (zx_id 2).
Proof. apply zx_eq_swap_invol. Qed.

(* * ** Quadruple swap 恒等 (two double-swaps). （已译） *)

Lemma zx_swap_quadruple :
  zx_eq (zx_swap ⊙ zx_swap ⊙ zx_swap ⊙ zx_swap) (zx_id 2).
Proof.
  (* parses as ((s⊙s)⊙s)⊙s ; re-associate to (s⊙s)⊙(s⊙s) *)
  eapply zx_eq_trans.
  - apply zx_eq_assoc.
  - eapply zx_eq_trans.
    + apply zx_eq_compose; apply zx_eq_swap_invol.
    + apply zx_eq_id_left.
Qed.

(* * ** Quadruple Hadamard 恒等 wire. （已译） *)

Lemma zx_h_quadruple :
  zx_eq (zx_h ⊙ zx_h ⊙ (zx_h ⊙ zx_h)) (zx_id 1).
Proof.
  eapply zx_eq_trans.
  - apply zx_eq_compose; apply zx_eq_h_invol.
  - apply zx_eq_id_left.
Qed.

(* * ** Identity Z-spider right absorbed 复合. （已译） *)

Lemma zx_compose_z_id_right {m : nat} (f : ZX m 1) :
  zx_eq (zx_z 1 1 phase_zero ⊙ f) f.
Proof.
  eapply zx_eq_trans.
  - apply zx_eq_compose; [ apply zx_eq_z_id | apply zx_eq_refl ].
  - apply zx_eq_id_left.
Qed.
