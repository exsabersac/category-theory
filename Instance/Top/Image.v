Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Closed.

Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/frame
 nLab: https://ncatlab.org/nlab/show/locale
 nLab: https://ncatlab.org/nlab/show/inverse+image
 nLab: https://ncatlab.org/nlab/show/interior

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(** ** (A) The inverse image on opens, as a functor *)

Program Definition Opens_preimage {X Y : TopSpace} (g : Y ~{Top}~> X) :
  Opens X ⟶ Opens Y := {|
  fobj := open_preimage g;
  fmap := fun U V (h : ∀ x : X, `1 U x → `1 V x) =>
            fun y (u : `1 U (g y)) => h (g y) u
|}.

Example Opens_preimage_obj {X Y : TopSpace} (g : Y ~{Top}~> X)
  (U : OpenSet X) : fobj[Opens_preimage g] U = open_preimage g U := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** (B) The space, and the refutation *)

(* The points: the naturals with a point at infinity. *)
Definition nat_inf_carrier@{o | Set < o +} : SetoidObject@{o o} :=
  {| carrier   := option nat
   ; is_setoid := eq_Setoid@{o} (option nat) |}.

(* A predicate is open when, if it holds at infinity, it holds on a tail.
   Predicates missing infinity are unconstrained -- so the topology is
   finer than the cofinite one and every subset of the naturals proper is
   open. *)
Definition nat_inf_open@{o} (U : nat_inf_carrier@{o} → Type@{o}) : Type@{o} :=
  U None → { N : nat & ∀ n : nat, (N <= n)%nat → U (Some n) }.

Lemma nat_inf_respects@{o} (U V : nat_inf_carrier@{o} → Type@{o}) :
  (∀ x, U x ↔ V x) → nat_inf_open U → nat_inf_open V.
Proof.
  intros HUV HU Hv.
  destruct (HU (snd (HUV None) Hv)) as [N k].
  exists N; intros n Hn; exact (fst (HUV (Some n)) (k n Hn)).
Qed.

Lemma nat_inf_proper@{o} (U : nat_inf_carrier@{o} → Type@{o}) :
  nat_inf_open U → ∀ x y : nat_inf_carrier, x ≈ y → U x → U y.
Proof. intros _ x y Hxy Ux; rewrite <- Hxy; exact Ux. Qed.

Lemma nat_inf_union@{o} (I : Type@{o})
  (U : I → (nat_inf_carrier@{o} → Type@{o})) :
  (∀ i, nat_inf_open (U i)) → nat_inf_open (fun x => { i : I & U i x }).
Proof.
  intros HU [i u].
  destruct (HU i u) as [N k].
  exists N; intros n Hn; exact (i; k n Hn).
Qed.

Lemma nat_inf_whole@{o} : nat_inf_open@{o} (fun _ => poly_unit@{o}).
Proof. intros _; exists 0%nat; intros n _; exact ttt. Qed.

Lemma nat_inf_inter@{o} (U V : nat_inf_carrier@{o} → Type@{o}) :
  nat_inf_open U → nat_inf_open V →
  nat_inf_open (fun x => U x ∧ V x).
Proof.
  intros HU HV [u v].
  destruct (HU u) as [N1 k1]; destruct (HV v) as [N2 k2].
  exists (Nat.max N1 N2); intros n Hn; split.
  - exact (k1 n (Nat.max_lub_l _ _ _ Hn)).
  - exact (k2 n (Nat.max_lub_r _ _ _ Hn)).
Qed.

Definition NatInf_Top@{o} : TopSpace@{o} := {|
  top_carrier    := nat_inf_carrier@{o};
  IsOpen         := nat_inf_open@{o};
  open_respects  := nat_inf_respects@{o};
  open_proper    := nat_inf_proper@{o};
  open_union     := nat_inf_union@{o};
  open_whole     := nat_inf_whole@{o};
  open_inter     := nat_inf_inter@{o}
|}.

(* The constant map from the point at infinity.  Continuity is free: the
   preimage of any predicate is a constant predicate on a one-point
   space, and [Point_Top] is discrete. *)
Definition nat_inf_point : Point_Top ~{Top}~> NatInf_Top := {|
  continuous_map :=
    const_morphism (top_carrier Point_Top) (top_carrier NatInf_Top) None;
  continuity := fun U _ x y _ h => h
|}.

(* The whole point, as an open of the one-point space. *)
Definition point_whole : OpenSet Point_Top :=
  (fun _ => poly_unit; open_whole Point_Top).

(* Everything except [Some N].  Written as ONE Prop-valued predicate
   rather than a two-branch match: a match with [poly_unit] at infinity
   and a negated equation at the naturals mixes [Type] with [Prop] and is
   rejected, whereas [∀ n, x = Some n → n = N → False] holds vacuously at
   infinity and is a [Prop] uniformly (Instance/Top/Kolmogorov.v's
   [tri_point_open] is the precedent for a Prop-valued open).  It is open
   because it contains the tail from N+1. *)
Lemma nat_inf_punctured_open@{o +} (N : nat) :
  IsOpen NatInf_Top@{o}
    (fun x : NatInf_Top@{o} => ∀ n : nat, x = Some n → n = N → False).
Proof.
  intros _; exists (S N); intros n Hn m Hm HmN.
  assert (Hnm : n = m) by (injection Hm; intro h; exact h).
  rewrite Hnm, HmN in Hn.
  exact (PeanoNat.Nat.nle_succ_diag_l N Hn).
Defined.

Definition nat_inf_punctured@{o +} (N : nat) : OpenSet NatInf_Top@{o} :=
  existT _ _ (nat_inf_punctured_open@{o} N).

(* The preimage of a punctured open along the constant map at infinity is
   the whole point: the map lands at infinity, which every punctured open
   contains vacuously. *)
Definition point_into_punctured (N : nat) :
  point_whole ~{Opens Point_Top}~> open_preimage nat_inf_point
                                     (nat_inf_punctured N).
Proof. intros pt _ n Hn; discriminate Hn. Defined.

(** THE REFUTATION.  No left adjoint exists. *)
Theorem nat_inf_no_left_adjoint
  (L : Opens Point_Top ⟶ Opens NatInf_Top)
  (A : L ⊣ Opens_preimage nat_inf_point) : False.
Proof.
  (* Transposing the identity at [L point_whole] shows that open contains
     infinity, hence a tail from some N. *)
  pose proof (to (@adj _ _ _ _ A point_whole (L point_whole))
                (id[L point_whole])) as Hinf.
  destruct (`2 (L point_whole) (Hinf ttt ttt)) as [N k].
  (* Transposing the other way at the punctured open gives an inclusion
     of [L point_whole] into it, contradicted at [Some N]. *)
  pose proof (from (@adj _ _ _ _ A point_whole (nat_inf_punctured N))
                (point_into_punctured N)) as Hincl.
  exact (Hincl (Some N) (k N (PeanoNat.Nat.le_refl N)) N eq_refl eq_refl).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** (C) The right adjoint, AT THIS WITNESS *)

(* [R U] holds at infinity exactly when [U] holds at the point, and holds
   at every natural.  Open: if it contains infinity it contains the tail
   from 0, every natural being in it. *)
Definition nat_inf_R_pred (U : OpenSet Point_Top) :
  NatInf_Top → Type :=
  fun x => match x with
           | None   => `1 U ttt
           | Some _ => poly_unit
           end.

Lemma nat_inf_R_open (U : OpenSet Point_Top) :
  IsOpen NatInf_Top (nat_inf_R_pred U).
Proof. intros _; exists 0%nat; intros n _; exact ttt. Qed.

Program Definition nat_inf_right_adjoint :
  Opens Point_Top ⟶ Opens NatInf_Top := {|
  fobj := fun U => (nat_inf_R_pred U; nat_inf_R_open U);
  fmap := fun U V (h : ∀ pt : Point_Top, `1 U pt → `1 V pt) =>
            fun x => match x
                     return nat_inf_R_pred U x → nat_inf_R_pred V x with
                     | None   => h ttt
                     | Some _ => fun w => w
                     end
|}.

(* The transposition.  Both directions are one-line implications at
   infinity, and the point's own [ttt] is recovered by case analysis on
   [poly_unit]. *)
Program Definition nat_inf_preimage_adjunction :
  Opens_preimage nat_inf_point ⊣ nat_inf_right_adjoint := {|
  adj := fun U V =>
    {| to   := {| morphism := fun h x =>
                    match x
                    return `1 U x → nat_inf_R_pred V x with
                    | None   => h ttt
                    | Some _ => fun _ => ttt
                    end |}
     ; from := {| morphism := fun k pt (u : `1 U (nat_inf_point pt)) =>
                    match pt return `1 V pt with
                    | ttt => k None u
                    end |} |}
|}.

Example nat_inf_adjunction_left :
  Opens_preimage nat_inf_point ⊣ nat_inf_right_adjoint
  := nat_inf_preimage_adjunction.
