Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.

Generalizable All Variables.

(** * Pushouts: ergonomic accessors *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Pushout_(category_theory)

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Pushout.

Context {C : Category}.

(** Pushout of the span [y <-f- x -g-> z]. *)
Definition IsPushout {x y z : C} (f : x ~> y) (g : x ~> z) : Type :=
  @Pullback (C^op) y z x f g.

Definition pushout_apex {x y z : C} {f : x ~> y} {g : x ~> z}
           (P : IsPushout f g) : C :=
  @Pull (C^op) y z x f g P.

Definition pushout_in1 {x y z : C} {f : x ~> y} {g : x ~> z}
           (P : IsPushout f g) : y ~{C}~> pushout_apex P :=
  @pullback_fst (C^op) y z x f g P.

Definition pushout_in2 {x y z : C} {f : x ~> y} {g : x ~> z}
           (P : IsPushout f g) : z ~{C}~> pushout_apex P :=
  @pullback_snd (C^op) y z x f g P.

(** 本节：The square commutes: both legs precomposed span agree. （已译） *)
Lemma pushout_commutes {x y z : C} {f : x ~> y} {g : x ~> z}
      (P : IsPushout f g) :
  pushout_in1 P ∘ f ≈ pushout_in2 P ∘ g.
Proof.
  exact (@pullback_commutes (C^op) y z x f g P).
Qed.

(** The 普遍性质: given any other cocone over same span there
 unique mediating 态射 pushout apex. （已译） *)
Lemma pushout_ump {x y z : C} {f : x ~> y} {g : x ~> z}
      (P : IsPushout f g)
      (Q : C) (q1 : y ~> Q) (q2 : z ~> Q)
      (Hcomm : q1 ∘ f ≈ q2 ∘ g) :
  ∃! u : pushout_apex P ~> Q,
    u ∘ pushout_in1 P ≈ q1 ∧ u ∘ pushout_in2 P ≈ q2.
Proof.
  exact (@ump_pullbacks (C^op) y z x f g P Q q1 q2 Hcomm).
Qed.

(** Convenience: the mediating morphism out of a pushout. *)
Definition pushout_med {x y z : C} {f : x ~> y} {g : x ~> z}
           (P : IsPushout f g)
           {Q : C} {q1 : y ~> Q} {q2 : z ~> Q}
           (Hcomm : q1 ∘ f ≈ q2 ∘ g)
  : pushout_apex P ~> Q :=
  unique_obj (pushout_ump P Q q1 q2 Hcomm).

Lemma pushout_med_in1 {x y z : C} {f : x ~> y} {g : x ~> z}
      (P : IsPushout f g)
      {Q : C} {q1 : y ~> Q} {q2 : z ~> Q}
      (Hcomm : q1 ∘ f ≈ q2 ∘ g) :
  pushout_med P Hcomm ∘ pushout_in1 P ≈ q1.
Proof.
  unfold pushout_med.
  destruct (unique_property (pushout_ump P Q q1 q2 Hcomm)) as [H _].
  exact H.
Qed.

Lemma pushout_med_in2 {x y z : C} {f : x ~> y} {g : x ~> z}
      (P : IsPushout f g)
      {Q : C} {q1 : y ~> Q} {q2 : z ~> Q}
      (Hcomm : q1 ∘ f ≈ q2 ∘ g) :
  pushout_med P Hcomm ∘ pushout_in2 P ≈ q2.
Proof.
  unfold pushout_med.
  destruct (unique_property (pushout_ump P Q q1 q2 Hcomm)) as [_ H].
  exact H.
Qed.

Lemma pushout_med_unique {x y z : C} {f : x ~> y} {g : x ~> z}
      (P : IsPushout f g)
      {Q : C} {q1 : y ~> Q} {q2 : z ~> Q}
      (Hcomm : q1 ∘ f ≈ q2 ∘ g)
      (v : pushout_apex P ~> Q) :
  v ∘ pushout_in1 P ≈ q1 -> v ∘ pushout_in2 P ≈ q2 ->
  pushout_med P Hcomm ≈ v.
Proof.
  intros H1 H2.
  unfold pushout_med.
  apply (uniqueness (pushout_ump P Q q1 q2 Hcomm)); split; assumption.
Qed.

(** Equality 引理: two mediators out pushout agree both
 pushout legs equal. Useful showing [u ≈ v] without
 exhibiting intermediate [pushout_med] explicitly. （已译） *)
Lemma pushout_med_eq {x y z : C} {f : x ~> y} {g : x ~> z}
      (P : IsPushout f g)
      {Q : C} {q1 : y ~> Q} {q2 : z ~> Q}
      (Hcomm : q1 ∘ f ≈ q2 ∘ g)
      (u v : pushout_apex P ~> Q) :
  u ∘ pushout_in1 P ≈ q1 ->
  u ∘ pushout_in2 P ≈ q2 ->
  v ∘ pushout_in1 P ≈ q1 ->
  v ∘ pushout_in2 P ≈ q2 ->
  u ≈ v.
Proof.
  intros Hu1 Hu2 Hv1 Hv2.
  transitivity (pushout_med P Hcomm).
  - symmetry. apply pushout_med_unique; assumption.
  - apply pushout_med_unique; assumption.
Qed.

End Pushout.

(** A category has all binary pushouts if every span has a pushout. *)
Class HasPushouts (C : Category) : Type := {
  pushout : forall {x y z : C} (f : x ~> y) (g : x ~> z), IsPushout f g
                                        (* a chosen pushout for every span *)
}.

Arguments pushout {C _ x y z} f g.

(* * [HasPushouts C] is exactly [HasPullbacks (C^op)] definitional
 unfolding [IsPushout]. We expose both directions 等价
 as functions so two predicates can be interchanged at will.（已译） *)
Definition HasPullbacks_op_of_HasPushouts
           {C : Category} (HP : HasPushouts C) : HasPullbacks (C^op).
Proof.
  unshelve econstructor.
  intros x y z f g.
  (* A pullback in C^op of f : x ~{C^op}~> z, g : y ~{C^op}~> z is a pushout in
     C of f : z ~{C}~> x, g : z ~{C}~> y; the latter is supplied by [HP]. *)
  exact (@pushout C HP z x y f g).
Defined.

Definition HasPushouts_of_HasPullbacks_op
           {C : Category} (HP : HasPullbacks (C^op)) : HasPushouts C.
Proof.
  unshelve econstructor.
  intros x y z f g.
  exact (@pullback (C^op) HP y z x f g).
Defined.
