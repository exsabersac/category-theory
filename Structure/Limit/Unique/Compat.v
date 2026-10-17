Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Span.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Limit.
Require Import Category.Structure.UniversalProperty.
Require Import Category.Structure.UniversalProperty.Limit.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Roof.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(*
   本文件给出极限相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Section EqualizerAgrees.

Context {C : Category}.
Context {x y : C}.
Context (f g : x ~{C}~> y).

(* An elementary equalizer, read as a limit witness pinned at its own
   apex, through Fork.v's bridge. *)
Definition is_equalizer_alimit {q : C} {e : q ~> x}
  (E : IsEqualizer f g q e) : IsALimit (APair f g) q :=
  limit_is_alimit (is_equalizer_limit f g E).

(*
   本节说明（余）极限、等化子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem equalizer_unique_agrees {q1 q2 : C} {e1 : q1 ~> x} {e2 : q2 ~> x}
  (E1 : IsEqualizer f g q1 e1) (E2 : IsEqualizer f g q2 e2) :
  to (equalizer_unique f g E1 E2)
    ≈ to (limit_unique_iso (is_equalizer_alimit E1)
                           (is_equalizer_alimit E2)).
Proof.
  apply limit_unique_iso_unique; intro p; destruct p; simpl.
  - exact (unique_property (eq_desc E2 e1 (fork_eq E1))).
  - transitivity (f ∘ (e2 ∘ unique_obj (eq_desc E2 e1 (fork_eq E1)))).
    { symmetry; apply comp_assoc. }
    now rewrite (unique_property (eq_desc E2 e1 (fork_eq E1))).
Qed.

(* 相关说明。 （已译） *)
Theorem equalizer_unique_agrees_iso {q1 q2 : C} {e1 : q1 ~> x}
  {e2 : q2 ~> x}
  (E1 : IsEqualizer f g q1 e1) (E2 : IsEqualizer f g q2 e2) :
  equalizer_unique f g E1 E2
    ≈ limit_unique_iso (is_equalizer_alimit E1) (is_equalizer_alimit E2).
Proof.
  apply to_equiv_implies_iso_equiv, equalizer_unique_agrees.
Qed.

End EqualizerAgrees.

(* 相关说明。 （已译） *)

Section PullbackAgrees.

Context {C : Category}.
Context {x y z : C}.
Context (f : x ~{C}~> z) (g : y ~{C}~> z).

(* A pullback square, read as a limit witness pinned at its own apex,
   through Pullback/Limit.v's bridge. *)
Definition pullback_alimit (P : Pullback f g) :
  IsALimit ((@ASpan (C^op) _ _ _ f g)^op) (Pull f g P) :=
  limit_is_alimit (Pullback_from_Universal f g P).

Theorem pullback_unique_agrees (P Q : Pullback f g) :
  to (pullback_unique P Q)
    ≈ to (limit_unique_iso (pullback_alimit P) (pullback_alimit Q)).
Proof.
  assert (T : to (pullback_unique P Q)
                ≈ unique_obj (ump_pullbacks f g Q (Pull f g P)
                     (pullback_fst f g P) (pullback_snd f g P)
                     (pullback_commutes f g P))).
  { unfold pullback_unique; simpl.
    destruct (unique_property
      (ump_pullbacks f g Q (Pull f g P) (pullback_fst f g P)
         (pullback_snd f g P) (pullback_commutes f g P))).
    destruct (unique_property
      (ump_pullbacks f g P (Pull f g Q) (pullback_fst f g Q)
         (pullback_snd f g Q) (pullback_commutes f g Q))).
    reflexivity. }
  rewrite T.
  destruct (unique_property
    (ump_pullbacks f g Q (Pull f g P) (pullback_fst f g P)
       (pullback_snd f g P) (pullback_commutes f g P))) as [HQfst HQsnd].
  apply limit_unique_iso_unique; intro r; destruct r.
  - exact HQfst.
  - transitivity
      (f ∘ (pullback_fst f g Q
              ∘ unique_obj (ump_pullbacks f g Q (Pull f g P)
                   (pullback_fst f g P) (pullback_snd f g P)
                   (pullback_commutes f g P)))).
    { symmetry; apply comp_assoc. }
    now rewrite HQfst.
  - exact HQsnd.
Qed.

Theorem pullback_unique_agrees_iso (P Q : Pullback f g) :
  pullback_unique P Q
    ≈ limit_unique_iso (pullback_alimit P) (pullback_alimit Q).
Proof.
  apply to_equiv_implies_iso_equiv, pullback_unique_agrees.
Qed.

End PullbackAgrees.

(* 相关说明。 （已译） *)

Section TransportUnique.

Context {J : Category}.
Context {C : Category}.
Context (F : J ⟶ C).

(*
   本节说明（余）极限、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition limit_unique_up_to_transport_iso
  (c d : C) (Hc : IsALimit F c) (Hd : IsALimit F d) :
  @Unique (@Isomorphism C^op c d) _
    (fun p =>
       @univ_property_respects_iso C^op (fun v => IsALimit F v)
         (fun v => @LimitSetoid J C F v)
         (LimitIsUniversalProperty J C F) c d p Hc ≈ Hd) :=
  @univ_property_unique_up_to_unique_iso C^op
    (fun v => IsALimit F v)
    (fun v => @LimitSetoid J C F v)
    (LimitIsUniversalProperty J C F) c d Hc Hd.

End TransportUnique.
