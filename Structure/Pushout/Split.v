Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.

Generalizable All Variables.

(** * When a pushout injection splits *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Pushout_(category_theory)

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section PushoutSplit.

Context {C : Category}.
Context {x y z : C}.
Context {f : x ~> y} {g : x ~> z}.
Context (P : IsPushout f g).

(** ** The first injection *)

(* If [f] factors through [g], the cocone [(id[y], r)] commutes, so the
   pushout hands back a retraction of [pushout_in1]. *)
Lemma pushout_in1_factor_commutes (r : z ~> y) (Hr : r ∘ g ≈ f) :
  id[y] ∘ f ≈ r ∘ g.
Proof.
  rewrite id_left.
  symmetry.
  exact Hr.
Qed.

Definition pushout_in1_retract (r : z ~> y) (Hr : r ∘ g ≈ f)
  : pushout_apex P ~> y :=
  pushout_med P (pushout_in1_factor_commutes r Hr).

Lemma pushout_in1_retract_comp (r : z ~> y) (Hr : r ∘ g ≈ f) :
  pushout_in1_retract r Hr ∘ pushout_in1 P ≈ id.
Proof.
  unfold pushout_in1_retract.
  exact (pushout_med_in1 P (pushout_in1_factor_commutes r Hr)).
Qed.

Definition pushout_in1_Section (r : z ~> y) (Hr : r ∘ g ≈ f)
  : Section (pushout_in1 P) :=
  {| section      := pushout_in1_retract r Hr
   ; section_comp := pushout_in1_retract_comp r Hr |}.

Lemma pushout_in1_Monic (r : z ~> y) (Hr : r ∘ g ≈ f) :
  Monic (pushout_in1 P).
Proof.
  apply sections_are_monic.
  exact (pushout_in1_Section r Hr).
Qed.

(** ** The second injection *)

Lemma pushout_in2_factor_commutes (s : y ~> z) (Hs : s ∘ f ≈ g) :
  s ∘ f ≈ id[z] ∘ g.
Proof.
  rewrite id_left.
  exact Hs.
Qed.

Definition pushout_in2_retract (s : y ~> z) (Hs : s ∘ f ≈ g)
  : pushout_apex P ~> z :=
  pushout_med P (pushout_in2_factor_commutes s Hs).

Lemma pushout_in2_retract_comp (s : y ~> z) (Hs : s ∘ f ≈ g) :
  pushout_in2_retract s Hs ∘ pushout_in2 P ≈ id.
Proof.
  unfold pushout_in2_retract.
  exact (pushout_med_in2 P (pushout_in2_factor_commutes s Hs)).
Qed.

Definition pushout_in2_Section (s : y ~> z) (Hs : s ∘ f ≈ g)
  : Section (pushout_in2 P) :=
  {| section      := pushout_in2_retract s Hs
   ; section_comp := pushout_in2_retract_comp s Hs |}.

Lemma pushout_in2_Monic (s : y ~> z) (Hs : s ∘ f ≈ g) :
  Monic (pushout_in2 P).
Proof.
  apply sections_are_monic.
  exact (pushout_in2_Section s Hs).
Qed.

End PushoutSplit.

(*
   本节说明 Split 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition pushout_in1_Section_of_Retraction
           {C : Category} {x y z : C} {f : x ~> y} {g : x ~> z}
           (P : IsPushout f g) (Sg : Section g)
  : Section (pushout_in1 P).
Proof.
  unshelve refine (pushout_in1_Section P (f ∘ section) _).
  rewrite <- comp_assoc.
  rewrite section_comp.
  apply id_right.
Defined.

Definition pushout_in2_Section_of_Retraction
           {C : Category} {x y z : C} {f : x ~> y} {g : x ~> z}
           (P : IsPushout f g) (Sf : Section f)
  : Section (pushout_in2 P).
Proof.
  unshelve refine (pushout_in2_Section P (g ∘ section) _).
  rewrite <- comp_assoc.
  rewrite section_comp.
  apply id_right.
Defined.

Lemma pushout_in1_Monic_of_Retraction
      {C : Category} {x y z : C} {f : x ~> y} {g : x ~> z}
      (P : IsPushout f g) (Sg : Section g) :
  Monic (pushout_in1 P).
Proof.
  apply sections_are_monic.
  exact (pushout_in1_Section_of_Retraction P Sg).
Qed.

Lemma pushout_in2_Monic_of_Retraction
      {C : Category} {x y z : C} {f : x ~> y} {g : x ~> z}
      (P : IsPushout f g) (Sf : Section f) :
  Monic (pushout_in2 P).
Proof.
  apply sections_are_monic.
  exact (pushout_in2_Section_of_Retraction P Sf).
Qed.

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition pushout_both_Section
           {C : Category} {x y z : C} {f : x ~> y} {g : x ~> z}
           (P : IsPushout f g) (Sf : Section f) (Sg : Section g)
  : Section (pushout_in1 P) * Section (pushout_in2 P) :=
  (pushout_in1_Section_of_Retraction P Sg,
   pushout_in2_Section_of_Retraction P Sf).

Lemma pushout_both_Monic
      {C : Category} {x y z : C} {f : x ~> y} {g : x ~> z}
      (P : IsPushout f g) (Sf : Section f) (Sg : Section g) :
  Monic (pushout_in1 P) * Monic (pushout_in2 P).
Proof.
  exact (pushout_in1_Monic_of_Retraction P Sg,
         pushout_in2_Monic_of_Retraction P Sf).
Qed.
