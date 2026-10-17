Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Construction.Cospan.Category.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Span_(category_theory)

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明拉回/推出、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CoprodCoverBridging.

Context {C : Category}.
Context `{H_Coc : @Cocartesian C}.

(** When you have [merge ∘ cover] 复合, you can bring the
 [inl/inr] selector across C-level: （已译） *)

Lemma merge_cover_inl
      {a b c d e : C}
      (m1 : c ~> e) (m2 : d ~> e)
      (h1 : a ~> c) (h2 : b ~> d) :
  (m1 ▽ m2) ∘ (cover h1 h2) ∘ inl ≈ m1 ∘ h1.
Proof.
  rewrite <- comp_assoc.
  rewrite cover_inl.
  rewrite comp_assoc.
  rewrite inl_merge.
  reflexivity.
Qed.

Lemma merge_cover_inr
      {a b c d e : C}
      (m1 : c ~> e) (m2 : d ~> e)
      (h1 : a ~> c) (h2 : b ~> d) :
  (m1 ▽ m2) ∘ (cover h1 h2) ∘ inr ≈ m2 ∘ h2.
Proof.
  rewrite <- comp_assoc.
  rewrite cover_inr.
  rewrite comp_assoc.
  rewrite inr_merge.
  reflexivity.
Qed.

(** Variant: [merge] composed [inl] right
 via two-step 复合, you can collapse directly. （已译） *)
Lemma merge_inl_assoc
      {a c d e : C} (m1 : c ~> e) (m2 : d ~> e) (h : a ~> c) :
  (m1 ▽ m2) ∘ inl ∘ h ≈ m1 ∘ h.
Proof.
  rewrite inl_merge; reflexivity.
Qed.

Lemma merge_inr_assoc
      {b c d e : C} (m1 : c ~> e) (m2 : d ~> e) (h : b ~> d) :
  (m1 ▽ m2) ∘ inr ∘ h ≈ m2 ∘ h.
Proof.
  rewrite inr_merge; reflexivity.
Qed.

End CoprodCoverBridging.

(*
   本节说明 Bridging 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CoprodJointEpi.

Context {C : Category}.
Context `{H_Coc : @Cocartesian C}.

(** Two 态射 out coproduct equal iff they agree on
 [inl] [inr]. （已译） *)
Lemma coprod_ext {a b c : C} (u v : a + b ~> c) :
  u ∘ inl ≈ v ∘ inl -> u ∘ inr ≈ v ∘ inr -> u ≈ v.
Proof.
  intros Hl Hr.
  (* u ≈ u ∘ id ≈ u ∘ (inl ▽ inr) ≈ (u ∘ inl) ▽ (u ∘ inr) *)
  rewrite <- (id_right u).
  rewrite <- merge_inl_inr.
  rewrite <- merge_comp.
  rewrite Hl, Hr.
  rewrite merge_comp.
  rewrite merge_inl_inr.
  rewrite id_right.
  reflexivity.
Qed.

End CoprodJointEpi.

(*
   本节说明 Bridging 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CospanEquivIntro.

Context {C : Category}.

Lemma cospan_equiv_intro {X Y : C}
      (f g : CospanArrow X Y)
      (phi : cospan_apex f ≅ cospan_apex g)
      (Hin1 : to phi ∘ cospan_in1 f ≈ cospan_in1 g)
      (Hin2 : to phi ∘ cospan_in2 f ≈ cospan_in2 g) :
  cospan_equiv f g.
Proof.
  exists phi; split; [exact Hin1 | exact Hin2].
Defined.

End CospanEquivIntro.

(* 相关说明。 （已译） *)

Section CospanComposeRewrites.

Context {C : Category}.
Context (HP : HasPushouts C).

Lemma cospan_compose_apex_eq {X Y Z : C}
      (g : CospanArrow Y Z) (f : CospanArrow X Y) :
  cospan_apex (cospan_compose HP g f)
  = pushout_apex (pushout (cospan_in2 f) (cospan_in1 g)).
Proof. reflexivity. Qed.

Lemma cospan_compose_in1_eq {X Y Z : C}
      (g : CospanArrow Y Z) (f : CospanArrow X Y) :
  cospan_in1 (cospan_compose HP g f)
  ≈ pushout_in1 (pushout (cospan_in2 f) (cospan_in1 g)) ∘ cospan_in1 f.
Proof. reflexivity. Qed.

Lemma cospan_compose_in2_eq {X Y Z : C}
      (g : CospanArrow Y Z) (f : CospanArrow X Y) :
  cospan_in2 (cospan_compose HP g f)
  ≈ pushout_in2 (pushout (cospan_in2 f) (cospan_in1 g)) ∘ cospan_in2 g.
Proof. reflexivity. Qed.

End CospanComposeRewrites.
