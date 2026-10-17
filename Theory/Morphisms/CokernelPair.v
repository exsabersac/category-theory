Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Morphisms.Duality.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/cokernel+pair
   Wikipedia: https://en.wikipedia.org/wiki/Epimorphism

   本文件给出余核对相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Section PushoutSquare.

Context {C : Category}.

(*
   本节说明拉回/推出、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition IsPushoutSquare {x y z : C} (f : x ~> y) (g : x ~> z)
           (P : C) (i1 : y ~> P) (i2 : z ~> P) : Type :=
  @IsPullback (C^op) y z x f g P i1 i2.

Section Accessors.

Context {x y z : C} {f : x ~> y} {g : x ~> z}.
Context {P : C} {i1 : y ~> P} {i2 : z ~> P}.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Build_IsPushoutSquare
           (Hcomm : i1 ∘ f ≈ i2 ∘ g)
           (Hump : ∀ (Q : C) (q1 : y ~> Q) (q2 : z ~> Q),
               q1 ∘ f ≈ q2 ∘ g →
               ∃! u : P ~> Q, u ∘ i1 ≈ q1 ∧ u ∘ i2 ≈ q2)
  : IsPushoutSquare f g P i1 i2 :=
  @Build_IsPullback (C^op) y z x f g P i1 i2 Hcomm Hump.

(* Both field readings are definitional: supplied by [:=], no tactic. *)

Definition is_pushout_square_commutes (H : IsPushoutSquare f g P i1 i2) :
  i1 ∘ f ≈ i2 ∘ g := is_pullback_commutes H.

Definition is_pushout_square_ump (H : IsPushoutSquare f g P i1 i2)
           (Q : C) (q1 : y ~> Q) (q2 : z ~> Q) (Hc : q1 ∘ f ≈ q2 ∘ g) :
  ∃! u : P ~> Q, u ∘ i1 ≈ q1 ∧ u ∘ i2 ≈ q2 :=
  is_pullback_ump H Q q1 q2 Hc.

(** *** The mediator kit *)

Definition pushout_square_med (H : IsPushoutSquare f g P i1 i2)
           {Q : C} {q1 : y ~> Q} {q2 : z ~> Q} (Hc : q1 ∘ f ≈ q2 ∘ g)
  : P ~> Q := unique_obj (is_pushout_square_ump H Q q1 q2 Hc).

Lemma pushout_square_med_in1 (H : IsPushoutSquare f g P i1 i2)
      {Q : C} {q1 : y ~> Q} {q2 : z ~> Q} (Hc : q1 ∘ f ≈ q2 ∘ g) :
  pushout_square_med H Hc ∘ i1 ≈ q1.
Proof.
  exact (fst (unique_property (is_pushout_square_ump H Q q1 q2 Hc))).
Qed.

Lemma pushout_square_med_in2 (H : IsPushoutSquare f g P i1 i2)
      {Q : C} {q1 : y ~> Q} {q2 : z ~> Q} (Hc : q1 ∘ f ≈ q2 ∘ g) :
  pushout_square_med H Hc ∘ i2 ≈ q2.
Proof.
  exact (snd (unique_property (is_pushout_square_ump H Q q1 q2 Hc))).
Qed.

Lemma pushout_square_med_unique (H : IsPushoutSquare f g P i1 i2)
      {Q : C} {q1 : y ~> Q} {q2 : z ~> Q} (Hc : q1 ∘ f ≈ q2 ∘ g)
      (v : P ~> Q) :
  v ∘ i1 ≈ q1 -> v ∘ i2 ≈ q2 -> pushout_square_med H Hc ≈ v.
Proof.
  intros H1 H2.
  apply (uniqueness (is_pushout_square_ump H Q q1 q2 Hc)); split; assumption.
Qed.

(* Two mediators agreeing on both legs are equal. *)
Lemma pushout_square_med_eq (H : IsPushoutSquare f g P i1 i2)
      {Q : C} {q1 : y ~> Q} {q2 : z ~> Q} (Hc : q1 ∘ f ≈ q2 ∘ g)
      (u v : P ~> Q) :
  u ∘ i1 ≈ q1 -> u ∘ i2 ≈ q2 -> v ∘ i1 ≈ q1 -> v ∘ i2 ≈ q2 -> u ≈ v.
Proof.
  intros Hu1 Hu2 Hv1 Hv2.
  transitivity (pushout_square_med H Hc).
  - symmetry; apply pushout_square_med_unique; assumption.
  - apply pushout_square_med_unique; assumption.
Qed.

End Accessors.

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition pushout_is_pushout_square {x y z : C}
           (f : x ~> y) (g : x ~> z) (P : IsPushout f g) :
  IsPushoutSquare f g (pushout_apex P) (pushout_in1 P) (pushout_in2 P) :=
  @pullback_is_pullback (C^op) y z x f g P.

Definition is_pushout_square_pushout {x y z : C}
           {f : x ~> y} {g : x ~> z}
           {P : C} {i1 : y ~> P} {i2 : z ~> P}
           (H : IsPushoutSquare f g P i1 i2) : IsPushout f g :=
  @is_pullback_pullback (C^op) y z x f g P i1 i2 H.

End PushoutSquare.

Arguments IsPushoutSquare {C x y z} f g P i1 i2.

(** ** The cokernel pair *)

(*
   本节说明拉回/推出、核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition cokernel_pair {C : Category} `{H : @HasPushouts C} {x y : C}
  (f : x ~> y) : IsPushout f f := pushout f f.

(* 相关说明。 （已译） *)
Definition IsCokernelPair {C : Category} {x y : C} (f : x ~> y)
           (P : C) (u v : y ~> P) : Type := IsPushoutSquare f f P u v.

Section CokernelPairAccessors.

Context {C : Category}.
Context {x y : C}.
Context {f : x ~> y}.

(* 相关说明。 （已译） *)
Context (P : IsPushout f f).

Definition ckp_obj : C := pushout_apex P.

(* The parallel pair. Both legs run y ~> ckp_obj: 这是 what makes the
 cokernel pair PARALLEL PAIR rather than general cocone. （已译） *)
Definition ckp_left : y ~> ckp_obj := pushout_in1 P.
Definition ckp_right : y ~> ckp_obj := pushout_in2 P.

(* The defining equation. *)
Lemma ckp_commutes : ckp_left ∘ f ≈ ckp_right ∘ f.
Proof. exact (pushout_commutes P). Qed.

(* The universal property, stated on PARALLEL PAIRS COEQUALIZING f. *)
Lemma ckp_ump (Q : C) (q1 q2 : y ~> Q) (Hc : q1 ∘ f ≈ q2 ∘ f) :
  ∃! u : ckp_obj ~> Q, u ∘ ckp_left ≈ q1 ∧ u ∘ ckp_right ≈ q2.
Proof. exact (pushout_ump P Q q1 q2 Hc). Qed.

Definition ckp_med {Q : C} {q1 q2 : y ~> Q} (Hc : q1 ∘ f ≈ q2 ∘ f)
  : ckp_obj ~> Q := pushout_med P Hc.

Lemma ckp_med_left {Q : C} {q1 q2 : y ~> Q} (Hc : q1 ∘ f ≈ q2 ∘ f) :
  ckp_med Hc ∘ ckp_left ≈ q1.
Proof. exact (pushout_med_in1 P Hc). Qed.

Lemma ckp_med_right {Q : C} {q1 q2 : y ~> Q} (Hc : q1 ∘ f ≈ q2 ∘ f) :
  ckp_med Hc ∘ ckp_right ≈ q2.
Proof. exact (pushout_med_in2 P Hc). Qed.

Lemma ckp_med_unique {Q : C} {q1 q2 : y ~> Q} (Hc : q1 ∘ f ≈ q2 ∘ f)
      (v : ckp_obj ~> Q) :
  v ∘ ckp_left ≈ q1 -> v ∘ ckp_right ≈ q2 -> ckp_med Hc ≈ v.
Proof. exact (pushout_med_unique P Hc v). Qed.

Lemma ckp_med_eq {Q : C} {q1 q2 : y ~> Q} (Hc : q1 ∘ f ≈ q2 ∘ f)
      (u v : ckp_obj ~> Q) :
  u ∘ ckp_left ≈ q1 -> u ∘ ckp_right ≈ q2 ->
  v ∘ ckp_left ≈ q1 -> v ∘ ckp_right ≈ q2 -> u ≈ v.
Proof. exact (pushout_med_eq P Hc u v). Qed.

(* 相关说明。 （已译） *)
Definition ckp_IsCokernelPair : IsCokernelPair f ckp_obj ckp_left ckp_right :=
  pushout_is_pushout_square f f P.

End CokernelPairAccessors.

Arguments ckp_obj {C x y f} P.
Arguments ckp_left {C x y f} P.
Arguments ckp_right {C x y f} P.

(* * ** Epimorphisms exactly 恒等 pushout squares （已译） *)

Section EpiCharacterization.

Context {C : Category}.
Context {x y : C}.
Context (f : x ~> y).

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition epic_pushout_square (E : Epic f) : IsPushoutSquare f f y id id.
Proof.
  destruct E as [cancel].
  unshelve eapply Build_IsPushoutSquare.
  - (* the square commutes, trivially *)
    reflexivity.
  - intros Q q1 q2 Hc.
    assert (Hq : q1 ≈ q2) by (apply cancel; exact Hc).
    unshelve refine {| unique_obj := q1 |}.
    + split.
      * apply id_right.
      * rewrite id_right; exact Hq.
    + intros v [Hv1 _].
      rewrite <- Hv1, id_right; reflexivity.
Defined.

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition pushout_square_epic (H : IsPushoutSquare f f y id id) : Epic f.
Proof.
  constructor.
  intros z g1 g2 Hg.
  pose proof (is_pushout_square_ump H z g1 g2 Hg) as U.
  destruct (unique_property U) as [U1 U2].
  rewrite <- U1, <- U2; reflexivity.
Defined.

Theorem epic_iff_pushout_square : Epic f ↔ IsPushoutSquare f f y id id.
Proof. split; [ exact epic_pushout_square | exact pushout_square_epic ]. Qed.

(* 相关说明。 （已译） *)

Context (P : IsPushout f f).

(* Forward: right cancellation applied to [ckp_commutes]. *)
Lemma epic_ckp_trivial (E : Epic f) : ckp_left P ≈ ckp_right P.
Proof.
  destruct E as [cancel].
  apply cancel.
  exact (ckp_commutes P).
Qed.

(* 相关说明。 （已译） *)
Lemma ckp_trivial_epic (Ht : ckp_left P ≈ ckp_right P) : Epic f.
Proof.
  constructor.
  intros z g1 g2 Hg.
  transitivity (ckp_med P Hg ∘ ckp_left P).
  - symmetry; exact (ckp_med_left P Hg).
  - rewrite Ht.
    exact (ckp_med_right P Hg).
Qed.

Theorem epic_iff_cokernel_pair_trivial :
  Epic f ↔ ckp_left P ≈ ckp_right P.
Proof. split; [ exact epic_ckp_trivial | exact ckp_trivial_epic ]. Qed.

(* * *** The same at full strength: left leg 同构 （已译） *)

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma epic_ckp_left_iso (E : Epic f) : IsIsomorphism (ckp_left P).
Proof.
  assert (Hid : id[y] ∘ f ≈ id[y] ∘ f) by reflexivity.
  unshelve refine {| two_sided_inverse := ckp_med P Hid |}.
  - (* ckp_left ∘ med ≈ id, by agreeing with id on both legs *)
    apply (ckp_med_eq P (ckp_commutes P)).
    + rewrite <- comp_assoc, (ckp_med_left P Hid); apply id_right.
    + rewrite <- comp_assoc, (ckp_med_right P Hid), id_right.
      exact (epic_ckp_trivial E).
    + apply id_left.
    + apply id_left.
  - (* med ∘ ckp_left ≈ id *)
    exact (ckp_med_left P Hid).
Qed.

(* Conversely, invertible left leg forces two legs agree: the
 self-cocone (ckp_left, ckp_left) mediated 态射 the
 invertibility pins 恒等. （已译） *)
Lemma ckp_left_iso_epic (I : IsIsomorphism (ckp_left P)) : Epic f.
Proof.
  destruct I as [k Hk1 Hk2].
  apply ckp_trivial_epic.
  assert (Hc : ckp_left P ∘ f ≈ ckp_left P ∘ f) by reflexivity.
  (* The self-mediator cocone (ckp_left, ckp_left) forced be
 恒等, because it 恒等 after invertible leg. （已译） *)
  assert (Hw : ckp_med P Hc ≈ id).
  { transitivity (ckp_med P Hc ∘ (ckp_left P ∘ k)).
    - rewrite Hk1, id_right; reflexivity.
    - rewrite comp_assoc, (ckp_med_left P Hc); exact Hk1. }
  (* The mediator carries RIGHT leg left one, being the
 恒等 it carries it itself. （已译） *)
  symmetry.
  transitivity (ckp_med P Hc ∘ ckp_right P).
  - rewrite Hw, id_left; reflexivity.
  - exact (ckp_med_right P Hc).
Qed.

Theorem epic_iff_cokernel_pair_left_iso :
  Epic f ↔ IsIsomorphism (ckp_left P).
Proof. split; [ exact epic_ckp_left_iso | exact ckp_left_iso_epic ]. Qed.

End EpiCharacterization.

Arguments epic_iff_pushout_square {C x y} f.
Arguments epic_iff_cokernel_pair_trivial {C x y} f P.
Arguments epic_iff_cokernel_pair_left_iso {C x y} f P.

(*
   本节说明拉回/推出、核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition epic_iff_chosen_ckp_trivial {C : Category}
           `{H : @HasPushouts C} {x y : C} (f : x ~> y) :
  Epic f ↔ ckp_left (cokernel_pair f) ≈ ckp_right (cokernel_pair f) :=
  epic_iff_cokernel_pair_trivial f (cokernel_pair f).

Definition epic_iff_chosen_ckp_left_iso {C : Category}
           `{H : @HasPushouts C} {x y : C} (f : x ~> y) :
  Epic f ↔ IsIsomorphism (ckp_left (cokernel_pair f)) :=
  epic_iff_cokernel_pair_left_iso f (cokernel_pair f).

(*
   本节说明 CokernelPair 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section OpConversions.

Context {C : Category}.
Context {x y : C}.
Context (f : x ~> y).

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition op_collapse_pushout_square :
  @IsPushoutSquare (C^op) y x x f f x id id
    = @IsPullback C x x y f f x id id := eq_refl.

(*
   本节说明拉回/推出、核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition op_collapse_cokernel_pair :
  @IsPushout (C^op) y x x f f = @Pullback C x x y f f := eq_refl.

Definition op_collapse_ckp_left (P : Pullback f f) :
  @ckp_left (C^op) y x f P = pullback_fst f f P := eq_refl.

Definition op_collapse_ckp_right (P : Pullback f f) :
  @ckp_right (C^op) y x f P = pullback_snd f f P := eq_refl.

(*
   本节说明 CokernelPair 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition IsIsomorphism_of_op {a b : C} (h : b ~> a)
           (I : @IsIsomorphism (C^op) a b h) : @IsIsomorphism C b a h :=
  @Build_IsIsomorphism C b a h
    (@two_sided_inverse (C^op) a b h I)
    (@is_left_inverse (C^op) a b h I)
    (@is_right_inverse (C^op) a b h I).

Definition op_IsIsomorphism_of {a b : C} (h : b ~> a)
           (I : @IsIsomorphism C b a h) : @IsIsomorphism (C^op) a b h :=
  @Build_IsIsomorphism (C^op) a b h
    (@two_sided_inverse C b a h I)
    (@is_left_inverse C b a h I)
    (@is_right_inverse C b a h I).

End OpConversions.

Section MonoCharacterization.

Context {C : Category}.
Context {x y : C}.
Context (f : x ~> y).

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem monic_iff_pullback_square : Monic f ↔ IsPullback f f x id id.
Proof.
  split.
  - intro M.
    exact (epic_pushout_square (C:=C^op) f (op_Epic_of_Monic f M)).
  - intro H.
    exact (Monic_of_op_Epic f (pushout_square_epic (C:=C^op) f H)).
Qed.

(*
   本节说明拉回/推出、核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem monic_iff_kernel_pair_trivial (P : Pullback f f) :
  Monic f ↔ pullback_fst f f P ≈ pullback_snd f f P.
Proof.
  split.
  - intro M.
    exact (epic_ckp_trivial (C:=C^op) f P (op_Epic_of_Monic f M)).
  - intro Ht.
    exact (Monic_of_op_Epic f (ckp_trivial_epic (C:=C^op) f P Ht)).
Qed.

(* Stated in C, not in C^op: the projection is an isomorphism there. *)
Theorem monic_iff_kernel_pair_fst_iso (P : Pullback f f) :
  Monic f ↔ IsIsomorphism (pullback_fst f f P).
Proof.
  split.
  - intro M.
    exact (IsIsomorphism_of_op _
             (epic_ckp_left_iso (C:=C^op) f P (op_Epic_of_Monic f M))).
  - intro I.
    exact (Monic_of_op_Epic f
             (ckp_left_iso_epic (C:=C^op) f P (op_IsIsomorphism_of _ I))).
Qed.

End MonoCharacterization.
