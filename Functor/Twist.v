Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
From Coq Require Import Eqdep_dec.

Generalizable All Variables.

(* * * Twisting 函子 family isomorphisms （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/natural+isomorphism

   本文件给出函子相关定义或实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Twist.

Context {C : Category}.
Context (F : C ⟶ C).
Context (α : ∀ x : C, x ≅ F x).

#[local] Obligation Tactic := idtac.

(* The twisted 函子. Note [fobj := fun x => x]: 对象 function is
 恒等 function itself, not merely function isomorphic it. （已译） *)
Program Definition Twist : C ⟶ C := {|
  fobj := fun x => x;
  fmap := fun x y f => (α y)⁻¹ ∘ fmap[F] f ∘ α x
|}.
Next Obligation.
  intros x y f g Hfg.
  now rewrite Hfg.
Qed.
Next Obligation.
  intros x; simpl.
  rewrite fmap_id, id_right.
  apply iso_from_to.
Qed.
Next Obligation.
  intros x y z f g; simpl.
  rewrite fmap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity |].
  rewrite (comp_assoc (α y)).
  rewrite iso_to_from, id_left.
  reflexivity.
Qed.

(*
   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Twist_fobj (x : C) : fobj[Twist] x = x.
Proof. reflexivity. Qed.

(* If α natural, twist strictly equal 恒等 函子:
 对象 equalities all [eq_refl], arrow condition is
 α cancelling itself across f. （已译） *)
Theorem Twist_natural_strict_id
  (nat : ∀ (x y : C) (f : x ~> y), α y ∘ f ≈ fmap[F] f ∘ α x) :
  @equiv _ Functor_StrictEq_Setoid Twist (@Id C).
Proof.
  exists (fun _ => eq_refl).
  intros x y f.
  (* Both transports along [eq_refl], hence 恒等, so the
 coherence condition reduces conversion arrow maps agreeing. （已译） *)
  change ((α y)⁻¹ ∘ fmap[F] f ∘ α x ≈ f).
  rewrite <- comp_assoc.
  rewrite <- nat.
  rewrite comp_assoc.
  rewrite iso_from_to.
  apply id_left.
Qed.

(*
   本节说明 Twist 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Twist_strict_id_natural
  (uip : ∀ (x : C) (p : x = x), p = eq_refl)
  (H : @equiv _ Functor_StrictEq_Setoid Twist (@Id C)) :
  ∀ (x y : C) (f : x ~> y), α y ∘ f ≈ fmap[F] f ∘ α x.
Proof.
  destruct H as [eq_on_obj coherent].
  intros x y f.
  pose proof (coherent x y f) as Hc.
  rewrite (uip x (eq_on_obj x)), (uip y (eq_on_obj y)) in Hc.
  (* with both 对象 equalities [eq_refl] transports vanish （已译） *)
  assert (Hred : (α y)⁻¹ ∘ fmap[F] f ∘ α x ≈ f) by exact Hc.
  assert (Hpost : α y ∘ ((α y)⁻¹ ∘ fmap[F] f ∘ α x) ≈ α y ∘ f)
    by (apply compose_respects; [ reflexivity | exact Hred ]).
  rewrite <- Hpost.
  rewrite !comp_assoc.
  rewrite iso_to_from, id_left.
  reflexivity.
Qed.

(* The distinctness criterion form it used: SINGLE 态射 at
 α not natural separates twist 恒等 in
 strict 函子 setoid. （已译） *)
Corollary Twist_not_strict_id
  (uip : ∀ (x : C) (p : x = x), p = eq_refl)
  {x y : C} {f : x ~> y}
  (Hnat : α y ∘ f ≈ fmap[F] f ∘ α x → False) :
  @equiv _ Functor_StrictEq_Setoid Twist (@Id C) → False.
Proof.
  intro H.
  exact (Hnat (Twist_strict_id_natural uip H x y f)).
Qed.

End Twist.

Arguments Twist {C} F α.

(*
   本节说明 Twist 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition uip_of_dec {A : Type}
  (dec : ∀ x y : A, {x = y} + {x <> y}) (x : A) (p : x = x) : p = eq_refl :=
  UIP_dec dec p eq_refl.

Section TwistId.

Context {C : Category}.
Context (α : ∀ x : C, x ≅ x).

(*
   本节说明函子、hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Twist_Id_weak_equiv :
  @equiv _ Functor_Setoid (Twist (@Id C) α) (@Id C).
Proof.
  exists α.
  intros x y f; simpl.
  reflexivity.
Qed.

End TwistId.
