Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Bicartesian.Matrix.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/disjoint+coproduct
   nLab:      https://ncatlab.org/nlab/show/zero+object
   nLab:      https://ncatlab.org/nlab/show/subobject
   Wikipedia: https://en.wikipedia.org/wiki/Free_product

   本文件给出不相交子对象相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* * ** The arrow out zero 对象 monic （已译） *)

Section ZeroMonic.

Context {C : Category}.
Context `{Z : @ZeroObject C}.

(*
   本节说明同构、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma zero_initial_monic (w : C) : Monic (@zero C (@zero_initial C Z) w).
Proof.
  constructor; intros v g1 g2 _.
  transitivity (from (@zero_coincide C Z) ∘ (to (@zero_coincide C Z) ∘ g1)).
  - rewrite comp_assoc, iso_from_to; cat.
  - transitivity (from (@zero_coincide C Z) ∘ (to (@zero_coincide C Z) ∘ g2)).
    + apply compose_respects; [reflexivity|].
      apply (@one_unique C (@zero_terminal C Z)).
    + rewrite comp_assoc, iso_from_to; cat.
Qed.

End ZeroMonic.

(* 相关说明。 （已译） *)

Section CoproductMeet.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context `{CC : @Cocartesian C}.
Context `{PB : @HasPullbacks C}.
Context (x y : C).

(* 相关说明。 （已译） *)
Definition sub_inl : SubObj (x + y) :=
  {| sub_dom := x; sub_mono := inl; sub_is_monic := inl_Monic x y |}.

Definition sub_inr : SubObj (x + y) :=
  {| sub_dom := y; sub_mono := inr; sub_is_monic := inr_Monic x y |}.

(* The bottom subobject coproduct: zero 对象, included the
 arrow out it. （已译） *)
Definition coprod_bot : SubObj (x + y) :=
  @sub_bot C (@zero_initial C Z) (x + y) (zero_initial_monic (x + y)).

(* Each leg chosen pullback two injections zero
 态射: apply retraction [id ▽ zero_mor] (resp. [zero_mor ▽ id])
 交换方块. （已译） *)
Lemma inl_pullback_leg_zero :
  pullback_fst _ _ (pullback (@inl C CC x y) (@inr C CC x y)) ≈ zero_mor.
Proof.
  set (P := pullback (@inl C CC x y) (@inr C CC x y)).
  transitivity ((@id C x ▽ @zero_mor C Z y x) ∘ inl ∘ pullback_fst _ _ P).
  - rewrite inl_merge; cat.
  - rewrite <- comp_assoc, (pullback_commutes _ _ P), comp_assoc, inr_merge.
    apply zero_mor_right.
Qed.

Lemma inr_pullback_leg_zero :
  pullback_snd _ _ (pullback (@inl C CC x y) (@inr C CC x y)) ≈ zero_mor.
Proof.
  set (P := pullback (@inl C CC x y) (@inr C CC x y)).
  transitivity ((@zero_mor C Z x y ▽ @id C y) ∘ inr ∘ pullback_snd _ _ P).
  - rewrite inr_merge; cat.
  - rewrite <- comp_assoc, <- (pullback_commutes _ _ P), comp_assoc,
      inl_merge.
    apply zero_mor_right.
Qed.

Theorem coproduct_injections_meet_trivial :
  sub_meet sub_inl sub_inr ≈ coprod_bot.
Proof.
  apply sub_le_antisym.
  - exists (from (@zero_coincide C Z) ∘ @one C (@zero_terminal C Z) _).
    simpl.
    rewrite inl_pullback_leg_zero, zero_mor_left.
    unfold zero_mor; rewrite comp_assoc; reflexivity.
  - apply sub_bot_least.
Defined.

(* The same fact nLab's form: pullback two injections the
 zero 对象, read off 同构 subobject 等价
 carries. （已译） *)
Definition coproduct_injections_pullback_zero :
  Pull (@inl C CC x y) (@inr C CC x y) (pullback inl inr)
    ≅ @initial_obj C (@zero_initial C Z) :=
  `1 coproduct_injections_meet_trivial.

End CoproductMeet.
