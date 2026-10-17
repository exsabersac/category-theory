Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(* * * The evaluation 函子 函子 范畴 （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/functor+category

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Evaluation.

Universe jo jh co ch.

Context {P : Category@{jo jh jh}} {X : Category@{co ch ch}}.

(* * ** The evaluation 函子 at fixed 对象 （已译） *)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Eval (p : P) : [P, X] ⟶ X := {|
  fobj := fun H => H p;
  fmap := fun _ _ s => transform[s] p
|}.

(** ** The two-variable evaluation *)

(*
   本节说明函子、Yoneda、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition EvalBi : ([P, X] ∏ P) ⟶ X := {|
  fobj := fun Hp => fst Hp (snd Hp);
  fmap := fun Hp Kq sf =>
            fmap[fst Kq] (snd sf) ∘ transform[fst sf] (snd Hp)
|}.
Next Obligation.
  proper; simpl in *.
  rewrite H, X0; reflexivity.
Qed.
Next Obligation.
  simpl in *.
  rewrite fmap_comp, <- !comp_assoc.
  apply compose_respects; [reflexivity |].
  rewrite comp_assoc, (naturality[t0] o1 o0 h), <- comp_assoc.
  reflexivity.
Qed.

(* * ** Partial application agrees fixed-对象 evaluation （已译） *)

(* On objects: on the nose. *)
Definition eval_partial_obj (p : P) (H : [P, X]) :
  fobj[Eval p] H = fobj[Partial_l EvalBi p] H := eq_refl.

(* On arrows: up ≈ — [Partial_l]'s action [bimap s id], which
 still carries [fmap id] 函子 law removes (probe). （已译） *)
Lemma eval_partial_map (p : P) (H K : [P, X]) (s : H ~{[P, X]}~> K) :
  fmap[Eval p] s ≈ fmap[Partial_l EvalBi p] s.
Proof. simpl; unfold bimap; simpl; cat. Qed.

(* Packaged as an isomorphism of functors in [[P, X], X], with identity
   components. *)
Program Definition eval_partial_iso (p : P) :
  @Isomorphism ([[P, X], X]) (Eval p) (Partial_l EvalBi p) := {|
  to   := {| transform := fun H => id |};
  from := {| transform := fun H => id |}
|}.

(* The other partial application 函子 itself. （已译） *)
Definition eval_partial_r_obj (H : [P, X]) (p : P) :
  fobj[Partial_r EvalBi H] p = fobj[H] p := eq_refl.

Lemma eval_partial_r_map (H : [P, X]) (p q : P) (f : p ~> q) :
  fmap[Partial_r EvalBi H] f ≈ fmap[H] f.
Proof. simpl; unfold bimap; simpl; cat. Qed.

(* * ** Naturality evaluated 对象 （已译） *)

(* Each arrow P gives transformation between evaluation 函子,
 component [fmap[H] f] at H; both 自然性 fields the
 自然性 transformation being evaluated. （已译） *)
Program Definition Eval_nat {p q : P} (f : p ~> q) : Eval p ⟹ Eval q := {|
  transform := fun H => fmap[H] f
|}.
Next Obligation. symmetry; apply naturality. Qed.
Next Obligation. apply naturality. Qed.

(* Assembled: evaluation is a functor P ⟶ [[P, X], X]. *)
Program Definition EvalFunctor : P ⟶ [[P, X], X] := {|
  fobj := Eval;
  fmap := fun _ _ f => Eval_nat f
|}.
Next Obligation. proper; rewrite X0; reflexivity. Qed.
Next Obligation. apply fmap_comp. Qed.

(* Its actions read back on the nose. *)
Definition EvalFunctor_obj (p : P) : fobj[EvalFunctor] p = Eval p := eq_refl.

Definition EvalFunctor_map {p q : P} (f : p ~> q) (H : [P, X]) :
  transform[fmap[EvalFunctor] f] H = fmap[H] f := eq_refl.

End Evaluation.

Arguments Eval {P X} p.
Arguments EvalBi {P X}.
Arguments EvalFunctor {P X}.
