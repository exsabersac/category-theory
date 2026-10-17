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

(** * The evaluation functor on a functor category *)

(*
 nLab: https://ncatlab.org/nlab/show/functor+category

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Evaluation.

Universe jo jh co ch.

Context {P : Category@{jo jh jh}} {X : Category@{co ch ch}}.

(** ** The evaluation functor at a fixed object *)

(* Mac Lane §V.3's E_c : [P, X] ⟶ X — objects to their value at p,
   transformations to their component at p.  The same data as
   Adjunction/Diagonal/Connected.v's [EvalAt] (measured, see the header);
   declared here in the light home the issue asks for. *)
Program Definition Eval (p : P) : [P, X] ⟶ X := {|
  fobj := fun H => H p;
  fmap := fun _ _ s => transform[s] p
|}.

(** ** The two-variable evaluation *)

(* The bifunctor [P, X] ∏ P ⟶ X whose partial application at p is [Eval p].
   The arrow action is in [Cat_Closed]'s order, [fmap[K] f ∘ transform[s] p]
   (Instance/Fun/Eval/Cat.v shows the two agree at [eq_refl]); the other
   order, [transform[s] q ∘ fmap[H] f], is the same arrow by naturality and
   is the one Functor/Hom/Yoneda/Natural.v's [YoEval] uses. *)
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

(** ** Partial application agrees with the fixed-object evaluation *)

(* On objects: on the nose. *)
Definition eval_partial_obj (p : P) (H : [P, X]) :
  fobj[Eval p] H = fobj[Partial_l EvalBi p] H := eq_refl.

(* On arrows: up to ≈ only — [Partial_l]'s action is [bimap s id], which
   still carries the [fmap id] the functor law removes (probe). *)
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

(* The other partial application is the functor itself. *)
Definition eval_partial_r_obj (H : [P, X]) (p : P) :
  fobj[Partial_r EvalBi H] p = fobj[H] p := eq_refl.

Lemma eval_partial_r_map (H : [P, X]) (p q : P) (f : p ~> q) :
  fmap[Partial_r EvalBi H] f ≈ fmap[H] f.
Proof. simpl; unfold bimap; simpl; cat. Qed.

(** ** Naturality in the evaluated object *)

(* Each arrow of P gives a transformation between evaluation functors,
   with component [fmap[H] f] at H; both naturality fields are the
   naturality of the transformation being evaluated. *)
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
