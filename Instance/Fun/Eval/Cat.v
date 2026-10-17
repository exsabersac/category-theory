Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Eval.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Cat.Cartesian.
Require Import Category.Instance.Cat.Cartesian.Closed.
Require Import Category.Instance.Cat.Exponential.

Generalizable All Variables.

(* * * The evaluation 函子 [Cat]'s exponential evaluation （已译） *)

(*
   本文件给出 Cat 相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CatEval.

Context (P X : Cat).

(* [Cat]'s exponential is the functor category (Instance/Cat/Cartesian/
   Closed.v's [Cat_Closed]), so the closed structure's own [eval] IS a
   functor [[P, X] ∏ P ⟶ X].  Named here; it is reachable only at [Cat]'s
   universes, which is why Instance/Fun/Eval.v builds [EvalBi] directly
   (see the header's universe measurement). *)
Definition CatEval : ([P, X] ∏ P) ⟶ X := @eval Cat Cat_Cartesian Cat_Closed P X.

(* 相关说明。 （已译） *)
Definition CatEval_obj (Hp : ([P, X] ∏ P)) :
  fobj[CatEval] Hp = fobj[EvalBi] Hp := eq_refl.

Definition CatEval_map (Hp Kq : ([P, X] ∏ P)) :
  @fmap _ _ CatEval Hp Kq = @fmap _ _ (@EvalBi P X) Hp Kq := eq_refl.

(* So fixed-对象 evaluation partial application [Cat]'s
 own evaluation: 对象 nose, arrows up ≈ (through
 Instance/Fun/Eval.v's [eval_partial_map]). （已译） *)
Definition eval_is_CatEval_partial_obj (p : P) (H : [P, X]) :
  fobj[Eval p] H = fobj[Partial_l CatEval p] H := eq_refl.

Lemma eval_is_CatEval_partial_map (p : P) (H K : [P, X]) (s : H ~{[P, X]}~> K) :
  fmap[Eval p] s ≈ fmap[Partial_l CatEval p] s.
Proof. exact (eval_partial_map p H K s). Qed.

End CatEval.

(* The parameter/adjunct passage issue asks record already exists as
 同构 [Cat]: Instance/Cat/Exponential.v's [Cat_exp_prod_l].
 Cited, not rebuilt. （已译） *)
Definition eval_transpose (J P X : Cat) :
  @Isomorphism Cat ([J ∏ P, X]) ([J, [P, X]]) := Cat_exp_prod_l J P X.
