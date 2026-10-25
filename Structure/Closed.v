Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(* nLab: https://ncatlab.org/nlab/show/closed+category

   本文件是 Eilenberg–Kelly「闭范畴」草稿（无张量的内部 hom）；
   [Closed] Class 仍注释掉。日常用的笛卡尔闭请看 Structure/Cartesian/Closed.v。
   Draft closed category (internal hom without tensor). For CCC see
   Structure/Cartesian/Closed.v.
*)

(*
   【阅读提示】/ Reading tip

   Haskell 对照的 curry/eval 在 Cartesian/Closed.v（CCC），不在本草稿。
   Curry/eval for Haskell programmers live in Cartesian/Closed.v, not here.
*)

Section Closed.

Context {C : Category}.
Context {D : Category}.
Context {E : Category}.

#[local] Set Transparent Obligations.

(* 双函子在第一变元上的柯里化 / Curry a bifunctor in the first variable *)
Program Definition Curry (F : C^op ∏ D ⟶ E) : C^op ⟶ [D, E] := {|
  fobj := fun x => {|
    fobj := fun y => F (x, y);
    fmap := fun y z (f : y ~{D}~> z) => fmap[F] (id[x], f)
  |};
  fmap := fun x y (f : x ~{C^op}~> y) => {|
    transform := fun z => fmap[F] (f, id[z])
  |}
|}.
Next Obligation. now proper; simpl_eq; rewrite X. Qed.
Next Obligation. now rewrite <- fmap_comp; simpl; cat. Qed.
Next Obligation. now rewrite <- !fmap_comp; simpl; cat. Qed.
Next Obligation. now rewrite <- !fmap_comp; simpl; cat. Qed.
Next Obligation. now proper; rewrite X. Qed.
Next Obligation. now rewrite <- !fmap_comp; simpl; cat. Qed.

(* 交换双函子两变元 / Flip arguments of a bifunctor *)
Program Definition Flip (F : C^op ∏ D ⟶ E) : D ∏ C^op ⟶ E := {|
  fobj := fun x => F (snd x, fst x);
  fmap := fun _ _ f => fmap[F] (snd f, fst f)
|}.
Next Obligation. now proper; simpl_eq; simpl in *; rewrite X, H. Qed.
Next Obligation. now rewrite <- fmap_comp. Qed.

Reserved Notation "[ X , Y ]"
  (at level 90, right associativity, format "[ X ,  Y ]").

End Closed.
