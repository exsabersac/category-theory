Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Free.

From Coq Require Import Arith.

Generalizable All Variables.

(** * Parallel-composition bifunctor on FreeCat *)

(*
   nLab: https://ncatlab.org/nlab/show/PROP
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

   本文件给出张量相关构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section FreeTensor.

Context (S : Signature).

(** The tensor bifunctor on FreeCat S. *)
Program Definition FreeCat_Tensor : FreeCat S ∏ FreeCat S ⟶ FreeCat S := {|
  fobj := fun p => Nat.add (fst p) (snd p);
  fmap := fun p q m =>
    @T_tens S (fst p) (fst q) (snd p) (snd q) (fst m) (snd m)
|}.
Next Obligation.
  unfold Proper, respectful.
  intros [f1 f2] [g1 g2] [Hf Hg]; simpl in *.
  apply TE_tens_cong; assumption.
Qed.
Next Obligation.
  apply TE_tens_id.
Qed.
Next Obligation.
  apply TE_sym, TE_interchange.
Qed.

End FreeTensor.

Arguments FreeCat_Tensor S : assert.
