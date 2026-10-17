Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Skeleton.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Poset.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/skeleton
 Wikipedia: https://en.wikipedia.org/wiki/Partially_ordered_set

   本文件给出预序集相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ProsetSkeletal.
Context {A : Type}.
Context {R : relation A}.
Variable P : PreOrder R.

(* 相关说明。 （已译） *)

Theorem Proset_Skeletal_iff_Antisymmetric :
  (Skeletal (Proset P) → @Antisymmetric A eq eq_equiv R) *
  (@Antisymmetric A eq eq_equiv R → Skeletal (Proset P)).
Proof.
  split.
  - intros Sk x y Rxy Ryx.
    apply (Sk x y).
    exists Rxy Ryx; exact I.
  - intros Anti x y i.
    exact (Anti x y (to i) (from i)).
Qed.

Theorem Poset_Skeletal `{Anti : @Antisymmetric A eq eq_equiv R} :
  Skeletal (@Poset A R P Anti).
Proof. intros x y i. exact (Anti x y (to i) (from i)). Qed.

(* Both Instance/Proset.v Instance/Poset.v define 常值 this
 name, file imports both, so name qualified explicitly rather than left import order. （已译） *)

Lemma Nat_le_Skeletal : Skeletal Poset.LessThanEqualTo_Category.
Proof.
  intros x y i.
  exact (partial_order_antisym PeanoNat.Nat.le_partialorder x y (to i) (from i)).
Qed.

(* 相关说明。 （已译） *)

Theorem skeleton_of_proset_antisymmetric (S : Skeleton (Proset P))
        (a b : skel_cat S) :
  R (`1 a) (`1 b) → R (`1 b) (`1 a) → `1 a = `1 b.
Proof.
  intros f g.
  apply (f_equal (fun z : skel_cat S => `1 z)).
  apply (skeleton_is_skeletal S).
  exists (f; skel_full S _ _ `2 a `2 b f) (g; skel_full S _ _ `2 b `2 a g);
    exact I.
Qed.

(*
   本节说明 Skeletal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Proset_Skeleton (Anti : @Antisymmetric A eq eq_equiv R) :
  Skeleton (Proset P) :=
  Skeleton_of_Skeletal (snd Proset_Skeletal_iff_Antisymmetric Anti).

End ProsetSkeletal.
