Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Instance.Proset.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(** * The category of a partially-ordered set. *)

(*
 Wikipedia: https://en.wikipedia.org/wiki/Partially_ordered_set
 Wikipedia: "Every poset (and every preorder) may be considered as a category

   本文件给出偏序集相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab:  https://ncatlab.org/nlab/show/Galois+connection
   Paper: Ore, "Galois connexions", Transactions of the AMS 55, 1944
   Paper: Lawvere, "Metric spaces, generalized logic, and closed

   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma eq_equiv {C : Type} : @Equivalence C eq.
Proof.
  split; auto. intros x y z; apply eq_trans.
Qed.

Definition Poset {C : Type} `{R : relation C}
           `(P : PreOrder C R) `{@Antisymmetric C eq eq_equiv R} : Category := Proset P.

Section Examples.
Definition LessThanEqualTo_Category : Category :=
  @Poset nat PeanoNat.Nat.le PeanoNat.Nat.le_preorder
    (partial_order_antisym PeanoNat.Nat.le_partialorder).
End Examples.
