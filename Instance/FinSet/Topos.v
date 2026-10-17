Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.Topos.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Closed.
Require Import Category.Instance.FinSet.Classifier.

Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(*
   本文件给出 topos 相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明topos相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition FinSet_Topos : ElementaryTopos FinSet := {|
  topos_terminal   := FinSet_Terminal;
  topos_cartesian  := FinSet_Cartesian;
  topos_pullbacks  := FinSet_Pullbacks;
  topos_closed     := FinSet_Closed;
  topos_classifier := FinSet_Classifier
|}.

(*
   本节说明topos相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example FinSet_Pow_two : @Pow FinSet FinSet_Topos 2%nat = 4%nat := eq_refl.

Example FinSet_Pow_zero : @Pow FinSet FinSet_Topos 0%nat = 1%nat := eq_refl.

(** 本节：The truth point evaluates [fin_true] sole element 1. （已译） *)

Example FinSet_truth_computes :
  @truth FinSet FinSet_Terminal FinSet_Classifier Fin.F1 = fin_true
  := eq_refl.

(*
   本节说明子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition point_true : 1%nat ~{FinSet}~> 2%nat := fun _ => fin_true.

Lemma point_true_monic : Monic point_true.
Proof.
  apply finset_monic_iff_injective; intros a b _.
  exact (eq_trans (fin1_unique a) (eq_sym (fin1_unique b))).
Qed.

Example FinSet_char_at_true :
  char point_true point_true_monic fin_true = fin_true := eq_refl.

Example FinSet_char_at_false :
  char point_true point_true_monic fin_false = fin_false := eq_refl.

(*
   本节说明 Topos 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example FinSet_Pow_membership :
  @eval FinSet FinSet_Cartesian FinSet_Closed 2%nat
        (@Ω FinSet FinSet_Terminal FinSet_Classifier)
    (fin_pair (Fin.FS (Fin.FS Fin.F1) : Fin.t 4) fin_true)
    = fin_false := eq_refl.
