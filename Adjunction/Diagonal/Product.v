Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Product.Internal.
Require Import Category.Structure.Cartesian.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * The diagonal–product adjunction Δ ⊣ × *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)

   本文件给出积（分量）构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[export]
Program Instance Diagonal_Product_Adjunction (C : Category) `{@Cartesian C} :
  Diagonal_Product C ⊣ ×(C) := {
  adj := fun _ _ =>
    {| to   := {| morphism := fun f => fst f △ snd f |}
     ; from := {| morphism := fun f => (exl ∘ f, exr ∘ f) |} |}
}.
Next Obligation. proper; apply fork_respects; auto. Qed.
Next Obligation. rewrite fork_comp; cat. Qed.
Next Obligation. unfork. Qed.
Next Obligation. unfork. Qed.
Next Obligation. split; unfork. Qed.
