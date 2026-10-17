Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(** The diagonal 函子 Δ : C ⟶ [J, C] (and binary Δ : C ⟶ C ∏ C). （已译） *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Diagonal_functor

   本文件给出函子相关定义或实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[export]
Program Instance Diagonal {C : Category} (J : Category) : C ⟶ [J, C] := {
  fobj := fun x =>
    {| fobj := fun _ => x
     ; fmap := fun _ _ _ => id[x] |};
  fmap := fun _ _ f =>
    {| transform := fun _ => f |}
}.

Section Diagonal_Product.

#[local] Set Transparent Obligations.

#[export]
Program Instance Diagonal_Product `(C : Category) : C ⟶ C ∏ C.

End Diagonal_Product.

Notation "Δ[ J ]( c )" := (Diagonal J c) (at level 0, format "Δ[ J ]( c )") : functor_scope.

Require Import Category.Instance.One.

Notation "Δ( c )" := (Diagonal _ c) (at level 0, format "Δ( c )") : functor_scope.
Notation "=( c )" := (Diagonal 1 c) (at level 0, format "=( c )") : functor_scope.

Definition Δ {C J : Category} := @Diagonal C J.

(*
   Wikipedia: https://en.wikipedia.org/wiki/Diagonal_functor
   Wikipedia: "In category theory, a branch of mathematics, the diagonal

   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Instance.Two.Discrete.

Theorem Diagonal_Product_Two (C : Category) :
  (∀ x, Diagonal_Product C x ≅ (Diagonal Two_Discrete x TwoDX,
                                Diagonal Two_Discrete x TwoDY)) *
  (∀ x y (f : x ~> y),
     fmap[Diagonal_Product C] f
       ≈ (transform[fmap[Diagonal Two_Discrete] f] TwoDX,
          transform[fmap[Diagonal Two_Discrete] f] TwoDY)).
Proof.
  split; intros.
  - isomorphism; simpl; intros; try exact (id, id); cat.
  - reflexivity.
Qed.

#[export]
Instance Transform_Const `(x ~{C}~> y) : Δ(x) ⟹ Δ(y).
Proof. construct; auto; cat_simpl. Qed.
