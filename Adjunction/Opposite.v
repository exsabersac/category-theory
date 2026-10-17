Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Opposite.

Generalizable All Variables.

(* * * The opposite (dual) hom-set 伴随: F ⊣ U yields U^op ⊣ F^op. （已译） *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

   本文件给出反范畴、反函子或反自然变换（2-胞方向反转）。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Opposite_Adjunction `(F : D ⟶ C) `(U : C ⟶ D)
        (A : F ⊣ U) :
  U^op ⊣ F^op := {|
  adj := fun x y =>
    {| to          := from (@adj _ _ _ _ A y x)
     ; from        := to (@adj _ _ _ _ A y x)
     ; iso_to_from := iso_from_to (@adj _ _ _ _ A y x)
     ; iso_from_to := iso_to_from (@adj _ _ _ _ A y x) |};

  to_adj_nat_l   := fun _ _ _ f g => @from_adj_nat_r _ _ _ _ A _ _ _ g f;
  to_adj_nat_r   := fun _ _ _ f g => @from_adj_nat_l _ _ _ _ A _ _ _ g f;
  from_adj_nat_l := fun _ _ _ f g => @to_adj_nat_r  _ _ _ _ A _ _ _ g f;
  from_adj_nat_r := fun _ _ _ f g => @to_adj_nat_l  _ _ _ _ A _ _ _ g f
|}.

(* Mirrors F^op notation 函子, at same level/scope. （已译） *)

Notation "N ^op" := (@Opposite_Adjunction _ _ _ _ N)
  (at level 7, format "N ^op", left associativity) : adjunction_scope.

Open Scope adjunction_scope.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Corollary Opposite_Adjunction_invol `(F : D ⟶ C) `(U : C ⟶ D) (A : F ⊣ U) :
  (A^op)^op = A.
Proof. reflexivity. Qed.
