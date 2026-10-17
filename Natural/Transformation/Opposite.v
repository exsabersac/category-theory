Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

Generalizable All Variables.

(* * * The opposite (dual) 自然变换. （已译） *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Opposite_category

   本文件给出反范畴、反函子或反自然变换（2-胞方向反转）。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Opposite_Transform `{F : C ⟶ D} {G : C ⟶ D} `(N : F ⟹ G) :
  G^op ⟹ F^op :=
  @Build_Transform (C^op) (D^op) (G^op) (F^op) N
    (λ (x y : (C ^op)%category) (f : x ~{C^op}~> y),
      @naturality_sym C D F G N y x f)
    (λ (x y : (C ^op)%category) (f : x ~{C^op}~> y),
      @naturality C D F G N y x f).

Notation "N ^op" := (@Opposite_Transform _ _ _ _ N)
  (at level 7, format "N ^op", left associativity) : transform_scope.

Open Scope transform_scope.

(* The op 函子 is involution natural transformations: applying it twice
 recovers `N` definitionally, since (C^op)^op = C (F^op)^op = F hold by
 reflexivity `N^op` reuses `N`'s components.（已译） *)

Corollary Opposite_Transform_invol `{F : C ⟶ D} {G : C ⟶ D} `(N : F ⟹ G) :
  (N^op)^op = N.
Proof. reflexivity. Qed.
