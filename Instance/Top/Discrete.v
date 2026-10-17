Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Forgetful.

Generalizable All Variables.

(*
 nLab:      https://ncatlab.org/nlab/show/discrete+space
 nLab:      https://ncatlab.org/nlab/show/universal+morphism
 Wikipedia: https://en.wikipedia.org/wiki/Discrete_space
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,

   本文件给出离散范畴实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The extension of a setoid map to the discrete space *)

(*
   本节说明 Discrete 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition disc_extend (A : SetoidObject) (Y : TopSpace)
  (g : SetoidMorphism A (top_carrier Y))
  : Discrete_Top A ~{Top}~> Y :=
  @Build_ContinuousMorphism (Discrete_Top A) Y g
    (out_of_discrete_continuous A Y g).

Example disc_extend_map (A : SetoidObject) (Y : TopSpace)
  (g : SetoidMorphism A (top_carrier Y)) (a : carrier A) :
  disc_extend A Y g a = g a := eq_refl.

(** ** The universal property (Mac Lane §III.1 Exercise 3, row three) *)

Theorem discrete_universal (A : SetoidObject) (Y : TopSpace)
  (g : SetoidMorphism A (top_carrier Y)) :
  ∃! f : Discrete_Top A ~{Top}~> Y, ∀ a, f a ≈ g a.
Proof.
  exists (disc_extend A Y g).
  - intro a; reflexivity.
  - intros f' Hf' a; simpl; symmetry; exact (Hf' a).
Qed.

(** ** The unit X → U(X_disc), and that it is the identity *)

Example disc_unit_target_strict (A : SetoidObject) :
  fobj[Top_Forget] (fobj[Top_Discrete] A) = Setoid_Lift A := eq_refl.

Definition disc_unit (A : SetoidObject)
  : Setoid_Lift A ~{Sets}~> fobj[Top_Forget] (fobj[Top_Discrete] A) := id.

Example disc_unit_is_id (A : SetoidObject) (a : carrier A) :
  disc_unit A a = a := eq_refl.

(** ** Agreement with the pre-existing transposition isomorphism *)

(* [discrete_adj]'s forward leg strips a continuous map to its underlying
   setoid map; on an extension it returns the map it started from. *)
Example disc_extend_is_adj_from (A : SetoidObject) (Y : TopSpace)
  (g : SetoidMorphism A (top_carrier Y)) :
  to (discrete_adj A Y) (disc_extend A Y g) = g := eq_refl.

(*
   本节说明 Discrete 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example disc_universal_at_indiscrete
  (g : SetoidMorphism bool_setoid_object
         (top_carrier TwoPoint_Indiscrete)) :
  ∃! f : Discrete_Top bool_setoid_object ~{Top}~> TwoPoint_Indiscrete,
    ∀ a, f a ≈ g a :=
  discrete_universal bool_setoid_object TwoPoint_Indiscrete g.

(* And the extension really is the identity on points, so the universal
   property is not collapsing anything. *)
Example disc_extend_indiscrete_computes
  (g : SetoidMorphism bool_setoid_object
         (top_carrier TwoPoint_Indiscrete)) (b : bool) :
  disc_extend bool_setoid_object TwoPoint_Indiscrete g b = g b := eq_refl.
