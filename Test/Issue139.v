Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Cartesian.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(*
   本文件为测试：Issue139。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Issue139.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.

(* Theorem 1, generically: a cartesian category with a terminal object is
   monoidal.  Before #139 this construction had no discoverable name. *)
Definition issue_139_cartesian_is_monoidal : @Monoidal C := Cartesian_Monoidal.

(* The tensor of that monoidal structure is exactly the categorical product. *)
Example issue_139_tensor_is_product (x y : C) :
  (x ⨂[Cartesian_Monoidal] y)%object = (x × y)%object.
Proof. reflexivity. Qed.

(* ...and its unit is exactly the terminal object. *)
Example issue_139_unit_is_terminal :
  @I C Cartesian_Monoidal = 1%object.
Proof. reflexivity. Qed.

(* Beyond the object level, the monoidal action on *morphisms* is the product's
   bifunctorial action: projecting after the tensor f ⨂ g recovers f on the
   left factor and g on the right.  These are genuine equational checks via the
   product UMP (exl_fork / exr_fork), so they fail for any non-product tensor --
   they exercise the structure itself, not merely the discoverable name. *)
Example issue_139_exl_tensor {a b c d : C} (f : a ~> b) (g : c ~> d) :
  exl ∘ (f ⨂[Cartesian_Monoidal] g) ≈ f ∘ exl.
Proof. simpl; now rewrite exl_fork. Qed.

Example issue_139_exr_tensor {a b c d : C} (f : a ~> b) (g : c ~> d) :
  exr ∘ (f ⨂[Cartesian_Monoidal] g) ≈ g ∘ exr.
Proof. simpl; now rewrite exr_fork. Qed.

End Issue139.

(* End-to-end: the surfaced construction is definitionally the monoidal
   structure that the concrete cartesian category Coq already uses
   (Instance/Coq.v builds Coq_Monoidal from Coq_Cartesian + Coq_Terminal). *)
Example issue_139_coq_monoidal :
  Coq_Monoidal = @Cartesian_Monoidal Coq Coq_Cartesian Coq_Terminal.
Proof. reflexivity. Qed.
