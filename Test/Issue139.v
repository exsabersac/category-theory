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

(* Theorem 1, generically: cartesian 范畴 终对象 is
 monoidal. Before #139 construction had no discoverable name. （已译） *)
Definition issue_139_cartesian_is_monoidal : @Monoidal C := Cartesian_Monoidal.

(* 相关说明。 （已译） *)
Example issue_139_tensor_is_product (x y : C) :
  (x ⨂[Cartesian_Monoidal] y)%object = (x × y)%object.
Proof. reflexivity. Qed.

(* ...and unit exactly 终对象. （已译） *)
Example issue_139_unit_is_terminal :
  @I C Cartesian_Monoidal = 1%object.
Proof. reflexivity. Qed.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example issue_139_exl_tensor {a b c d : C} (f : a ~> b) (g : c ~> d) :
  exl ∘ (f ⨂[Cartesian_Monoidal] g) ≈ f ∘ exl.
Proof. simpl; now rewrite exl_fork. Qed.

Example issue_139_exr_tensor {a b c d : C} (f : a ~> b) (g : c ~> d) :
  exr ∘ (f ⨂[Cartesian_Monoidal] g) ≈ g ∘ exr.
Proof. simpl; now rewrite exr_fork. Qed.

End Issue139.

(*
   本节说明幺半结构、幺半群、（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example issue_139_coq_monoidal :
  Coq_Monoidal = @Cartesian_Monoidal Coq Coq_Cartesian Coq_Terminal.
Proof. reflexivity. Qed.
