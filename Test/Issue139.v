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
Regression test for issue #139 ("CartesianMonoidal cleanup").

   Issue #139 observed that the library appeared to be missing the forward
   direction "every cartesian category is a monoidal category", and that the
   file Monoidal/Cartesian.v misleadingly held the *reverse* (Heunen-Vicary)
   result instead.  The forward direction in fact already existed, as
   CC_Monoidal in Monoidal/Internal/Product.v; it is now surfaced under the
   discoverable name Cartesian_Monoidal in Monoidal/Cartesian.v.

   These checks pin that down: the forward direction is available generically
   under its discoverable name; its tensor is the categorical product, on both
   objects and morphisms; its unit is the terminal object; and it agrees with
   the monoidal structure that a concrete cartesian category (Coq) uses.

--------
针对问题 #139（“笛卡尔单体清理”）的回归测试。

问题 #139 观察到库似乎缺少正向方向“每个笛卡尔范畴都是单体范畴”，并且文件 Monoidal/Cartesian.v 误导性地包含了*反向*（Heunen-Vicary）结果。事实上，正向方向已经存在于 Monoidal/Internal/Product.v 中的 CC_Monoidal；现在它在 Monoidal/Cartesian.v 中以可发现的名称 Cartesian_Monoidal 进行了展示。

这些检查确认了：正向方向以其可发现的名称通用可用；其张量是范畴积，对象和态射都适用；其单位是终对象；并且与具体笛卡尔范畴（Coq）使用的单体结构一致。
*)

Section Issue139.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.

(*
Theorem 1, generically: a cartesian category with a terminal object is
   monoidal.  Before #139 this construction had no discoverable name.

--------
定理1，一般地：具有终对象的笛卡尔范畴是单性的。在#139之前，这个构造没有可发现的名称。
*)
Definition issue_139_cartesian_is_monoidal : @Monoidal C := Cartesian_Monoidal.

(* The tensor of that monoidal structure is exactly the categorical product. / 那个幺半群结构的张量正是范畴乘积。 *)
Example issue_139_tensor_is_product (x y : C) :
  (x ⨂[Cartesian_Monoidal] y)%object = (x × y)%object.
Proof. reflexivity. Qed.

(* ...and its unit is exactly the terminal object. / ...它的单位正好是终对象。 *)
Example issue_139_unit_is_terminal :
  @I C Cartesian_Monoidal = 1%object.
Proof. reflexivity. Qed.

(*
Beyond the object level, the monoidal action on *morphisms* is the product's
   bifunctorial action: projecting after the tensor f ⨂ g recovers f on the
   left factor and g on the right.  These are genuine equational checks via the
   product UMP (exl_fork / exr_fork), so they fail for any non-product tensor --
   they exercise the structure itself, not merely the discoverable name.

--------
超越对象层次，对*态射*的幺半群作用是乘积的双函子作用：在张量 f ⨂ g 之后投影会在左因子上恢复 f，在右因子上恢复 g。这些是通过乘积的终极性质 (exl_fork / exr_fork) 进行的真实方程检查，因此，对于任何非乘积张量，它们都会失败——它们检验的是结构本身，而不仅仅是可被发现的名称。
*)
Example issue_139_exl_tensor {a b c d : C} (f : a ~> b) (g : c ~> d) :
  exl ∘ (f ⨂[Cartesian_Monoidal] g) ≈ f ∘ exl.
Proof. simpl; now rewrite exl_fork. Qed.

Example issue_139_exr_tensor {a b c d : C} (f : a ~> b) (g : c ~> d) :
  exr ∘ (f ⨂[Cartesian_Monoidal] g) ≈ g ∘ exr.
Proof. simpl; now rewrite exr_fork. Qed.

End Issue139.

(*
End-to-end: the surfaced construction is definitionally the monoidal
   structure that the concrete cartesian category Coq already uses
   (Instance/Coq.v builds Coq_Monoidal from Coq_Cartesian + Coq_Terminal).

--------
端到端：表面上的构造在定义上就是具体的笛卡尔范畴 Coq 已经使用的幺半群结构（Instance/Coq.v 从 Coq_Cartesian + Coq_Terminal 构建 Coq_Monoidal）。
*)
Example issue_139_coq_monoidal :
  Coq_Monoidal = @Cartesian_Monoidal Coq Coq_Cartesian Coq_Terminal.
Proof. reflexivity. Qed.
