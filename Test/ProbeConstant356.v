(**
* Boundary probe for Structure/Limit/Constant.v (issue #356)

    Mac Lane CWM 2nd ed. §IV.2, book p. 90, Exercise 8.

    WHY THIS FILE EXISTS.  The target carries five [Fail]s of its own and
    they are well formed -- the universe controls are APPLIED, which is
    what makes them discriminate at all (an unapplied polymorphic
    constant never meets the declared levels).  What an in-file negative
    CANNOT do is survive a rename: a whole-file rename moves the [Fail]
    and the constant it names together, so the guard stays green while
    the thing it guarded is gone.  Every negative below therefore names a
    constant of the TARGET, and this file mirrors the target's FULL
    import list -- a probe built on a short prefix is the classic way to
    make a negative pass for a reason it never measured.  (#477 added
    Structure/Limit/Absolute.v to the target's list, and the same line
    here; each stripped refusal's error text is unchanged by it.)

    KINDS, separated by the error TEXT rather than by label:
      CONVERSION   ends `(cannot unify "X" and "Y")`
      FORMABILITY  ends `(universe inconsistency: Cannot enforce ...)`
    A [Fail] that SUCCEEDS prints NOTHING under this repo's [coqc], so
    every negative here was stripped and run alone before being trusted.

    WHAT IS PINNED:

    N1 -- the opposite of a constant diagram is NOT the constant diagram
          on the opposite categories, on the nose.  This is why the
          colimit half is built DIRECTLY rather than by instantiating the
          limit half at [C^op]/[J^op]: [ACone n G] is not convertible for
          non-convertible [G].  BOTH DATA FIELDS agree at [eq_refl]
          (controls below), so the difference is confined to the three
          rebuilt law fields.

    N2 -- a functor does not carry a constant diagram to a constant
          diagram on the nose at the ARROW action.

--------
* Structure/Limit/Constant.v 的边界探测（问题 #356）

Mac Lane 《CWM》第2版 §IV.2，第90页，练习8。

为什么存在此文件。目标文件自身包含五个 [Fail]，它们结构良好——宇宙控制已被应用，这使它们能够进行区分（未应用的多态常量永远无法达到声明的级别）。文件内部的负值无法做到的事情是重命名后仍然存在：整个文件的重命名会将 [Fail] 和其命名的常量一起移动，因此守卫仍然显示绿色，而它所守护的对象已经不存在。因此，下列每个负值都命名了目标的一个常量，而此文件镜像了目标的完整导入列表——基于短前缀构建的探针是为了某个它从未测量的原因使负值通过的经典方式。 (#477 将 Structure/Limit/Absolute.v 添加到目标列表中，这里也是同一行；每个剥离拒绝的错误文本未因此更改。)

类型，按错误文本分开，而不是按标签分开：
      转换 以 `(cannot unify "X" and "Y")` 结尾
      可形成性 以 `(universe inconsistency: Cannot enforce ...)` 结尾
一个在此仓库的 [coqc] 下成功的 [Fail] 不会打印任何内容，所以这里的每个负例都是先被剥离并单独运行后才被信任。

固定内容是什么：

N1 —— 常量图的对立面并不是在对偶范畴上的常量图，正是如此。这就是为什么上确界部分是直接构建的，而不是通过在 [C^op]/[J^op] 上实例化下确界部分：对于不可转换的 [G]，[ACone n G] 不能转换。两个数据字段在 [eq_refl] 上一致（下面控制），因此差异仅限于三个重建的律字段。

N2 -- 一个函子在箭头作用下并不将常量图严格地映射为常量图。
*)
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Fun.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Cone.Const.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Structure.Limit.Components.
Require Import Category.Structure.Groupoid.Connected.
Require Import Category.Theory.Connected.Components.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Instance.Zero.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Instance.Coq.
Require Import Category.Structure.Limit.Absolute.
Require Import Category.Structure.Limit.Constant.

(** ** Instrument check — must ERROR ("The command has not failed!"). / ** 仪器检查 — 必须错误（“命令没有失败！”）。 *)
Fail Fail Check Category.

Section OppositeConstant.
Context {J C : Category}.
Context (c : C).

(*
CONTROLS: both DATA fields agree on the nose, which is what locates
   the failure of N1 in the LAW fields rather than in the actions.

--------
控制：两个数据字段完全一致，这正是定位 N1 在法律字段中的失败而不是在操作中的原因。
*)
Example probe_op_diag_fobj (x : J) :
  fobj[Opposite_Functor Δ[J](c)] x
    = fobj[@Diagonal (C^op) (J^op) c] x := eq_refl.

Example probe_op_diag_fmap {x y : J^op} (f : x ~{J^op}~> y) :
  fmap[Opposite_Functor Δ[J](c)] f
    = fmap[@Diagonal (C^op) (J^op) c] f := eq_refl.

(* N1. *)
Fail Example probe_op_diag_strict :
  Opposite_Functor Δ[J](c) = @Diagonal (C^op) (J^op) c := eq_refl.

(* CONTROL for N2: the target proves the ≈ form. / N2 的控制：目标证明了≈形式。 *)
Check @const_image_fmap_equiv.

(* N2. *)
Fail Example probe_const_image_fmap {D : Category} (F : C ⟶ D)
  {x y : J} (f : x ~{J}~> y) :
  fmap[F ◯ Δ[J](c)] f = fmap[Δ[J](F c)] f := eq_refl.

End OppositeConstant.

(**
** POSITIVE CONTROLS naming the surface, so a rename of any of these
    breaks this file at a NON-[Fail] line.

--------
** 阳性对照命名表面，因此重命名其中的任何一个都会在非 [Fail] 行破坏此文件。
*)

Check @const_acone.
Check @const_cone.
Check @const_IsALimit.
Check @const_IsLimitCone.
Check @const_Limit.
Check @const_acocone.
Check @const_cocone.
Check @const_IsAColimit.
Check @const_IsColimitCocone.
Check @leg_zigzag.
Check @const_cone_step.
Check @const_cone_zigzag.
Check @const_cocone_step.
Check @const_cocone_zigzag.
Check @Diagonal_Faithful.
Check @Diagonal_Full.
Check @Diagonal_Full_via_limit.
Check @const_AbsoluteLimit.
Check @const_AbsoluteColimit.
Check @TwoX_not_terminal.
Check @zero_const_limit_IsTerminalObj.
Check @const_limit_not_from_bare_connected.
Check @two_discrete_const_not_limit.
Check @const_limit_not_from_point_alone.
Check @td_const_IsALimit_product.
Check @Diagonal_Zero_not_Faithful.
Check @Diagonal_Two_Discrete_not_Full.
(*
Donor names the negatives depend on: without these a rename would
   leave a [Fail] passing for reference-not-found (#151).

--------
供体命名负数依赖于：没有这些，重命名将导致 [Fail] 被误认为引用未找到 (#151)。
*)
Check @Diagonal.
Check @Opposite_Functor.
Check @ConnectedNonempty.
