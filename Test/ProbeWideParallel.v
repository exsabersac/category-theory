(**
* Boundary probes for the wide walking parallel pair

    Companion to Instance/Parallel/Wide.v, Structure/Equalizer/Wide.v and
    Structure/Coequalizer/Wide.v (issue #322, Mac Lane §III.3, book
    pp. 64-65).  Those files make three strength claims whose negative
    side is a conversion or a universe boundary.  A measurement taken
    only in a header would not be noticed by a refactor, so the negatives
    are pinned here.  **If the [Fail] commands below stop failing, this
    file breaks the build.**

    Each negative is paired with a positive control that must SUCCEED,
    for the reason Test/ProbeQuiverConstructions.v gives: a [Fail] alone
    passes just as happily when a name has been renamed out from under
    it.  The instrument itself was checked — wrapping [Fail] around a
    succeeding command reports "The command has not failed!" and aborts
    compilation — and every negative below was compiled once with the
    [Fail] stripped, to confirm the reported error is the intended one
    and not a syntax, scope or resolution failure: three [cannot unify]
    conversion errors and one genuine universe inconsistency naming the
    declared level.

    The import list is the union of the three target files' own, in
    their order, so that nothing here passes for want of a definition
    that the targets do have in scope.

    THE THREE BOUNDARIES.

    (1) [WideParallel bool] IS NOT [Parallel], AS A TERM.  What is proved
    in Instance/Parallel/Wide.v is [WideParallel_bool_Parallel], an
    isomorphism in [StrictCat] — the strong reading, since [≅[Cat]] in
    this library is equivalence of categories.  It is NOT an equality of
    [Category] records, and the two hom-families are not convertible
    either: the wide shape's hom [ParX ~> ParY] IS the index type, while
    [Parallel]'s is a dependent pair over [bool].  Both are pinned.

    (2) THE DIAGRAM COMPARISON IS AT [Functor_StrictEq_Setoid], NOT AT
    [eq].  [AWide_bool_APair] identifies the wide diagram at a
    two-element family with the binary diagram pulled back along the
    comparison, with [eq_refl] object components — but the two [Functor]
    records are built from different arrow actions and different law
    proofs, so no Leibniz equality is available.

    (3) THE INDEX UNIVERSE IS BOUNDED BY THE AMBIENT HOM UNIVERSE.
    [AWide]'s constraint block contains [i <= h].  Instance/Parallel/
    Wide.v attributes that to [Functor]'s [fmap_respects] field rather
    than to anything this development does; the probe holds it to the
    claim, rejecting [AWide] at an index universe declared strictly
    above the target's hom universe and accepting it strictly below.

--------
* 用于宽行并行对的边界探针

本文件为 Instance/Parallel/Wide.v、Structure/Equalizer/Wide.v 和 Structure/Coequalizer/Wide.v 的配套文件（问题 #322，Mac Lane 第 III.3 节，书籍第 64-65 页）。这些文件提出了三个强度声明，其否定方向是转换或宇宙边界。如果只在头文件中进行测量，重构时不会注意到，因此否定项固定在此处。**如果下面的 [Fail] 命令不再失败，本文件将破坏构建。**

每个阴性测试都配有一个必须成功的阳性对照，原因如 Test/ProbeQuiverConstructions.v 所示：单独的 [Fail] 在名称已被重命名时也能顺利通过。该工具本身已经过检查 —— 在一个成功的命令周围包裹 [Fail] 会报告“命令未失败！”并中止编译 —— 且下面的每个阴性测试在去掉 [Fail] 后都编译过一次，以确认报告的错误是预期的错误，而不是语法、作用域或解析失败：三个 [cannot unify] 转换错误和一个真正的宇宙不一致错误，涉及所声明等级的命名。

导入列表是三个目标文件自身导入列表的并集，按它们的顺序排列，因此这里不会因为目标文件在作用域中有的定义而缺少定义而出现问题。

三界。

(1) [WideParallel bool] 不是作为术语的 [Parallel]。在 Instance/Parallel/Wide.v 中证明的是 [WideParallel_bool_Parallel]，这是 [StrictCat] 中的一个同构——强读法，因为在该库中 [≅[Cat] 是范畴的等价，而不是 [Category] 记录的相等，并且两个 Hom 系族也不可互相转换：宽形状的 Hom [ParX ~> ParY] 是索引类型，而 [Parallel] 的则是在 [bool] 上的依赖对。两者都被固定了。

(2) 图表比较位于 [Functor_StrictEq_Setoid]，而不是 [eq]。[AWide_bool_APair] 在一个双元族上确定了宽图，并沿比较拉回二进制图，包含 [eq_refl] 对象组件 —— 但是两个 [Functor] 记录是由不同的箭头操作和不同的定律证明构建的，因此没有莱布尼茨等式可用。

(3) 指数宇宙被环境同源宇宙所限制。[AWide] 的约束块包含 [i <= h]。实例/并行/宽.v 属性将其归因于 [Functor] 的 [fmap_respects] 字段，而不是归因于本开发做的任何事情；探针将其保持在该声明上，拒绝在目标同源宇宙严格之上的索引宇宙中的 [AWide]，并接受在其严格之下的 [AWide]。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Equalizer.Wide.
Require Import Category.Structure.Coequalizer.Wide.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Parallel.Wide.
Require Import Category.Instance.Two.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Instance.Cat.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

Local Open Scope category_scope.

(** ** (1) The two shapes are isomorphic, not equal / ** (1) 这两个形状是同构的，但不相等 *)

(** Positive control: the isomorphism itself, at both strengths. / 阳性对照：同构本身，在两种强度下。 *)
Check (WideParallel_bool_Parallel :
         @Isomorphism StrictCat (WideParallel bool) Parallel).
Check (WideParallel_bool_Parallel_Cat :
         @Isomorphism Cat (WideParallel bool) Parallel).

(**
Positive control: an arrow of the wide shape from [ParX] to [ParY] IS
    an index, by conversion.  This is the fact that makes the negative
    below a genuine measurement rather than an accident of packaging.

--------
阳性对照：从 [ParX] 到 [ParY] 的宽形箭头是一个索引，通过转换。这就是使下面的阴性成为真实测量而非包装意外的事实。
*)
Definition probe_wide_hom_is_index :
  (ParX ~{WideParallel bool}~> ParY) = bool := eq_refl.

(**
Negative: the two [Category] records are not Leibniz-equal.  (With
    the [Fail] stripped: cannot unify [WideParallel bool] with
    [Parallel].)

--------
否定：这两个 [Category] 记录不相等（Leibniz 意义上的相等）。(在去掉 [Fail] 后：无法将 [WideParallel bool] 与 [Parallel] 合一。)
*)
Fail Definition wide_bool_is_Parallel :
  WideParallel bool = Parallel := eq_refl.

(**
Negative: nor are the hom-families convertible at [ParX], [ParY] —
    [bool] against [∃ b : bool, ParHom b ParX ParY].  (With the [Fail]
    stripped: cannot unify the two types.)

--------
消极：nor 这些同类家庭在 [ParX]、[ParY]——[bool] 对抗 [∃ b : bool, ParHom b ParX ParY] 时是不可转换的。（去掉 [Fail] 后：无法统一这两种类型。）
*)
Fail Definition wide_bool_hom_is_Parallel_hom :
  (ParX ~{WideParallel bool}~> ParY) = (ParX ~{Parallel}~> ParY) := eq_refl.

(** ** (2) The diagram comparison is up to strict functor equality / ** (2) 图表比较是严格函子相等的 *)

Section DiagramComparison.

(*
[Functor_StrictEq_Setoid] identifies the hom and proof universes of its
   two categories, so a strict comparison against a diagram over
   [WideParallel bool] is a statement about categories with [h = p].  The
   level is FREE, not [Set]; the section declares it strictly above [Set]
   so that the control is not passing for the degenerate reason.

--------
[Functor_StrictEq_Setoid] 识别其两个范畴的 hom 和 proof 宇宙，因此对 [WideParallel bool] 上的图进行严格比较是关于具有 [h = p] 的范畴的陈述。该级别是 FREE，而不是 [Set]；该节声明它严格高于 [Set]，以便控制不会因退化原因而传递。
*)
Universes dco dch.
Constraint Set < dco.
Constraint Set < dch.

Context (C : Category@{dco dch dch}).
Context (x y : C).
Context (f g : x ~{C}~> y).

(**
Positive control: the comparison that IS proved, and the [eq_refl]
    identification of the arrow action that it rests on.

--------
阳性对照：已经得到证明的比较，以及它所依赖的箭头动作的[eq_refl]识别。
*)
Check (AWide_bool_APair f g).

Definition probe_awide_true_is_f :
  fmap[AWide (fun b : bool => if b then f else g)]
    (true : ParX ~{WideParallel bool}~> ParY) = f := eq_refl.

(**
Negative: the two functors are not Leibniz-equal.  (With the [Fail]
    stripped: cannot unify the two [Functor] records.)

--------
否定：这两个函子不是莱布尼茨相等的。（去掉 [Fail] 后：无法统一这两个 [Functor] 记录。）
*)
Fail Definition awide_bool_is_APair :
  AWide (fun b : bool => if b then f else g) = APair f g ◯ Par_of_Wide
  := eq_refl.

End DiagramComparison.

(** ** (3) The index universe is bounded by the ambient hom universe / ** (3) 指数宇宙被环境 Hom 宇宙所界定 *)

(**
Positive control: with the index universe declared strictly BELOW the
    target's hom universe, the diagram and both round trips build.

--------
正向控制：当指数宇宙被声明严格低于目标的同类宇宙时，图表和两个往返都能构建。
*)
Section SmallIndex.

Universes si so sh sp.
Constraint si < sh.
Constraint sh <= sp.

Context (C : Category@{so sh sp}).
Context (I : Type@{si}).
Context (a b : C).
Context (fs : I → a ~{C}~> b).
Context (i0 : I).

Check (AWide fs : WideParallel I ⟶ C).
Check (is_wide_equalizer_limit fs i0).
Check (is_wide_coequalizer_colimit fs i0).

End SmallIndex.

(**
Negative: with the index universe declared strictly ABOVE the
    target's hom universe, [AWide] is rejected.  (With the [Fail]
    stripped this reports a universe inconsistency naming the declared
    [bh] against [bi].)

--------
负面：当索引宇宙被声明严格高于目标的 hom 宇宙时，[AWide] 被拒绝。（去掉 [Fail] 后，这会报告一个宇宙不一致，将声明的 [bh] 与 [bi] 进行命名。）
*)
Section BigIndex.

Universes bi bo bh bp.
Constraint bh < bi.
Constraint bh <= bp.

Context (C : Category@{bo bh bp}).
Context (I : Type@{bi}).
Context (a b : C).
Context (fs : I → a ~{C}~> b).

Fail Check (AWide fs : WideParallel I ⟶ C).

End BigIndex.

(**
** Sharpness of the pointedness hypothesis, as a standing control

    The two theorems below are not probes — they are proved in the
    target files — but they are the statements the [i0] hypothesis of
    both round trips rests on, so they are checked here alongside the
    [Fail]s that guard the rest.

--------
** 尖锐性假说的尖点性，作为一个固定的控制

下面的两个定理不是探针——它们在目标文件中已被证明——但它们是两个回程的 [i0] 假说所依赖的陈述，因此它们在此与保护其余部分的 [Fail] 一起被检查。
*)
Check (wide_round_trip_needs_point :
         (∀ (q : _2) (e : q ~{_2}~> TwoY),
            IsWideEqualizer two_empty_family q e
            → IsALimit (AWide two_empty_family) q) → False).
Check (wide_coround_trip_needs_point :
         (∀ (q : _2) (e : TwoX ~{_2}~> q),
            IsWideCoequalizer two_empty_family q e
            → IsAColimit (AWide two_empty_family) q) → False).

(**
The instrument is not a no-op: a [Fail] on a succeeding command
    aborts compilation with "The command has not failed!".  The
    following line, uncommented, would do exactly that — it is left as a
    comment because a passing build cannot contain it.

      Fail Definition probe_wide_hom_is_index :
  (ParX ~{WideParallel bool}~> ParY) = bool := eq_refl.

    The controls above are the standing check that the [Fail]s are not
    passing for the wrong reason.

--------
该工具并非无操作：在后续命令上使用 [Fail] 会中止编译，并显示“命令未失败！”。以下未注释的代码行本会完全这样做——它被保留为注释，因为一个通过构建不能包含它。

  Fail Definition probe_wide_hom_is_index :
  (ParX ~{WideParallel bool}~> ParY) = bool := eq_refl.

上述控制是用于检查 [Fail] 不是因为错误原因而通过的常规检查。
*)
