Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Forgetful.
Require Import Category.Instance.Top.Discrete.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Sets.Pointed.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Abelianization.
Require Import Category.Instance.Grp.Abelianize.
Require Import Category.Instance.Grp.Completion.
Require Import Category.Instance.CMon.Grothendieck.
Require Import Category.Instance.Sets.Pointed.Free.
Require Import Category.Instance.Rng.Free.

Generalizable All Variables.

(**
* Boundary probe for issue #312 (maclane:III.1:ex3)

    Each delivered file carries its own [Fail] probes.  Those guard their
    measurements from INSIDE, which is exactly what a whole-file rename
    cannot test: rename a definition and its in-file [Fail] renames with
    it, so the guard goes vacuously green.  This file restates the
    cross-file boundaries from OUTSIDE, each against a positive control
    that NAMES the same constants, so renaming any of them breaks this
    file loudly.

    Negatives are grouped BY KIND and kept lexically apart.  Each was
    stripped of its [Fail] once and the resulting error read; the kind
    recorded is the kind that actually fired.

--------
* 用于问题 #312 的边界探测 (maclane:III.1:ex3)

每个交付的文件都包含自己的 [Fail] 探针。它们从内部保护自己的测量，这正是整体文件重命名无法测试的：重命名一个定义，其文件内的 [Fail] 也会随之重命名，所以保护探针便会虚设为绿色。这个文件从外部重新说明了跨文件边界，每个边界都针对一个正控制，该控制命名了相同的常量，因此重命名其中任何一个都会明显打破此文件。

负例按类型分组，并在词法上保持分离。每个负例曾被剥离过一次 [Fail] 并读取了由此产生的错误；记录的类型是实际触发错误的类型。
*)

(**
** Positive controls

    Every constant named in a negative below is also named here outside
    any [Fail], so a rename cannot silently vacate a guard.

--------
** 阳性对照

下面负面中命名的每个常量也在这里在任何 [Fail] 之外被命名，因此重命名不会悄无声息地使保护失效。
*)

Check @Top_Discrete.
Check @Top_Forget.
Check @discrete_universal.
Check @disc_unit.
Check @abelianize_left.
Check @Abelianization_Functor.
Check @abelianize_adjunction.
Check @abelianize_adjunction_via_transform.
Check @completion_adjunction.
Check @grothendieck_adjunction.
Check @free_pointed_adjunction.
Check @free_rng_ab_universal_arrow.

(**
** Positive controls: the four rows of Mac Lane §III.1 Exercise 3

    Row (b) is discharged by #400's Instance/Rng/Free.v and is CITED
    here rather than rebuilt, which is what that issue's dependency note
    on #312 requires.

--------
** 阳性对照：Mac Lane §III.1 练习 3 的四行

    行 (b) 已由 #400 的 Instance/Rng/Free.v 处理并被引用，而不是重建，这正是 #312 的依赖说明所要求的。
*)

Example row_a_abelianization : Grp ⟶ Ab := abelianize_left.
Example row_b_free_ring (A : Ab) : UniversalArrow A Rng_Forget_Ab :=
  free_rng_ab_universal_arrow A.
Example row_d_basepoint : Sets ⟶ PointedSets := FreePointed.

(**
** FORMABILITY negative: the discrete adjunction cannot be packaged

    This is #312's one genuinely obstructed row, and the obstruction is
    PRE-EXISTING, not introduced here: Instance/Top/Forgetful.v
    records that a functor out of [Top] lands in a lifted [Sets] while a
    functor into [Top] must come from the unlifted one, so an
    [Adjunction] record "would need both functors to share ONE Sets, at
    levels o and h simultaneously, with o < h: the packaged triple is
    unformable at every universe assignment."

    The controls above show BOTH functors exist and are nameable, so the
    negative is about the packaging and not about a missing constant.
    Stripped, it reports a [Functor] universe mismatch between the two
    instantiations of [Sets] — a FORMABILITY failure, not a conversion
    one.  Instance/Top/Discrete.v therefore delivers the universal
    property written out ([discrete_universal]) and the unit
    ([disc_unit]) rather than a packaged record, and claims nothing more.

--------
** 可成形性负面：离散附加无法打包

这是 #312 真正受阻的一行，而阻塞是预先存在的，并非在此引入：Instance/Top/Forgetful.v 记录了一个从 [Top] 出发的函子落在升高的 [Sets] 中，而一个进入 [Top] 的函子必须来自未升高的那个，因此一个 [Adjunction] 记录“将需要两个函子共享同一个集合集（Sets），同时在 o 和 h 级别，并且 o < h：在每一个宇宙分配下，这个封装的三元组都是无法形成的。”

上方的控件显示两个函子都存在且可命名，因此否定不是关于缺少常量，而是关于封装。剥离后，它报告了两个 [Sets] 实例之间的 [Functor] 宇宙不匹配——这是一个可形成性错误，而不是转换错误。因此，Instance/Top/Discrete.v 提供了写出的通用属性（[discrete_universal]）和单元（[disc_unit]），而不是封装记录，并且不声明其他内容。
*)

Fail Check (Top_Discrete ⊣ Top_Forget).

(**
** CONVERSION negative: the produced left adjoint is not the
       pre-existing functor on the nose

    [LeftAdjointFunctorFromUniversalArrows] PRODUCES a left functor, so
    [abelianize_adjunction] is stated against [abelianize_left] rather
    than against the pre-existing [Abelianization_Functor].  The two
    agree on objects definitionally and on arrows up to [≈]
    (Instance/Grp/Abelianize.v's [abelianize_left_obj] and
    [abelianize_left_iso]), but they are NOT the same functor record —
    the law fields are rebuilt.  Pinned so that a later edit cannot
    quietly assert the stronger identification.

--------
** 转换负向：生成的左伴随不是原有的函子本身

[LeftAdjointFunctorFromUniversalArrows] 生成一个左函子，因此 [abelianize_adjunction] 是针对 [abelianize_left] 陈述的，而不是针对原有的 [Abelianization_Functor]。两者在对象上定义上是一致的，并且在箭头上到 [≈]（一阶/群/阿贝尔化.v 的 [abelianize_left_obj] 和 [abelianize_left_iso]）是一致的，但它们不是同一个函子记录——定律字段是重新构建的。固定，以便后续编辑不能悄悄地断言更强的等同。
*)

Fail Example probe_left_is_pre_existing :
  abelianize_left = Abelianization_Functor := eq_refl.

(**
** Instrument check

    A [Fail] that must fail for a reason having nothing to do with #312,
    so a broken [Fail] mechanism would be visible here rather than
    silently passing every negative above.  Deliberately scope-free: a
    numeral would risk failing on a missing scope delimiter instead of on
    the proposition.

--------
** 仪器检查

必须因为与 #312 无关的原因而失败的 A [Fail]，因此坏掉的 [Fail] 机制会在这里可见，而不是在上述每个否定情况中静默通过。特意没有作用域限制：一个数字可能会因为缺少作用域分隔符而失败，而不是因为命题本身。
*)

Fail Example probe_312_instrument : (true = false) := eq_refl.
