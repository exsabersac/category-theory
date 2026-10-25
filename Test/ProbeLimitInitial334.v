(**
* Boundary probes for Structure/Limit/Initial.v (issue #334)

    Mac Lane CWM 2nd ed. §III.4 Exercise 3, book p. 72; Fong-Spivak
    *Seven Sketches* §3.5.3 Ex 3.98; Riehl *CTiC* 2nd ed. §3.1.

    This file pins the three measurements the target's header records and
    states are pinned nowhere.  The target is right that they are
    measurements; this file is where they stop being unguarded.

    THREE NEGATIVES OF TWO KINDS, kept lexically apart:

      * CONVERSION -- [initial_leg I F initial_obj] is not [id] on the
        nose.  It is [fmap[F] zero] at the initial object, and [zero]
        there is only [≈]-equal to [id] (by [zero_unique]), not
        convertible to it; [F] then has no reason to send it to [id]
        definitionally.  The target proves the [≈] form
        ([initial_leg_id]) and says plainly that the strict form fails.

      * CONVERSION (different cause; and an earlier draft of this file
        wrote the statement with [initial_Cones_Terminal] applied to no
        arguments, so its [Fail] fired on a MISSING ARGUMENT rather than
        on the refutation -- a false guard, caught by strip-verifying the
        failure KIND) -- the WHOLE-RECORD identity
        [Limit_Cones … = initial_Limit] is refuted, although the CONE
        components agree by [eq_refl] (that is the target's shipped
        [initial_Cones_strict]).  What differs is the rebuilt universal
        property, not the data.

      * FORMABILITY (universe), THREE of them -- the index category's
        hom-and-proof universes get identified with the ambient
        category's, and an earlier draft of this file blamed [IsALimit]
        ALONE on the strength of an [ACone] control.  That inference was
        invalid.  With J's levels declared apart, [ACone c F] and [Cone F]
        are formable, but [cone_leg N x]
        (Structure/Limit/Preservation.v), [IsLimitCone N] AND
        [IsALimit F c] (Structure/Limit.v) are all rejected with the
        same message.  Two of the three donors ARE cone vocabulary, so the
        control rules out [ACone]/[Cone] and nothing further; all three
        rejections are pinned below.  None of the three carries universe
        annotations, so this stays a repairable annotation defect of the
        family this repo has met before, NOT inherent content, and not
        claimed unavoidable here.

    Every negative is paired with a positive control NAMING ITS OWN
    CONSTANTS.  The measured rename-simulation score is at the end, over
    the constants the NEGATIVES name and no others.

--------
* Structure/Limit/Initial.v 的边界探针（问题 #334）

Mac Lane 《CWM》第2版 §III.4 练习 3，书第72页；Fong-Spivak 《七个草图》§3.5.3 练习 3.98；Riehl 《CTiC》第2版 §3.1。

此文件固定了目标的头部记录的三个测量值，而状态没有被固定。目标是正确的，它们确实是测量值；这个文件是它们不再未受保护的地方。

两类三重否定，在词汇上保持分开：

* 转换 -- [initial_leg I F initial_obj] 并不是正好等于 [id]。它在初始对象上是 [fmap[F] 零]，而且 [zero] 那里只有 [≈] 等于 [id]（通过 [zero_unique]），不能转换为它；因此 [F] 没有理由按定义将其发送到 [id]。目标证明了 [≈] 形式（[initial_leg_id]）并明确说明严格形式失败。

* 转换（原因不同；而且此文件的早期草稿将语句写成对没有参数的 [initial_Cones_Terminal] 应用，因此它的 [Fail] 在缺失参数上触发，而不是在反驳上触发——这是一个错误保护，通过剥离验证失败类型来捕获）——整条记录的身份 [Limit_Cones … = initial_Limit] 被反驳，尽管 CONE 组件通过 [eq_refl] 一致（即目标发布的 [initial_Cones_strict]）。不同之处在于重建的通用属性，而不是数据。

* 可构造性（宇宙），其中有三个——索引范畴的 hom-and-proof 宇宙被识别为与环境范畴相同，而本文件的早期草稿仅将 [IsALimit] 归咎于 [ACone] 控制的强度。 这种推论是无效的。 在 J 的级别被声明为分开的情况下，[ACone c F] 和 [Cone F] 是可构造的，但 [cone_leg N x]（Structure/Limit/Preservation.v）、[IsLimitCone N] 和 [IsALimit F c]（Structure/Limit.v）都遭到相同信息的拒绝。 三个捐赠者中有两个是锥体词汇，因此控制排除了 [ACone]/[Cone]，没有其他影响；三个拒绝信息均记录如下。 三者都没有携带宇宙注解，因此这仍然是该仓库之前遇到的可修复注解缺陷，而非固有内容，并且此处也不认为是不可避免的。

每个阴性对照都配有一个阳性对照，命名其自身的常数。测量的重命名-模拟得分在最后，是在阴性对照命名的常数上，而不是其他常数上。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Cones.
Require Import Category.Instance.Cones.Limit.
Require Import Category.Instance.One.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Ordinal.
Require Import Category.Structure.Limit.Initial.

(**
** Instrument check

    A [Fail] that never fails would make every negative below vacuous.

--------
** 仪器检查

    一个永不失败的 [Fail] 会使下面的每个负面都变得无效。
*)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(** ** Negative 1 (CONVERSION): the leg at the initial object is not [id] / ** 负 1（转换）：初始对象的腿不是 [id] *)

Section LegAtInitial.

Context (J C : Category) (I : @Initial J) (F : J ⟶ C).

Fail Definition probe_initial_leg_is_id :
  initial_leg I F (@initial_obj J I) = id := eq_refl.

(*
Positive controls naming the negative's own constants.  The [≈] form IS
   proved in the target, and every constant in the rejected equation is
   independently well-formed here.

--------
正控命名负控自身的常量。[≈] 形式在目标中被证明，而被拒绝方程中的每个常量在这里都是独立良构的。
*)
Check (initial_leg_id I F).
Check (initial_leg I F).
Check (@initial_obj J I).

End LegAtInitial.

(** ** Negative 2 (CONVERSION, different cause): the whole-record identity / ** 负2（转换，不同原因）：全记录身份 *)

Section WholeRecord.

Context (J C : Category) (I : @Initial J) (F : J ⟶ C).

Fail Definition probe_limit_cones_record :
  @Limit_Cones J C F (initial_Cones_Terminal I F)
    = initial_Limit I F := eq_refl.

(*
Positive controls.  The CONE components DO agree by [eq_refl] -- that is
   the target's own Example -- so what fails is the rebuilt universal
   property, not the data.

--------
阳性对照。CONE 组件确实通过 [eq_refl] 一致——也就是目标自身的示例——所以失败的是重建的通用属性，而不是数据。
*)
Check initial_Cones_strict.
Check (@Limit_Cones J C F).
Check (initial_Limit I F).
Check (initial_Cones_Terminal I F).

End WholeRecord.

(**
** Negative 3 (FORMABILITY, universe): IsALimit identifies J's levels

    A DIFFERENT KIND from 1 and 2.

--------
** 负3（可形成性，宇宙）：IsALimit 确定了 J 的级别

    与 1 和 2 不同的类型。
*)

Section UniverseIdentification.

Universe jo jh jp co ch cp.
Constraint jh < jp.

Context (J : Category@{jo jh jp}) (C : Category@{co ch cp})
        (F : J ⟶ C) (c : C) (x : J) (N : Cone F).

(*
Controls: these two pieces of cone vocabulary ARE formable with J's hom
   and proof levels declared APART.  They rule out [ACone] and [Cone] as
   the donor -- and nothing more, which is exactly the correction this
   file records.

--------
控制：这两个锥形词汇可以用 J 的同质和证明级别分开形成。它们排除了 [ACone] 和 [Cone] 作为供体——没有其他，这正是该文件记录的更正。
*)
Check (ACone c F).
Check (Cone F).

(**
** Negative 4 (FORMABILITY, universe): cone_leg identifies them too

    Same KIND as negatives 3 and 5, different CONSTANT.  This is the one
    that refutes the earlier draft's attribution: [cone_leg] is cone
    vocabulary and is rejected at the same levels.  It is also the donor
    this development meets FIRST -- [initial_med]'s body is
    `cone_leg N initial_obj`, and [initial_med] already displays
    `u0 = u2` while its type mentions no [IsALimit] at all.

--------
** 负4（可形成性，宇宙）：cone_leg 也识别它们

与负3和负5同类，但常数不同。这就是
反驳早期草案归因的那个：[cone_leg] 是 cone 词汇，并在相同层次被拒绝。它同时也是该发展最先遇到的供体——[initial_med] 的主体是 `cone_leg N initial_obj`，而 [initial_med] 已经显示 `u0 = u2`，同时其类型完全没有提到 [IsALimit]。
*)

Fail Check (cone_leg N x).

(** ** Negative 5 (FORMABILITY, universe): IsLimitCone likewise / ** 负 5（可形成性，宇宙）：IsLimitCone 同样 *)

Fail Check (IsLimitCone N).

End UniverseIdentification.

(* Controls naming the two constants of negatives 4 and 5. / 控制命名负数 4 和 5 的两个常量。 *)
Check @cone_leg.
Check @IsLimitCone.

(*
Control naming [IsALimit] itself.  The rename simulation over the
   constants in the NEGATIVES found it named by no control -- it occurred
   only inside the Fail above -- so that negative would have gone
   vacuously green on a rename.  Recorded rather than quietly added.

--------
控制命名 [IsALimit] 本身。对 NEGATIVES 中的常量进行重命名模拟时，发现它没有被任何控制命名——它只出现在上面的 Fail 中——所以该负值在重命名时本会徒然变为绿色。记录而不是悄悄添加。
*)
Check @IsALimit.

Section UniverseIdentification2.

Universe jo2 jh2 jp2 co2 ch2 cp2.
Constraint jh2 < jp2.

Context (J : Category@{jo2 jh2 jp2}) (C : Category@{co2 ch2 cp2})
        (F : J ⟶ C) (c : C).

Fail Check (IsALimit F c).

End UniverseIdentification2.

(**
** Applied controls for negatives 3-5

    [Check @IsALimit] above is name resolution ONLY; it cannot show that
    the three negatives fire on the CONSTRAINT rather than on some
    unrelated defect in how they are written.  These do: the SAME three
    applications, at levels DECLARED but deliberately NOT constrained
    apart, all elaborate.

--------
** 针对负数 3-5 的应用控制

    上面的 [Check @IsALimit] 仅用于名称解析；它不能显示这三个负数是在约束条件上触发的，而不是因为它们的写法中存在某些无关的缺陷。它们确实如此：相同的三个应用程序，在声明的级别上，但故意未单独约束，都很详尽。
*)

Section UniverseControl.

Universe jo3 jh3 jp3 co3 ch3 cp3.

Context (J : Category@{jo3 jh3 jp3}) (C : Category@{co3 ch3 cp3})
        (F : J ⟶ C) (c : C) (x : J) (N : Cone F).

Check (IsALimit F c).
Check (cone_leg N x).
Check (IsLimitCone N).

End UniverseControl.

(** ** Controls for the delivered results / ** 已交付结果的控制 *)

Check initial_leg.
Check initial_cone.
Check initial_med.
Check initial_med_commutes.
Check initial_med_unique.
Check initial_IsLimitCone.
Check initial_IsALimit.
Check limiting_iff_initial_leg_iso.
Check terminal_inj.
Check terminal_cocone.
Check terminal_IsColimitCocone.
Check terminal_IsAColimit.
Check colimiting_iff_terminal_inj_iso.
Check One_Initial.
Check point_IsALimit.
Check point_Cones_strict.
Check Ordinal_Succ_Terminal.
Check ordinal_succ_IsAColimit.
Check Omega_Initial.
Check Omega_no_Terminal.

(** ** Non-vacuity controls / ** 非空性控制 *)

Check point_Sets_med.
Check point_Sets_separates.
Check ordinal_omega_nonconstant.
Check ord_top_neq_bot.

(**
** MEASURED RENAME-SIMULATION SCORE

    The constants the NEGATIVES name:

      Negative 1: [initial_leg], [initial_obj]
      Negative 2: [Limit_Cones], [initial_Cones_Terminal], [initial_Limit]
      Negative 3: [IsALimit]
      Negative 4: [cone_leg]
      Negative 5: [IsLimitCone]

    That is EIGHT.  An earlier draft of this file scored 7/7 by listing
    [ACone] under negative 3 -- but [ACone] occurs in NO [Fail] here; it
    is a control, and including it inflated the denominator in the very
    sentence that denied padding.  It is dropped.  All eight are named by
    a positive control above, so renaming any one breaks this file rather
    than turning its negative vacuously green.  Score: 8/8, counted
    rather than recalled.

--------
** 测量后的重命名模拟得分

负数的常量名称：

  负数1：[initial_leg], [initial_obj]
  负数2：[Limit_Cones], [initial_Cones_Terminal], [initial_Limit]
  负数3：[IsALimit]
  负数4：[cone_leg]
  负数5：[IsLimitCone]

那是八个。在此文件的早期草稿中，通过在负数3下列出[ACone]获得了7/7分——但[ACone]在此处没有出现在任何[Fail]中；它是一个对照，包含它会膨胀那个否认填充的句子中的分母。因此它被删除了。上面一个正对照命名了全部八个，因此重命名其中任何一个都会破坏此文件，而不是让其负数自动变绿。得分：8/8，计数而不是回忆。
*)
