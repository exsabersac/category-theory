(**
* Probe: the universe boundary of Structure/Group/Representable.v

    Issue #341 (Mac Lane CWM 2nd ed. section III.6 Proposition 1 and
    remark 2).  The target file pins four refutations of its own, and all
    four are CONVERSION failures (`cannot unify`):
    `data_psh_data_law`, `data_psh_data_whole`, `rt_mul_strict` and
    `exp_mempty_is_Hom_Monoid`, each with a positive control beside it,
    and three of the four additionally with a proved `≈` repair.
    `data_psh_data_whole` is the exception and the asymmetry is not an
    oversight: no setoid on `HomGroupData` exists anywhere in the tree,
    so an `≈` statement about the whole record is not even formable, and
    its control is therefore the bare `data_psh_data_whole_control`.
    (An earlier revision of this sentence claimed a control OR a repair
    for each and was wrong about that one on both counts -- it had
    neither, `data_psh_data_law_control` being a control for the LAW
    FIELD rather than for the record.)

    This file supplies the OTHER kind: FORMABILITY, which needs a
    section declaring universe levels strictly apart.

    CORRECTION, added later: this file originally said a library file
    "cannot state" that kind, because it "cannot carry such a
    `Constraint` without constraining itself".  THAT IS FALSE.
    `Instance/Fun/Group.v` (issue #342) carries exactly such probes
    in-file, as `Universes`/`Constraint` inside a `Section` with
    `Context` variables and `Check` controls; the declarations are
    discharged at `End`, and a downstream consumer that imports the file
    can still declare its own levels strictly apart.  Measured, not
    assumed.  A separate Test file is therefore a CHOICE, not a
    necessity.

    THREE NEGATIVES, ALL FORMABILITY, plus a POSITIVE MEASUREMENT.

      * Negatives 1-3 attribute the hom = proof identification that every
        constant of the target carries in its BINDER.  Three subjects are
        rejected INDEPENDENTLY under `Constraint uh < up` -- the two
        ambient donors `Cartesian` and `Terminal`, and the target's OWN
        central record `HomGroupData` -- while a control naming a hom of
        such a category at those very levels is accepted.  Testing all
        three separately is the point: blaming whichever comes to mind
        first would be wrong.

        `GroupObject` is deliberately NOT among them, and the reason is a
        defect this file was written to avoid.  An earlier revision wrote
        negative 3 as

          Fail Check (fun (C : Category@{uo uh up}) (M : @Monoidal C)
                          (x : C) => @GroupObject C M x).

        and labelled it the `GroupObject` donor.  That is FALSE:
        elaboration never reaches `GroupObject`, because `@Monoidal C` in
        the binder is rejected first -- the error lands at character 52 of
        that line, which is the `C` argument of `Monoidal`.  (`GroupObject`
        in fact takes a `CartesianMonoidal`, not a `Monoidal`, so the line
        was doubly wrong.)  A class whose binder is already identified by
        an earlier argument cannot be tested apart from that argument;
        whether `GroupObject` contributes an identification OF ITS OWN is
        UNKNOWN, not refuted.  This is the same trap the sibling probe for
        issue #340 records for `MonoidObject` under `Monoidal`.

      * The POSITIVE is `HomGroupData`, and it is a sharper instance of
        the rule the index states elsewhere than the target file's own
        siblings: A UNIVERSE IDENTIFICATION CAN HIDE ENTIRELY IN THE
        BINDER.  `HomGroupData@{u u0}`'s constraint block is LITERALLY
        EMPTY -- `(* u u0 |=

--------
* 探测器：Structure/Group/Representable.v 的宇宙边界

问题 #341（Mac Lane CWM 第二版第 III.6 节命题 1 和备注 2）。目标文件自身有四个反驳，并且这四个都是 CONVERSION 失败（`cannot unify`）：`data_psh_data_law`、`data_psh_data_whole`、`rt_mul_strict` 和 `exp_mempty_is_Hom_Monoid`，每个旁边都有一个正向控制，其中四个中的三个额外具有已证明的 `≈` 修复。`data_psh_data_whole` 是例外，这种不对称并非疏忽：在树中的任何地方都不存在 `HomGroupData` 的集合体（setoid），因此关于整个记录的 `≈` 声明都无法形成，因此它的控制只是简单的 `data_psh_data_whole_control`。（本句的早期修订版声称每个都有一个控制或修复，但在这两点上都是错误的——它什么都没有，`data_psh_data_law_control` 是 LAW 字段的控制，而不是记录的控制。）

这个文件提供了另一种类型：可成形性，它需要一个严格区分宇宙层的声明部分。

更正，补充说明：该文件最初表示一个库文件“不能声明”那种类型，因为它“无法携带这样的 `Constraint` 而不约束自身”。这是错误的。`Instance/Fun/Group.v`（问题 #342）正是在文件内部携带了这样的探针，作为 `Section` 内带有 `Context` 变量和 `Check` 控制的 `Universes`/`Constraint`；这些声明在 `End` 时被释放，下游导入该文件的使用者仍然可以严格独立地声明自己的层级。经过测量，而非假设。因此，单独的测试文件是一个选择，而非必需。

三个阴性，全部可成型，加上一个阳性测量。

* 否定项1-3归因于同源 = 证明识别，即目标的每个常量在其绑定器中都携带的特性。 在 `约束 uh < up` 下三个主体是独立被拒绝的 —— 两个环境供体 `Cartesian` 和 `Terminal`，以及目标自身的中央记录 `HomGroupData` —— 而在这些层面命名该类别的同源的控制则被接受。 分别测试这三个是重点：先想到的那个来归咎是错误的。

`GroupObject` 故意不包括在其中，原因是为了避免本文件编写时的一个缺陷。早期的版本将负3写作

检查失败 (函数 (C : Category@{uo uh up}) (M : @Monoidal C M) (x : C) => @GroupObject C M x)。

并将其标记为 `GroupObject` 捐赠者。这是错误的：展开过程永远不会到达 `GroupObject`，因为绑定器中的 `@Monoidal C` 首先被拒绝——错误出现在该行的第 52 个字符，也就是 `Monoidal` 的 `C` 参数。(`GroupObject` 实际上接受的是 `CartesianMonoidal`，而不是 `Monoidal`，因此这一行是双重错误。) 一个绑定器已经被早先的参数确定的类，不能单独测试该参数；`GroupObject` 是否贡献了它自己的标识是未知的，并未被否定。这与问题 #340 下的兄弟探针记录 `MonoidObject` 在 `Monoidal` 下的陷阱相同。

* 积极的例子是“HomGroupData”，这是一个更清晰的实例
        索引中规定的规则在目标文件以外的地方
        兄弟姐妹：宇宙认同可以完全隐藏在
        BINDER。'HomGroupData@{u u0}' 的约束块字面意义上是
        EMPTY -- '（* u u0 |=
*)` -- yet its binder reads
        `forall {C : Category@{u u0 u0}}`, identifying hom with proof by
        reusing the level variable.  A reader who checks only the block
        concludes "no identification" and is wrong.  `About` it and read
        BOTH.

    Measured, not assumed: each negative below was stripped of its `Fail`
    once and its error read in full; all three are genuine universe
    inconsistencies naming the declared levels, with zero `cannot unify`.
    The file is rename-simulated with the `Require` lines PRESERVED, since
    two of the guarded names also name modules and renaming those lines
    would break the copy on a missing module rather than on the guard --
    reading as a pass. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoid.
Require Import Category.Structure.Group.
Require Import Category.Structure.Group.Representable.

Generalizable All Variables.

(** ** Negatives 1-3 (FORMABILITY): three donors identify hom with proof / ** Negatives 1-3 (FORMABILITY): three donors identify hom with proof / ** 否定项 1-3（可形成性）：三个捐赠者通过证据确认同型 *)

Section Donors.

Universe uo uh up.
Constraint uh < up.

(* Control: a hom-set of such a category is perfectly formable here. / Control: a hom-set of such a category is perfectly formable here. / 控制：这样的范畴的同态集合在这里可以完美形成。 *)
Check (fun (C : Category@{uo uh up}) (x y : C) => x ~> y).

(*
Controls: each guarded donor exists at UNCONSTRAINED levels.  Without
   these, a rename of any of them would leave its negative succeeding on a
   reference-not-found error rather than on the universe boundary.

--------
控制：每个受保护的捐赠者都存在于无限制的水平。没有这些，重命名它们中的任何一个将会导致其负值在遇到未找到引用的错误时，而不是在宇宙边界时成功。
*)
Check @Cartesian.
Check @Terminal.
Check @GroupObject.
Check @HomGroupData.

(* NEGATIVE 1. / 否定 1. *)
Fail Check (fun (C : Category@{uo uh up}) => @Cartesian C).

(* NEGATIVE 2. / 负 2. *)
Fail Check (fun (C : Category@{uo uh up}) => @Terminal C).

(*
NEGATIVE 3.  [HomGroupData] is the target's OWN central record, and
   unlike [GroupObject] it takes no monoidal argument -- its signature is
   [forall {C : Category}, obj[C] -> Type] -- so the rejection is
   attributable to it rather than to something elaborated before it.

--------
否定 3. [HomGroupData] 是目标自身的中央记录，并且与 [GroupObject] 不同，它不接受单元参数——它的签名是 [forall {C : Category}, obj[C] -> 类型] ——因此拒绝是由它本身引起的，而不是由它之前的某些展开引起的。
*)
Fail Check (fun (C : Category@{uo uh up}) (e : C) => @HomGroupData C e).

End Donors.

(**
** The positive measurement: an identification hiding in the BINDER

    Not a refutation -- a definition whose universe signature IS the
    measurement.  `About HomGroupData` prints an EMPTY constraint block
    over a binder that identifies hom with proof.

--------
** 正面测量：隐藏在 BINDER 中的一个识别

    不是反驳——是一个定义，其宇宙签名就是测量。`About HomGroupData` 打印了一个空的约束块，位于一个用证明标识 hom 的绑定器上。
*)

Definition probe_homgroupdata_binder
  `{C : Category} (e : C) : Type := HomGroupData e.

(*
About probe_homgroupdata_binder.
   About HomGroupData.
     HomGroupData@{u u0} :
       forall {C : Category@{u u0 u0}}, obj -> Type@{max(u,u0)}
     (* u u0 |=

--------
关于 probe_homgroupdata_binder。
   关于 HomGroupData。
     HomGroupData@{u u0} :
       forall {C : Category@{u u0 u0}}, obj -> Type@{max(u,u0)}
     (* u u0 |="
*)                      <-- EMPTY block
                    ^^^^^^^^^^^^^^^^^^   <-- hom = proof in the BINDER *)

(**
** What this file does NOT claim

    The identification is the DONORS' doing and is NOT claimed
    unavoidable; no lift was attempted.  Negative 3 DOES show
    [HomGroupData] rejected on its own, with no donor elaborated before
    it, so the rejection is attributable to that record; what is NOT
    established is whether it would still identify were [Category] itself
    stated with its levels apart.  And no separation is proved between the
    representable and the internal formulations.

--------
** 此文件未声明的内容

    识别是捐赠者的行为，并未声明为必然；未尝试解除。负3确实显示了[HomGroupData]自身被拒绝，之前没有说明捐赠者，因此拒绝归因于该记录；尚未确定的是，如果单独说明[Category]及其水平，它是否仍能进行识别。并且未证明可表示形式与内部配方之间存在分离。
*)
