(**
* Boundary probes for Structure/Ring.v and Structure/Lattice.v (#340)

    Mac Lane CWM 2nd ed. §III.6, book p. 75.

    The two targets already ship FOUR refutations of their own, and all
    four are CONVERSION (`Structure/Ring.v`,,
    `Structure/Lattice.v`, -- the Sets round trips, whole record
    and internal `Monoid` record respectively; each was stripped and each
    gives exactly one `cannot unify`, zero universe and zero typing
    errors).  This file pins what they CANNOT state: the universe
    boundary, which needs a section declaring levels strictly apart.

    CORRECTION, added later: this file originally continued "...which a
    library file cannot carry without constraining itself."  THAT IS
    FALSE.  `Instance/Fun/Group.v` (issue #342) carries exactly such
    probes in-file, as `Universes`/`Constraint` inside a `Section` with
    `Context` variables and `Check` controls; the declarations are
    discharged at `End`, and a downstream consumer that imports the file
    can still declare its own levels strictly apart.  Measured, not
    assumed.  So a separate Test file is a CHOICE here, not a necessity,
    and the in-file form is arguably better since it keeps a refutation
    beside what it refutes.

    THREE NEGATIVES, ALL FORMABILITY, plus a POSITIVE MEASUREMENT.

      * Negatives 1-3 attribute the hom = proof identification that every
        class in both files carries.  THREE donors do it INDEPENDENTLY --
        `Cartesian`, `Terminal` and `Monoidal` -- each rejected under
        `Constraint uh < up` while a control naming a hom at those very
        levels is accepted.  Testing all three separately is the point:
        blaming whichever comes to mind first would be wrong, and the
        classes here take all three.  `MonoidObject` is NOT a fourth
        donor and is not probed as one: its [Monoidal] argument is
        rejected first, so it cannot be tested apart from `Monoidal`,
        and whether it identifies anything of its own is UNKNOWN.

      * The POSITIVE is `dup_left`/`dup_right`, and it is the sharpest
        instance in this tree of a rule the index states elsewhere: A
        UNIVERSE IDENTIFICATION CAN HIDE ENTIRELY IN THE BINDER.
        `dup_left@{u u0}`'s constraint block is LITERALLY EMPTY --
        `(* u u0 |=

--------
* Structure/Ring.v 和 Structure/Lattice.v 的边界探针 (#340)

Mac Lane《CWM》第2版 §III.6，第75页。

这两个目标已经提供了他们自己的四个反驳，且全部四个都是转换（`Structure/Ring.v`，`Structure/Lattice.v`——分别是集合的往返、整个记录和内部的 `Monoid` 记录；每个都被剥离过，每个都只给出一个“无法统一”，没有宇宙错误也没有类型错误）。这个文件明确了他们无法声明的内容：宇宙边界，需要一个严格分开的层级声明的部分。

更正，后添加：这个文件最初接着写道“……这是一个库文件在不约束自己的情况下无法承载的。” 这是错误的。 `Instance/Fun/Group.v`（问题 #342）正是在文件内部承载了这样的探针，作为 `Universes`/`Constraint`，位于带有 `Context` 变量和 `Check` 控制的 `Section` 中；这些声明在 `End` 时被清除，而导入该文件的下游使用者仍然可以严格地声明自己的层级。 这是经过测量的，并非假设的。因此，一个单独的测试文件在这里是一个选择，而不是必需的，并且文件内部的形式可以说更好，因为它将反驳放在了其所反驳的内容旁边。

三个阴性，全部可成型，加上一个正向测量。

* 否定 1-3 归因于同态 = 证明识别，这是两个文件中的每个类都具有的。三个捐赠者独立完成此操作 -- `Cartesian`、`Terminal` 和 `Monoidal` -- 每个都在 `Constraint uh < up` 下被拒绝，而在这些层次上命名同态的控制则被接受。分别测试这三者的目的就是：仅仅责怪最先想到的那个是错误的，这里的类包含了三者。`MonoidObject` 并不是第四个捐赠者，也不会作为一个被探测：它的 [Monoidal] 参数首先被拒绝，因此无法与 `Monoidal` 分开测试，是否能识别它自己的任何内容尚不清楚。

* POSITIVE 是 `dup_left`/`dup_right`，它是在这棵树中最尖锐的一个例子，
        对应规则在其他地方说明：一个宇宙识别可以完全隐藏在绑定器中。
        `dup_left@{u u0}` 的约束块实际上是空的 --
        `(* u u0 |="
*)` -- yet its binder reads
        `C : Category@{u u0 u0}`, identifying hom with proof by reusing
        the level variable.  A reader who checks only the block concludes
        "no identification" and is wrong.  Run `About dup_left` to see it.
        Inherited from `Cartesian`, not introduced by either target.

    What the OBJECT universe does is worth as much as what the hom does:
    it stays FREE in all four classes, appearing only in `<=` bounds.

    Every negative is paired with a positive control naming its own
    constants.  The measured rename-simulation score is at the end, over
    the constants the NEGATIVES name and no others, with `Require` lines
    preserved. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Structure.Monoid.
Require Import Category.Structure.Group.
Require Import Category.Structure.Ring.
Require Import Category.Structure.Lattice.

Generalizable All Variables.

(**
** Instrument check

    A [Fail] that never fails would make every negative below vacuous.

--------
** 仪器检查

    一个永不失败的 [Fail] 会使下面的每个负面都变得无效。
*)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(**
** Negatives 1-3 (FORMABILITY): three INDEPENDENT donors identify hom
       with proof

    Each is rejected under `Constraint uh < up` while the control shows a
    hom-set of such a category is perfectly formable at those levels.

--------
** 消极例子 1-3（可形成性）：三位独立捐赠者确认 hom 并提供证明

每个都在 `Constraint uh < up` 下被拒绝，而对照组显示该类别的同态集合在这些层面上是完全可形成的。
*)

Section Donors.

Universe uo uh up.
Constraint uh < up.

(* Control: a hom-set of such a category exists. / 控制：这样的范畴的同态集存在。 *)
Check (fun (C : Category@{uo uh up}) (x y : C) => x ~> y).

(*
Controls: all three donors exist at UNCONSTRAINED levels.  Without
   these, a rename of any of them would leave its negative succeeding on a
   reference-not-found error rather than on the universe boundary.

--------
控制：三个供体都存在于不受限制的水平。没有这些，其中任何一个的重命名都会使其负值在引用未找到错误上成功，而不是在宇宙边界上成功。
*)
Check @Cartesian.
Check @Terminal.
Check @MonoidObject.
Check @Monoidal.

(* NEGATIVE 1. / 否定 1. *)
Fail Check (fun (C : Category@{uo uh up}) => @Cartesian C).

(* NEGATIVE 2. / 负 2. *)
Fail Check (fun (C : Category@{uo uh up}) => @Terminal C).

(*
NEGATIVE 3.  The donor is [Monoidal], NOT [MonoidObject].  An earlier
   revision of this file wrote the negative as

     Fail Check (fun (C : Category@{uo uh up}) (M : @Monoidal C)
                     (x : C) => @MonoidObject C M x).

   and labelled it the [MonoidObject] donor.  That was FALSE: elaboration
   never reaches [MonoidObject], because [@Monoidal C] in the binder is
   rejected first -- the error lands at the [C] argument of [Monoidal].
   [MonoidObject] cannot be probed apart from [Monoidal] at all, its own
   signature being
     [MonoidObject@{u u0} : forall {C : Category@{u u0 u0}},
                            Monoidal@{u u0} -> obj[C] -> Type@{u0}],
   whose [Monoidal] argument pins [C] before any field is consulted.  So
   whether [MonoidObject] contributes an identification OF ITS OWN is
   UNKNOWN -- not refuted, and not measured anywhere in this commit.

--------
负面 3。捐赠者是 [Monoidal]，而不是 [MonoidObject]。这个文件的早期修订将负面写为

     Fail Check (fun (C : Category@{uo uh up}) (M : @Monoidal C)
                     (x : C) => @MonoidObject C M x).

并将其标记为 [MonoidObject] 捐赠者。那是错误的：展开从未到达 [MonoidObject]，因为绑定中的 [@Monoidal C] 首先被拒绝——错误出现在 [Monoidal] 的 [C] 参数上。[MonoidObject] 完全无法在 [Monoidal] 之外进行探测，其自身签名为
     [MonoidObject@{u u0} : forall {C : Category@{u u0 u0}},
                            Monoidal@{u u0} -> obj[C] -> Type@{u0}],
其 [Monoidal] 参数在任何字段被检查之前固定 [C]。因此，[MonoidObject] 是否贡献了自身的识别是未知的——既未被否定，也未在此提交中测量到。
*)
Fail Check (fun (C : Category@{uo uh up}) => @Monoidal C).

End Donors.

(**
** The positive measurement: an identification hiding in the BINDER

    Not a refutation -- two definitions whose universe signatures ARE the
    measurement.  `About dup_left` prints an EMPTY constraint block over a
    binder that identifies hom with proof.

--------
** 正面测量：隐藏在绑定器中的一个标识

    不是反驳——两个定义，其宇宙签名就是测量。`About dup_left` 会在一个绑定器上打印一个空的约束块，该绑定器将 hom 与证明标识起来。
*)

Check @dup_left.
Check @dup_right.

(** ** Positive controls for the headline artifacts / ** 标题工件的阳性对照 *)

Check @InternalSemiring.
Check @InternalRing.
Check @InternalSemilattice.
Check @InternalLattice.

(**
The two derivations that are the mathematical content: annihilation is
    a THEOREM for a ring, and idempotence is DERIVED from absorption.

--------
这两个推导是数学内容：湮灭是一个环的定理，而幂等性是由吸收律导出的。
*)

Check @ring_annihilate_l.
Check @ring_annihilate_r.
Check @ring_cancel_idem.
Check @InternalRing_InternalSemiring.
Check @InternalRing_GroupObject.
Check @lattice_join_idem.
Check @lattice_meet_idem.
Check @lattice_bot_meet.
Check @lattice_top_join.

(** The Sets passages, both directions, in both files. / 在两个文件中，Sets 段落，两个方向。 *)

Check @Sets_InternalSemiring.
Check @Rig_of_InternalSemiring.
Check @Sets_InternalRing.
Check @Ring_of_InternalRing.
Check @Sets_InternalLattice.
Check @SetoidLattice_of_InternalLattice.
Check @SetoidLattice.

(**
Independence, proved by refutation rather than asserted: the two
    annihilation fields of a semiring do not follow from the rest, and
    absorption does not follow from the monoid structure.

--------
独立性，通过反驳而非宣称来证明：半环的两个消去域不依赖于其余部分，且吸收律也不由幺半群结构推出。
*)

Check @nat_plus_not_distributive.
Check @bool_or_not_annihilating.
Check @bool_join_not_absorbing.
Check @bool_xor_not_idempotent.

(** Computing witnesses. / 计算证人。 *)

Check @Nat_ISemiring.
Check @Int_IRing.
Check @Bool_Lattice.
Check @Bool_Semilattice.

(**
** MEASURED RENAME-SIMULATION SCORE

    Read off the `Fail` commands themselves, not from memory.

      Negative 1 names [Cartesian], [Category]
      Negative 2 names [Terminal], [Category]
      Negative 3 names [Monoidal], [Category]

    Excluding [Category] as core vocabulary named by almost every file in
    the tree -- the stated ground, rather than any claim that it is hard
    to guard -- the constants a NEGATIVE names are THREE: [Cartesian],
    [Terminal], [Monoidal].

    Each of the three is named by a positive control above -- [Monoidal]
    only after a first run scored 3/4 and showed it named ONLY inside
    Negative 3, so a rename left that `Fail` succeeding on a
    reference-not-found error.  That observation was the tell that
    Negative 3 was testing [Monoidal] rather than [MonoidObject], and it
    was read as an incidental guard gap instead; the negative is now
    written as what it measures.  [MonoidObject] keeps its control above
    even though no negative names it, since the prose discusses it.
    Score: 3/3, on
    an unpadded denominator, measured by compiling a renamed copy of this
    file against an instrument-checked baseline -- with the `Require`
    lines PRESERVED, since three of these four share a name with a module
    and renaming those lines would break the copy on a missing module
    rather than on the guard, reading as a pass.

--------
** 测量的重命名模拟分数

直接读出 `Fail` 命令本身，而不是从记忆中读出。

负数 1 命名为 [Cartesian]、[Category]
负数 2 命名为 [Terminal]、[Category]
负数 3 命名为 [Monoidal]、[Category]

排除几乎每个文件在树中都命名的核心词汇 [Category] —— 所述理由，而非任何关于它难以保护的说法 —— NEGATIVE 命名的常量有三个：[Cartesian]、[Terminal]、[Monoidal]。

这三者中的每一个都是由上方的阳性控制命名的——[Monoidal]，仅在第一次运行得分为3/4并显示它仅在内部被命名后。负3号，因此重命名留下了一个在参考未找到错误时成功的“失败”。该观察表明负3号实际上是在测试[Monoidal]而不是[MonoidObject]，而它被误读为偶然的保护间隙；现在负数被写成它所测量的内容。尽管没有负数命名它，[MonoidObject]仍保留其上方的控制，因为文章中讨论了它。得分：3/3，在未填充的分母上，由将此文件的重命名副本与经过仪器检查的基线进行编译测量——`Require` 行被保留，因为这四个中的三个与一个模块同名，重命名那些行会导致副本在缺少模块时出错，而不是在保护上出错，从而被视为通过。
*)
