(**
* Universe probe: the funny monoidal structure on StrictCat is Set-pinned.

    Companion to the "Universe scope" note of Instance/StrictCat/Premonoid.v.

    [Funny_Monoidal@{u} : Monoidal@{u Set}] (Instance/StrictCat/Funny.v) fixes
    the second universe of [Monoidal] — the level of StrictCat's member
    categories — at [Set], so every carrier category reached through the
    funny monoidal structure lives in [Category@{Set Set Set}].  This file
    pins the obstruction to lifting that restriction:

      - [StrictCat@{i v j v v} : Category@{i v v}] has object type
        [Category@{v v v}]: member categories at the rigid (monomorphic)
        level [v] declared below;

      - the tensor is unproblematic: [Build_Monoidal] applied to [_1] and
        [FunnyTensor] at member level [v] is accepted ([probe_tensor_ok]);

      - supplying a unitor is what fails.  The compiled [Funny_unit_left] of
        Construction/Funny/Unitors.v carries a rigid interior [Set] level
        ([Print Funny_unit_left] shows
        [from := Funny_unit_left_from@{u0 u0 u0 Set u0 u0}]), so
        [Build_Monoidal] at member level [v] reports

          universe inconsistency: Cannot enforce Set = v

        at the [unit_left] field (first [Fail] below);

      - consequently the compiled instance does not transport: casting
        [Funny_Monoidal@{i}] to [@Monoidal StrictCat@{i v j v v}] fails with
        the same message, [Monoidal@{i Set}] against [Monoidal@{i v}]
        (second [Fail] below).

    Lifting the restriction requires re-declaring the unitors with explicit
    universe binders in Construction/Funny/Unitors.v.  If that is ever done,
    the [Fail] commands here stop failing and this file breaks the build,
    flagging that the universe-scope note in Instance/StrictCat/Premonoid.v
    can be relaxed.

--------
* 宇宙探测器：StrictCat 上有趣的幺半群结构是 Set 固定的。

Instance/StrictCat/Premonoid.v 中“Universe scope”注释的配套说明。

[Funny_Monoidal@{u} : Monoidal@{u Set}]（实例/StrictCat/Funny.v）修复了 [Monoidal] 的第二个宇宙——StrictCat 的成员类别的级别——在 [Set]，因此通过有趣的幺半群结构达到的每个承载类别都位于 [Category@{Set Set Set}]。此文件固定了提升该限制的障碍：

- [StrictCat@{i v j v v} : Category@{i v v}] 有对象类型
        [Category@{v v v}]：在下列刚性（单态）级别声明的成员类别 [v]；

- 张量没有问题：在成员级别 [v] 上，将 [Build_Monoidal] 应用于 [_1] 和 [FunnyTensor] 被接受（[probe_tensor_ok]）；

- 提供 unitor 是失败的。编译后的 Construction/Funny/Unitors.v 的 [Funny_unit_left] 拥有一个严格的内部 [Set] 级别（[Print Funny_unit_left] 显示 [from := Funny_unit_left_from@{u0 u0 u0 Set u0 u0}]），因此在成员级别 [v] 的 [Build_Monoidal] 报告

宇宙不一致：无法强制执行 Set = v

在 [unit_left] 字段（下方第一个 [Fail]）；

- 因此，编译后的实例无法传输：将 [Funny_Monoidal@{i}] 转换为 [@Monoidal StrictCat@{i v j v v}] 失败，显示相同的消息，[Monoidal@{i Set}] 对 [Monoidal@{i v}]（下方的第二个 [Fail]）。

解除该限制需要在 Construction/Funny/Unitors.v 中重新声明带有显式宇宙绑定器的 unitors。如果那样做了，这里的 [Fail] 命令将不再失败，而这个文件会导致构建失败，从而标记 Instance/StrictCat/Premonoid.v 中的宇宙作用域注释可以放宽。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.One.
Require Import Category.Instance.StrictCat.
Require Import Category.Construction.Funny.
Require Import Category.Construction.Funny.Unitors.
Require Import Category.Instance.StrictCat.Funny.
Require Import Category.Structure.Monoidal.

(**
A rigid member level [v], with outer levels [i] (StrictCat's objects) and
    [j] strictly above it, as StrictCat's universe constraints require.

--------
一个刚性成员级别 [v]，其外部级别 [i]（StrictCat 的对象）和 [j] 严格位于其上方，正如 StrictCat 的宇宙约束所要求的那样。
*)
Monomorphic Universe i j v.
Monomorphic Constraint v < i.
Monomorphic Constraint v < j.

(**
** Positive control: everything up to the unitors is fine at level [v].

    The partial application supplies the carrier, the unit object and the
    tensor, so the failures below are not caused by [StrictCat], [_1] or
    [FunnyTensor] at member level [v].

--------
** 阳性对照：在 [v] 级别，直到联合器的一切都是正常的。

部分应用提供了载体、单位对象和张量，因此下面的失败不是由 [StrictCat]、[_1] 或 [FunnyTensor] 在 [v] 成员级别引起的。
*)
Definition probe_tensor_ok :=
  @Build_Monoidal StrictCat@{i v j v v} _1 FunnyTensor.

(**
** The reproduction: the unitor field is where [Set] is enforced.

    Error: The term "Funny_unit_left@{_ v}" has type "1 □ x ≅ x"
    while it is expected to have type "fobj[FunnyTensor@{..}] (1, x) ≅ x"
    (universe inconsistency: Cannot enforce Set = v).

--------
** 重现：unitor 字段是 [Set] 被强制执行的地方。

错误：术语 "Funny_unit_left@{_ v}" 的类型是 "1 □ x ≅ x"，
而期望的类型是 "fobj[FunnyTensor@{..}] (1, x) ≅ x"
（宇宙不一致：无法强制 Set = v）。
*)
Fail Check (@Build_Monoidal StrictCat@{i v j v v} _1 FunnyTensor
              (fun x : Category@{v v v} => @Funny_unit_left x)).

(**
** The compiled instance is pinned: it does not transport to level [v].

    Error: The term "Funny_Monoidal" has type "Monoidal@{i Set}"
    while it is expected to have type "Monoidal@{i v}"
    (universe inconsistency: Cannot enforce Set = v).

--------
** 已固定已编译的实例：它不会传输到级别 [v]。

错误：术语 "Funny_Monoidal" 的类型为 "Monoidal@{i Set}"
而期望的类型为 "Monoidal@{i v}"
（宇宙不一致：无法强制 Set = v）。
*)
Fail Check (Funny_Monoidal@{i} : @Monoidal StrictCat@{i v j v v}).

(**
** Positive control: [Funny_Monoidal] is a well-formed [Monoidal] at its
    own universe level.  This pins the two [Fail]s above to the specific
    [Set = v] universe conflict rather than to a malformed term or a renamed
    identifier: the instance exists and type-checks, it simply does not
    transport up to level [v].  Without this control a [Fail] would pass on
    any error at all.

--------
** 阳性对照：[Funny_Monoidal] 是一个在其自身宇宙层级上良构的 [Monoidal]。这将上面的两个 [Fail] 固定到特定的 [Set = v] 宇宙冲突，而不是固定到一个格式错误的术语或重命名的标识符：该实例存在并且类型检查通过，只是它不会传递到 [v] 层级。如果没有这个对照，[Fail] 将会传递任何错误。
*)
Check (Funny_Monoidal@{i} : @Monoidal StrictCat@{i Set j Set Set}).
