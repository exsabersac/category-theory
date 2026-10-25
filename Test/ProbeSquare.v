(**
* Boundary probes for the walking commutative square

    Companion to Instance/Square.v, Instance/Square/Product.v and
    Instance/Square/Rectangle.v (issue #300, Mac Lane §II.8 Ex. 1;
    Riehl §1.6 Examples 1.6.6 and 1.6.9).  Those files make three
    strength claims whose negative side is a universe or a typing
    boundary; measurements outside the tree would not be noticed by a
    refactor, so they are pinned here.  **If the [Fail] commands below
    stop failing, this file breaks the build.**

    Each negative is paired with a positive control that must SUCCEED,
    for the reason Test/ProbeQuiverConstructions.v gives: a [Fail] alone
    passes just as happily when a name has been renamed out from under
    it.  The instrument itself was checked — wrapping [Fail] around a
    succeeding command reports "The command has not failed!" and aborts
    compilation — and each negative was compiled once with the [Fail]
    stripped, to confirm the error is the intended one and not a syntax,
    scope or resolution failure — two [cannot unify] typing errors and,
    for the rectangle, the universe inconsistency [Cannot enforce Set =
    rh] naming the declared universe itself.

    THE THREE BOUNDARIES.

    (1) THE DONOR PIN IS GONE, and this is the probe that says so.
    Before issue #300, [Build_Quiver_Standard_Eq]
    (Construction/Free/Quiver.v) elaborated to [Quiver@{u u0 Set}] — its
    edge setoid's PROOF universe silently minimized to [Set], because it
    was built from [Corelib.Classes.CRelationClasses.eq_equivalence@{u}],
    which carries one universe binder and cannot separate the carrier's
    level from the proof level.  Since [InducedFunctor] identifies the
    target category's hom and proof universes with the quiver's, EVERY
    functor out of a free or presented category was confined to a target
    [Category@{o Set Set}].  Construction/Free/Quiver/Examples.v's header
    diagnosed exactly this and called lifting it out of scope; it is
    lifted now, and section [BigTarget] below is the guard —
    [SquareFunctor], [SquareFunctor_f], [square_universal] and the
    reverse passage, all applied at a category whose three universes are
    declared strictly above [Set].  There is no [Fail] half here: the
    claim IS that nothing is rejected, so the whole guard is a positive
    control.

    (2) [Square ≅[StrictCat] _2 ∏ _2] IS NOT AN EQUALITY OF CATEGORIES.
    Instance/Square/Product.v is explicit that the two object types are
    [SquareNode] and [TwoObj * TwoObj], distinct inductives, so no
    Leibniz equality of the [Category] records is available.  The
    negative probe is the attempted [eq_refl]; the positive control is
    the isomorphism itself, at [StrictCat] and not merely at [Cat].

    (3) THE RECTANGLE'S CONVERSE IS PINNED AT [Category@{co Set Set}],
    and its forward half is not.  Instance/Square/Rectangle.v records
    that [RectFunctor] inherits [Set] from [Theory/Shapes.v]'s
    [Functor_of_Pair] (which produces a functor out of
    [_3@{u Set Set}]) through [Construction/Cylinder.v]'s [Cyl_functor]
    (which identifies the hom and proof universes of its two
    categories), while the [Diagram] section carries no pin at all.
    Both halves are probed: the forward accessors typecheck above [Set],
    and building [RectFunctor] there is rejected.

--------
* 行走交换方格的边界探针

与 Instance/Square.v、Instance/Square/Product.v 和 Instance/Square/Rectangle.v 配套（问题 #300，Mac Lane §II.8 练习 1；Riehl §1.6 示例 1.6.6 和 1.6.9）。这些文件提出了三个强度声明，其负面方面是一个宇宙或类型边界；树外的测量不会被重构注意到，因此它们固定在这里。**如果下面的 [Fail] 命令不再失败，则此文件会破坏构建。**

每个阴性对照都配有一个必须成功的阳性对照，原因如 Test/ProbeQuiverConstructions.v 所示：单独的 [Fail] 即使名称已被重命名，也可以同样顺利通过。该仪器本身已被检查——将 [Fail] 包裹在后续命令周围会报告“命令未失败！”并中止编译——并且每个负面示例都在去掉 [Fail] 后编译一次，以确认错误是预期的，而不是语法、作用域或解析失败——两个 [cannot unify] 的输入错误，以及对于矩形而言，宇宙不一致 [无法强制 Set = rh]，命名声明的宇宙本身。

三界。

(1) 捐赠者 PIN 不见了，这是探针指出的。在第 #300 期之前，[Build_Quiver_Standard_Eq]（Construction/Free/Quiver.v）扩展为 [Quiver@{u u0 Set}]——其 edge setoid 的 PROOF 宇宙被悄悄缩小到 [Set]，因为它是由 [Corelib.Classes.CRelationClasses.eq_equivalence@{u}] 构建的，[Corelib.Classes.CRelationClasses.eq_equivalence@{u}] 带有一个宇宙绑定器，无法将载体的级别与证明级别分开。由于 [InducedFunctor] 将目标范畴的 hom 和证明宇宙与 quiver 的宇宙识别在一起，因此从自由或呈现范畴出的每个函子都被限制在目标 [Category@{o Set Set}]。Construction/Free/Quiver/Examples.v 的头部正好诊断了这一点，并称其为从作用域中提升；它现在已经被提升，下面的 [BigTarget] 部分是保护——[SquareFunctor]、[SquareFunctor_f]、[square_universal] 以及反向通路，全部应用于一个其三个宇宙严格声明在 [Set] 之上的类别。这里没有 [Fail] 半部分：声明确实是没有任何被拒绝，所以整个保护是正向控制。

(2) [Square ≅[StrictCat] _2 ∏ _2] 不是范畴的等式。
Instance/Square/Product.v 明确指出这两种对象类型是 [SquareNode] 和 [TwoObj * TwoObj]，属于不同的归纳类型，因此 [Category] 记录不可用 Leibniz 等式。
负面测试尝试的是 [eq_refl]；正面控制是同构本身，存在于 [StrictCat]，而不仅仅是 [Cat]。

(3) 矩形的逆方向固定在 [Category@{co Set Set}]，而其前半部分未固定。Instance/Square/Rectangle.v 记录了 [RectFunctor] 从 [Theory/Shapes.v] 的 [Functor_of_Pair] 继承 [Set]（这会从 [_3@{u Set Set}] 生成函子），通过 [Construction/Cylinder.v] 的 [Cyl_functor]（这会识别其两个范畴的 hom 和证明宇宙），而 [Diagram] 部分完全没有固定。两半部分都被探测：前向访问器在 [Set] 上方类型检查通过，而在那里构建 [RectFunctor] 被拒绝。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Free.Quiver.Presented.
Require Import Category.Instance.Two.
Require Import Category.Instance.Ordinal.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.Square.
Require Import Category.Instance.Square.Product.
Require Import Category.Instance.Square.Rectangle.

Local Open Scope category_scope.

(**
** (1) The donor pin is gone

    A target category whose three universes are declared strictly above
    [Set].  Before the lift described above, forming [SquareFunctor] at
    such a target was a universe inconsistency; it now typechecks.

--------
** (1) 捐赠者引脚丢失了

    一个目标类别，其三个宇宙被严格声明在 [Set] 之上。在上述提升之前，在这样的目标上形成 [SquareFunctor] 是宇宙不一致；现在可以进行类型检查。
*)

Section BigTarget.

Universes bo bh bp.
Constraint Set < bo.
Constraint Set < bh.
Constraint Set < bp.
Constraint bh <= bp.

Context (D : Category@{bo bh bp}).
Context (S : CommutingSquare D).

(**
The universal property of the presented square, applied above
    [Set].  This is the guard on the [Build_Quiver_Standard_Eq]
    generalisation.

--------
上面应用于 [Set] 的所呈方格的普适性质。这是 [Build_Quiver_Standard_Eq] 泛化中的保护。
*)
Check (SquareFunctor S : Square ⟶ D).

(**
...and its action on the generators, so the guard covers the
    theorems and not only the construction.

--------
……以及它对生成元的作用，因此守护覆盖的是定理，而不仅仅是构造。
*)
Check (SquareFunctor_f S).
Check (square_universal S).

(** The reverse direction was never pinned, and still is not. / 反向从未被固定，现在仍然没有被固定。 *)
Context (F : Square ⟶ D).

Check (CommutingSquareOfFunctor F : CommutingSquare D).
Check (square_functor_round_strict F).

End BigTarget.

(**
** (2) The 2 × 2 identification is an isomorphism, not an equality

    Positive control: the isomorphism in [StrictCat] — the strong
    reading, [≅[Cat]] in this library being an equivalence of
    categories.

--------
** (2) 2 × 2 身份映射是一个同构，而不是相等

    阳性对照：[StrictCat] 中的同构——强读数，
    在这个库中 [≅[Cat] 是范畴的等价。
*)
Check (Square_2x2_iso : Square ≅[StrictCat] (_2 ∏ _2)).
Check (Square_2x2_Cat_iso : Square ≅[Cat] (_2 ∏ _2)).

(**
Negative: the two categories are not Leibniz-equal, their object
    types being distinct inductives.  (With the [Fail] stripped this
    reports that [Square] and [_2 ∏ _2] cannot be unified.)

--------
否定：这两个类别不是莱布尼茨相等的，它们的对象类型是不同的归纳类型。（去掉 [Fail] 后，这显示 [Square] 和 [_2 ∏ _2] 无法统一。）
*)
Fail Check (eq_refl : Square = (_2 ∏ _2)).

(**
Nor are their object types.  (With the [Fail] stripped: cannot
    unify [SquareNode] with [TwoObj * TwoObj].)

--------
它们的对象类型也不是。（在去掉 [Fail] 后：无法将 [SquareNode] 与 [TwoObj * TwoObj] 统一。）
*)
Fail Check (eq_refl : SquareNode = (TwoObj * TwoObj)%type).

(**
The instrument is not a no-op: a [Fail] on a succeeding command
    aborts compilation with "The command has not failed!".  The
    following line, uncommented, would do exactly that — it is left as
    a comment because a passing build cannot contain it.

      Fail Check (Square_2x2_iso : Square ≅[StrictCat] (_2 ∏ _2)).

    The controls above are the standing check that the [Fail]s are not
    passing for the wrong reason.

--------
该工具不是无操作：一个 [Fail] 在后续命令中会使编译中止，并显示“命令未失败！”。下面的这一行，如果不注释掉，正是会发生这种情况——它被保留为注释，因为通过的构建不能包含它。

      Fail Check (Square_2x2_iso : Square ≅[StrictCat] (_2 ∏ _2))。

上述控制是固定检查，确保 [Fail] 并不是因为错误的原因而通过。
*)

(** ** (3) The rectangle: forward unpinned, converse pinned at [Set] / ** (3) 矩形：正向未固定，反向在 [Set] 固定 *)

Section BigRectangle.

Universes ro rh rp.
Constraint Set < ro.
Constraint Set < rh.
Constraint Set < rp.
Constraint rh <= rp.

Context (E : Category@{ro rh rp}).

(**
Forward half: the accessors and every commutativity statement
    typecheck at a target above [Set].

--------
前半部分：访问器和每个交换律声明在高于 [Set] 的目标处进行类型检查。
*)
Context (F : Rect ⟶ E).

Check (rect_u F).
Check (rect_left_commutes F).
Check (rect_right_commutes F).
Check (rect_outer_commutes F).
Check (rect_outer_two_ways F).
Check (rect_long_through_left F).
Check (rect_long_through_right F).

(**
The pasting principle carries no pin whatever — it mentions no
    shape category.

--------
粘贴原理完全不涉及针——它没有提到任何形状类别。
*)
Check (@paste_squares E).

(**
Negative half: the converse does not reach here.  (With the [Fail]
    stripped this reports a universe inconsistency, [Set] against the
    declared [rh].)

--------
负半：逆命题没有达到这里。（在去掉 [Fail] 后，这报告了一个宇宙不一致，[Set] 与声明的 [rh] 相对。）
*)
Context (R : CommutingRectangle E).

Fail Check (RectFunctor R : Rect ⟶ E).

End BigRectangle.

(**
Positive control for the converse: at a target whose hom and proof
    universes ARE [Set] it builds, and recovers all seven generators.

--------
相反情况的阳性对照：在其同源体和证明宇宙是 [Set] 的目标上，它构建并恢复所有七个生成器。
*)
Section SmallRectangle.

Universe so.

Context (E : Category@{so Set Set}).
Context (R : CommutingRectangle E).

Check (RectFunctor R : Rect ⟶ E).
Check (RectFunctor_u R).
Check (RectFunctor_p R).
Check (RectFunctor_r R).

End SmallRectangle.
