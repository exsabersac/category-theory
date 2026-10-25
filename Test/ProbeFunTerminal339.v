(**
* Boundary probes for Instance/Fun/Terminal.v (issue #339)

    Mac Lane CWM 2nd ed. §III.5 Exercise 5, book p. 74.

    The target ships its own two CONVERSION refutations with controls
    (`Instance/Fun/Terminal.v` and).  This file pins the SEVEN
    boundaries it cannot: six FORMABILITY negatives, which need a section
    declaring universe levels strictly apart and so cannot live in a
    library file, and one three-way SEPARATION that is a positive
    measurement rather than a refutation.

    SIX NEGATIVES, ALL FORMABILITY, in two groups:

      * Negatives 1-5 attribute the hom = proof identification that every
        result about `[C, D]` carries.  FIVE donors do it INDEPENDENTLY --
        `Terminal`, `Cartesian`, `HasIndexedProducts`, `IsIndexedProduct`
        and `Fun` -- each rejected under `Constraint uh < up` against
        controls that name a hom and a family at those very levels.  The
        point of testing all five separately is that blaming the first
        plausible donor would be wrong: `Fun` in fact does MORE than the
        other four, identifying hom with proof in BOTH arguments and the
        two hom levels with each other.

      * Negative 6 is why the target builds `Constant_Functor` instead of
        citing `Functor/Diagonal.v`.  `Diagonal`'s type mentions `[J, C]`
        and so inherits `Fun`'s identification; the constant functor built
        by hand does not, and keeps C's hom and proof APART.  The control
        is that very functor at the very levels the negative is rejected
        at, so the negative is attributable to `Diagonal` and not to the
        section.

    THE SEPARATION (no `Fail` -- three `About`-able definitions):
    `probe_functor_only`, `probe_cone_of_discrete` and
    `probe_limit_of_discrete` measured WHERE the `Set` pin on the
    `Limit`-of-a-discrete-diagram route came from, back when there was
    one.  Measured here rather than assumed, and the result CORRECTED
    what ONE of this tree's own docs/INDEX.md bullets said -- the
    `Construction/Coproduct/Indexed.v`/`Instance/Cat/Coproduct.v` one.
    (An earlier revision of this header named three bullets; the other
    two are sound, `Functor/Hom/Limit.v`'s naming both donors and
    `Structure/Limit/Product/Finite.v`'s citing the composite.)

      probe_functor_only      C : Category@{u1 u0 u0}    FREE
      probe_cone_of_discrete  C : Category@{u2 u1 u1}    FREE
      probe_limit_of_discrete C : Category@{u3 u2 u2}    FREE

    RECORDED CORRECTION.  An earlier revision of this table read the third
    row as `C : Category@{u1 Set Set}  PINNED`, and concluded: "So
    `DiscreteCat_Functor` ALONE does NOT pin the ambient category -- it
    fixes only the SHAPE, at `DiscreteCat@{u Set Set}`.  The ambient pin
    needs a SECOND donor that identifies the shape's hom and proof with
    the ambient's; it takes BOTH."  Both halves were correct measurements
    of the tree of the time, and the FIRST donor has since been repaired:
    `DiscreteCat_Functor` was annotated in place at
    `Instance/Discrete.v` in the PR "algebraic carriers are sets"
    (2026-09-17), so it fixes no shape universe at all and the third row
    is now FREE like the other two.  The separation therefore no longer
    has a `Set` to locate, and the three definitions are kept as positive
    CONTROLS: were the annotation dropped, the third row would print
    `Set` again.  They are `About`-able below; re-run them rather than
    trusting this table.  What is NOT repealed is the structural half of
    the old conclusion -- `Limit` and `IsALimit` identify the shape's
    hom-and-proof universe with the ambient's where `Cone` does not, so a
    second donor is still what would carry any ambient restriction.  Read
    the second half narrowly: the
    `Cone` RECORD is innocent, but that licenses no claim that
    `IsALimit`/`Limit` are the ONLY other donors, and they are not --
    `cone_leg` (`Structure/Limit/Preservation.v`, over
    `J : Category@{u u0 u0}` and `C : Category@{u1 u0 u0}`) and
    `IsLimitCone` identify them in exactly the same way, so
    CONE VOCABULARY is among the donors even though the record is not.
    `Structure/Limit/Initial.v`'s own bullet already warns that an
    `ACone` control rules out only `ACone`/`Cone`; an earlier revision of
    this header ran that control and drew the broader conclusion anyway.  The practical conclusion those bullets draw (do not route an
    indexed product through `Limit (DiscreteCat_Functor …)`) is unchanged
    and is what `Instance/Fun/Terminal.v` follows; only the attribution
    was wrong.

    Every negative is paired with a positive control naming its own
    constants.  The measured rename-simulation score is at the end, over
    the constants the NEGATIVES name and no others.

--------
* Instance/Fun/Terminal.v 的边界探针（问题 #339）

Mac Lane 《CWM》第2版 §III.5 练习5，第74页。

目标提供了它自己的两个转换反驳及其控制（`Instance/Fun/Terminal.v` 和）。该文件固定了它无法处理的七个边界：六个可形成性否定，需要一个明确声明宇宙层级严格分离的部分，因此不能放在库文件中，以及一个三向分离，它是一个正向测量而不是反驳。

六个否定，全是可形成性，分为两组：

* 否定 1-5 归因于同态 = 证明识别，每个关于 `[C, D]` 的结果都携带此特性。五个捐赠者独立执行此操作——`Terminal`、`Cartesian`、`HasIndexedProducts`、`IsIndexedProduct` 和 `Fun`——在 `Constraint uh < up` 的约束下，每个都被拒绝，这些约束针对那些在相同层次上命名同态和族的控制。分别测试所有五个的目的是，如果责怪第一个合理的捐赠者，那将是错误的：实际上 `Fun` 所做的超过其他四个，它在两个参数中都用证明识别同态，并且在两个同态层次之间也进行识别。

* 负 6 是目标构建 `Constant_Functor` 而不是引用 `Functor/Diagonal.v` 的原因。`Diagonal` 的类型提到 `[J, C]`，因此继承了 `Fun` 的标识；手动构建的常量函子没有继承，并且保持 C 的 hom 和证明分离。控制正是在负数被拒绝的那个级别上使用的那个函子，因此这个负数应归因于 `Diagonal`，而不是该节。

分离（没有 `Fail` —— 三个可“About”定义）：
`probe_functor_only`、`probe_cone_of_discrete` 和 `probe_limit_of_discrete` 测量了当时 `Limit` 的离散图路由上的 `Set` 引脚来自哪里，当时还存在一个。这里进行测量而不是假设，结果纠正了这个树自身文档/INDEX.md 子项中一条——`Construction/Coproduct/Indexed.v` / `Instance/Cat/Coproduct.v` 的那条。（该标题的早期修订命名了三条子项；其他两条是可靠的，即 `Functor/Hom/Limit.v` 命名了两个 donor，以及 `Structure/Limit/Product/Finite.v` 引用了组合。）

probe_functor_only      C : Category@{u1 u0 u0}    免费
      probe_cone_of_discrete  C : Category@{u2 u1 u1}    免费
      probe_limit_of_discrete C : Category@{u3 u2 u2}    免费

已记录更正。该表的早期修订版本将第三行读取为 `C : Category@{u1 Set Set} PINNED`，并得出结论：“因此，仅 `DiscreteCat_Functor` 并不能固定环境类别——它只固定形状，在 `DiscreteCat@{u Set Set}`。环境固定需要第二个捐赠者来将形状的同态和证明与环境的对应；需要两者。” 两部分都是当时树的正确测量，并且第一个捐赠者之后已被修复：`DiscreteCat_Functor` 已在 PR “代数承载体是集合” (2026-09-17) 中在 `Instance/Discrete.v` 进行原位注释，因此它根本不固定任何形状宇宙，第三行现在像另外两行一样是自由的。
因此，分离不再有一个 `Set` 可供定位，三个定义作为正向控制保持不变：如果注释被删除，第三行将再次打印 `Set`。它们可以在下面通过 `About` 查看；请重新运行它们，而不是依赖这个表格。未被废除的是旧结论的结构部分——`Limit` 和 `IsALimit` 使用形状的同源及证明宇宙来识别，而 `Cone` 不会，因此第二捐赠者仍然会承担任何环境限制。
仔细阅读下半部分：`Cone` RECORD 是无辜的，但这并不意味着可以声称 `IsALimit`/`Limit` 是唯一的其他捐赠者，而它们并不是——`cone_leg`（位于 `Structure/Limit/Preservation.v`，适用于 `J : Category@{u u0 u0}` 和 `C : Category@{u1 u0 u0}`）和 `IsLimitCone` 以完全相同的方式识别它们，因此即使该记录不是，CONE 词汇也属于捐赠者。`Structure/Limit/Initial.v` 自身的注释已经警告说，一个 `ACone` 控制只排除了 `ACone`/`Cone`；该标题的早期修订版本运行了该控制，并仍然得出了更广泛的结论。这些注释所得出的实际结论（不要将索引积通过 `Limit (DiscreteCat_Functor …)` 传递）保持不变，也是 `Instance/Fun/Terminal.v` 遵循的内容；只是归属有误。

每个阴性样本都配有一个阳性对照，其命名自己的常数。测得的重命名-模拟得分在最后，基于阴性样本命名的常数，而不是其他常数。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Limit.Product.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Fun.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Fun.Terminal.

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
** Negatives 1-5 (FORMABILITY): five INDEPENDENT donors identify hom
       with proof

    Each is rejected under `Constraint uh < up` while the controls show a
    hom-set and an object family are perfectly formable at those levels.
    Testing them separately is the point: no single one is "the" cause.

--------
** 否定 1-5（可形成性）：五个独立供体通过证据确认同源

每个在 `Constraint uh < up` 下被拒绝，而对照显示在这些水平上同源集和对象族完全可形成。单独测试它们是重点：没有一个是“唯一”的原因。
*)

Section Donors.

Universe uo uh up.
Constraint uh < up.

(* Control: a hom-set of such a category exists. / 控制：这样的范畴的同态集存在。 *)
Check (fun (C : Category@{uo uh up}) (x y : C) => x ~> y).

(*
Control: so does a family of its objects -- the shape the indexed
   results quantify over.

--------
控制：它的对象家族也是如此——索引结果所量化的形状。
*)
Check (fun (C : Category@{uo uh up}) (A : Type) (f : A -> C) => f).

(* NEGATIVE 1. / 否定 1. *)
Fail Check (fun (C : Category@{uo uh up}) => @Terminal C).

(*
Control: [Cartesian] exists at unconstrained levels.  Same reason as
   the [HasIndexedProducts] control below -- without it the negative
   would survive a rename of [Cartesian] on a reference-not-found
   error.

--------
控制：[Cartesian] 存在于不受限制的级别。与下面的 [HasIndexedProducts] 控制相同的原因——没有它，负面情况将在参考未找到错误时通过重命名 [Cartesian] 幸存。
*)
Check @Cartesian.

(* NEGATIVE 2. / 负 2. *)
Fail Check (fun (C : Category@{uo uh up}) => @Cartesian C).

(*
Control: [HasIndexedProducts] EXISTS and elaborates at UNCONSTRAINED
   levels.  Without this line the negative below would still "succeed"
   after a rename of [HasIndexedProducts], on a reference-not-found error
   rather than on the universe boundary -- measured, not guessed: an
   earlier revision omitted it and the rename simulation scored 5/7.

--------
控制：[HasIndexedProducts] 存在并在无限制级别下详述。没有这一行，下方的负测试在重命名 [HasIndexedProducts] 后仍然会“成功”，发生在引用未找到错误而不是在宇宙边界上——这是测量得出的，而非猜测：早期的一个版本遗漏了它，重命名模拟得分为 5/7。
*)
Check @HasIndexedProducts.

(* NEGATIVE 3. / 负三。 *)
Fail Check (fun (C : Category@{uo uh up}) => @HasIndexedProducts C).

(* Control: likewise for [IsIndexedProduct], for the same reason. / 控制：出于同样的原因，[IsIndexedProduct] 也是如此。 *)
Check @IsIndexedProduct.

(* NEGATIVE 4. / 负四 *)
Fail Check (fun (C : Category@{uo uh up}) (A : Type) (f : A -> C)
                (p : C) (proj : forall a, p ~> f a) =>
              @IsIndexedProduct C A f p proj).

(* Control: [Fun] exists at unconstrained levels. / 控制：[Fun] 存在于不受限制的水平。 *)
Check @Fun.

(*
NEGATIVE 5.  [Fun] does MORE than the other four: it identifies hom
   with proof in BOTH arguments and the two hom levels with each other.

--------
负 5. [Fun] 做得比其他四个更多：它在两个论证中都能识别同态并提供证明，并且还能识别两个同态级别之间的关系。
*)
Fail Check (fun (C D : Category@{uo uh up}) => @Fun C D).

End Donors.

(**
** Negative 6 (FORMABILITY): why the target builds its own constant
       functor rather than citing [Diagonal]

    [Diagonal]'s type mentions the functor category and so inherits
    [Fun]'s identification.  [Constant_Functor], built by hand with
    explicit binders, keeps C's hom and proof APART -- and the control
    below is that functor AT THE VERY LEVELS the negative is rejected at,
    so the rejection is attributable to [Diagonal].

--------
** 负 6（可形成性）：为什么目标构建自己的常量函子，而不是引用 [Diagonal]

[Diagonal] 的类型提到了函子类别，因此继承了 [Fun] 的标识。[Constant_Functor] 是手工构建的，带有显式绑定器，保持了 C 的同态和证明分离——下面的控制正是在负被拒绝的那个层次上的函子，所以拒绝可以归因于 [Diagonal]。
*)

Section DiagonalPin.

Universe co ch cp dro dh.
Constraint ch < cp.

(* Control: the three objects exist at these levels. / 控制：这三个对象存在于这些层级。 *)
Check (fun (C : Category@{co ch cp}) (D : Category@{dro dh dh})
           (T : @Terminal D) => (C, D, T)).

(* Control: so does the terminal object of D. / 控制：D 的终端对象也是如此。 *)
Check (fun (C : Category@{co ch cp}) (D : Category@{dro dh dh})
           (T : @Terminal D) => @terminal_obj D T).

(*
Control: and so does the target's OWN constant functor, at exactly
   these levels -- C's hom and proof strictly apart.

--------
控制：目标自身的常量函子也是如此，正好在这些层级——C 的同态和证明严格分开。
*)
Check (fun (C : Category@{co ch cp}) (D : Category@{dro dh dh}) (d : D) =>
         @Constant_Functor@{co ch cp dro dh dh} C D d).

(* Control: and its terminal specialization. / 控制：及其终端专化。 *)
Check (fun (C : Category@{co ch cp}) (D : Category@{dro dh dh})
           (T : @Terminal D) =>
         @Constant_Terminal_Functor@{co ch cp dro dh} C D T).

(* Control: [Diagonal] exists at unconstrained levels. / 控制：[Diagonal] 存在于不受限制的水平。 *)
Check @Diagonal.

(* NEGATIVE 6. / 负 6。 *)
Fail Check (fun (C : Category@{co ch cp}) (D : Category@{dro dh dh})
                (T : @Terminal D) =>
              fobj[@Diagonal D C] (@terminal_obj D T)).

End DiagonalPin.

(**
** The separation: where the [Set] pin on the [Limit] route USED to come from

    Not a refutation -- three definitions whose universe signatures are
    the measurement.  Run `About` on each to see it.

--------
** 分离：[Limit] 路由上的 [Set] 引脚曾经的来源

    不是反驳——三个定义，其宇宙标识就是测量。对每个运行 `About` 来查看它。
*)

Definition probe_functor_only
  {C : Category} {A : Type} (f : A -> C) : DiscreteCat A ⟶ C :=
  DiscreteCat_Functor f.

Definition probe_cone_of_discrete
  {C : Category} {A : Type} (f : A -> C) : Type :=
  Cone (DiscreteCat_Functor f).

Definition probe_limit_of_discrete
  {C : Category} {A : Type} (f : A -> C) : Type :=
  Limit (DiscreteCat_Functor f).

(** ** Positive controls for the headline artifacts / ** 标题工件的阳性对照 *)

Check @Functor_Category_Terminal.
Check @Constant_Functor.
Check @Constant_Terminal_Functor.
Check @Fun_iprod.
Check @Fun_iprod_proj.
Check @Fun_IsIndexedProduct.
Check @Fun_HasIndexedProducts.
Check @iprod_jointly_monic.
Check @cartesian_bool_IsIndexedProduct.
Check @Fun_bool_iprod_iso.
Check @terminal_empty_IsIndexedProduct.
Check @Fun_empty_iprod_terminal.

(**
The two CONVERSION refutations live in the target with their own
    controls; these name their constants so a rename breaks this file
    too.

--------
这两个 CONVERSION 反驳与它们自己的控件一起存在于目标中；它们为常量命名，因此重命名也会破坏此文件。
*)

Check @bool_fam.
Check @Fun_bool_iprod_iso_commutes.
Check @Fun_bool_iprod_iso_inv_commutes.

(**
** MEASURED RENAME-SIMULATION SCORE

    Read off the `Fail` commands themselves, not from memory.

      Negative 1 names [Terminal], [Category]
      Negative 2 names [Cartesian], [Category]
      Negative 3 names [HasIndexedProducts], [Category]
      Negative 4 names [IsIndexedProduct], [Category]
      Negative 5 names [Fun], [Category]
      Negative 6 names [Diagonal], [terminal_obj], [Terminal], [Category],
                       [fobj]

    Excluding core vocabulary ([Category], [fobj]) on the stated ground
    that it is named by almost every file in the tree rather than that it
    is hard to guard, the constants a NEGATIVE names are SEVEN:
    [Terminal], [Cartesian], [HasIndexedProducts], [IsIndexedProduct],
    [Fun], [Diagonal], [terminal_obj].

    Each of the seven is named by a positive control above -- note that
    [Fun_HasIndexedProducts] and [Fun_IsIndexedProduct] do NOT count as
    controls for [HasIndexedProducts] and [IsIndexedProduct], since `_`
    is a word character and a rename of the bare name does not touch
    them; the bare `Check`s in the Donors and DiagonalPin sections are
    what guard those.  TWO measurement defects were found and fixed
    before this score could be stated, and both are recorded rather than
    quietly repaired: (a) three of the seven -- [Cartesian], [Fun] and
    [Diagonal] -- were named ONLY inside their own `Fail`, so a rename
    left the `Fail` succeeding on "reference not found"; bare controls
    for all three are now present; and (b) the simulation itself was
    broken, because it renamed the module paths in the `Require Import`
    lines too, so the file failed to compile for the WRONG REASON and
    every result read as a pass.  A rename simulation must PRESERVE
    `Require`/`From` lines.  Score: 7/7,
    on an unpadded denominator, measured by compiling a renamed copy of
    this file against an instrument-checked baseline and confirming each
    one breaks it.

--------
** 测量的重命名模拟分数

直接读出 `Fail` 命令本身，而不是从记忆中读出。

负面 1 名称 [Terminal], [Category]
负面 2 名称 [Cartesian], [Category]
负面 3 名称 [HasIndexedProducts], [Category]
负面 4 名称 [IsIndexedProduct], [Category]
负面 5 名称 [Fun], [Category]
负面 6 名称 [Diagonal], [terminal_obj], [Terminal], [Category], [fobj]

排除核心词汇（[Category]、[fobj]），理由是它几乎被树中的每个文件命名，而不是因为它难以保护，常量的负面名称有七个：[Terminal]、[Cartesian]、[HasIndexedProducts]、[IsIndexedProduct]、[Fun]、[Diagonal]、[terminal_obj]。

七者中的每一个都由上面的正向控制命名——注意，[Fun_HasIndexedProducts] 和 [Fun_IsIndexedProduct] 不算作 [HasIndexedProducts] 和 [IsIndexedProduct] 的控制，因为 `_` 是一个单词字符，重命名裸名不会影响它们；在 Donors 和 DiagonalPin 部分中的裸 `Check` 才是保护它们的。在这个分数可以公布之前，发现并修复了两个测量缺陷，并且两者都被记录下来，而不是悄悄修复：(a) 七个测量中有三个——[Cartesian]、[Fun] 和 [Diagonal]——只在各自的 `Fail` 中命名，所以重命名后 `Fail` 因“未找到引用”而成功；现在三个的空控件都已存在；(b) 模拟本身有问题，因为它也重命名了 `Require Import` 行中的模块路径，所以文件编译失败的原因错误，每个结果都被读作通过。重命名模拟必须保留 `Require`/`From` 行。得分：7/7，在未加填充的分母上，通过将此文件重命名后的副本与经过工具检查的基线进行编译，并确认每一个都能使其出错来进行测量。
*)
