(**
* Boundary probes for powers and copowers

    Companion to Structure/Limit/Power.v and Structure/Limit/Power/Hom.v
    (issue #321; Mac Lane §III.3 def 3 and §III.4 def 4, Riehl §3.5 Examples
    3.5.4 and 3.5.8, Awodey §3.2).  **If the [Fail] commands below stop
    failing, this file breaks the build.**

    THE TWO KINDS OF NEGATIVE ARE KEPT LEXICALLY APART AND ARE NOT DESCRIBED
    WITH ONE WORD.

    (1) FORMABILITY.  Three [Fail Check]s, all about universes.

    Group (1a), two negatives: the smallness side condition at [Sets].  The
    index of [power] / [copower] at [Sets] must live at the universe of the
    CARRIERS of [Sets]' objects, not at the universe of [obj[Sets]], which
    sits strictly above it.  This is the same condition
    Instance/Sets/Products.v's header analyses for [indexed_product] and
    exhibits as a reproduction recipe; the two negatives here are that recipe
    landed as a guarded command, at the power vocabulary.  Two controls at a
    small index show the rejection is the index and not the vocabulary.

    Group (1b), one negative, and it guards an ENGINEERING FINDING rather
    than a mathematical boundary.  Instance/Sets/Products.v records
    that letting instance resolution close a [proper_morphism] field can pin
    a constant's index universe to [Set].  Written as a [Program Definition]
    the map [Sets_discrete J → J · 1] raises no obligation at all --
    resolution closes the field during elaboration -- and comes out pinned;
    Structure/Limit/Power/Hom.v therefore supplies that certificate by hand
    under [unshelve refine].  The negative is the [Program] variant, declared
    in this file, applied at an index strictly above [Set]; the control is
    the shipped hand-written constant at the SAME index.  The pair is what
    makes the finding a guarded claim rather than a remembered one.

    (2) CONVERSION.  Three claims of Leibniz equality, all rejected for the
    same underlying reason: in this library a POWER is not an EXPONENTIAL and
    a COPOWER is not a binary product -- the identifications proved in
    Structure/Limit/Power/Hom.v are isomorphisms in [Sets], and nothing
    stronger is available.  These are [Fail Definition ... := eq_refl] and
    not [Fail Example ... : T.]: a failing type ascription would guard only
    the statement, whereas what is claimed is convertibility of two terms.
    Each is paired with a control that DOES hold on the nose, so the
    rejection is attributable to the identification and not to a projection
    being stuck.

    COUNTS.  Six negatives -- three formability, three conversion -- and
    eight positive controls.  This is not a one-to-one pairing: the controls
    of each group serve that group's negatives jointly.  The instrument
    itself was checked -- wrapping [Fail] around a succeeding command reports
    "The command has not failed!" and stops compilation -- and every negative
    was compiled once with the [Fail] stripped, to confirm the error is the
    intended one:

      - group (1a), two reports of "universe inconsistency" -- "Cannot
        enforce o < <anon> because <anon> <= o" and "Cannot enforce o < o
        because o = o" -- each naming the declared level [o];
      - group (1b), one report of "universe inconsistency", "Cannot enforce
        uj <= <anon> because <anon> < uj".  Read that message precisely: it
        does NOT print [Set], and by itself it says only that the constant's
        index universe sits strictly below [uj].  That the level in question
        IS [Set] was measured separately, by elaborating the [Program]
        variant on its own and running [Set Printing Universes. About
        probe_copower_one_from_program.], whose constraint block reads
        [Set < u0, Set = u] -- an EQUALITY on the index universe, which is
        the finding.  The shipped hand-written constant prints [u < u0] and
        no [Set];
      - group (2), three "cannot unify" conversion errors, on
        [carrier (J ⋔ X)] against [carrier (Sets_pow J X)], on [J · Y]
        against [Sets_discrete J × Y], and on [fobj[power_hom_functor J b] c]
        against the exponential of the hom-setoid.

    The import list is the target files' own, in their order, plus both
    target files.  It is deliberately the full list and not a working prefix:
    a probe compiled against a short prefix can pass for the wrong reason.

--------
* 幂和余幂的边界探针

Structure/Limit/Power.v 和 Structure/Limit/Power/Hom.v 的配套文档（问题 #321；Mac Lane 第 III.3 节 定义 3 和 第 III.4 节 定义 4，Riehl 第 3.5 节 示例 3.5.4 和 3.5.8，Awodey 第 3.2 节）。**如果下面的 [Fail] 命令不再失败，此文件将导致构建失败。**

这两种否定在词汇上是分开的，并且不能用一个词来描述。

(1) 可成型性。三个 [Fail Check]，都关于宇宙。

组（1a），两个否定：[Sets] 的小尺寸副条件。[Sets] 处的 [power] / [copower] 的索引必须位于 [Sets] 对象的载体宇宙中，而不是位于 [obj[Sets] 的宇宙中，后者严格高于它。这与 Instance/Sets/Products.v 的头分析对 [indexed_product] 的条件相同，并作为重现配方；这里的两个否定是该配方作为受保护命令落在幂词汇表中。两个小索引的控制显示被拒绝的是索引，而不是词汇表。

组（1b），一个否定，它守护的是一个工程发现而不是数学边界。Instance/Sets/Products.v 记录了让实例解析关闭一个 [proper_morphism] 字段可以将常量的索引宇宙固定到 [Set]。写成 [Program Definition] 时，映射 [Sets_discrete J → J · 1] 根本不会产生任何义务——解析在详细说明期间关闭字段——并且最终固定；因此 Structure/Limit/Power/Hom.v 在 [unshelve refine] 下手动提供了该证明。负例是 [Program] 变体，在此文件中声明，应用于严格高于 [Set] 的索引；对照是同一索引处提供的手写常量。这个组合使得这个发现成为一个有保留的声明，而不是一个记忆中的声明。

(2) 转换。三个莱布尼茨等式的主张，都因相同的根本原因被拒绝：在这个库中，幂（POWER）不是指数（EXPONENTIAL），余幂（COPOWER）不是二元积（binary product）——在 Structure/Limit/Power/Hom.v 中证明的那些同一性（identifications）是在 [Sets] 中的同构（isomorphisms），没有更强的形式可用。这些是 [Fail Definition ... := eq_refl]，而不是 [Fail Example ... : T.]：失败的类型指定（type ascription）只会保护语句本身，而所主张的是两个项（terms）的可转换性。每个都配有一个精确成立的控制（control），因此拒绝应归因于同一性，而不是投影（projection）被卡住。

计数。六个负面案例——三个关于可形成性，三个关于转换——以及八个积极对照。这不是一对一的配对：每组的对照共同用于该组的负面案例。仪器本身已被检查——将 [Fail] 包裹在一个后续命令周围会报告“命令未失败！”并停止编译——每个负面案例也都在去掉 [Fail] 的情况下编译一次，以确认错误是预期的错误：

- 组（1a），两次“宇宙不一致”报告——“无法强制执行 o << <anon> 因为 <anon> <= o”和“无法强制执行 o < o 因为 o = o”——每个都命名为已声明的等级 [o]；
- 组（1b），一次“宇宙不一致”报告，“无法强制执行 uj <= <anon> 因为 <anon> < uj”。仔细阅读该信息：它并未打印 [Set]，仅单独表示该常量的索引宇宙严格位于 [uj] 之下。有问题的级别 IS [Set] 是单独测量的，通过单独展开 [Program] 变体并运行 [Set Printing Universes. About probe_copower_one_from_program.]，其约束块读取 [Set < u0, Set = u] —— 在索引宇宙上的一个等式，这是发现。已发出的手写常量打印 [u < u0]，而没有 [Set]；
- 组（2），三个“无法统一”转换错误，分别是在 [carrier (J ⋔ X)] 与 [carrier (Sets_pow J X)] 之间，[J · Y] 与 [Sets_discrete J × Y] 之间，以及 [fobj[power_hom_functor J b] 与同伦集指数之间。

导入列表是目标文件自身的列表，按照它们的顺序，加上两个目标文件。它故意使用完整列表而不是工作前缀：针对短前缀编译的探针可能会因错误的原因而通过。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Instance.Sets.Cocartesian.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Discrete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Limit.Indexed.Hom.
Require Import Category.Structure.Limit.Power.
Require Import Category.Structure.Limit.Power.Hom.

Generalizable All Variables.

(** ** (1a) The index of a power at [Sets] must be a small type / ** (1a) 在 [Sets] 处的幂指数必须是小类型 *)

Section BigIndex.

Universes o so.
Constraint o < so.

Context (X : SetoidObject@{o o}).

(* Positive control 1: at a small index the power is formable. / 阳性对照 1：在较小的指数下，功率是可形成的。 *)
Check (@power Sets@{o so} Sets_HasIndexedProducts@{so o} nat X).

(* Positive control 2: and so is the copower. / 阳性对照2：余幂也是如此。 *)
Check (@copower Sets@{o so} Sets_HasIndexedCoproducts@{so o} nat X).

(*
Negative 1: indexing by [obj[Sets]] itself is not.  [SetoidObject@{o o}]
   lives at [Type@{o+1}] while the index must live at [Type@{o}] -- the
   universe of the carriers, which is where the small sets are.

--------
负 1：按 [obj[Sets]] 本身进行索引是不行的。[SetoidObject@{o o}] 位于 [Type@{o+1}]，而索引必须位于 [Type@{o}]——承载者的宇宙，这里是小集合所在的地方。
*)
Fail Check (@power Sets@{o so} Sets_HasIndexedProducts@{so o}
              SetoidObject@{o o} X).

(* Negative 2: dually for the copower. / 负 2：对应于共幂。 *)
Fail Check (@copower Sets@{o so} Sets_HasIndexedCoproducts@{so o}
              SetoidObject@{o o} X).

End BigIndex.

(**
** (1b) The [Program] form of the copower-of-[1] insertion is pinned to
       [Set], and the shipped hand-written form is not

--------
** (1b) [Program] 型的 [1] 次幂插入被固定在 [Set] 上，而随附的手写形式则没有
*)

(*
This is the variant Structure/Limit/Power/Hom.v declines to use.  It
   raises no obligation: instance resolution closes [proper_morphism] during
   elaboration, the domain's [≈] being Leibniz [eq].

--------
这是变体 Structure/Limit/Power/Hom.v 拒绝使用的。它不引起任何义务：在展开期间，实例解析关闭 [proper_morphism]，域的 [≈] 为 Leibniz [eq]。
*)
Program Definition probe_copower_one_from_program (J : Type) :
  Sets_discrete J
    ~{Sets}~> @copower Sets Sets_HasIndexedCoproducts J 1%object := {|
  morphism := fun i : J => existT (fun _ : J => poly_unit) i ttt
|}.

Section ProgramPin.

Universe uj.
Constraint Set < uj.

Context (J : Type@{uj}).

(* Positive control 3: the shipped constant applies at this index. / 阳性对照 3：出货的常数在此索引处应用。 *)
Check (Sets_copower_one_from J).

(* Positive control 4: so does the isomorphism built from it. / 阳性对照 4：由此构建的同构也是如此。 *)
Check (Sets_copower_one J).

(*
Negative 3: the [Program] variant does not -- its index universe was
   pinned to [Set] by the resolved certificate.

--------
负3：[Program] 变体不起作用——其索引范围已被解析的证书固定为 [Set]。
*)
Fail Check (probe_copower_one_from_program J).

End ProgramPin.

(** ** (2) A power is not an exponential, and a copower is not a product / ** (2) 幂不是指数，余幂不是乘积 *)

Section Conversion.

Context (J : Type).
Context (X Y : obj[Sets]).
Context (C : Category).
Context (b c : C).

(*
Positive control 5: the carrier of a power at [Sets] IS the bare function
   type, on the nose.

--------
阳性对照 5：[Sets] 上的功率载体就是纯函数类型，正中要点。
*)
Definition probe_power_carrier_control :
  carrier (@power Sets Sets_HasIndexedProducts J X) = (J → carrier X)
  := eq_refl.

(*
Negative 4: but it is NOT the carrier of the exponential, which is a type
   of setoid MORPHISMS out of the discrete setoid on the index.
   [Sets_power_exponent] relates the two, and only up to isomorphism.

--------
负4：但它不是指数的承载者，指数是一种从指标上的离散集合态出发的集合态态射。[Sets_power_exponent] 将二者联系起来，而且仅在同构意义下。
*)
Fail Definition probe_power_is_exponent :
  carrier (@power Sets Sets_HasIndexedProducts J X)
  = carrier (Sets_pow J X) := eq_refl.

(* Positive control 6: the carrier of a copower IS the sigma type. / 阳性对照6：协同幂的承载体是σ型。 *)
Definition probe_copower_carrier_control :
  carrier (@copower Sets Sets_HasIndexedCoproducts J Y)
  = { _ : J & carrier Y } := eq_refl.

(*
Negative 5: and it is not the product object.  [Sets_copower_prod] is an
   isomorphism in [Sets], not an equality of objects.

--------
负5：它不是乘积对象。[Sets_copower_prod] 是 [Sets] 中的同构，而不是对象的相等。
*)
Fail Definition probe_copower_is_prod :
  @copower Sets Sets_HasIndexedCoproducts J Y
  = (Sets_discrete J × Y)%object := eq_refl.

(*
Positive control 7: Riehl's right-hand side [C(X, A)^I] IS a power in
   [Sets], on the nose.

--------
阳性对照7：Riehl 的右侧 [C(X, A)^I] 确实是 [Sets] 中的一个力量，恰到好处。
*)
Definition probe_rhs_control :
  fobj[power_hom_functor J b] c
  = @power Sets Sets_HasIndexedProducts J
      {| carrier := @hom C c b ; is_setoid := @homset C c b |} := eq_refl.

(*
Negative 6: it is not the exponential of the hom-setoid.  The superscript
   in [C(X, A)^I] is this library's [power], not its [^].

--------
负 6：它不是同类集合的指数。[C(X, A)^I] 中的上标是这个库的 [power]，而不是它的 [^]。
*)
Fail Definition probe_rhs_is_exponent :
  fobj[power_hom_functor J b] c
  = Sets_pow J {| carrier := @hom C c b ; is_setoid := @homset C c b |}
  := eq_refl.

(*
Positive control 8: the two comparison maps still compute, so the
   rejections above are not a projection being stuck.

--------
正向控制 8：这两个比较图仍然可以计算，因此上面的拒绝不是投影卡住造成的。
*)
Definition probe_transform_control (p : C) (ev : ∀ _ : J, p ~> b)
  (u : c ~> p) :
  transform (power_hom_transform b p ev) c u = fun j : J => ev j ∘ u
  := eq_refl.

End Conversion.
