(**
* Boundary probes for couniversal arrows

    Companion to Theory/Universal/Arrow/Dual.v and
    Theory/Universal/Arrow/Dual/Examples.v (issue #302, Mac Lane §III.1
    Definition 3).  That file makes several strength claims — some
    definitional, some only up to [≈] — and the negative side of each is
    a conversion boundary that no in-tree consumer would notice breaking.
    They are pinned here.  **If the [Fail] commands below stop failing,
    this file breaks the build.**

    Every negative is paired with a positive control that must SUCCEED,
    for the reason Test/ProbeQuiverConstructions.v gives: a [Fail] alone
    passes just as happily when a name has been renamed out from under
    it.  The instrument itself was checked — wrapping [Fail] around a
    succeeding command reports "The command has not failed!" and aborts
    compilation — and each negative below was compiled once with the
    [Fail] stripped, to confirm the error is the intended typing failure
    and not a syntax, scope or resolution error.

    THE FOUR BOUNDARIES.

    (1) THE COVARIANT READING IS REAL, NOT A REPACKAGING.  This is the
    claim the issue's design constraint turns on: [coarrow_obj] and
    [coarrow] are supplied by [:=] with no tactic, so the covariantly
    typed [F a ~{C}~> c] and the op-side [c ~{C^op}~> (F^op) a] are the
    same term.  Purely a positive control — the claim IS that nothing is
    rejected.

    (2) THE TERMINAL-OBJECT READING IS A THEOREM, NOT THE DEFINITION.
    [@Initial (=(c) ↓ F^op)] taken in the opposite categories is not
    convertible with [@Terminal (F ↓ =(c))]: [Comma] indexes its objects
    by an ORDERED pair of categories, so the first ranges over
    [1 ∏ D^op] and the second over [D ∏ 1], and [Product] of categories
    is not symmetric on the nose.  This is why
    [couniversal_arrow_terminal] exists as a construction rather than as
    a coercion.  The mismatch is located precisely here as well: it is
    NOT the terminal/initial axis (that conversion is free, and is a
    positive control below), and Construction/Comma.v's [Cocomma] — the
    route the issue proposed — does not close it, being neither of the
    two commas involved.

    (3) THE DUAL IS NOT THE PRIMAL.  [CouniversalArrow c F] and
    [UniversalArrow c F] are distinct types; the file is not a renaming.

    (4) THE COUNIT AGREES WITH THE COUNIVERSAL ARROW ONLY UP TO [≈].
    [AdjunctionFromCouniversalArrows] assembles by duality, and its
    object action does reduce ([right_adjoint_obj] is [eq_refl]) — but
    the transpose delivers [coarrow ∘ fmap[F] id], one [fmap_id] and one
    [id_right] short of the couniversal arrow itself.

--------
* 用于共宇箭的边界探测器

《Theory/Universal/Arrow/Dual.v》和《Theory/Universal/Arrow/Dual/Examples.v》的配套文件（问题 #302，Mac Lane §III.1 定义 3）。该文件提出了若干强度主张——有些是定义性的，有些仅在 [≈] 之前有效——而每个主张的负面部分都是一个转换边界，树内的使用者不会注意到破坏。它们在这里被固定。**如果下面的 [Fail] 命令不再失败，该文件将导致构建失败。**

每一个阴性样本都配有一个必须成功的阳性对照，其原因如 Test/ProbeQuiverConstructions.v 所示：单独的 [Fail] 即使在名称已被重命名的情况下也能顺利通过。仪器本身已被检查——将 [Fail] 包裹在一个成功的命令周围会报告“命令未失败！”并中止编译——下列每个阴性样本在去掉 [Fail] 后都编译过一次，以确认错误是预期的类型错误，而不是语法、作用域或解析错误。

四个边界。

(1) 协变阅读是真实的，而不是重新包装。这是该问题设计约束所关注的：[coarrow_obj] 和 [coarrow] 由 [:=] 提供，没有任何策略，因此协变类型的 [F a ~{C}~> c] 和操作端的 [c ~{C^op}~> (F^op) a] 是同一术语。纯粹是一个阳性对照——该声明是没有任何被拒绝。

(2) 终端对象读取是一个定理，而不是定义。 
[@Initial (=(c) ↓ F^op)] 在相反的范畴中取值并不能与 [@Terminal (F ↓ =(c))] 转换：[Comma] 通过范畴的有序对来索引其对象，因此第一个在 [1 ∏ D^op] 上取值，第二个在 [D ∏ 1] 上取值，而范畴的 [Product] 并不是自然对称的。这就是为什么 [couniversal_arrow_terminal] 作为一个构造存在，而不是作为强制转换。 不匹配正好发生在这里：它不是终端/初始轴（该转换是自由的，并且在下文是一个正向控制），而 Construction/Comma.v 的 [Cocomma] —— 问题提出的路径 —— 并没有解决它，因为它既不是所涉及的两个逗号中的任何一个。

(3) 对偶不是原始类型。[CouniversalArrow c F] 和 [UniversalArrow c F] 是不同的类型；该文件不是重命名。

(4) 共单位仅与共宇箭头一致到 [≈]。  
[AdjunctionFromCouniversalArrows] 通过对偶组装，其对象作用确实减少（[right_adjoint_obj] 是 [eq_refl]）——但转置提供的结果比共宇箭头本身少 [coarrow ∘ fmap[F] 个 id、一个 [fmap_id] 和一个 [id_right]。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Sets.
Require Import Category.Instance.One.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Arrow.Dual.
Require Import Category.Theory.Universal.Arrow.Dual.Examples.

Local Open Scope category_scope.

Section Probes.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {c : C}.
Context (U : CouniversalArrow c F).

(**
** (1) The covariant reading is definitional

    Positive controls.  [coarrow] has the covariant type, and IS the
    op-side [arrow] — the same term, not a transported one.

--------
** (1) 协变读法是定义性的

    阳性对照。[coarrow] 具有协变类型，并且是操作端的 [arrow] — 同一个术语，而非转移的术语。
*)

Check (coarrow U : F (coarrow_obj U) ~{C}~> c).

Check (eq_refl : coarrow U = @arrow (C^op) (D^op) c (Opposite_Functor F) U).

Check (eq_refl : coarrow_obj U
                   = @arrow_obj (C^op) (D^op) c (Opposite_Functor F) U).

(**
The couniversal mapping property likewise: its statement mentions no
    [op], and it is the primal statement's own term.

--------
同样的通用映射性质：它的陈述中没有提到 [op]，并且它是原始陈述本身的术语。
*)

Check (fun (d : D) (h : F d ~{C}~> c) =>
         eq_refl : @ump_couniversal_arrows C D c F U d h
                     = @ump_universal_arrows (C^op) (D^op) c
                         (Opposite_Functor F) U d h).

(**
** (2) The terminal-object reading is a theorem

    Positive control: the construction, and the fact that it chooses the
    couniversal object on the nose.

--------
** (2) 终端对象读法是一个定理

    正向控制：该构造，以及它精确选择共通对象的事实。
*)

Check (couniversal_arrow_terminal U : @Terminal (F ↓ =(c))).
Check (couniversal_arrow_terminal_obj U).
Check (couniversal_arrow_of_terminal (couniversal_arrow_terminal U)
         : CouniversalArrow c F).

(**
Negative: the op-side initial object is NOT that terminal object.
    (With the [Fail] stripped this reports that [arrow_initial] has type
    [@Initial (fobj[Diagonal 1] c ↓ F^op)] while [@Terminal (F ↓ =(c))] was
    expected -- a type mismatch; the target prints with its implicit argument
    elided, and the words "cannot unify" do NOT appear in this one, unlike
    the two Cocomma probes below.)

--------
消极：op 侧的初始对象不是那个终端对象。（去掉 [Fail] 后，这报告了 [arrow_initial] 的类型为 [@Initial (fobj[Diagonal 1] c ↓ F^op)]，而 [@Terminal (F ↓ =(c))] 是预期的 —— 类型不匹配；目标在打印时省略了隐式参数，而且与下面的两个 Cocomma 探针不同，这个报告中没有出现“无法统一”这几个字。）
*)
Fail Check (@arrow_initial (C^op) (D^op) c (Opposite_Functor F) U
              : @Terminal (F ↓ =(c))).

(**
Nor are the two comma categories themselves Leibniz-equal — the
    reason for the mismatch, isolated.  (Stripped: cannot unify.)

--------
这两个逗号范畴本身也不是莱布尼茨等价的——不匹配的原因，已被孤立。（已剥离：无法统一。）
*)
Fail Check (eq_refl
              : @Comma _1 (D^op) (C^op) (@Diagonal (C^op) _1 c)
                       (Opposite_Functor F)
                  = @Comma D _1 C F (@Diagonal C _1 c)).

(**
The mismatch is NOT the terminal/initial axis.  Positive control:
    a terminal object of F ↓ =(c) IS an initial object of its opposite,
    by conversion, `Initial K` being notation for `@Terminal (K^op)` and
    `(K^op)^op` being `K`.

--------
不匹配的不是终端/初始轴。正控制：F 的一个终端对象 ↓ =(c) 是其对偶的初始对象，通过转换，`Initial K` 是 `@Terminal (K^op)` 的符号，而 `(K^op)^op` 是 `K`。
*)
Check (fun T : @Terminal (F ↓ =(c)) => terminal_is_initial_op T).
Check (fun T : @Terminal (F ↓ =(c)) => (T : @Initial ((F ↓ =(c))^op))).

(**
...and it is not closed by Construction/Comma.v's [Cocomma] either,
    which the issue proposed as the route.  Positive control first: the
    cocomma of the same two functors exists.

--------
...并且它也没有被 Construction/Comma.v 的 [Cocomma] 关闭，这就是问题提出的路径。首先进行正控制：相同两个函子的 cocomma 是存在的。
*)
Check (@Cocomma D _1 C F (@Diagonal C _1 c) : Category).

(**
Negative: it is not the comma the op-side [arrow_initial] inhabits.
    (Stripped: cannot unify [@Initial (=(c) ↓ F^op)] with
    [@Initial (F ↑ =(c))].)

--------
负面：op-side [arrow_initial] 并不位于逗号处。
（已去除：无法将 [@Initial (=(c) ↓ F^op)] 与 [@Initial (F ↑ =(c))] 统一。）
*)
Fail Check (@arrow_initial (C^op) (D^op) c (Opposite_Functor F) U
              : @Initial (@Cocomma D _1 C F (@Diagonal C _1 c))).

(**
Negative: nor is it the opposite of F ↓ =(c) on the nose.
    (Stripped: cannot unify [F ↑ =(c)] with [(F ↓ =(c))^op].)

--------
负面：也不是 F ↓ =(c) 的相反。
    （剥离后：无法将 [F ↑ =(c)] 与 [(F ↓ =(c))^op] 统一。）
*)
Fail Check (eq_refl : @Cocomma D _1 C F (@Diagonal C _1 c)
                        = (@Comma D _1 C F (@Diagonal C _1 c))^op).

(**
** (3) The dual is not the primal

    Positive control: both types exist, at the same arguments.

--------
** (3) 对偶不是原始的

    正向控制：两种类型都存在，在相同的参数下。
*)
Check (CouniversalArrow c F : Type).
Check (UniversalArrow c F : Type).

(**
Negative: and they are different.  (Stripped: cannot unify
    [CouniversalArrow c F] with [UniversalArrow c F].)

--------
负面：它们是不同的。（已剥离：无法统一 [CouniversalArrow c F] 与 [UniversalArrow c F]。）
*)
Fail Check (eq_refl : CouniversalArrow c F = UniversalArrow c F).

End Probes.

(**
** (4) The counit agrees only up to [≈]

    Measured at the worked example, so the probe is about a real
    adjunction and not a variable.

--------
** (4) 余单位只一致到 [≈]

    在示例中测量，因此探针关于一个真实的伴随，而不是一个变量。
*)

Section CounitProbe.

Context `{C : Category}.
Context `{@Cartesian C}.
Context (p : C ∏ C).

(**
Positive controls: the object action of the assembled right adjoint
    reduces to the product on the nose, and the counit IS the projection
    pair up to [≈].

--------
阳性对照：已组装的右伴随的对象作用在本质上简化为乘积，而余单位在 [≈] 范围内是投影对。
*)
Check (eq_refl : fobj[@product_via_couniversal_functor C _] p
                   = (fst p × snd p)).
Check (@product_via_couniversal_counit C _ p).

(**
Negative: that agreement is not an [eq_refl].  (Stripped: cannot
    unify the [counit] with [proj_pair p].)

--------
消极：该协议不是 [eq_refl]。（已剥离：无法将 [counit] 与 [proj_pair p] 统一。）
*)
Fail Check (eq_refl
              : @counit (C ∏ C) C (Diagonal_Product C)
                        (@product_via_couniversal_functor C _)
                        (@product_via_couniversal C _) p
                  = @proj_pair C _ p).

End CounitProbe.

(**
The instrument is not a no-op: a [Fail] on a succeeding command
    aborts compilation with "The command has not failed!".  The
    following line, uncommented, would do exactly that — it is left as a
    comment because a passing build cannot contain it.

      Fail Check (@CouniversalArrow : forall (C D : Category),
                    obj[C] -> (D ⟶ C) -> Type).

    THE [@] IS LOAD-BEARING, and an earlier revision of this very block
    got it wrong — which is worth recording, since it is precisely the
    failure mode this file exists to rule out.  Without the [@], the
    exhibit reads [Fail Check (CouniversalArrow : ...)]; [Arguments
    CouniversalArrow {C D} c F] (Theory/Universal/Arrow/Dual.v) makes
    [C] and [D] implicit, so the bare name has type
    [obj[?C] -> ?D ⟶ ?C -> Type], the ascription genuinely fails, and
    the [Fail] SUCCEEDS — silently, exit 0.  A demonstration that the
    instrument is live would then have been an instance of the
    instrument passing for the wrong reason.  With the [@] the
    ascription holds and the [Fail] aborts as advertised (measured, exit
    1).

    The controls above are the standing check that the [Fail]s are not
    passing for the wrong reason.

--------
该工具不是无操作的：在后续命令上使用 [Fail] 会中止编译，并显示“命令未失败！”。 下一行，如果取消注释，将正是这样 —— 它被保留为注释，因为通过的构建不能包含它。

检查失败 (@CouniversalArrow : 对于所有 (C D : 范畴), obj[C] -> (D ⟶ C) -> 类型)。

[@] 是承重的，而这个模块的早期版本就出错了——这值得记录，因为这正是这个文件存在的原因：排除这种失败模式。没有 [@]，展示的内容显示 [Fail Check (CouniversalArrow : ...)]；[Arguments CouniversalArrow {C D} c F] (Theory/Universal/Arrow/Dual.v) 使 [C] 和 [D] 成为隐式的，所以裸名称的类型为 [obj[?C] -> ?D ⟶ ?C -> Type，类型标注确实失败，而 [Fail] 成功——默默地，退出 0。演示仪器处于活跃状态本可以是仪器以错误理由通过的实例。有了 [@]，类型标注成立，而 [Fail] 按照预期中断（测量，退出 1）。

上面的控制是用来确认 [Fail] 并不是出于错误原因而通过的站立检查。
*)
