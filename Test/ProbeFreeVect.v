(**
* Boundary probe: what is and is not definitional in the free module
      and the free vector space.

    Companion to Instance/Mod/Free.v and Instance/Vect/Free.v (Mac Lane
    §III.1 and §IV.1, Riehl §4.0).  Those files make several strength
    claims — some things hold at Leibniz [=] or by [eq_refl], others only
    up to [≈] — and a strength claim that lives only in a header is a
    claim nothing in the build would notice losing.  This file pins the
    boundary in the manner of Test/ProbeFreeGroupoid.v: **if the [Fail]
    commands here stop failing, this file breaks the build.**

    Both sides are pinned deliberately.  A [Fail] alone proves very
    little — it passes just as happily when the term is ill-typed for
    some unrelated reason, or when a name has been renamed out from under
    it.  So each negative probe is paired with a positive control which
    must SUCCEED, and the controls are the headline claims themselves.

    The instrument was checked before being trusted: wrapping [Fail]
    around a command that succeeds reports "The command has not failed!"
    and aborts compilation, so [Fail] here is not a no-op.  Each negative
    below was also run with the [Fail] stripped, and the error confirmed
    to be a genuine unification failure rather than a syntax, scope or
    universe error; the diagnoses are recorded beside each probe.

    The three negatives and their causes:

      - The COUNIT of the free-forgetful adjunction does not compute.  It
        is [from adj id], i.e. [unique_obj (ump_universal_arrows …)], and
        [ump_universal_arrows] (Theory/Universal/Arrow.v) is [Qed]-opaque,
        so no reduction is available.  The UNIT is on the other side of
        that boundary and does compute, which is the positive control
        [probe_unit_computes]; Instance/Mod/Free.v says so in terms and
        states the counit only up to [≈]
        ([free_module_counit_evaluates]).

      - The ACTION OF THE FREE FUNCTOR ON AN ARROW does not compute
        either, and for the same reason:
        [LeftAdjointFunctorFromUniversalArrows] defines [fmap] as the
        unique universal factorization, not by a formula.  That it
        relabels generators is therefore a theorem
        ([free_module_fmap_generators], the positive control here) rather
        than a computation — which is precisely why
        [free_module_naturality_in_set] needs a proof at all, while its
        sibling [free_module_naturality_in_module] closes by
        [reflexivity].

      - THE QUOTIENT IS GENUINE.  Commutativity of a formal sum is a step
        of the generated congruence [fv_eq] and not a definitional
        equality of the underlying inductive: the two formal sums
        e_true + e_false and e_false + e_true are distinct terms of
        [FVTerm].  The positive control is [fe_comm], which inhabits
        [fv_eq] between exactly those two terms.  This is what makes the
        setoid presentation of Instance/Mod/Free.v a quotient rather than
        a renaming, and it is why the linear extension needs
        [fv_eval_respects] before it is a morphism at all.

--------
* 边界探讨：在自由模和自由向量空间中，什么是定义性的，什么不是定义性的。

与 Instance/Mod/Free.v 和 Instance/Vect/Free.v 配套（Mac Lane §III.1 和 §IV.1, Riehl §4.0）。这些文件提出了若干强度声明——有些通过 Leibniz [=] 或 [eq_refl] 成立，其他的仅在 [≈] 上成立——而仅存在于头文件中的强度声明是构建过程中不会注意到丢失的声明。此文件以 Test/ProbeFreeGroupoid.v 的方式固定了边界：**如果这里的 [Fail] 命令停止失败，则此文件将破坏构建。**

双方都是刻意固定的。仅仅一个 [Fail] 几乎不能证明什么——当某个术语由于无关原因类型错误，或者名称被重命名后，它同样能够顺利通过。因此，每个负面测试都会配有一个必须成功的正面控制，而这些控制就是主要声明本身。

在被信任之前，该仪器已被检查：将 [Fail] 包裹在一个成功的命令周围会报告“命令未失败！”并中止编译，因此这里的 [Fail] 不是无操作。下面的每个负面测试也都在去掉 [Fail] 的情况下运行，并确认错误是一个真正的统一失败，而不是语法、作用域或泛型错误；诊断结果记录在每个探测旁边。

三大消极及其原因：

- 自由-遗忘关联的余单位无法计算。它是 [from adj id]，即 [unique_obj (ump_universal_arrows …)]，并且 [ump_universal_arrows]（Theory/Universal/Arrow.v）是 [Qed] 不透明的，因此无法进行归约。单位在该边界的另一侧，可以计算，这是正控制 [probe_unit_computes]；Instance/Mod/Free.v 按术语说明了这一点，并且只声称余单位到 [≈]（[free_module_counit_evaluates]）。

- 自由函子在箭头上的作用也无法计算，原因相同：[LeftAdjointFunctorFromUniversalArrows] 将 [fmap] 定义为唯一的泛分解，而不是通过公式。因此，它重新标记生成元是一个定理（[free_module_fmap_generators]，这里的正向控制），而不是一次计算——这正是为什么 [free_module_naturality_in_set] 需要证明，而它的兄弟命题 [free_module_naturality_in_module] 则通过 [reflexivity] 得以结束的原因。

- 商是本真的。形式和的交换性是由生成的同余 [fv_eq] 导出的一个步骤，而不是底层归纳定义的等式：两个形式和 e_true + e_false 和 e_false + e_true 是 [FVTerm] 的不同项。正控制是 [fe_comm]，它正好位于这两个项之间的 [fv_eq]。这就是为什么 Instance/Mod/Free.v 的集合呈现是商而不是重命名的原因，也解释了为什么线性扩展在成为一个态射之前需要 [fv_eval_respects]。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Free.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(*
Index arguments supplied once, as NOTATIONS (so each unfolds to the
   constructor itself) — the device Instance/Mod/Free.v uses for its own
   witnesses; [Local Notation] does not cross files.

--------
索引参数提供一次，作为符号 (因此每个展开为构造函数本身) — 设备 Instance/Mod/Free.v 用于其自身证据的方式；[Local Notation] 不跨文件。
*)
Local Notation zgen  := (@fv_gen Int_Ring TwoGens).
Local Notation zsmul := (@fv_smul Int_Ring TwoGens).
Local Notation zplus := (@fv_plus Int_Ring TwoGens).

(**
** Positive control: the unit computes

    The unit is [fmap[U] id ∘ arrow], and both factors reduce, so the
    unit of the free-forgetful adjunction IS the basis insertion on the
    nose.

--------
** 阳性对照：该单元计算

    该单元是 [fmap[U] id ∘ arrow]，并且两个因子都被化简，所以自由-遗忘伴随的单元就是正好在鼻子上的基底插入。
*)
Example probe_unit_computes (x : carrier TwoGens) :
  free_module_unit Int_Ring TwoGens x = zgen x := eq_refl.

(**
** Positive control: the linear extension computes

    The mediator is a [Fixpoint] on formal expressions, so evaluating it
    on a closed expression reduces all the way to a value of the target
    module's carrier.

--------
** 阳性对照：线性扩展计算

调解器是形式表达式上的 [Fixpoint]，因此在封闭表达式上对其求值会一直简化到目标模块承载的值。
*)
Example probe_extend_computes :
  fv_eval int_probe
    (zplus (zsmul 2%Z (zgen true)) (zgen false)) = 11%Z := eq_refl.

(**
** Negative: the counit does not compute

    Stripped of [Fail] this reports that [eq_refl] cannot unify the
    counit's value at a generator with the generator, the counit being
    [unique_obj] of a [Qed]-opaque uniqueness proof.  The [≈] statement
    IS available and is the control immediately below.

--------
** 负面：counit 无法计算

去掉 [Fail] 后，这报告了 [eq_refl] 无法将 counit 在生成器处的值与生成器统一，counit 是 [unique_obj] 的 [Qed] 不透明唯一性证明。[≈] 声明可用，并且是紧接在下方的控制。
*)
Fail Example probe_counit_computes :
  cmon_map (rm_hom (free_module_counit Int_Ring Int_RMod))
    (@fv_gen Int_Ring (RMod_Forget Int_Ring Int_RMod) 3%Z) = 3%Z := eq_refl.

Example probe_counit_up_to_equiv :
  cmon_map (rm_hom (free_module_counit Int_Ring Int_RMod))
    (@fv_gen Int_Ring (RMod_Forget Int_Ring Int_RMod) 3%Z) ≈ 3%Z.
Proof. exact (free_module_counit_generator Int_Ring Int_RMod 3%Z). Qed.

(**
** Negative: the free functor's action on an arrow does not compute

    Taken at the identity of the generating setoid, where a formula-based
    definition would reduce immediately.

--------
** 负面：自由函子的箭头作用无法计算

在生成集合等价物的恒等元处取值，其中基于公式的定义会立即化简。
*)
Fail Example probe_fmap_computes (x : carrier TwoGens) :
  cmon_map (rm_hom (fmap[FreeMod Int_Ring] (@id Sets TwoGens))) (zgen x)
    = zgen x := eq_refl.

Example probe_fmap_up_to_equiv (x : carrier TwoGens) :
  cmon_map (rm_hom (fmap[FreeMod Int_Ring] (@id Sets TwoGens))) (zgen x)
    ≈ zgen x.
Proof.
  exact (@free_module_fmap_generators Int_Ring TwoGens TwoGens
           (@id Sets TwoGens) x).
Qed.

(**
** Negative: commutativity of a formal sum is not definitional

    The carrier is a plain inductive; commutativity is a constructor of
    the quotienting relation, which is the positive control.

--------
** 负面：形式和的交换性不是定义性的

载体是一个普通的归纳类型；交换性是商关系的一个构造器，这是正面的控制。
*)
Fail Example probe_plus_comm_definitional :
  zplus (zgen true) (zgen false) = zplus (zgen false) (zgen true) := eq_refl.

Example probe_plus_comm_up_to_equiv :
  fv_eq (zplus (zgen true) (zgen false)) (zplus (zgen false) (zgen true)) :=
  fe_comm _ _.
