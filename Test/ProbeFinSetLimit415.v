(**
* Probe for Instance/FinSet/Limit.v (issue #415)

    Pins the measured boundaries of the native FinSet equalizer and of
    [FinSet_FinitelyComplete]: what converts, what does not, and what the
    constants are NOT.  Every refutation command below was stripped ONE AT
    A TIME in a copy of the whole file and compiled alone with its error
    read, so each refusal is of the kind its label says.

    Numbering:
     instrument      an absent name, refused — the refutation keyword is
                     live in this file.
     N1 CONVERSION   the PULLBACK-ROUTE equalizer object at the example
                     pair is not the numeral [2] by [eq_refl] ([lazy]
                     leaves a [fin_countP] over a predicate testing
                     [unique_obj (FinSet_Pullbacks_obligation_2 …)]); the
                     native object IS [2] (control).
     N2 CONVERSION   the PULLBACK-ROUTE terminal object from the empty
                     finite limit is not the numeral [1] by [eq_refl]; the
                     native one IS [1] (control), and the two apexes are
                     isomorphic by [terminal_unique] (control).
     N3 TYPING       [FinSet_HasEqualizers] is not a [HasEqualizers Sets]
                     — a plain has-type mismatch, no universe clause.
     N4 TYPING       [FinSet_FinitelyComplete] is not a [Complete FinSet]
                     ([FinitelyComplete] quantifies over a
                     [FiniteCategory] witness, [Complete] does not); the
                     converse direction [Complete_FinitelyComplete] is
                     accepted (control).
     N5 UNIVERSE     [FinSet]'s inherited bound [Set < u1]: the instance
                     cannot be instantiated with its hom-carrying level at
                     [Set]; the bare instance is accepted (control).

    Readbacks at [eq_refl]: [topos_HasEqualizers] at [FinSet_Topos] IS the
    pullback-route term (so N1 refutes both derived routes at once); the
    class's chosen object, inclusion and
    universal property ARE [FinSet_equalizer_obj], [FinSet_equalizer_incl]
    and [FinSet_IsEqualizer]; [FinSet_FinitelyComplete] IS
    [finitely_complete_from_generators …]; the empty pair has equalizer
    [0] and a pair of equal maps has equalizer [m], at concrete inputs.

    Guard coverage: every constant a negative names is also named outside
    a refutation command (the guard block at the end) — the exceptions,
    under the plain tokenization, being the sort [Set] that only N5 names,
    the two names the refuted [Example]s declare and the instrument's
    absent name — so a renamed or removed constant breaks the build on a
    positive line rather than letting a refutation pass for the wrong
    reason.

--------
* 探测实例/FinSet/Limit.v（问题 #415）

固定本机 FinSet 均衡器以及 [FinSet_FinitelyComplete] 的测量边界：什么可以转换，什么不可以，以及常量不是哪些。下面的每个反驳命令都在整份文件的副本中一次删除一个，并单独编译以读取其错误，所以每个拒绝的类型都如其标签所示。

编号：
     仪器      一个缺失的名字，被拒绝——反驳的关键字在此文件中是 live。N1 转换   例子对中的 PULLBACK-ROUTE 均衡器对象不是由 [eq_refl] 表示的数字 [2]（[lazy] 在测试 [unique_obj (FinSet_Pullbacks_obligation_2 …)] 的谓词上留下一个 [fin_countP]）；本地对象是 [2]（控制）。N2 转换   来自空有限极限的 PULLBACK-ROUTE 终端对象不是由 [eq_refl] 表示的数字 [1]；本地对象是 [1]（控制），且两个顶点通过 [terminal_unique]（控制）同构。N3 类型     [FinSet_HasEqualizers] 不是 [HasEqualizers Sets]——类型不匹配，无宇宙子句。
N4 输入       [FinSet_FinitelyComplete] 不是 [Complete FinSet]（[FinitelyComplete] 对 [FiniteCategory] 见证量化，[Complete] 不是）；相反方向 [Complete_FinitelyComplete] 被接受（控制）。 N5 宇宙     [FinSet] 的继承界 [Set < u1]：该实例不能以其携带同构的等级在 [Set] 实例化；裸实例被接受（控制）。

在 [eq_refl] 上的回读：[topos_HasEqualizers] 在 [FinSet_Topos] 是回拉路径项（因此 N1 同时驳斥了两个派生路径）；类的选定对象、包含和普遍性质分别是 [FinSet_equalizer_obj]、[FinSet_equalizer_incl] 和 [FinSet_IsEqualizer]；[FinSet_FinitelyComplete] 是 [finitely_complete_from_generators …]；空对具有等化器 [0]，一对相等映射在具体输入下具有等化器 [m]。

守卫覆盖：每个恒定的负名称在外部也有命名一个反驳命令（末尾的守卫块）——在普通分词下，例外是仅有 N5 名称的 [Set] 类型、被反驳的 [Example] 声明的两个名称以及仪器的缺失名称——因此，重命名或移除常量会在正行上破坏构建，而不是因错误原因让反驳通过。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Limit.Finite.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Topos.
Require Import Category.Structure.Topos.Monadic.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Sets.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Classifier.
Require Import Category.Instance.FinSet.Limit.
Require Import Category.Instance.FinSet.Topos.
Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(* instrument: the refutation keyword is live / instrument：反驳关键词是 live *)
Fail Check probe415_absent_name.

(** ** A: the pullback route does not compute; the native route does / ** A：回退路线无法计算；本地路线可以 *)

Definition p415_HasEqualizers_pb : HasEqualizers FinSet :=
  @HasEqualizers_of_HasPullbacks_Terminal FinSet FinSet_Terminal
    FinSet_Pullbacks.

Definition p415_FinitelyComplete_pb : @FinitelyComplete FinSet :=
  finitely_complete_of_pullbacks_terminal FinSet_Pullbacks FinSet_Terminal.

(* the topos-derived equalizer of FinSet IS the pullback-route term / 由拓扑派生的 FinSet 等化器是拉回路径项 *)
Example p415_topos_route_is_pullback_route :
  @topos_HasEqualizers FinSet FinSet_Topos = p415_HasEqualizers_pb
  := eq_refl.

(* control: the native equalizer object at the example pair is [2] / 控制：示例对中的本地均衡器对象是 [2] *)
Example p415_native_obj :
  `1 (@equalizer FinSet FinSet_HasEqualizers _ _
        finset_eq_example_f finset_eq_example_g) = 2%nat
  := eq_refl.

(* N1 CONVERSION *)
Fail Example p415_pb_obj :
  `1 (@equalizer FinSet p415_HasEqualizers_pb _ _
        finset_eq_example_f finset_eq_example_g) = 2%nat
  := eq_refl.

(* control: the native terminal object from the empty finite limit is [1] / 控制：来自空有限极限的原生终端对象是 [1] *)
Example p415_native_terminal :
  @terminal_obj FinSet (FinitelyComplete_Terminal FinSet_FinitelyComplete)
  = 1%nat
  := eq_refl.

(* N2 CONVERSION *)
Fail Example p415_pb_terminal :
  @terminal_obj FinSet (FinitelyComplete_Terminal p415_FinitelyComplete_pb)
  = 1%nat
  := eq_refl.

(* control: the two apexes agree up to isomorphism, by uniqueness / 控制：两个顶点在同构下是一致的，由于唯一性 *)
Definition p415_terminals_iso :
  @terminal_obj FinSet (FinitelyComplete_Terminal p415_FinitelyComplete_pb)
  ≅ @terminal_obj FinSet (FinitelyComplete_Terminal FinSet_FinitelyComplete)
  := terminal_unique (FinitelyComplete_Terminal p415_FinitelyComplete_pb)
                     (FinitelyComplete_Terminal FinSet_FinitelyComplete).

(** ** B: typing *)

(* N3 TYPING *)
Fail Check (FinSet_HasEqualizers : HasEqualizers Sets).

(* N4 TYPING *)
Fail Check (FinSet_FinitelyComplete : @Complete FinSet).

(* control: completeness would imply finite completeness *)
Check (@Complete_FinitelyComplete FinSet
       : @Complete FinSet → @FinitelyComplete FinSet).

(** ** C: universe / ** 宇宙 *)

(* control *)
Check FinSet_HasEqualizers@{_ _ _ _ _}.

(* N5 UNIVERSE *)
Fail Check FinSet_HasEqualizers@{_ _ Set _ _}.

(** ** D: readbacks / ** D：复读 *)

Section Readbacks.
  Context {m n : nat} (f g : Fin.t m → Fin.t n).

  Example p415_obj_readback :
    `1 (@equalizer FinSet FinSet_HasEqualizers m n f g)
    = FinSet_equalizer_obj f g
    := eq_refl.

  Example p415_incl_readback :
    `1 (`2 (@equalizer FinSet FinSet_HasEqualizers m n f g))
    = FinSet_equalizer_incl f g
    := eq_refl.

  Example p415_ump_readback :
    `2 (`2 (@equalizer FinSet FinSet_HasEqualizers m n f g))
    = FinSet_IsEqualizer f g
    := eq_refl.

  (* the inclusion is a fork, at the setoid of FinSet / 包含是一个分叉，在 FinSet 的等价类上 *)
  Example p415_fork :
    f ∘[FinSet] FinSet_equalizer_incl f g
    ≈ g ∘[FinSet] FinSet_equalizer_incl f g
    := fork_eq (FinSet_IsEqualizer f g).
End Readbacks.

Example p415_finitely_complete_readback :
  FinSet_FinitelyComplete
  = finitely_complete_from_generators FinSet_Terminal FinSet_Cartesian
      FinSet_HasEqualizers
  := eq_refl.

(* a pair that never agrees has the empty equalizer / 从不一致的一对有空均衡器 *)
Example p415_disjoint :
  FinSet_equalizer_obj (fun _ : Fin.t 2 => (Fin.F1 : Fin.t 2))
                       (fun _ => Fin.FS Fin.F1) = 0%nat
  := eq_refl.

(* a pair of equal maps has the whole source as equalizer / 一对相等的映射以整个源作为等化器 *)
Example p415_equal_maps :
  FinSet_equalizer_obj finset_eq_example_f finset_eq_example_f = 3%nat
  := eq_refl.

(** ** Guard block / ** 防守格挡 *)

Check @finset_eq_pred.
Check @FinSet_equalizer_obj.
Check @FinSet_equalizer_incl.
Check @finset_eq_pred_true.
Check @FinSet_equalizer_med.
Check @FinSet_IsEqualizer.
Check @FinSet_HasEqualizers.
Check @FinSet_FinitelyComplete.
Check @finset_eq_example_f.
Check @finset_eq_example_g.
Check @finset_eq_example_h.
Check @finset_eq_example_diagram.
Check @FinSet_FinitelyComplete_terminal_computes.
Check @FinSet_FinitelyComplete_parallel_computes.
Check @p415_HasEqualizers_pb.
Check @p415_FinitelyComplete_pb.
Check @HasEqualizers_of_HasPullbacks_Terminal.
Check @finitely_complete_of_pullbacks_terminal.
Check @FinitelyComplete_Terminal.
Check @Complete_FinitelyComplete.
Check @terminal_unique.
Check @Sets.
