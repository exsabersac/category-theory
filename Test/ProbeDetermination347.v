(*
The target's FULL import list is mirrored below, deliberately.  A short
   prefix is what makes a probe pass vacuously: with [Category.Instance.Sets]
   missing, the negative below failed on "Illegal application" because the
   [SetoidMorphism] coercion was out of scope, and with
   [Category.Theory.Isomorphism] missing it failed on "reference [to] not
   found" -- in both cases certifying nothing about conversion.

--------
目标的完整导入列表如下刻意反映。一个短前缀会使探针轻率地通过：当缺少 [Category.Instance.Sets] 时，下面的负测试因为“非法应用”而失败，因为 [SetoidMorphism] 强制转换超出了范围；当缺少 [Category.Theory.Isomorphism] 时，它因“未找到引用 [to]”而失败——在这两种情况下都无法证明任何关于转换的内容。
*)
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Arrow.Dual.
Require Import Category.Adjunction.Determination.

Generalizable All Variables.

(**
* Boundary probe for issue #347 (maclane:IV.1:thm2, awodey:9.2:cor5)

    Adjunction/Determination.v measures one strength boundary and diagnoses
    it, but ships no [Fail] of its own, so the measurement is unguarded there.
    This file pins it from OUTSIDE the target — an in-file [Fail] renames in
    lockstep with its own definition and so cannot detect a rename — with
    positive controls naming the same constants.

    The diagnosis being guarded is that the boundary is DONOR OPACITY and that
    the cause DISCRIMINATES: [coarrow] and [coarrow_obj] of the very same
    couniversal arrow DO reduce to [eq_refl], because they are transparent
    projections of the transparent [couniversal_arrow_from_UMP], while the
    MEDIATOR does not, because it is read out of [ump_couniversal_arrows]
    whose primal donor [ump_universal_arrows] (Theory/Universal/Arrow.v)
    is closed with [Qed].  Controls and negative therefore sit on the SAME
    object, which is what makes the attribution meaningful rather than a
    guess about opacity in general.

--------
* 针对问题 #347 的边界探测（maclane:IV.1:thm2, awodey:9.2:cor5）

Adjunction/Determination.v 测量一个强度边界并对其进行诊断，但自身不传送任何 [Fail]，因此该测量在此处未受保护。这个文件从目标的外部固定它——文件内的 [Fail] 会与自身定义同步重命名，因此无法检测重命名——并且正控件命名相同的常量。

被谨慎诊断的情况是，边界是供体不透明性，其原因区分为：[coarrow] 和 [coarrow_obj] 的同一普遍箭头确实约化为 [eq_refl]，因为它们是透明 [couniversal_arrow_from_UMP] 的透明投影，而调解者则不是，因为它是从 [ump_couniversal_arrows] 中读取的，其原始供体 [ump_universal_arrows]（Theory/Universal/Arrow.v）被 [Qed] 关闭。因此，对照组和负组位于同一个对象上，这正是使归因有意义而不是对不透明性的一般猜测的原因。
*)

Section Probe.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

(**
** Positive controls

    Every constant named in the negative is also named here outside any
    [Fail], so a rename cannot silently vacate the guard.  The first two are
    the discriminating half of the diagnosis: on the SAME couniversal arrow,
    the object and the arrow DO reduce.

--------
** 阳性对照

    在负对照中命名的每一个常量也都在这里的任何 [Fail] 之外被命名，因此重命名不会悄无声息地使保护失效。前两个是诊断的判别部分：在相同的通用箭头上，对象和箭头确实会约减。
*)

Example probe_ctl_obj (c : C) :
  coarrow_obj (adj_counit_couniversal A c) = U c := eq_refl.

Example probe_ctl_arrow (c : C) :
  coarrow (adj_counit_couniversal A c) = @counit C D F U A c := eq_refl.

Check @adj_counit_couniversal.
Check @adj_counit_couniversal_med.
Check @ump_couniversal_arrows.

(*
This control is what makes the negative below non-vacuous, and it was
   MISSING on the first cut: [unique_obj], [to] and the [adj[_]] notation
   appeared ONLY inside the [Fail], so renaming any of them would have made
   it fail on "reference not found" while this file still compiled -- the
   very false-pass mode the header above describes.  Stating the lemma at
   its true strength here names all three outside the [Fail].

--------
这个控制使下面的否定不再是空洞的，而它在第一次修改时是缺失的：[unique_obj]、[to] 和 [adj[_] 的符号只出现在 [Fail] 内，因此重命名其中任何一个都会导致“未找到引用”错误，而该文件仍然可以编译——正如上面的标题所描述的，非常错误的通过模式。在这里以其真实强度陈述引理，会在 [Fail] 外命名所有三个。
*)
Example probe_ctl_med (c : C) (d : D) (f : F d ~{C}~> c) :
  unique_obj (ump_couniversal_arrows (adj_counit_couniversal A c) f)
    ≈ to adj[A] f := adj_counit_couniversal_med A c d f.

(**
** CONVERSION negative: the mediator does not reduce

    [adj_counit_couniversal_med] is stated at [≈] and not at [=].  Stripped,
    this reports a genuine unification failure between the mediator and the
    forward transpose, not a missing reference.

--------
** CONVERSION 否定：中介者没有减少

[adj_counit_couniversal_med] 被声明在 [≈]，而不是在 [=]。剥离后，这报告了中介者与前向转置之间的真正统一失败，而不是缺失的引用。
*)

Fail Example probe_med_strict (c : C) (d : D) (f : F d ~{C}~> c) :
  unique_obj (ump_couniversal_arrows (adj_counit_couniversal A c) f)
    = to adj[A] f := eq_refl.

End Probe.

(**
** Instrument check

    A [Fail] that must fail for a reason having nothing to do with #347, so a
    broken [Fail] mechanism would be visible here rather than silently passing
    the negative above.  Scope-free deliberately: a numeral would risk failing
    on a missing scope delimiter instead of on the proposition.

--------
** 仪器检查

    一个 [Fail]，必须因为与 #347 无关的原因而失败，因此在此可以看到损坏的 [Fail] 机制，而不是像上面那样默默地通过负面。范围自由：故意这样做：数字可能会因为缺少范围分隔符而失败，而不是因为命题失败。
*)

Fail Example probe_347_instrument : (true = false) := eq_refl.
