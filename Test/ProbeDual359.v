(**
* Boundary probe for Structure/Monoidal/Dual.v (issue #359)

    Mac Lane CWM 2nd ed. §IV.2, book p. 88, the vector-space duality
    adjunction (the item maclane:IV.2:construction3): dualisation into a
    fixed object is contravariant and self-adjoint on the right.

    WHY THIS FILE EXISTS AT ALL.  The target carries eight [Fail]s of its
    own and they are well formed -- each was stripped once and its WHOLE
    error read, each sits beside an APPLIED control, and the instrument
    check is scope-free.  What an in-file negative CANNOT do is survive a
    rename: a whole-file rename moves the [Fail] and the constant it
    names in lockstep, so the guard stays green while the thing it
    guarded is gone.  Every negative below therefore names a constant of
    the TARGET, and the file mirrors ALL of the target's [Require] lines
    -- a probe built on a short prefix of that list is the classic way to
    make a negative pass for a reason it never measured (a missing
    coercion, an absent notation), certifying nothing.

    IT ALSO MIRRORS THE TARGET'S [Remove Hints] LINE, AND THAT LINE IS
    DEFENSIVE RATHER THAN LOAD BEARING — measured, in BOTH files:
    deleting

        Remove Hints Sets_Product_Monoidal : typeclass_instances.

    leaves the target compiling clean and leaves this probe compiling
    clean, and both of this file's negatives then fail with
    byte-identical error messages.  The reason it costs nothing is the
    one the target's own header gives: `C` arrives carrying a
    [SymMonClosed] instance whose coercion already determines the
    monoidal structure, so resolution is never offered a choice.  It is
    mirrored here for consistency with the target and with the two
    donors, where the ambient category is not so constrained.

    KINDS, separated by the error TEXT rather than by label -- and note
    that the tail ALONE does not separate two of them:
      FORMABILITY  ends `universe inconsistency: Cannot enforce cp = ch`
      CONVERSION   ends `cannot unify` between two terms of ONE type
      TYPING       also ends `cannot unify`, but on the OBJECT VARIABLES,
                   its body reporting two DIFFERENT objects of [Sets] as
                   the expected and the actual type

    THE REVIEWER'S CHECK IS THE POINT OF NEGATIVE 2.  The issue demands
    that the canonical double-dual morphism be CONSTRUCTED, not assumed
    invertible.  [Structure/Monoidal/StarAutonomous.v]'s class field
    [star_double_dual] merely POSITS some iso, and that file's own header
    says so, deferring the canonical pinning to its ledger
    entry 4.  Negative 2 pins the sharpest available form of that gap:
    for an ARBITRARY [StarAutonomous] instance the posited iso is not the
    canonical map.  Read it precisely -- it does NOT say the equation is
    false, only that the class does not force it.

--------
* 用于 Structure/Monoidal/Dual.v 的边界探测（问题 #359）

Mac Lane 《CWM》第二版 §IV.2，书本第88页，向量空间对偶伴随（项目 maclane:IV.2:construction3）：对偶化到一个固定对象是逆变的，并且在右侧是自伴的。

为什么这个文件会存在。目标自身带有八个 [Fail]，它们格式良好——每个都被剥离过一次并读取了整个错误，每个都位于一个已应用（APPLIED）控制旁边，且仪器检查是无范围的。一个文件内的负值不能做的是在重命名后存活：整个文件的重命名会同步移动 [Fail] 和它命名的常量，因此当它所保护的东西消失时保护器仍然保持绿色。因此，下列每个负值都命名了目标的一个常量，该文件镜像了目标的所有 [Require] 行——在该列表的短前缀上构建的探针是经典方式，用于使一个负值因为它从未测量过的原因（缺失的强制转换、缺失的符号）而通过，但并不证明任何东西。

它还会镜像目标的 [Remove Hints] 线路，并且该线路是防护性的而非承重的 —— 在两个文件中测量的：删除

移除 Hints Sets_Product_Monoidal : typeclass_instances。

使目标编译清洁，并使该探针编译清洁，并且该文件的两个负样例随后都以字节完全相同的错误信息失败。 它不花任何代价的原因是目标本身的头文件所给出的：`C` 带着一个 [SymMonClosed] 实例到达，其强制转换已经确定了单子结构，因此解析从未被提供选择。 这里为了与目标以及两个捐赠者保持一致而进行了镜像，其中环境类别没有受到如此约束。

种类，根据错误文本而不是根据标签来区分——并注意，仅尾部并不能分开其中两个：
  可形成性（FORMABILITY）以 `universe inconsistency: Cannot enforce cp = ch` 结束
  转换（CONVERSION）以 `cannot unify` 结束，发生在同一类型的两个项之间
  类型（TYPING）也以 `cannot unify` 结束，但发生在对象变量上，其主体报告 [Sets] 的两个不同对象作为预期类型和实际类型

审阅者的检查点是负点2。这个问题要求构造典型的双对偶态射，而不是假定其可逆。[Structure/Monoidal/StarAutonomous.v] 的类字段 [star_double_dual] 仅假设某个同构，并且该文件的头部也说明了这一点，将典型的钉定推迟到其账目条目4中。负点2 钉定了该差距的最尖锐形式：对于任意的 [StarAutonomous] 实例，假设的同构并不是典型映射。精确阅读——它并没有说这个方程是错误的，只是说该类并不强制它。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.StarAutonomous.
Require Import Category.Instance.Sets.
Require Import Category.Adjunction.Right.
Require Import Category.Structure.Monoidal.Dual.

Remove Hints Sets_Product_Monoidal : typeclass_instances.

Open Scope category_scope.

Generalizable All Variables.

Section ProbeDual359.

Context {C : Category}.
Context `{@SymMonClosed C}.
Context (d : C).

(*
Controls.  Every constant a negative names is also named OUTSIDE a
   [Fail] and APPLIED, never left bare -- an unapplied polymorphic
   constant elaborates for reasons unrelated to the negative and so
   certifies nothing.

--------
控制。每一个常数负名称也被命名在 [Fail] 之外并被应用，从不裸露——未应用的多态常数因与负名称无关的原因进行展开，因此不证明任何内容。
*)
Check (dd_unit d).
Check (double_dual_unit d).
Check (dual_self_adjoint_on_the_right d).
Check (fun x : C => dd_unit d x).
Check (fun x : C => transform[double_dual_unit d] x).
Check (@aor C C (dual d) (dual d) (dual_self_adjoint_on_the_right d)).

(*
CONVERSION 1 -- [dd_unit] is not the bare braid-transpose on the
   nose: the residue is `id ⨂ id`, and writing that residue out closes
   the very same statement at [eq_refl], which is what makes this
   negative discriminate rather than merely fail.

--------
转换 1 -- [dd_unit] 并不是鼻子上的裸编织转置：残差是 `id ⨂ id`，将该残差写出来会在 [eq_refl] 处闭合同一个语句，这就是使其为负判别而不仅仅是失败的原因。
*)
Fail Example probe359_braid_strict (x : C) :
  dd_unit d x = dcur (eval' ∘ braid) := eq_refl.

(* Control for CONVERSION 1, with the residue exhibited. / CONVERSION 1 的对照，显示了残留物。 *)
Example probe359_braid_residue (x : C) :
  dd_unit d x = dcur (eval' ∘ (id[x ⇒ d] ⨂ id[x]) ∘ braid) := eq_refl.

(*
TYPING -- off the diagonal the two legs of the bijection do not even
   share a type, so `to = from` is not statable there at all.  This is
   the honest form of Mac Lane's symmetry remark.

--------
键入——在对角线之外，双射的两条腿甚至没有共享一个类型，因此在那里根本无法表示 `to = from`。这是 Mac Lane 对称性评论的真实形式。
*)
Fail Example probe359_offdiagonal (a x : C) :
  to (@aor C C (dual d) (dual d) (dual_self_adjoint_on_the_right d) a x)
    = from (@aor C C (dual d) (dual d)
              (dual_self_adjoint_on_the_right d) a x) := eq_refl.

(* Control: ON the diagonal the two legs ARE the same term. / 控制：在对角线上，两条边是同一项。 *)
Example probe359_diagonal (a : C) :
  to (@aor C C (dual d) (dual d) (dual_self_adjoint_on_the_right d) a a)
    = from (@aor C C (dual d) (dual d)
              (dual_self_adjoint_on_the_right d) a a) := eq_refl.

End ProbeDual359.

(*
Instrument check.  [Fail] is live in this build and does notice a
   conversion failure.  Scope-free deliberately, so that it cannot fail
   on a missing scope delimiter instead of on the proposition.

--------
仪器检查。[Fail] 在此构建中处于活动状态，并确实会注意到转换失败。特意不使用作用域，以便它不会因缺少作用域分隔符而失败，而是因命题失败。
*)
Fail Example probe359_instrument : (true = false) := eq_refl.
