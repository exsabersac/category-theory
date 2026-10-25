(**
* Boundary probe for Adjunction/Right.v (issue #358)

    Mac Lane CWM 2nd ed. §IV.2 Definition 2, book p. 89 (the item
    maclane:IV.2:def2) -- a pair of contravariant
    functors each adjoint on the right, together with Mac Lane's own
    warning that this relation is NOT the ordinary adjunction read
    through an opposite category.

    WHY THIS FILE EXISTS AT ALL.  [Adjunction/Right.v] carries ten
    [Fail]s of its own and they are well formed -- each was stripped
    once and its whole error message read, each sits beside a control
    that must succeed, and the instrument check is scope-free.  What an
    in-file negative CANNOT do is survive a rename: a whole-file rename
    moves the [Fail] and the constant it names in lockstep, so the guard
    stays green while the thing it guarded is gone.  Every negative
    below therefore names a constant of the TARGET, and the file mirrors
    ALL of the target's [Require] lines -- a probe built on a short
    prefix of that list is the classic way to make a negative pass for a
    reason it never measured (a missing coercion, an absent notation),
    certifying nothing.

    KINDS, separated by the error TEXT rather than by label:
      TYPING       a plain `The term "H" has type ... while it is
                   expected to have type ...`, with NO `cannot unify`
                   and no universe clause
      CONVERSION   ends `(cannot unify "X" and "Y")`
      FORMABILITY  ends `(universe inconsistency: Cannot enforce ...)`

    THE FIRST NEGATIVE IS THE REVIEWER'S BAR.  The question that decides
    whether this issue has content at all is whether
    [AdjointOnTheRight S T] is merely an abbreviation for the ordinary
    [T^op ⊣ S].  It is not, and negative 1 is what says so: stripped, it
    reports

      The term "H" has type "T^op ⊣ S" while it is expected to have type
       "AdjointOnTheRight S T".

    -- a plain type mismatch.  The two are nevertheless INTERDERIVABLE,
    which is what the controls name: [Adjunction_of_AdjointOnTheRight]
    and [AdjointOnTheRight_of_Adjunction] pass both ways and all four
    round trips hold at [eq_refl] in the target.  So the class is a
    genuine record that is equivalent to, and not definitionally equal
    to, the ordinary adjunction at the opposite categories.

    NOTE THE ORIENTATION, which is easy to get backwards.  BOTH
    readings are correct and both are delivered: [T^op ⊣ S] is the one
    matching the direction of the book's bijection
    [A(a, T x) ≅ X(x, S a)], while [S^op ⊣ T] matches its INVERSE, and
    the target ships the second as the primed orientation with passages
    both ways.  So which one is "the" reduction is a question of which
    way the bijection is read, NOT an error in either spelling.
    Negative 2 is the reverse direction of negative 1, and negative 3
    separates the right-adjoint class from the left-adjoint one.

    WHAT IS NOT GUARDED HERE.  The target's four FORMABILITY negatives
    need section-local [Universes]/[Constraint] declarations naming
    levels that do not exist outside them, so they stay in the target
    beside their controls.  They measure TWO DIFFERENT identifications,
    two negatives each: that hom is identified with proof (rejected at
    [Opposite], and independently at [Sets] with no functor in the
    command at all), and that A's hom is identified with X's.  Neither
    is a claim about a name this file could rename-test.

--------
* 用于附加/右.v 的边界探针（问题 #358）

Mac Lane《CWM》第2版 §IV.2 定义 2，书中第89页（条目 maclane:IV.2:def2）——一对每个在右侧都有伴随的逆变函子，以及 Mac Lane 自己的警告，即这种关系不是通过对偶范畴来读取的普通伴随。

为什么这个文件会存在。[Adjunction/Right.v] 拥有十个它自己的 [Fail]，并且它们格式良好——每一个都曾被剥离一次，并且其完整的错误信息都已读取，每一个都紧挨着一个必须成功的控制，并且仪器检查是无作用域的。一个文件内的负面项绝不能做的事情是重命名后仍然存在：整个文件的重命名会同步移动 [Fail] 和它所命名的常量，因此当被保护的对象消失时，保护器仍然保持绿色。因此，下面的每个负面项都命名了目标对象的一个常量，并且该文件反映了目标对象的所有 [Require] 行——在该列表的一个短前缀上构建的探测是经典方法，用于让负面项通过一个它从未测量过的原因（缺失的强制转换，缺失的符号表示），而不会认证任何东西。

类型，按错误文本而非标签区分：
      TYPING       一个简单的 `The term "H" has type ... while it is expected to have type ...`，没有 `cannot unify` 也没有 universe 条款
      CONVERSION   以 `(cannot unify "X" and "Y")` 结尾
      FORMABILITY  以 `(universe inconsistency: Cannot enforce ...)` 结尾

第一个否定是评论者的屏障。决定这个问题是否有意义的问题是 [AdjointOnTheRight S T] 是否仅仅是普通 [T^op ⊣ S] 的缩写。事实并非如此，第一个否定就是这么说的：去掉修饰，它报告

术语“H”的类型为“T^op ⊣ S”，而预期类型为“AdjointOnTheRight S T”。

-- 一个简单的类型不匹配。不过，两者仍然可以互导，这就是控件命名的原因：[Adjunction_of_AdjointOnTheRight] 和 [AdjointOnTheRight_of_Adjunction] 双向传递，并且在目标中的 [eq_refl] 所有四次往返都成立。因此，该类是真正的记录，相当于普通的对偶范畴上的伴随，但不在定义上等同于它。

注意方向，这很容易弄反。两个读数都是正确的，并且都已提供：[T^op ⊣ S] 是与书中双射方向匹配的那个，而 [A(a, T x) ≅ X(x, S a)]，虽然 [S^op ⊣ T] 与其逆向匹配，并且目标将第二个作为带有双向通路的原始方向。因此，哪一个是“真正的”约简，取决于双射的阅读方式，而不是拼写的错误。负2 是负1 的反向，而负3 将右伴随类与左伴随类分开。

这里未被保护的内容是什么。目标的四个可形成性（FORMABILITY）否定需要在各自的节内进行本地 [Universes]/[Constraint] 声明，声明的级别在其他地方不存在，这样它们才会保留在目标中，与其控制项并列。它们测量两个不同的识别，每个识别两个否定：一个是同源体（hom）通过证据被识别（在 [Opposite] 被拒绝，并在 [Sets] 独立被拒绝，在命令中根本没有函数符），另一个是 A 的同源体被识别为 X 的同源体。这两者都不是关于此文件可能重新命名测试的名称的声明。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Adjunction.Opposite.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Adjunction.Natural.Transformation.Universal.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Adjunction.Right.

Open Scope category_scope.

Generalizable All Variables.

Section ProbeRight358.

Context {A X : Category}.
Context {S : (A^op) ⟶ X}.
Context {T : (X^op) ⟶ A}.

(*
Controls.  Every constant a negative names is also named OUTSIDE a
   [Fail] and APPLIED, never left bare -- an unapplied polymorphic
   constant elaborates for reasons unrelated to the negative and so
   certifies nothing.

--------
控制。每一个常数负名称也被命名在 [Fail] 之外并被应用，从不裸露——未应用的多态常数因与负名称无关的原因进行展开，因此不证明任何内容。
*)
Check (AdjointOnTheRight S T).
Check (AdjointOnTheLeft S T).
Check (@Adjunction (A^op) X (Opposite_Functor T) S).
Check @Adjunction_of_AdjointOnTheRight.
Check @AdjointOnTheRight_of_Adjunction.
Check (MutuallyRightAdjoint S T).
Check (fun H : AdjointOnTheRight S T =>
         MutuallyRightAdjoint_of_AdjointOnTheRight S T H).
Check (fun H : MutuallyRightAdjoint S T =>
         AdjointOnTheRight_of_MutuallyRightAdjoint S T H).
Check @AdjointOnTheRight_sym.
Check @right_does_not_imply_left.
Check @Chain3_not_AdjointOnTheLeft.
Check @Chain3_AdjointOnTheRight.
Check @Powerset_not_AdjointOnTheLeft.
Check @right_does_not_imply_left_in_Sets.

(* TYPING 1 -- the reviewer's bar: the class is not an abbreviation. / 打字 1——评论员的酒吧：类不是缩写。 *)
Fail Definition probe358_not_an_abbreviation
  (H : @Adjunction (A^op) X (Opposite_Functor T) S) :
  AdjointOnTheRight S T := H.

(* TYPING 2 -- and not in the other direction either. / 打字 2——也不是朝另一个方向。 *)
Fail Definition probe358_not_an_abbreviation_rev
  (H : AdjointOnTheRight S T) :
  @Adjunction (A^op) X (Opposite_Functor T) S := H.

(*
TYPING 3 -- right and left are different classes, not one class
   spelled two ways.  The MATHEMATICAL separation is the target's
   [right_does_not_imply_left], a theorem over all categories; this
   negative only records that they are not definitionally equal.

--------
输入 3 —— 右和左是不同的类，不是同一个类的两种拼写方式。数学上的分离是目标的 [right_does_not_imply_left]，它是关于所有类别的定理；这个否定只是记录它们在定义上不相等。
*)
Fail Definition probe358_right_is_not_left
  (H : AdjointOnTheRight S T) : AdjointOnTheLeft S T := H.

(*
CONVERSION 4-5 -- the hom-set presentation and the unit/counit
   presentation are interderivable but their round trips are NOT
   [eq_refl]: the classes are rebuilt rather than returned.  Contrast
   the FOUR round trips against the ordinary adjunction, which the
   target pins at [eq_refl].

--------
转换 4-5 —— 同类集表示法和单位/余单位表示法是可相互推导的，但它们的往返转换不是 [eq_refl]：这些类是被重建的，而不是直接返回的。 将这四次往返转换与普通的伴随比较，目标将其固定在 [eq_refl]。
*)
Fail Example probe358_MRA_round_strict (H : MutuallyRightAdjoint S T) :
  MutuallyRightAdjoint_of_AdjointOnTheRight S T
    (AdjointOnTheRight_of_MutuallyRightAdjoint S T H) = H := eq_refl.

Fail Example probe358_aor_MRA_round_strict (H : AdjointOnTheRight S T) :
  AdjointOnTheRight_of_MutuallyRightAdjoint S T
    (MutuallyRightAdjoint_of_AdjointOnTheRight S T H) = H := eq_refl.

End ProbeRight358.

(*
Instrument check.  [Fail] is live in this build and does notice a
   conversion failure.  Scope-free deliberately, so that it cannot fail
   on a missing scope delimiter instead of on the proposition.

--------
仪器检查。[Fail] 在此构建中处于活动状态，并确实会注意到转换失败。特意不使用作用域，以便它不会因缺少作用域分隔符而失败，而是因命题失败。
*)
Fail Example probe358_instrument : (true = false) := eq_refl.
