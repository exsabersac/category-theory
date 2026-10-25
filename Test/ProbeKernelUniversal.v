(**
* Boundary probes for kernels as universal elements

    Companion to Structure/Kernel/Universal.v and its satellite
    Structure/Kernel/Universal/Examples.v (issue #304).  Those files make
    strength claims of four different grades -- some definitional, some
    only up to [≈], one a universe restriction, and one a contrast
    between two packagings -- and the negative side of each is a boundary
    no in-tree consumer would notice breaking.  They are pinned here.
    **If the [Fail] commands below stop failing, this file breaks the
    build.**

    Every negative is paired with a positive control that must SUCCEED: a
    [Fail] alone passes just as happily when a name has been renamed out
    from under it.  The instrument itself was checked out of band --
    wrapping [Fail] around a succeeding [Check] reports "The command has
    not failed!" and aborts compilation -- and each negative below was
    compiled once with the [Fail] stripped, to confirm the error is the
    intended failure and not a syntax, scope or resolution error.  Where
    the stripped error is NOT of the form "cannot unify", the actual
    message is quoted at the probe.

    THE FOUR BOUNDARIES.

    (1) THE KILL PACKAGING IS NOT A RECORD-LEVEL BIJECTION, IN EITHER
    DIRECTION.  [kernel_aue] and [aue_kernel] preserve the underlying
    morphism by [eq_refl], and in one direction the mediator too; but
    neither whole record survives, and the obstruction is named: the kill
    shape (f ∘ h ≈ 0) and the fork shape (f ∘ h ≈ 0 ∘ h) are exchanged by
    the [Qed]-opaque [kill_fork] / [fork_kill], and [eq_desc] is
    proof-RELEVANT in its hypothesis, so even the [fork_eq] field alone
    does not come back.

    (2) THE FORK PACKAGING IS DEFINITIONALLY TIGHTER THAN THE KILL
    PACKAGING -- the opposite of what the naming suggests.  On the fork
    side one whole round trip IS [eq_refl] ([aue_equalizer_round]),
    because no reshaping happens; the other is not, and the ONLY
    obstruction there is that [sigT] has no eta, which
    [aue_equalizer_round_universal] states positively.

    (3) THE BUNDLED SETOID ISOMORPHISM CARRIES A UNIVERSE RESTRICTION THE
    UNIVERSE-FREE FORMS DO NOT.  [kernel_universal_element_iso] is stated
    over [C : Category@{u u0 u0}] with [u <= u0] -- objects at or below
    homs -- because [obj[Sets@{o so}]] is [SetoidObject@{o o}]
    (Instance/Sets.v), identifying a setoid's carrier and relation
    universes, while [KernelData]'s carrier sits at C's object universe
    and its relation at C's proof universe.  [Ab@{u u0}] is declared with
    [u0 < u], so neither it nor [Rng] can be substituted.  The passages,
    the round-trip lemmas and [kernel_representation] carry no such
    restriction and DO instantiate at [Ab]; the positive controls below
    are that pair.

    (4) THE TWO PRESHEAVES ARE DISTINCT TYPES.  [KillPresheaf f] and
    [ForkPresheaf f zmor] are naturally isomorphic ([kill_fork_iso]) with
    both components the identity on the underlying morphism, but they are
    not the same functor and their element types are not the same type,
    so the isomorphism is a construction and not a coercion.

--------
* 作为通用元素的核边界探针

本文件为 Structure/Kernel/Universal.v 及其附属文件 Structure/Kernel/Universal/Examples.v（问题 #304）的配套文件。这些文件提出了四种不同等级的强度声明——有些是定义性的，有些仅适用于 [≈]，有一个是宇宙限制，还有一个是对两种打包方式的对比——而每种声明的负面影响都是树内消费者不会注意到破坏的边界。它们在此处被固定。
**如果下面的 [Fail] 命令不再失败，本文件会导致构建失败。**

每个负面测试都配对有一个必须成功的正面控制：仅有 [Fail] 当一个名称被重命名移出它的控制范围时也一样能顺利通过。仪器本身是通过带外检查的——将 [Fail] 包裹在一个成功的 [Check] 上会报出“命令未失败！”并中止编译——下面的每个负面测试在去掉 [Fail] 后都编译过一次，以确认错误是预期的失败，而不是语法、作用域或解析错误。如果去掉保护后的错误不是“无法统一”的形式，实际消息会在探针处引用。

四个边界。

(1) 杀死包装在任一方向上都不是记录级双射。[kernel_aue] 和 [aue_kernel] 通过 [eq_refl] 保留了底层的态射，并且在一个方向上还保留了中介；但没有整个记录能够幸存下来，并且障碍已经命名：杀死形状 (f ∘ h ≈ 0) 和分叉形状 (f ∘ h ≈ 0 ∘ h) 被 [Qed] 不透明的 [kill_fork] / [fork_kill] 交换，而 [eq_desc] 在其假设中是证明相关的，因此即使只有 [fork_eq] 字段也无法恢复。

(2) 叉子包装从定义上比杀死包装更紧密——这与名称所暗示的相反。在叉子方面，一整个往返行程就是 [eq_refl]（[aue_equalizer_round]），因为没有发生重新成型；另一个则不是，唯一的阻碍是 [sigT] 没有 ETA，而 [aue_equalizer_round_universal] 明确说明了这一点。

(3) 捆绑的集合等价同构具有宇宙限制，而无宇宙形式则没有。[kernel_universal_element_iso] 是在 [C : Category@{u u0 u0}] 上声明的，带有 [u <= u0]——在 homs 的对象上或以下——因为 [obj[Sets@{o so}] 是 [SetoidObject@{o o}]（Instance/Sets.v），识别集合等价的承载和关系宇宙，而 [KernelData] 的承载位于 C 的对象宇宙，其关系位于 C 的证明宇宙。[Ab@{u u0}] 使用 [u0 < u] 声明，因此它和 [Rng] 都不能被替换。这些段落、往返引理和 [kernel_representation] 没有任何这样的限制，并且确实在 [Ab] 处实例化；下面的正向控制就是这对。

(4) 这两个预层是不同的类型。[KillPresheaf f] 和 [ForkPresheaf f zmor] 自然同构（[kill_fork_iso]），两者的分量都是底层态射上的恒等映射，但它们不是同一个函子，并且它们的元素类型也不是相同的类型，因此该同构是一个构造，而不是类型强制。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Kernel.
Require Import Category.Theory.Universal.Element.
Require Import Category.Structure.Kernel.Universal.
Require Import Category.Structure.Kernel.Universal.Examples.

Local Open Scope category_scope.

Section KillProbes.

Context {C : Category}.
Context {ZM : ZeroMorphisms C}.
Context {x y k : C}.
Context (f : x ~> y).
Context (i : k ~> x).
Context (K : IsKernelOf f i).
Context (U : AUniversalElement (KillPresheaf f) k).

(**
** (1) The kill packaging preserves the morphism, not the record

    Positive controls: the morphism survives both passages by [eq_refl],
    the mediator survives one of them as a TERM, and both survive up to
    [≈].

--------
** (1) 杀伤包装保留了同态，而不是记录

    阳性对照：同态在 [eq_refl] 的两次传代中都能存活，
    介体作为 TERM 在其中一次传代中存活，并且两者都能存活到 [≈]。
*)

Check (kernel_aue_morphism f K).
Check (aue_kernel_morphism f U).
Check (fun (d : C) (h : d ~{C}~> x) (Hh : f ∘ h ≈ zmor) =>
         kernel_aue_mediator f K d h Hh).
Check (fun (d : C) (h : d ~{C}~> x) (Hh : f ∘ h ≈ zmor ∘ h) =>
         kernel_round_mediator f K h Hh).
Check (fun (d : C) (p : Kills f d) => aue_kernel_round_mediator f U d p).

(**
Negative: the whole record does not come back on the kernel side.
    (Stripped: cannot unify [aue_kernel f (kernel_aue f K)] and [K].)

--------
负面：整个记录没有返回到内核端。
（已剥离：无法统一 [aue_kernel f (kernel_aue f K)] 和 [K]。）
*)
Fail Check (eq_refl : aue_kernel f (kernel_aue f K) = K).

(**
Negative: not even the [fork_eq] field alone -- [kill_fork] and
    [fork_kill] are opaque, so their composite is not the identity term.
    (Stripped: cannot unify the two [fork_eq] terms.)

--------
消极：即使只有 [fork_eq] 字段也不行 —— [kill_fork] 和 [fork_kill] 是不透明的，所以它们的组合不是恒等项。（已剥离：无法统一两个 [fork_eq] 项。）
*)
Fail Check (eq_refl : fork_eq (aue_kernel f (kernel_aue f K)) = fork_eq K).

(**
Negative: nor on the universal-element side.  (Stripped: cannot unify
    [kernel_aue f (aue_kernel f U)] and [U].)

--------
否定：在通用元素方面也不行。（已剥离：无法统一 [kernel_aue f (aue_kernel f U)] 和 [U]。）
*)
Fail Check (eq_refl : kernel_aue f (aue_kernel f U) = U).

(**
Negative: and the mediator round trip on the kill side is genuinely
    only up to [≈] -- the Leibniz form fails, unlike its fork-side twin
    [aue_equalizer_round_mediator], which holds at [=].  (Stripped: cannot
    unify the two [unique_obj] terms.)

--------
负面：在终止方上，中介往返实际上仅限于 [≈]——莱布尼茨形式失败，不像其分叉方的双胞胎 [aue_equalizer_round_mediator]，可以在 [=] 上成立。（已简化：无法统一两个 [unique_obj] 项。）
*)
Fail Check (fun (d : C) (p : Kills f d) =>
              eq_refl
                : unique_obj (@aue_universal (C^op) (KillPresheaf f) k
                                (kernel_aue f (aue_kernel f U)) d p)
                  = unique_obj (@aue_universal (C^op) (KillPresheaf f) k U d p)).

End KillProbes.

Section ForkProbes.

Context {C : Category}.
Context {x y k : C}.
Context (f g : x ~> y).
Context (i : k ~> x).
Context (E : IsEqualizer f g k i).
Context (V : AUniversalElement (ForkPresheaf f g) k).

(**
** (2) The fork packaging IS a record-level identity, one way

    Positive controls: one whole round trip is [eq_refl] on the whole
    record, and on the other side the universal clause survives up to the
    [sigT] repacking, which is the only thing missing.

--------
** (2) 分叉打包是在记录级的身份识别，是单向的

    阳性对照：一次完整的往返是整个记录上的 [eq_refl]，而在另一端，通用条款一直保留到 [sigT] 重新打包，这是唯一缺失的部分。
*)

Check (aue_equalizer_round f g E).
Check (aue_equalizer_round_universal f g V).
Check (aue_equalizer_round_elem f g V).
Check (fun (d : C) (p : Forks f g d) => aue_equalizer_round_mediator f g V d p).

(**
Negative: the other whole round trip is not [eq_refl].  (Stripped:
    cannot unify [equalizer_aue f g (aue_equalizer f g V)] and [V].)

--------
负面：另一趟完整往返旅行不是 [eq_refl]。（剥离后：无法统一 [equalizer_aue f g (aue_equalizer f g V)] 和 [V]。）
*)
Fail Check (eq_refl : equalizer_aue f g (aue_equalizer f g V) = V).

(**
** (4) The two presheaves are distinct types

    Positive control first: they are naturally isomorphic.

--------
** (4) 这两个预层是不同的类型

先看正对照：它们自然同构。
*)

Check (fun (ZM : ZeroMorphisms C) => kill_fork_iso f).

(**
Negative: and nevertheless not the same functor.  This one does NOT
    report "cannot unify"; stripped, the message is: the term [eq_refl]
    'has type "KillPresheaf f = KillPresheaf f" while it is expected to
    have type "KillPresheaf f = ForkPresheaf f zmor"'.

--------
否定：然而不是相同的函子。这个不会报告“无法统一”；去掉后，消息是：术语 [eq_refl] “的类型是 'KillPresheaf f = KillPresheaf f'，而期望的类型是 'KillPresheaf f = ForkPresheaf f zmor'。”
*)
Fail Check (fun ZM : ZeroMorphisms C =>
              eq_refl : KillPresheaf f = ForkPresheaf f zmor).

(**
Negative: nor are their element types the same type.  Stripped, again
    without a "cannot unify" line: the term [eq_refl] 'has type
    "Kills f k = Kills f k" while it is expected to have type
    "Kills f k = Forks f zmor k"'.

--------
消极：它们的元素类型也不是相同类型。再次剥离，没有“cannot unify”行：术语 [eq_refl] 的类型是“Kills f k = Kills f k”，而预期类型是“Kills f k = Forks f zmor k”。
*)
Fail Check (fun ZM : ZeroMorphisms C =>
              eq_refl : Kills f k = Forks f zmor k).

End ForkProbes.

(**
** (3) The universe restriction on the bundled isomorphism

    Positive control: at an abstract category -- where the elaborator is
    free to put the object universe at or below the hom universe -- both
    bundled isomorphisms exist.

--------
** (3) 捆绑同构的宇宙限制

    正控制：在一个抽象范畴——在这里展开器可以自由地将对象宇宙置于同态宇宙之上或之下——两种捆绑同构都存在。
*)

Check (fun (C : Category) (ZM : ZeroMorphisms C) (x y : C) (f : x ~> y)
           (k : C) => @kernel_universal_element_iso C ZM x y f k).

Check (fun (C : Category) (x y : C) (f g : x ~> y) (k : C) =>
         @equalizer_universal_element_iso C x y f g k).

(**
Negative: neither instantiates at a concrete algebraic category.
    These are UNIVERSE INCONSISTENCIES, not unification failures.
    Stripped, the first reports that [Ab] "has type
    Category@{a b b} while it is expected to have type Category@{c d d}",
    followed by "universe inconsistency: Cannot enforce b = d because
    b < a <= d" -- i.e. [Ab]'s own declaration [Ab@{u u0}] with [u0 < u]
    (objects strictly above homs) is exactly what is refused.  [@] is used
    throughout so that no implicit argument can make a command fail for an
    unrelated reason.

--------
消极：都没有在具体的代数范畴中实例化。这些是宇宙不一致，而不是统一失败。简化后，第一个报告 [Ab] “的类型是 Category@{a b b}，但预期类型是 Category@{c d d}”，随后出现“宇宙不一致：无法强制 b = d，因为 b < a <= d”——即 [Ab] 自己的声明 [Ab@{u u0}] 与 [u0 < u]（对象严格高于 Hom）正是被拒绝的。[@] 在整个过程中被使用，以确保没有隐含参数会因为无关原因导致命令失败。
*)

Fail Check (fun (A B : AbObject) (f : A ~{Ab}~> B) (k : Ab) =>
              @kernel_universal_element_iso Ab
                (ZeroMorphisms_of_ZeroObject Ab_Zero) A B f k).

Fail Check (fun (R S : Rng) (u v : R ~{Rng}~> S) (k : Rng) =>
              @equalizer_universal_element_iso Rng R S u v k).

(**
Positive control, immediately: the universe-free forms DO reach [Ab],
    and so does the representability statement.  This is the pair that
    makes the restriction a measured fact about the bundled packaging
    rather than about the theorem.

--------
阳性对照，立即：无宇宙形式确实达到 [Ab]，表示性陈述也是如此。这是一对使得限制成为关于捆绑封装的可测量事实，而不是关于定理的事实。
*)

Check (fun (A B : AbObject) (f : A ~{Ab}~> B) => ab_kernel_aue f).
Check (fun (A B : AbObject) (f : A ~{Ab}~> B) => ab_kernel_representation f).
Check (fun (A B : AbObject) (f : A ~{Ab}~> B) => ab_kernel_Representable f).
Check (fun (A B : AbObject) (f : A ~{Ab}~> B) => ab_kernel_repr_obj f).
Check (fun (A B : AbObject) (f : A ~{Ab}~> B) (z : AbObject)
           (h : z ~{Ab}~> A) => ab_kernel_round f h).

(**
** The zero-object bridge is definitional, and Rng has no zero morphisms

    Positive controls: [zmor] at the derived structure IS [zero_mor], the
    two kernel predicates are the same type, and the [Ab] witness computes.

--------
** 零对象桥是定义性的，而 Rng 没有零态射

    阳性对照：在导出结构中 [zmor] 是 [zero_mor]，两个核谓词是相同类型，并且 [Ab] 见证可以计算。
*)

Check (fun (C : Category) (Z : @ZeroObject C) (x y : C) =>
         @zmor_is_zero_mor C Z x y).

Check (fun (C : Category) (Z : @ZeroObject C) (x y k : C) (f : x ~> y)
           (i : k ~> x) => @IsKernel_is_IsKernelOf C Z x y f k i).

Check (ab_parity_med_computes).
Check (ab_parity_kernel_has_two).
Check (ab_parity_kernel_proper).

(**
Positive control on the negative theorem: Rng has no zero-morphism
    family, hence no zero object.  These are THEOREMS, not [Fail] probes --
    the difference matters, and is the reason the fork packaging exists.

--------
关于负定理的正控制：Rng 没有零态射族，因此没有零对象。这些是定理，不是 [Fail] 探针——区别很重要，也是分叉打包存在的原因。
*)

Check (Rng_no_zero_morphisms : ZeroMorphisms Rng → False).
Check (Rng_no_zero_object : @ZeroObject Rng → False).

(** ... and the fork presheaf is nevertheless formable there. / ... 但是分叉预层在那里仍然可以形成。 *)
Check (fun (R S : Rng) (u v : R ~{Rng}~> S) => Rng_fork_presheaf u v).
