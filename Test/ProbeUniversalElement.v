(**
* Boundary probes for universal elements

    Companion to Theory/Universal/Element.v, its satellites
    Theory/Universal/Element/Elements.v and
    Theory/Universal/Element/Examples.v (issue #303, Mac Lane §III.1
    Definition 2 and Remark 3).  Those files make strength claims of three
    different grades — some definitional, some only up to [≈], and one a
    universe restriction — and the negative side of each is a boundary no
    in-tree consumer would notice breaking.  They are pinned here.  **If the
    [Fail] commands below stop failing, this file breaks the build.**

    Every negative is paired with a positive control that must SUCCEED: a
    [Fail] alone passes just as happily when a name has been renamed out
    from under it.  The instrument itself was checked out of band —
    wrapping [Fail] around a succeeding [Check] reports "The command has
    not failed!" and aborts compilation — and each negative below was
    compiled once with the [Fail] stripped, to confirm the error is the
    intended failure and not a syntax, scope or resolution error.  Where
    the stripped error is NOT of the form "cannot unify", the actual
    message is quoted at the probe.

    THE FIVE BOUNDARIES.

    (1) THE MATE COMPUTES, BUT IS NOT THE COVARIANT LEMMA'S TERM.
    [ue_mate]'s ACTION is [fmap[H] k x] by [eq_refl] ([ue_mate_at]), and
    [Covariant_Yoneda_Lemma D H r] has the same action — but the two
    transformations are distinct terms, their naturality fields being
    separate opaque [Program] obligations.  Hence [ue_mate_covariant] is
    stated up to [≈] and not by [eq_refl].  The same seam separates
    [ue_mate] from the hand-built [ue_transform].

    (2) THE YONEDA PASSAGE PRESERVES THE ELEMENT, NOT THE RECORD.  The
    deliverable-2 isomorphism is an iso of SETOIDS, and what its two
    round-trip laws say is that the underlying element survives — which
    it does by [eq_refl].  The whole [AUniversalElement] record does not:
    [AUniversalElement_of_mate] rebuilds the factorization data.  This is
    the difference between the Yoneda passage and the two encodings'
    passage (§3 below), and it is why the header declines to call the
    former a bijection of types.

    (3) THE 3(b) PASSAGE IS DIFFERENT IN KIND — AND STILL NOT A RENAMING.
    [AUniversalElement (HomAfter S c) a] and [AUniversalArrow c S a] have
    field types that are convertible one for one, so both round trips are
    [eq_refl] ON THE WHOLE RECORD.  They are nevertheless distinct types,
    and the two passages are genuine constructions, not coercions.

    (4) THE 3(a) PASSAGE PRESERVES THE ELEMENT ON THE NOSE AND THE ARROW
    ONLY UP TO [≈].  Rebuilding a map out of the singleton from its value
    at [ttt] is [global_elements_iso]'s non-definitional leg, and that is
    where it lands.

    (5) THE YONEDA ROUTE CARRIES A UNIVERSE RESTRICTION THE DIRECT ROUTE
    DOES NOT.  [Yoneda_Lemma] — hence [representability_by_yoneda], hence
    [universal_element_representation] — is stated over
    [C : Category@{u0 u0 u0}], object, hom and proof universes IDENTIFIED.
    A category whose objects sit strictly above its homs cannot be
    substituted, and [Instance/Coq/Nat.v]'s [Endos] is one.  This is why
    every accessor in Theory/Universal/Element.v is routed through the
    hand-built [ue_transform] / [AUniversalElement_of_repr] rather than
    through the Yoneda composite, and why Examples.v exists at all: it
    instantiates at exactly the category the Yoneda route cannot reach.
    NOTE the scope — this is a restriction on the DONOR
    ([Structure/UniversalProperty.v], measured), not one introduced by
    issue #303, and nothing here shows it is unavoidable.

--------
* 通用元件的边界探测器

《Theory/Universal/Element.v》的伴随文件，其附属文件为
Theory/Universal/Element/Elements.v 和
Theory/Universal/Element/Examples.v（问题 #303，Mac Lane §III.1 定义 2 和备注 3）。这些文件提出了三种不同等级的强度声明——一些是定义性的，一些仅到 [≈] 为止，还有一个是宇宙限制——每一种的负面影响都是树内消费者注意不到的界限。它们在这里被固定。**如果下面的 [Fail] 命令不再失败，本文件将导致构建失败。**

每个负面测试都配有一个必须成功的正面控制测试：仅有 [Fail] 当一个名称被重命名后从其下移除时也能顺利通过。该工具本身是在带外进行检查的——将 [Fail] 包裹在一个成功的 [Check] 上会报告“命令未失败！”并中止编译——下面的每个负面测试都曾在去掉 [Fail] 的情况下编译一次，以确认错误是预期的失败，而不是语法、作用域或解析错误。当去掉后的错误不是“无法统一”形式时，实际消息会在探测中引用。

五大界限。

(1) 配偶会计算，但不是协变引理的项。[ue_mate] 的作用是由 [eq_refl]（[ue_mate_at]）实施的 [fmap[H] k x]，并且 [Covariant_Yoneda_Lemma D H r] 具有相同的作用——但这两个变换是不同的项，它们的自然性域是独立的不透明 [Program] 义务。因此 [ue_mate_covariant] 是在 [≈] 的范围内陈述的，而不是由 [eq_refl] 陈述的。同样的接缝将 [ue_mate] 与手工构建的 [ue_transform] 分开。

(2) YONEDA 通道保留的是元素，而不是记录。deliverable-2 同构是 SETOIDS 的同构，它的两个往返定律说明的是底层元素得以保留——实际上它确实通过 [eq_refl] 得以保留。整个 [AUniversalElement] 记录则没有：[AUniversalElement_of_mate] 重建了分解数据。这就是 Yoneda 通道与两个编码通道（见下文 §3）之间的区别，也正是为什么标题拒绝将前者称为类型之间的双射。

(3) 3(b) 段落在类型上是不同的——而且仍然不是重新命名。 [AUniversalElement (HomAfter S c) a] 和 [AUniversalArrow c S a] 的字段类型可以一一转换，因此两次往返都是针对整个记录的 [eq_refl]。 它们仍然是不同的类型，这两个段落是真正的构造，而不是强制转换。

(4) 3(a) 段仅在 [≈] 上保留鼻子和箭头的元素。从 [ttt] 的值重建单例映射是 [global_elements_iso] 的非定义性部分，这就是它落脚的地方。

(5) YONEDA 路径带有一个宇宙限制，而直接路径没有。[Yoneda_Lemma] —— 因此 [representability_by_yoneda]，因此 [universal_element_representation] —— 是在 [C : Category@{u0 u0 u0}]、对象、hom 和证明宇宙上声明的。一个其对象严格位于其 hom 之上的范畴不能被替换，而 [Instance/Coq/Nat.v] 的 [Endos] 就是这样的一个范畴。这就是为什么 Theory/Universal/Element.v 中的每个访问器都通过手工构建的 [ue_transform] / [AUniversalElement_of_repr] 路由，而不是通过 Yoneda 组合，以及为什么 Examples.v 的存在：它在 Yoneda 路径无法到达的恰好范畴上进行实例化。注意范围——这是对 DONOR ([Structure/UniversalProperty.v], measured) 的一个限制，而非由 issue #303 引入，这里没有任何东西表明它是不可避免的。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Yoneda.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.UniversalProperty.
Require Import Category.Construction.Elements.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Element.
Require Import Category.Theory.Universal.Element.Elements.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Coq.Nat.
Require Import Category.Theory.Universal.Element.Examples.

Local Open Scope category_scope.

Section Probes.

Context {D : Category}.
Context {H : D ⟶ Sets}.
Context {r : D}.
Context (U : AUniversalElement H r).

(**
** (1) The mate computes; the covariant lemma's term is not it

    Positive controls: the action is [eq_refl], and the two agree up to
    [≈].

--------
** (1) 配偶进行计算；协变引理的项不是它

    阳性对照：动作是 [eq_refl]，并且两者在 [≈] 上一致。
*)

Check (fun (d : D) (k : r ~{D}~> d) =>
         eq_refl : transform (ue_mate H r (@aue_elem D H r U)) d k
                     = fmap[H] k (@aue_elem D H r U)).

Check (ue_mate_covariant H r (@aue_elem D H r U)).
Check (ue_mate_is_transform H r U).

(**
Negative: the covariant Yoneda lemma's mate is not the same TERM.
    (Stripped: cannot unify [(Covariant_Yoneda_Lemma D H r)⁻¹ aue_elem] and
    [ue_mate H r aue_elem].)

--------
负面：协变 Yoneda 引理的伴随项不是相同的项。
（已剥离：无法统一 [(Covariant_Yoneda_Lemma D H r)⁻¹ aue_elem] 和 [ue_mate H r aue_elem]。）
*)
Fail Check (eq_refl : from (Covariant_Yoneda_Lemma D H r) (@aue_elem D H r U)
                        = ue_mate H r (@aue_elem D H r U)).

(**
Negative: nor is the hand-built transformation.  (Stripped: cannot
    unify [ue_mate H r aue_elem] and [ue_transform H r U].)

--------
消极：手工构建的转换也不是。（已剥离：无法统一 [ue_mate H r aue_elem] 和 [ue_transform H r U]。）
*)
Fail Check (eq_refl : ue_mate H r (@aue_elem D H r U) = ue_transform H r U).

(**
** (2) The Yoneda passage preserves the element, not the record

    Positive controls: the isomorphism exists, and the element survives
    both round trips by [eq_refl].

--------
** (2) Yoneda 通道保持元素，而不是记录

    阳性对照：同构存在，并且元素在经过 [eq_refl] 的两次往返后仍然存在。
*)

Check (universal_element_yoneda H r
         : @Isomorphism Sets
             (Build_SetoidObject (AUniversalElement H r)
                (AUniversalElementEquiv H r))
             (ue_yoneda_obj H r)).

Check (ue_yoneda_round_ue H r U).
Check (fun (x : H r) (I : IsIsomorphism (ue_mate H r x)) =>
         ue_yoneda_round_elem H r x I).

(**
Positive control that the naming of the sigma setoid changed nothing:
    [ue_yoneda_obj] IS [representability_by_yoneda]'s source, the
    [exists_setoid] instance included.

--------
阳性对照表明 sigma 等价类的命名没有改变任何内容：
    [ue_yoneda_obj] 是 [representability_by_yoneda] 的源，
    包含了 [exists_setoid] 实例。
*)
Check (rby_agrees H r).

(**
Negative: the whole record does not survive — [AUniversalElement_of_mate]
    rebuilds the factorization data.  (Stripped: cannot unify
    [ue_of_yoneda H r (ue_to_yoneda H r U)] and [U].)

--------
负面：整个记录没有保存 —— [AUniversalElement_of_mate] 重建了因式分解数据。（已剥离：无法统一 [ue_of_yoneda H r (ue_to_yoneda H r U)] 和 [U]。）
*)
Fail Check (eq_refl : ue_of_yoneda H r (ue_to_yoneda H r U) = U).

(**
** (3) The 3(b) passage IS a record-level bijection, and still not a
       renaming

    Positive controls: both round trips close by [eq_refl] on the WHOLE
    record, and the two clauses are literally the same clause.

--------
** (3) 3(b) 段是记录级双射，但仍不是重命名

阳性对照：两个往返在整个记录上都被 [eq_refl] 封闭，并且这两个条款在字面上是相同的条款。
*)

Check (fun (C : Category) (S : D ⟶ C) (c : C) (a : D)
           (V : AUniversalArrow c S a) => aua_of_hom_round S c V).

Check (fun (C : Category) (S : D ⟶ C) (c : C) (a : D)
           (V : AUniversalElement (HomAfter S c) a) => aue_of_hom_round S c V).

Check (fun (C : Category) (S : D ⟶ C) (c : C) (d d' : D)
           (k : d ~{D}~> d') (u : c ~{C}~> S d) => hom_after_fmap S c d d' k u).

(**
Negative: the two types are nonetheless distinct, so the passages are
    constructions and not coercions.  (Stripped: cannot unify
    [AUniversalElement (HomAfter S c) r] and [AUniversalArrow c S r].)

--------
否定：这两种类型仍然是不同的，因此这些段落是构造而不是强制。（精简：无法统一 [AUniversalElement (HomAfter S c) r] 和 [AUniversalArrow c S r]。）
*)
Fail Check (fun (C : Category) (S : D ⟶ C) (c : C) =>
              eq_refl : AUniversalElement (HomAfter S c) r
                          = AUniversalArrow c S r).

(**
** (4) The 3(a) passage: element on the nose, arrow up to [≈]

    Positive controls.

--------
** (4) 3(a) 段落：元件在鼻子上，箭头指向 [≈]

    阳性对照。
*)

Check (aue_aua_round H r U).
Check (fun V : AUniversalArrow SetsOne H r => aua_aue_round H r V).
Check (fun V : AUniversalArrow SetsOne H r => aue_of_aua_elem H r V).
Check (aua_of_aue_arrow H r U).

(**
Negative: the arrow does NOT survive by [eq_refl] — [global_element]
    rebuilds it from its value at [ttt].  (Stripped: cannot unify the two
    [universal_arrow] terms.)

--------
负面：箭头不能通过 [eq_refl] — [global_element] 存活，它是从 [ttt] 的值重建的。（已剥离：无法统一两个 [universal_arrow] 项。）
*)
Fail Check (fun V : AUniversalArrow SetsOne H r =>
              eq_refl
                : @universal_arrow _ _ SetsOne H r
                    (AUniversalArrow_of_AUniversalElement H r
                       (AUniversalElement_of_AUniversalArrow H r V))
                    = @universal_arrow _ _ SetsOne H r V).

End Probes.

(**
** (5) The Yoneda route's universe restriction

    Positive control, and the whole point of the direct route: at
    [Endos] — whose objects sit strictly above its homs — the general
    class is inhabited, the universal element is [O], and Riehl's initial
    object of the category of elements exists.

--------
** (5) 由根田路径的宇宙限制

    正控制，以及直接路径的全部意义：在 [Endos] —— 其对象严格位于其函子之上 —— 一般类是可居住的，通用元素是 [O]，并且 Riehl 的元素范畴的初始对象存在。
*)

Check (nat_UniversalElement : UniversalElement Endos_Forget).
Check (@eq_refl nat (@ue_elem Endos Endos_Forget nat_UniversalElement)
         : @ue_elem Endos Endos_Forget nat_UniversalElement = O).
Check (nat_Elements_Initial : @Initial (Elements Endos_Forget)).

(**
Positive control on the donor side: [representability_by_yoneda] and
    [Yoneda_Lemma] do exist and do apply — at a category whose three
    universes coincide.

--------
供体侧的阳性对照：[representability_by_yoneda] 和 [Yoneda_Lemma] 确实存在并且适用 —— 在一个其三个宇宙重合的类别上。
*)

Check (fun (C : Category@{Set Set Set}) (F : C^op ⟶ Sets) (c : C) =>
         representability_by_yoneda C F c).

(**
Negative: neither can be instantiated at [Endos].  These are UNIVERSE
    INCONSISTENCIES, not unification failures.  Stripped, each reports
    that [Endos] (resp. [Endos^op]) "has type Category@{a b b} while it is
    expected to have type Category@{c c c}", followed by "universe
    inconsistency: Cannot enforce a = b" -- i.e. the donor's identification
    of the object and hom universes is exactly what is refused.  [@] is used
    throughout so that no implicit argument can make a command fail for an
    unrelated reason; the instrument itself was checked separately, and
    note that a naive exhibit such as [Fail Check (@eq_refl nat 0 : 0 = 0)]
    would NOT test it -- [0] is [initial_obj] in [object_scope], so that
    command fails with "No interpretation for number 0" and the [Fail]
    passes for the wrong reason.

--------
负面：在 [Endos] 上两者都无法实例化。这些是宇宙不一致，而不是统一失败。去掉后，它们各自报告 [Endos]（分别为 [Endos^op]）“具有类型 Category@{a b b}，而期望类型为 Category@{c c c}”，随后是“宇宙不一致：无法强制 a = b”——即捐赠者对对象和同态宇宙的标识正是被拒绝的。整个过程中使用了 [@]，以确保没有隐含参数会因无关原因导致命令失败；该工具本身也已单独检查，并注意到像 [Fail Check (@eq_refl nat 0 : 0 = 0)] 这样天真的示例无法测试它——[0] 是 [object_scope] 中的 [initial_obj]，因此该命令因“数字 0 无解释”而失败，而 [Fail] 因错误原因通过。
*)

Fail Check (fun c : Endos =>
              @universal_element_representation Endos Endos_Forget c).

Fail Check (fun c : Endos => @Yoneda_Lemma (Endos^op) Endos_Forget c).

(**
... and so the Yoneda-composed accessor cannot produce the witness that
    the direct one does.  (Stripped: the same universe inconsistency.)

--------
... 因此，Yoneda 组合的访问器无法生成直接访问器所产生的见证。（剥离后：相同的宇宙不一致性。）
*)

Fail Check (@universal_element_of_representation Endos Endos_Forget NatSucc
              (@represented Endos Endos_Forget nat_succ_Representable)).

(**
Positive control, immediately: the direct accessor DOES.  This is the
    pair that makes the restriction a measured fact about the two routes
    rather than a claim about one.

--------
正向控制，立即：直接访问器确实如此。这一对使得该限制成为关于两条路径的可测事实，而不是关于其中一条路径的主张。
*)

Check (@AUniversalElement_of_repr Endos Endos_Forget NatSucc
         (@represented Endos Endos_Forget nat_succ_Representable)
         : AUniversalElement Endos_Forget NatSucc).
