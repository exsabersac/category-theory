(**
* Boundary probes for the quotient setoid and the Sets coequalizer

    Companion to Instance/Sets/Quotient.v, Instance/Sets/Coequalizer.v,
    Instance/Sets/Quotient/Partition.v and
    Instance/Sets/Coequalizer/Interconnect.v (issue #315; Mac Lane §III.1
    construction 4 and §III.3 remark 2 / exercise 5, Awodey §3.4-§3.5,
    Fong and Spivak §1.2.1 and §6.2.4).  Those files make five negative
    claims -- one about which route to a representation is available at
    [Sets], two universe walls, and two conversion boundaries -- pinned
    below by six [Fail] commands (the first boundary costs two) against
    twelve positive controls.  A measurement made once and written into a
    header is not guarded by anything; these are.  **If the [Fail]
    commands below stop failing, this file breaks the build.**

    Each negative is paired with a positive control that must SUCCEED,
    for the reason Test/ProbeQuiverConstructions.v gives: a [Fail] alone
    passes just as happily when a name has been renamed out from under
    it.  The instrument itself was checked -- wrapping [Fail] around a
    succeeding command reports "The command has not failed!" and aborts
    compilation -- and each negative was compiled once with the [Fail]
    stripped, to confirm the error is the intended one.  What each of the
    six strips reported is recorded beside its probe.

    THE FIVE BOUNDARIES.

    (1) THE YONEDA ROUTE TO A REPRESENTATION IS NOT AVAILABLE AT [Sets].
    Theory/Universal/Element.v's [universal_element_yoneda] is stated
    over [Yoneda_Lemma], which identifies a category's object, hom and
    proof universes; [Sets@{o so} : Category@{so o o}] has its objects
    strictly above its homs, so no instantiation exists.  This is the
    same donor restriction Test/ProbeUniversalElement.v pins at
    Instance/Coq/Nat.v's [Endos] -- a DIFFERENT category, so the two
    probes are not duplicates -- and it is why
    Instance/Sets/Quotient.v's [sets_quot_Representable] goes through the
    Yoneda-free [ue_representation].  Two positive controls: that route
    at [Sets], and the Yoneda one at a category whose three universes can
    be identified.

    (2) THE UNTRUNCATED CLASS OBJECT IS NOT AN OBJECT OF THE SAME [Sets].
    Instance/Sets/Quotient/Partition.v takes the class of an element to
    be a [Prop]-valued predicate.  That is not a stylistic choice: since
    [obj[Sets@{o so}]] is [SetoidObject@{o o}], a [Type@{o}]-valued
    predicate on the carrier has type [Type@{o+1}] and does not fit.  The
    probe must PIN THE UNIVERSE INSTANCE, because without a binder Coq
    silently uses two different [Sets] and the claim evaporates -- the
    erratum CLAUDE.md records for [Check (Cat : obj[Cat])], met here
    again.  Two positive controls: the [Prop]-valued carrier at the very
    same level, and the [Type]-valued one a level up.

    (2') THE IMPREDICATIVE PHRASING OF THE GENERATED RELATION DOES NOT
    FIT EITHER.  Awodey's §3.5 exercise 4 defines the coequalizer's
    relation as the intersection of all equivalence relations containing
    the given pairs.  Instance/Sets/Coequalizer.v's header says that
    phrasing is unavailable at [Sets]' universe and generates the
    relation inductively instead; the probe measures the claim, against a
    positive control showing that the [Prop]-valued intersection DOES
    fit.

    (3) COARSENING IS NOT CONVERSION.  Instance/Sets/Quotient.v's
    [sets_quot_finest_eq] closes by [eq_refl]: quotienting by the
    setoid's own `≈` returns the [SetoidObject] record itself.  The
    over-read to guard against is that a quotient whose relation is
    PROVABLY equivalent to `≈` does the same.  It does not:
    Instance/Sets/Coequalizer.v's [coeq_rel_diagonal] shows that the
    coequalizer of a map with itself relates exactly the `≈`-related
    points, and the object is still not the one it started from.

    (4) A COEQUALIZER IDENTIFICATION IS A DERIVATION, NOT A COMPUTATION.
    Instance/Sets/Coequalizer/Interconnect.v's header says the carrier of
    the coequalizer is the ic_port type on the nose while `≈` moves.  Both
    halves are probed: [IcP0] and [IcP1] are distinct ports (the [Fail]) and
    identified in the coequalizer (the control), so the coarsening is
    real and the carrier really did not move.

--------
* 商等价类的边界探针与集合的等化器

Companion to Instance/Sets/Quotient.v, Instance/Sets/Coequalizer.v, Instance/Sets/Quotient/Partition.v 和 Instance/Sets/Coequalizer/Interconnect.v（问题 #315；Mac Lane §III.1 构造 4 和 §III.3 备注 2 / 习题 5，Awodey §3.4-§3.5，Fong 和 Spivak §1.2.1 和 §6.2.4）。这些文件提出了五个否定主张——一个关于在 [Sets] 可用的表示路径，两个宇宙壁，以及两个转换边界——由下面六个 [Fail] 命令固定（第一个边界花费两个）相对于十二个正向控制。一旦测量完成并写入头文件，就不会受到任何保护；这些是受保护的。**如果下面的 [Fail] 命令停止失败，这个文件将导致构建失败。**

每个阴性都配有一个必须成功的阳性对照，原因如 Test/ProbeQuiverConstructions.v 所示：单独的 [Fail] 即使在名称已被重命名的情况下，也能同样顺利通过。该工具本身已被检查——将 [Fail] 包裹在一个成功的命令上会报告“该命令未失败！”并中止编译——每个阴性还曾在剥离 [Fail] 的情况下编译一次，以确认错误是预期的。每个六个剥离报告的内容都记录在其探针旁边。

五大界限。

(1) 在 [Sets] 中无法使用 YONEDA 到表示的路径。Theory/Universal/Element.v 的 [universal_element_yoneda] 是在 [Yoneda_Lemma] 上声明的，它识别一个范畴的对象、hom 和证明宇宙；[Sets@{o so} : Category@{so o o}] 的对象严格位于其 hom 之上，因此不存在实例化。这与 Test/ProbeUniversalElement.v 在 Instance/Coq/Nat.v 的 [Endos] 上固定的供体限制相同——这是一个不同的范畴，因此这两个探针不是重复的——这也是 Instance/Sets/Quotient.v 的 [sets_quot_Representable] 通过 Yoneda-free [ue_representation] 的原因。两个阳性对照：[Sets] 上的该路径，以及一个其三个宇宙可以被识别的范畴上的 Yoneda 路径。

(2) 未截断的类对象不是相同 [Sets] 的对象。Instance/Sets/Quotient/Partition.v 将元素的类视为 [Prop] 值的谓词。这不是一种风格选择：由于 [obj[Sets@{o so}]] 是 [SetoidObject@{o o}]，载体上的 [Type@{o}] 值的谓词类型为 [Type@{o+1}] 并且不匹配。探针必须固定宇宙实例，因为没有绑定器时，Coq 会悄悄地使用两个不同的 [Sets]，导致声明消失——勘误表 CLAUDE.md 记录了 [Check (Cat : obj[Cat]] 在这里再次出现。两个正面控制：在同一级别上的 [Prop] 值载体，以及高一级别的 [Type] 值载体。

(2') 生成关系的非断言性表述也不适用。Awodey 的 §3.5 练习 4 将余等化子的关系定义为包含给定对的所有等价关系的交集。Instance/Sets/Coequalizer.v 的头部说明该表述在 [Sets] 宇宙中不可用，因此改为归纳地生成关系；探针用以衡量该主张，与显示 [Prop] 值交集确实适用的阳性对照进行比较。

(3) 粗化不是转换。Instance/Sets/Quotient.v 的 [sets_quot_finest_eq] 通过 [eq_refl] 结束：对集合的自身 `≈` 取商返回的是 [SetoidObject] 记录本身。需要防范的超读是：商的关系可证明等价于 `≈` 的情况也会产生相同结果。但事实并非如此：Instance/Sets/Coequalizer.v 的 [coeq_rel_diagonal] 显示，一个映射与自身的并合同样精确关联了 `≈` 相关的点，而对象仍然不是其最初的状态。

(4) 余等化器的识别是一种推导，而不是计算。Instance/Sets/Coequalizer/Interconnect.v 的头文件指出，余等化器的承载类型在本质上是 ic_port 类型，而 `≈` 会移动它们。两部分都被探测：[IcP0] 和 [IcP1] 是不同的端口（[Fail]），并且在余等化器（控制端）中被识别，因此粗化是真实的，并且承载确实没有移动。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Theory.Universal.Element.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Instance.Sets.Quotient.Partition.
Require Import Category.Instance.Sets.Coequalizer.
Require Import Category.Instance.Sets.Coequalizer.Interconnect.

Generalizable All Variables.

(** ** (1) The Yoneda route at [Sets] / ** (1) [Sets]上的Yoneda路线 *)

Section YonedaAtSets.

Context (H : Sets ⟶ Sets).
Context (r : Sets).
Context (U : AUniversalElement H r).

(**
Positive control: the Yoneda-FREE route builds the representation
    at [Sets], and [Instance/Sets/Quotient.v] uses exactly it.

--------
阳性对照：Yoneda-FREE 路径在 [Sets] 上构建表示，而 [Instance/Sets/Quotient.v] 完全使用它。
*)
Check (ue_representation H r U).
Check (AUniversalElement_of_repr H r).

(**
Negative: the Yoneda-based statement of the same correspondence is
    not formable here.  (With the [Fail] stripped, both of the two
    commands below report a universe inconsistency of the form "The term
    "H" has type "Sets@{a b} ⟶ Sets@{a b}" while it is expected to have
    type "?D ⟶ Sets@{c d}" (universe inconsistency: Cannot enforce
    b = d because b < d)" -- the strict inequality being exactly [Sets]'
    objects sitting above its homs.)

--------
负面：基于Yoneda的相同对应陈述在这里无法形成。（在去掉[Fail]后，下面的两个命令都会报告一种宇宙不一致性，形式为“项‘H’的类型是‘Sets@{a b} ⟶ Sets@{a b}’，但预期类型是‘?D ⟶ Sets@{c d}’（宇宙不一致性：无法强制 b = d，因为 b < d）”——严格不等式正是[Sets]对象位于其态射之上的原因。）
*)
Fail Check (universal_element_yoneda H r).

Fail Check (universal_element_representation H r).

End YonedaAtSets.

(**
Positive control for the instrument: at a category whose object, hom
    and proof universes ARE identified, the Yoneda statement elaborates.
    So the refusal above is a fact about [Sets], not about the
    constant.

--------
仪器的阳性对照：在其对象、同态和证明宇宙已被识别的类别中，Yoneda 语句会进行阐述。因此，上述拒绝是关于 [Sets] 的事实，而不是关于该常量的。
*)
Section YonedaSmall.

Universe u.

Context (D : Category@{u u u}).
Context (K : D ⟶ Sets).
Context (d : D).

Check (universal_element_yoneda K d).

End YonedaSmall.

(** ** (2) The untruncated class object / ** (2) 未截断的类对象 *)

(**
Positive control: the [Prop]-valued part-carrier, at a PINNED [Sets]
    universe instance.

--------
阳性对照：[Prop] 值的部分载体，在 PINNED [Sets] 宇宙实例中。
*)
Definition probe_parts_prop@{o} (A : SetoidObject@{o o}) : Type@{o} :=
  carrier A -> Prop.

(** Positive control: the [Type]-valued one exists a level up. / 阳性对照：[Type] 值的那个存在于上一级。 *)
Definition probe_parts_type_up@{o o'} (A : SetoidObject@{o o}) : Type@{o'} :=
  carrier A -> Type@{o}.

(**
Negative: it does not exist at the level of the carrier.  (With the
    [Fail] stripped this reports "The term "A → Type" has type
    "Type@{o+1}" while it is expected to have type "Type@{o}" (universe
    inconsistency: Cannot enforce o < o because o = o)" -- a genuine
    universe inconsistency naming the declared binder.)

--------
消极：它在承载层面上不存在。（在去掉 [Fail] 后，这报告了“术语 'A → Type' 的类型为 'Type@{o+1}'，而预期的类型为 'Type@{o}'（宇宙不一致：无法强制 o < o 因为 o = o）”——一种真正的宇宙不一致，指明了声明的绑定器。）
*)
Fail Definition probe_parts_type_same@{o} (A : SetoidObject@{o o}) : Type@{o} :=
  carrier A -> Type@{o}.

(**
... and the [Prop]-valued relation really is usable as a quotient's
    `≈` at a pinned instance, which is what [prop_rel_squash_stable]
    rests on.

--------
... 并且 [Prop] 值的关系确实可以作为固定实例上商的 `≈`，这正是 [prop_rel_squash_stable] 所依赖的。
*)
Definition probe_prop_quotient@{o so} (A : obj[Sets@{o so}])
  (Rp : carrier A -> carrier A -> Prop) (HRp : Equivalence Rp) :
  obj[Sets@{o so}] :=
  {| carrier := carrier A ;
     is_setoid := {| equiv := Rp ; setoid_equiv := HRp |} |}.

(**
... and the impredicative phrasing Awodey's §3.5 exercise 4 uses for
    the generated relation -- the intersection of all equivalence
    relations containing the given pairs -- does not fit either, for the
    same reason: quantifying over all [crelation]s on the carrier
    quantifies over a [Type@{o+1}].  (With the [Fail] stripped this
    reports "The term "∀ R : crelation A, Equivalence R → R a b" has type
    "Type@{o+1}" while it is expected to have type "Type@{o}" (universe
    inconsistency: Cannot enforce o < o because o = o)".)

--------
... 而 Awodey §3.5 练习 4 对生成的关系使用的不可谓词措辞——所有包含给定对的等价关系的交集——也不适用，原因相同：对承载对象上的所有 [crelation] 进行量化实际上是在对一个 [Type@{o+1}] 进行量化。（去掉 [Fail] 后会报告“术语 '∀ R : crelation A, Equivalence R → R a b' 的类型是 'Type@{o+1}'，而预期类型是 'Type@{o}'（范畴不一致：无法强制 o < o，因为 o = o）”。）
*)
Fail Definition probe_intersection_type@{o} (A : SetoidObject@{o o})
  (a b : carrier A) : Type@{o} :=
  forall R : crelation@{o o} (carrier A), Equivalence R -> R a b.

(**
Positive control: the [Prop]-valued intersection DOES fit, [Prop]
    being impredicative -- which is why Awodey's phrasing is available
    classically and the inductive generation is what replaces it here.

--------
阳性对照：[Prop] 值的交集确实适合，[Prop] 是不可递归的——这就是为什么 Awodey 的表述在经典情况下可用，而归纳生成则在这里取代了它。
*)
Definition probe_intersection_prop@{o} (A : SetoidObject@{o o})
  (a b : carrier A) : Prop :=
  forall R : carrier A -> carrier A -> Prop,
    (forall x, R x x) -> R a b.

(** ** (3) Coarsening is not conversion / ** (3) 粗化不是转换 *)

(**
Positive control: quotienting by the setoid's OWN `≈` returns the
    record, by [eq_refl].

--------
正控制：通过集合等价自身的 `≈` 求商会返回记录，由 [eq_refl] 提供。
*)
Definition probe_finest_eq (A : SetoidObject) :
  SetsQuotient A (@equiv _ A) (@setoid_equiv _ A) = A := eq_refl.

(**
Negative: the coequalizer of a map with itself relates exactly the
    `≈`-related points ([coeq_rel_diagonal]) and is still not the
    codomain.  (With the [Fail] stripped this reports "cannot unify
    "SetsCoeq bool_false_map bool_false_map" and "BoolSet"" -- the two
    relations are provably interderivable and the two records are not
    convertible.)

--------
负面：一个映射与自身的协等化子恰好关联 `≈` 相关的点（[coeq_rel_diagonal]），但仍然不是余域。（去掉 [Fail] 后，这会报告“无法统一 `SetsCoeq bool_false_map bool_false_map` 与 `BoolSet`”——这两个关系是可证地互相推导的，但这两个记录不可转换。）
*)
Fail Definition probe_diagonal_eq :
  SetsCoeq bool_false_map bool_false_map = BoolSet := eq_refl.

(**
... while the fact the header actually claims -- that the two
    relations agree -- is a theorem, in tree.

--------
……而标题实际上声称的事实——这两个关系一致——在树中是一个定理。
*)
Check (@coeq_rel_diagonal UnitSet BoolSet bool_false_map).

(** ** (4) Identification in a coequalizer is a derivation / ** (4) 在余等化器中的识别是一种推导 *)

(**
Positive controls: the carrier did not move, and the two ports ARE
    identified in the coequalizer.

--------
阳性对照：载体没有移动，并且两个端口在共等化器中被识别。
*)
Definition probe_interconnect_carrier : carrier Interconnect = ic_port := eq_refl.

Check port_P0_P1_merged.

(**
Negative: they are nevertheless distinct ports.  (With the [Fail]
    stripped this reports "cannot unify "IcP0" and "IcP1"".)

--------
否定：它们仍然是不同的端口。（在去掉 [Fail] 后，这份报告显示“无法统一‘IcP0’和‘IcP1’”。）
*)
Fail Definition probe_ports_eq : IcP0 = IcP1 := eq_refl.

(**
... and the coequalizer does not identify everything: this is the
    mapping-out argument, in tree.

--------
...且余等化子并未将一切都识别：这是映射出论证，在树中。
*)
Check port_P0_P3_apart.
