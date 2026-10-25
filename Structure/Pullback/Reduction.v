Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Regular.

Generalizable All Variables.

(* * * Interdefinability of the finite (co)limit constructions / * * 有限（共）极限构造的相互可定义性 *)

(*
 nLab:      https://ncatlab.org/nlab/show/finite+limit
 https://ncatlab.org/nlab/show/pullback
 https://ncatlab.org/nlab/show/equalizer
 Wikipedia: https://en.wikipedia.org/wiki/Limit_(category_theory)
 https://en.wikipedia.org/wiki/Pullback_(category_theory)

 Mac Lane, CWM 2nd ed., §III.3 Exercise 2 p. 71 (`maclane:III.3:ex2`)
 and §III.4 Exercises 7, 9 and 10 pp. 72-73 (`maclane:III.4:ex7`,
 `maclane:III.4:ex9`, `maclane:III.4:ex10`).  Awodey, *Category
 Theory*, 2nd ed., §5.2 Proposition 5.7 and Corollary 5.8
 (`awodey:5.2:prop7`, `awodey:5.2:cor8`), §5.4 Proposition 5.16
 (`awodey:5.4:prop16`), and the chapter exercises 3 and 5
 (`awodey:5:ex3`, `awodey:5:ex5`).  Riehl, *Category Theory in
 Context*, §3.5 Lemmas 3.5.15 and 3.5.16 (`riehl:3.5:lem15`,
 `riehl:3.5:lem16`).

 ------------------------------------------------------------------
 ** What the reductions are, and why anyone cares

 A category has all FINITE limits as soon as it has a small handful of
 them, and there is more than one handful that works.  The two standard
 generating sets are

 (i)  a terminal object, binary products, and equalizers; and
 (ii) a terminal object and pullbacks,

 and the content of the classical results collected here is that each
 generates the other.  The practical payoff is that a construction one
 wants to perform in an arbitrary finitely complete category can be
 carried out with whichever presentation is cheapest to verify in the
 case at hand: pullbacks are what a fibration or a subobject lattice
 hands you directly, while products and equalizers are what an
 algebraic category hands you directly.

 The arguments are old and are usually left as exercises.  Mac Lane
 states three of them that way -- his Exercise 7 builds the pullback of
 f and g as the equalizer of f ∘ exl and g ∘ exr on x × y, his Exercise
 9 recovers an equalizer from a pullback, and his Exercise 10 obtains
 binary products as pullbacks over a terminal object.  Awodey works the
 same ground with proofs: his Proposition 5.7 is Mac Lane's Exercise 7
 with its converse, his Corollary 5.8 is the packaged "products and
 equalizers give pullbacks", and his Proposition 5.16 is the pullbacks
 half.  Riehl's Lemma 3.5.15 is the general statement that limits of
 arbitrary finite shape are generated, of which the binary case is
 proved here.

 Everything below is stated FIRST at the apex-pinned predicate level --
 [IsPullback] of Theory/Morphisms/Stability.v, [IsEqualizer] of
 Structure/Equalizer/Fork.v, [IsCoequalizer] of
 Structure/Coequalizer.v, [IsCartesianProduct] of
 Structure/Cartesian.v -- because those are the forms that can be
 applied to a square one already has.  The bundled classes
 ([HasPullbacks], [HasEqualizers], [Cartesian], [HasPushouts]) are
 packaged afterwards, and nothing here is declared an [Instance]:
 several of these reductions run in opposite directions, so registering
 them for resolution would loop.

 ------------------------------------------------------------------
 ** (D) Mac Lane's Exercise 9 and Awodey's Exercise 3 are NOT the same
 square, and this file proves it rather than asserting it

 It is tempting -- and the issue that prompted this file does it -- to
 describe the two "pullbacks give equalizers" constructions as one
 square read two ways.  They are not.

 - Mac Lane pulls back ⟨id, f⟩ and ⟨id, g⟩, two morphisms out of the
 SAME object x, over x × y.
 - Awodey and Riehl pull back the diagonal ⟨id, id⟩ : y ~> y × y
 along ⟨f, g⟩ : x ~> y × y, two morphisms out of DIFFERENT objects,
 over y × y.

 Three separate measurements say these differ, and all three are
 recorded as probes at the end of the file:

 1. The cospans do not share a codomain.  [x × y = y × y] is well
 typed and refused by [eq_refl] -- a CONVERSION negative.
 2, 3. The legs are not parallel.  [ml_left] inhabits [x ~> x × y]
 while [aw_pair] inhabits [x ~> y × y], so the equation between
 them cannot even be stated -- FORMABILITY negatives, and a
 different kind of failure from 1.

 Those are facts about how the two are written.  The difference is also
 structural, and that is the part worth keeping: BOTH of Mac Lane's
 legs are split monic, with one common retraction ([ml_left_split],
 [ml_right_split], each [exl ∘ - ≈ id]), whereas on Awodey's side only
 the diagonal is ([aw_diag_split]); the other leg retracts along [exl]
 to f itself ([aw_pair_retracts_to_f]), which is not an identity in
 general.  Read that at the strength it has: it exhibits a property one
 cospan has and the other lacks for general f, and it is NOT a proof
 that no isomorphism of cospans exists at particular f and g.  No such
 theorem is proved here and none is claimed.

 What IS true, and is proved, is the weaker and more useful statement:
 the two vertices are canonically isomorphic, because both are
 equalizers of the same parallel pair ([maclane_awodey_iso], through
 [equalizer_unique]), and the comparison commutes with both equalizing
 maps ([maclane_awodey_iso_commutes]) -- so it is an isomorphism of
 equalizers and not merely of objects.

 There is one genuine coincidence, and it is degenerate.  At f := id
 (hence y := x) Mac Lane's cospan and Awodey's consist of the very same
 two morphisms with the two legs interchanged, and that holds
 DEFINITIONALLY: [maclane_awodey_degenerate_left] and
 [maclane_awodey_degenerate_right] are both [eq_refl].  No converse is
 proved -- it is not shown that f = id is the only case.

 ------------------------------------------------------------------
 ** (F) The duality is NOT definitional, and the one step that costs
 something is named

 [Cocartesian C] is notation for [@Cartesian (C^op)] and
 [IsPushout f g] unfolds to a [Pullback] in [C^op], so one might expect
 the pushout half to fall out of the pullback half by instantiation
 alone.  It very nearly does, and the residue was measured rather than
 assumed.

 REFUTED: [HasCoequalizers C = HasEqualizers (C^op)] is refused by
 [eq_refl], and so is the predicate-level
 [IsCoequalizer f g q e = @IsEqualizer (C^op) y x f g q e] (negatives 6
 and 7, both CONVERSION failures).  [IsCoequalizer] and [IsEqualizer]
 are separately declared records, and Coq's record types are nominal:
 no amount of agreement between their fields makes them one type.

 CONFIRMED: every field type IS convertible.  [cofork]'s
 [e ∘ f ≈ e ∘ g] is accepted where [fork_eq]'s
 [f ∘[C^op] e ≈ g ∘[C^op] e] is expected, on the nose
 ([pos_cofork_is_fork_eq]), and likewise for the descent fields.  So
 both bridges -- [IsEqualizer_op_of_IsCoequalizer] and
 [IsCoequalizer_of_IsEqualizer_op] -- are supplied by [:=] with NO
 tactic and NO obligation, and BOTH round trips close by [eq_refl] on
 the whole record, record eta doing the work
 ([IsCoequalizer_op_round], [IsEqualizer_op_round]).

 So the honest accounting is: the duality is free except for TWO
 repackaging steps, [HasEqualizers_op_of_HasCoequalizers] and its
 mirror [HasCoequalizers_of_HasEqualizers_op], each of which destructs
 the existential and rebuilds it through the corresponding bridge.  (An
 earlier draft of this paragraph said "one", counting only the first
 and overlooking the second, which sits in the same section.)
 Everything on either side of them is instantiation.  In particular the
 coproduct vocabulary needs no translation at all --
 [Coprod_is_op_product], [inl_is_op_exl] and [inr_is_op_exr] are
 [eq_refl] -- so (A) is applied at [C^op] verbatim, and
 Structure/Pushout.v's own [HasPushouts_of_HasPullbacks_op] closes the
 loop.  The covariant reading is delivered too:
 [IsPushout_of_coequalizer] lands in Structure/Pushout.v's own
 [IsPushout], and its apex and both injections COMPUTE, by [eq_refl].

 ------------------------------------------------------------------
 ** Strength measurements

 Measured strict-first throughout; [eq_refl] was attempted before any
 [≈] was accepted.

 Closing by [eq_refl]:
 - [kernel_pair_is_pullback_along_itself]: Structure/Regular.v's
 [kernel_pair f] IS [pullback f f], so section (C) is about that
 constant and not a parallel notion of its own;
 - the two degenerate Mac Lane/Awodey coincidences at f := id;
 - both [IsCoequalizer]/[IsEqualizer (C^op)] record round trips;
 - the three coproduct-is-op-product readings;
 - the apex and both injections of [IsPushout_of_coequalizer].

 Holding only up to [≈], with the strict form REFUTED and probed:
 - [equalizer_pullback_round]: pairing the two projections that (A)
 extracts recovers the original equalizing map, but by
 [fork_exl_exr], which is a [≈]-law and not a conversion
 (negative 4);
 - [pullback_equalizer_round_fst]/[_snd]: projecting out of the
 pairing that (B) forms recovers the original projections, by
 [exl_fork]/[exr_fork] -- again [≈] only (negative 5).

 A note on (B), since it departs from the textbook: Awodey derives the
 uniqueness half of Proposition 5.7's converse from the fact that an
 equalizer is monic.  Structure/Equalizer/Fork.v has that lemma
 ([equalizer_monic]) and it was read, but it is NOT used here.  Any
 competing factorization through the pairing ⟨p1, p2⟩ projects to a
 competing factorization through p1 and p2 separately, so the PULLBACK's
 own uniqueness clause discharges the goal directly, and routing through
 monicity would be a longer path to the same place.

 ------------------------------------------------------------------
 ** What this file does NOT do

 Scoped to this file; none of these is a claim about the tree.

 - It does not treat WIDE pullbacks or wide equalizers, in any
 direction; those live elsewhere.
 - It does not conclude [Complete] or [Cocomplete], and does not
 state Riehl's Lemma 3.5.15 for limits of arbitrary finite shape.
 Only the binary/parallel-pair generators are related; assembling
 them into a completeness statement would need the finite-shape
 induction, which is not performed.
 - It does not derive a [Terminal] object from anything, so (E)'s
 hypotheses are not shown minimal, and no converse to (E) is given.
 - It does not compare the [Cartesian] structure that (E) produces
 with any pre-existing [Cartesian] structure on the same category;
 in particular no coherence or canonicity is claimed for it, and
 the two need not be the same instance.
 - It packages none of the [≈]-round-trips as an isomorphism of
 structures.
 - It declares no [Instance] and registers nothing for typeclass
 resolution.
 - It makes no universe claim of any kind. 

 --------
 nLab:       https://ncatlab.org/nlab/show/finite+limit 
 https://ncatlab.org/nlab/show/pullback 
 https://ncatlab.org/nlab/show/equalizer 
 Wikipedia:  https://en.wikipedia.org/wiki/Limit_(category_theory) 
 https://en.wikipedia.org/wiki/Pullback_(category_theory) 

 Mac Lane, 《CWM》第二版, §III.3 练习 2 第71页 ( `maclane:III.3:ex2` )
 和 §III.4 练习 7、9 和 10 第72-73页 ( `maclane:III.4:ex7` , `maclane:III.4:ex9` , `maclane:III.4:ex10` )。 Awodey, 《范畴理论》, 第二版, §5.2 命题 5.7 和 推论 5.8 ( `awodey:5.2:prop7` , `awodey:5.2:cor8` ), §5.4 命题 5.16 ( `awodey:5.4:prop16` ), 以及章末练习 3 和 5 ( `awodey:5:ex3` , `awodey:5:ex5` )。 Riehl, 《情境中的范畴理论》, §3.5 引理 3.5.15 和 3.5.16 ( `riehl:3.5:lem15` , `riehl:3.5:lem16` )。

 ------------------------------------------------------------------
 ** 这些约简是什么，以及为什么有人关心一旦一个范畴拥有少量的有限极限，它就拥有所有的有限极限，而且有不止一套可行的少量集合。两个标准的生成集合是

 (i) 一个终对象、二元积和等化子；以及
 (ii) 一个终对象和拉回。

 这里收集的经典结果的内容是，每一套都可以生成另一套。实际的意义在于，在任意有限完备的范畴中，想要执行的构造可以使用在具体情况下验证起来最便宜的呈现来完成：拉回是纤维化或子对象格直接提供的，而积和等化子是代数范畴直接提供的。这些论证很老，通常作为练习题留给读者。Mac Lane以这样的方式陈述了其中三个——他的练习7通过f ∘ exl和g ∘ exr在x × y上的等化器构建了f和g的拉回，他的练习9从拉回中恢复了一个等化器，他的练习10通过终对象上的拉回获得二元积。Awodey用证明处理了同样的内容：他的命题5.7是Mac Lane的练习7及其逆命题，他的推论5.8是封装好的“积与等化器给出拉回”，而他的命题5.16是拉回部分。Riehl的引理3.5.15是关于任意有限形状极限可以生成的一般性陈述，其中二元情况在这里得到了证明。下面的所有内容首先在顶点固定的谓词层面上说明 --
 [IsPullback] 来自 Theory/Morphisms/Stability.v，[IsEqualizer] 来自
 Structure/Equalizer/Fork.v，[IsCoequalizer] 来自
 Structure/Coequalizer.v，[IsCartesianProduct] 来自
 Structure/Cartesian.v -- 因为这些形式可以应用于已有的方格。打包的类
 ([HasPullbacks], [HasEqualizers], [Cartesian], [HasPushouts]) 随后打包，而这里没有声明任何 [Instance]：
 其中一些归约方向相反，所以注册它们以供解析会导致循环。

 ------------------------------------------------------------------
 ** (D) Mac Lane 的练习 9 和 Awodey 的练习 3 不是同一个方格，
 这个文件是证明它，而不是简单断言它很容易让人产生这样的想法——正是促使创建这个文件的问题所在——将两种“拉回给等化器”的构造描述为一个可以两种方式解读的方形。但它们并非如此。

 - Mac Lane 对 ⟨id, f⟩ 和 ⟨id, g⟩ 进行拉回，这是从同一个对象 x 出发的两个态射，作用在 x × y 上。
 - Awodey 和 Riehl 沿着 ⟨f, g⟩ : x → y × y 对对角线 ⟨id, id⟩ : y → y × y 进行拉回，这是从不同对象出的两个态射，作用在 y × y 上。

 三个独立的测量表明它们确实不同，这三次测量都作为探针记录在文件末尾：1. 共Span不共享同一个余域。[x × y = y × y] 类型正确，但被 [eq_refl] 拒绝 —— 是一个转换（CONVERSION）否定。
 2, 3. 这些边不平行。[ml_left] 属于 [x ~> x × y]，而 [aw_pair] 属于 [x ~> y × y]，所以它们之间的等式甚至无法表述 —— 形成性（FORMABILITY）否定，并且这种失败不同于第1种。这些是关于两者写法的事实。不同之处也是结构性的，这部分是值得保留的：Mac Lane 的两条腿都是分裂单态，每条都有一个共同的回退（[ml_left_split]、[ml_right_split]，每个 [exl ∘ - ≈ id]），而在 Awodey 的方面，只有对角线是（[aw_diag_split]）；另一条腿沿着 [exl] 回退到 f 本身（[aw_pair_retracts_to_f]），这通常不是一个恒等式。以它的原貌来理解：它展示了一个余楔的一条腿具有而另一条缺乏的性质，对一般的 f 成立，这并不是证明在特定的 f 和 g 下余楔没有同构。这里没有证明这样的定理，也没有声称这样做。真正成立并已被证明的是较弱且更有用的陈述：两个顶点在范畴上是典型同构的，因为它们都是相同平行对的等化器（[maclane_awodey_iso]，通过[equalizer_unique]），并且比较映射与两个等化映射都可交换（[maclane_awodey_iso_commutes]）——因此它是等化器之间的同构，而不仅仅是对象之间的同构。

 确实存在一次真正的巧合，但它是退化的。在 f := id（因此 y := x）时，Mac Lane 的共跨和 Awodey 的共跨由完全相同的两个态射构成，只是两条腿被互换，并且这在定义上成立：[maclane_awodey_degenerate_left] 和 [maclane_awodey_degenerate_right] 都是 [eq_refl]。没有证明逆命题——没有显示 f = id 是唯一的情况。------------------------------------------------------------------
 **（F）这种对偶性不是定义性的，而唯一一个有代价的步骤被命名

 [Cocartesian C] 是 [@Cartesian (C^op)] 的记法，而
 [IsPushout f g] 会展开为 [C^op] 中的 [Pullback]，因此人们可能会期望
 推出的一半可以仅凭实例化从拉回的一半得出。 它几乎可以做到，而残余部分是通过测量而非假设得出的。

 驳斥：[HasCoequalizers C = HasEqualizers (C^op)] 被 [eq_refl] 拒绝，
 谓词层面上的 [IsCoequalizer f g q e = @IsEqualizer (C^op) y x f g q e] 也是如此（负例 6 和 7，都是转换失败）。 [IsCoequalizer] 和 [IsEqualizer] 
 被分别声明为记录，且 Coq 的记录类型是名义类型：
 即使它们的字段完全一致，也不能将它们视为同一类型。已确认：每种字段类型都是可转换的。[cofork] 的 [e ∘ f ≈ e ∘ g] 在预期出现 [fork_eq] 的 [f ∘[C^op] e ≈ g ∘ [C^op] e 时，完全被接受（[pos_cofork_is_fork_eq]），降序字段也是如此。因此，两个桥——[IsEqualizer_op_of_IsCoequalizer] 和 [IsCoequalizer_of_IsEqualizer_op]——都是由 [:=] 提供的，无需任何策略，也无任何义务，并且两个来回都通过 [eq_refl] 在整个记录上完成，由记录 eta 完成工作（[IsCoequalizer_op_round]，[IsEqualizer_op_round]）。所以，坦率的说明是：二重性是免费的，除了两个重新打包步骤，[HasEqualizers_op_of_HasCoequalizers] 及其镜像 [HasCoequalizers_of_HasEqualizers_op]，每个步骤都会破坏存在性并通过相应的桥梁重新构建它。（该段落的早期草稿写的是“一个”，只计算了第一个步骤而忽略了同一部分中的第二个步骤。）它们两侧的所有内容都是实例化的。特别是，余积词汇根本不需要翻译——[Coprod_is_op_product]、[inl_is_op_exl] 和 [inr_is_op_exr] 是 [eq_refl] ——因此 (A) 在 [C^op] 逐字应用，而 Structure/Pushout.v 自身的 [HasPushouts_of_HasPullbacks_op] 关闭了循环。协变读法也被实现：[IsPushout_of_coequalizer] 落在 Structure/Pushout.v 自身的 [IsPushout] 中，并且它的顶点和两个注入通过 [eq_refl] 计算。------------------------------------------------------------------
 ** 强度测量

 测量严格按顺序进行；在接受任何 [≈] 之前尝试了 [eq_refl]。

 由 [eq_refl] 关闭：
 - [kernel_pair_is_pullback_along_itself] ：Structure/Regular.v 文件
 [kernel_pair f] 是 [pullback f f]，因此第 (C) 部分是关于该常量，而不是它自身的平行概念；
 - 在 f := id 时的两个退化 Mac Lane/Awodey 巧合；
 - [IsCoequalizer] / [IsEqualizer (C^op)] 都记录了往返过程；
 - 三种 coproduct-is-op-product 读法；
 - [IsPushout_of_coequalizer] 的顶点和两个注入。仅保持到 [≈]，使用严格形式 REFUTED 并进行探测：
 - [equalizer_pullback_round]：将 (A) 提取的两个投影配对可以恢复原始均衡映射，但通过 [fork_exl_exr]，这是一条 [≈] 定律，而不是转换（负 4）；
 - [pullback_equalizer_round_fst] / [_snd]：从 (B) 形成的配对中投影出来可以恢复原始投影，通过 [exl_fork] / [exr_fork] —— 再次只有 [≈]（负 5）。关于 (B) 的说明，由于它偏离了教材：Awodey 利用等化子是单射这一事实推导了命题 5.7 的逆命题的唯一性部分。Structure/Equalizer/Fork.v 中有该引理（[equalizer_monic]）并已被阅读，但在此并未使用。通过配对 ⟨p1, p2⟩ 的任何竞争分解都会分别投射为通过 p1 和 p2 的竞争分解，因此 PULLBACK 自身的唯一性条款可以直接解决目标，而通过单射性来处理将是通向同一结果的更长路径。

 ------------------------------------------------------------------
 ** 本文件不做的事情

 仅限于本文件；这些都不是关于树的声明。- 它不处理任何方向的宽拉回或宽等化器；这些内容在其他地方。- 它不推导 [Complete] 或 [Cocomplete]，也不陈述 Riehl 关于任意有限形状极限的引理 3.5.15。只有二元/并行对生成器相关；将它们组装成一个完备性声明需要有限形状归纳，而这并未执行。- 它没有从任何东西推导出 [Terminal] 对象，因此 (E) 的假设没有被显示为最小，也没有给出 (E) 的逆定理。- 它没有将 (E) 生成的 [Cartesian] 结构与同一范畴上任何已有的 [Cartesian] 结构进行比较；特别是，没有声称其具有相干性或规范性，而且这两个结构不必是同一实例。- 它没有将任何 [≈] 循环往返打包为结构的同构。
 - 它没有声明任何 [Instance]，也没有为类型类解析注册任何内容。
 - 它没有做出任何类型的宇宙声明。
*)

(* ====================================================================== *)
(* * * (A) Cartesian + equalizers give pullbacks / * *（A）笛卡尔范畴 + 等化器 给出拉回 *)

Section PullbackFromEqualizer.

Context {C : Category}.
Context `{@Cartesian C}.

(*
 maclane:III.4:ex7, forward; awodey:5.2:prop7, forward.  The two legs
 of the cospan are shifted onto the product and their equalizer taken:
 an element of x × y equalizing f ∘ exl and g ∘ exr is exactly a pair
 whose two components agree over z.  The projections of the resulting
 pullback square are the two components of the equalizing map. 

 --------
 maclane:III.4:例7, 正向; awodey:5.2:命题7, 正向。余跨的两个腿被转移到积上并取它们的等化器：x × y 中的一个元素使 f ∘ exl 和 g ∘ exr 等化，正好是一个它的两个分量在 z 上一致的对。由此得到的拉回方形的投影是等化映射的两个分量。
*)
Lemma pullback_of_equalizer {x y z : C} (f : x ~> z) (g : y ~> z)
      {E : C} {e : E ~> x × y}
      (Eq : IsEqualizer (f ∘ exl) (g ∘ exr) E e) :
  IsPullback f g E (exl ∘ e) (exr ∘ e).
Proof.
  constructor.
  - rewrite !comp_assoc.
    exact (fork_eq Eq).
  - intros Q q1 q2 Hq.
    assert (Hh : (f ∘ exl) ∘ (q1 △ q2) ≈ (g ∘ exr) ∘ (q1 △ q2)).
    { rewrite <- !comp_assoc, exl_fork, exr_fork.
      exact Hq. }
    destruct (eq_desc Eq (q1 △ q2) Hh) as [u Hu Huniq].
    unshelve eapply Build_Unique.
    + exact u.
    + split.
      * rewrite <- comp_assoc, Hu.
        apply exl_fork.
      * rewrite <- comp_assoc, Hu.
        apply exr_fork.
    + intros v [Hv1 Hv2].
      apply Huniq.
      apply ump_products; split.
      * rewrite comp_assoc.
        exact Hv1.
      * rewrite comp_assoc.
        exact Hv2.
Qed.

End PullbackFromEqualizer.

Definition HasPullbacks_of_Cartesian_HasEqualizers {C : Category}
           `{@Cartesian C} (E : @HasEqualizers C) : @HasPullbacks C.
Proof.
  constructor.
  intros x y z f g.
  destruct (@equalizer C E (x × y)%object z (f ∘ exl) (g ∘ exr))
    as [q [e Eq]].
  exact (is_pullback_pullback (pullback_of_equalizer f g Eq)).
Defined.

(* ====================================================================== *)
(* * * (B) The converse: a pullback square is an equalizer / * * (B) 逆命题：拉回方格是一个等化器 *)

Section EqualizerFromPullback.

Context {C : Category}.
Context `{@Cartesian C}.

Lemma equalizer_of_pullback {x y z : C} {f : x ~> z} {g : y ~> z}
      {P : C} {p1 : P ~> x} {p2 : P ~> y}
      (HP : IsPullback f g P p1 p2) :
  IsEqualizer (f ∘ exl) (g ∘ exr) P (p1 △ p2).
Proof.
  constructor.
  - rewrite <- !comp_assoc, exl_fork, exr_fork.
    exact (is_pullback_commutes HP).
  - intros Q h Hh.
    assert (Hq : f ∘ (exl ∘ h) ≈ g ∘ (exr ∘ h)).
    { rewrite !comp_assoc.
      exact Hh. }
    destruct (is_pullback_ump HP Q (exl ∘ h) (exr ∘ h) Hq)
      as [u [Hu1 Hu2] Huniq].
    unshelve eapply Build_Unique.
    + exact u.
    + rewrite <- fork_comp.
      symmetry.
      apply ump_products; split.
      * symmetry; exact Hu1.
      * symmetry; exact Hu2.
    + intros v Hv.
      apply Huniq; split.
      * rewrite <- Hv.
        now rewrite exl_fork_comp.
      * rewrite <- Hv.
        now rewrite exr_fork_comp.
Qed.

(* * ** The two passages round-trip, up to [≈] but not on the nose / * ** 这两个段落可以往返传输，直到 [≈]，但不是完全精确 *)

(*
 Starting from an equalizer [e : E ~> x × y] of the shifted pair, (A)
 produces the projections exl ∘ e and exr ∘ e, and (B) pairs them back
 up.  The result is [e] again -- but only up to [≈]: [fork_exl_exr] is a
 [≈]-law, not a conversion, so the strict form is refuted (see the
 probes at the end of the file). 

 --------
 从移位对的等化器 [e : E ~> x × y] 开始，(A) 产生投影 exl ∘ e 和 exr ∘ e，(B) 再将它们配对回去。结果再次是 [e] —— 但仅到 [≈] 为止：[fork_exl_exr] 是一个 [≈]-律，而不是一个转换，因此严格形式被驳斥（见文件末尾的探针）。
*)
Lemma equalizer_pullback_round {x y : C} (E : C) (e : E ~> x × y) :
  (exl ∘ e) △ (exr ∘ e) ≈ e.
Proof.
  now rewrite fork_comp, fork_exl_exr, id_left.
Qed.

(*
 The other composite, on each projection separately; this is exactly
 [exl_fork]/[exr_fork], i.e. again a [≈]-law and not a conversion. 

 --------
 另一个复合体，在每个投影上分别处理；这正是 [exl_fork] / [exr_fork]，即再次是一个 [≈] 定律，而不是转换。
*)
Lemma pullback_equalizer_round_fst {x y : C} {P : C}
      (p1 : P ~> x) (p2 : P ~> y) : exl ∘ (p1 △ p2) ≈ p1.
Proof. apply exl_fork. Qed.

Lemma pullback_equalizer_round_snd {x y : C} {P : C}
      (p1 : P ~> x) (p2 : P ~> y) : exr ∘ (p1 △ p2) ≈ p2.
Proof. apply exr_fork. Qed.

End EqualizerFromPullback.

(* ====================================================================== *)
(* * * (C) The kernel pair as an equalizer / * * (C) 核对偶作为等化器 *)

Section KernelPair.

Context {C : Category}.
Context `{@Cartesian C}.

(*
 maclane:III.4:ex7, second clause.  The kernel pair of f is the
 pullback of f along ITSELF, so this is (B) read at g := f and carries
 no new proof content -- the whole statement is [equalizer_of_pullback]
 instantiated, and it is written that way rather than reproved. 

 --------
 maclane:III.4:ex7，第二条款。f 的核对是 f 自身的拉回，所以这就是在 g := f 时阅读的 (B)，并且不包含新的证明内容——整个陈述是 [equalizer_of_pullback] 的实例化，并且写成那样而不是重新证明。
*)
Lemma kernel_pair_of_IsPullback {x y : C} {f : x ~> y}
      {P : C} {p1 p2 : P ~> x} (HP : IsPullback f f P p1 p2) :
  IsEqualizer (f ∘ exl) (f ∘ exr) P (p1 △ p2).
Proof. exact (equalizer_of_pullback HP). Qed.

(*
 The tie to the tree's existing notion.  Structure/Regular.v already
 defines [kernel_pair f := pullback f f] under [HasPullbacks], and the
 statements below are about THAT constant -- no parallel notion of a
 kernel pair is introduced here.  The identification is definitional
 ([kernel_pair_is_pullback_along_itself], by [eq_refl]). 

 --------
 与树的现有概念的联系。Structure/Regular.v 已经在 [HasPullbacks] 下定义了 [kernel_pair f := pullback f f]，下面的语句关于的是那个常数——这里没有引入核对的平行概念。这个标识是定义性的（由 [eq_refl] 定义的 [kernel_pair_is_pullback_along_itself]）。
*)
Context `{HPB : @HasPullbacks C}.

Definition kernel_pair_fst {x y : C} (f : x ~> y) :
  Pull f f (kernel_pair f) ~> x := pullback_fst f f (kernel_pair f).

Definition kernel_pair_snd {x y : C} (f : x ~> y) :
  Pull f f (kernel_pair f) ~> x := pullback_snd f f (kernel_pair f).

Lemma kernel_pair_IsEqualizer {x y : C} (f : x ~> y) :
  IsEqualizer (f ∘ exl) (f ∘ exr) (Pull f f (kernel_pair f))
              (kernel_pair_fst f △ kernel_pair_snd f).
Proof.
  exact (kernel_pair_of_IsPullback
           (pullback_is_pullback f f (kernel_pair f))).
Qed.

Example kernel_pair_is_pullback_along_itself {x y : C} (f : x ~> y) :
  kernel_pair f = pullback f f := eq_refl.

End KernelPair.

(* ====================================================================== *)
(* * * (D) Pullbacks give equalizers: two genuinely different squares / * * (D) 拉回给出等化器：两个真正不同的方形 *)

Section EqualizerFromPullbackSquares.

Context {C : Category}.
Context `{@Cartesian C}.
Context {x y : C}.
Context (f g : x ~> y).

(* * ** Mac Lane's square (maclane:III.4:ex9) / * ** 麦克莱恩的平方 (maclane:III.4:ex9) *)

Definition ml_left  : x ~> x × y := id △ f.
Definition ml_right : x ~> x × y := id △ g.

Lemma ml_projections_agree {E : C} {p1 p2 : E ~> x}
      (HP : IsPullback ml_left ml_right E p1 p2) : p1 ≈ p2.
Proof.
  pose proof (is_pullback_commutes HP) as Hc.
  assert (Hl : exl ∘ (ml_left ∘ p1) ≈ exl ∘ (ml_right ∘ p2))
    by now rewrite Hc.
  unfold ml_left, ml_right in Hl.
  rewrite !comp_assoc, !exl_fork, !id_left in Hl.
  exact Hl.
Qed.

Lemma equalizer_of_pullback_maclane {E : C} {p1 p2 : E ~> x}
      (HP : IsPullback ml_left ml_right E p1 p2) :
  IsEqualizer f g E p1.
Proof.
  pose proof (is_pullback_commutes HP) as Hc.
  pose proof (ml_projections_agree HP) as Hp.
  assert (Hr : f ∘ p1 ≈ g ∘ p2).
  { assert (Hr' : exr ∘ (ml_left ∘ p1) ≈ exr ∘ (ml_right ∘ p2))
      by now rewrite Hc.
    unfold ml_left, ml_right in Hr'.
    rewrite !comp_assoc, !exr_fork in Hr'.
    exact Hr'. }
  constructor.
  - rewrite Hr.
    now rewrite Hp.
  - intros Q h Hh.
    assert (Hcomm : ml_left ∘ h ≈ ml_right ∘ h).
    { unfold ml_left, ml_right.
      rewrite <- !fork_comp, !id_left.
      now rewrite Hh. }
    destruct (is_pullback_ump HP Q h h Hcomm) as [u [Hu1 Hu2] Huniq].
    unshelve eapply Build_Unique.
    + exact u.
    + exact Hu1.
    + intros v Hv.
      apply Huniq; split.
      * exact Hv.
      * now rewrite <- Hp.
Qed.

(* * ** Awodey's and Riehl's square (awodey:5:ex3, riehl:3.5:lem16) / * ** Awodey 和 Riehl 的方形 (awodey:5:ex3, riehl:3.5:lem16) *)

Definition aw_diag : y ~> y × y := id △ id.
Definition aw_pair : x ~> y × y := f △ g.

Lemma equalizer_of_pullback_awodey {E : C} {p1 : E ~> x} {p2 : E ~> y}
      (HP : IsPullback aw_pair aw_diag E p1 p2) :
  IsEqualizer f g E p1.
Proof.
  pose proof (is_pullback_commutes HP) as Hc.
  assert (Hl : f ∘ p1 ≈ p2).
  { assert (H' : exl ∘ (aw_pair ∘ p1) ≈ exl ∘ (aw_diag ∘ p2))
      by now rewrite Hc.
    unfold aw_pair, aw_diag in H'.
    rewrite !comp_assoc, !exl_fork, id_left in H'.
    exact H'. }
  assert (Hr : g ∘ p1 ≈ p2).
  { assert (H' : exr ∘ (aw_pair ∘ p1) ≈ exr ∘ (aw_diag ∘ p2))
      by now rewrite Hc.
    unfold aw_pair, aw_diag in H'.
    rewrite !comp_assoc, !exr_fork, id_left in H'.
    exact H'. }
  constructor.
  - now rewrite Hl, Hr.
  - intros Q h Hh.
    assert (Hcomm : aw_pair ∘ h ≈ aw_diag ∘ (f ∘ h)).
    { unfold aw_pair, aw_diag.
      rewrite <- !fork_comp, !id_left.
      now rewrite Hh. }
    destruct (is_pullback_ump HP Q h (f ∘ h) Hcomm) as [u [Hu1 Hu2] Huniq].
    unshelve eapply Build_Unique.
    + exact u.
    + exact Hu1.
    + intros v Hv.
      apply Huniq; split.
      * exact Hv.
      * rewrite <- Hl, <- comp_assoc.
        now rewrite Hv.
Qed.

(*
   * ** Comparing the two squares

   The two cospans are not the same square.  They do not share a
   codomain (x × y against y × y), and their legs are not even parallel:
   Mac Lane's two legs both issue from x, Awodey's from x and from y.
   Those are refuted at the end of the file, the leg comparisons being
   FORMABILITY negatives (ill-typed when x and y differ) rather than
   conversion negatives.

   The difference is not merely syntactic, and the FOUR lemmas below
   bear on it: BOTH of Mac Lane's legs are split monic, with the single
   common retraction exl, whereas [exl ∘ aw_pair] is f, which is not an
   identity FOR GENERAL f.  Read that hedge strictly.  It does NOT say
   Awodey's leg is never split -- at f := id it is, by [ml_right_split]
   -- and an earlier draft of this comment concluded "so no relabelling
   of objects can turn one cospan into the other", which is REFUTED by
   this file's own [maclane_awodey_degenerate_left]/[_right], where at
   f := id the two cospans are the same two morphisms.  No non-existence
   of a cospan isomorphism is proved anywhere here.  What is true is
   that the two vertices are canonically
   isomorphic, both being equalizers of the same parallel pair, and that
   the comparison commutes with the two equalizing maps. 

   --------
   * ** 比较这两个方格

   这两个余跨并不是同一个方格。它们没有共享一个余域（x × y 与 y × y），而且它们的边甚至不平行：Mac Lane 的两个边都从 x 出发，而 Awodey 的边分别从 x 和 y 出发。  
   这些在文件末尾被驳斥，边的比较属于可形成性（FORMABILITY）否定（当 x 和 y 不同时类型错误），而不是转换否定。差异不仅仅是句法上的，下面的四个引理与此有关：Mac Lane 的两条腿都是分裂单态，有唯一的公共回撤 exl，而 [exl ∘ aw_pair] 是 f，对于一般的 f 并不是恒等映射。严格理解这个限定词。它并没有说 Awodey 的腿从来不是分裂的——在 f := id 时，它确实是，由 [ml_right_split] 所示——而本评论的早期草稿得出的结论是“因此没有对象重标记可以把一个余楔变成另一个”，但这一点被本文件中的 [maclane_awodey_degenerate_left] / [_right] 反驳，在 f := id 时，这两个余楔是完全相同的两个态射。这里任何地方都没有证明不存在余楔同构。真实的情况是，这两个顶点在范畴论意义上是典型同构的，它们都是相同平行对的等化器，并且比较映射与两个等化映射交换。
*)

Lemma ml_left_split : exl ∘ ml_left ≈ id.
Proof. unfold ml_left. apply exl_fork. Qed.

Lemma ml_right_split : exl ∘ ml_right ≈ id.
Proof. unfold ml_right. apply exl_fork. Qed.

Lemma aw_diag_split : exl ∘ aw_diag ≈ id.
Proof. unfold aw_diag. apply exl_fork. Qed.

(*
 Awodey's other leg retracts to f.  NOTE THE NAME: an earlier draft
 called this [aw_pair_not_split], which asserted more than it proves and
 more than is true -- at f := id this very statement makes [aw_pair]
 split, discharged by [ml_right_split] above.  All that is proved is the
 retraction identity. 

 --------
 Awodey的另一条腿缩回到f。注意名称：早期草稿称其为[aw_pair_not_split]，它所断言的超过了它所证明的，也超过了事实——在f := id时，这个声明本身使[aw_pair]分裂，由上面的[ml_right_split]解除。唯一被证明的是收回恒等式。
*)
Lemma aw_pair_retracts_to_f : exl ∘ aw_pair ≈ f.
Proof. unfold aw_pair. apply exl_fork. Qed.

Lemma maclane_awodey_iso {E F : C} {p1 p2 : E ~> x} {r1 : F ~> x} {r2 : F ~> y}
      (HE : IsPullback ml_left ml_right E p1 p2)
      (HF : IsPullback aw_pair aw_diag F r1 r2) : E ≅ F.
Proof.
  exact (equalizer_unique f g (equalizer_of_pullback_maclane HE)
                              (equalizer_of_pullback_awodey HF)).
Defined.

Lemma maclane_awodey_iso_commutes {E F : C} {p1 p2 : E ~> x}
      {r1 : F ~> x} {r2 : F ~> y}
      (HE : IsPullback ml_left ml_right E p1 p2)
      (HF : IsPullback aw_pair aw_diag F r1 r2) :
  r1 ∘ to (maclane_awodey_iso HE HF) ≈ p1
    ∧ p1 ∘ from (maclane_awodey_iso HE HF) ≈ r1.
Proof.
  split; simpl.
  - exact (unique_property
             (eq_desc (equalizer_of_pullback_awodey HF) p1
                (fork_eq (equalizer_of_pullback_maclane HE)))).
  - exact (unique_property
             (eq_desc (equalizer_of_pullback_maclane HE) r1
                (fork_eq (equalizer_of_pullback_awodey HF)))).
Qed.

End EqualizerFromPullbackSquares.

(*
   * The two cospans coincide, up to swapping the two legs, exactly in the
   degenerate case f = id.  Both sides are checked at Leibniz equality. 

   --------
   * 两个余跨在交换两条支腿的情况下恰好在退化情况 f = id 时重合。双方均在莱布尼茨等式下进行了检查。
*)

Example maclane_awodey_degenerate_left {C : Category} `{@Cartesian C}
        {x : C} : @ml_left C _ x x id = @aw_diag C _ x := eq_refl.

Example maclane_awodey_degenerate_right {C : Category} `{@Cartesian C}
        {x : C} (g : x ~> x) :
  @ml_right C _ x x g = @aw_pair C _ x x id g := eq_refl.

(* ====================================================================== *)
(* * * (E) Pullbacks and a terminal object give products and equalizers / * * (E) 拉回和终对象产生积和等化器 *)

Section ProductFromPullback.

Context {C : Category}.
Context `{T : @Terminal C}.
Context {x y : C}.
Context {P : C} {p1 : P ~> x} {p2 : P ~> y}.
Context (HP : IsPullback (one : x ~> 1) (one : y ~> 1) P p1 p2).

(*
 maclane:III.4:ex10; awodey:5.4:prop16; riehl:3.5:lem15, binary case.
 Pulling back over the terminal object imposes no condition -- the
 square commutes automatically, by [one_unique] -- so the pullback of
 x --!--> 1 <--!-- y is the product, and its universal property is the
 product's with the commutation hypothesis discharged rather than
 assumed.  The conclusion is stated at [IsCartesianProduct], the
 apex-pinned form, before any class is packaged. 

 --------
 maclane:III.4:ex10; awodey:5.4:prop16; riehl:3.5:lem15，二元情况。拉回终对象不带来任何条件——方形自动交换，由 [one_unique]——因此 x --!--> 1 <--!-- y 的拉回是积，并且它的普遍性质是积的性质，交换假设已解除而非假定。结论在 [IsCartesianProduct] 中给出，这是顶点固定的形式，在任何类被打包之前。
*)
Definition pb_fork {a : C} (u : a ~> x) (v : a ~> y) : a ~> P :=
  unique_obj (is_pullback_ump HP a u v (one_unique _ _)).

Lemma pb_fork_fst {a : C} (u : a ~> x) (v : a ~> y) :
  p1 ∘ pb_fork u v ≈ u.
Proof.
  unfold pb_fork.
  now destruct (unique_property (is_pullback_ump HP a u v (one_unique _ _))).
Qed.

Lemma pb_fork_snd {a : C} (u : a ~> x) (v : a ~> y) :
  p2 ∘ pb_fork u v ≈ v.
Proof.
  unfold pb_fork.
  now destruct (unique_property (is_pullback_ump HP a u v (one_unique _ _))).
Qed.

Lemma pb_fork_unique {a : C} (u : a ~> x) (v : a ~> y) (h : a ~> P) :
  p1 ∘ h ≈ u → p2 ∘ h ≈ v → pb_fork u v ≈ h.
Proof.
  intros H1 H2.
  exact (uniqueness (is_pullback_ump HP a u v (one_unique _ _)) h
           (H1, H2)).
Qed.

Definition product_of_pullback : @IsCartesianProduct C x y P.
Proof using All.
  unshelve econstructor.
  - exact (@pb_fork).
  - exact p1.
  - exact p2.
  - intros a u u' Hu v v' Hv.
    apply pb_fork_unique.
    + now rewrite pb_fork_fst.
    + now rewrite pb_fork_snd.
  - intros a u v h; split.
    + intros Hh; split.
      * rewrite Hh.
        apply pb_fork_fst.
      * rewrite Hh.
        apply pb_fork_snd.
    + intros [H1 H2].
      symmetry.
      now apply pb_fork_unique.
Defined.

End ProductFromPullback.

Section CartesianFromPullbacks.

Context {C : Category}.
Context `{T : @Terminal C}.
Context (HPB : @HasPullbacks C).

(* The chosen pullback of the terminal cospan a --!--> 1 <--!-- b. / 终端余跨度 a --!--> 1 <--!-- b 的选定拉回。 *)
Definition pb_chosen (a b : C) : Pullback (one : a ~> 1) (one : b ~> 1) :=
  @pullback C HPB a b 1%object one one.

Definition pb_prod (a b : C) : C := Pull _ _ (pb_chosen a b).

Definition pb_prod_IsCartesianProduct (a b : C) :
  @IsCartesianProduct C a b (pb_prod a b) :=
  product_of_pullback (pullback_is_pullback one one (pb_chosen a b)).

Definition Cartesian_of_HasPullbacks_Terminal : @Cartesian C := {|
  product_obj := pb_prod ;
  fork := fun a b c u v =>
            @fork' C b c (pb_prod b c) (pb_prod_IsCartesianProduct b c) a u v ;
  exl := fun a b => @exl' C a b (pb_prod a b)
                      (pb_prod_IsCartesianProduct a b) ;
  exr := fun a b => @exr' C a b (pb_prod a b)
                      (pb_prod_IsCartesianProduct a b) ;
  fork_respects := fun a b c =>
    @fork'_respects C b c (pb_prod b c) (pb_prod_IsCartesianProduct b c) a ;
  ump_products := fun a b c =>
    @ump_product C b c (pb_prod b c) (pb_prod_IsCartesianProduct b c) a
|}.

(*
 Combining (E) with (D): the Awodey square is now available, so a
 category with pullbacks and a terminal object has all equalizers. 

 --------
 将 (E) 与 (D) 结合：Awodey 方格现在可用，因此具有拉回和终对象的范畴具有所有的等化器。
*)
Definition HasEqualizers_of_HasPullbacks_Terminal : @HasEqualizers C.
Proof using All.
  pose (CC := Cartesian_of_HasPullbacks_Terminal).
  constructor.
  intros a b f g.
  exists (Pull _ _ (@pullback C HPB a b (@product_obj C CC b b)
                      (@aw_pair C CC a b f g) (@aw_diag C CC b))).
  exists (pullback_fst _ _ _).
  exact (@equalizer_of_pullback_awodey C CC a b f g _ _ _
           (pullback_is_pullback _ _ _)).
Defined.

End CartesianFromPullbacks.

(* ====================================================================== *)
(* * * (F) The dual: cocartesian + coequalizers give pushouts / * *（F）对偶：余笛卡尔 + 余等化器产生推挤出 *)

Section Duality.

Context {C : Category}.

Definition IsEqualizer_op_of_IsCoequalizer {x y : C} {f g : x ~> y}
           {q : C} {e : y ~> q} (E : IsCoequalizer f g q e) :
  @IsEqualizer (C^op) y x f g q e :=
  @Build_IsEqualizer (C^op) y x f g q e (cofork E)
    (fun z h Hh => coeq_desc E h Hh).

Definition IsCoequalizer_of_IsEqualizer_op {x y : C} {f g : x ~> y}
           {q : C} {e : y ~> q} (E : @IsEqualizer (C^op) y x f g q e) :
  IsCoequalizer f g q e :=
  @Build_IsCoequalizer C x y f g q e (fork_eq E)
    (fun z h Hh => eq_desc E h Hh).

Example IsCoequalizer_op_round {x y : C} {f g : x ~> y}
        {q : C} {e : y ~> q} (E : IsCoequalizer f g q e) :
  IsCoequalizer_of_IsEqualizer_op (IsEqualizer_op_of_IsCoequalizer E) = E
  := eq_refl.

Example IsEqualizer_op_round {x y : C} {f g : x ~> y}
        {q : C} {e : y ~> q} (E : @IsEqualizer (C^op) y x f g q e) :
  IsEqualizer_op_of_IsCoequalizer (IsCoequalizer_of_IsEqualizer_op E) = E
  := eq_refl.

Definition HasEqualizers_op_of_HasCoequalizers
           (E : @HasCoequalizers C) : @HasEqualizers (C^op).
Proof.
  constructor.
  intros x y f g.
  destruct (@coeq C E y x f g) as [q [e Eq]].
  exists q, e.
  exact (IsEqualizer_op_of_IsCoequalizer Eq).
Defined.

Definition HasCoequalizers_of_HasEqualizers_op
           (E : @HasEqualizers (C^op)) : @HasCoequalizers C.
Proof.
  constructor.
  intros x y f g.
  destruct (@equalizer (C^op) E y x f g) as [q [e Eq]].
  exists q, e.
  exact (IsCoequalizer_of_IsEqualizer_op Eq).
Defined.

End Duality.

Section PushoutFromCoequalizer.

Context {C : Category}.
Context `{O : @Cocartesian C}.

(* The coproduct vocabulary of Structure/Cocartesian.v is the product vocabulary of C^op ON THE NOSE, which is what lets (A) be instantiated below with no translation step at all. / Structure/Cocartesian.v 的余积词汇正是 C^op 的积词汇，这正是使得下面的 (A) 可以在完全不经过任何转换步骤的情况下被实例化的原因。 *)
Example Coprod_is_op_product (a b : C) :
  @Coprod C O a b = @product_obj (C^op) O a b := eq_refl.

Example inl_is_op_exl {a b : C} :
  (@inl C O a b) = @exl (C^op) O a b := eq_refl.

Example inr_is_op_exr {a b : C} :
  (@inr C O a b) = @exr (C^op) O a b := eq_refl.

Lemma pushout_of_coequalizer {x y z : C} (f : x ~> y) (g : x ~> z)
      {E : C} {e : y + z ~> E}
      (Eq : IsCoequalizer (inl ∘ f) (inr ∘ g) E e) :
  @IsPullback (C^op) y z x f g E (e ∘ inl) (e ∘ inr).
Proof.
  exact (@pullback_of_equalizer (C^op) O y z x f g E e
           (IsEqualizer_op_of_IsCoequalizer Eq)).
Qed.

(* Read through the covariant accessors of Structure/Pushout.v. The apex and both injections compute: no transport, no [≈]-step. / 通读 Structure/Pushout.v 的协变访问器。顶点和两个注入都能计算：没有传输，没有 [≈] 步骤。 *)
Definition IsPushout_of_coequalizer {x y z : C} (f : x ~> y) (g : x ~> z)
      {E : C} {e : y + z ~> E}
      (Eq : IsCoequalizer (inl ∘ f) (inr ∘ g) E e) : IsPushout f g :=
  is_pullback_pullback (pushout_of_coequalizer f g Eq).

Example IsPushout_of_coequalizer_apex {x y z : C} (f : x ~> y) (g : x ~> z)
      {E : C} {e : y + z ~> E}
      (Eq : IsCoequalizer (inl ∘ f) (inr ∘ g) E e) :
  pushout_apex (IsPushout_of_coequalizer f g Eq) = E := eq_refl.

Example IsPushout_of_coequalizer_in1 {x y z : C} (f : x ~> y) (g : x ~> z)
      {E : C} {e : y + z ~> E}
      (Eq : IsCoequalizer (inl ∘ f) (inr ∘ g) E e) :
  pushout_in1 (IsPushout_of_coequalizer f g Eq) = e ∘ inl := eq_refl.

Example IsPushout_of_coequalizer_in2 {x y z : C} (f : x ~> y) (g : x ~> z)
      {E : C} {e : y + z ~> E}
      (Eq : IsCoequalizer (inl ∘ f) (inr ∘ g) E e) :
  pushout_in2 (IsPushout_of_coequalizer f g Eq) = e ∘ inr := eq_refl.

End PushoutFromCoequalizer.

Definition HasPushouts_of_Cocartesian_HasCoequalizers {C : Category}
           `{O : @Cocartesian C} (E : @HasCoequalizers C) : @HasPushouts C :=
  HasPushouts_of_HasPullbacks_op
    (@HasPullbacks_of_Cartesian_HasEqualizers (C^op) O
       (HasEqualizers_op_of_HasCoequalizers E)).

(* ====================================================================== *)
(*
   * * Measured negatives

   Every strengthening attempted and refused, recorded as a [Fail] so a
   later change to a donor breaks this file loudly rather than silently
   invalidating a prose claim.  The two KINDS are kept apart, and the
   split is measured rather than guessed: negatives 2 and 3 are
   FORMABILITY failures -- the two legs do not live in a common hom-set,
   so the equation cannot be stated -- while negatives 1, 4, 5, 6 and 7
   are CONVERSION failures, where both sides are well typed and [eq_refl]
   is refused.  Positive controls sit beside them.

   These are measurements made in this file, not a substitute for a
   guarded probe file with an instrument check. 

   --------
   * * 测量的负面结果

   每一次尝试增强但被拒绝的情况，都记录为 [Fail]，这样之后如果更改为捐赠者，会显而易见地导致此文件报错，而不是悄无声息地使散文声明无效。这两种类型被区分开来，并且其划分是经过测量的，而不是猜测的：负面结果 2 和 3 是可形成性（FORMABILITY）失败——两个分支不属于同一同类集合，因此无法陈述该方程——而负面结果 1、4、5、6 和 7 是转换（CONVERSION）失败，此时两边类型都正确，但 [eq_refl] 被拒绝。正面控制放置在它们旁边。

   这些是在此文件中进行的测量，而不是带有仪器检查的受控探测文件的替代。
*)

Section Negatives.

Context {C : Category}.
Context `{@Cartesian C}.
Context {x y : C}.
Context (f g : x ~> y).

(* 1. The two cospans of section (D) do not share a codomain. / 1. 第(D)节的两个余跨并不共享一个陪域。 *)
Fail Example neg_ml_aw_codomain :
  (x × y)%object = (y × y)%object := eq_refl.

(* positive control: the degenerate instantiation y := x does. / 阳性对照：退化实例化 y := x 所做的。 *)
Example pos_ml_aw_codomain_degenerate :
  (x × x)%object = (x × x)%object := eq_refl.

(* 2, 3. Nor are the legs parallel: these are ill-typed, not merely inconvertible. / 2, 3. 腿也不平行：这些是类型错误的，而不仅仅是不可转换的。 *)
Fail Example neg_ml_left_is_aw_pair :
  @ml_left C _ x y f = @aw_pair C _ x y f g := eq_refl.

Fail Example neg_ml_right_is_aw_diag :
  @ml_right C _ x y g = @aw_diag C _ y := eq_refl.

(*
 positive control: at f := id the legs DO coincide, up to swapping the
 two sides of the cospan -- this is [maclane_awodey_degenerate_*]. 

 --------
 阳性控制：在 f := id 时，腿确实重合，最多只是交换余跨的两边 —— 这是 [maclane_awodey_degenerate_*]。
*)
Example pos_ml_aw_degenerate :
  @ml_left C _ x x id = @aw_diag C _ x := eq_refl.

(* 4. The (A)/(B) round trip on the equalizing map is [≈], not [=]. / 4. 在均衡地图上的 (A)/(B) 往返行程是 [≈]，而不是 [=]。 *)
Fail Example neg_equalizer_pullback_round {E : C} (e : E ~> x × y) :
  (exl ∘ e) △ (exr ∘ e) = e := eq_refl.

(* 5. Nor is the reverse composite strict on the projections. / 5. 反向复合在投影上也不是严格的。 *)
Fail Example neg_pullback_equalizer_round {P : C}
     (p1 : P ~> x) (p2 : P ~> y) : exl ∘ (p1 △ p2) = p1 := eq_refl.

(* positive control for 4 and 5: both hold at [≈]. / 4和5的阳性对照：两者均保持在[≈]。 *)
Example pos_rounds_up_to_equiv {E : C} (e : E ~> x × y) :
  (exl ∘ e) △ (exr ∘ e) ≈ e := equalizer_pullback_round E e.

End Negatives.

Section NegativesDuality.

Context {C : Category}.

(*
 6, 7. The duality of section (F) is NOT definitional: [IsCoequalizer]
 and [IsEqualizer] are distinct record types, so neither the predicates
 nor the classes are related by [eq_refl], however convertible their
 fields are. 

 --------
 6, 7. (F) 节的对偶性不是定义性的：[IsCoequalizer] 和 [IsEqualizer] 是不同的记录类型，因此无论它们的字段如何可转换，其谓词和类都不通过 [eq_refl] 相关。
*)
Fail Example neg_HasCoequalizers_is_op :
  HasCoequalizers C = HasEqualizers (C^op) := eq_refl.

Fail Example neg_IsCoequalizer_is_op {x y : C} (f g : x ~> y)
     (q : C) (e : y ~> q) :
  IsCoequalizer f g q e = @IsEqualizer (C^op) y x f g q e := eq_refl.

(* positive control: the FIELD types are convertible, which is exactly why the bridge below needs no tactic. / 阳性对照：FIELD 类型是可转换的，这正是下面的桥梁不需要策略的原因。 *)
Example pos_cofork_is_fork_eq {x y : C} (f g : x ~> y)
        (q : C) (e : y ~> q) (Hyp : e ∘ f ≈ e ∘ g) :
  f ∘[C^op] e ≈ g ∘[C^op] e := Hyp.

End NegativesDuality.
