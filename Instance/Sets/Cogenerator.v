Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Concrete.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Adjunction.SAFT.

Generalizable All Variables.

(*
 Cogenerators of [Sets]: the object of truth values, under [Untruncate]
 or under [IEM]; the trivial large family, unconditionally; and why no
 SMALL one is unconditional

 nLab:  https://ncatlab.org/nlab/show/separator
 nLab:  https://ncatlab.org/nlab/show/adjoint+functor+theorem

 Mac Lane, “Categories for the Working Mathematician”, 2nd ed. (GTM 5),
 §V.7, book p. 127 (PDF p. 136), dualizes his Definition 4: a set Q of
 objects COGENERATES a category when, for every parallel pair
 h ≠ h' : a → b, some q ∈ Q carries g : b → q with g ∘ h ≠ g ∘ h'; his
 example is that any two-point set is a cogenerator of Set (catalogue
 item maclane:V.7:def5).  Riehl, “Category Theory in Context”, 2nd ed.,
 Definition 4.7.7, printed p. 177 (PDF p. 197), names the same notion a
 coseparating set: a separating set of C^op.  The notion is the third
 hypothesis of the special initial-object theorem, Mac Lane §V.8
 Theorem 1, book p. 128 (PDF pp. 137–138), and Riehl Lemma 4.7.11,
 printed p. 177 (PDF pp. 197–198), whose in-tree form is
 Adjunction/SAFT/InitialObject.v.  This file supplies the premise at
 [Sets]; Instance/Sets/SpecialInitial.v runs the theorem on it.

 WHAT IS BUILT.  Everything is stated against Adjunction/SAFT.v's
 [Cogenerator] record, whose field [cog_separates] is the positive
 cancellation law (arrows agreeing after every test arrow are equal);
 Instance/Sets/Generator.v's header records why the positive form, and
 not Mac Lane's “≠” form, is the one that makes sense over a
 [Type]-valued hom-setoid with no decision procedure.  In the refusals
 quoted in this header, a universe the compile generated is written
 <1>, <2>, ..., numbered afresh in each quote in order of first
 appearance, as Test/ProbeSpecialInitial452.v writes them, so that the
 numerals carry identity and no serial number is a claim.

 - [Sets_Cogenerator_untruncate U]: a one-member family, the setoid
 [Powerset_Prop_truth] of Instance/Sets/Powerset.v ([Prop] under
 mutual implication).  The test arrow at a point [y0] is that file's
 [Powerset_Prop_singleton_pred y0], the truncated singleton
 b ↦ ‖y0 ≈ b‖, reused rather than rebuilt.  Given [f g : x ~> y]
 agreeing after every test arrow, the test at [f a] gives
 ‖f a ≈ f a‖ ↔ ‖f a ≈ g a‖; the left side holds by reflexivity, and
 [Untruncate] (Instance/Sets/Classifier/OneLevel.v) removes the
 truncation from the right.  The hypothesis is used exactly once.
 - [Sets_Cogenerator_IEM E]: a one-member family, the two-element
 setoid [BoolSetoid] of Instance/Sets/Classifier/OneLevel.v, with
 test arrow [sets_bool_char E y0] sending [b] to [ptrue] exactly
 when [E] decides [y0 ≈ b] positively.  This is Mac Lane's two-point
 set, literally.  [inl] and [inr] are written [Datatypes.inl] and
 [Datatypes.inr]: under an import list that includes
 Structure/Cocartesian.v, that file's [inl] shadows the constructor
 and the unqualified pattern is refused with “Unknown constructor:
 inl” (measured: this file's import list plus that one refuses a
 one-line [match] on [inl]/[inr], this file's list alone accepts
 it), so the qualified names keep the proof independent of what a
 later edit imports.
 - Under [IEM] the first is available too: Instance/Sets/Classifier/
 OneLevel.v's [untruncate_of_IEM] turns [E : IEM] into an
 [Untruncate], and [Sets_Cogenerator_untruncate (untruncate_of_IEM
 E)] is accepted in a scratch file, closed under the global context,
 with the first's [Set < o].  What [Sets_Cogenerator_IEM] adds is the
 literal two-point object and the absence of that bound: at
 [o := Set] the composite is refused, “The term
 ”untruncate_of_IEM@{Set} E“ has type ”Untruncate@{Set}“ while it is
 expected to have type ”Untruncate@{<1>}“ (universe inconsistency:
 Cannot enforce <1> = Set because Set < <1>)”, while
 [Sets_Cogenerator_IEM E] is accepted there, which is what
 Instance/Sets/SpecialInitial.v's [sets_special_initial_IEM_at_Set]
 uses.
 - [Sets_Cogenerator_large]: the trivial LARGE family, with no
 hypothesis.  Its index is the type [SetoidObject@{o o}] of all
 objects and each object is its own member; for [f g : x ~> y],
 the test arrow [id] into the member [y] already separates, so
 arrows agreeing after every test agree outright.  It is not SMALL
 in the sense the special initial-object theorem needs: its index
 universe [c] lies strictly above [o] ([o < c], UNIVERSES below),
 while Adjunction/SAFT.v's [cogen_prod] identifies the index
 universe with the shape universe of its [Complete], which at
 Instance/Sets/Complete.v's [Sets_Complete] ([Complete@{o o o so}])
 is [o].  Test/ProbeSpecialInitial452.v's N13 and N14, labelled
 P_large_cog, pin the refusal.  With [o < c] and [Sets_Complete]
 ascribed [Complete@{o o o so}], N13
 ([p452_n13_large_prod_sets]), [cogen_prod Sets_Complete
 Sets_Cogenerator_large@{c o so}], is refused at the family: “The
 term ”Sets_Cogenerator_large“ has type ”Cogenerator@{c so o}
 Sets@{o so}“ while it is expected to have type ”Cogenerator@{o so
 o} Sets@{o so}“ (universe inconsistency: Cannot enforce c = o
 because o < c)”; N14 ([p452_n14_large_sio_sets]),
 [special_initial_object] there over the least subobject, is
 refused with the same text.  The controls: the constant itself at
 the universes below ([p452_large_cog]), and [cogen_prod] and
 [special_initial_object] at [Sets_Complete] with
 [Sets_Cogenerator_untruncate U] ([p452_small_prod_sets],
 [p452_small_sio_sets]).
 - [Sets_terminal_not_cogenerates]: the premise is a genuine
 condition at [Sets].  No family of copies of the terminal object
 cogenerates, whatever its index type, because every two arrows
 into the terminal object agree (Structure/Terminal.v's
 [one_unique]) while [Sets] has parallel arrows that differ
 (Theory/Concrete.v's [Sets_two_arrows]).  It is the counterpart of
 Instance/Sets/Generator.v's [Sets_empty_not_separates]: the empty
 set has no probes, the singleton has no discriminating tests.  It
 is a theorem about a well-typed hypothesis, not a refusal probe.

 All seven constants of this file are closed under the global context
 (Print Assumptions on each).  The three cogenerators are transparent
 ([Defined]), and the members of the two small ones read back by
 [eq_refl] ([sets_cogenerator_untruncate_obj],
 [sets_cogenerator_IEM_obj]).

 WHY THERE IS NO UNCONDITIONAL SMALL COGENERATOR AT [Sets] IN THIS
 TREE.  A measured refusal of one construction, not an impossibility
 proof: nothing here shows that [Sets] has no small [Cogenerator],
 small meaning indexed at [Sets_Complete]'s shape universe [o], where
 [cogen_prod] needs it; an unconditional LARGE one is
 [Sets_Cogenerator_large] above.  Classically the cogenerator is the
 object of truth values, and the test arrow at [y0] sends [b] to the
 truth value of [y0 ≈ b].  In this library [≈] is
 [Type]-valued (Lib/Setoid.v's [crelation]), so for an object [Y] of
 [Sets@{o so}] that truth value is a [Type@{o}].  Two ways of receiving
 it are pinned by Test/ProbeSpecialInitial452.v's N11 and N12, labelled
 P_type_truth, whose import list contains this file's and this file
 itself, each beside a positive control and each read by un-wrapping
 the refused command in its own copy of the WHOLE probe.  The object of
 truth values there is [Type@{l}] under [iffT], its equivalence proved
 in full ([p452_iff_setoid]), so that each refused command differs from
 its control in a universe only:

 (i) N11 ([p452_n11_truth_at]): [Type@{o}] under [iffT] as an object
 of [Sets@{o so}] is refused, because the carrier [Type@{o}]
 lives at [o+1]:
 “The term ”{| carrier := Type; is_setoid := p452_iff_setoid |}“
 has type ”SetoidObject“ while it is expected to have type
 ”obj[Sets]“ (universe inconsistency: Cannot enforce <1> = o
 because o < <1>).”
 The control, the same setoid one level down on [Type@{l}] with
 [l < o] ([p452_truth_low]), is accepted.  The form first
 measured on #452, in a scratch probe that left the equivalence
 proof as a hole, is refused with the same bound; the probe pins
 the closed form, since a hole could make the command refuse for
 its own reason.
 (ii) N12 ([p452_n12_char_at]): into that lower setoid, the test
 arrow [fun b => @equiv _ (is_setoid Y) y0 b] is refused for an
 arbitrary object [Y] of [Sets@{o so}]:
 “The term ”y0 ≈ b“ has type ”Type“ while it is expected to have
 type ”carrier {| carrier := Type; is_setoid := p452_iff_setoid
 |}“ (universe inconsistency: Cannot enforce o <= l because
 l < o).”
 The control, for [Y : SetoidObject@{l l}] ([p452_char_low]), is
 accepted, and so is [Sets_Cogenerator_untruncate] at the same
 universes ([p452_cog_untruncate]).  Both refusals are universe
 inconsistencies, not missing instances.

 This is the size wall of Structure/Complete.v's size note met from the
 other side: a [Type]-valued relation on a carrier sits one universe
 above it.  [Prop] and [poly_bool] truth values fit at [o], but reading
 an equation back out of them is exactly what [Untruncate] (from ‖P‖ to
 P) or [IEM] (deciding P) provides, and the tree has neither
 unconditionally; Instance/Sets/Classifier/OneLevel.v proves [DecImage]
 equivalent to [IEM] and leaves open whether [Untruncate] gives [IEM];
 the converse is its [untruncate_of_IEM] (above).
 The position is the same as that of [Sets]' subobject classifier
 (that file's [Sets_Classifier U]) and of its well-poweredness at the
 pin (Instance/Sets/WellPowered.v's [Sets_WellPowered_untruncate U]).

 UNIVERSES, measured with [Set Printing Universes. About …], stdlib
 bounds left out:

 Sets_Cogenerator_untruncate@{c o so} :
 Untruncate@{o} → Cogenerator@{c so o} Sets@{o so}
 ( * Set < o, o < so * )
 sets_bool_char@{o so} : ∀ {Y : SetoidObject@{o o}},
 IEM@{o} → Y → Y ~{ Sets@{o so} }~> BoolSetoid@{o}
 ( * o < so * )
 Sets_Cogenerator_IEM@{c o so} :
 IEM@{o} → Cogenerator@{c so o} Sets@{o so}
 ( * o < so * )
 Sets_Cogenerator_large@{c o so} :
 Cogenerator@{c so o} Sets@{o so}
 ( * o < c, o < so * )

 The [Set < o] of the first is [Prop]'s: [Powerset_Prop_truth] has
 carrier [Prop : Type@{Set+1}], as Instance/Sets/Powerset.v records.
 The [IEM] cogenerator carries no [Set] bound, and
 Instance/Sets/SpecialInitial.v's [sets_special_initial_IEM_at_Set]
 takes it at [o := Set].  The index universe [c] is free in the two
 small cogenerators.  The binders name what minimization already
 delivered: an unannotated draft of this file measured
 [Sets_Cogenerator_untruncate@{u u0 u1} : Untruncate@{u} →
 Cogenerator@{u0 u1 u} Sets@{u u1}] with [Set < u] and [u < u1], the
 same shape; they are there so that later edits cannot drift it.  A
 consumer through Adjunction/SAFT.v's [cogen_prod] identifies [c] with
 the shape universe of its [Complete] (the collapse recorded in
 Adjunction/SAFT/InitialObject.v), which at Instance/Sets/Complete.v's
 [Sets_Complete] is [o].  [Sets_Cogenerator_large] bounds [c] strictly
 above [o], its index being the type of objects, and that is the
 identification refused above.

 PLACEMENT.  Instance/Sets/Generator.v, beside [Sets_Generator], would
 be the natural home, and the import cost rules it out.  Measured as the
 transitive closure over .Makefile.coq.d, counting the root: that file's
 closure is 23 modules, and adding the three imports these constants
 need beyond it (Adjunction/SAFT.v, Instance/Sets/Powerset.v,
 Instance/Sets/Classifier/OneLevel.v) raises it to 87.  This file's own
 closure is 85 modules.

 NOT DELIVERED.  No unconditional SMALL [Cogenerator] at [Sets] (above):
 the unconditional [Sets_Cogenerator_large] is large, and [cogen_prod]
 at [Sets_Complete] refuses it.  No [BoolSetoid] cogenerator from
 [Untruncate] alone: the test arrow above needs a decision, which
 truncation does not supply, and no other route was tried.  No
 comparison of the three cogenerators, and no claim that any is
 minimal.  No cogenerator of any other concrete category
 ([Grp], [Ab] with Q/Z, [FinSet]) in this file.  (Since #454 other
 files build some: Instance/Mod/Cogenerator.v's unconditional but
 large [RMod_Cogenerator_large], which [cogen_prod] refuses as this
 file's [Sets_Cogenerator_large] is refused, and its conditional
 [QZ_Cogenerator] at [Ab] and [QZ_injective_cogenerator] at [RMod R],
 whose premise is Mac Lane's Exercise 2(b) fact about Q/Z and is shown
 there to entail double-negation elimination; and Instance/Mod/
 WellPowered.v's unconditional [RModop_Cogenerator] at (RMod R)^op.
 None is at [Grp] or [FinSet].)  Structure/Generator/Dual.v's
 [cog_of_gen] already gives one at [Sets^op] from [Sets_Generator];
 Instance/Sets/SpecialInitial.v applies it. 

 --------
 [Sets] 的协生成器：在 [Untruncate] 下或在 [IEM] 下的真值对象；平凡的大族，无条件；以及为什么没有小族是无条件的

 nLab: https://ncatlab.org/nlab/show/separator
 nLab: https://ncatlab.org/nlab/show/adjoint+functor+theoremMac Lane，《为工作中的数学家准备的范畴论》，第2版（GTM 5），§V.7，第127页（PDF第136页），对他的定义4进行对偶化：当对每一对平行箭头 h ≠ h' : a → b，存在某个 q ∈ Q 使得 g : b → q 满足 g ∘ h ≠ g ∘ h' 时，对象集 Q 生成一个范畴；他的例子是任意两个点的集合是 Set 的余生成器（目录项 maclane:V.7:def5）。Riehl，《上下文中的范畴论》，第2版，定义4.7.7，第177页印刷版（PDF第197页），将同一概念称为余分离集：C^op 的分离集。该概念是特殊初始对象定理的第三个假设，Mac Lane §V.8 定理1，第128页（PDF第137–138页），以及 Riehl 引理4.7.11，第177页印刷版（PDF第197–198页），其树内形式为 Adjunction/SAFT/InitialObject.v。此文件提供了在 [Sets] 上的前提；Instance/Sets/SpecialInitial.v 在其上运行定理。

 构建的内容。所有内容都是针对 Adjunction/SAFT.v 的 [Cogenerator] 记录陈述的，其字段 [cog_separates] 是正消去律（每个测试箭头后相符的箭头相等）；Instance/Sets/Generator.v 的头文件记录了为什么选择正形式，而不是 Mac Lane 的“≠”形式，这是在没有判定程序的 [Type] 值态射集上有意义的。在该头文件引用的拒绝中，编译生成的宇宙写作 <1>, <2>, ...，在每次引用中按首次出现的顺序重新编号，就像 Test/ProbeSpecialInitial452.v 所写的那样，因此这些数字具有唯一性且没有序列号的要求。- [Sets_Cogenerator_untruncate U]：一个单成员族，集合论
 [Powerset_Prop_truth] 来自 Instance/Sets/Powerset.v（[Prop] 在相互蕴含下）。在点 [y0] 的测试箭头是该文件的
 [Powerset_Prop_singleton_pred y0]，截断的单例
 b ↦ ‖y0 ≈ b‖，被重复使用而不是重建。给定 [f g : x ~> y]
 在每个测试箭头之后都一致，在 [f a] 的测试给出
 ‖f a ≈ f a‖ ↔ ‖f a ≈ g a‖；左边由自反性成立，而
 [Untruncate]（Instance/Sets/Classifier/OneLevel.v）去掉右边的
 截断。假设恰好使用一次。- [Sets_Cogenerator_IEM E]：一个单成员族，二元
 集合论 [BoolSetoid] 来自 Instance/Sets/Classifier/OneLevel.v，其
 测试箭头 [sets_bool_char E y0] 精确地将 [b] 发送到 [ptrue]，当且仅当 [E] 正向判定 [y0 ≈ b]。这就是 Mac Lane 的两点集合，字面意思。[inl] 和 [inr] 被写作 [Datatypes.inl] 和 [Datatypes.inr]：在包含 Structure/Cocartesian.v 的导入列表下，该文件的 [inl] 会隐藏构造函数，而未经限定的模式会被拒绝并显示“未知构造函数：inl”（测量结果：该文件的导入列表加上那个文件会拒绝在 [inl] / [inr] 上的一行 [match]，而仅使用该文件的列表则接受它），因此限定名称保持了证明不依赖于以后编辑导入的内容。- 在 [IEM] 下，第一个也是可用的：Instance/Sets/Classifier/OneLevel.v 的 [untruncate_of_IEM] 将 [E : IEM] 转换为 [Untruncate]，并且 [Sets_Cogenerator_untruncate (untruncate_of_IEM E)] 在一个临时文件中被接受，该文件在全局上下文中封闭，使用第一个的 [Set < o]。[Sets_Cogenerator_IEM] 添加的是字面上的两点对象以及该界的缺失：在 [o := Set] 处，该复合被拒绝，“术语 'untruncate_of_IEM@{Set} E' 的类型是 'Untruncate@{Set}'，而预期的类型是 'Untruncate@{<1>}'（宇宙不一致：无法强制 <1> = Set 因为 Set < <1>）”，而 [Sets_Cogenerator_IEM E] 在那里被接受，这正是 Instance/Sets/SpecialInitial.v 的 [sets_special_initial_IEM_at_Set] 所使用的。- [Sets_Cogenerator_large]：平凡的 LARGE 系列，没有假设。它的指标是所有对象的类型 [SetoidObject@{o o}]，并且每个对象都是它自己的成员；对于 [f g : x ~> y]，测试箭头 [id] 指向成员 [y] 已经分离，所以每次测试后同意的箭头直接同意。它在特殊初始对象定理所需的意义上不是 SMALL：它的指标宇宙 [c] 严格位于 [o] 之上（[o < c]，下面的 UNIVERSES），而 Adjunction/SAFT.v 的 [cogen_prod] 将指标宇宙与其 [Complete] 的形状宇宙相同，而在 Instance/Sets/Complete.v 的 [Sets_Complete]（[Complete@{o o o so}]）是 [o]。Test/ProbeSpecialInitial452.v 的 N13 和 N14，被标记为 P_large_cog，确定了拒绝。对于 [o < c] 和 [Sets_Complete]，被归类为 [Complete@{o o o so}]，N13（[p452_n13_large_prod_sets]），[cogen_prod Sets_Complete Sets_Cogenerator_large@{c o so}]，在族中被拒绝：“术语 'Sets_Cogenerator_large' 的类型为 'Cogenerator@{c so o} Sets@{o so}'，而期望类型为 'Cogenerator@{o so o} Sets@{o so}'（宇宙不一致：无法强制 c = o，因为 o < c）”；N14（[p452_n14_large_sio_sets]），[special_initial_object] 在最小子对象上也被拒绝，文本相同。控制：常数本身在以下宇宙（[p452_large_cog]），以及 [cogen_prod] 和 [special_initial_object] 在 [Sets_Complete] 上与 [Sets_Cogenerator_untruncate U]（[p452_small_prod_sets]，[p452_small_sio_sets]）。- [Sets_terminal_not_cogenerates]：前提在 [Sets] 是一个真正的条件。没有任何一族终对象的副本能够共同生成，无论其指标类型如何，因为每两个指向终对象的箭头都是相同的（Structure/Terminal.v 的 [one_unique]），而 [Sets] 有互不相同的平行箭头（Theory/Concrete.v 的 [Sets_two_arrows]）。它是 Instance/Sets/Generator.v 的 [Sets_empty_not_separates] 的对应物：空集没有探针，单元素集没有区分测试。这是关于类型良好的假设的定理，而不是拒绝探针。

 本文件的所有七个常量在全局上下文下都是封闭的（分别使用 Print Assumptions 查看）。三个共生生成器是透明的（[Defined]），两个小型生成器的成员通过 [eq_refl] 读回（[sets_cogenerator_untruncate_obj]，[sets_cogenerator_IEM_obj]）。为什么在这棵树的 [Sets] 处没有无条件的小型协生成器。一个有度量的拒绝某种构造，而不是不可能性证明：这里没有任何内容表明 [Sets] 没有小型 [Cogenerator]，小型指的是在 [Sets_Complete] 的形状宇宙 [o] 下索引，其中 [cogen_prod] 需要它；一个无条件的大型协生成器是上面的 [Sets_Cogenerator_large]。经典上，协生成器是真值对象，而 [y0] 处的测试箭头把 [b] 发送到 [y0 ≈ b] 的真值。在这个库中，[≈] 是 [Type] 值（Lib/Setoid.v 的 [crelation]），所以对于 [Sets@{o so}] 的一个对象 [Y]，该真值是一个 [Type@{o}]。接收它的两种方式由 Test/ProbeSpecialInitial452.v 的 N11 和 N12 固定，标记为 P_type_truth，其导入列表包含此文件及其自身，每个旁边都有一个阳性对照，并且每个通过在其自身的整个探针副本中解开被拒绝的命令来读取。那里真值对象是 [Type@{l}]，在 [iffT] 之下，其等价性已完全证明（[p452_iff_setoid]），以便每个被拒绝的命令在其宇宙中仅与其对照不同：(i) N11 ([p452_n11_truth_at])：[Type@{o}] 在 [iffT] 下作为 [Sets@{o so}] 的对象被拒绝，因为载体 [Type@{o}] 位于 [o+1]：
 “术语 “{| carrier := Type; is_setoid := p452_iff_setoid |}” 的类型是 “SetoidObject”，而预期类型为 “obj [Sets]”（宇宙不一致：无法强制 <1> = o，因为 o < <1>）。“
 控制，在 [Type@{l}] 上一层同样的集合体与 [l < o]（[p452_truth_low]）被接受。首次在 #452 上测量的形式，在一个留下等价性证明为空的临时探测中，也以相同的限制被拒绝；该探测固定了封闭形式，因为一个空可能会因自身原因导致命令被拒绝。(ii) N12 ([p452_n12_char_at])：在那个较低的等价集合中，对于 [Sets@{o so}] 的任意对象 [Y]，测试箭头 [fun b => @equiv _ (is_setoid Y) y0 b] 被拒绝：
 “术语 'y0 ≈ b' 的类型是 'Type'，而它被期望的类型是 'carrier {| carrier := Type; is_setoid := p452_iff_setoid |}'（宇宙不一致：无法强制 o <= l，因为 l < o）。”
 对于 [Y : SetoidObject@{l l}] ([p452_char_low]) 的控制被接受，[Sets_Cogenerator_untruncate] 在相同的宇宙 ([p452_cog_untruncate]) 也被接受。这两个拒绝都是宇宙不一致，而不是缺少实例。这是 Structure/Complete.v 的大小注释所达到的尺寸墙，从另一侧看：一个承载体上的 [Type] 值关系位于其上方一个宇宙。[Prop] 和 [poly_bool] 真值适合在 [o]，但从中读回一个方程恰恰是 [Untruncate]（从 ‖P‖ 到 P）或 [IEM]（决定 P）提供的，而该树无条件地都没有；Instance/Sets/Classifier/OneLevel.v 证明 [DecImage] 等价于 [IEM]，并且没有确定 [Untruncate] 是否给出 [IEM]；其逆是其 [untruncate_of_IEM]（上方）。该位置与 [Sets] 的子对象分类器（该文件的 [Sets_Classifier U]）以及其在 pin 上的良好幂等性（Instance/Sets/WellPowered.v 的 [Sets_WellPowered_untruncate U]）相同。使用 [Set Printing Universes. About …] 测量的宇宙，stdlib 边界省略：Sets_Cogenerator_untruncate@{c o so} ：
 Untruncate@{o} → Cogenerator@{c so o} Sets@{o so}
 （* 集合 < o, o < so *）
 sets_bool_char@{o so} ：∀ {Y : SetoidObject@{o o}},
 IEM@{o} → Y → Y ~{ Sets@{o so} }~> BoolSetoid@{o}
 （* o < so *）
 Sets_Cogenerator_IEM@{c o so} ：
 IEM@{o} → Cogenerator@{c so o} Sets@{o so}
 （* o < so *）
 Sets_Cogenerator_large@{c o so} ：
 Cogenerator@{c so o} Sets@{o so}
 （* o < c, o < so *）第一个的 [Set < o] 是 [Prop] 的：[Powerset_Prop_truth] 拥有载体 [Prop : Type@{Set+1}]，如 Instance/Sets/Powerset.v 所记录的。[IEM] 的共生成器不带有 [Set] 绑定，并且 Instance/Sets/SpecialInitial.v 的 [sets_special_initial_IEM_at_Set] 在 [o := Set] 接受它。索引宇宙 [c] 在两个小共生成器中是自由的。绑定器命名的是最小化已交付的内容：该文件的未注释草稿 [Sets_Cogenerator_untruncate@{u u0 u1} : Untruncate@{u} → Cogenerator@{u0 u1 u} Sets@{u u1}] 使用 [Set < u] 和 [u < u1]，形状相同；它们在那里是为了防止后续编辑导致偏移。通过 Adjunction/SAFT.v 的 [cogen_prod]，消费者将 [c] 与其 [Complete] 的形状宇宙进行识别（折叠记录在 Adjunction/SAFT/InitialObject.v 中），在 Instance/Sets/Complete.v 的 [Sets_Complete] 处是 [o]。[Sets_Cogenerator_large] 将 [c] 严格地界定在 [o] 之上，其索引是对象的类型，这正是上面拒绝的识别。放置。Instance/Sets/Generator.v 文件，本应与 [Sets_Generator] 放在一起，是自然的位置，但导入成本使其不可行。作为 .Makefile.coq.d 上的传递闭包来测量，包括根文件：该文件的闭包是 23 个模块，再加上这些常量需要的三个额外导入（Adjunction/SAFT.v、Instance/Sets/Powerset.v、Instance/Sets/Classifier/OneLevel.v），总数增至 87 个模块。该文件自身的闭包是 85 个模块。未交付。在  [Sets] 处没有无条件的小  [Cogenerator]（如上）：无条件的  [Sets_Cogenerator_large] 很大，且  [Sets_Complete] 处的  [cogen_prod] 拒绝它。没有来自  [Untruncate] 单独的  [BoolSetoid] 联合发生器：上面的测试箭头需要一个决定，而截断不能提供，而且没有尝试其他途径。没有三个位联合发生器的比较，也没有声称任何一个是最小的。该文件中没有任何其他具体类别（ [Grp]、带 Q/Z 的 [Ab]、[FinSet]）的联合发生器。(自 #454 以来，其他文件构建了一些：Instance/Mod/Cogenerator.v 的无条件但较大的 [RMod_Cogenerator_large]，而 [cogen_prod] 拒绝它，因为该文件的 [Sets_Cogenerator_large] 被拒绝，其条件性 [QZ_Cogenerator] 位于 [Ab] 和 [QZ_injective_cogenerator] 位于 [RMod R]，其前提是有关 Q/Z 的 Mac Lane 习题 2(b) 的事实，并在那里显示它蕴含双重否定消除；Instance/Mod/WellPowered.v 的无条件 [RModop_Cogenerator] 位于 (RMod R)^op。没有位于 [Grp] 或 [FinSet]。) Structure/Generator/Dual.v 的 [cog_of_gen] 已经从 [Sets_Generator] 在 [Sets^op] 提供了一个；Instance/Sets/SpecialInitial.v 应用了它。
*)

(* * ** Under [Untruncate]: truth values in [Prop] / * ** 在 [Untruncate] 中：[Prop] 的真值 *)

Definition Sets_Cogenerator_untruncate@{c o so +| Set < o, o < so +}
  (U : Untruncate@{o}) : Cogenerator@{c so o} Sets@{o so}.
Proof.
  refine (@Build_Cogenerator Sets@{o so} unit
            (fun _ => Powerset_Prop_truth@{o}) _).
  intros x y f g H a.
  pose proof (H tt (Powerset_Prop_singleton_pred@{o} (f a)) a) as Ha.
  simpl in Ha.
  apply U.
  exact (proj1 Ha (Powerset_squash_intro@{o} (reflexivity (f a)))).
Defined.

Example sets_cogenerator_untruncate_obj@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) :
  cog_obj (Sets_Cogenerator_untruncate U : Cogenerator Sets@{o so}) tt
    = Powerset_Prop_truth@{o} := eq_refl.

(* * ** Under [IEM]: truth values in [poly_bool] / * ** 在 [IEM] 中：[poly_bool] 的真值 *)

(* The characteristic map of the point [y0], decided by [E]. / 由 [E] 决定的点 [y0] 的特征图。 *)
Definition sets_bool_char@{o so +| o < so +} {Y : SetoidObject@{o o}}
  (E : IEM@{o}) (y0 : carrier Y) : Y ~{Sets@{o so}}~> BoolSetoid@{o}.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier Y) (is_setoid Y) poly_bool@{o} (is_setoid BoolSetoid@{o})
       (fun b => match E (@equiv _ (is_setoid Y) y0 b) with
                 | Datatypes.inl _ => ptrue@{o}
                 | Datatypes.inr _ => pfalse@{o}
                 end) _).
  intros b b' Hbb'; simpl.
  destruct (E (y0 ≈ b)) as [h|n], (E (y0 ≈ b')) as [h'|n']; try reflexivity.
  - destruct (n' (transitivity h Hbb')).
  - destruct (n (transitivity h' (symmetry Hbb'))).
Defined.

Definition Sets_Cogenerator_IEM@{c o so +| o < so +}
  (E : IEM@{o}) : Cogenerator@{c so o} Sets@{o so}.
Proof.
  refine (@Build_Cogenerator Sets@{o so} unit (fun _ => BoolSetoid@{o}) _).
  intros x y f g H a.
  pose proof (H tt (sets_bool_char E (f a)) a) as Ha.
  simpl in Ha.
  destruct (E (f a ≈ f a)) as [_|n]; [|destruct (n (reflexivity _))].
  destruct (E (f a ≈ g a)) as [h|_]; [exact h|discriminate Ha].
Defined.

Example sets_cogenerator_IEM_obj@{o so +| o < so +} (E : IEM@{o}) :
  cog_obj (Sets_Cogenerator_IEM E : Cogenerator Sets@{o so}) tt
    = BoolSetoid@{o} := eq_refl.

(* * ** Unconditionally, but large: every object tested by its identity / * ** 无条件，但大型：每个对象都通过其身份进行测试 *)

Definition Sets_Cogenerator_large@{c o so +| o < so, o < c +} :
  Cogenerator@{c so o} Sets@{o so}.
Proof.
  refine (@Build_Cogenerator Sets@{o so} SetoidObject@{o o} (fun Y => Y) _).
  intros x y f g H a.
  exact (H y (@id Sets@{o so} y) a).
Defined.

(** ** The condition is genuine / ** 这一状况是真实的 *)

(*
 A family of copies of the terminal object never cogenerates [Sets]:
 every two arrows into it agree, while the identity and negation of the
 two-element setoid differ. 

 --------
 终端对象的一族副本从不共生成 [Sets]：每两个箭头指向它时都一致，而二元集合等价类的恒等映射和取反映射却不同。
*)
Lemma Sets_terminal_not_cogenerates@{c o so +| o < so +} (I : Type@{c})
  (H : ∀ (x y : SetoidObject@{o o}) (f g : x ~{Sets@{o so}}~> y),
         (∀ (j : I)
            (k : y ~{Sets@{o so}}~> @terminal_obj Sets@{o so} Sets_Terminal),
            k ∘ f ≈ k ∘ g) → f ≈ g) : False.
Proof.
  apply Sets_two_arrows.
  apply H; intros j k.
  exact (@one_unique Sets@{o so} Sets_Terminal _ _ _).
Qed.
