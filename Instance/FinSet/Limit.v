(*
   * * FinSet is finitely complete

   Mac Lane, Categories for the Working Mathematician, 2nd ed., §V.1
   Exercise 4 (book p. 112, `maclane:V.1:ex4`): the category of finite
   sets has all finite limits.  nLab: https://ncatlab.org/nlab/show/FinSet
   and https://ncatlab.org/nlab/show/equalizer.  In this library the
   finite sets are the skeleton [FinSet] of Instance/FinSet.v — objects
   the naturals, arrows the functions [Fin.t m → Fin.t n] under pointwise
   Leibniz equality — which already had a terminal object
   ([FinSet_Terminal], the numeral [1]), binary products
   ([FinSet_Cartesian], the numeral [m * n] under the positional codec of
   Instance/FinSet/Product.v) and pullbacks ([FinSet_Pullbacks],
   Instance/FinSet/Classifier.v), but no equalizer of any kind: before
   this file no constant anywhere in the tree had type
   [HasEqualizers FinSet] (a tree-wide grep for that phrase finds nothing),
   and the string “qualizer” occurs under Instance/FinSet* exactly once,
   as prose (Instance/FinSet/Subsets.v).

   WHAT IS DELIVERED.
   (A) [FinSet_HasEqualizers : HasEqualizers FinSet], NATIVE and
   COMPUTING.  The equalizer of [f g : Fin.t m → Fin.t n] is the counted
   sub-object of agreement: the Boolean predicate [finset_eq_pred f g x
   := fin_eqb (f x) (g x)], its count [FinSet_equalizer_obj f g :=
   fin_countP (finset_eq_pred f g)] as the object, its un-ranking
   [FinSet_equalizer_incl := fin_select _] as the inclusion, and the
   rank [fin_rank] of a fork's values as the mediator
   ([FinSet_equalizer_med]).  The universal property
   [FinSet_IsEqualizer f g : @IsEqualizer FinSet m n f g _ _]
   (Structure/Equalizer/Fork.v's record) is closed by
   Instance/FinSet/Classifier.v's three codec lemmas [fin_select_sat],
   [fin_select_rank] and [fin_select_inj] together with [fin_eqb_eq]
   and [fin_eqb_refl]; nothing about [Fin.t] is proved here beyond
   the one-line [finset_eq_pred_true].  The construction is strictly
   simpler than [FinSet_Pullbacks]'s, which it mirrors: no pair codec
   is needed, so no [fin_unpair] layer.
   (B) [FinSet_FinitelyComplete : @FinitelyComplete FinSet], the
   quantified statement of Structure/Limit/Finite.v — a [Limit]
   for EVERY functor out of EVERY [FiniteCategory]-witnessed shape, the
   reading the issue's reviewer note asks for, not a bundle of named
   shapes — as ONE application of Mac Lane §V.2 Corollary 1 in the
   form #417 landed it: [finitely_complete_from_generators
   FinSet_Terminal FinSet_Cartesian FinSet_HasEqualizers].  The
   generators are FinSet's OWN: its numeral-[1] terminal object, its
   numeral-[m * n] products and the native equalizer above.
   (C) COMPUTATION, seven [eq_refl] examples — five at one parallel pair
   [3 ⇉ 2] agreeing at exactly two points: the equalizer object is the
   numeral [2], its inclusion selects the first and third points, the
   class's chosen object reads back as [2] through [`1 (equalizer f
   g)], the mediator of a one-point fork is the second point of the
   equalizer — and the two headline conversions through the GENERAL
   machinery: the terminal object recovered from the EMPTY finite
   limit, [terminal_obj (FinitelyComplete_Terminal
   FinSet_FinitelyComplete)], IS the numeral [1] by conversion
   ([FinSet_FinitelyComplete_terminal_computes]), and the finite limit
   over the parallel-pair SHAPE [Parallel] at [APair f g] — built by
   Finite.v's [finite_limit] out of three finite products and two
   equalizers, not by the equalizer instance directly — IS the numeral
   [2] ([FinSet_FinitelyComplete_parallel_computes]).  Both are
   MEASURED against the alternative: the same two statements about the
   pullback route [finitely_complete_of_pullbacks_terminal
   FinSet_Pullbacks FinSet_Terminal] and its equalizer
   [HasEqualizers_of_HasPullbacks_Terminal FinSet_Pullbacks] are
   REFUSED at [eq_refl], [lazy] leaving a [fin_countP] over a predicate
   that tests [unique_obj (FinSet_Pullbacks_obligation_2 …)], the
   pullback UMP that [Program] closed opaquely (the probe pins both).

   RELATION TO WHAT EXISTED, AND THREE STALE PREMISES OF THE ISSUE.
   Test/ProbeFinite417.v already carried a [FinSet_FinitelyComplete]
   at probe strength, by the pullback route, and its N10 records that the
   route does not compute; it is renamed there to
   [FinSet_FinitelyComplete_pb] so that this file owns the pinned name
   (the only collision over the nineteen names: one definition and three
   uses), and its N10 note now says which route it is about.  This file's
   [FinSet_FinitelyComplete_terminal_computes] is the first COMPUTING
   witness of finite completeness in the tree, which corrects
   Structure/Limit/Finite.v's “no computing witness” clause (recorded
   there as a correction, and in its docs/INDEX.md bullet).  The issue's
   “Current state” is stale on three points, each re-measured: there IS
   now a finiteness predicate on [Category] ([FiniteCategory], #417); the
   passage from the generators to all finite limits IS formalized, and the
   three places the issue cites as saying otherwise no longer do —
   Structure/Topos.v and Structure/Regular.v name
   [finitely_complete_of_pullbacks_terminal] as the theorem, and
   Structure/Pullback.v records the reduction as PROVED in
   Structure/Pullback/Reduction.v, one sentence of it alone still scoping
   the general claim away from that file without saying where it lives — so the
   issue's “discharge the disclosure” step edits TWO sentences, each line-
   neutrally: Structure/Pullback.v, and the like-worded
   Structure/Topos/Monadic.v (“no such statement is made anywhere in
   this library”, a leftover of #417) — both now point at Finite.v's
   [FinitelyComplete], built from products and equalizers rather than by shape
   induction — and nothing in the other two files; and the premise that stood,
   “no equalizer”, is the one this file answers.

   WHY NATIVE, AND WHAT IS NOT REQUIRED.  The tree already offered two
   derived equalizers for [FinSet] — [HasEqualizers_of_HasPullbacks_Terminal
   FinSet_Pullbacks] directly, and [@topos_HasEqualizers FinSet
   FinSet_Topos] through Structure/Topos/Monadic.v — and neither is
   written anywhere; both unfold to the same Awodey square over the
   opaque pullback UMP — the topos route IS the pullback-route term, read
   back at [eq_refl] in the probe — so neither computes (the pullback route
   measured above).  A native
   equalizer is what makes the general [finite_limit] REDUCE at [FinSet].
   Instance/FinSet/Pushout.v is deliberately NOT required: it re-declares
   eleven of Classifier.v's codec names at top level without requiring
   Classifier.v ([fin_eqb], [fin_eqb_refl], [fin_eqb_eq], [fin_countP],
   [fin_select], [fin_rank], [fin_select_sat], [fin_select_rank],
   [fin_pred], [fin_FS_inj], [fin_select_inj]), so a file requiring both
   gets shadowing on all eleven; its two extra lemmas [fin_rank_select]
   and [fin_rank_resp] turn out not to be needed.  No hypothesis is taken
   anywhere: [FinSet]'s decidable equality on [Fin.t] is [fin_eqb]'s, and
   every constant is closed under the global context.

   UNIVERSES, MEASURED OFF BOTH BINDER AND BLOCK OVER ALL 19 CONSTANTS.
   Ten of the nineteen carry an EMPTY universe binder (the predicate, the
   object, the inclusion, [finset_eq_pred_true], the three example maps
   and three of the examples — everything stated over [nat] and [Fin.t]
   alone); [FinSet_equalizer_med@{u}] and its example carry one free level
   and no constraint.  [FinSet_IsEqualizer@{u u0 u1 u2 u3} : … IsEqualizer@{u
   u0} …] and [FinSet_HasEqualizers@{u u0 u1 u2 u3} : HasEqualizers@{u u0}
   FinSet@{u u0 u1 u2}] carry exactly one constraint, [Set < u1], which is
   [FinSet]'s own ([FinSet@{u u0 u1 u2} : Category@{u u0 u0}] with
   [Set < u1], measured), inherited and not added.
   [FinSet_FinitelyComplete@{u u0 … u10} : FinitelyComplete@{u u0 u1 u2
   u3}] carries thirty-two constraints, among them [Set < u4] (again
   [FinSet]'s bound), the strict bounds [u1 < u], [u2 < u] and the stdlib
   caps ([Projections], [nat_rect], [case0], [caseS'], [prod_rect],
   [Logic_lemmas.equality]) that [finitely_complete_from_generators]
   and the codec bring; [FinitelyComplete@{u u0 u1 u2 u3} : Category@{u3
   u2 u2} → Type@{u}] itself pins nothing to [Set].  NO universe equation
   anywhere in the nineteen blocks; exactly SEVEN blocks carry a
   word-bounded [Set], every one as the strict lower bound [Set < _] on
   the level [FinSet]'s hom universe sits above, none as a pin.

   COUNTS.  19/19 constants closed under the global context with ZERO
   [Axioms:] lines — 10 [Definition], 1 [Lemma], 1 [Instance], 7
   [Example], no [Program] and so no generated obligation — all in the
   [make print-assumptions] gate FULLY QUALIFIED. ONE [Defined]-terminated
   proof ([FinSet_IsEqualizer]); flipped alone to [Qed] with this file and the
   probe recompiled, this file stays green and the probe breaks at ONE line,
   its universe control [Check FinSet_HasEqualizers@{_ _ _ _ _}] — the
   instance's universe instance drops from five levels to four once the proof
   is opaque — so the flip is load-bearing for nothing else and every
   conversion example survives it; it is kept [Defined] by the data
   convention, packing the mediator. Closure 73 modules excluding self,
   dominated by Structure/Limit/Finite.v's 66 (dropping that one [Require]
   leaves 36); Instance/FinSet/Classifier.v costs 4 at the margin and each of
   the other eleven [Category.*] [Require]s costs 0 (thirteen in all, each
   dropped alone). Zero collisions over the 19 names after the one rename in
   the #417 probe described above, and none over the probe's own
   [p415_]-prefixed names.

   Test/ProbeFinSetLimit415.v mirrors this file's [Require] list and carries 6
   refutation commands = 1 instrument check + 5 negatives of THREE kinds told
   apart by the error TEXT: 2 CONVERSION (the pullback route's equalizer
   object at the example pair against the numeral [2], and its terminal object
   from the empty finite limit against [1] — “cannot unify” with no universe
   clause — each beside the native route's accepted [eq_refl], the two
   terminal apexes also shown isomorphic by [terminal_unique]), 2 TYPING
   ([FinSet_HasEqualizers] ascribed at [HasEqualizers Sets], a plain has-type
   mismatch, and [FinSet_FinitelyComplete] ascribed at [Complete FinSet], a
   has-type mismatch whose unification clause compares the [FiniteCategory J]
   binder with a functor type, beside the accepted
   [Complete_FinitelyComplete]) and 1 UNIVERSE (the instance at hom-carrying
   level [Set], “Cannot enforce Set < Set”, the inherited bound, beside the
   bare instance accepted) — each stripped ONE AT A TIME in a copy of the
   whole file and compiled alone with its error read; readbacks at [eq_refl]
   of the class's chosen object, inclusion and universal property against this
   file's three constants, of [FinSet_FinitelyComplete] against its [:=], and
   two more concrete counts ([0] for a pair that never agrees, [3] for a pair
   of equal maps); guard coverage measured mechanically under the plain
   tokenization — comment-stripped, every identifier token inside a
   refutation command other than the keywords and the wildcard — 19
   identifiers inside, 15 also outside, the four exceptions exhaustively the
   sort [Set] (named only by the universe negative), the two names the
   refuted [Example]s declare and the instrument's absent name;
   rename-simulated 4/4 over the target constants the negatives name,
   each rename applied in THIS file only and every break landing on a control
   [Example] of the probe, none inside a refutation command. [make todo] grows
   by 6 lines, ALL in the probe — its 6 refutation commands, no header line
   of it naming the keyword — and this file and the edited #417 probe
   contribute ZERO.

   NOT DELIVERED.  [Complete FinSet] (false as stated over this library's
   [Complete], which quantifies over every small shape; not refuted here
   either); a native coequalizer or [FinitelyCocomplete FinSet] beyond the
   pushout-route witness Test/ProbeFinite417.v keeps; any comparison of
   [finite_limit]'s chosen products with [FinSet_Cartesian]'s, or of its
   chosen equalizer with [equalizer], beyond the two computing examples;
   a bridge from [FinSet_FinitelyComplete] to [FinSet_Topos]'s
   generators; a closed formula [fin_countP (fun _ => true) = n] or
   [FinSet_equalizer_obj f f = m]; naturality of the mediator in [h];
   and nothing registered as an [Instance] except [FinSet_HasEqualizers],
   which carries no hypothesis, is the sibling of [FinSet_Pullbacks] and
   [FinSet_Cartesian], and so may safely resolve. 

   --------
   * * FinSet 是有限完备的Mac Lane，《为在职数学家准备的范畴论》，第2版，第V.1节
   练习4（书第112页，`maclane:V.1:ex4`）：有限集合的范畴具有所有有限极限。nLab: https://ncatlab.org/nlab/show/FinSet 和 https://ncatlab.org/nlab/show/equalizer. 在这个库中，有限集合是 Instance/FinSet.v 的骨架 [FinSet] —— 对象是自然数，箭头是函数 [Fin.t m → Fin.t n] 在逐点莱布尼茨等式下 —— 它已经有终对象（[FinSet_Terminal]，即数字 [1]）、二元积（[FinSet_Cartesian]，即数字 [m * n] 在 Instance/FinSet/Product.v 的位置编码下）以及拉回（[FinSet_Pullbacks]，Instance/FinSet/Classifier.v），但没有任何种类的等化器：在此文件之前，任何树中的常量都没有类型 [HasEqualizers FinSet]（对该短语进行全树 grep 没有找到任何结果），并且字符串 “qualizer” 在 Instance/FinSet* 下恰好出现一次，作为散文（Instance/FinSet/Subsets.v）。交付内容。（A）[FinSet_HasEqualizers : HasEqualizers FinSet]，本地和计算。[f g : Fin.t m → Fin.t n] 的等化器是满足条件的子对象：布尔谓词 [finset_eq_pred f g x := fin_eqb (f x) (g x)]，其计数 [FinSet_equalizer_obj f g := fin_countP (finset_eq_pred f g)] 作为对象，其非排名 [FinSet_equalizer_incl := fin_select _] 作为包含，以及分支值的秩 [fin_rank] 作为中介 ([FinSet_equalizer_med])。通用性质 [FinSet_IsEqualizer f g : @IsEqualizer FinSet m n f g _ _] （Structure/Equalizer/Fork.v 的记录）由 Instance/FinSet/Classifier.v 的三个编解码引理 [fin_select_sat]、[fin_select_rank] 和 [fin_select_inj] 以及 [fin_eqb_eq] 和 [fin_eqb_refl] 完成；关于 [Fin.t] 的内容这里没有证明，除了单行 [finset_eq_pred_true]。该构造严格地比 [FinSet_Pullbacks] 的构造更简单，它是对其的镜像：不需要成对编解码器，因此也不需要 [fin_unpair] 层。(B) [FinSet_FinitelyComplete : @FinitelyComplete FinSet]，即 Structure/Limit/Finite.v 的量化陈述——针对来自每个 [FiniteCategory] 的函子，每个 [FiniteCategory] -见证形状的 [Limit]，正如问题审阅者笔记中要求的阅读方式，而不是命名形状的集合——作为 Mac Lane §V.2 推论 1 的一次应用，以 #417 的形式实现：[finitely_complete_from_generators FinSet_Terminal FinSet_Cartesian FinSet_HasEqualizers]。生成元是 FinSet 自身的：其数值 [1] 终对象、数值 [m * n] 积以及上述原生等化器。(C) 计算，七个 [eq_refl] 例子——其中五个在一个平行对上
   [3 ⇉ 2] 在恰好两个点上相符：等化器对象是数字 [2]，其包含选择第一个和第三个点，该类选择的对象通过 [`1 (equalizer f g)]` 读取回 [2]，一点分叉的中介是等化器的第二个点——以及通过 GENERAL 机制的两个主要转换：从 EMPTY 有限极限恢复的终对象，[terminal_obj (FinitelyComplete_Terminal FinSet_FinitelyComplete)]，通过转换 ([FinSet_FinitelyComplete_terminal_computes]) 是数字 [1]，以及在平行对形状 [Parallel] 在 [APair f g] 上的有限极限——由 Finite.v 的 [finite_limit] 通过三个有限积和两个构建均衡器，而不是直接由均衡器实例 —— 是数字 [2]（[FinSet_FinitelyComplete_parallel_computes]）。两者都是相对于替代方案进行衡量的：关于回拉路线 [finitely_complete_of_pullbacks_terminal FinSet_Pullbacks FinSet_Terminal] 及其等化器 [HasEqualizers_of_HasPullbacks_Terminal FinSet_Pullbacks] 的同两条声明在 [eq_refl]、[lazy] 被拒绝，留下一个 [fin_countP] 对一个测试 [unique_obj (FinSet_Pullbacks_obligation_2 …)] 的谓词，而回拉 UMP [Program] 不透明地闭合（探针两者都固定）。与已有内容的关系，以及该问题的三个陈旧前提。Test/ProbeFinite417.v 已经在探针强度下通过回拉路径携带了一个 [FinSet_FinitelyComplete]，其 N10 记录显示该路径无法计算；那里将其重命名为 [FinSet_FinitelyComplete_pb]，以便该文件拥有固定名称（在十九个名称中唯一的冲突：一个定义和三个使用），其 N10 注释现在说明了是哪个路径。该文件的 [FinSet_FinitelyComplete_terminal_computes] 是树中有限完备性第一个 COMPUTING 证据，它修正了 Structure/Limit/Finite.v 中的“无计算证据”条款（在该处作为修正记录，并在其 docs/INDEX.md 要点中）。该问题的“当前状态”在三个点上已经过时，每一点都重新测量过：现在在[Category]（[FiniteCategory]，第417号）上确实有一个有限性谓词；从生成元到所有有限极限的过程已经形式化，并且该问题引用的三处说法不再如此——Structure/Topos.v和Structure/Regular.v将[finitely_complete_of_pullbacks_terminal]作为定理命名，而Structure/Pullback.v在Structure/Pullback/Reduction.v中记录了归约已被证明，仅一句话仍然将一般性声明从该文件中隔离开而未说明其所在位置——因此该问题的“解除披露”步骤编辑了两句话，每行保持中性：Structure/Pullback.v，以及措辞相似的Structure/Topos/Monadic.v（“在此库中没有任何这样的陈述”，这是第417号遗留问题）——两者都now 指向 Finite.v 的点 [FinitelyComplete]，是由积和等化器构建的，而不是通过形状归纳——另外两个文件中没有任何内容；而存在的前提，“没有等化器”，就是这个文件所回答的。

   为什么是本地的，以及什么是不必要的。该树已经为 [FinSet] 提供了两个派生的等化器——[HasEqualizers_of_HasPullbacks_Terminal FinSet_Pullbacks] 直接提供，以及通过 Structure/Topos/Monadic.v 提供的 [@topos_HasEqualizers FinSet FinSet_Topos]——并且这两个都未在任何地方显式书写；两者都展开为在不透明的拉回 UMP 上的相同 Awodey 方形——拓扑路线就是拉回路线的术语，在 [eq_refl] 探针中读取——所以两者都不计算（上面测量的拉回路线）。本地等化器是让通用 [finite_limit] 在 [FinSet] 进行 REDUCE 的东西。Instance/FinSet/Pushout.v 特意未被要求：它在顶层重新声明了 Classifier.v 的十一种编解码器名称而不需要 Classifier.v（[fin_eqb], [fin_eqb_refl], [fin_eqb_eq], [fin_countP], [fin_select], [fin_rank], [fin_select_sat], [fin_select_rank], [fin_pred], [fin_FS_inj], [fin_select_inj]），因此一个同时需要两者的文件会在所有十一项上产生遮蔽；它的两个额外引理 [fin_rank_select] 和 [fin_rank_resp] 结果发现并不需要。任何地方都没有采用假设：[FinSet] 在 [Fin.t] 上的可判定等式是 [fin_eqb] 的，并且每个常量在全局上下文下都是封闭的。宇宙，测量覆盖了所有19个常数的绑定器和区块。19个常数中有十个包含一个空的宇宙绑定器（谓词、对象、包含、[finset_eq_pred_true]、三个示例映射和三个示例——所有内容仅在[nat]和[Fin.t]上陈述）；[FinSet_equalizer_med@{u}]及其示例带有一个自由层且没有约束。[FinSet_IsEqualizer@{u u0 u1 u2 u3} : … IsEqualizer@{u u0} …] 和 [FinSet_HasEqualizers@{u u0 u1 u2 u3} : HasEqualizers@{u u0} FinSet@{u u0 u1 u2}] 精确地带有一个约束，[Set < u1]，这个约束是[FinSet]自身的（[FinSet@{u u0 u1 u2} : Category@{u u0 u0}] 与 [Set < u1] 测量），是继承而非新增的。[FinSet_FinitelyComplete@{u u0 … u10} : FinitelyComplete@{u u0 u1 u2 u3}] 承载了三十二个约束，其中包括 [Set < u4]（再次指 [FinSet] 的约束）、严格约束 [u1 < u]、[u2 < u] 以及标准库上限（[Projections]、[nat_rect]、[case0]、[caseS']、[prod_rect]、[Logic_lemmas.equality]）由 [finitely_complete_from_generators] 和编解码器带来；[FinitelyComplete@{u u0 u1 u2 u3} : Category@{u3 u2 u2} → Type@{u}] 本身没有将任何内容固定到 [Set]。十九个模块中没有任何宇宙方程；正好有七个模块承载了字界 [Set]，每个模块都是层 [FinSet] 的同构宇宙上方的严格下界 [Set < _]，没有作为固定点。计数。19/19 个常量在全局上下文下封闭，具有零行 — 10 个 [Definition]，1 个 [Lemma]，1 个 [Instance]，7 个 [Example]，没有 [Program]，因此没有生成义务 — 全部在 [make print-assumptions] 门中完全限定。一个 [Defined] 终止的证明（[FinSet_IsEqualizer]）；单独翻转到 [Qed] 并重新编译探针，这个文件保持绿色，而探针在一行处断开，其宇宙控制 [Check FinSet_HasEqualizers@{_ _ _ _ _}] — 一旦证明是不可见的，该实例的宇宙实例级别从五级下降到四级 — 因此此翻转对其他没有负担，并且每个转换示例都能存活；它由数据约定保持 [Defined]，打包调解器。闭包 73 个模块（不包括自身），由 Structure/Limit/Finite.v 的 66 个主导（去掉那个 [Require] 后剩 36 个）；Instance/FinSet/Classifier.v 在边际上的成本为 4，而其他十一 个 [Category.*] [Require] 的成本为 0（总共十三个，每个单独删除）。在上述 #417 探查中的一次重命名之后，19 个名称中没有冲突，并且探查自身以 [p415_] 前缀的名称也没有冲突。Test/ProbeFinSetLimit415.v 反映了此文件的 [Require] 列表，并包含 6 个反驳命令 = 1 个工具检查 + 5 个三种类型的否定，通过错误 TEXT 区分：2 个 CONVERSION（例子对中的拉回路径的齐次对象对应 [2] ，以及来自空有限极限的终端对象对应 [1] — “无法统一”，没有宇宙条款 — 每个都在本地路径接受的 [eq_refl] 旁边，两个终端顶点也显示同构由 [terminal_unique] 证明）, 2 个 TYPING（ [FinSet_HasEqualizers] 在 [HasEqualizers Sets] 处被指定，一个普通的类型不匹配，ZWZ120WZZ 在 [Complete FinSet] 处被指定，一个类型不匹配，其统一条款将 [FiniteCategory J] 绑定与函子类型比较，旁边是接受的 [Complete_FinitelyComplete] ）以及 1 个 UNIVERSE（实例在 hom-carryi级别 [Set]，“无法强制执行 Set < Set”，继承的界限，旁边的裸实例被接受）——每次在整个文件的副本中单独剥离并单独编译，其错误被读取；在类选择对象的 [eq_refl] 中读取回，针对该文件的三个常量的包含性和通用属性，[FinSet_FinitelyComplete] 对其 [:=] ，以及另外两个具体计数（[0] 对永不一致的对，[3] 对相等映射对）；在普通标记化下机械测量守卫覆盖——注释被剥除，每个在反驳命令内的标识符标记，除了关键字和通配符——里面有 19 个标识符，外面有 15 个，四个例外完全属于 [Set] 类型（只由宇宙负数命名），两个名称被驳斥的 [Example] 声明以及仪器的缺失名称；
   在目标常量上模拟重命名 4/4 的否定名称，每个重命名仅在本文件中应用，并且每次断点都落在探针的控制 [Example] 上，驳斥命令内部没有。[make todo] 增长了 6 行，都在探针中——它的 6 个反驳命令，没有任何标题行命名关键字——而这个文件和编辑后的 #417 探针贡献为零。未交付。[Complete FinSet]（如本库所述为假，[Complete] 对每一个小形状进行了量化；在此也未被反驳）；一个本地的余等化器或 [FinitelyCocomplete FinSet] 超过 pushout 路径证据 Test/ProbeFinite417.v 所保持的；[finite_limit] 所选产品与 [FinSet_Cartesian] 的产品相比，或其所选的等化器与 [equalizer] 的比较，超出两个计算示例；从 [FinSet_FinitelyComplete] 到 [FinSet_Topos] 生成元的桥梁；一个闭合公式 [fin_countP (fun _ => true) = n] 或 [FinSet_equalizer_obj f f = m]；[h] 中中介的自然性；以及除了 [FinSet_HasEqualizers] 之外，没有注册的 [Instance]，[FinSet_HasEqualizers] 不携带假设，是 [FinSet_Pullbacks] 和 [FinSet_Cartesian] 的同胞，因此可以安全解决。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Limit.Finite.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Classifier.
Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(* * * The equalizer: the counted sub-object of agreement / * * 平衡器：被计数的协议子对象 *)

(*
 The Boolean predicate “f and g agree at x”, decided by the heterogeneous
 [fin_eqb] of Instance/FinSet/Classifier.v; [fin_eqb_eq] turns its [true]
 into Leibniz equality at the common index. 

 --------
 布尔谓词“f 和 g 在 x 上相等”，由 Instance/FinSet/Classifier.v 的异质 [fin_eqb] 决定；[fin_eqb_eq] 将其 [true] 转换为共同索引下的莱布尼茨等式。
*)
Definition finset_eq_pred {m n : nat} (f g : Fin.t m → Fin.t n) :
  Fin.t m → bool := fun x => fin_eqb (f x) (g x).

(* The equalizer object counts the agreements; the inclusion un-ranks. / 均衡器对象计算协议；包容性取消排名。 *)
Definition FinSet_equalizer_obj {m n : nat} (f g : Fin.t m → Fin.t n) : nat :=
  fin_countP (finset_eq_pred f g).

Definition FinSet_equalizer_incl {m n : nat} (f g : Fin.t m → Fin.t n) :
  Fin.t (FinSet_equalizer_obj f g) → Fin.t m :=
  fin_select (finset_eq_pred f g).

Lemma finset_eq_pred_true {m n : nat} (f g : Fin.t m → Fin.t n) (x : Fin.t m) :
  f x = g x → finset_eq_pred f g x = true.
Proof. intros H; unfold finset_eq_pred; rewrite H; apply fin_eqb_refl. Qed.

(* The mediator of a fork [h] ranks each value of [h], which the fork equation certifies to satisfy the predicate. / 分支 [h] 的中介对 [h] 的每个值进行排序，分支方程证明这些值满足谓词。 *)
Definition FinSet_equalizer_med {m n : nat} (f g : Fin.t m → Fin.t n)
  {z : nat} (h : Fin.t z → Fin.t m) (Hh : ∀ i, f (h i) = g (h i)) :
  Fin.t z → Fin.t (FinSet_equalizer_obj f g) :=
  fun i => fin_rank (finset_eq_pred f g) (h i)
                    (finset_eq_pred_true f g (h i) (Hh i)).

Definition FinSet_IsEqualizer {m n : nat} (f g : Fin.t m → Fin.t n) :
  @IsEqualizer FinSet m n f g (FinSet_equalizer_obj f g)
    (FinSet_equalizer_incl f g).
Proof.
  unshelve refine {| fork_eq := _; eq_desc := fun z h Hh => _ |}.
  - intro i; simpl.
    apply fin_eqb_eq. exact (fin_select_sat (finset_eq_pred f g) i).
  - unshelve refine {| unique_obj := FinSet_equalizer_med f g h Hh |}.
    + intro i; simpl. exact (fin_select_rank (finset_eq_pred f g) (h i) _).
    + intros v Hv i; simpl in *.
      unfold FinSet_equalizer_med.
      apply (fin_select_inj (finset_eq_pred f g)).
      rewrite (fin_select_rank (finset_eq_pred f g) (h i)). symmetry. apply Hv.
Defined.

#[export] Instance FinSet_HasEqualizers : HasEqualizers FinSet :=
  @Build_HasEqualizers FinSet
    (fun (m n : nat) (f g : Fin.t m → Fin.t n) =>
       (FinSet_equalizer_obj f g;
        (FinSet_equalizer_incl f g; FinSet_IsEqualizer f g))).

(* * * Finite completeness, by Mac Lane V.2 Corollary 1 / * * 有限完备性，作者：Mac Lane V.2 推论 1 *)

Definition FinSet_FinitelyComplete : @FinitelyComplete FinSet :=
  finitely_complete_from_generators FinSet_Terminal FinSet_Cartesian
    FinSet_HasEqualizers.

(** * Computation / * 计算 *)

(* A parallel pair [3 ⇉ 2] agreeing exactly at the first and third points. / 一对平行的 [3 ⇉ 2]，在第一个和第三个点完全一致。 *)
Definition finset_eq_example_f : Fin.t 3 → Fin.t 2 := fun _ => Fin.F1.
Definition finset_eq_example_g : Fin.t 3 → Fin.t 2 :=
  fun i => match i with Fin.FS Fin.F1 => Fin.FS Fin.F1 | _ => Fin.F1 end.

Example FinSet_equalizer_obj_computes :
  FinSet_equalizer_obj finset_eq_example_f finset_eq_example_g = 2%nat
  := eq_refl.

Example FinSet_equalizer_incl_computes_0 :
  FinSet_equalizer_incl finset_eq_example_f finset_eq_example_g Fin.F1 = Fin.F1
  := eq_refl.

Example FinSet_equalizer_incl_computes_1 :
  FinSet_equalizer_incl finset_eq_example_f finset_eq_example_g (Fin.FS Fin.F1)
  = Fin.FS (Fin.FS Fin.F1)
  := eq_refl.

Example FinSet_equalizer_readback :
  `1 (@equalizer FinSet _ _ _ finset_eq_example_f finset_eq_example_g) = 2%nat
  := eq_refl.

Definition finset_eq_example_h : Fin.t 1 → Fin.t 3 :=
  fun _ => Fin.FS (Fin.FS Fin.F1).

Example FinSet_equalizer_med_computes :
  FinSet_equalizer_med finset_eq_example_f finset_eq_example_g
    finset_eq_example_h (fun _ => eq_refl) Fin.F1
  = Fin.FS Fin.F1
  := eq_refl.

(*
 The terminal object recovered from the EMPTY finite limit is the numeral
 [1] by conversion on this route. 

 --------
 从空有限极限恢复的终端对象是通过这一路径的转换得到的数字 [1]。
*)
Example FinSet_FinitelyComplete_terminal_computes :
  @terminal_obj FinSet (FinitelyComplete_Terminal FinSet_FinitelyComplete)
  = 1%nat
  := eq_refl.

(*
 The finite limit over the parallel-pair SHAPE at the example — built by
 [finite_limit] out of three finite products and two equalizers, not by
 the equalizer instance directly — is the numeral [2] by conversion. 

 --------
 在这个例子中，平行对 SHAPE 上的有限极限——是由 [finite_limit] 用三个有限积和两个等化器构建的，而不是直接由等化器实例构建的——通过转换得到的是数字 [2]。
*)
Definition finset_eq_example_diagram : Parallel ⟶ FinSet :=
  @APair FinSet 3%nat 2%nat finset_eq_example_f finset_eq_example_g.

Example FinSet_FinitelyComplete_parallel_computes :
  vertex_obj[@limit_cone Parallel FinSet finset_eq_example_diagram
    (FinSet_FinitelyComplete Parallel Parallel_FiniteCategory
       finset_eq_example_diagram)]
  = 2%nat
  := eq_refl.
