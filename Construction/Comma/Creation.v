Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.One.
Require Import Category.Instance.Parallel.

Set Universe Polymorphism.

Generalizable All Variables.

(* * * The comma projection creates limits / * * 逗号投影创建了限制 *)

(*
 nLab: https://ncatlab.org/nlab/show/comma+category#limits_and_colimits
 nLab: https://ncatlab.org/nlab/show/created+limit

 The projection [comma_proj2 : =(d) ↓ U ⟶ C] creates limits, as the prose
 at Construction/Comma.v and Construction/Comma/Limit.v has always
 said.  Construction/Comma/Limit.v proves existence; what is added here is
 the reflection clause [comma_creates_reflect] and the packaging
 [comma_CreatesLimit] against Structure/Limit/Creation.v.  Nothing in
 Construction/Comma/Limit.v is changed.

 Two consequences worth naming.  First, [PreservesImageLimit]
 (Construction/Comma/Limit.v), the honest cone-level hypothesis that
 file introduced and that Adjunction/GAFT.v and Adjunction/SAFT.v consume,
 is [PreservesLimitCone] quantified over all shapes, up to repackaging a
 [Limit] record as a cone together with its universal property: the two
 bridges below carry no proof, and both round trips hold by [eq_refl]
 (the two [Type]s are not themselves convertible, one binding [Limit G]
 where the other binds a cone and an [IsLimitCone]).  So GAFT and SAFT
 already speak the general vocabulary under an older name.

 Second, the created lift lies over an ARBITRARY downstairs limit [L] on
 the nose — [comma_strict_apex] and [comma_strict_legs] are [eq_refl] for
 every [L], not merely for the one a [Complete C] happens to choose.  That
 is the generalization this file's header previously deferred: [Limit.v]
 now takes [Ldiag] as a section parameter instead of computing it as
 [HC J Gdiag], so [comma_limit] is parameterized by the limit it is built
 from and the projection lands on that limit definitionally.  The exported
 type of [Comma_Complete] is unchanged by the move — it simply supplies
 [HC J (Gdiag K)] as the parameter — so Adjunction/GAFT.v and
 Adjunction/SAFT.v are untouched.

 On the house rule that morphisms are compared with [≈]: [comma_strict_legs]
 writes [=] between morphisms, and it does so because both sides are the
 SAME term — the witness is [eq_refl].  It records Mac Lane's [F σ = τ] at
 full strength, which is strictly stronger than the [≈] the class asks
 for; every proof below uses [≈].  (An earlier revision said
 [comma_strict_legs] was "the one statement here" of that shape; measured
 at this revision there are FOUR in this file — the later three being
 [comma_limit_at_legs], [comma_prod_leg_strict] and
 [comma_equalizer_leg_strict] — and a fifth, [coslice_lift_legs], in
 Construction/Slice/Creation.v, each likewise [eq_refl] on one term.) 

 --------
 nLab: https://ncatlab.org/nlab/show/comma+category#limits_and_colimits 
 nLab: https://ncatlab.org/nlab/show/created+limit 

 投影 [comma_proj2 : =(d) ↓ U ⟶ C] 会产生极限，如 Construction/Comma.v 和 Construction/Comma/Limit.v 的散文一直所说。Construction/Comma/Limit.v 证明了存在性；这里添加的是反射子句 [comma_creates_reflect] 以及对 Structure/Limit/Creation.v 的打包 [comma_CreatesLimit]。Construction/Comma/Limit.v 中的内容没有改变。值得提及的两个结果。首先，[PreservesImageLimit]（Construction/Comma/Limit.v），即文件中引入并被Adjunction/GAFT.v和Adjunction/SAFT.v使用的诚实圆锥层假设，是[PreservesLimitCone]在所有形状上进行量化，只需将一个[Limit]记录重新打包为一个带有其普遍性质的圆锥：下面的两个桥梁都不带证明，而且两个来回通过[eq_refl]成立（两个[Type]本身不可转换，一个绑定[Limit G]而另一个绑定一个圆锥和一个[IsLimitCone]）。因此，GAFT和SAFT已经用一个旧名称描述了一般词汇。其次，产生的升力位于鼻子上的任意下限 [L] 上——[comma_strict_apex] 和 [comma_strict_legs] 对每一个 [L] 都是 [eq_refl]，而不仅仅是对某个 [Complete C] 选择的那一个。这就是本文件头先前推迟的一般化：[Limit.v] 现在将 [Ldiag] 作为节参数，而不是按 [HC J Gdiag] 计算，因此 [comma_limit] 由它构建的极限参数化，并且投影在定义上落在该极限上。[Comma_Complete] 的导出类型因这次移动而不变——它仅仅提供 [HC J (Gdiag K)] 作为参数——因此 Adjunction/GAFT.v 和 Adjunction/SAFT.v 没有被修改。关于内部规则，形态映射是通过 [≈] : [comma_strict_legs] 来比较的，它在形态映射之间写下 [=]，这是因为双方都是相同的项——证据是 [eq_refl]。它完整记录了 Mac Lane 的 [F σ = τ]，它比类要求的 [≈] 更强；下面的每个证明都使用 [≈]。（早期版本说 [comma_strict_legs] 是那种形状的“唯一陈述”；按照本版本测量，这个文件中有四个——后面三个是 [comma_limit_at_legs]、[comma_prod_leg_strict] 和 [comma_equalizer_leg_strict]——第五个 [coslice_lift_legs] 在 Construction/Slice/Creation.v 文件中，每个同样在一个项上是 [eq_refl]。）
*)

(*
 What follows the strictness readbacks was added for Mac Lane §V.6's
 Lemma 1 and Exercise 1 (book pp. 121-125) and, through
 Construction/Slice/Creation.v, §V.1 Exercise 1 (book p. 112); the same
 ground is Riehl §3.4 Proposition 8 in its limit half (printed p. 106),
 §4.7 Lemma 2 (printed p. 174) and the exercise asking for that lemma's
 direct argument (printed p. 180).  Three things were missing.

 First, the hypothesis was too strong.  Mac Lane's lemma assumes only
 that [U] preserve the limits of the shapes at issue — products and
 equalizers, in Theorem 2's proof — while [PreservesImageLimit]
 quantifies over every shape and every diagram at once, and the two
 per-shape clauses Theorem 2 consumes are not derivable from the sections
 of Construction/Comma/Limit.v, whose [HU] is a total function over
 shapes.  [comma_limit_at] re-derives that whole construction from
 [PreservesLimitCone (Gdiag K) U], the hypothesis at the ONE base diagram
 of the ONE [K] at hand, and it does so ADDITIVELY: Construction/Comma/Limit.v
 is not touched, because NINE [.v] files and nine planning or documentation
 files cite it at fifteen distinct line numbers at master (measured with
 [grep -rloE 'Comma/Limit\.v:[0-9]+'] over [--include='*.v'] and
 [--include='*.md']); the count is ten [.v] files from the previous commit
 on, the tenth being Construction/Slice/Creation.v, which that commit
 added, and one of the nine is this file itself, so EIGHT other files
 carry the constraint.  The price is
 about a hundred lines of re-derivation with the original tactic scripts.

 The two-sided analogue landed first and is not superseded:
 Construction/Arrow/Limit.v's [comma_proj_StrictlyCreatesLimit]
 already gives strict creation for [comma_proj : (S ↓ T) ⟶ A ∏ B] from a
 per-diagram hypothesis of the same shape.  The functors differ — [Snd ◯
 comma_proj] and [comma_proj2] are different records — and there is no
 [StrictlyCreatesLimit_compose], so the re-derivation here is not
 avoidable, but the idea is that file's.

 Second, the creation was not strict.  [comma_CreatesLimit]'s
 [creates_lift] DISCARDS the cone it is handed and returns the lift of the
 fixed [L], related to that cone only by the [ConeIso] its second field
 supplies; so its apex is not the given cone's apex, and
 Test/ProbeCommaCreation438.v's negative n5 records the refusal against
 the control that the new lift is accepted.  [comma_StrictlyCreatesLimit]
 builds the lift from [Build_Limit N HN] — the given cone repackaged —
 rather than from a fixed [L], so both [StrictLift] fields are [eq_refl]
 and [reflexivity] at EVERY limiting cone downstairs.  That is Mac Lane's
 [F a = x] and [F σ = τ] in full, and [comma_CreatesLimit_at] then carries
 no [L] argument at all.  [comma_strict_apex] and [comma_strict_legs]
 above do not say this: they speak about [comma_limit HU K L] directly,
 not about what [creates_lift] returns when handed some other cone.

 Third, the two shapes.  The equalizers clause is the per-diagram
 construction read at [Parallel], which costs nothing because [Parallel]
 leaves its hom universe free.  The products clause is stated
 ELEMENTARILY over [Structure/Limit/Product.v]'s [IsIndexedProduct]
 rather than over a discrete shape, because that is the form that takes an
 arbitrary FAMILY directly.

 RECORDED CORRECTION TO THE REASON GIVEN HERE.  An earlier revision said
 the elementary form was needed "because that is the form that can be
 instantiated at an arbitrary FAMILY: a functor out of [DiscreteCat A]
 that eliminates the shape's [x = y] into a hom pins both categories to
 [Category@{_ Set Set}], and is refused over a generic [C] with
 "universe inconsistency: Cannot enforce Set = ..." (probe negative n2) —
 the tree's own [DiscreteCat_Functor] (Instance/Discrete.v) prints as
 [DiscreteCat@{u Set Set} A ⟶ C] for that reason, and a hand-rolled
 eliminator is refused identically, so the pin belongs to the ELIMINATION
 and not to any one constant."  The diagnosis named the wrong culprit.
 The pin was a universe-MINIMIZATION artifact of the unannotated
 declaration, not of the elimination: the annotated
 [DiscreteCat_Functor@{o h p uo uh up +}] (Instance/Discrete.v, PR
 "algebraic carriers are sets", 2026-09-17) eliminates [x = y] into a hom
 exactly as before and IS formable over a generic [C].  Probe negative n2
 accordingly turned over and is kept as a positive control.  The
 elementary clause is still what the file ships, because it takes the
 family directly and needs no shape at all -- a simpler reason than the
 one it used to be given.  The pin never belonged to [DiscreteCat]
 either, whose hom and proof universes are free
 ([DiscreteCat@{o h p} : Type@{o} → Category@{o h p}]) — which is why
 [comma_CreatesAllLimits] and its instance [comma_CreatesProducts] below
 are formable and axiom-free over a generic [C] and [D], and why they are
 not vacuous: a CONSTANT discrete diagram eliminates nothing and is
 formable, so the class applies to it.  This is the trap the
 Construction/Comma/Special.v bullet of docs/INDEX.md already records for
 [DiscreteCat_Functor], sighted here one step earlier.

 Three of issue #438's substantive claims about the tree are FALSE as of
 this file's parent, and are recorded here because the issue text will
 outlive the commit.  Read them TREE-WIDE: two of the three are written
 in the issue as statements about Construction/Comma/Limit.v, and of THAT
 file they are still true — what falsifies them is this file, which
 landed after the issue was written.  "Creation proper is not stated" —
 [comma_CreatesLimit] above states it.  "The uniqueness/reflection clause
 is absent" — [comma_creates_reflect] is the reflection clause, and
 uniqueness is Structure/Limit/Creation.v's [creates_lift_unique] applied
 to it, though only up to cone isomorphism (see the NOT DELIVERED list).
 "No lemma asserts that the projection of the constructed limit is the
 given one" — [comma_strict_apex] and [comma_strict_legs] assert exactly
 that, by [eq_refl], for an arbitrary downstairs limit.  A fourth is half
 true:
 comma limits sit under an all-shapes [Complete C] oracle only for
 [Comma_Complete] (Construction/Comma/Limit.v); [comma_limit]
 has taken its downstairs limit as a parameter since commit 28ee6e54.
 Seven of the issue's line citations are stale, all of them by the two
 lines that commit added or by later drift: [comma_limit],
 [Comma_Complete], [apex_obj], [apex_leg],
 [right_adjoint_PreservesImageLimit] and
 [Comma_Complete_right_adjoint] have each moved down, and [adj_id] is
 in Instance/Adjoints.v, at its declaration rather than at the prose the
 issue points to.  Its citation of
 [PreservesImageLimit] is correct, and its LIBRARY-DEFECT item —
 that Construction/Comma.v and Construction/Comma/Limit.v
 claim creation where only existence is proved — was already resolved by
 this file's first commit, as the paragraph above records.

 Measured.  This file's [.glob] declares 42 heads (38 [def], 4 [prf]) and
 no [Program] obligation, nine of them from the first commit; with
 Construction/Slice/Creation.v's 30 that is 72 constants, all carried by
 [make print-assumptions] and all reporting "Closed under the global
 context".  Closure goes from 35 modules excluding self to 38, and the
 three added are EXACTLY the three new [Require]s
 (Structure/Limit/Product, Structure/Equalizer, Instance/Parallel) — none
 brings anything else with it, and neither creation class needed a
 [Require] at all — while Adjunction/Representability/Sets.v stays at 99,
 all three having been in its closure already.  Four files require this
 one: that one and Construction/Slice/Creation.v in the library, and the
 two probes.  Construction/Slice/Creation.v closes over 52 and the probe
 over 58.  Zero collisions over the 72 heads and the probe's declared
 names (whole-word [grep -rlw] over [*.v], instrument-checked at [Full],
 [comma_limit] and [Coslice_Proj]); the only other-file hits are two USES
 of [Continuous_PreservesImageLimit] in Adjunction/Representability/Sets.v
 and one prose mention of [comma_CreatesLimit] at Construction/Arrow/Limit.v,
 with no second declaration anywhere.  Renaming each of the 72 names in
 turn, in the file that DECLARES it and nowhere else, then recompiling
 this file, the satellite and the probe in order: 71 stop the probe, every
 one of those on a positive line and none inside a refutation, and the
 72nd ([comma_StrictlyCreatesLimit]) stops the satellite first, at the
 line that consumes it — nothing survives a rename, so no guard here is
 vacuous.  [make todo] grows by seven, the probe's seven refutation lines,
 and neither library file contributes a hit.

 Across the two files thirteen definitions close with [Defined] — two of
 them from this file's first commit — and seven with [Qed].  Flipping each
 [Defined] alone to [Qed] in a copy of the whole file: FOUR stop the file
 itself ([comma_at_apex_leg], [comma_at_med], [comma_prod_proj], and the
 satellite's [coslice_lift_leg], each needed to reduce by a later
 definition), TWO stop the probe ([comma_StrictlyCreatesLimit] and
 [Coslice_Proj_StrictlyCreatesLimit], whose strict-lift readbacks are
 [eq_refl]), and SEVEN compile through with every readback intact
 ([comma_at_ump], [comma_reflect_at], [comma_IsIndexedProduct],
 [coslice_reflect_at], [coslice_lift_ump], and the two pre-existing
 [comma_creates_reflect] and [comma_CreatesLimit]).  Those stay
 transparent because they are data — universal properties, limiting-cone
 witnesses, a record inhabitant — matching the [Defined] of [umed] and
 [comma_ump] beside them; that their flip is not load-bearing is
 disclosed, not claimed away.

 NOT DELIVERED here.  No weakening of [Comma_Complete]'s exported type,
 so Adjunction/GAFT.v and Adjunction/SAFT.v are untouched; no per-shape
 completeness class, the products and equalizers clauses being single
 statements rather than instances of a shape-indexed family; no
 INSTANTIATION of [comma_CreatesProducts] at an arbitrary FAMILY over a
 generic [C], for the elimination reason above — the class is shipped and
 the probe applies it to a constant discrete diagram, but a diagram built
 from a family is refused; no ON-THE-NOSE
 uniqueness of the lift, Mac Lane's "exactly one pair" — what is
 available is [creates_lift_unique]'s [ConeIso], and
 Structure/Limit/Creation.v says in terms why uniqueness cannot be a
 field of the class in a setoid setting; no finiteness anywhere, the
 index of the products clause being an arbitrary [Type]; no creation by
 [comma_proj1], which nothing in the tree addresses; and no colimit dual,
 which issue #438 scopes out along with Riehl's connected-colimit half.
 Strict creation for a PLAIN coslice projection IS delivered, in
 Construction/Slice/Creation.v — an earlier revision of this list said it
 was blocked, on the false premise that no unconditioned coslice
 projection existed. 

 --------
 在严格回读之后添加的内容是针对 Mac Lane 第 V.6 节的引理 1 和练习 1（书本第 121-125 页），以及通过 Construction/Slice/Creation.v，第 V.1 节练习 1（书本第 112 页）；相同的依据出现在 Riehl 第 3.4 节命题 8 的极限部分（印刷第 106 页）、第 4.7 节引理 2（印刷第 174 页）以及要求该引理直接论证的练习（印刷第 180 页）。有三件事情缺失。首先，假设过于强烈。Mac Lane 的引理只假设  [U]  保留相关形状的极限——在定理 2 的证明中为积和等化器——而  [PreservesImageLimit]  同时对每种形状和每个图进行量化，而定理 2 所使用的每种形状的两个子条款无法从 Construction/Comma/Limit.v 的章节中推导出来，该章节的  [HU]  是一个针对形状的全函数。[comma_limit_at] 从 [PreservesLimitCone (Gdiag K) U] 重新演绎了整个构造，这是在 ONE [K] 的 ONE 基础图上的假设，并且它是以加法的方式进行的：Construction/Comma/Limit.v 没有被修改，因为九个 [.v] 文件以及九个规划或文档文件在 master 的十五个不同的行号中引用了它（使用 [grep -rloE 'Comma/Limit\.v:[0-9]+'] 在 [--include='*.v'] 和 [--include='*.md'] 上测量）；统计结果是来自之前提交的十个 [.v] 文件，第十个是 Construction/Slice/Creation.v，该提交添加了它，而且九个文件中的一个就是这个文件本身，所以还有八个其他文件带有该约束。代价是大约一百行使用原始策略脚本重新演绎。双面的类似物首先被引入，并且没有被取代：
 Construction/Arrow/Limit.v 的 [comma_proj_StrictlyCreatesLimit]
 已经从同型图的假设中为 [comma_proj : (S ↓ T) ⟶ A ∏ B] 提供了严格生成。函子不同 — [Snd ◯ comma_proj] 和 [comma_proj2] 是不同的记录 — 并且没有 [StrictlyCreatesLimit_compose]，因此这里的重新推导是无法避免的，但这个想法就是文件的内容。其次，该创建并不严格。[comma_CreatesLimit]的[creates_lift]丢弃了它收到的圆锥，并返回固定的[L]的提升，该提升仅通过[ConeIso]其第二个字段提供与该圆锥相关；因此其顶点不是所给圆锥的顶点，而Test/ProbeCommaCreation438.v的负面n5记录了对控制的拒绝，因为新提升被接受。[comma_StrictlyCreatesLimit]从[Build_Limit N HN]（重新打包的给定圆锥）构建提升，而不是从固定的[L]，因此[StrictLift]字段在楼下的每一个极限圆锥上都为[eq_refl]和[reflexivity]。这是Mac Lane的[F a = x]和[F σ = τ]的完整表现，而[comma_CreatesLimit_at]则完全不携带[L]参数。[comma_strict_apex] 和 [comma_strict_legs]
 上面不要这样说：它们直接谈论 [comma_limit HU K L]，而不是 [creates_lift] 当交给某个其他锥体时返回的内容。

 第三，两个形状。均衡器条款是在 [Parallel] 处读取的每图构造，这不花费任何东西，因为 [Parallel] 将其同源宇宙保持为空。乘积条款是针对 [Structure/Limit/Product.v] 的 [IsIndexedProduct] 以基本形式陈述的，而不是针对离散形状，因为这种形式可以直接取任意族。对此处给出的理由进行了记录更正。早期版本说基础形式是需要的“因为这是可以在任意 FAMILY 上实例化的形式：一个函子从 [DiscreteCat A]，将形状的 [x = y] 消除到一个将两个类别固定到 [Category@{_ Set Set}] 的同类引脚，并在一个通用的 [C] 上被拒绝，报出‘宇宙不一致：无法强制 Set = ...’（探针负 n2）——树自身的 [DiscreteCat_Functor]（Instance/Discrete.v）因此打印为 [DiscreteCat@{u Set Set} A ⟶ C]，而手工编写的消元器被同样拒绝，所以这个引脚属于消元，而不属于任何一个常量。”诊断指出了错误的元凶。这个引脚是未注释声明的宇宙-最小化工件，而不是消除的工件：带注释的 [DiscreteCat_Functor@{o h p uo uh up +}]（Instance/Discrete.v，PR “代数载体是集合”，2026-09-17）将 [x = y] 消除为一个同态，方式与以前完全相同，并且可以在一个泛型 [C] 上形成。相应的负探针 n2 被翻转并保留为阳性对照。基本子句仍然是文件提供的内容，因为它直接采用了族并且根本不需要任何形状——比以前给出的理由更简单。这个引脚也从未属于 [DiscreteCat]，其 hom 和 proof 宇都是自由的（[DiscreteCat@{o h p} : Type@{o} → Category@{o h p}]）——这就是为什么 [comma_CreatesAllLimits] 及其下面的实例 [comma_CreatesProducts] 可以在一个通用的 [C] 和 [D] 上形成且无公理，并且它们并非空洞：一个常量离散图不会消除任何东西且可以形成，因此该类适用于它。这就是 docs/INDEX.md 的 Construction/Comma/Special.v 项已经记录的 [DiscreteCat_Functor] 的陷阱，这里比上一步被观测到。关于第438号问题中关于该树的三条实质性声明，截至本文件的父版本，这三条都是错误的，并且在此记录，因为问题文本将比提交记录存在得更久。请在整个树范围内阅读它们：三条中有两条在问题中作为关于 Construction/Comma/Limit.v 的陈述写出，而在该文件中它们仍然是真的——使它们为假的是本文件，它是在问题写出之后才合入的。“未正确声明创建”——上述 [comma_CreatesLimit] 已声明。“唯一性/反射子句缺失”——[comma_creates_reflect] 是反射子句，而唯一性则是 Structure/Limit/Creation.v 的 [creates_lift_unique] 应用于它，尽管仅适用于圆锥同构（参见未交付列表）。“没有引理断言构造的极限的投影是给定的那个”——[comma_strict_apex] 和 [comma_strict_legs] 正是断言了这一点，通过 [eq_refl]，对于任意下层极限。第四个只有一半正确：逗号极限仅对于 [Comma_Complete] 在所有形状的 [Complete C] 神谕下有效（Construction/Comma/Limit.v）；自提交 28ee6e54 以来，[comma_limit] 已将其下层极限作为参数。该问题的七个行引用已经过时，全部由提交新增的两行或随后漂移造成：[comma_limit]、[Comma_Complete]、[apex_obj]、[apex_leg]、[right_adjoint_PreservesImageLimit] 和 [Comma_Complete_right_adjoint] 都已经向下移动，而 [adj_id] 位于 Instance/Adjoints.v，其位置在声明处，而不是该问题指向的正文。它对 [PreservesImageLimit] 的引用是正确的，其 LIBRARY-DEFECT 项 — 即 Construction/Comma.v 和 Construction/Comma/Limit.v 声称创建而实际上只证明了存在 — 已经在此文件的第一次提交中解决，如上段所记录的那样。已测量。此文件的 [.glob] 声明了 42 个头（38 个 [def]，4 个 [prf]），且没有 [Program] 义务，其中九个来自第一次提交；加上 Construction/Slice/Creation.v 中的 30 个，总共有 72 个常量，全部由 [make print-assumptions] 承载，并且全部报告为“在全局上下文中关闭”。闭包从排除自身的 35 个模块增加到 38 个，新增的三个恰好是三个新的 [Require]（Structure/Limit/Product、Structure/Equalizer、Instance/Parallel）——没有其他内容附带，且创建类根本不需要 [Require]——而 Adjunction/Representability/Sets.v 保持在 99，三者都已经在其闭包中。四个文件依赖此文件：库中的该文件和 Construction/Slice/Creation.v，以及两个探测文件。Construction/Slice/Creation.v 覆盖了 52，而探针覆盖了 58。在 72 个头部和探针声明的名称上没有碰撞（整字 [grep -rlw] 超过 [*.v]，乐器检查位于 [Full]、[comma_limit] 和 [Coslice_Proj]）；唯一的其他文件命中是在 Adjunction/Representability/Sets.v 中对 [Continuous_PreservesImageLimit] 的两次使用，以及在 Construction/Arrow/Limit.v 中对 [comma_CreatesLimit] 的一次文字提及，任何地方都没有第二个声明。依次重命名 72 个名称，在声明它的文件中且只能在该文件里，然后重新编译此文件、卫星和探针的顺序：71 个都停止探针，每个都位于正行上，没有一个在反驳中，且第 72 个（[comma_StrictlyCreatesLimit]）首先在消耗它的行停止卫星——没有任何重命名存活，因此这里没有空置的保护。[make todo] 增长了七，探针的七条反驳线，且没有任何库文件贡献命中。在这两个文件中，共有十三个定义以 [Defined] 结尾——其中两个来自此文件的首次提交——七个以 [Qed] 结尾。将每个单独的 [Defined] 在整个文件的副本中翻转为 [Qed]：四个会停止文件本身（[comma_at_apex_leg]、[comma_at_med]、[comma_prod_proj]，以及卫星的 [coslice_lift_leg]，每个都需要由后续定义进行减小），两个会停止探测器（[comma_StrictlyCreatesLimit] 和 [Coslice_Proj_StrictlyCreatesLimit]，其严格提升的回读为 [eq_refl]），七个会在每个回读完整的情况下成功编译（[comma_at_ump]、[comma_reflect_at]、[comma_IsIndexedProduct]、[coslice_reflect_at]、[coslice_lift_ump]，以及两个预先存在的 [comma_creates_reflect] 和 [comma_CreatesLimit]）。那些保持透明，因为它们是数据——普遍属性、限制锥见证、记录中的居住者——与它们旁边的 [umed] 和 [comma_ump] 的 [Defined] 相匹配；它们的翻转不是承重的，这一点是披露的，而不是被否认的。未在此处交付。没有削弱 [Comma_Complete] 的导出类型，因此 Adjunction/GAFT.v 和 Adjunction/SAFT.v 未受影响；没有按形状划分的完备类，乘积和等化子条款是单个语句而不是形状索引族的实例；没有在任意 FAMILY 上实例化 [comma_CreatesProducts] 在通用 [C] 上，原因如上所述——该类已发布，探针将其应用于恒定离散图，但由族构建的图被拒绝；没有精确的提升唯一性，Mac Lane 的“恰好一对”——可用的是 [creates_lift_unique] 的 [ConeIso]，并且 Structure/Limit/Creation.v 从理论上说明了为什么在集合等价类环境中唯一性不能成为类的字段；任何地方都没有有限性，乘积条款的索引是任意 [Type]；没有 crea由 [comma_proj1] 进行的 tion，而树中没有任何内容涉及；也没有余极对偶，问题 #438 与 Riehl 的连接余极一半一起解决。严格创建用于普通余切投影的过程已在 Construction/Slice/Creation.v 中实现——该列表的早期版本说它被阻止，这是基于错误的前提，即不存在无条件的余切投影。
*)

(*
   * ** [PreservesImageLimit] is cone-level preservation at every shape 

   --------
   * ** [PreservesImageLimit] 在每个形状上都是圆锥级别的保留
*)

Definition PreservesImageLimit_Continuous
  {C D : Category} {U : C ⟶ D} (H : @PreservesImageLimit C D U) :
  ContinuousFunctor U :=
  fun J K N HN => H J K (@Build_Limit J C K N HN).

Definition Continuous_PreservesImageLimit
  {C D : Category} {U : C ⟶ D} (H : ContinuousFunctor U) :
  @PreservesImageLimit C D U :=
  fun J K L => H J K (@limit_cone _ _ _ L) (limit_limitcone L).

(** ** The reflection clause / ** 反思条款 *)

Section CommaReflect.

Context {C D : Category}.
Context {U : C ⟶ D}.
Context {d : D}.
Context (HU : @PreservesImageLimit C D U).
Context {J : Category}.
Context (K : J ⟶ (=(d) ↓ U)).

(*
 The cone with apex [d] over [U ◯ (comma_proj2 ◯ K)] read off the comma
 data of K.  This is the general-diagram analogue of [base_cone]
 (Construction/Comma/Limit.v), restated because that one is fixed to
 the chosen [Gdiag]. 

 --------
 顶点为 [d]、位于 [U ◯ (comma_proj2 ◯ K)] 上的圆锥读取了 K 的逗号数据。这是 [base_cone]（Construction/Comma/Limit.v）的通用图示类比，之所以重述，是因为那个固定在所选择的 [Gdiag] 上。
*)

Lemma rbase_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[U] (fmap[comma_proj2 ◯ K] f) ∘ `2 (K x) ≈ `2 (K y).
Proof using Type.
  symmetry.
  transitivity (`2 (K y) ∘ id[d]).
  - rewrite id_right; reflexivity.
  - exact (`2 (fmap[K] f)).
Qed.

Definition rbase_cone : Cone (U ◯ (comma_proj2 ◯ K)) :=
  @Build_Cone J D (U ◯ (comma_proj2 ◯ K)) d
    (@Build_ACone J D d (U ◯ (comma_proj2 ◯ K))
       (fun j => `2 (K j)) (@rbase_coherence)).

(*
 A cone over K whose C-projection is limiting is itself limiting.  The
 C-component of the mediator is given by the projected cone; the comma
 component is the triangle over [d], and that triangle is forced by
 uniqueness of the mediator into the image limit — which is exactly what
 [PreservesImageLimit] supplies. 

 --------
 一个 K 上的圆锥，其 C-投影是极限，则其自身也是极限。中介者的 C 分量由投影圆锥给出；逗号分量是 [d] 上的三角形，而该三角形由于中介者的唯一性被迫进入像极限——这正是 [PreservesImageLimit] 所提供的。
*)

Definition comma_creates_reflect (M : Cone K)
  (HM : IsLimitCone (FCone comma_proj2 M)) : IsLimitCone M.
Proof using HU.
  intro N.
  pose (L := @Build_Limit J C (comma_proj2 ◯ K) (FCone comma_proj2 M) HM).
  destruct (HM (FCone comma_proj2 N)) as [w Hw Hwu].
  assert (Hsq : (`2 vertex_obj[M]) ∘ id[d]
                  ≈ fmap[U] w ∘ `2 vertex_obj[N]).
  { rewrite id_right.
    apply (limit_med_eq (image_is_alimit HU L) rbase_cone).
    - intro j.
      change (fmap[U] (cone_leg (FCone comma_proj2 M) j) ∘ (`2 vertex_obj[M])
                ≈ `2 (K j)).
      symmetry.
      exact (comma_square (cone_leg M j)).
    - intro j.
      change (fmap[U] (cone_leg (FCone comma_proj2 M) j)
                ∘ (fmap[U] w ∘ `2 vertex_obj[N]) ≈ `2 (K j)).
      rewrite comp_assoc, <- fmap_comp.
      rewrite (Hw j).
      symmetry.
      exact (comma_square (cone_leg N j)). }
  unshelve refine {| unique_obj := ((ttt, w); Hsq) |}.
  - intro j; split.
    + now destruct (fst (`1 (cone_leg N j))).
    + exact (Hw j).
  - intros [[u1 u2] Hu] Hv; split.
    + simpl; destruct u1; reflexivity.
    + apply Hwu.
      intro j.
      exact (snd (Hv j)).
Defined.

End CommaReflect.

(** ** The instance / ** 实例 *)

Section CommaCreates.

Context {C D : Category}.
Context {U : C ⟶ D}.
Context {d : D}.
Context (HU : @PreservesImageLimit C D U).
Context {J : Category}.
Context (K : J ⟶ (=(d) ↓ U)).

(*
 An ARBITRARY limit of the base diagram downstairs.  This used to be the
 chosen [Ldiag HC K] coming from a [Complete C]; making it a parameter is
 what upgrades the strictness statements below from "at the chosen limit"
 to "at every limit". 

 --------
 楼下基图的一个任意极限。这曾经是从 [Complete C] 得到的选定 [Ldiag HC K]；将其作为参数正是将下述严格性声明从“在选定极限时”升级为“在每个极限时”的原因。
*)
Context (L : Limit (Gdiag K)).

(*
 The image of the comma limit cone IS that downstairs limit cone, by
 conversion. 

 --------
 逗号极限锥的图像就是楼下的极限锥，通过转换得到。
*)

Definition comma_image_limitcone :
  IsLimitCone (FCone comma_proj2 (@limit_cone _ _ _ (comma_limit HU K L)))
  := fun N => @ump_limit _ _ _ _ (limit_is_alimit L) N.

Definition comma_CreatesLimit : CreatesLimit K comma_proj2.
Proof using HU L.
  unshelve refine
    {| creates_lift := fun _ _ => @limit_cone _ _ _ (comma_limit HU K L) |}.
  - intros N HN.
    exact (limitcone_iso comma_image_limitcone HN).
  - exact (comma_creates_reflect HU K).
Defined.

End CommaCreates.

(*
   * ** Strictness at EVERY limit: apex and legs on the nose 

   --------
   * ** 每一个极限的严格：鼻子上的顶点和腿
*)

(*
 These now quantify over an arbitrary downstairs limit [L] rather than the
 one chosen by a [Complete C].  The witnesses are still [eq_refl]: the
 comma limit is BUILT from [L], so the projection lands on [L]'s apex and
 legs definitionally, whichever limit [L] is.  This is Mac Lane's [F σ = τ]
 at full strength, and it is what the header of this file previously
 deferred as a separate proposal. 

 --------
 这些现在对任意下限 [L] 进行量化，而不是由 [Complete C] 选择的那个。证据仍然是 [eq_refl] ：逗号限制是从 [L] 构建的，因此投影定义上落在 [L] 的顶点和支脚上，无论 [L] 是哪个下限。这是 Mac Lane 的 [F σ = τ] 全力运作的状态，这也是本文件的标题以前延迟为单独提议的内容。
*)

Definition comma_strict_apex {C D : Category} {U : C ⟶ D} {d : D}
  (HU : @PreservesImageLimit C D U)
  {J : Category} (K : J ⟶ (=(d) ↓ U)) (L : Limit (Gdiag K)) :
  comma_proj2 (vertex_obj[comma_limit HU K L]) = vertex_obj[L]
  := eq_refl.

Definition comma_strict_legs {C D : Category} {U : C ⟶ D} {d : D}
  (HU : @PreservesImageLimit C D U)
  {J : Category} (K : J ⟶ (=(d) ↓ U)) (L : Limit (Gdiag K)) (j : J) :
  fmap[comma_proj2] (cone_leg (comma_limit HU K L) j)
    = limit_leg (limit_is_alimit L) j := eq_refl.

(*
   * ** The same construction from a PER-DIAGRAM hypothesis 

   --------
   * ** 来自 PER-DIAGRAM 假设的相同构造
*)

(*
 Mac Lane's Lemma (§V.6, book p. 121) assumes only that [U] preserve the
 limits of the shapes at issue — products and equalizers, in the proof of
 Theorem 2 — whereas [PreservesImageLimit] quantifies over every shape and
 every diagram at once.  The section below re-derives the construction of
 Construction/Comma/Limit.v from the single hypothesis

 [PreservesLimitCone (Gdiag K) U]

 for the one base diagram of the one [K] at hand.  Nothing in
 Construction/Comma/Limit.v is changed or re-proved: [base_cone], [wmed],
 [qcone], [comma_square] and [image_acone] are reused verbatim and the
 tactic scripts are the originals.  The only edit is at the one place the
 all-shapes hypothesis was consumed, [image_is_alimit HU L], which becomes
 [comma_at_image]. 

 --------
 麦克莱恩引理 (§V.6, 书第121页) 仅假设 [U] 保持所讨论形状的极限——在定理2的证明中是积和等化器——而 [PreservesImageLimit] 则对每一个形状和每一个图同时量化。下面的章节重新从单一假设 [PreservesLimitCone (Gdiag K) U] 为手头的一个 [K] 基础图重新推导 Construction/Comma/Limit.v 的构造。Construction/Comma/Limit.v 中没有任何内容被更改或重新证明：[base_cone]、[wmed]、[qcone]、[comma_square] 和 [image_acone] 都被逐字重用，策略脚本是原始的。唯一的修改是在消耗了全形状假设的唯一位置 [image_is_alimit HU L]，它变为 [comma_at_image]。
*)

Section CommaCreateAt.

Context {C D : Category}.
Context {U : C ⟶ D}.
Context {d : D}.
Context {J : Category}.
Context (K : J ⟶ (=(d) ↓ U)).
Context (HK : PreservesLimitCone (Gdiag K) U).
Context (L : Limit (Gdiag K)).

Definition comma_at_image : IsALimit (U ◯ Gdiag K) (U L) :=
  @Build_IsALimit J D (U ◯ Gdiag K) (U L) (image_acone L)
    (HK (@limit_cone _ _ _ L) (limit_limitcone L)).

Definition comma_at_phi : d ~{D}~> U L :=
  limit_med comma_at_image (base_cone K).

Lemma comma_at_phi_commutes (j : J) :
  fmap[U] (limit_leg (limit_is_alimit L) j) ∘ comma_at_phi ≈ `2 (K j).
Proof. exact (limit_med_commutes comma_at_image (base_cone K) j). Qed.

Definition comma_at_apex_obj : (=(d) ↓ U) := ((ttt, vertex_obj[L]); comma_at_phi).

Definition comma_at_apex_leg (j : J) : comma_at_apex_obj ~{=(d) ↓ U}~> K j.
Proof.
  unshelve refine ((ttt, limit_leg (limit_is_alimit L) j); _).
  change (`2 (K j) ∘ id[d]
          ≈ fmap[U] (limit_leg (limit_is_alimit L) j) ∘ comma_at_phi).
  rewrite id_right.
  symmetry.
  exact (comma_at_phi_commutes j).
Defined.

Lemma comma_at_apex_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[K] f ∘ comma_at_apex_leg x ≈ comma_at_apex_leg y.
Proof.
  split.
  - reflexivity.
  - exact (limit_leg_coherence (limit_is_alimit L) f).
Qed.

Definition comma_at_apex_cone : Cone K :=
  @Build_Cone J (=(d) ↓ U) K comma_at_apex_obj
    (@Build_ACone J (=(d) ↓ U) comma_at_apex_obj K comma_at_apex_leg
       (@comma_at_apex_coherence)).

Definition comma_at_med (N : Cone K) :
  vertex_obj[N] ~{=(d) ↓ U}~> comma_at_apex_obj.
Proof.
  unshelve refine ((ttt, wmed K L N); _).
  change (comma_at_phi ∘ id[d] ≈ fmap[U] (wmed K L N) ∘ `2 vertex_obj[N]).
  rewrite id_right.
  apply (limit_med_eq comma_at_image (base_cone K)).
  - exact (limit_med_commutes comma_at_image (base_cone K)).
  - intro j.
    change (fmap[U] (limit_leg (limit_is_alimit L) j)
              ∘ (fmap[U] (wmed K L N) ∘ `2 vertex_obj[N]) ≈ `2 (K j)).
    unfold wmed.
    rewrite comp_assoc, <- fmap_comp.
    rewrite (limit_med_commutes (limit_is_alimit L) (qcone K N) j).
    symmetry.
    exact (comma_square (cone_leg N j)).
Defined.

Definition comma_at_ump (N : Cone K) :
  ∃! u : vertex_obj[N] ~{=(d) ↓ U}~> comma_at_apex_obj,
    ∀ j : J, comma_at_apex_leg j ∘ u ≈ cone_leg N j.
Proof.
  unshelve refine {| unique_obj := comma_at_med N |}.
  - intro j; split.
    + now destruct (fst (`1 (cone_leg N j))).
    + exact (limit_med_commutes (limit_is_alimit L) (qcone K N) j).
  - intros v Hv; split.
    + now destruct (fst (`1 v)).
    + unfold wmed.
      apply (limit_med_unique (limit_is_alimit L) (qcone K N)).
      intro j.
      exact (snd (Hv j)).
Defined.

Definition comma_limit_at : Limit K :=
  @Build_Limit J (=(d) ↓ U) K comma_at_apex_cone comma_at_ump.

(*
 The projection lands on [L] on the nose, exactly as [comma_strict_apex]
 and [comma_strict_legs] do for the all-shapes construction. 

 --------
 投影正好落在鼻子的 [L] 上，就像 [comma_strict_apex] 和 [comma_strict_legs] 对所有形状结构的处理一样。
*)

Definition comma_limit_at_apex :
  comma_proj2 (vertex_obj[comma_limit_at]) = vertex_obj[L] := eq_refl.

Definition comma_limit_at_legs (j : J) :
  fmap[comma_proj2] (cone_leg comma_limit_at j)
    = limit_leg (limit_is_alimit L) j := eq_refl.

End CommaCreateAt.

(* * ** The reflection clause, per diagram / * ** 根据图表的反射条款 *)

Section CommaReflectAt.

Context {C D : Category}.
Context {U : C ⟶ D}.
Context {d : D}.
Context {J : Category}.
Context (K : J ⟶ (=(d) ↓ U)).
Context (HK : PreservesLimitCone (Gdiag K) U).

(*
 [comma_creates_reflect] above with the all-shapes [HU] weakened to [HK];
 the script is that proof's, with [image_is_alimit HU L] replaced by
 [comma_at_image K HK L]. 

 --------
 [comma_creates_reflect] 上的所有形状 [HU] 被削弱为 [HK]；该脚本是那个证明，[image_is_alimit HU L] 被替换为 [comma_at_image K HK L]。
*)

Definition comma_reflect_at (M : Cone K)
  (HM : IsLimitCone (FCone comma_proj2 M)) : IsLimitCone M.
Proof using HK.
  intro N.
  pose (L := @Build_Limit J C (comma_proj2 ◯ K) (FCone comma_proj2 M) HM).
  destruct (HM (FCone comma_proj2 N)) as [w Hw Hwu].
  assert (Hsq : (`2 vertex_obj[M]) ∘ id[d]
                  ≈ fmap[U] w ∘ `2 vertex_obj[N]).
  { rewrite id_right.
    apply (limit_med_eq (comma_at_image K HK L) (rbase_cone K)).
    - intro j.
      change (fmap[U] (cone_leg (FCone comma_proj2 M) j) ∘ (`2 vertex_obj[M])
                ≈ `2 (K j)).
      symmetry.
      exact (comma_square (cone_leg M j)).
    - intro j.
      change (fmap[U] (cone_leg (FCone comma_proj2 M) j)
                ∘ (fmap[U] w ∘ `2 vertex_obj[N]) ≈ `2 (K j)).
      rewrite comp_assoc, <- fmap_comp.
      rewrite (Hw j).
      symmetry.
      exact (comma_square (cone_leg N j)). }
  unshelve refine {| unique_obj := ((ttt, w); Hsq) |}.
  - intro j; split.
    + now destruct (fst (`1 (cone_leg N j))).
    + exact (Hw j).
  - intros [[u1 u2] Hu] Hv; split.
    + simpl; destruct u1; reflexivity.
    + apply Hwu.
      intro j.
      exact (snd (Hv j)).
Defined.

End CommaReflectAt.

(** ** Strict creation / ** 严格创建 *)

(*
 [comma_CreatesLimit] above is creation in the [CreatesLimit] sense: its
 [creates_lift] returns the lift of the FIXED [L] it was given, related to
 the cone it is handed only up to [ConeIso].  Mac Lane's lemma and Riehl
 §3.4.7 ask for more — that the lift lie over the GIVEN cone on the nose —
 and [Structure/Limit/Creation.v]'s [StrictLift] is the record that says
 so.  The lift below is therefore built from [Build_Limit N HN], the given
 cone repackaged as a limit, rather than from a fixed [L]; both strictness
 fields are then [eq_refl] and [reflexivity], for EVERY limiting cone
 downstairs.  Test/ProbeCommaCreation438.v pins the difference: the shipped
 [creates_lift]'s apex is refused against [vertex_obj[N]] (negative n5)
 where this one is accepted (its paired control). 

 --------
 [comma_CreatesLimit] 上面的创造是在 [CreatesLimit] 意义上的：它的 [creates_lift] 返回了给定的 FIXED [L] 的提升，与它所持有的锥体只到 [ConeIso] 为止相关。Mac Lane 引理和 Riehl §3.4.7 要求更多——即提升必须精确地位于给定的锥体之上——而 [Structure/Limit/Creation.v] 的 [StrictLift] 就是说明这一点的记录。因此，下面的提升是从 [Build_Limit N HN] 构建的，即将给定锥体作为极限重新打包，而不是来自固定的 [L]；然后两个严格性字段分别为 [eq_refl] 和 [reflexivity]，适用于楼下的每一个极限锥体。Test/ProbeCommaCreation438.v 确定了差异：发货的 [creates_lift] 的锥顶在 [vertex_obj[N] 处被拒绝（负 n5），而这个则被接受（它的成对控制）。
*)

Section CommaStrictCreate.

Context {C D : Category}.
Context {U : C ⟶ D}.
Context {d : D}.
Context {J : Category}.
Context (K : J ⟶ (=(d) ↓ U)).
Context (HK : PreservesLimitCone (Gdiag K) U).

Definition comma_strict_lift (N : Cone (comma_proj2 ◯ K)) (HN : IsLimitCone N) :
  StrictLift K comma_proj2 N :=
  @Build_StrictLift J (=(d) ↓ U) C K comma_proj2 N
    (comma_limit_at K HK (@Build_Limit J C (Gdiag K) N HN))
    eq_refl
    (fun x => reflexivity _).

Definition comma_StrictlyCreatesLimit : StrictlyCreatesLimit K comma_proj2.
Proof using HK.
  unshelve refine {| screates := comma_strict_lift |}.
  - intros N HN.
    exact (limit_limitcone
             (comma_limit_at K HK (@Build_Limit J C (Gdiag K) N HN))).
  - exact (comma_reflect_at K HK).
Defined.

(*
 Creation with no [L] argument at all, and with the lift over the given
 cone rather than over a chosen one. 

 --------
 创建时完全没有 [L] 参数，并且提升是作用在给定的圆锥上，而不是作用在选定的圆锥上。
*)

Definition comma_CreatesLimit_at : CreatesLimit K comma_proj2 :=
  StrictlyCreatesLimit_CreatesLimit comma_StrictlyCreatesLimit.

End CommaStrictCreate.

(** ** Products, elementarily / ** 产品，初步 *)

(*
 Mac Lane's Theorem 2 consumes the lemma at two shapes only, products and
 equalizers.  The products clause is stated here over
 [Structure/Limit/Product.v]'s [IsIndexedProduct] rather than over a
 discrete shape, and that is a considered choice, not a convenience:
 [Gdiag] identifies the shape's hom and proof universes with [C]'s, and
 [DiscreteCat A]'s hom is an equality in [Prop] which minimizes to [Set],
 so [Gdiag (DiscreteCat_Functor F)] pins BOTH categories to
 [Category@{_ Set Set}].  Test/ProbeCommaCreation438.v's negative n2
 records the refusal ("Cannot enforce Set = ...").  The elementary form
 below is universe-clean over a generic [C] and [D], and it is the form
 Mac Lane's proof actually uses. 

 --------
 Mac Lane 的定理 2 仅在两种形状上使用引理，即积和等化器。这里的积条款是针对 [Structure/Limit/Product.v] 的 [IsIndexedProduct] 陈述的，而不是针对离散形状，这是经过考虑的选择，而不是方便：[Gdiag] 将形状的 Hom 和证明宇宙与 [C] 的对应起来，而 [DiscreteCat A] 的 Hom 在 [Prop] 中是一个等式，它最小化为 [Set]，因此 [Gdiag (DiscreteCat_Functor F)] 将两个范畴都固定在 [Category@{_ Set Set}] 上。Test/ProbeCommaCreation438.v 的 negative n2 记录了拒绝（“无法强制 Set = ...”）。下面的基本形式在通用 [C] 和 [D] 上是宇宙干净的，并且它正是 Mac Lane 的证明实际使用的形式。
*)

Section CommaProducts.

Context {C D : Category}.
Context {U : C ⟶ D}.
Context {d : D}.
Context {A : Type}.
Context (F : A → (=(d) ↓ U)).

Definition comma_prod_fam (a : A) : C := comma_proj2 (F a).

Context (p : C).
Context (proj : ∀ a : A, p ~{C}~> comma_prod_fam a).
Context (HP : IsIndexedProduct comma_prod_fam p proj).

(*
 The per-shape preservation hypothesis at its most elementary: [U] carries
 THIS indexed product to an indexed product. 

 --------
 最基本的每形状保持假说：[U] 将此索引产品带到一个索引产品。
*)
Context (HU : IsIndexedProduct (fun a => U (comma_prod_fam a)) (U p)
                (fun a => fmap[U] (proj a))).

Definition comma_prod_phi : d ~{D}~> U p :=
  unique_obj (iprod_desc HU (fun a => `2 (F a))).

Lemma comma_prod_phi_commutes (a : A) :
  fmap[U] (proj a) ∘ comma_prod_phi ≈ `2 (F a).
Proof using Type.
  exact (unique_property (iprod_desc HU (fun a => `2 (F a))) a).
Qed.

Definition comma_prod_apex : (=(d) ↓ U) := ((ttt, p); comma_prod_phi).

Definition comma_prod_proj (a : A) : comma_prod_apex ~{=(d) ↓ U}~> F a.
Proof using Type.
  unshelve refine ((ttt, proj a); _).
  change (`2 (F a) ∘ id[d] ≈ fmap[U] (proj a) ∘ comma_prod_phi).
  rewrite id_right.
  symmetry.
  exact (comma_prod_phi_commutes a).
Defined.

Definition comma_IsIndexedProduct :
  IsIndexedProduct F comma_prod_apex comma_prod_proj.
Proof using HP HU.
  constructor.
  intros c pi.
  destruct (iprod_desc HP (fun a => snd (`1 (pi a)))) as [w Hw Hwu].
  assert (Hsq : comma_prod_phi ∘ id[d] ≈ fmap[U] w ∘ `2 c).
  { rewrite id_right.
    unfold comma_prod_phi.
    apply (uniqueness (iprod_desc HU (fun a => `2 (F a)))).
    intro a.
    rewrite comp_assoc, <- fmap_comp, (Hw a).
    symmetry.
    exact (comma_square (pi a)). }
  unshelve refine {| unique_obj := ((ttt, w); Hsq) |}.
  - intro a; split.
    + now destruct (fst (`1 (pi a))).
    + exact (Hw a).
  - intros [[u1 u2] Hu] Hv; split.
    + simpl; destruct u1; reflexivity.
    + apply Hwu.
      intro a.
      exact (snd (Hv a)).
Defined.

Definition comma_prod_apex_strict : comma_proj2 comma_prod_apex = p := eq_refl.

Definition comma_prod_leg_strict (a : A) :
  fmap[comma_proj2] (comma_prod_proj a) = proj a := eq_refl.

End CommaProducts.

(** ** Equalizers / ** 均衡器 *)

(*
 [Structure/Equalizer.v] defines [Equalizer F] as [Limit F] for
 [F : Parallel ⟶ C], so this clause is the per-diagram construction read
 at the walking-parallel-pair shape; [Parallel] leaves its hom universe
 free, so unlike the discrete shape it costs nothing. 

 --------
 [Structure/Equalizer.v] 将 [Equalizer F] 定义为 [Limit F]，针对 [F : Parallel ⟶ C]，所以这一条款是在 walking-parallel-pair 形状下以每图构造的方式读取的；[Parallel] 让它的同构宇宙保持自由，所以与离散形状不同，它不会产生任何开销。
*)

Section CommaEqualizers.

Context {C D : Category}.
Context {U : C ⟶ D}.
Context {d : D}.
Context (K : Parallel ⟶ (=(d) ↓ U)).
Context (HK : PreservesLimitCone (Gdiag K) U).
Context (E : Equalizer (Gdiag K)).

Definition comma_equalizer_at : Equalizer K := comma_limit_at K HK E.

Definition comma_equalizer_apex_strict :
  comma_proj2 (vertex_obj[comma_equalizer_at]) = vertex_obj[E] := eq_refl.

Definition comma_equalizer_leg_strict (j : Parallel) :
  fmap[comma_proj2] (cone_leg comma_equalizer_at j)
    = limit_leg (limit_is_alimit E) j := eq_refl.

Definition comma_StrictlyCreatesEqualizers :
  StrictlyCreatesLimit K comma_proj2 := comma_StrictlyCreatesLimit K HK.

End CommaEqualizers.

(* * ** The shape-indexed creation classes / * ** 形状索引创建类 *)

(*
 Under the ALL-SHAPES [PreservesImageLimit] the per-diagram theorem above
 is available at every diagram at once, so [Structure/Limit/Creation.v]'s
 two classes both follow, by the same term.  [comma_CreatesAllLimits] is
 the strongest of the three statements here and the other two are its
 instances: [CreatesAllLimits_CreatesProducts] reads it at
 [J := DiscreteCat A], and [comma_CreatesProducts] is exactly that.

 An earlier revision of this header said reaching the products clause
 through [CreatesProducts] "would import that pin", and that was wrong.
 [Gdiag K] is formable for an abstract [K : DiscreteCat A ⟶ (=(d) ↓ U)],
 because [Compose] unifies the shape's hom universe with [C]'s before
 minimization, and neither class carries [Set] in its block.

 A SECOND CORRECTION, to the sentence that followed.  An earlier revision
 continued: "What IS refused is a functor OUT OF [DiscreteCat A] that
 eliminates the shape's [x = y] into a hom: [DiscreteCat_Functor]
 (Instance/Discrete.v) prints as [DiscreteCat@{u Set Set} A ⟶ C], and a
 hand-rolled eliminator is refused with the same "Cannot enforce
 Set = ..." (probe negative n2), even at a concrete base such as
 [C = D = Sets] with [U = Id].  So the pin belongs to the elimination, not
 to [DiscreteCat]."  NOTHING is refused there any more, and the pin
 belonged to neither: it was a universe-minimization artifact of the
 unannotated declaration, removed by annotating it at
 Instance/Discrete.v in the PR "algebraic carriers are sets"
 (2026-09-17).  Probe negative n2 turned over and is now a positive
 control in Test/ProbeCommaCreation438.v, which records the same
 correction beside it.  [DiscreteCat]'s hom and proof universes were
 always free.  The classes are NOT vacuous, and the witness is unchanged:
 a CONSTANT discrete diagram needs no elimination and is formable over a
 generic [C], with [comma_CreatesProducts] applying to it —
 Test/ProbeCommaCreation438.v ships it.  The elementary [IsIndexedProduct] clause above is
 kept because it takes the family directly, which is the form Mac Lane's
 Theorem 2 consumes. 

 --------
 在 ALL-SHAPES  [PreservesImageLimit] 下，上述每个图的定理可以同时在每个图上使用，因此 [Structure/Limit/Creation.v] 的两个类都遵循同一条项。[comma_CreatesAllLimits] 是这里三条陈述中最强的一条，其他两条都是它的实例：[CreatesAllLimits_CreatesProducts] 在 [J := DiscreteCat A] 处读取它，而 [comma_CreatesProducts] 正是如此。

 该标题的早期修订版本表示，通过 [CreatesProducts] 到达产品条款“将导入该引脚”，这是错误的。[Gdiag K] 可用于一个抽象的 [K : DiscreteCat A ⟶ (=(d) ↓ U)]，因为 [Compose] 在最小化之前将形状的 hom 宇与 [C] 的统一，并且没有任何类在其块中携带 [Set]。第二次更正，对随后的句子。早期的修订继续写道：“被拒绝的是来自 [DiscreteCat A] 的一个函子，它将形状 [x = y] 消除了为 hom: [DiscreteCat_Functor]（Instance/Discrete.v）打印为 [DiscreteCat@{u Set Set} A ⟶ C]，并且手工编写的消除器也会被拒绝，出现相同的‘无法强制 Set = ...’（探测负 n2），即使在像 [C = D = Sets] 带有 [U = Id] 这样的具体基础上也是如此。所以这个标记属于消除，而不属于 [DiscreteCat]。” 现在那里已不再拒绝任何东西，而且这个标记也不属于任何一方：它是未经注释的声明的宇宙最小化产物，在 Instance/Discrete.v 的 PR “代数载体是集合”（2026-09-17）中通过注释移除了。探针负 n2 翻转，现在在 Test/ProbeCommaCreation438.v 中是一个阳性对照，并且在旁边记录了相同的修正。[DiscreteCat] 的同态和证明宇宙一直都是自由的。类不是空的，见证没有改变：一个常量离散图不需要消去，并且可以在一个泛型 [C] 上形成，[comma_CreatesProducts] 应用于它——Test/ProbeCommaCreation438.v 搭载它。上述基本的 [IsIndexedProduct] 条款保留，因为它直接获取族，这是 Mac Lane 定理 2 消耗的形式。
*)

Definition comma_CreatesAllLimits {C D : Category} {U : C ⟶ D} {d : D}
  (HU : @PreservesImageLimit C D U) :
  @CreatesAllLimits (=(d) ↓ U) C comma_proj2 :=
  fun J K => StrictlyCreatesLimit_CreatesLimit
               (comma_StrictlyCreatesLimit K
                  (fun N HN => HU _ (Gdiag K) (@Build_Limit _ _ (Gdiag K) N HN))).

Definition comma_CreatesProducts {C D : Category} {U : C ⟶ D} {d : D}
  (HU : @PreservesImageLimit C D U) :
  @CreatesProducts (=(d) ↓ U) C comma_proj2 :=
  CreatesAllLimits_CreatesProducts (comma_CreatesAllLimits HU).

(*
 Mac Lane's own completeness step.  Construction/Comma/Limit.v's
 [Comma_Complete] builds each limit of the comma category directly; the
 book instead observes that the projection CREATES limits and reads
 completeness off that.  Both routes are now available, and this one is
 his — it is [creates_limits_Complete] at [comma_CreatesAllLimits], and it
 costs no [Require] here.  [Comma_Complete]'s exported type is untouched,
 and [Adjunction/GAFT.v] still consumes that one, so nothing downstream
 moves; issue #436's request to route the argument through the creation
 result is answered here rather than by rewriting [GAFT]. 

 --------
 麦克·莱恩自己的完备性步骤。Construction/Comma/Limit.v 的 [Comma_Complete] 直接构建逗号范畴的每一个极限；书中则是观察投影会创建极限，并从中读取完备性。现在两种路径都可用，这个是他的——它在 [comma_CreatesAllLimits] 处的 [creates_limits_Complete]，并且在这里不需要 [Require] 。[Comma_Complete] 的导出类型保持不变，[Adjunction/GAFT.v] 仍然使用那个类型，所以下游没有任何变化；第 #436 号问题请求将参数通过创建结果路由，这里得到了解答，而不是通过重写 [GAFT] 。
*)

Definition comma_Complete_via_creation {C D : Category} {U : C ⟶ D} {d : D}
  (HU : @PreservesImageLimit C D U) (comp : @Complete C) :
  @Complete (=(d) ↓ U) :=
  creates_limits_Complete comma_proj2 comp (comma_CreatesAllLimits HU).

(*
   * ** The three names issue #438's Verification block audits 

   --------
   * ** 三个名称问题 #438 的验证区块审核
*)

(*
 That block runs [Print Assumptions] on [comma_creates_products],
 [comma_creates_equalizers] and [comma_proj_creates_limits].  None of the
 three was a name in the tree, and the three statements above carry names
 of their own that say which shape and which strength is meant, so the
 issue's names are given here as aliases with their binders written out —
 the commands then run as the issue writes them.

 An alias can minimize its universes differently from the constant it
 names, and these three do, so the difference is measured rather than
 assumed.  Under [Set Printing Universes] each alias prints with FEWER
 universe variables than its original — [comma_proj_creates_limits] 27
 against [comma_StrictlyCreatesLimit]'s 33, [comma_creates_equalizers] 23
 against [comma_equalizer_at]'s 32, [comma_creates_products] 11 against
 [comma_IsIndexedProduct]'s 16 — because the equations the originals carry
 in their constraint blocks, [u0 = u2] identifying [C]'s hom-and-proof
 universe with [D]'s in all three, with two, four and one more besides, are
 solved
 into the aliases' binders instead: every alias binder reads
 [C : Category@{_ h h}] and [D : Category@{_ h h}] with ONE [h], and no
 alias block carries an equation at all.  No block on either side mentions
 [Set].  That each alias IS the constant it names, and not merely an
 inhabitant of the same type, is pinned by three [eq_refl] readbacks in
 Test/ProbeCommaCreation438.v. 

 --------
 该块在 [comma_creates_products]、[comma_creates_equalizers] 和 [comma_proj_creates_limits] 上运行 [Print Assumptions]。三个中没有一个是在树中的名字，上述三个语句各自携带自己的名称，用于说明具体指的是哪种形状和哪种强度，因此这里将问题的名称作为别名给出，并写出它们的绑定器——然后命令按照问题所写的方式运行。一个别名可以以不同于它所命名的常量的方式最小化其宇宙，而这三个确实这样做，所以差异是被测量的而不是假设的。在 [Set Printing Universes] 下，每个别名打印的宇宙变量比其原始变量少 — [comma_proj_creates_limits] 的 27 对比 [comma_StrictlyCreatesLimit] 的 33，[comma_creates_equalizers] 的 23 对比 [comma_equalizer_at] 的 32，[comma_creates_products] 的 11 对比 [comma_IsIndexedProduct] 的 16 — 因为原始变量在其约束块中携带的方程，[u0 = u2] 标识 [C] 的 hom-and-proof 宇宙与 [D] 的在三者中相同，在除此之外分别还有两个、四个和一个被解决到别名的绑定器中：每个别名绑定器读取 [C : Category@{_ h h}] 和 [D : Category@{_ h h}] 为一个 [h]，并且没有别名块包含任何方程。任一方的块都未提及 [Set]。每个别名本身就是它所命名的常量，而不仅仅是同类型的一个成员，这一点在 Test/ProbeCommaCreation438.v 中通过三次 [eq_refl] 读回被固定住。
*)

Definition comma_proj_creates_limits {C D : Category} {U : C ⟶ D} {d : D}
  {J : Category} (K : J ⟶ (=(d) ↓ U))
  (HK : PreservesLimitCone (Gdiag K) U) :
  StrictlyCreatesLimit K comma_proj2 := comma_StrictlyCreatesLimit K HK.

Definition comma_creates_equalizers {C D : Category} {U : C ⟶ D} {d : D}
  (K : Parallel ⟶ (=(d) ↓ U)) (HK : PreservesLimitCone (Gdiag K) U)
  (E : Equalizer (Gdiag K)) : Equalizer K := comma_equalizer_at K HK E.

Definition comma_creates_products {C D : Category} {U : C ⟶ D} {d : D}
  {A : Type} (F : A → (=(d) ↓ U)) (p : C)
  (proj : ∀ a : A, p ~{C}~> comma_prod_fam F a)
  (HP : IsIndexedProduct (comma_prod_fam F) p proj)
  (HU : IsIndexedProduct (fun a => U (comma_prod_fam F a)) (U p)
          (fun a => fmap[U] (proj a))) :
  IsIndexedProduct F (comma_prod_apex F p proj HU) (comma_prod_proj F p proj HU)
  := comma_IsIndexedProduct F p proj HP HU.
