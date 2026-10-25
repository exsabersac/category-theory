Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(*
 Generating (separating) families of objects, and single separators

 nLab:  https://ncatlab.org/nlab/show/separator
 nLab:  https://ncatlab.org/nlab/show/generator

 Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
 §V.7 ("Subobjects and Generators"), book p. 127 (PDF p. 136),
 Definition 4, is the source: a set of objects GENERATES C when two
 parallel arrows that agree after every arrow out of a member of the
 set are equal.  Mac Lane remarks that "separates" would be the better
 word -- the set separates the arrows of C, it does not build them --
 and this file follows him, keeping "generator" only in the names the
 literature has fixed.  His two illustrations are the one-point set
 for Set and the additive group of integers for Ab; neither is
 discharged IN THIS FILE -- the witnesses are Instance/Sets/Generator.v
 (the singleton and the terminal object), Instance/Grp/Generator.v
 (Awodey's free group on one generator) and Instance/Ab/Generator.v
 (the free abelian group on one generator, Mac Lane's ℤ up to an
 isomorphism that is not in tree), and the NOT DELIVERED paragraph
 below says what each leaves open.

 Awodey, "Category Theory" (1st ed., Carnegie Mellon pre-print,
 September 2005), §7.2, printed p. 154 (PDF p. 163), states the
 single-object case and the characterization this file proves: an
 object c of a locally small category is a generator (separator)
 exactly when the covariant representable Hom(c, -) is faithful, that
 is, when arrows out of x are determined by their effect on the
 generalized elements of x based at c.

 Riehl, "Category Theory in Context", 2nd ed., Definition 4.7.7,
 printed p. 177 (PDF p. 197), calls the family a SEPARATING SET and
 defines a COSEPARATING set to be a separating set in the opposite
 category -- the duality that Structure/Generator/Dual.v carries out
 on the nose.  Riehl's Epilogue §E.4, printed p. 257 (PDF p. 277),
 recalls the same notion as clause (vi) of Giraud's theorem, and
 states the joint-faithfulness reading alongside it.

 THE TWO FORMS.  [Generator C] is the family form: a small [Type] of
 indices, an object for each index, and the separation clause.  It is
 shaped field for field after Adjunction/SAFT.v's [Cogenerator],
 its dual, so that the bridge between them moves no data (that bridge
 is Structure/Generator/Dual.v, kept in a separate file because
 SAFT.v's requirement closure must not be pulled into Structure/).
 [IsSeparator c] is Awodey's single-object form, and
 [Generator_of_separator] packages a separator as a family over the
 index [unit].  [separator_of_generator] is the converse, over any
 index type whose elements are all the one index named.

 THE CONSTRUCTIVE READING.  Both clauses are stated POSITIVELY, as
 cancellation laws: if all the tests agree then the arrows agree.
 Riehl's Definition 4.7.7 and the §E.4 recollection are written the
 other way round -- for parallel f ≠ g there are a member G and an
 arrow h : G ~> B with f ∘ h ≠ g ∘ h -- which is the CONTRAPOSITIVE.
 The two readings are not interderivable in this library, and the
 reason is not a shortage of effort.  ≈ is a [crelation], Type-valued
 (Lib/Setoid.v), with no decision procedure and no double-negation
 elimination: from the ≠ form one gets ¬¬(f ≈ g) and stops, and from
 the positive form one gets ¬(∀ tests agree) and stops, an explicit
 witnessing pair (j, k) being exactly what constructive logic does not
 hand back from a negated universal.  What IS free is that last step,
 and it is landed rather than described: [gen_separates_contra] and
 [separator_contra] below take f ≉ g to the statement that the tests
 cannot all agree.  A reader who wants Riehl's form as written must
 supply a decider -- Structure/Complete/Freyd.v's [DecHom] is the
 tree's vocabulary for that -- and nothing here assumes one.  The
 weakened ≠ form is NOT stated as though it were the definition.

 THE IN-TREE SITUATION, MEASURED, AND WHAT THE ISSUE GOT WRONG.
 Issue #447 recorded, as its verified current state, that a search for
 Generator / Separator / SeparatingFamily / Generates finds exactly
 one [Cogenerator] record and nothing else.  That is STALE, and the
 correction is recorded here rather than silently: with
 grep -rn 'Separator' --include='*.v' over this worktree,
 Theory/Concrete.v carries a whole single-object development already.
 [Class Separator (t : C)] is the same condition as [IsSeparator]
 with the two objects implicit; [Separator_of_Faithful] is one half
 of Awodey's characterization, already proved;
 [Concrete_of_Separator] contains the OTHER half, not as a
 named lemma but as the [underlying_faithful] obligation of the
 concretization it builds; and the Sets witness the issue asks for
 is [Sets_Separator], with [Sets_WellPointed] and the
 non-vacuity refutation [Sets_empty_not_Separator] beside it.
 So what is genuinely new here is the FAMILY notion, the joint-
 faithfulness characterization in both directions, the transport
 lemmas, and the duality file -- not the single-object condition.
 [IsSeparator] is kept anyway, and is not a rival: it is the frozen
 interface this issue was built against in parallel, it is Type-valued
 rather than a class (so it composes as a function, which is what
 every characterization below consumes), and
 Structure/Generator/Concrete.v carries the two bridges
 [Separator_of_IsSeparator] / [IsSeparator_of_Separator] in both
 directions, so the tree does not end with two unrelated notions.
 That bridge is a THIRD file for a measured reason: Theory/Concrete.v
 defines [bool_setoid_object] and Instance/Sets.v defines a
 different [bool_setoid_object], so requiring Concrete here
 would shadow the Sets one for every later file, and the witnesses
 built against this interface use Sets.

 The dual side is as the issue described it.  Adjunction/SAFT.v's
 [Cogenerator] is the only cogenerating vocabulary, its header says
 "Equivalently the representables [C(-, cog_obj j)] are jointly
 faithful" as PROSE and proves it nowhere, and exactly one site
 really consumes the field (apply (cog_separates G g1 g2) inside
 [cogenerator_canonical_monic]).  Structure/Generator/Dual.v proves
 that prose, both ways.

 WHAT THE CHARACTERIZATIONS COST: UNPACKING, NOT PROOF.  Every
 equivalence below is a term, never a tactic script, because the two
 sides have literally the same hypothesis once two definitions are
 unfolded.  [Hom c,─] is Functor/Hom.v's [Curried_Hom C] applied to
 c, whose [fmap] at f : x ~> y is the setoid map k ↦ f ∘ k
 (post-composition); the Sets hom-setoid is Instance/Sets.v's
 [SetoidMorphism_equiv], which is pointwise -- f ≈ g means ∀ a, f a ≈
 g a with ≈ taken in the codomain.  So the faithfulness hypothesis
 [fmap[[Hom c,─]] f ≈ fmap[[Hom c,─]] g] unfolds to
 [∀ k : c ~> x, f ∘ k ≈ g ∘ k], which IS the separation hypothesis,
 and the proof term on each side is the identity up to eta.  What is
 NOT free is the packaging: [Faithful] is a one-field CLASS, so
 [Faithful [Hom c,─] := H] with H an [IsSeparator] is REFUSED --
 measured, with the same requirement list:
 Example f2_eq (H : IsSeparator c) : Faithful [Hom c,─] := H.
 is rejected with
 "The term "H" has type "IsSeparator c" while it is expected to have
 type "Faithful (fobj[C] c)"" --
 a class record is not a function.  Hence [Build_Faithful] one way and
 [fmap_inj] the other, and the same for the family form through
 [JointlyFaithful].

 VARIANCE IS THE WHOLE CONTENT, AND THE WRONG ONE IS NOT REFUTED BY
 TYPING ALONE.  For a family [F : J -> C], the statement
 [JointlyFaithful (fun j => [Hom ─, F j])] -- the CONTRAVARIANT
 representables -- is perfectly well formed: [Hom ─, A] is
 Functor/Hom.v's [Curried_CoHom C] at A, a functor C^op ⟶ Sets, so
 the joint-faithfulness statement is about C^op arrows and says that
 the family COseparates.  It is a different statement, not a
 malformed one.  What is refused is deriving it from [Generator C]:
 with the identical proof term, Rocq reports
 "The term "k" has type "gen_obj G j ~{ C }~> y" while it is
 expected to have type
 "carrier (fobj[fobj[Curried_CoHom C] (gen_obj G j)] x)"" --
 the probe object sits at the wrong end of the arrow.  So the reading
 proved below, [generator_jointly_faithful], is the covariant one and
 only that, and the contravariant one is Dual.v's
 [cogenerator_jointly_faithful] over a [Cogenerator].

 WHY THE ISOMORPHISM TRANSPORT IS HERE.  [separator_iso] moves
 [IsSeparator] along c ≅ d.  It is not decoration: the Sets witness
 needs it.  The singleton [unit_setoid_object] (Instance/Sets.v)
 takes its setoid field from Lib/Setoid.v's [unit_setoid], while
 the terminal object of [Sets_Terminal] (Instance/Sets.v) takes
 its from [Unit_Setoid] -- measured, not read off the source:
 Example t1 : @terminal_obj Sets Sets_Terminal
 = {| carrier := poly_unit ; is_setoid := Unit_Setoid |} := eq_refl.
 is ACCEPTED, while
 Example f3_term :
 @terminal_obj Sets Sets_Terminal = unit_setoid_object := eq_refl.
 is rejected with (cannot unify "1" and "unit_setoid_object") -- so
 "the terminal object separates Sets" and "the singleton separates
 Sets" are two statements, and whichever is proved reaches the other
 only along an isomorphism.  [hom_test_iso] is the shared step: it
 carries a family of tests out of d to a family of tests out of c, and
 [separator_iso], [gen_iso] and [gen_family_mono] are its three
 consumers.

 UNIVERSES, measured with [Set Printing Universes. About ...] rather
 than read off the source, which carries no annotation.  [Generator]
 prints as
 Generator@{u u0 u1} : Category@{u0 u1 u1} → Type@{max(u+1,u0,u1)}
 with an EMPTY constraint block, [u] being the level of the index
 [Type]; [IsSeparator@{u u0 u1} : ∀ {C : Category@{u0 u1 u1}},
 obj[C] → Type@{u}] carries only [u0 <= u] and [u1 <= u].  Every
 constant in this file binds its category as [Category@{_ u0 u0}],
 the hom level identified with the proof level.  [JointlyFaithful]
 goes one step further and identifies the two CATEGORIES' hom and
 proof levels with EACH OTHER -- it prints
 [∀ {C : Category@{u1 u2 u2}} {D : Category@{u3 u2 u2}} ...] -- which
 is the shape Theory/Functor.v's [Faithful] already prints and is
 NOT forced by the [Functor] record (Theory/Functor.v prints six
 independent levels with only ≤ bounds between them), so the collapse
 belongs to the faithfulness layer rather than being introduced here.
 The constants that mention [Sets] ([separator_faithful],
 [faithful_separator], [generator_jointly_faithful],
 [jointly_faithful_generator], [generator_iff_jointly_faithful]) carry
 in addition the block of Instance/Sets.v's
 [Sets@{o so} : Category@{so o o}] -- the strict [u0 < u2], the
 setoid-object level above the carrier level, and [u0 <= compose.u0],
 [u0 <= compose.u1], [u0 <= compose.u2], [u0 <= ID.u0] -- together
 with the ≤-bounds [IsSeparator] and [Faithful] contribute themselves
 ([u <= u1], [u0 <= u1], [u <= u3], [u2 <= u3]; an earlier revision of
 this sentence said "exactly the Sets block", which an audit measured
 as four bounds short).  Inherited, and attributed by [About] on
 [Sets], [IsSeparator] and [Faithful] rather than guessed.
 [hom_test_iso] and its three consumers
 carry the stdlib [u0 <= prod_rect.u0/u1/u2]; [gen_extend] adds the
 strict [u0 < u4], which is [iso_id]'s own (Theory/Isomorphism.v
 prints [p < u]); [separator_of_generator] carries
 [u0 <= eq_rect_r.u1] and [u2 <= eq_rect_r.u0], the price of the
 [rewrite] on the index equation.  [gen_separates_contra] has an
 EMPTY block.  No constant in this file is pinned to [Set].

 NOT DELIVERED.  No example in this file: the witnesses live in
 Instance/Sets/Generator.v, Instance/Grp/Generator.v and
 Instance/Ab/Generator.v, and Mac Lane's one-point set for Set was IN
 TREE already under another name (Theory/Concrete.v's
 [Sets_Separator], for the class; Structure/Generator/Concrete.v's
 bridge reads it as an [IsSeparator], and the Sets witness file proves
 the terminal-object statement directly as well).  Mac Lane's integers
 for Ab are delivered only up to the isomorphism ℤ ≅ F_ab(1), which is
 not in tree (Instance/Ab/Generator.v says what it would cost).  No
 name [generator_iff_jointly_faithful] over a BUNDLED [Generator]: the
 issue's pinned name is landed for an unbundled family [F : J -> C]
 ([Separates F]), because a biconditional between [Generator C] and a
 [JointlyFaithful] statement would have to quantify the index on one
 side only.  No collapse of a family to a single
 object: the classical remark that a generating family with a
 coproduct yields the single generator ∐_j G_j is NOT proved, and the
 reason is not cost -- IT IS UNSOUND AS STATED.  Arrows out of a
 coproduct are families of arrows out of the summands, so if one
 summand has no arrow at all into x then no arrow out of ∐_j G_j does
 either, and the separation hypothesis at x is vacuously satisfied
 while the family's is not.  A concrete refutation, in the topos
 Set × Set: {(1, ∅), (∅, 1)} separates (the first factor tests the
 first components, the second the second), its coproduct is (1, 1),
 and Hom((1,1), (2, ∅)) is empty while (2, ∅) carries two distinct
 parallel endomorphisms.  That argument is prose here and is NOT
 formalized -- the tree has no Set × Set instance wired to this file
 -- but it is the reason no [gen_collapse] appears below, and a future
 issue wanting one must first find the hypothesis that repairs it.
 No dense or strong generator: density (Theory/Density.v) and the
 extremal / strong / regular strengthenings of separation are not
 defined, and nothing here says a separating family detects
 isomorphisms or epimorphisms.  No Giraud clause: Riehl §E.4 (vi) is
 cited as the source of the vocabulary only, and no part of Giraud's
 theorem is stated.  No smallness: [gen_index] is a bare [Type] with
 no smallness condition attached, exactly as [cog_index] is in SAFT.v,
 so "set of objects" is read as "family indexed by a Type" throughout.
 No setoid structure on generators: [Generator C] carries no
 equivalence and nothing below respects one; [gen_iso] builds a new
 generator from an old one, it does not identify them.  No adjunction,
 no functoriality, no transport of separation along a functor in
 either direction. 

 --------
 生成（分离）物体的族，以及单个分隔符

 nLab:   https://ncatlab.org/nlab/show/separator 
 nLab:   https://ncatlab.org/nlab/show/generatorMac Lane，《为工作中的数学家准备的范畴》，第2版（GTM 5），§V.7（“子对象与生成元”），书本第127页（PDF第136页），定义4，是来源：一个对象集合GENERATES C，当且仅当两个平行箭头在集合中每个对象出的箭头作用下都相等时，相等。Mac Lane 评论说“separates”会是更好的词——这个集合分离C的箭头，它并不构造箭头——这个文件遵循他的做法，仅在文献固定的名称中保留“generator”。他的两个例子分别是 Set 的单点集合和 Ab 的整数加法群；在本文件中都没有展开——相关证明见 Instance/Sets/Generator.v（单元素集合和终对象）、Instance/Grp/Generator.v（Awodey 的单生成元自由群）以及 Instance/Ab/Generator.v（单生成元自由阿贝尔群，Mac Lane 的 ℤ，直到一个不在树中的同构），下面的未交付段落说明了每个例子留下的空白。Awodey，《范畴论》（第一版，卡内基梅隆预印本，2005年9月），§7.2，纸质书第154页（PDF第163页）指出了单对象情况以及本文件所证明的表征：局部小范畴中的一个对象c正好在其协变可表示函子Hom(c, -)是忠实函子时成为生成元（分离子），也就是说，当从x出的箭头可以通过它们在以c为基的x的广义元素上的作用来确定时。Riehl，《语境中的范畴论》，第2版，第4.7.7条定义，印刷版第177页（PDF第197页），将该族称为分离集，并将余分离集定义为对偶范畴中的分离集——这是《结构/生成元/对偶.v》直接实现的对偶性。Riehl的尾声 §E.4，印刷版第257页（PDF第277页），将相同的概念回忆为Giraud定理的条款(vi)，并同时陈述了联合忠实性的解释。两种形式。[Generator C] 是族形式：一个小的 [Type] 指数集合，每个指数对应一个对象，以及分离子句。它是根据 Adjunction/SAFT.v 的 [Cogenerator] 逐字段形成的，其对偶形式，使得它们之间的桥不会移动任何数据（该桥是 Structure/Generator/Dual.v，保存在单独的文件中，因为 SAFT.v 的需求闭包不能被引入 Structure/ 中）。[IsSeparator c] 是 Awodey 的单对象形式，而 [Generator_of_separator] 将分离器作为 [unit] 上的族进行打包。[separator_of_generator] 则是相反的形式，适用于所有元素都属于同一个命名指数的任意指数类型。建设性解读。两个条款都是以肯定的方式陈述的，作为消去律：如果所有测试都一致，则箭头也一致。Riehl 的定义 4.7.7 和 §E.4 的回顾是相反写的——对于平行的 f ≠ g，存在一个成员 G 和一个箭头 h : G ~> B，使得 f ∘ h ≠ g ∘ h——这就是逆否命题。在这个库中，这两种解读不能相互推导，原因不是努力不足。≈ 是一个 [crelation] 型值（Lib/Setoid.v），没有判定过程，也不能进行双重否定消去：从 ≠ 形式只能得到 ¬¬(f ≈ g) 并停下，而从正形式只能得到 ¬(∀ 测试一致) 并停下，一个显式的见证对 (j, k) 恰恰是建设性逻辑不从否定的全称断言中返回的东西。免费的就是最后一步， 它是实现而不是描述的：下面的 [gen_separates_contra] 和 [separator_contra] 将 f ≉ g 转化为测试不能全部一致的陈述。想要 Riehl 原文形式的读者必须提供一个判定器 —— Structure/Complete/Freyd.v 的 [DecHom] 是该树的词汇 —— 这里没有假设有判定器。弱化的 ≠ 形式并不是以它是定义的方式陈述的。树内情况、测量，以及该问题的错误之处。问题 #447 记录为其已验证的当前状态，即搜索 Generator / Separator / SeparatingFamily / Generates 只能找到一个 [Cogenerator] 记录，别无其他。这是过时的，修正记录在此而不是悄悄进行：在此工作树上使用 grep -rn 'Separator' --include='*.v'，Theory/Concrete.v 已经包含了完整的单对象开发。[Class Separator (t : C)] 与 [IsSeparator] 的条件相同，两者对象为隐含；[Separator_of_Faithful] 是 Awodey 描述的一半，已被证明；[Concrete_of_Separator] 包含另一半，不以命名引理的形式出现，而是作为它构造的具体化的 [underlying_faithful] 义务；而问题所要求的集合见证是 [Sets_Separator]，旁边是 [Sets_WellPointed] 和非空反驳 [Sets_empty_not_Separator]。因此，这里真正新的部分是 FAMILY 概念、双向联合忠实性描述、传输引理以及对偶文件——而不是单对象条件。[IsSeparator] 无论如何都会保留，并且不是竞争者：它是该问题并行构建时的冻结接口，它是类型值而不是类（因此它可以作为函数组合，这正是下面每个表征所使用的），并且 Structure/Generator/Concrete.v 在两个方向上携带了 [Separator_of_IsSeparator] / [IsSeparator_of_Separator] 两座桥，因此树不会以两个不相关的概念结束。那座桥是第三个文件，有其考量的原因：Theory/Concrete.v 定义了 [bool_setoid_object]，而 Instance/Sets.v 定义了不同的 [bool_setoid_object]，因此在此处要求 Concrete 会遮蔽 Sets 中的定义，对后续的每个文件都会有影响，并且针对该接口构建的证人使用的是 Sets。双侧与问题描述一致。Adjunction/SAFT.v 的 [Cogenerator] 是唯一的共生成词汇，其标题写着“等价地，可表示的 [C(-, cog_obj j)] 是联合忠实的”，以散文形式出现，但没有任何证明，并且实际上只有一个站点真正使用了该字段（在 [cogenerator_canonical_monic] 内部应用 (cog_separates G g1 g2)）。Structure/Generator/Dual.v 从两个方向证明了这一散文内容。特征化的代价：展开，而非证明。下面的每个等式都是一个项，从不使用战术脚本，因为一旦展开两个定义，等式两边的假设完全相同。[Hom c,─] 是 Functor/Hom.v 中的 [Curried_Hom C] 应用于 c，其在 f : x ~> y 处的 [fmap] 是集合同构映射 k ↦ f ∘ k（后组合）；Sets 的同态集合是 Instance/Sets.v 中的 [SetoidMorphism_equiv]，它是逐点的——f ≈ g 意味着 ∀ a, f a ≈ g a，其中 ≈ 在值域中取得。因此，忠诚性假设 [fmap[[Hom c,─] ] f ≈ fmap [[Hom c,─] ] g] 展开为 [∀ k : c ~> x, f ∘ k ≈ g ∘ k]，这就是分离假设，而两边的证明项在 eta 意义下是相同的。不免费的部分是包装：[Faithful] 是一个单字段类，因此 [Faithful [Hom c,─] := H]，其中 H 是一个 [IsSeparator]，被拒绝 -- 使用相同的需求列表测量：
 示例 f2_eq (H : IsSeparator c) : Faithful [Hom c,─] := H 被拒绝，提示 "术语 'H' 的类型是 'IsSeparator c'，而期望类型是 'Faithful (fobj [C] c)'" --
 类记录不是函数。因此 [Build_Faithful] 一种方式，[fmap_inj] 另一种方式，同样对于通过 [JointlyFaithful] 的族形式也是如此。方差是全部内容，仅凭类型无法驳斥错误的内容。对于一个族 [F : J -> C] ，语句 [JointlyFaithful (fun j => [Hom ─, F j] )] -- 逆变可表示项 -- 是完全符合形式的：[Hom ─, A] 是 Functor/Hom.v 中的 [Curried_CoHom C] 在 A 处的值，一个函子 C^op ⟶ Sets，因此联合忠实性声明是关于 C^op 的箭头，并且表示该族 COseparates。它是一个不同的声明，而不是格式错误的声明。被拒绝的是从 [Generator C] 推导它：使用相同的证明项，Rocq 报告说
 "项 'k' 的类型是 'gen_obj G j ~{ C }~> y'，而预期类型是 'carrier (fobj [fobj[Curried_CoHom C]  (gen_obj G j)] x)'" -- 探针对象位于箭头的错误端。所以读数证明下面的 [generator_jointly_faithful] 是协变的，只有它，而逆变的是 Dual.v 的 [cogenerator_jointly_faithful] 在一个 [Cogenerator] 上。为什么同构传输在这里。[separator_iso] 移动 [IsSeparator] 沿着 c ≅ d。它不是装饰：集合见证需要它。单元素 [unit_setoid_object] (Instance/Sets.v) 从 Lib/Setoid.v 的 [unit_setoid] 获取它的集合体字段，而 [Sets_Terminal] (Instance/Sets.v) 的终对象从 [Unit_Setoid] 获取 -- 是测量的，不是从源读取的：
 示例 t1 : @terminal_obj Sets Sets_Terminal
 = {| carrier := poly_unit ; is_setoid := Unit_Setoid |} := eq_refl. 被接受，而
 示例 f3_term :
 @terminal_obj Sets Sets_Terminal = unit_setoid_object := eq_refl. 被拒绝，报错 (不能统一 "1" 和 "unit_setoid_object") -- 所以
 "终对象区分集合" 和 "单元素区分集合" 是两个说法，无论哪一个被证明，只能沿着同构到达另一个。[hom_test_iso] 是共享步骤：它将 d 的一系列测试传递到 c 的一系列测试，并且 [separator_iso]、[gen_iso] 和 [gen_family_mono] 是它的三个使用者。宇宙，用 [Set Printing Universes. About ...] 测量，而不是从源读取，因为源没有注释。[Generator] 打印为
 Generator@{u u0 u1} : Category@{u0 u1 u1} → Type@{max(u+1,u0,u1)}
 带有一个空约束块，[u] 是索引 [Type] 的层级；[IsSeparator@{u u0 u1} : ∀ {C : Category@{u0 u1 u1}},
 obj [C] → Type@{u}] 只包含 [u0 <= u] 和 [u1 <= u]。文件中的每个常量都将其范畴绑定为 [Category@{_ u0 u0}]，同态层次与证明层次相同。[JointlyFaithful] 进一步，将两个类别的 hom 和证明级别彼此关联——它打印 [∀ {C : Category@{u1 u2 u2}} {D : Category@{u3 u2 u2}} ...] ——这是 Theory/Functor.v 的 [Faithful] 已经打印的，并且不是由 [Functor] 记录强制的（Theory/Functor.v 仅在它们之间有 ≤ 约束的情况下打印六个独立级别），因此这个合并属于忠实性层，而不是在此引入的。提到 [Sets]（[separator_faithful]、[faithful_separator]、[generator_jointly_faithful]、[jointly_faithful_generator]、[generator_iff_jointly_faithful]）的常量还包含 Instance/Sets.v 的块 [Sets@{o so} : Category@{so o o}] ——严格的 [u0 < u2]，以及高于载体级别的集合体对象级别，以及 [u0 <= compose.u0]、[u0 <= compose.u1]、[u0 <= compose.u2]、[u0 <= ID.u0] ——连同 ≤-界 [IsSeparator] 和 [Faithful] 本身也作出贡献（[u <= u1]、[u0 <= u1]、[u <= u3]、[u2 <= u3]；该句的早期版本说的是“正是 Sets 块”，审计发现少了四个界限）。由 [About] 继承，并归因于 [Sets]、[IsSeparator] 和 [Faithful]，而不是猜测获得的。[hom_test_iso] 及其三个使用者
 携带标准库 [u0 <= prod_rect.u0/u1/u2]；[gen_extend] 添加了严格的 [u0 < u4]，这是 [iso_id] 自己的（Theory/Isomorphism.v 打印 [p < u]）；[separator_of_generator] 携带 [u0 <= eq_rect_r.u1] 和 [u2 <= eq_rect_r.u0]，即 [rewrite] 在索引方程上的价格。[gen_separates_contra] 具有一个空块。此文件中没有常量被固定为 [Set]。未交付。本文件中没有示例：见证者位于 Instance/Sets/Generator.v、Instance/Grp/Generator.v 和 Instance/Ab/Generator.v，而 Mac Lane 的集合的一点集在 TREE 中已以其他名称存在（Theory/Concrete.v 的 [Sets_Separator]，用于类；Structure/Generator/Concrete.v 的 bridge 将其作为 [IsSeparator] 读取，并且 Sets 的见证文件也直接证明了终端对象声明）。Mac Lane 的 Ab 的整数只交付到同构 ℤ ≅ F_ab(1)，该同构不在 TREE 中（Instance/Ab/Generator.v 说明了成本）。没有名字 [generator_iff_jointly_faithful] 在一个捆绑的 [Generator] 上：该问题的固定名称是针对一个未捆绑的族 [F : J -> C]（[Separates F]）而提出的，因为 [Generator C] 和 [JointlyFaithful] 陈述之间的等价条件只会对一边的指标进行量化。一个族不会坍缩为单个对象：经典的观点是一个带有余积的生成族会产生单个生成器 ∐_j G_j，但这并未被证明，原因并非成本高，而是如陈述所述并不可靠。余积的箭头是来自各个分项的箭头族，所以如果某个分项完全没有箭头指向 x，那么 ∐_j G_j 的箭头也不会有，而 x 处的分离假设是自动满足的，而族的假设则不满足。在拓扑点集范畴 Set × Set 中，一个具体的反驳：{(1, ∅), (∅, 1)} 是分离的（第一个因子测试第一个分量，第二个测试第二个分量），它的余积是 (1, 1)，而 Hom((1,1), (2, ∅)) 是空的，同时 (2, ∅) 有两个不同的平行自同态。这个论证在这里是散文形式，并没有形式化——这棵树没有 Set × Set 实例连接到这个文件——但它是下面没有 [gen_collapse] 的原因，未来如果希望出现一个，必须首先找到修复它的假设。没有稠密或强生成元：稠密性（Theory/Density.v）以及分离的极端/强/正则强化都没有定义，这里也没有任何内容说明一个分离族能够检测同构或满射。没有 Giraud 条款：Riehl §E.4 (vi) 仅被引用为词汇来源，并未陈述 Giraud 定理的任何部分。没有小性：[gen_index] 是一个裸露的 [Type]，没有附加小性条件，就像 SAFT.v 中的 [cog_index] 一样，因此“对象集合”在整个文本中被理解为“由类型索引的族”。生成元没有集合结构：[Generator C] 没有携带等价关系，下方的任何内容也不遵守等价关系；[gen_iso] 从一个旧生成元构建一个新生成元，它们不会被认同。没有伴随、没有函子性、沿任意方向的函子也没有分离的迁移。
*)

(* * ** Generating (separating) families and objects / * ** 生成（分离）家庭和物体 *)

(*
 Mac Lane §V.7 p. 127 / Riehl 4.7.7 / Awodey §7.2: a family of objects
 SEPARATES (generates) C when parallel arrows agreeing after every arrow
 OUT of a member are equal.  Stated positively as a cancellation law,
 the constructively correct reading, exactly as [Cogenerator] states its
 dual. 

 --------
 Mac Lane §V.7 第127页 / Riehl 4.7.7 / Awodey §7.2：一族对象
 当平行箭头在每个成员的箭头之后一致时，该族对象将C分离（生成）出来。如果以正面的方式表述为消去律，这是构造上正确的解读，正如[Cogenerator]所陈述其对偶一样。
*)
Record Generator {C : Category} := {
  gen_index : Type;
  gen_obj : gen_index -> C;
  gen_separates : forall (x y : C) (f g : x ~> y),
    (forall (j : gen_index) (k : gen_obj j ~> x), f ∘ k ≈ g ∘ k) -> f ≈ g
}.

Arguments Generator : clear implicits.
Arguments gen_index {C} _.
Arguments gen_obj {C} _ _.
Arguments gen_separates {C} _ {x y} f g _.

(*
 Awodey's single-object form: one object whose generalized elements
 distinguish parallel arrows. 

 --------
 Awodey 的单对象形式：一个对象，其广义元素区分平行箭头。
*)
Definition IsSeparator {C : Category} (c : C) : Type :=
  forall (x y : C) (f g : x ~> y),
    (forall k : c ~> x, f ∘ k ≈ g ∘ k) -> f ≈ g.

Definition Generator_of_separator {C : Category} (c : C) (H : IsSeparator c) :
  Generator C := {|
  gen_index := unit;
  gen_obj := fun _ => c;
  gen_separates := fun x y f g Hk => H x y f g (fun k => Hk tt k)
|}.

(*
 Joint faithfulness of a family of functors: the arrows are told apart
 by SOME member.  For the representables [Hom (gen_obj j), ─] this is
 the separation condition read through [fmap]. 

 --------
 一族函子的联合忠实性：箭头可以被某个成员区分。对于可表示的  [Hom (gen_obj j), ─]，这就是通过 [fmap] 阅读的分离条件。
*)
Definition JointlyFaithful {C D : Category} {J : Type}
  (F : J -> C ⟶ D) : Type :=
  forall (x y : C) (f g : x ~> y),
    (forall j : J, fmap[F j] f ≈ fmap[F j] g) -> f ≈ g.

(* * ** Awodey §7.2: separation IS faithfulness of the representable / * ** Awodey §7.2: 分离就是可表示性的忠实性 *)

Section Characterizations.

Context {C : Category}.

(*
 Forward.  The hypothesis of [Faithful [Hom c,─]] at f, g is
 [fmap[[Hom c,─]] f ≈ fmap[[Hom c,─]] g], which unfolds -- through
 Instance/Sets.v's pointwise hom-setoid and Functor/Hom.v's
 post-composition [fmap] -- to [∀ k : c ~> x, f ∘ k ≈ g ∘ k], the
 hypothesis of [IsSeparator c].  Only the packaging moves: [Faithful]
 is a class, so the term is built with its constructor. 

 --------
 向前。[Faithful [Hom c,─] 在 f, g 的假设是 [fmap[[Hom c,─] f ≈ fmap [[Hom c,─] g]，它通过 Instance/Sets.v 的逐点同态集合和 Functor/Hom.v 的后组合 [fmap] 展开为 [∀ k : c ~> x, f ∘ k ≈ g ∘ k]，这是 [IsSeparator c] 的假设。只有封装发生了变化：[Faithful] 是一个类，所以该项是用它的构造函数构建的。
*)
Definition separator_faithful (c : C) (H : IsSeparator c) :
  Faithful [Hom c,─] :=
  @Build_Faithful C Sets [Hom c,─] (fun x y f g E => H x y f g (fun k => E k)).

(*
 Backward, by the same unfolding read the other way: [fmap_inj] is the
 field of [Faithful], and its hypothesis is already the separation
 hypothesis. 

 --------
 反过来，用同样的展开方式反向阅读：[fmap_inj] 是 [Faithful] 的场，其假设已经是分离假设。
*)
Definition faithful_separator (c : C) (F : Faithful [Hom c,─]) :
  IsSeparator c :=
  fun x y f g H => @fmap_inj _ _ [Hom c,─] F x y f g (fun k => H k).

(* * ** Mac Lane §V.7 / Riehl §E.4: the family form is joint faithfulness / * ** Mac Lane §V.7 / Riehl §E.4：这个族的形式是联合忠诚 *)

(*
 The family of covariant representables on the members of a generating
 family is jointly faithful, and conversely.  The index of the functor
 family is the generator's own index, so the two statements quantify
 over the same [Type]. 

 --------
 生成家族成员上的协变可表示的家族是联合忠实的，反之亦然。函子家族的指标是生成器自身的指标，因此这两个陈述量化的是相同的 [Type]。
*)
Definition generator_jointly_faithful (G : Generator C) :
  JointlyFaithful (fun j : gen_index G => [Hom gen_obj G j,─]) :=
  fun x y f g H => gen_separates G f g (fun j k => H j k).

Definition jointly_faithful_generator {J : Type} (F : J -> C)
  (H : JointlyFaithful (fun j : J => [Hom F j,─])) : Generator C :=
  @Build_Generator C J F (fun x y f g Hk => H x y f g (fun j k => Hk j k)).

(* * ** The single-object / family bridge / * ** 单一对象/家庭桥 *)

(*
 [Generator_of_separator] above is one direction.  This is its converse,
 for a family whose index has only the one element named: the object at
 that index separates by itself.  The transport is on the INDEX, by
 [rewrite] on a Leibniz equation between indices (data, not morphisms),
 after reverting the test arrow whose type mentions it. 

 --------
 [Generator_of_separator] 上面是一个方向。这是它的逆，对于一个索引只有一个元素的族：该索引处的对象独自分离。传输是在索引上，通过 [rewrite] 在指数之间的 Leibniz 方程上（数据，而不是态射），在反转类型中提到它的测试箭头之后。
*)
Definition separator_of_generator (G : Generator C) (j0 : gen_index G)
  (Hsing : forall j : gen_index G, j = j0) : IsSeparator (gen_obj G j0).
Proof.
  intros x y f g H.
  apply (gen_separates G f g); intros j k.
  revert k; rewrite (Hsing j); intros k; apply H.
Defined.

(*
 The round trip on a separator: packaging it as a [unit]-indexed family
 and reading the object back off gives the separator one started with
 ON THE NOSE -- the composite is [H] at [eq_refl], the index singleton
 condition on [unit] being [eq_refl] at [tt].  This equation is what
 makes the [Defined] above load-bearing: with [separator_of_generator]
 closed by [Qed] the same [eq_refl] is refused (measured).  A first
 draft stated only the TYPE [IsSeparator c], which [H] itself inhabits;
 an audit caught the vacuity and the equation replaced it. 

 --------
 在分离器上的往返：将其打包为一个 [unit] 索引的族，然后再读取对象，会得到分离器最初的状态——完全一致——复合体在 [eq_refl] 上是 [H]，[unit] 上的索引单象条件在 [tt] 上是 [eq_refl]。这个方程使得上面的 [Defined] 承重：当 [separator_of_generator] 由 [Qed] 关闭时，同一个 [eq_refl] 被拒绝（测量）。初稿仅声明 [IsSeparator c] 类型，而 [H] 本身也属于它；审核发现其空洞性，并用方程替代了它。
*)
Example separator_generator_roundtrip (c : C) (H : IsSeparator c) :
  separator_of_generator (Generator_of_separator c H) tt
    (fun j => match j with tt => eq_refl end) = H := eq_refl.

(*
 The issue's pinned name, as the biconditional it names, for an
 UNBUNDLED family [F : J -> C]: [Separates F] is the separation clause
 of [Generator] with the family held fixed, and the two directions are
 the two terms above read at that family.  Type-valued, so the "iff" is
 a pair. 

 --------
 该问题的固定名称，如其所命名的双条件，对于非捆绑族 [F : J -> C] : [Separates F]，是 [Generator] 的分离条款，同时保持该族不变，而两个方向是上述两个项在该族下的读法。类型值，因此“当且仅当”是一对。
*)
Definition Separates {J : Type} (F : J -> C) : Type :=
  forall (x y : C) (f g : x ~> y),
    (forall (j : J) (k : F j ~> x), f ∘ k ≈ g ∘ k) -> f ≈ g.

Definition generator_iff_jointly_faithful {J : Type} (F : J -> C) :
  (Separates F -> JointlyFaithful (fun j : J => [Hom F j,─])) *
  (JointlyFaithful (fun j : J => [Hom F j,─]) -> Separates F) :=
  (fun H x y f g E => H x y f g (fun j k => E j k),
   fun H x y f g E => H x y f g (fun j k => E j k)).

(* The same bridge one level up, between the two faithfulness notions: [JointlyFaithful] over a [unit] index is [Faithful]. / 同一座桥在更高一级，在两种忠诚概念之间： [JointlyFaithful] 在一个 [unit] 索引上是 [Faithful]。 *)
Definition jointly_faithful_faithful {D : Category} (F : C ⟶ D)
  (H : Faithful F) : JointlyFaithful (fun _ : unit => F) :=
  fun x y f g E => @fmap_inj _ _ F H x y f g (E tt).

Definition faithful_jointly_faithful {D : Category} (F : C ⟶ D)
  (H : JointlyFaithful (fun _ : unit => F)) : Faithful F :=
  @Build_Faithful C D F (fun x y f g E => H x y f g (fun _ => E)).

End Characterizations.

(* * ** Transport along isomorphisms and along maps of index types / * **沿同构以及沿索引类型的映射进行传输 *)

Section Transport.

Context {C : Category}.

(*
 The shared step of all three transports below.  If the arrows out of d
 already separate the pair (f, g), so do the arrows out of an isomorphic
 c: test with k ∘ from i and cancel [to i] on the right.  Stated for a
 FIXED pair, because that is what every consumer has in hand. 

 --------
 下面所有三种传输的共同步骤。如果来自 d 的箭头已经分开了 (f, g) 这对，那么来自同构 c 的箭头也同样分开：用 k ∘ 从 i 测试，并在右边消去 [to i]。对于一个固定的对来说，这是因为每个使用者手中都有这对。
*)
Lemma hom_test_iso {x y : C} (f g : x ~> y) {c d : C} (i : c ≅ d)
  (H : forall k : d ~> x, f ∘ k ≈ g ∘ k) (k : c ~> x) : f ∘ k ≈ g ∘ k.
Proof.
  specialize (H (k ∘ from i)).
  rewrite !comp_assoc in H.
  rewrite <- (id_right (f ∘ k)), <- (id_right (g ∘ k)).
  rewrite <- (iso_from_to i).
  rewrite !comp_assoc.
  now rewrite H.
Qed.

(*
 Separation is an isomorphism-invariant property of an object.  This is
 what moves a witness between two presentations of the same object --
 see the header on the terminal object of [Sets] and the singleton. 

 --------
 分离是对象的一个同构不变性质。这就是将一个见证在同一个对象的两个表示之间移动的原因——参见 [Sets] 的终端对象和单例的头信息。
*)
Definition separator_iso {c d : C} (H : IsSeparator c) (i : c ≅ d) :
  IsSeparator d :=
  fun x y f g Hk => H x y f g (hom_test_iso f g i Hk).

(*
 Monotonicity along a map of index types: a family that CONTAINS a
 separating family, each member up to isomorphism, separates.  The new
 family is indexed by K and the old index is carried into it by u. 

 --------
 沿指数类型映射的单调性：包含一个分离族的族，其每个成员至同构，都可以分离。新的族由 K 索引，原来的索引通过 u 引入其中。
*)
Definition gen_family_mono (G : Generator C) {K : Type} (ob : K -> C)
  (u : gen_index G -> K) (i : forall j, gen_obj G j ≅ ob (u j)) :
  Generator C :=
  @Build_Generator C K ob
    (fun x y f g H =>
       gen_separates G f g (fun j => hom_test_iso f g (i j) (H (u j)))).

(* Replacing each member by an isomorphic object, the index kept. / 将每个成员替换为一个同构对象，索引保持不变。 *)
Definition gen_iso (G : Generator C) (d : gen_index G -> C)
  (i : forall j, gen_obj G j ≅ d j) : Generator C :=
  gen_family_mono G d (fun j => j) i.

(*
 Adding objects to a separating family keeps it separating.  The
 isomorphisms are [iso_id]: on the [inl] summand the two families are
 convertible, so this is the definitional case of [gen_family_mono]. 

 --------
 向一个分离族添加对象会保持其分离性。 同构是 [iso_id]：在 [inl] 直和部分上，这两个族是可转换的，所以这是 [gen_family_mono] 的定义性情况。
*)
Definition gen_extend (G : Generator C) {K : Type} (ob : K -> C) :
  Generator C :=
  gen_family_mono G (fun jk => match jk with
                               | inl j => gen_obj G j
                               | inr k => ob k
                               end) inl (fun _ => iso_id).

End Transport.

(* * ** Riehl's contrapositive reading, as far as it is free / * ** 里尔的逆否读法，就其自由程度而言 *)

Section Contrapositive.

Context {C : Category}.

(*
 Riehl 4.7.7 states separation as: f ≉ g yields a member and an arrow
 out of it that the two arrows treat differently.  Constructively only
 this much comes back -- the tests cannot ALL agree -- and the step
 from there to an explicit witnessing pair is the one this library
 cannot take without a decider (see the header). 

 --------
 Riehl 4.7.7 将分离状态描述为：f ≉ g 产生一个元素以及从中引出的箭头，这两个箭头的处理方式不同。构造上只有这么多结果——测试不能全部一致——而从这里到一个明确的证据对的步骤是该库在没有判定器的情况下无法完成的（见标题）。
*)
Definition gen_separates_contra (G : Generator C) {x y : C} (f g : x ~> y)
  (Hne : f ≈ g -> False) :
  (forall (j : gen_index G) (k : gen_obj G j ~> x), f ∘ k ≈ g ∘ k) -> False :=
  fun H => Hne (gen_separates G f g H).

Definition separator_contra {c : C} (H : IsSeparator c) {x y : C}
  (f g : x ~> y) (Hne : f ≈ g -> False) :
  (forall k : c ~> x, f ∘ k ≈ g ∘ k) -> False :=
  fun Hk => Hne (H x y f g Hk).

End Contrapositive.
