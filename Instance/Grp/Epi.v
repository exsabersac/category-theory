Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.Grp.

Generalizable All Variables.

(*
 Obligations are discharged by hand throughout, as in Instance/Grp.v, so that
 every proof below is visible in the source rather than delegated to a
 default tactic. 

 --------
 义务从始至终都是通过手动完成的，就像在 Instance/Grp.v 中一样，因此下面的每个证明在源代码中都是可见的，而不是委托给默认策略。
*)
#[local] Obligation Tactic := idtac.

(* * * Epimorphisms in the category of groups / * * 群范畴中的上同态 *)

(*
 Book: Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 Springer GTM 5, 1998, Section I.5 (“Monics, Epis, and Zeros”),
 printed p. 21, Exercise 5
 nLab: https://ncatlab.org/nlab/show/epimorphisms+of+groups+are+surjective
 nLab: https://ncatlab.org/nlab/show/epimorphism

 Mac Lane's Exercise I.5.5 asks for the proof that every epimorphism of
 groups is surjective.  Several presentations circulate, and they differ in
 which set gets permuted.

 - Mac Lane's own hint, read off the printed text of the second edition at
 p. 21, permutes the underlying SET of H.  It splits into two cases: if
 the image M has index two, use the factor group H/M; otherwise choose
 three DISTINCT cosets M, Mu, Mv of M, put s in Perm H equal to the
 identity except that s(xu) = xv and s(xv) = xu for every x in M, and
 compare the homomorphism sending h to left multiplication by h with its
 conjugate by s.  The two cosets that s exchanges are the two NON-base
 ones, and there is no adjoined point anywhere in the hint.
 - The form more often quoted in later expositions permutes the coset
 space H/M with one extra point adjoined, and conjugates by the
 transposition exchanging the BASE coset with that extra point.
 - The nLab page cited above gives neither.  It gives Todd Trimble's
 argument, which replaces the coset set by a FUNCTION SPACE -- the
 G-module A^G of functions into a nontrivial abelian group -- and forces
 the two splittings j(g) = (g, 0) and k(g) = (g, phi(g)) of the
 semidirect-product extension 0 -> A^G -> G |x| A^G -> G -> 1 to
 coincide.

 What is formalized below is the SECOND form -- permutations of H/M with a
 point adjoined, conjugation by the base-coset transposition -- because that
 is the form issue #251 specifies.  One ingredient of it is then changed, for
 a reason that is proved rather than asserted, and the classical
 biconditional carries a hypothesis whose real status is set out next.

 WHAT IS PROVED, EXACTLY.

 [grp_surjective_is_epic]      surjective -> epic.  Unconditional.
 [grp_not_epic_of_witness]     given h0 TOGETHER WITH a proof that h0 has
 no preimage, f is not epic.  Unconditional.
 [grp_epic_image_dense]        epic f -> for every h, h cannot be shown to
 miss the image.  Unconditional.
 [grp_epic_iff_surjective]     epic f <-> surjective f, under the named
 hypothesis [GrpImageStable].

 The first three carry no hypothesis at all and no axiom; [Print Assumptions]
 reports “Closed under the global context” for every constant in this file.
 (That is a claim over a growing set.  Since the PR “algebraic carriers are
 sets” (2026-09-17) this file declares four constants it did not before --
 [StableSetoid_PropEquiv], [SetoidPermutation_PropEquiv], [grp_two_prop] and
 [sym3_letters_prop], with [grp_two_prel], [sym3_prel] and [grp_two_setoid]
 alongside -- and the first two are enumerated in the `make
 print-assumptions` gate and do report “Closed under the global context”.
 The other five were not individually re-run, and this note says so rather
 than restating the claim as though they had been.)

 THE CONSTRUCTIVE CONTENT IS THE DENSITY THEOREM, AND NO SEPARATE “COST” CAN
 BE ISOLATED.  The classical proof runs by contraposition and begins by
 choosing an element outside the image.  Constructively, the negation of
 “every h has a preimage” does not produce such an element: that inference
 is the schema not-forall to exists-not, which is not derivable here and
 which this library does not assume.  So the theorem with real content is
 the contrapositive WITH AN EXPLICIT WITNESS, [grp_not_epic_of_witness],
 and that is the form in which the argument is carried out below.  From it,
 [grp_epic_image_dense] follows immediately: an epimorphism has a DENSE
 image, in the sense that no element can be exhibited outside it.  That
 density theorem is the whole of what the permutation argument buys, and it
 is unconditional and axiom-free.

 The remaining step to surjectivity is the passage from “h cannot be shown
 to miss the image” to “h has a preimage” -- that is, double-negation
 elimination at [GrpImage f h], which is exactly [GrpImageStable].  It would
 be tempting to present that as a small, independently interesting price
 paid for the classical statement.  It is nothing of the kind, and the file
 proves that it is not.  Under [Epic f] the hypothesis is EQUIVALENT to the
 conclusion it is supposed to buy: surjectivity gives stability outright
 ([surjective_gives_stable]), stability gives surjectivity by
 [grp_epic_is_surjective], and the two directions together are
 [stability_is_the_conclusion].  So [grp_epic_is_surjective] adds nothing
 over [grp_epic_image_dense]; it restates it under an assumption that
 already IS its conclusion.

 Nor is [GrpImageStable] minimal.  The strictly weaker
 [DenseImpliesSurjective] -- the single implication “if the image is dense
 then f is surjective”, with no pointwise structure at all -- already
 suffices ([weaker_hypothesis_suffices]) and is implied by stability
 ([stable_implies_weaker]); and it is ALSO equivalent to the conclusion
 under [Epic f] ([surjective_gives_weaker], [weaker_is_the_conclusion]).
 The deflation is therefore not an artefact of how [GrpImageStable] happens
 to be phrased.  Nothing weaker than the conclusion can serve either, and
 for a reason that needs no proof: the conclusion is itself a sufficient
 hypothesis, so it is the weakest one there is, and every hypothesis that
 completes the proof implies it by definition of completing the proof.  What
 this file can and does prove is the sharp half of that -- that both
 hypotheses actually on offer are implied BY the conclusion as well, hence
 equivalent to it.  The honest summary is therefore: the constructive
 theorem is [grp_epic_image_dense], and the classical statement is precisely
 its double-negation elimination, with no principle of independent interest
 in between.  [GrpImageDecidable_Stable] records that a decision procedure
 for image membership is one way to have that elimination, and
 [grp_two_incl_decidable] discharges it on a concrete finite group.  No
 [Axiom] is introduced anywhere in this file.

 WHY THE CONSTRUCTION CHANGES.  The transposition in the classical argument
 is the step that cannot be written down.  To define “exchange the base
 coset with the extra point and leave every other coset alone” one must
 decide, of an arbitrary coset, whether it IS the base coset -- that is,
 decide membership in the image.  That is not an impression about the
 difficulty of the definition; it is [transposition_decides_image], proved
 below.  Take ANY permutation t of the setoid [Grp_Coset f] with a point
 adjoined, and assume only the FIRST half of the transposition's
 specification -- that t carries every coset inside the image to the
 adjoined point.  Then [GrpImageDecidable f] follows: full decidability of
 image membership, obtained by matching on the coproduct constructor, with
 no decision procedure used anywhere in the proof.  Half the specification
 of the textbook transposition already delivers the entire decision problem,
 so assuming the transposition would make this file's theorem conditional on
 the very thing it is trying to isolate.  (Mac Lane's own permutation meets
 the same obstruction: to know whether to send an element of H to xv, to xu,
 or to itself, one must decide whether it lies in Mu or in Mv, and since
 those are RIGHT cosets, “y in Mu” is “y u^-1 in M” -- image membership
 again, after a translation.  Only the adjoined-point form is formalized
 here, and only for it is the obstruction proved.)

 So the H-set is changed.  Instead of the cosets with a point adjoined, the
 argument uses [GrpCosetPower], the double-negation-stable power set of the
 coset space: setoid maps from [Grp_Coset f] to [StableSetoid].  H acts on it
 by (h . S)(c) = S(h^-1 c), and the role of the transposition is played by
 [grp_twist], which complements the value of S at the base coset:

 twist S c  :=  (c in M -> not (S c))  /\  (c not in M -> S c)

 The formula says “complement at the base coset, leave alone elsewhere”
 without deciding which case obtains, and over a Boolean base it is exactly
 that.  Three facts about it carry the proof, and they are the three the
 transposition has in the coset argument:

 [grp_twist_involutive]        the twist is an involution.  This is what
 forces the truth values to be restricted to
 the stable ones: the step is exactly
 double-negation elimination at the value of
 S, and it is available for no wider class.
 [grp_twist_act_commute]       the twist commutes with the action of every
 element OF the image, so the two
 homomorphisms agree after f
 ([grp_twisted_action_agrees]).
 [grp_twist_act_not_commute]   at an element outside the image the two do
 not commute, witnessed at the distinguished
 subset c |-> not-not (c in M) and at the
 base coset -- so the two homomorphisms are
 distinct in the hom-setoid
 ([grp_actions_differ]).

 The permutation group itself is [SymGrp], the symmetric group of a setoid,
 whose elements are invertible setoid maps presented as a pair of maps with
 both round trips ([SetoidPermutation]); the inverse is data, so no choice is
 involved in inverting a permutation.  The second homomorphism is the first
 conjugated by the twist, using the inner automorphism [grp_conj].

 WHERE THE EQUIVARIANCE STEP HAS CONTENT, AND WHERE IT DOES NOT.  The second
 of those three facts -- that the twist commutes with the action of every
 element of the image -- says something only when the image actually MOVES
 the coset space.  Left translation by an element m of M sends the coset xM
 to a different coset exactly when x^-1 m x lies outside M, so the step is
 non-degenerate precisely when the image is NON-NORMAL, which is the case the
 permutation argument exists to handle.  Neither of the easy witnesses is of
 that kind: [Grp_exl] is surjective ([grp_two_exl_surjective]), so every
 element lies in its image and the coset setoid is indiscrete, and
 [grp_two_incl] has index two inside an abelian group.  At the latter the
 degeneracy is total, and rather than being passed over it is proved:
 [grp_two_incl_image_acts_trivially] shows that THE WHOLE IMAGE acts as the
 identity permutation of [GrpCosetPower] there, so [grp_twist_act_commute]
 and [grp_twisted_action_agrees] hold at that witness for the empty reason.

 The file therefore carries a second witness whose image is not normal.  A
 non-normal subgroup needs a non-abelian ambient group, so the smallest one
 available is the symmetric group on three letters; [grp_two_sym3] includes
 Z/2 into it ([grp_two_sym3_injective]) as the order-two subgroup generated
 by the transposition of two of the three letters.  There
 [grp_two_sym3_conj_outside] exhibits a conjugate of an image element lying
 outside the image -- so the image is not normal --
 [grp_two_sym3_moves_a_coset] exhibits a concrete stable subset, the
 indicator of a coset, that an element OF the image genuinely moves, and
 [grp_two_sym3_image_acts_nontrivially] concludes that the image does not act
 by the identity permutation.  At that witness the equivariance step compares
 two homomorphisms whose values are not identities, and so has content.  The
 general forms are [grp_act_moves_coset], for an arbitrary translating
 element and an arbitrary coset representative whose conjugate escapes, and
 [grp_image_acts_nontrivially], for a translating element of the form f g.

 WHY THE TRUTH VALUES COME FROM Prop.  Instance/Sets.v states the
 analogous characterization of epimorphisms in [Sets] and leaves its reverse
 direction unproved, with the reason recorded in that file's header: the
 truth-value object it needs does not fit at the universe of the setoids
 being classified.  Instance/Sets/Classifier.v is that object,
 [PropSetoid], carrier Type@{o} under bi-implication, and the classifier
 theorems there are consequently cross-universe.  Here the truth values are
 drawn from [Prop] instead.  Because [Prop] is impredicative, [StableProp]
 sits just above [Set] -- at a level fixed once and for all, not one level
 above whatever the ambient carriers happen to be -- and the entire
 construction stays inside a single instance of [Grp], which it
 must, since [Epic] quantifies over the objects of one such instance.  The
 one visible price is that the ambient carrier universe must lie strictly
 above [Set]; the concrete witness at the end of the file is built with that
 in mind.

 CONTRAST.  The corresponding statement for rings is false: the inclusion of
 the integers into the rationals is an epimorphism that is not surjective
 (Riehl, “Category Theory in Context”, Dover 2016, Exercises 1.2.iv and
 1.6.v(ii), as cited in the header of Instance/Grp.v).  There is no category
 of rings in this tree, so that counterexample is not formalized here; the
 contrast is recorded because it is what makes the present theorem a fact
 about groups rather than a general fact about algebraic categories.

 CONTRAST, NEARER TO HOME.  Instance/Grp.v proves the monomorphism
 counterpart, [Grp_injectivity_is_monic], as a biconditional with no side
 hypothesis at all.  The asymmetry is not an accident of presentation.  The
 monic direction is probed by the KERNEL, a sub-setoid of a carrier already
 in hand, and the probe maps out of it are the inclusion and the constant
 map.  The epi direction has to manufacture its probe from the coset space
 and a power set of it, and that is where the constructive content of the
 two statements parts company.

 NOTATION.  [∃] is [sigT] and [∧] is [prod] in this library
 (Lib/Foundation.v), so [GrpImage] is [Type]-valued and a proof of it
 yields an actual preimage; [↔] is [iffT] (Lib/Foundation.v).  Morphism
 equality is `≈` throughout, never `=`: the token `=` does not occur in a
 single statement or proof term in this file, only in these comments. 

 --------
 书籍：Mac Lane，《为在职数学家准备的范畴论》，第2版，Springer GTM 5，1998，第I.5节（“单态、满态与零”），印刷第21页，练习5
 nLab：https://ncatlab.org/nlab/show/epimorphisms+of+groups+are+surjective
 nLab：https://ncatlab.org/nlab/show/epimorphism

 Mac Lane的练习I.5.5要求证明每个群的满态映射都是满射。有几种不同的讲解流传开来，它们在排列的集合上有所不同。- Mac Lane 自己的提示，在第二版印刷文本第 21 页注明，会置换 H 的底层集合。它分为两种情况：如果像 M 的指数为二，则使用因子群 H/M；否则选择 M 的三个不同陪集 M、Mu、Mv，在 Perm H 中设 s 等于恒等映射，除了对每个 x 属于 M，有 s(xu) = xv 和 s(xv) = xu，然后将将 h 映射到左乘 h 的同态与其被 s 共轭的同态进行比较。s 交换的两个陪集是两个非基点的陪集，而且提示中任何地方都没有附加点。- 在后来的讲解中更常引用的形式，是置换陪集空间 H/M，并附加一个额外点，然后通过交换基点陪集与该额外点的换位进行共轭。- 上述引用的 nLab 页面都没有提供这些信息。它给出了Todd Trimble的论证，该论证将余类集合替换为函数空间——映入非平凡阿贝尔群的G-模A^G——并强制半直积扩张 0 -> A^G -> G |x| A^G -> G -> 1 的两个分裂 j(g) = (g, 0) 和 k(g) = (g, phi(g)) 重合。

 下面形式化的是第二种形式——在H/M的排列上添加一个点，通过基余类换位进行共轭——因为这是问题#251指定的形式。其中的一个组成部分随后被更改，原因是被证明而非断言的，而且经典的等价命题带有一个假设，其真实状态接下来被阐明。

 确切地说，所证明的是什么。[grp_surjective_is_epic]       满射 -> 史诗态。 无条件。
 [grp_not_epic_of_witness]      给定 h0 以及一个证明 h0 没有原像的证明，f 不是史诗态。 无条件。
 [grp_epic_image_dense]         史诗态 f -> 对于每个 h，不能证明 h 不在像中。 无条件。
 [grp_epic_iff_surjective]      史诗态 f <-> 满射 f，在已命名的假设 [GrpImageStable] 下。前三个完全没有假设，也没有公理；[Print Assumptions] 对此文件中的每一个常量都报告“在全局上下文下封闭”。
 （这是对一个增长集合的声明。自从 PR“代数承载体是集合”（2026-09-17）以来，这个文件声明了四个此前未声明的常量——[StableSetoid_PropEquiv]、[SetoidPermutation_PropEquiv]、[grp_two_prop] 和 [sym3_letters_prop]，以及 [grp_two_prel]、[sym3_prel] 和 [grp_two_setoid]——前两个在 `make print-assumptions` 阶段被枚举，并确实报告“在全局上下文下封闭”。其他五个没有单独重新运行，这条说明就是这样说的，而不是像它们已经被运行那样重复声明该声明。）建设性的内容是密度定理，并且不能隔离出任何单独的“代价”。经典证明通过反证法进行，从选择像之外的一个元素开始。在建设性方法中，“每个 h 都有一个原像”的否定并不能产生这样的元素：这种推理是从“非全称”到“存在非”的模式，而这在这里不可推出，本库也不假定它。因此，具有实际内容的定理是带有明确见证的反命题，[grp_not_epic_of_witness]，而这正是下面论证进行的形式。从它可以立即得到 [grp_epic_image_dense]：一个满射具有稠密的像，意思是没有任何元素可以被显示在它之外。那个密度定理就是排列论证所获得的一切，而且它是无条件的且不依赖公理。到满射性的剩余步骤是从“无法证明 h 会遗漏像”到“h 有原像”——也就是在 [GrpImage f h] 处进行双重否定消去，这正好是 [GrpImageStable]。将其作为为经典陈述付出的一个小而独立有趣的代价可能让人感到诱人。但事实并非如此，文件也证明了这一点。在 [Epic f] 下，假设等价于它应当得到的结论：满射性直接给出稳定性（[surjective_gives_stable]），通过 [grp_epic_is_surjective] 稳定性给出满射性，并且两个方向组合在一起为 [stability_is_the_conclusion]。因此 [grp_epic_is_surjective] 对于 [grp_epic_image_dense] 并无增加；它只是在一个已经即是其结论的假设下重新表述。[GrpImageStable] 也不是最小的。严格更弱的 [DenseImpliesSurjective] —— 单一的蕴含“如果像是稠密的，则 f 是满射的”，完全没有逐点结构 —— 已经足够（[weaker_hypothesis_suffices]）并且由稳定性（[stable_implies_weaker]）所蕴含；并且在 [Epic f] 下，它也等价于结论（[surjective_gives_weaker]，[weaker_is_the_conclusion]）。因此，这种缩减并不是 [GrpImageStable] 正好被表述方式的人工产物。没有比结论更弱的条件也能起作用，而且原因无需证明：结论本身就是一个充分的假设，所以它是最弱的条件，每一个完成证明的假设都按完成证明的定义蕴含它。这个文件能够并确实证明的是那一半尖锐的部分——即提供的两个假设实际上也由结论所暗示，因此与结论等价。因此，诚实的总结是：构造定理是 [grp_epic_image_dense]，而经典表述恰好是它的双重否定消去，中间没有任何独立重要的原理。[GrpImageDecidable_Stable] 记载了图像成员资格的判定程序是一种获得该消去的方法，而 [grp_two_incl_decidable] 在一个具体的有限群上实现了它。本文件中没有引入 [Axiom]。为什么构造会发生变化。在经典论证中，换位是无法写下的步骤。要定义“将基余类与额外点交换，并保持其他所有余类不变”，必须决定任意余类是否是基余类——也就是说，必须决定其是否属于像。这不是对定义难度的印象；这是 [transposition_decides_image]，如下所证。取集合 [Grp_Coset f] 上任意排列 t，并加上一个点，并仅假设换位规范的前半部分——即 t 将像中的每个余类映射到附加点。然后 [GrpImageDecidable f] 就随之成立：通过匹配余积构造子获得像成员资格的完全可判定性，并且在证明中未使用任何判定程序。教科书换位法的规格有一半已经提供了整个判定问题，所以假设换位法成立会导致该文件的定理依赖于它试图孤立的事情。（Mac Lane 自己的置换也遇到了同样的障碍：要决定将 H 的一个元素映射到 xv、xu 还是它自身，必须确定它是否位于 Mu 或 Mv 中，并且因为这些是右陪集，“y 属于 Mu” 等于 “y u^-1 属于 M”——又是映像的归属问题，只是经过了平移。这里只将附加点的形式进行形式化，而且只有它的障碍被证明。）因此 H 集发生了变化。不再是附加了一个点的陪集，论证使用的是  [GrpCosetPower] ，陪集空间的双否定稳定幂集：从 [Grp_Coset f] 到 [StableSetoid] 的等价类映射。H 通过 (h . S)(c) = S(h^-1 c) 在其上作用，而换位操作的角色由 [grp_twist] 扮演，它在基陪集上取 S 的补值：

 twist S c  :=  (c 属于 M -> not (S c))  /\  (c 不属于 M -> S c)

 这个公式表示“在基陪集上取补，其他地方保持不变”，而不决定哪种情况成立，在布尔基上它正是如此。关于它的三个事实支撑了整个证明，它们也是换位在陪集论证中具有的三个性质：[grp_twist_involutive] 扭转是一个自反变换。这就是迫使真值被限制为稳定值的原因：这个步骤正好是在 S 的值上进行双重否定消去，并且它对于更广的类不可用。[grp_twist_act_commute] 扭转与映像中每个元素的作用交换，因此在 f 之后两个同态是一致的（[grp_twisted_action_agrees]）。[grp_twist_act_not_commute] 在图像之外的一个元素上，这两个不交换，这在区分子集 c |-> not-not (c 在 M 中) 以及在基底陪集上得以体现——所以这两个同态在同态集 ( [grp_actions_differ] ) 中是不同的。

 置换群本身是 [SymGrp]，一个集合同态的对称群，其元素是可逆的集合同态映射，以一对映射的形式表示，其中两次往返 ( [SetoidPermutation] )；逆元是数据，因此在求置换的逆时不涉及选择。第二个同态是由扭转共轭的第一个同态，使用内自同构 [grp_conj]。等变性步骤在哪些情况下有内容，哪些情况下没有内容。三条事实中的第二条——即扭转与像中的每个元素的作用可交换——只有在像实际移动陪集空间时才有意义。由 M 的一个元素 m 作左平移会将陪集 xM 送到一个不同的陪集，恰好当 x^-1 m x 位于 M 之外时，所以这个步骤恰当非退化正是当像是非正规（NON-NORMAL）时，这正是排列论证存在的处理情况。两个简单的证据都不属于这种类型：[Grp_exl] 是满射（[grp_two_exl_surjective]），因此每个元素都在其像中，陪集集合是平凡的，并且 [grp_two_incl] 在一个阿贝尔群内的指数为二。在后者，退化是完全的，并且与其被忽略，不如说它被证明了：[grp_two_incl_image_acts_trivially] 表明整个图像在那里的 [GrpCosetPower] 中作为恒等排列起作用，因此 [grp_twist_act_commute] 和 [grp_twisted_action_agrees] 在该见证下因空理由成立。因此，该文件包含第二个证据，其像不是正规子群。一个非正规子群需要一个非阿贝尔的上层群，因此可用的最小群是三个元素的对称群；[grp_two_sym3] 将 Z/2 包含在其中（[grp_two_sym3_injective]），作为由三个字母中两个字母的换位生成的二阶子群。在 [grp_two_sym3_conj_outside] 中展示了一个像元素的共轭位于像之外 —— 因此该像不是正规子群 —— [grp_two_sym3_moves_a_coset] 展示了一个具体的不变子集，即一个陪集的指示函数，一个像中的元素确实移动它，而 [grp_two_sym3_image_acts_nontrivially] 得出该像不通过恒等置换作用。在该证据点上，等变性步骤比较了两个其值不是恒等元的同态，因此具有实质内容。一般形式是 [grp_act_moves_coset]，对于任意平移元素和一个任意陪集代表，其共轭元素会逃逸；以及 [grp_image_acts_nontrivially]，对于形式为 f g 的平移元素。为什么真值来自 Prop. Instance/Sets.v 说明了 [Sets] 中上同态的类似刻画，并且其逆向方向未被证明，原因记录在该文件的头部：所需的真值对象在被分类的集合类型的宇宙中不适用。Instance/Sets/Classifier.v 是那个对象，[PropSetoid]，在双重蕴含下的载体 Type@{o}，因此其中的分类定理是跨宇宙的。在这里，真值来自 [Prop]。因为 [Prop] 是不可谓的，[StableProp] 位于 [Set] 之上——在一个固定的层次，不是高于当前环境载体的某个层次——并且整个构造保持在单一的 [Grp] 实例中，这是必须的，因为 [Epic] 对该实例的对象进行量化。唯一显而易见的代价是环境载体的宇宙必须严格位于 [Set] 之上；文件末尾的具体证据就是基于这一点构建的。对比。对于环的对应说法是错误的：整数包含到有理数的映射是一个非满射的满射（Riehl，《上下文中的范畴论》，Dover 2016，第 1.2.iv 和 1.6.v(ii) 题，见 Instance/Grp.v 的标题引用）。在此树中没有环的范畴，因此该反例未在此处形式化；之所以记录这种对比，是因为它说明了本定理是关于群的事实，而不是关于代数范畴的一般事实。对比，更接近家。实例/Grp.v 证明了单态对应物 [Grp_injectivity_is_monic]，作为一个没有任何附加假设的双条件命题。这个不对称并非表述上的偶然。单态方向由 KERNEL 探测，这是一个已经掌握的承载对象的子集族，而探测映射是包含映射和常映射。满态方向必须从陪集空间及其幂集构造出探测映射，这也是两个陈述的建设性内容分歧的地方。符号说明。[∃] 在此库 (Lib/Foundation.v) 中是 [sigT]，[∧] 是 [prod]，因此 [GrpImage] 是 [Type] 值，并且它的证明产出一个实际的原像；[↔] 是 [iffT] (Lib/Foundation.v)。态射相等性在整个文件中都是 `≈`，从未是 `=`：标记 `=` 在本文件的任何陈述或证明项中都未出现，仅出现在这些注释中。
*)

(** ** Double-negation-stable types / ** 双重否定稳定类型 *)

(*
 [Stable P] says that [P] is its own double negation: a proof of [P] can be
 recovered from the impossibility of refuting it.  Every negation is stable,
 and stability is inherited by implications into a stable type and by
 conjunctions of stable propositions.  These are the only facts about
 stability the construction below needs. 

 --------
 [Stable P] 说 [P] 是它自身的双重否定：可以从无法驳斥它中恢复对 [P] 的证明。每个否定都是稳定的，而稳定性会被继承到稳定类型的蕴涵中，以及稳定命题的合取中。这些是下面构造所需的关于稳定性的唯一事实。
*)
Definition Stable (P : Type) : Type := ¬¬P → P.

Lemma stable_not (P : Type) : Stable (¬P).
Proof.
  intros HH p.
  apply HH.
  intro np.
  exact (np p).
Qed.

Lemma stable_not_not (P : Type) : Stable (¬¬P).
Proof. exact (stable_not (¬P)). Qed.

Lemma stable_arrow (P Q : Type) : Stable Q → Stable (P → Q).
Proof.
  intros HQ HH p.
  apply HQ.
  intro nq.
  apply HH.
  intro g.
  exact (nq (g p)).
Qed.

(* Stability of a conjunction, stated for [Prop] because the truth values below are propositions and the library's `∧` is the [Type]-valued [prod]. / 合取的稳定性，对于 [Prop] 陈述，因为下面的真值是命题，并且库中的 `∧` 是 [Type] 值的 [prod]。 *)
Lemma stable_and (P Q : Prop) : Stable P → Stable Q → Stable (P /\ Q).
Proof.
  intros HP HQ HH.
  split.
  - apply HP.
    intro np.
    apply HH.
    intros [p _].
    exact (np p).
  - apply HQ.
    intro nq.
    apply HH.
    intros [_ q].
    exact (nq q).
Qed.

(*
 The setoid of double-negation-stable PROPOSITIONS under bi-implication.
 The truth values are drawn from [Prop] rather than from [Type@{o}], and
 that choice is what keeps the construction inside a single universe: the
 size obstruction recorded at Instance/Sets.v (the truth-value object of
 [Sets] lives one universe up, cf. [PropSetoid] in
 Instance/Sets/Classifier.v) does not bite here, because [Prop] is
 impredicative and so [StableProp] sits just above [Set], at a level that
 does not depend on the ambient carriers.  Restricting to the stable
 propositions is what makes the involution [grp_twist] below definable with
 no decision procedure anywhere. 

 --------
 在双重否定稳定命题下的集合等价类，按双重蕴涵关系组织。
 真值从 [Prop] 中取，而不是从 [Type@{o}] 中取，
 这种选择使得构造保持在单一宇宙内：
 Instance/Sets.v 中记录的大小障碍（[Sets] 的真值对象位于上一级宇宙，参见 Instance/Sets/Classifier.v 中的 [PropSetoid]）在这里不会产生影响，
 因为 [Prop] 是不可预设的，因此 [StableProp] 位于 [Set] 之上，
 其层级不依赖于周围的载体。限制在稳定命题上正是使得下面的自反变换 [grp_twist] 可定义，且不依赖任何地方的判定过程。
*)
Definition StableProp : Type := ∃ P : Prop, Stable P.

Definition StableProp_equiv : crelation StableProp := λ P Q, `1 P ↔ `1 Q.

Lemma StableProp_equivalence : Equivalence StableProp_equiv.
Proof.
  unfold StableProp_equiv.
  constructor.
  - intro P.
    split; exact (λ x, x).
  - intros P Q [pq qp].
    split; assumption.
  - intros P Q R [pq qp] [qr rq].
    split.
    + exact (λ x, qr (pq x)).
    + exact (λ x, qp (rq x)).
Qed.

Definition StableSetoid : SetoidObject :=
  {| carrier   := StableProp
   ; is_setoid := {| equiv        := StableProp_equiv
                   ; setoid_equiv := StableProp_equivalence |} |}.

(*
 G5.  [StableSetoid] is propositional: `≈` there is [`1 P ↔ `1 Q] with `↔`
 the library's [iffT], a [Type]-valued pair of implications between two
 [Prop]s, and the [Prop] mirror is the [/\] of the same two implications.
 Needed since the PR “algebraic carriers are sets” (2026-09-17), because
 [SymGrp GrpCosetPower] is a [GrpObject] and therefore owes [grp_prop]. 

 --------
 G5. [StableSetoid] 是命题性的：`≈` 存在 [`1 P ↔ `1 Q]，其包含图书馆的 [iffT]，一个 [Type] 值的两两蕴含对在两个 [Prop] 之间，并且 [Prop] 镜像是同一两个蕴含的 [/\]。自 PR “代数载体是集合”（2026-09-17）以来需要，因为 [SymGrp GrpCosetPower] 是 [GrpObject]，因此欠 [grp_prop]。
*)
Definition StableSetoid_PropEquiv : PropEquiv (is_setoid StableSetoid).
Proof.
  unshelve refine
    {| pequiv := fun P Q : StableProp => (`1 P -> `1 Q) /\ (`1 Q -> `1 P) |}.
  - intros P Q [pq qp]; split; assumption.
  - intros P Q [pq qp]; split; assumption.
Defined.

(** ** The image of a homomorphism / ** 同态的像 *)

(*
 Membership in the image, as data: a preimage together with the equation
 witnessing it.  [∃] is [sigT] in this library (Lib/Foundation.v), so this is
 the [Type]-valued statement and a proof of it yields the preimage. 

 --------
 图像中的成员资格，作为数据：一个原像以及证明它的方程。在这个库（Lib/Foundation.v）中，[∃] 是 [sigT]，所以这是 [Type] 值的陈述，对它的证明产生原像。
*)
Definition GrpImage {G H : GrpObject} (f : G ~{Grp}~> H) (h : carrier H) : Type :=
  ∃ g : carrier G, grp_map f g ≈ h.

(*
 Surjectivity of a group homomorphism: every element of the codomain has a
 preimage.  Stated with `≈`, never with `=`.  This is the [Type]-valued
 reading, matching [surjective] at Lib/Setoid.v -- forced, since `≈` is
 itself [Type]-valued and a [Prop] existential could not be eliminated into
 it.  It does NOT make a surjection a split epimorphism: the preimage chosen
 for h need not respect `≈`, so it assembles no setoid map and a fortiori no
 homomorphism, and [grp_surjective_is_epic] below is therefore not an
 instance of [retractions_are_epic] (Theory/Morphisms.v). 

 --------
 群同态的满射性：值域中的每个元素都有一个原像。用 `≈` 表示，从不使用 `=` 表示。这是 [Type] 值的读法，与 Lib/Setoid.v 中的 [surjective] 匹配——这是强制的，因为 `≈` 本身是 [Type] 值，而 [Prop] 存在量词无法消去到其中。它并不使满射成为分裂上射：为 h 选择的原像不必遵循 `≈`，因此它不会组成集合化映射，更不用说同态了，因此下面的 [grp_surjective_is_epic] 不是 [retractions_are_epic]（Theory/Morphisms.v）的一个实例。
*)
Definition GrpSurjective {G H : GrpObject} (f : G ~{Grp}~> H) : Type :=
  ∀ h : carrier H, GrpImage f h.

Section Image.

Context {G H : GrpObject}.
Context (f : G ~{Grp}~> H).

Lemma GrpImage_respects (a b : carrier H) :
  a ≈ b → GrpImage f a → GrpImage f b.
Proof.
  intros Hab [g Hg].
  exists g.
  now rewrite Hg.
Qed.

Lemma GrpImage_unit : GrpImage f (grp_unit H).
Proof.
  exists (grp_unit G).
  apply (grp_map_unit f).
Qed.

Lemma GrpImage_mul (a b : carrier H) :
  GrpImage f a → GrpImage f b → GrpImage f (grp_mul H a b).
Proof.
  intros [ga Ha] [gb Hb].
  exists (grp_mul G ga gb).
  rewrite (grp_map_mul f).
  now rewrite Ha, Hb.
Qed.

Lemma GrpImage_inv (a : carrier H) :
  GrpImage f a → GrpImage f (grp_inv H a).
Proof.
  intros [g Hg].
  exists (grp_inv G g).
  rewrite (grp_map_inv f).
  now rewrite Hg.
Qed.

(** ** Left cosets of the image / ** 像的左陪集 *)

(*
 The left-coset relation x ~ y :≡ y⁻¹x lies in the image.  In a setoid
 library the coset space needs no quotient type: it is the carrier of [H]
 again, re-equipped with this coarser equivalence. 

 --------
 左陪集关系 x ~ y :≡ y⁻¹x 属于像。在一个集合体库中，陪集空间不需要商类型：它是 [H] 的承载体，再次配备上这个更粗的等价关系。
*)
Definition grp_coset_rel : crelation (carrier H) :=
  λ x y, GrpImage f (grp_mul H (grp_inv H y) x).

Lemma grp_coset_of_equiv (x y : carrier H) : x ≈ y → grp_coset_rel x y.
Proof.
  intro Hxy.
  unfold grp_coset_rel.
  apply (GrpImage_respects (grp_unit H)).
  - rewrite <- Hxy.
    symmetry.
    apply grp_mul_inv_l.
  - apply GrpImage_unit.
Qed.

Lemma grp_coset_refl (x : carrier H) : grp_coset_rel x x.
Proof.
  apply grp_coset_of_equiv.
  reflexivity.
Qed.

Lemma grp_coset_sym (x y : carrier H) : grp_coset_rel x y → grp_coset_rel y x.
Proof.
  intro Hxy.
  unfold grp_coset_rel in *.
  apply (GrpImage_respects (grp_inv H (grp_mul H (grp_inv H y) x))).
  - rewrite grp_inv_mul.
    rewrite grp_inv_inv.
    reflexivity.
  - now apply GrpImage_inv.
Qed.

Lemma grp_coset_trans (x y z : carrier H) :
  grp_coset_rel x y → grp_coset_rel y z → grp_coset_rel x z.
Proof.
  intros Hxy Hyz.
  unfold grp_coset_rel in *.
  apply (GrpImage_respects
           (grp_mul H (grp_mul H (grp_inv H z) y)
                      (grp_mul H (grp_inv H y) x))).
  - rewrite grp_mul_assoc.
    rewrite <- (grp_mul_assoc H y (grp_inv H y) x).
    rewrite grp_mul_inv_r.
    now rewrite grp_mul_unit_l.
  - now apply GrpImage_mul.
Qed.

Lemma grp_coset_equivalence : Equivalence grp_coset_rel.
Proof.
  constructor.
  - exact grp_coset_refl.
  - exact grp_coset_sym.
  - exact grp_coset_trans.
Qed.

(* The coset space of the image, as a setoid. / 作为集合同构的像的陪集空间。 *)
Definition Grp_Coset : SetoidObject :=
  {| carrier   := carrier H
   ; is_setoid := {| equiv        := grp_coset_rel
                   ; setoid_equiv := grp_coset_equivalence |} |}.

(*
 Coset-equivalent elements lie in the image together.  Like the equivalence
 laws above, this uses the image's being a SUBGROUP rather than merely a
 subset, through [GrpImage_mul] and [GrpImage_inv]. 

 --------
 陪集等价的元素一起位于像中。像的这个特性与上面的等价律类似，它使用了像是一个子群而不仅仅是一个子集，通过  [GrpImage_mul] 和 [GrpImage_inv] 实现。
*)
Lemma GrpImage_coset (x y : carrier H) :
  grp_coset_rel x y → GrpImage f x → GrpImage f y.
Proof.
  intros Hxy Hx.
  apply (GrpImage_respects (grp_mul H x (grp_inv H (grp_mul H (grp_inv H y) x)))).
  - rewrite grp_inv_mul.
    rewrite grp_inv_inv.
    rewrite <- grp_mul_assoc.
    rewrite grp_mul_inv_r.
    apply grp_mul_unit_l.
  - apply GrpImage_mul; [assumption|].
    now apply GrpImage_inv.
Qed.

Lemma GrpImage_coset_iff (x y : carrier H) :
  grp_coset_rel x y → GrpImage f x ↔ GrpImage f y.
Proof.
  intro Hxy.
  split.
  - now apply GrpImage_coset.
  - apply GrpImage_coset.
    now apply grp_coset_sym.
Qed.

(*
 Left translation by [a], as a setoid map of the coset space: the coset
 relation is preserved because (ay)⁻¹(ax) ≈ y⁻¹x. 

 --------
 由 [a] 提供的左翻译，作为陪集空间的集合映射：陪集关系被保留，因为 (ay)⁻¹(ax) ≈ y⁻¹x。
*)
Program Definition grp_translate (a : carrier H) :
  SetoidMorphism Grp_Coset Grp_Coset := {| morphism := grp_mul H a |}.
Next Obligation.
  intros a x y Hxy.
  simpl in *.
  unfold grp_coset_rel in *.
  apply (GrpImage_respects (grp_mul H (grp_inv H y) x)); [|assumption].
  rewrite grp_inv_mul.
  rewrite grp_mul_assoc.
  rewrite <- (grp_mul_assoc H (grp_inv H a) a x).
  rewrite grp_mul_inv_l.
  now rewrite grp_mul_unit_l.
Qed.

(* Translating by an element OF the image does not change image membership. This is the M-equivariance input to the twist below. / 通过图像的一个元素进行平移不会改变图像的归属。这是下面扭曲操作的 M-等变性输入。 *)
Lemma GrpImage_translate (m c : carrier H) :
  GrpImage f m →
  (GrpImage f (grp_mul H (grp_inv H m) c) ↔ GrpImage f c).
Proof.
  intro Hm.
  split.
  - intro Hmc.
    apply (GrpImage_respects (grp_mul H m (grp_mul H (grp_inv H m) c))).
    + rewrite <- grp_mul_assoc.
      rewrite grp_mul_inv_r.
      apply grp_mul_unit_l.
    + now apply GrpImage_mul.
  - intro Hc.
    apply GrpImage_mul; [|assumption].
    now apply GrpImage_inv.
Qed.

End Image.

Arguments grp_coset_rel {G H} f _ _.
Arguments Grp_Coset {G H} f.
Arguments grp_translate {G H} f a.

(* * ** The symmetric group of a setoid / * ** 一个集合的对称群 *)

(*
 A permutation of a setoid: an invertible setoid map, presented as a pair of
 setoid maps with both round trips up to `≈`.  Nothing here is a bijection on
 the nose; the inverse is data, so no choice principle is involved. 

 --------
 一个集合等价类的置换：一个可逆的集合等价类映射，表示为一对集合等价类映射，并且两次往返均达到 `≈`。这里没有任何东西是精确的一一对应；逆映射是数据，因此不涉及选择原则。
*)
Record SetoidPermutation (X : SetoidObject) := {
  sperm_to   : SetoidMorphism X X;
  sperm_from : SetoidMorphism X X;

  sperm_to_from : ∀ x, sperm_to (sperm_from x) ≈ x;
  sperm_from_to : ∀ x, sperm_from (sperm_to x) ≈ x
}.

Arguments sperm_to {X} _.
Arguments sperm_from {X} _.
Arguments sperm_to_from {X} _ _.
Arguments sperm_from_to {X} _ _.

(*
 The backward map of a permutation is determined by the forward one, so
 comparing permutations on their forward maps alone loses nothing.  This is
 why the setoid below mentions only [sperm_to]. 

 --------
 一个排列的逆映射由它的正映射决定，因此仅比较排列的正映射不会丢失任何信息。这就是下方的集合只提到 [sperm_to] 的原因。
*)
Lemma sperm_from_determined {X : SetoidObject} (p q : SetoidPermutation X) :
  (∀ x, sperm_to p x ≈ sperm_to q x) → ∀ x, sperm_from p x ≈ sperm_from q x.
Proof.
  intros Hpq x.
  transitivity (sperm_from q (sperm_to q (sperm_from p x))).
  - symmetry.
    apply (sperm_from_to q).
  - apply (proper_morphism (sperm_from q)).
    transitivity (sperm_to p (sperm_from p x)).
    + symmetry.
      apply Hpq.
    + apply (sperm_to_from p).
Qed.

(*
 Two permutations are equivalent when their forward maps agree pointwise;
 by [sperm_from_determined] the backward maps then agree as well.  Stating
 the relation on the forward map alone keeps the obligations small. 

 --------
 当两个置换的前向映射在每一点上都相同时，它们是等价的；因此其反向映射也会相应一致。仅在前向映射上陈述关系可以保持义务的简单性。
*)
#[export]
Program Instance SetoidPermutation_Setoid (X : SetoidObject) :
  Setoid (SetoidPermutation X) := {|
  equiv := λ p q, ∀ x, sperm_to p x ≈ sperm_to q x
|}.
Next Obligation.
  intro X.
  constructor.
  - intros p x.
    reflexivity.
  - intros p q Hpq x.
    now symmetry.
  - intros p q r Hpq Hqr x.
    now transitivity (sperm_to q x).
Qed.

(* G4. Permutations are compared pointwise on their forward maps, so a permutation setoid is propositional whenever the underlying setoid is. / G4. 排列在它们的前向映射上逐点比较，因此当底层集合同构时，排列集合同构是命题性的。 *)
Definition SetoidPermutation_PropEquiv (X : SetoidObject)
  (PX : PropEquiv (is_setoid X)) : PropEquiv (SetoidPermutation_Setoid X).
Proof.
  unshelve refine
    {| pequiv := fun p q : SetoidPermutation X =>
                   forall x : carrier X,
                     @pequiv _ _ PX (sperm_to p x) (sperm_to q x) |}.
  - intros p q Hpq x; exact (pequiv_to _ _ (Hpq x)).
  - intros p q Hpq x; exact (pequiv_from _ _ (Hpq x)).
Defined.

Program Definition sperm_id (X : SetoidObject) : SetoidPermutation X := {|
  sperm_to   := setoid_morphism_id;
  sperm_from := setoid_morphism_id
|}.
Next Obligation. intros X x; reflexivity. Qed.
Next Obligation. intros X x; reflexivity. Qed.

Program Definition sperm_compose {X : SetoidObject}
        (p q : SetoidPermutation X) : SetoidPermutation X := {|
  sperm_to   := setoid_morphism_compose (sperm_to p) (sperm_to q);
  sperm_from := setoid_morphism_compose (sperm_from q) (sperm_from p)
|}.
Next Obligation.
  intros X p q x; simpl.
  rewrite (sperm_to_from q (sperm_from p x)).
  apply (sperm_to_from p).
Qed.
Next Obligation.
  intros X p q x; simpl.
  rewrite (sperm_from_to p (sperm_to q x)).
  apply (sperm_from_to q).
Qed.

Definition sperm_inv {X : SetoidObject} (p : SetoidPermutation X) :
  SetoidPermutation X := {|
  sperm_to      := sperm_from p;
  sperm_from    := sperm_to p;
  sperm_to_from := sperm_from_to p;
  sperm_from_to := sperm_to_from p
|}.

(*
 The symmetric group of a setoid: permutations under composition.  This is
 the “permutations as invertible setoid maps” the argument needs.

 RECORDED STRENGTH CHANGE.  Before the PR “algebraic carriers are sets”
 (2026-09-17) this read [SymGrp (X : SetoidObject) : GrpObject].  A
 [GrpObject] now carries [grp_prop], so the symmetric group is formed only
 of a setoid that is itself propositional, and [PX] is an explicit second
 argument.  Every one of the thirteen call sites below discharges it, so
 nothing in this file is conditional in substance; what changed is the
 signature, and the theorems whose STATEMENTS mention [SymGrp] now mention
 the witness too. 

 --------
 一个集合同构的对称群：在复合下的置换。这就是论证所需要的“作为可逆集合同构映射的置换”。

 已记录的强度变化。在 PR “代数载体是集合”（2026-09-17）之前，这里是 [SymGrp (X : SetoidObject) : GrpObject]。现在 [GrpObject] 携带 [grp_prop]，因此对称群仅由自身为命题性的集合同构构成，并且 [PX] 是一个显式的第二个参数。下面的十三个调用点中的每一个都处理了它，所以此文件中的内容在实质上没有条件变化；变化的是签名，以及其陈述中提到 [SymGrp] 的定理现在也提到了该见证。
*)
Definition SymGrp (X : SetoidObject) (PX : PropEquiv (is_setoid X)) :
  GrpObject.
Proof.
  unshelve notypeclasses refine {|
    grp_setoid := {| carrier   := SetoidPermutation X
                   ; is_setoid := SetoidPermutation_Setoid X |};
    grp_unit := sperm_id X;
    grp_mul  := @sperm_compose X;
    grp_inv  := @sperm_inv X;
    grp_prop := SetoidPermutation_PropEquiv X PX
  |}.
  - (* composition respects `≈` / 作品尊重 `≈` *)
    intros p p' Hp q q' Hq x; simpl.
    rewrite (Hq x).
    exact (Hp (sperm_to q' x)).
  - (* associativity, on the nose after unfolding composition / 结合性，在展开组合后正中要点 *)
    intros p q r x; simpl.
    reflexivity.
  - (* left unit / 左单元 *)
    intros p x; simpl.
    reflexivity.
  - (* left inverse: the backward round trip / 左逆：反向往返 *)
    intros p x; simpl.
    apply (sperm_from_to p).
Defined.

(** ** Inner automorphisms / ** 内自同构 *)

Program Definition grp_conj_map (K : GrpObject) (s : carrier K) :
  SetoidMorphism (grp_setoid K) (grp_setoid K) :=
  {| morphism := λ a, grp_mul K (grp_mul K s a) (grp_inv K s) |}.
Next Obligation.
  intros K s a b Hab.
  now rewrite Hab.
Qed.

Lemma grp_conj_mul (K : GrpObject) (s a b : carrier K) :
  grp_mul K (grp_mul K s (grp_mul K a b)) (grp_inv K s)
    ≈ grp_mul K (grp_mul K (grp_mul K s a) (grp_inv K s))
                (grp_mul K (grp_mul K s b) (grp_inv K s)).
Proof.
  assert (Hcancel : ∀ c : carrier K,
             grp_mul K (grp_inv K s) (grp_mul K s c) ≈ c).
  { intro c.
    rewrite <- grp_mul_assoc.
    rewrite grp_mul_inv_l.
    apply grp_mul_unit_l. }
  rewrite !grp_mul_assoc.
  rewrite Hcancel.
  reflexivity.
Qed.

(*
 Conjugation by a fixed element is an endomorphism of the group; classically
 it is the inner automorphism at [s], but invertibility is neither proved
 here nor needed -- only the homomorphism property is used below. 

 --------
 由固定元素的共轭是群的一个自同态；传统上它是在 [s] 处的内自同构，但这里既未证明可逆性，也不需要——下面只使用了同态性质。
*)
Definition grp_conj (K : GrpObject) (s : carrier K) : K ~{Grp}~> K :=
  Build_GrpHom' (grp_conj_map K s) (grp_conj_mul K s).

(* * ** The action of H on the stable power set of the coset space / * ** H 在陪集空间的稳定幂集上的作用 *)

Section Epi.

Context {G H : GrpObject}.
Context (f : G ~{Grp}~> H).

(*
 The stable-valued “power set” of the coset space: setoid maps from the
 cosets of the image to the stable propositions.  This is the H-set the
 argument permutes. 

 --------
 余类空间的稳定值“幂集”：从像的余类到稳定命题的集合映射。这就是参数进行置换的 H-集。
*)
Definition GrpCosetPower : SetoidObject :=
  {| carrier   := SetoidMorphism (Grp_Coset f) StableSetoid
   ; is_setoid := @SetoidMorphism_Setoid (Grp_Coset f) StableSetoid |}.

(*
 The witness [SymGrp] asks for at this setoid.  It comes from the TARGET
 alone -- [hom_PropEquiv] (Instance/Sets/Propositional.v) constrains only
 the codomain -- so NOTHING is asked of [Grp_Coset f], and in particular
 [grp_coset_rel] is NOT truncated by this change. 

 --------
 证人 [SymGrp] 在这个集合中提出请求。它仅来自目标 —— [hom_PropEquiv]（Instance/Sets/Propositional.v）只限制了余域 —— 因此对 [Grp_Coset f] 没有任何要求，特别是 [grp_coset_rel] 并未因这一更改而被截断。
*)
Definition grp_coset_power_prop : PropEquiv (is_setoid GrpCosetPower) :=
  @hom_PropEquiv (Grp_Coset f) StableSetoid StableSetoid_PropEquiv.

(* The left action of H, (h · S)(c) = S(h⁻¹ c). / H 的左作用，(h · S)(c) = S(h⁻¹ c)。 *)
Program Definition grp_act_map (h : carrier H) :
  SetoidMorphism GrpCosetPower GrpCosetPower :=
  {| morphism := λ S,
       setoid_morphism_compose S (grp_translate f (grp_inv H h)) |}.
Next Obligation.
  intros h S S' HS c; simpl.
  exact (HS _).
Qed.

Program Definition grp_act (h : carrier H) :
  SetoidPermutation GrpCosetPower := {|
  sperm_to   := grp_act_map h;
  sperm_from := grp_act_map (grp_inv H h)
|}.
Next Obligation.
  intros h S c; simpl.
  apply (proper_morphism S).
  apply grp_coset_of_equiv.
  rewrite grp_inv_inv.
  rewrite <- grp_mul_assoc.
  rewrite grp_mul_inv_r.
  apply grp_mul_unit_l.
Qed.
Next Obligation.
  intros h S c; simpl.
  apply (proper_morphism S).
  apply grp_coset_of_equiv.
  rewrite grp_inv_inv.
  rewrite <- grp_mul_assoc.
  rewrite grp_mul_inv_l.
  apply grp_mul_unit_l.
Qed.

Program Definition grp_action_map :
  SetoidMorphism (grp_setoid H) (grp_setoid (SymGrp GrpCosetPower grp_coset_power_prop)) :=
  {| morphism := grp_act |}.
Next Obligation.
  intros h h' Hh S c; simpl.
  apply (proper_morphism S).
  apply grp_coset_of_equiv.
  now rewrite Hh.
Qed.

Lemma grp_action_mul (h1 h2 : carrier H) :
  grp_act (grp_mul H h1 h2)
    ≈ grp_mul (SymGrp GrpCosetPower grp_coset_power_prop) (grp_act h1) (grp_act h2).
Proof.
  intros S c; simpl.
  apply (proper_morphism S).
  apply grp_coset_of_equiv.
  rewrite grp_inv_mul.
  apply grp_mul_assoc.
Qed.

(* H acts on the stable power set of its coset space by permutations. / H 通过排列作用于其陪集空间的稳定幂集。 *)
Definition grp_action : H ~{Grp}~> SymGrp GrpCosetPower grp_coset_power_prop :=
  Build_GrpHom' grp_action_map grp_action_mul.

(* * ** The twist: an involution that is equivariant for the image only / * ** 扭曲：仅对图像等变的自同构 *)

(*
 The twisted membership predicate at a coset: [S] with its value at the base
 coset complemented.  Constructively one cannot say “complemented at the base
 coset AND unchanged elsewhere” by cases -- that needs a decision procedure
 for membership in the image.  The formula below says the same thing without
 deciding anything, and it is an involution precisely because the values are
 double-negation stable. 

 --------
 在一个陪集上的扭曲成员谓词：[S]，其在基陪集的值被补充。按构造方法不能通过分情况说“在基陪集上补充且其他地方不变”——这需要一个对像中成员资格的判定程序。下面的公式在不判定任何事情的情况下表达了同样的意思，并且它正好是一个自反映射，因为这些值在双重否定下保持稳定。
*)
Definition grp_twist_ty (S : carrier GrpCosetPower) (c : carrier H) : Prop :=
  (GrpImage f c → ¬ `1 (S c)) /\ (¬ GrpImage f c → `1 (S c)).

Lemma grp_twist_stable (S : carrier GrpCosetPower) (c : carrier H) :
  Stable (grp_twist_ty S c).
Proof.
  unfold grp_twist_ty.
  apply stable_and.
  - apply stable_arrow.
    apply stable_not.
  - apply stable_arrow.
    exact (`2 (S c)).
Qed.

Program Definition grp_twist_val (S : carrier GrpCosetPower) :
  SetoidMorphism (Grp_Coset f) StableSetoid :=
  {| morphism := λ c, (grp_twist_ty S c; grp_twist_stable S c) |}.
Next Obligation.
  intros S x y Hxy.
  destruct (GrpImage_coset_iff f x y Hxy) as [Exy Eyx].
  destruct (proper_morphism S x y Hxy) as [Sxy Syx].
  split.
  - intros [A B].
    split.
    + intros hy sy.
      exact (A (Eyx hy) (Syx sy)).
    + intro ny.
      apply Sxy, B.
      intro hx.
      exact (ny (Exy hx)).
  - intros [A B].
    split.
    + intros hx sx.
      exact (A (Exy hx) (Sxy sx)).
    + intro nx.
      apply Syx, B.
      intro hy.
      exact (nx (Eyx hy)).
Qed.

Program Definition grp_twist_map :
  SetoidMorphism GrpCosetPower GrpCosetPower :=
  {| morphism := grp_twist_val |}.
Next Obligation.
  intros S S' HS c.
  destruct (HS c) as [Scc' Sc'c].
  split.
  - intros [A B].
    split.
    + intros hc sc'.
      exact (A hc (Sc'c sc')).
    + intro nc.
      exact (Scc' (B nc)).
  - intros [A B].
    split.
    + intros hc sc.
      exact (A hc (Scc' sc)).
    + intro nc.
      exact (Sc'c (B nc)).
Qed.

(*
 The twist is an involution.  Its forward direction is where stability of
 the values does its real work; the only other use of that stability is
 [grp_twist_stable] just above, which merely checks that a twisted value is
 again stable, so that it lands in [StableProp] at all. 

 --------
 这个扭转是一个自反变换。它的正向方向是值的稳定性发挥其真正作用的地方；这种稳定性的唯一其他用途是在上面的 [grp_twist_stable]，它只是检查一个扭转后的值再次稳定，以便它能够落入 [StableProp]。
*)
Lemma grp_twist_involutive (S : carrier GrpCosetPower) (c : carrier H) :
  grp_twist_ty (grp_twist_val S) c ↔ `1 (S c).
Proof.
  split.
  - intro A.
    apply (`2 (S c)).
    intro ns.
    assert (nne : ¬¬ GrpImage f c).
    { intro ne.
      exact (ns (proj2 (proj2 A ne) ne)). }
    assert (Ht : grp_twist_ty S c).
    { split.
      - intros _.
        exact ns.
      - intro ne.
        destruct (nne ne). }
    exact (nne (λ He, proj1 A He Ht)).
  - intros Hs.
    split.
    + intros He Ht.
      exact (proj1 Ht He Hs).
    + intro Hne.
      split.
      * intro He.
        destruct (Hne He).
      * intros _.
        exact Hs.
Qed.

Lemma grp_twist_roundtrip (S : carrier GrpCosetPower) :
  grp_twist_map (grp_twist_map S) ≈ S.
Proof.
  intro c.
  apply grp_twist_involutive.
Qed.

Definition grp_twist : carrier (SymGrp GrpCosetPower grp_coset_power_prop) := {|
  sperm_to      := grp_twist_map;
  sperm_from    := grp_twist_map;
  sperm_to_from := grp_twist_roundtrip;
  sperm_from_to := grp_twist_roundtrip
|}.

(* The twisted action: conjugate the action by the twist. / 扭曲的动作：通过扭曲来共轭动作。 *)
Definition grp_twisted_action : H ~{Grp}~> SymGrp GrpCosetPower grp_coset_power_prop :=
  grp_conj (SymGrp GrpCosetPower grp_coset_power_prop) grp_twist ∘[Grp] grp_action.

(* * ** The twist commutes with the image, and only with the image / * ** 扭转与图像交换运算，仅与图像交换运算 *)

Lemma grp_twist_act_commute (g : carrier G) (S : carrier GrpCosetPower) :
  grp_twist_map (grp_act_map (grp_map f g) S)
    ≈ grp_act_map (grp_map f g) (grp_twist_map S).
Proof.
  intro c.
  assert (Hm : GrpImage f (grp_map f g)).
  { exists g.
    reflexivity. }
  destruct (GrpImage_translate f (grp_map f g) c Hm) as [Emc Ecm].
  split.
  - intros [A B].
    split.
    + intros hmc smc.
      exact (A (Emc hmc) smc).
    + intro nmc.
      apply B.
      intro hc.
      exact (nmc (Ecm hc)).
  - intros [A B].
    split.
    + intros hc smc.
      exact (A (Ecm hc) smc).
    + intro nc.
      apply B.
      intro hmc.
      exact (nc (Emc hmc)).
Qed.

(* The two homomorphisms agree after f. / 两个同态在 f 之后是相同的。 *)
Lemma grp_twisted_action_agrees :
  grp_twisted_action ∘[Grp] f ≈ grp_action ∘[Grp] f.
Proof.
  intro g.
  intro S.
  transitivity (grp_act_map (grp_map f g)
                  (grp_twist_map (grp_twist_map S))).
  - apply grp_twist_act_commute.
  - apply (proper_morphism (grp_act_map (grp_map f g))).
    apply grp_twist_roundtrip.
Qed.

(* The distinguished stable subset: the double negation of image membership. / 显著的稳定子集：映像成员资格的双重否定。 *)
Program Definition grp_dense_subset :
  SetoidMorphism (Grp_Coset f) StableSetoid :=
  {| morphism := λ c, (¬¬ GrpImage f c ; stable_not_not (GrpImage f c)) |}.
Next Obligation.
  intros x y Hxy.
  destruct (GrpImage_coset_iff f x y Hxy) as [Exy Eyx].
  split.
  - intros nnx ny.
    exact (nnx (λ hx, ny (Exy hx))).
  - intros nny nx.
    exact (nny (λ hy, nx (Eyx hy))).
Qed.

(* An element outside the image stays outside it after inversion and after multiplying by the unit -- the shape in which the action presents it. / 图像之外的元素在反演之后以及乘以单位之后仍然保持在外部——动作呈现它的形状。 *)
Lemma grp_image_misses_translate (h0 : carrier H) (Hh0 : ¬ GrpImage f h0) :
  ¬ GrpImage f (grp_mul H (grp_inv H h0) (grp_unit H)).
Proof.
  intro Hin.
  apply Hh0.
  apply (GrpImage_respects f
           (grp_inv H (grp_mul H (grp_inv H h0) (grp_unit H)))).
  - rewrite grp_mul_unit_r.
    apply grp_inv_inv.
  - now apply GrpImage_inv.
Qed.

(*
 At an element outside the image the action is not the identity permutation.
 So the homomorphism being conjugated below is not the constant map at the
 unit, and the argument is not a comparison of two trivial maps.  (Nothing
 is claimed here about elements INSIDE the image; that case is the subject
 of the next block, and it turns on whether the image is normal.) 

 --------
 在像外的元素上，该作用不是恒等置换。
 因此，下面被共轭的同态不是单位元上的常值映射，并且该论证不是两个平凡映射的比较。（这里并没有对像内的元素作出任何声明；该情况是下一部分的主题，它取决于像是否为正规子群。）
*)
Lemma grp_action_not_identity (h0 : carrier H) (Hh0 : ¬ GrpImage f h0) :
  grp_act h0 ≈ grp_unit (SymGrp GrpCosetPower grp_coset_power_prop) → False.
Proof.
  intro Heq.
  destruct (Heq grp_dense_subset (grp_unit H)) as [Hfwd Hbwd].
  assert (Hnn : ¬¬ GrpImage f (grp_unit H)).
  { intro Hno.
    exact (Hno (GrpImage_unit f)). }
  exact (Hbwd Hnn (grp_image_misses_translate h0 Hh0)).
Qed.

(* * ** When an element OF the image moves the coset space / * ** 当图像的一个元素移动陪集空间 *)

(*
 The stable subset picked out by a single coset: the indicator of x0·M,
 double-negated so that it lands in [StableProp].  Being a union of cosets
 -- here a single one -- is exactly what makes the indicator respect the
 coset relation, so it is a legitimate element of [GrpCosetPower].  At the
 base coset it recovers [grp_dense_subset], which is
 [grp_coset_indicator_base] below. 

 --------
 由单个陪集选出的稳定子集：x0·M 的指示函数，双重否定以使其落在 [StableProp] 中。作为陪集的并集——这里是单个陪集——正是使指示函数尊重陪集关系的原因，因此它是 [GrpCosetPower] 的合法元素。在基陪集上，它重现 [grp_dense_subset]，即下面的 [grp_coset_indicator_base]。
*)
Program Definition grp_coset_indicator (x0 : carrier H) :
  SetoidMorphism (Grp_Coset f) StableSetoid :=
  {| morphism := λ c, (¬¬ grp_coset_rel f c x0 ; stable_not_not _) |}.
Next Obligation.
  intros x0 x y Hxy.
  split.
  - intros nnx ny.
    apply nnx; intro hx.
    exact (ny (grp_coset_trans f y x x0 (grp_coset_sym f x y Hxy) hx)).
  - intros nny nx.
    apply nny; intro hy.
    exact (nx (grp_coset_trans f x y x0 Hxy hy)).
Qed.

(* The indicator of the base coset is the distinguished subset already in use, so the two blocks are about the same construction and not two of them. / 基协类的指示符是已经在使用的特殊子集，因此这两个块大约是相同的构造，而不是两个不同的块。 *)
Lemma grp_coset_indicator_base :
  grp_coset_indicator (grp_unit H) ≈ grp_dense_subset.
Proof.
  intro c.
  assert (Hto : @equiv _ (is_setoid (grp_setoid H))
                  (grp_mul H (grp_inv H (grp_unit H)) c) c).
  { rewrite grp_inv_unit.
    apply grp_mul_unit_l. }
  assert (Hfrom : @equiv _ (is_setoid (grp_setoid H)) c
                    (grp_mul H (grp_inv H (grp_unit H)) c)).
  { symmetry.
    exact Hto. }
  split.
  - intros nn nc.
    apply nn; intro hc.
    exact (nc (GrpImage_respects f _ c Hto hc)).
  - intros nn nc.
    apply nn; intro hc.
    exact (nc (GrpImage_respects f c _ Hfrom hc)).
Qed.

(*
 Translation by m moves the coset x0·M as soon as x0⁻¹m⁻¹x0 lies outside the
 image -- which is precisely where normality gives out.  Evaluating at x0,
 the indicator of x0·M holds while its translate does not, and that single
 disagreement is the whole content.  Nothing here asks m to be in the image;
 the point of the lemma is that it may be, which is what makes the
 equivariance step [grp_twist_act_commute] a statement about permutations
 that actually move something. 

 --------
 由 m 进行的平移会移动陪集 x0·M，只要 x0⁻¹m⁻¹x0 落在像之外——这正是正规性失效的地方。在 x0 处评估时，x0·M 的指示函数成立，而它的平移则不成立，而那一个不一致就是全部内容。这里并不要求 m 在像中；引理的要点是它可以在其中，这也是使等变性步骤 [grp_twist_act_commute] 成为关于实际上移动某些元素的置换的陈述的原因。
*)
Lemma grp_act_moves_coset (m x0 : carrier H) :
  ¬ GrpImage f (grp_mul H (grp_inv H x0) (grp_mul H (grp_inv H m) x0)) →
  grp_act_map m (grp_coset_indicator x0) ≈ grp_coset_indicator x0 → False.
Proof.
  intros Hout Heq.
  destruct (Heq x0) as [_ Hbwd].
  exact (Hbwd (λ n, n (grp_coset_refl f x0)) Hout).
Qed.

(*
 The same thing one level up, and stated for an element OF the image: if
 some conjugate of f g escapes the image, then f g does not act by the
 identity permutation of [GrpCosetPower]. 

 --------
 同样的事情，但在上一级，并针对图像的一个元素说明：如果 f g 的某个共轭变换逃出了图像，那么 f g 就不是通过 [GrpCosetPower] 的恒等置换作用的。
*)
Lemma grp_image_acts_nontrivially (g : carrier G) (x0 : carrier H) :
  ¬ GrpImage f (grp_mul H (grp_inv H x0)
                  (grp_mul H (grp_inv H (grp_map f g)) x0)) →
  grp_act (grp_map f g) ≈ grp_unit (SymGrp GrpCosetPower grp_coset_power_prop) → False.
Proof.
  intros Hout Heq.
  exact (grp_act_moves_coset (grp_map f g) x0 Hout
           (Heq (grp_coset_indicator x0))).
Qed.

(* At an element OUTSIDE the image the twist does not commute with the action: the two sides disagree at the distinguished subset and the base coset. / 在图像之外的元素上，扭曲与作用不交换：两边在特别子集和基础陪集上不一致。 *)
Lemma grp_twist_act_not_commute (h0 : carrier H) (Hh0 : ¬ GrpImage f h0) :
  grp_twist_map (grp_act_map h0 grp_dense_subset)
    ≈ grp_act_map h0 (grp_twist_map grp_dense_subset) → False.
Proof.
  intro Heq.
  pose proof (grp_image_misses_translate h0 Hh0) as Hne.
  destruct (Heq (grp_unit H)) as [Hfwd Hbwd].
  assert (HL : grp_twist_ty (grp_act_map h0 grp_dense_subset) (grp_unit H)).
  { split.
    - intros _ Hnn.
      exact (Hnn Hne).
    - intro Hno.
      destruct (Hno (GrpImage_unit f)). }
  destruct (Hfwd HL) as [_ B].
  exact (B Hne Hne).
Qed.

(*
 The two homomorphisms are distinct in the hom-setoid of [Grp], witnessed at
 the concrete element [h0] of H and the concrete permutation argument
 [grp_twist_map grp_dense_subset]. 

 --------
 这两个同态在  [Grp] 的同集上是不同的，其证据在 H 的具体元素  [h0] 和具体置换参数  [grp_twist_map grp_dense_subset] 上体现。
*)
Lemma grp_actions_differ (h0 : carrier H) (Hh0 : ¬ GrpImage f h0) :
  grp_twisted_action ≈ grp_action → False.
Proof.
  intro Heq.
  apply (grp_twist_act_not_commute h0 Hh0).
  transitivity (grp_twist_map
                  (grp_act_map h0 (grp_twist_map
                                     (grp_twist_map grp_dense_subset)))).
  - apply (proper_morphism grp_twist_map).
    apply (proper_morphism (grp_act_map h0)).
    symmetry.
    apply grp_twist_roundtrip.
  - exact (Heq h0 (grp_twist_map grp_dense_subset)).
Qed.

(*
 The twist is never the identity permutation, for any f whatsoever: the
 permutation group in play is therefore never the trivial group, and the
 witness above is not secretly the unit. 

 --------
 对于任何函数 f，转动从来都不是恒等排列：因此所涉及的排列群从来都不是平凡群，上述证据也并非暗中是单位元。
*)
Lemma grp_twist_not_identity :
  grp_twist ≈ grp_unit (SymGrp GrpCosetPower grp_coset_power_prop) → False.
Proof.
  intro Heq.
  destruct (Heq grp_dense_subset (grp_unit H)) as [Hfwd Hbwd].
  assert (Hnn : ¬¬ GrpImage f (grp_unit H)).
  { intro Hno.
    exact (Hno (GrpImage_unit f)). }
  destruct (Hbwd Hnn) as [A _].
  exact (A (GrpImage_unit f) Hnn).
Qed.

(** ** The theorems / ** 定理 *)

(*
 THE MAIN THEOREM, in its constructive contrapositive form.  Given an element
 of the codomain TOGETHER WITH a proof that it has no preimage, f is not an
 epimorphism.  The witness is an explicit hypothesis because the passage from
 “not surjective” to “some element misses the image” is not constructive. 

 --------
 主要定理，以其构造性的逆否形式给出。给定余域的一个元素以及它没有原像的证明，f 不是一个满射。这个证据是一个明确的假设，因为从“非满射”到“某些元素不在像中”的推导不是构造性的。
*)
Theorem grp_not_epic_of_witness (h0 : carrier H) :
  ¬ GrpImage f h0 → ¬ Epic f.
Proof.
  intros Hh0 [Hepic].
  apply (grp_actions_differ h0 Hh0).
  apply Hepic.
  apply grp_twisted_action_agrees.
Qed.

(* The unconditional positive reading: the image of an epimorphism of groups is dense, i.e. no element of the codomain can be shown to miss it. / 无条件正读：群的一个满射的像是稠密的，即不能证明陪域中的任何元素不在它之中。 *)
Theorem grp_epic_image_dense :
  Epic f → ∀ h : carrier H, ¬¬ GrpImage f h.
Proof.
  intros Hepic h Hno.
  exact (grp_not_epic_of_witness h Hno Hepic).
Qed.

(* The easy direction, unconditional. / 简单的方向，无条件的。 *)
Theorem grp_surjective_is_epic : GrpSurjective f → Epic f.
Proof.
  intro Hsurj.
  constructor.
  intros z g1 g2 Heq h.
  destruct (Hsurj h) as [g Hg].
  rewrite <- Hg.
  exact (Heq g).
Qed.

(*
 The hypothesis under which the classical statement is recovered: membership
 in the image is its own double negation.  It is named here for legibility,
 not because it is an independent principle -- [stability_is_the_conclusion]
 below shows that under [Epic f] it is the conclusion itself. 

 --------
 恢复经典陈述的假设：属于像本身就是其自身的双重否定。这里为了可读性而命名它，并不是因为它是一个独立的原理——下面的 [stability_is_the_conclusion] 显示在 [Epic f] 下它本身就是结论。
*)
Definition GrpImageStable : Type := ∀ h : carrier H, Stable (GrpImage f h).

(* A decision procedure for image membership is one way to have it. / 图像成员资格的判定程序是一种实现它的方法。 *)
Definition GrpImageDecidable : Type :=
  ∀ h : carrier H, GrpImage f h ∨ ¬ GrpImage f h.

Lemma GrpImageDecidable_Stable : GrpImageDecidable → GrpImageStable.
Proof.
  intros Hdec h Hnn.
  destruct (Hdec h) as [Hin|Hout].
  - exact Hin.
  - destruct (Hnn Hout).
Qed.

Theorem grp_epic_is_surjective : GrpImageStable → Epic f → GrpSurjective f.
Proof.
  intros Hstable Hepic h.
  apply Hstable.
  exact (grp_epic_image_dense Hepic h).
Qed.

(* Mac Lane's Exercise I.5.5, in the form this library can state: over a codomain whose image membership is double-negation stable, the epimorphisms of Grp are exactly the surjections. / Mac Lane练习题 I.5.5，以该库可以表述的形式：在像的成员资格是双重否定稳定的陪域上，Grp 的满射正是其原像态射。 *)
Theorem grp_epic_iff_surjective :
  GrpImageStable → (Epic f ↔ GrpSurjective f).
Proof.
  intro Hstable.
  split.
  - now apply grp_epic_is_surjective.
  - apply grp_surjective_is_epic.
Qed.

(* * ** The hypothesis is the conclusion / * ** 假设就是结论 *)

(*
 [GrpImageStable] looks like a modest extra assumption bought cheaply.  The
 results below show it is not an assumption of independent standing at all:
 once [grp_epic_image_dense] is in hand, it is the conclusion of the theorem
 restated.  Every proof here is one or two lines from what precedes it, which
 is precisely the point -- the deflation is immediate the moment one looks
 for it. 

 --------
 [GrpImageStable] 看起来像是一个以低成本换来的适度额外假设。下面的结果显示，它根本不是一个独立存在的假设：一旦 [grp_epic_image_dense] 到手，它就是重新陈述的定理的结论。这里的每一个证明都只比前面的内容多一两行，这正是重点——一旦去寻找，简化是立竿见影的。
*)

(* The trivial half: surjectivity gives stability outright. / 平凡的一半：满射性直接提供稳定性。 *)
Theorem surjective_gives_stable : GrpSurjective f → GrpImageStable.
Proof. intros Hs h _; exact (Hs h). Qed.

(*
 Hence for an EPIMORPHISM the hypothesis is EQUIVALENT to the conclusion it
 is supposed to buy, and [grp_epic_is_surjective] adds nothing beyond the
 unconditional [grp_epic_image_dense]. 

 --------
 因此，对于一个上同态，假设与它应当得到的结论是等价的，而 [grp_epic_is_surjective] 并没有增加任何超出无条件 [grp_epic_image_dense] 的内容。
*)
Theorem stability_is_the_conclusion (Hepic : Epic f) :
  GrpImageStable ↔ GrpSurjective f.
Proof.
  split.
  - intro Hst.
    exact (grp_epic_is_surjective Hst Hepic).
  - exact surjective_gives_stable.
Qed.

(*
 [GrpImageStable] is not even the weakest hypothesis that completes the
 proof.  All the argument ever does with it is discharge the double negation
 supplied by [grp_epic_image_dense], so the single implication from density
 to surjectivity -- with no pointwise structure at all -- already suffices.
 This is the “why is stability stated pointwise?” question answered: it need
 not be. 

 --------
 [GrpImageStable] 甚至不是完成证明所需的最弱假设。 对它的所有论证仅仅是消解由 [grp_epic_image_dense] 提供的双重否定，所以从密度到满射的单一蕴涵——根本不需要任何逐点结构——已经足够了。这就是“为什么稳定性要逐点陈述？”的问题的答案：它不需要逐点陈述。
*)
Definition DenseImpliesSurjective : Type :=
  (∀ h : carrier H, ¬¬ GrpImage f h) → GrpSurjective f.

Theorem weaker_hypothesis_suffices :
  DenseImpliesSurjective → Epic f → GrpSurjective f.
Proof.
  intros Hw He.
  exact (Hw (grp_epic_image_dense He)).
Qed.

Theorem stable_implies_weaker : GrpImageStable → DenseImpliesSurjective.
Proof. intros Hst Hd h; exact (Hst h (Hd h)). Qed.

Theorem surjective_gives_weaker : GrpSurjective f → DenseImpliesSurjective.
Proof. intros Hs _; exact Hs. Qed.

(* And the weaker form collapses in exactly the same way, so the deflation is not an artefact of how [GrpImageStable] is phrased. / 而较弱的形式也完全以相同的方式崩溃，因此通缩并不是 [GrpImageStable] 表述方式的一个人为产物。 *)
Theorem weaker_is_the_conclusion (Hepic : Epic f) :
  DenseImpliesSurjective ↔ GrpSurjective f.
Proof.
  split.
  - intro Hw.
    exact (weaker_hypothesis_suffices Hw Hepic).
  - exact surjective_gives_weaker.
Qed.

(* * ** Why the textbook transposition is not available / * ** 为什么教材中的调位不可用 *)

(*
 The classical H-set: the cosets of the image with one point adjoined.  This
 is the set the usually-quoted proof permutes, and it is built here only to
 state the obstruction to permuting it as that proof requires. 

 --------
 经典的 H 集：在映像上添加一个点后的陪集。这是通常引用的证明中所排列的集合，它在这里构建仅仅是为了说明按照该证明的要求排列它时所存在的阻碍。
*)
Definition CosetPlusPt : Type := carrier (Grp_Coset f) ∨ poly_unit.

Definition cpp_rel : crelation CosetPlusPt := λ x y,
  match x, y with
  | inl c, inl d => grp_coset_rel f c d
  | inr _, inr _ => poly_unit
  | _, _         => False
  end.

Lemma cpp_equivalence : Equivalence cpp_rel.
Proof.
  constructor.
  - intros [c|u]; simpl; [ apply grp_coset_refl | exact ttt ].
  - intros [c|u] [d|v]; simpl; try contradiction;
      [ apply grp_coset_sym | intros _; exact ttt ].
  - intros [c|u] [d|v] [e|w]; simpl; try contradiction;
      [ apply grp_coset_trans | intros _ _; exact ttt ].
Qed.

Definition CosetPlusPtSetoid : SetoidObject :=
  {| carrier   := CosetPlusPt
   ; is_setoid := {| equiv := cpp_rel ; setoid_equiv := cpp_equivalence |} |}.

(*
 Being the adjoined point is recognisable from the CONSTRUCTOR alone: this
 is a case split on a coproduct, not a decision procedure, and it is the
 only case split the theorem below performs. 

 --------
 从构造函数本身就可以识别出相邻的点：这是对余积的情况拆分，而不是决策程序，并且这是下面定理所执行的唯一情况拆分。
*)
Lemma cpp_is_pt_or_not (x : CosetPlusPt) :
  (@equiv _ (is_setoid CosetPlusPtSetoid) x (inr ttt))
    ∨ ¬ (@equiv _ (is_setoid CosetPlusPtSetoid) x (inr ttt)).
Proof.
  destruct x as [c|u].
  - right; intro Hx; exact Hx.
  - left; exact ttt.
Qed.

(*
 THE OBSTRUCTION, stated positively.  Suppose given any permutation t of the
 classical H-set satisfying merely the FIRST half of the transposition's
 specification: every coset lying inside the image goes to the adjoined
 point.  Then image membership is DECIDABLE.

 Nothing is assumed about what t does elsewhere, t is not required to be an
 involution, and the two clauses “exchange the base coset with the point”
 and “fix everything else” are not both used -- only the first.  So the
 textbook transposition cannot be constructed here without first having the
 decidability that this file exists to isolate; the transposition has to be
 replaced, and the twist on [GrpCosetPower] is what replaces it.

 The proof is the round trip of t.  If t sends the coset of h to the point,
 then it agrees there with the image it takes the base coset to, and
 applying [sperm_from] identifies h with the unit in the coset setoid, which
 puts h in the image; otherwise the hypothesis rules out h being in the
 image at all. 

 --------
 障碍，积极陈述。假设给定任意的经典 H-集合的排列 t，仅满足换位规范的前半部分：映像内的每个陪集都映射到附加点。然后，映像成员资格是可判定的。

 关于 t 在其他地方的行为没有任何假设，t 不需要是一个自反的排列，并且“两条款‘交换基陪集与该点’和‘固定其他所有’”并不都被使用——只使用第一条。因此，在没有首先拥有这个文件试图孤立的可判定性之前，教科书中的换位在此无法构造；换位必须被替换，而 [GrpCosetPower] 上的扭曲便是用来替代它的。证明是 t 的往返。如果 t 将 h 的陪集发送到某个点，那么它在该点上与它将基陪集送到的像一致，并且应用 [sperm_from] 将 h 与陪集合中的单位元关联起来，这将 h 放入像中；否则假设排除了 h 完全属于像的可能性。
*)
Theorem transposition_decides_image
  (t : SetoidPermutation CosetPlusPtSetoid)
  (Hbase : ∀ c, GrpImage f c →
             @equiv _ (is_setoid CosetPlusPtSetoid)
               (sperm_to t (inl c)) (inr ttt)) :
  GrpImageDecidable.
Proof.
  intro h.
  destruct (cpp_is_pt_or_not (sperm_to t (inl h))) as [Hpt|Hnpt].
  - left.
    assert (Hsame : @equiv _ (is_setoid CosetPlusPtSetoid)
                      (sperm_to t (inl h)) (sperm_to t (inl (grp_unit H)))).
    { transitivity (inr ttt : CosetPlusPt).
      - exact Hpt.
      - symmetry.
        exact (Hbase (grp_unit H) (GrpImage_unit f)). }
    assert (Hback : @equiv _ (is_setoid CosetPlusPtSetoid)
                      (inl h) (inl (grp_unit H))).
    { transitivity (sperm_from t (sperm_to t (inl h))).
      - symmetry; apply (sperm_from_to t).
      - transitivity (sperm_from t (sperm_to t (inl (grp_unit H)))).
        + apply (proper_morphism (sperm_from t)); exact Hsame.
        + apply (sperm_from_to t). }
    simpl in Hback.
    unfold grp_coset_rel in Hback.
    apply (GrpImage_respects f (grp_mul H (grp_inv H (grp_unit H)) h)).
    + rewrite grp_inv_unit.
      apply grp_mul_unit_l.
    + exact Hback.
  - right.
    intro Hin.
    exact (Hnpt (Hbase h Hin)).
Qed.

End Epi.

(* ------------------------------------------------------------------------ *)
(** ** Concrete witnesses / ** 具体证人 *)

(*
 Everything above is proved for an arbitrary homomorphism, so the file owes
 concrete instances at which the constructions can be inspected.  Two are
 built, and they are not interchangeable.  The first, [grp_two_incl], is the
 cheapest map that is not epic, and it exercises the outside-the-image half
 of the argument; its image is normal, and the inside-the-image half
 degenerates completely there -- which is proved, at
 [grp_two_incl_image_acts_trivially], rather than left unsaid.  The second,
 [grp_two_sym3], has a non-normal image, and it is there that the
 equivariance step compares permutations that move something.

 Neither witness can be built on Instance/Grp.v's [Z2], and the reason is a
 universe one, checkable with [Set Printing Universes].  [StableProp] is a type of
 propositions, so it lies strictly above [Set]; [GrpCosetPower] places it at
 the same universe as the group carriers, so the ambient carrier universe o
 must satisfy Set < o.  Meanwhile [Z2] carries `≈` as [@eq bool] and its
 relation universe elaborates to [Set] itself, while [SymGrp] forces the
 carrier and relation universes of every object of the ambient [Grp] to
 coincide.  So [Z2] can only inhabit a [Grp] whose carrier universe is
 [Set], which is one too low.

 The two readbacks in this paragraph were re-measured after the PR
 “algebraic carriers are sets” (2026-09-17) and BOTH are restated.  An
 earlier revision quoted [Z2@{u} : GrpObject@{u Set u}] and
 [SymGrp@{u u0} : SetoidObject@{u0 u0} -> GrpObject@{u0 u0 u0}].  The
 [PropEquiv] field permuted [GrpObject]'s three universe roles from
 (carrier, proof, aux) to (aux, carrier, proof) and [SymGrp] gained the
 witness argument, so the same two facts now read

 Z2@{u} : GrpObject@{u Set Set}
 SymGrp@{u u0} : ∀ X : SetoidObject@{u0 u0},
 PropEquiv@{u0 u0} (is_setoid X) → GrpObject@{u0 u0 u0}

 -- [Z2] is now pinned at [Set] in the CARRIER as well as the relation, so
 the obstruction is if anything sharper, and the conclusion is unchanged.
 CORRECTION (#450): the obstruction is gone.  #450 wrote out [Z2]'s
 universes in place, and [About] now reads [Z2@{p} : GrpObject@{p p p}]
 over [bool_setoid@{u} : Setoid@{u u} bool], so [Z2] inhabits [Grp] at
 every carrier level; everything above in this comment describes the
 tree before #450, and the witnesses below are kept as they are.  The two-element group below repeats [Z2] on a
 carrier and an equivalence built from [poly_unit], which is
 universe-polymorphic, so no universe of [GrpTwo] is pinned and the general
 theorems apply to it directly.  The three-letter setoid of the second
 witness is built the same way, for the same reason. 

 --------
 以上所有内容都是针对任意同态证明的，因此该文件提供了具体实例以便检查这些构造。构建了两个实例，它们不可互换。第一个，[grp_two_incl]，是最便宜的非满射映射，它处理论证中“像之外”的部分；它的像是正规子群，而“像之内”的部分在那里完全退化——这一点在[grp_two_incl_image_acts_trivially]中得到了证明，而不是保持未知。第二个，[grp_two_sym3]，具有非正规像，它是在此处进行等变步骤以比较移动某些元素的置换的。任何证人都不能建立在 Instance/Grp.v 的 [Z2] 上，原因是宇宙层面的，可以通过 [Set Printing Universes] 检查。[StableProp] 是一种命题类型，因此它严格位于 [Set] 之上；[GrpCosetPower] 将其放置在与群承载体相同的宇宙中，所以环境承载体宇宙 o 必须满足 Set < o。与此同时，[Z2] 作为 [@eq bool] 承载 `≈`，并且其关系宇宙展开为 [Set] 本身，而 [SymGrp] 强制环境 [Grp] 的每个对象的承载体和关系宇宙一致。因此 [Z2] 只能存在于承载体宇宙为 [Set] 的 [Grp] 中，而这太低了。本段中的两个回读在 PR “代数载体是集合” (2026-09-17) 之后重新测量，并且两者都被重新表述。早期的修订引用了 [Z2@{u} : GrpObject@{u Set u}] 和 [SymGrp@{u u0} : SetoidObject@{u0 u0} -> GrpObject@{u0 u0 u0}] 。[PropEquiv] 域将 [GrpObject] 的三个宇宙角色从 (carrier, proof, aux) 重新排列为 (aux, carrier, proof)，并且 [SymGrp] 增加了 witness 参数，因此现在这两个事实读作

 Z2@{u} : GrpObject@{u Set Set}
 SymGrp@{u u0} : ∀ X : SetoidObject@{u0 u0},
 PropEquiv@{u0 u0} (is_setoid X) → GrpObject@{u0 u0 u0}-- [Z2] 现在在 CARRIER 中以及关系中都固定在 [Set]，因此阻碍如果有的话更为尖锐，但结论保持不变。  
 修正 (#450)：阻碍已消失。 #450 将 [Z2] 的宇宙原样写出，而 [About] 现在读取 [Z2@{p} : GrpObject@{p p p}] 之上 [bool_setoid@{u} : Setoid@{u u} bool]，因此 [Z2] 在每个载体层上都属于 [Grp]；本评论中上面的内容描述的是 #450 之前的树，下面的证人保持不变。  
 下面的二元素群在载体和由 [poly_unit] 构建的等价上重复 [Z2]，该等价是宇宙多态的，因此 [GrpTwo] 没有任何宇宙被固定，一般定理可以直接应用于它。  
 第二个证人的三字母同质集合以相同方式构建，理由相同。
*)

Definition grp_two_carrier : Type := poly_unit ∨ poly_unit.

Definition grp_two_zero : grp_two_carrier := inl ttt.
Definition grp_two_one  : grp_two_carrier := inr ttt.

Definition grp_two_rel : crelation grp_two_carrier := λ x y,
  match x, y with
  | inl _, inl _ => poly_unit
  | inr _, inr _ => poly_unit
  | _, _ => False
  end.

Lemma grp_two_equivalence : Equivalence grp_two_rel.
Proof.
  constructor.
  - intros [u|u]; exact ttt.
  - intros [u|u] [v|v] Hxy; try exact ttt; contradiction.
  - intros [u|u] [v|v] [w|w] Hxy Hyz; try exact ttt; contradiction.
Qed.

Definition grp_two_add (x y : grp_two_carrier) : grp_two_carrier :=
  match x, y with
  | inl _, _      => y
  | _, inl _      => x
  | inr _, inr _  => grp_two_zero
  end.

(*
 The [Prop] mirror of [grp_two_rel].  The relation itself matches into
 [poly_unit], which is a [Type], so it is not already a [Prop]; the mirror
 replaces [poly_unit] by [True] leg for leg, and the two implications are
 four-way case analyses.  Needed since the PR “algebraic carriers are sets”
 (2026-09-17), because [GrpTwo] is a [GrpObject]. 

 --------
 [Prop] 是 [grp_two_rel] 的镜像。该关系本身匹配到 [poly_unit]，这是一个 [Type]，所以它还不是一个 [Prop]；镜像用 [True] 逐个替换 [poly_unit]，而且这两个蕴含都是四向情况分析。由于 PR “代数载体是集合”（2026-09-17）的原因，这是必要的，因为 [GrpTwo] 是一个 [GrpObject]。
*)
Definition grp_two_prel (x y : grp_two_carrier) : Prop :=
  match x, y with
  | inl _, inl _ => True
  | inr _, inr _ => True
  | _, _ => False
  end.

Definition grp_two_setoid : SetoidObject :=
  {| carrier   := grp_two_carrier
   ; is_setoid := {| equiv        := grp_two_rel
                   ; setoid_equiv := grp_two_equivalence |} |}.

Definition grp_two_prop : PropEquiv (is_setoid grp_two_setoid).
Proof.
  unshelve refine {| pequiv := grp_two_prel |}.
  - intros [u|u] [v|v] h; simpl in *; try exact ttt; contradiction.
  - intros [u|u] [v|v] h; simpl in *; try exact I; contradiction.
Defined.

(*
 Z/2 again, on a universe-polymorphic carrier: addition modulo two, with
 every element its own inverse. 

 --------
 Z/2 再次出现在一个宇宙多态载体上：模二加法，每个元素都是它自身的逆元。
*)
Definition GrpTwo : GrpObject.
Proof.
  unshelve notypeclasses refine {|
    grp_setoid := grp_two_setoid;
    grp_unit := grp_two_zero;
    grp_mul  := grp_two_add;
    grp_inv  := λ x, x;
    grp_prop := grp_two_prop
  |}.
  - intros x x' Hx y y' Hy.
    destruct x as [|], x' as [|], y as [|], y' as [|];
      simpl in *; try contradiction; exact ttt.
  - intros a b c.
    destruct a as [|], b as [|], c as [|]; exact ttt.
  - intros a.
    destruct a as [|]; exact ttt.
  - intros a.
    destruct a as [|]; exact ttt.
Defined.

(*
 The probe: the inclusion of Z/2 as the first factor of Z/2 x Z/2.  Two of
 the four elements are in the image, so there are two cosets -- that count is
 arithmetic done by hand.  What the two Examples below prove between them is
 only the first half of it: that the image contains an element OTHER than
 the unit.  That the image is a PROPER subgroup is the separate
 [grp_two_incl_misses]. 

 --------
 探针：将 Z/2 作为 Z/2 × Z/2 的第一个因子包含进来。四个元素中有两个在像中，因此有两个陪集——这个计数是手工做的算术。下面的两个例子所证明的，只是其中的前半部分：即像中包含一个非单位元素。像是一个真子群是另一个独立的问题。
*)
Definition grp_two_incl : GrpTwo ~{Grp}~> Grp_product GrpTwo GrpTwo.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom GrpTwo (Grp_product GrpTwo GrpTwo)
       {| morphism := λ x, (x, grp_two_zero) |} _ _).
  - intros x y Hxy.
    split; [exact Hxy | exact ttt].
  - split; exact ttt.
  - intros a b.
    split; [reflexivity | exact ttt].
Defined.

(* The image is a NON-TRIVIAL subgroup: (1,0) is in it ... / 该图像是一个非平凡子群：(1,0) 属于其中… *)
Example grp_two_incl_image_nontrivial :
  GrpImage grp_two_incl (grp_two_one, grp_two_zero).
Proof.
  exists grp_two_one.
  split; exact ttt.
Qed.

(* ... and (1,0) is not the unit, so the image is more than {1}. / ... 并且 (1,0) 不是单位，所以图像大于 {1}。 *)
Example grp_two_incl_image_witness_not_unit :
  @equiv _ (grp_setoid (Grp_product GrpTwo GrpTwo))
    (grp_two_one, grp_two_zero) (grp_unit (Grp_product GrpTwo GrpTwo)) → False.
Proof.
  intros [H1 _].
  exact H1.
Qed.

(* ... and it is a PROPER subgroup: (0,1) has no preimage. / ...并且它是一个正规子群：(0,1) 没有原像。 *)
Lemma grp_two_incl_misses :
  ¬ GrpImage grp_two_incl (grp_two_zero, grp_two_one).
Proof.
  intros [b Hb].
  destruct Hb as [_ H2].
  exact H2.
Qed.

(*
 The two homomorphisms into the permutation group are distinct IN THE
 HOM-SETOID of [Grp], at the concrete element (0,1) of the codomain. 

 --------
 映射到置换群的两个同态在 [Grp] 的同集半范畴中是不同的，在值域的具体元素 (0,1) 处。
*)
Theorem grp_two_actions_differ :
  grp_twisted_action grp_two_incl ≈ grp_action grp_two_incl → False.
Proof.
  exact (grp_actions_differ grp_two_incl
           (grp_two_zero, grp_two_one) grp_two_incl_misses).
Qed.

(*
 Neither of the two permutations that carry the argument is secretly the
 identity: not the twist, and not the action at the missing element. 

 --------
 携带该论证的两个置换都不是隐秘的恒等置换：既不是扭转，也不是在缺失元素上的作用。
*)
Theorem grp_two_action_not_identity :
  grp_act grp_two_incl (grp_two_zero, grp_two_one)
    ≈ grp_unit (SymGrp (GrpCosetPower grp_two_incl) (grp_coset_power_prop grp_two_incl)) → False.
Proof.
  exact (grp_action_not_identity grp_two_incl
           (grp_two_zero, grp_two_one) grp_two_incl_misses).
Qed.

(*
 The permutation group in play is not the trivial group: the twist is a
 permutation different from the identity. 

 --------
 正在使用的置换群不是平凡群：扭转是一个与恒等置换不同的置换。
*)
Theorem grp_two_twist_not_identity :
  grp_twist grp_two_incl
    ≈ grp_unit (SymGrp (GrpCosetPower grp_two_incl) (grp_coset_power_prop grp_two_incl)) → False.
Proof. exact (grp_twist_not_identity grp_two_incl). Qed.

(*
 THE LIMIT OF THIS WITNESS, proved rather than glossed over.  The image of
 [grp_two_incl] has index two in an abelian group, hence is normal, hence
 translates every coset to itself: the ENTIRE image acts as the identity
 permutation of [GrpCosetPower].  So at this witness the equivariance step
 -- [grp_twist_act_commute], and with it [grp_twisted_action_agrees] -- is
 an equation between conjugates of the identity, and carries no information.
 The small witness cannot exercise that step, and no rearrangement of it
 could; the case the step exists for is a non-normal image, which is what
 [grp_two_sym3] below supplies. 

 --------
 这个证据的极限，更倾向于被证明而非被掩盖。[grp_two_incl] 的像在阿贝尔群中指数为二，因此是正规子群，因此将每个陪集映射到自身：整个像作为 [GrpCosetPower] 的恒等置换作用。因此在这个证据下，等变性步骤——[grp_twist_act_commute]，以及随之的 [grp_twisted_action_agrees]——是在恒等元素的共轭之间的方程，不携带任何信息。这个小证据无法执行该步骤，也无法通过任何重新排列来完成；该步骤存在的情况是一个非正规像，而下面的 [grp_two_sym3] 提供了这种情况。
*)
Theorem grp_two_incl_image_acts_trivially :
  ∀ g : carrier GrpTwo,
    @equiv _ (grp_setoid (SymGrp (GrpCosetPower grp_two_incl) (grp_coset_power_prop grp_two_incl)))
      (grp_act grp_two_incl (grp_map grp_two_incl g))
      (grp_unit (SymGrp (GrpCosetPower grp_two_incl) (grp_coset_power_prop grp_two_incl))).
Proof.
  intros g S c; simpl.
  apply (proper_morphism S).
  exists g.
  destruct g as [u|u]; destruct c as [c1 c2];
    destruct c1 as [a|a]; destruct c2 as [b|b]; simpl; split; exact ttt.
Qed.

(* Hence [grp_two_incl] is not an epimorphism, by the main theorem. / 因此，按照主定理，[grp_two_incl] 不是一个满射。 *)
Theorem grp_two_incl_not_epic : ¬ Epic grp_two_incl.
Proof.
  exact (grp_not_epic_of_witness grp_two_incl
           (grp_two_zero, grp_two_one) grp_two_incl_misses).
Qed.

(*
 The hypothesis of the classical form, discharged on a concrete finite
 group: membership in the image of [grp_two_incl] is decidable, hence
 stable. 

 --------
 经典形式的假设，作用于一个具体的有限群：属于  [grp_two_incl] 的像是可判定的，因此是稳定的。
*)
Definition grp_two_incl_decidable : GrpImageDecidable grp_two_incl.
Proof.
  intros [x y].
  destruct y as [u|u].
  - left.
    exists x.
    split; [reflexivity | exact ttt].
  - right.
    intros [b Hb].
    destruct Hb as [_ H2].
    exact H2.
Defined.

Definition grp_two_incl_epic_iff_surjective :
  Epic grp_two_incl ↔ GrpSurjective grp_two_incl :=
  grp_epic_iff_surjective grp_two_incl
    (GrpImageDecidable_Stable grp_two_incl grp_two_incl_decidable).

(* The same conclusion again, this time routed through the classical form, so that the biconditional is exercised and not merely stated. / 同样的结论，这一次通过经典形式传递，以便双条件被运用，而不仅仅是被陈述。 *)
Theorem grp_two_incl_not_epic_classically : ¬ Epic grp_two_incl.
Proof.
  intro Hepic.
  apply grp_two_incl_misses.
  exact (fst grp_two_incl_epic_iff_surjective Hepic
           (grp_two_zero, grp_two_one)).
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** A second witness, with a NON-NORMAL image / * ** 第二位证人，显示非正常图像 *)

(*
 The witness above cannot exercise the equivariance step: its image is
 normal, so it acts trivially on the coset space, which is exactly what
 [grp_two_incl_image_acts_trivially] proves.  A non-normal subgroup
 requires a non-abelian ambient group -- every group of order less than six
 is abelian -- so the smallest possible home for one is the symmetric group
 on three letters, and that is what is built here.

 The group is not written down as a multiplication table.  It is [SymGrp]
 applied to a three-element setoid, so its multiplication IS composition of
 setoid maps and its associativity is the associativity of composition,
 already discharged once and for all in [SymGrp].  Only the two
 transpositions that the argument needs are named, each as a self-inverse
 map together with the two facts that make it a [SetoidPermutation]. 

 --------
 上面的证据不能执行等变步骤：它的像是正规子群，因此它在陪集空间上的作用是平凡的，这正是 [grp_two_incl_image_acts_trivially] 所证明的。一个非正规子群需要一个非阿贝尔的外围群——每个阶小于六的群都是阿贝尔群——所以它可能存在的最小群是三个元素的对称群，这正是这里构建的。

 该群没有以乘法表的形式写出。它是 [SymGrp] 应用于一个三元素集合集的结果，因此它的乘法就是集合映射的复合，其结合性就是复合的结合性，这已经在 [SymGrp] 中被一次性解决。论证中只需要提到的两个换位被命名，每个作为自反映射，以及使其成为 [SetoidPermutation] 的两个事实。
*)

Definition sym3_letter : Type := poly_unit ∨ (poly_unit ∨ poly_unit).

Definition sym3_l0 : sym3_letter := inl ttt.
Definition sym3_l1 : sym3_letter := inr (inl ttt).
Definition sym3_l2 : sym3_letter := inr (inr ttt).

Definition sym3_rel : crelation sym3_letter := λ x y,
  match x, y with
  | inl _, inl _             => poly_unit
  | inr (inl _), inr (inl _) => poly_unit
  | inr (inr _), inr (inr _) => poly_unit
  | _, _                     => False
  end.

Lemma sym3_equivalence : Equivalence sym3_rel.
Proof.
  constructor.
  - intros [u|[u|u]]; exact ttt.
  - intros [u|[u|u]] [v|[v|v]] Hxy; try exact ttt; contradiction.
  - intros [u|[u|u]] [v|[v|v]] [w|[w|w]] Hxy Hyz; try exact ttt; contradiction.
Qed.

Definition Sym3Letters : SetoidObject :=
  {| carrier   := sym3_letter
   ; is_setoid := {| equiv        := sym3_rel
                   ; setoid_equiv := sym3_equivalence |} |}.

(*
 The [Prop] mirror of [sym3_rel], on the model of [grp_two_prel] above and
 for the same reason: [GrpSym3] below is a [GrpObject] and [SymGrp] asks
 its setoid for a [PropEquiv]. 

 --------
 [Prop] 是 [sym3_rel] 的镜像，依据上面的 [grp_two_prel] 模型，并且出于相同的原因：下面的 [GrpSym3] 是一个 [GrpObject]，且 [SymGrp] 向它的集合体请求一个 [PropEquiv]。
*)
Definition sym3_prel (x y : sym3_letter) : Prop :=
  match x, y with
  | inl _, inl _             => True
  | inr (inl _), inr (inl _) => True
  | inr (inr _), inr (inr _) => True
  | _, _                     => False
  end.

Definition sym3_letters_prop : PropEquiv (is_setoid Sym3Letters).
Proof.
  unshelve refine {| pequiv := sym3_prel |}.
  - intros [u|[u|u]] [v|[v|v]] h; simpl in *; try exact ttt; contradiction.
  - intros [u|[u|u]] [v|[v|v]] h; simpl in *; try exact I; contradiction.
Defined.

Definition sym3_map (p : sym3_letter → sym3_letter)
           (Hp : ∀ x y, sym3_rel x y → sym3_rel (p x) (p y)) :
  SetoidMorphism Sym3Letters Sym3Letters.
Proof.
  unshelve notypeclasses refine {| morphism := p |}.
  exact Hp.
Defined.

(* A self-inverse map of the letters is a permutation of them, with itself as its own backward map: both round trips are the same fact. / 字母的自反映射是它们的一种排列，其自身作为它自己的反向映射：两个往返是相同的事实。 *)
Definition sym3_perm (p : sym3_letter → sym3_letter)
           (Hp : ∀ x y, sym3_rel x y → sym3_rel (p x) (p y))
           (Hi : ∀ x, sym3_rel (p (p x)) x) : SetoidPermutation Sym3Letters.
Proof.
  unshelve notypeclasses refine
    {| sperm_to := sym3_map p Hp ; sperm_from := sym3_map p Hp |}.
  - exact Hi.
  - exact Hi.
Defined.

(* The transposition of the last two letters. It generates the order-two subgroup that plays the role of the image. / 最后两个字母的换位。它生成了扮演像角色的二阶子群。 *)
Definition sym3_swap12 (x : sym3_letter) : sym3_letter :=
  match x with
  | inl u       => inl u
  | inr (inl u) => inr (inr u)
  | inr (inr u) => inr (inl u)
  end.

Lemma sym3_swap12_respects :
  ∀ x y, sym3_rel x y → sym3_rel (sym3_swap12 x) (sym3_swap12 y).
Proof.
  intros [u|[u|u]] [v|[v|v]] Hxy; try exact ttt; contradiction.
Qed.

Lemma sym3_swap12_involutive : ∀ x, sym3_rel (sym3_swap12 (sym3_swap12 x)) x.
Proof. intros [u|[u|u]]; exact ttt. Qed.

Definition sym3_s : SetoidPermutation Sym3Letters :=
  sym3_perm sym3_swap12 sym3_swap12_respects sym3_swap12_involutive.

(* The transposition of the first two letters. It is the coset representative whose conjugate escapes the image. / 前两个字母的换位。它是陪集代表，它的共轭元素逃离了像。 *)
Definition sym3_swap01 (x : sym3_letter) : sym3_letter :=
  match x with
  | inl u       => inr (inl u)
  | inr (inl u) => inl u
  | inr (inr u) => inr (inr u)
  end.

Lemma sym3_swap01_respects :
  ∀ x y, sym3_rel x y → sym3_rel (sym3_swap01 x) (sym3_swap01 y).
Proof.
  intros [u|[u|u]] [v|[v|v]] Hxy; try exact ttt; contradiction.
Qed.

Lemma sym3_swap01_involutive : ∀ x, sym3_rel (sym3_swap01 (sym3_swap01 x)) x.
Proof. intros [u|[u|u]]; exact ttt. Qed.

Definition sym3_a : SetoidPermutation Sym3Letters :=
  sym3_perm sym3_swap01 sym3_swap01_respects sym3_swap01_involutive.

(* What the two transpositions do, spelled out so that the descriptions above -- “of the last two letters”, “of the first two” -- are checkable rather than decoration. / 这两个换位的作用，用文字说明，以便上面提到的——“最后两个字母的”“前两个字母的”——可以被核查，而不是装饰。 *)
Example sym3_swaps_act :
  (sym3_rel (sym3_swap12 sym3_l0) sym3_l0
     ∧ sym3_rel (sym3_swap12 sym3_l1) sym3_l2
     ∧ sym3_rel (sym3_swap12 sym3_l2) sym3_l1)
  ∧ (sym3_rel (sym3_swap01 sym3_l0) sym3_l1
       ∧ sym3_rel (sym3_swap01 sym3_l1) sym3_l0
       ∧ sym3_rel (sym3_swap01 sym3_l2) sym3_l2).
Proof. repeat split; exact ttt. Qed.

Definition GrpSym3 : GrpObject := SymGrp Sym3Letters sym3_letters_prop.

(*
 Z/2 included as the subgroup generated by the transposition of the last two
 letters.  The only law with any content is that the transposition squares
 to the identity. 

 --------
 Z/2 包含为由最后两个字母的交换生成的子群。唯一有实际内容的规律是该交换平方为单位元。
*)
Definition sym3_of_two (x : grp_two_carrier) : SetoidPermutation Sym3Letters :=
  match x with
  | inl _ => sperm_id Sym3Letters
  | inr _ => sym3_s
  end.

Definition grp_two_sym3 : GrpTwo ~{Grp}~> GrpSym3.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom GrpTwo GrpSym3 {| morphism := sym3_of_two |} _ _).
  - intros x y Hxy.
    destruct x as [u|u], y as [v|v]; simpl in Hxy;
      try contradiction; intros [z|[z|z]]; exact ttt.
  - intros [z|[z|z]]; exact ttt.
  - intros a b.
    destruct a as [u|u], b as [v|v]; intros [z|[z|z]]; exact ttt.
Defined.

(*
 It really is an inclusion, so the image really is of order two: a
 transposition is not the identity, witnessed at the second letter. 

 --------
 它确实是一个包含，所以这个映像的阶确实是二：一个换位不是恒等置换，在第二个字母上可以看出。
*)
Lemma grp_two_sym3_injective :
  ∀ a b : carrier GrpTwo,
    grp_map grp_two_sym3 a ≈ grp_map grp_two_sym3 b → a ≈ b.
Proof.
  intros [u|u] [v|v] Hab; try exact ttt; exact (Hab sym3_l1).
Qed.

(* The image is proper: the OTHER transposition has no preimage. / 像是适当的：另一个置换没有原像。 *)
Lemma grp_two_sym3_misses : ¬ GrpImage grp_two_sym3 sym3_a.
Proof.
  intros [g Hg].
  destruct g as [u|u]; exact (Hg sym3_l0).
Qed.

(*
 The image is NOT NORMAL, which is the whole point of this witness.  The
 element below is a conjugate of the image element [sym3_s] -- a transposition
 is its own inverse, so a⁻¹s⁻¹a is a⁻¹sa up to `≈` -- and it sends the first
 letter to the THIRD, whereas both members of the image fix the first letter.
 So it lies outside the image.  This is the hypothesis of
 [grp_act_moves_coset], written at exactly the element and the coset
 representative that lemma wants. 

 --------
 这个图像并不正常，这正是这个见证的意义所在。下面的元素是图像元素 [sym3_s] 的共轭——一个换位是它自己的逆，因此 a⁻¹s⁻¹a 在 `≈` 下相当于 a⁻¹sa——并且它将第一个字母发送到第三个字母，而图像的两个成员都固定第一个字母。因此它位于图像之外。这是 [grp_act_moves_coset] 的假设，正好写在引理所需的元素和陪集代表上。
*)
Lemma grp_two_sym3_conj_outside :
  ¬ GrpImage grp_two_sym3
      (grp_mul GrpSym3 (grp_inv GrpSym3 sym3_a)
         (grp_mul GrpSym3
            (grp_inv GrpSym3 (grp_map grp_two_sym3 grp_two_one)) sym3_a)).
Proof.
  intros [g Hg].
  destruct g as [u|u]; exact (Hg sym3_l0).
Qed.

(*
 A concrete stable subset that an element OF THE IMAGE moves: the indicator
 of the coset [sym3_a]·M is not fixed by translation by [sym3_s].  This is
 the statement whose absence made the first witness degenerate. 

 --------
 一个具体的稳定子集，其中图像的一个元素移动：陪集  [sym3_a] ·M 的指示函数不被  [sym3_s] 的平移固定。这就是第一个证据退化的原因，其缺失导致了这一点。
*)
Theorem grp_two_sym3_moves_a_coset :
  grp_act_map grp_two_sym3 (grp_map grp_two_sym3 grp_two_one)
      (grp_coset_indicator grp_two_sym3 sym3_a)
    ≈ grp_coset_indicator grp_two_sym3 sym3_a → False.
Proof.
  exact (grp_act_moves_coset grp_two_sym3 _ sym3_a grp_two_sym3_conj_outside).
Qed.

(*
 Hence the image does not act by the identity permutation -- contrast
 [grp_two_incl_image_acts_trivially], where it does.  At this witness the
 equivariance step [grp_twist_act_commute] and the agreement
 [grp_twisted_action_agrees] compare permutations that move something. 

 --------
 因此，该图像并不通过恒等置换起作用——对比 [grp_two_incl_image_acts_trivially]，它确实如此。在这一见证下，等变步骤 [grp_twist_act_commute] 和一致性 [grp_twisted_action_agrees] 比较了移动某些东西的置换。
*)
Theorem grp_two_sym3_image_acts_nontrivially :
  grp_act grp_two_sym3 (grp_map grp_two_sym3 grp_two_one)
    ≈ grp_unit (SymGrp (GrpCosetPower grp_two_sym3) (grp_coset_power_prop grp_two_sym3)) → False.
Proof.
  exact (grp_image_acts_nontrivially grp_two_sym3 grp_two_one sym3_a
           grp_two_sym3_conj_outside).
Qed.

(*
 And the main theorem applies here too, so the second witness is a witness
 for the argument as a whole and not only for its degenerate step. 

 --------
 主要定理在这里也适用，所以第二个证人是对整个论证的证人，而不仅仅是对它的退化步骤的证人。
*)
Theorem grp_two_sym3_not_epic : ¬ Epic grp_two_sym3.
Proof.
  exact (grp_not_epic_of_witness grp_two_sym3 sym3_a grp_two_sym3_misses).
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** Epi and monic are incomparable in Grp / * ** Epi 和 monic 在群（Grp）中是不可比的 *)

(*
 The easy direction on a concrete surjection that is NOT an isomorphism: the
 first projection of Z/2 x Z/2 is onto, hence epic, and it is not monic. 

 --------
 一个关于不是同构的具体满射的容易方向：Z/2 × Z/2 的第一个投影是满的，因此是史的，但它不是单的。
*)
Definition grp_two_exl_surjective : GrpSurjective (@Grp_exl GrpTwo GrpTwo).
Proof.
  intro h.
  exists (h, grp_two_zero).
  reflexivity.
Defined.

Theorem grp_two_exl_epic : Epic (@Grp_exl GrpTwo GrpTwo).
Proof.
  exact (grp_surjective_is_epic (@Grp_exl GrpTwo GrpTwo)
           grp_two_exl_surjective).
Qed.

Lemma grp_two_exl_not_monic : Monic (@Grp_exl GrpTwo GrpTwo) → False.
Proof.
  intro Hm.
  destruct (Grp_injectivity_is_monic (@Grp_exl GrpTwo GrpTwo)) as [_ Hinj].
  assert (Heq : @equiv _ (grp_setoid (Grp_product GrpTwo GrpTwo))
                  (grp_two_zero, grp_two_zero) (grp_two_zero, grp_two_one)).
  { apply (Hinj Hm).
    reflexivity. }
  destruct Heq as [_ H2].
  exact H2.
Qed.

(*
 So [Epic] and [Monic] do not coincide in [Grp]: there is an epimorphism
 that is not a monomorphism, and hence not an isomorphism. 

 --------
 所以 [Epic] 和 [Monic] 在 [Grp] 中不重合：存在一个不是单射的满射，因此不是同构。
*)
Corollary grp_two_epic_not_monic :
  Epic (@Grp_exl GrpTwo GrpTwo) ∧ (Monic (@Grp_exl GrpTwo GrpTwo) → False).
Proof.
  split.
  - exact grp_two_exl_epic.
  - exact grp_two_exl_not_monic.
Qed.

(*
 The reverse containment has a counterexample too, so the two classes are
 INCOMPARABLE and not merely distinct.  [grp_two_incl] is injective on the
 nose -- the second component of the product is constant, so agreement of
 the images under `≈` is agreement of the first components -- hence monic
 by Instance/Grp.v's [Grp_injectivity_is_monic], and it is not epic by
 [grp_two_incl_not_epic] above. 

 --------
 逆包含也有反例，所以这两个类是不可比较的，而不仅仅是不同。[grp_two_incl] 在字面上是单射的——乘积的第二个分量是常数，因此在 `≈` 下像的相等就是第一个分量的相等——因此通过 Instance/Grp.v 的 [Grp_injectivity_is_monic] 它是单射的，并且根据上面的 [grp_two_incl_not_epic] 它不是满射的。
*)
Lemma grp_two_incl_injective :
  ∀ a b : carrier GrpTwo,
    grp_map grp_two_incl a ≈ grp_map grp_two_incl b → a ≈ b.
Proof.
  intros a b Hab.
  exact (fst Hab).
Qed.

Theorem grp_two_incl_monic : Monic grp_two_incl.
Proof.
  exact (fst (Grp_injectivity_is_monic grp_two_incl) grp_two_incl_injective).
Qed.

Corollary grp_two_epic_monic_incomparable :
  (Epic (@Grp_exl GrpTwo GrpTwo) ∧ (Monic (@Grp_exl GrpTwo GrpTwo) → False))
    ∧ (Monic grp_two_incl ∧ ¬ Epic grp_two_incl).
Proof.
  split.
  - exact grp_two_epic_not_monic.
  - split.
    + exact grp_two_incl_monic.
    + exact grp_two_incl_not_epic.
Qed.
