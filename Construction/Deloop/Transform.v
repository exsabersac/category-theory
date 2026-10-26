Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Construction.Deloop.
Require Import Category.Structure.Groupoid.
Require Import Category.Structure.Groupoid.Connected.

Generalizable All Variables.

(*
   * * Natural transformations between group homomorphisms are conjugations 

   --------
   * * 群同态之间的自然变换是共轭变换
*)

(*
 nLab:      https://ncatlab.org/nlab/show/natural+transformation
 nLab:      https://ncatlab.org/nlab/show/delooping
 nLab:      https://ncatlab.org/nlab/show/automorphism+2-group
 Wikipedia: https://en.wikipedia.org/wiki/Inner_automorphism
 Book:      Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 GTM 5, §I.4, printed p. 18 (Exercise 3)
 Book:      Awodey, “Category Theory”, 2nd ed., Oxford Logic Guides 52,
 2010, §7.7 (“Functor categories”), Example 7.21, printed
 pp. 167-168
 Book:      Awodey, “Category Theory”, 1st ed. (Carnegie Mellon pre-print,
 September 2005), §7.7, Example 7.21, printed p. 175
 Book:      Riehl, “Category Theory in Context”, Exercise 1.4.ii,
 printed p. 30

 CITATION NOTE.  AWODEY CHANGED THE FORMULA BETWEEN EDITIONS, and both
 printings have now been read.  For a transformation ϑ : f → g between
 homomorphisms f, g : G → H the FIRST edition (printed p. 175) writes

 f(x) · h = h · g(x),    equivalently    h⁻¹ · f(x) · h = g(x),

 and calls ϑ “an inner automorphism y ↦ h⁻¹ · y · h of H (called
 conjugation by h), that takes f to g”; the SECOND edition (printed p. 167)
 writes

 g(x) · h = h · f(x),    equivalently    g(x) = h · f(x) · h⁻¹,

 and calls ϑ “an inner automorphism y → h · y · h⁻¹ of H (called
 conjugation by h) that takes f to g”.  (Both quotations, and those below,
 normalize the superscript inverse and the inter-word spacing; nothing else
 is changed — the two printings really do use different arrow glyphs and
 different comma placement in that sentence.)

 The two differ in which of the source and the target multiplies on the
 left of h.  Each edition is internally consistent, and the two forms are
 carried to each other by h ↦ h⁻¹: the first edition's is exactly
 [transform_iff_conjugate_SWAPPED] below, whose proof derives it from the
 second edition's [transform_iff_conjugate] by doing nothing but replacing
 h by h⁻¹.  THIS FILE FOLLOWS THE SECOND EDITION, because that is the
 orientation the library's own composition order produces — see the
 COMPOSITION ORDER note below, which derives it rather than assuming it.
 Every Awodey quotation below is from the second printing unless the first
 is named.

 The catalog entry behind this file cites the FIRST edition, as
 Structure/Groupoid.v also does for §7.7, and ITS PARAPHRASE IS CORRECT FOR
 THE EDITION IT CITES: nothing here corrects it, and no erratum against it
 is claimed anywhere in this file.

 Mac Lane's Exercise 3 is cited by location only: its content is what this
 file proves, but its wording is not quoted, not having been checked
 against the book.

 Two monoid homomorphisms S, T : M → N correspond to two functors between
 the deloopings B M ⟶ B N ([Deloop_map] and [Deloop_unmap] below; the round
 trip through a homomorphism is the identity on the nose, the one through a
 functor on its morphism part).  A natural transformation between those two
 functors has exactly one component, at the single object, so it is a single
 element h of N; and its one naturality square says

 T g · h  ≈  h · S g       for every g in M,

 which for a group N is

 T g  ≈  h · S g · h⁻¹,

 the statement that h conjugates S into T.  This file proves that
 correspondence in both directions, at the level of setoids, and draws the
 consequence Awodey draws: since h is invertible when N is a group, every
 such transformation is invertible, so the functor category is a groupoid.

 Contents:

 Deloop_map f              the functor B M ⟶ B N of a homomorphism f
 Deloop_unmap F            the homomorphism of a functor; a left inverse
 of [Deloop_map] by [eq_refl]
 deloop_compose_mon_op     composition in B N IS the product of N
 Intertwines F G h         T g · h ≈ h · S g, for every g
 transform_intertwines     a transformation's component intertwines
 intertwines_transform     and conversely
 transform_iff_intertwines the two together (monoids, no inverses)
 transform_intertwiner_iso the correspondence as a bijection of setoids
 Conjugates F G h          T g ≈ h · S g · h⁻¹, for every g
 conjugates_is_conjugation and that IS Structure/Groupoid.v's
 [conjugate], by [eq_refl]
 transform_conjugator_iso  the same bijection over a group, onto the
 set of CONJUGATING elements
 transform_conjugator_hom  and at two homomorphisms: B S ⟹ B T IS the
 set of elements conjugating S into T
 transform_iff_conjugate   Mac Lane §I.4 Exercise 3, both directions
 transform_iff_conjugate_SWAPPED
 the same statement with h replaced by h⁻¹ —
 Awodey's first-edition orientation
 conjugates_inverse        h⁻¹ conjugates the other way
 Fun_IsGroupoid            [C, D] is a groupoid whenever D is
 Deloop_Fun_IsGroupoid     Awodey's consequence: H^G is a groupoid
 deloop_ginv_conjugates    and the inverse conjugates back, by h⁻¹
 abelian_conjugates_agree  the statement is EMPTY for abelian targets
 Bool_Xor_abelian, Z3_abelian   which the older witnesses are
 S3_hom_conjugate          a nonabelian witness: two homomorphisms
 Z/2 → S3 conjugate by a non-central element
 ([S3_conjugator_noncentral])
 S3_conjugation_moves      and the conjugation is not the identity
 Deloop_S3_two_objects     H^G has two provably distinct objects
 S3_no_transform_trivial   and two with NO arrow between them, so it is
 not connected ([Deloop_Fun_S3_not_connected])
 Deloop_Fun_S3_not_deloop  hence not equivalent to the delooping of any
 MONOID — not merely of any group — in either
 direction

 The delooping itself, and the monoid/group records [MonObject] and
 [GrpObject], are Construction/Deloop.v; that file's header states that “the
 functor-level half of the dictionary — that functors between deloopings are
 exactly monoid homomorphisms” is deliberately left out of it, and
 [Deloop_map]/[Deloop_unmap] below are that half.  [MonHom], [IsGroupoid],
 [ginv] and the symmetric group [S3_Grp] come from Structure/Groupoid.v. 

 --------
 nLab:       https://ncatlab.org/nlab/show/natural+transformation
 nLab:       https://ncatlab.org/nlab/show/delooping
 nLab:       https://ncatlab.org/nlab/show/automorphism+2-group
 Wikipedia:  https://en.wikipedia.org/wiki/Inner_automorphism
 书籍:      Mac Lane，《为工作中的数学家而作的范畴论》，第2版，GTM 5，第I.4节，第18页（练习3）
 书籍:      Awodey，《范畴论》，第2版，牛津逻辑指南52，2010，第7.7节（“函子范畴”），例7.21，第167-168页
 书籍:      Awodey，《范畴论》，第1版（卡内基梅隆预印本，2005年9月），第7.7节，例7.21，第175页
 书籍:      Riehl，《情境中的范畴论》，练习1.4.ii，第30页引用说明。AWODEY 在各版本之间更改了公式，并且两个版本的印刷本现在都已阅读。对于同态 f, g : G → H 之间的变换 ϑ : f → g，第一版（印在第175页）写道

 f(x) · h = h · g(x)，   等价于  h⁻¹ · f(x) · h = g(x)，

 并称 ϑ 为“将 f 变为 g 的 H 的内部自同构 y ↦ h⁻¹ · y · h（称为 h 的共轭）”；第二版（印在第167页）写道

 g(x) · h = h · f(x)，   等价于  g(x) = h · f(x) · h⁻¹并将ϑ称为“H 的一个内自同构 y → h · y · h⁻¹（称为由 h 的共轭），它将 f 映射到 g”。（下面的引文以及本句引文都对上标逆以及单词间的空格进行了规范化；除此之外没有更改——这两种印刷版的箭头符号和该句中的逗号放置确实不同。）两者的区别在于源对象和目标对象乘在 h 的左边的方式。每个版本内部都是一致的，这两种形式可以通过 h ↦ h⁻¹ 相互转换：第一版的正是下面的 [transform_iff_conjugate_SWAPPED]，其证明仅通过将第二版的 [transform_iff_conjugate] 中的 h 替换为 h⁻¹ 就得出。此文件遵循第二版，因为这是图书馆自身组合顺序产生的方向——参见下面的组合顺序说明，它是推导出来的而非假定的。下面 Awodey 的每条引用均来自第二次印刷，除非特别指出第一版。该文件背后的目录条目引用了第一版，正如 Structure/Groupoid.v 在 §7.7 中所做的那样，其释义对于所引用的版本是正确的：这里没有任何内容对其进行更正，并且在此文件中也没有声称有任何勘误。 

 Mac Lane 的练习 3 仅按位置引用：其内容就是此文件所证明的，但其措辞未被引用，也没有与书本进行核对。两个幺半群同态 S, T : M → N 对应于两个函子之间的退化 BM ⟶ BN（下图 [Deloop_map] 和 [Deloop_unmap]）；通过同态的往返是严格的恒等，而通过函子的往返则是在其态射部分上的恒等。 这两个函子之间的一个自然变换在唯一对象处恰好有一个分量，因此它是 N 中的一个单元素 h；其唯一的自然性方格表示

 T g · h  ≈  h · S g       对于 M 中的每个 g，

 在群 N 中，这等价于

 T g  ≈  h · S g · h⁻¹，

 也就是 h 将 S 共轭成 T 的陈述。 该文档证明了在集类（setoids）层面上这一对应关系的双向性，并得出了 Awodey 的结论：由于当 N 是群时 h 是可逆的，每个这样的变换都是可逆的，因此函子范畴是一个群范畴（groupoid）。内容：Deloop_map f              同态 f 对应的函子 B M ⟶ B N
 Deloop_unmap F            函子的同态；[Deloop_map] 的左逆，由 [eq_refl] 定义
 deloop_compose_mon_op     B N 中的组成是 N 的乘积
 Intertwines F G h         对每个 g, T g · h ≈ h · S g
 transform_intertwines     一个变换的分量相互交织
 intertwines_transform     反之亦然
 transform_iff_intertwines 两者一起（幺半群，无逆元）
 transform_intertwiner_iso 对应关系作为集合等价的双射
 Conjugates F G h          对每个 g, T g ≈ h · S g · h⁻¹
 conjugates_is_conjugation 这就是 Structure/Groupoid.v 的 [conjugate]，由 [eq_refl] 定义
 transform_conjugator_iso  th在一个群上的相同双射，映射到共轭元素集合
 transform_conjugator_hom 和两个同态：B S ⟹ B T 是将 S 共轭到 T 的元素集合
 transform_iff_conjugate Mac Lane §I.4 练习 3，双向
 transform_iff_conjugate_SWAPPED 同样的命题，但将 h 替换为 h⁻¹ —— Awodey 第一版的方向
 conjugates_inverse h⁻¹ 以相反方式共轭
 Fun_IsGroupoid 当 D 是群oid 时，[C, D] 是群oid
 Deloop_Fun_IsGroupoid Awodey 的结论：H^G 是群oid
 deloop_ginv_conjugates 并且逆映射通过 h⁻¹ 共轭回去
 abelian_conjugates_agree 对于阿贝尔群，该命题为空伊恩目标
 Bool_Xor_abelian, Z3_abelian   老见证者
 S3_hom_conjugate          一个非阿贝尔见证者：两个同态
 Z/2 → S3 被一个非中心元素共轭
 ([S3_conjugator_noncentral])
 S3_conjugation_moves      并且共轭动作不是恒等的
 Deloop_S3_two_objects     H^G 有两个可证明显不同的对象
 S3_no_transform_trivial   并且它们之间没有箭头，所以它
 不是连通的 ([Deloop_Fun_S3_not_connected])
 Deloop_Fun_S3_not_deloop  因此，它不等价于任何幺半群的循环化
 — 不仅仅是任何群 — 在任一方向上去循环本身，以及单子/群记录 [MonObject] 和 [GrpObject] 位于 Construction/Deloop.v；该文件的头部声明“字典的函子级部分——即去循环之间的函子恰好是单子同态”被故意省略了，而下面的 [Deloop_map] / [Deloop_unmap] 就是这一部分。[MonHom]、[IsGroupoid]、[ginv] 以及对称群 [S3_Grp] 来自 Structure/Groupoid.v。
*)

(*
 What the exercise is about, and the two ways to get it wrong

 nLab:  https://ncatlab.org/nlab/show/automorphism+2-group
 Paper: Eilenberg, Mac Lane, “General theory of natural equivalences”,
 Trans. Amer. Math. Soc. 58(2), 1945

 Mac Lane's Exercise 3 in §I.4 is about as small as a complete example of a
 natural transformation gets.  A group has one object, so a functor out of
 it has nothing to do on objects and is exactly a homomorphism; a natural
 transformation between two such functors has one component, and the
 naturality square — an equation between two composites of three arrows —
 becomes an equation between two products of three elements.  The answer,
 conjugacy, is a fact about groups that predates category theory entirely;
 what the exercise shows is that naturality REPRODUCES it, with no
 group-theoretic input beyond the definitions.  That is the phenomenon the
 1945 paper was written about, here at its smallest.

 The reading upward is the theory of 2-groups.  The delooping B G of a
 group is a one-object groupoid; the functor category B H ^ B G is a
 groupoid ([Deloop_Fun_IsGroupoid]) whose objects CORRESPOND to the
 homomorphisms G → H — they are functors, and the round trip through a
 functor is an identity only on the morphism part
 ([Deloop_map_unmap_fmap], [Deloop_map_unmap_fobj]) — and whose arrows are
 the conjugacies between them.  Two consequences
 are immediate from the definitions below rather than cited: two objects
 are joined by an arrow exactly when the homomorphisms are conjugate
 ([transform_iff_conjugate]), so the connected components are the conjugacy
 classes; and [Intertwines] at F = G says exactly that h commutes with
 every S a, so the endomorphisms of the object S are the centralizer in H
 of the image of S.  The nLab records the corresponding automorphism
 2-group as AUT(H) ≔ Aut(B H), presented by the crossed module
 H →Ad Aut(H) (nLab, “automorphism 2-group”); this file stops at the
 groupoid and builds no 2-group, but the non-connectedness witness at the
 end is exactly a pair of homomorphisms in different conjugacy classes.

 TWO TRAPS, both addressed below rather than in prose only, and both
 scoped there to exactly where they bite.

 The first is VACUITY.  In an abelian group conjugation is the identity:
 h · a · h⁻¹ ≈ a for every h.  So over an abelian target the conjugation
 theorem, however carefully stated, distinguishes nothing at all, and any
 demonstration built on such a target is worthless as evidence that the
 statement has content.  That is not left as a warning here:
 [abelian_conjugates_agree] PROVES that a conjugating element between two
 functors into an abelian target forces the two functors to agree on every
 arrow, and [Bool_Xor_abelian] and [Z3_abelian] show that Z/2 and Z/3 —
 the tree's only groups until Structure/Groupoid.v added S3 — are abelian,
 hence useless for this statement ([Bool_conjugates_agree] spells the
 instantiation out at Z/2).  The witness used here is therefore the
 symmetric group S3, which Structure/Groupoid.v introduced as the tree's
 first nonabelian group: the two homomorphisms Z/2 → S3 picking out the
 transpositions a and c are conjugate by the three-cycle r
 ([S3_hom_conjugate]), the conjugation moves them
 ([S3_conjugation_moves]), and the conjugating element is non-central
 ([S3_conjugator_noncentral], which is that file's [S3_not_abelian] read as
 a statement about r).  [S3_conjugation_needs_nonabelian] closes the loop by
 DERIVING that S3 is nonabelian from those two facts together, so the
 witness cannot be degenerate without contradicting itself.

 The second is COMPOSITION ORDER.  In this library f ∘ g means “g first”,
 and Construction/Deloop.v takes `compose f g := mon_op f g` — the monoid
 product in the same argument order, which [deloop_compose_mon_op] below
 restates as an equation holding by [eq_refl].  Reading naturality
 (`fmap[G] f ∘ η ≈ η ∘ fmap[F] f`, Theory/Natural/Transformation.v) through
 that gives, for η : S ⟹ T with component h,

 T g · h ≈ h · S g,       hence      T g ≈ h · S g · h⁻¹.

 So the TARGET of the transformation multiplies on the LEFT of h, and it is
 the target that is the conjugate of the source.  That is Awodey's
 SECOND-EDITION orientation (Example 7.21, 2nd ed. p. 167, quoted with the
 superscript inverse and inter-word spacing normalized): “what is a natural
 transformation between two group homomorphisms f, g : G → H? Such a map
 ϑ : f → g would be an element h ∈ H such that for every x ∈ G, we have
 g(x) · h = h · f(x) or, equivalently, g(x) = h · f(x) · h⁻¹.”  Source f,
 target g, target on the left — the same way round as [Intertwines] and
 [Conjugates] below.  ([transform_intertwines] is literally the [naturality]
 field: it is proved by `naturality n ttt ttt` with no rewriting at all,
 which is the sharpest available check that no side has been silently
 swapped.)

 HOW MUCH THE DIRECTION MATTERS, exactly.  Not as much as “trap” suggests
 at the ∃-quantified level.  [transform_iff_conjugate] and its
 source-on-the-left twin [transform_iff_conjugate_SWAPPED] are both proved
 below, and both are biconditionals with the SAME left-hand side, so their
 two right-hand sides are equivalent in this file by composing them; the
 proof actually carried out is the swapped one from the standard one, by
 sending h to h⁻¹ ([conjugates_inverse]) and nothing else.  Neither
 orientation is a false statement, and neither is Awodey's first edition,
 whose formula is the swapped one (see the CITATION NOTE above).
 What the direction does fix is every statement made about a GIVEN h —
 [Intertwines], [Conjugates], [transform_intertwines], [S3_hom_conjugate],
 [deloop_ginv_conjugates] — where exchanging the sides changes the claim
 rather than merely its notation, and where getting it backwards would
 quietly mean something else about a named element.  The opposite
 convention for delooping — composition as `mon_op g f` — would deloop the
 opposite monoid (Construction/Deloop/Opposite.v) and exchange the two
 sides of every equation in this file. 

 --------
 练习的内容，以及两种出错的方式

 nLab:   https://ncatlab.org/nlab/show/automorphism+2-group 
 论文: Eilenberg, Mac Lane, 《自然等价的一般理论》，
 美国数学会会刊 58(2), 1945麦克·莱恩在§I.4中的练习3几乎是一个自然变换完整例子的最小版本。一个群只有一个对象，因此从它出发的函子在对象上没有任何操作，正好就是一个同态；两个这样的函子之间的自然变换有一个分量，自然性方形——三个箭头的两个复合之间的方程——变成了三个元素的两个乘积之间的方程。答案，共轭，是一个完全早于范畴论的群论事实；这个练习展示的是自然性再现了它，而群论的输入仅限于定义。这就是1945年论文所讨论的现象，这里是它最小的表现形式。向上阅读的是二群的理论。群的去环 B G 是一个单对象群范畴；函子范畴 B H ^ B G 是一个群范畴（[Deloop_Fun_IsGroupoid]），其对象对应于同态 G → H——它们是函子，并且通过函子的往返只在态射部分是恒等的（[Deloop_map_unmap_fmap], [Deloop_map_unmap_fobj]）——其箭头是它们之间的共轭。从下面的定义中（而不是引用）可以立即得到两个结论：两个对象恰好当同态是共轭时由一条箭头连接（[transform_iff_conjugate]），因此连通分支就是共轭类；并且在 F = G 时 [Intertwines] 恰好说明 h 与每个 S a 交换，因此对象 S 的自同态就是 S 像在 H 中的中心化子。nLab 记录了相应的自同构二群为 AUT(H) ≔ Aut(B H)，由交叉模 H →Ad Aut(H) 表示（nLab，“自同构二群”）；此文件停在群范畴处，并未构建二群，但最后的非连通性证据恰好是一对属于不同共轭类的同态。

 两个陷阱，都在下面处理，而不仅仅是用文字说明，并且都精确地限定在它们产生问题的地方。第一个是空性。在阿贝尔群中，共轭是恒等：
 h · a · h⁻¹ ≈ a 对于每个 h 都成立。因此在阿贝尔的目标上，共轭定理，无论如何仔细陈述，根本没有区分任何东西，而建立在这样的目标上的任何演示对于证明该命题有内涵都是无用的。这里不给出警告：
 [abelian_conjugates_agree] 证明在两个函子映射到阿贝尔目标之间的共轭元素强制两个函子在每条箭头上都一致，[Bool_Xor_abelian] 和 [Z3_abelian] 显示 Z/2 和 Z/3 ——在 Structure/Groupoid.v 添加 S3 之前树中的唯一群——都是阿贝尔群，因此对该命题无用（[Bool_conjugates_agree] 在 Z/2 上详细说明了具体实例）。因此，这里使用的见证是对称群 S3，Structure/Groupoid.v 将其介绍为树的第一个非阿贝尔群：两个同态 Z/2 → S3，选出换位 a 和 c，通过三循环 r ([S3_hom_conjugate]) 共轭，共轭操作移动它们 ([S3_conjugation_moves])，并且共轭元素是非中心的 ([S3_conjugator_noncentral]，该文件中的 [S3_not_abelian] 被解读为关于 r 的陈述)。[S3_conjugation_needs_nonabelian] 通过从这两个事实一起推导出 S3 是非阿贝尔群来闭合循环，因此该见证不能退化而不自相矛盾。第二点是组合顺序。在这个库中，f ∘ g 的意思是“先 g”，而 Construction/Deloop.v 采用 `compose f g := mon_op f g` —— 单元的乘积，参数顺序相同，下面的 [deloop_compose_mon_op] 将其重新表述为 [eq_refl] 所持有的一个方程。通过该方式阅读自然性（`fmap [G]ZZ  f ∘ η ≈ η ∘ fmap [F]ZZ  f`，Theory/Natural/Transformation.v）会得到，对于 η : S ⟹ T，分量为 h，有

 T g · h ≈ h · S g，因此      T g ≈ h · S g · h⁻¹。因此，变换的目标在 h 的左侧相乘，并且是目标是源的共轭。这就是 Awodey 的第二版取向（示例 7.21，第二版第 167 页，引用时上标逆元和单词间距已规范化）：“两个群同态 f, g : G → H 之间的自然变换是什么？这样的映射 ϑ : f → g 将是 H 中的一个元素 h，使得对于每个 x ∈ G，我们有 g(x) · h = h · f(x)，或者等价地，g(x) = h · f(x) · h⁻¹。” 源 f，目标 g，目标在左——与下面的 [Intertwines] 和 [Conjugates] 顺序相同。（[transform_intertwines] 完全是 [naturality] 字段：它由 `naturality n ttt ttt` 证明，完全没有重写，这是目前能够得到的最严格检查，以确保没有一方被暗中交换。）方向到底有多重要。并不像“陷阱”所暗示的那样重要，在存在量化的层面上。[transform_iff_conjugate]及其左侧为源的双胞胎[transform_iff_conjugate_SWAPPED]都在下文中被证明，且两者都是具有相同左侧的双条件，因此通过组合它们，这个文件中的两个右侧是等价的；实际进行的证明是从标准证明中交换过来的，通过将h映射为h⁻¹（[conjugates_inverse]）而没有其他操作。两种方向都不属于错误陈述，Awodey的第一版也不是错误的，其公式是交换过的那个（参见上面的引用说明）。方向所修正的是关于给定的 h — [Intertwines]、[Conjugates]、[transform_intertwines]、[S3_hom_conjugate]、[deloop_ginv_conjugates] — 的每一个声明，其中交换两边会改变声明本身而不仅仅是它的表示，并且如果弄反了，会悄悄地表示命名元素的不同含义。对于去环的相反约定——组合为 `mon_op g f`——会去环相反的幺半群（Construction/Deloop/Opposite.v）并交换该文件中每个方程的两边。
*)

(*
 The obligations in this file are all elementary: for each of the two
 setoid bijections below, one [Equivalence], two [Proper]s and the two
 round trips; and for the S3 witness, one unit law and one finite case
 check over the multiplication table.  None of them wants [cat_simpl]'s
 program machinery, so the ambient obligation tactic is switched off,
 following Construction/Deloop.v and Instance/CMon.v. 

 --------
 本文件中的义务都是基础性的：对于下面的两个集合双射，每个都包括一个 [Equivalence]、两个 [Proper] 以及两次往返；对于 S3 的证明项，包括一个单位律和对乘法表的有限情况检查。它们中没有一个需要 [cat_simpl] 的程序机制，因此按照 Construction/Deloop.v 和 Instance/CMon.v 的做法，环境义务策略被关闭。
*)
#[local] Obligation Tactic := idtac.

(* * ** Functors between deloopings are monoid homomorphisms / * ** 延拓之间的函子是幺半群同态 *)

(*
 One half of the functor-level dictionary: a homomorphism f : M → N becomes
 a functor B M ⟶ B N.  There is nothing to do on objects, and the three
 functor laws are the three homomorphism laws by projection — respecting
 `≈`, preserving the unit, preserving the product — in the orientation
 [MonHom] states them, so no obligation is generated.

 ([Build_Functor] is applied to explicit arguments rather than written with
 record syntax because the record fields alone do not determine the two
 categories.) 

 --------
 函子级字典的一半：一个同态 f : M → N 变成一个函子 B M ⟶ B N。在对象上无需操作，三个函子律通过投影就是三个同态律——尊重 `≈`，保持单位，保持乘积——在方向 [MonHom] 中说明了它们，因此不会产生义务。

 （[Build_Functor] 适用于显式参数，而不是用记录语法书写，因为仅靠记录字段无法确定这两个范畴。）
*)
Definition Deloop_map {M N : MonObject} (f : MonHom M N) :
  Deloop M ⟶ Deloop N :=
  @Build_Functor (Deloop M) (Deloop N)
    (fun _ => ttt)                              (* nothing to choose on objects / 对象上没有可选择的项 *)
    (fun _ _ a => f a)                          (* an arrow is an element / 箭头是一种元素 *)
    (fun _ _ => mon_map_respects f)
    (fun _ => mon_map_unit f)                   (* fmap id ≈ id is f 1 ≈ 1 / fmap id ≈ id 是 f 1 ≈ 1 *)
    (fun _ _ _ a b => mon_map_op f a b).        (* fmap (a ∘ b) is f (a · b) / fmap (a ∘ b) 是 f (a · b) *)

(*
 And the other half: a functor between deloopings is a homomorphism, its
 action on the single hom-set.  Again every homomorphism law is a functor
 law by projection. 

 --------
 另一半：在退化间的函子是一个同态，它在单一同集上的作用。同样，每一个同态定律通过投影都是一个函子定律。
*)
Definition Deloop_unmap {M N : MonObject} (F : Deloop M ⟶ Deloop N) :
  MonHom M N := {|
  mon_map          := fun a => @fmap _ _ F ttt ttt a;
  mon_map_respects := @fmap_respects _ _ F ttt ttt;
  mon_map_unit     := @fmap_id _ _ F ttt;
  mon_map_op       := fun a b => @fmap_comp _ _ F ttt ttt ttt a b
|}.

(*
 The round trip through a homomorphism is the identity ON THE NOSE — an
 equality of whole records, law fields included, holding by [eq_refl]
 because [Set Primitive Projections] gives records definitional eta and
 because neither construction rebuilds a single field.  This is the same
 strength as [hom_monoid_Deloop] in Construction/Deloop.v, and it is what
 licenses reading the statements below, which are phrased with
 [Deloop_unmap], as statements about the homomorphisms one started with. 

 --------
 通过同态的往返是精确的恒等——整个记录的相等，包括字段的法律字段，由 [eq_refl] 保持，因为 [Set Primitive Projections] 给出了记录的定义性 eta，并且因为没有一个构造重建任何字段。这与 Construction/Deloop.v 中的 [hom_monoid_Deloop] 的强度相同，这也允许将下面用 [Deloop_unmap] 表述的陈述，解读为关于最初开始的同态的陈述。
*)
Example Deloop_unmap_map {M N : MonObject} (f : MonHom M N) :
  Deloop_unmap (Deloop_map f) = f := eq_refl.

(*
 The round trip through a functor is the identity on the morphism part,
 again by [eq_refl], and agrees with F at every object — but only
 propositionally there, by a case split.  [poly_unit] is an ordinary
 inductive type with no definitional eta (a variable x : poly_unit is not
 convertible to [ttt], which was checked before this comment was written),
 so the object map of [Deloop_map (Deloop_unmap F)] — the constant function
 at [ttt] — and that of F are not the same term.  The whole functors are
 therefore NOT claimed equal, and nothing below needs them to be. 

 --------
 通过函子进行的往返在态射部分是恒等的，仍然通过 [eq_refl]，并且在每个对象上与 F 一致——但在那里只是命题性的，通过分情况讨论。[poly_unit] 是一个普通的归纳类型，没有定义性的 eta（一个变量 x : poly_unit 并不可以转换为 [ttt]，这是在写这条评论之前检查过的），因此 [Deloop_map (Deloop_unmap F)] 的对象映射——在 [ttt] 上的常值函数——与 F 的对象映射不是同一项。因此整个函子不被主张相等，下面的内容也不需要它们相等。
*)
Example Deloop_map_unmap_fmap {M N : MonObject} (F : Deloop M ⟶ Deloop N)
  (a : carrier M) :
  @fmap _ _ (Deloop_map (Deloop_unmap F)) ttt ttt a = @fmap _ _ F ttt ttt a
  := eq_refl.

Example Deloop_map_unmap_fobj {M N : MonObject} (F : Deloop M ⟶ Deloop N)
  (x : Deloop M) : fobj[Deloop_map (Deloop_unmap F)] x = fobj[F] x.
Proof. destruct (fobj[F] x); reflexivity. Qed.

(*
 Distinct homomorphisms give distinct functors, hence distinct OBJECTS of
 the functor category.  The type ascription on the projected morphism map
 is what makes it non-dependent, so that [f_equal] applies: the hom-set of
 a delooping does not vary with the object. 

 --------
 不同的同态给出不同的函子，因此给出函子范畴中不同的对象。投影态射映射上的类型标注使其成为非依赖型，因此 [f_equal] 适用：一个去环化的同态集不会随着对象的变化而变化。
*)
Lemma Deloop_map_distinct {M N : MonObject} (f g : MonHom M N) (a : carrier M) :
  (f a = g a → False) → Deloop_map f = Deloop_map g → False.
Proof.
  intros Hne Heq.
  apply Hne.
  exact (f_equal
           (fun F : Deloop M ⟶ Deloop N => (@fmap _ _ F ttt ttt a : carrier N))
           Heq).
Qed.

(* * ** The composition-order convention, checked / * ** 组合顺序约定，已检查 *)

(*
 Composition in a delooping IS the monoid product, in the same argument
 order: the two are the same function, not merely equivalent.  Every
 equation in this file is read through this one, so it is recorded as a
 proof rather than as a remark.  (The objects must be supplied explicitly —
 the hom is the same setoid at every pair, so nothing in a composite
 determines them.) 

 --------
 在去卷环的情况下的组合是幺半群的乘积，按照相同的参数顺序：两者是相同的函数，而不仅仅是等价的。这个文件中的每一个等式都是通过这一点来读取的，所以它被记录为一个证明，而不是作为备注。（必须明确提供对象——在每一对之间同态都是相同的集合，因此复合中的任何内容都不能确定它们。）
*)
Example deloop_compose_mon_op (N : MonObject) :
  @compose (Deloop N) ttt ttt ttt = @mon_op N := eq_refl.

(* * ** The characterization, for monoids / * ** 单子的特征化 *)

Section Intertwining.

Context {M N : MonObject}.
Context (F G : Deloop M ⟶ Deloop N).

(*
 h intertwines F and G when   G a · h ≈ h · F a   for every a.  This is the
 naturality square of a transformation F ⟹ G written multiplicatively, and
 it is Awodey's form of the condition: no inverses appear, so it is stated
 for monoids and specializes to groups below.

 Note which side is which: the TARGET G multiplies on the left of h, the
 SOURCE F on the right. 

 --------
 当对每个 a 都有 G a · h ≈ h · F a 时，h 将 F 和 G 交织在一起。这是一个变换 F ⟹ G 的自然性方形，用乘法形式表示，这是 Awodey 的条件形式：没有出现逆元，因此它针对单子群陈述，并在下面特化到群。

 注意哪一边对应哪一边：目标 G 在 h 的左侧相乘，源 F 在右侧相乘。
*)
Definition Intertwines (h : carrier N) : Type :=
  ∀ a : carrier M, mon_op (Deloop_unmap G a) h ≈ mon_op h (Deloop_unmap F a).

(*
 Forward direction.  A natural transformation has a single component, at
 the single object, and that component intertwines — this is the
 [naturality] field itself, instantiated at the one object twice, with no
 rewriting whatever.  That the proof term is exactly `naturality n ttt ttt`
 is the check that the two sides of the equation have not been swapped. 

 --------
 正向方向。一个自然变换只有一个分量，位于单个对象上，而该分量相互交织——这就是 [naturality] 场本身，在这个单一对象上实例化了两次，没有任何重写。证明项恰好是 `naturality n ttt ttt`，这是检查方程两边没有被交换的验证。
*)
Definition transform_intertwines (n : F ⟹ G) : Intertwines (transform n ttt) :=
  naturality n ttt ttt.

(*
 Backward direction.  An intertwining element is a natural transformation:
 take it as the component at the only object.  (The objects are destructed
 because a bare variable of [poly_unit] is not convertible to [ttt] —
 [fmap] at a variable object is not the same term as [fmap] at [ttt] — and
 after the case split the naturality square is the intertwining equation
 verbatim.) 

 --------
 反向方向。一个交织元素是一个自然变换：把它看作唯一对象处的分量。（对象被析构，因为 [poly_unit] 的一个裸变量不能转换为 [ttt]——变量对象处的 [fmap] 与 [ttt] 处的 [fmap] 不是同一个项——在情况拆分之后，自然性方格就是交织方程逐字对应。）
*)
Definition intertwines_transform (h : carrier N) (I : Intertwines h) : F ⟹ G.
Proof.
  refine (@Build_Transform' _ _ F G (fun _ => h) _).
  intros x y a.
  destruct x, y.
  exact (I a).
Defined.

(*
 The component of the transformation built from h is h, by [eq_refl]. 

 --------
 由 h 构建的变换分量是 h，通过 [eq_refl]。
*)
Example intertwines_transform_component (h : carrier N) (I : Intertwines h) :
  transform (intertwines_transform h I) ttt = h := eq_refl.

(*
 The two directions together.  Both sides are data — a transformation one
 way, an element with its equations the other — so this is Lib/Foundation.v's
 Type-valued `↔` ([iffT]) and `∃` ([sigT]), not the propositional pair. 

 --------
 两个方向一起。两边都是数据——一边是单向的转换，一边是带有其方程的元素——所以这是 Lib/Foundation.v 的类型值 `↔`（[iffT]）和 `∃`（[sigT]），而不是命题对。
*)
Theorem transform_iff_intertwines : (F ⟹ G) ↔ ∃ h : carrier N, Intertwines h.
Proof.
  split.
  - intro n.
    exists (transform n ttt).
    exact (transform_intertwines n).
  - intros [h I].
    exact (intertwines_transform h I).
Defined.

(* * ** The correspondence at the level of setoids / * ** 在集合范畴水平上的对应 *)

(*
 Setoid-level care, which is what the task behind this file asks for: not
 merely that the two collections are inhabited together, but that they
 CORRESPOND.  They do, and the correspondence is a bijection of setoids —
 an isomorphism in [Sets] — between

 - the transformations F ⟹ G under [Transform_Setoid], where two
 transformations are identified when their components agree at every
 object; and

 - the INTERTWINING elements of N, i.e. the elements h carrying a proof
 of [Intertwines h], where two are identified when the ELEMENTS are
 `≈`-equal in N.

 Intertwining, not conjugating: N is a bare monoid here, with no inverses,
 so “h conjugates F into G” has nothing to refer to yet.  The version over
 a group — the literal set of CONJUGATING elements, cut out by [Conjugates]
 — is [transform_conjugator_iso] below, where the two conditions on h agree
 by [conjugates_iff_intertwines].

 The second setoid ignores the intertwining witness.  That is deliberate
 and is the honest reading of “the set of elements”: the witness is proof
 content with no equality of its own, and identifying elements by their
 underlying element of N makes the collection the sub-setoid of N cut out
 by the condition.  It is also forced by the first setoid, which sees only
 components.

 The isomorphism is in [Sets], where it says exactly what a bijection of
 setoids says: two `≈`-respecting maps, inverse to each other up to `≈`.
 Nothing in this file is stated in [Cat], where `≅` would mean only
 equivalence of categories.

 What is NOT claimed: nothing here says the correspondence is a group
 isomorphism, or natural in F and G, or that it identifies composition of
 transformations with multiplication in N.  (Vertical composition does take
 components to composites — [nat_compose]'s component at x is the composite
 of the two components, and composition in a delooping is [mon_op] — but
 for three different functors F ⟹ G ⟹ K that composition is a category's,
 not a monoid's, and the statement is not made here.) 

 --------
 集合态级别的关心，这正是本文件背后的任务所要求的：不仅仅是这两个集合同时有元素，而是它们对应。它们确实对应，并且这种对应是集合态的双射——在 [Sets] 中的同构——在以下之间：

 - 在 [Transform_Setoid] 下的变换 F ⟹ G，其中当两个变换在每个对象上的分量相同时，它们被认为是相同的；以及

 - N 的交织元素，即携带 [Intertwines h] 证明的元素 h，其中当元素在 N 中 `≈` 相等时，它们被认为是相同的。交织，而非共轭：这里的 N 是一个裸单子，没有逆元，所以“h 将 F 共轭到 G”还没有任何参考。在群上的版本——共轭元素的字面集合，由 [Conjugates] 切出——在下面的 [transform_conjugator_iso] 中，其中关于 h 的两个条件通过 [conjugates_iff_intertwines] 一致。

 第二个集合类忽略了交织证据。这是故意为之，也是对“元素集合”的诚实解读：证据本身是一个证明内容，没有自身的等式，通过其在 N 中的基础元素来识别元素，使得该集合成为由条件切出的 N 的子集合类。这也由第一个集合类强制决定，因为第一个集合类只看到组件。同构位于 [Sets] 中，它确切地说明了集合结构（setoids）的一一对应：两个尊重 `≈` 的映射，相互为逆，至多在 `≈` 下成立。这个文件中没有在 [Cat] 中陈述任何内容，其中 `≅` 只意味着范畴的等价。

 未声明的内容：这里没有说这种对应关系是群同构，也没有说它在 F 和 G 下是自然的，或者它将变换的复合映射为 N 中的乘法。（垂直复合确实会将分量映射到复合 — [nat_compose] 在 x 的分量是两个分量的复合，并且在延展中复合是 [mon_op] — 但是对于三个不同的函子 F ⟹ G ⟹ K，这种复合是范畴的复合，而不是幺半群的复合，并且这里没有做这样的陈述。）
*)

Definition Intertwiner : Type := ∃ h : carrier N, Intertwines h.

Program Definition Intertwiner_Setoid : Setoid Intertwiner := {|
  equiv := fun p q => `1 p ≈ `1 q
|}.
Next Obligation.
  constructor; repeat intro.
  - reflexivity.
  - now symmetry.
  - now transitivity (`1 y).
Qed.

Definition Deloop_Transforms : SetoidObject := {|
  carrier   := F ⟹ G;
  is_setoid := Transform_Setoid
|}.

Definition Deloop_Intertwiners : SetoidObject := {|
  carrier   := Intertwiner;
  is_setoid := Intertwiner_Setoid
|}.

(*
 A transformation to its component, with the naturality square read as the
 intertwining condition. 

 --------
 转化为其成分，自然性方阵被理解为交错条件。
*)
Program Definition transform_intertwiner :
  Deloop_Transforms ~{Sets}~> Deloop_Intertwiners := {|
  morphism := fun n => existT _ (transform n ttt) (transform_intertwines n)
|}.
Next Obligation.
  intros n1 n2 Hn.
  exact (Hn ttt).
Qed.

(* And back. *)
Program Definition intertwiner_transform :
  Deloop_Intertwiners ~{Sets}~> Deloop_Transforms := {|
  morphism := fun p => intertwines_transform (`1 p) (`2 p)
|}.
Next Obligation.
  intros p q Hpq x; simpl.
  exact Hpq.
Qed.

(*
 The bijection.  One round trip is [reflexivity], the two elements being
 convertible; the other needs the case split on the object, because a
 transformation's component at a variable object is only reachable from its
 component at [ttt] after that variable is known to be [ttt]. 

 --------
 双射。一次往返是 [reflexivity]，这两个元素是可互换的；另一次则需要对对象进行情况划分，因为变量对象上的变换组件只有在该变量被确认是 [ttt] 后，才能从 [ttt] 上的组件访问。
*)
Program Definition transform_intertwiner_iso :
  Deloop_Transforms ≅[Sets] Deloop_Intertwiners := {|
  to   := transform_intertwiner;
  from := intertwiner_transform
|}.
Next Obligation.
  intro p; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros n x; simpl.
  destruct x.
  reflexivity.
Qed.

End Intertwining.

Arguments Intertwines {M N} F G h.
Arguments Intertwiner {M N} F G.

(*
   * ** The characterization, for groups: Mac Lane §I.4 Exercise 3 

   --------
   * ** 关于群的刻画：Mac Lane §I.4 练习 3
*)

Section GroupConjugation.

Context {M : MonObject}.
Context {Grp : GrpObject}.
Context (F G : Deloop M ⟶ Deloop Grp).

(*
 h conjugates F into G when  G a ≈ h · F a · h⁻¹  for every a.  This is the
 equation Mac Lane's exercise asks about and Awodey's Example 7.21 writes as
 `g(x) = h · f(x) · h⁻¹`, bracketed the way the derivation below produces
 it; the two bracketings agree by associativity. 

 --------
 h 将 F 共轭为 G，当 G a ≈ h · F a · h⁻¹ 对每个 a 都成立时。这就是 Mac Lane 的练习题所讨论的方程，Awodey 在示例 7.21 中写作 `g(x) = h · f(x) · h⁻¹`，按照下面推导产生的括号方式；由于结合律，这两种括号方式是一致的。
*)
Definition Conjugates (h : carrier Grp) : Type :=
  ∀ a : carrier M,
    Deloop_unmap G a ≈ mon_op (mon_op h (Deloop_unmap F a)) (grp_inv h).

(*
 And “conjugation by h” is not a new notion here: the right-hand side above
 is Structure/Groupoid.v's [conjugate] — the inner automorphism
 y ↦ h · y · h⁻¹ that Awodey's example names — evaluated in the groupoid
 [Deloop Grp] at the single object, on the nose.  This is an equality of
 TYPES holding by [eq_refl], so it is also an independent check that this
 file's composition order agrees with that of the existing conjugation
 machinery. 

 --------
 而“通过 h 的共轭”在这里并不是一个新概念：上面的右侧是 Structure/Groupoid.v 中的 [conjugate]——Awodey 示例中命名的内自同构 y ↦ h · y · h⁻¹——在群对象 [Deloop Grp] 的单一对象上直接求值。这是通过 [eq_refl] 成立的类型等式，因此它也是对该文件的组合顺序与现有共轭机制一致的独立验证。
*)
Example conjugates_is_conjugation (h : carrier Grp) :
  Conjugates h
    = ∀ a : carrier M,
        Deloop_unmap G a
          ≈ conjugate (Deloop_IsGroupoid Grp) (x:=ttt) (x':=ttt)
              h (Deloop_unmap F a)
  := eq_refl.

(*
 Conjugating and intertwining are the same condition on h once inverses are
 available: multiply the intertwining equation on the right by h⁻¹ to reach
 the conjugation form, and the conjugation form on the right by h to get
 back. 

 --------
 一旦逆存在，对 h 进行共轭和交织是相同的条件：将交织方程右乘 h⁻¹ 可得到共轭形式，右乘 h 可返回共轭形式。
*)
Lemma intertwines_conjugates (h : carrier Grp) :
  Intertwines F G h → Conjugates h.
Proof.
  intros I a.
  rewrite <- (I a).
  rewrite <- mon_op_assoc.
  rewrite grp_inv_r.
  now rewrite mon_op_unit_r.
Qed.

Lemma conjugates_intertwines (h : carrier Grp) :
  Conjugates h → Intertwines F G h.
Proof.
  intros Cj a.
  rewrite (Cj a).
  rewrite <- mon_op_assoc.
  rewrite grp_inv_l.
  now rewrite mon_op_unit_r.
Qed.

Lemma conjugates_iff_intertwines (h : carrier Grp) :
  Conjugates h ↔ Intertwines F G h.
Proof.
  split.
  - apply conjugates_intertwines.
  - apply intertwines_conjugates.
Defined.

End GroupConjugation.

Arguments Conjugates {M Grp} F G h.

(* * ** The set of conjugating elements / * ** 共轭元素的集合 *)

Section ConjugatorIso.

Context {M : MonObject}.
Context {Grp : GrpObject}.
Context (F G : Deloop M ⟶ Deloop Grp).

(*
 The literal deliverable: over a GROUP the transformations F ⟹ G correspond
 to the set of CONJUGATING elements — the elements h of Grp satisfying
 [Conjugates F G h], the equation `G a ≈ h · F a · h⁻¹` that names an inner
 automorphism.  [transform_intertwiner_iso] above is the same bijection
 over a bare monoid, where the condition can only be stated as intertwining
 because no inverses exist; here it is stated as conjugation outright.

 No new mathematical content has to be proved — only the same five
 obligations again.  The two conditions on h are interchangeable
 once inverses are available ([intertwines_conjugates] and
 [conjugates_intertwines]), so the two maps are those of
 [transform_intertwiner_iso] with the witness converted on the way through,
 and the two round trips are still [reflexivity] and a case split on the
 object.

 Every disclosure made for the intertwiner setoid above applies here
 verbatim: the equality is that of the underlying elements of Grp, so the
 proof of [Conjugates] is not seen, and the isomorphism is in [Sets] —
 a bijection of setoids, nothing more. 

 --------
 字面上的交付物：在一个群上，变换 F ⟹ G 对应于共轭元素的集合——群中的元素 h 满足方程 [Conjugates F G h]，即命名为内自同构的方程 `G a ≈ h · F a · h⁻¹`。上面的 [transform_intertwiner_iso] 是相同的一一对应映射，但在一个裸单子上，由于不存在逆元，条件只能以交错的形式表述；这里则直接以共轭形式表述。 

 不需要证明新的数学内容——只需要再次满足相同的五个义务。一旦逆元存在，h 的两个条件是可互换的（[intertwines_conjugates] 和 [conjugates_intertwines]），因此这两个映射是 [transform_intertwiner_iso] 的映射，并在过程中转换了证人，并且两个往返映射仍然是 [reflexivity]，并对对象进行情况划分。上面为互连集合等价类所做的每一项披露在这里原文适用：等式是 Grp 基础元素的等式，因此 [Conjugates] 的证明不可见，而同构存在于 [Sets]——集合等价类的双射，仅此而已。
*)
Definition Conjugator : Type := ∃ h : carrier Grp, Conjugates F G h.

Program Definition Conjugator_Setoid : Setoid Conjugator := {|
  equiv := fun p q => `1 p ≈ `1 q
|}.
Next Obligation.
  constructor; repeat intro.
  - reflexivity.
  - now symmetry.
  - now transitivity (`1 y).
Qed.

Definition Deloop_Conjugators : SetoidObject := {|
  carrier   := Conjugator;
  is_setoid := Conjugator_Setoid
|}.

(*
 A transformation to its component, read as a conjugating element. 

 --------
 转变为其组成部分，读作一个结合元素。
*)
Program Definition transform_conjugator :
  Deloop_Transforms F G ~{Sets}~> Deloop_Conjugators := {|
  morphism := fun n => existT _ (transform n ttt)
    (intertwines_conjugates F G _ (transform_intertwines F G n))
|}.
Next Obligation.
  intros n1 n2 Hn.
  exact (Hn ttt).
Qed.

(* And back. *)
Program Definition conjugator_transform :
  Deloop_Conjugators ~{Sets}~> Deloop_Transforms F G := {|
  morphism := fun p => intertwines_transform F G (`1 p)
    (conjugates_intertwines F G (`1 p) (`2 p))
|}.
Next Obligation.
  intros p q Hpq x; simpl.
  exact Hpq.
Qed.

(*
 The bijection the exercise asks for, over a group: the collection of
 transformations F ⟹ G IS the set of conjugating elements.  Taken at
 F = [Deloop_map S] and G = [Deloop_map T] it is the statement that the
 transformations B S ⟹ B T correspond to the elements of Grp conjugating
 S into T — [transform_iff_conjugate] below with the correspondence made
 explicit instead of existentially quantified away. 

 --------
 练习要求的群上的双射：变换 F ⟹ G 的集合就是共轭元素的集合。当取 F = [Deloop_map S] 和 G = [Deloop_map T] 时，它表明变换 B S ⟹ B T 对应于将 S 共轭为 T 的群元素 —— 下面的 [transform_iff_conjugate]，将对应关系明确指出，而不是通过存在量词隐藏起来。
*)
Program Definition transform_conjugator_iso :
  Deloop_Transforms F G ≅[Sets] Deloop_Conjugators := {|
  to   := transform_conjugator;
  from := conjugator_transform
|}.
Next Obligation.
  intro p; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros n x; simpl.
  destruct x.
  reflexivity.
Qed.

End ConjugatorIso.

Arguments Conjugator {M Grp} F G.

(*
 The same bijection read at two homomorphisms, which is the exercise's own
 phrasing: the transformations B S ⟹ B T ARE the elements of C conjugating
 S into T.  This is only [transform_conjugator_iso] instantiated, and it is
 named because that is the exercise's own phrasing. 

 --------
 在两个同态上读取相同的双射，这是练习题自身的表述：变换 B S ⟹ B T 就是将 S 共轭为 T 的 C 的元素。这只是 [transform_conjugator_iso] 的实例化，并且之所以这样命名，是因为这是练习题自身的表述。
*)
Definition transform_conjugator_hom {B C : GrpObject} (S T : MonHom B C) :
  Deloop_Transforms (Deloop_map S) (Deloop_map T)
    ≅[Sets] Deloop_Conjugators (Deloop_map S) (Deloop_map T) :=
  transform_conjugator_iso (Deloop_map S) (Deloop_map T).

(*
 Right cancellation in a group, the one piece of group arithmetic used
 below that is not already in Construction/Deloop.v. 

 --------
 群中的右消去，下文中使用的群运算中有一部分在 Construction/Deloop.v 中尚未包含。
*)
Lemma grp_cancel_r {Grp : GrpObject} (a b c : carrier Grp) :
  mon_op a c ≈ mon_op b c → a ≈ b.
Proof.
  intro H.
  rewrite <- (mon_op_unit_r a), <- (grp_inv_r c), mon_op_assoc, H.
  rewrite <- mon_op_assoc, grp_inv_r.
  now rewrite mon_op_unit_r.
Qed.

(*
 Conjugation by h⁻¹ runs the other way.  This is the computation Awodey's
 consequence rests on, isolated from the transformation that carries it. 

 --------
 由 h⁻¹ 的共轭是另一种方式。这是 Awodey 的结果所基于的计算，从承载它的变换中孤立出来。
*)
Lemma conjugates_inverse {M : MonObject} {Grp : GrpObject}
  (F G : Deloop M ⟶ Deloop Grp) (h : carrier Grp) :
  Conjugates F G h → Conjugates G F (grp_inv h).
Proof.
  intro Cj.
  apply intertwines_conjugates.
  intro a.
  apply (grp_cancel_r _ _ h).
  rewrite <- !mon_op_assoc.
  rewrite grp_inv_l, mon_op_unit_r.
  rewrite (conjugates_intertwines F G h Cj a).
  rewrite mon_op_assoc, grp_inv_l.
  now rewrite mon_op_unit_l.
Qed.

(*
 Mac Lane, “Categories for the Working Mathematician”, §I.4, Exercise 3, in
 both directions: for groups B and C and homomorphisms S, T : B → C, a
 natural transformation between the two functors those homomorphisms give
 between the deloopings is inhabited exactly when some h in C conjugates S
 into T.

 The forward direction extracts the single component; the backward
 direction builds the transformation from h.  Nothing is assumed about B
 beyond its being a monoid — its inverses are never used — but it is stated
 for groups because that is Mac Lane's setting; [transform_iff_intertwines]
 above is the monoid form. 

 --------
 Mac Lane，《为实际数学家准备的范畴论》，§I.4，练习3，对于两个方向：对于群 B 和 C 以及同态 S, T : B → C，当且仅当某个 C 中的 h 将 S 共轭到 T 时，那些同态在 delooping 间给出的两个函子之间的自然变换才存在。

 正向方向提取单个分量；反向方向则由 h 构建变换。关于 B 没有假设，除了它是一个幺半群——从未使用其逆元——但它是针对群陈述的，因为这是 Mac Lane 的设定；上面的 [transform_iff_intertwines] 是幺半群形式。
*)
Theorem transform_iff_conjugate {B C : GrpObject} (S T : MonHom B C) :
  (Deloop_map S ⟹ Deloop_map T)
    ↔ ∃ h : carrier C,
        ∀ g : carrier B, T g ≈ mon_op (mon_op h (S g)) (grp_inv h).
Proof.
  split.
  - intro n.
    destruct (fst (transform_iff_intertwines (Deloop_map S) (Deloop_map T)) n)
      as [h I].
    exists h.
    exact (intertwines_conjugates (Deloop_map S) (Deloop_map T) h I).
  - intros [h C'].
    apply (snd (transform_iff_intertwines (Deloop_map S) (Deloop_map T))).
    exists h.
    exact (conjugates_intertwines (Deloop_map S) (Deloop_map T) h C').
Defined.

(*
 The same statement with the two sides exchanged: the SOURCE exhibited as
 the conjugate of the target, rather than the target as the conjugate of
 the source.  This is Awodey's first-edition equation, moved across:
 `f(x) · h = h · g(x)`, printed there as `h⁻¹ · f(x) · h = g(x)`, is
 `f(x) = h · g(x) · h⁻¹` with f the source and g the target — the statement
 below.  See the CITATION NOTE at the top of the file.

 It is a real theorem, proved here rather than described, and its proof is
 the whole content of the remark: at this level — where h is EXISTENTIALLY
 QUANTIFIED — it follows from [transform_iff_conjugate] by sending h to h⁻¹
 and nothing else, [conjugates_inverse] supplying each step.  Since the two
 are biconditionals with the same left-hand side, their right-hand sides
 are thereby equivalent, and the choice of side is not a choice between a
 true statement and a false one here.

 It is at the COMPONENT level that the direction is real content: the
 statements about a given h — [Intertwines], [Conjugates],
 [transform_intertwines], [S3_hom_conjugate], [deloop_ginv_conjugates] —
 each say something different when the sides are exchanged, and it is those
 that the library's composition order pins down. 

 --------
 将两边交换后的相同陈述：将来源显示为目标的共轭，而不是将目标显示为来源的共轭。这是Awodey第一版的方程，移动后：`f(x) · h = h · g(x)`，在那里印刷为`h⁻¹ · f(x) · h = g(x)`，是`f(x) = h · g(x) · h⁻¹`，其中f为来源，g为目标——如下所示的陈述。请参阅文件顶部的引用说明。这是一个真正的定理，在这里是被证明的而不是被描述的，它的证明就是这个注释的全部内容：在这个层次上——即 h 是存在量化的——它从 [transform_iff_conjugate] 推出，只需将 h 变为 h⁻¹ 而无需其他操作，[conjugates_inverse] 提供每一步。由于这两个是具有相同左侧的双条件语句，因此它们的右侧由此等价，在这里选择哪一边并不是在真假之间做选择。

 真正的内容在于组件（COMPONENT）层次上：关于给定的 h 的陈述——[Intertwines]、[Conjugates]、[transform_intertwines]、[S3_hom_conjugate]、[deloop_ginv_conjugates]——当交换两边时每个陈述都表达不同的内容，而正是这些内容由库的组合顺序确定。
*)
Theorem transform_iff_conjugate_SWAPPED {B C : GrpObject} (S T : MonHom B C) :
  (Deloop_map S ⟹ Deloop_map T)
    ↔ ∃ h : carrier C,
        ∀ g : carrier B, S g ≈ mon_op (mon_op h (T g)) (grp_inv h).
Proof.
  split.
  - intro n.
    destruct (fst (transform_iff_conjugate S T) n) as [h Cj].
    exists (grp_inv h).
    exact (conjugates_inverse (Deloop_map S) (Deloop_map T) h Cj).
  - intros [h Cj].
    apply (snd (transform_iff_conjugate S T)).
    exists (grp_inv h).
    exact (conjugates_inverse (Deloop_map T) (Deloop_map S) h Cj).
Defined.

(*
   * ** Awodey §7.7: the functor category is a groupoid 

   --------
   * ** Awodey §7.7: 函子范畴是群范畴
*)

(*
 The general fact behind Awodey's consequence, which is where its content
 actually lies: if every arrow of D is invertible then so is every natural
 transformation into D, since the componentwise inverses are again natural
 — the naturality square for them is the original square with the two
 components moved across it — and a transformation whose components are
 two-sided inverses is a two-sided inverse.  (Only that direction is proved
 here; the converse, that an invertible transformation has invertible
 components, is not needed and is not stated.)

 Awodey draws the conclusion for two GROUPOIDS: “It is clear that if G and
 H are any groupoids, then the functor category H^G is also a groupoid”
 (2nd ed., p. 168).  What is proved here is stronger in the domain: C is an
 arbitrary category, and only D must be a groupoid.

 The delooping case is the corollary below; the general statement is proved
 here rather than only at deloopings because the argument uses nothing
 about the domain, and because the inverse it produces has the component
 this file needs — [ginv] at each object, which for a delooping IS the
 group inverse ([deloop_ginv_component]). 

 --------
 阿沃迪（Awodey）结论背后的普遍事实，其内容实际上在于：如果D中的每一条箭头都是可逆的，那么每一个指向D的自然变换也是可逆的，因为按分量取的逆变换仍然是自然的——它们的自然性平方图就是原来的平方图，只是两个分量被移动到了平方图的另一侧——而且分量都是双向逆的变换本身也是双向逆的。（这里只证明了这个方向；逆方向，即可逆变换的分量也是可逆的，并不需要，也没有陈述。）Awodey 对两个群范畴得出结论：“很明显，如果 G 和 H 是任意的群范畴，那么函子范畴 H^G 也是一个群范畴”（第2版，第168页）。这里证明的内容在定义域上更强：C 是任意范畴，而只有 D 必须是一个群范畴。

 去环化的情形是下面的推论；这里证明了一般性陈述，而不仅仅是在去环化情况下，因为该论证没有使用定义域的任何特性，并且它产生的逆具有该文件所需的组成部分 —— 在每个对象上的 [ginv]，对于去环化来说这就是群的逆元（[deloop_ginv_component]）。
*)
Definition Fun_ginv {C D : Category} (GD : IsGroupoid D) {F K : C ⟶ D}
  (n : F ⟹ K) : K ⟹ F.
Proof.
  refine (@Build_Transform' _ _ K F (fun x => ginv GD (transform n x)) _).
  intros x y f.
  symmetry.
  apply (ginv_move_r GD).
  rewrite <- comp_assoc.
  rewrite naturality.
  rewrite comp_assoc, ginv_left.
  now rewrite id_left.
Defined.

Definition Fun_IsGroupoid {C D : Category} (GD : IsGroupoid D) :
  IsGroupoid ([C, D]).
Proof.
  intros F K n.
  refine (@Build_IsIsomorphism ([C, D]) F K n (Fun_ginv GD n) _ _).
  - intro x; simpl.
    rewrite fmap_id.
    apply ginv_right.
  - intro x; simpl.
    rewrite fmap_id.
    apply ginv_left.
Defined.

(*
 Awodey §7.7: for groups G and H the functor category H^G is a groupoid.
 Only the TARGET need be a group — the domain may be the delooping of any
 monoid, since the inverse of a transformation is built from the inverse of
 its component, which lives in the target. 

 --------
 Awodey §7.7：对于群 G 和 H，函子范畴 H^G 是一个群群。
 只有目标需要是群——定义域可以是任意幺半群的退圈，因为变换的逆由其分量的逆构成，而分量在目标中。
*)
Definition Deloop_Fun_IsGroupoid (M : MonObject) (Grp : GrpObject) :
  IsGroupoid ([Deloop M, Deloop Grp]) :=
  Fun_IsGroupoid (Deloop_IsGroupoid Grp).

(*
 Awodey's invertibility sentence, named — “Clearly, every such arrow
 ϑ : f → g has an inverse ϑ⁻¹ : g → f (conjugation by h⁻¹)”, which stands
 in both editions (2nd ed. p. 167, 1st ed. p. 175): every natural
 transformation between two functors into the delooping of a group is
 invertible.  This is [Deloop_Fun_IsGroupoid] read at one transformation. 

 --------
 Awodey 的可逆性定理句子，名为——“显然，每个这样的箭头 ϑ : f → g 都有一个逆 ϑ⁻¹ : g → f（通过 h⁻¹ 共轭）”，该句在两版中都有出现（第 2 版第 167 页，第 1 版第 175 页）：两个函子到一个群的去环化的每个自然变换都是可逆的。这是 [Deloop_Fun_IsGroupoid] 在一个变换下的读法。
*)
Definition deloop_transform_invertible {M : MonObject} {Grp : GrpObject}
  {F G : Deloop M ⟶ Deloop Grp} (n : F ⟹ G) :
  @IsIsomorphism ([Deloop M, Deloop Grp]) F G n :=
  Deloop_Fun_IsGroupoid M Grp F G n.

(*
 And the inverse really is conjugation by h⁻¹, in two steps.  First, its
 component is the group inverse of the component, on the nose: no
 transport, no rewriting, [eq_refl]. 

 --------
 而逆映射实际上是通过 h⁻¹ 的共轭，分两步进行。首先，它的分量是该分量的群逆，完全一致：无需传送，无需重写，[eq_refl]。
*)
Example deloop_ginv_component {M : MonObject} {Grp : GrpObject}
  {F G : Deloop M ⟶ Deloop Grp} (n : F ⟹ G) :
  transform (ginv (Deloop_Fun_IsGroupoid M Grp) n) ttt
    = grp_inv (transform n ttt) := eq_refl.

(*
 Second, that element conjugates G back into F.  Together with the equation
 above this is Awodey's sentence in full: the transformation is invertible,
 and its inverse is conjugation by h⁻¹. 

 --------
 其次，该元素将 G 共轭回 F。结合上面的方程，这就是 Awodey 的完整句子：变换是可逆的，其逆变换是通过 h⁻¹ 共轭得到的。
*)
Lemma deloop_ginv_conjugates {M : MonObject} {Grp : GrpObject}
  {F G : Deloop M ⟶ Deloop Grp} (n : F ⟹ G) :
  Conjugates G F (grp_inv (transform n ttt)).
Proof.
  apply conjugates_inverse.
  apply intertwines_conjugates.
  exact (transform_intertwines F G n).
Qed.

(*
   * ** The first trap: the statement is empty over an abelian target 

   --------
   * ** 第一个陷阱：在阿贝尔目标上语句为空
*)

(*
 Conjugation in an abelian group is the identity, so a conjugating element
 between two functors into an abelian target forces them to agree on every
 arrow: the conjugation theorem, over such a target, relates nothing that
 was not already equal.  This is proved, not asserted, because it is the
 precise sense in which an abelian witness would demonstrate nothing. 

 --------
 在阿贝尔群中，共轭是恒等的，因此，一个阿贝尔目标下两个函子之间的共轭元素会强制它们在每一个箭头上都一致：在这样的目标下，共轭定理关联的没有任何原本不相等的东西。这是被证明的，而不是被断言的，因为这是阿贝尔证明者不会显示任何新东西的确切意义。
*)
Lemma abelian_conjugates_agree {M : MonObject} {Grp : GrpObject}
  (F G : Deloop M ⟶ Deloop Grp) (h : carrier Grp)
  (comm : ∀ a b : carrier Grp, mon_op a b ≈ mon_op b a)
  (Cj : Conjugates F G h) :
  ∀ a : carrier M, Deloop_unmap G a ≈ Deloop_unmap F a.
Proof.
  intro a.
  rewrite (Cj a).
  rewrite (comm h (Deloop_unmap F a)).
  rewrite <- mon_op_assoc.
  rewrite grp_inv_r.
  now rewrite mon_op_unit_r.
Qed.

(*
 Z/2 and Z/3 — the only groups the tree had until Structure/Groupoid.v
 added S3 — are both abelian, so by the lemma above neither can display a
 conjugation that moves anything. 

 --------
 Z/2 和 Z/3 —— 在 Structure/Groupoid.v 添加 S3 之前，树上唯一的群 —— 都是阿贝尔群，因此根据上面的引理，它们都不能展示能移动任何元素的共轭作用。
*)
Lemma Bool_Xor_abelian :
  ∀ a b : carrier Bool_Xor_Grp, mon_op a b ≈ mon_op b a.
Proof. intros [|] [|]; reflexivity. Qed.

Lemma Z3_abelian : ∀ a b : carrier Z3_Grp, mon_op a b ≈ mon_op b a.
Proof. intros [| |] [| |]; reflexivity. Qed.

(*
 Instantiated at Z/2 — the library's first group witness, and the target
 one would reach for first.  Over it a conjugating element forces the two
 functors to agree pointwise, so nothing about conjugacy can be seen
 there.  (Only that direction is proved; the converse, that agreeing
 functors are conjugate, is not needed and is not stated.) 

 --------
 在 Z/2 实例化——这是该库的第一个群见证，也是人们首先会接触的目标。在它之上，一个共轭元素迫使两个函子按点一致，因此在这里看不到任何关于共轭的信息。（只证明了该方向；相反的方向，即一致的函子是共轭的，并不需要，也未被陈述。）
*)
Corollary Bool_conjugates_agree {M : MonObject}
  (F G : Deloop M ⟶ Deloop Bool_Xor_Grp) (h : carrier Bool_Xor_Grp)
  (Cj : Conjugates F G h) :
  ∀ a : carrier M, Deloop_unmap G a ≈ Deloop_unmap F a.
Proof. exact (abelian_conjugates_agree F G h Bool_Xor_abelian Cj). Qed.

(** ** A nonabelian witness / ** 一个非阿贝尔证明 *)

(*
 An element of order dividing two names a homomorphism Z/2 → S3, since
 Z/2 is generated by one element of order two.  Three instances are used
 below: the trivial homomorphism and the two picking out the transpositions
 a and c.  (The hypothesis is Coq's `=` because Structure/Groupoid.v builds
 [S3_Mon] over the carrier setoid whose [equiv] field IS [eq], as it does
 for [Z3_Mon] and as Construction/Deloop.v does for [Bool_Xor]; so `≈` and
 `=` are the same relation here and nothing weaker is being assumed.) 

 --------
 一个阶数能被二整除的元素命名了一个同态 Z/2 → S3，因为 Z/2 是由一个阶为二的元素生成的。下面使用了三个例子：平凡同态，以及两个选择换位 a 和 c 的同态。（假设是 Coq 的 `=`，因为 Structure/Groupoid.v 在其承载集合上建立了 [S3_Mon]，其 [equiv] 字段是 [eq]，就像对 [Z3_Mon] 所做的，以及 Construction/Deloop.v 对 [Bool_Xor] 所做的；所以这里 `≈` 和 `=` 是同一个关系，并且没有假设更弱的条件。）
*)
Program Definition S3_involution_hom (x : S3) (Hx : S3_mul x x = S3_e) :
  MonHom Bool_Xor S3_Mon := {|
  mon_map := fun b => if b then x else S3_e
|}.
Next Obligation.                        (* the unit goes to the unit / 该单位去单位 *)
  intros x Hx.
  reflexivity.
Qed.
Next Obligation.                        (* and the product to the product / 而产品到产品 *)
  intros x Hx a b.
  destruct x, a, b; simpl; try reflexivity; discriminate Hx.
Qed.

Definition S3_hom_e : MonHom Bool_Xor S3_Mon := S3_involution_hom S3_e eq_refl.
Definition S3_hom_a : MonHom Bool_Xor S3_Mon := S3_involution_hom S3_a eq_refl.
Definition S3_hom_c : MonHom Bool_Xor S3_Mon := S3_involution_hom S3_c eq_refl.

(*
 The conjugating element is NON-CENTRAL, which is the whole point of
 choosing it: this is Structure/Groupoid.v's [S3_not_abelian] read as the
 statement that r does not commute with a.  ([mon_op] at [S3_Mon] is
 [S3_mul] and `≈` is `=`, both definitionally, so that lemma is this
 statement already.) 

 --------
 结合元素是非中心的，这正是选择它的关键：这是 Structure/Groupoid.v 中的 [S3_not_abelian]，读作 r 与 a 不交换的陈述。（[mon_op] 在 [S3_Mon] 的位置是 [S3_mul]，`≈` 是 `=`，都在定义上，因此该引理已经是这个陈述了。）
*)
Definition S3_conjugator_noncentral :
  mon_op (m:=S3_Mon) S3_r S3_a ≈ mon_op (m:=S3_Mon) S3_a S3_r → False :=
  S3_not_abelian.

(*
 The witness the vacuity note requires: the three-cycle r conjugates the
 homomorphism picking out a into the one picking out c.  Both cases are a
 computation in the multiplication table — r · a · r⁻¹ = b · rr = c. 

 --------
 证人空白注记要求：三循环 r 将选取 a 的同态共轭到选取 c 的同态。两种情况都是乘法表中的计算 — r · a · r⁻¹ = b · rr = c。
*)
Theorem S3_hom_conjugate :
  @Conjugates Bool_Xor S3_Grp (Deloop_map S3_hom_a) (Deloop_map S3_hom_c) S3_r.
Proof. intros [|]; reflexivity. Qed.

(*
 So a natural transformation between the two homomorphisms exists, built
 through the backward direction of the theorem. 

 --------
 因此存在两个同态之间的自然变换，它是通过定理的逆向构建的。
*)
Definition S3_conjugating_transform :
  Deloop_map S3_hom_a ⟹ Deloop_map S3_hom_c :=
  snd (@transform_iff_conjugate Bool_Xor_Grp S3_Grp S3_hom_a S3_hom_c)
      (existT _ S3_r S3_hom_conjugate).

(*
 Its single component is the conjugating element r itself, by [eq_refl] —
 the backward direction of the theorem puts h in as the component and
 nothing intervenes. 

 --------
 它的单一组成部分是结合元素 r 本身，通过 [eq_refl] —— 定理的反向将 h 作为组成部分，而没有其他干扰。
*)
Example S3_conjugating_transform_component :
  transform S3_conjugating_transform ttt = S3_r := eq_refl.

(*
 And it is not degenerate: the two homomorphisms it relates are different,
 so the conjugation genuinely moves one to the other. 

 --------
 并且它不是退化的：它所关联的两个同态是不同的，因此共轭确实将一个移到了另一个。
*)
Theorem S3_conjugation_moves :
  (∀ g : carrier Bool_Xor, S3_hom_a g ≈ S3_hom_c g) → False.
Proof.
  intro H.
  specialize (H true).
  discriminate H.
Qed.

(*
 The two facts together DERIVE that S3 is nonabelian, which is the check
 that the witness exercises exactly the hypothesis it was chosen for: were
 the target abelian, [abelian_conjugates_agree] would force the two
 homomorphisms to agree, and [S3_conjugation_moves] says they do not.  A
 witness over Z/2 or Z/3 could not survive this test: [Bool_Xor_abelian] and
 [Z3_abelian], fed to the same lemma, are the proof that it would not. 

 --------
 这两个事实一起推导出 S3 是非交换的，这正是检验者所检验的，即它恰好用于选择的假设：如果目标是交换的，那么 [abelian_conjugates_agree] 将迫使两个同态一致，而 [S3_conjugation_moves] 说明它们不一致。在 Z/2 或 Z/3 上的证据无法通过这项测试：将 [Bool_Xor_abelian] 和 [Z3_abelian] 输入同一个引理，证明了它不会通过。
*)
Corollary S3_conjugation_needs_nonabelian :
  (∀ a b : carrier S3_Grp, mon_op a b ≈ mon_op b a) → False.
Proof.
  intro comm.
  apply S3_conjugation_moves.
  intro g.
  symmetry.
  exact (@abelian_conjugates_agree Bool_Xor S3_Grp
           (Deloop_map S3_hom_a) (Deloop_map S3_hom_c) S3_r comm
           S3_hom_conjugate g).
Qed.

(*
   * ** Awodey's second sentence: a groupoid, but not a group 

   --------
   * ** Awodey 的第二句话：一个群族，但不是一个群
*)

(*
 Awodey, immediately after the invertibility remark (2nd ed., p. 167):
 “But H^G is still not usually a group, simply because there may be many
 different homomorphisms G → H, so the functor category H^G has more than
 one object.”  Here are two such homomorphisms: those Z/2 → S3 picking out
 a and c are different functors, so the object type of the functor category
 is not a singleton.  (They are also the two that
 [S3_conjugating_transform] connects, so this groupoid carries an arrow
 between distinct objects.) 

 --------
 Awodey，在可逆性说明之后立即（第2版，第167页）：
 “但是 H^G 通常仍然不是一个群，仅仅是因为可能存在许多不同的 G → H 的同态，所以函子范畴 H^G 有多个对象。” 这里有两个这样的同态：那些 Z/2 → S3 选择 a 和 c 的同态是不同的函子，因此函子范畴的对象类型不是单例。（它们也是 [S3_conjugating_transform] 连接的两个同态，因此这个群族在不同对象之间存在一条箭头。）
*)
Theorem Deloop_S3_two_objects :
  Deloop_map S3_hom_a = Deloop_map S3_hom_c → False.
Proof.
  apply (Deloop_map_distinct S3_hom_a S3_hom_c true).
  discriminate.
Qed.

Definition Deloop_Fun_S3 : Category := [Deloop Bool_Xor_Grp, Deloop S3_Grp].

(*
 The stronger statement, which object-counting alone does not give: the
 functor category is not a group even up to equivalence.  A group, read as
 a category, is a one-object groupoid, so “essentially a group” means
 “equivalent to a delooping”; and a category equivalent to a delooping is
 connected, since an equivalence is full and a delooping has an arrow
 between any two of its objects (there being one object and at least the
 identity arrow).

 [Full] here is the library's chosen-section form, so no choice principle
 is used: [prefmap] is applied to the unit element of the monoid. 

 --------
 更强的说法，仅仅通过计数对象无法得出：函子范畴即使到同值也不是群。一个群，如果作为范畴来理解，是一个单对象群范畴，因此“本质上是群”意味着“等价于某个去环化”；而等价于去环化的范畴是连通的，因为等价态是全的，并且去环化在其任意两个对象之间都有箭头（因为只有一个对象且至少有恒等箭头）。

 [Full] 这里是库中选择的截面形式，因此没有使用选择公理：[prefmap] 被应用于幺半群的单位元素。
*)
Definition deloop_equivalence_connected {C : Category} {N : MonObject}
  (F : C ⟶ Deloop N) (E : EquivalenceOfCategories F) : Connected C.
Proof.
  pose proof (Equivalence_Full E) as Ful.
  intros x y.
  apply hom_zigzag.
  exact (@prefmap _ _ F Ful x y mon_unit).
Defined.

(*
 The trivial homomorphism and the one picking out a are NOT conjugate: an
 intertwining element would satisfy a · h ≈ h · e, i.e. a · h ≈ h, and no
 element of S3 does — which the proof checks over its six elements.  So the
 functor category has two objects with no arrow between them. 

 --------
 平凡同态和选取 a 的同态 **不是共轭的**：一个交错元素应满足 a · h ≈ h · e，即 a · h ≈ h，而 S3 中没有元素满足这一点——证明对其六个元素进行了检查。因此，该函子范畴有两个对象，但它们之间没有箭头。
*)
Theorem S3_no_transform_trivial :
  (Deloop_map S3_hom_e ⟹ Deloop_map S3_hom_a) → False.
Proof.
  intro n.
  destruct (fst (transform_iff_intertwines
                   (Deloop_map S3_hom_e) (Deloop_map S3_hom_a)) n) as [h I].
  specialize (I true).
  simpl in I.
  destruct h; discriminate I.
Qed.

(*
 Hence it is not connected — a zig-zag between those two objects would
 collapse, the category being a groupoid, to an arrow between them. 

 --------
 因此它不连接——在这两个对象之间的之字形路径会坍塌，因为该范畴是一个群范畴，会变成它们之间的一条箭头。
*)
Theorem Deloop_Fun_S3_not_connected : Connected Deloop_Fun_S3 → False.
Proof.
  intro K.
  apply S3_no_transform_trivial.
  exact (zigzag_hom (Deloop_Fun_IsGroupoid Bool_Xor_Grp S3_Grp)
           (K (Deloop_map S3_hom_e) (Deloop_map S3_hom_a))).
Qed.

(*
 And therefore it is not equivalent to the delooping of any monoid — in
 particular of any group — so it is a groupoid that is not a group in a
 stronger sense than object-counting gives.  Both directions of the
 equivalence are covered: the second statement turns an equivalence out of
 a delooping into one into it, by [EquivalenceOfCategories_sym]. 

 --------
 因此，它不等价于任何幺半群的去环绕 —— 特别是任何群 —— 所以它是一个群体，但在比对象计数提供的更强意义上不是群。等价性的两个方向都已涵盖：第二个陈述通过 [EquivalenceOfCategories_sym] 将一个来自去环绕的等价变为一个指向它的等价。
*)
Theorem Deloop_Fun_S3_not_deloop (N : MonObject) (F : Deloop_Fun_S3 ⟶ Deloop N)
  (E : EquivalenceOfCategories F) : False.
Proof.
  exact (Deloop_Fun_S3_not_connected (deloop_equivalence_connected F E)).
Qed.

Corollary Deloop_Fun_S3_not_deloop_rev (N : MonObject)
  (F : Deloop N ⟶ Deloop_Fun_S3) (E : EquivalenceOfCategories F) : False.
Proof.
  exact (Deloop_Fun_S3_not_deloop N (@quasi_inverse _ _ F E)
           (@EquivalenceOfCategories_sym _ _ F E)).
Qed.
