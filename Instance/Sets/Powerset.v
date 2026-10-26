Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.

(*
 [Monad] and [FAlg] are required only so that the two formability
 statements at the end of the file — [Powerset_Prop_Monad_statement] and
 [Powerset_Prop_FAlg] — can be entered into the environment.  Neither
 module depends on anything under Instance/, and nothing in the tree
 imports this file, so no cycle is introduced.  CORRECTION (#466): the
 clause “nothing in the tree imports this file” does not hold.  Before
 #466, forty-three files of _CoqProject required this module, and with
 #466's six files (its five and Test/ProbeSupLat466.v) forty-nine do (a
 script over their [Require] lines, comments stripped).  No cycle arises
 all the same: the transitive closure of the [Require] lines of
 Theory/Monad.v and Construction/FAlg.v, thirteen files, contains no file
 under Instance/, measured by the same script. 

 --------
 [Monad] 和 [FAlg] 仅仅是为了让文件末尾的两个可形成性声明——[Powerset_Prop_Monad_statement] 和 [Powerset_Prop_FAlg]——能够被输入到环境中。没有任何模块依赖于 Instance/ 下的内容，并且树中的任何内容都未导入此文件，因此不会引入循环。更正 (#466)：'树中的任何内容都未导入此文件' 这一条款不成立。在 #466 之前，_CoqProject 的四十三个文件需要此模块，而随着 #466 的六个文件（它的五个文件和 Test/ProbeSupLat466.v）后，现在有四十九个文件需要此模块（通过对它们的 [Require] 行的脚本处理，去掉了注释）。尽管如此，没有产生循环：Theory/Monad.v 和 Construction/FAlg.v 的 [Require] 行的传递闭包，共十三个文件，未包含 Instance/ 下的任何文件，由同一脚本测量。
*)
Require Import Category.Theory.Monad.
Require Import Category.Construction.FAlg.

Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(* * * The covariant and contravariant power-set functors on [Sets] / * * 在 [Sets] 上的协变和逆变幂集函子 *)

(*
 nLab:      https://ncatlab.org/nlab/show/power+set
 Wikipedia: https://en.wikipedia.org/wiki/Power_set

 The power set of a set is the set of its subsets, and it carries two
 actions on functions.  Covariantly, a function f : X → Y sends a subset
 S ⊆ X to its DIRECT image f S = { y | ∃ x ∈ S, f x = y }, giving an
 endofunctor of Set; contravariantly, it sends a subset T ⊆ Y to its
 INVERSE image f^{-1} T = { x | f x ∈ T }, giving a functor Set^op ⟶ Set.
 This file builds both, together with the singleton transformation whose
 components pick out {a}, over TWO carriers of subsets — one
 proof-relevant, one truncated — for reasons set out below.

 ATTRIBUTION, and what was and was not consulted.  The construction is
 the first worked example of a functor in Mac Lane, “Categories for the
 Working Mathematician”, 2nd ed. (GTM 5), §I.3, printed p. 13, with the
 contravariant companion at §II.2, printed p. 33; it is also Awodey,
 “Category Theory”, §5.6, printed p. 120, and Riehl, “Category Theory in
 Context”, §1.3 Example 1.3.2(i), with the singleton transformation at
 §1.4 Example 1.4.4(iii).  Both the section-and-page coordinates AND the
 one-line descriptions of what those passages contain are reproduced from
 the catalogue entry of the issue this file answers
 (jwiegley/category-theory#227).  The printed texts themselves were not
 consulted while writing this file, so every statement here about their
 content is the issue's characterization rather than a reading of the
 books.  The mathematical content below stands on its own proofs.

 WHAT IS ALREADY IN THE TREE, AND WHAT IS NEW HERE.  Several neighbouring
 constructions exist and none of them is either of these functors.
 [Structure/Topos.v] defines the INTERNAL power object of an
 elementary topos, [Pow a := Ω ^ a] — an assignment on objects with no
 action on morphisms.  [Theory/Subobject/Functor.v] defines
 [Sub : C^op ⟶ Sets] by chosen-pullback reindexing — the categorical
 generalization of the CONTRAVARIANT construction, at the level of
 subobjects of a general category.  Closest of all,
 [Instance/Sets/Image.v] builds [Sets_Image f], the image of ONE
 morphism as an object of [Sets] (carrier [∃ y, ∃ x, f x ≈ y]),
 together with its epi/mono factorization — that is the direct image of
 the whole domain, with no action on subsets.  And [Instance/Ens.v] is a
 category of ensembles, not a functor — though its objects
 ([∃ T : Type, Ensemble T], with [Ensemble T] the [Prop]-valued
 predicates on [T]) are the in-tree precedent for the truncated carrier
 below, as are [Instance/Rel.v]'s homs ([A ~> Ensemble B]).  What
 this file adds is the concrete Set-level pair: an honest [Functor] whose
 morphism action is the direct image, and its contravariant partner whose
 morphism action is the inverse image, over carriers of predicates on a
 setoid.

 TWO CARRIERS ARE SHIPPED, AND ONE QUESTION DECIDES WHICH A CONSUMER
 NEEDS: does it require an ENDOfunctor?  The issue's shared-module note
 records that several further constructions are filed against this same
 module (jwiegley/category-theory#227 names #466 — the power-set monad —
 and #704; its QA correction lists the full claimant set as #227, #466,
 #704, #750, #871, #1005).  Those numbers, and the issue's description of
 what each covers, are quoted and not independently audited here.  What IS
 checked here is the consequence for consumers:

 [Powerset_obj] / [Powerset] / [Powerset_op] — PROOF-RELEVANT subsets:
 predicates valued in [Type@{o}], so the power set lands one universe
 up (the next section derives this).  A consumer that maps out of the
 power set, or that wants the witness of membership to carry data,
 wants this carrier.  It is not an endofunctor, and the price is
 concrete: [@Monad Sets Powerset] and [FAlg Powerset] are both
 rejected by the universe checker, because [Theory/Monad.v] and
 [Construction/FAlg.v] each require an endofunctor.  So the
 power-set monad (#466) and any initial-algebra reading (#750) cannot
 ride on this carrier, and [Sets_Lift ⟹ Powerset] below, though it is
 the singleton family, cannot serve as a monad unit.

 [Powerset_Prop_obj] / [Powerset_Prop] — the same subsets with
 membership truncated to a [Prop], which puts the power set at the
 SAME universe as the carriers and so gives a genuine endofunctor
 [Sets ⟶ Sets].  Both [@Monad Sets Powerset_Prop] and
 [FAlg Powerset_Prop] are formable over it; the two types are entered
 into the environment at the end of this file, as
 [Powerset_Prop_Monad_statement] and [Powerset_Prop_FAlg], so that
 claim is machine-checked rather than asserted in prose.  Neither the
 monad nor an initial algebra is BUILT here — this file establishes
 only that they have become statable.

 Truncation is what buys the endofunctor, and what it costs is exactly
 proof relevance: over [Powerset_Prop] one can no longer read back WHICH
 [x ∈ S] witnessed [y ∈ f S].  That is the whole reason both carriers are
 shipped instead of one, and [Powerset_truncate] at the end of the file is
 the comparison from the proof-relevant carrier to the truncated one.  The
 design point survives either way: build the carriers here once, and let
 the rest ride on them rather than on private copies. 

 --------
 nLab：       https://ncatlab.org/nlab/show/power+set 
 Wikipedia：  https://en.wikipedia.org/wiki/Power_set 

 一个集合的幂集是它的子集的集合，并且它在函数上有两种作用。 共变地，一个函数 f : X → Y 将子集 S ⊆ X 发送到它的直接像 f S = { y | ∃ x ∈ S, f x = y }，生成 Set 的一个自范畴函子； 逆变地，它将子集 T ⊆ Y 发送到它的逆像 f^{-1} T = { x | f x ∈ T }，生成一个函子 Set^op ⟶ Set。本文件构建了这两者，以及单元素变换，其分量抽取 {a}，作用于子集的两个载体——一个与证明相关，一个被截断——原因如下所述。归属，以及咨询了什么和未咨询什么。该构造是在 Mac Lane 的《为工作数学家准备的范畴论》（Categories for the Working Mathematician），第二版（GTM 5）§I.3，第13页中第一个实现函子（functor）的示例，其对偶伴随在 §II.2，第33页；它也出现在 Awodey 的《范畴论》（Category Theory），§5.6，第120页，以及 Riehl 的《上下文中的范畴论》（Category Theory in Context），§1.3 示例 1.3.2(i)，其单例变换（singleton transformation）在 §1.4 示例 1.4.4(iii)。段落和页码坐标以及对这些段落内容的一行描述均从该文件所回答的问题的目录条目中复制（jwiegley/category-theory#227）。在撰写此文件时，并未参考印刷文本本身，因此这里关于其内容的每一条陈述都是对该期刊的概述，而不是对书籍的具体阅读。下面的数学内容有其独立的证明。树中已有的内容，以及这里的新内容。存在几个相邻的构造，但它们都不是这些函子。[Structure/Topos.v] 定义了初等拓扑的内部幂对象，[Pow a := Ω ^ a] —— 对对象的一个赋值，但不作用于态射。[Theory/Subobject/Functor.v] 通过选择的拉回重索引定义了 [Sub : C^op ⟶ Sets] —— 对范畴论中子对象层面的逆变构造的推广。最接近的是，[Instance/Sets/Image.v] 构建了 [Sets_Image f]，即作为 [Sets] 对象（载体 [∃ y, ∃ x, f x ≈ y]）的一个态射的一般像，同时给出其单/满射分解 —— 这就是整个定义域的直接像，不作用于子集。[Instance/Ens.v] 是一个集合范畴的类别，而不是函子——尽管它的对象（[∃ T : Type, Ensemble T]，其中 [Ensemble T] 是 [Prop] 值的 [T] 上的谓词）是下面截断载体的树内前驱，[Instance/Rel.v] 的态射（[A ~> Ensemble B]）也是如此。此文件添加的是具体的 Set 级别对：一个诚实的 [Functor]，其态射作用是直接像，以及其对变伙伴，其态射作用是逆像，作用于集合上谓词的载体。两个载体已经发货，而一个问题决定了消费者需要哪一个：它是否需要一个 ENDOfunctor？该问题的共享模块说明记录了几个进一步的构造针对同一个模块提出（jwiegley/category-theory#227 提到 #466——幂集 monad——和 #704；其 QA 更正列出了完整的声称集合为 #227、#466、#704、#750、#871、#1005）。这些编号，以及该问题对每个覆盖内容的描述，在此引用，并未独立审核。这里检查的是对消费者的影响：[Powerset_obj] / [Powerset] / [Powerset_op] — 与证明相关的子集：谓词在 [Type@{o}] 中取值，因此幂集会提升一个宇宙（下一节将推导出这一点）。一个从幂集映射出去的消费者，或者希望成员身份的见证携带数据的消费者，需要这个承载器。它不是一个自函子，代价是具体的：[@Monad Sets Powerset] 和 [FAlg Powerset] 都被宇宙检查器拒绝，因为 [Theory/Monad.v] 和 [Construction/FAlg.v] 各自都需要一个自函子。因此，幂集单子（#466）以及任何初代数读取（#750）都无法在这个承载器上运行，而下面的 [Sets_Lift ⟹ Powerset]，尽管它是单元素族，也不能作为单子单位。[Powerset_Prop_obj] / [Powerset_Prop] —— 相同的子集，其成员资格被截断为 [Prop]，这使得幂集处于与承载对象相同的宇宙中，从而给出了一个真正的端函子 [Sets ⟶ Sets]。[@Monad Sets Powerset_Prop] 和 [FAlg Powerset_Prop] 都可以在其上构造；这两种类型在本文件末尾被输入到环境中，作为 [Powerset_Prop_Monad_statement] 和 [Powerset_Prop_FAlg]，因此该主张是通过机器验证的，而不是用文字声明。这里既没有构建单子也没有构建初始代数——本文件仅确立它们已经可以表述。截断就是购买端函子，而它的代价正好是证明相关性：在 [Powerset_Prop] 上，你再也无法读取回 [x ∈ S] 见证的 [y ∈ f S]。这正是两个承载体都要发送而不是只发送一个的全部原因，并且文件末尾的 [Powerset_truncate] 是从与证明相关的承载体到截断承载体的比较。设计要点两种方式都能保留：在这里构建承载体一次，然后让其余部分依赖它们而不是依赖私有副本。
*)

(* ------------------------------------------------------------------------ *)
(* * ** Universe placement, stated precisely / * ** 宇宙位置，精确说明 *)

(*
 A PROOF-RELEVANT predicate carrier does not fit at the level of the setoid
 it is a power set of, and the discipline adopted here is to say so in the
 type of the functor rather than to hide it.  Everything in this section is
 about that carrier; the last section of the file shows that a TRUNCATED
 carrier does fit, and what the truncation costs.  Be careful throughout
 about which universe is which.

 [Sets@{o so} : Category@{so o o}] (Instance/Sets.v), and a
 [Category@{o h p}] has [obj : Type@{o}].  So QUA CATEGORY the object
 universe of [Sets@{o so}] is [so]: its objects are the [SetoidObject@{o o}]s,
 and [o] is the universe of those objects' CARRIERS — the level at which
 the small sets themselves live.  The constraint [o < so] is forced
 (printed by [About Sets] as `o so |= o < so`).

 Morphism equivalence in this library is [Type]-valued: [Setoid] carries
 [equiv : crelation A] (Lib/Setoid.v), so for [X : SetoidObject@{o o}]
 and [x y : carrier X] the proposition [x ≈ y] is a [Type@{o}], not a
 [Prop].  If a subset of [X] is CHOSEN to be a predicate valued in
 [Type@{o}] — recording, for each element, the data of why it belongs —
 then it is exactly the carrier of [PropSetoid] (Instance/Sets/Classifier.v
 — carrier [Type@{o}] under [↔], which denotes [iffT] here,
 Lib/Foundation.v).  And [Type@{o} : Type@{o+1}], so a predicate type
 [carrier X → Type@{o}] sits at [Type@{so}], one level above the carriers.

 The word CHOSEN is doing real work there, and an earlier version of this
 header wrote “therefore” instead — see the retraction below.  Nothing
 about a [Type@{o}]-valued [≈] forces subsets to be valued where [≈] is; a
 subset only has to RESPECT [≈].

 Hence [Powerset_obj@{o so} : SetoidObject@{o o} → SetoidObject@{so so}]:
 it takes an OBJECT OF [Sets@{o so}] to an OBJECT OF [Sets@{so sso}].  The
 functors below are stated at that honest cross-universe type,

 Powerset    : Sets@{o so} ⟶ Sets@{so sso}
 Powerset_op : (Sets@{o so})^op ⟶ Sets@{so sso}

 which is the same discipline, and the same donors, as
 Instance/Sets/Classifier.v: [Setoid_Lift] re-types a
 [SetoidObject@{o o}] as a [SetoidObject@{so so}] by rebuilding it (the
 library's records are not cumulative), and [PropSetoid] is the
 truth-value setoid one level up.  Instance/Sets.v records where
 the want of a level-[o] truth-value object first bites: the reverse
 direction of [surjectivity_is_epic] ends in a
 non-completing proof, discarded by the command that throws a
 proof away, so that lemma never enters the environment.

 One consequence is worth stating plainly, and stating WITH ITS SCOPE.
 Because the codomain category differs from the domain category, the
 [Type@{o}]-valued power-set functor is NOT an endofunctor, and for THIS
 carrier Riehl's transformation [Id ⟹ P] is not typeable as written:
 [Transform] requires its two functors to share both domain and codomain,
 and here it is the codomains that differ, so [@Id Sets ⟹ Powerset] is
 rejected by the universe checker, with an inconsistency of the shape
 “Cannot enforce u = v because v < u”.  That rejection was checked while
 writing this file; it is not reproduced here as a command, since a
 deliberately ill-typed command in the source would trip the repository's
 hygiene grep.  For this carrier the honest form is
 [Sets_Lift ⟹ Powerset], where [Sets_Lift] is the lifting functor built
 below from Classifier.v's [Setoid_Lift]/[SetoidMorphism_Lift] — a functor
 that changes nothing but the universe: it keeps the carrier verbatim
 ([Setoid_Lift]'s [carrier] field is [carrier X], Classifier.v) and
 the underlying function verbatim up to η ([SetoidMorphism_Lift]'s
 function is [λ a, f a], Classifier.v).

 A RETRACTION, BECAUSE AN EARLIER VERSION OF THIS HEADER OVERSTATED THAT
 SCOPE.  It said that Riehl's [Id ⟹ P] “is not statable” in this library,
 full stop, and offered the universe checker as the reason for it.  That
 is withdrawn.  What the universe checker rejects is [@Id Sets ⟹ Powerset]
 for the specific [Type@{o}]-valued carrier; the general claim does not
 follow from it, and is false.  The step that does not follow is the one
 above: from “[≈] is [Type@{o}]-valued” it was inferred that a subset must
 be valued in [Type@{o}].  A [Prop]-valued predicate respects a
 [Type@{o}]-valued [≈] perfectly well, because [Type@{o} → Prop] is itself
 a [Prop] by the impredicativity of [Prop].  Taking that route — subsets
 valued in [Prop], with the direct-image existential truncated
 impredicatively by [Powerset_squash] — puts the whole power set back at
 level [o] and yields a genuine endofunctor together with Riehl's
 transformation.  Both are built in the last section of this file, as
 [Powerset_Prop] and [Powerset_Prop_Singleton], and both are
 [Print Assumptions]-clean.  The one universe cost is [Set < o], since
 [Prop : Type@{Set+1}].

 The inherited justification does not carry over either.  This header
 claimed that Instance/Sets/Classifier.v “works through the same
 obstruction”.  It does not, and that file says so in its own words:
 [Prop] (with [iff]) “would fit at level o size-wise, but could
 not receive the [Type@{o}]-valued characteristic predicate
 [λ b, ∃ a, m a ≈ b] without truncating away the witness that
 [sets_char_pullback] and [sets_char_unique] must recover”.  The
 classifier's obstruction is WITNESS RECOVERY, forced on it by a pullback
 universal property; a power set carries no such obligation, so truncation
 costs it nothing it is required to have.  In-tree precedent for
 [Prop]-valued subsets at the carrier's own level: Instance/Ens.v,
 whose objects are [∃ T : Type, Ensemble T] with [Ensemble T] the
 [Prop]-valued predicates on [T], and Instance/Rel.v, whose homs are
 [A ~> Ensemble B].

 What truncation genuinely costs is proof relevance, and that is the whole
 reason both carriers are shipped: over [Powerset_Prop] one can no longer
 read back WHICH [x ∈ S] witnessed [y ∈ f S].

 No universe hacks are used: no cumulativity assumptions, no disabled
 universe checking, and every definition below is [Print Assumptions]-clean.
 Impredicativity IS used, in one place and in its standard form —
 [Powerset_squash A := ∀ Q : Prop, (A → Q) → Q] is a [Prop] precisely
 because [Prop] is impredicative, and that is what keeps the truncated
 power set at level [o].  It is a property of the ambient theory rather
 than an added assumption, and it costs no axiom.  Nothing here uses
 [funext]: subsets are compared by pointwise [↔] (or, on the truncated
 carrier, pointwise implication both ways) and setoid maps by pointwise
 [≈], which is the whole point of the setoid discipline
 (Instance/Sets.v). 

 --------
 具有证明相关性的谓词承载体在其集合广义等价类的层级上并不合适，这里采纳的做法是在函子类型中直接说明这一点，而不是隐藏它。本节的所有内容都关于该承载体；文件的最后一节显示了一个截断的承载体确实适用，以及截断的代价。在整个过程中要小心区分各个宇宙层。 

 [Sets@{o so} : Category@{so o o}]（实例/Sets.v），而 [Category@{o h p}] 有 [obj : Type@{o}]。因此 QUA CATEGORY 的对象宇宙 [Sets@{o so}] 是 [so]：它的对象是 [SetoidObject@{o o}]，而 [o] 是这些对象承载体的宇宙——即小集合本身所在的层级。约束 [o < so] 被强制执行（由 [About Sets] 打印为 `o so |= o < so`）。这个库中的态射等价是 [Type] 值的：[Setoid] 承载 [equiv : crelation A]（Lib/Setoid.v），所以对于 [X : SetoidObject@{o o}] 和 [x y : carrier X] 命题 [x ≈ y] 是 [Type@{o}]，而不是 [Prop]。如果选择 [X] 的子集作为 [Type@{o}] 值的谓词——记录每个元素属于它的原因数据——那么它正好是 [PropSetoid] 的承载（Instance/Sets/Classifier.v——承载 [Type@{o}] 在 [↔] 下，这里表示 [iffT]，Lib/Foundation.v）。并且 [Type@{o} : Type@{o+1}]，所以谓词类型 [carrier X → Type@{o}] 位于 [Type@{so}]，比承载高一级。单词 CHOSEN 在这里发挥了真正的作用，而这个标题的早期版本写的是“therefore”——参见下面的撤回。没有任何关于 [Type@{o}] 值的 [≈] 强制子集在 [≈] 的位置上取值；子集只需要遵守 [≈]。

 因此 [Powerset_obj@{o so} : SetoidObject@{o o} → SetoidObject@{so so}]：它将一个 [Sets@{o so}] 的对象映射到一个 [Sets@{so sso}] 的对象。下面的函子在那个跨宇宙类型上被诚实地陈述：

 幂集    : Sets@{o so} ⟶ Sets@{so sso}
 幂集_逆 : (Sets@{o so})^op ⟶ Sets@{so sso}这是同一学科，并且源自同一捐赠者，就像 Instance/Sets/Classifier.v: [Setoid_Lift] 通过重建将 [SetoidObject@{o o}] 重新类型化为 [SetoidObject@{so so}]（库的记录不是累积的），而 [PropSetoid] 是上一级的真值集合。Instance/Sets.v 记录了缺少一级 [o] 真值对象时首次遇到的问题：[surjectivity_is_epic] 的反向方向最终导致未完成的证明，被抛弃证明的命令丢弃，因此该引理从未进入环境。有一个结果值得明确指出，并且说明其范围。因为余域类别不同于定义域类别，所以 [Type@{o}] 值的幂集函子不是一个自函子，并且对于这个承载体 Riehl 的变换 [Id ⟹ P] 按照原文形式是不可类型化的：[Transform] 要求它的两个函子在定义域和余域上都相同，而这里余域不同，所以 [@Id Sets ⟹ Powerset] 被宇宙检查器拒绝，其不一致形式为“无法强制 u = v 因为 v < u”。在编写此文件时，该拒绝情况已被检查；这里没有作为命令重现，因为源代码中故意类型错误的命令会触发仓库的卫生检查 grep。对于这个承载体，诚实的形式是 [Sets_Lift ⟹ Powerset]，其中 [Sets_Lift] 是从 Classifier.v 的 [Setoid_Lift] / [SetoidMorphism_Lift] 构建的提升函子——一个只改变宇宙的函子：它逐字保持承载体（[Setoid_Lift] 的 [carrier] 字段是 [carrier X]，Classifier.v）以及潜在函数逐字保持到 η（[SetoidMorphism_Lift] 的函数是 [λ a, f a]，Classifier.v）。撤回，因为该标题的早期版本夸大了该范围。它曾说 Riehl 的 [Id ⟹ P] “在此库中无法表述”，句号，并以宇宙检查器为理由。这一点被撤回。宇宙检查器拒绝的是特定 [Type@{o}] 值的载体的 [@Id Sets ⟹ Powerset]；从中并不能推出普遍性声明，该声明是错误的。上一步不成立的是：从“[≈] 是 [Type@{o}] 值”推断出一个子集必须被赋值为 [Type@{o}]。[Prop] 值的谓词完全可以兼容 [Type@{o}] 值的 [≈]，因为 [Type@{o} → Prop] 本身就是一个 [Prop]，这得益于 [Prop] 的不可限定性。采取那条路径——在 [Prop] 中取值的子集，其直接像存在量化被 [Powerset_squash] 截断的不可归纳地——将整个幂集放回在 [o] 级别，并产生一个真正的自函子以及 Riehl 的变换。两者都在本文件的最后一节中构建，分别为 [Powerset_Prop] 和 [Powerset_Prop_Singleton]，并且两者都是 [Print Assumptions]-干净的。唯一的宇宙开销是 [Set < o]，因为 [Prop : Type@{Set+1}]。继承的理由也不会传递。这一标题声称 Instance/Sets/Classifier.v“通过相同的阻碍工作”。实际上并非如此，该文件自己也明确说明了这一点：[Prop]（与 [iff]）“在大小上适合 O 级别，但无法在不截断必须由 [sets_char_pullback] 和 [sets_char_unique] 恢复的见证的情况下接收 [Type@{o}] 值特征谓词 [λ b, ∃ a, m a ≈ b]”。分类器的阻碍是见证恢复，这是由拉回的普适性质强加给它的；而幂集不存在这种义务，因此截断不会损失它必需拥有的东西。在载体自身层面上，[Prop] 值子集的树内先例：Instance/Ens.v，其对象是带有 [Ensemble T] 的 [∃ T : Type, Ensemble T] ，[Ensemble T] 是 [T] 上的 [Prop] 值谓词，以及 Instance/Rel.v，其同态是 [A ~> Ensemble B]。

 截断真正的代价是证明相关性，这也是两个载体都被提供的全部原因：在 [Powerset_Prop] 上，再也无法回溯看到哪个 [x ∈ S] 见证了 [y ∈ f S]。没有使用宇宙黑客：没有累积性假设，没有禁用宇宙检查，下面的每个定义都是 [Print Assumptions] -干净的。使用了自反性，在一个地方以其标准形式——[Powerset_squash A := ∀ Q : Prop, (A → Q) → Q] 是 [Prop]，恰恰因为 [Prop] 是自反性的，这也是保持截断幂集在 [o] 级别的原因。这是环境理论的一个性质，而不是额外的假设，也不需要任何公理。这里没有使用 [funext]：子集通过逐点 [↔] 进行比较（或者，在截断载体上，通过双向逐点蕴涵比较）且集合同构映射通过逐点 [≈] 进行比较，这正是集合同构纪律 (Instance/Sets.v) 的全部意义。
*)

(* ------------------------------------------------------------------------ *)
(** ** The predicate setoid [P X] / ** 谓词宿结构 [P X] *)

(*
 A subset of [X] is a predicate on [carrier X] that respects [≈], and two
 subsets are equivalent — [≈], never [=] — when they hold of the same
 elements.  Both halves are already available: a [SetoidMorphism] into
 [PropSetoid] IS a [≈]-respecting [Type@{o}]-valued predicate, and
 [SetoidMorphism_Setoid] compares two of them pointwise in [PropSetoid],
 i.e. by [↔].  So the predicate setoid needs no new record — it is the
 hom-setoid [Setoid_Lift X ~> PropSetoid] of [Sets@{so sso}], packaged as
 an object of that same category. 

 --------
 [X] 的一个子集是在 [carrier X] 上的一个谓词，它尊重 [≈]，并且两个子集是等价的 — [≈]，从不 [=] — 当它们对相同的元素成立时。两个部分都已经可用：一个 [SetoidMorphism] 到 [PropSetoid] 的映射是一个 [≈] 尊重的 [Type@{o}] 值谓词，而 [SetoidMorphism_Setoid] 在 [PropSetoid] 中逐点比较它们中的两个，即通过 [↔]。因此，谓词集合不需要新的记录 — 它是 [Sets@{so sso}] 的同态集合 [Setoid_Lift X ~> PropSetoid]，作为同一范畴的对象封装。
*)

Definition Powerset_obj@{o so} (X : SetoidObject@{o o}) :
  SetoidObject@{so so} :=
  {| carrier   := SetoidMorphism@{so so so} (Setoid_Lift@{o so} X)
                                            PropSetoid@{o so}
   ; is_setoid := @SetoidMorphism_Setoid@{so so so}
                    (Setoid_Lift@{o so} X) PropSetoid@{o so} |}.

(*
 Membership is application of the predicate; this lemma is the [≈]-respect
 of a subset, in the form the proofs below want it. 

 --------
 成员资格是谓词的应用；这个引理是子集的 [≈]-尊重，形式是下面的证明所需要的。
*)
Lemma Powerset_mem_respects@{o so} {X : SetoidObject@{o o}}
  (S : carrier (Powerset_obj@{o so} X)) {x y : carrier X}
  (H : @equiv _ (is_setoid X) x y) : S x → S y.
Proof. exact (fst (@proper_morphism _ _ _ _ S x y H)). Defined.

(* ------------------------------------------------------------------------ *)
(* * ** The lifting functor [Sets_Lift] / * ** 提升函子 [Sets_Lift] *)

(*
 [Setoid_Lift] and [SetoidMorphism_Lift] of Instance/Sets/Classifier.v
 assemble into a functor from [Sets] to [Sets] one universe up.  It is the
 identity on carriers and (up to η) on underlying functions, so both
 functor laws below are a reflexivity and [fmap_respects] hands back its
 own hypothesis; its only job is to give the singleton transformation a
 domain with the right codomain category. 

 --------
 Instance/Sets/Classifier.v 的 [Setoid_Lift] 和 [SetoidMorphism_Lift] 组装成从 [Sets] 到 [Sets] 的函子，比原先的宇宙高一个层级。它在承载对象上是恒等的，并且（在 η 意义下）在底层函数上也是恒等的，因此下面的两个函子律都是自反性，并且 [fmap_respects] 返回它自身的假设；它唯一的作用是为单子转换提供一个具有正确余类别的定义域。
*)

Definition Sets_Lift@{o so sso} : @Functor Sets@{o so} Sets@{so sso}.
Proof.
  unshelve refine
    (@Build_Functor Sets@{o so} Sets@{so sso}
       Setoid_Lift@{o so} (@SetoidMorphism_Lift@{o so}) _ _ _).
  - (* fmap respects ≈: pointwise agreement is unchanged by the lift / fmap 尊重 ≈：点对点的一致性在提升后不变 *)
    intros X Y f g H a; exact (H a).
  - (* fmap_id *)
    intros X a; reflexivity.
  - (* fmap_comp / fmap_组合 *)
    intros X Y Z f g a; reflexivity.
Defined.

(* ------------------------------------------------------------------------ *)
(* * ** The direct image, and the covariant functor / * ** 直接像，和余变函子 *)

(*
 The direct image of [S ⊆ X] along [f : X ~> Y]: the subset of those [y]
 for which some [x ∈ S] has [f x ≈ y].  Note the [≈]: this is the image in
 the setoid sense, and respectfulness in [y] then needs nothing beyond the
 transitivity and symmetry of [≈] in [Y]. 

 --------
 沿着 [f : X ~> Y] 的 [S ⊆ X] 的直接像：那些 [y] 的子集，其中某些 [x ∈ S] 具有 [f x ≈ y]。注意 [≈]：这是集合等价意义下的像，并且在 [y] 中的尊重性仅需 [Y] 中 [≈] 的传递性和对称性。
*)

Definition Powerset_image@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) (S : carrier (Powerset_obj@{o so} X)) :
  carrier (Powerset_obj@{o so} Y).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{so so so}
       (carrier Y) (Setoid_Lift_instance@{o so} (is_setoid Y))
       Type@{o} (is_setoid PropSetoid@{o so})
       (λ y, ∃ x : carrier X, S x ∧ @equiv _ (is_setoid Y) (f x) y) _).
  intros y y' Hyy'; split; intros [x [Hx Hfx]]; exists x; split.
  - exact Hx.
  - now transitivity y.
  - exact Hx.
  - transitivity y'; [exact Hfx | now symmetry].
Defined.

(*
 Taking direct images is itself a setoid map on subsets: equivalent
 subsets have equivalent images. 

 --------
 直接成像本身就是子集上的一个集合映射：等价子集具有等价的像。
*)
Definition Powerset_map@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) :
  SetoidMorphism@{so so so} (Powerset_obj@{o so} X) (Powerset_obj@{o so} Y).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{so so so}
       (carrier (Powerset_obj@{o so} X)) (is_setoid (Powerset_obj@{o so} X))
       (carrier (Powerset_obj@{o so} Y)) (is_setoid (Powerset_obj@{o so} Y))
       (λ S, Powerset_image@{o so} f S) _).
  intros S T HST y; split; intros [x [Hx Hfx]]; exists x; split.
  - exact (fst (HST x) Hx).
  - exact Hfx.
  - exact (snd (HST x) Hx).
  - exact Hfx.
Defined.

Lemma Powerset_map_respects@{o so} {X Y : SetoidObject@{o o}}
  (f g : X ~{Sets@{o so}}~> Y) (H : f ≈ g) :
  Powerset_map@{o so} f ≈ Powerset_map@{o so} g.
Proof.
  intros S y; split; intros [x [Hx Hfx]]; exists x; split.
  - exact Hx.
  - transitivity (f x); [ now symmetry | exact Hfx ].
  - exact Hx.
  - transitivity (g x); [ exact (H x) | exact Hfx ].
Qed.

(*
 Functoriality.  [fmap_id]: the direct image along the identity of [S] is
 the [≈]-saturation of [S], which is [S] itself because subsets respect
 [≈]. 

 --------
 函子性。[fmap_id]：沿着[S]的恒等映射的直接像是[S]的[≈]-饱和集，因为子集遵守[≈]，所以它本身就是[S]。
*)
Lemma Powerset_map_id@{o so} {X : SetoidObject@{o o}} :
  Powerset_map@{o so} (@id Sets@{o so} X) ≈ @setoid_morphism_id@{so so so}
                                              (Powerset_obj@{o so} X).
Proof.
  intros S y; split.
  - intros [x [Hx Hxy]]; exact (Powerset_mem_respects S Hxy Hx).
  - intro Hy; exists y; split; [ exact Hy | reflexivity ].
Qed.

(*
 [fmap_comp]: the image along a composite is the image of the image; the
 intermediate witness is [g x]. 

 --------
 [fmap_comp]：沿复合映射的像是像的像；中间见证是 [g x]。
*)
Lemma Powerset_map_comp@{o so} {X Y Z : SetoidObject@{o o}}
  (f : Y ~{Sets@{o so}}~> Z) (g : X ~{Sets@{o so}}~> Y) :
  Powerset_map@{o so} (f ∘[Sets@{o so}] g)
    ≈ @setoid_morphism_compose@{so so so}
        (Powerset_obj@{o so} X) (Powerset_obj@{o so} Y) (Powerset_obj@{o so} Z)
        (Powerset_map@{o so} f) (Powerset_map@{o so} g).
Proof.
  intros S z; split.
  - intros [x [Hx Hfg]].
    exists (g x); split.
    + exists x; split; [ exact Hx | reflexivity ].
    + exact Hfg.
  - intros [y [[x [Hx Hgy]] Hfz]].
    exists x; split.
    + exact Hx.
    + transitivity (f y); [ exact (proper_morphism f _ _ Hgy) | exact Hfz ].
Qed.

(*
 The covariant power-set functor, at the cross-universe type argued for in
 the header. 

 --------
 协变幂集函子，在标题中讨论的跨宇宙类型上。
*)
Definition Powerset@{o so sso} : @Functor Sets@{o so} Sets@{so sso}.
Proof.
  unshelve refine
    (@Build_Functor Sets@{o so} Sets@{so sso}
       Powerset_obj@{o so} (@Powerset_map@{o so}) _ _ _).
  - intros X Y f g H; exact (Powerset_map_respects@{o so} f g H).
  - intros X; exact (@Powerset_map_id@{o so} X).
  - intros X Y Z f g; exact (@Powerset_map_comp@{o so} X Y Z f g).
Defined.

(*
 [fmap[Powerset]] IS the direct image: the two sides are the very same
 term, so the equality is Leibniz (=) rather than ≈.  This is the same
 situation as [bimap_fmap] in Functor/Bifunctor.v, whose comment
 records the identical justification. 

 --------
 [fmap[Powerset] ] 是直接映像：两边是完全相同的项，所以等号是莱布尼茨等号（=）而不是≈。这与 Functor/Bifunctor.v 中的 [bimap_fmap] 的情况相同，其注释记录了相同的理由。
*)
Lemma Powerset_fmap_image@{o so sso} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) (S : carrier (Powerset_obj@{o so} X)) :
  fmap[Powerset@{o so sso}] f S = Powerset_image@{o so} f S.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------------ *)
(* * ** The inverse image, and the contravariant functor / * ** 逆像，以及逆变函子 *)

(*
 The inverse image of [T ⊆ X] along [f : Y ~> X] is [λ y, T (f y)] — the
 underlying function of [T] composed with that of [f].  No image
 quantifier appears, which is exactly what makes the two actions different
 (see the [Fin]-sized witnesses below). 

 --------
 沿着 [f : Y ~> X] 的 [T ⊆ X] 的逆像是 [λ y, T (f y)] —— [T] 的基础函数与 [f] 的基础函数的复合。没有出现像量化器，这正是使这两个操作不同的原因（见下方 [Fin] 大小的见证）。
*)

Definition Powerset_preimage@{o so} {X Y : SetoidObject@{o o}}
  (f : Y ~{Sets@{o so}}~> X) (T : carrier (Powerset_obj@{o so} X)) :
  carrier (Powerset_obj@{o so} Y).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{so so so}
       (carrier Y) (Setoid_Lift_instance@{o so} (is_setoid Y))
       Type@{o} (is_setoid PropSetoid@{o so})
       (λ y, T (f y)) _).
  intros y y' Hyy'.
  exact (@proper_morphism _ _ _ _ T (f y) (f y')
           (proper_morphism f _ _ Hyy')).
Defined.

Definition Powerset_comap@{o so} {X Y : SetoidObject@{o o}}
  (f : Y ~{Sets@{o so}}~> X) :
  SetoidMorphism@{so so so} (Powerset_obj@{o so} X) (Powerset_obj@{o so} Y).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{so so so}
       (carrier (Powerset_obj@{o so} X)) (is_setoid (Powerset_obj@{o so} X))
       (carrier (Powerset_obj@{o so} Y)) (is_setoid (Powerset_obj@{o so} Y))
       (λ T, Powerset_preimage@{o so} f T) _).
  intros T U HTU y; exact (HTU (f y)).
Defined.

Lemma Powerset_comap_respects@{o so} {X Y : SetoidObject@{o o}}
  (f g : Y ~{Sets@{o so}}~> X) (H : f ≈ g) :
  Powerset_comap@{o so} f ≈ Powerset_comap@{o so} g.
Proof.
  intros T y; split; intro Ht.
  - exact (Powerset_mem_respects T (H y) Ht).
  - exact (Powerset_mem_respects T (symmetry (H y)) Ht).
Qed.

Lemma Powerset_comap_id@{o so} {X : SetoidObject@{o o}} :
  Powerset_comap@{o so} (@id Sets@{o so} X)
    ≈ @setoid_morphism_id@{so so so} (Powerset_obj@{o so} X).
Proof. intros T x; split; intro Ht; exact Ht. Qed.

(*
 Contravariance: the inverse image along [g ∘ f] is the inverse image
 along [f] of the inverse image along [g] — the composition order in
 [Sets] is reversed, which is what [Opposite] arranges. 

 --------
 逆变：沿 [g ∘ f] 的逆像是沿 [f] 的逆像的逆像，沿 [g]——在 [Sets] 中的组合顺序被颠倒，这正是 [Opposite] 所安排的。
*)
Lemma Powerset_comap_comp@{o so} {X Y Z : SetoidObject@{o o}}
  (f : Z ~{Sets@{o so}}~> Y) (g : Y ~{Sets@{o so}}~> X) :
  Powerset_comap@{o so} (g ∘[Sets@{o so}] f)
    ≈ @setoid_morphism_compose@{so so so}
        (Powerset_obj@{o so} X) (Powerset_obj@{o so} Y) (Powerset_obj@{o so} Z)
        (Powerset_comap@{o so} f) (Powerset_comap@{o so} g).
Proof. intros T z; split; intro Ht; exact Ht. Qed.

(* The contravariant power-set functor. / 逆变幂集函子。 *)
Definition Powerset_op@{o so sso} :
  @Functor (Sets@{o so})^op Sets@{so sso}.
Proof.
  unshelve refine
    (@Build_Functor (Sets@{o so})^op Sets@{so sso}
       Powerset_obj@{o so}
       (fun (X Y : SetoidObject@{o o}) (f : Y ~{Sets@{o so}}~> X) =>
          Powerset_comap@{o so} f) _ _ _).
  - intros X Y f g H; exact (Powerset_comap_respects@{o so} f g H).
  - intros X; exact (@Powerset_comap_id@{o so} X).
  - intros X Y Z f g; exact (@Powerset_comap_comp@{o so} X Y Z f g).
Defined.

(*
 As with [Powerset_fmap_image] above: the two sides are the very same
 term, so the equality here is Leibniz (=) and not ≈, on the
 Functor/Bifunctor.v precedent.  The file has five such same-term
 equalities in all, this being the second; the other three
 ([Powerset_Prop_fmap_image], [Powerset_Prop_Lift_obj] and
 [Powerset_Prop_Lift_fmap]) are in the last section and carry the same
 justification.  Every other statement about subsets in this file uses
 [≈]. 

 --------
 与上面的 [Powerset_fmap_image] 一样：两边是完全相同的项，因此这里的等式是莱布尼兹（=），而不是 ≈，依据 Functor/Bifunctor.v 的惯例。该文件共有五个此类同项等式，这是第二个；其他三个（[Powerset_Prop_fmap_image]、[Powerset_Prop_Lift_obj] 和 [Powerset_Prop_Lift_fmap]）在最后一节，并具有相同的理由。文件中关于子集的其他每个声明都使用 [≈]。
*)
Lemma Powerset_op_fmap_preimage@{o so sso} {X Y : SetoidObject@{o o}}
  (f : Y ~{Sets@{o so}}~> X) (T : carrier (Powerset_obj@{o so} X)) :
  fmap[Powerset_op@{o so sso}] (f : X ~{(Sets@{o so})^op}~> Y) T
    = Powerset_preimage@{o so} f T.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------------ *)
(** ** The singleton transformation / ** 单例转换 *)

(* The subset {a}, as a predicate: [λ x, a ≈ x]. / 子集 {a}，作为谓词： [λ x, a ≈ x] 。 *)
Definition Powerset_singleton_pred@{o so} {X : SetoidObject@{o o}}
  (a : carrier X) : carrier (Powerset_obj@{o so} X).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{so so so}
       (carrier X) (Setoid_Lift_instance@{o so} (is_setoid X))
       Type@{o} (is_setoid PropSetoid@{o so})
       (λ x, @equiv _ (is_setoid X) a x) _).
  intros x x' Hxx'; split; intro H.
  - now transitivity x.
  - transitivity x'; [ exact H | now symmetry ].
Defined.

Definition Powerset_singleton_map@{o so} {X : SetoidObject@{o o}} :
  SetoidMorphism@{so so so} (Setoid_Lift@{o so} X) (Powerset_obj@{o so} X).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{so so so}
       (carrier X) (Setoid_Lift_instance@{o so} (is_setoid X))
       (carrier (Powerset_obj@{o so} X)) (is_setoid (Powerset_obj@{o so} X))
       (λ a, Powerset_singleton_pred@{o so} a) _).
  intros a a' Haa' x.
  (*
 [Haa'] arrives at the LIFTED relation of [Setoid_Lift X]; it is
 definitionally the relation of [X] itself, and re-ascribing it here
 keeps the rest of the proof at the level of the carriers. 

 --------
 [Haa'] 到达 [Setoid_Lift X] 的提升关系；从定义上讲，它就是 [X] 本身的关系，而在这里重新赋予它可以使证明的其余部分保持在承载者的层次上。
*)
  assert (Ha : @equiv _ (is_setoid X) a a') by exact Haa'.
  split; intro H.
  - exact (transitivity (symmetry Ha) H).
  - exact (transitivity Ha H).
Defined.

(*
 The naturality square, componentwise: the direct image of a singleton is
 the singleton of the image.  This is where the direct image earns its
 name — the existential over [S] collapses because [S] is a singleton. 

 --------
 自然性平方，逐分量：单元素的直接像是该像的单元素。这就是直接像得名的原因——因为  [S]  上的存在量化消失了，因为  [S]  是一个单元素。
*)
Lemma Powerset_image_singleton@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) (a : carrier X) :
  Powerset_image@{o so} f (Powerset_singleton_pred@{o so} a)
    ≈ Powerset_singleton_pred@{o so} (f a).
Proof.
  intro y; simpl; split.
  - intros [x [Hax Hfy]].
    transitivity (f x); [ exact (proper_morphism f _ _ Hax) | exact Hfy ].
  - intro Hfa; exists a; split; [ reflexivity | exact Hfa ].
Qed.

(*
 Riehl's Example 1.4.4(iii) FOR THE PROOF-RELEVANT CARRIER, in its honest
 cross-universe form: not [Id ⟹ Powerset] — which for this carrier is not
 typeable, since [Id] would have to be a functor into [Sets] one level
 up — but [Sets_Lift ⟹ Powerset], with [Sets_Lift] the carrier-preserving
 lift.  Riehl's statement in its own shape, [Id ⟹ P] with both sides
 endofunctors of one [Sets], is delivered over the truncated carrier as
 [Powerset_Prop_Singleton]. 

 --------
 Riehl 的例子 1.4.4(iii) 关于证明相关载体，在其真实的跨宇宙形式中：不是 [Id ⟹ Powerset] —— 对于这个载体这是不可类型化的，因为 [Id] 必须是进入 [Sets] 上一层的函子 —— 而是 [Sets_Lift ⟹ Powerset]，[Sets_Lift] 是保持载体的提升。Riehl 以其自身形式陈述时，[Id ⟹ P] 两边都是 [Sets] 的自函子，通过截断载体呈现为 [Powerset_Prop_Singleton]。
*)
Definition Powerset_Singleton@{o so sso} :
  @Transform Sets@{o so} Sets@{so sso} Sets_Lift@{o so sso} Powerset@{o so sso}.
Proof.
  unshelve refine
    (@Build_Transform' Sets@{o so} Sets@{so sso}
       Sets_Lift@{o so sso} Powerset@{o so sso}
       (fun X => @Powerset_singleton_map@{o so} X) _).
  intros X Y f a.
  exact (Powerset_image_singleton@{o so} f a).
Defined.

(* ------------------------------------------------------------------------ *)
(* * ** Non-vacuity: the direct image is not a relabelling / * ** 非空性：直接映像不是重新标记 *)

(*
 The witnesses in this section are chosen against three ways of proving
 nothing.

 (1) An INJECTIVE [f] cannot witness that the direct image does anything
 interesting: [Powerset_injective_reflects] below PROVES that along an
 injective map the direct image identifies no two distinct subsets.
 So the genuine witness must use a non-injective map, and it does.

 (2) A DEGENERATE CARRIER cannot witness anything either.  The empty and
 one-element setoids are avoided entirely below: every concrete
 witness in this file uses [Fin.t 2] or [Fin.t 3] (Witness 1 and 1b
 use both, Witness 2 only [Fin.t 2]), and each witness either proves,
 or is stated next to a lemma proving, that the relevant elements are
 distinct — so no conclusion rests on a collapse of the carrier.

 (3) A statement that would hold equally of the IDENTITY functor proves
 nothing about [fmap].  [Powerset_image_moves] below exhibits an [f]
 and an [S] with [fmap[Powerset] f S ≉ S], and
 [Powerset_direct_ne_inverse] separates the covariant action from the
 contravariant one on the same input. 

 --------
 本节中的证人是针对三种证明无效的方法挑选的。

 (1) 一个单射的 [f] 无法证明直接像有什么有趣的行为：下面的 [Powerset_injective_reflects] 证明，在一个单射映射下，直接像不会将两个不同的子集识别为相同。因此，真正的证人必须使用非单射映射，并且确实如此。

 (2) 一个退化的载体也无法证明任何事情。下面完全避免使用空集合和单元素集合：本文件中的每个具体证人都使用 [Fin.t 2] 或 [Fin.t 3]（证人 1 和 1b 都使用这两者，证人 2 仅使用 [Fin.t 2]），且每个证人要么直接证明，要么位于证明相关元素不同的引理旁边，因此没有结论依赖于载体的坍缩。(3) 对于恒等函子成立的陈述，并不能证明关于 [fmap] 的任何事情。下面的 [Powerset_image_moves] 展示了一个 [f] 和一个 [S]，且 [fmap[Powerset] f S ≉ S，并且 [Powerset_direct_ne_inverse] 将协变作用与同一输入上的逆变作用区分开来。
*)

(*
 Distinct points have distinct singletons, and equivalent points have
 equivalent ones: [Powerset_singleton_pred] is injective up to [≈].  This
 is what turns a statement about points into a statement about subsets. 

 --------
 不同的点有不同的单点集，相等的点有相等的单点集：[Powerset_singleton_pred] 在 [≈] 之上是单射的。这就是将关于点的陈述转化为关于子集的陈述的原因。
*)
Lemma Powerset_singleton_faithful@{o so} {X : SetoidObject@{o o}}
  (a b : carrier X) :
  Powerset_singleton_pred@{o so} a ≈ Powerset_singleton_pred@{o so} b
    ↔ @equiv _ (is_setoid X) a b.
Proof.
  split.
  - intro H.
    exact (symmetry (fst (H a) (reflexivity a))).
  - intros Hab x; simpl; split; intro H.
    + transitivity a; [ now symmetry | exact H ].
    + transitivity b; [ exact Hab | exact H ].
Qed.

(*
 THE DEGENERACY THEOREM.  Along an injective map the direct image reflects
 equivalence of subsets: nothing is merged.  This is the precise sense in
 which an injective witness is “just relabelling”, and the reason the
 concrete witnesses below use a non-injective map. 

 --------
 退化定理。沿着单射映射，直接像会反映子集的等价性：没有任何东西被合并。这就是单射见证者“只是重新标记”的确切含义，也是下面具体见证者使用非单射映射的原因。
*)
Theorem Powerset_injective_reflects@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y)
  (Hinj : ∀ a b : carrier X, f a ≈ f b → @equiv _ (is_setoid X) a b)
  (S T : carrier (Powerset_obj@{o so} X))
  (H : Powerset_image@{o so} f S ≈ Powerset_image@{o so} f T) : S ≈ T.
Proof.
  intro x; split; intro Hx.
  - destruct (fst (H (f x)) (existT _ x (Hx, reflexivity (f x))))
      as [x' [Hx' Hfx']].
    exact (Powerset_mem_respects T (Hinj x' x Hfx') Hx').
  - destruct (snd (H (f x)) (existT _ x (Hx, reflexivity (f x))))
      as [x' [Hx' Hfx']].
    exact (Powerset_mem_respects S (Hinj x' x Hfx') Hx').
Qed.

(*
 THE MERGING THEOREM.  Conversely, the direct image merges the singletons
 {a} and {b} EXACTLY when [f a ≈ f b].  Read right-to-left it says the
 direct image collapses fibres; read left-to-right it says it collapses
 nothing else, so the identification on singletons tracks the fibres of
 [f] precisely.  [Powerset_not_injective_on_subsets] below draws out the
 right-to-left corollary in full, rather than leaving it to prose. 

 --------
 合并定理。相反，直接像仅在 \{a\} 和 \{b\} 合并时才成立，此时 [f a ≈ f b]。 从右向左读，它表示直接像会压缩纤维；从左向右读，它表示不会压缩其他任何东西，因此在单元素上的识别精确跟踪了 [f] 的纤维。下面的 [Powerset_not_injective_on_subsets] 完整地展示了从右向左的推论，而不是仅通过文字说明。
*)
Theorem Powerset_merges_fibre@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) (a b : carrier X) :
  Powerset_image@{o so} f (Powerset_singleton_pred@{o so} a)
    ≈ Powerset_image@{o so} f (Powerset_singleton_pred@{o so} b)
  ↔ f a ≈ f b.
Proof.
  split.
  - intro H.
    apply (fst (Powerset_singleton_faithful@{o so} (f a) (f b))).
    transitivity (Powerset_image@{o so} f (Powerset_singleton_pred@{o so} a)).
    { symmetry; exact (Powerset_image_singleton@{o so} f a). }
    transitivity (Powerset_image@{o so} f (Powerset_singleton_pred@{o so} b)).
    { exact H. }
    exact (Powerset_image_singleton@{o so} f b).
  - intro H.
    transitivity (Powerset_singleton_pred@{o so} (f a)).
    { exact (Powerset_image_singleton@{o so} f a). }
    transitivity (Powerset_singleton_pred@{o so} (f b)).
    { exact (snd (Powerset_singleton_faithful@{o so} (f a) (f b)) H). }
    symmetry.
    exact (Powerset_image_singleton@{o so} f b).
Qed.

(*
 The corollary that makes the merging theorem bite, machine-checked rather
 than left as prose: if [f] identifies two DISTINCT points, then
 [fmap[Powerset] f] identifies two distinct subsets — so it is not
 injective on subsets.  (“Not injective” is taken in the positive sense,
 [∃ a b, a ≉ b ∧ f a ≈ f b], which is the sense a witness supplies; the
 negative reading offers no constructive way to extract the pair.) 

 --------
 使合并定理生效的推论，通过机器验证，而不是仅作为文字表述：如果 [f] 识别出两个不同的点，那么 [fmap[Powerset] f] 就会识别出两个不同的子集——因此它在子集上不是单射。（“不是单射”是以积极的意义理解的，即 [∃ a b, a ≉ b ∧ f a ≈ f b]，这也是证据提供的意义；否定的理解无法提供构造性的方法来提取这一对。）
*)
Corollary Powerset_not_injective_on_subsets@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) (a b : carrier X)
  (Hab : @equiv _ (is_setoid X) a b → False) (Hf : f a ≈ f b) :
  (Powerset_singleton_pred@{o so} a ≈ Powerset_singleton_pred@{o so} b
     → False)
  ∧ (Powerset_image@{o so} f (Powerset_singleton_pred@{o so} a)
       ≈ Powerset_image@{o so} f (Powerset_singleton_pred@{o so} b)).
Proof.
  split.
  - intro H.
    exact (Hab (fst (Powerset_singleton_faithful@{o so} a b) H)).
  - exact (snd (Powerset_merges_fibre@{o so} f a b) Hf).
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** Sanity: [FinSet]-sized computations / * ** 理智：[FinSet] 大小的计算 *)

(*
 Small finite setoids, as objects of [Sets]: the standard [Fin.t n] under
 Leibniz equality (the discrete setoid [Fin_Setoid] of Lib/Setoid.v —
 the same one Instance/FinSet.v runs its hom-setoids over, per that
 file's header note).  Only [n = 2] and [n = 3] are used, so no
 witness below rests on an empty or singleton carrier.

 A note on [=] versus [≈] in this section.  Morphism equivalence is still
 [≈] everywhere: every claim about subsets, images and preimages below is
 stated with [≈].  The [=] that appears is Coq's Leibniz equality between
 ELEMENTS of [Fin.t n], and on these carriers [≈] is [=] by construction —
 [Fin_Setoid]'s [equiv] field is [eq] (Lib/Setoid.v) — so writing
 [=] there names the same relation, not a stricter one. 

 --------
 作为 [Sets] 的对象的小有限集合体：在 Leibniz 等式下的标准 [Fin.t n]（Lib/Setoid.v 的离散集合体 [Fin_Setoid]——Instance/FinSet.v 在该文件的标题注释中对其同质集合体进行操作的相同集合体）。这里只使用 [n = 2] 和 [n = 3]，因此下面没有基于空载体或单元素载体的见证。

 关于本节中 [=] 与 [≈] 的说明。态射等价在各处仍然是 [≈]：下面关于子集、像和原像的每个声明都是用 [≈] 表示的。出现的 [=] 是 Coq 中 ELEMENTS 的 Leibniz 等式 [Fin.t n]，在这些载体上 [≈] 是 [=]——[Fin_Setoid] 的 [equiv] 字段是 [eq]（Lib/Setoid.v）——所以在那里写 [=] 表示同一个关系，而不是更严格的关系。
*)

Definition fin_setoid_object (n : nat) : SetoidObject :=
  {| carrier := Fin.t n ; is_setoid := Fin_Setoid |}.

(*
 Every function between discrete setoids is a setoid map: [≈] is [=] on
 both sides, so respectfulness is [f_equal]. 

 --------
 离散集合之间的每个函数都是集合映射：[≈] 在两边都是 [=]，因此可尊重性是 [f_equal]。
*)
Definition fin_map {m n : nat} (f : Fin.t m → Fin.t n) :
  fin_setoid_object m ~{Sets}~> fin_setoid_object n :=
  @Build_SetoidMorphism _ (is_setoid (fin_setoid_object m))
                        _ (is_setoid (fin_setoid_object n))
                        f (fun x y H => f_equal f H).

(*
 [fin32] collapses the first two elements of a three-element set and sends
 the third elsewhere: 0 ↦ 0, 1 ↦ 0, 2 ↦ 1.  It is neither injective (0 and
 1 collide) nor constant (2 goes elsewhere), so neither the merging below
 nor its non-triviality is an artefact of a degenerate map. 

 --------
 [fin32] 将一个三元素集合的前两个元素合并，并将第三个元素发送到其他地方：0 ↦ 0，1 ↦ 0，2 ↦ 1。它既不是单射（0 和 1 冲突），也不是常值映射（2 去向不同），因此下面的合并及其非平凡性都不是一个退化映射的产物。
*)
Definition fin32 (i : Fin.t 3) : Fin.t 2 :=
  Fin.caseS' i (fun _ => Fin.t 2) Fin.F1
    (fun j => Fin.caseS' j (fun _ => Fin.t 2) Fin.F1
                (fun _ => Fin.FS Fin.F1)).

Example fin32_at_0 : fin32 Fin.F1 = Fin.F1 := eq_refl.
Example fin32_at_1 : fin32 (Fin.FS Fin.F1) = Fin.F1 := eq_refl.
Example fin32_at_2 : fin32 (Fin.FS (Fin.FS Fin.F1)) = Fin.FS Fin.F1 := eq_refl.

(* The three elements of [Fin.t 3] used below are pairwise distinct, and so are the two elements of [Fin.t 2]: the carriers are not collapsing. / 下面使用的 [Fin.t 3] 的三个元素两两不同，[Fin.t 2] 的两个元素也是如此：载体没有坍塌。 *)
Lemma fin3_0_ne_1 : @Fin.F1 2 = Fin.FS Fin.F1 → False.
Proof. discriminate. Qed.

Lemma fin2_0_ne_1 : @Fin.F1 1 = Fin.FS Fin.F1 → False.
Proof. discriminate. Qed.

(* WITNESS 1 (merging along a non-injective map). {0} and {1} are distinct subsets of the three-element set... / 证人1（沿非单射映射合并）。{0} 和 {1} 是三元素集合的不同子集... *)
Lemma fin32_singletons_distinct :
  Powerset_singleton_pred (X:=fin_setoid_object 3) Fin.F1
    ≈ Powerset_singleton_pred (X:=fin_setoid_object 3) (Fin.FS Fin.F1)
  → False.
Proof.
  intro H.
  exact (fin3_0_ne_1 (fst (Powerset_singleton_faithful _ _) H)).
Qed.

(* ... but [fmap[Powerset] fin32] sends them to the same subset {0}. / ...但是 [fmap[Powerset] fin32] 将它们发送到同一个子集 {0}。 *)
Lemma fin32_images_merge :
  fmap[Powerset] (fin_map fin32)
      (Powerset_singleton_pred (X:=fin_setoid_object 3) Fin.F1)
    ≈ fmap[Powerset] (fin_map fin32)
        (Powerset_singleton_pred (X:=fin_setoid_object 3) (Fin.FS Fin.F1)).
Proof.
  exact (snd (Powerset_merges_fibre (fin_map fin32) Fin.F1 (Fin.FS Fin.F1))
             eq_refl).
Qed.

(*
 And the merging is not because the action is constant: the third
 singleton has a DIFFERENT image, so [fmap[Powerset] fin32] takes at least
 two values on singletons.  Together with the previous lemma, and with the
 left-to-right half of [Powerset_merges_fibre], this says that the
 identification here tracks the fibres of [fin32] and nothing more. 

 --------
 并且合并并不是因为动作是恒定的：第三个单元素集有一个不同的像，所以 [fmap[Powerset] fin32] 在单元素集上至少取两个值。结合前面的引理，以及 [Powerset_merges_fibre] 的从左到右的一半，这表明这里的识别跟踪了 [fin32] 的纤维，而没有更多。
*)
Lemma fin32_third_image_distinct :
  fmap[Powerset] (fin_map fin32)
      (Powerset_singleton_pred (X:=fin_setoid_object 3) Fin.F1)
    ≈ fmap[Powerset] (fin_map fin32)
        (Powerset_singleton_pred (X:=fin_setoid_object 3)
           (Fin.FS (Fin.FS Fin.F1)))
  → False.
Proof.
  intro H.
  exact (fin2_0_ne_1
           (fst (Powerset_merges_fibre (fin_map fin32) Fin.F1
                   (Fin.FS (Fin.FS Fin.F1))) H)).
Qed.

(*
 The direct image of a two-element subset of [Fin.t 3] is computed as
 expected: {0,1} maps onto {0}, a PROPER subset of the two-element target
 (the second lemma), so the image is not everything either. 

 --------
 ZW0WZZ 的一个二元子集的直接像按预期计算：{0,1} 映射到 {0}，是二元目标的一个真子集（第二个引理），因此像也不是全部。
*)
Definition fin3_sub01 : carrier (Powerset_obj (fin_setoid_object 3)).
Proof.
  unshelve refine {| morphism := fun i : Fin.t 3 =>
                       (i = Fin.F1) ∨ (i = Fin.FS Fin.F1) |}.
  intros x y ->; split; intro H; exact H.
Defined.

Lemma fin32_image_sub01 :
  fmap[Powerset] (fin_map fin32) fin3_sub01
    ≈ Powerset_singleton_pred (X:=fin_setoid_object 2) Fin.F1.
Proof.
  intro y; split.
  - intros [i [Hi Hfi]].
    destruct Hi as [H0 | H1].
    + rewrite <- Hfi, H0; reflexivity.
    + rewrite <- Hfi, H1; reflexivity.
  - intro Hy.
    exists Fin.F1; split.
    + exact (Datatypes.inl eq_refl).
    + exact Hy.
Qed.

Lemma fin32_image_sub01_proper_subset :
  fmap[Powerset] (fin_map fin32) fin3_sub01 (Fin.FS Fin.F1) → False.
Proof.
  intro H.
  exact (fin2_0_ne_1 (fst (fin32_image_sub01 (Fin.FS Fin.F1)) H)).
Qed.

(* [fin3_sub01] really does have exactly two elements, and they are distinct: nothing below rests on it accidentally collapsing. / [fin3_sub01] 确实恰好有两个元素，并且它们是不同的：下面没有东西会因意外坍塌而依赖它。 *)
Lemma fin3_sub01_has_0 : fin3_sub01 Fin.F1.
Proof. exact (Datatypes.inl eq_refl). Qed.

Lemma fin3_sub01_has_1 : fin3_sub01 (Fin.FS Fin.F1).
Proof. exact (Datatypes.inr eq_refl). Qed.

Lemma fin3_sub01_lacks_2 : fin3_sub01 (Fin.FS (Fin.FS Fin.F1)) → False.
Proof. intros [H | H]; discriminate. Qed.

(*
 Having two distinct elements, [fin3_sub01] is equivalent to no singleton
 at all.  This is what makes the inverse-image witness below substantive:
 the direct image of a singleton is always a singleton
 ([Powerset_image_singleton]), so no direct image of a singleton can equal
 this subset. 

 --------
 具有两个不同的元素，[fin3_sub01] 相当于根本不存在单元素集合。这就是下面的逆像证据具有实质性的原因：单元素集合的直像总是单元素集合（[Powerset_image_singleton]），所以单元素集合的任何直像都不可能等于这个子集。
*)
Lemma fin3_sub01_not_singleton (a : Fin.t 3) :
  fin3_sub01 ≈ Powerset_singleton_pred (X:=fin_setoid_object 3) a → False.
Proof.
  intro H.
  assert (H0 : a = Fin.F1) by exact (fst (H Fin.F1) fin3_sub01_has_0).
  assert (H1 : a = Fin.FS Fin.F1)
    by exact (fst (H (Fin.FS Fin.F1)) fin3_sub01_has_1).
  exact (fin3_0_ne_1 (eq_trans (eq_sym H0) H1)).
Qed.

(*
 A three-way eliminator for [Fin.t 3], assembled from the standard
 library's [Fin.caseS'] and [Fin.case0] — the same two primitives
 Instance/FinSet.v uses, in [fin_split] (via [Fin.caseS']) and in
 [FinSet_Initial] (via [Fin.case0]).  No [dependent destruction] is
 used anywhere in this file, and [Print Assumptions] reports every
 constant here closed under the global context. 

 --------
 一个针对 [Fin.t 3] 的三向消元器，由标准库的 [Fin.caseS'] 和 [Fin.case0] 组装而成——Instance/FinSet.v 在 [fin_split]（通过 [Fin.caseS']）和 [FinSet_Initial]（通过 [Fin.case0]）中使用的同两个原语。本文件中没有使用任何 [dependent destruction]，而 [Print Assumptions] 报告此处每个常量在全局上下文下是封闭的。
*)
Definition fin3_case (P : Fin.t 3 → Type)
  (H0 : P Fin.F1) (H1 : P (Fin.FS Fin.F1))
  (H2 : P (Fin.FS (Fin.FS Fin.F1))) : ∀ i : Fin.t 3, P i.
Proof.
  intro i.
  apply (Fin.caseS' i P H0); intro j.
  apply (Fin.caseS' j (fun j => P (Fin.FS j)) H1); intro k.
  apply (Fin.caseS' k (fun k => P (Fin.FS (Fin.FS k))) H2); intro l.
  exact (Fin.case0 (fun l => P (Fin.FS (Fin.FS (Fin.FS l)))) l).
Defined.

(*
 WITNESS 1b (the inverse image along the same non-injective, NON-ENDO map).
 Pulling the singleton {0} back along [fin32] GROWS it to the two-element
 {0,1} — the fibre of 0.  This is beyond anything the direct image can do
 to a singleton: [Powerset_image_singleton] says every direct image of a
 singleton IS a singleton, and [fin3_sub01_not_singleton] says this subset
 is not one.  The map here is not an endomorphism, so the two sides even
 live in different power sets, which the covariant action could not
 arrange from this starting point. 

 --------
 见证 1b（沿着相同的非单射、非自同态映射的逆像）。
 将单元素集合 {0} 沿 [fin32] 拉回，会将其扩展为包含两个元素的集合 {0,1}——0 的纤维。这超出了直接像对单元素集合所能做的范围：[Powerset_image_singleton] 说明单元素集合的每个直接像都是单元素集合，而 [fin3_sub01_not_singleton] 说明这个子集不是单元素集合。这里的映射不是自同态，因此两边甚至位于不同的幂集里，而从这个起点，共变作用无法安排这种情况。
*)
Lemma fin32_preimage_sng0 :
  fmap[Powerset_op] (fin_map fin32 : fin_setoid_object 2
                       ~{(Sets)^op}~> fin_setoid_object 3)
      (Powerset_singleton_pred (X:=fin_setoid_object 2) Fin.F1)
    ≈ fin3_sub01.
Proof.
  refine (fin3_case
            (fun i => fmap[Powerset_op] (fin_map fin32 : fin_setoid_object 2
                          ~{(Sets)^op}~> fin_setoid_object 3)
                        (Powerset_singleton_pred
                           (X:=fin_setoid_object 2) Fin.F1) i
                      ↔ fin3_sub01 i) _ _ _).
  - split; intro H.
    + exact (Datatypes.inl eq_refl).
    + exact eq_refl.
  - split; intro H.
    + exact (Datatypes.inr eq_refl).
    + exact eq_refl.
  - split; intro H.
    + discriminate H.
    + destruct H; discriminate.
Qed.

(*
 WITNESS 2 (the action is not the identity, and not the inverse image).
 [fin_const0] is the constant map [Fin.t 2 → Fin.t 2] at 0; both actions
 then land in the same setoid [Powerset_obj (fin_setoid_object 2)], so
 they can be compared directly. 

 --------
 证人 2（作用不是恒等，也不是逆像）。
 [fin_const0] 是在 0 的常值映射 [Fin.t 2 → Fin.t 2]；随后两个作用都映射到同一个集合化 [Powerset_obj (fin_setoid_object 2)]，因此可以直接比较。
*)
Definition fin_const0 : Fin.t 2 → Fin.t 2 := fun _ => Fin.F1.

Lemma fin_const0_image :
  fmap[Powerset] (fin_map fin_const0)
      (Powerset_singleton_pred (X:=fin_setoid_object 2) (Fin.FS Fin.F1))
    ≈ Powerset_singleton_pred (X:=fin_setoid_object 2) Fin.F1.
Proof.
  exact (Powerset_image_singleton (fin_map fin_const0) (Fin.FS Fin.F1)).
Qed.

(*
 The direct image MOVES the subset {1} to {0}; the identity functor's
 action would have left it where it was. 

 --------
 直接像将子集 {1} 移动到 {0}；恒等函子作用的话，本来会保持它在原处。
*)
Lemma Powerset_image_moves :
  fmap[Powerset] (fin_map fin_const0)
      (Powerset_singleton_pred (X:=fin_setoid_object 2) (Fin.FS Fin.F1))
    ≈ Powerset_singleton_pred (X:=fin_setoid_object 2) (Fin.FS Fin.F1)
  → False.
Proof.
  intro H.
  apply fin2_0_ne_1.
  apply (fst (Powerset_singleton_faithful
                (X:=fin_setoid_object 2) Fin.F1 (Fin.FS Fin.F1))).
  transitivity (fmap[Powerset] (fin_map fin_const0)
                  (Powerset_singleton_pred (X:=fin_setoid_object 2)
                     (Fin.FS Fin.F1))).
  { symmetry; exact fin_const0_image. }
  exact H.
Qed.

(*
 The inverse image of {1} along the same constant map is EMPTY, while its
 direct image contains 0.  So on this one input, in this one power set,
 the covariant action and the contravariant action of the same morphism
 disagree. 

 --------
 沿着相同的常数映射，{1} 的逆像是空的，而它的直接像包含 0。因此，在这个输入上，在这个幂集中，相同态射的协变作用和逆变作用是不同的。
*)
Lemma fin_const0_preimage_empty (y : Fin.t 2) :
  fmap[Powerset_op] (fin_map fin_const0 : fin_setoid_object 2
                       ~{(Sets)^op}~> fin_setoid_object 2)
      (Powerset_singleton_pred (X:=fin_setoid_object 2) (Fin.FS Fin.F1)) y
  → False.
Proof. intro H; exact (fin2_0_ne_1 (eq_sym H)). Qed.

Lemma fin_const0_image_inhabited :
  fmap[Powerset] (fin_map fin_const0)
      (Powerset_singleton_pred (X:=fin_setoid_object 2) (Fin.FS Fin.F1))
      Fin.F1.
Proof. exact (snd (fin_const0_image Fin.F1) (reflexivity _)). Qed.

Theorem Powerset_direct_ne_inverse :
  fmap[Powerset] (fin_map fin_const0)
      (Powerset_singleton_pred (X:=fin_setoid_object 2) (Fin.FS Fin.F1))
    ≈ fmap[Powerset_op] (fin_map fin_const0 : fin_setoid_object 2
                           ~{(Sets)^op}~> fin_setoid_object 2)
        (Powerset_singleton_pred (X:=fin_setoid_object 2) (Fin.FS Fin.F1))
  → False.
Proof.
  intro H.
  exact (fin_const0_preimage_empty Fin.F1
           (fst (H Fin.F1) fin_const0_image_inhabited)).
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** The second carrier: [Prop]-valued subsets, and a genuine endofunctor / * ** 第二个承载体：[Prop] 值的子集，以及一个真正的自函子 *)

(*
 Everything above is about the proof-relevant carrier, which lands one
 universe up and so is not an endofunctor.  This section builds the other
 carrier, at the SAME universe as the sets it is a power set of, and with
 it the two things the cross-universe carrier cannot supply: an
 endofunctor of [Sets], and Riehl's Example 1.4.4(iii) in its own shape,
 [Id ⟹ P].

 The move is the one the header's retraction describes.  A subset is not
 obliged to be valued where [≈] is valued; it is only obliged to RESPECT
 [≈].  So take subsets to be [Prop]-valued and truncate the direct image's
 existential impredicatively.  [Prop] then serves as the truth-value
 object at level [o] itself, and the whole power set stays put.

 Three prices are paid here, all of them visible in the types.

 (1) PROOF RELEVANCE.  [Powerset_squash (∃ x, S x ∧ f x ≈ y)] records
 only THAT some [x] witnesses membership, never which; the
 [Type@{o}]-valued carrier above records which.  This is the reason
 both carriers are shipped.  [Powerset_truncate] at the end of this
 section is the comparison between them, and it runs from the
 proof-relevant carrier to this one.  No map in the other direction
 is built here, and none is claimed either way.

 (2) [Set < o].  [Prop : Type@{Set+1}], so a [SetoidObject@{o o}] whose
 carrier is [Prop] forces [Set < o].  That is harmless in itself,
 but it does mean the [Fin]-based witnesses of the previous section
 cannot be reused verbatim: [fin_setoid_object] is pinned at
 [SetoidObject@{Set Set}] because [Fin_Setoid] (Lib/Setoid.v) is
 [Setoid@{Set Set}].  Hence the separate, universe-polymorphic
 [Powerset_Prop_fin_object] below, which is the only reason it
 exists.

 (3) [Powerset_Prop_truth]'s equivalence is [Prop]-valued (Coq's [/\] of
 the two implications), where [PropSetoid]'s is [Type]-valued
 ([↔] = [iffT]).  So the projections of an [≈] between two subsets
 are [proj1]/[proj2] in this section and [fst]/[snd] above.  The
 proofs below use [hnf in H] where a hypothesis whose type is a
 [Powerset_squash] arrives still wrapped in the constant that
 produced it.

 Nothing else changes: [≈] is still how morphisms and subsets are compared
 here (apart from the same-term [=] lemmas, which are flagged individually
 where they occur), no axiom is used, and no [funext]. 

 --------
 以上所有内容都关于证明相关的承载体，它位于一个更高的宇宙，因此不是自函子。本节构建另一种承载体，它位于与其所生成的集合相同的宇宙中，并且能够实现跨宇宙承载体无法提供的两个功能：[Sets] 的自函子，以及 Riehl 的例 1.4.4(iii) 以其自身形态呈现，即 [Id ⟹ P]。

 这个操作就是标题所描述的收缩那样。一个子集不必在 [≈] 所处的值域中取值；它只必须尊重 [≈]。因此，将子集取为 [Prop] 值，并以非建设性的方式截断直接像的存在性。[Prop] then serves as the truth-value object at level [o] itself, 整个幂集保持原位。

 这里付出了三个代价，全部在类型中可见。(1) 证据相关性。[Powerset_squash (∃ x, S x ∧ f x ≈ y)] 仅记录某些 [x] 是否是见证成员，从未记录具体哪些；上述 [Type@{o}] 值载体记录了具体哪些。这就是两个载体都被发送的原因。本节末尾的 [Powerset_truncate] 是它们之间的比较，它是从与证据相关的载体到这个载体进行的。这里没有建立任何反向映射，也没有对任何方向声称存在映射。(2) [Set < o]。[Prop : Type@{Set+1}]，所以一个载体是[Prop]的[SetoidObject@{o o}]会强制[Set < o]。这本身是无害的，但确实意味着前一节基于[Fin]的证明不能逐字重复使用：[fin_setoid_object]被固定在[SetoidObject@{Set Set}]，因为[Fin_Setoid]（Lib/Setoid.v）是[Setoid@{Set Set}]。因此下面独立的、宇宙多态的[Powerset_Prop_fin_object]存在，这是其存在的唯一原因。(3) [Powerset_Prop_truth] 的等价性是 [Prop] 值的（Coq 的 [/\] 关于两个蕴含），其中 [PropSetoid] 的值是 [Type]（[↔] = [iffT]）。因此，在两子集之间的 [≈] 的投影在本节中是 [proj1] / [proj2]，在上文中是 [fst] / [snd]。下面的证明使用 [hnf in H]，其中类型为 [Powerset_squash] 的假设仍然被产生它的常量包裹着。 

 其他没有改变：[≈] 仍然是这里比较态射和子集的方式（除了相同项 [=] 引理，它们在出现的地方单独标记），没有使用公理，也没有 [funext]。
*)

(*
 Propositional truncation, impredicatively.  [∀ Q : Prop, (A → Q) → Q] is
 a [Prop] whatever universe [A] lives in, which is exactly what keeps the
 power set at level [o]. 

 --------
 命题截断，以自反的方式。[∀ Q : Prop, (A → Q) → Q] 是一个 [Prop]，无论 [A] 生活在哪个宇宙中，这正是使幂集保持在 [o] 层级的原因。
*)
Definition Powerset_squash@{o} (A : Type@{o}) : Prop := ∀ Q : Prop, (A → Q) → Q.

Definition Powerset_squash_intro@{o} {A : Type@{o}} (a : A) :
  Powerset_squash@{o} A := fun Q k => k a.

(*
 The truth-value object at level [o]: [Prop] under mutual implication.
 Assembled in the same shape as [PropSetoid] (Classifier.v), one
 universe lower.  [Prop : Type@{Set+1}], which is where the [Set < o]
 constraint comes from. 

 --------
 在互相蕴涵下，位于 [o] 级别的真值对象：[Prop]。以与 [PropSetoid]（Classifier.v）相同的形状组装，低一个宇宙。[Prop : Type@{Set+1}]，即 [Set < o] 约束的来源。
*)
Definition Powerset_Prop_truth_equiv@{o} : crelation@{o o} Prop :=
  λ P Q : Prop, (P → Q) /\ (Q → P).

Lemma Powerset_Prop_truth_equivalence@{o} :
  Equivalence@{o o} Powerset_Prop_truth_equiv@{o}.
Proof.
  unfold Powerset_Prop_truth_equiv; constructor.
  - intro P; split; intro H; exact H.
  - intros P Q [HPQ HQP]; split; assumption.
  - intros P Q R [HPQ HQP] [HQR HRQ]; split; intro H; auto.
Qed.

Definition Powerset_Prop_truth@{o} : SetoidObject@{o o} :=
  {| carrier   := Prop
   ; is_setoid := {| equiv        := Powerset_Prop_truth_equiv@{o}
                   ; setoid_equiv := Powerset_Prop_truth_equivalence@{o} |} |}.

(*
 A truncated subset of [X] is a [≈]-respecting [Prop]-valued predicate —
 that is, a [SetoidMorphism] into [Powerset_Prop_truth], compared
 pointwise by [SetoidMorphism_Setoid], exactly as [Powerset_obj] is
 compared.  No lift appears: domain and codomain are both at [o]. 

 --------
 [X] 的一个截断子集是一个 [≈]-遵循的 [Prop] 值谓词——它是一个从 [SetoidMorphism] 到 [Powerset_Prop_truth] 的映射，通过 [SetoidMorphism_Setoid] 逐点比较，就像比较 [Powerset_obj] 一样。没有提升出现：定义域和值域都在 [o]。
*)
Definition Powerset_Prop_obj@{o} (X : SetoidObject@{o o}) : SetoidObject@{o o} :=
  {| carrier   := SetoidMorphism@{o o o} X Powerset_Prop_truth@{o}
   ; is_setoid := @SetoidMorphism_Setoid@{o o o} X Powerset_Prop_truth@{o} |}.

(* The direct image, truncated: [y] belongs to [f S] when SOME [x ∈ S] has [f x ≈ y], with the “some” squashed. / 直接图像，截断：[y] 属于 [f S] 当某些 [x ∈ S] 拥有 [f x ≈ y]，‘某些’被压缩。 *)
Definition Powerset_Prop_image@{o} {X Y : SetoidObject@{o o}}
  (f : SetoidMorphism@{o o o} X Y) (S : carrier (Powerset_Prop_obj@{o} X)) :
  carrier (Powerset_Prop_obj@{o} Y).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier Y) (is_setoid Y) Prop (is_setoid Powerset_Prop_truth@{o})
       (λ y, Powerset_squash@{o}
               (∃ x : carrier X, S x ∧ @equiv _ (is_setoid Y) (f x) y)) _).
  intros y y' Hyy'; split; intros H Q k; apply H; intros [x [Hx Hfx]];
    apply k; exists x; split; try exact Hx.
  - now transitivity y.
  - transitivity y'; [ exact Hfx | now symmetry ].
Defined.

(* Equivalent subsets have equivalent images. / 等价子集有等价的映像。 *)
Definition Powerset_Prop_map@{o} {X Y : SetoidObject@{o o}}
  (f : SetoidMorphism@{o o o} X Y) :
  SetoidMorphism@{o o o} (Powerset_Prop_obj@{o} X) (Powerset_Prop_obj@{o} Y).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier (Powerset_Prop_obj@{o} X)) (is_setoid (Powerset_Prop_obj@{o} X))
       (carrier (Powerset_Prop_obj@{o} Y)) (is_setoid (Powerset_Prop_obj@{o} Y))
       (λ S, Powerset_Prop_image@{o} f S) _).
  intros S T HST y; split; intros H Q k; apply H; intros [x [Hx Hfx]];
    apply k; exists x; split; try exact Hfx.
  - exact (proj1 (HST x) Hx).
  - exact (proj2 (HST x) Hx).
Defined.

(* [fmap_respects]. / [fmap_respects] 。 *)
Lemma Powerset_Prop_map_respects@{o} {X Y : SetoidObject@{o o}}
  (f g : SetoidMorphism@{o o o} X Y) (H : f ≈ g) :
  Powerset_Prop_map@{o} f ≈ Powerset_Prop_map@{o} g.
Proof.
  intros S y; split; intros Hs Q k; hnf in Hs; apply Hs; intros [x [Hx Hfx]];
    apply k; exists x; split; try exact Hx.
  - transitivity (f x); [ now symmetry | exact Hfx ].
  - transitivity (g x); [ exact (H x) | exact Hfx ].
Qed.

(*
 [fmap_id]: as for the proof-relevant carrier, the image of [S] along the
 identity is the [≈]-saturation of [S], which is [S] because subsets
 respect [≈]. 

 --------
 [fmap_id]：至于与证明相关的载体，[S] 沿着恒等映射的像是 [S] 的 [≈]-饱和，因为子集遵循 [≈]，所以它是 [S]。
*)
Lemma Powerset_Prop_map_id@{o} {X : SetoidObject@{o o}} :
  Powerset_Prop_map@{o} (@setoid_morphism_id@{o o o} X)
    ≈ @setoid_morphism_id@{o o o} (Powerset_Prop_obj@{o} X).
Proof.
  intros S y; split; intro H.
  - hnf in H; apply H; intros [x [Hx Hxy]].
    exact (proj1 (@proper_morphism _ _ _ _ S x y Hxy) Hx).
  - exact (Powerset_squash_intro@{o} (existT _ y (H, reflexivity y))).
Qed.

(* [fmap_comp]: the intermediate witness is [g x], and the truncation goes through because the goal is a [Prop] at every step. / [fmap_comp]：中间见证是[g x]，并且截断通过了，因为目标是在每一步都是[Prop]。 *)
Lemma Powerset_Prop_map_comp@{o} {X Y Z : SetoidObject@{o o}}
  (f : SetoidMorphism@{o o o} Y Z) (g : SetoidMorphism@{o o o} X Y) :
  Powerset_Prop_map@{o} (@setoid_morphism_compose@{o o o} X Y Z f g)
    ≈ @setoid_morphism_compose@{o o o}
        (Powerset_Prop_obj@{o} X) (Powerset_Prop_obj@{o} Y)
        (Powerset_Prop_obj@{o} Z)
        (Powerset_Prop_map@{o} f) (Powerset_Prop_map@{o} g).
Proof.
  intros S z; split; intros H Q k; hnf in H; apply H.
  - intros [x [Hx Hfg]]; apply k; exists (g x); split.
    + exact (Powerset_squash_intro@{o} (existT _ x (Hx, reflexivity (g x)))).
    + exact Hfg.
  - intros [y [Hy Hfz]]; hnf in Hy; apply Hy; intros [x [Hx Hgy]]; apply k;
      exists x; split; [ exact Hx | ].
    transitivity (f y); [ exact (proper_morphism f _ _ Hgy) | exact Hfz ].
Qed.

(*
 THE ENDOFUNCTOR.  Domain and codomain are the same category, at the same
 universes — which is the whole point of this section. 

 --------
 端函子。定义域和余域是相同的范畴，在相同的宇宙中——这正是本节的重点。
*)
Definition Powerset_Prop@{o so} : @Functor Sets@{o so} Sets@{o so}.
Proof.
  unshelve refine
    (@Build_Functor Sets@{o so} Sets@{o so}
       Powerset_Prop_obj@{o} (@Powerset_Prop_map@{o}) _ _ _).
  - intros X Y f g H; exact (Powerset_Prop_map_respects@{o} f g H).
  - intros X; exact (@Powerset_Prop_map_id@{o} X).
  - intros X Y Z f g; exact (@Powerset_Prop_map_comp@{o} X Y Z f g).
Defined.

(* As with [Powerset_fmap_image]: the two sides are the very same term, so the equality is Leibniz (=) rather than ≈, on the Functor/Bifunctor.v precedent. / 与 [Powerset_fmap_image] 一样：两边是完全相同的项，所以等式是 Leibniz (=) 而不是 ≈，依据 Functor/Bifunctor.v 的先例。 *)
Lemma Powerset_Prop_fmap_image@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) (S : carrier (Powerset_Prop_obj@{o} X)) :
  fmap[Powerset_Prop@{o so}] f S = Powerset_Prop_image@{o} f S.
Proof. reflexivity. Qed.

(* The truncated singleton {a}: [λ x, Powerset_squash (a ≈ x)]. / 截断的单例 {a}：[λ x, Powerset_squash (a ≈ x)]。 *)
Definition Powerset_Prop_singleton_pred@{o} {X : SetoidObject@{o o}}
  (a : carrier X) : carrier (Powerset_Prop_obj@{o} X).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier X) (is_setoid X) Prop (is_setoid Powerset_Prop_truth@{o})
       (λ x, Powerset_squash@{o} (@equiv _ (is_setoid X) a x)) _).
  intros x x' Hxx'; split; intros H Q k; apply H; intro Ha; apply k.
  - now transitivity x.
  - transitivity x'; [ exact Ha | now symmetry ].
Defined.

Definition Powerset_Prop_singleton_map@{o} {X : SetoidObject@{o o}} :
  SetoidMorphism@{o o o} X (Powerset_Prop_obj@{o} X).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier X) (is_setoid X)
       (carrier (Powerset_Prop_obj@{o} X)) (is_setoid (Powerset_Prop_obj@{o} X))
       (λ a, Powerset_Prop_singleton_pred@{o} a) _).
  intros a a' Haa' x; split; intros H Q k; hnf in H; apply H; intro Hx; apply k.
  - transitivity a; [ now symmetry | exact Hx ].
  - transitivity a'; [ exact Haa' | exact Hx ].
Defined.

(*
 The naturality square, componentwise: the direct image of a singleton is
 the singleton of the image, and truncation respects that because the
 existential over a singleton collapses. 

 --------
 自然性方块，逐分量：单例的直接像是像的单例，并且截断遵循这一点，因为单例上的存在量化会坍缩。
*)
Lemma Powerset_Prop_image_singleton@{o} {X Y : SetoidObject@{o o}}
  (f : SetoidMorphism@{o o o} X Y) (a : carrier X) :
  Powerset_Prop_image@{o} f (Powerset_Prop_singleton_pred@{o} a)
    ≈ Powerset_Prop_singleton_pred@{o} (f a).
Proof.
  intro y; split; intros H Q k; hnf in H; apply H.
  - intros [x [Hax Hfy]]; hnf in Hax; apply Hax; intro Ha; apply k.
    transitivity (f x); [ exact (proper_morphism f _ _ Ha) | exact Hfy ].
  - intro Hfa; apply k; exists a; split;
      [ exact (Powerset_squash_intro@{o} (reflexivity a)) | exact Hfa ].
Qed.

(*
 RIEHL EXAMPLE 1.4.4(iii), IN ITS OWN SHAPE.  Both sides are endofunctors
 of one and the same [Sets@{o so}]; the naturality square is the lemma
 immediately above, and is proved, not postulated. 

 --------
 RIEHL 示例 1.4.4(iii)，以其自身的形式。两边都是同一个 [Sets@{o so}] 的自函子；自然性方形是上面紧接的引理，并且是被证明的，而非假设的。
*)
Definition Powerset_Prop_Singleton@{o so} :
  @Transform Sets@{o so} Sets@{o so} (@Id Sets@{o so}) Powerset_Prop@{o so}.
Proof.
  unshelve refine
    (@Build_Transform' Sets@{o so} Sets@{o so}
       (@Id Sets@{o so}) Powerset_Prop@{o so}
       (fun X => @Powerset_Prop_singleton_map@{o} X) _).
  intros X Y f a.
  exact (Powerset_Prop_image_singleton@{o} f a).
Defined.

(* ------------------------------------------------------------------------ *)
(* * ** The blocked consumers, unblocked / * ** 被屏蔽的消费者，已取消屏蔽 *)

(*
 [Theory/Monad.v] ([Context `{M : C ⟶ C}]) and
 [Construction/FAlg.v] ([Program Definition FAlg `(F : C ⟶ C)]) each
 require an endofunctor, so over [Powerset] neither of the two types below
 can be formed: substituting it reports “The term ”Powerset“ has type
 ”Sets@{a b} ⟶ Sets@{b c}“ while it is expected to have type
 ”Sets@{d e} ⟶ Sets@{d e}“”, with the same universe inconsistency as
 before.  Over [Powerset_Prop] both types elaborate, and naming them here
 puts that claim in the environment where the type checker settles it,
 instead of leaving it as a sentence in a comment.

 These are TYPES, not constructions.  No monad structure and no initial
 algebra is built anywhere in this file; #466 and #750 remain open.  What
 has changed is that they can now be stated over a carrier that lives in
 this module.  CORRECTION (#466): #466 is delivered, outside this file.
 Instance/Sets/Powerset/Monad.v builds the monad on [Powerset_Prop] with
 #227's singleton transformation as its unit, and its readback
 [Powerset_Monad_statement] inhabits [Powerset_Prop_Monad_statement];
 Instance/SupLat.v identifies the monad's algebras with the complete
 semilattices.  #750, the initial-algebra question, remains open. 

 --------
 [Theory/Monad.v]（[Context `{M : C ⟶ C}]）和 [Construction/FAlg.v]（[Program Definition FAlg `(F : C ⟶ C)]）各自都需要一个 endofunctor，因此在 [Powerset] 上无法形成下面的两种类型：替换时会报告“术语 'Powerset' 的类型为 'Sets@{a b} ⟶ Sets@{b c}'，而期望的类型为 'Sets@{d e} ⟶ Sets@{d e}'”，与之前相同的范畴不一致。在 [Powerset_Prop] 上，两种类型都能够展开，这里为它们命名将该声明放入类型检查器可以解决它的环境中，而不是仅仅作为注释中的一句话。这些是类型，不是构造。在这个文件中没有构建任何单子结构和初始代数；#466 和 #750 仍然未解决。变化在于它们现在可以在存在于此模块中的承载上陈述。修正 (#466)：#466 已在此文件之外交付。Instance/Sets/Powerset/Monad.v 在 [Powerset_Prop] 上构建了单子，其单位为 #227 的单例变换，其读回 [Powerset_Monad_statement] 属于 [Powerset_Prop_Monad_statement]；Instance/SupLat.v 将单子的代数与完全半格识别。#750，即初始代数的问题，仍然未解决。
*)

Definition Powerset_Prop_Monad_statement : Type := @Monad Sets Powerset_Prop.

Definition Powerset_Prop_FAlg : Category := FAlg Powerset_Prop.

(* ------------------------------------------------------------------------ *)
(* * ** Non-vacuity for the truncated carrier / * ** 截断载体的非空性 *)

(*
 Truncation is the one step that could plausibly have destroyed the
 content, by collapsing distinct subsets together.  It does not, and the
 next two results say so rather than leaving it to be assumed.

 Singletons are still faithful, up to truncation: equivalent singletons
 give a squashed proof that the points are equivalent.  That is the
 analogue of [Powerset_singleton_faithful] above, with the conclusion
 squashed because on this carrier the hypothesis is. 

 --------
 截断是唯一一个可能会通过将不同的子集合并在一起来破坏内容的步骤。它并没有破坏内容，接下来的两个结果说明了这一点，而不是让人去假设。

 单元素集在截断后仍然是可信的：等价的单元素集给出了一个压缩的证明，证明这些点是等价的。这相当于上面的 [Powerset_singleton_faithful]，其结论由于在该承载体上假设已经成立而被压缩。
*)
Lemma Powerset_Prop_singleton_faithful@{o} {X : SetoidObject@{o o}}
  (a b : carrier X)
  (H : Powerset_Prop_singleton_pred@{o} a ≈ Powerset_Prop_singleton_pred@{o} b) :
  Powerset_squash@{o} (@equiv _ (is_setoid X) a b).
Proof.
  intros Q k.
  assert (Hba : Powerset_squash@{o} (@equiv _ (is_setoid X) b a))
    by exact (proj1 (H a) (Powerset_squash_intro@{o} (reflexivity a))).
  apply Hba; intro Hb; apply k; now symmetry.
Qed.

(*
 The two-element discrete setoid, universe-polymorphic.  This duplicates
 [fin_setoid_object] for exactly one reason, given in the section header:
 that one is pinned at [SetoidObject@{Set Set}], and [Powerset_Prop_truth]
 forces [Set < o]. 

 --------
 双元素离散集合，宇宙多态。这只出于标题部分给出的一个原因重复了 [fin_setoid_object]：那一个固定在 [SetoidObject@{Set Set}]，而 [Powerset_Prop_truth] 强制 [Set < o]。
*)
Definition Powerset_Prop_fin_object@{o} (n : nat) : SetoidObject@{o o} :=
  {| carrier   := Fin.t n
   ; is_setoid :=
       {| equiv        := @eq (Fin.t n)
        ; setoid_equiv :=
            {| Equivalence_Reflexive  := @eq_refl (Fin.t n)
             ; Equivalence_Symmetric  := @eq_sym (Fin.t n)
             ; Equivalence_Transitive := @eq_trans (Fin.t n) |} |} |}.

(*
 Concretely, over a two-element carrier: the truncated power set does not
 collapse.  [fin2_0_ne_1] is reused from the previous section — it is a
 statement about [Fin.t 2] alone and carries no universe of its own. 

 --------
 具体来说，在一个两元素的承载上：截断幂集不会坍缩。[fin2_0_ne_1] 是从上一节重用的——它是关于 [Fin.t 2] 的一个陈述，并且不包含它自己的宇宙。
*)
Lemma Powerset_Prop_singletons_distinct@{o} :
  Powerset_Prop_singleton_pred@{o} (X:=Powerset_Prop_fin_object@{o} 2) Fin.F1
    ≈ Powerset_Prop_singleton_pred@{o} (X:=Powerset_Prop_fin_object@{o} 2)
        (Fin.FS Fin.F1)
  → False.
Proof.
  intro H.
  exact (Powerset_Prop_singleton_faithful@{o} _ _ H False fin2_0_ne_1).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Relating the two carriers / ** 关联这两个载体 *)

(*
 Truncation is a map from the proof-relevant power set to the [Prop]-valued
 one, and it is natural.  The component sends a [Type@{o}]-valued subset
 [S] to [λ x, Powerset_squash (S x)]; that this respects [≈] at both levels
 is the whole of the proof. 

 --------
 截断是从证明相关幂集到 [Prop] 值的映射，并且它是自然的。该分量将一个 [Type@{o}] 值的子集 [S] 发送到 [λ x, Powerset_squash (S x)]；它在两个层面上尊重 [≈] 的事实就是整个证明。
*)
Definition Powerset_truncate_map@{o so} {X : SetoidObject@{o o}} :
  SetoidMorphism@{so so so} (Powerset_obj@{o so} X)
                            (Setoid_Lift@{o so} (Powerset_Prop_obj@{o} X)).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{so so so}
       (carrier (Powerset_obj@{o so} X)) (is_setoid (Powerset_obj@{o so} X))
       (carrier (Powerset_Prop_obj@{o} X))
       (Setoid_Lift_instance@{o so} (is_setoid (Powerset_Prop_obj@{o} X)))
       (fun S => _) _).
  - unshelve refine
      (@Build_SetoidMorphism@{o o o}
         (carrier X) (is_setoid X) Prop (is_setoid Powerset_Prop_truth@{o})
         (λ x, Powerset_squash@{o} (S x)) _).
    intros x x' Hxx'; split; intros H Q k; apply H; intro Hs; apply k.
    + exact (fst (@proper_morphism _ _ _ _ S x x' Hxx') Hs).
    + exact (snd (@proper_morphism _ _ _ _ S x x' Hxx') Hs).
  - intros S T HST x; split; intros H Q k; hnf in H; apply H; intro Hs; apply k.
    + exact (fst (HST x) Hs).
    + exact (snd (HST x) Hs).
Defined.

(*
 The codomain functor of that transformation is [Sets_Lift ◯ Powerset_Prop],
 assembled directly rather than through the library's [Compose].  The
 reason is a universe one, and it is about [Compose] rather than about
 either factor: its signature is

 Compose@{u u0 u1 u2 u3} :
 ∀ {C : Category@{u0 u3 u3}} {D : Category@{u1 u3 u3}}
 {E : Category@{u u3 u3}}, D ⟶ E → C ⟶ D → C ⟶ E

 so the three categories may differ in their OBJECT universe but share one
 hom/proof universe [u3].  Here the two categories have different hom
 universes — [Sets@{o so} : Category@{so o o}] and
 [Sets@{so sso} : Category@{sso so so}] — so [Compose] would require
 [o = so].  Only the packaging is affected: [Powerset_Prop_Lift_obj] and
 [Powerset_Prop_Lift_fmap] below check, by [reflexivity], that this functor
 IS the composite on objects and on morphisms. 

 --------
 该变换的余域函子是 [Sets_Lift ◯ Powerset_Prop]，直接组装，而不是通过库中的 [Compose]。原因是宇宙相关的，它关乎 [Compose]，而不是任一因子：其签名为

 Compose@{u u0 u1 u2 u3} :
 ∀ {C : Category@{u0 u3 u3}} {D : Category@{u1 u3 u3}}
 {E : Category@{u u3 u3}}, D ⟶ E → C ⟶ D → C ⟶ E

 因此，这三个范畴在对象宇宙上可能不同，但共享一个同态/证明宇宙 [u3]。这里两个范畴有不同的同态宇宙——[Sets@{o so} : Category@{so o o}] 和 [Sets@{so sso} : Category@{sso so so}]——所以 [Compose] 将需要 [o = so]。仅仅是包装受到影响：下方的 [Powerset_Prop_Lift_obj] 和 [Powerset_Prop_Lift_fmap] 通过 [reflexivity] 检查，该函子在对象和态射上都是复合。
*)
Definition Powerset_Prop_Lift@{o so sso} : @Functor Sets@{o so} Sets@{so sso}.
Proof.
  unshelve refine
    (@Build_Functor Sets@{o so} Sets@{so sso}
       (fun X => Setoid_Lift@{o so} (Powerset_Prop_obj@{o} X))
       (fun X Y f => @SetoidMorphism_Lift@{o so}
                       (Powerset_Prop_obj@{o} X) (Powerset_Prop_obj@{o} Y)
                       (Powerset_Prop_map@{o} f)) _ _ _).
  - intros X Y f g H S; exact (Powerset_Prop_map_respects@{o} f g H S).
  - intros X S; exact (@Powerset_Prop_map_id@{o} X S).
  - intros X Y Z f g S; exact (@Powerset_Prop_map_comp@{o} X Y Z f g S).
Defined.

(*
 Same-term equalities, closed by [reflexivity], on the
 Functor/Bifunctor.v precedent: [Powerset_Prop_Lift] is the lift of
 [Powerset_Prop], object-wise and morphism-wise. 

 --------
 由 [reflexivity] 封闭的同项等式，关于 Functor/Bifunctor.v 的前例：[Powerset_Prop_Lift] 是 [Powerset_Prop] 的提升，对象上和态射上均是如此。
*)
Lemma Powerset_Prop_Lift_obj@{o so sso} (X : SetoidObject@{o o}) :
  Powerset_Prop_Lift@{o so sso} X = Setoid_Lift@{o so} (Powerset_Prop@{o so} X).
Proof. reflexivity. Qed.

Lemma Powerset_Prop_Lift_fmap@{o so sso} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) :
  fmap[Powerset_Prop_Lift@{o so sso}] f
    = @SetoidMorphism_Lift@{o so} (Powerset_Prop_obj@{o} X)
        (Powerset_Prop_obj@{o} Y) (fmap[Powerset_Prop@{o so}] f).
Proof. reflexivity. Qed.

(*
 THE COMPARISON.  Truncating the proof-relevant power set commutes with
 taking direct images: squashing an image is the image of the squash.  One
 direction unwraps an inner squash into the ambient [Prop] goal, the other
 wraps a witness with [Powerset_squash_intro]; both stay inside [Prop]
 throughout, which is what makes the equivalence available at all. 

 --------
 比较。截断与证据相关的幂集与取直像是可交换的：压缩一个像等于像的压缩。一个方向将内部压缩解开到外部 [Prop] 目标中，另一个方向则用 [Powerset_squash_intro] 包装一个证据；两者在整个过程中都保持在 [Prop] 内，这正是使得等价性成为可能的原因。
*)
Definition Powerset_truncate@{o so sso} :
  @Transform Sets@{o so} Sets@{so sso}
    Powerset@{o so sso} Powerset_Prop_Lift@{o so sso}.
Proof.
  unshelve refine
    (@Build_Transform' Sets@{o so} Sets@{so sso}
       Powerset@{o so sso} Powerset_Prop_Lift@{o so sso}
       (fun X => @Powerset_truncate_map@{o so} X) _).
  intros X Y f S y; split; intros H Q k; hnf in H; apply H.
  - intros [x [Hx Hfx]]; hnf in Hx; apply Hx; intro Hs; apply k;
      exists x; split; [ exact Hs | exact Hfx ].
  - intros [x [Hx Hfx]]; apply k; exists x; split;
      [ exact (Powerset_squash_intro@{o} Hx) | exact Hfx ].
Defined.
