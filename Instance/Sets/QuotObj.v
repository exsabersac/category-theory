Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Subobject.Quotient.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Instance.Sets.Pushout.

Generalizable All Variables.

(*
   * * Quotient objects of a setoid: the witness half of Mac Lane §V.7
   Definition 3 

   --------
   * * 集合格的商对象：Mac Lane §V.7 的证据部分
   定义 3
*)

(*
 nLab:      https://ncatlab.org/nlab/show/quotient+object
 nLab:      https://ncatlab.org/nlab/show/quotient+set
 nLab:      https://ncatlab.org/nlab/show/coimage
 Wikipedia: https://en.wikipedia.org/wiki/Quotient_object

 Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
 §V.7, book p. 126 (PDF p. 135), Definition 3, is the source.  Dually to
 the subobjects of Definition 2, a quotient object of x is an
 equivalence class of epimorphisms OUT of x, ordered by factorization,
 and Mac Lane's whole point is that in a category where the epis are
 the onto maps these are the familiar quotients.  Theory/Subobject/
 Quotient.v carries the definition -- [QuotObj x] is [@SubObj (C^op) x]
 and nothing more -- and this file is the first half of the answer to
 "and where epis ARE onto?", at [Sets].  The [FinSet] and [Grp] halves
 are Instance/FinSet/QuotObj.v and Instance/Grp/QuotObj.v.

 WHAT IS DELIVERED.

 (1) The onto clause, in both directions and with nothing assumed.
 [Sets_quot_epi_surjective] says the epimorphism of a quotient object
 is a surjection and [Sets_quot_of_surjection] says every surjection
 presents a quotient object; both are Instance/Sets.v's
 [surjectivity_is_epic] read through the accessors of the interface
 stub, one leg apiece.  No stability or decidability
 hypothesis appears, and none is hidden: `≈` is [Type]-valued in this
 library, so the biconditional's backward leg RETURNS the preimage as
 data.  This is the point at which [Sets] and [Grp] part company --
 Instance/Grp/QuotObj.v has to take the double-negation stability of
 image membership as a hypothesis, and says so.

 (2) The element-level quotient as a quotient object.
 [SetsQuotient_QuotObj] packages Instance/Sets/Quotient.v's
 [SetsQuotient A R HR] -- the SAME CARRIER under a coarser `≈` -- with
 its projection.  The surjectivity witness is
 [Equivalence_Reflexive] and nothing else, the projection being the
 identity function.  The [SetoidCoarser] argument [HC] is carried
 explicitly and is not optional: the projection does not exist without
 it.

 (3) The COIMAGE, as an [ImageOf] in [Sets^op].  Read
 Theory/Subobject/Lattice.v's record at [C := Sets^op] and each
 field turns over: [im_sub] is a quotient object OF THE DOMAIN,
 [im_factor] is the map from that quotient to the codomain,
 [im_commutes] is the triangle, and [im_least] says the coimage is
 COARSER than every quotient through which f factors.  The coimage is
 the quotient by the kernel relation [sets_coimage_rel a b := f a ≈ f b],
 whose object-level twin is Instance/Sets/Pullback.v's [sets_ker]
 (the kernel pair).  [Sets_HasCoimages] is the class form at [Sets^op],
 registered as an [#[export] Instance] so that [HasImages (Sets^op)]
 resolves by class search (an audit found the first draft a plain
 [Definition], which resolution cannot see).
 One expectation was WRONG and is recorded rather than smoothed over:
 [im_least] is NOT [sets_quot_med]'s job.  That mediator maps OUT of a
 quotient; [im_least] needs a map INTO the coimage from a competing
 quotient's codomain, and since the coimage's carrier is the carrier of
 X such a map must CHOOSE a preimage.  The choice is free here because
 surjectivity is data, and it is well defined into the coimage (though
 not into X) because two preimages of `≈`-equal points have equal
 f-values, which is exactly equality in the coimage.

 (4) A worked binary MEET, at the stub's [quot_meet] -- which at [Sets]
 is the PUSHOUT of the two epis, Instance/Sets/Pushout.v supplying
 it.  The pair is the parity quotient of the discrete setoid on [nat]
 (Instance/Sets/Quotient.v, already in tree) and the residue-mod-3
 quotient defined here, and the answer is the TOTAL quotient
 (Instance/Sets/Quotient.v's [TotalRelT]):
 [Sets_quot_meet_parity_mod3].  The proof never touches
 the pushout apex.  Both sides are greatest lower bounds of the same
 two-element family, so Theory/Subobject/Lattice.v's
 [IsIntersection_unique] identifies them, and the only arithmetic is
 [Sets_meet_collapse]: a quotient coarser than both identifies m with
 m+3 (same residue) and m+3 with m+1 (same parity), hence consecutive
 naturals, hence everything.  Both invariant equations hold by
 [eq_refl] -- [Nat.even (S (S k)) = Nat.even k] by the stdlib
 fixpoint's own reduction, and [nat_tri (S (S (S k))) = nat_tri k]
 because [nat_tri] is written as a three-step fixpoint here for exactly
 that reason, in place of [Nat.modulo], which would have cost an
 arithmetic lemma.  [Sets_quot_meet_collapses] then reads the same fact
 off the apex itself, with no comparison isomorphism in sight.

 (5) The BOTTOM quotient object, and the measurement of its hypothesis.
 The stub's [quot_bot] asks for [Epic (one : X ~> 1)], and in [Sets]
 that is exactly inhabitedness of the carrier: [Sets_one_epic_of_inhabited]
 discharges it from a point in three lines with nothing assumed, so
 [Sets_quot_bot] is the coarsest quotient object X ↠ 1 of every
 inhabited setoid, and [Sets_one_not_epic_empty] refutes it at the empty
 setoid (the two constant maps [Sets_pick true]/[Sets_pick false] out of
 the singleton agree after ∅ → 1 for free and differ at [ttt]).  This
 is what makes the hypothesis object-dependent rather than rare, the
 claim Theory/Subobject/Quotient.v's header makes and cites here.

 STRENGTHS, and what they are NOT.  Everything about quotient objects
 here is stated at ≈, never at Leibniz equality: [QuotObj x] inherits
 [SubObj]'s setoid (Theory/Subobject.v) and has no antisymmetry, so
 [Sets_quot_meet_parity_mod3] is an equivalence of quotient objects and
 the same statement at `=` is REFUSED (measured: CONVERSION, "cannot
 unify quot_meet Sets_Q_parity Sets_Q_mod3 and Sets_Q_total").  Nothing
 in this file computes by [eq_refl]; the computing readbacks of this
 development are in Instance/FinSet/QuotObj.v, where the objects are
 natural numbers.

 MEASUREMENTS, each re-runnable.  33 constants
 (grep -E '^(def|prf|thm|ind|constr|proj|class|inst|meth|rec|corec|ax|
 defax) ' on the .glob), no [Program] anywhere so
 [strings … .vo | grep obligation] returns nothing, and all 33 report
 "Closed under the global context" under [Print Assumptions] -- the
 [Sets] layer is often a place where stdlib axioms enter (docs/
 AXIOMS.md), and here none does.  5 [Defined] and 7 [Qed] (grep -c on
 '^Defined\.' / '^Qed\.'; a first draft of this paragraph said 28
 constants, 3 [Defined] and 8 [Qed], figures stale by the time it was
 committed and corrected here); flipping each [Defined] to [Qed] in
 turn, exactly TWO are required to be transparent: [sets_coimage_med],
 whose underlying function the [change] in [sets_coimage_least] must
 see ("Error: Not convertible"), and [Sets_pick], whose morphism the
 [cbn]/[discriminate] in [Sets_one_not_epic_empty] must reduce ("Not a
 discriminable equality"); the other three recompile green as [Qed]
 and are kept [Defined] because [sub_le], `≈` on [QuotObj] and an
 [Epic] proof consumed by [quot_bot] are data.  The requirement
 closure is 75 files COUNTING THIS FILE (iterated over .Makefile.coq.d;
 74 before Structure/Initial.v joined it).  No name introduced here occurs
 anywhere else in the tree (swept over all .glob files with
 '^[a-z]+ [0-9:]+ [^ ]* NAME$', instrument-checked on [sub_le]; a first
 draft called the kernel relation [sets_ker] and the sweep found
 Instance/Sets/Pullback.v, hence [sets_coimage_rel]).

 UNIVERSES, measured with [Set Printing Universes. About …].  Every
 constant here is [@{o so}] with [o < so], the idiom of
 Instance/Powerset/Subobject.v, and binds its category as
 [Sets@{o so}], which Instance/Sets.v declares as
 [Category@{so o o}] -- hom level and proof level are the SAME
 universe, which is what [SubObj] demands.  That identification is
 INHERITED and is not introduced here: Theory/Subobject.v's record
 itself prints as [∀ {C : Category@{u u0 u0}}, …], as the header of
 Theory/Subobject/Lattice.v records, and [Sets] happens to satisfy it
 on the nose.  No constant here pins any universe to [Set].

 NOT DELIVERED.  No WORKED join: [Sets_quot_join] is delivered as the
 one-line transport of [quot_join] at [Sets_Cartesian] and
 [Sets_HasCoimages] (an earlier revision of this paragraph said the
 join needed "a product instance not assembled here", which an audit
 refuted -- the instance was Instance/Sets/Cartesian.v all along),
 but no pair of quotients has its join computed, unlike the meet.
 No lattice laws: commutativity, associativity,
 idempotence and absorption for [quot_meet] are not restated at [Sets],
 being transports of Theory/Subobject/Lattice.v and not facts about
 setoids.  No top quotient object.  The BOTTOM one IS delivered, at
 every inhabited setoid ([Sets_quot_bot], through
 [Sets_one_epic_of_inhabited]; [Sets_one_not_epic_empty] shows the
 hypothesis is exactly inhabitedness), and the total quotient of
 [NatDiscrete] is shown below every quotient of it directly
 ([Sets_Q_total_below]) -- an argument specific to an inhabited
 carrier for the same reason, the constant map it builds having to
 name an element.  No indexed meet.  No claim that the coimage agrees with
 Instance/Sets/Image.v's image: the two are related by the
 epi-mono factorization of [Sets] and nothing here states it.  No
 [eq_refl] readback of any construction.  No uniqueness of the
 coimage's mediating map ([sub_le_unique] dualized), which would need
 the epi of the competing quotient cancelled on the right and is not
 stated. 

 --------
 nLab:       https://ncatlab.org/nlab/show/quotient+object 
 nLab:       https://ncatlab.org/nlab/show/quotient+set 
 nLab:       https://ncatlab.org/nlab/show/coimage 
 Wikipedia:  https://en.wikipedia.org/wiki/Quotient_object 

 Mac Lane，《为工作数学家而写的范畴论》，第二版（GTM 5），
 §V.7，第126页（PDF第135页），定义3，是来源。相对于
 定义2的子对象，x 的商对象是 x 的外射（epimorphism）的等价类，通过因式分解排序，
 Mac Lane 的整个观点是，在一个外射都为满射的范畴中，这些就是熟悉的商对象。理论/子对象/
 Quotient.v 包含该定义——[QuotObj x] 是 [@SubObj (C^op) x]
 而没有其他内容——并且这个文件是对“当外射真的都是满射时？”这一问题的前半部分回答，位于 [Sets]。[FinSet] 和 [Grp] 的后半部分分别是 Instance/FinSet/QuotObj.v 和 Instance/Grp/QuotObj.v。

 所交付的内容。(1) 在两个方向上，且没有任何假设的满射子句。[Sets_quot_epi_surjective] 说商对象的上射是一个满射，而 [Sets_quot_of_surjection] 说每一个满射都可以表示一个商对象；两者都是 Instance/Sets.v 里的。[surjectivity_is_epic] 通过接口存根的访问器阅读，每次一条腿。没有出现稳定性或可判定性假设，也没有隐藏的：`≈` 在此库中是 [Type] 值的，所以双条件的反向分支将原像作为数据返回。这是 [Sets] 和 [Grp] 分道扬镳的点——Instance/Grp/QuotObj.v 必须把像成员资格的双重否定稳定性作为假设，并明确说明。(2) 元素级商作为商对象。 [SetsQuotient_QuotObj] 打包 Instance/Sets/Quotient.v 的 [SetsQuotient A R HR] -- 在更粗糙的 `≈` 下的相同载体 -- 及其投影。 满射性证明为 [Equivalence_Reflexive]，除此之外没有其他，投影为恒等函数。 [SetoidCoarser] 参数 [HC] 是显式携带的，并且不是可选的：没有它投影是不存在的。(3) COIMAGE，作为 [ImageOf] 在 [Sets^op] 中。阅读 Theory/Subobject/Lattice.v 在 [C := Sets^op] 的记录，每个字段解释如下：[im_sub] 是域的一个商对象，[im_factor] 是从该商到余域的映射，[im_commutes] 是三角图，[im_least] 表示余像比 f 可因式分解的每个商都更粗。余像是通过核关系 [sets_coimage_rel a b := f a ≈ f b] 的商，其对象级对应是 Instance/Sets/Pullback.v 的 [sets_ker]（核对）。[Sets_HasCoimages] 是在 [Sets^op] 的类形式，注册为 [#[export] 实例，以便 [HasImages (Sets^op)] 可以通过类搜索解析（审计发现初稿是一个普通 [Definition] ，解析无法识别）。有一个预期是错误的，并被记录而不是被忽略：[im_least] 并不是 [sets_quot_med] 的工作。该中介映射出一个商；[im_least] 需要从竞争商的余定义域映射到余像，并且由于余像的承载对象是 X 的承载对象，这样的映射必须选择一个原像。这里的选择是自由的，因为满射性是已知数据，并且它在余像中定义良好（尽管在 X 中不然），因为两个 `≈` 相等点的原像具有相等的 f 值，这正是余像中的相等性。(4) 一个已完成的二元 MEET，在存根的 [quot_meet] —— 在 [Sets] 处，它是两个 epi 的 PUSHOUT，Instance/Sets/Pushout.v 提供它。该对是 [nat] 上离散集合类的奇偶商集（Instance/Sets/Quotient.v，已在树中）和此处定义的模 3 余数商集的商对，答案是总商集（Instance/Sets/Quotient.v 的 [TotalRelT]）：[Sets_quot_meet_parity_mod3]。证明从未涉及推顶点。两边都是同一个二元族的最大下界，所以 Theory/Subobject/Lattice.v 的 [IsIntersection_unique] 将它们识别，并且唯一的算术是 [Sets_meet_collapse]：一个比两者都粗的商集将 m 与 m+3（相同余数）以及 m+3 与 m+1（相同奇偶性）识别，因此是连续自然数，因此识别所有元素。两个不变量方程成立，因为 [eq_refl] -- [Nat.even (S (S k)) = Nat.even k] 通过标准库不变点自身的化简成立，而 [nat_tri (S (S (S k))) = nat_tri k] 因为 [nat_tri] 在这里正是以三步不变点的形式写出，取代了 [Nat.modulo]，否则将需要一个算术引理。然后 [Sets_quot_meet_collapses] 直接从顶点读取同样的事实，没有看到比较同构。(5) 底部商对象及其假设的测量。   
 该存根的 [quot_bot] 请求 [Epic (one : X ~> 1)]，并且在 [Sets]  
 中这正是承载体的具有人性：[Sets_one_epic_of_inhabited]  
 从三条线中的一点将其释放出来，无需假设任何东西，所以  
 [Sets_quot_bot] 是每个具有人性等价类的最粗商对象 X ↠ 1，并且 [Sets_one_not_epic_empty] 在空等价类中反驳它（来自单元素的两个常量映射 [Sets_pick true] / [Sets_pick false] 在 ∅ → 1 后自动一致，并在 [ttt] 不同）。  
 这正是使假设依赖于对象而非稀有的原因，Theory/Subobject/Quotient.v 文件头部所提出的主张，并在此引用。优势，以及它们不是的东西。关于商对象的所有内容在这里都是在 ≈ 下陈述的，从不在 Leibniz 等式下陈述：[QuotObj x] 继承了 [SubObj] 的集合等价体（Theory/Subobject.v），并且没有反对称性，因此 [Sets_quot_meet_parity_mod3] 是商对象的一个等价，而在 `=` 处的相同陈述被拒绝（测量：转换，"无法统一 quot_meet Sets_Q_parity Sets_Q_mod3 和 Sets_Q_total"）。本文件中没有任何内容通过 [eq_refl] 进行计算；该开发的计算回显在 Instance/FinSet/QuotObj.v 中，其中对象是自然数。测量，每个都可以重新运行。33 个常量（在 .glob 上使用 grep -E '^(def|prf|thm|ind|constr|proj|class|inst|meth|rec|corec|ax|defax) '），没有任何 [Program]，所以 [strings … .vo | grep obligation] 返回空，并且所有 33 个在 [Print Assumptions] 下都报告“在全局上下文下封闭”——[Sets] 层通常是 stdlib 公理进入的地方（docs/AXIOMS.md），而这里没有任何进入。5 [Defined] 和 7 [Qed]（在 '^Defined\.' / '^Qed\.' 上使用 grep -c；本段的初稿说 28 个常量，3 [Defined] 和 8 [Qed]，数字在提交时已经过时并在此处更正）；依次将每个 [Defined] 翻转为 [Qed]，恰需两个是透明的：[sets_coimage_med]，其底层函数 [change] 在 [sets_coimage_least] 中必须看到（"错误：不可转换"），以及 [Sets_pick]，其同态映射 [cbn] / [discriminate] 在 [Sets_one_not_epic_empty] 中必须规约（"不是可区分的等式"）；其他三个作为 [Qed] 重新编译为绿色，并保持 [Defined]，因为 [sub_le]、`≈` 在 [QuotObj] 上以及 [Epic] 的证明被 [quot_bot] 消耗是数据。需求关闭包含75个文件，包括此文件（在 .Makefile.coq.d 上迭代；在 Structure/Initial.v 加入它之前有74个文件）。这里引入的任何名称在树的其他地方都不存在（在所有 .glob 文件上清扫过，使用 '^ [a-z] +  [0-9:] +  [^ ] * NAME$'，在 [sub_le] 上进行了工具检查；一个最初的草稿将内核关系称为 [sets_ker]，清扫发现了 Instance/Sets/Pullback.v，因此 [sets_coimage_rel]）。宇宙，用 [Set Printing Universes. About …] 测量。这里的每个常量都是 [@{o so}]，带有 [o < so]，Instance/Powerset/Subobject.v 的习语，并将其类别绑定为 [Sets@{o so}]，而 Instance/Sets.v 将其声明为 [Category@{so o o}] —— 同态级别和证明级别是相同的宇宙，这正是 [SubObj] 所要求的。这个识别是继承的，并不是在这里引入的：Theory/Subobject.v 的记录本身显示为 [∀ {C : Category@{u u0 u0}}, …]，作为 Theory/Subobject/Lattice.v 记录的标题，并且 [Sets] 恰好完全符合它。这里没有常量将任何宇宙固定为 [Set]。未交付。没有工作的连接：[Sets_quot_join] 作为 [quot_join] 在 [Sets_Cartesian] 和 [Sets_HasCoimages] 的单行传输交付（该段落的早期版本说该连接需要“一个未在此组装的产品实例”，但审计否定了——该实例一直是 Instance/Sets/Cartesian.v），但没有任何商的配对计算其连接，与交不同。没有格律：[quot_meet] 的交换律、结合律、幂等律和吸收律在 [Sets] 未重新陈述，它们是 Theory/Subobject/Lattice.v 的传输，而非关于集代数的事实。没有顶商对象。最下面的那个已经在每个有元素的集合（[Sets_quot_bot]，通过[Sets_one_epic_of_inhabited]；[Sets_one_not_epic_empty]显示假设正是其可居性）上实现，并且[NatDiscrete]的总商在其每个商（[Sets_Q_total_below]）之下直接显示——这是针对同一有元素承载体的特定论证，原因相同，它构建的常数映射必须命名一个元素。没有索引交集。没有声称余像与Instance/Sets/Image.v的像一致：两者通过[Sets]的反向-单态分解相关联，这里没有说明。没有对任何构造的[eq_refl]回读。没有余像居中映射的唯一性（[sub_le_unique]对偶化），这需要右侧竞争商的满射被抵消，但这里没有说明。
*)

Section SetsQuotObj.

Universe o so.
Constraint o < so.

(* * ** Mac Lane's "where epis are onto" clause, both ways / * ** 马克·莱恩的“当epis是满射时”的条款，双向 *)

(*
 The epimorphism of a quotient object of [Sets] is a surjection.  This
 is [Instance/Sets.v]'s [epic_implies_surjective] -- the backward
 leg of [surjectivity_is_epic] -- applied to the [Epic] the
 accessor [quot_is_epic] reads off the [Monic] in [Sets^op].  The
 preimage is DATA: `≈` is [Type]-valued, so [∃] is [sigT] and `1 of
 this is an honest element of the carrier. 

 --------
 [Sets] 的商对象的上同态是一个满射。这是 [Instance/Sets.v] 的 [epic_implies_surjective] —— [surjectivity_is_epic] 的反向部分 —— 应用于 [Epic]，访问器 [quot_is_epic] 读取 [Sets^op] 中的 [Monic]。原像是数据：`≈` 是 [Type] 值的，所以 [∃] 是 [sigT]，并且其中的 1 是载体的一个真实元素。
*)
Definition Sets_quot_epi_surjective {X : SetoidObject@{o o}}
  (q : @QuotObj Sets@{o so} X) :
  ∀ b : carrier (quot_cod q), ∃ a : carrier X, quot_epi q a ≈ b :=
  fun b => epic_implies_surjective (quot_epi q) (quot_is_epic q) b.

(*
 ... and conversely every surjection of setoids presents a quotient
 object, by the forward leg and [mk_quot]. 

 --------
 ... 相反，每个集合族的满射都呈现一个商对象，通过正向部分和 [mk_quot]。
*)
Definition Sets_quot_of_surjection {X B : SetoidObject@{o o}}
  (h : X ~{Sets@{o so}}~> B)
  (Hs : ∀ b : carrier B, ∃ a : carrier X, h a ≈ b) :
  @QuotObj Sets@{o so} X :=
  mk_quot h (surjective_implies_epic h Hs).

(*
   * ** The quotient of a setoid by an equivalence relation, as a
   quotient object 

   --------
   * ** 由等价关系对集合格取商，作为商对象
*)

(*
 [Instance/Sets/Quotient.v]'s [SetsQuotient A R HR] is A with a
 coarser `≈`; its projection is the IDENTITY FUNCTION, so it is
 surjective with the element itself as preimage and the surjectivity
 witness is [Equivalence_Reflexive] and nothing more.  [HC] is not
 decoration: the projection does not exist without it, its
 respectfulness clause being convertible with [SetoidCoarser R]
 (Instance/Sets/Quotient.v). 

 --------
 [Instance/Sets/Quotient.v] 的 [SetsQuotient A R HR] 是带有更粗糙 `≈` 的 A；它的投影是恒等函数，因此它是满射的，其原像是元素本身，满射性的证据是 [Equivalence_Reflexive]，仅此而已。[HC] 不是装饰：没有它投影无法存在，其尊重性条款可以与 [SetoidCoarser R] (Instance/Sets/Quotient.v) 相互转换。
*)
Definition SetsQuotient_QuotObj (A : SetoidObject@{o o})
  (R : crelation (carrier A)) (HR : Equivalence R) (HC : SetoidCoarser R) :
  @QuotObj Sets@{o so} A :=
  Sets_quot_of_surjection (sets_quot_proj A R HR HC)
    (fun b => (b; @Equivalence_Reflexive _ R HR b)).

(** ** The coimage of a setoid map / ** 集合范畴映射的余像 *)

Section Coimage.

Context {X Y : SetoidObject@{o o}}.
Context (f : X ~{Sets@{o so}}~> Y).

(*
 The kernel relation of f, as a coarsening of X's own `≈`.  The
 OBJECT-level counterpart is Instance/Sets/Pullback.v's [sets_ker],
 the kernel pair; this is the same information as a relation on the
 carrier, which is what Instance/Sets/Quotient.v's quotient consumes. 

 --------
 f 的核关系，作为 X 自身 `≈` 的一种粗化。
 对象层面的对应是 Instance/Sets/Pullback.v 的 [sets_ker]，核对；这与在载体上的关系是相同的信息，这正是 Instance/Sets/Quotient.v 的商所使用的。
*)
Definition sets_coimage_rel : crelation (carrier X) := fun a b => f a ≈ f b.

Lemma sets_coimage_rel_Equivalence : Equivalence sets_coimage_rel.
Proof.
  constructor; unfold sets_coimage_rel.
  - intro a; reflexivity.
  - intros a b H; now symmetry.
  - intros a b c H1 H2; now transitivity (f b).
Qed.

(* Coarser than `≈` because f is a setoid map: this IS [proper_morphism]. / 比 `≈` 更粗，因为 f 是一个集合同态映射：这就是 [proper_morphism]。 *)
Definition sets_coimage_rel_coarser : SetoidCoarser sets_coimage_rel :=
  fun a b H => proper_morphism f a b H.

Definition Sets_coimage : @QuotObj Sets@{o so} X :=
  SetsQuotient_QuotObj X sets_coimage_rel sets_coimage_rel_Equivalence
    sets_coimage_rel_coarser.

(*
 f itself respects its own kernel relation, by the IDENTITY
 implication, so the descended map is [sets_quot_med] at that witness. 

 --------
 f 本身通过恒等关系尊重其自身的核关系，因此在该见证下，下降映射是 [sets_quot_med]。
*)
Definition sets_coimage_resp : RespMap sets_coimage_rel Y :=
  existT (SetsRespects sets_coimage_rel Y) f
    (fun a b (H : sets_coimage_rel a b) => H).

Definition sets_coimage_factor :
  Y ~{Sets@{o so}^op}~> quot_cod Sets_coimage :=
  sets_quot_med sets_coimage_rel sets_coimage_rel_Equivalence
    sets_coimage_resp.

(*
 The triangle, read in [Sets^op]: composition there is composition in
 [Sets] with the arguments swapped, so this is
 [sets_coimage_factor ∘ quot_epi Sets_coimage ≈ f] and the projection
 being the identity function leaves nothing to compute. 

 --------
 三角形，在 [Sets^op] 中读取：组合在那里存在组合，在 [Sets] 中参数交换，因此这是 [sets_coimage_factor ∘ quot_epi Sets_coimage ≈ f]，而投影作为恒等函数不需要计算任何内容。
*)
Lemma sets_coimage_commutes :
  sub_mono Sets_coimage ∘[Sets@{o so}^op] sets_coimage_factor ≈ f.
Proof. intro a; simpl; reflexivity. Qed.

(*
 Minimality needs a map OUT of a competing quotient INTO the coimage,
 whose carrier is the carrier of X -- so it has to choose a preimage.
 [sets_quot_med] is the wrong donor here: it maps out of the quotient,
 not into it.  Choosing is free, the preimage being data. 

 --------
 极小性需要一个从竞争商映射到余像的映射，其载体是 X 的载体——所以它必须选择一个原像。[sets_quot_med] 是这里错误的提供者：它是从商映射出去的，而不是映射进去的。选择是自由的，原像是数据。
*)
Definition sets_coimage_pick (w : @QuotObj Sets@{o so} X)
  (p : carrier (quot_cod w)) : carrier X :=
  `1 (Sets_quot_epi_surjective w p).

Lemma sets_coimage_pick_eq (w : @QuotObj Sets@{o so} X)
  (p : carrier (quot_cod w)) :
  quot_epi w (sets_coimage_pick w p) ≈ p.
Proof. exact (`2 (Sets_quot_epi_surjective w p)). Qed.

(* The choice is well defined INTO THE COIMAGE, though not into X: two preimages of `≈`-equal points have the same value under f, which is exactly equality in the coimage. / 该选择在共像中定义良好，尽管在 X 中不是：`≈` 的两个前像是相等的点，它们在 f 下具有相同的值，这正是共像中的相等。 *)
Definition sets_coimage_med (w : @QuotObj Sets@{o so} X)
  (g : Y ~{Sets@{o so}^op}~> quot_cod w)
  (Hg : sub_mono w ∘[Sets@{o so}^op] g ≈ f) :
  quot_cod Sets_coimage ~{Sets@{o so}^op}~> quot_cod w.
Proof.
  unshelve refine {| morphism := sets_coimage_pick w |}.
  intros p q Hpq.
  change (f (sets_coimage_pick w p) ≈ f (sets_coimage_pick w q)).
  transitivity (g (quot_epi w (sets_coimage_pick w p))).
  - symmetry; exact (Hg _).
  - transitivity (g (quot_epi w (sets_coimage_pick w q))).
    + apply proper_morphism.
      rewrite !sets_coimage_pick_eq; exact Hpq.
    + exact (Hg _).
Defined.

Lemma sets_coimage_least (w : @QuotObj Sets@{o so} X)
  (g : Y ~{Sets@{o so}^op}~> quot_cod w)
  (Hg : sub_mono w ∘[Sets@{o so}^op] g ≈ f) :
  @sub_le (Sets@{o so}^op) X Sets_coimage w.
Proof.
  exists (sets_coimage_med w g Hg).
  intro a.
  change (f (sets_coimage_pick w (quot_epi w a)) ≈ f a).
  unfold sets_coimage_pick.
  transitivity
    (g (quot_epi w (`1 (Sets_quot_epi_surjective w (quot_epi w a))))).
  - symmetry; exact (Hg _).
  - transitivity (g (quot_epi w a)).
    + apply proper_morphism.
      exact (`2 (Sets_quot_epi_surjective w (quot_epi w a))).
    + exact (Hg a).
Qed.

(*
 Theory/Subobject/Lattice.v's [ImageOf], instantiated at [Sets^op]:
 [im_sub] is a quotient object of the DOMAIN, [im_factor] the map from
 the quotient to the codomain, [im_commutes] the triangle, and
 [im_least] says the coimage is BELOW (that is, coarser than) every
 quotient through which f factors. 

 --------
 Theory/Subobject/Lattice.v 的 [ImageOf]，在 [Sets^op] 处实例化：
 [im_sub] 是 DOMAIN 的商对象，[im_factor] 是从商到上域的映射，[im_commutes] 是三角形，而
 [im_least] 表示余像位于（即比） f 可分解的每个商之下（即比它们更粗）。
*)
Definition Sets_CoimageOf : @ImageOf (Sets@{o so}^op) Y X f := {|
  im_sub := Sets_coimage;
  im_factor := sets_coimage_factor;
  im_commutes := sets_coimage_commutes;
  im_least := fun w g Hg => sets_coimage_least w g Hg
|}.

End Coimage.

(*
 The class form.  The anonymous record literal [{| image_of := … |}] is
 REFUSED here -- it elaborates the field against [C := Sets] and reports
 "has type @ImageOf Sets^op X Y f while it is expected to have type
 @ImageOf Sets Y X f" -- so the constructor is named and its category
 argument given explicitly. 

 --------
 类的形式。这里拒绝了匿名记录字面量 [{| image_of := … |}] —— 它对 [C := Sets] 展开字段并报告 “具有类型 @ImageOf Sets^op X Y f，而期望的类型是 @ImageOf Sets Y X f” —— 因此构造函数被命名，并且它的类别参数被显式给出。
*)
#[export] Instance Sets_HasCoimages : @HasImages (Sets@{o so}^op) :=
  @Build_HasImages (Sets@{o so}^op) (fun Y X f => @Sets_CoimageOf X Y f).

(*
 The JOIN of two quotient objects at Sets, by transport and nothing
 else: Theory/Subobject/Quotient.v's [quot_join] wants a [Cartesian]
 structure on the category -- Instance/Sets/Cartesian.v's
 [Sets_Cartesian], which IS a [@Cocartesian (Sets^op)] on the nose
 (Structure/Cocartesian.v makes [Cocartesian C] notation for
 [@Cartesian (C^op)], and [Sets^op^op] is [Sets] by reflexivity) -- and
 the coimages just registered.  The join is the coimage of the pairing
 of the two epis into the product of their codomains.  An earlier
 revision of this file said the join "needs a product instance not
 assembled here"; an audit refuted that by compiling this one line, so
 it is landed rather than left as a false obstruction.  Its least-
 upper-bound property and the lattice laws are [quot_join_is_lub],
 [quot_join_comm] and their siblings, read at [Sets]; none is restated
 here. 

 --------
 在集合（Sets）中通过传输和其他操作得到的两个商对象的 JOIN：Theory/Subobject/Quotient.v 的 [quot_join] 想要在该范畴上有一个 [Cartesian] 结构——Instance/Sets/Cartesian.v 的 [Sets_Cartesian] ，这在本质上是一个 [@Cocartesian (Sets^op)] 结构（Structure/Cocartesian.v 为 [@Cartesian (C^op)] 制作了 [Cocartesian C] 符号，且 [Sets^op^op] 通过自反性是 [Sets]）——以及刚登记的余像。此 join 是这两个满射映入它们余域积的配对的余像。该文件的早期版本曾说 join“需要一个此处未组装的积实例”；一次审查通过编译这一行否定了这个说法，因此它是已落实的，而非留下的虚假障碍。它的最上界性质和格律是 [quot_join_is_lub]、[quot_join_comm] 及其相关内容，可在 [Sets] 查看；此处不再重复。
*)
Definition Sets_quot_join {X : SetoidObject@{o o}}
  (q r : @QuotObj Sets@{o so} X) : @QuotObj Sets@{o so} X :=
  quot_join q r.

(* * ** A worked meet: parity ∧ residue-mod-3 on the naturals / * ** 一个已完成的集合：自然数上的奇偶性 ∧ 模3余数 *)

(*
 The residue mod 3, by a three-step fixpoint rather than by [Nat.modulo],
 so that [nat_tri (S (S (S m))) = nat_tri m] holds by [eq_refl] and the
 collapse argument below needs no arithmetic lemma.  Its parity
 counterpart, [Nat.even (S (S m)) = Nat.even m], holds by [eq_refl] for
 the same reason. 

 --------
 模 3 的余数，通过三步不动点而不是通过 [Nat.modulo]，因此 [nat_tri (S (S (S m))) = nat_tri m] 由 [eq_refl] 保持，并且下面的塌缩论证不需要算术引理。它的奇偶对应，[Nat.even (S (S m)) = Nat.even m]，出于同样的原因由 [eq_refl] 保持。
*)
Fixpoint nat_tri (n : nat) : nat :=
  match n with
  | O => 0
  | S O => 1
  | S (S O) => 2
  | S (S (S m)) => nat_tri m
  end.

Definition nat_mod3 : crelation (carrier NatDiscrete@{o}) :=
  fun m n => nat_tri m = nat_tri n.

Lemma nat_mod3_Equivalence : Equivalence nat_mod3.
Proof.
  constructor.
  - intro m; reflexivity.
  - intros m n H; now symmetry.
  - intros m n k H1 H2; now transitivity (nat_tri n).
Qed.

Definition nat_mod3_coarser : SetoidCoarser nat_mod3 :=
  fun m n (H : m = n) => f_equal nat_tri H.

(*
 The three quotient objects of the discrete setoid on [nat]:
 Instance/Sets/Quotient.v's parity, the residue mod 3, and that
 file's total relation. 

 --------
 离散集合等价类 [nat] 的三个商对象：Instance/Sets/Quotient.v 中的奇偶性、模 3 的余数，以及该文件的全关系。
*)
Definition Sets_Q_parity : @QuotObj Sets@{o so} NatDiscrete@{o} :=
  SetsQuotient_QuotObj NatDiscrete@{o} nat_parity nat_parity_Equivalence
    nat_parity_coarser.

Definition Sets_Q_mod3 : @QuotObj Sets@{o so} NatDiscrete@{o} :=
  SetsQuotient_QuotObj NatDiscrete@{o} nat_mod3 nat_mod3_Equivalence
    nat_mod3_coarser.

Definition Sets_Q_total : @QuotObj Sets@{o so} NatDiscrete@{o} :=
  SetsQuotient_QuotObj NatDiscrete@{o} (TotalRelT NatDiscrete@{o})
    (TotalRelT_Equivalence NatDiscrete@{o})
    (TotalRelT_coarser NatDiscrete@{o}).

(*
 The total quotient is the BOTTOM of the factorization order on
 quotient objects of [NatDiscrete]: it factors through every quotient
 (every quotient has it below), by the constant map out of that
 quotient's codomain, whose respectfulness is [ttt].  An earlier
 revision of this comment said "every quotient factors through it",
 the reverse direction; the statement below was always the right one. 

 --------
 总商是 [NatDiscrete] 的商对象分解顺序的底部：它通过每个商（每个商在其之下），由该商的陪域中的常值映射，其尊重性是 [ttt]。此评论的早期版本说“每个商都通过它分解”，这是相反的方向；下面的陈述一直是正确的。
*)
Lemma Sets_Q_total_below (w : @QuotObj Sets@{o so} NatDiscrete@{o}) :
  @sub_le (Sets@{o so}^op) NatDiscrete@{o} Sets_Q_total w.
Proof.
  unshelve eexists.
  - unshelve refine {| morphism := fun _ : carrier (quot_cod w) => 0%nat |}.
    intros p q Hpq; exact ttt.
  - intro a; exact ttt.
Defined.

(*
 The arithmetic of the meet, done once: a quotient coarser than both
 parity and residue-mod-3 identifies EVERY pair of naturals.  m and
 m+3 agree mod 3, m+3 and m+1 agree in parity, so consecutive
 naturals are identified and induction finishes.  Both steps are
 [eq_refl] at the two invariants. 

 --------
 完成一次交的算术：一个比奇偶性和模3余数都粗的商识别每一对自然数。m 和 m+3 在模3下相同，m+3 和 m+1 的奇偶性相同，因此连续自然数被识别，归纳完成。两个步骤在两个不变量上都是 [eq_refl]。
*)
Lemma Sets_meet_collapse (v : @QuotObj Sets@{o so} NatDiscrete@{o})
  (H1 : @sub_le (Sets@{o so}^op) NatDiscrete@{o} v Sets_Q_parity)
  (H2 : @sub_le (Sets@{o so}^op) NatDiscrete@{o} v Sets_Q_mod3)
  (m n : nat) : quot_epi v m ≈ quot_epi v n.
Proof.
  destruct H1 as [k1 Hk1].
  destruct H2 as [k2 Hk2].
  assert (step : ∀ p : nat, quot_epi v p ≈ quot_epi v (S p)).
  { intro p.
    transitivity (k2 p); [ symmetry; exact (Hk2 p) | ].
    transitivity (k2 (S (S (S p)))).
    { exact (proper_morphism k2 p (S (S (S p)))
               (eq_refl : nat_tri p = nat_tri p)). }
    transitivity (quot_epi v (S (S (S p)))); [ exact (Hk2 _) | ].
    transitivity (k1 (S (S (S p)))); [ symmetry; exact (Hk1 _) | ].
    transitivity (k1 (S p)).
    { exact (proper_morphism k1 (S (S (S p))) (S p)
               (eq_refl : Nat.even (S p) = Nat.even (S p))). }
    exact (Hk1 _). }
  assert (zero : ∀ p : nat, quot_epi v 0%nat ≈ quot_epi v p).
  { induction p as [| p IH]; [ reflexivity | now rewrite IH ]. }
  now rewrite <- (zero m), <- (zero n).
Qed.

Lemma Sets_Q_total_IsMeet :
  @IsMeet (Sets@{o so}^op) NatDiscrete@{o} Sets_Q_parity Sets_Q_mod3
    Sets_Q_total.
Proof.
  constructor.
  - intro b; destruct b; exact (Sets_Q_total_below _).
  - intros v Hv.
    unshelve eexists.
    + unshelve refine
        {| morphism :=
             fun p : carrier (quot_cod Sets_Q_total) => quot_epi v p |}.
      intros p q _.
      exact (Sets_meet_collapse v (Hv true) (Hv false) p q).
    + intro a; reflexivity.
Defined.

(*
 The stub's [quot_meet] at [Sets], evaluated.  Both sides are greatest
 lower bounds of the same two-element family, so they agree -- at ≈ on
 [QuotObj], which is the strongest relation available here ([QuotObj]
 has no Leibniz antisymmetry, exactly as [SubObj] has none). 

 --------
 存根在 [Sets] 处的 [quot_meet] 已评估。双方都是同一两元素族的最大下界，因此它们一致——约在 [QuotObj] 处，这是这里可用的最强关系（[QuotObj] 没有莱布尼茨反对称性，正如 [SubObj] 也没有一样）。
*)
Theorem Sets_quot_meet_parity_mod3 :
  @quot_meet Sets@{o so} Sets_HasPushouts NatDiscrete@{o}
    Sets_Q_parity Sets_Q_mod3 ≈ Sets_Q_total.
Proof.
  apply (@IsIntersection_unique (Sets@{o so}^op) NatDiscrete@{o} bool
           (sub_pair Sets_Q_parity Sets_Q_mod3)).
  - exact (@sub_meet_IsMeet (Sets@{o so}^op)
             (HasPullbacks_op_of_HasPushouts Sets_HasPushouts)
             NatDiscrete@{o} Sets_Q_parity Sets_Q_mod3).
  - exact Sets_Q_total_IsMeet.
Qed.

(*
 The same fact read on elements of the pushout apex itself, with no
 comparison isomorphism in sight: in the pushout of the two
 projections every natural is identified with every other. 

 --------
 相同的事实体现在推顶点本身的元素上，没有任何比较同构可见：在两个投影的推积中，每个自然变换都与其他自然变换相同。
*)
Corollary Sets_quot_meet_collapses (m n : nat) :
  quot_epi (@quot_meet Sets@{o so} Sets_HasPushouts NatDiscrete@{o}
              Sets_Q_parity Sets_Q_mod3) m
    ≈ quot_epi (@quot_meet Sets@{o so} Sets_HasPushouts NatDiscrete@{o}
                  Sets_Q_parity Sets_Q_mod3) n.
Proof.
  exact (Sets_meet_collapse _ (sub_meet_le_l _ _) (sub_meet_le_r _ _) m n).
Qed.

(* * ** The bottom quotient object: [Epic one] is inhabitedness / * ** 底商对象：[Epic one] 是有栖性 *)

(*
 Theory/Subobject/Quotient.v's [quot_bot] is conditional on
 [Epic (one : X ~> 1)].  In [Sets] that hypothesis is EXACTLY
 inhabitedness of the carrier, both ways.  Given a point [x0], two maps
 out of the singleton that agree after [one] agree at their only
 argument, because [one x0] IS that argument -- three lines and
 nothing assumed.  At the empty setoid the two constant maps 1 → bool
 agree after ∅ → 1 for free (there is nothing to check) and differ at
 [ttt], so [one] is not epic there.  Hence the coarsest quotient
 object, X ↠ 1, exists at every inhabited setoid and the theory's
 hypothesis is not a gap at [Sets]; it is object-dependent, and this
 pair of constants is the measurement. 

 --------
 Theory/Subobject/Quotient.v 的 [quot_bot] 依赖于 [Epic (one : X ~> 1)]。在 [Sets] 中，该假设恰好是承载类型的存在性，双向都成立。给定一个点 [x0]，从单元素集合到它的两个映射在 [one] 之后一致，则在它们的唯一参数上也一致，因为 [one x0] 就是那个参数 —— 三行代码且没有假设。在空集合效应下，两个从 1 到 bool 的常数映射在 ∅ → 1 之后天然一致（因为没有什么需要检查的）并且在 [ttt] 上不同，因此 [one] 在那里不是幂态(epic)。因此，在每个非空集合效应上，最粗的商对象 X ↠ 1 都存在，并且理论假设在 [Sets] 上不是一个缺口；它依赖于对象，这对常数映射就是测量。
*)
Definition Sets_one_epic_of_inhabited {X : SetoidObject@{o o}}
  (x0 : carrier X) : Epic (@one Sets@{o so} Sets_Terminal X).
Proof.
  constructor; intros Z g1 g2 H u.
  destruct u.
  exact (H x0).
Defined.

Definition Sets_quot_bot {X : SetoidObject@{o o}} (x0 : carrier X) :
  @QuotObj Sets@{o so} X :=
  @quot_bot Sets@{o so} Sets_Terminal X (Sets_one_epic_of_inhabited x0).

(*
 The two constant maps 1 → bool, without [Program] (this file has no
 obligations and the measurements below say so). 

 --------
 两个恒定映射 1 → bool，没有 [Program]（此文件没有任何义务，下面的测量结果也说明了这一点）。
*)
Definition Sets_pick (b : bool) :
  @terminal_obj Sets@{o so} Sets_Terminal ~{Sets@{o so}}~>
    bool_setoid_object@{o o}.
Proof.
  unshelve refine {| morphism := fun _ => b |}.
  proper.
Defined.

Lemma Sets_one_not_epic_empty :
  Epic (@one Sets@{o so} Sets_Terminal
          (@initial_obj Sets@{o so} Sets_Initial)) → False.
Proof.
  intros [He].
  assert (H : Sets_pick true
                ∘ @one Sets@{o so} Sets_Terminal
                    (@initial_obj Sets@{o so} Sets_Initial)
              ≈ Sets_pick false
                ∘ @one Sets@{o so} Sets_Terminal
                    (@initial_obj Sets@{o so} Sets_Initial))
    by (intro u; contradiction).
  pose proof (He _ _ _ H ttt) as E.
  cbn in E.
  discriminate E.
Qed.

End SetsQuotObj.
