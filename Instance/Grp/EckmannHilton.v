Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Heunen_Vicary.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Structure.Monoid.
Require Import Category.Structure.Group.
Require Import Category.Theory.EckmannHilton.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Epi.

Generalizable All Variables.

(*
 Every statement below mentions the group [G] and, in the first half,
 the group-object structure [GO]; but several of them -- [AbelianGrp G] in
 particular -- do not mention [GO] in their STATEMENT while consuming it
 in the PROOF.  Lib.v sets [Default Proof Using “Type”], which keeps only
 the section variables occurring in the statement, so the section
 hypotheses must be requested explicitly.  This is exactly the discipline
 Theory/EckmannHilton.v adopts, and for the same reason. 

 --------
 下面的每个陈述都提到了群体 [G]，并且在前半部分提到了群体-对象结构 [GO]；但是其中几个——特别是 [AbelianGrp G]——在其陈述中并未提到 [GO]，却在证明中使用了它。Lib.v 设置了 [Default Proof Using “Type”]，该设置仅保留出现在陈述中的部分变量，因此必须显式请求部分假设。这正是 Theory/EckmannHilton.v 采用的规范，原因也是相同的。
*)
Local Set Default Proof Using "All".

(* * * Group objects in Grp are abelian groups / * * Grp中的对象是阿贝尔群 *)

(*
 Book: Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 Springer GTM 5, 1998, Section III.6 (“Groups in Categories”),
 Exercise 4, printed p. 76
 Paper: Eckmann, Hilton, “Structure maps in group theory”, Fundamenta
 Mathematicae 50, 1961, Theorem 1.12
 nLab:  https://ncatlab.org/nlab/show/Eckmann-Hilton+argument
 nLab:  https://ncatlab.org/nlab/show/group+object

 Mac Lane's Exercise 4 has two halves.

 (a) An abelian group's multiplication, unit and inversion are themselves
 group homomorphisms, so an abelian group assembles into a group
 object in Grp.

 (b) Conversely, every group object in Grp arises that way: the second
 multiplication agrees with the first, and the first is commutative.

 Half (b) is the Eckmann-Hilton argument.  This file CONSUMES
 Theory/EckmannHilton.v rather than re-deriving it -- it is that file's
 FOURTH consumer, after Structure/Semiadditive.v, Instance/Top/LoopSpace.v
 and Theory/Centre.v (measured by [Require], not by name: a grep for the
 token [EckmannHilton] returns EIGHT files -- Theory/EckmannHilton.v
 itself, the three consumers above, this file, and three that mention it
 in prose only (Instance/Grp/Quotient.v,
 Instance/Sets/Quotient/Partition.v and Structure/Bicartesian/Matrix.v);
 the looser token [Eckmann] returns TWENTY.  An earlier draft said seven
 and nineteen, silently dropping the donor from each; an audit corrected
 both, and the numbers quoted here are what the stated greps actually
 print). 

 --------
 书籍：Mac Lane，《为工作数学家准备的范畴》，第2版，Springer GTM 5，1998，第III.6节（“范畴中的群”），练习4，第76页印刷版
 论文：Eckmann, Hilton，《群论中的结构映射》，Fundamenta Mathematicae 50, 1961，第1.12定理
 nLab：https://ncatlab.org/nlab/show/Eckmann-Hilton+argument
 nLab：https://ncatlab.org/nlab/show/group+object

 Mac Lane的练习4有两部分。

 (a) 一个阿贝尔群的乘法、单位元和取逆操作本身是群同态，因此一个阿贝尔群可以组成Grp中的一个群对象。

 (b) 反过来，Grp中的每一个群对象都是以这种方式出现的：第二个乘法与第一个乘法一致，并且第一个是交换的。一半（b）是 Eckmann-Hilton 论证。该文件使用 Theory/EckmannHilton.v 而不是重新推导它——它是该文件的第四个使用者，在 Structure/Semiadditive.v、Instance/Top/LoopSpace.v 和 Theory/Centre.v 之后（按 [Require] 测量，而不是按名称：搜索标记 [EckmannHilton] 会返回八个文件——Theory/EckmannHilton.v 本身，上述三个使用者、本文件，以及三个仅在文本中提到它的文件（Instance/Grp/Quotient.v、Instance/Sets/Quotient/Partition.v 和 Structure/Bicartesian/Matrix.v）；更宽松的标记 [Eckmann] 会返回二十个。早期草稿说是七个和十九个，默默地省略了各自的捐赠者；审计纠正了两者，这里引用的数字是实际的 grep 输出）。
*)

(*
 A PROSE-TO-THEOREM CONVERSION, AND ITS THREE SITES

 The statement proved here is asserted in prose, unproved, in three
 places in the tree:

 - Structure/Group.v, the [GroupObject] background essay: “A group
 object in Grp itself is an abelian group: the two multiplications
 satisfy an interchange law, and the Eckmann-Hilton argument ... forces
 them to coincide and to commute”.  (Theory/EckmannHilton.v cites
 that passage in Structure/Group.v one line below the sentence's key
 line, so that existing cross-reference is off by one.  It is left
 alone -- this file modifies nothing outside itself.  An audit caught
 an off-by-one in THIS sentence too: it had named the line carrying
 only the parenthetical gloss rather than the citing token itself.)
 - Theory/EckmannHilton.v, in the list of facts the principle
 explains: “a group object in Grp is an abelian group.  The ambient
 multiplication and the internal one interchange because the internal
 one is a homomorphism for the ambient one.”
 - Theory/EckmannHilton.v again, in the roster of in-tree prose
 appeals to the principle.

 No formal statement of the exercise existed anywhere: a search for the
 phrases “group object in Grp” and “objects in Grp” over the tree's [.v]
 files returns exactly those three prose lines and nothing else. 

 --------
 从散文到定理的转换及其三个位置

 这里证明的陈述以散文形式在树的三个地方出现，未被证明：- Structure/Group.v，[GroupObject] 背景文章：“Grp 中的一个群对象本身是一个阿贝尔群：两种乘法满足交换律，Eckmann-Hilton 论证……迫使它们重合并交换。”（Theory/EckmannHilton.v 在句子关键行的下一行引用了 Structure/Group.v 中的这段话，所以现有的交叉引用偏差一行。不做修改——这个文件不修改自身之外的内容。审计也发现本句也存在一行偏差：它引用了仅包含括号注释的行，而不是引用标记本身。）
 - Theory/EckmannHilton.v，在列举该原理解释的事实时：“Grp 中的群对象是阿贝尔群。”环境乘法和内部乘法可以互换，因为内部乘法对于环境乘法来说是一个同态。
 —— 《Theory/EckmannHilton.v》中，再次在树形散文的名单中引用了该原理。

 练习的正式表述不存在于任何地方：在树的 [.v] 文件中搜索“Grp 中的群对象”和“Grp 中的对象”这两个短语，只返回这三行散文，没有其他内容。
*)

(*
 A PRIOR-ART CORRECTION.  The issue's “Current state” section says that
 “no category Grp and no category of group objects exists”.  BOTH halves
 are stale.  [Grp] is Instance/Grp.v and [GrpCat], the category of
 group objects in a cartesian monoidal category, is
 Theory/Algebra/Group/Hom.v.  An object of [GrpCat GrpS] is precisely a
 [GrpS]-object together with a [@GroupObject GrpS GrpCM] structure on it,
 which is the datum quantified over below; but Theory/Algebra/Group/Hom.v
 is NOT required here (it would add nine modules to this file's
 dependency closure, measured, for no statement that is made), so
 nothing below is phrased in terms of [GrpCat].

 The sibling exercise is Instance/Fun/Group.v, which is Exercise 3 of the
 same section -- group objects in a FUNCTOR category are pointwise
 groups.  It is a different exercise and is neither used nor duplicated
 here; the two files share only the idiom of reading a diagrammatic
 [GroupObject] law at a point. 

 --------
 先前技术的更正。该问题的“当前状态”部分说“没有类别 Grp，也没有组对象的类别”。这两个部分都是过时的。[Grp] 是 Instance/Grp.v，而 [GrpCat]，是笛卡尔单体范畴中组对象的类别，是 Theory/Algebra/Group/Hom.v。[GrpCat GrpS] 的一个对象恰好是一个 [GrpS] 对象以及它上的一个 [@GroupObject GrpS GrpCM] 结构，这正是下面量化的数据；但这里不需要 Theory/Algebra/Group/Hom.v（它会为此文件的依赖闭包增加九个模块，而没有提出任何声明），因此下面没有以 [GrpCat] 表述的内容。兄弟练习是 Instance/Fun/Group.v，这是同一章节的练习3——在函子类别中的群对象是逐点群。这是一个不同的练习，这里既不使用也不重复；这两个文件仅共享在某一点阅读图示 [GroupObject] 定律的习惯用法。
*)

(*
 THE CRUX, AND WHY IT COSTS ONE LINE

 An object of [GrpCat GrpS] is a group [G] whose multiplication
 [mappend : G ⨂ G ~> G] is itself a MORPHISM OF Grp, i.e. a [GrpHom].
 Instance/Grp.v's [GrpHom] carries

 grp_map_mul : ∀ a b, f (grp_mul _ a b) ≈ grp_mul _ (f a) (f b)

 and the source of [mappend] is [Grp_product G G], whose multiplication
 is componentwise.  Writing [f x y := grp_map mappend (x, y)] and
 [g := grp_mul G], instantiating [grp_map_mul] at the two PAIRS [(a, c)]
 and [(b, d)] gives

 f (g a b) (g c d) ≈ g (f a c) (f b d)

 which is Theory/EckmannHilton.v's [interchange] verbatim.  The
 “middle-two swap” that the middle-four interchange law is usually
 described by is entirely absorbed into WHICH pairs are fed to
 [grp_map_mul]: the proof term of [gob_interchange] is literally
 [grp_map_mul mappend (a, c) (b, d)], with no tactic and no reassociation.
 Nothing else in half (b) has any content: the two unit laws are
 [mempty_left] and [mempty_right] read at the points [(ttt, a)] and
 [(a, ttt)], and respectfulness is [proper_morphism] of the underlying
 setoid map.

 The unit laws are usable because [CC_Monoidal]'s unitors are the
 TRANSPARENT cartesian isomorphisms [prod_one_l] and [prod_one_r]
 (an audit corrected the mechanism here: the record literal at
 Structure/Monoidal/Internal/Product.v names ONLY [tensor] and [I],
 and the three isomorphism fields are filled by TYPECLASS RESOLUTION
 against Structure/Cartesian.v's [#[export] Program
 Instance]s [prod_one_l], [prod_one_r] and [prod_assoc] -- so exactly six
 naturality and two coherence fields become [Program] obligations, eight
 in all); had they been opaque
 obligations, [mempty_left] would have compared [mappend ∘ mempty ⨂ id]
 with a term that reduces to nothing and this route would have been
 closed.  This is worth recording because the same file's obligations ARE
 opaque and a reader scanning it will see them first. 

 --------
 关键点，以及为什么它花费了一行代码

 [GrpCat GrpS] 的一个对象是一个群 [G]，其乘法 [mappend : G ⨂ G ~> G] 本身是 Grp 的态射，即 [GrpHom]。
 Instance/Grp.v 的 [GrpHom] 包含

 grp_map_mul : ∀ a b, f (grp_mul _ a b) ≈ grp_mul _ (f a) (f b)

 并且 [mappend] 的源是 [Grp_product G G]，其乘法是按分量进行的。写成 [f x y := grp_map mappend (x, y)] 和 [g := grp_mul G]，在两个 PAIRS [(a, c)] 和 [(b, d)] 上实例化 [grp_map_mul] 得到

 f (g a b) (g c d) ≈ g (f a c) (f b d)这是 Theory/EckmannHilton.v 的 [interchange] 原文。通常描述为“中间两个交换”的中间四个交换律完全被吸收到输入 [grp_map_mul] 的配对中：[gob_interchange] 的证明项字面上就是 [grp_map_mul mappend (a, c) (b, d)]，没有使用任何策略，也没有重新结合。半部分(b)的其他内容都没有实质内容：两个单位律是 [mempty_left] 和 [mempty_right]，分别在 [(ttt, a)] 和 [(a, ttt)] 点阅读，尊重性是基础集合范畴映射 [proper_morphism]。这些单位律是可用的，因为 [CC_Monoidal] 的单位元是透明的笛卡尔同构 [prod_one_l] 和 [prod_one_r] （一次审核纠正了这里的机制：Structure/Monoidal/Internal/Product.v 中的记录字面量仅命名了 [tensor] 和 [I]，而三个同构字段是通过针对 Structure/Cartesian.v 的 [#[export] 的类型类解析（TYPECLASS RESOLUTION）填充的 Program Instance]s [prod_one_l]、[prod_one_r] 和 [prod_assoc] ——因此恰好六个自然而然性和两个相干性字段变成 [Program] 的义务，一共八个）；如果它们是不可见的义务，[mempty_left] 就会将 [mappend ∘ mempty ⨂ id] 与归约为无的项进行比较，这条路径将会被关闭。值得记录的是，因为同一文件的义务是不可见的，读者扫描时会首先看到它们。
*)

(*
 WHAT IS PROVED, IN ORDER

 (1) [GrpS], [GrpCM], [GrpMon], [GrpTensor] -- the ambient data, with two
 [eq_refl] readings pinning that the tensor IS Instance/Grp.v's own
 [Grp_product] and the tensor unit IS [Grp_trivial].
 (2) [AbelianGrp] -- commutativity of a [GrpObject], named for the first
 time (see the naming note below).
 (3) Half (b): [gmul2], [gunit2], [ginv2] read a group-object structure
 elementwise; [gmul2_respects], [gmul2_unit_left],
 [gmul2_unit_right] and [gob_interchange] are the five inputs
 Theory/EckmannHilton.v asks for; then [gob_units_agree],
 [gob_mul_agrees], [gob_mul_comm] and the headline
 [group_object_abelian] are its outputs, and [gob_inv_agrees]
 finishes the identification by uniqueness of inverses.
 (4) [group_object_mul_unique], [group_object_unit_unique],
 [group_object_inverse_unique] -- the group-object structure on a
 group is unique when it exists, which is what “arises this way”
 means.
 (5) Half (a): [ab_mappend], [grp_ab_inverse], [ab_MonoidObject] and the
 headline [abelian_GroupObject].
 (6) [abelian_iff_group_object] and the packaged [maclane_III_6_ex4].
 (7) Strengths: three [eq_refl] round trips one way, three [≈] round
 trips the other, with the failures diagnosed.
 (8) Non-vacuity: Z/2 with computing operations, the trivial group as the
 degenerate case proved degenerate, and S3 -- a nonabelian group with
 PROVABLY NO group-object structure, so the theorem excludes
 something.
 (9) A probe section: SIX negatives of three kinds against five positive
 controls and an instrument check.  (CORRECTION, #450: FOUR
 negatives of TWO kinds since #450, against SEVEN positive
 controls, the two universe negatives having become [Check]
 controls beside the five [ctrl_] constants; see the probe
 section.) 

 --------
 按顺序证明的内容是什么(1) [GrpS], [GrpCM], [GrpMon], [GrpTensor] —— 环境数据，其中两个 [eq_refl] 读数确认张量就是 Instance/Grp.v 自身的 [Grp_product]，并且张量单位是 [Grp_trivial]。(2) [AbelianGrp] —— 一个 [GrpObject] 的交换性，首次命名（见下面的命名说明）。(3) 一半 (b)：[gmul2], [gunit2], [ginv2] 逐元素读取群对象结构；[gmul2_respects], [gmul2_unit_left], [gmul2_unit_right] 和 [gob_interchange] 是 Theory/EckmannHilton.v 所要求的五个输入；然后 [gob_units_agree], [gob_mul_agrees], [gob_mul_comm] 和标题 [group_object_abelian] 是它的输出，[gob_inv_agrees] 通过逆元的唯一性完成识别。(4) [group_object_mul_unique]，[group_object_unit_unique]，[group_object_inverse_unique] —— 当存在时，群上的群对象结构是唯一的，这就是“以这种方式产生”的意思。(5) 一半 (a)：[ab_mappend]，[grp_ab_inverse]，[ab_MonoidObject] 以及标题 [abelian_GroupObject]。(6) [abelian_iff_group_object] 和打包的 [maclane_III_6_ex4]。(7) 优点：三次 [eq_refl] 单程往返，三次 [≈] 另一方向往返，并进行故障诊断。(8) 非空性：Z/2 具有计算操作，平凡群作为退化情况被证明是退化的，以及 S3 —— 一个非阿贝尔群且可证明没有群对象结构的群，因此定理排除了某些东西。(9) 探针部分：针对五个阳性对照和一次仪器检查的三种类型的六个阴性对照。(更正，#450：自#450以来有四个负样本，属于两种类型，对应七个阳性对照，其中两个宇宙负样本已成为[Check]对照，与五个[ctrl_]常数并列；见探针部分。)
*)

(*
 WHAT EACH HALF COSTS

 Half (b) costs nothing beyond the five inputs above; every conclusion is
 an [exact] of an [eh_*] applied to them.  Two of Eckmann-Hilton's four
 outputs are REDUNDANT in this instance and are deliberately not
 restated: [eh_assoc] and [eh_g_assoc] conclude associativity, which both
 operations already have by hypothesis ([mappend_assoc] for one,
 [grp_mul_assoc] for the other).  What this instance genuinely consumes
 is [eh_units], [eh_ops], [eh_comm] and [eh_g_comm] -- four, not three;
 an audit caught the omission of [eh_comm], which [gob_mul_comm] spends.
 That is the honest accounting:
 the argument is strictly more general than the use made of it here,
 because it assumes neither associativity nor commutativity of either
 operation, and this file supplies both associativities for free.

 Half (a) costs three homomorphism constructions, and commutativity is
 spent EXACTLY ONCE in each of two of them: in [ab_mappend]'s
 [grp_map_mul] obligation, which is the middle-four interchange
 [(a·c)·(b·d) ≈ (a·b)·(c·d)], and in [grp_ab_inverse]'s, where
 [grp_inv_mul] delivers [(a·b)⁻¹ ≈ b⁻¹·a⁻¹] and commutativity turns it
 into [a⁻¹·b⁻¹].  The third, [mempty], is not constructed at all:
 Instance/Grp.v's [Grp_zero_hom] already IS the constant-at-the-unit
 homomorphism out of the trivial group, and it is reused rather than
 rebuilt.  The five diagrammatic laws of [MonoidObject] and
 [GroupObject] are then pointwise readings of [grp_mul_unit_l],
 [grp_mul_unit_r], [grp_mul_assoc], [grp_mul_inv_l] and [grp_mul_inv_r];
 none of them spends commutativity. 

 --------
 每一半的成本

 半部分 (b) 除了上述五个输入外不需要额外成本；每一个结论都是将一个 [eh_*] 应用于它们的 [exact]。Eckmann-Hilton 的四个输出中有两个在这种情况下是多余的，故意没有重新陈述：[eh_assoc] 和 [eh_g_assoc] 得出结合性，而两个操作按假设已经具备结合性（一个是 [mappend_assoc]，另一个是 [grp_mul_assoc]）。这个实例真正消耗的是 [eh_units]、[eh_ops]、[eh_comm] 和 [eh_g_comm] —— 四个，而不是三个；审计发现漏掉了 [eh_comm]，而 [gob_mul_comm] 则使用了它。这是诚实的核算：
 这个论证比这里使用的更一般，因为它既不假设任一操作的结合性，也不假设交换性，而这个文件免费提供了两个结合性。一半的 (a) 花费了三个同态构造，并且在其中两个中，每个仅恰好使用一次交换性：在  [ab_mappend] 的 [grp_map_mul]  义务中，这是中间四交换 [(a·c)·(b·d) ≈ (a·b)·(c·d)] ，以及在 [grp_ab_inverse] 中，其中 [grp_inv_mul] 将 [(a·b)⁻¹ ≈ b⁻¹·a⁻¹] 转换，并且交换性将其变为 [a⁻¹·b⁻¹]。第三个 [mempty] 根本没有构造：Instance/Grp.v 的 [Grp_zero_hom] 已经是从平凡群出的单位常数同态，并且它被复用而不是重建。然后，ZWZ21WZZ 和 ZWZ22WZZ 的五个图示律便是 ZWZ23WZZ、ZWZ24WZZ、ZWZ25WZZ、ZWZ26WZZ 和 ZWZ27WZZ 的逐点读数；它们都没有使用交换性。
*)

(*
 STRENGTHS, MEASURED STRICT-FIRST

 Going from an abelian group to a group object and back, all three
 operations return AT LEIBNIZ EQUALITY, by [eq_refl]:
 [abelian_roundtrip_mul], [_unit], [_inv].  Nothing needed proving there;
 the group-object structure built in half (a) has [grp_mul G] literally
 inside it, and the pair projections reduce by iota.

 Going the other way -- from an arbitrary group object, through half (b),
 and back through half (a) -- reaches only [≈]:
 [group_object_roundtrip_mul], [_unit], [_inv].  The diagnosis is not
 “rebuilt law fields”: it is that [gmul2 G GO] is a projection of a
 VARIABLE [GO], so there is nothing to reduce at all, and no amount of
 transparency downstream would change that.  The whole-record round trip
 [abelian_GroupObject G (group_object_abelian G GO) = GO] is refuted for
 the same reason and pinned as a probe.

 Also refuted, and pinned as [probe_other_roundtrip] -- an audit found
 this paragraph claiming “pinned” while NO negative in the file mentioned
 [HA] at all, so the guard is now real rather than asserted:
 [AbelianGrp G ↔ GroupObject G] is a biconditional
 and NOT an isomorphism of types.  The composite
 [group_object_abelian G (abelian_GroupObject G HA)] is a different proof
 term from [HA] -- it routes through [eh_g_comm] -- and there is no
 setoid on [AbelianGrp G] under which to state that they agree, [AbelianGrp G]
 being a family of [≈]-proofs and not a setoid carrier.  What replaces
 the missing type isomorphism is the uniqueness triple (4) above, which
 says the STRUCTURE is determined even though its PROOFS are not. 

 --------
 优势，严格优先测量

 从阿贝尔群到群对象再返回，所有三个操作通过 [eq_refl] 的方式返回勒布尼茨等式：
 [abelian_roundtrip_mul], [_unit], [_inv]。这里无需证明；在 (a) 部分构建的群对象结构中，[grp_mul G] 实际上就在其中，并且通过 iota 简化了对偶投影。

 反过来 —— 从任意群对象，通过 (b) 部分，再通过 (a) 部分返回 —— 只能得到 [≈]：
 [group_object_roundtrip_mul], [_unit], [_inv]。诊断结果并不是“重建的法则域”：原因是 [gmul2 G GO] 是变量 [GO] 的一个投影，因此根本没有需要简化的部分，并且下游的任何透明度都无法改变这一点。整体记录的往返 [abelian_GroupObject G (group_object_abelian G GO) = GO] 也因同样原因被驳回，并被标记为探测。同样被驳斥，并标记为 [probe_other_roundtrip] —— 审计发现这一段声称“标记”，而在文件中根本没有提到 [HA]，所以该守护现在是真实的，而不是被断言的：[AbelianGrp G ↔ GroupObject G] 是一个双条件关系，而不是类型同构。复合 [group_object_abelian G (abelian_GroupObject G HA)] 与 [HA] 是不同的证明项 —— 它通过 [eh_g_comm] —— 并且在 [AbelianGrp G] 上没有集合同构能够说明它们一致，[AbelianGrp G] 是 [≈] 证明的家族，而不是集合同构承载。取代缺失的类型同构的是上文（4）中的唯一性三元组，它说明结构是确定的，即使其证明不是。
*)

(*
 THE Set PIN, DISCLOSED

 [Grp_Terminal] (Instance/Grp.v) rides [Grp_trivial]
 (Instance/Grp.v), which is declared with a single universe binder
 where the record wants more, so [Grp_trivial@{u} : GrpObject@{u u Set}]
 and [Grp_Terminal@{u} : Terminal@{u Set}]: the HOM universe is pinned
 at [Set].  (CORRECTION, the PR “algebraic carriers are sets”
 (2026-09-17): an earlier revision wrote [Grp_trivial]'s readback as
 [GrpObject@{u Set u}] and cited [Grp_Terminal] and [Grp_trivial] at
 lines of Instance/Grp.v they have since left.  That PR permuted
 [GrpObject]'s universe
 roles from (carrier, proof, aux) to (aux, carrier, proof) and moved
 both constants down the file; the two readbacks above are re-measured
 by [About] under [Set Printing Universes] after it.  [Grp_Terminal]'s
 is unchanged, and so is the pin.)  Since a [CartesianMonoidal]
 structure on Grp needs a terminal
 object, everything in this file is confined to groups whose hom-setoids
 live in [Set], which is what the local abbreviation

 Monomorphic Universe gu.  Definition GrpS := Grp@{gu Set}.

 makes explicit rather than leaving to elaboration.  The pin is
 MEASURED, not guessed: the probe section declares [Constraint Set < ph],
 accepts [Grp@{pu ph}] as a category AND [Grp_Cartesian] at those very
 levels, and rejects [Grp_Terminal] with “Cannot enforce Set = ph” -- so
 the cause is [Grp_Terminal] specifically, not [Grp] and not the
 cartesian structure.  The same rejection propagates to
 [CC_CartesianMonoidal], with the error still reported AT
 [Grp_Terminal].

 This is a DONOR defect.  It is not repaired here (Instance/Grp.v is not
 touched), and it is NOT claimed unavoidable -- [unit_setoid] is
 polymorphic and the pin looks like the universe-minimization family
 recorded elsewhere in this tree -- only located.

 CORRECTION (#450): the donor defect is repaired.  #450 wrote out the
 universes of Instance/Grp.v's zero-object constants in place, and
 [About] now reads [Grp_trivial@{p} : GrpObject@{p p p}] and
 [Grp_Terminal@{u p} : Terminal@{u p}], whose only constraints on local
 universes are [Set < u] and [p < u], the rest being stdlib bounds on [p].
 The two universe negatives in section [ProbeUniversePin] below then
 stopped being refused (the build stopped at the first with Rocq's
 report that the guarded command had been accepted) and are kept as
 controls.  Everything ABOVE this
 correction describes the tree before #450.  This file's own statements
 were NOT generalized: [GrpS] is still [Grp@{gu Set}], the fixed reading
 every constant below is stated at, and restating them at [Grp@{u p}]
 is not undertaken here. 

 --------
 设置的 PIN，已披露[Grp_Terminal]（Instance/Grp.v）继承了 [Grp_trivial]（Instance/Grp.v），它用一个单一的宇宙绑定声明，而该记录需要更多，所以 [Grp_trivial@{u} : GrpObject@{u u Set}] 和 [Grp_Terminal@{u} : Terminal@{u Set}]：HOM 宇宙在 [Set] 被固定。（更正，PR “代数载体是集合”（2026-09-17）：早期版本将 [Grp_trivial] 的回读写为 [GrpObject@{u Set u}]，并在 Instance/Grp.v 的行上引用了 [Grp_Terminal] 和 [Grp_trivial]，它们后来已经离开。该 PR 将 [GrpObject] 的宇宙角色从（载体、证明、辅助）排列改为（辅助、载体、证明），并将两个常量移到文件的下方；上述两个回读随后由 [About] 在 [Set Printing Universes] 下重新测量。[Grp_Terminal] 的
 状态保持不变，pin 也是如此。）由于 Grp 上的 [CartesianMonoidal] 结构需要一个终端对象，本文件中的所有内容都被限制在同类集生活在 [Set] 的群中，这正是本地缩写

 Monomorphic Universe gu. 定义 GrpS := Grp@{gu Set}.

 明确表示出来，而不是留给推导。pin 是被测量的，而非猜测的：探测部分声明了 [Constraint Set < ph]，接受 [Grp@{pu ph}] 作为一个范畴，并在那些级别接受 [Grp_Cartesian]，并拒绝 [Grp_Terminal]，报错为“Cannot enforce Set = ph” —— 因此原因具体是 [Grp_Terminal]，而非 [Grp]，也不是笛卡尔结构。相同的拒绝也传播到 [CC_CartesianMonoidal]，错误仍在 [Grp_Terminal] 处报告。这是一个DONOR缺陷。这里没有修复它（Instance/Grp.v未被修改），也没有声称它是无法避免的——[unit_setoid]是多态的，并且引脚看起来像记录在此树其他地方的宇宙最小化系列——仅被定位。更正 (#450)：供体缺陷已修复。#450 在原位列出了 Instance/Grp.v 的零对象常量的宇宙，并且 [About] 现在读取为 [Grp_trivial@{p} : GrpObject@{p p p}] 和 [Grp_Terminal@{u p} : Terminal@{u p}]，其对局部宇宙的唯一约束是 [Set < u] 和 [p < u]，其余的为 [p] 的标准库边界。下面 [ProbeUniversePin] 部分中的两个宇宙负值随后不再被拒绝（构建在 Rocq 报告守护命令已被接受后在第一个停止），并作为控制保留。此更正上方的所有内容描述的是 #450 之前的树。此文件自身的声明未被泛化：[GrpS] 仍为 [Grp@{gu Set}]，每个以下常量的固定读取已声明，在此不对它们在 [Grp@{u p}] 重新陈述。
*)

(*
 NOTATION AND SCOPE NOTES, MEASURED

 Three notation hazards were reported to this file's author as parse
 errors.  All three were re-measured here, and the report was WRONG
 about two of them.

 - [obj[Grp@{gu Set}]] PARSES AND ELABORATES FINE.  [Check] returns
 [obj[Grp] : Type].  There is no bracket-versus-[@{}] conflict.
 - [fobj[@tensor _ GrpCM]] PARSES AND ELABORATES FINE too, printing
 [fobj[(⨂)]].  The [fobj[ F ]] notation is closed on both sides, so its
 argument parses at level 200 and an [@]-applied head is fine.
 - What DOES bite, and what most likely produced the reports above, is
 something else: [fobj] lives in Category.Theory.Functor and its
 notation lives in [object_scope].  Requiring only
 Category.Instance.Grp loads that module without importing its names,
 so [fobj] is then “not found in the current environment” -- a NAME
 RESOLUTION error, not a parse error.  This file requires
 Category.Theory.Functor explicitly for exactly that reason.
 - The third hazard is REAL but is an elaboration error, not a parse
 error: bare [G ⨂[GrpCM] G] picks the MORPHISM notation
 (Structure/Monoidal.v) over the object one, and reports
 that [G] “has type obj[GrpS] while it is expected to have type
 ?x ~{GrpS}~> ?w”.  Either a [%object] delimiter or a result-type
 ascription selects the object reading.  Below, the object is written
 [@fobj _ _ GrpTensor (G, H)] so that no scope discipline is needed.

 Independently: [inverse] is effectively a keyword downstream of
 Structure/Group.v, whose notation quotes the token, so the
 group-object inversion is projected by its fully qualified name
 [@Category.Structure.Group.inverse]. 

 --------
 符号和范围说明，已测量

 有三种符号危险被报告给本文件的作者，作为解析错误。这里对这三种危险都进行了重新测量，而报告中有两项是错误的。- [obj[Grp@{gu Set}]] 解析和展开正常。[Check] 返回 [obj[Grp]：类型]。没有括号与 [@{}] 的冲突。- [fobj[@tensor _ GrpCM]] 解析和展开也正常，打印 [fobj[(⨂)]]。[fobj[ F ]] 符号在两边都已闭合，因此其参数在 200 级别解析，[@] 应用的头也是可以的。- 真正有问题的，以及最有可能产生上述报告的，是其他东西：[fobj] 属于 Category.Theory.Functor，其符号属于 [object_scope]。只要求 Category.Instance.Grp 会加载该模块而不导入其名称，因此 [fobj] 在当前环境中“未找到”——这是一个名称解析错误，而不是解析错误。正是出于这个原因，该文件明确要求 Category.Theory.Functor。- 第三个风险是真实存在的，但它是一个展开错误，而不是解析错误：裸露的 [G ⨂[GrpCM] G] 选择了 MORPHISM 符号（Structure/Monoidal.v）而非对象符号，并报告 [G] “的类型是 obj [GrpS] ，而预期类型是 ?x ~{GrpS}~> ?w”。无论是 [%object] 分隔符还是结果类型标注都会选择对象解释。下文中，对象被写作 [@fobj _ _ GrpTensor (G, H)] ，因此不需要任何作用域规则。

 独立来看：[inverse] 实际上是 Structure/Group.v 下游的一个关键字，其符号引用了该标记，因此群对象的逆运算通过其完全限定名称 [@Category.Structure.Group.inverse] 被投射。
*)

(*
 UNIVERSES, AND THE AXIOM COUNT

 Measured off BOTH the binder and the constraint block of every one of
 the file's 58 constants, with [Set Printing Universes]:

 - [GrpS@{} : Category@{gu Set Set}], constraint block [Set < gu].  So
 the object universe is free and the HOM and PROOF universes are BOTH
 [Set].  That identification is not this file's doing: [Grp]'s second
 universe binder fills both slots, and [Grp@{gu Set}] was the only
 instance a terminal object had before #450 (see THE Set PIN and its
 correction; since #450 [GrpS] is a choice, no longer a necessity).
 - Every constant carries [Set < gu] except FIVE, each for a reason:
 [ctrl_probe_category] and [ctrl_probe_cartesian] live at
 [Grp@{pu ph}] and carry [Set < ph], [ph < pu] instead, which is
 exactly what makes them controls; [eh_probe_instrument] is over [bool];
 [Z2_GroupObject_nondegenerate] carries only
 [u <= Logic_lemmas.equality.u0]; and
 [trivial_GroupObject_degenerate] has an EMPTY constraint block.
 [ctrl_probe_terminal] carries BOTH [Set < gu] and [Set < ph], since
 it mentions both categories.
 - NO constraint block anywhere in the file contains a universe
 EQUATION.  Every constraint is a strict [<] or a bound [<=]; the [=]
 signs in the whole [About] dump are the TEN TERM equalities in the
 [eq_refl] Examples and readings ([grp_tensor_is_product],
 [grp_tensor_unit_is_trivial], the three [abelian_roundtrip_*], the four
 [Z2_gob_*] and [eh_probe_instrument]) -- an earlier draft of this
 paragraph said TWO, which an audit corrected.  So the [Set] pin is
 the ONLY identification, and it was INHERITED from [Grp_Terminal]
 rather than introduced here (since #450 it is kept by [GrpS]'s
 definition alone).
 - The predicate itself is free in its own universe:
 [AbelianGrp@{u} : obj -> Type@{u}], constraint block [Set < gu] only.

 58/58 constants are closed under the global context. 

 --------
 宇宙，以及公理计数

 测量了该文件的 58 个常量中每一个的绑定器和约束块，使用 [Set Printing Universes]：- [GrpS@{} : Category@{gu Set Set}]，约束块 [Set < gu]。所以对象宇宙是自由的，而 HOM 和 PROOF 宇宙都是 [Set]。这个标识不是这个文件的操作：[Grp] 的第二个宇宙绑定填充了两个位置，而 [Grp@{gu Set}] 是#450之前终端对象的唯一实例（参见 The Set PIN 及其修正；自#450 起 [GrpS] 是一个选择，不再是必需）。- 每个常量都携带 [Set < gu]，只有 FIVE 除外，每个都有原因：[ctrl_probe_category] 和 [ctrl_probe_cartesian] 位于 [Grp@{pu ph}] 并携带 [Set < ph]，[ph < pu]，正是这使它们成为控件；[eh_probe_instrument] 位于 [bool] 上；[Z2_GroupObject_nondegenerate] 仅携带 [u <= Logic_lemmas.equality.u0]；而 [trivial_GroupObject_degenerate] 具有空的约束块。[ctrl_probe_terminal] 同时携带 [Set < gu] 和 [Set < ph]，因为它提到了两个类别。- 文件中没有任何约束块包含一个宇宙方程。每一个约束都是严格的 [<] 或有界的 [<=]；整个 [About] 转储中的 [=] 符号是 [eq_refl] 示例和读数中的十大等式（[grp_tensor_is_product]、[grp_tensor_unit_is_trivial]、三个 [abelian_roundtrip_*]、四个 [Z2_gob_*] 和 [eh_probe_instrument]）——这个段落的早期草稿写的是两个，经审计更正。因此 [Set] 引脚是唯一的标识，并且它是继承自 [Grp_Terminal]，而不是在此引入（自 #450 起，它仅由 [GrpS] 的定义保留）。- 该谓词在其自身的宇宙中是自由的：只有 [AbelianGrp@{u} : obj -> Type@{u}]，约束块 [Set < gu]。  

 58/58 常量在全局上下文中是封闭的。
*)

(*
 THE DEPENDENCY ON Instance/Grp/Epi.v

 That file is required for ONE thing: [GrpSym3], [sym3_s], [sym3_a] and
 [sym3_l0], which supply the nonabelian witness at the end.  It was
 chosen over Instance/Grp/TwoFunctors.v's [S3] by measurement: relative
 to the closure this file already needs, Epi.v adds exactly ONE module
 (itself), whereas TwoFunctors.v adds four (itself, Functor/Twist.v,
 Instance/Cat.v and Instance/StrictCat.v).  Neither S3 was rebuilt. 

 --------
 对 Instance/Grp/Epi.v 的依赖

 该文件只用于一件事：[GrpSym3]、[sym3_s]、[sym3_a] 和 [sym3_l0]，它们提供末尾的非阿贝尔见证。通过测量，该文件被选中，而不是 Instance/Grp/TwoFunctors.v 的 [S3]：相对于该文件已经需要的闭包，Epi.v 精确添加了一个模块（它自己），而 TwoFunctors.v 添加了四个模块（它自己、Functor/Twist.v、Instance/Cat.v 和 Instance/StrictCat.v）。S3 都没有被重建。
*)

(*
 THE NAME [AbelianGrp]

 No predicate of this shape is named anywhere in the tree: searches for
 the token [AbelianGrp], for the shape
 [grp_mul _ a b ≈ grp_mul _ b a], and for a [Commutative]-style
 predicate over [GrpObject] all come back empty of a NAMED one.  The
 condition itself is written INLINE at four sites in three files -- as a
 hypothesis [comm] at Instance/Grp/TwoFunctors.v and at
 Instance/Grp/Abelianization.v, and as a conclusion at
 Instance/Grp/Center.v -- so this is a naming, not a
 discovery, and all four sites are left alone.  [AbelianGrp] here is a
 PREDICATE on Instance/Grp.v's [GrpObject]; it is NOT
 Structure/Abelian.v's [Class Abelian] (a property of a CATEGORY) and it
 is NOT Instance/Ab.v's [AbObject] (a record extending [CMonObject]).

 WHY THE SUFFIX.  A first draft of this file called the predicate plainly
 [Abelian], on the argument -- correct as far as it goes -- that the two
 notions are different and live in different files.  That argument misses
 the MECHANICAL hazard, which is what forced the rename: the
 [make print-assumptions] gate compiles every audited module into ONE
 scope, and Structure/Abelian.v IS required there, so a bare
 [Print Assumptions Abelian.] would resolve to whichever of the two was
 imported last and could silently audit the wrong constant.  That is not
 a remote hazard: a sweep of the 277 modules the gate pulls into its one
 scope counts THIRTY-TWO top-level names declared in two of them at once,
 of which three were audited under a bare name -- and one of those three,
 [fp_generators_distinct], was resolving to Instance/Mon/Coproduct.v's
 monoid theorem where the surrounding gate block plainly means
 Instance/Grp/Pushout.v's group one.  All three now carry fully-qualified
 gate entries, which is the only spelling immune to Require-order drift,
 and the twenty-nine others stay latent because no gate entry names them.
 [BoolSet] was one of those (declared in both Instance/Sets/Quotient.v and
 Instance/Sets/Pullback.v until the Pullback.v one was renamed
 [PbBoolSet]), and a second collision on a name as central as
 [Abelian] is not worth the aesthetics.  [grp_ab_inverse] and
 [eh_probe_instrument] carry suffixes for a WEAKER reason, and an audit
 corrected an earlier draft that said “for the same reason”: they collided
 with Instance/Ab/Character/Finite.v and Test/ProbePolynomial.v,
 but NEITHER of those files is required into the print-assumptions scope
 ([Locate ab_inverse] there returns nothing), so those two renames are
 tree-wide name hygiene and not a gate hazard.  All three collisions were
 found only by sweeping this file's OWN declared names against the tree with
 attribute prefixes allowed; a grep anchored at [Definition|Instance]
 misses [#[export] Program Instance] and would have reported none.
 No bridge to [AbObject] is built: that record is a different one, the
 only in-tree passage between the two hierarchies is
 Instance/Grp/Abelianization.v's [Ab_to_GrpOb] going the other way, and
 Instance/Ab.v is not in this file's dependency closure. 

 --------
 名称 [AbelianGrp]

 树中的任何地方都没有名为这种形式的谓词：对标记 [AbelianGrp]、形式 [grp_mul _ a b ≈ grp_mul _ b a] 以及 [Commutative] 风格的 [GrpObject] 谓词的搜索，所有的 NAMED 都找不到。该条件本身以 INLINE 方式写在三个文件的四个位置——作为假设 [comm] 在 Instance/Grp/TwoFunctors.v 和 Instance/Grp/Abelianization.v 中，以及作为结论在 Instance/Grp/Center.v 中——所以这是命名，而不是发现，四个位置都保持不变。这里的 [AbelianGrp] 是 Instance/Grp.v 的 [GrpObject] 上的 PREDICATE；它不是 Structure/Abelian.v 的 [Class Abelian]（一个 CATEGORY 的属性），也不是 Instance/Ab.v 的 [AbObject]（一个扩展 [CMonObject] 的记录）。为什么要加后缀。这个文件的初稿将谓词直接命名为 [Abelian]，对参数的处理--就目前而言是正确的--基于这样一个论点：这两个概念不同，并且位于不同的文件中。这个论点忽视了机械上的风险，这也是迫使重命名的原因：[make print-assumptions] 模块会将每个审核过的模块编译到同一个作用域中，而 Structure/Abelian.v 在那里是必须的，因此一个单独的 [Print Assumptions Abelian.] 将会解析为最后导入的那个，并且可能悄无声息地审核错误的常量。那不是一个遥远的风险：对门控拉入其唯一作用域的277个模块的扫描显示，其中两个模块中同时声明了三十二个顶层名称，其中三个是在裸名下进行审核的——而其中一个，[fp_generators_distinct]，正在解析到Instance/Mon/Coproduct.v的模范定理，而周围的门控块显然意味着Instance/Grp/Pushout.v的群体定理。现在这三个都带有完全限定的门控条目，这是唯一能够免受Require顺序漂移影响的拼写方式，而其余二十九个保持潜伏状态，因为没有门控条目引用它们。[BoolSet]就是其中之一（在Instance/Sets/Quotient.v和Instance/Sets/Pullback.v中都声明过，直到Pullback.v的那个被重命名为[PbBoolSet]），而像[Abelian]这样中央名称的第二次冲突不值得在美学上考虑。[grp_ab_inverse] 和 [eh_probe_instrument] 附加后缀的原因较弱，审计更正了早期草稿中写的“出于同样原因”：它们与 Instance/Ab/Character/Finite.v 和 Test/ProbePolynomial.v 冲突，但这两个文件都不需要导入 print-assumptions 范围（[Locate ab_inverse] 那里没有返回任何内容），所以这两个重命名是整个树的命名卫生措施，而不是门级危险。所有三个冲突都是通过将该文件自身声明的名称与允许属性前缀的树进行比对才发现的；在 [Definition|Instance] 上锚定的 grep 将错过 [#[export] Program Instance] 并且什么都不会报告。没有通向 [AbObject] 的桥梁：那个记录是不同的，两个层次结构之间的唯一树内通路是 Instance/Grp/Abelianization.v 的 [Ab_to_GrpOb] 朝相反的方向，且 Instance/Ab.v 不在此文件的依赖闭包中。
*)

(*
 WHAT IS NOT DELIVERED

 - No statement about [GrpCat GrpS] as a CATEGORY: no forgetful functor,
 no comparison with [Ab], and in particular no claim that group
 objects in Grp form a category equivalent to abelian groups.  Only the
 OBJECTS are classified.
 - No bridge to Instance/Ab.v's [AbObject], for the reason above.
 - No morphism-level statement: nothing is proved about [GroupHom]s
 between two group objects in Grp, so “the identification is
 functorial” is neither stated nor proved.
 - No iterated collapse: the monoid analogue (a monoid object in the
 category of monoids is a commutative monoid) is not stated, and
 neither is the observation that the tower stops here.
 - No relation to Structure/Group/Representable.v's hom-group reading of
 a group object, and none to Instance/Fun/Group.v's Exercise 3.
 - The Set pin is disclosed and located, not repaired here.  (Since
 #450 the donor is repaired in Instance/Grp.v, but this file's
 constants are still stated at [GrpS] = [Grp@{gu Set}].)
 - [AbelianGrp G ↔ GroupObject G] is a biconditional only; the two type
 isomorphism attempts are refuted rather than achieved (see STRENGTHS).
 - S3 is shown to carry NO group-object structure, but no CLASSIFICATION
 of which groups do is offered beyond the biconditional itself, and no
 nonabelian group other than S3 is exhibited. 

 --------
 未交付的内容- 关于 [GrpCat GrpS] 作为一个类别没有说明：没有遗忘函子，也没有与 [Ab] 的比较，特别是没有声称 Grp 中的群对象形成一个与阿贝尔群等价的类别。仅对象被分类。- 没有与 Instance/Ab.v 中 [AbObject] 的桥接，原因如上。- 没有态射层面的说明：关于两个 Grp 中的群对象之间的 [GroupHom] 什么都没有证明，因此“该识别是函子性的”既未声明也未证明。- 没有迭代坍塌：单子类比（单子类别中的单子对象是交换单子）没有说明，也没有说明塔结构在此处停止。- 与 Structure/Group/Representable.v 中群对象的同态群解释没有关系，也与 Instance/Fun/Group.v 的练习3无关。- Set 引脚已被揭示和定位，这里未进行修复。（自 #450 起，供体在 Instance/Grp.v 中已被修复，但本文件的常量仍然声明为 [GrpS] = [Grp@{gu Set}]。）
 - [AbelianGrp G ↔ GroupObject G] 只是一个双条件；两种类型同构的尝试被反驳而非实现（参见 STRENGTHS）。
 - S3 被证明不携带群对象结构，但除了双条件本身外，没有提供哪些群确实具有该结构的分类，并且未展示除 S3 外的任意非阿贝尔群。
*)

(* * ** The ambient category and its cartesian monoidal structure / * ** 环境范畴及其笛卡尔幺半结构 *)

(*
 The Set-pinned Grp.  See THE Set PIN above: [Grp_Terminal] forced the
 hom universe until #450, and naming the instance here keeps every
 statement below at one fixed reading rather than letting elaboration
 pick per-constant instances. 

 --------
 设置固定组。见上面的设置固定：[Grp_Terminal] 强制 hom 宇宙直到 #450，并且在此处命名该实例可以使下面的每条语句保持一个固定的读法，而不是让展开为每个常量实例选择。
*)
Monomorphic Universe gu.

Definition GrpS : Category := Grp@{gu Set}.

Definition GrpCM : @CartesianMonoidal GrpS :=
  @CC_CartesianMonoidal GrpS Grp_Cartesian Grp_Terminal.

Definition GrpMon : @Monoidal GrpS := GrpCM.

Definition GrpTensor := @tensor GrpS GrpMon.

(*
 The tensor IS Instance/Grp.v's own direct product, and the tensor unit
 IS its own trivial group -- by [eq_refl], so no comparison morphism is
 needed anywhere below. 

 --------
 张量是 Instance/Grp.v 自身的直积，而张量单位是它自身的平凡群——根据 [eq_refl]，因此下面任何地方都不需要比较态射。
*)
Example grp_tensor_is_product (G H : GrpS) :
  @fobj _ _ GrpTensor (G, H) = Grp_product G H := eq_refl.

Example grp_tensor_unit_is_trivial :
  @Category.Structure.Monoidal.I GrpS GrpMon = Grp_trivial := eq_refl.

(** ** Abelian groups / ** 阿贝尔群 *)

Definition AbelianGrp (G : GrpS) : Type :=
  ∀ a b : carrier G, grp_mul G a b ≈ grp_mul G b a.

(* * ** Half (b): a group object in Grp is abelian / * ** 半 (b)：Grp 中的一个群对象是阿贝尔群 *)

Section GroupObjectInGrp.

Context (G : GrpS).
Context (GO : @GroupObject GrpS GrpCM G).

Definition gob_monoid : @MonoidObject GrpS GrpMon G :=
  @groupobject_is_monoid GrpS GrpCM G GO.

(*
 The three structure morphisms, read elementwise.  [gmul2] is the SECOND
 multiplication -- the internal one -- as opposed to [grp_mul G], which
 is the group's own. 

 --------
 三个结构态射，按元素读取。[gmul2] 是第二种乘法——内部的乘法——与 [grp_mul G] 不同，后者是群本身的乘法。
*)
Definition gmul2 (a b : carrier G) : carrier G :=
  grp_map (@mappend GrpS GrpMon G gob_monoid) (a, b).

Definition gunit2 : carrier G :=
  grp_map (@mempty GrpS GrpMon G gob_monoid) ttt.

Definition ginv2 (a : carrier G) : carrier G :=
  grp_map (@Category.Structure.Group.inverse GrpS GrpCM G GO) a.

(*
 Input 1 of 5 to Eckmann-Hilton: [gmul2] respects [≈], because the
 underlying [SetoidMorphism] does and the product setoid's equivalence
 is componentwise.  Kept a plain [Lemma] rather than an [Instance]: it is
 passed explicitly to the [eh_*] lemmas, and registering a [Proper] for
 a projection of a variable would only slow resolution. 

 --------
 对 Eckmann-Hilton 的输入 1/5：[gmul2] 遵循 [≈]，因为基础的 [SetoidMorphism] 遵循，并且乘积等价类的等价关系是按分量计算的。保留了一个普通的 [Lemma] 而不是 [Instance]：它被显式传递到 [eh_*] 引理中，并且为变量的投影注册一个 [Proper] 只会减慢求解速度。
*)
Lemma gmul2_respects : Proper (equiv ==> equiv ==> equiv) gmul2.
Proof.
  intros a a' Ha b b' Hb.
  unfold gmul2.
  apply proper_morphism.
  split; assumption.
Qed.

(*
 Inputs 2 and 3: the two unit laws.  These ARE [mempty_left] and
 [mempty_right] read at a point; the unitors of [CC_Monoidal] are the
 transparent cartesian projections, so nothing else is needed. 

 --------
 输入2和3：两个单位律。这些是[mempty_left]和[mempty_right]在某一点的读值；[CC_Monoidal]的单位元是透明的笛卡尔投影，因此不需要其他东西。
*)
Lemma gmul2_unit_left (a : carrier G) : gmul2 gunit2 a ≈ a.
Proof. exact (@mempty_left GrpS GrpMon G gob_monoid (ttt, a)). Qed.

Lemma gmul2_unit_right (a : carrier G) : gmul2 a gunit2 ≈ a.
Proof. exact (@mempty_right GrpS GrpMon G gob_monoid (a, ttt)). Qed.

(*
 Input 4, THE CRUX.  [mappend] is a morphism of Grp, so it is a group
 homomorphism out of the direct product; its [grp_map_mul] clause,
 instantiated at the pairs [(a, c)] and [(b, d)], IS the interchange law
 in exactly the orientation Theory/EckmannHilton.v states it.  No
 tactic, no reassociation, no middle-two shuffling: the swap lives in
 the choice of pairs. 

 --------
 输入 4，核心。[mappend] 是 Grp 的一个态射，所以它是从直积出来的群同态；它的 [grp_map_mul] 条款，在配对 [(a, c)] 和 [(b, d)] 处实例化，就是交换律，正如 Theory/EckmannHilton.v 所说明的方向。没有策略，没有重新结合，没有中间两个元素的调整：交换存在于配对的选择中。
*)
Lemma gob_interchange (a b c d : carrier G) :
  gmul2 (grp_mul G a b) (grp_mul G c d)
    ≈ grp_mul G (gmul2 a c) (gmul2 b d).
Proof.
  exact (grp_map_mul (@mappend GrpS GrpMon G gob_monoid) (a, c) (b, d)).
Qed.

(*
 Input 5 is [grp_mul G]'s own unit and respectfulness data, which
 Instance/Grp.v already supplies: [grp_mul_respects] is a field,
 [grp_mul_unit_l] is a field, and [grp_mul_unit_r] is derived there. 

 --------
 输入5是[grp_mul G]自身的单位和尊重数据，而实例/组.v已经提供：[grp_mul_respects]是一个字段，[grp_mul_unit_l]是一个字段，[grp_mul_unit_r]是从中派生的。
*)

(* Eckmann-Hilton, output 1: the two units coincide. / 埃克曼-希尔顿，输出1：两个单位重合。 *)
Theorem gob_units_agree : gunit2 ≈ grp_unit G.
Proof.
  exact (eh_units gmul2 (grp_mul G) gunit2 (grp_unit G)
           gmul2_respects (grp_mul_respects G)
           gmul2_unit_left gmul2_unit_right
           (grp_mul_unit_l G) (grp_mul_unit_r G)
           gob_interchange).
Qed.

(* Output 2: the two multiplications coincide. / 输出2：这两个乘法结果一致。 *)
Theorem gob_mul_agrees (a b : carrier G) : gmul2 a b ≈ grp_mul G a b.
Proof.
  exact (eh_ops gmul2 (grp_mul G) gunit2 (grp_unit G)
           gmul2_respects (grp_mul_respects G)
           gmul2_unit_left gmul2_unit_right
           (grp_mul_unit_l G) (grp_mul_unit_r G)
           gob_interchange a b).
Qed.

(* Output 3, the internal reading of commutativity. / 输出 3，交换性的内部读数。 *)
Theorem gob_mul_comm (a b : carrier G) : gmul2 a b ≈ gmul2 b a.
Proof.
  exact (eh_comm gmul2 (grp_mul G) gunit2 (grp_unit G)
           gmul2_respects (grp_mul_respects G)
           gmul2_unit_left gmul2_unit_right
           (grp_mul_unit_l G) (grp_mul_unit_r G)
           gob_interchange a b).
Qed.

(* THE HEADLINE of half (b): the group's OWN multiplication is commutative. This is [eh_g_comm], the [g]-side reading, which is what a consumer holding only [grp_mul G] wants. / 半标题（b）：该群体自身的乘法是交换的。这是 [eh_g_comm]，[g] 方向的阅读，这正是只持有 [grp_mul G] 的消费者想要的。 *)
Theorem group_object_abelian : AbelianGrp G.
Proof.
  exact (eh_g_comm gmul2 (grp_mul G) gunit2 (grp_unit G)
           gmul2_respects (grp_mul_respects G)
           gmul2_unit_left gmul2_unit_right
           (grp_mul_unit_l G) (grp_mul_unit_r G)
           gob_interchange).
Qed.

(* The two inverse laws of [GroupObject], read at a point. [∆] copies and [eliminate] discards, so both sides reduce to elementwise statements about [gmul2], [ginv2] and [gunit2]. / [GroupObject] 的两个逆律，在一点处读取。[∆] 复制，而 [eliminate] 丢弃，所以两边都归约为关于 [gmul2]、[ginv2] 和 [gunit2] 的元素级陈述。 *)
Lemma gob_inv_left (a : carrier G) : gmul2 (ginv2 a) a ≈ gunit2.
Proof. exact (@left_inverse GrpS GrpCM G GO a). Qed.

Lemma gob_inv_right (a : carrier G) : gmul2 a (ginv2 a) ≈ gunit2.
Proof. exact (@right_inverse GrpS GrpCM G GO a). Qed.

(*
 Eckmann-Hilton says nothing about inversion, but once the two
 multiplications and the two units have been identified, the group
 object's inversion is a left inverse for the group's own
 multiplication, and Instance/Grp.v's [grp_inv_unique_l] finishes. 

 --------
 Eckmann-Hilton 对反演没有任何说明，但一旦两个乘法和两个单位被识别出来，群对象的反演就是该群自身乘法的左逆，而 Instance/Grp.v 的 [grp_inv_unique_l] 就完成了。
*)
Theorem gob_inv_agrees (a : carrier G) : ginv2 a ≈ grp_inv G a.
Proof.
  apply grp_inv_unique_l.
  rewrite <- gob_mul_agrees.
  rewrite gob_inv_left.
  apply gob_units_agree.
Qed.

(*
 “Every group object in Grp arises this way”, packaged: all three
 structure morphisms are the group's own. 

 --------
 “Grp 中的每个群对象都是通过这种方式产生的”，打包：所有三种结构态射都是群自身的。
*)
Definition group_object_structure_forced :
  (∀ a b : carrier G, gmul2 a b ≈ grp_mul G a b)
    ∧ (gunit2 ≈ grp_unit G)
    ∧ (∀ a : carrier G, ginv2 a ≈ grp_inv G a) :=
  (gob_mul_agrees, (gob_units_agree, gob_inv_agrees)).

End GroupObjectInGrp.

(* * ** Uniqueness of the group-object structure / * ** 群-对象结构的唯一性 *)

(*
 Because every group-object structure on [G] is [G]'s own structure,
 any two of them agree.  This is the content of “arises this way” that a
 bare biconditional does not carry. 

 --------
 因为在 [G] 上的每一个群-对象结构都是 [G] 自身的结构，所以它们任意两个是一致的。这就是“以这种方式产生”的内容，而一个单纯的双条件语句并不包含这一点。
*)

Theorem group_object_mul_unique (G : GrpS)
        (GO GO' : @GroupObject GrpS GrpCM G) (a b : carrier G) :
  gmul2 G GO a b ≈ gmul2 G GO' a b.
Proof.
  rewrite gob_mul_agrees.
  symmetry.
  apply gob_mul_agrees.
Qed.

Theorem group_object_unit_unique (G : GrpS)
        (GO GO' : @GroupObject GrpS GrpCM G) :
  gunit2 G GO ≈ gunit2 G GO'.
Proof.
  rewrite gob_units_agree.
  symmetry.
  apply gob_units_agree.
Qed.

Theorem group_object_inverse_unique (G : GrpS)
        (GO GO' : @GroupObject GrpS GrpCM G) (a : carrier G) :
  ginv2 G GO a ≈ ginv2 G GO' a.
Proof.
  rewrite gob_inv_agrees.
  symmetry.
  apply gob_inv_agrees.
Qed.

(* * ** Half (a): an abelian group is a group object in Grp / * ** 半 (a)：阿贝尔群是在 Grp 中的群对象 *)

Section AbelianIsGroupObject.

Context (G : GrpS).
Context (HA : AbelianGrp G).

(*
 The multiplication as a morphism of Grp.  The only obligation with
 content is [grp_map_mul], which is the middle-four interchange
 [(a·c)·(b·d) ≈ (a·b)·(c·d)]; commutativity is spent there exactly
 once, on the inner pair. 

 --------
 作为群的态射的乘法。唯一具有内容的义务是 [grp_map_mul]，它是中间四交换 [(a·c)·(b·d) ≈ (a·b)·(c·d)]；交换性正好在那里使用了一次，在内部对上。
*)
Definition ab_mappend : Grp_product G G ~{GrpS}~> G.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom (Grp_product G G) G
       {| morphism := fun p => grp_mul G (fst p) (snd p) |} _ _).
  - intros p q Hpq.
    destruct Hpq as [H1 H2]; simpl in *.
    now rewrite H1, H2.
  - simpl.
    apply grp_mul_unit_l.
  - intros [a b] [c d]; simpl.
    rewrite !grp_mul_assoc.
    apply grp_mul_respects; [reflexivity |].
    rewrite <- !grp_mul_assoc.
    apply grp_mul_respects; [| reflexivity].
    apply HA.
Defined.

(*
 Inversion as a morphism of Grp.  Instance/Grp.v's [grp_inv_mul] gives
 the ANTIhomomorphism law [(a·b)⁻¹ ≈ b⁻¹·a⁻¹]; commutativity is spent
 exactly once, turning it into a homomorphism law.
 (Instance/Grp.v's [Grp_inv_to]
 already packages inversion as a morphism into the OPPOSITE group, which
 needs no hypothesis; that is a different arrow and is not reused.) 

 --------
 作为群的态射的逆元。Instance/Grp.v 中的 [grp_inv_mul] 给出了 ANTIhomomorphism 定律 [(a·b)⁻¹ ≈ b⁻¹·a⁻¹]；交换性恰好使用了一次，将其转变为同态定律。（Instance/Grp.v 中的 [Grp_inv_to] 已经将逆元封装为到对偶群的态射，这不需要假设；那是一条不同的箭头，并且不会被重用。）
*)
Definition grp_ab_inverse : G ~{GrpS}~> G.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom G G {| morphism := grp_inv G |} _ _).
  - intros a b Hab.
    now rewrite Hab.
  - apply grp_inv_unit.
  - intros a b; simpl.
    rewrite grp_inv_mul.
    apply HA.
Defined.

(*
 The underlying monoid object.  The unit morphism is REUSED, not built:
 [Grp_zero_hom G] is already the constant-at-the-unit homomorphism out
 of the trivial group, and the trivial group is definitionally the
 tensor unit ([grp_tensor_unit_is_trivial] above).  All three laws are
 pointwise readings of Instance/Grp.v's own group laws; none of them
 spends commutativity. 

 --------
 底层的幺半群对象。单位态射是重用的，不是构建的：
 [Grp_zero_hom G] 已经是从平凡群到单位的常值同态，而平凡群在定义上就是张量单位（上面的 [grp_tensor_unit_is_trivial]）。三个法则都是 Instance/Grp.v 自身群法则的逐点解读；它们都没有使用交换律。
*)
Definition ab_MonoidObject : @MonoidObject GrpS GrpMon G.
Proof.
  unshelve notypeclasses refine
    (@Build_MonoidObject GrpS GrpMon G (Grp_zero_hom G) ab_mappend _ _ _).
  - intros [u a]; simpl.
    apply grp_mul_unit_l.
  - intros [a u]; simpl.
    apply grp_mul_unit_r.
  - intros [[a b] c]; simpl.
    apply grp_mul_assoc.
Defined.

(*
 THE HEADLINE of half (a).  Both inverse laws are [grp_mul_inv_l] and
 [grp_mul_inv_r] read at a point: [∆] copies, [eliminate] discards, and
 the right-hand side [mempty ∘ eliminate] is the constant-at-the-unit
 endomorphism. 

 --------
 （a）部分的标题。两个逆定律是 [grp_mul_inv_l] 和 [grp_mul_inv_r]，在一点上读作：[∆] 复制，[eliminate] 丢弃，而右边的 [mempty ∘ eliminate] 是单位端的不变量自同态。
*)
Definition abelian_GroupObject : @GroupObject GrpS GrpCM G.
Proof.
  unshelve notypeclasses refine
    (@Build_GroupObject GrpS GrpCM G ab_MonoidObject grp_ab_inverse _ _).
  - intro a; simpl.
    apply grp_mul_inv_l.
  - intro a; simpl.
    apply grp_mul_inv_r.
Defined.

End AbelianIsGroupObject.

(** ** Mac Lane's Exercise 4 / ** 马克·莱恩练习 4 *)

(* [↔] is Lib's Type-valued [iffT] (Lib/Foundation.v), which is what the two sides need: [AbelianGrp G] is a family of [≈]-proofs and [GroupObject G] is data, so neither is a [Prop]. / [↔] 是 Lib 的类型值 [iffT]（Lib/Foundation.v），这正是双方所需的：[AbelianGrp G] 是一族 [≈] 证明，而 [GroupObject G] 是数据，因此两者都不是 [Prop]。 *)
Definition abelian_iff_group_object (G : GrpS) :
  AbelianGrp G ↔ @GroupObject GrpS GrpCM G :=
  (abelian_GroupObject G, group_object_abelian G).

(* The exercise, packaged: the biconditional together with the clause that makes the backward direction say “arises this way” rather than merely “exists”. / 练习，打包：双条件连同使反向表达说“这样产生”而不仅仅是“存在”的从句。 *)
Definition maclane_III_6_ex4 (G : GrpS) :
  (AbelianGrp G ↔ @GroupObject GrpS GrpCM G)
    ∧ (∀ GO : @GroupObject GrpS GrpCM G,
         (∀ a b : carrier G, gmul2 G GO a b ≈ grp_mul G a b)
           ∧ (gunit2 G GO ≈ grp_unit G)
           ∧ (∀ a : carrier G, ginv2 G GO a ≈ grp_inv G a)) :=
  (abelian_iff_group_object G, group_object_structure_forced G).

(* * ** Strengths, measured strict-first / * ** 优点，严格优先测量 *)

(*
 AbelianGrp group to group object and back: all three operations return at
 LEIBNIZ equality.  The structure built in half (a) has [grp_mul G],
 [grp_unit G] and [grp_inv G] literally inside it, and the pair
 projections reduce by iota, so these need no proof. 

 --------
 AbelianGrp 群到群对象再返回：所有三个操作在 LEIBNIZ 等式下返回。半部分 (a) 构建的结构字面上包含 [grp_mul G]、[grp_unit G] 和 [grp_inv G]，并且对投影通过 iota 化简，因此这些不需要证明。
*)

Example abelian_roundtrip_mul (G : GrpS) (HA : AbelianGrp G)
        (a b : carrier G) :
  gmul2 G (abelian_GroupObject G HA) a b = grp_mul G a b := eq_refl.

Example abelian_roundtrip_unit (G : GrpS) (HA : AbelianGrp G) :
  gunit2 G (abelian_GroupObject G HA) = grp_unit G := eq_refl.

Example abelian_roundtrip_inv (G : GrpS) (HA : AbelianGrp G)
        (a : carrier G) :
  ginv2 G (abelian_GroupObject G HA) a = grp_inv G a := eq_refl.

(*
 Group object to abelian group and back: only [≈].  The obstruction is
 NOT rebuilt law fields -- it is that [gmul2 G GO] projects a VARIABLE
 [GO], so no reduction is available on that side at all.  Probes 3 and 5
 pin the two strict failures. 

 --------
 将群对象转换为交换群再转换回去：只有 [≈]。障碍不是重建律域——而是 [gmul2 G GO] 投射了一个变量 [GO]，因此在那一边根本没有可用的化简。探针 3 和 5 确定了两个严格的失败。
*)

Theorem group_object_roundtrip_mul (G : GrpS)
        (GO : @GroupObject GrpS GrpCM G) (a b : carrier G) :
  gmul2 G (abelian_GroupObject G (group_object_abelian G GO)) a b
    ≈ gmul2 G GO a b.
Proof.
  symmetry.
  apply gob_mul_agrees.
Qed.

Theorem group_object_roundtrip_unit (G : GrpS)
        (GO : @GroupObject GrpS GrpCM G) :
  gunit2 G (abelian_GroupObject G (group_object_abelian G GO))
    ≈ gunit2 G GO.
Proof.
  symmetry.
  apply gob_units_agree.
Qed.

Theorem group_object_roundtrip_inv (G : GrpS)
        (GO : @GroupObject GrpS GrpCM G) (a : carrier G) :
  ginv2 G (abelian_GroupObject G (group_object_abelian G GO)) a
    ≈ ginv2 G GO a.
Proof.
  symmetry.
  apply gob_inv_agrees.
Qed.

(** ** Non-vacuity / ** 非空性 *)

(*
 The degenerate case first, and proved degenerate: the trivial group is
 abelian, so it carries a group-object structure, but every pair of its
 elements is identified, so nothing about it separates anything. 

 --------
 首先是退化情况，并且已经证明是退化的：平凡群是阿贝尔的，因此它具有群对象的结构，但它的每一对元素都是相同的，所以没有什么能够将它的任何东西区分开来。
*)

Lemma trivial_abelian : AbelianGrp Grp_trivial.
Proof.
  intros a b.
  reflexivity.
Qed.

Definition trivial_GroupObject : @GroupObject GrpS GrpCM Grp_trivial :=
  abelian_GroupObject Grp_trivial trivial_abelian.

Lemma trivial_GroupObject_degenerate (a b : carrier Grp_trivial) : a ≈ b.
Proof.
  destruct a, b.
  reflexivity.
Qed.

(* Z/2, Instance/Grp.v's own witness, reused rather than rebuilt. / Z/2，Instance/Grp.v 自有的见证者，被重复使用而不是重建。 *)

Lemma Z2_abelian : AbelianGrp Z2.
Proof.
  intros a b; simpl.
  destruct a, b; reflexivity.
Qed.

Definition Z2_GroupObject : @GroupObject GrpS GrpCM Z2 :=
  abelian_GroupObject Z2 Z2_abelian.

(* The group-object structure on Z/2 COMPUTES. / 在 Z/2 上的群-对象结构进行计算。 *)

Example Z2_gob_mul_tt : gmul2 Z2 Z2_GroupObject true true = false :=
  eq_refl.

Example Z2_gob_mul_tf : gmul2 Z2 Z2_GroupObject true false = true :=
  eq_refl.

Example Z2_gob_unit : gunit2 Z2 Z2_GroupObject = false := eq_refl.

Example Z2_gob_inv : ginv2 Z2 Z2_GroupObject true = true := eq_refl.

(*
 And it is not degenerate: the multiplication is not constant, and the
 carrier has two provably distinct elements ([Z2_nontrivial] is
 Instance/Grp.v's). 

 --------
 它不是退化的：乘法不是恒定的，并且载体有两个可证明不同的元素（[Z2_nontrivial] 是 Instance/Grp.v 的）。
*)

Lemma Z2_gob_not_constant :
  gmul2 Z2 Z2_GroupObject true true ≈ gmul2 Z2 Z2_GroupObject true false
    → False.
Proof.
  simpl.
  discriminate.
Qed.

Lemma Z2_GroupObject_nondegenerate :
  (∀ a b : carrier Z2, a ≈ b) → False.
Proof.
  intro Hall.
  exact (Z2_nontrivial (Hall true false)).
Qed.

(*
 THE EXCLUSION.  A theorem that classifies is worthless if it excludes
 nothing, so here is a group that provably carries NO group-object
 structure: the symmetric group on three letters, Instance/Grp/Epi.v's
 [GrpSym3], with [sym3_s] and [sym3_a] two transpositions.  The two
 composites differ already at the first letter, and [sym3_rel] at two
 distinct letters reduces to [False], so the refutation is a single
 application. 

 --------
 排除定理。如果一个定理将对象分类但排除了没有任何对象，那么它是毫无价值的，所以这里有一个证明上不包含任何群对象结构的群：三个字母的对称群，Instance/Grp/Epi.v 的 [GrpSym3]，其中 [sym3_s] 和 [sym3_a] 是两个换位。两个复合在第一个字母就已经不同，而 [sym3_rel] 在两个不同字母上简化为 [False]，因此反证只需一次应用。
*)

Definition Sym3 : GrpS := GrpSym3.

Lemma Sym3_not_abelian : AbelianGrp Sym3 → False.
Proof.
  intro H.
  exact (H sym3_s sym3_a sym3_l0).
Qed.

Theorem Sym3_no_group_object : @GroupObject GrpS GrpCM Sym3 → False.
Proof.
  intro GO.
  exact (Sym3_not_abelian (group_object_abelian Sym3 GO)).
Qed.

(** ** Probes *)

(*
 SIX negatives of THREE kinds, each paired with a positive control that
 names every constant the negative names, plus an instrument check.
 Each [Fail] below was stripped once and its error read: the kinds are
 genuinely distinct, and the two universe negatives report their failure
 AT [Grp_Terminal] in both cases.  (CORRECTION, #450: this line said
 “Five negatives” before #450, one short already: at the parent commit
 e139ecfb the file had six guarded negatives, two universe, one typing
 and three conversion.  And the two universe negatives are controls
 since #450 lifted the donor pin, so what remains is FOUR negatives of
 TWO kinds: the typing negative and the three conversion negatives.
 Counted: five guarded commands in this file, those four and the
 instrument, and seven positive controls, the five [ctrl_] constants
 and the two [Check]s that replaced the universe negatives.)

 A PARSE error cannot be captured by [Fail] -- the file aborts even
 inside it -- so the notation findings recorded in the header above are
 prose, not probes. 

 --------
 三类六个负样，每个都配有一个正对照，正对照会命名负样所命名的每一个常量，以及一个仪器检查。下面的每个 [Fail] 都只剥离过一次并读取过其错误：这些种类确实是不同的，并且两个宇宙负样在两种情况下都在 [Grp_Terminal] 处报告了它们的失败。（更正，#450：在 #450 之前这一行写的是“五个负样”，已经少了一个：在父提交 e139ecfb 中，该文件有六个受保护的负样，两个宇宙负样，一个类型负样和三个转换负样。而且这两个宇宙负样是对照，因为 #450 取消了捐赠针脚，所以剩下的是两类四个负样：类型负样和三个转换负样。）统计：此文件中有五个受保护的命令，那四个命令和仪器，以及七个阳性对照，五个 [ctrl_] 常数和替换了宇宙阴性值的两个 [Check]。)

 解析错误无法被 [Fail] 捕获——即使在其内部文件也会中止——所以上面标题中记录的符号发现是散文，而不是探针。
*)

Section ProbeUniversePin.

Universe pu ph.
Constraint Set < ph.

(*
 Positive controls.  The first two say that at a hom universe strictly
 above [Set] the category Grp still elaborates and is still cartesian --
 so neither [Grp] nor [Grp_Cartesian] is the cause.  The third is the
 sharp contrast for the negative that followed until #450: the SAME
 constant [Grp_Terminal] is accepted at [GrpS], where the hom universe
 IS [Set], and was rejected one line later where it is not.  Since #450
 it is accepted there too. 

 --------
 阳性对照。前两个表明，在一个严格大于 [Set] 的 Hom 宇宙中，Grp 类别仍然可以展开，并且仍然是笛卡尔的——所以 [Grp] 和 [Grp_Cartesian] 都不是原因。第三个则是之前负例直到 #450 的明显对照：相同的常数 [Grp_Terminal] 在 [GrpS] 被接受，其中 Hom 宇宙是 [Set]，而在下一行当它不是时被拒绝。自 #450 起，它在那里也被接受。
*)
Definition ctrl_probe_category : Category := Grp@{pu ph}.

Definition ctrl_probe_cartesian : @Cartesian Grp@{pu ph} := Grp_Cartesian.

Definition ctrl_probe_terminal : @Terminal GrpS := Grp_Terminal.

(*
 FORMABILITY (universe), 1 of 2, a CONTROL since #450.  Until then this
 was a guarded negative named [probe_terminal_pinned], refused with “The term
 Grp_Terminal has type Terminal@{_ Set} while it is expected to have
 type Terminal@{pu ph} (universe inconsistency: Cannot enforce Set =
 ph).”  #450 annotated [Grp_Terminal] in place, the build reported the
 guarded command accepted, and the command is kept as a [Check] so that
 no constant is added to the file's count. 

 --------
 可形成性（宇宙），2 中的 1，自 #450 起为一个控制。在此之前，这是一个受保护的负命令，名为 [probe_terminal_pinned]，被拒绝，提示“术语 Grp_Terminal 的类型为 Terminal@{_ Set}，而期望类型为 Terminal@{pu ph}（宇宙不一致：无法强制 Set = ph）。”#450 将 [Grp_Terminal] 注释到原位，构建报告受保护命令已被接受，并且该命令被保留为 [Check]，因此文件的常量计数未增加。
*)
Check (Grp_Terminal : @Terminal Grp@{pu ph}).

(*
 FORMABILITY (universe), 2 of 2, a CONTROL since #450.  The rejection
 used to propagate to the cartesian monoidal structure, reported at
 [Grp_Terminal]; since #450 the structure is formable at [Grp@{pu ph}]. 

 --------
 可塑性（宇宙），2之2，自#450起的控制。拒绝以前传播到笛卡尔单体结构，在[Grp_Terminal]报告；自#450起，该结构在[Grp@{pu ph}]可塑。
*)
Check (@CC_CartesianMonoidal Grp@{pu ph} Grp_Cartesian Grp_Terminal
       : @CartesianMonoidal Grp@{pu ph}).

End ProbeUniversePin.

(*
 TYPING.  [GroupObject] wants a [CartesianMonoidal]; [GrpMon] is only a
 [Monoidal].  “The term GrpMon has type Monoidal while it is expected to
 have type CartesianMonoidal.” 

 --------
 输入。[GroupObject] 想要一个 [CartesianMonoidal]；[GrpMon] 仅仅是一个 [Monoidal]。“术语 GrpMon 的类型是 Monoidal，但预期类型是 CartesianMonoidal。”
*)
Definition ctrl_probe_groupobject : Type := @GroupObject GrpS GrpCM Z2.

Fail Definition probe_needs_cartesian : Type :=
  @GroupObject GrpS GrpMon Z2.

(*
 CONVERSION, 1 of 3 (labelled “1 of 2” before #450, although the third
 was already below).  The two multiplications agree at [≈] and NOT on
 the nose: [gmul2 G GO] projects a variable [GO], so nothing reduces.
 “cannot unify gmul2 G GO a b and grp_mul G a b”. 

 --------
 转换，3 中的 1（在 #450 之前标记为“2 中的 1”，尽管第三个已经在下面）。两个乘法在 [≈] 上一致，而不是完全一致：[gmul2 G GO] 投影了一个变量 [GO]，因此没有任何简化。
 “无法统一 gmul2 G GO a b 和 grp_mul G a b”。
*)
Example ctrl_probe_mul_agrees (G : GrpS)
        (GO : @GroupObject GrpS GrpCM G) (a b : carrier G) :
  gmul2 G GO a b ≈ grp_mul G a b := gob_mul_agrees G GO a b.

Fail Example probe_mul_strict (G : GrpS)
        (GO : @GroupObject GrpS GrpCM G) (a b : carrier G) :
  gmul2 G GO a b = grp_mul G a b := eq_refl.

(*
 CONVERSION, 2 of 3 (labelled “2 of 2” before #450, likewise).  The
 whole-record round trip through both halves is
 refuted for the same reason: “cannot unify
 abelian_GroupObject G (group_object_abelian G GO) and GO”.  What DOES
 hold is [group_object_roundtrip_mul] and its two siblings, at [≈].
 This is also why [abelian_iff_group_object] is a biconditional and not
 an isomorphism of types. 

 --------
 转换，3 中的第 2（在 #450 之前标为“2 of 2”，同样如此）。通过两个部分的整体记录往返由于相同的原因被否定：“无法统一 abelian_GroupObject G (group_object_abelian G GO) 和 GO”。真正成立的是 [group_object_roundtrip_mul] 及其两个同类，在 [≈] 处。这也是为什么 [abelian_iff_group_object] 是双条件而不是类型同构的原因。
*)
Fail Example probe_record_roundtrip (G : GrpS)
        (GO : @GroupObject GrpS GrpCM G) :
  abelian_GroupObject G (group_object_abelian G GO) = GO := eq_refl.

(*
 CONVERSION, 3 of 3.  The OTHER composite is refuted too, and this probe
 exists because an audit found the header claiming it was “pinned” when
 no negative mentioned [HA] at all: the round trip that starts from an
 [AbelianGrp] proof is likewise not the identity, so the biconditional is
 a biconditional in both directions and not an isomorphism of types.
 Every constant it names -- [AbelianGrp], [abelian_GroupObject],
 [group_object_abelian] -- is already named by a positive command above,
 so it needs no control of its own. 

 --------
 转换，第3部分，共3部分。另一个复合也被驳斥了，而且这个探针存在是因为审计发现头部声称它是“固定”的，而实际上没有任何负面信息提到[HA]：从[AbelianGrp]证明开始的往返过程同样不是恒等映射，因此双条件在两个方向上都是双条件，而不是类型的同构。它命名的每一个常量——[AbelianGrp]、[abelian_GroupObject]、[group_object_abelian]——都已经被上面一个正命令命名，所以它不需要自行控制。
*)
Fail Example probe_other_roundtrip (G : GrpS) (HA : AbelianGrp G) :
  group_object_abelian G (abelian_GroupObject G HA) = HA := eq_refl.

(*
 Instrument check: the [Fail] mechanism is live in this file, so the
 six negatives above (four since #450) are not passing vacuously.
 Note that [1] parses as [terminal_obj] in [category_scope], which is
 why the check is written over [bool]. 

 --------
 仪器检查：[Fail] 机制在此文件中是活跃的，所以上面的六个否定（自 #450 起为四个）并不是虚假的通过。请注意，[1] 在 [category_scope] 中被解析为 [terminal_obj]，这就是为什么检查写在 [bool] 上的原因。
*)
Example eh_probe_instrument : true = true := eq_refl.

Fail Example probe_instrument_neg : true = false := eq_refl.
