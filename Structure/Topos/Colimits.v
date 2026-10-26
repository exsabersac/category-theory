Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Terminal.
Require Import Category.Theory.Equivalence.Pullback.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.Topos.
Require Import Category.Structure.Topos.Power.
Require Import Category.Structure.Topos.Monadic.
Require Import Category.Functor.Hom.Internal.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Comparison.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(*
 [Category.Functor.Opposite] opens [functor_scope], and
 [Category.Theory.Monad], which has no [Open Scope] of its own, carries it in
 by requiring that module; after either Require a bare [C^op] on a CATEGORY
 parses as [Opposite_Functor C] and is rejected with “The term C has type
 Category while it is expected to have type ?C ⟶ ?D”.  Reopening
 [category_scope] restores the reading this file wants.  A second hazard, met
 while building [EM_Terminal]: a [{| t_alg := … |}] record literal needs
 [Category.Monad.Algebra] REQUIRED EXPLICITLY -- requiring only
 [Category.Monad.Eilenberg.Moore], which uses the record, reports “t_alg: Not
 a projection”. 

 --------
 [Category.Functor.Opposite] 打开 [functor_scope]，以及 [Category.Theory.Monad]，它本身没有 [Open Scope]，通过要求该模块将其引入；在任一情况下，如果在 CATEGORY 上仅 Require 一个 [C^op]，会被解析为 [Opposite_Functor C] 并因“术语 C 的类型是 Category，而期望类型是 ?C ⟶ ?D”而被拒绝。重新打开 [category_scope] 会恢复该文件所需的读取。第二个风险出现在构建 [EM_Terminal] 时：一个 [{| t_alg := … |}] 记录字面量需要明确 REQUIRED 的 [Category.Monad.Algebra] —— 仅仅要求 [Category.Monad.Eilenberg.Moore]（它使用该记录）会报告 “t_alg: Not a projection”。
*)
Open Scope category_scope.

(*
 EVERY ELEMENTARY TOPOS HAS FINITE COLIMITS.

 nLab:      https://ncatlab.org/nlab/show/topos
 nLab:      https://ncatlab.org/nlab/show/Pare%27s+theorem
 Wikipedia: https://en.wikipedia.org/wiki/Topos
 Paper:     Paré, “Colimits in topoi”, Bulletin of the American
 Mathematical Society 80 (1974), pp. 556-561

 THREE BOOKS STATE THIS IN FOUR PLACES AND NONE OF THEM PROVES IT.

 Mac Lane, “Categories for the Working Mathematician”, 2nd ed., §IV.10,
 book p. 107 (`maclane:IV.10:remark2`), closes the topos section with:

 “The axioms for a topos have many useful consequences. For exam-
 ples, every topos has all finite colimits.”

 The Appendix “Foundations”, §App.1, book p. 290
 (`maclane:App.1:remark2`), singles out the initial object:

 “These axioms for a topos then hold for the category of sets. They
 have a number of strong consequences. For example, they give all
 finite cate- gorical products and pullbacks, as well as all finite
 coproducts, including an initial object 0, the empty set.”

 Awodey, “Category Theory” (1st ed., Carnegie Mellon pre-print,
 September 2005), §8.8, printed p. 210
 (`awodey:8.8:remark-topos-properties`), immediately after Definition
 8.16:

 “This compact definition proves to be amazingly rich in
 consequences: it can be shown for instance that topoi also have all
 finite colimits and that every slice category of a topos is again a
 topos. We refer the reader to the books by Mac Lane and Moerdijk,
 Johnstone, and McLarty for information on topoi, and here just give
 an example (albeit one the covers a very large number of cases).”

 Fong and Spivak, “Seven Sketches in Compositionality”, §7.2.1, printed
 p. 225 (`7sketches:7.2.1:remark-topos-properties`):

 “Although we will not prove it in this book, toposes are categories
 that are similar to Set in many ways. Here are some facts that are
 true of any topos E:
 1. E has all limits,
 2. E has all colimits,
 3. E is cartesian closed,
 4. E has epi-mono factorizations,
 5. E has a subobject classifier 1 --true--> Ω.”

 Mac Lane-Moerdijk, the reference Mac Lane §IV.10 and Awodey both send the
 reader to (the Appendix page and Seven Sketches name none), was NOT available
 here.  The proof below is Paré's, RECONSTRUCTED and CHECKED BY COMPILATION.

 THE ROUTE, in one paragraph.  The contravariant power-object functor
 P = Ω^(−) : E^op ⟶ E is self-adjoint on the right through the
 cartesian-closed [flip], with no subobject classifier consumed at that
 step (Structure/Topos/Power.v).  It is MONADIC: reflexive coequalizers
 in E^op are three lines of pre-existing reductions, P is faithful
 through the singleton map, P reflects isomorphisms because a topos is
 balanced, and P carries the equalizer of a co-reflexive pair to a SPLIT
 coequalizer -- direct image along a mono (no image factorization) for
 the two sections, Beck-Chevalley by pullback pasting for the fourth
 law.  Crude monadicity is then CONSUMED (Structure/Topos/Monadic.v's
 [power_object_monadic], through Monad/Monadicity/Crude.v's
 [crude_monadicity]).  So E^op is equivalent to the Eilenberg-Moore
 category of P ◯ P^op, whose terminal object and pullbacks are built
 here on the carriers and transported back along the equivalence.  In
 E^op a terminal object is an INITIAL object of E, a binary product is a
 COPRODUCT, an equalizer is a COEQUALIZER and a pullback is a PUSHOUT --
 all four by NOTATION or by a pre-existing one-line bridge.

 WHY THE ELEMENTARY ROUTE AND NOT THE [Limit] ROUTE.  The universe fact behind
 it is a MEASUREMENT, pinned in Test/ProbeToposColimits405.v; the conclusion
 drawn from it is an inference.  [Terminal_Limit] (Structure/Limit/Terminal.v)
 and [Cartesian_Limit] (Structure/Limit/Cartesian.v) are stated over
 [Category@{u Set Set}]: they pin the ambient category's hom AND proof
 universes to the literal [Set].  Going through them would have made “every
 elementary topos has finite colimits” a theorem about Set-homed toposes only
 -- an inference from those two refusals and not a compiled comparison, since
 the [Limit] route was not built.  So no [Cone], [Limit], [Colimit] or
 [Cocomplete] token occurs outside a comment in Structure/Topos/Power.v,
 Structure/Topos/Monadic.v, Theory/Equivalence/Pullback.v or this file --
 MEASURED, and with one stated exception: the module path
 [Category.Structure.Limit.Preservation] appears in one [Require] of
 Structure/Topos/Monadic.v, where it supplies [ReflectsIsos] and no limit
 vocabulary at all.  Correspondingly no [Cocomplete] claim is made: the
 theorem is exactly the four elementary generator records, packaged as
 [topos_has_finite_colimits].

 WHAT IS NEW TO THE TREE BEYOND THE ISSUE'S ASK.  A topos is balanced; the
 singleton map and its monicity; the direct image along a mono and its
 retraction law; Beck-Chevalley for subobjects along a pullback square; the
 power functor, its self-adjointness and its monadicity; pullbacks transported
 along an equivalence of categories (Theory/Equivalence/Pullback.v -- MEASURED
 with the five new files excluded, a whole-tree search for the six names
 [Terminal_transport], [Initial_transport], [Cartesian_transport],
 [Cocartesian_transport], [HasEqualizers_transport] and
 [HasPullbacks_transport] returns 8 lines, all in
 Theory/Equivalence/Terminal.v, naming [Terminal_transport],
 [Initial_transport] and their two object readbacks; read that as a NAME
 search, since other structures ARE carried across an equivalence under other
 names -- Instance/Proset/Limit.v's [Complete_equivalence_invariant] and
 [Cocomplete_equivalence_invariant], Theory/Equivalence/Monoidal.v's
 [Transported_Monoidal], Theory/Equivalence/Adjunction.v's
 [Transported_Adjunction] -- so what is new is the PULLBACK case, not the
 pattern); and, at the instance level, the FIRST [HasCoequalizers FinSet] the
 tree has ever had (in Test/ProbeToposColimits405.v -- no .v file declares a
 constant of that type, and the only two .v hits for the phrase
 [HasCoequalizers FinSet] elsewhere are NOT-DELIVERED notes in
 Instance/Sets/Coequalizer.v and Instance/Sets/Coequalizer/Interconnect.v
 about what those two files do not build, which therefore do not go stale).

 NO CONSTANT DECLARED HERE IS REGISTERED AS AN [Instance].  A chosen colimit
 must not become globally resolvable: the delivered constants are plain
 [Definition]s (with [Example]s, [Lemma]s and one [Program Definition] beside
 them), so a consumer passes the topos explicitly, exactly as
 Instance/FinSet/Topos.v's [FinSet_Topos] is passed explicitly.  The one
 registration below is the [Existing Instance pow_monad] of the section
 preamble, declared local to this section and there only so that [t_alg],
 [ret] and [join] resolve.

 NOT DELIVERED.  No [Cocomplete] and no infinite colimits.  No
 [Limit]/[Colimit]-shaped statement and no finite-shape induction -- both the
 colimit theorem and Structure/Topos/Monadic.v's [topos_finitely_complete] are
 at GENERATOR level, and a [Limit K]-for-every-finite-shape-J statement is
 still not claimed anywhere in this library.  No image factorization and no
 direct image along a general arrow (only along monos).  No route through
 Beck's precise theorem.  No naturality of any identification.  No [eq_refl]
 readback at FinSet: the agreement with FinSet's computable colimits is
 delivered at [≅]; the [eq_refl] form for the initial object is pinned as a
 CONVERSION refusal in the probe (the coproduct and pushout readbacks are
 delivered at [≅] only, and no [eq_refl] form of them is attempted); and its
 cause is NOT isolated -- the derived object is the quasi-inverse
 [Crude_Inverse] at [EM_Terminal]'s object ([topos_Initial_obj] reads that
 back at [eq_refl]), i.e. the reflexive coequalizer Monad/Monadicity/Crude.v
 chooses through [op_HasReflexiveCoequalizers] and [topos_HasEqualizers], a
 chain that never consumes [PowF_ReflectsIsos] ([Crude_Inverse] takes no
 [ReflectsIsos] argument at all; in Crude.v [refl] enters only
 [crude_theta_iso] and one [Proof using]), and no experiment names the
 constant that blocks the reduction.  No second concrete topos.  Nothing about
 slices of a topos (Awodey's other half), nor about epi-mono factorization
 (Seven Sketches' clause 4), both of which are separate obligations.

 Of this file's five [Defined] tokens, [em_pb_fst], [em_pb_snd] and
 [EM_Pullback] are LOAD-BEARING -- each flipped alone to [Qed] breaks the
 file, [em_pb_fst] and [em_pb_snd] at [EM_Pullback]'s own commuting-square
 obligation and [EM_Pullback] at its first readback, [EM_Pullback_carrier] --
 and [EM_Terminal]'s two data obligations are not, the file compiling
 unchanged with either flipped alone; the flip was run per token. 

 --------
 每个初等拓扑都有有限余极限。

 nLab:       https://ncatlab.org/nlab/show/topos 
 nLab:       https://ncatlab.org/nlab/show/Pare%27s+theorem 
 维基百科:   https://en.wikipedia.org/wiki/Topos 
 论文:       Paré, “Colimits in topoi”, 美国数学学会公报 80 (1974), 第556-561页

 三本书在四个地方陈述了这一点，但没有一本证明它。

 Mac Lane, “为工作数学家而作的范畴论”，第2版，§IV.10，书页107 (`maclane:IV.10:remark2`)，以如下内容结束了拓扑部分：

 “拓扑的公理有许多有用的结果。例如，每个拓扑都有所有有限余极限。”

 附录“基础”，§App.1，书页290 (`maclane:App.1:remark2`)，特别指出了初始对象：这些对拓扑的公理随后适用于集合的范畴。它们有许多强烈的推论。例如，它们给出了所有有限的范畴积和拉回，以及所有有限的余积，包括一个初始对象 0，即空集。这个紧凑的定义在后果上被证明极为丰富：例如，可以证明，上述范畴（topoi）也具有所有有限余极限，并且一个上范畴（topos）的每一个slice范畴再次是一个上范畴。关于上范畴的资料，我们建议读者参考Mac Lane和Moerdijk、Johnstone以及McLarty的书籍，这里仅给出一个例子（尽管这个例子覆盖了非常多的情况）。

 Fong 和 Spivak，《组合性的七个概述》，§7.2.1，印刷页225 (`7sketches:7.2.1:remark-topos-properties`)：“虽然我们在本书中不会证明它，但拓扑类是与集合在许多方面相似的范畴。以下是任何拓扑类 E 都成立的一些事实：
 1. E 拥有所有极限，
 2. E 拥有所有余极限，
 3. E 是笛卡尔闭范畴，
 4. E 拥有满射-单射分解，
 5. E 有一个子对象分类器 1 --true--> Ω。

 Mac Lane-Moerdijk，参考文献 Mac Lane §IV.10 和 Awodey 都将读者引导到（附录页和 Seven Sketches 均未命名），在这里不可用。下面的证明是 Paré 的，已重新构建并通过编译检查。路线，用一段话说明。逆变幂对象函子
 P = Ω^(−) : E^op ⟶ E 通过笛卡尔闭的 [flip] 在右侧自伴，不需要在该步骤中使用子对象分类器（Structure/Topos/Power.v）。它是单子性的：E^op 中的自反共等化子是三行已有的化简，P 通过单元素映射是忠实的，P 反映同构，因为拓扑是平衡的，并且 P 将共自反对的等化子映射为分裂共等化子——沿单态的直接像（没有像分解）用于两个截面，第四条公理通过拉回粘贴满足 Beck-Chevalley 条件。粗略的单子性随后被使用（Structure/Topos/Monadic.v 的 [power_object_monadic]，通过 Monad/Monadicity/Crude.v 的 [crude_monadicity]）。所以 E^op 等价于 P ◯ P^op 的 Eilenberg-Moore 范畴，其终对象和拉回在这里建立在载体上，并沿着等价关系传回。在 E^op 中，终对象是 E 的初对象，二元积是余积，相等化子是余相等化子，拉回是推出——所有四个都是通过符号或通过现有的一行桥完成的。为什么选择基本路线而不是 [Limit] 路线。其背后的宇宙事实是一个测量，记录在 Test/ProbeToposColimits405.v 中；由此得出的结论是一个推论。[Terminal_Limit]（Structure/Limit/Terminal.v）和 [Cartesian_Limit]（Structure/Limit/Cartesian.v）是建立在 [Category@{u Set Set}] 上的：它们将环境范畴的同态和证明宇宙固定到字面上的 [Set]。通过它们的话，“每个基本拓扑都有有限余积”将仅成为关于 Set-homed 拓扑的定理——这是从那两个拒绝中得出的推论，而不是一个编译的比较，因为 [Limit] 路线尚未建立。因此，除了在注释中之外，不存在 [Cone]、[Limit]、[Colimit] 或 [Cocomplete] 令牌出现在 Structure/Topos/Power.v、Structure/Topos/Monadic.v、Theory/Equivalence/Pullback.v 或本文件中——MEASURED，并且有一个明确说明的例外：模块路径 [Category.Structure.Limit.Preservation] 出现在 Structure/Topos/Monadic.v 的一个 [Require] 中，它提供了 [ReflectsIsos] 并且完全没有限制词汇。相应地，没有提出任何 [Cocomplete] 声明：该定理正好是作为 [topos_has_finite_colimits] 打包的四个基本生成器记录。在超出问题要求之外，树有什么新变化。一个拓扑是平衡的；单例映射及其单射性；沿单射的直接像及其收缩律；沿拉回方格的子对象的 Beck-Chevalley 定理；幂函子，其自伴性及其单子性质；沿范畴等价传送的拉回（Theory/Equivalence/Pullback.v -- 在排除五个新文件后测量，对六个名字 [Terminal_transport]、[Initial_transport]、[Cartesian_transport]、[Cocartesian_transport]、[HasEqualizers_transport] 和 [HasPullbacks_transport] 进行全树搜索返回 8 行，全部在 Theory/Equivalence/Terminal.v 中，命名为 [Terminal_transport]、[Initial_transport] 及其两个对象的读取返回；将其视为 NAME 搜索，因为其他结构在等价下会由其他名字传递 -- Instance/Proset/Limit.v 的 [Complete_equivalence_invariant] 和 [Cocomplete_equivalence_invariant]，Theory/Equivalence/Monoidal.v 的 [Transported_Monoidal]，Theory/Equivalence/Adjunction.v 的
 [Transported_Adjunction]  -- 新的部分是 PULLBACK 情况，而不是模式); 并且，在实例级别上，树有过的第一个 [HasCoequalizers FinSet]（在 Test/ProbeToposColimits405.v 中 -- 没有 .v 文件声明该类型的常量，并且该短语的唯一两个 .v 次数 [HasCoequalizers FinSet] 出现在 Instance/Sets/Coequalizer.v 和 Instance/Sets/Coequalizer/Interconnect.v 中的 NOT-DELIVERED 注释里，关于这两个文件没有构建的内容，因此不会过时）。这里没有声明的常量被注册为 [Instance]。所选择的余极限不能变为全局可解析：传递的常量是普通的 [Definition]（有 [Example]、[Lemma] 和一个 [Program Definition] 在它们旁边），所以消费者明确传递 topos，就像在 Instance/FinSet/Topos.v 中的 [FinSet_Topos] 被明确传递一样。下面的唯一注册是该节前言的 [Existing Instance pow_monad]，仅在本节本地声明，以便 [t_alg]、[ret] 和 [join] 得到解析。未交付。没有 [Cocomplete]，也没有无限余极限。没有 [Limit] / [Colimit] 形状的语句，也没有有限形状归纳——余极限定理和 Structure/Topos/Monadic.v 中的 [topos_finitely_complete] 都在生成器层面，并且库中仍未声称任何 [Limit K] 对每个有限形状 J 的语句。没有像的分解，也没有沿一般箭头的直接像（仅沿单射）。没有经过 Beck 精确定理的途径。没有任何识别的自然性。在 FinSet 上没有 [eq_refl] 的回读：与 FinSet 的可计算余极限的一致性在 [≅] 上传递；初始对象的 [eq_refl] 形式在探针中被固定为 CONVERSION 拒绝（只有在 [≅] 上传递余积和推出回读，并且没有尝试它们的 [eq_refl] 形式）；其原因未被隔离——导出的对象是 [Crude_Inverse] 在 [EM_Terminal] 的对象上的准逆（[topos_Initial_obj] 在 [eq_refl] 上回读），即自反的余等价器 Monad/Monadicity/Crude.v 通过 [op_HasReflexiveCoequalizers] 和 [topos_HasEqualizers] 选择的一条链，这条链从不消耗 [PowF_ReflectsIsos]（[Crude_Inverse] 完全不接受 [ReflectsIsos] 参数；在 Crude.v 中 [refl] 只进入 [crude_theta_iso] 和一个 [Proof using]），并且没有实验命名会阻止归约的常数。没有第二个具体拓扑。关于拓扑片（Awodey 的另一半）或关于 epi-mono 分解（《七个草图》第 4 条款）没有任何说明，这两者都是独立的义务。

 在这个文件的五个 [Defined] 令牌中，[em_pb_fst]、[em_pb_snd] 和 [EM_Pullback] 是承重的——每个单独翻转为 [Qed] 都会破坏文件，[em_pb_fst] 和 [em_pb_snd] 在 [EM_Pullback] 自身的交换方格义务处，以及 [EM_Pullback] 在它的第一次回读 [EM_Pullback_carrier] 时——而 [EM_Terminal] 的两个数据义务不是，单独翻转任何一个文件编译都不会改变；翻转是按每个令牌执行的。
*)

Section ToposColimits.

Context {C : Category}.
Context `{H : @ElementaryTopos C}.

Local Notation TT := (PowF ◯ Opposite_Functor PowF).
Local Notation EMT := (@EilenbergMoore C TT pow_monad).

(*
 The monad is not a registered instance -- a chosen monad structure
 must not become globally resolvable -- so it is made available to
 [t_alg], [ret] and [join] locally, for this section only. 

 --------
 该单子不是注册实例 —— 所选的单子结构不应变得全局可解析 —— 因此它仅在本节内局部提供给 [t_alg]、[ret] 和 [join]。
*)
#[local] Existing Instance pow_monad.

(** ** (A) The terminal algebra / **（A）终端代数 *)

(*
 The terminal object of C carries a unique algebra structure, and every
 algebra map into it is unique, both by [one_unique]. 

 --------
 C 的终端对象具有唯一的代数结构，并且根据 [one_unique]，指向它的每个代数映射都是唯一的。
*)
Program Definition EM_Terminal : @Terminal EMT := {|
  terminal_obj := (@terminal_obj C _; _)
|}.
Next Obligation.
  unshelve refine {| t_alg := one |}; apply one_unique.
Defined.
Next Obligation.
  unshelve refine {| t_alg_hom := one |}; apply one_unique.
Defined.
Next Obligation.
  destruct f, g; simpl; apply one_unique.
Qed.

(* * ** (B) Pullbacks of algebras, computed on carriers / * **（B）代数的回拉，在承载上计算 *)

Section EMPullback.

Context {xa ya za : EMT}.
Context (FF : xa ~{EMT}~> za) (GG : ya ~{EMT}~> za).

Definition em_pb : Pullback (t_alg_hom[FF]) (t_alg_hom[GG]) :=
  @pullback C _ _ _ _ (t_alg_hom[FF]) (t_alg_hom[GG]).

Definition em_pb_carrier : C := Pull _ _ em_pb.
Definition em_pb_p1 : em_pb_carrier ~> ``xa := pullback_fst _ _ em_pb.
Definition em_pb_p2 : em_pb_carrier ~> ``ya := pullback_snd _ _ em_pb.

(*
 The two candidate actions on the carriers form a cone over the target
 algebra: each algebra square turns [t_alg_hom] past the action, and the
 pullback square then equates the two T-images. 

 --------
 载体上的两个候选动作在目标代数上形成一个锥：每个代数方格在作用后将 [t_alg_hom] 翻转，然后拉回方格将两个 T 像等同起来。
*)
Lemma em_pb_cone :
  t_alg_hom[FF] ∘ (t_alg[projT2 xa] ∘ fmap[TT] em_pb_p1)
    ≈ t_alg_hom[GG] ∘ (t_alg[projT2 ya] ∘ fmap[TT] em_pb_p2).
Proof.
  rewrite !comp_assoc.
  rewrite !t_alg_hom_commutes.
  rewrite <- !comp_assoc, <- !fmap_comp.
  apply compose_respects; [reflexivity|].
  apply fmap_respects.
  exact (pullback_commutes _ _ em_pb).
Qed.

Definition em_pb_action : TT em_pb_carrier ~> em_pb_carrier :=
  unique_obj (ump_pullbacks _ _ em_pb _
                (t_alg[projT2 xa] ∘ fmap[TT] em_pb_p1)
                (t_alg[projT2 ya] ∘ fmap[TT] em_pb_p2)
                em_pb_cone).

Lemma em_pb_action_1 :
  em_pb_p1 ∘ em_pb_action ≈ t_alg[projT2 xa] ∘ fmap[TT] em_pb_p1.
Proof.
  exact (fst (unique_property
    (ump_pullbacks _ _ em_pb _ _ _ em_pb_cone))).
Qed.

Lemma em_pb_action_2 :
  em_pb_p2 ∘ em_pb_action ≈ t_alg[projT2 ya] ∘ fmap[TT] em_pb_p2.
Proof.
  exact (snd (unique_property
    (ump_pullbacks _ _ em_pb _ _ _ em_pb_cone))).
Qed.

(* Both algebra laws are checked leg by leg through joint monicity; the unit law spends [fmap_ret] and [t_id], the action law [fmap_comp], [t_action] and [join_fmap_fmap]. / 两个代数定律都是通过联合单性逐步检查的；单位定律使用 [fmap_ret] 和 [t_id]，作用定律使用 [fmap_comp]、[t_action] 和 [join_fmap_fmap]。 *)
Lemma em_pb_t_id : em_pb_action ∘ ret ≈ id.
Proof.
  apply (is_pullback_jointly_monic (pullback_is_pullback _ _ em_pb)).
  - rewrite comp_assoc, em_pb_action_1, <- comp_assoc, <- fmap_ret,
            comp_assoc, t_id, id_left, id_right.
    reflexivity.
  - rewrite comp_assoc, em_pb_action_2, <- comp_assoc, <- fmap_ret,
            comp_assoc, t_id, id_left, id_right.
    reflexivity.
Qed.

Lemma em_pb_t_action :
  em_pb_action ∘ fmap[TT] em_pb_action ≈ em_pb_action ∘ join.
Proof.
  apply (is_pullback_jointly_monic (pullback_is_pullback _ _ em_pb)).
  - rewrite !comp_assoc, em_pb_action_1, <- !comp_assoc, <- fmap_comp,
            em_pb_action_1, fmap_comp, comp_assoc, t_action,
            <- !comp_assoc, join_fmap_fmap, !comp_assoc.
    reflexivity.
  - rewrite !comp_assoc, em_pb_action_2, <- !comp_assoc, <- fmap_comp,
            em_pb_action_2, fmap_comp, comp_assoc, t_action,
            <- !comp_assoc, join_fmap_fmap, !comp_assoc.
    reflexivity.
Qed.

Definition em_pb_algebra : TAlgebra TT em_pb_carrier := {|
  t_alg    := em_pb_action ;
  t_id     := em_pb_t_id ;
  t_action := em_pb_t_action
|}.

Definition em_pb_alg_obj : EMT := (em_pb_carrier; em_pb_algebra).

Definition em_pb_fst : em_pb_alg_obj ~{EMT}~> xa.
Proof.
  unshelve refine {| t_alg_hom := em_pb_p1 |}.
  exact em_pb_action_1.
Defined.

Definition em_pb_snd : em_pb_alg_obj ~{EMT}~> ya.
Proof.
  unshelve refine {| t_alg_hom := em_pb_p2 |}.
  exact em_pb_action_2.
Defined.

(* The mediator of a competing cone of algebras is the carrier mediator; that it is an algebra map is again checked leg by leg. / 一个竞争代数锥的中介是载体中介；它是一个代数映射，这一点同样是逐步验证的。 *)
Lemma em_pb_med_commutes (q : EMT) (q1 : q ~{EMT}~> xa)
      (q2 : q ~{EMT}~> ya)
      (Hq : t_alg_hom[FF] ∘ t_alg_hom[q1] ≈ t_alg_hom[GG] ∘ t_alg_hom[q2]) :
  unique_obj (ump_pullbacks _ _ em_pb _ (t_alg_hom[q1]) (t_alg_hom[q2]) Hq)
    ∘ t_alg[projT2 q]
  ≈ em_pb_action ∘ fmap[TT]
      (unique_obj (ump_pullbacks _ _ em_pb _ (t_alg_hom[q1])
                     (t_alg_hom[q2]) Hq)).
Proof.
  pose proof (unique_property
    (ump_pullbacks _ _ em_pb _ (t_alg_hom[q1]) (t_alg_hom[q2]) Hq))
    as [M1 M2].
  apply (is_pullback_jointly_monic (pullback_is_pullback _ _ em_pb)).
  - rewrite comp_assoc.
    change (pullback_fst _ _ em_pb) with em_pb_p1.
    rewrite M1, (t_alg_hom_commutes (TAlgebraHom := q1)).
    rewrite comp_assoc, em_pb_action_1, <- !comp_assoc, <- !fmap_comp.
    now rewrite M1.
  - rewrite comp_assoc.
    change (pullback_snd _ _ em_pb) with em_pb_p2.
    rewrite M2, (t_alg_hom_commutes (TAlgebraHom := q2)).
    rewrite comp_assoc, em_pb_action_2, <- !comp_assoc, <- !fmap_comp.
    now rewrite M2.
Qed.

(* Built with [unshelve refine] rather than [Program] so that the competing cone and its commuting witness are named by [intros] rather than by [Program]'s numbering. / 使用 [unshelve refine] 构建，而不是 [Program]，这样竞争的圆锥及其交换证人就由 [intros] 命名，而不是由 [Program] 的编号命名。 *)
Definition EM_Pullback : Pullback FF GG.
Proof.
  unshelve refine {| Pull         := em_pb_alg_obj
                   ; pullback_fst := em_pb_fst
                   ; pullback_snd := em_pb_snd |}.
  - (* the square commutes: it is the carrier square / 方形是可交换的：它是承载方形 *)
    exact (pullback_commutes _ _ em_pb).
  - (* the universal property: the carrier mediator, made an algebra map by [em_pb_med_commutes]; uniqueness is the carrier's, since a morphism of EMT is determined by its underlying arrow / 泛性质：承载中介，由 [em_pb_med_commutes] 制作了一个代数映射；唯一性归于承载，因为 EMT 的态射由其基础箭头确定 *)
    intros q q1 q2 Hq.
    unshelve refine {| unique_obj := _ |}.
    + unshelve refine {| t_alg_hom := unique_obj
        (ump_pullbacks _ _ em_pb _ t_alg_hom[q1] t_alg_hom[q2] Hq) |}.
      apply em_pb_med_commutes.
    + exact (unique_property
        (ump_pullbacks _ _ em_pb _ t_alg_hom[q1] t_alg_hom[q2] Hq)).
    + intros v Hv.
      exact (uniqueness
        (ump_pullbacks _ _ em_pb _ t_alg_hom[q1] t_alg_hom[q2] Hq)
        t_alg_hom[v] Hv).
Defined.

End EMPullback.

Definition EM_HasPullbacks : @HasPullbacks EMT :=
  {| pullback := fun x y z F G => EM_Pullback F G |}.

(* * ** (C) Transport back, and the four shapes / * **（C）运输回来，以及四种形状 *)

(* The equivalence read backwards: EM(P ◯ P^op) ≃ C^op. / 向后读的等价式：EM(P ◯ P^op) ≃ C^op。 *)
Definition pow_equivalence_sym :
  @EquivalenceOfCategories EMT (C^op)
    (@quasi_inverse (C^op) EMT (EM_Comparison pow_adjunction)
       pow_equivalence) :=
  @EquivalenceOfCategories_sym (C^op) EMT (EM_Comparison pow_adjunction)
    pow_equivalence.

(*
 [@Initial C] IS [@Terminal (C^op)], so the terminal algebra transports
 straight to an initial object of the topos. 

 --------
 [@Initial C] 是 [@Terminal (C^op)]，因此末端代数直接传输到拓扑的初始对象。
*)
Definition topos_Initial : @Initial C :=
  Terminal_transport pow_equivalence_sym EM_Terminal.

Definition topos_HasPullbacks_op : @HasPullbacks (C^op) :=
  HasPullbacks_transport pow_equivalence_sym EM_HasPullbacks.

(*
 [@Cocartesian C] IS [@Cartesian (C^op)], and the terminal object of
 C^op is the initial object just built. 

 --------
 [@Cocartesian C] 是 [@Cartesian (C^op)]，并且 C^op 的终对象是刚建立的初始对象。
*)
Definition topos_Cocartesian : @Cocartesian C :=
  @Cartesian_of_HasPullbacks_Terminal (C^op) topos_Initial
    topos_HasPullbacks_op.

Definition topos_HasEqualizers_op : @HasEqualizers (C^op) :=
  @HasEqualizers_of_HasPullbacks_Terminal (C^op) topos_Initial
    topos_HasPullbacks_op.

Definition topos_HasCoequalizers : @HasCoequalizers C :=
  @HasCoequalizers_of_HasEqualizers_op C topos_HasEqualizers_op.

Definition topos_HasPushouts : @HasPushouts C :=
  HasPushouts_of_HasPullbacks_op topos_HasPullbacks_op.

(*
 MAC LANE §IV.10 REMARK 2, at generator level: initial object, binary
 coproducts, coequalizers, pushouts. 

 --------
 MAC LANE §IV.10 备注 2，在生成元层面：初始对象，二元余积，共等化器，推出。
*)
Definition topos_has_finite_colimits :
  @Initial C * @Cocartesian C * @HasCoequalizers C * @HasPushouts C :=
  (topos_Initial, topos_Cocartesian, topos_HasCoequalizers,
   topos_HasPushouts).

(** ** (D) Readbacks / **（D）复述 *)

(*
 The initial object IS the quasi-inverse's image of the terminal
 algebra, and the terminal algebra's carrier IS the terminal object of
 the topos -- both on the nose. 

 --------
 初始对象就是终结代数的拟逆像，而终结代数的承载对象就是拓扑中的终结对象——两者都是严格对应的。
*)
Example topos_Initial_obj :
  @initial_obj C topos_Initial
    = @quasi_inverse (C^op) EMT (EM_Comparison pow_adjunction)
        pow_equivalence (@terminal_obj EMT EM_Terminal) := eq_refl.

Example EM_Terminal_carrier :
  ``(@terminal_obj EMT EM_Terminal) = @terminal_obj C _ := eq_refl.

(* A pullback of algebras is the pullback of the carriers, with both projections the carrier projections. / 代数的拉回是载体的拉回，两者的投射都是载体投射。 *)
Example EM_Pullback_carrier {xa ya za : EMT}
        (FF : xa ~{EMT}~> za) (GG : ya ~{EMT}~> za) :
  ``(Pull FF GG (EM_Pullback FF GG)) = em_pb_carrier FF GG := eq_refl.

Example EM_Pullback_fst {xa ya za : EMT}
        (FF : xa ~{EMT}~> za) (GG : ya ~{EMT}~> za) :
  t_alg_hom[pullback_fst FF GG (EM_Pullback FF GG)]
    = em_pb_p1 FF GG := eq_refl.

Example EM_Pullback_snd {xa ya za : EMT}
        (FF : xa ~{EMT}~> za) (GG : ya ~{EMT}~> za) :
  t_alg_hom[pullback_snd FF GG (EM_Pullback FF GG)]
    = em_pb_p2 FF GG := eq_refl.

(* The pushout is the transported pullback read in C^op, with no second construction interposed. / 推挤是作为C^op中读取的传递拉回，没有插入第二个构造。 *)
Example topos_HasPushouts_is_op {x y z : C} (f : x ~> y) (g : x ~> z) :
  @pushout C topos_HasPushouts x y z f g
    = @pullback (C^op) topos_HasPullbacks_op y z x f g := eq_refl.

(* The four components of the headline are the four records built above. / 标题的四个组成部分是上面建立的四个记录。 *)
Example topos_has_finite_colimits_fst :
  fst (fst (fst topos_has_finite_colimits)) = topos_Initial := eq_refl.

Example topos_has_finite_colimits_snd :
  snd (fst (fst topos_has_finite_colimits)) = topos_Cocartesian := eq_refl.

Example topos_has_finite_colimits_thd :
  snd (fst topos_has_finite_colimits) = topos_HasCoequalizers := eq_refl.

Example topos_has_finite_colimits_fth :
  snd topos_has_finite_colimits = topos_HasPushouts := eq_refl.

End ToposColimits.
