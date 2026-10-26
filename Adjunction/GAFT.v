Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.WeaklyInitial.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.One.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Discrete.

Set Universe Polymorphism.

Generalizable All Variables.

(** * Freyd's General Adjoint Functor Theorem  / * 弗雷德一般伴随定理*)

(*
nLab:      https://ncatlab.org/nlab/show/adjoint+functor+theorem
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functor_theorem

   The General Adjoint Functor Theorem (GAFT, Freyd; Mac Lane CWM V.6) gives
   sufficient conditions for a functor [U : C ⟶ D] to have a left adjoint.  It
   has two ingredients, one universal-arrow-shaped and one solution-set-shaped:

     - if every object [d : D] has a *universal arrow* into [U] — packaged
       here as an initial object of the comma category [=(d) ↓ U] — then those
       arrows assemble into a left adjoint.  This is [GAFT_from_initials], and
       it is immediate from [Theory/Universal/Arrow.v]
       ([AdjunctionFromUniversalArrows]).

     - Freyd's theorem then *manufactures* those initial objects from a
       completeness hypothesis on [C], a limit-preservation hypothesis on [U],
       and a *solution set* at each [d].  A solution set is a small family of
       arrows [d ~> U (sol_obj i)] through which every [d ~> U c] factors; it
       is exactly a *weakly* initial family in [=(d) ↓ U].  Comma completeness
       ([Construction/Comma/Limit.v]) plus the passage from a weakly initial
       family to a genuine initial object ([Theory/WeaklyInitial.v]) then
       promote that weakly initial family to an initial object, feeding
       [GAFT_from_initials].

   VARIANCE.  [Theory/Universal/Arrow.v] states its universal-arrow adjunction
   for a functor [U0 : D0 ⟶ C0] and produces a left adjoint [C0 ⟶ D0].  We
   instantiate it with [C0 := D], [D0 := C], [U0 := U], so that [=(c) ↓ U0]
   with [c : C0 = D] is our [=(d) ↓ U] and the induced left adjoint is
   [D ⟶ C], exactly as required by the packaging [{ F : D ⟶ C & F ⊣ U }].

   HYPOTHESIS FORM (donor-signature deviation, recorded honestly).  The
   operative preservation hypothesis of [GAFT] is [PreservesImageLimit U] from
   [Construction/Comma/Limit.v], the cone-level statement that [U] carries a
   limit cone of any diagram to a limit cone (the image cone
   [(U L, fmap[U] π_•)] is universal).  This is the mathematically correct
   reading of “U preserves limits”, and it is precisely what
   [Comma_Complete] consumes.  The apex-only class [PreservesAllLimits] of
   [Structure/Limit/Preservation.v] records only that the apex object [U L]
   carries *some* limit structure, whose legs need not be the image legs; as
   [Construction/Comma/Limit.v] documents in detail, two cone structures on the
   same apex can differ by a non-invertible endomorphism, so apex-only
   preservation does not by itself make the image cone universal.  Taking the
   cone-level [PreservesImageLimit] is therefore a strengthening to the correct
   notion of preservation — a leaner, honest hypothesis — and never a weakening
   of the conclusion, which remains a full left adjoint [F ⊣ U].  This mirrors
   the identical, documented choice made by [Comma_Complete] itself. 

--------
nLab:      https://ncatlab.org/nlab/show/adjoint+functor+theorem
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functor_theorem

   一般伴随函子定理 (GAFT, Freyd; Mac Lane CWM V.6) 给出函子 [U : C ⟶ D] 有左伴随的
   充分条件。它有两成分，一呈普遍箭头形，一呈解集形：

     - 若每个对象 [d : D] 都有进入 [U] 的*普遍箭头*——此处打包为逗号范畴 [=(d) ↓ U]
       的初始对象——则这些箭头组装成左伴随。这是 [GAFT_from_initials]，直接来自
       [Theory/Universal/Arrow.v]（[AdjunctionFromUniversalArrows]）。

     - Freyd 定理随后从 [C] 的完备性假设、[U] 的极限保持假设，以及每个 [d] 处的*解集*
       *制造*那些初始对象。解集是小族箭头 [d ~> U (sol_obj i)]，每个 [d ~> U c] 经其分解；
       恰是 [=(d) ↓ U] 中的*弱*初始族。逗号完备性（[Construction/Comma/Limit.v]）加上
       从弱初始族到真正初始对象的通路（[Theory/WeaklyInitial.v]）把该弱初始族提升为
       初始对象，喂给 [GAFT_from_initials]。

   变差。[Theory/Universal/Arrow.v] 对其函子 [U0 : D0 ⟶ C0] 陈述普遍箭头伴随并产出
   左伴随 [C0 ⟶ D0]。我们以 [C0 := D]、[D0 := C]、[U0 := U] 实例化，使 [=(c) ↓ U0]
   （[c : C0 = D]）即我们的 [=(d) ↓ U]，诱导左伴随为 [D ⟶ C]，恰如打包
   [{ F : D ⟶ C & F ⊣ U }] 所需。

   假设形式（donor-signature 偏差，诚实记录）。[GAFT] 的操作性保持假设是
   [Construction/Comma/Limit.v] 的 [PreservesImageLimit U]，锥层陈述：[U] 把任意图的
   极限锥带到极限锥（像锥 [(U L, fmap[U] π_•)] 普遍）。这是「U 保持极限」的数学正确读法，
   恰是 [Comma_Complete] 所消耗的。[Structure/Limit/Preservation.v] 的仅顶点类
   [PreservesAllLimits] 只记录顶点对象 [U L] 携带*某个*极限结构，腿不必是像腿；如
   [Construction/Comma/Limit.v] 详述，同顶点上两锥结构可差非可逆自同态，故仅顶点保持
   本身不使像锥普遍。取锥层 [PreservesImageLimit] 因此是加强到正确保持概念——更瘦、诚实的
   假设——从不削弱结论，结论仍是完整左伴随 [F ⊣ U]。这镜像 [Comma_Complete] 自身的
   相同、已文档化选择。 
*)

(*
The converse of continuity: provenance, obstruction, and use

   nLab:  https://ncatlab.org/nlab/show/adjoint+functor+theorem
   Book:  Freyd, “Abelian Categories: An Introduction to the Theory of
          Functors”, Harper & Row 1964 (TAC Reprints 3, 2003)
   Paper: Kan, “Adjoint Functors”, Trans. AMS 87(2), 1958
   Paper: Porst, “The history of the General Adjoint Functor Theorem”,
          arXiv:2310.19528, 2023
   Post:  Milewski, “Freyd's Adjoint Functor Theorem”, 2020

   The theorem answers one question: which limit-preserving functors are
   right adjoints.  That a right adjoint preserves limits is elementary, and
   is proven in-tree as [rapl_is_alimit] of Adjunction/Continuity.v (RAPL);
   [GAFT] answers the converse: sufficient conditions under which a
   continuous [U] is a right adjoint, exhibited here as the left adjoint
   [F ⊣ U].

   Adjoint functors were a recent notion when the theorem was proved.  Kan
   introduced them (Kan, “Adjoint Functors”, Trans. AMS 87(2), 1958), and
   Mac Lane records that Bourbaki had just missed the concept in a 1948
   draft appendix.  Both the general and the special adjoint functor
   theorems then first appeared in print in Freyd's 1964 book, where — as
   nLab records — they sit in the exercise section of chapter 3 rather than
   among the headline results.  Porst has argued that the substance of the
   result reaches back further still, into the universal-mapping-problem
   tradition of the late 1940s (Porst, arXiv 2023) — a claim about
   provenance, not settled consensus.  Freyd and Scedrov later renamed the
   solution-set condition pre-adjointness (1990).

   The hypotheses repair a genuine size obstruction rather than decorate the
   statement.  Building the adjoint pointwise as a limit over the comma
   category breaks down because that category is large, and a large category
   need not have large limits; indeed a small complete category is a
   preorder (Freyd), so completeness cannot be exploited naively at large
   size.  The [SolutionSet] record is the minimal patch — a small family
   [sol_arr] through which every [d ~> U c] factors, that is, a weakly
   initial family in the comma [=(d) ↓ U].  Freyd's repair runs in two
   stages, both carried out by [initial_from_weakly_initial] of
   Theory/WeaklyInitial.v: take the [iprod] of the family to a weakly
   initial object, then equalize all of its endomorphisms to sharpen weak
   initiality into genuine initiality.  In [GAFT] those products and
   equalizers come from [Comma_Complete], and [wif_of_sols] is the passage
   from a [SolutionSet] to the [WeaklyInitialFamily] consumed there.

   The special adjoint functor theorem trades the explicit solution set for
   structural smallness of the domain: Adjunction/SAFT.v manufactures a
   [SolutionSet] from well-poweredness ([SubobjectIndex]) and a cogenerating
   family ([Cogenerator]), so [SAFT] never asks the caller to supply one.
   (CORRECTION, #451: [SubobjectIndex] is not well-poweredness -- it lacks
   the exhaustiveness clause of Structure/WellPowered.v's [WellPowered] and
   the empty family inhabits it -- and [SAFT] does ask for one more datum,
   [SubobjectCover], which factors every arrow through the given index and
   is refutable at the identity of [Sets] (Adjunction/SAFT/Sets.v's
   [SubobjectCover_Id_Sets_absurd]).)
   Continuity by itself does not suffice, and the boundary is sharp: nLab
   records a counterexample that Joyal attributes to Mac Lane, a product
   of representables over the simple groups that is continuous yet not
   representable.  The modern sharpening (Adámek and Rosický) makes it a
   biconditional between locally presentable categories, where a functor
   has a left adjoint exactly when it is accessible and preserves small
   limits.

   The reach is broad.  When [U] forgets structure its left adjoint is the
   free construction, which Milewski glosses as freely ad-libbing the
   forgotten information.  A full subcategory is reflective exactly when its
   inclusion has a left adjoint, so the theorem is the standard tool for
   producing reflectors (Construction/Reflective.v,
   Construction/Localization.v).  Limits, colimits and Kan extensions are
   themselves adjoints, so it yields existence criteria for them; and in the
   order-theoretic degenerate case it is the adjoint functor theorem for
   preorders, the Galois-connection setting that Instance/Poset.v cites
   [SolutionSet] to explain.  Adjunction/GAFT/Examples.v runs
   [GAFT_from_initials] end to end to recover the diagonal adjoint Δ ⊣ (×),
   proving the produced functor naturally isomorphic to Δ
   ([diagonal_product_via_gaft_is_diagonal]).

   The computational reading is the generate-then-constrain recipe familiar
   from free-algebra constructions.  Milewski reads the solution set as a
   way to cut a large comma category down to a manageable size, and the
   construction holographically: gather all information about an object
   through the morphisms out of it, ship that record back through [U], and
   reconstruct the best preimage as a limit.  The product-then-equalizer
   shape tuples the small family and carves it by imposing every self-map;
   Milewski notes an unexpected connection to defunctionalization, the
   Reynolds program transformation that motivated the account. 

--------
连续性的反面：出处、阻碍和使用

nLab：https://ncatlab.org/nlab/show/adjoint+functor+theorem
 书：弗雷德，《阿贝尔范畴：理论导论》
 Functors”，Harper & Row 1964（TAC Reprints 3，2003）
 论文：Kan，“伴随”，Trans。 美国医学会 87(2), 1958
 论文：Porst，“一般伴随定理的历史”，
 arXiv:2310.19528, 2023
 帖子：Milewski，“弗雷德伴随定理”，2020

该定理回答了一个问题：哪些保极限函子是
 右伴随词。 右伴随保留极限是基本的，并且
 在树内被证明为 Adjunction/Continuity.v (RAPL) 的 [rapl_is_alimit]；
 [GAFT] 回答相反：充分条件
 连续 [U] 是右伴随，此处展示为左伴随
 [F ⊣ U]。

当该定理被证明时，伴随是一个新概念。 坎
 介绍了它们（Kan，“伴随”，Trans. AMS 87(2), 1958），以及
 Mac Lane 记录说 Bourbaki 在 1948 年的一辆汽车中刚刚错过了这个概念
 附录草案。 一般伴随和特殊伴随
 定理随后首次出现在 Freyd 1964 年的书中，其中 —
 nLab 记录——它们位于第 3 章的练习部分，而不是
 在头条新闻结果中。 波斯特认为，该法案的实质内容是
 结果可以追溯到更远的地方，进入通用映射问题
 20 世纪 40 年代末的传统（Porst，arXiv 2023）——关于
 出处，尚未达成共识。 弗雷德和谢德罗夫后来更名为
 解集条件预伴随性（1990）。

这些假设修复了真正大小的障碍，而不是装饰了
 声明。 逐点构建伴随词作为逗号的限制
 类别分解是因为类别很大，而且类别很大
 不需要有很大的限制； 事实上，一个小的完整类别是
 预购（Freyd），因此完整性不能被天真地广泛利用
 尺寸。 [SolutionSet] 记录是最小的补丁 - 一个小家庭
 [sol_arr] 通过它每个 [d ~> U c] 因子，即弱
 逗号 [=(d) ↓ U] 中的初始系列。 弗雷德的维修分两次进行
 阶段，均由 [initial_from_weakly_initial] 执行
 Theory/WeaklyInitial.v：把家族的[iprod]带到弱化
 初始对象，然后均衡其所有自同态以锐化弱
 最初性变成真正的最初性。 在 [GAFT] 中这些产品和
 均衡器来自[Comma_Complete]，[wif_of_sols]是通道
 从 [SolutionSet] 到那里使用的 [WeaklyInitialFamily]。

特殊伴随定理将显式解集换为
 域的结构小：Adjunction/SAFT.v 制造了
 [SolutionSet] 动力强劲 ([SubobjectIndex]) 和热电联产
 系列 ([Cogenerator])，因此 [SAFT] 从不要求调用者提供一个。 
（更正，#451：[SubobjectIndex] 的功能并不强大——它缺乏
 Structure/WellPowered.v 的 [WellPowered] 的详尽性条款和
 空的家庭居住在其中 - [SAFT] 确实要求再提供一项数据，
 [SubobjectCover]，它将通过给定索引的每个箭头分解为因子，并
 [Sets] 的身份是可反驳的（Adjunction/SAFT/Sets.v 的
 [SubobjectCover_Id_Sets_absurd]）。）
 连续性本身是不够的，而且边界很清晰：nLab
 Joyal 记录了一个反例，归因于 Mac Lane 的一款产品
 连续但不连续的简单群上的可表示数
 具有代表性。 现代锐化（阿达梅克和罗西基）使其成为
 局部呈现类别之间的双条件，其中函子
 恰好在可访问时具有左伴随并保留较小的值
 限制。

影响范围很广。 当 [U] 忘记结构时，它的左伴随是
 自由构造，米勒夫斯基将其解释为自由即兴创作
 忘记信息。 完整的子类别在其出现时准确反映
 包含有左伴随，因此该定理是以下问题的标准工具：
 生产反射器（Construction/Reflective.v，
 构建/本地化.v)。 极限、余极限和 Kan 扩展是
 它们本身是伴随的，因此它产生了它们的存在标准； 并在
 序论简并情况它是伴随定理
 preorders，Instance/Poset.v 引用的伽罗瓦连接设置
 [SolutionSet] 来解释一下。 Adjunction/GAFT/Examples.v 运行
 [GAFT_from_initials]端到端恢复对角伴随Δ ⊣ (×)，
 证明生成的函子自然同构于 Δ
 ([diagonal_product_via_gaft_is_diagonal])。

计算读取是熟悉的“生成然后约束”配方
 来自自由代数构造。 Milewski 将解集读取为
 将大逗号类别削减到可管理大小的方法，以及
 全息构造：收集有关对象的所有信息
 通过其中的态射，通过 [U] 发送回记录，以及
 重建最佳原像作为极限。 产品然后均衡器
 shape 将小家庭组合起来，并通过强加每个自我地图来雕刻它；
 米莱夫斯基指出，与去功能化有着意想不到的联系，
 雷诺兹计划转型推动了该帐户。 
*)

(** ** Solution sets  / ** 解决方案集*)

(*
A solution set at [d : D] for [U : C ⟶ D]: a small [Type] of indices, a
   family of objects [sol_obj i : C] with arrows [sol_arr i : d ~> U (sol_obj i)],
   such that every [h : d ~> U c] factors through some member,
   [fmap[U] t ∘ sol_arr i ≈ h].  No uniqueness of the factorization is asked —
   this is a *weakly* initial family in the comma category [=(d) ↓ U]. 

--------
[U : C ⟶ D] 的 [d : D] 解决方案集：一个小的 [Type] 索引，一个
 带有箭头 [sol_arr i : d ~> U (sol_obj i)] 的对象系列 [sol_obj i : C]，
 这样每个 [h : d ~> U c] 都会通过某个成员，
 [fmap[U] t ∘ sol_arr i ≈ h]。 不询问因式分解的唯一性 -
 这是逗号类别 [=(d) ↓ U] 中的“弱”初始家族。 
*)
(* THE INDEX UNIVERSE IS NAMED [i], AND IT IS FREE HERE ON PURPOSE.
   [SolutionSet@{i dobj cobj h}] carries an EMPTY constraint block: [i] is
   related to nothing, so a solution set may be indexed at any level -- by
   a [bool], by [Subgroup G], by a sigma over the objects of the ambient
   category.  That freedom is the whole reason the record is worth having
   separately from the weakly initial family it becomes.

   THE IDENTIFICATION IS IMPOSED AT [GAFT], NOT HERE, and declaring it
   here would WEAKEN this record.  See [GAFT] below: applying the
   theorem forces [i] onto the ambient hom universe [h], through
   [Complete]'s single shape-object universe.  The refusals recorded in
   Instance/Mod/TensorAFT.v and Test/ProbeModTensorAFT449.v are that
   forcing meeting an index that sits strictly above [h].

   Measured readback:

     SolutionSet@{i dobj cobj h} :
     ∀ {C : Category@{cobj h h}} {D : Category@{dobj h h}},
     C ⟶ D → obj[D] → Type@{max(i+1,cobj,h)}
     (* i dobj cobj h |=  *)                     <-- empty, as intended *)
Record SolutionSet@{i dobj cobj h}
  {C : Category@{cobj h h}} {D : Category@{dobj h h}} (U : C ⟶ D) (d : D) := {
  sol_index : Type@{i};
  sol_obj : sol_index -> C;
  sol_arr : forall i, d ~> U (sol_obj i);
  sol_covers {c} (h : d ~> U c) :
    { i : sol_index & { t : sol_obj i ~> c & fmap[U] t ∘ sol_arr i ≈ h } }
}.

Arguments sol_index {C D U d} _.
Arguments sol_obj {C D U d} _ _.
Arguments sol_arr {C D U d} _ _.
Arguments sol_covers {C D U d} _ {c} _.

(** ** The universal-arrow half: initial objects give a left adjoint  / ** 万能箭头半：初始对象给出左伴随*)

(*
If every [d : D] has an initial object in the comma category [=(d) ↓ U],
   then [U] has a left adjoint.  Immediate from [Theory/Universal/Arrow.v]:
   each such initial object is a [UniversalArrow d U], and a universal arrow at
   every object assembles into the left adjoint by
   [AdjunctionFromUniversalArrows], instantiated with the codomain [D] on the
   left (see the VARIANCE note above). 

--------
如果每个 [d : D] 在逗号类别 [=(d) ↓ U] 中都有一个初始对象，
 那么 [U] 有一个左伴随。 立即来自 [Theory/Universal/Arrow.v]：
 每个这样的初始对象都是一个 [UniversalArrow d U]，以及一个通用箭头
 每个对象都组装成左伴随
 [AdjunctionFromUniversalArrows]，用密码域 [D] 实例化
 左（参见上面的方差注释）。 
*)
Theorem GAFT_from_initials {C D : Category} (U : C ⟶ D)
  (H : forall d : D, @Initial (=(d) ↓ U)) : { F : D ⟶ C & F ⊣ U }.
Proof.
  pose (Hu := fun d : D => {| arrow_initial := H d |} : @UniversalArrow D C d U).
  exists (@LeftAdjointFunctorFromUniversalArrows D C U Hu).
  exact (@AdjunctionFromUniversalArrows D C U Hu).
Qed.

(** ** Auxiliary bridges from completeness  / ** 辅助桥梁的完整性*)

(*
Every complete category has all binary equalizers: take the limit of the
   walking parallel pair [APair f g] and read it, at its apex, as an elementary
   equalizer via [equalizer_is_equalizer] of [Structure/Equalizer/Fork.v]. 

--------
每个完整类别都有所有二元均衡器：取极限
 平行行走 [APair f g] 并在其顶点读取它，作为基本的
 通过 [equalizer_is_equalizer] 或 [Structure/Equalizer/Fork.v] 进行均衡器。 
*)
Definition Complete_HasEqualizers {A : Category} (HA : @Complete A) :
  HasEqualizers A.
Proof.
  constructor.
  intros x y f g.
  pose (L := HA Parallel (APair f g)).
  eexists.
  eexists.
  exact (equalizer_is_equalizer f g L).
Defined.

(*
A solution set at [d] is a weakly initial family in the comma [=(d) ↓ U]:
   the family members are the comma objects [(sol_obj i, sol_arr i)], and the
   covering arrow for any comma object [(c, h)] is the [U]-factorization
   [(sol_obj i, t)] of [h] supplied by [sol_covers], upgraded to a comma
   morphism (its commuting triangle is exactly the factorization equation, the
   left leg [fmap[=(d)] _] collapsing to [id[d]]). 

--------
[d] 处设置的解是逗号 [=(d) ↓ U] 中的弱初始族：
 系列成员是逗号对象 [(sol_obj i, sol_arr i)]，并且
 任何逗号对象的覆盖箭头 [(c, h)] 是 [U] 分解
 [sol_covers]提供的[h]的[(sol_obj i, t)]，升级为逗号
 态射（它的交换三角形正是分解方程，
 左腿 [fmap[=(d)] _] 塌陷为 [id[d]]）。 
*)
(* THE INDEX UNIVERSE IS CARRIED ACROSS ON THE NOSE, and the binders say
   so: the solution set's [i] is the weakly initial family's [i], with no
   level change in either direction.  That is what makes this bridge and
   its converse [sols_of_wif] below an identification of index types
   rather than a resizing, and it is why the size condition [GAFT]
   imposes can be read off [initial_from_weakly_initial] alone.  Measured:

     wif_of_sols@{i cobj dobj h comma u u0 u1 u2 u3} :
     ∀ {C : Category@{cobj h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
       (d : obj[D]),
       SolutionSet@{i dobj cobj h} U d
       → WeaklyInitialFamily@{i comma h} (=(d) ↓ U)
     (* i cobj dobj h comma u u0 u1 u2 u3 |= h < u1 / u0 <= comma *) *)
Definition wif_of_sols@{i cobj dobj h comma +}
  {C : Category@{cobj h h}} {D : Category@{dobj h h}} (U : C ⟶ D) (d : D)
  (S : SolutionSet@{i dobj cobj h} U d)
  : WeaklyInitialFamily@{i comma h} (=(d) ↓ U).
Proof.
  destruct S as [idx obj arr cov].
  unshelve refine (@Build_WeaklyInitialFamily (=(d) ↓ U) idx
                     (fun i => ((ttt, obj i); arr i)) _).
  intro Y.
  destruct Y as [[oY cY] hY].
  destruct (cov cY hY) as [i [t e]].
  exists i.
  unshelve refine ((ttt, t); _).
  change (hY ∘ id[d] ≈ fmap[U] t ∘ arr i).
  rewrite id_right.
  symmetry; exact e.
Defined.

(** ** Freyd's General Adjoint Functor Theorem  / ** 弗雷德一般伴随定理*)

(*
Freyd's GAFT.  [C] complete, [U] preserving (image) limits, and a solution
   set at every [d], yield a left adjoint [F ⊣ U].  For each [d]:

     - comma completeness [Comma_Complete] makes [=(d) ↓ U] complete;
     - the solution set becomes a weakly initial family [wif_of_sols];
     - the two products (over the solution-set index, and over the
       endomorphisms of that product) and the equalizers demanded by
       [initial_from_weakly_initial] are drawn from that comma completeness;
     - [initial_from_weakly_initial] then yields an initial object of
       [=(d) ↓ U], fed to [GAFT_from_initials].

   See the header for why the preservation hypothesis is the cone-level
   [PreservesImageLimit] rather than the apex-only [PreservesAllLimits]. 

--------
弗雷德的天赋。 [C] 完整、[U] 保留（图像）限制以及解决方案
 在每个 [d] 处设置，产生一个左伴随 [F ⊣ U]。 对于每个 [d]：

 - 逗号完整性 [Comma_Complete] 使 [=(d) ↓ U] 完整；
 - 解集成为弱初始族[wif_of_sols]；
 - 两个乘积（在解集索引上，以及在
 该乘积的自同态）以及所要求的均衡器
 [initial_from_weakly_initial] 是从逗号完整性中得出的；
 - [initial_from_weakly_initial] 然后产生一个初始对象
 [=(d) ↓ U]，馈送到 [GAFT_from_initials]。 

请参阅标题以了解为什么保存假设是锥体水平
 [PreservesImageLimit] 而不是仅限顶点的 [PreservesAllLimits]。 
*)
(* THE UNIVERSE BINDERS ARE THE STATEMENT OF THE SIZE CONDITION, and they
   are written out because the two identifications below are what every
   application of this theorem stands or falls on.

     [cobj], [dobj]  the object universes of [C] and of [D],
     [h]             the hom-and-proof universe of BOTH -- one level, not
                     two, because [Adjunction] relates the two hom-setoids,

   and then, in the two annotated hypotheses:

     (i)  [SolutionSet@{h dobj cobj h}] -- the solution-set INDEX universe
          is [h].  [SolutionSet] itself leaves it free (empty constraint
          block, see above); it is this application that pins it.
     (ii) [@Complete@{h h h cobj} C] -- [Complete]'s SHAPE-OBJECT universe
          is [h] as well, identified with the ambient hom universe.

   WHY (ii), which is the one that surprises.  The proof takes TWO limits
   inside the comma category, through [initial_from_weakly_initial]:

       initial_from_weakly_initial@{u u0 u1 u2 u3}
         {C : Category@{u2 u3 u3}} (W : WeaklyInitialFamily@{u0 u2 u3} C)
         (P : Limit@{u u0 u3 u2} (DiscreteCat_Functor (wif_obj W)))
         (Limit@{u3 u3 u3 u2} (DiscreteCat_Functor
            (fun _ : iprod (wif_obj W) P ~> iprod (wif_obj W) P => …)))
         (HasEqualizers C) : Terminal C

   The FIRST limit is over a discrete shape whose objects are the family
   index [u0]; the SECOND is over a discrete shape whose objects are a
   HOM-SET of the ambient category, so its shape-object universe is the
   ambient hom universe [u3].  [Complete] offers ONE shape-object universe
   for every shape at once, so the second limit drags it up to [h] and the
   first -- the solution set -- is dragged with it.  That is (i) and (ii)
   in one sentence: the equalizer of all endomorphisms of the product is
   what puts the solution-set index at the hom universe.

   WHAT IS NOT HERE ANY MORE.  An earlier revision of this theorem printed
   [C : Category@{u1 Set Set}] and [Complete@{u4 u4 Set u1}], with [h] the
   literal [Set].  That [Set] was a universe-minimization artifact of
   Instance/Discrete.v's unannotated [DiscreteCat_Functor], reaching this
   statement through the [DiscreteCat_Functor] limits taken in the proof
   below; the donor was annotated in the PR
   “algebraic carriers are sets” (2026-09-17) and no literal [Set] remains.
   The size condition (i)+(ii) survives it unchanged, which is the point:
   it is structural and was never about [Set].

   The measured readback, after the annotation:

     GAFT@{cobj dobj h u u0 u1} :
     ∀ {C : Category@{cobj h h}} {D : Category@{dobj h h}} (U : C ⟶ D),
       Complete@{h h h cobj}
       → PreservesImageLimit@{cobj h dobj h u0 h u1 h}
         → (∀ d : obj[D], SolutionSet@{h dobj cobj h} U d)
           → ∃ F : D ⟶ C, Adjunction@{cobj h h dobj h h h h u1 h u} F U
     (* cobj dobj h u u0 u1 |= h < u0 / h < u1
                               / cobj <= u0 / dobj <= u0 / … *)

   -- the two strict bounds [h < u0] and [h < u1] being the [Type]s the
   comma categories and the adjunction record live in.  The trailing [+]
   on the binder list allows those auxiliary levels, which is why they
   print as [u], [u0], [u1] AFTER the three named ones; the three named
   are the ones the size condition is about, and no [Set] appears among
   any of them. *)
Theorem GAFT@{cobj dobj h +} {C : Category@{cobj h h}} {D : Category@{dobj h h}}
  (U : C ⟶ D)
  (comp : @Complete@{h h h cobj} C) (cont : @PreservesImageLimit C D U)
  (sols : forall d : D, SolutionSet@{h dobj cobj h} U d)
  : { F : D ⟶ C & F ⊣ U }.
Proof.
  apply GAFT_from_initials.
  intro d.
  pose (HCat := @Comma_Complete C D U d cont comp).
  pose (W := wif_of_sols U d (sols d)).
  pose (P := HCat _ (DiscreteCat_Functor (wif_obj W))).
  refine (@initial_from_weakly_initial (=(d) ↓ U) W P
            (HCat _ (DiscreteCat_Functor
                       (fun _ : (iprod (wif_obj W) P ~> iprod (wif_obj W) P)
                        => iprod (wif_obj W) P)))
            (Complete_HasEqualizers HCat)).
Qed.

(**
** The converse of [wif_of_sols]

    A weakly initial family of the comma category is a solution set —
    the exact converse of [wif_of_sols], with the same index — and an
    initial object of the comma category is therefore a one-member
    solution set: Mac Lane §V.6 Theorem 1's necessity direction, in this
    file's vocabulary (#435).  Appended here so that no line above moves. 

--------
** [wif_of_sols] 的逆过程

 逗号范畴的弱初始族是一个解集 -
 与 [wif_of_sols] 完全相反，具有相同的索引 - 和
 因此，逗号类别的初始对象是一个成员
 解集：Mac Lane §V.6 定理1的必然性方向，在此
 文件的词汇表（#435）。 附加到此处，以便上面的行不会移动。 
*)

(* The converse, with the index universe [i] carried across on the nose in
   the other direction — see [wif_of_sols] above.  Measured: the two have
   the SAME binder list and the same two constraints,

     sols_of_wif@{i cobj dobj h comma u u0 u1 u2 u3} :
     ∀ {C : Category@{cobj h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
       (d : obj[D]),
       WeaklyInitialFamily@{i comma h} (=(d) ↓ U)
       → SolutionSet@{i dobj cobj h} U d
     (* i cobj dobj h comma u u0 u1 u2 u3 |= h < u1 / u0 <= comma *)

   which is the sharpest statement that the passage is an identification
   and not a resizing. *)
Definition sols_of_wif@{i cobj dobj h comma +}
  {C : Category@{cobj h h}} {D : Category@{dobj h h}} (U : C ⟶ D) (d : D)
  (W : WeaklyInitialFamily@{i comma h} (=(d) ↓ U))
  : SolutionSet@{i dobj cobj h} U d.
Proof.
  unshelve refine
    {| sol_index := wif_index W
     ; sol_obj := fun i => snd (`1 (wif_obj W i))
     ; sol_arr := fun i => `2 (wif_obj W i) |}.
  intros c h.
  destruct (wif_cover W (((ttt, c); h) : (=(d) ↓ U))) as [i m].
  exists i.
  destruct m as [[u t] sq].
  exists t.
  simpl in sq |- *.
  now rewrite <- sq, id_right.
Defined.

(* The solution set's index is the family's, on the nose.  / 解决方案集的索引是家庭的，就在鼻子上。*)
Example sols_of_wif_index {C D : Category} (U : C ⟶ D) (d : D)
  (W : WeaklyInitialFamily (=(d) ↓ U)) :
  sol_index (sols_of_wif U d W) = wif_index W := eq_refl.

Definition sols_of_comma_initial {C D : Category} (U : C ⟶ D) (d : D)
  (I : @Initial (=(d) ↓ U)) : SolutionSet U d :=
  sols_of_wif U d (weakly_initial_of_initial I).

(* The one member is the initial comma object, on the nose.  / 第一个成员是第一个逗号对象，位于鼻子上。*)
Example sols_of_comma_initial_index {C D : Category} (U : C ⟶ D) (d : D)
  (I : @Initial (=(d) ↓ U)) :
  sol_index (sols_of_comma_initial U d I) = poly_unit := eq_refl.

Example sols_of_comma_initial_obj {C D : Category} (U : C ⟶ D) (d : D)
  (I : @Initial (=(d) ↓ U)) (u : poly_unit) :
  sol_obj (sols_of_comma_initial U d I) u
    = snd (`1 (@initial_obj (=(d) ↓ U) I)) := eq_refl.

(**
** GAFT's inner step, exported

    [GAFT] above reaches its comma-initial objects inside its own [Qed]:
    comma completeness, [wif_of_sols], the two products and
    [Complete_HasEqualizers].  #437 needs that object on its own, so the
    five lines are repeated here as a [Definition] — the theorem's proof is
    NOT rewritten to use it, since every line of this file above stays put
    (eleven external citations point into it). 

--------
** GAFT 的内部步骤，导出

 上面的 [GAFT] 在其自己的 [Qed] 内到达其逗号开头的对象：
 逗号完整性，[wif_of_sols]，这两种产品和
 [Complete_HasEqualizers]。 #437 需要该对象本身，所以
 这里重复五行作为 [Definition] — 定理的证明是
 不重写以使用它，因为上面这个文件的每一行都保留在原处
 （十一个外部引用指向它）。 
*)

(* The same two identifications as [GAFT] — [Complete]'s shape-object
   universe and the solution-set index are both the ambient hom universe
   [h] — since this is [GAFT]'s inner step lifted out verbatim.  Measured:

     comma_initial_of_sols@{cobj dobj h u u0 u1 u2 u3 u4 u5} :
     ∀ {C : Category@{cobj h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
       (d : obj[D]),
       Complete@{h h h cobj}
       → PreservesImageLimit@{cobj h dobj h u4 h u5 h}
         → SolutionSet@{h dobj cobj h} U d → Terminal@{u h}
     (* cobj dobj h u u0 u1 u2 u3 u4 u5 |= h < u4 / u1 <= u *) *)
Definition comma_initial_of_sols@{cobj dobj h +}
  {C : Category@{cobj h h}} {D : Category@{dobj h h}} (U : C ⟶ D) (d : D)
  (comp : @Complete@{h h h cobj} C) (cont : @PreservesImageLimit C D U)
  (S : SolutionSet@{h dobj cobj h} U d) : @Initial (=(d) ↓ U).
Proof.
  pose (HCat := @Comma_Complete C D U d cont comp).
  pose (W := wif_of_sols U d S).
  pose (P := HCat _ (DiscreteCat_Functor (wif_obj W))).
  refine (@initial_from_weakly_initial (=(d) ↓ U) W P
            (HCat _ (DiscreteCat_Functor
                       (fun _ : (iprod (wif_obj W) P ~> iprod (wif_obj W) P)
                        => iprod (wif_obj W) P)))
            (Complete_HasEqualizers HCat)).
Defined.

(*
GAFT itself, re-derived from the exported step, agrees with the theorem
   above on its statement — the two are interchangeable at the type. 

--------
从导出步骤重新导出的 GAFT 本身与该定理一致
 上面的声明 - 两者在类型上可以互换。 
*)
(* Same binders as [GAFT], which is what “agrees on its statement” means
   here: the two are interchangeable at the type AND at the universe
   graph's two identifications.  Measured:

     GAFT_via_comma_initial@{cobj dobj h u u0 u1 u2 u3 u4 u5 u6} :
     ∀ {C : Category@{cobj h h}} {D : Category@{dobj h h}} (U : C ⟶ D),
       Complete@{h h h cobj}
       → PreservesImageLimit@{cobj h dobj h u6 h u h}
         → (∀ d : obj[D], SolutionSet@{h dobj cobj h} U d)
           → ∃ F : D ⟶ C, Adjunction@{cobj h h dobj h h h h u h u0} F U
     (* … |= h < u / u3 <= u1 *) *)
Definition GAFT_via_comma_initial@{cobj dobj h +}
  {C : Category@{cobj h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h cobj} C) (cont : @PreservesImageLimit C D U)
  (sols : ∀ d : D, SolutionSet@{h dobj cobj h} U d) : { F : D ⟶ C & F ⊣ U } :=
  GAFT_from_initials U (fun d => comma_initial_of_sols U d comp cont (sols d)).

(** ** The converse: an adjunction supplies its own solution sets  / ** 相反：附加物提供自己的解决方案集*)

(*
Mac Lane §V.6 Theorem 2 (book p. 123) and Awodey §9.8 Theorem 28 read the
   theorem above as a CHARACTERIZATION: for [U] with complete domain, having
   a left adjoint is EQUIVALENT to preserving limits and satisfying the
   solution set condition.  The sufficient direction is [GAFT]; the
   necessary one is two statements, of which the tree already had the first
   ([right_adjoint_PreservesImageLimit], Construction/Comma/Limit.v) and
   none of the second — nothing anywhere built a [SolutionSet U d] out of an
   adjunction.

   It costs nothing to build.  The solution set is a SINGLETON: the unit
   [η d : d ~> U (F d)] is the one arrow needed, since every [h : d ~> U c]
   factors through it as [U (ε c ∘ fmap[F] h) ∘ η d] by the triangle
   identities.  No completeness, no limit preservation, no smallness
   hypothesis and no discrete-shape limit enter, so unlike [GAFT] itself
   this direction carries no [Set] pin.  Read the universe claim precisely:
   it is stated over [Category@{uo uh uh}] — the hom and proof universes
   identified, and the SAME [uh] for both categories — which is the
   identification [Adjunction] and [SolutionSet] already carry and not one
   introduced here, so an earlier revision of this sentence saying “the
   three universes free” was wrong.  What is free is [Set]: the necessity
   direction is accepted at a category with [Set] strictly below its homs,
   where the biconditional is refused (probe n6 and its control).

   Mac Lane's completeness step is available through #438's creation
   result — [comma_Complete_via_creation] (Construction/Comma/Creation.v)
   derives [Comma_Complete]'s conclusion from [comma_CreatesAllLimits] and
   [creates_limits_Complete], which is his argument rather than
   Construction/Comma/Limit.v's direct construction.  [GAFT] itself is not
   rewritten to use it: that would move lines eleven external citations
   point at, and would put Construction/Comma/Creation.vo into this file's
   closure for no theorem gained.

   Everything below is appended, so no line at or above 328 moves. 

--------
Mac Lane §V.6 定理 2（本书第 123 页）和 Awodey §9.8 定理 28 阅读
 上述定理作为表征：对于具有完整域的 [U]，具有
 左伴随相当于保留极限并满足
 解集条件。 足够的方向是[GAFT]； 的
 必要的一个是两个语句，其中树已经有第一个
 （[right_adjoint_PreservesImageLimit]，构造/逗号/Limit.v）和
 没有第二个 — 没有任何地方可以用
 附属物。

建造不需要花费任何成本。 解集是一个 SINGLETON：单位
 [η d : d ~> U (F d)] 是所需的一支箭，因为每个 [h : d ~> U c]
 通过三角形将其分解为 [U (ε c ∘ fmap[F] h) ∘ η d]
 身份。 没有完整性，没有限制保存，没有狭小
 假设且没有输入离散形状限制，因此与 [GAFT] 本身不同
 该方向没有 [Set] 引脚。 仔细阅读宇宙主张：
 它是在 [Category@{uo uh uh}] 上描述的——本宇宙和证明宇宙
 已确定，并且两个类别的相同 [uh] - 这是
 [Adjunction] 和 [SolutionSet] 已携带标识，没有之一
 介绍到这里，所以这句话的早期修改是“the
 三个宇宙免费”是错误的。 [Set] 是免费的：必需品
 [Set] 严格低于其 homs 的方向被接受，
 其中双条件被拒绝（探针 n6 及其控制）。

Mac Lane 的完整性步骤可通过 #438 的创建获得
 结果 — [comma_Complete_via_creation] (Construction/Comma/Creation.v)
 从 [comma_CreatesAllLimits] 得出 [Comma_Complete] 的结论，并且
 [creates_limits_Complete]，这是他的论点而不是
 Construction/Comma/Limit.v 的直接构造。 [GAFT] 本身不是
 重写以使用它：这将移动第十一行外部引用
 指向，并将 Construction/Comma/Creation.vo 放入该文件的
 没有获得定理的闭包。

下面的所有内容都是附加的，因此 328 或以上的线不会移动。 
*)

Definition solution_set_of_adjunction {C D : Category} {F : D ⟶ C} {U : C ⟶ D}
  (A : F ⊣ U) (d : D) : SolutionSet U d.
Proof.
  unshelve refine
    {| sol_index := poly_unit
     ; sol_obj := fun _ => F d
     ; sol_arr := fun _ => @unit _ _ _ _ A d |}.
  intros c h.
  exists ttt.
  exists (@counit _ _ _ _ A c ∘ fmap[F] h).
  rewrite fmap_comp, <- comp_assoc.
  rewrite unit_comp, comp_assoc.
  rewrite fmap_counit_unit.
  apply id_left.
Defined.

(* The three data fields read back on the nose.  / 三个数据字段直接读回。*)

Definition solution_set_of_adjunction_index {C D : Category} {F : D ⟶ C}
  {U : C ⟶ D} (A : F ⊣ U) (d : D) :
  sol_index (solution_set_of_adjunction A d) = poly_unit := eq_refl.

Definition solution_set_of_adjunction_obj {C D : Category} {F : D ⟶ C}
  {U : C ⟶ D} (A : F ⊣ U) (d : D) (i : poly_unit) :
  sol_obj (solution_set_of_adjunction A d) i = F d := eq_refl.

Definition solution_set_of_adjunction_arr {C D : Category} {F : D ⟶ C}
  {U : C ⟶ D} (A : F ⊣ U) (d : D) (i : poly_unit) :
  sol_arr (solution_set_of_adjunction A d) i = @unit _ _ _ _ A d := eq_refl.

(** ** Mac Lane's own route, through the comma-initial object  / ** Mac Lane自己的路线，通过逗号开头的对象*)

(*
The book does not exhibit a solution set directly: it observes that the
   unit is a UNIVERSAL ARROW, hence an initial object of the comma category,
   hence a weakly initial family of one, hence a solution set.  That chain is
   in the tree already — [universal_arrow_from_UMP], [arrow_initial],
   [sols_of_comma_initial] — so the route can be walked as a second reading
   and compared with the direct one.  It collapses: the arrow of the derived
   solution set is again the unit, by [eq_refl]. 

--------
本书没有直接展示解决方案集：它指出
 单位是通用箭头，因此是逗号类别的初始对象，
 因此是一个弱初始族，因此是一个解集。 那个链条是
 已经在树中 - [universal_arrow_from_UMP]、[arrow_initial]、
 [sols_of_comma_initial] — 因此可以将路线作为第二次读数来行走
 并与直接比较。 它崩溃了：导出的箭头
 解决方案集又是一个单元，由 [eq_refl] 提供。 
*)

Definition universal_arrow_of_adjunction {C D : Category} {F : D ⟶ C}
  {U : C ⟶ D} (A : F ⊣ U) (d : D) : UniversalArrow d U.
Proof.
  unshelve refine (universal_arrow_from_UMP d U (F d) (@unit _ _ _ _ A d) _).
  intros c h.
  exists (@counit _ _ _ _ A c ∘ fmap[F] h).
  - rewrite fmap_comp, <- comp_assoc.
    rewrite unit_comp, comp_assoc.
    rewrite fmap_counit_unit.
    symmetry; apply id_left.
  - intros g Hg.
    rewrite Hg, fmap_comp, comp_assoc.
    rewrite counit_comp, <- comp_assoc.
    rewrite counit_fmap_unit.
    apply id_right.
Defined.

Definition comma_initial_of_adjunction {C D : Category} {F : D ⟶ C}
  {U : C ⟶ D} (A : F ⊣ U) (d : D) : @Initial (=(d) ↓ U) :=
  @arrow_initial _ _ d U (universal_arrow_of_adjunction A d).

Definition solution_set_of_adjunction_via_comma {C D : Category} {F : D ⟶ C}
  {U : C ⟶ D} (A : F ⊣ U) (d : D) : SolutionSet U d :=
  sols_of_comma_initial U d (comma_initial_of_adjunction A d).

(*
The composite [universal_arrow_from_UMP → arrow_initial →
   weakly_initial_of_initial → sols_of_wif] reduces all the way to the
   unit. 

--------
复合材料 [universal_arrow_from_UMP → arrow_initial →
 weakly_initial_of_initial→sols_of_wif]一直减少到
 单位。 
*)

Definition solution_set_via_comma_index {C D : Category} {F : D ⟶ C}
  {U : C ⟶ D} (A : F ⊣ U) (d : D) :
  sol_index (solution_set_of_adjunction_via_comma A d)
    = sol_index (solution_set_of_adjunction A d) := eq_refl.

Definition solution_set_via_comma_obj {C D : Category} {F : D ⟶ C}
  {U : C ⟶ D} (A : F ⊣ U) (d : D)
  (i : sol_index (solution_set_of_adjunction_via_comma A d)) :
  sol_obj (solution_set_of_adjunction_via_comma A d) i = F d := eq_refl.

Definition solution_set_via_comma_arr {C D : Category} {F : D ⟶ C}
  {U : C ⟶ D} (A : F ⊣ U) (d : D)
  (i : sol_index (solution_set_of_adjunction_via_comma A d)) :
  sol_arr (solution_set_of_adjunction_via_comma A d) i
    = @unit _ _ _ _ A d := eq_refl.

(** ** The characterization  / ** 表征*)

(*
Mac Lane §V.6 Theorem 2 / Awodey §9.8 Theorem 28.  [Defined], so that the
   readbacks below hold; and the reverse half is [GAFT] ITSELF rather than
   [GAFT_via_comma_initial], because [GAFT] is [Qed] and the two are not
   convertible — building it from the latter stops [GAFT_iff_rev_is_GAFT]
   below, this file's own readback, before Adjunction/GAFT/Sets.v's
   [Sets_Id_has_left_is_GAFT_at_Sets_Id] is ever reached.  Both readbacks
   stop; the nearer one is the one that fires. 

--------
Mac Lane §V.6 定理 2 / Awodey §9.8 定理 28. [Defined]，因此
 回读低于保持； 后半部分是 [GAFT] ITSELF 而不是
 [GAFT_via_comma_initial]，因为[GAFT]是[Qed]并且两者不是
 敞篷车 - 从后者构建它停止 [GAFT_iff_rev_is_GAFT]
 下面是该文件自己的回读，位于 Adjunction/GAFT/Sets.v 之前
 [Sets_Id_has_left_is_GAFT_at_Sets_Id] 已经达到。 两次回读
 停止； 较近的就是开火的。 
*)

Theorem GAFT_iff {C D : Category} (U : C ⟶ D) (comp : @Complete C) :
  { F : D ⟶ C & F ⊣ U }
    ↔ (@PreservesImageLimit C D U * (∀ d : D, SolutionSet U d)).
Proof.
  split.
  - intros [F A].
    split.
    + exact (right_adjoint_PreservesImageLimit A).
    + exact (solution_set_of_adjunction A).
  - intros [cont sols].
    exact (GAFT U comp cont sols).
Defined.

Definition GAFT_iff_fwd {C D : Category} (U : C ⟶ D) (comp : @Complete C)
  (H : { F : D ⟶ C & F ⊣ U }) :
  @PreservesImageLimit C D U * (∀ d : D, SolutionSet U d) :=
  fst (GAFT_iff U comp) H.

Definition GAFT_iff_rev {C D : Category} (U : C ⟶ D) (comp : @Complete C)
  (H : @PreservesImageLimit C D U * (∀ d : D, SolutionSet U d)) :
  { F : D ⟶ C & F ⊣ U } :=
  snd (GAFT_iff U comp) H.

(* The reverse half IS GAFT, on the nose.  / 反面的一半是 GAFT，在鼻子上。*)

Definition GAFT_iff_rev_is_GAFT {C D : Category} (U : C ⟶ D)
  (comp : @Complete C) (cont : @PreservesImageLimit C D U)
  (sols : ∀ d : D, SolutionSet U d) :
  GAFT_iff_rev U comp (cont, sols) = GAFT U comp cont sols := eq_refl.
