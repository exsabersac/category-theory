(*
 The poset category 3: four presentations, its freeness, and its
 composition table.

 SOURCES.  Awodey, *Category Theory* (1st ed., CMU pre-print, September
 2005), §4.5 Exercise 3 (printed p. 91) -- give four different
 presentations by generators and relations of the poset category 3, and
 say whether 3 is free.  Fong & Spivak, *Seven Sketches in
 Compositionality* (CUP, 2019), §3.2.1 Exercise 3.10 (printed p. 83) --
 write out the composition table of the category 3, whose six morphisms
 are three identities, two generating steps, and their composite.

 A CORRECTION TO THE CATALOGUE ENTRY.  Its current-state note says that
 the category 3 “is not presented by generators and relations, and its
 freeness is not addressed”.  BOTH halves were already false at the
 commit this file was written against, and both are measured here rather
 than restated:

 - [Construction/Free/Quiver/Presented.v] already carries
 one presentation of 3 in full -- [Ord3Node], [Ord3Edge]
 (generators a : 0 -> 1, b : 1 -> 2, c : 0 -> 2),
 [Ord3Quiver], [ord3_path_c], [ord3_path_ab],
 [ord3_free_distinct], [Ord3_count], [Ord3_lhs], [Ord3_rhs],
 [Ord3Eqns], [Ord3Finite], [Ord3Presentation], [Ord3] and
 [ord3_relation_holds].  That is the commutative-triangle
 presentation, and it is CONSUMED here as presentation (i); not one
 of those constants is rebuilt.

 - [Construction/Free/Quiver/Examples.v] already carries
 [ordinal_free m : FreeOnQuiver (LinQuiver m) ≅[StrictCat] Ordinal m]
 (with [ordinal_free_S] and [ordinal_free_0] beneath it, the
 weaker [ordinal_free_Cat] beside it, and the m = 3 instance
 [chain_free]).  So “is 3 free?  yes, on the linear two-edge
 graph” is [ordinal_free 3], ALREADY PROVED.  It is CONSUMED here as
 [three_is_free]; no freeness statement is reproved.

 - [Theory/Shapes.v] already names all three non-identity
 arrows of [_3] -- [three_01], [three_12] and
 [three_02 := three_12 ∘ three_01].  This file's [three_a],
 [three_b] and [three_c] ARE those terms
 ([three_a_is_shapes]/[three_b_is_shapes]/[three_c_is_shapes], all
 [eq_refl]); they are respelled as raw [le_t] terms so that the
 composition table below is a COMPUTATION rather than the unfolding
 of [three_02]'s definition, and the identification is recorded
 rather than the prior art passed over.

 WHAT IS DELIVERED.  Four presentations of the category 3, each shown
 isomorphic to [Instance/Ordinal.v]'s [_3] in [StrictCat], whose
 hom-setoid demands Leibniz equality on objects where [Cat]'s identifies
 naturally isomorphic functors ([Instance/StrictCat.v]'s header records
 that contrast).  No implication between the two readings is proved
 here; [StrictCat] is simply what the comparisons below inhabit:

 (i)   [Ord3]    -- three generators a, b, c; one relation c = b ∘ a.
 CONSUMED from Presented.v.  [Ord3_iso].
 (ii)  [Lin3]    -- two generators a, b; NO relations.  This is the
 free presentation, and [Lin3_iso] is built by
 CONSUMING [ordinal_free 3].
 (iii) [Ord3Rev] -- three generators a, b, c; one relation b ∘ a = c,
 the SAME equation written the other way round.
 [Ord3Rev_iso].
 (iv)  [Tri4]    -- four generators a, b, c, d; two relations
 c = b ∘ a and d = b ∘ a.  [Tri4_iso].

 WHAT MAKES THE FOUR DISTINCT, machine-checked rather than asserted.
 Their generator counts are 3, 2, 3 and 4 ([ord3_gen_total_3],
 [lin3_gen_total_2], [tri4_gen_total_4]) and their relation counts 1, 0,
 1 and 2 ([ord3_rel_total_1], [lin3_rel_total_0], [ord3_rev_rel_total_1],
 [tri4_rel_total_2]), so (i), (ii) and (iv) differ pairwise already in
 that data ([three_presentation_counts_differ]); and (iii) shares (i)'s
 quiver ([ord3_rev_shares_ord3_quiver], [eq_refl]), so it differs from
 (ii) and (iv) by those same numbers.  (i) and (iii)
 agree on both counts and are told apart by their equations instead: the
 left-hand side of (i)'s single equation is [ord3_path_c] and of (iii)'s
 is [ord3_path_ab] ([ord3_lhs_is_c], [ord3_rev_lhs_is_ab], both
 [eq_refl]), and those two paths are NOT the same arrow of the free
 category -- that is Presented.v's own [ord3_free_distinct], consumed as
 [ord3_presentations_differ].  No single constant states “the four
 records are pairwise distinct”; what is shipped is those numbers and
 that separation, from which a reader reads it off.

 THE ENGINE for the comparisons is one general lemma, [pq_same_iso]:
 two relation families that generate the same congruence present
 isomorphic categories, by identity-on-everything functors.  It is what
 relates (i) and (iii) with no path analysis at all, and its hypotheses
 are exactly what a presentation obtained from another by adding a
 derivable equation supplies.
 Its degenerate case [pq_trivial_iso] -- a relation family every member
 of which is already an [≈] presents the base category itself -- is what
 turns (ii) into a statement about [FreeOnQuiver (LinQuiver 3)] and so
 lets [ordinal_free 3] be applied.

 For (i) and (iv) the comparison needs the paths of the free category
 classified.  That is [o3_classify] and [t4_classify], written in
 [Instance/Square.v]'s [wsq_spec]/[wsq_classify] idiom: put the endpoint
 analysis in the SPECIFICATION, then induct on the path.  The
 classifications are stated at LEIBNIZ equality, not [≈] -- a deliberate
 strengthening, following [Instance/Square.v], and the reason
 the free arrow counts below mean what they say.  From them [ord3_thin]
 and [tri4_thin] follow, and thinness is what makes the two comparison
 functors mutually inverse.

 THE COMPOSITION TABLE (Seven Sketches Exercise 3.10) is stated at [_3]
 itself, since all four presentations are shown isomorphic to it.  Six
 morphisms ([three_arrow_total_6]), of which three are identities
 ([three_identity_total_3]) and three are not
 ([three_nonidentity_total_3]); the enumeration is duplicate-free
 ([three_pairs_nodup]), sound ([three_pairs_sound]) and complete
 ([three_pairs_complete]); the three descending hom-sets are EMPTY
 ([three_no_10], [three_no_20], [three_no_21]).  All ten composable
 pairs are computed, and every one holds at LEIBNIZ equality by
 [eq_refl] -- composition in [Ordinal n] is [le_t_trans], a [Fixpoint]
 that reduces on closed indices -- so
 [three_table_ba : three_b ∘ three_a = three_c] is an equation of terms
 and not merely of [≈]-classes.  READ WHAT THE TABLE CARRIES, though:
 [_3] is thin AND its hom-setoid is Leibniz equality, so EVERY equation
 between parallel arrows already follows from [Instance/Ordinal.v]'s
 [ord_thin] -- what the ten entries pin down is therefore the
 INHABITATION pattern, which endpoint pairs carry an arrow at all,
 rather than the composites; the claim made for them is only that they
 hold at Leibniz rather than at [≈], and the non-vacuity paragraph
 below is what supplies the content.  Equality of morphisms is DECIDED by
 [three_mor_eq_dec], on the bundled morphism type [OrdMor 3] of
 [Instance/Ordinal.v], through that file's
 [ord_coords_inj]: a morphism of 3 is determined by its pair of
 endpoint indices.  At the level of parallel arrows the decision is
 total and always answers yes, which is exactly what thinness says
 ([three_equiv_dec], [ord3_equiv_dec], [ord3_rev_equiv_dec],
 [tri4_equiv_dec], [lin3_equiv_dec]).

 WHY THE COUNT OF SIX IS NOT VACUOUS.  A collapsed category would count
 fewer.  The three objects are pairwise distinct
 ([three_objects_distinct]); the three descending hom-sets are empty, so
 3 is not a preorder in which everything is related; and the generating
 step a is not invertible ([three_a_not_iso]), so 3 is not a groupoid
 with three objects in disguise.  The quotients are not vacuous either,
 and that is measured as an arithmetic: the free category on (i)'s
 quiver has SEVEN arrows and the presented one six, so exactly one
 identification happened ([ord3_merge_arithmetic]); on (iv)'s quiver the
 free category has EIGHT, so exactly two did ([tri4_merge_arithmetic]).
 Read those two numbers at their strength: what is PROVED is that the
 count functions [ord3_free_homcount] and [tri4_free_homcount] fold to
 seven and to eight, and what makes them the right functions is the
 classifications above together with the distinctness of the competing
 0 -> 2 paths -- [ord3_free_distinct] for (i), and [t4_c_ne_d],
 [t4_c_ne_ab], [t4_d_ne_ab] for (iv).

 WHAT IS NOT DELIVERED.  No walking isomorphism, no cyclic group and no
 one-object presented category -- those are other modules of this issue
 ([Instance/Presented/Cyclic.v] is the one already in tree).  No
 presentation of 3 is exhibited that generates a DIFFERENT category, so
 nothing here says how much a presentation may be changed before the
 category moves.  No Tietze transformations relating the four
 presentations as data, and no notion of equivalence of presentations:
 the four are compared only through the categories they present.  The
 isomorphisms are not compared with each other, so nothing says that
 (i)'s and (iii)'s comparison functors agree.  No universal property is
 restated: Presented.v's [PresentedFunctor] is applied, and neither it
 nor [presented_universal] is re-derived.  Nothing is said about
 [Theory/Metacategory.v]'s unrelated [Three], whose header
 records that it has no objects at all -- and note that this
 module's own short name is [Three] too, so a file importing both has a
 module and a constant of that name in scope at once; nothing declared
 below is called [Three].  No decision procedure for equality of
 objects of the presented categories is packaged beyond the two
 [eq_dec]s used internally.  And no count is given for the free category
 on (ii)'s quiver as a fold: [three_arrow_total_6] counts the arrows of
 [_3] and [three_is_free] relates the two categories, but no transfer of
 a number along an isomorphism of categories is formalized anywhere in
 this file. 

 --------
 偏序集范畴 3：四种表示形式，它的自由性，以及它的复合表。

 来源。Awodey，《范畴论》（第1版，CMU 预印本，2005年9月），§4.5 习题 3（印刷版第91页）——通过生成元和关系给出偏序集范畴 3 的四种不同表示形式，并说明 3 是否是自由的。Fong & Spivak，《复合性的七个描绘》（剑桥大学出版社，2019），§3.2.1 习题 3.10（印刷版第83页）——写出范畴 3 的复合表，该范畴的六个态射为三个恒等态射、两个生成步骤及它们的复合。对目录条目的更正。目前的状态说明说类别3“没有通过生成元和关系呈现，并且其自由性没有被讨论”。在写入此文件的提交时，这两部分都是错误的，这里进行衡量而不是重述：

 - [Construction/Free/Quiver/Presented.v] 已经完整地提供了类别3的一种表示——[Ord3Node]、[Ord3Edge]（生成元 a : 0 -> 1, b : 1 -> 2, c : 0 -> 2）、[Ord3Quiver]、[ord3_path_c]、[ord3_path_ab]、[ord3_free_distinct]、[Ord3_count]、[Ord3_lhs]、[Ord3_rhs]、[Ord3Eqns]、[Ord3Finite]、[Ord3Presentation]、[Ord3] 和 [ord3_relation_holds]。这就是交换三角形表示，并且在这里被用作表示 (i)；这些常量中没有一个被重新构建。-  [Construction/Free/Quiver/Examples.v] 已经包含 [ordinal_free m : FreeOnQuiver (LinQuiver m) ≅[StrictCat] 序数 m]（其下有 [ordinal_free_S] 和 [ordinal_free_0]，旁边有较弱的 [ordinal_free_Cat]，以及 m = 3 的实例 [chain_free]）。所以 “3 是自由的吗？是的，在线性二边图上” 是 [ordinal_free 3]，已经被证明。在这里它被作为 [three_is_free] 使用；没有重新证明任何自由性声明。- [Theory/Shapes.v] 已经命名了 [_3] 的所有三个非恒等箭头——[three_01]、[three_12] 和 [three_02 := three_12 ∘ three_01]。这个文件的 [three_a]、[three_b] 和 [three_c] 是那些项（[three_a_is_shapes] / [three_b_is_shapes] / [three_c_is_shapes]，全部是 [eq_refl]）；它们被重新拼写为原始 [le_t] 项，以便下面的组合表是一次计算，而不是展开 [three_02] 的定义，并且该标识被记录下来，而不是忽略已有成果。交付内容。类别 3 的四个呈现，每个呈现都同构于 [Instance/Ordinal.v] 的 [_3] 在 [StrictCat] 中，其同态集合要求在对象上具有莱布尼茨相等性，其中 [Cat] 自然地识别同构函子（[Instance/StrictCat.v] 的标题记录了对比）。这里没有证明两种解读之间的任何蕴涵；[StrictCat] 只是下述比较所依附的对象：(i)    [Ord3]     -- 三个生成元 a、b、c；一个关系 c = b ∘ a。
 从 Presented.v 消耗得到 [Ord3_iso] 。
 (ii)   [Lin3]     -- 两个生成元 a、b；没有关系。这是自由表示，[Lin3_iso] 通过消耗 [ordinal_free 3] 构建。
 (iii)  [Ord3Rev]     -- 三个生成元 a、b、c；一个关系 b ∘ a = c，相同的等式以另一种方式书写。
 [Ord3Rev_iso] 。
 (iv)   [Tri4]     -- 四个生成元 a、b、c、d；两个关系 c = b ∘ a 和 d = b ∘ a。[Tri4_iso] 。是什么让这四个不同，经过机器检查而非断言。它们的生成元计数分别是 3、2、3 和 4（[ord3_gen_total_3], [lin3_gen_total_2], [tri4_gen_total_4]），它们的关系计数分别是 1、0、1 和 2（[ord3_rel_total_1], [lin3_rel_total_0], [ord3_rev_rel_total_1], [tri4_rel_total_2]），所以 (i)、(ii) 和 (iv) 已经通过这些数据在成对上有所不同（[three_presentation_counts_differ]）；而 (iii) 与 (i) 共享箭图（[ord3_rev_shares_ord3_quiver], [eq_refl]），因此它在这些数字上与 (ii) 和 (iv) 不同。(i) 和 (iii) 两者在计数上相同，而是通过它们的方程区分：(i) 的单个方程的左边是 [ord3_path_c]，(iii) 的左边是 [ord3_path_ab]（[ord3_lhs_is_c], [ord3_rev_lhs_is_ab]，都是 [eq_refl]），而这两条路径不是自由范畴中的同一箭——也就是 Presented.v 自身的 [ord3_free_distinct]，被作为 [ord3_presentations_differ] 使用。没有任何单一常量声明“这四个记录两两不同”；所传递的是这些数字和那个分离，从中读者可以读出它。  用于比较的引擎是一个通用引理，[pq_same_iso]：两个生成相同同余的关系族通过对所有事物的恒等函子呈现同构的范畴。它恰好将 (i) 与 (iii) 关联起来，而完全不需要路径分析，其假设正是通过添加可推导方程从另一个陈述获得的陈述所提供的。 其退化情况 [pq_trivial_iso] —— 一个其每个成员已经是 [≈] 的关系族呈现基础范畴本身 —— 正是将 (ii) 转化为关于 [FreeOnQuiver (LinQuiver 3)] 的陈述，并因此允许应用 [ordinal_free 3]。对于 (i) 和 (iv)，比较需要自由范畴路径的分类。也就是说，[o3_classify] 和 [t4_classify]，用 [Instance/Square.v] 的 [wsq_spec] / [wsq_classify] 习惯表达：将端点分析放在规范中，然后对路径进行归纳。分类是在莱布尼茨等式下陈述的，而不是 [≈] —— 这是一个刻意的强化，遵循 [Instance/Square.v]，并且下面自由箭头的计数正是它们所表示的意思。由此可以得到 [ord3_thin] 和 [tri4_thin]，薄性正是使这两个比较函子互为逆的原因。组合表（七个草图练习 3.10）在 [_3] 本身中给出，因为所有四个展示都与其同构。六个态射（[three_arrow_total_6]），其中三个是恒等态射（[three_identity_total_3]），三个不是（[three_nonidentity_total_3]）；枚举没有重复（[three_pairs_nodup]）、可靠（[three_pairs_sound]）且完整（[three_pairs_complete]）；三个下降的 Hom 集为空（[three_no_10]、[three_no_20]、[three_no_21]）。所有十个可组合对都已计算，并且每个都在莱布尼茨等式下成立 [eq_refl] — [Ordinal n] 中的组合是 [le_t_trans]，一个 [Fixpoint]，它在封闭指标上可约 —— 因此 [three_table_ba : three_b ∘ three_a = three_c] 是项的等式，而不仅仅是 [≈] 类的等式。读表格所包含的内容，不过：
 [_3] 是薄的，并且它的同构集合是莱布尼茨等式，所以平行箭头之间的每个方程已经可以从 [Instance/Ordinal.v] 的 [ord_thin] 推出——因此这十个条目确定的就是存在模式，即哪些端点对携带箭头，而不是复合；对它们的主张仅仅是它们在莱布尼茨下成立，而不是在 [≈] 下成立，下面的非空段落提供了内容。态射的等式由 [three_mor_eq_dec] 决定，在 [Instance/Ordinal.v] 的捆绑态射类型 [OrdMor 3] 上，通过该文件的 [ord_coords_inj]：一个三值态射由其端点索引对决定。在平行箭头的层面上，决策是完全的，并且总是回答是，这正是薄弱性所说的（[three_equiv_dec]，[ord3_equiv_dec]，[ord3_rev_equiv_dec]，[tri4_equiv_dec]，[lin3_equiv_dec]）。为什么计数为六并非空洞。一个崩塌的范畴会计数更少。三个对象两两不同 ([three_objects_distinct])；三个下降的同态集为空，所以3不是一个一切都相关的预序；并且生成步骤a不可逆 ([three_a_not_iso])，所以3不是一个伪装成三个对象的群范畴。这些商也不是空的，这可以通过算术来衡量：(i)的箭图上的自由范畴有七个箭头，而所呈现的范畴有六个，所以恰好发生了一次识别 ([ord3_merge_arithmetic])；(iv)的箭图上的自由范畴有八个箭头，所以恰好发生了两次 ([tri4_merge_arithmetic])。按它们的强度读取那两个数字：已证明的是计数函数 [ord3_free_homcount] 和 [tri4_free_homcount] 能折叠成七和八，使它们成为正确函数的是上述分类以及竞争的 0 -> 2 路径的不同性——(i) 的 [ord3_free_distinct]，以及 (iv) 的 [t4_c_ne_d]、[t4_c_ne_ab]、[t4_d_ne_ab]。未实现的内容。没有行同构，没有循环群，也没有单对象表示范畴——这些都是本期的其他模块（[Instance/Presented/Cyclic.v] 已在树中）。没有展示生成不同范畴的三的表示，所以这里没有说明在范畴发生变化之前，一个表示可以被改变多少。没有将四个表示作为数据进行 Tietze 变换，也没有表示等价的概念：四个表示只是通过它们呈现的范畴来进行比较。同构之间没有进行比较，所以没有说明 (i) 和 (iii) 的比较函子是否一致。没有重述任何泛性质：Presented.v 的 [PresentedFunctor] 已应用，且它和 [presented_universal] 都没有被重新推导。没有说明 [Theory/Metacategory.v] 与无关的 [Three]，其头文件记录它根本没有任何对象——并且注意这个模块自己的短名称也是 [Three]，因此一个导入两者的文件同时会在作用域中有一个同名的模块和常量；下面声明的东西没有一个叫 [Three]。在所呈现的类别对象的相等性方面，没有封装的判定程序，除了内部使用的两个 [eq_dec]。而且对于 (ii) 的箭形图上的自由类别没有给出计数：[three_arrow_total_6] 计数 [_3] 的箭头，而 [three_is_free] 关联两个类别，但在这个文件中没有在类别同构下传递数字的形式化操作。
*)

Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Free.Quiver.Presented.
Require Import Category.Construction.Free.Quiver.Examples.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Ordinal.
Require Import Category.Theory.Shapes.
Require Import Category.Instance.StrictCat.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Vectors.Fin.
Require Import Coq.Lists.List.

Generalizable All Variables.

#[local] Existing Instance edgeset.

#[local] Obligation Tactic := idtac.

(* ---------- (A) presentations that generate the same congruence ---------- / ----------（A）产生相同一致性的演示---------- *)

(*
 Leastness of the generated congruence, in the shape a comparison of two
 presentations wants: it is enough that every generating equation of [R]
 is DERIVABLE in [S], not that it is one of [S]'s own generators. 

 --------
 生成的合同的最小性，在比较两个表示的形式上需要：只要 [R] 的每一个生成方程都可以在 [S] 中推导出来就足够了，而不需要它是 [S] 自己的生成元之一。
*)
(*
 [Construction/Quotient.v]'s [cc_least] is exactly this, applied at
 the congruence [CongClosure S].  That file's own comment on the sibling
 [cc_kernel] says such a passage is “a one-line corollary of
 leastness ... not a second induction”, so this is a term and not an
 induction. 

 --------
 [Construction/Quotient.v] 的 [cc_least] 正是如此，应用在同余 [CongClosure S] 上。该文件自己对同级 [cc_kernel] 的注释说这样的段落是“最小性的一行推论……不是第二次归纳”，所以这是一个项而不是归纳。
*)
Definition pq_cc_mono {C : Category} (R S : HomRelT C)
  (HRS : ∀ x y (f g : x ~> y), R x y f g → CongClosure S x y f g)
  {x y : C} {f g : x ~> y} :
  CongClosure R x y f g → CongClosure S x y f g :=
  @cc_least C R (CongClosure S) (CongClosure_Congruence S) HRS x y f g.

Section SameCong.

Context {C : Category} (R S : HomRelT C).
Context (HRS : ∀ x y (f g : x ~> y), R x y f g → CongClosure S x y f g).
Context (HSR : ∀ x y (f g : x ~> y), S x y f g → CongClosure R x y f g).

(*
 Both quotients have the same objects, the same hom TYPES, the same
 identities and the same composition -- only the hom-setoid differs -- so
 the comparison is the identity on everything, and all its content is the
 respectfulness obligation. 

 --------
 两个商都有相同的对象、相同的同态类型、相同的恒等式和相同的组合——唯一不同的是同态集——所以比较在所有方面都是恒等的，其全部内容就是遵守尊重性约束。
*)
Program Definition pq_same_to : QuotientCong C R ⟶ QuotientCong C S := {|
  fobj := fun x => x;
  fmap := fun x y f => f
|}.
Next Obligation. intros a b f g H; exact (pq_cc_mono R S HRS H). Qed.
Next Obligation. intros; apply cc_refl. Qed.
Next Obligation. intros; apply cc_refl. Qed.

Program Definition pq_same_from : QuotientCong C S ⟶ QuotientCong C R := {|
  fobj := fun x => x;
  fmap := fun x y f => f
|}.
Next Obligation. intros a b f g H; exact (pq_cc_mono S R HSR H). Qed.
Next Obligation. intros; apply cc_refl. Qed.
Next Obligation. intros; apply cc_refl. Qed.

(*
 Two presentations over ONE quiver whose relations generate the same
 congruence present isomorphic categories -- and at [StrictCat], since
 the object components are [eq_refl]. 

 --------
 关于一个箭袋的两个表示，其关系生成相同的合同，则表现为同构的范畴——并且在 [StrictCat] 处，由于对象分量是 [eq_refl]。
*)
Program Definition pq_same_iso :
  QuotientCong C R ≅[StrictCat] QuotientCong C S := {|
  to := pq_same_to;
  from := pq_same_from
|}.
Next Obligation.
  exists (fun x => eq_refl); intros x y f; simpl; apply cc_refl.
Qed.
Next Obligation.
  exists (fun x => eq_refl); intros x y f; simpl; apply cc_refl.
Qed.

End SameCong.

Section Trivial.

Context {C : Category} (R : HomRelT C).
Context (HF : ∀ x y (f g : x ~> y), R x y f g → f ≈ g).

(*
 The degenerate case: relations that assert nothing new.  [Id] merges
 them, so the library's own lift is the collapsing functor. 

 --------
 退化情况：那些没有断言任何新内容的关系。[Id] 将它们合并，因此库自身的 lift 就是坍缩范畴函子。
*)
Definition pq_collapse : QuotientCong C R ⟶ C :=
  QuotientCongLift R Id[C] HF.

Program Definition pq_trivial_iso : QuotientCong C R ≅[StrictCat] C := {|
  to := pq_collapse;
  from := QuotientCongProj R
|}.
Next Obligation.
  exists (fun x => eq_refl); intros x y f; simpl; reflexivity.
Qed.
Next Obligation.
  exists (fun x => eq_refl); intros x y f; simpl; apply cc_refl.
Qed.

End Trivial.

(* ---------- (B) the three objects of 3 ---------- / ----------（B）3的三个对象---------- *)

(* [Ord_obj 3] is a record over [nat] with a bound, not a three-constructor inductive, so case analysis on it has to be proved. The fourth branch is where the bound is spent. / [Ord_obj 3] 是一个带有界的 [nat] 上的记录，而不是一个三构造子归纳类型，因此对它进行模式匹配需要证明。第四个分支是消耗界的地方。 *)
Lemma ord3_cases (x : Ord_obj 3) :
  ((x = ord3_0) + (x = ord3_1) + (x = ord3_2))%type.
Proof.
  destruct x as [i H]; destruct i as [| [| [| i]]].
  - left; left; apply ord_obj_eq; reflexivity.
  - left; right; apply ord_obj_eq; reflexivity.
  - right; apply ord_obj_eq; reflexivity.
  - exfalso.
    exact (le_t_zero_absurd
             (le_t_SS_inv (le_t_SS_inv (le_t_SS_inv H)))).
Qed.

Lemma three_obj_eq_dec (x y : Ord_obj 3) : {x = y} + {x <> y}.
Proof.
  destruct (Nat.eq_dec (ord_val x) (ord_val y)) as [E | E].
  - left; exact (ord_obj_eq E).
  - right; intro Hxy; apply E; now rewrite Hxy.
Defined.

Lemma three_objects_distinct :
  ((ord3_0 = ord3_1 → False) * (ord3_1 = ord3_2 → False) *
   (ord3_0 = ord3_2 → False))%type.
Proof.
  repeat split; intro H; apply (f_equal ord_val) in H; discriminate H.
Qed.

Definition three_nodes : list (Ord_obj 3) :=
  ord3_0 :: ord3_1 :: ord3_2 :: nil.

Lemma three_nodes_complete (x : Ord_obj 3) : In x three_nodes.
Proof.
  destruct (ord3_cases x) as [[E | E] | E]; subst; simpl; tauto.
Qed.

Lemma three_nodes_nodup : NoDup three_nodes.
Proof.
  pose proof three_objects_distinct as [[H01 H12] H02].
  repeat constructor; simpl; intuition congruence.
Qed.

Definition three_all_pairs : list (Ord_obj 3 * Ord_obj 3) :=
  list_prod three_nodes three_nodes.

Example three_all_pairs_9 : length three_all_pairs = 9%nat := eq_refl.

Lemma three_all_pairs_complete (x y : Ord_obj 3) :
  In (x, y) three_all_pairs.
Proof. apply in_prod; apply three_nodes_complete. Qed.

(* ---------- (C) the six morphisms of 3, and the composition table ------- / ---------- (C) 3 的六个态射，以及组合表 ------- *)

(*
 Seven Sketches Exercise 3.10.  The two generating steps and the one
 composite; the three identities are the category's own. 

 --------
 七个草图 练习 3.10。两个生成步骤和一个复合步骤；这三个同一性是该范畴自身的。
*)
Definition three_a : ord3_0 ~{_3}~> ord3_1 := le_t_S le_t_n.
Definition three_b : ord3_1 ~{_3}~> ord3_2 := le_t_S le_t_n.
Definition three_c : ord3_0 ~{_3}~> ord3_2 := le_t_S (le_t_S le_t_n).

(*
 PRIOR ART, and the three are not merely analogous but the SAME TERMS:
 [Theory/Shapes.v] already names all three non-identity arrows
 of [_3].  They are spelled out again here rather than consumed for one
 reason, and it is a reason about STRENGTH: that file DEFINES its 0 -> 2
 arrow as the composite ([three_02 := three_12 ∘ three_01]), so with it
 [three_table_ba] below would hold by unfolding a definition, where
 written independently as a raw [le_t] term it holds because
 [le_t_trans] COMPUTES.  The identification is recorded instead. 

 --------
 现有技术，而且这三者不仅仅是类似的，而是相同的术语：
 [Theory/Shapes.v] 已经命名了 [_3] 的所有三个非同一性箭头。这里再次列出它们，而不是只为了使用一次，其原因是关于强度的问题：该文件将其 0 -> 2 的箭头定义为复合箭头（[three_02 := three_12 ∘ three_01]），因此在下面的 [three_table_ba] 中，通过展开定义可以成立，而作为独立书写的原始 [le_t] 项，它成立是因为 [le_t_trans] 可以计算。相应的标识记录下来了。
*)
Example three_a_is_shapes : three_a = three_01 := eq_refl.
Example three_b_is_shapes : three_b = three_12 := eq_refl.
Example three_c_is_shapes : three_c = three_02 := eq_refl.

Definition three_id0 : ord3_0 ~{_3}~> ord3_0 := id.
Definition three_id1 : ord3_1 ~{_3}~> ord3_1 := id.
Definition three_id2 : ord3_2 ~{_3}~> ord3_2 := id.

(* The three descending hom-sets are empty. This is what keeps 3 from being a preorder in which everything is related, and it is used again below to prove the enumeration complete. / 三个下降的同态集是空的。这就是为什么 3 不是一个所有元素都相关的预序，它在下面又被用来证明枚举的完整性。 *)
Theorem three_no_10 (p : ord3_1 ~{_3}~> ord3_0) : False.
Proof. exact (le_t_zero_absurd p). Qed.

Theorem three_no_20 (p : ord3_2 ~{_3}~> ord3_0) : False.
Proof. exact (le_t_zero_absurd p). Qed.

Theorem three_no_21 (p : ord3_2 ~{_3}~> ord3_1) : False.
Proof. exact (le_t_zero_absurd (le_t_SS_inv p)). Qed.

(*
 THE TABLE.  Ten composable pairs, every one an equation of TERMS:
 composition in [Ordinal n] is [le_t_trans], which recurses on its second
 argument and so reduces outright on these closed indices.  The [≈] of
 [Ordinal n] is [Morphism_equality], i.e. Leibniz equality, so stating
 these with [=] is the same claim read at its strongest, and no
 [ord_thin] appeal is needed anywhere in the table. 

 --------
 表格。十对可组合的项，每一对都是一个项的等式：
 在 [Ordinal n] 中的组合是 [le_t_trans]，它在其第二个参数上递归，因此在这些封闭的索引上直接化简。[Ordinal n] 的 [≈] 是 [Morphism_equality]，即莱布尼茨等式，因此使用 [=] 陈述这些就是在最强的情况下的同一主张，并且表格中的任何地方都不需要 [ord_thin] 的引用。
*)
Example three_table_ba : three_b ∘ three_a = three_c := eq_refl.

Example three_table_a_id0 : three_a ∘ three_id0 = three_a := eq_refl.
Example three_table_id1_a : three_id1 ∘ three_a = three_a := eq_refl.
Example three_table_b_id1 : three_b ∘ three_id1 = three_b := eq_refl.
Example three_table_id2_b : three_id2 ∘ three_b = three_b := eq_refl.
Example three_table_c_id0 : three_c ∘ three_id0 = three_c := eq_refl.
Example three_table_id2_c : three_id2 ∘ three_c = three_c := eq_refl.

Example three_table_id0 : three_id0 ∘ three_id0 = three_id0 := eq_refl.
Example three_table_id1 : three_id1 ∘ three_id1 = three_id1 := eq_refl.
Example three_table_id2 : three_id2 ∘ three_id2 = three_id2 := eq_refl.

(* Every parallel pair agrees, so the table above is the whole of it: no further entry could name a different arrow. / 每一对平行箭头都一致，所以上表就是全部：没有其他条目可以命名不同的箭头。 *)
Theorem three_thin (x y : Ord_obj 3) (p q : x ~{_3}~> y) : p = q.
Proof. exact (ord_thin p q). Qed.

(*
 The six inhabited endpoint pairs: three loops, the two steps, and the
 composite. 

 --------
 六个有人居住的端点对：三个环路、两个步骤，以及复合体。
*)
Definition three_pairs : list (Ord_obj 3 * Ord_obj 3) :=
  (ord3_0, ord3_0) :: (ord3_1, ord3_1) :: (ord3_2, ord3_2) ::
  (ord3_0, ord3_1) :: (ord3_1, ord3_2) :: (ord3_0, ord3_2) :: nil.

Lemma three_pairs_nodup : NoDup three_pairs.
Proof.
  pose proof three_objects_distinct as [[H01 H12] H02].
  repeat constructor; simpl; intuition congruence.
Qed.

Theorem three_pairs_sound (q : Ord_obj 3 * Ord_obj 3) :
  In q three_pairs → fst q ~{_3}~> snd q.
Proof.
  pose proof three_objects_distinct as [[H01 H12] H02].
  destruct q as [x y]; intro H.
  destruct (ord3_cases x) as [[Ex | Ex] | Ex];
    destruct (ord3_cases y) as [[Ey | Ey] | Ey]; subst; simpl in H;
    solve [ exact three_id0 | exact three_id1 | exact three_id2
          | exact three_a | exact three_b | exact three_c
          | exfalso; intuition congruence ].
Qed.

Theorem three_pairs_complete (x y : Ord_obj 3) :
  (x ~{_3}~> y) → In (x, y) three_pairs.
Proof.
  intro p.
  destruct (ord3_cases x) as [[Ex | Ex] | Ex];
    destruct (ord3_cases y) as [[Ey | Ey] | Ey]; subst;
    solve [ simpl; tauto
          | exfalso; solve [ exact (three_no_10 p)
                           | exact (three_no_20 p)
                           | exact (three_no_21 p) ] ].
Qed.

(*
 The count, as a number.  [three_homcount] gives the number of arrows
 between each ordered pair of objects; the two lemmas either side of it
 say that it is 1 exactly on the listed pairs, and the per-pair
 statements above say what those numbers mean. 

 --------
 计数，作为一个数字。[three_homcount] 给出了每一对有序对象之间箭头的数量；它两边的两个引理说明它在所列的对上正好为 1，而上面的每对语句说明这些数字的含义。
*)
Definition three_homcount (x y : Ord_obj 3) : nat :=
  if Nat.leb (ord_val x) (ord_val y) then 1%nat else 0%nat.

Lemma three_homcount_in (x y : Ord_obj 3) :
  three_homcount x y = 1%nat → In (x, y) three_pairs.
Proof.
  destruct (ord3_cases x) as [[Ex | Ex] | Ex];
    destruct (ord3_cases y) as [[Ey | Ey] | Ey]; subst;
    solve [ intros _; simpl; tauto | discriminate ].
Qed.

Lemma three_in_homcount (x y : Ord_obj 3) :
  In (x, y) three_pairs → three_homcount x y = 1%nat.
Proof.
  pose proof three_objects_distinct as [[H01 H12] H02].
  destruct (ord3_cases x) as [[Ex | Ex] | Ex];
    destruct (ord3_cases y) as [[Ey | Ey] | Ey]; subst;
    solve [ intros _; reflexivity | simpl; intuition congruence ].
Qed.

Definition three_arrow_total : nat :=
  fold_right (fun q n => three_homcount (fst q) (snd q) + n)%nat 0%nat
    three_all_pairs.

(* Seven Sketches Exercise 3.10: six morphisms. / 七个草图 练习 3.10：六个同态。 *)
Theorem three_arrow_total_6 : three_arrow_total = 6%nat.
Proof. reflexivity. Qed.

Definition three_identity_total : nat :=
  fold_right (fun x n => three_homcount x x + n)%nat 0%nat three_nodes.

(* ...three of them identities... / ...他们三个身份... *)
Theorem three_identity_total_3 : three_identity_total = 3%nat.
Proof. reflexivity. Qed.

Definition three_nonidentity_total : nat :=
  (three_arrow_total - three_identity_total)%nat.

(* ...and three of them not: the two generating steps and the composite. / ...其中有三个不是：两个生成步骤和组合步骤。 *)
Theorem three_nonidentity_total_3 : three_nonidentity_total = 3%nat.
Proof. reflexivity. Qed.

(*
 [Instance/Ordinal.v]'s independent count of endpoint pairs, read at
 n = 3.  Its left side is TWICE the morphism count, and its proof there
 is one rewrite by [ord_pairs_length] and the closed form
 [ord_tri_closed], so the six above is confirmed by an argument that
 shares no text with the fold. 

 --------
 [Instance/Ordinal.v] 的独立端点对计数，读取于 n = 3。它的左侧是映射计数的两倍，其证明采用了 [ord_pairs_length] 的一次重写和封闭形式 [ord_tri_closed]，因此上面的六个通过一个与 fold 没有文本共享的论证得到确认。
*)
Corollary three_morphism_count : (2 * length (ord_pairs 3) = 3 * (3 + 1))%nat.
Proof. exact (ord_morphism_count 3). Qed.

Example three_ord_pairs_6 : length (ord_pairs 3) = 6%nat := ord_pairs_3.

(* ---------- deciding equality of morphisms ---------- / ---------- 决定态射的相等性 ---------- *)

(*
 A morphism of 3, bundled with its endpoints, is determined by the pair
 of endpoint indices -- objects by [ord_obj_eq], the arrow between them
 by thinness.  Both halves are [Instance/Ordinal.v]'s, consumed. 

 --------
 一个带有其端点的 3 的态射，由端点索引对决定——对象由 [ord_obj_eq] 表示，二者之间的箭头由薄性表示。两部分都是 [Instance/Ordinal.v]，并已使用。
*)
Theorem three_mor_eq_coords (a b : OrdMor 3) :
  ord_coords a = ord_coords b → a = b.
Proof. exact (@ord_coords_inj 3 a b). Qed.

Theorem three_coords_eq_mor (a b : OrdMor 3) :
  a = b → ord_coords a = ord_coords b.
Proof. intro E; now rewrite E. Qed.

(*
 Hence equality of morphisms is decided, by comparing two natural
 numbers. 

 --------
 因此，态射的相等是通过比较两个自然数来决定的。
*)
Definition three_mor_eq_dec (a b : OrdMor 3) : {a = b} + {a <> b}.
Proof.
  destruct (Nat.eq_dec (fst (ord_coords a)) (fst (ord_coords b))) as [E1 | E1].
  - destruct (Nat.eq_dec (snd (ord_coords a)) (snd (ord_coords b)))
      as [E2 | E2].
    + left; apply three_mor_eq_coords.
      destruct (ord_coords a), (ord_coords b); simpl in *; congruence.
    + right; intro E; apply E2; now rewrite E.
  - right; intro E; apply E1; now rewrite E.
Defined.

(*
 At the level of PARALLEL arrows the decision is total and always
 answers yes.  That is not a weakness of the procedure: it is exactly
 what thinness of 3 says, and all the content sits in the endpoint
 analysis above -- which pairs of objects carry an arrow at all. 

 --------
 在平行箭头的层面上，决策是完全的，并且总是回答“是”。这并不是该程序的弱点：这正是厚度为3所说明的，所有内容都位于上述端点分析中——哪些对象对携带箭头。
*)
Definition three_equiv_dec (x y : Ord_obj 3) (p q : x ~{_3}~> y) :
  ((p ≈ q) + (p ≈ q → False))%type := inl (three_thin x y p q).

(*
 Non-vacuity of the count of six.  A category with fewer objects, or one
 in which the step a were invertible, would count differently. 

 --------
 六的计数非空。一个对象较少的范畴，或其中步骤 a 可逆的范畴，其计数方式会不同。
*)
Theorem three_a_not_iso : @IsIsomorphism _3 ord3_0 ord3_1 three_a → False.
Proof. intros [g _ _]; exact (three_no_10 g). Qed.

(* ---------- (D) presentation (i): the commutative triangle ---------- / ---------- (D) 展示 (i)：交换三角形 ---------- *)

(*
 Generators a : 0 -> 1, b : 1 -> 2, c : 0 -> 2; one relation c = b ∘ a.
 Every piece of the presentation is [Construction/Free/Quiver/
 Presented.v]'s, CONSUMED: [Ord3Quiver], [Ord3Eqns], [Ord3Finite],
 [Ord3Presentation], [Ord3], [ord3_path_c], [ord3_path_ab],
 [ord3_free_distinct] and [ord3_relation_holds].  What is added here is
 the classification of the free paths, thinness, and the comparison with
 [_3]. 

 --------
 生成元 a : 0 -> 1, b : 1 -> 2, c : 0 -> 2；一个关系 c = b ∘ a。每个呈现的部分都是 [Construction/Free/Quiver/Presented.v] 的，已消耗: [Ord3Quiver], [Ord3Eqns], [Ord3Finite], [Ord3Presentation], [Ord3], [ord3_path_c], [ord3_path_ab], [ord3_free_distinct] 和 [ord3_relation_holds]。这里新增的是自由路径的分类、稀疏性，以及与 [_3] 的比较。
*)
Example three_pres_i_is_Ord3 : FinitelyPresented Ord3Presentation = Ord3 :=
  eq_refl.

Definition FreeOrd3 : Category := FreeOnQuiver Ord3Quiver.

Definition o3_a : Ord3_0 ~{FreeOrd3}~> Ord3_1 :=
  tlist_singleton (B:=@edges Ord3Quiver) Ord3_a.
Definition o3_b : Ord3_1 ~{FreeOrd3}~> Ord3_2 :=
  tlist_singleton (B:=@edges Ord3Quiver) Ord3_b.

(*
 The specification: for each ordered pair of nodes, exactly which paths
 join them.  [False] marks the three pairs joined by no path.  The
 equalities are LEIBNIZ, not [≈] -- the strengthening
 [Instance/Square.v] documents, and what makes the free count
 below a count of arrows rather than of [≈]-classes. 

 --------
 规格说明：对于每一对有序节点，准确地说明哪些路径将它们连接起来。[False] 标记了三对没有路径连接的节点。等式是 LEIBNIZ 的，而不是 [≈]——增强的 [Instance/Square.v] 记录了这些内容，并且使得下面的自由计数是箭头的计数，而不是 [≈] 类的计数。
*)
Definition o3_spec (y : Ord3Node) :
  ∀ x : Ord3Node, (x ~{FreeOrd3}~> y) → Type :=
  match y as y0 return ∀ x : Ord3Node, (x ~{FreeOrd3}~> y0) → Type with
  | Ord3_0 =>
      fun x => match x as x0 return (x0 ~{FreeOrd3}~> Ord3_0) → Type with
      | Ord3_0 => fun p => p = tnil
      | Ord3_1 => fun _ => False
      | Ord3_2 => fun _ => False
      end
  | Ord3_1 =>
      fun x => match x as x0 return (x0 ~{FreeOrd3}~> Ord3_1) → Type with
      | Ord3_0 => fun p => p = o3_a
      | Ord3_1 => fun p => p = tnil
      | Ord3_2 => fun _ => False
      end
  | Ord3_2 =>
      fun x => match x as x0 return (x0 ~{FreeOrd3}~> Ord3_2) → Type with
      | Ord3_0 => fun p => ((p = ord3_path_c) + (p = ord3_path_ab))%type
      | Ord3_1 => fun p => p = o3_b
      | Ord3_2 => fun p => p = tnil
      end
  end.

(*
 One induction on the path: the empty path forces source and target to
 agree, and a step is one of the three edges, which pins the source and
 hands the rest to the induction hypothesis.  The 0 -> 2 branch is the
 only one entering the disjunction, once on each side. 

 --------
 路径上的一次归纳：空路径迫使源和目标一致，而一步是三条边之一，它固定源并将其余部分交给归纳假设。0 -> 2 分支是进入析取的唯一分支，每一边各有一次。
*)
Theorem o3_classify (y x : Ord3Node) (p : x ~{FreeOrd3}~> y) : o3_spec y x p.
Proof.
  induction p as [ | i j e p IH ].
  - destruct y; reflexivity.
  - destruct e; destruct y; simpl in *;
      try contradiction;
      try (rewrite IH; reflexivity).
    + right; rewrite IH; reflexivity.
    + left;  rewrite IH; reflexivity.
Qed.

Corollary free_ord3_no_10 (p : Ord3_1 ~{FreeOrd3}~> Ord3_0) : False.
Proof. exact (o3_classify _ _ p). Qed.

Corollary free_ord3_no_20 (p : Ord3_2 ~{FreeOrd3}~> Ord3_0) : False.
Proof. exact (o3_classify _ _ p). Qed.

Corollary free_ord3_no_21 (p : Ord3_2 ~{FreeOrd3}~> Ord3_1) : False.
Proof. exact (o3_classify _ _ p). Qed.

(*
 Any two parallel arrows of the PRESENTED triangle agree.  The only pair
 the classification leaves apart is [ord3_path_c] against
 [ord3_path_ab], and the imposed relation is exactly what closes it --
 [ord3_relation_holds], consumed. 

 --------
 展示的三角形中的任意两条平行箭头是一致的。分类唯一留下不匹配的一对是 [ord3_path_c] 对 [ord3_path_ab]，而施加的关系正是使其闭合的——[ord3_relation_holds]，被消耗。
*)
Theorem ord3_thin (x y : Ord3Node) (p q : x ~{Ord3}~> y) : p ≈ q.
Proof.
  pose proof (o3_classify y x p) as Hp.
  pose proof (o3_classify y x q) as Hq.
  destruct x, y; simpl in Hp, Hq;
    try contradiction;
    try (subst; apply cc_refl).
  destruct Hp as [Hp | Hp]; destruct Hq as [Hq | Hq]; subst.
  - apply cc_refl.
  - exact ord3_relation_holds.
  - exact (cc_sym ord3_relation_holds).
  - apply cc_refl.
Qed.

Definition ord3_equiv_dec (x y : Ord3Node) (p q : x ~{Ord3}~> y) :
  ((p ≈ q) + (p ≈ q → False))%type := inl (ord3_thin x y p q).

(*
 The comparison into 3.  [_3] is thin, so both the quiver
 homomorphism's respectfulness and the merging hypothesis the presented
 category's universal property asks for are [ord_thin]; the functor
 itself is [PresentedFunctor], consumed. 

 --------
 比较到3。[_3]很薄，因此箭袋同态的尊重性以及合并假设下所需的所呈现类别的普遍性都是[ord_thin]；函子本身是[PresentedFunctor]，被使用。
*)
Definition o3_ord (n : Ord3Node) : Ord_obj 3 :=
  match n with
  | Ord3_0 => ord3_0
  | Ord3_1 => ord3_1
  | Ord3_2 => ord3_2
  end.

Definition o3_edge_arr (x y : Ord3Node) (e : Ord3Edge x y) :
  o3_ord x ~{_3}~> o3_ord y :=
  match e with
  | Ord3_a => le_t_S le_t_n
  | Ord3_b => le_t_S le_t_n
  | Ord3_c => le_t_S (le_t_S le_t_n)
  end.

Definition o3_qhom : QuiverHomomorphism Ord3Quiver (QuiverOfCat _3) :=
  Build_QuiverHomomorphism Ord3Quiver (QuiverOfCat _3) o3_ord o3_edge_arr
    (fun x y e e' _ => ord_thin _ _).

Definition Ord3_to : Ord3 ⟶ _3 :=
  @PresentedFunctor Ord3Quiver (fe_rel Ord3Eqns) _3 o3_qhom
    (fun x y f g _ => ord_thin _ _).

Example ord3_to_gen_a :
  fmap[Ord3_to] (@pgen Ord3Quiver (fe_rel Ord3Eqns) _ _ Ord3_a) ≈ three_a.
Proof. apply ord_thin. Qed.

Example ord3_to_gen_b :
  fmap[Ord3_to] (@pgen Ord3Quiver (fe_rel Ord3Eqns) _ _ Ord3_b) ≈ three_b.
Proof. apply ord_thin. Qed.

Example ord3_to_gen_c :
  fmap[Ord3_to] (@pgen Ord3Quiver (fe_rel Ord3Eqns) _ _ Ord3_c) ≈ three_c.
Proof. apply ord_thin. Qed.

Definition ord3_gen {x y : Ord3Node} (e : @edges Ord3Quiver x y) :
  x ~{Ord3}~> y :=
  @pgen Ord3Quiver (fe_rel Ord3Eqns) x y e.

Definition o3_node (k : nat) : Ord3Node :=
  match k with
  | O => Ord3_0
  | S O => Ord3_1
  | _ => Ord3_2
  end.

(*
 The comparison out of 3.  The three descending cases are refuted by the
 [le_t] argument, which is where the order of 3 is spent. 

 --------
 三者的比较。三种递减的情况被 [le_t] 论证所驳斥，这正是三的顺序被耗尽的地方。
*)
Definition o3_arr : ∀ i j : nat, le_t i j → (o3_node i ~{Ord3}~> o3_node j).
Proof.
  intros i j; destruct i as [| [| i]]; destruct j as [| [| j]]; intro H.
  - exact id.
  - exact (ord3_gen Ord3_a).
  - exact (ord3_gen Ord3_c).
  - exact (False_rect _ (le_t_zero_absurd H)).
  - exact id.
  - exact (ord3_gen Ord3_b).
  - exact (False_rect _ (le_t_zero_absurd H)).
  - exact (False_rect _ (le_t_zero_absurd (le_t_SS_inv H))).
  - exact id.
Defined.

Program Definition Ord3_from : _3 ⟶ Ord3 := {|
  fobj := fun x => o3_node (ord_val x);
  fmap := fun x y f => o3_arr (ord_val x) (ord_val y) f
|}.
Solve All Obligations with (repeat intro; apply ord3_thin).

Lemma o3_node_ord (n : Ord3Node) : o3_node (ord_val (o3_ord n)) = n.
Proof. now destruct n. Qed.

Lemma o3_ord_node (x : Ord_obj 3) : o3_ord (o3_node (ord_val x)) = x.
Proof. destruct (ord3_cases x) as [[E | E] | E]; subst; reflexivity. Qed.

(*
 Presentation (i) presents the category 3, at [StrictCat] strength: both
 object components are the equalities above, and both morphism
 components are discharged by thinness of the two sides. 

 --------
 演示 (i) 展示了类别 3，在 [StrictCat] 强度下：两个对象成分都是上述的等式，两个态射成分都由两边的薄性抵消。
*)
Program Definition Ord3_iso : Ord3 ≅[StrictCat] _3 := {|
  to := Ord3_to;
  from := Ord3_from
|}.
Next Obligation.
  exists o3_ord_node; intros x y f; apply ord_thin.
Qed.
Next Obligation.
  exists o3_node_ord; intros x y f; apply ord3_thin.
Qed.

(*
 How much the relation does.  [o3_classify] bounds each free hom-set
 from above, and [ord3_free_distinct] (Presented.v, consumed) shows
 the 0 -> 2 one really does have two elements, so the free category on
 the triangle quiver has SEVEN arrows against 3's six: the presentation
 makes exactly one identification. 

 --------
 关系有多少。[o3_classify] 从上方界定每个自由同态集，而 [ord3_free_distinct] (Presented.v, consumed) 显示 0 -> 2 确实有两个元素，所以三角形 quiver 上的自由范畴有七条箭头，而 3 的则有六条：该呈示正好进行了一次同一化。
*)
Definition ord3_nodes : list Ord3Node := Ord3_0 :: Ord3_1 :: Ord3_2 :: nil.

Definition ord3_all_pairs : list (Ord3Node * Ord3Node) :=
  list_prod ord3_nodes ord3_nodes.

Definition ord3_free_homcount (x y : Ord3Node) : nat :=
  match x, y with
  | Ord3_0, Ord3_0 => 1%nat
  | Ord3_1, Ord3_1 => 1%nat
  | Ord3_2, Ord3_2 => 1%nat
  | Ord3_0, Ord3_1 => 1%nat
  | Ord3_1, Ord3_2 => 1%nat
  | Ord3_0, Ord3_2 => 2%nat
  | _, _ => 0%nat
  end.

Definition ord3_free_arrow_total : nat :=
  fold_right (fun q n => ord3_free_homcount (fst q) (snd q) + n)%nat 0%nat
    ord3_all_pairs.

Theorem ord3_free_arrow_total_7 : ord3_free_arrow_total = 7%nat.
Proof. reflexivity. Qed.

Theorem ord3_free_two_paths : ord3_path_c ≈ ord3_path_ab → False.
Proof. exact ord3_free_distinct. Qed.

Example ord3_merge_arithmetic :
  (ord3_free_arrow_total - three_arrow_total)%nat = 1%nat := eq_refl.

(* ---------- (E) presentation (ii): two generators, no relations -------- / ---------- (E) 呈现 (ii)：两个生成元，无关系 -------- *)

(*
 THE FREENESS VERDICT.  Awodey's question “is 3 free?” is answered YES,
 by CONSUMING [Construction/Free/Quiver/Examples.v]'s [ordinal_free]
 at m = 3.  The category 3 is the free category on the linear two-edge
 graph 0 -> 1 -> 2: the arrow 0 -> 2 is the two-edge PATH, forced by
 composition, and not a generator subject to a relation. 

 --------
 自由性判决。Awodey 的问题“3 是自由的吗？”的答案是肯定的，通过在 m = 3 时使用 [Construction/Free/Quiver/Examples.v] 的 [ordinal_free] 得出。类别 3 是线性两边图 0 -> 1 -> 2 上的自由类别：箭头 0 -> 2 是由组合强制的两边路径，而不是受关系约束的生成箭头。
*)
(*
 [Examples.v]'s [chain_free] IS this constant -- same type, same
 body -- so it is aliased rather than restated; the local name is kept
 so this section reads without a cross-file alias. 

 --------
 [Examples.v] 的 [chain_free] 是这个常量——相同类型，相同主体——所以它是别名而不是重新声明；局部名称被保留，所以这一部分可以在不使用跨文件别名的情况下阅读。
*)
Definition three_is_free : FreeOnQuiver (LinQuiver 3) ≅[StrictCat] _3 :=
  chain_free.

(*
 The three witnesses of that reading, all from Examples.v: the two
 generating steps have path length one, and the arrow they compose to
 has path length two -- it is a composite, not a fourth edge. 

 --------
 那个读数的三个见证者，全部来自 Examples.v：两个生成步骤的路径长度为一，它们组合成的箭头的路径长度为二——它是一个复合箭头，而不是第四条边。
*)
Example three_gen_0_length : tlist_length chain_e0 = 1%nat := chain_e0_length.
Example three_gen_1_length : tlist_length chain_e1 = 1%nat := chain_e1_length.
Example three_composite_length : tlist_length chain_e10 = 2%nat :=
  chain_e10_length.

Example three_composite_is_composite : chain_e10 = chain_e1 ∘ chain_e0 :=
  eq_refl.

(* The same thing as a PRESENTATION: the linear quiver, made finite, with the empty family of equations. / 与演示文稿相同的东西：线性箭袋，使其有限，并带有空的方程族。 *)
Definition lin3_ecount (x y : LinQuiver 3) : nat :=
  if Nat.eq_dec (S (ord_val x)) (ord_val y) then 1%nat else 0%nat.

Definition lin3_edge (x y : LinQuiver 3) :
  Fin.t (lin3_ecount x y) → @edges (LinQuiver 3) x y.
Proof.
  unfold lin3_ecount.
  destruct (Nat.eq_dec (S (ord_val x)) (ord_val y)) as [E | E].
  - intros _; exact E.
  - intro i; exact (Fin.case0 _ i).
Defined.

Definition lin3_eindex (x y : LinQuiver 3)
  (e : @edges (LinQuiver 3) x y) : Fin.t (lin3_ecount x y).
Proof.
  unfold lin3_ecount.
  destruct (Nat.eq_dec (S (ord_val x)) (ord_val y)) as [E | E].
  - exact Fin.F1.
  - exact (False_rect _ (E e)).
Defined.

(*
 An edge of the linear quiver is a proof of a [nat] equation, so two
 edges with the same endpoints agree by UIP on [nat] -- Hedberg, no
 axiom.  That is Examples.v's [linear_edge_unique], consumed. 

 --------
 线性箭头的一个边是 [nat] 方程的证明，因此具有相同端点的两条边在 [nat] 上根据 UIP 一致 -- Hedberg，无公理。也就是说 Examples.v 的 [linear_edge_unique] 已被使用。
*)
Lemma lin3_edge_rt (x y : LinQuiver 3) (e : @edges (LinQuiver 3) x y) :
  lin3_edge x y (lin3_eindex x y e) ≈ e.
Proof. apply linear_edge_unique. Qed.

Definition Lin3Finite : FiniteQuiver (LinQuiver 3) :=
  @Build_FiniteQuiver (LinQuiver 3) 3 (@ord_of_fin 3) (@fin_of_ord 3)
    (@ord_of_fin_of_ord 3) lin3_ecount lin3_edge lin3_eindex lin3_edge_rt.

Definition Lin3Eqns : FiniteEquations (LinQuiver 3).
Proof.
  unshelve refine {| fe_count := fun _ _ => 0%nat |};
    intros x y i; exact (Fin.case0 _ i).
Defined.

Definition Lin3Presentation : FinitePresentation := {|
  fp_quiver := LinQuiver 3;
  fp_finite := Lin3Finite;
  fp_eqns := Lin3Eqns
|}.

Definition Lin3 : Category := FinitelyPresented Lin3Presentation.

(* No relations, at every pair of endpoints. / 没有关系，在每一对端点上。 *)
Theorem lin3_no_equations (x y : LinQuiver 3) :
  @fe_count _ Lin3Eqns x y = 0%nat.
Proof. reflexivity. Qed.

Lemma lin3_rel_empty (x y : LinQuiver 3)
  (f g : x ~{FreeOnQuiver (LinQuiver 3)}~> y) :
  fe_rel Lin3Eqns x y f g → f ≈ g.
Proof. intros [i _]; exact (Fin.case0 _ i). Qed.

(* Quotienting by nothing changes nothing... / 除以零不改变任何东西…… *)
Definition Lin3_free_iso : Lin3 ≅[StrictCat] FreeOnQuiver (LinQuiver 3) :=
  pq_trivial_iso (fe_rel Lin3Eqns) lin3_rel_empty.

(* ...so presentation (ii) presents 3, by [ordinal_free 3]. / ...所以演示 (ii) 由 [ordinal_free 3] 提出 3。 *)
Definition Lin3_iso : Lin3 ≅[StrictCat] _3 :=
  iso_compose three_is_free Lin3_free_iso.

Theorem lin3_thin (x y : LinQuiver 3) (p q : x ~{Lin3}~> y) : p ≈ q.
Proof. exact (cc_equiv (linear_free_thin x y p q)). Qed.

Definition lin3_equiv_dec (x y : LinQuiver 3) (p q : x ~{Lin3}~> y) :
  ((p ≈ q) + (p ≈ q → False))%type := inl (lin3_thin x y p q).

(* ---------- (F) presentation (iii): the equation written backwards ----- / ----------（F）演示（iii）：方程倒写----- *)

(*
 The same three generators, and the same single equation with its two
 sides exchanged: [Ord3Eqns] imposes c = b ∘ a, [Ord3RevEqns] imposes
 b ∘ a = c.  As presentation DATA the two are different, and section (H)
 below says how they are told apart; as categories they coincide,
 because a congruence is symmetric. 

 --------
 相同的三个生成元，以及相同的单个方程，其两边互换：[Ord3Eqns] 强加 c = b ∘ a，[Ord3RevEqns] 强加 b ∘ a = c。作为表示数据，这两者是不同的，下文的(H)节说明了它们如何区分；作为范畴，它们是一致的，因为同余是对称的。
*)
Definition Ord3RevEqns : FiniteEquations Ord3Quiver := {|
  fe_count := Ord3_count;
  fe_lhs := Ord3_rhs;
  fe_rhs := Ord3_lhs
|}.

Definition Ord3RevPresentation : FinitePresentation := {|
  fp_quiver := Ord3Quiver;
  fp_finite := Ord3Finite;
  fp_eqns := Ord3RevEqns
|}.

Definition Ord3Rev : Category := FinitelyPresented Ord3RevPresentation.

Lemma ord3_rev_relation_holds :
  @equiv _ (@homset Ord3Rev Ord3_0 Ord3_2) ord3_path_ab ord3_path_c.
Proof. apply cc_gen. exists Fin.F1. split; reflexivity. Qed.

(* Each presentation's generating equation is DERIVABLE in the other -- one [cc_sym] apiece -- so [pq_same_iso] applies with no path analysis. / 每个表达式生成的方程都可以从另一个导出——每个 [cc_sym] 一份——因此 [pq_same_iso] 可直接应用，无需路径分析。 *)
Lemma ord3_rev_into_ord3 (x y : Ord3Quiver)
  (f g : x ~{FreeOnQuiver Ord3Quiver}~> y) :
  fe_rel Ord3RevEqns x y f g → CongClosure (fe_rel Ord3Eqns) x y f g.
Proof.
  destruct x, y; intros [i [Hf Hg]];
    try (exact (Fin.case0 _ i)).
  exact (cc_trans (cc_equiv Hf)
           (cc_trans (cc_sym ord3_relation_holds)
                     (cc_equiv (symmetry Hg)))).
Qed.

Lemma ord3_into_ord3_rev (x y : Ord3Quiver)
  (f g : x ~{FreeOnQuiver Ord3Quiver}~> y) :
  fe_rel Ord3Eqns x y f g → CongClosure (fe_rel Ord3RevEqns) x y f g.
Proof.
  destruct x, y; intros [i [Hf Hg]];
    try (exact (Fin.case0 _ i)).
  exact (cc_trans (cc_equiv Hf)
           (cc_trans (cc_sym ord3_rev_relation_holds)
                     (cc_equiv (symmetry Hg)))).
Qed.

Definition Ord3Rev_Ord3_iso : Ord3Rev ≅[StrictCat] Ord3 :=
  pq_same_iso (fe_rel Ord3RevEqns) (fe_rel Ord3Eqns)
    ord3_rev_into_ord3 ord3_into_ord3_rev.

(* Presentation (iii) presents the category 3. / 演示（iii）呈现第3类。 *)
Definition Ord3Rev_iso : Ord3Rev ≅[StrictCat] _3 :=
  iso_compose Ord3_iso Ord3Rev_Ord3_iso.

Theorem ord3_rev_thin (x y : Ord3Node) (p q : x ~{Ord3Rev}~> y) : p ≈ q.
Proof.
  exact (pq_cc_mono (fe_rel Ord3Eqns) (fe_rel Ord3RevEqns)
           ord3_into_ord3_rev (ord3_thin x y p q)).
Qed.

Definition ord3_rev_equiv_dec (x y : Ord3Node) (p q : x ~{Ord3Rev}~> y) :
  ((p ≈ q) + (p ≈ q → False))%type := inl (ord3_rev_thin x y p q).

(* ---------- (G) presentation (iv): four generators, two relations ------ / ---------- (G) 呈现 (iv)：四个生成元，两个关系 ------ *)

(*
 Generators a : 0 -> 1, b : 1 -> 2 and TWO parallel arrows c, d : 0 -> 2,
 with both of them equated to the composite: c = b ∘ a and d = b ∘ a.
 The nodes are [Ord3Node] again, so Presented.v's node enumeration
 ([Ord3_node], [Ord3_index], [Ord3_node_rt]) is reused; the edges are
 new. 

 --------
 生成元 a：0 -> 1，b：1 -> 2，以及两个平行箭头 c, d：0 -> 2，且都等于合成：c = b ∘ a 和 d = b ∘ a。节点仍然是 [Ord3Node]，所以 Presented.v 的节点编号 ([Ord3_node], [Ord3_index], [Ord3_node_rt]) 被重复使用；边是新的。
*)
Inductive Tri4Edge : Ord3Node → Ord3Node → Set :=
  | Tri4_a : Tri4Edge Ord3_0 Ord3_1
  | Tri4_b : Tri4Edge Ord3_1 Ord3_2
  | Tri4_c : Tri4Edge Ord3_0 Ord3_2
  | Tri4_d : Tri4Edge Ord3_0 Ord3_2.

Definition Tri4Quiver : Quiver :=
  Build_Quiver_Standard_Eq Ord3Node Tri4Edge.

Definition FreeTri4 : Category := FreeOnQuiver Tri4Quiver.

Definition t4_a : Ord3_0 ~{FreeTri4}~> Ord3_1 :=
  tlist_singleton (B:=@edges Tri4Quiver) Tri4_a.
Definition t4_b : Ord3_1 ~{FreeTri4}~> Ord3_2 :=
  tlist_singleton (B:=@edges Tri4Quiver) Tri4_b.
Definition t4_c : Ord3_0 ~{FreeTri4}~> Ord3_2 :=
  tlist_singleton (B:=@edges Tri4Quiver) Tri4_c.
Definition t4_d : Ord3_0 ~{FreeTri4}~> Ord3_2 :=
  tlist_singleton (B:=@edges Tri4Quiver) Tri4_d.
Definition t4_ab : Ord3_0 ~{FreeTri4}~> Ord3_2 :=
  tcons (B:=@edges Tri4Quiver) _ Tri4_a
    (tlist_singleton (B:=@edges Tri4Quiver) Tri4_b).

Definition t4_spec (y : Ord3Node) :
  ∀ x : Ord3Node, (x ~{FreeTri4}~> y) → Type :=
  match y as y0 return ∀ x : Ord3Node, (x ~{FreeTri4}~> y0) → Type with
  | Ord3_0 =>
      fun x => match x as x0 return (x0 ~{FreeTri4}~> Ord3_0) → Type with
      | Ord3_0 => fun p => p = tnil
      | Ord3_1 => fun _ => False
      | Ord3_2 => fun _ => False
      end
  | Ord3_1 =>
      fun x => match x as x0 return (x0 ~{FreeTri4}~> Ord3_1) → Type with
      | Ord3_0 => fun p => p = t4_a
      | Ord3_1 => fun p => p = tnil
      | Ord3_2 => fun _ => False
      end
  | Ord3_2 =>
      fun x => match x as x0 return (x0 ~{FreeTri4}~> Ord3_2) → Type with
      | Ord3_0 => fun p => ((p = t4_c) + (p = t4_d) + (p = t4_ab))%type
      | Ord3_1 => fun p => p = t4_b
      | Ord3_2 => fun p => p = tnil
      end
  end.

Theorem t4_classify (y x : Ord3Node) (p : x ~{FreeTri4}~> y) : t4_spec y x p.
Proof.
  induction p as [ | i j e p IH ].
  - destruct y; reflexivity.
  - destruct e; destruct y; simpl in *;
      try contradiction;
      try (rewrite IH; reflexivity).
    + right; rewrite IH; reflexivity.
    + left; left; rewrite IH; reflexivity.
    + left; right; rewrite IH; reflexivity.
Qed.

(*
 The three 0 -> 2 paths of the free category are pairwise distinct.  For
 c against ab and d against ab the intermediate node already separates
 them, as in Presented.v's [ord3_free_distinct]; c against d is the case
 that needs UIP on the nodes, which they have by decidable equality
 (Hedberg, through [UIP_dec] -- no axiom is assumed). 

 --------
 自由范畴的三个 0 -> 2 路径是两两不同的。对于 c 与 ab 以及 d 与 ab，已有的中间节点已经将它们分开，如 Presented.v 的 [ord3_free_distinct] 所示；c 与 d 的情况则需要在节点上使用 UIP，而它们通过可判定的等式拥有 UIP（Hedberg，通过 [UIP_dec] -- 没有假设任何公理）。
*)
Definition ord3_node_eq_dec (x y : Ord3Node) : {x = y} + {x <> y}.
Proof.
  destruct x, y; solve [ left; reflexivity | right; discriminate ].
Defined.

Lemma t4_c_ne_d : t4_c ≈ t4_d → False.
Proof.
  unfold t4_c, t4_d, tlist_singleton; simpl.
  unfold tlist_quiver_equiv; simpl.
  intros [q He Ht].
  rewrite (UIP_dec ord3_node_eq_dec q eq_refl) in He.
  simpl in He; discriminate He.
Qed.

Lemma t4_c_ne_ab : t4_c ≈ t4_ab → False.
Proof.
  unfold t4_c, t4_ab, tlist_singleton; simpl.
  unfold tlist_quiver_equiv; simpl. intros [q He Ht]. discriminate q.
Qed.

Lemma t4_d_ne_ab : t4_d ≈ t4_ab → False.
Proof.
  unfold t4_d, t4_ab, tlist_singleton; simpl.
  unfold tlist_quiver_equiv; simpl. intros [q He Ht]. discriminate q.
Qed.

Definition Tri4_count (x y : Tri4Quiver) : nat :=
  match x, y with Ord3_0, Ord3_2 => 2%nat | _, _ => 0%nat end.

Definition t4_pick (i : Fin.t 2) : Ord3_0 ~{FreeTri4}~> Ord3_2 :=
  match i with
  | Fin.F1 => t4_c
  | Fin.FS _ => t4_d
  end.

Definition Tri4_lhs (x y : Tri4Quiver) :
  Fin.t (Tri4_count x y) → x ~{FreeTri4}~> y.
Proof.
  destruct x, y; simpl; intro i;
    solve [ exact (Fin.case0 _ i) | exact (t4_pick i) ].
Defined.

Definition Tri4_rhs (x y : Tri4Quiver) :
  Fin.t (Tri4_count x y) → x ~{FreeTri4}~> y.
Proof.
  destruct x, y; simpl; intro i;
    solve [ exact (Fin.case0 _ i) | exact t4_ab ].
Defined.

Definition Tri4Eqns : FiniteEquations Tri4Quiver := {|
  fe_count := Tri4_count;
  fe_lhs := Tri4_lhs;
  fe_rhs := Tri4_rhs
|}.

Definition Tri4_ecount (x y : Ord3Node) : nat :=
  match x, y with
  | Ord3_0, Ord3_1 => 1%nat
  | Ord3_1, Ord3_2 => 1%nat
  | Ord3_0, Ord3_2 => 2%nat
  | _, _ => 0%nat
  end.

Definition Tri4_edge (x y : Ord3Node) :
  Fin.t (Tri4_ecount x y) → Tri4Edge x y.
Proof.
  destruct x, y; simpl; intro i;
    solve [ exact (Fin.case0 _ i)
          | exact Tri4_a | exact Tri4_b
          | exact (match i with
                   | Fin.F1 => Tri4_c
                   | Fin.FS _ => Tri4_d
                   end) ].
Defined.

Definition Tri4_eindex (x y : Ord3Node) (e : Tri4Edge x y) :
  Fin.t (Tri4_ecount x y) :=
  match e in Tri4Edge a b return Fin.t (Tri4_ecount a b) with
  | Tri4_a => Fin.F1
  | Tri4_b => Fin.F1
  | Tri4_c => Fin.F1
  | Tri4_d => Fin.FS Fin.F1
  end.

Lemma Tri4_edge_rt (x y : Ord3Node) (e : Tri4Edge x y) :
  Tri4_edge x y (Tri4_eindex x y e) = e.
Proof. destruct e; reflexivity. Qed.

Definition Tri4Finite : FiniteQuiver Tri4Quiver :=
  @Build_FiniteQuiver Tri4Quiver 3 Ord3_node Ord3_index Ord3_node_rt
    Tri4_ecount Tri4_edge Tri4_eindex Tri4_edge_rt.

Definition Tri4Presentation : FinitePresentation := {|
  fp_quiver := Tri4Quiver;
  fp_finite := Tri4Finite;
  fp_eqns := Tri4Eqns
|}.

Definition Tri4 : Category := FinitelyPresented Tri4Presentation.

Lemma tri4_c_ab : @equiv _ (@homset Tri4 Ord3_0 Ord3_2) t4_c t4_ab.
Proof. apply cc_gen. exists Fin.F1. split; reflexivity. Qed.

Lemma tri4_d_ab : @equiv _ (@homset Tri4 Ord3_0 Ord3_2) t4_d t4_ab.
Proof. apply cc_gen. exists (Fin.FS Fin.F1). split; reflexivity. Qed.

(*
 The two relations collapse the three-element 0 -> 2 hom-set of the free
 category to one class; every other hom-set was already a singleton or
 empty, so the presented category is thin. 

 --------
 这两个关系将自由范畴的三元素 0 -> 2 同态集归并为一个类；其他每个同态集要么已经是单元素，要么为空，因此所呈现的范畴是稀薄的。
*)
Theorem tri4_thin (x y : Ord3Node) (p q : x ~{Tri4}~> y) : p ≈ q.
Proof.
  pose proof (t4_classify y x p) as Hp.
  pose proof (t4_classify y x q) as Hq.
  destruct x, y; simpl in Hp, Hq;
    try contradiction;
    try (subst; apply cc_refl).
  destruct Hp as [[Hp | Hp] | Hp]; destruct Hq as [[Hq | Hq] | Hq]; subst.
  - apply cc_refl.
  - exact (cc_trans tri4_c_ab (cc_sym tri4_d_ab)).
  - exact tri4_c_ab.
  - exact (cc_trans tri4_d_ab (cc_sym tri4_c_ab)).
  - apply cc_refl.
  - exact tri4_d_ab.
  - exact (cc_sym tri4_c_ab).
  - exact (cc_sym tri4_d_ab).
  - apply cc_refl.
Qed.

Definition tri4_equiv_dec (x y : Ord3Node) (p q : x ~{Tri4}~> y) :
  ((p ≈ q) + (p ≈ q → False))%type := inl (tri4_thin x y p q).

Definition t4_edge_arr (x y : Ord3Node) (e : Tri4Edge x y) :
  o3_ord x ~{_3}~> o3_ord y :=
  match e with
  | Tri4_a => le_t_S le_t_n
  | Tri4_b => le_t_S le_t_n
  | Tri4_c => le_t_S (le_t_S le_t_n)
  | Tri4_d => le_t_S (le_t_S le_t_n)
  end.

Definition t4_qhom : QuiverHomomorphism Tri4Quiver (QuiverOfCat _3) :=
  Build_QuiverHomomorphism Tri4Quiver (QuiverOfCat _3) o3_ord t4_edge_arr
    (fun x y e e' _ => ord_thin _ _).

Definition Tri4_to : Tri4 ⟶ _3 :=
  @PresentedFunctor Tri4Quiver (fe_rel Tri4Eqns) _3 t4_qhom
    (fun x y f g _ => ord_thin _ _).

Definition tri4_gen {x y : Ord3Node} (e : @edges Tri4Quiver x y) :
  x ~{Tri4}~> y :=
  @pgen Tri4Quiver (fe_rel Tri4Eqns) x y e.

Definition t4_arr : ∀ i j : nat, le_t i j → (o3_node i ~{Tri4}~> o3_node j).
Proof.
  intros i j; destruct i as [| [| i]]; destruct j as [| [| j]]; intro H.
  - exact id.
  - exact (tri4_gen Tri4_a).
  - exact (tri4_gen Tri4_c).
  - exact (False_rect _ (le_t_zero_absurd H)).
  - exact id.
  - exact (tri4_gen Tri4_b).
  - exact (False_rect _ (le_t_zero_absurd H)).
  - exact (False_rect _ (le_t_zero_absurd (le_t_SS_inv H))).
  - exact id.
Defined.

Program Definition Tri4_from : _3 ⟶ Tri4 := {|
  fobj := fun x => o3_node (ord_val x);
  fmap := fun x y f => t4_arr (ord_val x) (ord_val y) f
|}.
Solve All Obligations with (repeat intro; apply tri4_thin).

(* Presentation (iv) presents the category 3. / 演示（四）呈现第3类。 *)
Program Definition Tri4_iso : Tri4 ≅[StrictCat] _3 := {|
  to := Tri4_to;
  from := Tri4_from
|}.
Next Obligation.
  exists o3_ord_node; intros x y f; apply ord_thin.
Qed.
Next Obligation.
  exists o3_node_ord; intros x y f; apply tri4_thin.
Qed.

(*
 The four-generator quiver's free category has EIGHT arrows -- the three
 0 -> 2 paths are pairwise distinct by the three lemmas above -- so this
 presentation makes exactly two identifications. 

 --------
 四生成元箭袋的自由范畴有八条箭头——上述三个引理表明三条 0 -> 2 的路径两两不同——因此这个表示正好进行了两个同一化。
*)
Definition tri4_free_homcount (x y : Ord3Node) : nat :=
  match x, y with
  | Ord3_0, Ord3_0 => 1%nat
  | Ord3_1, Ord3_1 => 1%nat
  | Ord3_2, Ord3_2 => 1%nat
  | Ord3_0, Ord3_1 => 1%nat
  | Ord3_1, Ord3_2 => 1%nat
  | Ord3_0, Ord3_2 => 3%nat
  | _, _ => 0%nat
  end.

Definition tri4_free_arrow_total : nat :=
  fold_right (fun q n => tri4_free_homcount (fst q) (snd q) + n)%nat 0%nat
    ord3_all_pairs.

Theorem tri4_free_arrow_total_8 : tri4_free_arrow_total = 8%nat.
Proof. reflexivity. Qed.

Example tri4_merge_arithmetic :
  (tri4_free_arrow_total - three_arrow_total)%nat = 2%nat := eq_refl.

(* ---------- (H) the four presentations, compared ---------- / ---------- (H) 四种演示的比较 ---------- *)

(* Generator counts, folded over every ordered pair of nodes. / 生成器计数，对每一对有序节点进行折叠。 *)
Definition lin3_gen_total : nat :=
  fold_right (fun q n => lin3_ecount (fst q) (snd q) + n)%nat 0%nat
    three_all_pairs.

Theorem lin3_gen_total_2 : lin3_gen_total = 2%nat.
Proof. reflexivity. Qed.

Definition ord3_gen_total : nat :=
  fold_right (fun q n => Ord3_ecount (fst q) (snd q) + n)%nat 0%nat
    ord3_all_pairs.

Theorem ord3_gen_total_3 : ord3_gen_total = 3%nat.
Proof. reflexivity. Qed.

Definition tri4_gen_total : nat :=
  fold_right (fun q n => Tri4_ecount (fst q) (snd q) + n)%nat 0%nat
    ord3_all_pairs.

Theorem tri4_gen_total_4 : tri4_gen_total = 4%nat.
Proof. reflexivity. Qed.

(*
 Relation counts, likewise.  Presentations (i) and (iii) share their
 quiver, hence their generator count and their relation count. 

 --------
 关系数量同样重要。 表述 (i) 和 (iii) 共享它们的箭图，因此它们的生成元数量和关系数量也相同。
*)
Definition lin3_rel_total : nat :=
  fold_right (fun q n => @fe_count _ Lin3Eqns (fst q) (snd q) + n)%nat 0%nat
    three_all_pairs.

Theorem lin3_rel_total_0 : lin3_rel_total = 0%nat.
Proof. reflexivity. Qed.

Definition ord3_rel_total : nat :=
  fold_right (fun q n => @fe_count _ Ord3Eqns (fst q) (snd q) + n)%nat 0%nat
    ord3_all_pairs.

Theorem ord3_rel_total_1 : ord3_rel_total = 1%nat.
Proof. reflexivity. Qed.

Definition ord3_rev_rel_total : nat :=
  fold_right
    (fun q n => @fe_count _ Ord3RevEqns (fst q) (snd q) + n)%nat 0%nat
    ord3_all_pairs.

Theorem ord3_rev_rel_total_1 : ord3_rev_rel_total = 1%nat.
Proof. reflexivity. Qed.

Definition tri4_rel_total : nat :=
  fold_right (fun q n => @fe_count _ Tri4Eqns (fst q) (snd q) + n)%nat 0%nat
    ord3_all_pairs.

Theorem tri4_rel_total_2 : tri4_rel_total = 2%nat.
Proof. reflexivity. Qed.

(*
 The three quivers have three different generator counts, so no two of
 (i), (ii), (iv) are the same presentation data; (iii) shares (i)'s
 quiver, hence its generator count, and so differs from (ii) and (iv) by
 the same numbers. 

 --------
 这三个箭袋有三个不同的生成元数量，所以(i)、(ii)、(iv)中没有两个是相同的表示数据；(iii)与(i)的箭袋相同，因此其生成元数量相同，因此它与(ii)和(iv)的差异是相同的数字。
*)
Theorem three_presentation_counts_differ :
  (((ord3_gen_total = lin3_gen_total → False) *
    (ord3_gen_total = tri4_gen_total → False)) *
   (lin3_gen_total = tri4_gen_total → False))%type.
Proof.
  repeat split; unfold ord3_gen_total, lin3_gen_total, tri4_gen_total;
    discriminate.
Qed.

Example ord3_rev_shares_ord3_quiver :
  fp_quiver Ord3RevPresentation = fp_quiver Ord3Presentation := eq_refl.

(*
 (i) and (iii) agree on both counts, so what tells them apart is the
 equation itself: the left-hand side of (i)'s is the generator c and of
 (iii)'s is the composite path b ∘ a... 

 --------
 (i) 和 (iii) 在两个方面都一致，所以区分它们的因素是方程本身：(i) 的左侧是生成元 c，而 (iii) 的左侧是复合路径 b ∘ a...
*)
Example ord3_lhs_is_c :
  @fe_lhs _ Ord3Eqns Ord3_0 Ord3_2 Fin.F1 = ord3_path_c := eq_refl.

Example ord3_rev_lhs_is_ab :
  @fe_lhs _ Ord3RevEqns Ord3_0 Ord3_2 Fin.F1 = ord3_path_ab := eq_refl.

(*
 ...and those two are not the same arrow of the free category.  This is
 Presented.v's [ord3_free_distinct], consumed; it is the reason the
 two presentation records are distinguishable even though the categories
 they present are isomorphic. 

 --------
 ...而且那两个不是自由范畴的同一个箭头。这是 Presented.v 的 [ord3_free_distinct]，已被使用；这就是为什么即使它们所表示的范畴同构，这两个表示记录仍然可以区分的原因。
*)
Theorem ord3_presentations_differ : ord3_path_c ≈ ord3_path_ab → False.
Proof. exact ord3_free_distinct. Qed.

(*
 AWODEY §4.5 EXERCISE 3.  Four presentations of the category 3.  Every
 one is isomorphic to [_3] in [StrictCat], hence to each of the others;
 and by the counts above the four presentation records are pairwise
 distinguishable. 

 --------
 AWODEY §4.5 练习 3。类别 3 的四个表示。每一个都与 [_3] 在 [StrictCat] 中同构，因此也与其他表示同构；根据上述计数，四个表示记录两两可区分。
*)
Definition three_four_presentations :
  (((Ord3 ≅[StrictCat] _3) * (Lin3 ≅[StrictCat] _3)) *
   ((Ord3Rev ≅[StrictCat] _3) * (Tri4 ≅[StrictCat] _3)))%type :=
  ((Ord3_iso, Lin3_iso), (Ord3Rev_iso, Tri4_iso)).

(* The four in one place, as data rather than as prose. / 四个在一个地方，以数据而非散文的形式。 *)
Definition three_presentations : list FinitePresentation :=
  Ord3Presentation :: Lin3Presentation ::
  Ord3RevPresentation :: Tri4Presentation :: nil.

Example three_presentations_4 : length three_presentations = 4%nat := eq_refl.
