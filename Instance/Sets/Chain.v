Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Omega.
Require Import Category.Construction.Chain.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Cocomplete.

Generalizable All Variables.

(** * The ω-chain colimit in [Sets] / * 在 [Sets] 中的 ω-链余极限 *)

(*
 nLab:      https://ncatlab.org/nlab/show/sequential+colimit
 nLab:      https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor
 Wikipedia: https://en.wikipedia.org/wiki/Direct_limit

 Riehl, “Category Theory in Context”, Dover 2016, §3.1 Example 3.1.26 --
 the colimit of an increasing chain of sets is their union.  Mac Lane,
 “Categories for the Working Mathematician” 2nd ed., Springer GTM 5
 1998, §V.1 Exercise 8 asks for the general statement, all small
 colimits; that is Instance/Sets/Cocomplete.v's [Sets_Cocomplete], and
 this file only READS it at the ω-shape.  Riehl's phrasing is honoured
 literally: the chain colimit is stated as a [Colimit] over
 Construction/Chain.v's shape, obtained by INSTANTIATING the general
 witness, and no second construction is written -- the bodies of
 [Sets_Omega_Colimit] and [Sets_Chain_Colimit] are applications of
 [Sets_Cocomplete] and nothing else.

 WHAT IS HERE

 [Sets_Omega_Colimit] gives a [Colimit G] for an ARBITRARY diagram
 [G : Omega ⟶ Sets] over the ordinal ω (Instance/Omega.v), and
 [Sets_Chain_Colimit] specialises it to [Chain F], the initial-algebra
 chain [0 ~> F 0 ~> F² 0 ~> ...] of an endofunctor of [Sets]
 (Construction/Chain.v).  That second constant is exactly the argument
 [adamek_cocomplete] (Theory/Adamek/Corollaries.v) forms as
 [CC _ (Chain F)], so it is the ω-colimit Adámek's theorem consumes.

 The apex and the legs are read off by conversion: the carrier is the
 sum [{ n : nat & G n }] over the stages ([Sets_omega_carrier],
 [Sets_chain_carrier]), the leg at [n] is the [n]th injection
 ([Sets_omega_inj_at]), and the produced colimit's apex is the quotient
 object of Instance/Sets/Cocomplete.v ([Sets_omega_apex]) -- all four at
 [eq_refl].

 THE UNION READING, AND EXACTLY HOW FAR IT GOES

 “The colimit is the union” is two statements about the generated
 relation, and only ONE of them is proved here.

 SUFFICIENCY, proved: [omega_colim_of_stage] -- if [x : G m] and
 [y : G n] have images that agree at some common later stage [k], then
 they are identified in the colimit.  The proof is three constructors of
 [colim_rel] chained by [cr_trans]: glue [x] up to [k], apply [cr_point]
 to the hypothesis there, and glue [y] back down.  [omega_colim_step] is
 the one-step corollary a reader wants first.

 NECESSITY, *not* proved: nothing here shows the converse, that two
 colimit-identified elements must already agree at a common later stage.
 Without it the union reading is one-directional, and in particular the
 legs are NOT shown injective for a chain of injective connecting maps
 -- which is the content of calling the colimit a union rather than a
 quotient of a sum.  No inclusion-cone statement in that sense is made.

 The reason it is left undone, so that a later attempt starts informed.
 The converse needs a directedness merge -- given agreement at [k₁] and
 at [k₂], push both to a common bound -- and that step compares
 [fmap[G] p] with [fmap[G] p'] for two order proofs [p p' : le_t n k].
 [Omega]'s hom-setoid is [Morphism_equality] (Instance/Omega.v),
 strict Leibniz equality of [le_t] derivations, so [fmap_respects] gives
 nothing unless [p = p'].  The lemma supplying [p = p'] ALREADY EXISTS:
 [le_t_irr {m n} (f g : le_t m n) : f = g] at Instance/Ordinal.v,
 axiom-free by UIP on [nat], in a file that itself requires
 Instance/Omega.v and reuses that very [le_t].  So the deferral is a
 SCOPE choice about how much of the ω-reading to build here, NOT a
 missing lemma, and a later attempt should start from that constant.
 An earlier draft said instead that “Instance/Omega.v declares [le_t]
 with no uniqueness lemma, so that would have to be proved first, by
 dependent elimination.  That was judged substantial”.  The file-local
 absence is real; the inference drawn from it was wrong, and it would
 have sent a later reader to re-derive a lemma the tree already has.

 UNIVERSES, FROM THE CONSTRAINT BLOCKS

 The two constants sit at different strengths and the difference is
 entirely inherited.

 Sets_Omega_Colimit@{u u0 u1} :
 ∀ G : Functor@{u u0 u0 u1 u0 u0}, Colimit@{u0 u u0 u1} G
 ( * u u0 u1 |= u0 < u1   u <= u0   ... * )

 is FREE: it keeps [Sets_Cocomplete]'s own [ud <= uo], so [Omega]'s
 objects sit at or below [Sets]' carrier universe and nothing is pinned.

 Sets_Chain_Colimit@{u} :
 ∀ F : Functor@{u Set Set u Set Set},
 Colimit@{Set Set Set u} (Chain F)
 ( * u |= Set < False_rect.u0   Set < u * )

 is PINNED: it is a statement about [Sets@{Set u}], setoids whose
 carriers live in [Set].  The cause is measured and is not this file's.
 [Chain@{u u0 u1}] (Construction/Chain.v) has result type
 [Functor@{u1 Set Set u u0 u0}] -- it fixes [Omega]'s hom and proof
 universes at [Set] -- and [Cocomplete]'s own shape forces the diagram
 category's hom universe to coincide with [Sets]' carrier universe, so
 the [Set] travels across.  [Sets_Initial@{u u0}], the other donor
 [Chain] consumes, is free and is NOT the cause.  The pin belongs to
 Construction/Chain.v, is NOT repaired here, and is NOT claimed
 unavoidable.

 NON-VACUITY: THE OTHER HALF, AT THE ω-SHAPE

 Instance/Sets/Cocomplete.v's [two_fibres_not_collapsed] shows the
 generated relation does not collapse everything, at a DISCRETE shape,
 where it can merge nothing.  The complementary fact needs a shape that
 HAS a connecting map, and is proved here at a constant ω-diagram
 [OmegaPoints]: [omega_stages_merged] identifies the summands at stages
 0 and 1 in the colimit (by [omega_colim_step], i.e. the glue along the
 generating step), while [omega_stages_apart_in_coproduct] shows the
 coproduct's own [≈] keeps them apart, its index component demanding
 [0 = 1].  So the merge is genuinely the quotient's doing.  Both stages
 are inhabited, by [omega_point], and the two theorems are stated at
 those inhabitants.

 Taken with the other file, what the two witnesses JOINTLY establish is
 that NEITHER endpoint describes [colim_rel] uniformly: this pair
 refutes “always the coproduct's relation”, the discrete pair refutes
 “always total”.  That is a statement about the FAMILY, not about any
 one diagram.  It is NOT the claim that the relation lies strictly
 inside that interval at some shape -- here it does not, [colim_rel]
 being TOTAL at [OmegaPoints], the fibres being singletons and any two
 stages ordered.  An earlier draft wrote “placed strictly between ...
 EACH FACT AT ITS OWN SHAPE”; the hedge does not rescue the claim.

 WHAT IS NOT DELIVERED, SCOPED TO THIS FILE

 * The necessity half above, hence no theorem that the ω-colimit IS the
 union and no injectivity of the legs.

 * No [AdamekData] (Theory/Adamek.v) and so no initial [F]-algebra:
 Theory/Adamek/Corollaries.v records that no [AdamekData]
 witness is constructed anywhere in the tree, and this file does not
 change that.  What it supplies is the [Colimit] argument, not the
 leg-agreement bridge.

 * No filtered-colimit vocabulary, no cofinality statement, and no
 comparison of the ω-shape colimit with any other shape's.

 STATUS: axiom-free.  All 14 constants -- 12 named and the 2 [Program]
 obligations of [OmegaPoints], which the ambient obligation tactic
 discharges -- report “Closed under the global context”. 

 --------
 nLab:       https://ncatlab.org/nlab/show/sequential+colimit 
 nLab:       https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor 
 维基百科:  https://en.wikipedia.org/wiki/Direct_limit 

 Riehl，《情境下的范畴论》，Dover 2016，第3.1节 示例3.1.26 —— 一个递增集合链的余极限是它们的并集。Mac Lane，《为在职数学家准备的范畴论》第二版，Springer GTM 5，1998，第V.1节 习题8 要求一般陈述，即所有小余极限；也就是 Instance/Sets/Cocomplete.v 的 [Sets_Cocomplete] ，而这个文件仅在 ω 形状下读取它。Riehl 的措辞被忠实保留：链的余极限被陈述为 Construction/Chain.v 形状上的 [Colimit]，通过实例化一般的证据获得，并且没有写第二个构造——[Sets_Omega_Colimit] 和 [Sets_Chain_Colimit] 的主体是 [Sets_Cocomplete] 的应用，而没有其他内容。

 这里是什么[Sets_Omega_Colimit] 为任意图 [G : Omega ⟶ Sets] 在序数 ω 上（Instance/Omega.v）提供了 [Colimit G]，并且 [Sets_Chain_Colimit] 将其专门化为 [Chain F]，即 [Sets] 的一个自函子初始代数链 [0 ~> F 0 ~> F² 0 ~> ...]（Construction/Chain.v）。第二个常量恰好是 [adamek_cocomplete]（Theory/Adamek/Corollaries.v）形成 [CC _ (Chain F)] 的参数，因此它是 Adámek 定理所使用的 ω-余极限。

 顶点和边通过换算读取：载体是各阶段 [{ n : nat & G n }] 上的和（[Sets_omega_carrier], [Sets_chain_carrier]），[n] 处的边是 [n] 次注入（[Sets_omega_inj_at]），产生的余极点的顶点是实例/集合/完备余极限.v 中的商对象（[Sets_omega_apex]）——全部四个在 [eq_refl]。

 并集读取，以及它到底能延伸到哪里“余极限是并集”是关于生成关系的两个陈述，而这里只证明了其中一个。

 充分性，已证明：[omega_colim_of_stage] —— 如果 [x : G m] 和 [y : G n] 的像在某个共同的后续阶段 [k] 上一致，那么它们在余极限中被识别。证明由三个 [colim_rel] 构造器通过 [cr_trans] 链接而成：将 [x] 粘合到 [k]，应用 [cr_point] 于该处的假设，然后将 [y] 粘合回来。[omega_colim_step] 是读者首先想要的一步推论。必要性，*未*被证明：这里没有任何内容表明相反的情况，即两个由余极限识别的元素必须已经在某个共同的后续阶段相同。没有它的话，联合的理解是单向的，特别是对于一条由单射连接映射组成的链，不能证明各腿是单射的——这正是将余极限称为联合而不是和的商的内容。没有在这个意义上提出包含锥的陈述。之所以留到未完成，是为了让之后的尝试从有信息的地方开始。相反，需要一个定向合并——在 [k₁] 和 [k₂] 达成一致的情况下，将两者推到一个共同的界限——而且那一步比较 [fmap[G] p] 与 [fmap[G] p'] 对于两个序证明 [p p' : le_t n k]。[Omega] 的同态集合是 [Morphism_equality]（Instance/Omega.v），[le_t] 推导的严格莱布尼茨等式，因此 [fmap_respects] 除非 [p = p']，否则没有任何作用。提供 [p = p'] 的引理已经存在：[le_t_irr {m n} (f g : le_t m n) : f = g] 在 Instance/Ordinal.v，基于 [nat] 的 UIP 无公理，在该文件本身需要 Instance/Omega.v 并重用非常同一 [le_t]。所以这种延迟是关于在此构建多少 ω 读法的作用域选择，而不是缺失的引理，之后的尝试应该从该常量开始。早期草稿中则说“Instance/Omega.v 声明了 [le_t]，但没有唯一性引理，所以必须先通过依赖消去来证明。这被认为是实质性的”。文件本地的缺失是真的；从中得出的推断是错误的，而且会让后来的读者重新推导出树中已有的引理。

 来自约束块的宇宙

 这两个常量位于不同的强度上，差异完全是继承来的。

 Sets_Omega_Colimit@{u u0 u1} ：
 ∀ G : Functor@{u u0 u0 u1 u0 u0}, Colimit@{u0 u u0 u1} G
 （* u u0 u1 |= u0 < u1   u <= u0   ... *）

 是自由的：它保留了 [Sets_Cocomplete] 自身的 [ud <= uo]，因此 [Omega] 的对象位于 [Sets] 载体宇宙或以下，并且没有任何被固定。Sets_Chain_Colimit@{u} ：
 对于所有 F : Functor@{u Set Set u Set Set},
 Colimit@{Set Set Set u} (Chain F)
 ( * u |= Set < False_rect.u0   Set < u * )

 是固定的（PINNED）：它是关于 [Sets@{Set u}] 的陈述，[Sets@{Set u}] 是其载体位于 [Set] 的集合等价类。原因已被测量，并非由此文件引起。
 [Chain@{u u0 u1}] （Construction/Chain.v）具有结果类型 [Functor@{u1 Set Set u u0 u0}] -- 它固定了 [Omega] 的 hom 和证明
 泛型在 [Set] -- 并且 [Cocomplete] 自身的形状强制图范畴的 hom 泛型与 [Sets] 的载体泛型一致，因此 [Set] 传递过去。[Sets_Initial@{u u0}]，另一个提供者 [Chain] 消耗它，是自由的，并非原因。该固定点属于 Construction/Chain.v，在此未修复，也不声称不可避免。

 非空性（NON-VACUITY）：另一半，在 ω-形状Instance/Sets/Cocomplete.v 的 [two_fibres_not_collapsed] 显示生成的关系不会在一个离散形状上将一切合并，在那里它什么都不能合并。互补的事实需要一个具有连接映射的形状，并且在这里通过一个常数 ω-图证明 [OmegaPoints]：[omega_stages_merged] 在余极限的阶段 0 和 1 处识别求和项（通过 [omega_colim_step]，即沿生成步骤的粘合），而 [omega_stages_apart_in_coproduct] 显示余积自身的 [≈] 将它们分开，它的指标分量要求 [0 = 1]。因此，合并实际上是商的作用。两个阶段都有元素，由 [omega_point]，并且这两个定理在这些元素处陈述。结合另一个文件，这两个证人共同证明的是：没有任何一个端点能够统一描述 [colim_rel]：这一对否定了“积的关系总是如此”，这一对的离散性否定了“总是全的”。 这是一条关于整个族的声明，而不是关于任何一个图的声明。 这并不是说该关系在某个形状下严格位于该区间内——在这里不是这样，[colim_rel] 在 [OmegaPoints] 上是全的，纤维是单元集，且任意两个阶段是有序的。 早期草稿写道“严格位于每个形状的各自事实之间”；这种保留并不能挽救这一说法。  

 本文件没有提供的内容范围：

 * 上述必要性部分，因此没有定理说明 ω-余极限就是并集，也没有各腿的单射性。* 没有 [AdamekData]（Theory/Adamek.v），因此也没有初始 [F] -代数：Theory/Adamek/Corollaries.v 记录了在树的任何地方都没有构造 [AdamekData] 见证者，而这个文件并没有改变这一点。它提供的是 [Colimit] 参数，而不是 leg-agreement 桥。

 * 没有筛选余极限（filtered-colimit）词汇，没有上界论述（cofinality statement），也没有将 ω-形状余极限与任何其他形状的余极限进行比较。

 状态：无公理。所有 14 个常量——12 个已命名的和 2 个 [Program] [OmegaPoints] 义务，由环境义务策略（ambient obligation tactic）处理——都显示“在全局上下文下关闭”。
*)

Section SetsOmegaColimit.

Context (G : Omega ⟶ Sets).

(* * ** The colimit, as an instance of the general witness / * ** 余极限，作为一般见证的一个实例 *)

Definition Sets_Omega_Colimit : Colimit G := Sets_Cocomplete Omega G.

(* * ** What the apex and the legs are, by conversion / * ** 由转换得出的顶点和腿是什么 *)

Example Sets_omega_carrier :
  carrier (Sets_colim_obj G) = { n : nat & carrier (G n) }.
Proof. reflexivity. Qed.

Example Sets_omega_inj_at (n : nat) (x : G n) :
  Sets_colim_inj G n x = existT _ n x.
Proof. reflexivity. Qed.

Example Sets_omega_apex :
  @vertex_obj _ _ _ (@limit_cone _ _ _ Sets_Omega_Colimit) = Sets_colim_obj G.
Proof. reflexivity. Qed.

(* * ** Agreeing at a common later stage suffices / * ** 在稍晚的共同阶段达成一致即可 *)

Lemma omega_colim_of_stage (m n k : nat)
  (p : m ~{Omega}~> k) (q : n ~{Omega}~> k) (x : G m) (y : G n) :
  fmap[G] p x ≈ fmap[G] q y ->
  @equiv _ (Sets_colim_obj G) (existT _ m x) (existT _ n y).
Proof.
  intros H.
  apply (@cr_trans _ G _ (existT _ k (fmap[G] p x))).
  - exact (@cr_glue _ G m k p x).
  - apply (@cr_trans _ G _ (existT _ k (fmap[G] q y))).
    + exact (@cr_point _ G k (fmap[G] p x) (fmap[G] q y) H).
    + exact (@cr_sym _ G _ _ (@cr_glue _ G n k q y)).
Qed.

(* The one-sided special case a reader of “the colimit is the union” wants first: an element and its image one step along are already identified. / 读者想要的“余极限就是并集”的单边特殊情况是：首先，一个元素及其跨一步的像已经被识别出来。 *)
Corollary omega_colim_step (n : nat) (x : G n) :
  @equiv _ (Sets_colim_obj G) (existT _ n x)
    (existT _ (S n) (fmap[G] (omega_step n) x)).
Proof. exact (@cr_glue _ G n (S n) (omega_step n) x). Qed.

End SetsOmegaColimit.

(* * ** The initial-algebra chain of an endofunctor of [Sets] / * ** [Sets] 的自函子初代数链 *)

Definition Sets_Chain_Colimit (F : Sets ⟶ Sets) : Colimit (Chain F) :=
  Sets_Cocomplete Omega (Chain F).

(* Its apex is the sum of the chain's stages, by conversion. / 它的顶点是链条各阶段通过转换的总和。 *)
Example Sets_chain_carrier (F : Sets ⟶ Sets) :
  carrier (Sets_colim_obj (Chain F)) = { n : nat & carrier (chain_obj F n) }.
Proof. reflexivity. Qed.

(* * * Non-vacuity: the quotient merges something the coproduct keeps apart / * * 非空性：商将某些被余积分开的东西合并起来 *)

(*
 Instance/Sets/Cocomplete.v's [two_fibres_not_collapsed] shows the
 generated relation does not collapse everything, at a DISCRETE shape,
 where by construction it can merge nothing.  This is the other half, at
 a shape that HAS a connecting map: two summands at DIFFERENT indices,
 kept apart by the coproduct's own `≈`, are identified in the colimit.
 Together the two witnesses show that NEITHER endpoint describes
 [colim_rel] uniformly across shapes.  Neither is a general theorem
 about all shapes, and neither places the relation strictly inside that
 interval at its own shape -- see the header for the measurement. 

 --------
 Instance/Sets/Cocomplete.v 的 [two_fibres_not_collapsed] 显示生成的关系不会在一个 DISCRETE 形状下把一切都折叠起来，根据构造，它在该情况下无法合并任何东西。另一半则是在一个有连接映射的形状上：两个不同指数的直和，因为余积自身的 `≈` 保持分开，在余极限中被识别在一起。两者共同证明了在所有形状中，[colim_rel] 既不在任一端点处统一描述。任一端点都不是关于所有形状的一般定理，也没有把该关系严格限定在其自身形状的该区间内 —— 参见测量的标题。
*)

Section OmegaMergeWitness.

(*
 A constant ω-diagram: the same singleton at every stage, every
 connecting map the identity.  This file leaves the ambient obligation
 tactic in place (unlike Instance/Sets/Cocomplete.v, which sets it to
 [idtac]), and all three functor laws are constant identities, so no
 obligation survives to be discharged by hand. 

 --------
 一个常数 ω-图：在每个阶段都是相同的单例，每个连接映射都是恒等映射。这个文件保留了环境义务策略（与 Instance/Sets/Cocomplete.v 不同，后者将其设置为 [idtac]），并且三个函子定律都是恒等的，所以没有义务需要手动解决。
*)
Program Definition OmegaPoints : Omega ⟶ Sets := {|
  fobj := fun _ => unit_setoid_object;
  fmap := fun _ _ _ => id
|}.

Definition omega_point (n : nat) : carrier (OmegaPoints n) := ttt.

(* MERGED in the colimit: stage 0 and stage 1 are identified, by the glue along the generating step [0 ~> 1]. / 在余极限中合并：阶段 0 和阶段 1 被识别，通过沿生成步骤 [0 ~> 1] 的粘合。 *)
Theorem omega_stages_merged :
  @equiv _ (Sets_colim_obj OmegaPoints)
    (existT _ 0%nat (omega_point 0)) (existT _ 1%nat (omega_point 1)).
Proof. exact (omega_colim_step OmegaPoints 0%nat (omega_point 0)). Qed.

(*
 ... and KEPT APART by the coproduct, whose `≈` at distinct indices
 demands an equality of those indices.  So the merge above is genuinely
 the quotient's doing and not already present downstairs. 

 --------
 ... 并且由余积分开，其在不同索引处的 `≈` 要求这些索引相等。因此，上述合并确实是商的作用，而不是已经存在于下层的。
*)
Theorem omega_stages_apart_in_coproduct :
  @equiv _ (Sets_colim_sum OmegaPoints)
    (existT _ 0%nat (omega_point 0)) (existT _ 1%nat (omega_point 1)) -> False.
Proof. intros [e _]; discriminate e. Qed.

End OmegaMergeWitness.
