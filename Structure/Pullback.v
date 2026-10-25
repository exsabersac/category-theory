Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.

Generalizable All Variables.

(*
 A pullback (also called a fibered product) is the limit of a cospan
 `b → a ← c`; it is dual to the pushout (a pullback in C is a pushout in
 C^op).

 nLab:      https://ncatlab.org/nlab/show/pullback
 Wikipedia: https://en.wikipedia.org/wiki/Pullback_(category_theory)

 Universal property, in this library's notation: a pullback of f and g is an
 object [Pull] with projections [pullback_fst : Pull ~> x] and
 [pullback_snd : Pull ~> y] satisfying f ∘ pullback_fst ≈ g ∘ pullback_snd,
 such that for every (Q, q1, q2) with f ∘ q1 ≈ g ∘ q2 there is a unique
 u : Q ~> Pull with pullback_fst ∘ u ≈ q1 and pullback_snd ∘ u ≈ q2. 

 --------
 拉回（也称作纤维积）是余尖（cospan）`b → a ← c` 的极限；它是推出（pushout）的对偶（在 C 中的拉回即在 C^op 中的推出）。

 nLab: https://ncatlab.org/nlab/show/pullback 
 Wikipedia: https://en.wikipedia.org/wiki/Pullback_(category_theory)

 在本库的记号中，范畴论中的普遍性性质：f 和 g 的拉回是一个对象 [Pull] ，带有投影 [pullback_fst : Pull ~> x] 和 [pullback_snd : Pull ~> y] ，满足 f ∘ pullback_fst ≈ g ∘ pullback_snd，使得对于每一个 (Q, q1, q2) 且 f ∘ q1 ≈ g ∘ q2，存在唯一的 u : Q ~> Pull 且 pullback_fst ∘ u ≈ q1 和 pullback_snd ∘ u ≈ q2。
*)

(*
 Given a cospan in C:

 A         B
 \       /
 f \     / g
 \   /
 v
 C

 This can be thought of, set-theoretically, as singling out the pairs that
 agree under f and g, i.e. those satisfying the equation:

 f(a) = g(b),   for a ∈ A, b ∈ B

 A pullback is the subset of the cartesian product of A and B,
 X ⊆ A × B, consisting of exactly those pairs (a, b) for which f(a) = g(b),
 where the following diagram commutes:

 X
 /   \
 pA /     \ pB
 /       \
 A         B
 \       /
 f \     / g
 \   /
 v
 C

 An example of this is an INNER JOIN of two SQL tables, where f projects a
 primary key from A, and g a foreign key referencing A, so that X contains
 exactly those pairs of rows from A and B where id(A) = fkey(B).

 Wikipedia: "In fact, the pullback is the universal solution to finding a
 commutative square like this. In other words, given any commutative square
 [replacing in the above X with Y, and pA and pB with qA and qB] there is a
 unique function h : Y → X such that pA ∘ h ≈ qA and pB ∘ h ≈ qB." 

 --------
 给定C中的共向：

 A B
 \       /
 f \ / g
 \   /
 v
 C

 从集合论角度看，这可以被看作是选出
 在f和g下一致，即满足以下方程的条件：

 f（a） = g（b），对于∈A， b ∈ B

 拉回是A和B笛卡尔积的子集，
 X ⊆ A × B，恰好由满足 f（a） = g（b） 的对（a， b）组成，
 其中下图交换：

 X
 /   \
 pA / \ pB
 /       \
 A B
 \       /
 f \ / g
 \   /
 v
 C一个例子是两个 SQL 表的 INNER JOIN，其中 f 投射 A 的主键，g 投射引用 A 的外键，因此 X 精确包含所有来自 A 和 B 的行对，其中 id(A) = fkey(B)。

 维基百科：“事实上，pullback 是寻找像这样的交换平方的通用解。换句话说，给定任何交换平方 [replacing in the above X with Y, and pA and pB with qA and qB]，存在唯一函数 h : Y → X，使得 pA ∘ h ≈ qA 且 pB ∘ h ≈ qB。”
*)

(*
 Definition, in terms of morphisms and universal properties:

 Wikipedia: "A pullback of the morphisms f and g consists of an object P
 [Pull] and two morphisms p1 : P → X [pullback_fst] and p2 : P → Y
 [pullback_snd] for which the diagram

 P ---p2---> Y
 |           |
 p1|           |g
 |           |
 X ---f----> Z

 commutes. Moreover, the pullback (P, p1, p2) must be universal with respect
 to this diagram. That is, for any other such triple (Q, q1, q2) for which
 the following diagram commutes, there must exist a unique u : Q → P (called
 a mediating morphism) such that

 p1 ∘ u = q1,    p2 ∘ u = q2

 As with all universal constructions, a pullback, if it exists, is unique up
 to isomorphism. In fact, given two pullbacks (A, a1, a2) and (B, b1, b2) of
 the same cospan X → Z ← Y, there is a unique isomorphism between A and B
 respecting the pullback structure (proven below as [pullback_unique])." 

 --------
 从态射和泛性质的角度定义：

 维基百科：“态射 f 和 g 的抽象积由一个对象 P 以及两个态射 p1 : P → X 和 p2 : P → Y 组成，使得下图交换：

 P ---p2---> Y
 |           |
 p1|           |g
 |           |
 X ---f----> Z

 此外，抽象积 (P, p1, p2) 必须相对于该图是普遍的。也就是说，对于任何其他满足以下图交换的三元组 (Q, q1, q2)，必须存在唯一的 u : Q → P（称为中介态射），使得

 p1 ∘ u = q1,    p2 ∘ u = q2与所有普适构造一样，如果存在拉回，它在同构意义下是唯一的。实际上，给定同一共尖 X → Z ← Y 的两个拉回 (A, a1, a2) 和 (B, b1, b2)，存在唯一的同构从 A 到 B 并且尊重拉回结构（下面证明为 [pullback_unique]）。
*)

(*
 Purpose, history, and the reach of the pullback

 nLab:  https://ncatlab.org/nlab/show/base+change
 nLab:  https://ncatlab.org/nlab/show/finite+limit
 nLab:  https://ncatlab.org/nlab/show/hyperdoctrine
 nLab:  https://ncatlab.org/nlab/show/span

 The pullback is the categorical semantics of an equation (nLab,
 "pullback"), and every use of it is some avatar of solving that equation
 universally.  One limit thereby subsumes many familiar operations.
 Pulling a monomorphism back along f computes the preimage of the
 subobject it names; the pullback of two monomorphisms is the
 intersection of subobjects; the pullback of f along itself is its
 kernel pair ([kernel_pair] in Structure/Regular.v); and trivializing z
 to the terminal object recovers the binary product, the reduction
 recorded in the closing notes of this file.  Conversely, a terminal
 object together with [HasPullbacks] generates every finite limit
 (Borceux, "Handbook of Categorical Algebra" I, Prop. 2.8.2), which is
 why Structure/Regular.v presents finite completeness economically as
 exactly those two structures.

 The name is imported from topology.  Steenrod's induced bundle
 (Steenrod, "The Topology of Fibre Bundles", Princeton University Press
 1951) forms, from a bundle over M and a map N → M, the bundle of pairs
 of a point of N and a bundle point over its image — this construction
 verbatim — and the classification of principal G-bundles as pullbacks
 of a universal bundle made the operation central to algebraic topology.
 Algebraic geometry knows the same limit as Grothendieck's produit fibré
 (Grothendieck and Dieudonné, "Éléments de géométrie algébrique" I,
 Publ. Math. IHÉS 4, 1960, §3.2); base change along a morphism is the
 engine of the relative point of view there, and for affine schemes the
 fibre product of Spec A and Spec B over Spec R is Spec of the tensor
 product A ⊗_R B (Wikipedia, "Pullback (category theory)").  The
 adjective "cartesian" descends from Grothendieck's fibered categories
 (Streicher, "Fibered Categories à la Jean Bénabou", arXiv:1801.02927):
 the cartesian arrows of the codomain fibration are precisely pullback
 squares, a correspondence realized in-tree by
 [codomain_cleaving_pullbacks] in Construction/Displayed/Codomain.v.

 In categorical logic, substitution is pullback.  Lawvere's
 hyperdoctrines (Lawvere, "Adjointness in Foundations", Dialectica 23,
 1969) cast reindexing along f as the interpretation of substitution and
 the quantifiers ∃ and ∀ as its adjoints, and Seely identified locally
 cartesian closed categories as semantics for dependent type theory
 (Seely, "Locally cartesian closed categories and type theory", Math.
 Proc. Camb. Phil. Soc. 95, 1984), reading the adjoint triple
 Σ_f ⊣ f* ⊣ Π_f as dependent sum, substitution, and dependent product.
 The base-change functor between slices, with its left adjoint, is built
 in Construction/Slice/Pullback.v as [Bang_Functor] ⊣ [Star_Functor],
 proved there as [Base_Functor_Adjunction] (dependent sum on the LEFT);
 topos theory rests on the same operation, for
 Structure/SubobjectClassifier.v exhibits every mono as a pullback of
 [truth] in exactly one way, and Theory/Subobject/Functor.v obtains the
 Sub functor by chosen-pullback reindexing.

 A design note.  The [Pullback] record below packages the apex
 existentially — a pullback of f and g exists, and here is one — so it
 cannot assert that a GIVEN commuting square is a pullback.  The
 apex-pinned predicate [IsPullback], with conversions in both
 directions, the pasting law [pullback_paste], mono-stability
 [monic_pullback_stable], and the strengthened uniqueness
 [pullback_transport] — re-derived there because [pullback_unique]
 below is Qed-opaque — live in Theory/Morphisms/Stability.v, and that
 split carries the subobject and classifier developments.
 Structure/Pullback/Limit.v reconciles this record with [Limit] of a
 cospan diagram over the walking roof of Instance/Roof.v;
 Construction/Span/Category.v composes spans by exactly this
 construction (nLab, "span"); Instance/FinSet/Classifier.v computes
 [FinSet_Pullbacks] as counted subsets, so pullback objects reduce on
 closed inputs; and the INNER JOIN reading in the header above is
 developed by Spivak ("Category Theory for the Sciences", MIT Press
 2014).

 [WeakPullback] earns its keep in coalgebra.  Rutten's structure theory
 of bisimulations (Rutten, "Universal coalgebra: a theory of systems",
 Theoretical Computer Science 249, 2000) turns on whether an
 endofunctor weakly preserves pullbacks — carries pullback squares to
 weak pullback squares — and existence-only mediators, as in
 [weak_ump_pullbacks], are exactly what that hypothesis consumes. 

 --------
 回撤的目的、历史及影响范围

 nLab:   https://ncatlab.org/nlab/show/base+change 
 nLab:   https://ncatlab.org/nlab/show/finite+limit 
 nLab:   https://ncatlab.org/nlab/show/hyperdoctrine 
 nLab:   https://ncatlab.org/nlab/show/span拉回是一个方程的范畴语义（nLab，“pullback”），每一次使用它都是以某种方式普遍地解这个方程。一个极限因此包含了许多熟悉的操作。沿着f拉回一个单态计算它所命名的子对象的原像；两个单态的拉回是子对象的交集；f自身的拉回是它的核对（[kernel_pair] 在 Structure/Regular.v 中）；将 z 简化为终对象则恢复二元积，这是本文件结尾备注中记录的归约。反过来，终对象与 [HasPullbacks] 一起生成每一个有限极限（Borceux，《范畴代数手册》I，命题）。2.8.2），这就是为什么 Structure/Regular.v 经济地将有限完备性呈现为恰好这两个结构。这个名称是从拓扑学引入的。Steenrod 的诱导丛（Steenrod，《纤维丛的拓扑》，普林斯顿大学出版社，1951）由 M 上的一个丛和一个映射 N → M 构成，形成 N 的一个点与其像上的丛点的配对丛——这个构造逐字对应——主 G 丛作为一个万能丛的拉回的分类使得该操作在代数拓扑中具有核心地位。代数几何也认识到同样的极限，即 Grothendieck 的 produit fibré（Grothendieck 和 Dieudonné，《代数几何要素》I，Publ. Math.IHÉS 4, 1960, §3.2）；沿着一个态射的基变换是相对观点的引擎，对于仿射模式，Spec A 和 Spec B 在 Spec R 上的纤维积是张量积 A ⊗_R B 的 Spec（维基百科，“拉回（范畴论）”）。形容词“笛卡尔的”源自格罗滕迪克的纤维范畴（Streicher，“Fibered Categories à la Jean Bénabou”，arXiv:1801.02927）：余域纤维化的笛卡尔箭头恰好是拉回平方，这种对应关系在树中由 [codomain_cleaving_pullbacks] 在 Construction/Displayed/Codomain.v 中实现。在范畴逻辑中，替换就是拉回。Lawvere 的超命题（Lawvere, “Adjointness in Foundations”, Dialectica 23, 1969）将沿 f 的重索引看作替换的解释，并将量词 ∃ 和 ∀ 看作它的伴随，Seely 将局部笛卡尔闭范畴识别为依赖类型理论的语义（Seely, “Locally cartesian closed categories and type theory”, Math. Proc. Camb. Phil. Soc. 95, 1984），将伴随三重 Σ_f ⊣ f* ⊣ Π_f 解释为依赖和、替换和依赖积。切片之间的基变换函子及其左伴随在 Construction/Slice/Pullback.v 中构造为 [Bang_Functor] ⊣ [Star_Functor]， 并在那里证明为 [Base_Functor_Adjunction]（左侧的依赖和）； 拓扑学理论也依赖同样的操作，因为 Structure/SubobjectClassifier.v 将每个单射展示为 [truth] 的唯一拉回，而 Theory/Subobject/Functor.v 通过选定的拉回重索引得到 Sub 函子。一个设计说明。下面的 [Pullback] 记录以存在方式封装了顶点——存在 f 和 g 的拉回，而这里就是一个——所以它不能断言某个给定的交换方形是一个拉回。顶点固定谓词 [IsPullback]，双向转换，粘贴律 [pullback_paste]，单态稳定性 [monic_pullback_stable]，以及强化的唯一性 [pullback_transport]——在那里重新推导，因为下面的 [pullback_unique] 是 Qed-不透明的——都在 Theory/Morphisms/Stability.v 中，并且该拆分承载了子对象和分类器的发展。Structure/Pullback/Limit.v 将此记录与 Instance/Roof.v 的行走屋顶上的余叉图 [Limit] 调和；Construction/Span/Category.v 正是通过这种构造（nLab，“span”）来组合跨度；Instance/FinSet/Classifier.v 将 [FinSet_Pullbacks] 计算为计数子集，因此在封闭输入上拉回对象会简化；上面标题中的 INNER JOIN 读法由 Spivak（《科学的范畴论》，MIT 出版社，2014）发展。[WeakPullback] 在余代数中发挥作用。Rutten 的双模拟结构理论（Rutten，《通用余代数：系统理论》，理论计算机科学 249, 2000）依赖于一个终函子是否弱保持拉回——将拉回方格映射到弱拉回方格——而仅存在的中介者，如 [weak_ump_pullbacks]，正是该假设所需要的。
*)

Record Pullback {C : Category} {x y z : C} (f : x ~> z) (g : y ~> z) := {
  Pull         : C;            (* the pullback object b ×_a c (fibered product) / 拉回对象 b ×_a c（纤维积） *)
  pullback_fst : Pull ~> x;    (* projection p1 : Pull ~> x / 投影 p1 : 拉 ~> x *)
  pullback_snd : Pull ~> y;    (* projection p2 : Pull ~> y / 投影 p2 : 拉 ~> y *)

  (* the projection square commutes / 投影平方可交换 *)
  pullback_commutes : f ∘ pullback_fst ≈ g ∘ pullback_snd;

  (*
 universal property: the commuting square is terminal among such squares,
 i.e. every competing cone (Q, q1, q2) factors through a unique mediator u 

 --------
 通用性质：对于这样的方形图，交换方是终端的，即每一个竞争圆锥 (Q, q1, q2) 都可以通过唯一的中介 u 进行分解
*)
  ump_pullbacks : ∀ Q (q1 : Q ~> x) (q2 : Q ~> y), f ∘ q1 ≈ g ∘ q2
    → ∃! u : Q ~> Pull, pullback_fst ∘ u ≈ q1 ∧ pullback_snd ∘ u ≈ q2
}.

Coercion pullback_ob {C : Category} {x y z : C} (f : x ~> z) (g : y ~> z)
         (L : Pullback f g) := @Pull _ _ _ _ _ _ L.

(*
   * Pullbacks are unique up to a unique isomorphism respecting the projections.
   This is the standard proof from the universal property: each pullback gives
   a mediating morphism into the other, and the round-trip mediator into a
   pullback from itself must equal [id] by uniqueness. 

   --------
   * 拉回在满足投影的唯一同构下是唯一的。这是来自泛性质的标准证明：每个拉回都会给出一个到另一个的中介态射，并且从自身到拉回的往返中介态射必须由于唯一性而等于 [id]。
*)
Lemma pullback_unique {C : Category} {x y z : C} {f : x ~> z} {g : y ~> z}
      (P Q : Pullback f g) : Pull f g P ≅ Pull f g Q.
Proof.
  pose proof (ump_pullbacks f g Q _ (pullback_fst f g P) (pullback_snd f g P)
                            (pullback_commutes f g P)) as HQ.
  pose proof (ump_pullbacks f g P _ (pullback_fst f g Q) (pullback_snd f g Q)
                            (pullback_commutes f g Q)) as HP.
  pose proof (ump_pullbacks f g P _ (pullback_fst f g P) (pullback_snd f g P)
                            (pullback_commutes f g P)) as HPP.
  pose proof (ump_pullbacks f g Q _ (pullback_fst f g Q) (pullback_snd f g Q)
                            (pullback_commutes f g Q)) as HQQ.
  destruct (unique_property HQ) as [HQfst HQsnd].
  destruct (unique_property HP) as [HPfst HPsnd].
  unshelve refine {|
    to   := unique_obj HQ;
    from := unique_obj HP
  |}.
  - (* to ∘ from ≈ id at Pull Q, by uniqueness against HQQ / 在拉取 Q 时，由于与 HQQ 的唯一性，得到 to ∘ from ≈ id *)
    transitivity (unique_obj HQQ).
    + symmetry; apply (uniqueness HQQ); split.
      * rewrite comp_assoc, HQfst; exact HPfst.
      * rewrite comp_assoc, HQsnd; exact HPsnd.
    + apply (uniqueness HQQ); split; apply id_right.
  - (* from ∘ to ≈ id at Pull P, by uniqueness against HPP / 从 ∘ 到 ≈ id 在 Pull P，通过与 HPP 的唯一性 *)
    transitivity (unique_obj HPP).
    + symmetry; apply (uniqueness HPP); split.
      * rewrite comp_assoc, HPfst; exact HQfst.
      * rewrite comp_assoc, HPsnd; exact HQsnd.
    + apply (uniqueness HPP); split; apply id_right.
Defined.

(*
   * A category has all binary pullbacks if every cospan has a pullback.
   This is the dual of [HasPushouts] in [Structure/Pushout.v]. 

   --------
   * 如果每个共跨度都有一个拉回，则一个范畴具有所有二元拉回。
   这是 [Structure/Pushout.v] 中 [HasPushouts] 的对偶。
*)
Class HasPullbacks (C : Category) : Type := {
  pullback : forall {x y z : C} (f : x ~> z) (g : y ~> z), Pullback f g
}.

Arguments pullback {C _ x y z} f g.

(*
 A weak pullback differs from a pullback in that the mediating morphism is
 merely required to exist; uniqueness is dropped. 

 --------
 弱拉回不同于拉回之处在于，中介态射只需存在即可；不要求唯一性。
*)
Record WeakPullback {C : Category} {x y z : C} (f : x ~> z) (g : y ~> z) := {
  weak_pull : C;
  weak_pullback_fst : weak_pull ~> x;
  weak_pullback_snd : weak_pull ~> y;

  weak_pullback_commutes :
    f ∘ weak_pullback_fst ≈ g ∘ weak_pullback_snd;

  weak_ump_pullbacks :
    ∀ Q (q1 : Q ~> x) (q2 : Q ~> y),
      f ∘ q1 ≈ g ∘ q2
      → ∃ u : Q ~> weak_pull,
          weak_pullback_fst ∘ u ≈ q1 ∧ weak_pullback_snd ∘ u ≈ q2
}.

(* Every pullback is a weak pullback by forgetting uniqueness. / 每一次回调都是通过忘记独特性而显得薄弱的回调。 *)
Definition Pullback_to_WeakPullback {C : Category} {x y z : C}
           {f : x ~> z} {g : y ~> z} (P : Pullback f g) : WeakPullback f g.
Proof.
  refine {|
    weak_pull              := Pull f g P;
    weak_pullback_fst      := pullback_fst f g P;
    weak_pullback_snd      := pullback_snd f g P;
    weak_pullback_commutes := pullback_commutes f g P
  |}.
  intros Q q1 q2 H.
  pose proof (ump_pullbacks f g P Q q1 q2 H) as U.
  exists (unique_obj U).
  exact (unique_property U).
Defined.

(*
 Both reductions sketched below are now PROVED, in
 [Structure/Pullback/Reduction.v]; the two dated TODO markers that stood
 here since 2017 are retired accordingly.  The terminal-object
 trivialization is [product_of_pullback] (apex-pinned, landing in
 [IsCartesianProduct]) and
 [Cartesian_of_HasPullbacks_Terminal]; the wide generalization -- an
 [I]-indexed product as the wide pullback over the terminal object, Riehl
 2nd ed. Lemma 3.5.15 -- is [wide_pullback_product] in
 [Structure/Pullback/Wide.v]. 

 --------
 下面概述的两种约简现在在 [Structure/Pullback/Reduction.v] 中已被证明，自 2017 年以来标注为 TODO 的两条记录也因此被撤销。终端对象的平凡化是 [product_of_pullback]（顶点固定，降落在 [IsCartesianProduct]）以及 [Cartesian_of_HasPullbacks_Terminal]；广义推广——作为终端对象上的广泛拉回的一个 [I] 索引的乘积，参见 Riehl 第二版引理 3.5.15——在 [Structure/Pullback/Wide.v] 中是 [wide_pullback_product]。
*)
(*
 Wikipedia: "The pullback is similar to the product, but not the same. One
 may obtain the product by "forgetting" that the morphisms f and g exist,
 and forgetting that the object Z exists. One is then left with a discrete
 category containing only the two objects X and Y, and no arrows between
 them. This discrete category may be used as the index set to construct the
 ordinary binary product. Thus, the pullback can be thought of as the
 ordinary (Cartesian) product, but with additional structure. Instead of
 "forgetting" Z, f, and g, one can also "trivialize" them by specializing Z
 to be the terminal object (assuming it exists). f and g are then uniquely
 determined and thus carry no information, and the pullback of this cospan
 can be seen to be the product of X and Y." 

 --------
 维基百科：“拉回（pullback）类似于积（product），但不完全相同。可以通过‘忽略’态射 f 和 g 的存在，以及忽略对象 Z 的存在来得到积。这样，就只剩下一个离散范畴，其中仅包含两个对象 X 和 Y，并且它们之间没有箭头。这个离散范畴可以用作构建普通二元积的索引集合。因此，拉回可以被认为是普通（笛卡尔）积，但具有额外的结构。除了‘忽略’ Z、f 和 g 之外，也可以通过将 Z 专门化为终对象（如果存在的话）来‘使它们平凡化’。此时 f 和 g 唯一确定，因此不携带任何信息，可以看到这个余叉图（cospan）的拉回是 X 和 Y 的积。”
*)

(*
 Also PROVED in [Structure/Pullback/Reduction.v]: [pullback_of_equalizer]
 with [HasPullbacks_of_Cartesian_HasEqualizers] for the direction quoted
 below, and [equalizer_of_pullback] for the converse (Awodey 2nd ed. Prop.
 5.7).  Read the last sentence of the quotation with care: this file does
 NOT establish the general "all finite limits" claim -- only the binary and
 parallel-pair generators are related here; that claim is Structure/Limit/
 Finite.v's [FinitelyComplete], built from products and equalizers. 

 --------
 也在 [Structure/Pullback/Reduction.v] 中证明：[pullback_of_equalizer]
 使用 [HasPullbacks_of_Cartesian_HasEqualizers] 对下面引用的方向进行证明，
 并使用 [equalizer_of_pullback] 证明逆命题（Awodey 第二版，命题 5.7）。仔细阅读引用中的最后一句话：该文件并未建立一般的“所有有限极限”结论——这里只涉及二元和并行对生成器；该结论是 Structure/Limit/Finite.v 的 [FinitelyComplete]，由积和等化子构建。
*)
(*
 Wikipedia: "... another way of characterizing the pullback: as the
 equalizer of the morphisms f ∘ p1, g ∘ p2 : X × Y → Z where X × Y is the
 binary product of X and Y and p1 and p2 are the natural projections. This
 shows that pullbacks exist in any category with binary products and
 equalizers. In fact, by the existence theorem for limits, all finite limits
 exist in a category with a terminal object, binary products and
 equalizers." 

 --------
 维基百科：“……另一种描述拉回的方式：将其视为态射 f ∘ p1, g ∘ p2 : X × Y → Z 的等化子，其中 X × Y 是 X 和 Y 的二元积，p1 和 p2 是自然投影。这表明在任何具有二元积和等化子的范畴中都存在拉回。事实上，根据极限存在定理，在具有终对象、二元积和等化子的范畴中，所有有限极限都存在。”
*)
