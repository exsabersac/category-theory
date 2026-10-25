Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(** The interval category 2 (the "walking arrow"). / 二度音程类别（“行进箭头”）。 *)

(*
 nLab:      https://ncatlab.org/nlab/show/interval+category
 nLab:      https://ncatlab.org/nlab/show/walking+structure (walking morphism)
 Wikipedia: https://en.wikipedia.org/wiki/Posetal_category

 2 is the ordinal {0 < 1} regarded as a (thin / posetal) category: two
 objects 0, 1, their identities, and a single non-identity arrow 0 → 1.
 There is NO arrow 1 → 0.  Here the objects are named TwoX (= 0) and
 TwoY (= 1), and the non-identity arrow is TwoXY : TwoX ~> TwoY.

 2 is the "walking arrow": a functor 2 ⟶ C is exactly a choice of one
 morphism of C (the image of TwoXY), so functors out of 2 classify the
 morphisms of C, and the functor category [2, C] is the arrow category of
 C (objects = arrows of C, morphisms = commutative squares).  Both halves
 of that sentence are theorems in Theory/Shapes.v: [Walk] and [arrow_of]
 with their round trips for the first, and [Two_Fun_Arrow] for the
 second, the latter an equivalence of categories in the sense of
 Instance/Cat.v rather than an isomorphism of categories. 

 --------
 nLab:       https://ncatlab.org/nlab/show/interval+category
 nLab:       https://ncatlab.org/nlab/show/walking+structure（行走态射）
 Wikipedia:  https://en.wikipedia.org/wiki/Posetal_category

 2 是顺序集 {0 < 1}，被视为一个（稀疏/偏序）范畴：两个对象 0 和 1，它们的恒等映射，以及一个从 0 到 1 的非恒等箭头。
 没有从 1 到 0 的箭头。这里对象被命名为 TwoX (= 0) 和 TwoY (= 1)，非恒等箭头是 TwoXY : TwoX ~> TwoY。2 是“行走箭头”：一个函子 2 ⟶ C 恰好是 C 的一个态射的选择（TwoXY 的像），因此从 2 出发的函子分类了 C 的态射，而函子范畴 [2, C] 是 C 的箭头范畴（对象 = C 的箭头，态射 = 交换方形图）。该句的两半都是 Theory/Shapes.v 中的定理：第一部分是 [Walk] 和 [arrow_of] 以及它们的往返，第二部分是 [Two_Fun_Arrow]，后者在 Instance/Cat.v 的意义下是范畴的等价，而不是范畴的同构。
*)

(*
 The smallest non-trivial shape, and the smallest object of truth values

 nLab:      https://ncatlab.org/nlab/show/diagram
 nLab:      https://ncatlab.org/nlab/show/walking+morphism
 nLab:      https://ncatlab.org/nlab/show/walking+structure
 Paper:     Lawvere, "Metric spaces, generalized logic, and closed
 categories", Rendiconti del Seminario Matematico e Fisico
 di Milano XLIII, 1973
 Paper:     Foltz, Lair, Kelly, "Algebraic categories with few
 monoidal biclosed structures or none", J. Pure Appl.
 Algebra 17(2), 1980

 Two readings of [_2] run through the library, and the header above
 states the first of them.  In one it is a SHAPE, the diagram over which
 a construction is taken; in the other it is an object of TRUTH VALUES,
 the base over which enrichment produces preorders.  Both readings turn
 on the same property, that [_2] is thin.

 As a shape, [_2] is the smallest non-trivial one, and the arrow-category
 identification recorded above is the first entry in a longer list.  A
 diagram of shape J in a category C is a functor from J to C; the
 category J is its shape, index, or scheme, and a limit or colimit is a
 universal cone over such a functor, presented through the diagonal
 functor of Functor/Diagonal.v (nLab, "diagram"; Mac Lane, Categories
 for the Working Mathematician, 2nd ed., 1998).  The shape isolates the
 combinatorial pattern of a construction from the category in which it is
 instantiated, and the small shapes together account for the finite
 limits and colimits: the walking parallel pair [Parallel]
 (Instance/Parallel.v) for equalizers and coequalizers, the walking span
 [Roof] (Instance/Roof.v) for pushouts and pullbacks, the discrete pair
 [Two_Discrete] (Instance/Two/Discrete.v) for binary products and
 coproducts, and the empty shape [_0] (Instance/Zero.v) for terminal and
 initial objects, with the point [_1] (Instance/One.v) the trivial
 one-object shape.

 The name "walking arrow" belongs to a settled family of synonyms.  The
 nLab records walking, free-standing, and free-living for the one idea,
 attributes "walking" to James Dolan, and traces "free-living" to Foltz,
 Lair and Kelly (1980); the governing principle is that the walking X
 coclassifies X, so that functors OUT OF it are exactly the X-structures
 of the target.  The arrow-category reading above is that principle taken
 at a single morphism.

 The second reading regards [_2] as the two-element order {TwoX < TwoY}
 with meet for tensor and the top [TwoY] for unit.  Lawvere, dating the
 observation to a 1967 lecture of Richard Swan, drew the analogy between
 the composition of hom-objects and the triangle inequality and read off
 its consequences by varying the base: over [_2] enrichment produces
 preorders, over the interval [0, ∞] it produces metric spaces (Lawvere,
 1973).  The library carries the first case in full.
 Instance/Two/Monoidal.v places the cartesian monoidal structure
 [Two_Monoidal] on [_2] (tensor the meet [two_meet], unit the top
 [TwoY]), and Construction/Enriched/Two.v then proves categories enriched
 over it to be preorders and enriched functors to be monotone maps
 ([Enriched_Two_preorder], [EnrichedFunctor_Two_monotone]).  The move is
 from asking whether an arrow x ⟶ y exists to asking whether x ≤ y holds.

 [_2] carries two further identities.  It is the directed interval: the
 canonical interval object of Cat, the 1-simplex, the 1-globe, and the
 first oriental, so that a natural transformation between two functors
 from C to D is a functor from C ∏ [_2] to D, a directed homotopy (nLab,
 "walking morphism").  And it underlies a decategorified logic: thin
 categories are exactly those enriched over the Boolean algebra [_2] as a
 cartesian monoidal category, a Heyting algebra is a skeletal thin
 finitely-cocomplete cartesian-closed category, and a Boolean algebra a
 skeletal thin finitely-cocomplete star-autonomous one (Wikipedia,
 "Posetal category").  That [_2] itself is skeletal is [Two_Skeletal]
 (Theory/Skeleton/Separation.v).

 Computationally, thinness means the hom is proof-irrelevant, a mere
 proposition, so [_2] is a (0,1)-category.  Instance/Two/Monoidal.v makes
 this concrete: [Two_thin] below says any two parallel arrows coincide
 (Instance/Two/Monoidal.v's [two_thin] is now that lemma re-exported), which
 discharges every coherence obligation uniformly and is why the strict
 [Morphism_equality] setoid recorded above suffices.  Two consequences
 follow.  A functor out of [_2] materializes one morphism together with
 its endpoints, as [_2_as_Set] does by carrying [TwoXY] to the empty
 function from False to True.  And an enrichment over [_2] must compute a
 truth value, an object of [_2], for each pair of objects, which is why
 Construction/Enriched/Two.v carries a decidable, Type-valued order: the
 constructive reading of whether x ≤ y holds. 

 --------
 最小的非平凡形状，以及最小的真值对象

 nLab:       https://ncatlab.org/nlab/show/diagram 
 nLab:       https://ncatlab.org/nlab/show/walking+morphism 
 nLab:       https://ncatlab.org/nlab/show/walking+structure 
 论文:     Lawvere, "度量空间、广义逻辑和闭范畴", 米兰数学与物理研讨会报告 XLIII, 1973
 论文:     Foltz, Lair, Kelly, "具有少量或无单体双闭结构的代数范畴", 纯应用代数杂志 17(2), 1980

 [_2] 的两种读法贯穿整个文库，上面的标题陈述了其中第一种读法。在一种读法中，它是一个形状（SHAPE），在其上进行构造；在另一种读法中，它是一个真值对象（TRUTH VALUES），通过该基础进行丰富化以生成预序。两种读法都依赖于同一性质，即 [_2] 是薄的。作为一种形状，[_2] 是最小的非平凡形状，上面记录的箭头分类识别是一个更长列表中的第一个条目。在范畴 C 中的形状 J 的图是从 J 到 C 的函子；范畴 J 是其形状、索引或方案，而极限或余极限是该函子上的一个普遍锥，通过 Functor/Diagonal.v 的对角函子表示（nLab，“diagram”；Mac Lane，《Categories for the Working Mathematician》，第 2 版，1998 年）。这个形状将一个结构的组合模式与其被实例化的范畴隔离开来，而这些小形状一起解释了有限极限和余极限：用于等化器和共同等化器的步行平行对 [Parallel] (Instance/Parallel.v)，用于推出和拉回的步行跨度 [Roof] (Instance/Roof.v)，用于二元积和二元余积的离散对 [Two_Discrete] (Instance/Two/Discrete.v)，用于终对象和始对象的空形状 [_0] (Instance/Zero.v)，以及作为简单的单对象形状的点 [_1] (Instance/One.v)。“walking arrow”这个名称属于一组固定的同义词。nLab 为同一个概念记录了 walking、free-standing 和 free-living，将“walking”归因于 James Dolan，并将“free-living”追溯到 Foltz、Lair 和 Kelly（1980）；支配原则是 walking X 对 X 进行同类分类，因此由其导出的函子正好是目标的 X-结构。上述箭头范畴的理解就是将该原则应用于单一的态射。第二种理解将 [_2] 看作二元素的秩序 {TwoX < TwoY}，其会合为张量，顶部 [TwoY] 作为单位。Lawvere 将这一观察追溯到 Richard Swan 1967 年的一次讲座，他将同对象的组合与三角不等式进行了类比，并通过改变基类推导其结果：在 [_2] 上，丰富结构生成了预序，在区间 [0, ∞] 上，它生成了度量空间（Lawvere, 1973）。库完整包含了第一种情况。Instance/Two/Monoidal.v 将笛卡尔单元结构 [Two_Monoidal] 放置于 [_2] 上（张量为会合 [two_meet]，单位为顶部 [TwoY]），然后 Construction/Enriched/Two.v 证明了在其上丰富的范畴是预序，丰富函子是单调映射（[Enriched_Two_preorder]，[EnrichedFunctor_Two_monotone]）。这个转变是从询问是否存在箭头 x ⟶ y，变为询问 x ≤ y 是否成立。[_2] 拥有另外两个身份。它是有向区间：Cat 的典范区间对象、1-单形、1-球体，以及第一个东方，因此从 C 到 D 的两个函子之间的自然变换是一个从 C ∏ [_2] 到 D 的函子，一个有向同伦（nLab，"walking morphism"）。它还构成了去范畴化逻辑：薄范畴恰好是那些在笛卡尔单体范畴下以布尔代数 [_2] 富化的范畴，Heyting 代数是骨架薄、有限完备、闭笛卡尔范畴，而布尔代数则是骨架薄、有限完备、星自主范畴（Wikipedia，"Posetal category"）。[_2] 本身是骨架的这一点是 [Two_Skeletal] （Theory/Skeleton/Separation.v）。在计算上，薄性意味着 hom 是与证明无关的，仅仅是一个命题，因此 [_2] 是一个 (0,1)-范畴。Instance/Two/Monoidal.v 将其具体化：下面的 [Two_thin] 表示任何两个平行箭头都相同（Instance/Two/Monoidal.v 的 [two_thin] 现在是那个重新导出的引理），这统一地释放了每个相干性义务，这也是上述严格 [Morphism_equality] 集合体足够的原因。由此产生两个结果。一个来自 [_2] 的函子体现了一个态射及其端点，正如 [_2_as_Set] 通过将 [TwoXY] 携带到从 False 到 True 的空函数所做的那样。并且 [_2] 上的一个增强必须为每一对对象计算一个真值——[_2] 的对象，这就是为什么 Construction/Enriched/Two.v 包含一个可判定的、类型值的顺序：即 x ≤ y 是否成立的构造性解读。
*)

Inductive TwoObj : Set := TwoX | TwoY.

Inductive TwoHom : TwoObj → TwoObj → Set :=
  | TwoIdX : TwoHom TwoX TwoX
  | TwoIdY : TwoHom TwoY TwoY
  | TwoXY  : TwoHom TwoX TwoY.

Definition TwoHom_inv_t : ∀ x y, TwoHom x y → Prop.
Proof.
  intros [] [] f.
  - exact (f = TwoIdX).
  - exact (f = TwoXY).
  - exact False.          (* Unused, any Prop is ok here / 未使用，这里任何道具都可以 *)
  - exact (f = TwoIdY).
Defined.

Corollary TwoHom_inv x y f : TwoHom_inv_t x y f.
Proof. destruct f; reflexivity. Qed.

Lemma TwoHom_Y_X_absurd : TwoHom TwoY TwoX → False.
Proof. inversion 1. Qed.

#[export] Hint Extern 4 => contradiction TwoHom_Y_X_absurd : two_laws.

Local Set Warnings "-intuition-auto-with-star".

(*
 The category 2 has two objects TwoX, TwoY, their identity morphisms, and
 one non-identity morphism TwoXY : TwoX ~> TwoY from the first to the
 second.  The hom-sets carry strict (Leibniz) equality via
 Morphism_equality, since 2 is thin (at most one arrow between objects). 

 --------
 类别2有两个对象TwoX、TwoY，它们的恒等态射，以及一个从第一个对象到第二个对象的非恒等态射TwoXY : TwoX ~> TwoY。由于2是薄的（对象之间最多有一个箭头），同态集合通过Morphism_equality携带严格的（莱布尼茨）等式。
*)

Program Definition _2 : Category := {|
  obj     := TwoObj;
  hom     := TwoHom;
  homset  := Morphism_equality;
  id      := fun x => match x with
    | TwoX => TwoIdX
    | TwoY => TwoIdY
    end;
  compose := fun x y z (f : TwoHom y z) (g : TwoHom x y) =>
    match x, y, z with
    | TwoX, TwoX, TwoX => TwoIdX
    | TwoY, TwoY, TwoY => TwoIdY
    | TwoX, TwoX, TwoY => TwoXY
    | TwoX, TwoY, TwoY => TwoXY
    | _,    _,    _    => _
    end
|}.
Next Obligation. destruct x, y, z; intuition; auto with *. Qed.
Next Obligation.
  destruct x, y, z; auto with two_laws;
  intuition; discriminate.
Qed.
Next Obligation.
  destruct x, y, z; auto with two_laws;
  intuition; discriminate.
Qed.
Next Obligation.
  destruct x, y, z; auto with two_laws;
  intuition; discriminate.
Qed.
Next Obligation. destruct f; auto. Qed.
Next Obligation. destruct f; auto. Qed.
Next Obligation. destruct x, y, z, w; auto with two_laws; intuition; auto with *. Qed.
Next Obligation. destruct x, y, z, w; auto with two_laws; intuition. Qed.

(* ------------------------------------------------------------------------ *)
(* * ** A bimorphism that is not an isomorphism / * ** 一个不是同构的双态射 *)

(*
 Mac Lane, CWM 2nd ed., §I.5 Exercise 3: there are categories carrying an
 arrow that is both monic and epic yet has no inverse, so "bimorphic ⇒ iso"
 -- the property called BALANCEDness (nLab: balanced category) -- is not a
 theorem of category theory.  [Bimorphic] is defined in Theory/Morphisms.v
 and, before this, was never instantiated anywhere in the tree, so the
 library had no witness that the notion is even inhabited, let alone that it
 is strictly weaker than invertibility.

 The interval category 2 supplies the cheapest one.  [TwoXY] is monic and
 epic for the same degenerate reason -- 2 is thin, so any two parallel
 arrows are equal outright -- and it is not invertible because there is no
 arrow TwoY ~> TwoX at all ([TwoHom_Y_X_absurd]).

 Balancedness is a property of particular categories rather than of the
 notion of arrow, and 2 is a category where it does not hold.  For the
 contrast, [Sets] IS balanced in tree: [Sets_balanced]
 (Instance/Sets.v) assembles [Monic f -> Epic f -> IsIsomorphism f] from
 [injectivity_is_monic] and [epic_implies_surjective] via [bijective_is_iso].
 An earlier revision of this comment said the second half was unavailable --
 "the direction abandoned at Instance/Sets.v" -- and that was true when
 written; it was proved subsequently.  So the contrast is genuine and
 sharper than first stated: [2] is not balanced while [Sets] is. 

 --------
 Mac Lane, CWM 第二版，§I.5 练习 3：存在一些范畴，它们有箭头既是单射又是满射，但没有逆，因此“双态 ⇒ 同构”（bimorphic ⇒ iso）——称为平衡性（BALANCEDness）（nLab: balanced category）——并不是范畴论的定理。[Bimorphic] 在 Theory/Morphisms.v 中定义，在此之前，从未在树的任何地方被实例化过，所以该库没有证据表明这一概念甚至是存在的，更不用说它严格比可逆性弱了。

 区间范畴 2 提供了最简单的一个。[TwoXY] 由于同样的退化原因既是单射又是满射——2 是稀薄的，因此任何两条平行箭头都直接相等——且它不可逆，因为根本不存在箭头 TwoY ~> TwoX（[TwoHom_Y_X_absurd]）。平衡性是特定范畴的一个属性，而不是箭头概念的属性，且在范畴 2 中该属性不成立。相比之下，[Sets] 在树结构中是平衡的：[Sets_balanced]（Instance/Sets.v）通过 [bijective_is_iso] 从 [injectivity_is_monic] 和 [epic_implies_surjective] 组装 [Monic f -> Epic f -> IsIsomorphism f]。之前对该注释的修改中提到后半部分不可用——“在 Instance/Sets.v 中被放弃的方向”——在撰写时确实如此；但随后已经得到了证明。因此，这种对比是真实的，且比最初表述的更加明显：[2] 不平衡，而 [Sets] 则平衡。
*)

Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.

(* Any two parallel arrows of 2 agree: the category is thin. / 任何两个平行的 2 箭头都是相等的：该范畴是薄范畴。 *)
Lemma Two_thin {x y : TwoObj} (f g : x ~{_2}~> y) : f ≈ g.
Proof.
  destruct x, y.
  - now rewrite (TwoHom_inv _ _ f), (TwoHom_inv _ _ g).
  - now rewrite (TwoHom_inv _ _ f), (TwoHom_inv _ _ g).
  - contradiction (TwoHom_Y_X_absurd f).
  - now rewrite (TwoHom_inv _ _ f), (TwoHom_inv _ _ g).
Qed.

Definition TwoXY_monic : @Monic _2 TwoX TwoY TwoXY.
Proof. constructor; intros z g1 g2 _; apply Two_thin. Qed.

Definition TwoXY_epic : @Epic _2 TwoX TwoY TwoXY.
Proof. constructor; intros z g1 g2 _; apply Two_thin. Qed.

Definition TwoXY_bimorphic : @Bimorphic _2 TwoX TwoY TwoXY :=
  (TwoXY_epic, TwoXY_monic).

(* But it has no inverse: an inverse would be an arrow TwoY ~> TwoX. / 但它没有逆：逆应该是一个箭头 TwoY ~> TwoX。 *)
Lemma TwoXY_not_iso : @IsIsomorphism _2 TwoX TwoY TwoXY → False.
Proof. intros [g _ _]; exact (TwoHom_Y_X_absurd g). Qed.

(* The exercise, packaged: 2 is not balanced. / 打包的练习：2 不平衡。 *)
Definition two_bimorphic_not_iso :
  @Bimorphic _2 TwoX TwoY TwoXY * (@IsIsomorphism _2 TwoX TwoY TwoXY → False) :=
  (TwoXY_bimorphic, TwoXY_not_iso).


(*
 Mac Lane, CWM 2nd ed., §I.5, printed p. 19.  CITED BY LOCATION; the printed
 text was not consulted.  The in-tree catalog entry for the item
 (doc/plan/books/maclane/inventory/I.json, id maclane:I.5:def5) records the
 aside that an arrow with a right inverse is epi, and that the converse
 holds in Set but not in Grp (paraphrased, not quoted).

 Mac Lane's own counterexample is out of reach in this tree, which has no
 category of groups.  Structure/Group.v defines group OBJECTS in a
 cartesian monoidal category, not Grp.  Instance/Comp.v comes closest and
 still misses: it has a TYPE of groups ([Group], algebras for the
 group signature and its equations) and a CATEGORY [Algs], but
 the objects of [Algs] are [OpAlgebra S] -- structures for a signature with
 the equations dropped -- so instantiating it at the group signature does
 not produce Grp.  Categories of algebras the tree does have, several of
 them: [Models T C] for a Lawvere theory (Theory/Lawvere/Model.v),
 [OperadAlgebras] for an operad (Theory/Multicategory/Algebra.v),
 [FAlg F] for an endofunctor (Construction/FAlg.v), [Algs] again, and
 the commutative monoids of Instance/CMon.v, which is the one carried far
 enough to serve as the tree's semiadditive witness.  None of them is Grp,
 and none is instantiated at the group signature anywhere in the tree:
 [GroupOp] (Instance/Comp.v) is used to build the TYPE [Group]
 and the single algebra [BoolOp], never the category [Algs] and
 never a Lawvere theory.

 The interval category gives a blunter counterexample, for the same reason
 it refutes balancedness above: [TwoXY] is epic, and there is no arrow
 TwoY ~> TwoX at all, so nothing can serve as a right inverse.  The same
 observation rules out regularity in the sense of Theory/Morphisms.v, since
 a pseudoinverse for [TwoXY] would also have to be an arrow TwoY ~> TwoX.
 So [RegularMorphism] is a real condition on an arrow: it is not satisfied
 by every arrow of every category, and in particular not by every
 epimorphism.

 Both halves of the witness are degenerate, and both degeneracies are worth
 naming.  [TwoXY] is epic because 2 is THIN, so [TwoXY_epic] proves nothing
 about cancellation; and it is non-regular because the reverse hom-set is
 EMPTY, so [TwoXY_not_regular] proves nothing about pseudoinverses.  The
 tree's other refutation of regularity has the same shape --
 [finset_empty_to_one_not_regular] (Instance/FinSet/Regular.v) again has an
 empty reverse hom-set -- and that is not a coincidence to be corrected by
 looking harder.  Over [Sets] the empty hom-set is what makes such a
 refutation available at all: [sets_coarsen_not_regular_absurd]
 (Instance/Sets/Regular.v) exhibits an arrow with INHABITED domain and
 INHABITED reverse hom-set whose non-regularity is refutable outright, its
 regularity being exactly the decidability of an arbitrary proposition
 ([sets_coarsen_regular_iff_dec]).  Where that proposition is undecided,
 neither answer can be proved, so the degeneracy above is a fact about the
 setting rather than a shortcut taken here. 

 --------
 Mac Lane, CWM 第二版，第 I.5 节，印刷页 19。引用自位置；未查阅印刷文本。该条目的树内目录条目（doc/plan/books/maclane/inventory/I.json，ID maclane:I.5:def5）记录了一个附注，即一个有右逆的箭头是满射，并且在 Set 中逆命题成立，但在 Grp 中不成立（意译，未引用原文）。Mac Lane 自己的反例在这棵树中是无法实现的，因为它没有群的范畴。Structure/Group.v 在一个笛卡尔幺半范畴中定义了群对象，而不是 Grp。Instance/Comp.v 是最接近的，但仍然不完全：它有一个群的类型（[Group]，即群的符号及其方程的代数）和一个范畴 [Algs]，但 [Algs] 的对象是 [OpAlgebra S]——这是在去掉方程后的符号结构——所以在群符号下实例化它并不能生成 Grp。该树确实有多种代数的类别，其中包括：[Models T C] 代表一个 Lawvere 理论 (Theory/Lawvere/Model.v)，[OperadAlgebras] 代表一个操作代数 (Theory/Multicategory/Algebra.v)，[FAlg F] 代表一个自函子 (Construction/FAlg.v)，[Algs] 再次出现，还有 Instance/CMon.v 的交换幺半群，这是唯一被充分使用到能够作为树的半加性证据的。它们没有一个是 Grp，并且在树中的任何地方都没有实例化到群签名：[GroupOp] (Instance/Comp.v) 用于构建 TYPE [Group] 和单个代数 [BoolOp]，从未用于类别 [Algs]，也从未用于 Lawvere 理论。区间范畴给出了一个更直白的反例，原因与上述它驳斥平衡性相同：[TwoXY] 是一个满射，并且根本没有箭头 TwoY ~> TwoX，所以没有什么可以作为右逆。相同的观察也排除了 Theory/Morphisms.v 意义下的正规性，因为 [TwoXY] 的伪逆也必须是一个箭头 TwoY ~> TwoX。因此 [RegularMorphism] 对一个箭头来说是一个真正的条件：并非每个范畴的每个箭头都满足它，尤其不是每个满射都满足。证人的两个部分都是退化的，而且这两种退化都值得命名。[TwoXY] 是史诗级的，因为 2 是纤细的，所以 [TwoXY_epic] 并不能证明取消性；而且它是非正则的，因为逆同态集合是空的，所以 [TwoXY_not_regular] 并不能证明伪逆。树的另一个正则性反驳具有相同的形状——[finset_empty_to_one_not_regular]（Instance/FinSet/Regular.v）再次有一个空的逆同态集合——这并不是通过更仔细地观察就能纠正的巧合。在 [Sets] 上，空的同态集合正是使这种反驳成为可能的原因：[sets_coarsen_not_regular_absurd]（Instance/Sets/Regular.v）展示了一个具有可拥有域和可拥有逆同态集合的箭头，其非正则性可以直接反驳，其正则性正是任意命题的可判定性（[sets_coarsen_regular_iff_dec]）。当那个命题尚未确定时，两个答案都无法被证明，所以上面的退化是关于该设置的事实，而不是这里采取的捷径。
*)

Lemma TwoXY_not_regular : @RegularMorphism _2 TwoX TwoY TwoXY → False.
Proof. intros [g _]; exact (TwoHom_Y_X_absurd g). Qed.

(*
 Both one-sided splittings are ruled out through regularity, rather than by
 repeating the argument: a section or a retraction is regular. 

 --------
 两种单方面分裂都通过正规性被排除，而不是通过重复论证：一个截面或一个收缩是正规的。
*)
Lemma TwoXY_not_retraction : @Retraction _2 TwoX TwoY TwoXY → False.
Proof. intro R; exact (TwoXY_not_regular (regular_of_retraction _ R)). Qed.

Lemma TwoXY_not_section : @Section _2 TwoX TwoY TwoXY → False.
Proof. intro S; exact (TwoXY_not_regular (regular_of_section _ S)). Qed.

(* Packaged: an arrow that is epic, does not split, and is not regular. / 封装：一支史诗级的箭，不会分裂，也不是普通箭。 *)
Definition two_epic_not_regular :
  @Epic _2 TwoX TwoY TwoXY
  * (@Retraction _2 TwoX TwoY TwoXY → False)
  * (@RegularMorphism _2 TwoX TwoY TwoXY → False) :=
  (TwoXY_epic, TwoXY_not_retraction, TwoXY_not_regular).


Require Import Category.Instance.Sets.

(*
 A functor 2 ⟶ Sets is precisely a morphism of Sets; this one picks out the
 unique map (the empty function) from False to True, sending TwoXY there. 

 --------
 一个函子 2 ⟶ 集合 正好是集合的一个态射；这个函子选出了从 False 到 True 的唯一映射（空函数），将 TwoXY 发送到那里。
*)

Program Definition _2_as_Set : _2 ⟶ Sets := {|
  fobj := fun x =>
    match x with
    | TwoX => {| carrier := False |}
    | TwoY => {| carrier := True |}
    end;
  fmap := fun x y f =>
    match x, y with
    | TwoY, TwoY => _
    | _, _       => _
    end
|}.
Next Obligation.
  construct.
  - repeat intro.
    contradiction.
  - equivalence.
Defined.
Next Obligation.
  construct.
  - repeat intro.
    exact True.
  - equivalence.
Defined.
Next Obligation.
  construct; auto.
Defined.
Next Obligation.
  construct; auto.
  - destruct x, y; simpl in *; auto with two_laws.
  - proper.
    destruct x, y; simpl in *; auto with two_laws.
Qed.
Next Obligation.
  destruct x; simpl in *; auto with two_laws.
  contradiction.
Qed.
Next Obligation.
  destruct x, y, z; simpl in *; auto with two_laws.
  contradiction.
Qed.
