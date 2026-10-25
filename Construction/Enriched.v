Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.

Reserved Infix "⟿" (at level 90, right associativity).

(*
   * A category enriched over a monoidal category K (a K-category). 

   --------
   * 一个在单体范畴 K 上加强的范畴（一个 K-范畴）。
*)

(*
 nLab: https://ncatlab.org/nlab/show/enriched+category
 Wikipedia: https://en.wikipedia.org/wiki/Enriched_category

 Given a monoidal category (K, ⨂, I) playing the role of V, a K-enriched
 category replaces each hom-set by a hom-object (x ⟿ y) : K.  Composition
 is the K-morphism ecompose : (y ⟿ z) ⨂ (x ⟿ y) ~> (x ⟿ z) (the codomain
 factor on the left, mirroring ordinary composition order), and the
 identity is the K-morphism eid : I ~> (x ⟿ x) that names the identity
 inside the hom-object.  The three coherence axioms below assert, as
 equalities of K-morphisms, the associativity diagram and the two unit
 diagrams of Kelly's definition, with unit_left, unit_right and
 tensor_assoc supplying the unitors and associator of K.

 Taking K = Set recovers ordinary (locally small) categories: hom-objects
 become hom-sets, eid picks out an element, and ecompose a function.
 Taking K = Ab gives preadditive categories, with bilinear composition —
 made literally computational in Construction/Enriched/Ab.v over
 Instance/Ab/Monoidal.v's ⟨Ab, ⊗, ℤ⟩. 

 --------
 nLab：https://ncatlab.org/nlab/show/enriched+category
 Wikipedia：https://en.wikipedia.org/wiki/Enriched_category

 给定一个单体范畴 (K, ⨂, I) 作为 V 的角色，一个 K-丰富范畴将每个 Hom 集替换为一个 Hom 对象 (x ⟿ y) : K。复合是 K-态射 ecompose : (y ⟿ z) ⨂ (x ⟿ y) ~> (x ⟿ z)（左侧为余域因子，反映普通复合顺序），身份是 K-态射 eid : I ~> (x ⟿ x)，它在 Hom 对象中命名身份。下面的三个相容公理作为 K-态射的等式，断言了 Kelly 定义中的结合性图和两个单位图，其中 unit_left、unit_right 和 tensor_assoc 提供了 K 的单子态射和结合子。取 K = Set 可以恢复普通（局部小）范畴：同态对象变为同态集，eid 选择一个元素，ecompose 是一个函数。取 K = Ab 得到预加性范畴，其复合是双线性的——在 Construction/Enriched/Ab.v 中通过 Instance/Ab/Monoidal.v 的 ⟨Ab, ⊗, ℤ⟩ 实现字面计算。
*)

(*
 Why enrichment, and the bases that tune it

 nLab:      https://ncatlab.org/nlab/show/enriched+category
 Wikipedia: https://en.wikipedia.org/wiki/Enriched_category
 Paper: Eilenberg, Kelly, "Closed Categories", in Proceedings of the
 Conference on Categorical Algebra (La Jolla 1965), Springer
 1966, pp. 421-562
 Book:  Kelly, "Basic Concepts of Enriched Category Theory", London
 Mathematical Society Lecture Note Series 64, Cambridge University
 Press 1982; reprinted Repr. Theory Appl. Categ. No. 10 (2005)
 Paper: Lawvere, "Metric spaces, generalized logic, and closed
 categories", Rend. Sem. Mat. Fis. Milano 43 (1973), 135-166

 Ordinary category theory records between two objects only a SET of
 morphisms, and thereby discards whatever structure that collection
 naturally carries.  Yet what lies between two objects very often carries
 more than a bare set: the linear maps between vector spaces form a
 vector space, the maps between chain complexes a chain complex, the
 arrows between two points of a preorder are one or none — a truth value
 — and the separation between two points of a metric space is a distance.
 Enrichment is the discipline that keeps this structure rather than
 discarding it: the hom-object (x ⟿ y) of the header is asked to live in
 whatever monoidal base K carries the structure at hand, its tensor
 composing hom-objects and its unit naming identities, and a theorem
 proved over K then respects that structure by construction (nLab).

 The definition descends from Eilenberg and Kelly, "Closed Categories"
 (La Jolla 1965, Springer 1966), which introduced the closed and monoidal
 machinery from which the coherence axioms are drawn, and was consolidated
 into the standard reference by Kelly's "Basic Concepts of Enriched
 Category Theory" (1982), the source for the enriched Yoneda lemma and
 weighted limits.  A complete, cocomplete, closed symmetric monoidal base,
 the setting over which the theory is usually developed, is often called a
 cosmos (nLab).

 The base acts as a dial that sets what a hom IS, and each classical
 setting names a familiar theory (nLab): K = Set recovers ordinary locally
 small categories; K = Ab gives preadditive categories with bilinear
 composition, the entry to homological algebra; K = 2, the two truth
 values under meet, gives preorders; K = Cat gives strict 2-categories;
 K = Vect and K = Top give linear and topological categories; K = Ch, the
 chain complexes, gives the dg-categories behind derived and triangulated
 categories; and K = sSet, the simplicial sets, gives the simplicial
 categories that serve as a model for (∞,1)-categories.  Lawvere observed
 that a category enriched over the non-negative extended reals ordered by
 ≥ under addition is exactly a generalized metric space: the hom-object is
 a distance, [ecompose] is the triangle inequality, and [eid] records that
 the self-distance is zero (Lawvere 1973).  This is the "generalized
 logic" reading, under which preorder- and quantale-enriched categories
 become systems of generalized truth values.  Any closed monoidal base is
 moreover enriched in itself through its internal hom, as
 Structure/Closed.v records.

 Enrichment is not the same as an internal category: an enriched
 hom-object lives IN K, one object per pair of external objects, whereas
 an internal category packs all objects and morphisms into two K-objects
 with structure maps, the two agreeing in good cases and diverging in
 general (nLab).

 Two of the dial settings are made literally computational here.
 [Category_is_Enriched_over_Set] is a definitional round trip over
 [Sets_Product_Monoidal]: a Sets-enriched category unfolds to an ordinary
 [Category] and back, [eid] at the unit point supplying the identity and
 [ecompose] on a pair (f, g) the composite, so enrichment over Set adds
 nothing, as it must; [Functor_is_Enriched_over_Set] does the same for
 [EnrichedFunctor].  Construction/Enriched/Two.v sharpens the slogan that
 a preorder is a category with at most one arrow per hom: a hom-object is a
 truth value, [eid] forces the diagonal (reflexivity), [ecompose] under
 meet forces transitivity, and the three coherence laws hold on their own
 because the base is thin, carrying at most one parallel arrow, so any two
 coincide ([Enriched_Two_preorder], [EnrichedFunctor_Two_monotone], both
 directions).  The surrounding structure sits alongside: the enriched
 natural transformations [EnrichedTransform]
 (Construction/Enriched/Natural.v) and their Sets-level recovery
 [EnrichedTransform_is_Transform] (Construction/Enriched/Sets.v), the
 identity and composite functors of Construction/Enriched/Compose.v, the
 ordinary functor category of Construction/Enriched/Fun.v, and the
 hand-built CMon-enriched example of Structure/Preadditive.v (with
 the standalone Ab-enriched class in Structure/AbCategory.v — proved
 equivalent to enrichment over ⟨Ab, ⊗, ℤ⟩ by Construction/Enriched/Ab.v's
 [Enriched_Ab_iff_AbEnriched] — and
 Structure/Additive.v bundling it with a zero object and
 biproducts); Instance/Poset.v reads posets as truth-value
 enrichment. 

 --------
 为什么要做丰富化，以及调节它的基

 nLab:       https://ncatlab.org/nlab/show/enriched+category
 维基百科:  https://en.wikipedia.org/wiki/Enriched_category
 论文: Eilenberg, Kelly, “封闭范畴”，载于 La Jolla 1965 年范畴代数会议论文集，Springer 1966 年，第 421-562 页
 书籍: Kelly, “丰富范畴理论的基本概念”，伦敦数学学会讲义系列 64，剑桥大学出版社 1982 年；重印 Repr. Theory Appl. Categ. 第 10 号 (2005)
 论文: Lawvere, “度量空间、广义逻辑与封闭范畴”，Rend. Sem. Mat. Fis. Milano 43 (1973), 135-166普通的范畴论只在两个对象之间记录一个集合（SET） 的态射，因此丢弃了该集合自然携带的任何结构。然而，两个对象之间的关系通常不仅仅是一个简单的集合：向量空间之间的线性映射本身形成一个向量空间，链复形之间的映射形成一个链复形，前序集合中两个点之间的箭头是有或者没有——一个真值——而度量空间中两个点之间的分离则是一个距离。增广是保持这一结构而不是丢弃它的学科：标题的同态对象 (x ⟿ y) 被要求存在于承载所需结构的任何幺半群基 K 中，其张量将同态对象组合，其单位命名恒等式，并且在 K 上证明的一个定理则通过构造尊重该结构（nLab）。这个定义源自 Eilenberg 和 Kelly 的《闭范畴》(La Jolla 1965, Springer 1966)，该书引入了闭合和单体结构的机制，从中得出了相干公理，并通过 Kelly 的《富范畴论的基本概念》(1982) 得到了巩固，该书是富化 Yoneda 引理和加权极限的来源。一个完备、余完备、闭合的对称单体基，即理论通常发展的背景，常被称为宇宙(nLab)。基底充当一个旋钮，用于设置一个 hom 是什么，每个经典设置都给出了一个熟悉的理论名称（nLab）：K = Set 恢复普通的局部小范畴；K = Ab 给出具有双线性组合的前加性范畴，这是进入同调代数的入口；K = 2，在会聚下的两个真值，给出预序；K = Cat 给出严格的 2-范畴；K = Vect 和 K = Top 给出线性和拓扑范畴；K = Ch，即链复形，给出导出范畴和三角范畴背后的 dg-范畴；而 K = sSet，即单纯形集，给出作为 (∞,1)-范畴模型的单纯形范畴。劳维尔观察到，一个在按加法下的非负扩展实数上富化的范畴，恰好是一个广义度量空间：Hom对象是距离，[ecompose]是三角不等式，而[eid]记录了自身距离为零（劳维尔 1973）。这是“广义逻辑”的解读，在这种解读下，预序和量化器富化的范畴变成广义真值系统。任何闭单体基还可以通过其内部Hom在自身上富化，正如Structure/Closed.v所记录的那样。丰富化与内部范畴不同：一个丰富化的同对象存在于 K 中，每对外部对象对应一个对象，而内部范畴将所有对象和态射打包到两个 K-对象中，并带有结构映射，这两个在好的情况下是一致的，一般情况下则可能不同（nLab）。这里有两个拨号设置是字面上进行计算的。[Category_is_Enriched_over_Set] 是一个定义性的往返操作，对应于
 [Sets_Product_Monoidal]：一个增强集合的范畴展开成普通范畴 [Category] 并返回，[eid] 在单位点提供恒等映射，而
 [ecompose] 对于一对 (f, g) 提供复合，因此在 Set 上的增强没有增加任何内容，这是理所当然的；[Functor_is_Enriched_over_Set] 对于
 [EnrichedFunctor] 也是一样。Construction/Enriched/Two.v 强化了那个口号：一个预序是每个 Hom 至多有一个箭头的范畴：一个 Hom 对象是一个真值，[eid] 强制对角线（自反性），[ecompose] 在取交下强制传递性，并且三个相容性定律自动成立，因为基础是单薄的，最多携带一个平行箭头，因此任何两个箭头都重合（[Enriched_Two_preorder]、[EnrichedFunctor_Two_monotone]，两者方向）。周围的结构包括：丰富的自然变换 [EnrichedTransform]（Construction/Enriched/Natural.v）及其集合级的恢复 [EnrichedTransform_is_Transform]（Construction/Enriched/Sets.v），Construction/Enriched/Compose.v 中的恒等和复合函子，Construction/Enriched/Fun.v 中的普通函子范畴，以及 Structure/Preadditive.v 中手工构建的 CMon 丰富示例（以及 Structure/AbCategory.v 中独立的 Ab-enriched 类——由 Construction/Enriched/Ab.v 的 [Enriched_Ab_iff_AbEnriched] 证明等价于 ⟨Ab, ⊗, ℤ⟩ 上的丰富——以及 Structure/Additive.v 将其与零对象和双积绑定）；Instance/Poset.v 将偏序集解释为真值丰富。
*)

Class Enriched (K : Category) `{@Monoidal K} := {
  eobj : Type;

  ehom : eobj → eobj → K where "a ⟿ b" := (ehom a b);

  eid {x} : I ~{K}~> (x ⟿ x);                                  (* identity j_x / 身份 j_x *)
  ecompose {x y z} : (y ⟿ z) ⨂ (x ⟿ y) ~{K}~> (x ⟿ z);        (* composition / 作文 *)

  (*
 left unit: ecompose after eid on the codomain factor is unit_left 

 --------
 左单位：在上的余域因子上的 eid 之后分解为 unit_left
*)
  eid_left  {x y} :
    ecompose ∘ eid ⨂ id << I ⨂ (x ⟿ y) ~~> (x ⟿ y) >> unit_left;
  (*
 right unit: ecompose after eid on the domain factor is unit_right 

 --------
 右单元：在域因子上的eid之后分解为 unit_right
*)
  eid_right {x y} :
    ecompose ∘ id ⨂ eid << (x ⟿ y) ⨂ I ~~> (x ⟿ y) >> unit_right;

  (*
 associativity: the two composition paths agree up to tensor_assoc 

 --------
 结合性：两个组合路径在张量结合律下是一致的
*)
  ecompose_assoc {x y z w} :
    ecompose ∘ ecompose ⨂ id
      << ((z ⟿ w) ⨂ (y ⟿ z)) ⨂ (x ⟿ y) ~~> (x ⟿ w) >>
    ecompose ∘ id ⨂ ecompose ∘ tensor_assoc
}.

Infix "⟿" := ehom (at level 90, right associativity).

Coercion eobj : Enriched >-> Sortclass.

(** A K-enriched functor between K-categories. / 在 K-范畴之间的 K-增强函子。 *)

(*
 nLab: https://ncatlab.org/nlab/show/enriched+functor
 Wikipedia: https://en.wikipedia.org/wiki/Enriched_category#Enriched_functors

 An object map efobj together with hom-object maps efmap : (x ⟿ y) ~>
 (efobj x ⟿ efobj y) in K, commuting with eid and ecompose. 

 --------
 nLab:  https://ncatlab.org/nlab/show/enriched+functor 
 维基百科:  https://en.wikipedia.org/wiki/Enriched_category#Enriched_functors 

 一个对象映射 efobj 以及同态对象映射 efmap : (x ⟿ y) ~>
 (efobj x ⟿ efobj y) 在 K 中，与 eid 和 ecompose 对应。
*)

Class EnrichedFunctor
      (K : Category) `{@Monoidal K}
      (C : Enriched K) (D : Enriched K) := {
  efobj : C → D;
  efmap {x y} : (x ⟿ y) ~{K}~> (efobj x ⟿ efobj y);

  (* preserves identity: efmap takes eid to eid / 保持身份：efmap 将 eid 映射到 eid *)
  efmap_id : ∀ x,
    efmap ∘ eid << I ~~> (efobj x ⟿ efobj x) >> eid;
  (* preserves composition: efmap commutes with ecompose / 保持组合：efmap 与 ecompose 交换 *)
  efmap_comp : ∀ x y z,
    ecompose ∘ efmap ⨂ efmap
      << (y ⟿ z) ⨂ (x ⟿ y) ~~> (efobj x ⟿ efobj z) >>
    efmap ∘ ecompose
}.

Require Import Category.Instance.Sets.

Theorem Category_is_Enriched_over_Set : Enriched Sets ↔ Category.
Proof.
  split; intros.
  - unshelve refine
      {| obj     := eobj
       ; hom     := @ehom _ _ X
       ; homset  := @ehom _ _ X
       ; id      := fun x => @eid _ _ X x ttt
       ; compose := fun x y z f g => @ecompose _ _ X x y z (f, g) |}.
    + intros.
      proper.
      destruct X.
      simpl in *.
      destruct (ecompose0 x y z).
      simpl in *.
      now apply proper_morphism; simpl; auto.
    + intros.
      destruct X.
      simpl in *.
      now sapply (eid_left0 x y (ttt, f)).
    + intros.
      destruct X.
      simpl in *.
      now sapply (eid_right0 x y (f, ttt)).
    + intros.
      destruct X.
      simpl in *.
      symmetry.
      now sapply (ecompose_assoc0 x y z w ((f, g), h)).
    + intros.
      destruct X.
      simpl in *.
      now sapply (ecompose_assoc0 x y z w ((f, g), h)).
  - unshelve refine
      (@Build_Enriched Sets Sets_Product_Monoidal
          obj
          (fun x y : X => {| carrier := x ~> y |})
          (fun x => {| morphism := fun _ => id[x] |})
          (fun x y z => {| morphism := fun p => fst p ∘ snd p |})
          _ _ _).
    + now apply homset.
    + now proper.
    + proper; simpl.
      apply compose_respects;
      now match goal with
        [ H : _ ≈ _ |- _ ] => apply H
      end.
    + now simpl; intros; cat.
    + now simpl; intros; cat.
    + now simpl; intros; cat.
Defined.

Theorem Functor_is_Enriched_over_Set (C D : Category) :
  EnrichedFunctor
    Sets
    (snd Category_is_Enriched_over_Set C)
    (snd Category_is_Enriched_over_Set D)
    ↔ (C ⟶ D).
Proof.
  split; intros.
  - destruct X; simpl in *.
    construct.
    + now apply efobj0.
    + now apply efmap0.
    + proper.
      now apply efmap0.
    + now apply efmap_id0.
    + simpl in *.
      now srewrite (efmap_comp0 x y z (f, g)).
  - destruct X; simpl in *.
    construct.
    + now apply fobj.
    + construct.
      * now apply fmap.
      * proper.
        now apply fmap_respects.
    + now apply fmap_id.
    + simpl.
      symmetry.
      now apply fmap_comp.
Defined.
