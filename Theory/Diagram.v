From Coq Require Import Lia.
Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.PreorderReflection.

Generalizable All Variables.

(** * Diagrams and commutativity / * 图表与可换性 *)

(*
nLab: https://ncatlab.org/nlab/show/commutative+diagram

   A DIAGRAM in a category [C] over a quiver (directed multigraph) [G] is a
   labelling of the vertices of [G] by objects of [C] and of its edges by
   morphisms of [C], respecting sources and targets.  That is exactly a quiver
   homomorphism [G ⇨ QuiverOfCat C] (Construction/Free/Quiver.v, which
   declares both [QuiverHomomorphism] and [Quiver]), which is how [Diagram] is
   defined below.

   A PATH in [G] is a finite composable chain of edges, i.e. an inhabitant of
   [tlist edges x y] (Lib/TList.v); it is also, definitionally, a morphism
   [x ~> y] of the free category [FreeOnQuiver G] (Construction/Free/Quiver.v).
   [dpath] denotes such a path by composing its edge labels in [C], and
   [Commutative D] asserts that ANY two paths sharing a source and a target
   denote [≈]-equal morphisms.  The quantification is over all pairs of
   vertices and all pairs of parallel paths of arbitrary length; no diagram
   shape is privileged.

   The bridge to the free category runs both ways.  [FunctorOfDiagram] sends a
   diagram to the functor [FreeOnQuiver G ⟶ C] extending it (this is
   Quiver.v's [InducedFunctor]), [DiagramOfFunctor] restricts a functor along
   the unit [UnitQuiverCatAdjunction] back to a diagram, and the two round
   trips are proved: [functor_of_diagram_of_functor] in the hom-setoid of
   StrictCat and [diagram_of_functor_of_diagram] in [QuiverCategory].  Under
   that correspondence [Commutative D] is precisely [CommutativeShape] of the
   extending functor, i.e. the functor sends every parallel pair of the free
   category to a single morphism ([commutative_iff_shape],
   [shape_iff_commutative]).

   SCOPE of “correspondence”: both directions are maps of the underlying
   types, and both round trips are proved pointwise.  Respectfulness of the
   two maps for the two equivalences, and naturality in [G] and [C], are NOT
   established here, so nothing below asserts an isomorphism of hom-setoids.
   What IS proved is that the two maps are mutually inverse up to [≈],
   pointwise; that is weaker than a bijection of the underlying types, since
   the round trips are up to [≈] rather than up to [=], and weaker than a
   bijection of the setoid quotients, since without respectfulness the maps do
   not descend to them.
   The universal property that would package them is already in the tree --
   Construction/Free/Quiver.v's [UniversalArrowQuiverCat] and its
   [FreeForgetfulAdjunction].  The two round trips below are NOT derived from
   it: each is proved directly by induction.  They carry the same content its
   existence and uniqueness halves would give, but that agreement is not
   itself proved here.

   Instances: the walking square and the walking triangle are built as quivers
   here, and for each the general predicate is proved EQUIVALENT to the single
   familiar two-composite equation ([square_commutative_iff],
   [triangle_commutative_iff]).  The naturality square of a natural
   transformation is such a commuting square
   ([naturality_square_commutative_iff]).  A faithful functor reflects
   commutativity ([faithful_reflects_commutative]) and every functor preserves
   it ([functor_preserves_commutative]); both also hold in the
   diagram-as-functor formulation, for an arbitrary indexing category
   ([faithful_reflects_commutative_shape],
   [functor_preserves_commutative_shape]).

--------
nLab: https://ncatlab.org/nlab/show/commutative+diagram

   范畴 [C] 中形状为 quiver [G] 的图 (diagram)：顶点映到对象，边映到端点标签之间的态射。
   交换性说：沿任意两路径的复合在 ≈ 下一致。本文件给出图的数据与交换条件；与极限/余极限
   的连接见 Structure/Limit 与相关构造。长历史短文若仍为英文属后续波次。
*)

(*
Diagrams and commutation: sources and in-tree connections

   Book:  Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
          Springer GTM 5, 1998, §I.1 “Axioms for Categories”, printed p. 8
          (PDF p. 18), the third numbered definition of that section.
   Book:  Fong and Spivak, “Seven Sketches in Compositionality”, CUP 2019,
          §3.3.4 Definition 3.51, printed p. 95 (PDF p. 107).
   Book:  Riehl, “Category Theory in Context”, 2nd ed., §1.1, printed
          pp. 3-4 (PDF pp. 23-24); §1.6, printed p. 39 (PDF p. 59);
          Lemma 1.6.20, printed p. 46 (PDF p. 66).
   nLab:  https://ncatlab.org/nlab/show/commutative+diagram

   The three books are cited BY LOCATION only.  Their printed text was not
   consulted while writing this file, so nothing here quotes or paraphrases
   them; the locations record where each result is stated, and the Coq
   statements below stand on their own.  The attributions follow the issue
   that requested this file (jwiegley/category-theory#216), which supplies
   those locations.

   Why this file exists.  Commutativity is the working language of category
   theory, and the reusable in-tree statements of it each fix a single FIGURE
   with a fixed number of sides: [Construction/Sq.v] fixes a square
   ([dsq := fun a b c d h u v k => k ∘ u ≈ v ∘ h]), [Structure/Cone.v]'s
   [cone_coherence] fixes the apex triangle of a cone leg, and
   [Theory/Morphisms/Stability.v]'s [is_pullback_commutes] fixes the
   pullback square.  Each of the three ranges over arbitrary MORPHISMS -- so
   its sides may themselves be long composites -- but each pins the figure,
   and none quantifies over PAIRS OF PARALLEL PATHS in a shape.  That last
   quantification is what [Commutative] adds, and it is what makes the
   predicate independent of any drawing.  Issue #216's coverage pass reports
   that elsewhere in the tree commutativity appears only as an ad hoc [≈]
   equation between two named composites; that survey is the issue's, and is
   not re-verified here.

   Relation to the solver.  [Solver/Expr.v] reifies composite morphisms as
   an untyped term grammar [Term ::= Ident | Morph nat | Comp Term Term],
   and its own header comment (Solver/Expr.v) records that this grammar
   “is exactly a term of the free category on the quiver whose edges are the
   variables [arrs]”.  The typed in-tree counterpart of that grammar is
   [Mor ::= Ident | Morph edge | Comp] of Construction/Free/Quiver.v,
   normalised to a path by [morDA].  [dterm] below interprets [Mor] in
   [C] with the same reading of [Comp] that Solver/Denote.v uses (there,
   “[Comp f g] denotes [f ∘ g]”), and [dterm_dpath] proves that interpreting a
   term agrees with denoting its normal-form path.  [commutative_dterm] is the
   consequence a solver would want: over a commutative diagram, ALL parallel
   terms are interchangeable, not merely the ones a normaliser can identify.

   The Seven Sketches footnote packaging -- that a diagram commutes exactly
   when it factors through the preorder reflection of its indexing category --
   is proved below in both directions ([commutative_shape_factors],
   [factors_commutative_shape], [factors_commutative_shape'],
   [commutative_factors]) and packaged as the single biconditional
   [commutes_iff_factors], over Construction/PreorderReflection.v.  The
   forward factorization is moreover an equality of FUNCTORS in StrictCat's
   hom-setoid ([shape_factor_functor]), not merely a pointwise agreement.
   That file needed no new machinery: Construction/Quotient.v already
   quotients a category by a hom-congruence, and the preorder reflection is
   that quotient at the total congruence; what it adds is the universal
   property [ThinLift], which makes it THE universal thin quotient rather than
   a quotient that happens to be thin.

   SCOPE.  What Construction/PreorderReflection.v supplies is the construction
   and its thinness only.  The remaining parts of
   jwiegley/category-theory#803 -- the truncated object preorder, functoriality
   of the reflection on [Cat], and the adjunction with the inclusion of
   preorders -- are NOT built, and nothing below depends on them.

--------
图表与换向：电源及树内连接

书籍：Mac Lane，《为工作中的数学家准备的范畴论》，第2版，Springer GTM 5，1998年，§I.1 “范畴的公理”，印刷版第8页（PDF第18页），本节的第三个编号定义。
书籍：Fong 和 Spivak，《组合性中的七个草图》，CUP 2019年，§3.3.4 定义3.51，印刷版第95页（PDF第107页）。
书籍：Riehl，《上下文中的范畴论》，第2版，§1.1，印刷版第3-4页（PDF第23-24页）；§1.6，印刷版第39页（PDF第59页）；引理1.6.20，印刷版第46页（PDF第66页）。
nLab: https://ncatlab.org/nlab/show/commutative+diagram

这三本书仅按位置引用。在撰写此文件时并未查阅它们的印刷文本，因此这里没有引用或改述它们；这些位置记录了每个结果陈述的地方，而下面的 Coq 声明独立存在。归属信息遵循提出此文件的议题（jwiegley/category-theory#216），该议题提供了这些位置。

为什么这个文件存在。交换性是范畴论的工作语言，它的每个可重用树内语句都固定一个具有固定边数的图形：[Construction/Sq.v]固定一个正方形（[dsq := fun a b c d h u v k => k ∘ u ≈ v ∘ h]），[Structure/Cone.v]的[cone_coherence]固定一个锥形腿的顶点三角形，而[Theory/Morphisms/Stability.v]的[is_pullback_commutes]固定拉回正方形。三个范围中的每一个都覆盖任意的态射——因此它的边本身可能是长组合——但每一个都固定了图形，并且没有一个对图形中的平行路径对进行量化。最后那种量化是[Commutative]所增加的，并且它令该谓词独立于任何绘图。问题 #216 的覆盖检查报告中，在树的其他地方，交换性仅作为两个命名组合之间的特设 [≈] 方程出现；该调查属于该问题的范围，在这里不再重新验证。

与求解器的关系。[Solver/Expr.v] 将复合态射具象化为无类型项文法 [Term ::= Ident | Morph nat | Comp Term Term]，而其自身的头部注释（Solver/Expr.v）记录了这个文法“正好是自由范畴上四元图（其边为变量 [arrs]）的一项”。该文法的类型化树内对应物是 Construction/Free/Quiver.v 中的 [Mor ::= Ident | Morph edge | Comp]，通过 [morDA] 被归一化为一条路径。下面的 [dterm] 在 [C] 中解释 [Mor]，使用与 Solver/Denote.v 相同的 [Comp] 读法（在那里，“[Comp f g] 表示 [f ∘ g]”），并且 [dterm_dpath] 证明了解释一个项与表示其归一化路径是一致的。[commutative_dterm] 是求解器想要的结论：在一个交换图上，所有平行项都是可互换的，而不仅仅是归一化器能识别的那些。

《七个草图》脚注打包——当一个图表通过其索引范畴的预序反射进行分解时精确交换——在下面两个方向上都得到了证明（[commutative_shape_factors], [factors_commutative_shape], [factors_commutative_shape'], [commutative_factors]），并作为单个双条件 [commutes_iff_factors] 打包，在 Construction/PreorderReflection.v 中。同时，正向分解在 StrictCat 的同态集合体中是函子等式（[shape_factor_functor]），而不仅仅是逐点一致。该文件不需要新的机制：Construction/Quotient.v 已经通过同态合同对一个范畴进行商化，而预序反射就是那在总合同下的商；它新增的是普适性性质 [ThinLift]，这使它成为普适薄商，而不是恰好是薄的商。

范围。Construction/PreorderReflection.v 提供的仅仅是构造及其稀疏性。jwiegley/category-theory#803 的其余部分——截断对象的预序、[Cat] 上反射的函子性，以及与预序包含的伴随关系——尚未构建，并且下面的内容不依赖于它们。
*)

#[local] Existing Instance edgeset.

(** ** Diagrams, path denotation, and the commutativity predicate / ** 图表、路径表示法和交换性谓词 *)

Section DiagramCore.

Context {G : Quiver}.
Context {C : Category}.

(*
A diagram in [C] of shape [G]: vertices go to objects, edges to morphisms
   between the labels of their endpoints.  Source and target preservation is
   automatic because a [Quiver]'s edges are indexed by their endpoints.

--------
[C] 中形状为 [G] 的图：顶点对应对象，边对应其端点标签之间的态射。源和目标的保持是自动的，因为 [Quiver] 的边是由其端点索引的。
*)
(*
   【Diagram 定义展开】/ Definition walkthrough

   1) 这是什么 / What this is
      图 = 箭图同态 G → QuiverOfCat C：顶点→对象、边→态射（端点已索引，源靶自动保）。
      Diagram = quiver homomorphism into the underlying quiver of C.
      与「函子 J ⟶ C」：自由范畴 FreeOnQuiver G 上的函子与交换图互通（下文桥）。
      Bridges to functors on FreeOnQuiver; commutativity = path denotations agree.

   2) 邻近 / Nearby
      dedge / dpath —— 边标签与路径复合
      Commutative —— 同端点路径表示相等
      FunctorOfDiagram / DiagramOfFunctor —— 与函子互转

   阅读：Quiver → Diagram → dpath → Commutative → Free 桥 → 走路方形等例子。
   Read: Quiver → Diagram → paths → commutativity → free bridge → walking shapes.
*)

Definition Diagram : Type := QuiverHomomorphism G (QuiverOfCat C).

Context (D : Diagram).

(*
The morphism labelling an edge.  [fnodes] is a coercion, so [D x] is the
   object labelling the vertex [x].

--------
标记一条边的态射。[fnodes] 是一个强制转换，因此 [D x] 是标记顶点 [x] 的对象。
*)
Definition dedge {x y : G} (e : edges x y) : D x ~{C}~> D y :=
  @fedgemap G (QuiverOfCat C) D x y e.

(*
Denotation of a path: compose the edge labels along it.  The empty path
   denotes the identity; [e ::: p] denotes [dpath p ∘ dedge e], the edge first
   because a path runs source-to-target while [∘] is written right-to-left.

--------
后后后后后创造有利于拥护后ô加大力度淌后后 页 、-
được 表示身份;已为喽啰嘞的Z语。
提供咨询意见, * 因为一个路径运行源审查报告目标, 而享有同等权利 。
*)
Fixpoint dpath {x y : G} (p : tlist edges x y) : D x ~{C}~> D y :=
  match p in tlist' _ i return D i ~{C}~> D y with
  | tnil            => id
  | tcons _ e rest  => dpath rest ∘ dedge e
  end.

(* Path denotation turns concatenation into composition. / 路径表示将连接转变为组合。 *)
Lemma dpath_app {x y z : G} (p : tlist edges x y) (q : tlist edges y z) :
  dpath (p +++ q) ≈ dpath q ∘ dpath p.
Proof.
  induction p as [ | i m e p IH ].
  - rewrite tlist_app_tnil_l; simpl.
    now rewrite id_right.
  - rewrite <- tlist_app_comm_cons; simpl.
    rewrite IH.
    now rewrite comp_assoc.
Qed.

(*
Mac Lane's condition: any two paths with the same source and the same
   target have the same composite.  Both vertices and both paths are
   universally quantified, and paths carry no length bound, so this covers
   every diagram shape at once rather than a fixed square or triangle.

   The EMPTY path counts as a path, so taking [q := tnil] forces every
   endo-path to denote [id]: over a shape with a loop [e : x -> x],
   [Commutative] therefore requires [dedge D e ≈ id], and a diagram drawing a
   non-identity endomorphism is not [Commutative].  That is the intended
   reading and it matches the functor formulation, whose quantification over
   parallel pairs likewise includes the identity; [commutative_iff_shape]
   proves the two agree.

   That consequence is not left as prose: [loop_commutative_iff] below proves
   it in both directions over the walking loop, and
   Theory/Diagram/Examples.v exhibits a concrete diagram that draws a
   non-identity endomorphism and is therefore not [Commutative].

   CARE IS NEEDED STATING WHAT THIS SEPARATES.  It is NOT that the
   figure-fixing statements cannot express a loop condition: Construction/
   Sq.v's [dsq a b c d h u v k := k ∘ u ≈ v ∘ h] quantifies over arbitrary
   OBJECTS, so all four corners may be instantiated to one object [X], making
   [h : X ~> X] an endo-path; [dsq X X X X e id id id] then reduces to
   [id ∘ id ≈ id ∘ e], which is exactly [e ≈ id].  The real distinction is
   about who supplies the condition.  [Commutative] FORCES [e ≈ id] from the
   SHAPE alone, with no choice of instantiation: the empty path is always
   available as a competitor to any endo-path.  [dsq] can be INSTANTIATED to
   state that equation but never forces it, and the degenerate instantiation
   is not what any of its in-tree uses does.  For [cone_coherence] and
   [is_pullback_commutes] the point is different again -- each is a FIELD of a
   record, so it cannot be freely instantiated at all.

--------
Mac Lane 的条件：任何具有相同起点和相同终点的两条路径，其复合结果相同。顶点和路径都是全称量化的，并且路径没有长度限制，因此这涵盖了每种图形形状，而不仅仅是固定的方形或三角形。

空路径被计为一条路径，因此采取 [q := tnil] 会迫使每个自同态路径表示 [id]：在具有 [e : x -> x] 循环的形状上，[Commutative] 因此需要 [dedge D e ≈ id]，而绘制非恒等自同态的图不是 [Commutative]。这是预期的解释，并且它与函子表述相符，后者对平行对的量化同样包括恒等；[commutative_iff_shape] 证明两者一致。

这个结论不是以散文的形式留下的：下面的 [loop_commutative_iff] 在行走循环上从两个方向证明了它，并且 Theory/Diagram/Examples.v 展示了一个具体的图，该图绘制了一个非恒等自同态，因此不是 [Commutative]。

在说明这些内容区分点时需要小心。并不是说那些固定数值的语句不能表达循环条件：Construction/Sq.v 的 [dsq a b c d h u v k := k ∘ u ≈ v ∘ h] 对任意对象进行量化，因此四个角都可能实例化为同一个对象 [X]，使得 [h : X ~> X] 成为一个内路径；[dsq X X X X e id id id] 然后简化为 [id ∘ id ≈ id ∘ e]，而这正是 [e ≈ id]。真正的区别在于由谁来提供条件。[Commutative] 完全依赖 SHAPE 强制 [e ≈ id]，无需选择实例化：空路径始终可用，作为任何内路径的竞争者。[dsq] 可以实例化来说明那个方程，但永远不会强制它，而且退化的实例化并不是其树内用法所做的任何事情。对于 [cone_coherence] 和 [is_pullback_commutes]，情况又不同 —— 它们各自是记录的一个字段，所以完全不能自由实例化。
*)
Definition Commutative : Type :=
  ∀ (x y : G) (p q : tlist edges x y), dpath p ≈ dpath q.

End DiagramCore.

Arguments Diagram : clear implicits.
Arguments dedge {G C} D {x y} e.
Arguments dpath {G C} D {x y} p.
Arguments Commutative {G C} D.

(** ** The diagram-as-functor form of the predicate / ** 谓词的图作为函子形式 *)

(*
The Seven Sketches formulation: a diagram is a functor out of an indexing
   category, and it commutes when every parallel pair of the indexing category
   has a single image.  For an indexing category that is free on a quiver this
   is the same condition as [Commutative], proved below.

--------
七个草图的表述：图是一个从索引范畴出的函子，当索引范畴的每一对平行箭头都有唯一像时，它是可交换的。对于一个在络图上自由的索引范畴，这与下面证明的 [Commutative] 条件相同。
*)
Definition CommutativeShape {J C : Category} (F : J ⟶ C) : Type :=
  ∀ (x y : J) (f g : x ~{J}~> y), fmap[F] f ≈ fmap[F] g.

(** ** The bridge to the free category / ** 通往自由范畴的桥 *)

Section DiagramBridge.

Context {G : Quiver}.
Context {C : Category}.

(*
A diagram extends to a functor on the free category: this is Quiver.v's
   [InducedFunctor], named here for the correspondence.

--------
一个图表扩展到自由范畴上的函子：这是 Quiver.v 的 [InducedFunctor]，在此因其对应关系而命名。
*)
Definition FunctorOfDiagram (D : Diagram G C) : FreeOnQuiver G ⟶ C :=
  InducedFunctor G D.

(*
... and a functor on the free category restricts to a diagram, by
   composing with the unit of the free/forgetful adjunction, which sends an
   edge to the one-edge path.

--------
... 并且一个自由范畴上的函子通过与自由/遗忘伴随的幺元组合，限制为一个图，该幺元将一条边映射为单边路径。
*)
Definition DiagramOfFunctor (F : FreeOnQuiver G ⟶ C) : Diagram G C :=
  QuiverComp (UnitQuiverCatAdjunction G)
             (QuiverHomomorphismOfFunctor (FreeOnQuiver G) C F).

(* Path denotation is the extending functor's action on morphisms. / 路径表示是扩展函子的在态射上的作用。 *)
Lemma dpath_fmap (D : Diagram G C) {x y : G} (p : tlist edges x y) :
  dpath D p ≈ fmap[FunctorOfDiagram D] p.
Proof.
  induction p as [ | i m e p IH ]; simpl; [ reflexivity | ].
  now rewrite IH.
Qed.

(*
Denoting a path in the restricted diagram is applying the original functor
   to that path, viewed as a morphism of the free category.  Proved for paths
   of arbitrary length, by induction.

--------
在受限图中表示一条路径是将原始函子应用于该路径，将其视为自由范畴的一个态射。通过归纳法证明任意长度的路径。
*)
Lemma dpath_of_functor (F : FreeOnQuiver G ⟶ C) {x y : G} (p : tlist edges x y) :
  dpath (DiagramOfFunctor F) p ≈ fmap[F] p.
Proof.
  induction p as [ | i m e p IH ]; simpl.
  - change (@tnil _ _ y) with (@id (FreeOnQuiver G) y).
    now rewrite fmap_id.
  - (*
[≈], not [=]: [tlist_app_cons] (Lib/TList.v) is proved by
       [destruct], so the two sides are not the same term and the
       Functor/Bifunctor.v exception does not apply.  This mirrors the
       [RW] step of Construction/Free/Quiver.v.

--------
[≈]，而不是 [=]：[tlist_app_cons]（Lib/TList.v）由 [destruct] 证明，所以两边不是相同的项，Functor/Bifunctor.v 异常不适用。这与 Construction/Free/Quiver.v 的 [RW] 步骤相呼应。
*)
    assert (Hsplit : @equiv _ (@homset (FreeOnQuiver G) i y) (e ::: p)
                       (@compose (FreeOnQuiver G) _ _ _ p (tlist_singleton e)))
      by (unfold tlist_singleton; simpl; now rewrite <- tlist_app_cons).
    rewrite Hsplit, fmap_comp.
    apply compose_respects; [ exact IH | reflexivity ].
Qed.

(*
Round trip one: extending the restriction of a functor gives that functor
   back.  The equivalence used is [Functor_StrictEq_Setoid]
   (Theory/Functor.v), which is exactly the hom-setoid of the strict
   category of categories (Instance/StrictCat.v): objects agree on the nose
   -- here by [eq_refl], since the two functors have the same object map by
   definition -- and the transported morphism maps agree up to [≈].

--------
往返一：扩展函子限制会给出该函子本身。使用的等价是 [Functor_StrictEq_Setoid]（Theory/Functor.v），它正好是严格范畴类的同态集合（Instance/StrictCat.v）：对象完全一致——这里通过 [eq_refl]，因为根据定义两个函子的对象映射相同——且传输后的态射映射在 [≈] 下一致。
*)
Lemma functor_of_diagram_of_functor (F : FreeOnQuiver G ⟶ C) :
  @equiv _ (@Functor_StrictEq_Setoid (FreeOnQuiver G) C)
         (FunctorOfDiagram (DiagramOfFunctor F)) F.
Proof.
  exists (fun _ => eq_refl).
  intros x y p.
  change (fmap[FunctorOfDiagram (DiagramOfFunctor F)] p ≈ fmap[F] p).
  transitivity (dpath (DiagramOfFunctor F) p);
    [ symmetry; apply dpath_fmap | apply dpath_of_functor ].
Qed.

(*
Round trip two: restricting the extension of a diagram gives that diagram
   back, as morphisms of [QuiverCategory].  The vertex maps agree definitionally
   ([eq_refl]); on edges the round trip inserts one identity, removed by
   [id_left].

--------
往返二：限制一个图的扩展会得到该图本身，作为 [QuiverCategory] 的态射。顶点映射在定义上是一致的（[eq_refl]）；在边上，往返会插入一个恒等映射，该恒等映射由 [id_left] 移除。
*)
Lemma diagram_of_functor_of_diagram (D : Diagram G C) :
  DiagramOfFunctor (FunctorOfDiagram D) ≈[QuiverCategory] D.
Proof.
  exists (fun _ => eq_refl).
  intros x y e; simpl.
  now rewrite id_left.
Qed.

(*
Commutativity of a diagram is exactly the statement that its extending
   functor identifies parallel morphisms of the free category.  This is the
   agreement of Mac Lane's quiver-and-paths formulation with the Seven
   Sketches diagram-as-functor formulation: morphisms of [FreeOnQuiver G] ARE
   the paths of [G], so the two quantifications range over the same pairs.

--------
图的交换性恰恰是其扩展函子识别自由范畴中平行态射的陈述。这是 Mac Lane 的箭图与路径表述与《七个素描》中图作为函子表述的一致性：[FreeOnQuiver G] 的态射就是 [G] 的路径，因此这两个量化范围是相同的对。
*)
Theorem commutative_iff_shape (D : Diagram G C) :
  Commutative D ↔ CommutativeShape (FunctorOfDiagram D).
Proof.
  split; intros H x y p q.
  - transitivity (dpath D p); [ symmetry; apply dpath_fmap | ].
    transitivity (dpath D q); [ apply H | apply dpath_fmap ].
  - transitivity (fmap[FunctorOfDiagram D] p); [ apply dpath_fmap | ].
    transitivity (fmap[FunctorOfDiagram D] q);
      [ apply H | symmetry; apply dpath_fmap ].
Qed.

(* The same correspondence read from the functor side. / 从函子一边读的相同对应关系。 *)
Theorem shape_iff_commutative (F : FreeOnQuiver G ⟶ C) :
  CommutativeShape F ↔ Commutative (DiagramOfFunctor F).
Proof.
  split; intros H x y p q.
  - transitivity (fmap[F] p); [ apply dpath_of_functor | ].
    transitivity (fmap[F] q); [ apply H | symmetry; apply dpath_of_functor ].
  - transitivity (dpath (DiagramOfFunctor F) p);
      [ symmetry; apply dpath_of_functor | ].
    transitivity (dpath (DiagramOfFunctor F) q);
      [ apply H | apply dpath_of_functor ].
Qed.

End DiagramBridge.

(** ** Terms over a diagram / ** 图表上的术语 *)

Section DiagramTerms.

Context {G : Quiver}.
Context {C : Category}.
Context (D : Diagram G C).

(*
Interpret a formal composite (Construction/Free/Quiver.v) in [C].  The
   reading of [Comp f g] as [f ∘ g] is the one Solver/Denote.v documents for
   the untyped [Term] of Solver/Expr.v.

--------
在 [C] 中解释一个正式的复合体（Construction/Free/Quiver.v）。将 [Comp f g] 读作 [f ∘ g] 是 Solver/Denote.v 为 Solver/Expr.v 的无类型 [Term] 所记录的方式。
*)
Fixpoint dterm {x y : G} (t : Mor x y) : D x ~{C}~> D y :=
  match t in @Mor _ x0 y0 return D x0 ~{C}~> D y0 with
  | Ident      => id
  | Morph e    => dedge D e
  | Comp f g   => dterm f ∘ dterm g
  end.

(* Interpreting a term agrees with denoting the path it normalises to. / 解释一个术语与表示它规范化到的路径是一致的。 *)
Lemma dterm_dpath {x y : G} (t : Mor x y) : dterm t ≈ dpath D (morDA t).
Proof.
  induction t as [ x | x y e | x y z f IHf g IHg ]; simpl.
  - reflexivity.
  - now rewrite id_left.
  - rewrite dpath_app.
    now rewrite IHf, IHg.
Qed.

(*
Over a commutative diagram every pair of parallel terms is interchangeable,
   whatever their shapes or lengths.

--------
在交换图上，每一对平行项都是可互换的，无论它们的形状或长度如何。
*)
Corollary commutative_dterm (Hc : Commutative D) {x y : G} (s t : Mor x y) :
  dterm s ≈ dterm t.
Proof.
  rewrite (dterm_dpath s), (dterm_dpath t).
  now apply Hc.
Qed.

End DiagramTerms.

Arguments dterm {G C} D {x y} t.

(** ** Transporting a diagram along a functor / ** 沿函子传输图形 *)

Section DiagramFunctorial.

Context {G : Quiver}.
Context {C E : Category}.

(* The image of a diagram under a functor, again a diagram. / 函子下的图像，又是一个图。 *)
Definition PostcomposeDiagram (U : C ⟶ E) (D : Diagram G C) : Diagram G E :=
  QuiverComp D (QuiverHomomorphismOfFunctor C E U).

(* The functor commutes with path denotation, for paths of arbitrary length. / 函子与路径表示式交换，对于任意长度的路径均成立。 *)
Lemma dpath_postcompose (U : C ⟶ E) (D : Diagram G C)
      {x y : G} (p : tlist edges x y) :
  dpath (PostcomposeDiagram U D) p ≈ fmap[U] (dpath D p).
Proof.
  induction p as [ | i m e p IH ]; simpl.
  - now rewrite fmap_id.
  - transitivity (fmap[U] (dpath D p) ∘ fmap[U] (dedge D e)).
    + apply compose_respects; [ exact IH | reflexivity ].
    + symmetry; apply fmap_comp.
Qed.

(* Every functor preserves commutativity. / 每个函子都保持交换性。 *)
Theorem functor_preserves_commutative (U : C ⟶ E) (D : Diagram G C) :
  Commutative D -> Commutative (PostcomposeDiagram U D).
Proof.
  intros Hc x y p q.
  transitivity (fmap[U] (dpath D p)); [ apply dpath_postcompose | ].
  transitivity (fmap[U] (dpath D q));
    [ apply fmap_respects, Hc | symmetry; apply dpath_postcompose ].
Qed.

(*
Riehl, Lemma 1.6.20: a FAITHFUL functor reflects commutativity.  If the
   image diagram commutes then the diagram already commutes.  The proof is by
   [fmap_inj] (Theory/Functor.v) applied to the two path denotations, and
   holds for parallel paths of arbitrary length because [dpath_postcompose]
   does.

--------
Riehl，引理 1.6.20：一个忠实函子会反映交换性。如果像图交换，则图本身已经交换。证明是通过应用 [fmap_inj]（Theory/Functor.v）于两条路径的表示，并且对于任意长度的平行路径都成立，因为 [dpath_postcompose] 也成立。
*)
Theorem faithful_reflects_commutative (U : C ⟶ E) `{@Faithful C E U}
        (D : Diagram G C) :
  Commutative (PostcomposeDiagram U D) -> Commutative D.
Proof.
  intros Hc x y p q.
  apply fmap_inj.
  transitivity (dpath (PostcomposeDiagram U D) p);
    [ symmetry; apply dpath_postcompose | ].
  transitivity (dpath (PostcomposeDiagram U D) q);
    [ apply Hc | apply dpath_postcompose ].
Qed.

End DiagramFunctorial.

(*
The same two facts in the diagram-as-functor formulation, where they need
   no quiver at all: they hold for a diagram indexed by ANY category.

--------
在图作为函子（diagram-as-functor）表述中的同样两个事实，它们根本不需要箭头图：它们对于任何范畴索引的图都成立。
*)
Theorem functor_preserves_commutative_shape {J C E : Category}
        (U : C ⟶ E) (F : J ⟶ C) :
  CommutativeShape F -> CommutativeShape (U ◯ F).
Proof.
  intros Hc x y f g; simpl.
  now apply fmap_respects, Hc.
Qed.

Theorem faithful_reflects_commutative_shape {J C E : Category}
        (U : C ⟶ E) `{@Faithful C E U} (F : J ⟶ C) :
  CommutativeShape (U ◯ F) -> CommutativeShape F.
Proof.
  intros Hc x y f g.
  apply fmap_inj.
  exact (Hc x y f g).
Qed.

(** ** The walking square / ** 行走的广场 *)

(*
Four vertices and four edges,

        A --u--> B
        |        |
        h        v
        |        |
        v        v
        C --k--> D

   with no edge out of D and no edge into A.

--------
四个顶点和四条边，

        A --u--> B
        |        |
        h        v
        |        |
        v        v
        C --k--> D

   D 没有出边，A 没有入边。
*)
Inductive SqNode : Set := SqA | SqB | SqC | SqD.

Definition sq_edge (i j : SqNode) : Type :=
  match i, j with
  | SqA, SqB => unit
  | SqA, SqC => unit
  | SqB, SqD => unit
  | SqC, SqD => unit
  | _  , _   => Empty_set
  end.

Definition SquareQuiver : Quiver := Build_Quiver_Standard_Eq SqNode sq_edge.

(* Sanity: the edge sets are the intended ones. / 理智：边缘集合是预期的那些。 *)
Example sq_edge_AB : @edges SquareQuiver SqA SqB = unit := eq_refl.
Example sq_edge_BD : @edges SquareQuiver SqB SqD = unit := eq_refl.
Example sq_edge_DA : @edges SquareQuiver SqD SqA = Empty_set := eq_refl.

(* The two paths from A to D. / 从A到D的两条路径。 *)
Definition sq_via_B : tlist (@edges SquareQuiver) SqA SqD :=
  tcons SqA (tt : @edges SquareQuiver SqA SqB)
    (tcons SqB (tt : @edges SquareQuiver SqB SqD) tnil).

Definition sq_via_C : tlist (@edges SquareQuiver) SqA SqD :=
  tcons SqA (tt : @edges SquareQuiver SqA SqC)
    (tcons SqC (tt : @edges SquareQuiver SqC SqD) tnil).

(*
This quiver genuinely has a parallel pair: the two paths are DISTINCT
   morphisms of the free category, since they pass through different vertices
   and [SqB = SqC] is refutable.  Without this the commutativity predicate
   would be vacuous on this shape.

--------
这个箭袋真的有一对平行：这两条路径是自由范畴的不同态射，因为它们经过不同的顶点，并且 [SqB = SqC] 是可反驳的。没有这个，这个形状上的交换性谓词将是空洞的。
*)
Lemma sq_via_B_neq_via_C :
  (sq_via_B ≈[FreeOnQuiver SquareQuiver] sq_via_C) -> False.
Proof.
  intro Hbc.
  unfold sq_via_B, sq_via_C in Hbc; simpl in Hbc.
  destruct Hbc as [Hq _ _].
  discriminate Hq.
Qed.

(*
ACYCLICITY, proved rather than asserted.  Ranking the vertices so that every
   edge strictly increases the rank bounds the length of any path by the rank
   difference; an endo-path has rank difference zero, hence length zero, hence
   is [tnil].  This is what makes the endo-path clause of [Commutative] inert
   on this shape -- NOT the emptiness of the self-edge sets, which alone would
   leave a directed cycle of length two or more possible.

--------
无环性，通过证明而非断言。将顶点排序，使每一条边严格增加等级，从而任何路径的长度都被等级差所限制；一个端点路径的等级差为零，因此长度为零，因此是 [tnil]。这就是使 [Commutative] 的端点路径条款在这种形状上无效的原因——而不是自边集合的空性，仅凭这一点仍然可能存在长度为二或更长的有向环。
*)
Definition sq_rank (i : SqNode) : nat :=
  match i with SqA => 0 | SqB => 1 | SqC => 1 | SqD => 2 end.

Lemma sq_len_rank (i j : SqNode) (p : tlist (@edges SquareQuiver) i j) :
  (sq_rank i + tlist_length p <= sq_rank j)%nat.
Proof.
  induction p as [ | i m e p IH ]; simpl.
  - lia.
  - destruct i, m; simpl in e; try contradiction; simpl in *; lia.
Qed.

Lemma sq_endo_paths_are_nil (i : SqNode)
      (p : tlist (@edges SquareQuiver) i i) : tlist_length p = 0%nat.
Proof. pose proof (sq_len_rank i i p); lia. Qed.

Section WalkingSquare.

Context {C : Category}.
Context {a b c d : C} (u : a ~> b) (v : b ~> d) (h : a ~> c) (k : c ~> d).

Definition sq_obj (i : SqNode) : C :=
  match i with SqA => a | SqB => b | SqC => c | SqD => d end.

Definition sq_edgemap (i j : SqNode) : sq_edge i j -> sq_obj i ~> sq_obj j :=
  match i, j return sq_edge i j -> sq_obj i ~> sq_obj j with
  | SqA, SqB => fun _ => u
  | SqA, SqC => fun _ => h
  | SqB, SqD => fun _ => v
  | SqC, SqD => fun _ => k
  | _  , _   => fun e => match e with end
  end.

Program Definition SquareDiagram : Diagram SquareQuiver C :=
  {| fnodes := sq_obj ; fedgemap := sq_edgemap |}.

(*
The edge labels are the four given morphisms.  The equality is Leibniz (=)
   rather than [≈] because the two sides are the very same term; this is the
   convention documented at Functor/Bifunctor.v.

--------
边的标签是给定的四个态射。等式是 Leibniz (=)，而不是 [≈]，因为两边是完全相同的项；这是在 Functor/Bifunctor.v 中记录的惯例。
*)
Example sq_label_u : dedge SquareDiagram (tt : @edges SquareQuiver SqA SqB) = u
  := eq_refl.
Example sq_label_k : dedge SquareDiagram (tt : @edges SquareQuiver SqC SqD) = k
  := eq_refl.

(* The composite denoted by each of the two paths. / 由这两条路径各自表示的复合体。 *)
Example sq_denote_via_B : dpath SquareDiagram sq_via_B ≈ v ∘ u.
Proof. simpl; now rewrite id_left. Qed.

Example sq_denote_via_C : dpath SquareDiagram sq_via_C ≈ k ∘ h.
Proof. simpl; now rewrite id_left. Qed.

(*
The specification of every path of the square, by its endpoints.  [False]
   marks the vertex pairs joined by no path at all.  Read as: assuming the
   square commutes, a path's denotation is determined by its endpoints.

--------
每条方形路径的规范，由其端点决定。[False] 标记没有任何路径连接的顶点对。理解为：假设方形可交换，一条路径的表示由其端点确定。
*)
Definition sq_spec (i j : SqNode) : (sq_obj i ~{C}~> sq_obj j) -> Type :=
  match i, j return (sq_obj i ~{C}~> sq_obj j) -> Type with
  | SqA, SqA => fun f => f ≈ id
  | SqB, SqB => fun f => f ≈ id
  | SqC, SqC => fun f => f ≈ id
  | SqD, SqD => fun f => f ≈ id
  | SqA, SqB => fun f => f ≈ u
  | SqA, SqC => fun f => f ≈ h
  | SqA, SqD => fun f => f ≈ v ∘ u
  | SqB, SqD => fun f => f ≈ v
  | SqC, SqD => fun f => f ≈ k
  | _  , _   => fun _ => False
  end.

Lemma sq_paths (Hsq : v ∘ u ≈ k ∘ h) (i j : SqNode)
      (p : tlist (@edges SquareQuiver) i j) :
  sq_spec i j (dpath SquareDiagram p).
Proof.
  induction p as [ | i m e p IH ].
  - destruct j; simpl; reflexivity.
  - (*
Closed explicitly rather than with [cat]: every component of [cat]
       (Lib/Tactics.v) always succeeds, so [cat] can never report a
       missing step; and exactly one of these goals -- [k ∘ h ≈ v ∘ u] -- is
       the one place [Hsq] is used, so it is discharged by name.  The [ [> ... ] ]
       selector pins that to EXACTLY one remaining goal: without it, an edit
       that made [try reflexivity] close every goal would leave the chain
       running on none, silently succeeding with [Hsq] unused -- the same class
       of quiet-success defect the [cat] removal above is about.  This matches
       [tri_paths] below.

--------
明确关闭而不是使用 [cat]：[cat]（Lib/Tactics.v）的每个组件总是成功，因此 [cat] 永远无法报告缺失的步骤；并且正好有一个目标——[k ∘ h ≈ v ∘ u]——是唯一使用 [Hsq] 的位置，因此它通过名称被解除。[ [> ... ] 选择器将其固定到唯一剩余的一个目标：如果没有它，一个编辑使 [try reflexivity] 关闭每个目标将使链条在没有目标的情况下继续运行，并悄无声息地成功且 [Hsq] 未被使用——这与上面提到的 [cat] 移除所涉及的悄无声息成功缺陷属同一类。这与下面的 [tri_paths] 相符。
*)
    destruct i, m; simpl in e; try destruct e;
      destruct j; simpl in *; try contradiction;
      rewrite IH; rewrite ?id_left; try reflexivity; [> symmetry; exact Hsq ].
Qed.

(* The one equation implies the general predicate over ALL parallel pairs. / 这个方程暗示了对所有平行对的一般谓词。 *)
Theorem square_commutes (Hsq : v ∘ u ≈ k ∘ h) : Commutative SquareDiagram.
Proof.
  intros x y p q.
  pose proof (sq_paths Hsq _ _ p) as Hp.
  pose proof (sq_paths Hsq _ _ q) as Hq.
  destruct x, y; simpl in Hp, Hq; try contradiction;
    now rewrite Hp, Hq.
Qed.

(*
... and conversely, instantiating the predicate at the two paths from A to
   D recovers the equation.

--------
... 相反，在从 A 到 D 的两条路径上实例化谓词可以恢复该方程。
*)
Theorem square_commutes_inv : Commutative SquareDiagram -> v ∘ u ≈ k ∘ h.
Proof.
  intro Hc.
  pose proof (Hc SqA SqD sq_via_B sq_via_C) as Heq.
  unfold sq_via_B, sq_via_C in Heq; simpl in Heq.
  now rewrite !id_left in Heq.
Qed.

(*
So on the square shape the general predicate carries exactly the content of
   the familiar two-composite equation: nothing more, nothing less.  The
   informal reason usually given -- that this shape has just one pair of
   distinct parallel paths -- is a statement about paths up to equality and is
   NOT proved here; what is proved is the [↔] itself, semantically, via
   [sq_paths].

--------
因此，在方形图形上，一般谓词恰好包含熟悉的两个复合方程的内容：不多也不少。通常给出的非正式原因——这个形状只有一对不同的平行路径——是关于路径相等的陈述，这里没有证明；这里证明的是 [↔] 本身，从语义上，通过 [sq_paths]。
*)
Theorem square_commutative_iff :
  Commutative SquareDiagram ↔ v ∘ u ≈ k ∘ h.
Proof.
  split; [ apply square_commutes_inv | apply square_commutes ].
Qed.

End WalkingSquare.

(** ** The walking triangle / ** 行走的三角形 *)

(*
Three vertices, with a direct edge and a two-step route:

        X --w------------> Z
         \                ^
          u              /
           \            /
            > Y --v----/

   (the two-step route is [u] then [v]; [w] is the direct edge).

--------
三个顶点，一个直接边和一条两步路线：

        X --w------------> Z
         \                ^
          u              /
           \            /
            > Y --v----/

   （两步路线是 [u] 然后 [v]；[w] 是直接边）。
*)
Inductive TriNode : Set := TrX | TrY | TrZ.

Definition tri_edge (i j : TriNode) : Type :=
  match i, j with
  | TrX, TrY => unit
  | TrY, TrZ => unit
  | TrX, TrZ => unit
  | _  , _   => Empty_set
  end.

Definition TriangleQuiver : Quiver := Build_Quiver_Standard_Eq TriNode tri_edge.

Definition tri_via_Y : tlist (@edges TriangleQuiver) TrX TrZ :=
  tcons TrX (tt : @edges TriangleQuiver TrX TrY)
    (tcons TrY (tt : @edges TriangleQuiver TrY TrZ) tnil).

Definition tri_direct : tlist (@edges TriangleQuiver) TrX TrZ :=
  tcons TrX (tt : @edges TriangleQuiver TrX TrZ) tnil.

(*
Again a genuine parallel pair: the two-step route and the direct edge are
   distinct morphisms of the free category, since their first edges land on
   different vertices and [TrY = TrZ] is refutable.

--------
再次出现一个真正的平行对：两步路径和直接边是自由范畴的不同态射，因为它们的第一条边落在不同的顶点上，并且 [TrY = TrZ] 是可证伪的。
*)
Lemma tri_via_Y_neq_direct :
  (tri_via_Y ≈[FreeOnQuiver TriangleQuiver] tri_direct) -> False.
Proof.
  intro Hxy.
  unfold tri_via_Y, tri_direct in Hxy; simpl in Hxy.
  destruct Hxy as [Hq _ _].
  discriminate Hq.
Qed.

(* Acyclicity of the triangle, by the same rank argument. / 通过相同的秩论证，证明三角形的无环性。 *)
Definition tri_rank (i : TriNode) : nat :=
  match i with TrX => 0 | TrY => 1 | TrZ => 2 end.

Lemma tri_len_rank (i j : TriNode) (p : tlist (@edges TriangleQuiver) i j) :
  (tri_rank i + tlist_length p <= tri_rank j)%nat.
Proof.
  induction p as [ | i m e p IH ]; simpl.
  - lia.
  - destruct i, m; simpl in e; try contradiction; simpl in *; lia.
Qed.

Lemma tri_endo_paths_are_nil (i : TriNode)
      (p : tlist (@edges TriangleQuiver) i i) : tlist_length p = 0%nat.
Proof. pose proof (tri_len_rank i i p); lia. Qed.

Section WalkingTriangle.

Context {C : Category}.
Context {x y z : C} (u : x ~> y) (v : y ~> z) (w : x ~> z).

Definition tri_obj (i : TriNode) : C :=
  match i with TrX => x | TrY => y | TrZ => z end.

Definition tri_edgemap (i j : TriNode) : tri_edge i j -> tri_obj i ~> tri_obj j :=
  match i, j return tri_edge i j -> tri_obj i ~> tri_obj j with
  | TrX, TrY => fun _ => u
  | TrY, TrZ => fun _ => v
  | TrX, TrZ => fun _ => w
  | _  , _   => fun e => match e with end
  end.

Program Definition TriangleDiagram : Diagram TriangleQuiver C :=
  {| fnodes := tri_obj ; fedgemap := tri_edgemap |}.

Definition tri_spec (i j : TriNode) : (tri_obj i ~{C}~> tri_obj j) -> Type :=
  match i, j return (tri_obj i ~{C}~> tri_obj j) -> Type with
  | TrX, TrX => fun f => f ≈ id
  | TrY, TrY => fun f => f ≈ id
  | TrZ, TrZ => fun f => f ≈ id
  | TrX, TrY => fun f => f ≈ u
  | TrY, TrZ => fun f => f ≈ v
  | TrX, TrZ => fun f => f ≈ w
  | _  , _   => fun _ => False
  end.

Lemma tri_paths (Htri : v ∘ u ≈ w) (i j : TriNode)
      (p : tlist (@edges TriangleQuiver) i j) :
  tri_spec i j (dpath TriangleDiagram p).
Proof.
  induction p as [ | i m e p IH ].
  - destruct j; simpl; reflexivity.
  - destruct i, m; simpl in e; try destruct e;
      destruct j; simpl in *; try contradiction;
      rewrite IH; rewrite ?id_left; try reflexivity; [> exact Htri ].
Qed.

Theorem triangle_commutes (Htri : v ∘ u ≈ w) : Commutative TriangleDiagram.
Proof.
  intros i j p q.
  pose proof (tri_paths Htri _ _ p) as Hp.
  pose proof (tri_paths Htri _ _ q) as Hq.
  destruct i, j; simpl in Hp, Hq; try contradiction;
    now rewrite Hp, Hq.
Qed.

Theorem triangle_commutes_inv : Commutative TriangleDiagram -> v ∘ u ≈ w.
Proof.
  intro Hc.
  pose proof (Hc TrX TrZ tri_via_Y tri_direct) as Heq.
  unfold tri_via_Y, tri_direct in Heq; simpl in Heq.
  now rewrite !id_left in Heq.
Qed.

Theorem triangle_commutative_iff :
  Commutative TriangleDiagram ↔ v ∘ u ≈ w.
Proof.
  split; [ apply triangle_commutes_inv | apply triangle_commutes ].
Qed.

End WalkingTriangle.

(** ** The walking loop: the empty path carries content / ** 步行环路：空旷的道路承载着内容 *)

(*
One vertex, one loop edge.

        X --e--> X   (a single edge from X to itself)

   Both shapes above are ACYCLIC, so in each of them the endo-path clause of
   [Commutative] is instantiated only at [tnil] and says nothing; this shape is
   the one that exercises it.  Note that “every [edges i i] is [Empty_set]”
   would NOT by itself establish that -- a directed cycle of length two or more
   produces an endo-path with no self-edge anywhere in it.  What actually
   rules cycles out is that the edges strictly increase a rank, which is proved
   below as [sq_endo_paths_are_nil] and [tri_endo_paths_are_nil] rather than
   asserted.

--------
一个顶点，一个环路边。

        X --e--> X   （从 X 到自身的一条边）

上面的两个形状都是无环的，因此在它们每一个中，[Commutative] 的自身路径条款仅在 [tnil] 处实例化，并且没有说明任何内容；这个形状就是使用它的形状。请注意，“每个 [edges i i] 都是 [Empty_set]” 本身不会证明这一点——长度为两或更多的有向循环会产生一个其中没有自边的自身路径。实际上排除循环的是边严格增加一个级别，这在下面被证明为 [sq_endo_paths_are_nil] 和 [tri_endo_paths_are_nil]，而不是被断言。
*)
Inductive LoopNode : Set := LpX.

Definition loop_edge (i j : LoopNode) : Type :=
  match i, j with LpX, LpX => unit end.

Definition LoopQuiver : Quiver := Build_Quiver_Standard_Eq LoopNode loop_edge.

Example loop_edge_XX : @edges LoopQuiver LpX LpX = unit := eq_refl.

Section WalkingLoop.

Context {C : Category}.
Context {a : C}.
Context (e : a ~> a).

Definition loop_obj (i : LoopNode) : C := a.

Definition loop_edgemap (i j : LoopNode)
  : loop_edge i j -> loop_obj i ~> loop_obj j :=
  match i, j with LpX, LpX => fun _ => e end.

(*
As with [SquareDiagram] and [TriangleDiagram], the [fedgemap_respects]
   obligation here is discharged by the file-global [Obligation Tactic]
   (Lib/Tactics.v's [cat_simpl]).  That is wide automation of exactly the
   kind this file argues against for LOAD-BEARING steps, so it is worth being
   explicit that these three are not load-bearing: each edge map is a constant
   or a match on a finite enumeration, and the obligation resolves to
   [CMorphisms.reflexive_proper].

--------
与 [SquareDiagram] 和 [TriangleDiagram] 一样，这里的 [fedgemap_respects] 义务由文件全局的 [Obligation Tactic]（Lib/Tactics.v 的 [cat_simpl]）完成。这正是该文件反对用于承重步骤的广泛自动化类型，因此值得明确指出，这三者都不是承重的：每个边映射都是一个常量或有限枚举的匹配，而义务会解析为 [CMorphisms.reflexive_proper]。
*)
Program Definition LoopDiagram : Diagram LoopQuiver C :=
  {| fnodes := loop_obj ; fedgemap := loop_edgemap |}.

(*
Every path in this shape denotes an iterate of [e]; under [e ≈ id] they all
   denote [id].

--------
这个形状中的每条路径表示 [e] 的一次迭代；在 [e ≈ id] 下它们都表示 [id]。
*)
Lemma loop_paths (He : e ≈ id) (i j : LoopNode)
      (p : tlist (@edges LoopQuiver) i j) :
  dpath LoopDiagram p ≈ id.
Proof.
  induction p as [ | i m ed p IH ].
  - reflexivity.
  - simpl; rewrite IH, id_left; destruct i, m; exact He.
Qed.

(*
The forward direction is the empty-path argument itself: compare the
   one-edge path against [tnil].

--------
前向方向就是空路径参数本身：将单边路径与 [tnil] 进行比较。
*)
Theorem loop_commutes_inv : Commutative LoopDiagram -> e ≈ id.
Proof.
  intro Hc.
  pose proof (Hc LpX LpX
                (tcons LpX (tt : @edges LoopQuiver LpX LpX) tnil) tnil) as H.
  simpl in H.
  now rewrite id_left in H.
Qed.

Theorem loop_commutes (He : e ≈ id) : Commutative LoopDiagram.
Proof.
  intros i j p q.
  now rewrite (loop_paths He _ _ p), (loop_paths He _ _ q).
Qed.

(*
So on the walking loop, commutativity is exactly the statement that the
   drawn endomorphism is the identity.  This is the header claim about [tnil],
   proved rather than asserted.

--------
因此，在行走循环上，可交换性恰好是所绘制的自同态是恒等映射的陈述。这是关于 [tnil] 的标题性声明，是被证明的，而非断言的。
*)
Theorem loop_commutative_iff : Commutative LoopDiagram ↔ e ≈ id.
Proof.
  split.
  - apply loop_commutes_inv.
  - apply loop_commutes.
Qed.

End WalkingLoop.

(** ** The naturality square as a commuting diagram / ** 作为交换图的自然性平方 *)

Section NaturalitySquare.

Context {C D : Category}.
Context {F G : C ⟶ D}.
Context (alpha : F ⟹ G).

(*
The naturality square at [f : p ~> q], as a diagram of shape
   [SquareQuiver]:

        F p --fmap[F] f--> F q
         |                  |
       alpha p            alpha q
         |                  |
         v                  v
        G p --fmap[G] f--> G q

--------
在 [f : p ~> q] 的自然性方图，如形状为 [SquareQuiver] 的图示：

        F p --fmap[F] f--> F q
         |                  |
       alpha p            alpha q
         |                  |
         v                  v
        G p --fmap[G] f--> G q
*)
Definition NaturalitySquareDiagram {p q : C} (f : p ~> q)
  : Diagram SquareQuiver D :=
  SquareDiagram (fmap[F] f) (@transform _ _ _ _ alpha q)
                (@transform _ _ _ _ alpha p) (fmap[G] f).

(*
It commutes, by naturality.  [naturality_sym] (Theory/Natural/Transformation.v)
   is literally the equation [square_commutes] asks for.

--------
它通过自然性作交换。[naturality_sym]（Theory/Natural/Transformation.v）正是 [square_commutes] 所要求的方程。
*)
Theorem naturality_square_commutes {p q : C} (f : p ~> q) :
  Commutative (NaturalitySquareDiagram f).
Proof.
  apply square_commutes.
  apply naturality_sym.
Qed.

(*
And commutativity of that diagram gives naturality back, so for this shape
   the diagrammatic condition and the naturality equation are the same
   statement.

--------
并且该图的交换性会带回自然性，因此对于这种形状，图示条件和自然性方程是相同的陈述。
*)
Theorem naturality_of_commutative_square {p q : C} (f : p ~> q) :
  Commutative (NaturalitySquareDiagram f) ->
  @transform _ _ _ _ alpha q ∘ fmap[F] f
    ≈ fmap[G] f ∘ @transform _ _ _ _ alpha p.
Proof.
  apply square_commutes_inv.
Qed.

Theorem naturality_square_commutative_iff {p q : C} (f : p ~> q) :
  Commutative (NaturalitySquareDiagram f)
    ↔ @transform _ _ _ _ alpha q ∘ fmap[F] f
        ≈ fmap[G] f ∘ @transform _ _ _ _ alpha p.
Proof.
  apply square_commutative_iff.
Qed.

End NaturalitySquare.


(** ** Commutativity as factorization through the preorder reflection / ** 作为通过前序反射的因式分解的交换性 *)

(*
Fong and Spivak, Seven Sketches in Compositionality, §3.3.4, the footnote to
   Definition 3.51 (cited by location; see the header): a diagram commutes
   exactly when it factors through the preorder reflection of its indexing
   category.  Construction/PreorderReflection.v builds that reflection as the
   quotient of a category by the total hom-congruence.

   The intuition is that the reflection destroys precisely the information
   commutativity asks a diagram to ignore.  In [PreorderReflect J] all parallel
   morphisms are identified, so a functor out of it CANNOT distinguish two
   parallel paths -- it commutes for want of the ability to do otherwise -- and
   conversely a functor that already identifies parallel morphisms descends
   through the quotient.

--------
Fong 和 Spivak，《组合性中的七个草图》，§3.3.4，定义 3.51 的脚注（按位置引用；见标题）：当且仅当一个图经过其索引范畴的预序反射进行分解时，该图才交换。Construction/PreorderReflection.v 将该反射构建为一个范畴在全同态合同下的商。

直觉上，这个反射恰恰破坏了交换性要求图忽略的信息。在 [PreorderReflect J] 中，所有并行的态射都被识别，因此一个从它出发的函子无法区分两条并行路径——因为缺乏其他能力，它就交换——反过来，一个已经识别并行态射的函子会通过该商下降。
*)

(*
(=>) A shape-commuting functor factors through the reflection, and the
   factorization reproduces it on the nose.  The mediating functor is
   [QuotientLift] at the total congruence, whose hypothesis is exactly
   [CommutativeShape].

--------
(=>) 一个形状交换函子通过反射进行分解，并且该分解精确地再现了它。中介函子是在全余合上的 [QuotientLift]，其假设正好是 [CommutativeShape]。
*)
Definition ShapeFactor {J C : Category} (F : J ⟶ C) (Hc : CommutativeShape F)
  : PreorderReflect J ⟶ C :=
  @QuotientLift J (TotalRel J) _ C F (fun x y f g _ => Hc x y f g).

Theorem commutative_shape_factors {J C : Category} (F : J ⟶ C)
        (Hc : CommutativeShape F) :
  ∀ (x y : J) (f : x ~> y),
    fmap[ShapeFactor F Hc] (fmap[Reflect J] f) = fmap[F] f.
Proof.
  intros. exact (@QuotientLift_proj J (TotalRel J) _ C F _ x y f).
Qed.

(*
The Leibniz [=] here is the library's same-term exception, not a lapse from
   [≈]: Construction/Quotient.v's [QuotientLift_proj] is proved by
   [reflexivity], the two sides being the same term, exactly as at
   Functor/Bifunctor.v.

--------
这里的 Leibniz [=] 是库中同一项例外，而不是 [≈] 的疏漏：Construction/Quotient.v 的 [QuotientLift_proj] 是通过 [reflexivity] 证明的，双方是同一项，正如在 Functor/Bifunctor.v 中一样。
*)

(* (<=) Anything of the form [K ◯ Reflect J] commutes, whatever [K] is. / (<=) 形式为 [K ◯ Reflect J] 的任何东西都是可交换的，无论 [K] 是什么。 *)
Theorem factors_commutative_shape {J C : Category}
        (K : PreorderReflect J ⟶ C) :
  CommutativeShape (K ◯ Reflect J).
Proof.
  intros x y f g; simpl; apply fmap_respects; exact I.
Qed.

(*
The converse in the form that matches the forward direction: a functor that
   merely AGREES with such a composite -- pointwise up to [≈], with object maps
   equal on the nose, which is how Construction/Quotient.v states its
   uniqueness -- is itself shape-commuting.

--------
与正向形式相对应的逆命题：一个函子仅仅与这样的复合函子一致——逐点地直到 [≈]，且对象映射完全相等，这正是 Construction/Quotient.v 陈述其唯一性的方式——它本身就是形状交换的。
*)
Theorem factors_commutative_shape' {J C : Category} (F : J ⟶ C)
        (K : PreorderReflect J ⟶ C)
        (Hobj : ∀ x : J, fobj[K] x = fobj[F] x)
        (Hfac : ∀ (x y : J) (f : x ~> y),
                   hom_cast (Hobj x) (Hobj y)
                     (fmap[K] (fmap[Reflect J] f)) ≈ fmap[F] f) :
  CommutativeShape F.
Proof.
  intros x y f g.
  rewrite <- (Hfac x y f), <- (Hfac x y g).
  apply hom_cast_respects.
  apply fmap_respects.
  exact I.
Qed.

(*
And hence for Mac Lane's quiver form of the predicate, through
   [commutative_iff_shape]: a commuting diagram factors through the preorder
   reflection of its FREE category.

--------
因此，对于 Mac Lane 的谓词的箭袋形式，通过 [commutative_iff_shape]：一个可交换图通过其 FREE 范畴的预序反射进行分解。
*)
Theorem commutative_factors {G : Quiver} {C : Category} (D : Diagram G C)
        (Hc : Commutative D) :
  ∀ (x y : FreeOnQuiver G) (f : x ~> y),
    fmap[ShapeFactor (FunctorOfDiagram D) (fst (commutative_iff_shape D) Hc)]
        (fmap[Reflect _] f)
      = fmap[FunctorOfDiagram D] f.
Proof.
  intros. apply commutative_shape_factors.
Qed.

(*
The two directions above are usually quoted as a single biconditional, so
   state it.  “Factors through the reflection” is packaged as the data of a
   functor out of [PreorderReflect J] agreeing with [F], in exactly the form
   Construction/Quotient.v uses for its own uniqueness statement: object
   maps equal on the nose, morphism maps agreeing up to [≈] after conjugating
   by [hom_cast] along those equalities.

--------
上面两个方向通常被引用为单个双条件，因此请陈述它。“通过反射的因子”被包装为一个从 [PreorderReflect J] 出发同 [F] 一致的函子的数据，形式完全与 Construction/Quotient.v 用于自身唯一性陈述的形式相同：对象映射在本质上相等，态射映射在沿着这些等式通过 [hom_cast] 共轭后，与 [≈] 一致。
*)
Definition FactorsThroughReflection {J C : Category} (F : J ⟶ C) : Type :=
  { K : PreorderReflect J ⟶ C &
  { Hobj : ∀ x : J, fobj[K] x = fobj[F] x &
    ∀ (x y : J) (f : x ~> y),
      hom_cast (Hobj x) (Hobj y)
        (fmap[K] (fmap[Reflect J] f)) ≈ fmap[F] f }}.

(*
The factorization is moreover an equality of FUNCTORS in StrictCat's
   hom-setoid, not merely a pointwise agreement -- the same equivalence
   [functor_of_diagram_of_functor] above is stated in.

--------
此外，这种分解在 StrictCat 的同态集合（hom-setoid）中是函子（FUNCTORS）的相等，而不仅仅是逐点的一致 —— 上述相同的等价 [functor_of_diagram_of_functor] 也有陈述。
*)
Lemma shape_factor_functor {J C : Category} (F : J ⟶ C) (Hc : CommutativeShape F) :
  @equiv _ (@Functor_StrictEq_Setoid J C) (ShapeFactor F Hc ◯ Reflect J) F.
Proof.
  exists (fun _ => eq_refl); intros; reflexivity.
Qed.

Theorem commutes_iff_factors {J C : Category} (F : J ⟶ C) :
  CommutativeShape F ↔ FactorsThroughReflection F.
Proof.
  split.
  - intro Hc.
    exists (ShapeFactor F Hc), (fun _ => eq_refl).
    (*
[hom_cast eq_refl eq_refl] disappears definitionally, and the
       factorization holds on the nose by [QuotientLift_proj].

--------
[hom_cast eq_refl eq_refl] 从定义上消失，并且因式分解通过 [QuotientLift_proj] 精确成立。
*)
    intros x y f; reflexivity.
  - intros [K [Hobj Hfac]].
    exact (factors_commutative_shape' F K Hobj Hfac).
Qed.
