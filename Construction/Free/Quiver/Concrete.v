Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Concrete.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Free.Quiver.

From Coq Require Import Eqdep_dec.

Generalizable All Variables.

(* * * Quivers as a concrete category: the multi-sorted case / * * 作为具体范畴的箭袋：多排序情况 *)

(*
 nLab:      https://ncatlab.org/nlab/show/quiver
 nLab:      https://ncatlab.org/nlab/show/concrete+category
 Wikipedia: https://en.wikipedia.org/wiki/Quiver_(mathematics)
 Book:      Riehl, "Category Theory in Context", Dover 2016, §1.6,
 Example 1.6.19, printed p. 46
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 GTM 5, Springer 1998, §I.7, printed p. 26

 Riehl's Example 1.6.19 is the sharpest small illustration of what a chosen
 underlying-set functor is for.  A quiver has TWO sorts of element, vertices
 and arrows, and neither sort alone determines a quiver homomorphism:

 - the VERTEX functor is not faithful, because a homomorphism can move
 parallel edges around while fixing every vertex;
 - the ARROW functor is not faithful, because a homomorphism can permute
 isolated vertices while fixing every edge (there being none to move);
 - their DISJOINT UNION is faithful, so quivers are concrete after all.

 All three functors are built here over the in-tree quiver category
 `QuiverCategory` (Construction/Free/Quiver.v), whose objects are the
 `Quiver` records of that file: a node type together with an edge
 setoid `edges x y` for each ordered pair of nodes.  Since edges are indexed
 by their endpoints rather than carrying source/target maps, the "set of
 arrows" has to be assembled: [QArrow] below is the type of triples
 (source, target, edge), and [QArrow_Setoid] compares two such triples by an
 equality of endpoints together with an `≈` of edges moved along it.

 [QuiverVertices] : Q ↦ the nodes of Q             (not faithful)
 [QuiverArrows]   : Q ↦ the triples of Q           (not faithful)
 [QuiverElements] : Q ↦ nodes of Q ⊎ triples of Q  (faithful, see below)

 These are the first `Sets`-valued functors on quivers in the library.
 `QuiverCategory` is the only quiver category in the tree, and the only
 quiver-facing functors that existed before this file are
 Construction/Free/Quiver.v's `Forgetful : StrictCat ⟶ QuiverCategory`
 and `FreeCatFunctor : QuiverCategory ⟶ StrictCat`, neither of which
 lands in `Sets`.  The quiver-building idiom used for the witnesses below,
 `Build_Quiver_Standard_Eq`, is the one Test/Issue138.v already uses.

 Both negative results are genuine refutations, each witnessed by two
 PARALLEL homomorphisms exhibited explicitly and shown distinct in the
 hom-setoid of `QuiverCategory` — not merely written differently:

 [LoopQuiver]  one node, two parallel loops; the identity and the
 loop-swapping endomorphism agree on nodes, differ on edges
 ([QuiverVertices_not_Faithful]).
 [DiscQuiver]  two nodes, no edges; the identity and the node-swapping
 endomorphism agree on arrows (there are none), differ on nodes
 ([QuiverArrows_not_Faithful]).

 Scope of the positive half, disclosed
 -------------------------------------

 [QuiverElements] is proved faithful under one hypothesis on the target
 quiver: uniqueness of identity proofs for its node type ([NodeUIP]).
 Where that hypothesis enters is worth stating precisely.

 Equivalence of quiver homomorphisms in `QuiverCategory`
 (`QuiverHomomorphismEquivalence`) is a SIGMA type: `F ≈ G` consists of a
 family `node_equiv : ∀ x, F x = G x` TOGETHER WITH a coherence condition
 that quantifies over all edges and refers to that one chosen family.  From
 `fmap[QuiverElements] F ≈ fmap[QuiverElements] G` one recovers, on the node
 summand, a family `ne x : F x = G x`, and on the arrow summand, for each
 edge separately, its own pair of endpoint equalities.  Nothing in that
 hypothesis ties the per-edge equalities to the ones `ne` supplies, and this
 development found no way to replace one by the other short of [NodeUIP].
 With [NodeUIP] the replacement is immediate, and the proof goes through.

 Riehl's quivers have SETS of vertices, for which uniqueness of identity
 proofs holds; so [NodeUIP] is the hypothesis under which her example is
 being reproduced.  Accordingly the `Concrete` instance is delivered for the
 full subcategory (in the sense of Construction/Subcategory.v) of quivers
 satisfying it — [SetQuiverCat], built with that file's generic `Sub` —
 rather than for `QuiverCategory` itself, and BOTH negative
 results are reproved there ([SetQuiverVertices_not_Faithful],
 [SetQuiverArrows_not_Faithful]) so that all of Example 1.6.19 lives in one
 category.  Both witness quivers have node types with decidable equality
 (`poly_unit` and `bool`), so they are objects of [SetQuiverCat] by
 [NodeDecEq_NodeUIP], an axiom-free Hedberg step through
 `Eqdep_dec.UIP_dec` — the same device Construction/Quotient.v uses for
 `obj_uip`.

 An unrestricted `Concrete QuiverCategory` is therefore NOT claimed here,
 and the restriction is NOT a shortcut: the closing section of this file
 proves that `Faithful QuiverElements` IMPLIES UIP, so the hypothesis is
 forced rather than convenient. (The first commit said only that this was
 an obstruction to the proof rather than a refutation; an audit closed
 the loop, and its argument is integrated below.) Since UIP is
 independent of Rocq's logic, `Faithful QuiverElements` is not provable
 here, and concreteness of `QuiverCategory` VIA THIS FUNCTOR is
 unreachable axiom-free.

 Whether some OTHER functor to `Sets` concretizes `QuiverCategory` is
 still left open. No such functor is known to the author of this file,
 and there is a structural reason for pessimism — pointwise data over any
 carrier yields equalities one element at a time, whereas the target
 requires a single node family coherent with every edge at once — but no
 non-existence proof is offered.

 Obligation discipline: this file sets `Obligation Tactic := idtac`, so
 every proof below introduces its own variables and none depends on a
 Program-generated name. 

 --------
 nLab:       https://ncatlab.org/nlab/show/quiver 
 nLab:       https://ncatlab.org/nlab/show/concrete+category 
 Wikipedia:  https://en.wikipedia.org/wiki/Quiver_(mathematics) 
 书籍:      Riehl，《Category Theory in Context》，Dover 2016，第§1.6节，
 例 1.6.19，印刷版第46页
 书籍:      Mac Lane，《Categories for the Working Mathematician》，第2版，
 GTM 5, Springer 1998，第§I.7节，印刷版第26页

 Riehl 的例 1.6.19 是对选定底集函子用途的最精确的小型示例。一个箭图（quiver）有两种元素：顶点和箭头，而且单靠任何一类元素都无法确定一个箭图同态:- VERTEX函子不是忠实的，因为同态可以在固定每个顶点的同时移动平行的边；
 - ARROW函子不是忠实的，因为同态可以在固定每条边的同时排列孤立顶点（因为没有边可移动）；
 - 它们的DISJOINT UNION是忠实的，所以箭图（quiver）毕竟是具体的。这里构建了三个函子，它们都是在树内箭图范畴 `QuiverCategory`（Construction/Free/Quiver.v）上构建的，其对象是该文件中的 `Quiver` 记录：每个节点类型以及每对有序节点的边集合 `edges x y`。由于边是由其端点索引，而不是携带源/目标映射，因此箭集合必须被组装：下面的 [QArrow] 是 (源, 目标, 边) 三元组的类型，而 [QArrow_Setoid] 通过端点的相等以及沿其移动的 `≈` 边来比较两个这样的三元组。

 [QuiverVertices]  : Q ↦ Q 的节点             （非忠实）
 [QuiverArrows]  : Q ↦ Q 的三元组           （非忠实）
 [QuiverElements]  : Q ↦ Q 的节点 ⊎ Q 的三元组  （忠实，见下文）这些是库中箭袋上的第一个 `Sets` 值函子。
 `QuiverCategory`是树中唯一的箭袋类别，也是唯一的
 在此文件之前存在的向箭袋函子为
 Construction/Free/Quiver.v 的 `Forgetful : StrictCat ⟶ QuiverCategory`
 以及`FreeCatFunctor : QuiverCategory ⟶ StrictCat`，都不是
 `Sets`。下面见证人使用的“建造箭袋”成语，
 `Build_Quiver_Standard_Eq` ，是 Test/Issue138.v 已经在用的那个。

 这两个否定结果都是真实的反驳，每个反驳都有两人见证
 在
 `QuiverCategory`人——不仅仅是写法不同：[LoopQuiver] 一个节点，两个平行的环；恒等映射和环互换的自同态在节点上相同，在边上不同（[QuiverVertices_not_Faithful]）。
 [DiscQuiver] 两个节点，没有边；恒等映射和节点互换的自同态在箭头上相同（没有箭头），在节点上不同（[QuiverArrows_not_Faithful]）。

 正半部分的范围，已公开
 -------------------------------------

 [QuiverElements] 已在目标箭图上的一个假设下被证明为忠实：其节点类型的恒等证明唯一性（[NodeUIP]）。这个假设应用的地方值得精确说明。在 `QuiverCategory` (`QuiverHomomorphismEquivalence`) 中，箭图同态的等价性是一种 SIGMA 类型：`F ≈ G` 由一个家族 `node_equiv : ∀ x, F x = G x` 以及一个一致性条件组成，该条件对所有边进行量化，并引用所选择的那个家族。从 `fmap [QuiverElements]ZZ  F ≈ fmap [QuiverElements]ZZ  G` 可以在节点直和上恢复一个家族 `ne x : F x = G x`，而在箭头直和上，对于每一条边单独恢复它自己的端点等式。该假设中没有任何内容将每条边的等式与 `ne` 提供的等式联系起来，并且这一发展没有找到在不使用 [NodeUIP] 的情况下互相替换的方法。有了 [NodeUIP]，替换立即可行，证明得以继续。Riehl 的箭袋具有顶点集合，对于这些集合身份证明的唯一性成立；因此 [NodeUIP] 是她的例子被复制时所依据的假设。因此，`Concrete` 实例被提供用于满足该假设的箭袋的全子范畴（在 Construction/Subcategory.v 的意义下）——[SetQuiverCat]，使用该文件的通用 `Sub` 构建——而不是用于 `QuiverCategory` 本身，而且两个负结果都在此重新证明（[SetQuiverVertices_not_Faithful]，[SetQuiverArrows_not_Faithful]），以便示例 1.6.19 的全部内容都在一个范畴里。两个见证箭袋的节点类型具有可判等性（`poly_unit` 和 `bool`），因此它们是 [SetQuiverCat] 的对象，由 [NodeDecEq_NodeUIP]，经过 `Eqdep_dec.UIP_dec` 的无公理 Hedberg 步骤——这是 Construction/Quotient.v 对 `obj_uip` 所使用的相同方法。因此，这里没有声称一个无限制的 `Concrete QuiverCategory`，并且这个限制不是捷径：本文件的结尾部分证明了 `Faithful QuiverElements` 意味着 UIP，所以假设是被迫的而不是方便的。（第一次提交只说明这对证明是一个阻碍，而不是反驳；一次审核闭合了这个循环，其论证已整合如下。）由于 UIP 与 Rocq 的逻辑无关，`Faithful QuiverElements` 在这里无法被证明，并且通过此函子实现 `QuiverCategory` 的具体性在无公理的情况下是不可达的。是否有其他函子到 `Sets` 具体化 `QuiverCategory` 仍然是未解决的问题。作者尚未知道任何这样的函子，并且有一个结构上的悲观理由——在任何承载体上的逐点数据会一次性产生一个元素的等式，而目标需要一个与每条边瞬时一致的单一节点族——但没有提供不存在的证明。

 义务纪律：此文件设置了 `Obligation Tactic := idtac`，因此下面的每个证明都会引入自己的变量，并且没有一个依赖于程序生成的名称。
*)

#[local] Existing Instance edgeset.
#[local] Obligation Tactic := idtac.

(* * ** Uniqueness of identity proofs on nodes / * ** 节点身份证明的唯一性 *)

(*
 The hypothesis discussed in the header: the node type of `Q` is a set in
 the sense of uniqueness of identity proofs. 

 --------
 标题中讨论的假设：`Q` 的节点类型在身份证明唯一性的意义上是一个集合。
*)
Definition NodeUIP (Q : Quiver) : Type :=
  ∀ (x y : @nodes Q) (p q : x = y), p = q.

(*
 Decidable node equality gives [NodeUIP] with no axiom, by Hedberg's theorem
 in the form `Eqdep_dec.UIP_dec`.  Construction/Quotient.v's `obj_uip` is
 the same step for the objects of a category. 

 --------
 可判定的节点相等通过 Hedberg 定理在没有公理的情况下给出 [NodeUIP]，以 `Eqdep_dec.UIP_dec` 的形式。Construction/Quotient.v 中的 `obj_uip` 对一个范畴的对象而言是相同的步骤。
*)
Lemma NodeDecEq_NodeUIP (Q : Quiver)
      (dec : ∀ x y : @nodes Q, {x = y} + {x ≠ y}) : NodeUIP Q.
Proof.
  intros x y p q.
  exact (UIP_dec dec p q).
Qed.

(** ** The vertex functor / ** 顶点函子 *)

(*
 Q ↦ its node type, under Leibniz equality; a homomorphism ↦ its node map.
 Functoriality is immediate: hom-equivalence in `QuiverCategory` carries a
 family of node equalities as its first component. 

 --------
 Q ↦ 它的节点类型，在莱布尼茨等式下；同态 ↦ 它的节点映射。
 函子性是显而易见的：`QuiverCategory` 中的同态等价携带一族节点等式作为其第一个分量。
*)
Program Definition QuiverVertices : QuiverCategory ⟶ Sets := {|
  fobj := fun Q => {| carrier   := @nodes Q
                    ; is_setoid := {| equiv        := @eq (@nodes Q)
                                    ; setoid_equiv := eq_equivalence |} |};
  fmap := fun Q Q' F => {| morphism := @fnodes Q Q' F |}
|}.
Next Obligation. intros Q Q' F a b Hab; simpl in *; subst; exact eq_refl. Qed.
Next Obligation.
  intros Q Q' F G HFG a.
  destruct HFG as [ne _].
  exact (ne a).
Qed.
Next Obligation. intros Q a; reflexivity. Qed.
Next Obligation. intros Q1 Q2 Q3 F G a; reflexivity. Qed.

(** ** The arrow functor / ** 箭头函子 *)

(*
 The arrows of a quiver, assembled from the endpoint-indexed edge families
 of Construction/Free/Quiver.v into a single type of triples. 

 --------
 箭袋中的箭矢，由 Construction/Free/Quiver.v 中以端点索引的边族组装成单一类型的三元组。
*)
Record QArrow (Q : Quiver) := {
  qsrc  : @nodes Q;
  qtgt  : @nodes Q;
  qedge : edges qsrc qtgt
}.

Arguments qsrc {Q} _.
Arguments qtgt {Q} _.
Arguments qedge {Q} _.

(* Move an edge along equalities of its two endpoints. / 沿着其两个端点的等式移动一条边。 *)
Definition qmove {Q : Quiver} {a a' b b' : @nodes Q}
           (p : a = a') (q : b = b') (e : edges a b) : edges a' b' :=
  Logic.transport (fun t => edges a' t) q
    (Logic.transport (fun s => edges s b) p e).

(*
 Two arrows are equivalent when their endpoints agree and, after moving the
 first edge onto the second's endpoints, the edges agree in the edge setoid.
 The endpoint comparison is `=` and not `≈` because Construction/Free/
 Quiver.v gives nodes no setoid structure of their own — only edges carry
 one; the edge comparison is `≈`, as the library's discipline requires. 

 --------
 当两个箭头的端点一致，并且在将第一个边移动到第二个边的端点后，这些边在边的等价集合中一致时，它们是等价的。端点比较使用 `=`，而不是 `≈`，因为 Construction/Free/Quiver.v 并没有赋予节点自身的等价结构——只有边才有；边的比较使用 `≈`，这是库的规范所要求的。
*)
Definition QArrow_equiv {Q : Quiver} (u v : QArrow Q) : Type :=
  { p : qsrc u = qsrc v &
  { q : qtgt u = qtgt v & qmove p q (qedge u) ≈ qedge v } }.

Lemma QArrow_equiv_refl {Q : Quiver} (u : QArrow Q) : QArrow_equiv u u.
Proof.
  destruct u as [a b e].
  exists eq_refl, eq_refl; simpl.
  reflexivity.
Qed.

Lemma QArrow_equiv_sym {Q : Quiver} (u v : QArrow Q) :
  QArrow_equiv u v → QArrow_equiv v u.
Proof.
  destruct u as [a b e], v as [a' b' e']; intros [p [q Hq]]; simpl in *.
  destruct p, q; simpl in *.
  exists eq_refl, eq_refl; simpl.
  now symmetry.
Qed.

Lemma QArrow_equiv_trans {Q : Quiver} (u v w : QArrow Q) :
  QArrow_equiv u v → QArrow_equiv v w → QArrow_equiv u w.
Proof.
  destruct u as [a b e], v as [a' b' e'], w as [a'' b'' e''].
  intros [p [q Hq]] [p' [q' Hq']]; simpl in *.
  destruct p, q, p', q'; simpl in *.
  exists eq_refl, eq_refl; simpl.
  now transitivity e'.
Qed.

#[export] Program Instance QArrow_Setoid (Q : Quiver) : Setoid (QArrow Q) := {|
  equiv := @QArrow_equiv Q
|}.
Next Obligation.
  intro Q; constructor.
  - exact (@QArrow_equiv_refl Q).
  - exact (@QArrow_equiv_sym Q).
  - exact (@QArrow_equiv_trans Q).
Qed.

(*
 Introduction forms for the arrow setoid, so that no proof below has to see
 through the `≈` notation to reach the underlying sigma type. 

 --------
 箭头集合同构的引入形式，这样下面的任何证明都不必通过 `≈` 符号来理解其底层的 sigma 类型。
*)
Lemma QArrow_intro {Q : Quiver} (u v : QArrow Q)
      (p : qsrc u = qsrc v) (q : qtgt u = qtgt v) :
  qmove p q (qedge u) ≈ qedge v → u ≈ v.
Proof. intro H; exact (existT _ p (existT _ q H)). Qed.

(* The common case: the endpoints agree on the nose. / 常见情况：端点完全一致。 *)
Lemma QArrow_intro_same {Q : Quiver} {a b : @nodes Q} (e e' : edges a b) :
  e ≈ e' →
  {| qsrc := a ; qtgt := b ; qedge := e |} ≈
  {| qsrc := a ; qtgt := b ; qedge := e' |}.
Proof. intro H; exact (existT _ eq_refl (existT _ eq_refl H)). Qed.

(*
 The coherence condition of `QuiverHomomorphismEquivalence`, restated as an
 equivalence of moved edges.  Both directions are proved by eliminating the
 two endpoint equalities, which is legitimate here because all four
 endpoints are universally quantified variables. 

 --------
 `QuiverHomomorphismEquivalence` 的相干条件，重新表述为移动边的等价性。两条方向都通过消去两个端点等式来证明，这在这里是合法的，因为所有四个端点都是全称量化变量。
*)
Lemma qmove_bridge {Q : Quiver} {a1 a2 b1 b2 : @nodes Q}
      (p : a1 = a2) (q : b1 = b2) (f : edges a1 b1) (g : edges a2 b2) :
  Logic.transport (fun t => edges a1 t) q f ≈
    Logic.transport_r (fun t => edges t b2) p g → qmove p q f ≈ g.
Proof. destruct p, q; unfold qmove, Logic.transport_r; simpl; trivial. Qed.

Lemma qmove_bridge_inv {Q : Quiver} {a1 a2 b1 b2 : @nodes Q}
      (p : a1 = a2) (q : b1 = b2) (f : edges a1 b1) (g : edges a2 b2) :
  qmove p q f ≈ g →
  Logic.transport (fun t => edges a1 t) q f ≈
    Logic.transport_r (fun t => edges t b2) p g.
Proof. destruct p, q; unfold qmove, Logic.transport_r; simpl; trivial. Qed.

(* The action of a homomorphism on arrows. / 同态对箭头的作用。 *)
Definition qarrow_map {Q Q' : Quiver} (F : QuiverHomomorphism Q Q')
           (u : QArrow Q) : QArrow Q' :=
  {| qsrc  := F (qsrc u)
   ; qtgt  := F (qtgt u)
   ; qedge := @fedgemap _ _ F _ _ (qedge u) |}.

(* The arrow map respects the arrow setoid. / 箭头映射遵守箭头集合的等价关系。 *)
Lemma qarrow_map_respects {Q Q' : Quiver} (F : QuiverHomomorphism Q Q')
      (u v : QArrow Q) : u ≈ v → qarrow_map F u ≈ qarrow_map F v.
Proof.
  destruct u as [a b e], v as [a' b' e']; intros [p [q Hq]]; simpl in *.
  destruct p, q; simpl in *.
  unfold qarrow_map; simpl.
  apply QArrow_intro_same.
  now apply (@fedgemap_respects _ _ F).
Qed.

(* Two homomorphisms that are equivalent agree on every arrow. / 两个等价的同态在每一条箭头上都一致。 *)
Lemma qarrow_map_agrees {Q Q' : Quiver} (F G : Q ~{QuiverCategory}~> Q')
      (HFG : F ≈ G) (u : QArrow Q) : qarrow_map F u ≈ qarrow_map G u.
Proof.
  destruct HFG as [ne coh].
  apply (QArrow_intro (qarrow_map F u) (qarrow_map G u)
                      (ne (qsrc u)) (ne (qtgt u))).
  apply qmove_bridge, coh.
Qed.

Program Definition QuiverArrows : QuiverCategory ⟶ Sets := {|
  fobj := fun Q => {| carrier := QArrow Q ; is_setoid := QArrow_Setoid Q |};
  fmap := fun Q Q' F => {| morphism := qarrow_map F |}
|}.
Next Obligation. intros Q Q' F u v Huv; now apply qarrow_map_respects. Qed.
Next Obligation. intros Q Q' F G HFG u; now apply qarrow_map_agrees. Qed.
Next Obligation. intros Q u; destruct u as [a b e]; reflexivity. Qed.
Next Obligation.
  intros Q1 Q2 Q3 F G u; destruct u as [a b e]; reflexivity.
Qed.

(** ** The disjoint-union functor / ** 不相交并集函子 *)

(*
 Riehl's V ⊎ E: the elements of a quiver are its vertices and its arrows.
 Vertices and arrows are never identified with one another. 

 --------
 Riehl 的 V ⊎ E：一个箭袋的元素是它的顶点和箭头。
 顶点和箭头永远不会互相认同。
*)
Definition QElt (Q : Quiver) : Type := (@nodes Q + QArrow Q)%type.

Definition QElt_equiv {Q : Quiver} (z w : QElt Q) : Type :=
  match z, w with
  | Datatypes.inl x, Datatypes.inl y => x = y
  | Datatypes.inr u, Datatypes.inr v => QArrow_equiv u v
  | _, _ => False
  end.

#[export] Program Instance QElt_Setoid (Q : Quiver) : Setoid (QElt Q) := {|
  equiv := @QElt_equiv Q
|}.
Next Obligation.
  intro Q; constructor.
  - intros [x|u]; simpl.
    + reflexivity.
    + apply QArrow_equiv_refl.
  - intros [x|u] [y|v]; simpl; try contradiction.
    + intro Hxy; now symmetry.
    + apply QArrow_equiv_sym.
  - intros [x|u] [y|v] [z|w]; simpl; try contradiction.
    + intros H1 H2; now transitivity y.
    + apply QArrow_equiv_trans.
Qed.

Definition qelt_map {Q Q' : Quiver} (F : QuiverHomomorphism Q Q')
           (z : QElt Q) : QElt Q' :=
  match z with
  | Datatypes.inl x => Datatypes.inl (F x)
  | Datatypes.inr u => Datatypes.inr (qarrow_map F u)
  end.

Program Definition QuiverElements : QuiverCategory ⟶ Sets := {|
  fobj := fun Q => {| carrier := QElt Q ; is_setoid := QElt_Setoid Q |};
  fmap := fun Q Q' F => {| morphism := qelt_map F |}
|}.
Next Obligation.
  intros Q Q' F z w Hzw.
  destruct z as [n|u], w as [n'|v]; simpl in *; try contradiction.
  - now subst.
  - now apply qarrow_map_respects.
Qed.
Next Obligation.
  intros Q Q' F G HFG z.
  destruct z as [n|u]; simpl.
  - destruct HFG as [ne _]; exact (ne n).
  - now apply qarrow_map_agrees.
Qed.
Next Obligation.
  intros Q z; destruct z as [n|u]; simpl.
  - reflexivity.
  - destruct u as [a b e]; apply QArrow_equiv_refl.
Qed.
Next Obligation.
  intros Q1 Q2 Q3 F G z; destruct z as [n|u]; simpl.
  - reflexivity.
  - destruct u as [a b e]; apply QArrow_equiv_refl.
Qed.

(*
 The positive half of Riehl's example, at the scope disclosed in the header:
 a quiver homomorphism is determined by its action on vertices and arrows
 together, once the target's node type satisfies uniqueness of identity
 proofs.  The node summand supplies the node family; the arrow summand
 supplies the coherence, after [NodeUIP] identifies its own endpoint
 equalities with the ones the node summand chose. 

 --------
 Riehl 示例的正半部分，在标题中披露的范围内：
 一个箭袋同态由其对顶点和箭头的作用共同决定，一旦目标的节点类型满足身份证明的唯一性。节点直和提供节点族；箭头直和提供相干性，在 [NodeUIP] 将其自身的端点等式与节点直和选择的等式对应后。
*)
Theorem QuiverElements_faithful_under_NodeUIP
        {Q Q' : QuiverCategory} (uip : NodeUIP Q')
        (F G : Q ~{QuiverCategory}~> Q') :
  fmap[QuiverElements] F ≈ fmap[QuiverElements] G → F ≈ G.
Proof.
  intro H.
  (* The node family, read off the vertex summand. / 节点族，从顶点直和中读出。 *)
  unshelve refine (existT _ (fun x => H (Datatypes.inl x)) _).
  intros x y f; simpl.
  (* The arrow summand at the arrow (x, y, f). / 箭头 (x, y, f) 处的箭头和数。 *)
  pose proof (H (Datatypes.inr {| qsrc := x; qtgt := y; qedge := f |})) as Ha.
  simpl in Ha.
  destruct Ha as [ps [pt Hc]].
  (*
 [NodeUIP] replaces the arrow summand's endpoint equalities by the ones
 the vertex summand supplied. 

 --------
 [NodeUIP] 用顶点项提供的端点等式替换箭头项的端点等式。
*)
  rewrite (uip _ _ ps (H (Datatypes.inl x))) in Hc.
  rewrite (uip _ _ pt (H (Datatypes.inl y))) in Hc.
  exact (qmove_bridge_inv _ _ _ _ Hc).
Qed.

(* * ** Witness quivers, and the two negative results / * ** 目击者颤抖，以及两个负面结果 *)

(*
 One node carrying two parallel loops.  A homomorphism out of it is a choice
 of node and a map on the two loops, so the node data cannot see the loop
 data — this is what defeats the vertex functor. 

 --------
 一个节点携带两个平行的环。从它出的同态是节点的选择以及两个环上的映射，所以节点数据无法看到环数据——这就是击败顶点函子的原因。
*)
Definition LoopQuiver : Quiver :=
  Build_Quiver_Standard_Eq poly_unit (fun _ _ => bool).

(*
 The loop-swapping endomorphism: identity on the single node, negation on
 the two loops. 

 --------
 环交换自同态：在单个节点上为恒等，在两个环上为取反。
*)
Program Definition loop_swap : LoopQuiver ~{QuiverCategory}~> LoopQuiver := {|
  fnodes   := Datatypes.id;
  fedgemap := fun _ _ => negb
|}.

(*
 Transport along a constant type family is the identity.  The edge family of
 [LoopQuiver] is constant, so every transport appearing in its
 hom-equivalence disappears, whatever equality proof it is taken along. 

 --------
 沿着常量类型族的传输是恒等的。[LoopQuiver] 的边族是常量的，所以在它的同构等价中出现的每个传输都会消失，无论沿着哪种等式证明进行。
*)
Lemma transport_const {A B : Type} {a a' : A} (p : a = a') (b : B) :
  Logic.transport (fun _ : A => B) p b = b.
Proof. destruct p; reflexivity. Qed.

(*
 The identity and [loop_swap] are DISTINCT in the hom-setoid of
 `QuiverCategory`: whatever node equality is offered, the coherence
 condition would force `true = negb true`. 

 --------
 在 `QuiverCategory` 的同态集合中，恒等式和 [loop_swap] 是不同的：无论提供什么节点等式，一致性条件都会迫使 `true = negb true`。
*)
Lemma loop_swap_distinct :
  @id QuiverCategory LoopQuiver ≈ loop_swap → False.
Proof.
  intros [ne coh].
  specialize (coh ttt ttt true).
  simpl in coh.
  unfold Logic.transport_r in coh.
  rewrite !transport_const in coh.
  discriminate.
Qed.

(*
 [QArrow] and [QuiverArrows] are not degenerate: [LoopQuiver] has two
 arrows, distinct in [QArrow_Setoid].  Without this the arrow functor could
 be the constant empty functor and [QuiverArrows_not_Faithful] below would
 be uninformative. 

 --------
 [QArrow] 和 [QuiverArrows] 不是退化的：[LoopQuiver] 有两个箭头，在 [QArrow_Setoid] 中是不同的。没有这个，箭头函子可能是恒等的空函子，下面的 [QuiverArrows_not_Faithful] 将没有信息价值。
*)
Definition loop_arrow (b : bool) : QArrow LoopQuiver :=
  Build_QArrow LoopQuiver ttt ttt b.

Lemma LoopQuiver_arrows_distinct :
  QArrow_equiv (loop_arrow true) (loop_arrow false) → False.
Proof.
  intros [p [q Hq]].
  unfold qmove, loop_arrow in Hq; simpl in Hq.
  rewrite !transport_const in Hq.
  discriminate.
Qed.

(*
 Riehl's first negative: the vertex functor is not faithful.  The identity
 and [loop_swap] have the same node map. 

 --------
 Riehl 的第一个负面结论：顶点函子不是忠实的。恒等映射和 [loop_swap] 有相同的节点映射。
*)
Theorem QuiverVertices_not_Faithful : Faithful QuiverVertices → False.
Proof.
  intro HF.
  apply loop_swap_distinct.
  apply (fmap_inj (F:=QuiverVertices)).
  simpl; intro x.
  reflexivity.
Qed.

(*
 Two nodes and no edges.  A homomorphism out of it is a pair of nodes and no
 edge data at all — this is what defeats the arrow functor. 

 --------
 两个节点，没有边。从它出来的一个同态是两个节点，根本没有边的数据——这就是箭头函子被击败的原因。
*)
Definition DiscQuiver : Quiver :=
  Build_Quiver_Standard_Eq bool (fun _ _ => Empty_set).

(* The node-swapping endomorphism of [DiscQuiver]. / [DiscQuiver] 的节点交换自同态。 *)
Program Definition disc_swap : DiscQuiver ~{QuiverCategory}~> DiscQuiver := {|
  fnodes   := negb;
  fedgemap := fun _ _ => Datatypes.id
|}.

(*
 The identity and [disc_swap] are DISTINCT in the hom-setoid: any node
 family would have to prove `true = negb true`. 

 --------
 在同态集内，身份和 [disc_swap] 是不同的：任何节点族都必须证明 `true = negb true`。
*)
Lemma disc_swap_distinct :
  @id QuiverCategory DiscQuiver ≈ disc_swap → False.
Proof.
  intros [ne coh].
  pose proof (ne true) as Hne.
  simpl in Hne.
  discriminate.
Qed.

(*
 Riehl's second negative: the arrow functor is not faithful.  The identity
 and [disc_swap] have the same action on arrows, [DiscQuiver] having none. 

 --------
 Riehl 的第二个否定：箭头函子不是忠实的。恒等和 [disc_swap] 在箭头上的作用相同，而 [DiscQuiver] 没有作用。
*)
Theorem QuiverArrows_not_Faithful : Faithful QuiverArrows → False.
Proof.
  intro HF.
  apply disc_swap_distinct.
  apply (fmap_inj (F:=QuiverArrows)).
  simpl; intros [a b e].
  destruct e.
Qed.

(*
   * ** The full subcategory of set-quivers, and its concreteness 

   --------
   * ** 集合箭图的完整子范畴及其具体性
*)

(*
 Quivers whose node type satisfies uniqueness of identity proofs — Riehl's
 quivers, whose vertices form a set.  Every morphism between two of them is
 retained ([SetQuivers_Full]), so this is a full subcategory in the sense of
 Construction/Subcategory.  [SetQuivers_Full] is recorded because a reader
 will want it, but no proof below consumes it: what the results actually
 rest on is that [Sub]'s hom-setoid is DEFINITIONALLY the base one, so no
 transfer lemma is needed.v.  Its objects are PAIRS of a quiver and a
 [NodeUIP] witness, so the object map of the inclusion forgets a proof
 component and injectivity of that map is NOT claimed; what is used below is
 only that the inclusion is faithful (and full, by [SetQuivers_Full]). 

 --------
 满足身份唯一性证明节点类型的箭袋——Riehl 的箭袋，其顶点形成一个集合。它们之间的每个态射都被保留（[SetQuivers_Full]），所以这是一个全子范畴，按照 Construction/Subcategory 的意义。[SetQuivers_Full] 被记录下来，因为读者会需要它，但下面没有证明使用它：实际依赖的结果是 [Sub] 的同态集合是定义上与基础集合相同，所以不需要转移引理。它的对象是一个箭袋与 [NodeUIP] 证据对的形式，因此包含映射的对象映射会忘记一个证明分量，并且不声称该映射是单射；下面使用的只是包含是忠实的（并且全的，由 [SetQuivers_Full]）。
*)
Program Definition SetQuivers : Subcategory QuiverCategory := {|
  sobj := NodeUIP;
  shom := fun _ _ _ _ _ => poly_unit
|}.
Next Obligation. intros; exact ttt. Qed.
Next Obligation. intros; exact ttt. Qed.

Definition SetQuiverCat : Category := Sub QuiverCategory SetQuivers.

Lemma SetQuivers_Full : Full QuiverCategory SetQuivers.
Proof. intros x y ox oy f; exact ttt. Qed.

(* The three functors, restricted along the inclusion. / 沿着包含限制的三个函子。 *)
Definition SetQuiverVertices : SetQuiverCat ⟶ Sets :=
  QuiverVertices ◯ Incl QuiverCategory SetQuivers.

Definition SetQuiverArrows : SetQuiverCat ⟶ Sets :=
  QuiverArrows ◯ Incl QuiverCategory SetQuivers.

Definition SetQuiverElements : SetQuiverCat ⟶ Sets :=
  QuiverElements ◯ Incl QuiverCategory SetQuivers.

(*
 Both witness quivers are set-quivers, by Hedberg from decidable node
 equality. 

 --------
 两个见证振动都是由 Hedberg 根据可判定的节点等式定义的集合振动。
*)
Lemma LoopQuiver_NodeUIP : NodeUIP LoopQuiver.
Proof.
  apply NodeDecEq_NodeUIP.
  intros x y; destruct x, y; left; reflexivity.
Qed.

Lemma DiscQuiver_NodeUIP : NodeUIP DiscQuiver.
Proof.
  apply NodeDecEq_NodeUIP.
  intros x y; destruct x, y;
    solve [ left; reflexivity | right; intro Hxy; discriminate ].
Qed.

Definition LoopSetQuiver : SetQuiverCat := (LoopQuiver; LoopQuiver_NodeUIP).
Definition DiscSetQuiver : SetQuiverCat := (DiscQuiver; DiscQuiver_NodeUIP).

(*
 The two negatives survive the restriction: the witnesses are set-quivers,
 so all of Example 1.6.19 takes place inside [SetQuiverCat]. 

 --------
 这两个否定克服了限制：证人是集合箭袋，因此示例 1.6.19 的所有内容都发生在 [SetQuiverCat] 内。
*)
Theorem SetQuiverVertices_not_Faithful : Faithful SetQuiverVertices → False.
Proof.
  intro HF.
  apply loop_swap_distinct.
  exact (fmap_inj (F:=SetQuiverVertices)
                  (x:=LoopSetQuiver) (y:=LoopSetQuiver)
                  (id; ttt) (loop_swap; ttt) (fun n => eq_refl)).
Qed.

Theorem SetQuiverArrows_not_Faithful : Faithful SetQuiverArrows → False.
Proof.
  intro HF.
  apply disc_swap_distinct.
  unshelve refine (fmap_inj (F:=SetQuiverArrows)
                            (x:=DiscSetQuiver) (y:=DiscSetQuiver)
                            (id; ttt) (disc_swap; ttt) _).
  simpl; intros [a b e]; destruct e.
Qed.

(*
 The positive half, unconditionally on [SetQuiverCat]: the [NodeUIP] witness
 the theorem needs is carried by the target object. 

 --------
 正半部分，无条件地在 [SetQuiverCat] 上：定理所需的 [NodeUIP] 证据由目标对象携带。
*)
#[export] Instance SetQuiverElements_Faithful : Faithful SetQuiverElements.
Proof.
  constructor; intros x y f g Hfg.
  exact (QuiverElements_faithful_under_NodeUIP `2 y `1 f `1 g Hfg).
Qed.

(*
 Riehl's Example 1.6.19: quivers are concrete, by way of the disjoint union
 of their vertices and their arrows.  Neither summand alone would do. 

 --------
 Riehl的例子1.6.19：通过顶点和箭头的离散并集，quiver是具体的。单独的任一和都不行。
*)
#[export] Instance SetQuiver_Concrete : Concrete SetQuiverCat := {|
  underlying          := SetQuiverElements;
  underlying_faithful := SetQuiverElements_Faithful
|}.

(*
 Non-vacuity of [SetQuiver_Concrete]: the hom-setoids it is injective on are
 not trivial.  [loop_swap_distinct] and [disc_swap_distinct] each exhibit
 two parallel morphisms that differ, and equivalence in [SetQuiverCat] is by
 definition equivalence of the underlying quiver homomorphisms. 

 --------
 [SetQuiver_Concrete] 的非空性：它在其上是单射的同态集合不是平凡的。[loop_swap_distinct] 和 [disc_swap_distinct] 各自展示了两个不同的平行态射，而 [SetQuiverCat] 中的等价定义上是其底层弦图同态的等价。
*)
Lemma SetQuiverCat_two_arrows :
  @id SetQuiverCat LoopSetQuiver ≈ (loop_swap; ttt) → False.
Proof. exact loop_swap_distinct. Qed.

(* ------------------------------------------------------------------------ *)
(*
   * ** The node-UIP hypothesis is necessary, not merely convenient 

   --------
   * ** 节点-UIP假设是必要的，而不仅仅是方便的
*)

(*
 The restriction to `NodeUIP` above is forced. If the disjoint-union
 functor were faithful on ALL quivers, UIP would follow — so, UIP being
 independent of Rocq's logic, that faithfulness is not provable and
 `Concrete QuiverCategory` is unreachable through this functor.

 The witness is a single quiver whose edges record BOTH endpoints:
 over a node type N with a distinguished c, take `edges x y := (c = x) *
 (c = y)`. Two endomorphisms constant at c differ by transporting the
 edge along a loop. The disjoint-union functor identifies them, because
 on the arrow summand it is enough to supply the loop itself. But
 equality in `QuiverCategory` demands ONE shared node family coherent
 with every edge simultaneously, and a single loop cannot satisfy the
 source constraint and the target constraint at once unless it is
 trivial. That last step is [uip_key] below, isolated so the arithmetic
 is visible. 

 --------
 上面对 `NodeUIP` 的限制是强制的。如果离散并联合函子在所有箭图上都是忠实的，那么 UIP 将随之成立——因此，由于 UIP 独立于 Rocq 的逻辑，这种忠实性是不可证明的，而通过此函子无法到达 `Concrete QuiverCategory`。证人是一个单一的箭筒，其边记录了两个端点：
 对于带有一个特殊节点 c 的节点类型 N，取 `edges x y := (c = x) * (c = y)`。两个在 c 上恒定的自同态通过沿环传输边而不同。互不相交的并集函子将它们识别出来，因为在箭头分量上只需要提供环本身。但在  `QuiverCategory` 中的相等要求有一个共享的节点族，同时与每条边一致，而单一环无法同时满足源约束和目标约束，除非它是平凡的。最后一步是下面的  [uip_key] ，单独列出以便算式清晰可见。
*)

Lemma uip_transport_id {A} {c a : A} (p : c = a) :
  Logic.transport (fun s => c = s) p eq_refl = p.
Proof. destruct p; reflexivity. Qed.

Lemma uip_transport_l {A} {c : A} {K : Type} {a a2 : A}
      (p : a = a2) (u : c = a) (v : K) :
  Logic.transport (fun s => ((c = s) * K)%type) p (u, v)
  = (Logic.transport (fun s => c = s) p u, v).
Proof. destruct p; reflexivity. Qed.

Lemma uip_transport_r {A} {c : A} {K : Type} {b b2 : A}
      (q : b = b2) (u : K) (v : c = b) :
  Logic.transport (fun t => (K * (c = t))%type) q (u, v)
  = (u, Logic.transport (fun t => c = t) q v).
Proof. destruct q; reflexivity. Qed.

(*
 One shared loop cannot meet the source and the target constraint at
 once unless the loop it is compared against is trivial. 

 --------
 除非所比较的循环是平凡的，否则一个共享循环无法同时满足源和目标约束。
*)
Lemma uip_key {A} {c : A} (shared loop : c = c) :
  Logic.transport (fun t : A => ((c = c) * (c = t))%type) shared
    (eq_refl, eq_refl)
  = Logic.transport (fun s : A => ((c = s) * (c = c))%type) (eq_sym shared)
      (Logic.transport (fun s : A => ((c = s) * (c = c))%type) loop
         (eq_refl, eq_refl))
  → loop = eq_refl.
Proof.
  rewrite (uip_transport_r (c:=c) (K:=(c=c)) shared eq_refl eq_refl).
  rewrite (uip_transport_l (c:=c) (K:=(c=c)) loop eq_refl eq_refl).
  rewrite (uip_transport_l (c:=c) (K:=(c=c)) (eq_sym shared)
                (Logic.transport (fun s => c = s) loop eq_refl) eq_refl).
  rewrite !uip_transport_id.
  intro H.
  pose proof (f_equal fst H) as H1.
  pose proof (f_equal snd H) as H2.
  simpl in H1, H2.
  rewrite H2 in H1.
  simpl in H1.
  exact (eq_sym H1).
Qed.

Section UIPNecessity.

Context (N : Set) (c : N) (loop : c = c).

(*
 The probe quiver: edges from x to y record proofs that c is BOTH x and
 y, so an edge constrains its two endpoints independently. 

 --------
 探针振动：从 x 到 y 的边记录了 c 同时是 x 和 y 的证明，因此一条边独立地约束它的两个端点。
*)
Definition UIPQuiver : Quiver :=
  Build_Quiver_Standard_Eq N (fun x y => ((c = x) * (c = y))%type).

Definition uip_edge_id : @edges UIPQuiver c c := (eq_refl, eq_refl).
Definition uip_edge_moved : @edges UIPQuiver c c :=
  @qmove UIPQuiver c c c c loop eq_refl uip_edge_id.

Program Definition uip_hom_id : UIPQuiver ~{QuiverCategory}~> UIPQuiver :=
  {| fnodes := fun _ => c ; fedgemap := fun _ _ _ => uip_edge_id |}.
Program Definition uip_hom_moved : UIPQuiver ~{QuiverCategory}~> UIPQuiver :=
  {| fnodes := fun _ => c ; fedgemap := fun _ _ _ => uip_edge_moved |}.

(* The disjoint-union functor cannot tell them apart. / 不相交并集函子无法区分它们。 *)
Lemma uip_homs_agree_on_elements :
  fmap[QuiverElements] uip_hom_id ≈ fmap[QuiverElements] uip_hom_moved.
Proof.
  intro z; destruct z as [n|u]; simpl.
  - reflexivity.
  - destruct u as [a b e]; simpl.
    exact (existT _ loop (existT _ eq_refl eq_refl)).
Qed.

(*
 But the quiver category equates them only when the loop is trivial. 

 --------
 但是只有当环路是平凡的时候，箭袋类别才会将它们等同起来。
*)
Lemma uip_homs_equal_forces_trivial :
  uip_hom_id ≈ uip_hom_moved → loop = eq_refl.
Proof.
  intros [shared coh].
  specialize (coh c c (eq_refl, eq_refl)).
  simpl in coh.
  unfold Logic.transport_r, uip_edge_moved, qmove, uip_edge_id in coh;
    simpl in coh.
  exact (uip_key (shared c) loop coh).
Qed.

End UIPNecessity.

(*
 Hence the hypothesis under which [QuiverElements] was proved faithful is
 exactly what that faithfulness would give back. 

 --------
 因此，在该假设下证明 [QuiverElements] 是忠实的，正是那种忠实性所能回馈的东西。
*)
Theorem faithful_QuiverElements_implies_UIP :
  Faithful QuiverElements →
  ∀ (N : Set) (c : N) (loop : c = c), loop = eq_refl.
Proof.
  intros HF N c loop.
  apply (uip_homs_equal_forces_trivial N c loop).
  apply (fmap_inj (F:=QuiverElements)).
  apply uip_homs_agree_on_elements.
Qed.
