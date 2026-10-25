Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Displayed.
Require Import Category.Construction.Displayed.Total.
Require Import Category.Construction.Indexed.

Generalizable All Variables.

(** * The Grothendieck construction / * 格罗滕迪克构造 *)

(*
 nLab:      https://ncatlab.org/nlab/show/Grothendieck+construction
 Wikipedia: https://en.wikipedia.org/wiki/Grothendieck_construction

 The Grothendieck construction assembles an indexed category
 [A : IndexedCat B] (Construction/Indexed.v, the coherent
 "pseudofunctor-lite") into a category over [B], presented as a displayed
 category (Theory/Displayed.v) whose total category
 (Construction/Displayed/Total.v) is the classical ∫ A:

 - an object over [x : B] is an object of the fibre [idx_fib A x];
 - a morphism over [f : x ~> y] from [dx] to [dy] is a fibre morphism
 [idx_map A f dx ~> dy] — reindex forward along [f], then compare in
 the target fibre;
 - the identity over [id] is the unit iso [idx_id]; composition over
 [f ∘ g] reindexes the inner leg forward along [f] and mediates with
 the chosen composition iso [idx_comp];
 - transport along [e : f ≈ g] precomposes with the inverse of the
 mediator iso [idx_resp e], recentring the source from [idx_map g dx]
 to [idx_map f dx].

 Every displayed law is discharged from a corresponding coherence field
 of [IndexedCat]: proof irrelevance and functoriality of transport come
 from [idx_resp_id] and [idx_resp_trans]; the unit laws from
 [idx_unit_left]/[idx_unit_right] plus naturality of [idx_id];
 associativity from the cocycle [idx_cocycle] plus naturality of
 [idx_comp] in the fibre argument; and the transport/composition
 interchange from compatibility of [idx_comp] with [idx_resp]
 ([idx_comp_resp_l]/[idx_comp_resp_r]).  This file is the payoff of the
 coherent-data design: a bare [Functor B Cat] could not supply the
 cross-application equations these proofs consume (see the honesty note
 in Construction/Indexed.v).

 Following the sanctioned staging for this construction, each displayed
 law is first proven as a standalone lemma about [IndexedCat] — stated
 over an arbitrary proof of the base-law instance it transports along,
 which is harmless by proof irrelevance of [idx_resp] — and the
 [Displayed] record is then assembled from the named lemmas.

 [Grothendieck A] is the total category ∫ A, and [Grothendieck_Proj] is
 the evident projection ∫ A ⟶ B, taking an object over [x] to [x]. 

 --------
 nLab：       https://ncatlab.org/nlab/show/Grothendieck+construction 
 维基百科：  https://en.wikipedia.org/wiki/Grothendieck_construction 

 Grothendieck 构造将一个索引范畴
 [A : IndexedCat B]  （Construction/Indexed.v，连贯的“伪函子轻量版”）组装成一个位于  [B]  上的范畴，呈现为一个显示范畴（Theory/Displayed.v），其总范畴（Construction/Displayed/Total.v）是经典的 ∫ A：- 在  [x : B] 上的一个对象是纤维  [idx_fib A x] 上的一个对象；
 - 从  [dx] 到  [dy] 的  [f : x ~> y] 上的一个态射是纤维态射  [idx_map A f dx ~> dy] — 沿  [f] 前重索引，然后在目标纤维中比较；
 - 在  [id] 上的恒等是单位同构  [idx_id]；在  [f ∘ g] 上的复合沿  [f] 前重索引内侧腿，并通过选择的复合同构  [idx_comp] 进行调解；
 - 沿  [e : f ≈ g] 的平移与调解同构  [idx_resp e] 的逆前复合，将源从  [idx_map g dx] 重新集中到  [idx_map f dx] 。每一个显示的定律都来自对应的连贯场 [IndexedCat]：证明不相关性和传输的函子性来自 [idx_resp_id] 和 [idx_resp_trans]；单位定律来自 [idx_unit_left] / [idx_unit_right] 加上 [idx_id] 的自然性；结合性来自 [idx_cocycle] 的 Cocycle 加上 [idx_comp] 在纤维参数下的自然性；传输/组合交换来自 [idx_comp] 与 [idx_resp] 的兼容性（[idx_comp_resp_l] / [idx_comp_resp_r]）。该文件是连贯数据设计的成果：一个裸露的 [Functor B Cat] 无法提供这些证明所使用的跨应用方程（见 Construction/Indexed.v 中的诚实性说明）。根据这一构造的批准阶段，每条展示的定律首先作为关于 [IndexedCat] 的独立引理被证明——这是在其所携带的基础定律实例的任意证明上陈述的，由于 [idx_resp] 的证明不可相关性，这是无害的——然后 [Displayed] 记录由命名的引理组装而成。

 [Grothendieck A] 是总范畴 ∫ A，[Grothendieck_Proj] 是明显的投射 ∫ A ⟶ B，将 [x] 上的对象映射到 [x]。
*)

(*
 Where the construction comes from, and what it is for

 nLab:  https://ncatlab.org/nlab/show/Grothendieck+construction
 Text:  Grothendieck, "Catégories fibrées et descente", SGA 1,
 Exposé VI, Séminaire de Géométrie Algébrique du Bois Marie
 1960–61, Lecture Notes in Mathematics 224, Springer 1971
 Notes: Vistoli, "Grothendieck topologies, fibered categories and
 descent theory", in FGA Explained, AMS Surveys and
 Monographs 123, 2005 (arXiv:math/0412512)

 The construction flattens an indexed family of categories into a
 single category over the base.  The external, indexed view presents
 the data as a pseudofunctor B ⟶ Cat, assigning a fibre to each
 object and a reindexing functor to each morphism; the internal,
 fibred view presents the same content as one total category with a
 projection that records the index of each object.  It is due to
 Alexander Grothendieck, who introduced fibered categories to
 organize descent in algebraic geometry: Exposé VI of SGA 1 develops
 them from the 1960–61 seminar, and Jean Giraud carried the theory
 further in the years that followed.

 The reorganization is more than a convenience.  Passing to the total
 category is one half of the Grothendieck correspondence, a
 2-equivalence between the indexed categories over B — the
 pseudofunctors into Cat — and the Grothendieck (op)fibrations over
 B.  Theory/Fibration.v is the fibred target of that correspondence;
 Construction/Grothendieck/Fibration.v shows [Grothendieck_Proj] to
 be a split opfibration with chosen lifts;
 Construction/Grothendieck/RoundTrip.v travels the reverse road,
 reconstructing an indexed category from a cleaving and assembling
 [RoundTrip_Equivalence]; and Construction/Grothendieck/Fiber.v
 confirms through [fiber_grothendieck_equiv] that the fibres of the
 total category recover the original [idx_fib].  In the descent
 setting where the notion began, a stack is exactly a pseudofunctor,
 or equivalently a fibration in groupoids, satisfying a descent
 condition for a Grothendieck topology.

 The construction is the categorification of the dependent sum.  Its
 total category [Grothendieck], built as [Total] of the displayed
 category [Grothendieck_Displayed], has for objects the dependent
 pairs (x; dx) of a base object and an object of its fibre, and
 [Grothendieck_Proj] is the first projection, exactly as a Σ-type
 projects onto its index.  This reading is why the file routes
 through the displayed primitive of Theory/Displayed.v (Ahrens,
 Lumsdaine, "Displayed Categories", Logical Methods in Computer
 Science 15(1), 2019): a displayed category records a family in
 dependent, fibered style, so the total category is assembled without
 ever comparing base objects for equality.  When the family does not
 vary the sum degenerates to a product, and
 Construction/Grothendieck/Strict.v proves
 [Grothendieck_Constant_iso], identifying the total category of a
 constant family with B ∏ D.

 Restricting the fibres to sets, viewed as discrete categories,
 recovers the category of elements el(F), whose projection is a
 discrete opfibration and whose objects pair an element of the
 functor with the object it lies over; this is the arena of the
 Yoneda lemma (Functor/Hom/Yoneda.v), and, read as data, rows that
 pair a table with a tuple, the projection recording which table
 each inhabits.  The same flattening organizes structures throughout
 mathematics.  It collects the modules over every ring into one
 category fibered over the ring, and realizes the semidirect product
 of groups as the total category of an action functor, pairs of a
 group element and a fibre element multiplying by a rule twisted by
 the action.  Taking nerves, Thomason identified the classifying
 space of the total category with the homotopy colimit of the
 diagram, the oplax colimit at the level of categories.  The
 construction further expresses a weighted colimit as an ordinary
 colimit, and in type theory it models the relationship between a
 type theory and a logic over that type theory. 

 --------
 构造的来源及其用途

 nLab: https://ncatlab.org/nlab/show/Grothendieck+construction
 文献: Grothendieck, 《Catégories fibrées et descente》, SGA 1,  
 第 VI 篇报告, Bois Marie 代数几何研讨会 1960–61, 
 数学讲义 224, Springer 1971
 注释: Vistoli, 《Grothendieck 拓扑、纤维范畴与下降理论》, 收录于 FGA Explained, AMS 调查与专著 123, 2005 (arXiv:math/0412512)该构造将一个索引类别族展平成一个基类别上的单一类别。外部的、索引视角将数据呈现为一个伪函子 B ⟶ Cat，为每个对象分配一个纤维，为每个态射分配一个重索引函子；内部的、纤维视角则将相同的内容呈现为一个总类别，并带有一个记录每个对象索引的投射。它归功于亚历山大·格罗滕迪克，他引入了纤维类别以组织代数几何中的下降理论：SGA 1 的 Exposé VI 从 1960–61 年的研讨会发展了它们，而让·吉罗随后进一步发展了这一理论。重组不仅仅是一种便利。通过总范畴是 Grothendieck 对应的一半，这是在 B 上的指示范畴——即到 Cat 的伪函子——与 B 上的 Grothendieck (对)纤维化之间的 2-等价。Theory/Fibration.v 是该对应的纤维目标；Construction/Grothendieck/Fibration.v 展示了 [Grothendieck_Proj] 是一个具有选定抬升的分裂对纤维化；Construction/Grothendieck/RoundTrip.v 走反方向的道路，从一个切分重建指示范畴并组装 [RoundTrip_Equivalence]；而 Construction/Grothendieck/Fiber.v 通过 [fiber_grothendieck_equiv] 证实总范畴的纤维恢复了原来的 [idx_fib] 。在这一起源于下行环境的概念中，层叠（stack）恰好就是一个伪函子，或者等价地说，是一个群范畴上的纤维化，满足一个关于格罗滕迪克拓扑的下行条件。该构造是依赖和的范畴化。其总范畴 [Grothendieck] 构建为显示范畴 [Grothendieck_Displayed] 的 [Total]，对象是基对象和其纤维对象的依赖对 (x; dx)，而 [Grothendieck_Proj] 是第一投影，正如 Σ 型投影到其索引一样。这种理解是文件通过 Theory/Displayed.v（Ahrens, Lumsdaine, “显示范畴”, Logical Methods in Computer Science 15(1), 2019）的显示原语路由的原因：显示范畴以依赖的、纤维化的方式记录一个族，因此总范畴的组装过程中从未比较过基对象的相等性。当这个族不发生变化时，和退化为一个积，并且 Construction/Grothendieck/Strict.v 证明了 [Grothendieck_Constant_iso]，将一个常值族的总范畴与 B ∏ D 识别起来。将纤维限制在集合上，视为离散范畴，可以恢复元素范畴 el(F)，其投影是一个离散余纤维化，其对象将函子中的元素与其所在的对象配对；这是 Yoneda 引理（Functor/Hom/Yoneda.v）的领域，并且，如果作为数据读取，则是将表与一个元组配对的行，投影记录每个元组属于哪个表。同样的扁平化方法组织了整个数学中的结构。它将每个环上的模收集到一个纤维化在该环上的范畴中，并且将群的半直积实现为一个作用函子的总范畴，群元素与纤维元素按作用扭曲的规则相乘。通过取神经，Thomason 将总体范畴的分类空间识别为图的同伦余极限，即范畴层面的松弛余极限。该构造进一步将加权余极限表示为普通余极限，并且在类型理论中，它模拟了类型理论与该类型理论上逻辑之间的关系。
*)

#[local] Obligation Tactic := idtac.

Section Grothendieck.

Context {B : Category}.
Context (A : IndexedCat B).

(*
   * ** Reindexing preserves isomorphisms

   [idx_map A f] carries fibre isos to fibre isos.  This is the generic
   fact that functors preserve isomorphisms, packaged with a stable head
   so the iso-level inversions below can name its components. 

   --------
   * ** 重建索引保持同构

   [idx_map A f] 将纤维同构传递到纤维同构。这是函子保持同构的通用事实，与一个稳定的头部一起打包，因此下面的同构级反转可以命名其分量。
*)

Program Definition idx_map_iso {x y : B} (f : x ~> y) {a b : idx_fib A x}
  (i : a ≅ b) : idx_map A f a ≅ idx_map A f b := {|
  to   := fmap[idx_map A f] (to i);
  from := fmap[idx_map A f] (from i)
|}.
Next Obligation.
  intros; simpl.
  rewrite <- fmap_comp, iso_to_from.
  apply fmap_id.
Qed.
Next Obligation.
  intros; simpl.
  rewrite <- fmap_comp, iso_from_to.
  apply fmap_id.
Qed.

(*
   * ** The from-side coherence pack

   The displayed structure below writes its transports and mediators with
   [from]-components, so each coherence field of [IndexedCat] is consumed
   here in inverted orientation.  Inverting an equation between composites
   of isos is [to_equiv_implies_iso_equiv] applied at an [iso_compose]
   packaging of each side, projected to the [from] components — note the
   inverses compose in reverse order. 

   --------
   * ** 来自端的一致性包

   显示的结构如下，用 [from] 组件写出了它的传输器和中介，因此这里每个 [IndexedCat] 的一致性场都是以反向方式消耗的。在同构复合物之间求逆方程是将 [to_equiv_implies_iso_equiv] 应用于每一侧的 [iso_compose] 打包，然后投影到 [from] 组件——注意逆元按相反顺序组合。
*)

(*
 Transport inverses are proof-irrelevant, so [from] at [e] agrees with
 [to] at any proof [e'] of the reversed relation. 

 --------
 传输逆元是与证明无关的，所以 [from] 在 [e] 上与 [to] 在任意逆关系的证明 [e'] 上一致。
*)
Lemma idx_resp_from_flip {x y : B} {f g : x ~> y} (e : f ≈ g) (e' : g ≈ f)
  (a : idx_fib A x) :
  from (idx_resp A e a) ≈ to (idx_resp A e' a).
Proof.
  rewrite <- (idx_resp_to_sym A e a).
  apply idx_resp_irrel.
Qed.

(* [idx_comp_resp_l], inverted. / [idx_comp_resp_l]，倒置。 *)
Lemma idx_comp_resp_l_from {x y z : B} {f f' : y ~> z} (g : x ~> y)
  (e : f ≈ f') (e' : f ∘ g ≈ f' ∘ g) (a : idx_fib A x) :
  from (idx_resp A e (idx_map A g a)) ∘ from (idx_comp A f' g a)
    ≈ from (idx_comp A f g a) ∘ from (idx_resp A e' a).
Proof.
  exact (snd (to_equiv_implies_iso_equiv
    (iso_compose (idx_comp A f' g a) (idx_resp A e (idx_map A g a)))
    (iso_compose (idx_resp A e' a) (idx_comp A f g a))
    (idx_comp_resp_l A g e e' a))).
Qed.

(* [idx_comp_resp_r], inverted. / [idx_comp_resp_r]，倒置。 *)
Lemma idx_comp_resp_r_from {x y z : B} (f : y ~> z) {g g' : x ~> y}
  (e : g ≈ g') (e' : f ∘ g ≈ f ∘ g') (a : idx_fib A x) :
  fmap[idx_map A f] (from (idx_resp A e a)) ∘ from (idx_comp A f g' a)
    ≈ from (idx_comp A f g a) ∘ from (idx_resp A e' a).
Proof.
  exact (snd (to_equiv_implies_iso_equiv
    (iso_compose (idx_comp A f g' a) (idx_map_iso f (idx_resp A e a)))
    (iso_compose (idx_resp A e' a) (idx_comp A f g a))
    (idx_comp_resp_r A f e e' a))).
Qed.

(*
 [idx_unit_left] rearranged: cancelling the composition iso against its
 inverse isolates the mediator of the left unit law. 

 --------
 [idx_unit_left] 重排：将合成同构与其逆元相抵消，可以隔离左单位律的中介元。
*)
Lemma idx_unit_left_from {x y : B} (f : x ~> y) (a : idx_fib A x) :
  to (idx_id A (idx_map A f a)) ∘ from (idx_comp A (@id B y) f a)
    ≈ to (idx_resp A (id_left f) a).
Proof.
  rewrite <- (idx_unit_left A f a).
  rewrite <- comp_assoc.
  rewrite iso_to_from.
  apply id_right.
Qed.

(* [idx_unit_right] rearranged likewise. / [idx_unit_right] 同样重新排列。 *)
Lemma idx_unit_right_from {x y : B} (f : x ~> y) (a : idx_fib A x) :
  fmap[idx_map A f] (to (idx_id A a)) ∘ from (idx_comp A f (@id B x) a)
    ≈ to (idx_resp A (id_right f) a).
Proof.
  rewrite <- (idx_unit_right A f a).
  rewrite <- comp_assoc.
  rewrite iso_to_from.
  apply id_right.
Qed.

(* [idx_cocycle], inverted: the from-composites reverse. / [idx_cocycle]，反转：复合物的反向。 *)
Lemma idx_cocycle_from {w x y z : B} (f : y ~> z) (g : x ~> y) (h : w ~> x)
  (a : idx_fib A w) :
  from (idx_comp A f g (idx_map A h a)) ∘ from (idx_comp A (f ∘ g) h a)
    ≈ fmap[idx_map A f] (from (idx_comp A g h a))
        ∘ (from (idx_comp A f (g ∘ h) a)
             ∘ from (idx_resp A (comp_assoc f g h) a)).
Proof.
  exact (snd (to_equiv_implies_iso_equiv
    (iso_compose (idx_comp A (f ∘ g) h a) (idx_comp A f g (idx_map A h a)))
    (iso_compose (iso_compose (idx_resp A (comp_assoc f g h) a)
                              (idx_comp A f (g ∘ h) a))
                 (idx_map_iso f (idx_comp A g h a)))
    (idx_cocycle A f g h a))).
Qed.

(*
   * ** The displayed laws, one standalone lemma each

   Each lemma below is the exact shape of one law of the displayed
   category, with the data of the construction inlined and the transport
   proof held abstract: any proof of the relevant base relation works, by
   proof irrelevance of [idx_resp], and quantifying over it lets the
   record assembly below unify against whatever proof term the [Displayed]
   interface pins. 

   --------
   * ** 显示的定律，每个定律单独列出

   下面的每个定律都是显示类别中一条定律的精确形式，构造的数据被内联，传输证明保持抽象：相关基关系的任何证明都可使用，根据  [idx_resp] 的证明无关性，量化它使下方的记录组装能够与  [Displayed] 接口固定的任何证明项统一。
*)

Lemma Grothendieck_transport_trans {x y : B}
  {dx : idx_fib A x} {dy : idx_fib A y} {f g h : x ~> y}
  (e1 : f ≈ g) (e2 : g ≈ h) (e3 : f ≈ h) (ff : idx_map A f dx ~> dy) :
  (ff ∘ from (idx_resp A e1 dx)) ∘ from (idx_resp A e2 dx)
    ≈ ff ∘ from (idx_resp A e3 dx).
Proof.
  rewrite <- comp_assoc.
  rewrite (idx_resp_from_trans A e1 e2 dx).
  apply compose_respects.
  - reflexivity.
  - apply idx_resp_from_irrel.
Qed.

Lemma Grothendieck_transport_comp_l {x y z : B}
  {dx : idx_fib A x} {dy : idx_fib A y} {dz : idx_fib A z}
  {f f' : y ~> z} {g : x ~> y} (e : f ≈ f') (e' : f ∘ g ≈ f' ∘ g)
  (ff : idx_map A f dy ~> dz) (gg : idx_map A g dx ~> dy) :
  (ff ∘ from (idx_resp A e dy)) ∘ fmap[idx_map A f'] gg
      ∘ from (idx_comp A f' g dx)
    ≈ (ff ∘ fmap[idx_map A f] gg ∘ from (idx_comp A f g dx))
        ∘ from (idx_resp A e' dx).
Proof.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (from (idx_resp A e dy)) (fmap[idx_map A f'] gg)).
  rewrite <- (idx_resp_natural_from A e gg).
  rewrite <- !comp_assoc.
  rewrite (idx_comp_resp_l_from g e e' dx).
  reflexivity.
Qed.

Lemma Grothendieck_transport_comp_r {x y z : B}
  {dx : idx_fib A x} {dy : idx_fib A y} {dz : idx_fib A z}
  {f : y ~> z} {g g' : x ~> y} (e : g ≈ g') (e' : f ∘ g ≈ f ∘ g')
  (ff : idx_map A f dy ~> dz) (gg : idx_map A g dx ~> dy) :
  ff ∘ fmap[idx_map A f] (gg ∘ from (idx_resp A e dx))
     ∘ from (idx_comp A f g' dx)
    ≈ (ff ∘ fmap[idx_map A f] gg ∘ from (idx_comp A f g dx))
        ∘ from (idx_resp A e' dx).
Proof.
  rewrite fmap_comp.
  rewrite <- !comp_assoc.
  rewrite (idx_comp_resp_r_from f e e' dx).
  reflexivity.
Qed.

Lemma Grothendieck_did_left {x y : B}
  {dx : idx_fib A x} {dy : idx_fib A y} {f : x ~> y}
  (e : f ≈ @id B y ∘ f) (ff : idx_map A f dx ~> dy) :
  to (idx_id A dy) ∘ fmap[idx_map A (@id B y)] ff
     ∘ from (idx_comp A (@id B y) f dx)
    ≈ ff ∘ from (idx_resp A e dx).
Proof.
  rewrite (idx_resp_from_flip e (id_left f) dx).
  rewrite <- (idx_id_natural A ff).
  rewrite <- comp_assoc.
  rewrite (idx_unit_left_from f dx).
  reflexivity.
Qed.

Lemma Grothendieck_did_right {x y : B}
  {dx : idx_fib A x} {dy : idx_fib A y} {f : x ~> y}
  (e : f ≈ f ∘ @id B x) (ff : idx_map A f dx ~> dy) :
  ff ∘ fmap[idx_map A f] (to (idx_id A dx))
     ∘ from (idx_comp A f (@id B x) dx)
    ≈ ff ∘ from (idx_resp A e dx).
Proof.
  rewrite (idx_resp_from_flip e (id_right f) dx).
  rewrite <- comp_assoc.
  rewrite (idx_unit_right_from f dx).
  reflexivity.
Qed.

Lemma Grothendieck_assoc {w x y z : B}
  {dw : idx_fib A w} {dx : idx_fib A x} {dy : idx_fib A y} {dz : idx_fib A z}
  {f : y ~> z} {g : x ~> y} {h : w ~> x}
  (e : (f ∘ g) ∘ h ≈ f ∘ (g ∘ h))
  (ff : idx_map A f dy ~> dz) (gg : idx_map A g dx ~> dy)
  (hh : idx_map A h dw ~> dx) :
  ff ∘ fmap[idx_map A f]
         (gg ∘ fmap[idx_map A g] hh ∘ from (idx_comp A g h dw))
     ∘ from (idx_comp A f (g ∘ h) dw)
    ≈ (ff ∘ fmap[idx_map A f] gg ∘ from (idx_comp A f g dx)
          ∘ fmap[idx_map A (f ∘ g)] hh ∘ from (idx_comp A (f ∘ g) h dw))
        ∘ from (idx_resp A e dw).
Proof.
  rewrite (idx_resp_from_flip e (comp_assoc f g h) dw).
  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (from (idx_comp A f g dx))
                      (fmap[idx_map A (f ∘ g)] hh)).
  rewrite <- (idx_comp_natural_from A f g hh).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (from (idx_comp A f g (idx_map A h dw)))
                      (from (idx_comp A (f ∘ g) h dw))).
  rewrite (idx_cocycle_from f g h dw).
  rewrite <- !comp_assoc.
  rewrite (iso_from_to (idx_resp A (comp_assoc f g h) dw)).
  rewrite id_right.
  reflexivity.
Qed.

(*
   * ** The displayed category over B, its total category, the projection 

   --------
   * ** 显示的 B 类别，其总类别，投影
*)

(*
   【Grothendieck 构造展开】/ Grothendieck walkthrough
   （口吻对齐 Theory/Category.v；受众：Coq 小白 + 范畴论小白的 Haskell 程序员）

   1) 这是什么 / What this is
      把「索引范畴」A : IndexedCat B（每个 b 一个纤维范畴 + 沿箭头的重索引）
      摊平成一个总范畴 ∫ A，并带投影 ∫ A ⟶ B。
      Flatten an indexed family of categories into one total category over B.
      Haskell 直觉：像「依赖和」Σ (b : B). Fib(b)，态射还要带基态射与纤维态射。
      Like a dependent sum of categories, with reindexing in the morphisms.

   2) 两步交付 / Two steps
      Grothendieck_Displayed : Displayed B
        - dobj x      = 纤维 idx_fib A x 的对象
        - dhom … f    = idx_map A f dx ~> dy（先沿 f 前推再比）
        - did / dcomp  用 idx_id / idx_comp 的同构调解
      Grothendieck := Total … ；Grothendieck_Proj := Total_Proj …
      Displayed presentation first, then total category.

   3) 为何要 IndexedCat / Why IndexedCat
      裸 Functor B Cat 缺跨应用连贯等式；本库用 IndexedCat 的 idx_resp /
      idx_comp / idx_cocycle 等字段放电显示范畴定律。
      Coherence fields discharge Displayed laws.

   阅读：IndexedCat → Displayed 字段 → Total → Proj。
   Read: IndexedCat → Displayed fields → Total → Proj.
*)

Program Definition Grothendieck_Displayed : Displayed B := {|
  dobj := fun x => idx_fib A x;
  dhom := fun x y dx dy f => idx_map A f dx ~{ idx_fib A y }~> dy;
  dhomset := fun x y dx dy f => @homset (idx_fib A y) (idx_map A f dx) dy;
  dtransport := fun x y dx dy f g e ff => ff ∘ from (idx_resp A e dx);
  did := fun x dx => to (idx_id A dx);
  dcomp := fun x y z dx dy dz f g ff gg =>
             ff ∘ fmap[idx_map A f] gg ∘ from (idx_comp A f g dx)
|}.
Next Obligation.
  (* dtransport_respects / 运输尊重 *)
  intros x y dx dy f g e ff gg Hfg; simpl.
  now rewrite Hfg.
Qed.
Next Obligation.
  (*
 dtransport_id, from proof irrelevance of [idx_resp] 

 --------
 dtransport_id，从 [idx_resp] 的证明无关性
*)
  intros x y dx dy f e ff; simpl.
  rewrite (idx_resp_from_id A e dx).
  apply id_right.
Qed.
Next Obligation.
  (* dtransport_trans / dtransport_trans *)
  intros x y dx dy f g h e1 e2 ff; simpl.
  apply Grothendieck_transport_trans.
Qed.
Next Obligation.
  (* dcomp_respects / dcomp_尊重 *)
  intros x y z dx dy dz f g ff ff' Hf gg gg' Hg; simpl.
  now rewrite Hf, Hg.
Qed.
Next Obligation.
  (* dtransport_comp_l / dtransport_comp_l *)
  intros x y z dx dy dz f f' g e e' ff gg; simpl.
  apply Grothendieck_transport_comp_l.
Qed.
Next Obligation.
  (* dtransport_comp_r / dtransport_comp_r *)
  intros x y z dx dy dz f g g' e e' ff gg; simpl.
  apply Grothendieck_transport_comp_r.
Qed.
Next Obligation.
  (* did_left *)
  intros x y dx dy f ff; simpl.
  apply Grothendieck_did_left.
Qed.
Next Obligation.
  (* did_right / 做对了 *)
  intros x y dx dy f ff; simpl.
  apply Grothendieck_did_right.
Qed.
Next Obligation.
  (* dcomp_assoc / dcomp_结合 *)
  intros w x y z dw dx dy dz f g h ff gg hh; simpl.
  apply Grothendieck_assoc.
Qed.

(*
   * The Grothendieck construction ∫ A: the total category of the displayed
   presentation. 

   --------
   * Grothendieck 构造 ∫ A：所展示表示的总范畴。
*)
Definition Grothendieck : Category := Total Grothendieck_Displayed.

(** The projection ∫ A ⟶ B, taking first components. / 投影 ∫ A ⟶ B，取第一分量。 *)
Definition Grothendieck_Proj : Grothendieck ⟶ B :=
  Total_Proj Grothendieck_Displayed.

End Grothendieck.
