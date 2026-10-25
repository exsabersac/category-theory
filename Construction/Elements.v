Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.
Require Import Category.Construction.Comma.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.One.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Terminal.

Generalizable All Variables.

(*
   * The category of elements of a Sets-valued functor, and its projection. 

   --------
   * 一个取值为集合的函子元素的范畴，以及它的投射。
*)

(*
 nLab: https://ncatlab.org/nlab/show/category+of+elements
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_elements

 BOOK LOCATIONS. Recorded from the statement of issue #345: Mac Lane,
 "Categories for the Working Mathematician", III.7; Riehl, "Category
 Theory in Context", 2.4 (Definitions 2.4.1 and 2.4.2, Exercise
 2.4.ii); Awodey, "Category Theory", 8.6. Those texts were not
 consulted while writing this file. The locations are given so a
 reader can look the construction up; nothing beyond the locations is
 reproduced here, and no claim is made about the wording or numbering
 at those places.

 THE CONSTRUCTION. For K : D ⟶ Sets, an object of [Elements K] is a
 pair (d, x) with d an object of D and x an element of the setoid K d;
 a morphism (d, x) ~> (d', y) is a morphism f : d ~> d' of D that
 carries x to y, that is, [fmap[K] f x ≈ y]. The projection
 [Elements_proj] sends (d, x) to d and a morphism to its underlying
 D-morphism.

 SETOID PRESENTATION. Two different `≈` occur below and neither is
 Leibniz equality. In the hom condition [fmap[K] f x ≈ y] the `≈` is
 the equivalence of the target setoid K d': every object of Sets is a
 carrier packaged with a Setoid (Instance/Sets.v), and every
 morphism of Sets is a carrier function together with a proof that it
 respects `≈` (Instance/Sets.v). In the hom-setoid of
 [Elements] the `≈` is D's own hom equivalence. The books state the
 hom condition with an equality of elements; this file states it with
 `≈`, which is the setoid reading issue #345 asks for.

 HOM-SETOID, AND WHAT IT BUYS. [Elements] compares two morphisms by
 their underlying D-morphisms alone; the carried condition takes no
 part in the comparison. That is the encoding already in use at
 Construction/Slice.v (sigma object, sigma hom, hom-setoid on
 the first component) and, componentwise, at Construction/Comma.v.
 One consequence is recorded here because consumers rely on it:
 faithfulness of [Elements_proj] is DEFINITIONAL rather than a theorem
 with content. The identity function typechecks as the injectivity
 proof, which [Elements_proj_faithful_definitional] exhibits, and the
 [Faithful] instance (Theory/Functor.v) is then discharged with
 nothing left to prove. Fullness does not hold in general and is not
 claimed: a D-morphism must carry the element to be a morphism here.

 ROUTE TAKEN. The definition below is direct: objects are literally
 the pairs. The comma presentation is related to it by a proved
 comparison instead of being taken as the definition. Two other routes
 are present in the tree and are deliberately not used.

 (1) The comma route. With the constant functor =(c) : 1 ⟶ Sets of
 Functor/Diagonal.v, taken at the singleton of Instance/Sets.v
 ([Sets_Terminal]), the comma category of Construction/Comma.v has
 the same content. Its objects are triples ((ttt, d); h) in which h is
 a setoid map out of the singleton, so an element is presented as a map
 rather than as an inhabitant, and every morphism carries a contentless
 component in the terminal category 1 (the FIRST component of the
 underlying pair, in Comma.v's encoding). Taking that
 as the definition would in addition turn the comparison this file is
 asked for into a definitional identity. It is therefore introduced
 below as [ElementsComma] and compared, following the precedent of
 Construction/Slice.v ([Comma_Slice]) and
 Instance/Cones/Comma.v ([Cones_Comma]).

 (2) The Grothendieck route. The background essay at
 Construction/Grothendieck.v says that restricting the fibres
 of an indexed category to sets viewed as discrete categories recovers
 the category of elements el(F). That sentence is background prose,
 not a construction, and this file does not obtain [Elements] from it.
 The obstruction sits at the coherence level. [DiscreteCat]
 (Instance/Discrete.v) has [hom := fun x y => x = y] with
 [Morphism_equality] as its hom-setoid, so a fibre [DiscreteCat (K d)]
 carries strict equality of elements. The fibre functors themselves can
 be formed from the underlying carrier maps, but the coherence cells an
 [IndexedCat] asks for would then have to be Leibniz equalities of
 elements, whereas K's functor laws supply equivalences in the fibre
 setoid. The direct route below has no such requirement.

 THE COMMA COMPARISON, STATED EXACTLY. [Elements_Comma] is an
 isomorphism in Cat, [Elements K ≅[Cat] ElementsComma]. Cat's
 hom-setoid is natural isomorphism of functors (Instance/Cat.v), so an
 isomorphism in Cat is an equivalence of categories; no statement is
 made in StrictCat, and none is intended. What is delivered concretely
 is the functor pair [Elements_to_Comma] and [Elements_from_Comma]
 together with the two natural isomorphisms. The round trip
 [Elements_from_Comma ◯ Elements_to_Comma] is the identity on objects
 and on morphisms, and its natural isomorphism has identity components.
 The other round trip is not the identity: it replaces a setoid map h
 out of the singleton by the constant map at [h ttt], and those two
 records agree pointwise up to `≈` without being the same term.
 Compatibility with the projections is recorded separately as
 [Elements_proj_comma_iso], a natural isomorphism in [[Elements K, D]]
 between [comma_proj2 ◯ Elements_to_Comma] and [Elements_proj] whose
 components are identities; the two functors agree on objects and on
 morphisms, and only the packaged proof fields differ.

 ORIENTATION, AND THE PRESHEAF READING. [Elements] as defined is the
 covariant construction: for K : D ⟶ Sets it lies over D. For a
 presheaf P : C^op ⟶ Sets the books use the other arrow orientation, in
 which a morphism (c, x) ~> (c', x') is f : c ~> c' with
 [fmap[P] f x' ≈ x]. That is [PElements P] below, the opposite
 (Construction/Opposite.v) of the covariant construction on C^op,
 and [PElements_hom] is a definitional check -- it holds by
 [reflexivity] -- that the hom type is exactly the one just displayed.
 The orientation is chosen so that the projection stays covariant:
 [PElements_proj] lands in C, with [fmap] the first projection and no
 transport, which typechecks because the opposite of the opposite of C
 is C (Construction/Opposite.v, [op_invol]).

 WORKING WITH Sets HOM EQUATIONS. [fmap_id], [fmap_comp] and
 [fmap_respects] for a functor into Sets are equations in a Sets
 hom-setoid, hence pointwise families indexed by elements
 (Instance/Sets.v). Setoid rewriting with them underneath an
 application does not apply, and [apply fmap_id] does not unify with an
 element-level goal. The three element-level readings are packaged once
 as [elements_id_cond], [elements_comp_cond] and
 [elements_respects_cond]; the first two carry every proof below
 ([elements_respects_cond] is used by none of them -- it is exported for
 consumers), and consumers should reuse all three rather than rewrite
 the functor laws in place. Note also that [=(1)] does not elaborate inside a functor type,
 because there [1] is read as the terminal category; write
 [=(1%object)], or use the named [SetsOne] below.

 NOT IN THIS FILE. The remaining items of issue #345 are listed so
 their absence is not read as an oversight. The contravariant analogue
 of the comma comparison, [PElements P ≅[Cat] (=(1) ↓ P)^op], is not
 proved here: it asks for a transport of an isomorphism in Cat along
 opposites, which no in-tree lemma supplies yet. The description of
 [lim F] as the sections of the projection needs limits of Sets-valued
 diagrams, which the tree does not have, and its section condition is a
 strict equation of functors whereas `≈` in Cat is natural
 isomorphism. The characterization of the elements category as a
 pullback in Cat waits on pullbacks in Cat (issue #337) and on the
 category of pointed sets (issue #261). The identification of [colim F]
 with the connected components of the elements category waits on issues
 #352 and #355. The discrete-opfibration predicate is owned by issues
 #809 and #948; what this file supplies is the chosen lift
 [Elements_lift] over a base morphism, the definitional check
 [Elements_lift_over] that the projection returns that base morphism,
 and faithfulness, which together are the uniqueness reading in the
 form the setoid presentation permits. 

 --------
 nLab:  https://ncatlab.org/nlab/show/category+of+elements
 Wikipedia:  https://en.wikipedia.org/wiki/Category_of_elements

 书籍位置。根据第345期声明记录：Mac Lane，《数学工作者的范畴》，III.7；Riehl，《上下文中的范畴论》，2.4（定义2.4.1和2.4.2，练习2.4.ii）；Awodey，《范畴论》，8.6。在编写此文件时未参考这些文本。提供这些位置是为了读者可以查找该构造；此处未重复除了这些位置之外的内容，也不对这些地方的表述或编号作出任何声明。构造。对于 K : D ⟶ 集合，一个 [Elements K] 的对象是一个对 (d, x)，其中 d 是 D 的一个对象，x 是集合带 K d 的一个元素；一个态射 (d, x) ~> (d', y) 是 D 的态射 f : d ~> d'，它将 x 映射到 y，也就是说，[fmap[K] f x ≈ y。投影 [Elements_proj] 将 (d, x) 发送到 d，并将一个态射发送到其对应的 D-态射。SETOID 演示。下面出现了两个不同的 `≈`，并且都不是莱布尼茨相等。在同态条件 [fmap[K] f x ≈ y 中，`≈` 是目标集合的等价关系 K d'：Sets 的每个对象都是一个与集合类型封装在一起的承载对象（Instance/Sets.v），Sets 的每个态射都是一个承载函数，同时附有一个它遵守 `≈` 的证明（Instance/Sets.v）。在 [Elements] 的同态集合中，`≈` 是 D 自己的同态等价。书籍中用元素的相等性来表示同态条件；该文件使用 `≈` 来表示，这是集合类型阅读问题 #345 所要求的。HOM-SETOID，以及它的作用。[Elements] 仅通过它们的底层 D-态射来比较两个态射；所携带的条件在比较中不起作用。这就是在 Construction/Slice.v（sigma 对象、sigma 态射、第一分量上的态射集合概念）以及 Construction/Comma.v 中按分量使用的编码方式。这里记录了一个结果，因为使用者依赖它：[Elements_proj] 的忠实性是定义性的，而非有内容的定理。恒等函数类型检查通过作为单射性的证明，[Elements_proj_faithful_definitional] 展示了这一点，而 [Faithful] 实例（Theory/Functor.v）随后无需剩余任何证明即可被接受。完全性在一般情况下不成立，也没有声称成立：一个 D-态射必须携带元素才能在此处成为态射。所采取的路线。下面的定义是直接的：对象字面上就是这些对。逗号表示法是通过已证明的比较与其相关，而不是被作为定义。树中存在另外两条路线，并且刻意未使用。(1) 逗号路由。使用常函子 =(c) : 1 ⟶ Sets 来自 Functor/Diagonal.v，在 Instance/Sets.v 的单例上取值 ([Sets_Terminal])，Construction/Comma.v 的逗号范畴具有相同的内容。它的对象是三元组 ((ttt, d); h)，其中 h 是从单例映射出的集合等价映射，因此元素以映射而非成员的形式呈现，并且每个态射在终端范畴 1 中携带一个无内容的分量（在 Comma.v 编码中为底层对的第一个分量）。将其作为定义还会将本文件所要求的比较转变为定义恒等。因此，它在下面介绍为 [ElementsComma]，并进行比较，遵循 Construction/Slice.v ([Comma_Slice]) 和 Instance/Cones/Comma.v ([Cones_Comma]) 的先例。(2) Grothendieck 路线。Construction/Grothendieck.v 中的背景文章提到，将索引范畴的纤维限制为作为离散范畴的集合，会恢复元素范畴 el(F)。这句话是背景说明，而不是构造，而且该文件并没有从中获得 [Elements]。障碍出现在一致性层面。[DiscreteCat]（Instance/Discrete.v）拥有 [hom := fun x y => x = y]，其齐次集为 [Morphism_equality]，因此纤维 [DiscreteCat (K d)] 保持元素的严格相等性。纤维函子本身可以由底层承载映射构成，但 [IndexedCat] 所要求的一致性单元必须是元素的 Leibniz 相等，而 K 的函子规律只能提供纤维齐次集中的等价性。下面的直接路线没有这样的要求。逗号比较，精确陈述。[Elements_Comma] 在 Cat 中是一个同构，[Elements K ≅[Cat] ElementsComma]。Cat 的同态集合是函子自然同构（Instance/Cat.v），因此在 Cat 中的同构是范畴等价；在 StrictCat 中没有声明，也没有打算声明。具体传递的是函子对 [Elements_to_Comma] 和 [Elements_from_Comma]，以及两个自然同构。循环往返 [Elements_from_Comma ◯ Elements_to_Comma] 在对象和态射上都是恒等的，并且其自然同构具有恒等分量。另一个循环往返不是恒等的：它将来自单元素集的集合同态映射 h 替换为在 [h ttt] 上的常映射，并且这两个记录在点上根据 `≈` 一致，但不是同一项。与投影的兼容性被单独记录为 [Elements_proj_comma_iso]，它是 [[Elements K, D] 中 [comma_proj2 ◯ Elements_to_Comma] 与 [Elements_proj] 之间的自然同构，其分量是恒等的；两个函子在对象和态射上是一致的，只有封装的证明字段不同。方向，以及预层读法。[Elements] 如定义，它是协变构造：对于 K : D ⟶ Sets，它位于 D 上。对于预层 P : C^op ⟶ Sets，书中使用另一种箭头方向，其中一个态射 (c, x) ~> (c', x') 是 f : c ~> c' 且 [fmap[P] f x' ≈ x。也就是说，下面的 [PElements P]，是 C^op 上协变构造的对偶 (Construction/Opposite.v)，并且 [PElements_hom] 是定义检查——它根据 [reflexivity] 成立——同态类型正是刚显示的那个。同态方向的选择是为了让投影保持协变：[PElements_proj] 落在 C 中，[fmap] 是第一个投影且没有传输，这能通过类型检查，因为 C 的对偶的对偶是 C (Construction/Opposite.v，[op_invol]) 。处理集合的同态方程。[fmap_id], [fmap_comp] 和 [fmap_respects] 对于一个到集合的函子来说，是集合同态集的方程，因此是由元素（Instance/Sets.v）索引的逐点族。在应用下使用集合同态重写不适用，而 [apply fmap_id] 与元素级目标不统一。三个元素级的读法被打包为 [elements_id_cond], [elements_comp_cond] 和 [elements_respects_cond]；前两个携带以下所有证明（[elements_respects_cond] 没有被它们使用——它是为使用者导出的），使用者应该重用这三个，而不是在原地重写函子定律。另请注意 [=(1)] 在函子类型中不会详细展开，因为 [1] 被读取为终类；可以写 [=(1%object)]，或者使用下面命名的 [SetsOne]。不在此文件中。#345 问题的其余条目列出是为了避免它们的缺失被视为疏忽。逗号比较的逆变类比 [PElements P ≅[Cat]  (=(1) ↓ P)^op] 并未在此证明：它需要沿着对偶在 Cat 中传输一个同构，而目前树状结构中还没有相关引理。将 [lim F] 描述为投影的截面需要集合值图的极限，但树中没有，并且它的截面条件是函子之间的严格方程，而 Cat 中的 `≈` 则是自然同构。将元素范畴表征为 Cat 中的拉回依赖于 Cat 中的拉回（#337 问题）和基点集合范畴（#261 问题）。将 [colim F] 与元素范畴的连通分量的对应关系的确认，取决于问题 #352 和 #355。离散上射范谓词由问题 #809 和 #948 所拥有；本文件提供的是基态态射之上的选定提升 [Elements_lift]、将投影返回该基态态射的定义检查 [Elements_lift_over]，以及忠实性，这些加在一起就是集合商表示所允许的唯一性解读。
*)

Section Elements.

Context {D : Category}.
Context (K : D ⟶ Sets).

(*
 The functor laws of K, read at an element. A Sets hom equation is a
 pointwise family, so it must be instantiated at the element before it
 can be used as an ordinary equivalence. 

 --------
 K 的函子定律，在一个元素上阅读。集合的同态方程是逐点族的，因此必须在元素上实例化后才能作为普通等价使用。
*)

Lemma elements_id_cond {d : D} (x : K d) : fmap[K] id x ≈ x.
Proof. exact (@fmap_id _ _ K _ x). Qed.

Lemma elements_comp_cond {c d e : D} {x : K c} {y : K d} {z : K e}
      (u : d ~> e) (v : c ~> d) :
  fmap[K] v x ≈ y → fmap[K] u y ≈ z → fmap[K] (u ∘ v) x ≈ z.
Proof.
  intros Hv Hu.
  transitivity (fmap[K] u (fmap[K] v x)).
  - exact (@fmap_comp _ _ K _ _ _ u v x).
  - now rewrite Hv.
Qed.

Lemma elements_respects_cond {c d : D} {x : K c} (f g : c ~> d) :
  f ≈ g → fmap[K] f x ≈ fmap[K] g x.
Proof. intro Hfg; exact (@fmap_respects _ _ K _ _ f g Hfg x). Qed.

(*
 Objects are the pairs (d, x) with x an element of the setoid K d;
 morphisms are the D-morphisms that carry the element. The hom-setoid
 looks only at the underlying D-morphism, so the carried condition is
 not compared. 

 --------
 对象是成对的 (d, x)，其中 x 是集合同构 K d 的一个元素；态射是携带该元素的 D-态射。同构集合仅关注底层的 D-态射，因此携带条件不进行比较。
*)

(*
   【Elements 范畴定义展开】/ Elements walkthrough
   （口吻对齐 Theory/Category.v；受众：Coq 小白 + 范畴论小白的 Haskell 程序员）

   1) 这是什么 / What this is
      对 K : D ⟶ Sets，元素范畴 el(K)：对象 = (d, x)（x ∈ K d）；
      态射 = 把 x「运」到 y 的 D-态射 f（fmap[K] f x ≈ y）。
      Objects (d, x∈Kd); arrows are D-maps carrying the element.
      Haskell 对照：像「带标签的值」+(f 作用后要对上) —— 依赖对 + 相干条件。
      Like tagged values with a transport condition.

   2) 编码 / Encoding
      - obj := ∃ d, K d
      - hom := ∃ f, fmap[K] f (`2 x) ≈ `2 y
      - ≈ 只比底层 D-态射（条件证明无关）→ Elements_proj 定义性忠实

   3) 两条 ≈ / Two different ≈
      条件里的 ≈ 是 Sets 目标 setoid 的；homset 的 ≈ 是 D 自己的。
      Neither is Leibniz =.

   4) 旁路 / Nearby routes
      ElementsComma := Δ(1) ↓ K（逗号表述）；本文件用同构比较，不用逗号当初定义。
      Grothendieck 路线因离散纤维的 = vs ≈ 未采用。

   阅读：(d,x) → 搬运条件 → 分量 ≈ → Elements_proj。
   Read: pairs → carry condition → ≈ on D → projection.
*)

Program Definition Elements : Category := {|
  obj := ∃ d : D, K d;
  hom := fun x y => ∃ f : `1 x ~{D}~> `1 y, fmap[K] f (`2 x) ≈ `2 y;
  homset := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |};
  id := fun x => (id; _);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; _)
|}.
Next Obligation. apply elements_id_cond. Qed.
Next Obligation. eapply elements_comp_cond; eassumption. Qed.

(*
 The projection, taking (d, x) to d and a morphism to its first
 component. 

 --------
 这个投影，将 (d, x) 映射到 d，并将一个态射映射到它的第一个分量。
*)

Program Definition Elements_proj : Elements ⟶ D := {|
  fobj := fun x => `1 x;
  fmap := fun _ _ f => `1 f
|}.

Program Instance Elements_proj_Faithful : Faithful Elements_proj.

(*
 Faithfulness is definitional under the hom-setoid chosen above: the
 injectivity statement is the identity implication, and this witness
 records that fact for readers of the instance. 

 --------
 在上述选择的同态集下，忠实性是定义性的：单射性陈述是身份蕴含，而这个证明为实例的读者记录了这一事实。
*)

Definition Elements_proj_faithful_definitional
  {x y : Elements} (f g : x ~{Elements}~> y) :
  fmap[Elements_proj] f ≈ fmap[Elements_proj] g → f ≈ g :=
  fun H => H.

(*
 The chosen lift of a base morphism at an element, and the definitional
 check that the projection returns that base morphism. 

 --------
 在一个元素上的基态态射的选定提升，以及定义性检查以确认投影返回该基态态射。
*)

Program Definition Elements_lift {d d' : D} (x : K d) (f : d ~> d') :
  ((d; x) : Elements) ~{Elements}~> (d'; fmap[K] f x) := (f; _).

Lemma Elements_lift_over {d d' : D} (x : K d) (f : d ~> d') :
  fmap[Elements_proj] (Elements_lift x f) ≈ f.
Proof. reflexivity. Qed.

(*
 The comma presentation. [SetsOne] is the singleton of Sets_Terminal,
 and [=(SetsOne)] is the constant functor 1 ⟶ Sets at it. 

 --------
 逗号表示法。[SetsOne] 是 Sets_Terminal 的单例，[=(SetsOne)] 是常量函子 1 ⟶ Sets 在其上的值。
*)

Definition SetsOne : Sets := @terminal_obj Sets Sets_Terminal.

Definition ElementsComma : Category := =(SetsOne) ↓ K.

Program Definition Elements_to_Comma : Elements ⟶ ElementsComma := {|
  fobj := fun x => ((ttt, `1 x); {| morphism := fun _ => `2 x |});
  fmap := fun _ _ f => ((ttt, `1 f); _)
|}.

Program Definition Elements_from_Comma : ElementsComma ⟶ Elements := {|
  fobj := fun x => (snd `1 x; `2 x ttt);
  fmap := fun _ _ f => (snd `1 f; _)
|}.

(*
 An isomorphism in Cat, hence an equivalence of categories: `≈` between
 functors is natural isomorphism. [Elements_from_Comma] after
 [Elements_to_Comma] is the identity on objects and on morphisms -- up to
 eta: the equation holds after destructing the object (both projections
 agree by bare reflexivity), not by reflexivity at a variable -- and its
 natural isomorphism has identity components; the other round trip
 replaces a setoid map h by the constant map at h ttt, which agrees with
 h pointwise up to `≈` and not as a term. 

 --------
 在 Cat 中的同构，因此是范畴的等价：在函子之间的 `≈` 是自然同构。[Elements_from_Comma] 之后 [Elements_to_Comma] 在对象和态射上都是恒等——到 eta 为止：该方程在析构对象后成立（两个投影通过纯粹自反性一致），而不是在变量上的自反性——并且它的自然同构的分量是恒等；另一个往返过程将集合映射 h 替换为恒定映射 h ttt，它在点上与 h 一致，到 `≈` 为止，并且不是作为项。
*)

Theorem Elements_Comma : Elements ≅[Cat] ElementsComma.
Proof.
  isomorphism; simpl; intros.
  - apply Elements_to_Comma.
  - apply Elements_from_Comma.
  - constructive.
    + exists (ttt, id); abstract (intros u; destruct u; symmetry;
                                  apply elements_id_cond).
    + exists (ttt, id); abstract (intros u; destruct u; symmetry;
                                  apply elements_id_cond).
    + abstract (split; [reflexivity | cat]).
    + abstract (split; [reflexivity | cat]).
    + abstract (split; [reflexivity |
                        simpl; rewrite id_right, id_left; reflexivity]).
  - constructive.
    + exists id; abstract (apply elements_id_cond).
    + exists id; abstract (apply elements_id_cond).
    + abstract cat.
    + abstract cat.
    + abstract (simpl; rewrite id_right, id_left; reflexivity).
Qed.

End Elements.

(*
 Instances declared inside a section are not registered once the section
 closes; re-register so downstream files can resolve
 [Faithful (Elements_proj K)] by typeclass search rather than by name. 

 --------
 在一个部分中声明的实例在该部分关闭后不会被注册；需要重新注册，以便下游文件可以通过类型类搜索而不是通过名称解析 [Faithful (Elements_proj K)]。
*)
#[export] Existing Instance Elements_proj_Faithful.

(*
 [Category.Functor.Opposite] is not imported because nothing here needs
 it.  (An earlier draft claimed importing it would shadow the category
 [^op] notation and break the presheaf section; that was tested and is
 FALSE -- the two notations live in different scopes, category_scope and
 functor_scope, and coexist.  The import is omitted purely as unused.) 

 --------
 [Category.Functor.Opposite] 没有被导入，因为这里没有任何内容需要它。（早期的草稿声称导入它会遮蔽类别 [^op] 的符号并破坏预层部分；经过测试，这是错误的——这两个符号位于不同的作用域中，category_scope 和 functor_scope，并且可以共存。导入被省略纯粹是因为未使用。）
*)

Require Import Category.Construction.Opposite.
Require Import Category.Instance.Fun.

Section Elements_Comma_Projection.

Context {D : Category}.
Context (K : D ⟶ Sets).

(*
 Compatibility of the comma comparison with the projections to D. The
 two functors agree on objects and on morphisms; only their packaged
 proof fields differ, so the statement is a natural isomorphism with
 identity components and not an equation of functors. 

 --------
 逗号比较与到 D 的投影的兼容性。两个函子在对象和态射上是一致的；只有它们封装的证明字段不同，所以该陈述是具有恒等分量的自然同构，而不是函子的等式。
*)

Program Definition Elements_proj_comma_iso :
  comma_proj2 ◯ Elements_to_Comma K ≅[[Elements K, D]] Elements_proj K := {|
  to   := {| transform := fun _ => id |};
  from := {| transform := fun _ => id |}
|}.

End Elements_Comma_Projection.

Section Presheaf_Elements.

Context {C : Category}.
Context (P : C^op ⟶ Sets).

(*
 The contravariant (presheaf) orientation: the opposite of the covariant
 construction taken on C^op. Objects are still the pairs (c, x) with x
 an element of P c. 

 --------
 逆变（预层）方向：在 C^op 上取协变构造的相反。对象仍然是对 (c, x)，其中 x 是 P c 的一个元素。
*)

Definition PElements : Category := (Elements P)^op.

(*
 A definitional check, closed by [reflexivity]: the hom type is the one
 the presheaf orientation asks for, with the element condition running
 backwards. 

 --------
 一个定义性的检查，由 [reflexivity] 关闭：同态类型是预层方向所要求的类型，元素条件是反向运行的。
*)

Lemma PElements_hom (x y : PElements) :
  (x ~{PElements}~> y) = (∃ f : `1 x ~{C}~> `1 y, fmap[P] f (`2 y) ≈ `2 x).
Proof. reflexivity. Qed.

(*
 The projection stays covariant: it lands in C, with no transport,
 because the opposite of the opposite of C is C. 

 --------
 投影保持协变：它落在 C 中，无需传输，因为 C 的对立的对立是 C。
*)

Program Definition PElements_proj : PElements ⟶ C := {|
  fobj := fun x => `1 x;
  fmap := fun _ _ f => `1 f
|}.

End Presheaf_Elements.
