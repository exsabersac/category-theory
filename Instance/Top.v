Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Subcategory.

Generalizable All Variables.

(* * * The category of topological spaces / * * 拓扑空间的范畴 *)

(*
 Mac Lane, “Categories for the Working Mathematician”, 2nd ed., §I.7,
 printed p. 25
 nLab:      https://ncatlab.org/nlab/show/Top
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_topological_spaces
 Book:      Fong and Spivak, “Seven Sketches in Compositionality”,
 §7.3.2, Definition 7.25 (open covers)
 Book:      Riehl, “Category Theory in Context”, Examples 1.3.14(iv)
 and 1.4.4(v)

 This is the category [Top]. Mac Lane's roll-call of the standard large
 categories (CWM §I.7, printed p. 25) lists `Top`: objects the
 topological spaces, arrows the continuous maps. It is the ambient
 category of general topology, and the source of much categorical
 vocabulary — in the mathematics at large (none of it formalized here)
 the subspace and quotient topologies are limits and colimits, the
 product topology is the categorical product, and the initial and final
 topologies are those (co)limit constructions read as universal
 properties.  CORRECTION (#457): “none of it formalized here” holds of
 this file only, and was already untrue of the library before #457
 (the quotient topologies inside Instance/Top/Pushout.v's pushouts and
 Instance/Top/Wedge.v's wedges, Instance/Top/Coproduct.v's coproducts,
 Instance/Top/Presheaf.v's [OpenSub]); #457 adds the general
 constructions.  The subspace and quotient
 topologies along an arbitrary function, with the equalizers and
 coequalizers Mac Lane's Proposition V.9.1 and its dual build from
 them, are Instance/Top/Subspace.v's, over Instance/Top/Prop.v's
 Prop-valued spaces rather than this file's [Top]; over [Top] itself
 the quotient topology is Instance/Top/Subspace/TypeValued.v's
 [TQuot], the general subspace topology exists there only unpackaged,
 one universe above the points (the open case is
 Instance/Top/Presheaf.v's [OpenSub]), and particular quotient
 topologies build Instance/Top/Pushout.v's pushouts and
 Instance/Top/Wedge.v's wedges.  No products of [Top] are built
 (Instance/Top/Coproduct.v's header scopes that negative), nor the
 initial and final topologies of FAMILIES of maps.  CORRECTION (#458):
 the second holds of [Top] only, and there of GENERAL families: no
 general initial or final topology of a family is built over [Top],
 though Instance/Top/Cocomplete/TypeValued.v's [TSigma] is the final
 topology of one kind of family, the injections of a disjoint union.
 The initial and final topologies of families are Instance/Top/
 Complete.v's [PInit] and Instance/Top/Cocomplete.v's [PFinal], over
 Instance/Top/Prop.v's Prop-valued spaces, and the products, limits
 and colimits of [PTopCat] are built from them; over [Top] itself
 Instance/Top/Cocomplete/TypeValued.v builds the coproducts indexed at
 or below the points and the coequalizers, and still no products.

 objects: topological spaces  (a setoid of points + a family of opens)
 arrows: continuous maps     (preimages of opens are open)
 hom-setoid: f ≈ g  :=  ∀ x, f x ≈ g x   (pointwise, on the map part)
 identity: the identity map
 composition: composition of maps, preimages composing contravariantly

 The companion file Instance/Top/Closed.v carries the opens of a space as
 a thin category (Riehl, CTiC Example 1.3.14(iv)) and the complementation
 duality with its closed sets (Example 1.4.4(v)). 

 --------
 Mac Lane，《为工作数学家准备的范畴论》，第2版，第I.7节，印刷第25页
 nLab：https://ncatlab.org/nlab/show/Top
 维基百科：https://en.wikipedia.org/wiki/Category_of_topological_spaces
 书籍：Fong 和 Spivak，《组合性中的七个草图》，第7.3.2节，定义7.25（开覆盖）
 书籍：Riehl，《上下文中的范畴论》，例子1.3.14(iv)和1.4.4(v)这是类别 [Top]。麦克·莱恩对标准大范畴的点名册（CWM §I.7，印刷第25页）列出了 `Top`：对象是拓扑空间，态射是连续映射。它是一般拓扑学的环境范畴，也是许多范畴论词汇的来源——在广义数学中（这里没有形式化）子空间和商空间的拓扑是极限和余极限，积拓扑是范畴积，初始拓扑和终结拓扑是作为普适性质解释的那些（余）极限构造。更正 (#457)：“这里没有任何形式化”仅适用于此文件，并且在 #457 之前对于库已经不成立（Instance/Top/Pushout.v 中的推送出以及 Instance/Top/Wedge.v 中的楔形、Instance/Top/Coproduct.v 中的余积、Instance/Top/Presheaf.v 中的 [OpenSub] 的商拓扑）；#457 添加了通用构造。沿任意函数的子空间与商拓扑，以及由它们构造的等化器和共等化器（Mac Lane 命题 V.9.1 及其对偶），是 Instance/Top/Subspace.v 中的实例，位于 Instance/Top/Prop.v 的命题值空间之上，而不是本文件的 [Top]；在 [Top] 本身之上，商拓扑是 Instance/Top/Subspace/TypeValued.v 的 [TQuot]，通用子空间拓扑仅以未打包形式存在，比点高一宇宙（开集情况见 Instance/Top/Presheaf.v 的 [OpenSub]），特定商拓扑通过构建 Instance/Top/Pushout.v 的 pushouts 和 Instance/Top/Wedge.v 的 wedges。未构建 [Top] 的积（Instance/Top/Coproduct.v 的头部作用域对此有负面说明），也未构建映射族的初拓扑和终拓扑。更正 (#458)：第二个只适用于 [Top]，以及一般族那里：没有一般族的初始或末端拓扑是在 [Top] 上构建的，尽管 Instance/Top/Cocomplete/TypeValued.v 的 [TSigma] 是某种族的末端拓扑，即不相交并的注入。族的初始和末端拓扑分别是 Instance/Top/Complete.v 的 [PInit] 和 Instance/Top/Cocomplete.v 的 [PFinal]，作用在 Instance/Top/Prop.v 的 Prop 值空间上，而 [PTopCat] 的积、极限和余极限是由它们构建的；在 [Top] 本身之上，Instance/Top/Cocomplete/TypeValued.v 构建在点索引或以下的余积和余等化器，但仍然没有积。对象：拓扑空间（一个点的集合+一个开集族）
 箭头：连续映射（开集的原像是开集）
 同态集合：f ≈ g := ∀ x, f x ≈ g x（逐点，在映射部分）
 恒等：恒等映射
 复合：映射的复合，原像以逆变方式组合

 伴随文件 Instance/Top/Closed.v 将空间的开集作为一个薄范畴（Riehl, CTiC 示例 1.3.14(iv)）以及其闭集的补集对偶（示例 1.4.4(v)）。
*)

(*
 Design: what a topological space is, constructively

 nLab:      https://ncatlab.org/nlab/show/locale
 nLab:      https://ncatlab.org/nlab/show/constructive+mathematics
 Book:      Johnstone, “Stone Spaces”, CUP 1982 (the locale/space
 adjunction and the pointfree tradition)
 Book:      Bishop, “Foundations of Constructive Analysis”, McGraw-Hill
 1967 (the setoid discipline this file inherits)

 Four decisions govern the encoding below, and each is forced by the
 surrounding library rather than chosen for taste.

 1. POINTS ARE A SETOID.  Objects carry a [SetoidObject] of points, not
 a bare type: this is the same Bishop-set discipline that makes
 Instance/Sets.v the library's stand-in for Set.  A consequence is
 that an open set must be a predicate that respects `≈`; the field
 [open_proper] demands exactly that, so the topology cannot separate
 two points the carrier's own equality has already identified.

 2. OPENS ARE A PREDICATE ON PREDICATES, HENCE ONE UNIVERSE UP.  A
 topology is a subset of the powerset, so [IsOpen] has type
 `(carrier → Type) → Type`: it quantifies over predicates on the
 carrier and therefore lives strictly above the universe of points.
 This is the same placement Theory/Subobject/Functor.v gives its
 Sets-valued presheaf `Sub : C^op ⟶ Sets` — a subobject lattice is
 a powerset-sized object over a hom-sized base — and the same size
 phenomenon that keeps the truth-value object of Instance/Sets.v's
 [surjectivity_is_epic] out of Sets and confines the classifier
 theorems to Instance/Sets/Classifier.v.  Concretely, the record is
 declared [TopSpace@{o}]: points, their equalities, the values of an
 open predicate, the index type of a union and the openness witnesses
 all sit at `Type@{o}`, following the `SetoidObject@{o o}` discipline
 of Instance/Sets.v — so [TopSpace@{o}] itself lands at `Type@{o+1}`,
 the [IsOpen] field having quantified over the `Type@{o+1}` of
 predicates on the carrier (a record sits at the level of its largest
 field type, not above it).  The ascent shows up again one step later:
 [Continuous] quantifies over the opens of the codomain, so the
 hom-sets of [Top] live at `o+1`, which is the declared constraint
 `o < h` on [ContinuousMorphism_equiv] below.  Because all of this is
 universe-polymorphic, [Top] exists at every level rather than needing
 a chosen “universe of small sets”.

 3. THE AXIOMS ARE STATED IN THEIR TYPE-VALUED FORM.  The union axiom
 quantifies over an arbitrary index TYPE and forms the dependent sum
 `{ i : I & U i x }` — the constructive reading of `⋃ᵢ Uᵢ`, where an
 element of the union carries the index witnessing membership.  The
 binary intersection is the product `U x ∧ V x`, and the whole space
 is the constant predicate [poly_unit].  Because `≈`-equality of
 predicates is pointwise `↔` (the library's [iffT]) rather than
 Rocq's `=`, closure under unions alone is not enough: [open_respects]
 records that being open is invariant under pointwise equivalence,
 which is what lets the union axiom be applied up to reindexing.

 4. THE EMPTY OPEN AND THE CONSTANTS ARE THEOREMS, NOT AXIOMS.  The
 union over the empty index type gives the empty open, and — the
 lemma that does the most work downstream — the union over the index
 type `P` of copies of the whole space gives [open_const]: EVERY
 constant predicate is open, in every space.  Its corollary
 [open_uniform] says every “uniform” predicate (one that holds at a
 point as soon as it holds anywhere) is open.  This is the
 constructive replacement for the classical remark that `∅` and `X`
 are open in every topology: constructively there are many more
 predicates that cannot be told apart from `∅` or `X`, and all of
 them must be open.  It is exactly what makes the one-point space
 terminal (§ [Top_Terminal]) and every map into an indiscrete space
 continuous (§ [into_indiscrete_continuous]).

 What is deliberately NOT attempted here: the pointfree turn.  A
 constructive analyst usually prefers locales (frames of opens with no
 points at all — Johnstone, “Stone Spaces”), precisely because the
 point-set axioms above behave badly without excluded middle.  This
 file stays point-set because the work order is Mac Lane's `Top`, and
 because the point-set encoding is what supports the mono/epi
 characterizations below. 

 --------
 设计：什么是拓扑空间，构造性地

 nLab:       https://ncatlab.org/nlab/show/locale 
 nLab:       https://ncatlab.org/nlab/show/constructive+mathematics 
 书籍:      Johnstone，《石空间》，CUP 1982（局部/空间对偶与无点传统）
 书籍:      Bishop，《构造分析基础》，McGraw-Hill 1967（本文件继承的集合等价纪律）

 以下编码由四个决定支配，每一个都是由周围库迫使的，而不是出于个人喜好选择的。1. 点是一个集合类。对象携带一个点的 [SetoidObject]，而不是一个裸类型：这与 Bishop 集合规范相同，使得 Instance/Sets.v 成为库中 Set 的替代品。一个结果是，一个开集必须是一个尊重 `≈` 的谓词；字段 [open_proper] 正好要求这一点，因此拓扑不能区分载体自身的等式已经识别的两个点。2. 开集是谓词上的谓词，因此属于比一个宇宙更高一级的类型。一个拓扑是幂集的子集，因此 [IsOpen] 的类型是 `(carrier → Type) → Type`：它对载体上的谓词进行量化，因此严格地位于点的宇宙之上。这与 Theory/Subobject/Functor.v 对其 Set 值预层 `Sub : C^op ⟶ Sets` 的放置相同——一个子对象格是基于 Hom 的对象上的幂集大小对象——以及同样的尺寸现象，使得 Instance/Sets.v 的 [surjectivity_is_epic] 真值值对象无法归入 Sets，并将分类器定理限制在 Instance/Sets/Classifier.v 中。具体来说，该记录被声明为 [TopSpace@{o}]：点，它们的等式，一个开放谓词的值，一个联合的索引类型以及开放性证明，都位于 `Type@{o}`，遵循 Instance/Sets.v 的 `SetoidObject@{o o}` 规范——因此 [TopSpace@{o}] 本身位于 `Type@{o+1}`，[IsOpen] 字段对承载（carrier）上的谓词 `Type@{o+1}` 进行了量化（记录位于其最大字段类型的层级，而不是其上方）。这个上升在之后的一步再次显现：[Continuous] 对陪域的开集进行了量化，因此 [Top] 的同态集合位于 `o+1`，这正是下面对 [ContinuousMorphism_equiv] 声明的约束 `o < h`。因为这一切都是宇宙多态的，[Top] 存在于每一个层级，而不需要选择一个“小集合的宇宙”。3. 公理以其类型值形式陈述。并集公理对任意索引类型进行量化，并形成依赖和 `{ i : I & U i x }` —— `⋃ᵢ Uᵢ` 的构造性表述，其中并集的一个元素携带证明成员资格的索引。二元交集是积 `U x ∧ V x`，而整个空间是常量谓词 [poly_unit]。由于谓词的 `≈`-等式是逐点 `↔`（库的 [iffT]）而不是 Rocq 的 `=`，所以仅闭合于并集是不够的：[open_respects] 记录了开集在逐点等价下保持不变，这使得并集公理可以应用于重新索引。4. 空开集和常量是定理，而不是公理。对空索引类型的并集给出了空开集，而 —— 下游工作量最大的引理 —— 对索引类型 `P` 的整个空间副本的并集给出了 [open_const]：每个常量谓词在每个空间中都是开集。其推论 [open_uniform] 表明每个“均匀”谓词（也就是说，只要在某处成立，它在该点就成立）也是开集的。这是对经典命题的构造性替代：经典命题指出 `∅` 和 `X` 在每个拓扑中都是开集；在构造性观点下，有许多谓词无法与 `∅` 或 `X` 区分开来，并且它们全部必须是开集。正是这种特性使得单点空间成为终空间 (§  [Top_Terminal])，并且每个映射到不分离空间的映射都是连续的 (§  [into_indiscrete_continuous])。

 这里故意没有尝试的：无点（pointfree）方法。构造分析学家通常更喜欢使用局域（完全开集的框架，完全没有点——Johnstone, “Stone Spaces”），正因为在没有排中律的情况下，上述点集公理会表现不良。该文件保持点集方法，因为工作顺序是 Mac Lane 的 `Top`，并且因为点集编码支持下面的单/满同态特征描述。
*)

(** ** Spaces *)

(*
 A topological space: a setoid of points together with a family of open
 predicates closed under the usual operations.  The three closure fields
 [open_union]/[open_whole]/[open_inter] are the classical axioms; the two
 [open_respects]/[open_proper] fields are the setoid bookkeeping described
 in the header.  The single universe [o] is spelled out rather than
 inferred, for the reason given in the header's point 2: pinning it to one
 variable is what keeps every space an object of one and the same [Top]. 

 --------
 拓扑空间：一个点的集合以及一族在通常运算下封闭的开谓词。三个闭包字段 [open_union] / [open_whole] / [open_inter] 是经典公理；两个 [open_respects] / [open_proper] 字段是标题中描述的集合记账。单一宇宙 [o] 是明确写出的而不是推断出的，原因如标题的第2点所述：将其固定在一个变量上可以使每个空间都是同一个 [Top] 的对象。
*)

Record TopSpace@{o} := {
  top_carrier :> SetoidObject@{o o};    (* the setoid of points / 点的集合体 *)

  (* the topology: which predicates on the points are open / 拓扑：哪些点的谓词是开放的 *)
  IsOpen : (top_carrier → Type@{o}) → Type@{o};

  (* being open is invariant under pointwise equivalence of predicates / 在谓词的逐点等价下，开性是不变的 *)
  open_respects (U V : top_carrier → Type@{o}) :
    (∀ x, U x ↔ V x) → IsOpen U → IsOpen V;

  (* every open respects the carrier's own equality on points / 每一次开放都尊重承运人在积分上的平等 *)
  open_proper (U : top_carrier → Type@{o}) :
    IsOpen U → ∀ x y : top_carrier, x ≈ y → U x → U y;

  (* closure under arbitrary (type-indexed) unions / 在任意（类型索引）并集下的闭包 *)
  open_union (I : Type@{o}) (U : I → (top_carrier → Type@{o})) :
    (∀ i, IsOpen (U i)) → IsOpen (fun x => { i : I & U i x });

  (* the whole space is open / 整个空间都是开放的 *)
  open_whole : IsOpen (fun _ => poly_unit@{o});

  (* closure under binary intersection / 在二元交集下的封闭性 *)
  open_inter (U V : top_carrier → Type@{o}) :
    IsOpen U → IsOpen V → IsOpen (fun x => U x ∧ V x)
}.

(*
 Every constant predicate is open.  Proof: the union, indexed by the type
 [P] itself, of `P`-many copies of the whole space is pointwise equivalent
 to the constant predicate `P` — the witness of membership IS an element
 of `P`.  Classically this says no more than “∅ and X are open”; here it
 is the engine behind terminality of the point and the continuity of every
 map into an indiscrete space. 

 --------
 每个常量谓词都是开的。证明：将整个空间的 `P` 个副本按类型 [P] 本身索引的并集，在点上等价于常量谓词 `P` ——成员资格的证据是 `P` 的一个元素。从经典角度来看，这只说明“∅ 和 X 是开的”；在这里，它是点的终端性以及每个映射到不可分空间的连续性的动力。
*)
Lemma open_const (X : TopSpace) (P : Type) : IsOpen X (fun _ => P).
Proof.
  apply (open_respects X (fun _ => { _ : P & poly_unit }) (fun _ => P)).
  - intro x; split.
    + exact (fun w => projT1 w).
    + exact (fun p => (p; ttt)).
  - apply (open_union X P (fun _ _ => poly_unit)).
    intro i; exact (open_whole X).
Qed.

(* The empty predicate is open: the union over the empty index type, which is the [P := False] case of [open_const]. / 空谓词是开放的：对空索引类型的并集，这是 [open_const] 的 [P := False] 情况。 *)
Corollary open_empty (X : TopSpace) : IsOpen X (fun _ => False).
Proof. exact (open_const X False). Qed.

(*
 A predicate is “uniform” when it holds at every point as soon as it holds
 at some point.  Every uniform predicate is open, being pointwise
 equivalent to the constant predicate “this predicate is inhabited
 somewhere”.  Classically the uniform predicates are just ∅ and X;
 constructively they are the whole of the coarsest topology, and this
 lemma says that topology is contained in every other one. 

 --------
 当一个谓词在某一点成立时，它在每一点都成立，这个谓词就是“统一”的。每个统一谓词都是开集的，因为它在每一点上都等价于常值谓词“这个谓词在某处有元素”。在经典逻辑下，统一谓词只是 ∅ 和 X；在构造逻辑下，它们是最粗拓扑的全部，而这个引理说明这个拓扑包含在每个其他拓扑中。
*)
Lemma open_uniform (X : TopSpace) (U : X → Type) :
  (∀ x y : X, U x → U y) → IsOpen X U.
Proof.
  intro HU.
  apply (open_respects X (fun _ => { z : X & U z }) U).
  - intro x; split.
    + intro w; exact (HU (projT1 w) x (projT2 w)).
    + intro Ux; exact (x; Ux).
  - apply open_const.
Qed.

(** ** Continuous maps / ** 连续映射 *)

(*
 Continuity, in its categorical form: the preimage of every open is open.
 The map itself is a [SetoidMorphism], so it already respects the two
 carriers' equalities; continuity is the extra topological condition. 

 --------
 连续性，其分类形式：每个开集的原像都是开集。该映射本身是一个 [SetoidMorphism]，因此它已经满足两个载体的等式；连续性是额外的拓扑条件。
*)
Definition Continuous (X Y : TopSpace)
           (f : SetoidMorphism (top_carrier X) (top_carrier Y)) : Type :=
  ∀ U : Y → Type, IsOpen Y U → IsOpen X (fun x => U (f x)).

(*
 A morphism of [Top]: a setoid map on points that is moreover continuous.
 This wraps [SetoidMorphism] exactly as [SetoidMorphism] wraps a bare
 function in Instance/Sets.v. 

 --------
 [Top] 的一个态射：在点上的集合等价映射，并且是连续的。
 这正如 [SetoidMorphism] 包装了 Instance/Sets.v 中的一个裸函数一样，[SetoidMorphism] 也被包装。
*)
Record ContinuousMorphism (X Y : TopSpace) := {
  continuous_map :> SetoidMorphism (top_carrier X) (top_carrier Y);
  continuity : Continuous X Y continuous_map
}.

Arguments continuous_map {X Y} _.
Arguments continuity {X Y} _ _ _.

(*
 The hom-setoid compares only the map part, pointwise up to the codomain's
 `≈`.  The continuity witness is not compared: two continuous maps that
 agree on points are the same arrow of [Top], whatever proofs of
 continuity they happen to carry.  This is the same extensional discipline
 as [SetoidMorphism_equiv], and it is what makes [Top] a category without
 any proof-irrelevance axiom. 

 --------
 同态集合只比较映射部分，在每一点上根据到值域的 `≈` 来比较。连续性的证明不被比较：两个在各点上相同的连续映射，在 [Top] 中是相同的箭头，无论它们携带的连续性证明如何。这与 [SetoidMorphism_equiv] 的外延处理方式相同，这也是 [Top] 能成为一个不依赖任何证明不可区分公理的范畴的原因。
*)
(*
 The universes are declared: [o] is the space's own level, [h] the level
 of the hom (strictly above [o], because [Continuous] quantifies over the
 opens of the codomain — the hom-sets of [Top] genuinely live one step up
 from its points), and [p] the level at which morphism equality is
 recorded.  The `h ≤ p` constraint is the one [Category] itself imposes;
 left to inference the relation would be minimized down to [o] and no
 longer fit a hom-setoid. 

 --------
 这些宇宙被声明为：[o] 是空间本身的层级，[h] 是 hom 的层级（严格高于 [o]，因为 [Continuous] 对应上值域的开集进行量化 —— [Top] 的 hom 集合实际上比其点高一层），而 [p] 是记录态射相等性的层级。`h ≤ p` 约束是 [Category] 本身施加的；如果由推导决定，该关系将被最小化到 [o]，再也不适合 hom-集合结构。
*)
Definition ContinuousMorphism_equiv@{o h p | o < h, h <= p +}
  {X Y : TopSpace@{o}} : crelation@{h p} (ContinuousMorphism@{h o} X Y) :=
  fun f g => ∀ x : X, continuous_map f x ≈ continuous_map g x.

Arguments ContinuousMorphism_equiv {X Y} _ _ /.

#[export]
Program Instance ContinuousMorphism_Setoid@{o h p | o < h, h <= p +}
  {X Y : TopSpace@{o}} : Setoid@{h p} (ContinuousMorphism@{h o} X Y) := {|
  equiv := ContinuousMorphism_equiv@{o h p}
|}.
Next Obligation.
  constructor.
  - intros f x; reflexivity.
  - intros f g Hfg x; symmetry; exact (Hfg x).
  - intros f g h Hfg Hgh x; transitivity (continuous_map g x).
    + exact (Hfg x).
    + exact (Hgh x).
Qed.

(*
 The identity map is continuous: the preimage of U along the identity is
 U itself, up to eta. 

 --------
 恒等映射是连续的：沿恒等映射的 U 的原像是 U 本身，最多差一个 eta。
*)
Definition top_id {X : TopSpace} : ContinuousMorphism X X := {|
  continuous_map := setoid_morphism_id;
  continuity := fun _ H => H
|}.

(* Composition: preimages compose contravariantly, so the preimage along `g ∘ f` of an open is the preimage along `f` of the preimage along `g`. / 组成：逆像是逆变组合的，因此沿 `g ∘ f` 的开集的逆像就是沿 `f` 的逆像，再沿 `g` 的逆像。 *)
Definition top_compose {X Y Z : TopSpace}
           (g : ContinuousMorphism Y Z) (f : ContinuousMorphism X Y) :
  ContinuousMorphism X Z := {|
  continuous_map := setoid_morphism_compose g f;
  continuity := fun U H => continuity f _ (continuity g U H)
|}.

Lemma top_compose_respects {X Y Z : TopSpace} :
  Proper (equiv ==> equiv ==> equiv) (@top_compose X Y Z).
Proof.
  intros g1 g2 Hg f1 f2 Hf x; simpl.
  rewrite (Hg (continuous_map f1 x)).
  apply proper_morphism, Hf.
Qed.

(*
 The category of topological spaces and continuous maps.  The category
 laws hold pointwise on the map parts, exactly as in [Sets]; the
 continuity witnesses play no part because the hom-setoid ignores them. 

 --------
 拓扑空间与连续映射的范畴。范畴定律在映射部分逐点成立，正如在 [Sets] 中一样；连续性见证不参与其中，因为 Hom-集合等价忽略了它们。
*)
(*
   【Top 范畴实例展开】/ Top instance walkthrough
   （薄注即可；受众同 Functor.v）

   1) 这是什么 / What this is
      Top = 拓扑空间与连续映射：对象 TopSpace；态射 ContinuousMorphism。
      Topology spaces + continuous maps.
      ≈ 只看底层 setoid 映射逐点，连续性证明不参与相等（与 Sets 同风格）。
      ≈ ignores continuity witnesses; compares underlying maps.

   2) 关键字段 / Key fields
      - obj := TopSpace；hom := ContinuousMorphism
      - homset := ContinuousMorphism_Setoid；id/compose := top_id/_compose

   Haskell 对照：无直接对应；可想成「带开集数据的 Sets」。
   Analogy: Sets equipped with open-set data.

   阅读：TopSpace/Continuous → Top → Terminal/Initial → 子范畴（Hausdorff 等）。
   Read: spaces/maps → Top → (co)limits → subcategories.
*)
Program Definition Top : Category := {|
  obj     := TopSpace;
  hom     := ContinuousMorphism;
  homset  := @ContinuousMorphism_Setoid;
  id      := @top_id;
  compose := @top_compose;

  compose_respects := @top_compose_respects
|}.

(** ** Two extreme topologies / ** 两种极端拓扑 *)

Section Discrete.

Context (A : SetoidObject).

(*
 The discrete topology: EVERY predicate that respects the carrier's `≈`
 is open.  Setoid bookkeeping is the only constraint left; this is the
 finest topology on A. 

 --------
 离散拓扑：每一个尊重载体 `≈` 的谓词都是开集。集合等价关系的记账是唯一剩下的约束；这是 A 上最细的拓扑。
*)
Definition discrete_open (U : A → Type) : Type :=
  ∀ x y : A, x ≈ y → U x → U y.

Lemma discrete_respects (U V : A → Type) :
  (∀ x, U x ↔ V x) → discrete_open U → discrete_open V.
Proof.
  intros HUV HU x y Hxy Vx.
  exact (fst (HUV y) (HU x y Hxy (snd (HUV x) Vx))).
Qed.

Lemma discrete_union (I : Type) (U : I → (A → Type)) :
  (∀ i, discrete_open (U i)) → discrete_open (fun x => { i : I & U i x }).
Proof.
  intros HU x y Hxy w.
  exact (projT1 w; HU (projT1 w) x y Hxy (projT2 w)).
Qed.

Lemma discrete_whole : discrete_open (fun _ => poly_unit).
Proof. intros x y Hxy w; exact w. Qed.

Lemma discrete_inter (U V : A → Type) :
  discrete_open U → discrete_open V → discrete_open (fun x => U x ∧ V x).
Proof.
  intros HU HV x y Hxy w.
  exact (HU x y Hxy (fst w), HV x y Hxy (snd w)).
Qed.

Definition Discrete_Top : TopSpace := {|
  top_carrier    := A;
  IsOpen         := discrete_open;
  open_respects  := discrete_respects;
  open_proper    := fun _ H => H;
  open_union     := discrete_union;
  open_whole     := discrete_whole;
  open_inter     := discrete_inter
|}.

End Discrete.

Section Indiscrete.

Context (A : SetoidObject).

(*
 The indiscrete (coarsest) topology.  The textbook presentation is
 `{∅, X}`, but that collection is NOT closed under arbitrary unions
 constructively: given a family of members, deciding whether some member
 is the whole space (so that the union is the whole space) rather than
 all of them being empty (so that the union is empty) is precisely an
 instance of excluded middle, and no such decision is available.
 The constructive rendering keeps the UNIFORM predicates: those that hold
 everywhere as soon as they hold somewhere.  Classically the uniform
 predicates are exactly ∅ and X, so this agrees with the textbook
 definition; constructively it is closed under everything required, and
 by [open_uniform] it is contained in every topology on A — which makes
 every setoid map into an indiscrete space continuous
 ([into_indiscrete_continuous] below). 

 --------
 不连续（最粗）拓扑。教材中的表示是 `{∅, X}`，但该集合在任意并下并不封闭：从构造上讲，给定一族成员，要判断是否有某个成员是整个空间（从而并是整个空间），而不是所有成员都是空的（从而并为空），这恰好是排中律的一个实例，而没有这样的判定方法。构造性表述保持了统一谓词：一旦它们在某处成立，就在所有地方都成立。从经典角度看，统一谓词正好是 ∅ 和 X，因此这与教材中的定义一致；从构造角度看，它在所有必要情况下都是封闭的，并且根据 [open_uniform]，它包含在 A 上的每个拓扑中 —— 这使得每个集合同态映射到不可分空间都是连续的（见下面的 [into_indiscrete_continuous]）。
*)
Definition indiscrete_open (U : A → Type) : Type :=
  ∀ x y : A, U x → U y.

Lemma indiscrete_respects (U V : A → Type) :
  (∀ x, U x ↔ V x) → indiscrete_open U → indiscrete_open V.
Proof.
  intros HUV HU x y Vx.
  exact (fst (HUV y) (HU x y (snd (HUV x) Vx))).
Qed.

Lemma indiscrete_proper (U : A → Type) :
  indiscrete_open U → ∀ x y : A, x ≈ y → U x → U y.
Proof. intros HU x y _ Ux; exact (HU x y Ux). Qed.

Lemma indiscrete_union (I : Type) (U : I → (A → Type)) :
  (∀ i, indiscrete_open (U i)) → indiscrete_open (fun x => { i : I & U i x }).
Proof.
  intros HU x y w.
  exact (projT1 w; HU (projT1 w) x y (projT2 w)).
Qed.

Lemma indiscrete_whole : indiscrete_open (fun _ => poly_unit).
Proof. intros x y w; exact w. Qed.

Lemma indiscrete_inter (U V : A → Type) :
  indiscrete_open U → indiscrete_open V →
  indiscrete_open (fun x => U x ∧ V x).
Proof.
  intros HU HV x y w.
  exact (HU x y (fst w), HV x y (snd w)).
Qed.

Definition Indiscrete_Top : TopSpace := {|
  top_carrier    := A;
  IsOpen         := indiscrete_open;
  open_respects  := indiscrete_respects;
  open_proper    := indiscrete_proper;
  open_union     := indiscrete_union;
  open_whole     := indiscrete_whole;
  open_inter     := indiscrete_inter
|}.

End Indiscrete.

(* Every setoid map into an indiscrete space is continuous. The preimage of a uniform predicate is uniform, and by [open_uniform] every uniform predicate is open in every space. / 每个集合等价类映射到一个无分离空间都是连续的。均匀谓词的逆像是均匀的，并且根据 [open_uniform]，每个均匀谓词在每个空间中都是开的。 *)
Lemma into_indiscrete_continuous (X : TopSpace) (A : SetoidObject)
      (f : SetoidMorphism (top_carrier X) A) :
  Continuous X (Indiscrete_Top A) f.
Proof.
  intros U HU.
  apply open_uniform.
  intros x y Ufx.
  exact (HU (f x) (f y) Ufx).
Qed.

(* Dually, every setoid map out of a discrete space is continuous: the preimage of any open respects `≈` because the map does. / 同样地，从离散空间出的每一个集合等价映射都是连续的：任何开集的原像都遵循 `≈`，因为映射本身是连续的。 *)
Lemma out_of_discrete_continuous (A : SetoidObject) (Y : TopSpace)
      (f : SetoidMorphism A (top_carrier Y)) :
  Continuous (Discrete_Top A) Y f.
Proof.
  intros U HU x y Hxy Ufx.
  exact (open_proper Y U HU (f x) (f y) (proper_morphism f x y Hxy) Ufx).
Qed.

(*
 The constant setoid map, and its respectfulness certificate.  These are
 spelled out rather than left to [Program] because instance resolution
 solves the [Proper] goal with a lemma whose universes are pinned to
 [Set], which would in turn pin the carrier universe of every space
 receiving a constant map.  Supplying the field explicitly keeps the
 construction universe-polymorphic — the discipline the header's point 2
 describes. 

 --------
 恒定集同态映射及其尊重性证明。这些被明确说明，而不是留给 [Program]，因为实例解析通过一个其宇宙固定为 [Set] 的引理解决了 [Proper] 目标，这反过来会固定接收恒定映射的每个空间的载体宇宙。显式提供该字段可以保持构造的宇宙多态性——这是标题第2点所描述的规范。
*)
Lemma const_proper (A B : SetoidObject) (b : B) :
  Proper (respectful equiv equiv) (fun _ : A => b).
Proof. intros u v Huv; reflexivity. Qed.

Definition const_morphism (A B : SetoidObject) (b : B) : SetoidMorphism A B := {|
  morphism        := fun _ => b;
  proper_morphism := const_proper A B b
|}.

(** ** Terminal and initial objects / ** 终对象和始对象 *)

(* The one-point space. Its carrier is the singleton setoid used by [Sets_Terminal]; the topology is discrete (on a one-point carrier the discrete and indiscrete topologies agree). / 单点空间。它的承载体是 [Sets_Terminal] 使用的单例集合；拓扑是离散的（在单点承载体上，离散拓扑和不可分拓扑是一致的）。 *)
Definition Point_Top : TopSpace := Discrete_Top unit_setoid_object.

(* Terminality. The unique map sends everything to the point; its continuity is [open_const], since the preimage of any predicate on a single point is a CONSTANT predicate upstairs. / 终端性。这个唯一的映射将一切都送到那个点；它的连续性是[open_const]，因为对单个点上的任何谓词的逆像在上层都是一个常量谓词。 *)
Definition top_one (X : TopSpace) : ContinuousMorphism X Point_Top := {|
  continuous_map := const_morphism (top_carrier X) (top_carrier Point_Top) ttt;
  continuity := fun U _ => open_const X (U ttt)
|}.

(*
 Any two maps into the point agree, since the codomain has exactly one
 element up to `≈`.  The universes of this lemma and of the instance
 below are annotated for the same reason as [ContinuousMorphism_equiv]:
 left to inference, elaboration pinned the space level of [Point_Top] to
 `Set`, which quietly MONOMORPHIZED the whole [Terminal] instance — the
 terminal object then no longer applied to spaces whose carrier lives
 above `Set`, contradicting the header's promise that [Top] exists at
 every level.  (Caught by the audit of the first commit, which also
 verified this annotation restores polymorphism.) 

 --------
 任意两个映射到一个点是相同的，因为值域至多有一个元素。该引理及下面实例的宇宙标注原因与前面相同：左侧推理时，展开将 [Point_Top] 的空间层级固定为 `Set`，这静默地将整个 [Terminal] 实例单态化——于是终端对象不再适用于其载体高于 `Set` 的空间，与标题中承诺 [Top] 在每个层级存在的说法相矛盾。（在第一次提交的审核中发现，这次审核还验证了此标注恢复了多态性。）
*)
Lemma top_one_unique@{o h p}
  (X : TopSpace@{o}) (f g : X ~{Top@{h o}}~> Point_Top@{o}) : f ≈ g.
Proof.
  intro x.
  destruct (continuous_map f x), (continuous_map g x); reflexivity.
Qed.

#[export]
Program Instance Top_Terminal@{o h p} : @Terminal Top@{h o} := {
  terminal_obj := Point_Top@{o};
  one := @top_one@{h o};
  one_unique := @top_one_unique@{o h p}
}.

(* The empty space: carrier [False], every predicate open (vacuously, since the discrete condition quantifies over points that do not exist). / 空白空间：载体 [False]，每个谓词都是开放的（空洞地，因为离散条件对不存在的点进行量化）。 *)
Definition Empty_Top : TopSpace :=
  Discrete_Top {| carrier := False; is_setoid := False_Setoid |}.

Definition empty_map (X : TopSpace) :
  SetoidMorphism (top_carrier Empty_Top) (top_carrier X).
Proof.
  refine {| morphism := fun z : False => False_rect _ z |}.
  repeat intro; contradiction.
Defined.

Definition top_zero (X : TopSpace) : ContinuousMorphism Empty_Top X.
Proof.
  refine {| continuous_map := empty_map X |}.
  intros U HU; repeat intro; contradiction.
Defined.

(*
 Any two maps out of the empty space agree, there being no point at which
 they could differ. 

 --------
 在空集中的任意两幅映射都是相同的，因为没有任何点使它们可能不同。
*)
Lemma top_zero_unique (X : TopSpace) (f g : Empty_Top ~{Top}~> X) : f ≈ g.
Proof. intro z; contradiction. Qed.

#[export]
Program Instance Top_Initial : @Initial Top := {
  terminal_obj := Empty_Top;
  one := top_zero;
  one_unique := top_zero_unique
}.

(*
 [Top] has NO zero object, and this is a THEOREM rather than an aside:
 a zero object would be simultaneously terminal and initial, the point
 space maps into any terminal object, any initial object maps into the
 empty space, and the coincidence iso would then manufacture an
 inhabitant of [False] out of [ttt].  (The first commit merely asserted
 this in a comment; the audit asked for the two-line proof.) 

 --------
 [Top] 没有零对象，这是一个定理而不是附注：
 一个零对象将同时是终对象和初对象，点空间映射到任何终对象，任何初对象映射到空空间，然后同构巧合将从 [ttt] 制造出 [False] 的一个元件。（第一次提交只是通过注释断言了这一点；审计要求给出两行证明。）
*)
Theorem Top_no_zero_object : @ZeroObject Top → False.
Proof.
  intros [T I coincide].
  exact (continuous_map (@zero _ I Empty_Top)
           (from coincide (continuous_map (@one _ T Point_Top) ttt))).
Qed.

(*
 The concrete instance of the same fact: the chosen terminal and initial
 objects themselves are not isomorphic. 

 --------
 同一事实的具体实例：所选择的终端对象和初始对象本身不是同构的。
*)
Example point_not_iso_empty : Point_Top ≅[Top] Empty_Top → False.
Proof. intro iso; exact (continuous_map (to iso) ttt). Qed.

(* * ** Monomorphisms are the injections / * ** 单射是注入 *)

(*
 Injectivity up to `≈` characterizes the monos of [Top].  The hard
 direction probes f with the two constant maps out of the one-point
 space, exactly as [injectivity_is_monic] does in Instance/Sets.v; the
 probes are continuous by [open_const]. 

 --------
 到 `≈` 的单射性刻画了 [Top] 的单态。困难的方向用来自一点评空间的两个常映射探测 f，正如 [injectivity_is_monic] 在 Instance/Sets.v 中所做的那样；根据 [open_const]，这些探测是连续的。
*)
Definition top_point (X : TopSpace) (a : X) :
  ContinuousMorphism Point_Top X := {|
  continuous_map := const_morphism (top_carrier Point_Top) (top_carrier X) a;
  continuity := fun U _ => open_const Point_Top (U a)
|}.

Theorem top_monic_iff {X Y : TopSpace} (f : X ~{Top}~> Y) :
  (∀ a b : X, f a ≈ f b → a ≈ b) ↔ Monic f.
Proof.
  split.
  - intros Hinj.
    constructor; intros Z g1 g2 Hg z.
    exact (Hinj (continuous_map g1 z) (continuous_map g2 z) (Hg z)).
  - intros [Hmonic] a b Hab.
    exact (Hmonic Point_Top (top_point X a) (top_point X b)
                  (fun _ => Hab) ttt).
Qed.

(* * ** Epimorphisms are the surjections / * ** 上射是满射 *)

(*
 Membership in the image, as a Type-valued sigma: the same shape
 Instance/Sets.v uses in [surjectivity_is_epic] and Lib/Setoid.v's
 [surjective] class, namely a CHOSEN preimage rather than a
 propositional truncation.  In a setoid library this is the honest
 reading — the round trip in [bijective_is_iso] recovers an actual
 inverse function from it, with no appeal to choice. 

 --------
 在像中的成员资格，作为一个类型值的σ：与 Instance/Sets.v 中在 [surjectivity_is_epic] 和 Lib/Setoid.v 的 [surjective] 类中使用的形状相同，即选择的原像，而不是命题性截断。在集合同构库中，这是正确的解释——在 [bijective_is_iso] 中的往返恢复了实际的逆函数，而无需诉诸选择。
*)
Definition InImage {X Y : TopSpace} (f : X ~{Top}~> Y) (b : Y) : Type :=
  ∃ a : X, f a ≈ b.

(* The image predicate respects the codomain's equality. / 像的谓词遵守陪域的相等性。 *)
Lemma InImage_respects {X Y : TopSpace} (f : X ~{Top}~> Y) (b b' : Y) :
  b ≈ b' → InImage f b → InImage f b'.
Proof.
  intros Hbb w.
  exact (projT1 w; transitivity (projT2 w) Hbb).
Qed.

(*
 *** The cokernel-pair space

 The unconditional constructive proof that epis in [Top] are surjective.
 Given f : X ~> Y, glue two copies of Y along the image of f: the carrier
 is `Y + Y`, and the two copies are identified EXACTLY over the image.
 No inductive closure of a generating relation is needed — the relation
 below is already transitive, because “lies in the image” transports
 along `≈` ([InImage_respects]).  A predicate is open when it respects
 the gluing and both of its restrictions along the two legs are open in
 Y.  The two legs then agree after f, so an epi f forces the legs to be
 equal, which says precisely that every point of Y lies in the image.

 This argument is fully constructive: no decidability hypothesis, no
 choice, and — unlike the classical two-point probe recalled below and
 unlike the truth-value route Instance/Sets.v currently documents — no
 jump to a higher universe, since `Y + Y` sits at the same level as Y.
 (The route, not the statement, is what jumps there; see the note before
 the indiscrete probe below.) 

 --------
 *** 余核对空间

 在 [Top] 中，闪射态（epis）是满射的无条件构造性证明。
 给定 f : X ~> Y，将两个 Y 的副本沿 f 的像粘合：载体是 `Y + Y`，并且两个副本在像上完全相同地被识别。
 不需要生成关系的归纳闭包——下面的关系已经是传递的，因为“属于像”可以沿 `≈`（[InImage_respects]）传递。当一个谓词符合这种粘合且其沿两条腿的限制在 Y 中都是开集时，它就是开集。然后，两条腿在 f 之后一致，因此一个闪射态 f 强制两条腿相等，这正好说明 Y 的每个点都在像中。这个论证是完全构造性的：没有可判定性假设，没有选择，而且——不同于下面回顾的经典两点探针，也不同于 Instance/Sets.v 当前记录的真值路线——没有跳到更高的宇宙，因为 `Y + Y` 位于与 Y 相同的层次。（是路线，而不是陈述，跳到了那里；见下文关于不连续探针之前的注释。）
*)

Section CokernelPair.

Context {X Y : TopSpace}.
Context (f : X ~{Top}~> Y).

(* The glued carrier: two copies of the points of Y. / 粘合载体：Y 的两份点的副本。 *)
Definition CP_point : Type := Datatypes.sum (carrier (top_carrier Y))
                                            (carrier (top_carrier Y)).

(*
 The gluing relation.  Within a copy it is Y's own equality; across the
 copies it additionally demands membership in the image of f. 

 --------
 粘接关系。在一个副本内，它是 Y 自身的等式；在副本之间，它还要求属于 f 的像。
*)
Definition CP_rel (u v : CP_point) : Type :=
  match u, v with
  | Datatypes.inl y, Datatypes.inl y' => y ≈ y'
  | Datatypes.inr y, Datatypes.inr y' => y ≈ y'
  | Datatypes.inl y, Datatypes.inr y' => (y ≈ y') ∧ InImage f y
  | Datatypes.inr y, Datatypes.inl y' => (y ≈ y') ∧ InImage f y
  end.

Lemma CP_rel_refl : Reflexive CP_rel.
Proof. intros [y|y]; simpl; reflexivity. Qed.

Lemma CP_rel_sym : Symmetric CP_rel.
Proof.
  intros [y|y] [y'|y'] H; simpl in *.
  - now symmetry.
  - exact (symmetry (fst H), InImage_respects f y y' (fst H) (snd H)).
  - exact (symmetry (fst H), InImage_respects f y y' (fst H) (snd H)).
  - now symmetry.
Qed.

Lemma CP_rel_trans : Transitive CP_rel.
Proof.
  intros [a|a] [b|b] [c|c] H1 H2; simpl in *.
  (* inl inl inl / inl inl inl *) - now transitivity b.
  (* inl inl inr / inl inl inr *) - exact (transitivity H1 (fst H2),
                             InImage_respects f b a (symmetry H1) (snd H2)).
  (* inl inr inl / inl inr inl *) - exact (transitivity (fst H1) (fst H2)).
  (* inl inr inr / inl inr inr *) - exact (transitivity (fst H1) H2, snd H1).
  (* inr inl inl / inr inl inl *) - exact (transitivity (fst H1) H2, snd H1).
  (* inr inl inr / inr inl inr *) - exact (transitivity (fst H1) (fst H2)).
  (* inr inr inl / inr inr inl *) - exact (transitivity H1 (fst H2),
                             InImage_respects f b a (symmetry H1) (snd H2)).
  (* inr inr inr / 印度卢比 印度卢比 印度卢比 *) - now transitivity b.
Qed.

Definition CP_Setoid : Setoid CP_point := {|
  equiv := CP_rel;
  setoid_equiv := Build_Equivalence CP_rel CP_rel_refl CP_rel_sym CP_rel_trans
|}.

Definition CP_carrier : SetoidObject :=
  {| carrier := CP_point; is_setoid := CP_Setoid |}.

(* A glued predicate is open when it respects the gluing and restricts to an open along each of the two legs. / 当一个粘贴谓词遵守粘贴并且在两条分支上各自限制为开放时，它是开放的。 *)
Definition CP_open (W : CP_carrier → Type) : Type :=
  ((∀ u v, CP_rel u v → W u → W v)
     ∧ IsOpen Y (fun y => W (Datatypes.inl y))
     ∧ IsOpen Y (fun y => W (Datatypes.inr y)))%type.

Lemma CP_respects (W W' : CP_carrier → Type) :
  (∀ u, W u ↔ W' u) → CP_open W → CP_open W'.
Proof.
  intros HW HO.
  refine (_, (_, _)).
  - intros u v Huv W'u.
    exact (fst (HW v) (fst HO u v Huv (snd (HW u) W'u))).
  - exact (open_respects Y _ _ (fun y => HW (Datatypes.inl y)) (fst (snd HO))).
  - exact (open_respects Y _ _ (fun y => HW (Datatypes.inr y)) (snd (snd HO))).
Qed.

Lemma CP_proper (W : CP_carrier → Type) :
  CP_open W → ∀ u v : CP_carrier, u ≈ v → W u → W v.
Proof. intros HO u v Huv; exact (fst HO u v Huv). Qed.

Lemma CP_union (I : Type) (W : I → (CP_carrier → Type)) :
  (∀ i, CP_open (W i)) → CP_open (fun u => { i : I & W i u }).
Proof.
  intro HW.
  refine (_, (_, _)).
  - intros u v Huv w.
    exact (projT1 w; fst (HW (projT1 w)) u v Huv (projT2 w)).
  - exact (open_union Y I (fun i y => W i (Datatypes.inl y))
                      (fun i => fst (snd (HW i)))).
  - exact (open_union Y I (fun i y => W i (Datatypes.inr y))
                      (fun i => snd (snd (HW i)))).
Qed.

Lemma CP_whole : CP_open (fun _ => poly_unit).
Proof. exact (fun _ _ _ w => w, (open_whole Y, open_whole Y)). Qed.

Lemma CP_inter (W W' : CP_carrier → Type) :
  CP_open W → CP_open W' → CP_open (fun u => W u ∧ W' u).
Proof.
  intros HO HO'.
  refine (_, (_, _)).
  - intros u v Huv w.
    exact (fst HO u v Huv (fst w), fst HO' u v Huv (snd w)).
  - exact (open_inter Y _ _ (fst (snd HO)) (fst (snd HO'))).
  - exact (open_inter Y _ _ (snd (snd HO)) (snd (snd HO'))).
Qed.

Definition CokernelPair : TopSpace := {|
  top_carrier   := CP_carrier;
  IsOpen        := CP_open;
  open_respects := CP_respects;
  open_proper   := CP_proper;
  open_union    := CP_union;
  open_whole    := CP_whole;
  open_inter    := CP_inter
|}.

(*
 The two legs.  Each is a setoid map by construction (within a copy the
 gluing relation IS Y's equality), and continuous because the two
 restriction conditions are literally the second and third components of
 [CP_open]. 

 --------
 这两条腿。每一条从构造上都是一个集合同态映射（在一个副本中，粘合关系就是 Y 的等式），并且是连续的，因为这两个限制条件实际上是 [CP_open] 的第二和第三个分量。
*)
Definition CP_inl : SetoidMorphism (top_carrier Y) CP_carrier.
Proof.
  refine {| morphism := Datatypes.inl |}.
  intros u v Huv; exact Huv.
Defined.

Definition CP_inr : SetoidMorphism (top_carrier Y) CP_carrier.
Proof.
  refine {| morphism := Datatypes.inr |}.
  intros u v Huv; exact Huv.
Defined.

Definition CP_leftLeg : ContinuousMorphism Y CokernelPair :=
  Build_ContinuousMorphism Y CokernelPair CP_inl (fun W HW => fst (snd HW)).

Definition CP_rightLeg : ContinuousMorphism Y CokernelPair :=
  Build_ContinuousMorphism Y CokernelPair CP_inr (fun W HW => snd (snd HW)).

(*
 The defining coequalizing property: the legs agree after f, because at a
 point of the image the gluing relation holds — witnessed by the very
 preimage that puts the point in the image. 

 --------
 定义的共等化性质：在 f 之后，各条腿是一致的，因为在像的一个点处，粘合关系成立——由将该点置于像中的原像本身证明。
*)
Lemma CP_legs_agree :
  CP_leftLeg ∘[Top] f ≈ CP_rightLeg ∘[Top] f.
Proof.
  intro a; simpl.
  refine (_, _).
  - reflexivity.
  - refine (a; _); reflexivity.
Qed.

End CokernelPair.

(*
 Epimorphisms of [Top] are exactly the surjections, unconditionally.

 Forward: a surjection is right-cancellable pointwise.  Backward: apply
 the epi to the two legs of the cokernel-pair space, which agree after f
 by [CP_legs_agree]; the resulting equality of legs says that for every
 b the glued points `inl b` and `inr b` are related, and by construction
 that relation carries a preimage of b. 

 --------
 [Top] 的上同态正好是满射，无条件。

 正向：一个满射在每一点上是右可约的。反向：将上同态应用于余核对空间的两条腿，在 f 之后通过 [CP_legs_agree] 它们相等；两条腿的结果相等意味着对于每个 b，粘合点 `inl b` 和 `inr b` 是相关的，并且根据构造，该关系带有 b 的原像。
*)
Theorem top_epic_iff {X Y : TopSpace} (f : X ~{Top}~> Y) :
  (∀ b : Y, ∃ a : X, f a ≈ b) ↔ Epic f.
Proof.
  split.
  - intros Hsurj.
    constructor; intros Z g1 g2 Hg b.
    destruct (Hsurj b) as [a Ha].
    rewrite <- Ha.
    exact (Hg a).
  - intros [Hepic] b.
    exact (snd (Hepic (CokernelPair f) (CP_leftLeg f) (CP_rightLeg f)
                      (CP_legs_agree f) b)).
Qed.

(* The same statement in cokernel-pair form, naming the construction that does the work. / 以余核对形式表达的相同语句，命名执行该工作的构造。 *)
Theorem top_epic_surjective_via_cokernel_pair
        {X Y : TopSpace} (f : X ~{Top}~> Y) :
  Epic f → ∀ b : Y, InImage f b.
Proof. intro He; exact (snd (top_epic_iff f) He). Qed.

(* * ** The classical two-point probe, and its constructive status / * ** 经典的双探针及其建设状态 *)

(*
 The textbook proof that epis of Top are surjective probes f with two maps
 into the two-point INDISCRETE space — not the Sierpinski space, whose
 topology `{∅, {1}, Z}` characterizes DENSE images rather than surjective
 ones: the constant map at [true] and the characteristic map of the image.
 The
 two agree after f, so an epi makes them equal, and evaluating at b says b
 is in the image.

 Constructively the characteristic map is the obstruction: forming
 `fun b => if b ∈ im f then true else false` requires DECIDING image
 membership, which is exactly the hypothesis [dec] below.  So this route
 is hypothesis-scoped.  The unconditional theorem is
 [top_epic_surjective_via_cokernel_pair] above, which replaces the
 two-element codomain by the cokernel-pair space and needs no decision
 procedure at all; that contrast is the documented constructive status of
 the classical argument.  (Instance/Sets.v currently reaches the same
 statement differently: its note at [surjectivity_is_epic] routes the
 converse through a truth-value object one universe up, keeps the whole
 lemma out of the environment, and defers the cross-universe statements
 to Instance/Sets/Classifier.v.  That obstruction belongs to the
 truth-value ROUTE, not to the statement: the cokernel-pair argument
 used here works at a single universe in [Sets] as well — the audit of
 this file's first commit checked so by transplanting the construction —
 and carrying that upgrade into Instance/Sets.v is the business of the
 epis-are-surjections issue #245, not of this file.) 

 --------
 教科书中证明 Top 类范畴中的指标（epi）是满射的一般方法是将 f 与两个映射映射到两点不可分空间——而不是 Sierpinski 空间，其拓扑结构 `{∅, {1}, Z}` 描述的是稠密像而非满射像：一个是常值映射到 [true]，另一个是像的特征映射。经过 f 后这两个映射一致，因此指标使它们相等，并在 b 点取值时说明 b 在像中。从构造上讲，特征映射就是障碍：形成 `fun b => if b ∈ im f then true else false` 需要决定图像的成员资格，这正是下面的假设 [dec]。因此，这条路径是以假设为范围的。无条件的定理是上面的 [top_epic_surjective_via_cokernel_pair]，它用余核对空间替代了双元素陪域，完全不需要决策过程；这种对比就是对经典论证的构造性状态的记录。（Instance/Sets.v 目前以不同方式得到同一结论：它在 [surjectivity_is_epic] 的注释将逆向路由到高一个宇宙的真值对象，保持整个引理不在环境中，并将跨宇宙的陈述推迟到 Instance/Sets/Classifier.v。）该阻碍属于真值路径，而不属于该陈述：这里使用的余核对 argument 在 [Sets] 的单一宇宙中也适用——通过移植该构造，本文件的首次提交审计已经验证了这一点——并将该升级应用到 Instance/Sets.v 是 epis-are-surjections 问题 #245 的事务，而不是本文件的事务。
*)

Definition bool_setoid_object : SetoidObject := {|
  carrier   := bool;
  is_setoid := {| equiv := @eq bool; setoid_equiv := eq_equivalence |}
|}.

(*
 The two-point indiscrete space used as the probe.  Every setoid map into
 it is continuous ([into_indiscrete_continuous]), which is the only
 property of it the argument uses. 

 --------
 用作探针的两点不可分空间。映入它的每个集合映射都是连续的（[into_indiscrete_continuous]），这是论证中使用它的唯一性质。
*)
Definition TwoPoint_Indiscrete : TopSpace := Indiscrete_Top bool_setoid_object.

Section IndiscreteProbe.

Context {X Y : TopSpace}.
Context (f : X ~{Top}~> Y).
Context (dec : ∀ b : Y, InImage f b ∨ ¬ (InImage f b)).

(* The characteristic function of the image, read off the decision. / 图像的特征函数，根据它作出决策。 *)
Definition image_char (b : Y) : bool :=
  match dec b with
  | Datatypes.inl _ => true
  | Datatypes.inr _ => false
  end.

Definition image_char_setoid_map :
  SetoidMorphism (top_carrier Y) bool_setoid_object.
Proof using X Y dec f.
  refine {| morphism := image_char |}.
  intros b b' Hbb; unfold image_char.
  destruct (dec b) as [w|n], (dec b') as [w'|n'].
  - reflexivity.
  - destruct (n' (InImage_respects f b b' Hbb w)).
  - destruct (n (InImage_respects f b' b (symmetry Hbb) w')).
  - reflexivity.
Defined.

Definition image_char_map : ContinuousMorphism Y TwoPoint_Indiscrete :=
  Build_ContinuousMorphism Y TwoPoint_Indiscrete image_char_setoid_map
    (into_indiscrete_continuous Y bool_setoid_object image_char_setoid_map).

Definition always_true_setoid_map :
  SetoidMorphism (top_carrier Y) bool_setoid_object :=
  const_morphism (top_carrier Y) bool_setoid_object true.

Definition always_true_map : ContinuousMorphism Y TwoPoint_Indiscrete :=
  Build_ContinuousMorphism Y TwoPoint_Indiscrete always_true_setoid_map
    (into_indiscrete_continuous Y bool_setoid_object always_true_setoid_map).

(* The classical route, made honest: under [dec], an epi is surjective. / 经典路线，诚实实现：在 [dec] 下，一个上射是满射的。 *)
Theorem top_epic_surjective_via_indiscrete :
  Epic f → ∀ b : Y, InImage f b.
Proof using X Y dec f.
  intros [Hepic] b.
  assert (Hagree : always_true_map ∘[Top] f ≈ image_char_map ∘[Top] f).
  { intro a; simpl; unfold image_char.
    destruct (dec (continuous_map f a)) as [w|n].
    - reflexivity.
    - exfalso; apply n; refine (a; _); reflexivity. }
  pose proof (Hepic TwoPoint_Indiscrete always_true_map image_char_map Hagree b)
    as Heq.
  simpl in Heq; unfold image_char in Heq.
  destruct (dec b) as [w|n].
  - exact w.
  - discriminate Heq.
Qed.

End IndiscreteProbe.

(** ** Open covers / ** 打开盖子 *)

(*
 Fong and Spivak, “Seven Sketches in Compositionality”, §7.3.2,
 Definition 7.25: a family of opens covers a set when the set is the union
 of the family.  Stated here at the level of predicates: the covered
 predicate is pointwise equivalent to the union of the family, and every
 member of the family is open. 

 --------
 Fong 和 Spivak，《组合性中的七个草图》，§7.3.2，定义 7.25：当一个集合等于一个开集族的并集时，该开集族覆盖该集合。在谓词层面上表述：被覆盖的谓词在每一点上等价于该族的并集，并且该族的每一个成员都是开集。
*)
Definition Covers {X : TopSpace} {I : Type}
           (U : I → (X → Type)) (V : X → Type) : Type :=
  ((∀ i, IsOpen X (U i)) ∧ (∀ x : X, V x ↔ ∃ i : I, U i x))%type.

(*
 The empty family covers the empty predicate — the nullary instance of the
 definition: with no members the union is empty, so what the family covers
 is exactly the empty predicate. 

 --------
 空族覆盖了空谓词——定义的零元实例：由于没有成员，联合为空，因此族所覆盖的正是空谓词。
*)
Definition covers_nothing (X : TopSpace) :
  Covers (X:=X) (I:=False) (fun _ _ => False) (fun _ => False).
Proof.
  split.
  - intro i; contradiction.
  - intro x; split.
    + contradiction.
    + intro w; exact (projT2 w).
Defined.

(* The one-member family consisting of the whole space covers the whole space. / 由整个空间组成的一个成员家庭覆盖整个空间。 *)
Definition covers_whole (X : TopSpace) :
  Covers (X:=X) (I:=poly_unit) (fun _ _ => poly_unit) (fun _ => poly_unit).
Proof.
  split.
  - intro i; exact (open_whole X).
  - intro x; split.
    + intro w; exact (ttt; w).
    + intro w; exact (projT2 w).
Defined.

(** ** Separation and compactness / ** 分离与紧凑 *)

(*
 Hausdorff (T2): distinct points are separated by disjoint opens.  This is
 the literal classical separation axiom, with “distinct” rendered as
 `¬ (x ≈ y)` (apartness in the carrier's own equality) and the existential
 as a Σ-type carrying the two chosen opens.  A constructive topologist
 would usually prefer a positive apartness relation; that refinement is
 out of scope here, where the work order asks only for the definition. 

 --------
 Hausdorff (T2)：不同的点被不相交的开集分开。这是字面上的经典分离公理，其中“不同”被表示为 `¬ (x ≈ y)`（载体自身的平等中的分离性），而存在性则以 Σ 型呈现，携带两个选择的开集。一个构造性的拓扑学家通常会更喜欢一个正分离关系；这一细化超出了此处的范围，这里的工作顺序仅要求定义。
*)
Definition IsHausdorff (X : TopSpace) : Type :=
  ∀ x y : X, ¬ (x ≈ y) →
    ∃ U : X → Type, ∃ V : X → Type,
      ((IsOpen X U ∧ IsOpen X V)
         ∧ (U x ∧ V y)
         ∧ (∀ z : X, U z → V z → False))%type.

(*
 Compactness of the WHOLE space: every open cover of the whole space has a
 finite subcover, presented as a list of indices together with, for each
 point, a member of that list covering it.  The finiteness is the list;
 the choice of index for each point is data, as everywhere in this
 library. 

 --------
 整个空间的紧致性：整个空间的每个开覆盖都有一个有限子覆盖，该子覆盖表示为一个索引列表，并且对于每个点，给出覆盖它的列表成员。有限性体现在列表上；对于每个点选择索引是数据，就像在本库的其他地方一样。
*)
Definition IsCompact (X : TopSpace) : Type :=
  ∀ (I : Type) (U : I → (X → Type)),
    Covers U (fun _ => poly_unit) →
    ∃ l : list I, ∀ x : X, ∃ i : I, (List.In i l ∧ U i x)%type.

(*
 Non-vacuity: the one-point space satisfies both predicates, so neither
 subcategory below is empty.  Compactness is witnessed by the singleton
 list containing the index that covers the point; the separation axiom is
 satisfied vacuously, there being no pair of distinct points to
 separate — exactly the classical situation.
 CORRECTION (#455): as proved, [Point_Hausdorff] is monomorphised at a
 [Set] carrier (About: [Point_Hausdorff@{u} : IsHausdorff@{u Set Set Set}
 Point_Top@{Set}]), so it witnesses the separation half only at the
 [Set]-carrier instances of [Top]; [Point_Compact] is universe-general.
 Instance/Top/StoneCech.v's [Discrete_Hausdorff] separates every discrete
 space at every universe, and its [Point_CH] is the one-point space as an
 object of [CompHaus] at every carrier universe. 

 --------
 非空性：一点评空间满足两个谓词，因此下面的子类别都不为空。紧性可以通过包含覆盖该点的索引的单例列表来证明；分离公理可以通过虚设满足，因为没有不同的点对需要分离——这正是经典情况。
 修正（#455）：如已证明，[Point_Hausdorff] 在 [Set] 载体上被单态化（关于：[Point_Hausdorff@{u} : IsHausdorff@{u Set Set Set} Point_Top@{Set} ]），因此它仅在 [Set] -载体实例的 [Top] 上证明了分离的一半；[Point_Compact] 是宇宙通用的。Instance/Top/StoneCech.v 的 [Discrete_Hausdorff] 在每个宇宙上分离每个离散空间，并且它的 [Point_CH] 是作为 [CompHaus] 对象的单点评空间，在每个载体宇宙上都是如此。
*)
Lemma Point_Compact : IsCompact Point_Top.
Proof.
  intros I U HU.
  destruct (fst (snd HU ttt) ttt) as [i Hi].
  refine (Datatypes.cons i Datatypes.nil; _).
  intro x; destruct x.
  refine (i; _); split.
  - left; reflexivity.
  - exact Hi.
Qed.

Lemma Point_Hausdorff : IsHausdorff Point_Top.
Proof.
  intros x y Hxy; destruct x, y.
  exfalso; apply Hxy; reflexivity.
Qed.

(*
 The full subcategory of Hausdorff spaces.  [shom] retains every
 continuous map, so closure under identity and composition is trivial —
 the same shape as [Sheaves_sub] in Theory/Sheaf/Category.v and
 [Models_sub] in Theory/Lawvere/Model.v. 

 --------
 豪斯多夫空间的完整子范畴。[shom] 保留每一个连续映射，所以在恒等映射和复合运算下的闭包是显而易见的——与 Theory/Sheaf/Category.v 中的 [Sheaves_sub] 以及 Theory/Lawvere/Model.v 中的 [Models_sub] 的形式相同。
*)
Definition Hausdorff_Subcategory : Subcategory Top :=
  @Build_Subcategory Top
    (fun X : Top => IsHausdorff X)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition HausdorffSpaces : Category := Sub Top Hausdorff_Subcategory.

Lemma Hausdorff_Full :
  Category.Construction.Subcategory.Full Top Hausdorff_Subcategory.
Proof. intros x y ox oy g; exact I. Qed.

(*
 The full subcategory of compact Hausdorff spaces.  Only the definition is
 provided: the deeper theory (that compact Hausdorff spaces are closed
 under continuous images, that a continuous bijection out of a compact
 space into a Hausdorff space is a homeomorphism, monadicity over Sets)
 is out of scope for this file. 

 --------
 紧致豪斯多夫空间的完整子范畴。 仅提供定义：更深入的理论（紧致豪斯多夫空间在连续映射下是封闭的，从紧致空间到豪斯多夫空间的连续双射是同胚映射，对集合的幺范畴性）不在此文件的范围内。
*)
Definition CompactHausdorff_Subcategory : Subcategory Top :=
  @Build_Subcategory Top
    (fun X : Top => (IsCompact X ∧ IsHausdorff X)%type)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition CompactHausdorffSpaces : Category :=
  Sub Top CompactHausdorff_Subcategory.

Lemma CompactHausdorff_Full :
  Category.Construction.Subcategory.Full Top CompactHausdorff_Subcategory.
Proof. intros x y ox oy g; exact I. Qed.

(* ------------------------------------------------------------------------ *)
(* * ** Non-vacuity: a two-point discrete space, and what it distinguishes / * ** 非空性：一个两点离散空间，以及它所区分的内容 *)

(*
 Except for the epi probe, everything above could in principle be
 exercised on spaces with at most one point.  This closing section
 (supplied by the audit of the first commit) works over the two-point
 DISCRETE space and pins down, with witnesses rather than prose:
 continuity genuinely excludes maps — the identity carrier map from the
 indiscrete two-point space to the discrete one is not continuous, even
 though the underlying setoid map is a perfectly good arrow of [Sets];
 the separation predicate holds of a space with two distinguishable
 points and is refuted by its indiscrete twin, so [IsHausdorff] is
 neither vacuous nor universal; and the monic/epic characterizations
 separate real morphisms — a constant endomap of the discrete two-point
 space is neither monic nor epic, while a nonidentity morphism (negation)
 exists and the identity is both. 

 --------
 除了表面探针，上述所有内容原则上都可以在最多只有一个点的空间上进行。这一结束部分
 （由首次提交的审计提供）在两个点的离散空间上工作，并通过证据而非文字说明加以确定：
 连续性确实排除了映射——从不可分的两个点空间到离散空间的恒等承载映射并不连续，即使其底层集合态映射在 [Sets] 中是一个完全有效的箭头；
 分离谓词适用于具有两个可区分点的空间，并被其不可分的双胞空间否定，所以 [IsHausdorff] 既不是空的，也不是普遍的；
 单/满性特征区分实际态射——离散两个点空间的常映射端态射既非单态也非满态，而非恒等态射（否定）存在并且恒等态射同时具备两者。
*)

Definition Bool_Discrete : TopSpace := Discrete_Top bool_setoid_object.

Lemma singleton_true_open :
  IsOpen Bool_Discrete (fun b : bool_setoid_object => b = true).
Proof. intros x y Hxy Hx; simpl in Hxy; now subst. Qed.

Theorem indiscrete_to_discrete_id_not_continuous :
  Continuous TwoPoint_Indiscrete Bool_Discrete setoid_morphism_id → False.
Proof.
  intro Hc.
  pose proof (Hc (fun b : bool_setoid_object => b = true)
                 singleton_true_open) as H.
  simpl in H.
  specialize (H true false eq_refl).
  discriminate.
Qed.

Theorem Bool_Discrete_Hausdorff : IsHausdorff Bool_Discrete.
Proof.
  intros x y Hxy.
  exists (fun z : bool_setoid_object => z = x).
  exists (fun z : bool_setoid_object => z = y).
  repeat split.
  - intros u v Huv Hu; simpl in Huv; now subst.
  - intros u v Huv Hu; simpl in Huv; now subst.
  - intros z Hz Hz'; simpl in *; subst; apply Hxy; reflexivity.
Qed.

Theorem TwoPoint_Indiscrete_not_Hausdorff :
  IsHausdorff TwoPoint_Indiscrete → False.
Proof.
  intro H.
  destruct (H true false ltac:(simpl; discriminate))
    as [U [V [[HU HV] [[Ut Vf] Hdisj]]]].
  exact (Hdisj false (HU true false Ut) Vf).
Qed.

(*
 Negation is a continuous nonidentity endomap of the discrete two-point
 space; the constant-true endomap is continuous by [open_const]. 

 --------
 否定是离散两点空间的连续非同一性端映射；恒为真的端映射由 [open_const] 保持连续。
*)
Definition negb_setoid : SetoidMorphism bool_setoid_object bool_setoid_object.
Proof. refine {| morphism := negb |}. Defined.

Definition negb_map : Bool_Discrete ~{Top}~> Bool_Discrete :=
  Build_ContinuousMorphism Bool_Discrete Bool_Discrete negb_setoid
    (out_of_discrete_continuous bool_setoid_object Bool_Discrete negb_setoid).

Definition const_true_map : Bool_Discrete ~{Top}~> Bool_Discrete :=
  Build_ContinuousMorphism Bool_Discrete Bool_Discrete
    (const_morphism bool_setoid_object bool_setoid_object true)
    (fun U _ => open_const Bool_Discrete (U true)).

Lemma negb_map_not_id : negb_map ≈ @id Top Bool_Discrete → False.
Proof. intro H; pose proof (H true) as Ht; simpl in Ht; discriminate. Qed.

Theorem const_true_not_monic : Monic const_true_map → False.
Proof.
  intro Hm.
  pose proof (snd (top_monic_iff const_true_map) Hm) as Hinj.
  pose proof (Hinj true false eq_refl) as H; simpl in H; discriminate.
Qed.

Theorem const_true_not_epic : Epic const_true_map → False.
Proof.
  intro He.
  pose proof (snd (top_epic_iff const_true_map) He false) as w.
  destruct w as [a Ha]; simpl in Ha; discriminate.
Qed.

Theorem id_monic_and_epic :
  (Monic (@id Top Bool_Discrete) * Epic (@id Top Bool_Discrete))%type.
Proof.
  split.
  - apply top_monic_iff; intros a b H; exact H.
  - apply top_epic_iff; intro b; exists b; reflexivity.
Qed.
