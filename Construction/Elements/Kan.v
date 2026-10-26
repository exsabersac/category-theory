Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(*
   * Kan's form of the coyoneda lemma over the category of elements. 

   --------
   * Kan 关于元素范畴的 Coyoneda 引理形式。
*)

(*
 nLab: https://ncatlab.org/nlab/show/co-Yoneda+lemma
 nLab: https://ncatlab.org/nlab/show/category+of+elements

 BOOK LOCATION.  Recorded from the statement of issue #319: Mac Lane,
 “Categories for the Working Mathematician” (2nd ed.), III.2,
 Exercise 3, book p. 62.  That text was not consulted while writing
 this file; the location is given so a reader can look the exercise
 up, and nothing beyond the location is reproduced here.  No claim is
 made about the wording or numbering at that place.

 THE STATEMENT.  For K : D ⟶ Sets with category of elements
 [Elements K] and projection Q := [Elements_proj K], and for an object
 a of D, there is a bijection between

 - natural transformations K ⟹ [Hom a,─] into the covariant
 representable at a, and
 - cones from the constant functor at a to Q,

 natural in a.  Maps out of K into a representable are the same thing
 as cones over the elements projection.

 A SAME-NAME TRAP, FLAGGED BY THE ISSUE ITSELF.  Theory/Coend/Yoneda.v
 carries a [coyoneda_reduction] — the coend formula
 ∫^x C(x,c) × F x ≅ F c.  That is a DIFFERENT theorem which happens to
 share the name “coyoneda”; it is about coends, mentions no category
 of elements, and neither statement is derived from the other here.
 Nothing below refers to it.

 WHAT IS DELIVERED, AND AT WHAT STRENGTH
 ---------------------------------------

 (1) The two passages, as plain [Definition]s applying the record
 constructor to named lemmas — no [Program], hence no obligation, in
 either passage or in the Δ bridge, so the terms whose conversion
 behaviour is measured below are transparent and the measurements mean
 what they say.  ([Program] is used for the three isomorphism
 definitions, whose obligations are respectfulness and the inverse
 laws and are opaque; nothing is claimed at [eq_refl] about those.
 The fourth isomorphism, [kan_iso_transform], is a plain [Definition]
 composing two of them.)

 [kan_cone_of_nat]  : (K ⟹ [Hom a,─]) → ACone a Q
 [kan_nat_of_cone]  : ACone a Q → (K ⟹ [Hom a,─])

 (2) Both round trips at `≈` — [kan_nat_cone_nat] in the hom-setoid of
 [D, Sets], which closes by [reflexivity] outright, and
 [kan_cone_nat_cone] in [AConeEquiv], which must first destruct the
 sigma object.  Whole-record Leibniz equality is REFUTED for both and
 pinned in Test/ProbeCoyoneda.v; see “Strict attempts” below.

 (3) The pointwise isomorphism of setoids
 [kan_iso_at : KanNat K a ≅[Sets] KanCone K a], and

 (4) the naturality-in-a upgrade
 [kan_coyoneda : KanNat K ≅[[D^op, Sets]] KanCone K],
 an isomorphism in the functor category, which is the “natural
 isomorphism” reading the exercise asks for.  Its two components ARE
 the legs of [kan_iso_at] by [eq_refl] ([kan_coyoneda_to_component],
 [kan_coyoneda_from_component]), so (4) is an upgrade of (3) and not a
 parallel construction.

 (5) The literal Δ-reading, [Transform (Δ[Elements K](a)) Q], related
 to the [ACone] form in both directions with both round trips, and the
 composite [kan_iso_transform] delivering Mac Lane's own phrasing
 Nat(K, D(a,−)) ≅ Nat(Δa, Q) as an isomorphism of setoids in Sets.

 THE DESIGN DECISION: WHY [ACone] AND NOT [Transform (Δ a) Q]
 -----------------------------------------------------------

 The two are the same data — [ACone c F] is an apex-indexed leg family
 [vertex_map] plus [cone_coherence], and a [Transform] out of a
 constant functor is that same family plus a naturality square — but
 they are NOT the same record, and they are not convertible: the cone
 law reads [fmap[F] f ∘ ψ x ≈ ψ y] while naturality against Δa reads
 [fmap[F] f ∘ τ x ≈ τ y ∘ id], so the two differ by an [id_right] and
 a [Transform] additionally carries [naturality_sym].  A choice had to
 be made and it is [ACone], for one reason that is not a matter of
 taste: Structure/Cone.v already builds [ConePresheaf F : C^op ⟶
 Sets], the presheaf of cones over F, whose reindexing along
 g : a' ~> a precomposes every leg with g.  That IS the right-hand
 side of the exercise AS A FUNCTOR OF a, already assembled, with its
 functor laws already proved.  Taking the Δ-reading as primary would
 have required building that presheaf again by hand for no gain.

 The Δ-reading is therefore not dropped, it is delivered as a proved
 bridge ([kan_transform_of_cone], [kan_cone_of_transform]) with both
 round trips and packaged as [kan_cone_transform_iso].  What the
 bridge costs is exactly one [id_right] in each direction, which is
 the measurement, not a guess: both round trips are REFUTED at
 [eq_refl] and hold at `≈` by [reflexivity], the leg family surviving
 on the nose in both directions and only the law fields being rebuilt.

 THE CRUX OF THE BACKWARD PASSAGE
 --------------------------------

 Objects of [Elements K] are pairs (d, x) compared by LEIBNIZ equality
 — [obj] carries no setoid in this library — while the elements x
 themselves live in a setoid.  So when x ≈ y in K d without x = y, the
 pairs (d, x) and (d, y) are two DIFFERENT objects.  A cone therefore
 assigns them two legs, a priori unrelated, whereas the transformation
 it is supposed to become must have a component at d that RESPECTS `≈`
 on K d.

 That respectfulness is not assumed and is not an extra hypothesis: it
 is DERIVED, in [kan_leg_respects], from cone coherence alone.  The
 witness is [elements_same], the morphism (d, x) ~> (d, y) whose
 underlying D-morphism is the identity — it exists precisely because
 [fmap[K] id x ≈ x ≈ y] — and coherence at it gives
 [id ∘ ψ (d,x) ≈ ψ (d,y)].  This is the same phenomenon
 Theory/Natural/Transformation/Arrows.v records for the arrows-only
 presentation of a natural transformation, where respectfulness in the
 arrow argument is likewise derivable rather than carried; the
 mechanism there is a detour through [f ∘ id] and here it is the
 identity-carried morphism between two elements, so it is an analogy
 of shape and not a reuse of that file, which is not imported.

 UNIVERSES (measured in the constraint blocks with [Set Printing
 Universes], not read off the binders)
 --------------------------------------------------------------------

 Everything below lives over a category [D : Category@{u u0 u0}] with
 [K : D ⟶ Sets@{u0 _}].  The measured facts:

 - [KanNat@{u u0 u1 u2 u3}] and [KanCone@{u u0 u1 u2}] EACH carry
 [u <= u0] — D's objects at or below D's homs — and so therefore do
 [kan_iso_at], [kan_coyoneda] and [kan_iso_transform];
 - [kan_cone_of_nat@{u u0 u1 u2 u3 u4}] and
 [kan_nat_of_cone@{u u0 u1 u2 u3 u4}] DO NOT.  Each block bounds
 [u] and [u0] below [Elements K]'s own object universe — which is
 [u2] in the first block and [u3] in the second, the two constants
 numbering their binders differently — with nothing forcing that
 universe below [u0].  (Read the binder names from the block you
 are looking at: [kan_nat_of_cone]'s [u2] is a DIFFERENT universe,
 carrying [u1 <= u2].)

 So the restriction is real but it enters at the PACKAGING, not at the
 mathematics: the two passages are formable over a category whose
 objects sit strictly ABOVE its homs, and it is the presheaf and the
 setoid of transformations that refuse there.  That is not inferred
 from the blocks — it is pinned, at one universe setting, by
 formability negatives 8-10 against positive controls 6 and 7 of
 Test/ProbeCoyoneda.v, which differ from the negatives in exactly which
 constant is named.

 Where each pin comes from, and that the two are INDEPENDENT:

 - RHS.  [ConePresheaf@{u0 u1 u2 u3 u4 u5 u}] carries [u0 <= u4], its
 index category's OBJECT universe below its target category's HOM
 universe (a cone's leg family is indexed by the objects of the
 index category and lands in homs of the target).  The index here
 is [Elements K], whose object universe is bounded below by both
 [u] and [u0].  Chaining gives [u <= u0].
 - LHS.  Independently: [KanNat K a] must be an OBJECT of
 [Sets@{u0 _}], hence a [Type@{u0}], and it is a type of natural
 transformations, i.e. of families indexed by [obj[D] : Type@{u}].
 So again [u <= u0].  Negative 9 pins this half on its own.

 The restriction is stated rather than worked around; it is NOT
 introduced by the comparison, it is what each side costs on its own,
 and for the same underlying reason — a set of natural transformations,
 or of cones, is a family indexed by objects, so the objects must fit
 where hom-sets live.  Nothing here is claimed unavoidable, and no
 attempt is made to restate the theorem at a coarser level.

 Two further donor pins are inherited and named so a consumer is not
 surprised.  Instance/Fun.v's [Fun] identifies its source and target
 hom levels ([u0 = u2] in its own block) and demands hom = proof in
 both, so [D, Sets] and [D^op, Sets] pin D's hom and proof levels
 together at [Sets]' carrier level.  Theory/Functor.v's [Compose]
 demands ONE shared hom-and-proof level across its three categories,
 which is what [KanNat]'s assembly spends.  Both pins are recorded in
 Functor/Construction/Postcompose.v's Universes section; neither is
 introduced here.

 AN ENGINEERING FINDING, RECORDED BECAUSE IT COST TIME
 -----------------------------------------------------

 The two inverse laws of [kan_coyoneda] need an [id_right] that the
 corresponding laws of [kan_iso_at] do not, and the reason is not about
 this construction at all: Theory/Natural/Transformation.v defines
 [nat_id]'s component as [fmap[F] id], not as [id].  So the identity of
 a FUNCTOR CATEGORY reindexes, and the goal carries an [∘ id] that must
 be discharged — whereas in [Sets] the identity is
 [setoid_morphism_id] and no such factor appears.  (Neither side closes
 by a bare [reflexivity]: [kan_iso_at]'s laws go through
 [kan_cone_nat_cone], which must itself destruct the sigma object, per
 (2) above.  The contrast is the [id_right], not the tactic.)  The same
 [nat_id] fact is recorded twice in this tree — at
 Functor/Representable.v, about [repr_induced_id], and at
 Functor/Representable/Functorial.v, about the comparison with
 [repr_pair_iso] (which is itself declared in
 Functor/Hom/Yoneda/Iso.v, not in Functor/Representable.v).  It is
 restated here because a reader comparing the two isomorphism proofs
 below would otherwise take the asymmetry for an accident.

 Strict attempts, measured and refuted
 -------------------------------------

 Every comparison was tried at [eq_refl] first.  SEVEN were REFUTED,
 each with its cause diagnosed, and all seven are pinned as CONVERSION
 negatives in Test/ProbeCoyoneda.v (which also carries the three
 FORMABILITY negatives above and twelve positive controls).  The
 causes, which are three and not seven:

 - REBUILT LAW FIELDS.  [kan_nat_of_cone (kan_cone_of_nat τ) = τ] and
 its component-family and single-component variants.  [Transform]
 and [SetoidMorphism] both carry primitive projections with eta
 conversion (measured, not assumed), so record equality reduces to
 field equality — and the [naturality], [naturality_sym] and
 [proper_morphism] fields of the rebuilt records are this file's
 own lemmas rather than τ's.  `≈` is [crelation]-valued, so there
 is no definitional proof irrelevance to close the gap.  Positive
 control 2 shows the UNDERLYING FUNCTIONS do agree on the nose, so
 the obstruction is located exactly at the proofs.
 - MISSING sigT ETA.  The leg family of
 [kan_cone_of_nat (kan_nat_of_cone ψ)] is [fun j => ψ (`1 j; `2 j)],
 and stdlib [sigT] has no eta rule here — Lib/Foundation.v's
 [Set Primitive Projections] governs this library's own records,
 not [sigT].  This cause is INDEPENDENT of the first: it defeats
 even the bare leg family at a variable object (negative 4), which
 is why [kan_cone_nat_cone] destructs the pair before closing by
 [reflexivity], and positive control 3 is that same statement with
 the pair destructed.
 - THE Δ-BRIDGE [id_right].  Both bridge round trips at the whole
 record.  Here the sigma plays no part and the DATA returns on the
 nose in BOTH directions at a variable object (positive controls 4
 and 5), so the only remaining obstruction is the law field, which
 is rebuilt through the [id_right] described above.

 What DOES hold strictly: the object actions of both functors
 ([kan_nat_obj], [kan_cone_obj]), the identification of the two
 components of the natural isomorphism with the legs of the pointwise
 one ([kan_coyoneda_to_component], [kan_coyoneda_from_component]), the
 leg family of the forward passage read at a pair
 ([kan_cone_of_nat_leg]), the component of the backward passage read
 at an element ([kan_nat_of_cone_component]), and both leg families of
 the Δ bridge ([kan_transform_of_cone_component],
 [kan_cone_of_transform_leg]).

 AXIOMS.  All 46 constants of this module — the 32 named ones plus the
 14 [Program] obligations of the three isomorphism definitions,
 enumerated with [Print Module] per the methodology of docs/AXIOMS.md —
 report “Closed under the global context”.  Twelve of them are wired into the
 [print-assumptions] gate of the Makefile; the names were checked
 against the whole tree first and collide with nothing, which matters
 because the gate [Require]s everything into one scope and a later
 [Require] would silently win.

 PRIOR ART, SCOPED TO WHAT WAS SEARCHED
 --------------------------------------

 Theory/Universal/Element/Elements.v is a DIFFERENT theorem over the
 same construction — universal elements are initial objects of the
 category of elements, its eight constants all of the
 [Elements_Initial] family — and is neither used nor generalized here.

 [rg ACone --glob '*.v'] over the tree returns twenty files — the glob
 matters, since the unrestricted [rg ACone] returns forty-nine, the
 difference being CLAUDE.md, the planning ledger and the per-chapter
 coverage JSON.  One (Structure/Cone.v)
 declares the class; two are this file and its probe; one
 (Theory/Diagram/Examples.v) mentions it in PROSE only, in a note about
 a shape match, and constructs no cone.  The remaining sixteen —
 Adjunction/Continuity.v, Construction/Comma/{Creation,Limit}.v,
 Instance/Top/Forgetful.v, Monad/Eilenberg/Moore/Limit.v,
 Structure/{Coequalizer,Limit}.v, Structure/Equalizer/Fork.v,
 Structure/Limit/{Kan/Pointwise,Preservation,Preservation/Separation,
 Product,Weighted}.v, Structure/UniversalProperty/Limit.v,
 Theory/Adamek.v and Theory/Equivalence/Limit.v — are every one of them
 limit- or colimit-related, and none has this shape.  That is a
 statement about that grep and not a survey of the tree.

 NOT DELIVERED
 -------------

 - no presheaf (contravariant) orientation: nothing is stated for
 [PElements P] and the contravariant representable, and the
 transport of the isomorphism along opposites is not performed;
 - no identification of either side with a limit or a Kan extension,
 and in particular no claim that Q is a discrete opfibration or
 that the exercise's bijection is an instance of the pointwise Kan
 formula of Structure/Limit/Kan/Pointwise.v;
 - no naturality in K: only the variable a is varied, K being fixed
 throughout, so the two sides are not exhibited as functors of the
 pair;
 - no statement in [StrictCat] and no Leibniz equality of the two
 functors [KanNat K] and [KanCone K] — [kan_coyoneda] is an
 isomorphism in [D^op, Sets], which is the honest strength;
 - no bijection of the underlying TYPES: both isomorphisms are of
 setoids, and the round trips are up to `≈`;
 - the Δ-reading is NOT upgraded to a naturality statement: [KanDelta]
 is a [SetoidObject] and is never exhibited as a functor
 [D^op ⟶ Sets], so [kan_iso_transform] is pointwise in a and is not
 shown natural.  Only the [ACone] side carries the naturality, which
 is exactly why [ConePresheaf] was taken as primary; the cost is that
 Mac Lane's own phrasing is delivered one strength below the headline. 

 --------
 nLab:  https://ncatlab.org/nlab/show/co-Yoneda+lemma 
 nLab:  https://ncatlab.org/nlab/show/category+of+elements 

 书籍位置。摘自第319期声明：Mac Lane，《为工作数学家准备的范畴论》（第2版），III.2，练习3，书中第62页。在编写此文件时未参考该文本；提供该位置是为了让读者查找练习，并且这里只有位置信息。未对该处的用词或编号作出任何声明。

 陈述。对于 K : D ⟶ 集合 与元素范畴
 [Elements K] 及投影 Q :=  [Elements_proj K] ，以及 D 的对象 a，存在以下之间的双射关系

 - 从 K 到协变可表示函子在 a 处的自然变换 K ⟹  [Hom a,─] ，以及
 - 从常值函子到 Q 的锥。在 a 中是自然的。从 K 到 a 的映射表示为可表示的，与元素投影上的锥体是同一件事。

 同名陷阱，由问题本身标记。Theory/Coend/Yoneda.v 包含一个 [coyoneda_reduction] —— 即共端公式 ∫^x C(x,c) × F x ≅ F c。这是一个不同的定理，仅恰好共享“coyoneda”这个名字；它关于共端，没有提到元素的范畴，而且这里没有哪个陈述是从另一个推导出来的。下面没有任何内容引用它。

 交付的内容是什么，以及其强度是什么
 ---------------------------------------(1) 这两段话，作为普通的 [Definition]，将记录构造函数应用于命名引理——没有 [Program]，因此在任何一段或 Δ 桥中都没有义务，因此下面测量其转换行为的项是透明的，测量结果就是其字面含义。（[Program] 用于三个同构定义，其义务是尊重性和逆律，是不透明的；在 [eq_refl] 没有对它们作任何声明。第四个同构，[kan_iso_transform]，是一个普通的 [Definition]，组合其中两个。）

 [kan_cone_of_nat]   ：(K ⟹ [Hom a,─] ) → ACone a Q
 [kan_nat_of_cone]   ：ACone a Q → (K ⟹ [Hom a,─] )(2) 在集合等价类 [D, Sets] 的同态集中，`≈` — [kan_nat_cone_nat] 的两次往返，其中通过 [reflexivity] 直接闭合，以及在 [AConeEquiv] 中的 [kan_cone_nat_cone] ，此处必须先拆解 sigma 对象。两者的全记录 Leibniz 相等性都被否定，并在 Test/ProbeCoyoneda.v 中固定；见下文 “严格尝试”。

 (3) 集合等价类 [kan_iso_at : KanNat K a ≅[Sets] KanCone K a] 的逐点同构，以及

 (4) 自然性升级 [kan_coyoneda : KanNat K ≅[[D^op, Sets] ] KanCone K]，这是函子范畴中的一个同构，即练习要求的“自然同构”。它的两个分量正是 [kan_iso_at] 的两条支腿由 [eq_refl]（[kan_coyoneda_to_component], [kan_coyoneda_from_component]）组成，因此 (4) 是 (3) 的升级，而不是平行构造。(5) 字面 Δ-读取，[Transform (Δ[Elements K] (a)) Q]，与 [ACone] 形式在两个方向上以及双向来回相关，并且复合的 [kan_iso_transform] 提供了 Mac Lane 自身的表述 Nat(K, D(a,−)) ≅ Nat(Δa, Q) 作为集合套中同构。 

 设计决策：为什么是 [ACone] 而不是 [Transform (Δ a) Q] 
 -----------------------------------------------------------这两者是相同的数据——[ACone c F] 是一个顶点索引的腿族 [vertex_map] 加上 [cone_coherence]，而 [Transform] 从一个常值函子出发，是同一个族加上一个自然性方格——但是它们不是相同的记录，并且它们不可转换：圆锥定律写作 [fmap[F] f ∘ ψ x ≈ ψ y，而针对 Δa 的自然性写作 [fmap[F] f ∘ τ x ≈ τ y ∘ id，因此两者在 [id_right] 上有所不同，并且 [Transform] 额外携带 [naturality_sym]。必须做出一个选择，而这个选择是 [ACone]，有一个原因不涉及个人偏好：Structure/Cone.v 已经构建了 [ConePresheaf F : C^op ⟶ Sets]，即 F 上的圆锥预层，其沿 g : a' ~> a 的重索引将每条腿与 g 预组合。那确实是作为 a 的函子已经组装好的练习右侧，并且其函子律已经被证明。将 Δ 读法作为主要方式将需要手动重新构建该预层，但不会有任何收益。

 因此 Δ 读法并未被放弃，而是作为已证明的桥（[kan_transform_of_cone]，[kan_cone_of_transform]）提供，既包含来回操作，又打包为 [kan_cone_transform_iso]。该桥的成本恰好是每个方向一个 [id_right]，这是一种测量，而不是猜测：两个来回操作在 [eq_refl] 被驳回，并在 `≈` 由 [reflexivity] 保持，两方向上都严格保留了腿族，仅法律字段被重建。

 向后传递的关键点
 --------------------------------[Elements K] 的对象是成对的 (d, x)，通过 LEIBNIZ 等式比较 —— 在这个库中 [obj] 不携带任何集合构造 —— 而元素 x 本身存在于一个集合构造中。因此，当 x ≈ y 在 K d 中但 x ≠ y 时，成对的 (d, x) 和 (d, y) 是两个不同的对象。因此，一个锥体会为它们分配两条腿，先验上不相关，而它所应成为的变换在 d 处必须具有一个尊重 K d 上 `≈` 的分量。这种尊重性不是假定的，也不是额外的假设：它是在 [kan_leg_respects] 中，仅从圆锥一致性中得出的。证据是 [elements_same]，即形态 (d, x) ~> (d, y)，其底层 D-态射是恒等态射——它恰好存在，因为 [fmap[K] id x ≈ x ≈ y]——在此处的一致性给予 [id ∘ ψ (d,x) ≈ ψ (d,y)]。这与 Theory/Natural/Transformation/Arrows.v 为仅箭头表示的自然变换记录的现象相同，其中箭头参数中的尊重性同样是可推导的，而不是被携带；其机制是通过 [f ∘ id] 的绕行，而这里是两个元素之间由恒等态射携带的形态，因此它是一种形状上的类比，而不是重用该文件，该文件并未被导入。宇宙（用约束块中的 [设置打印宇宙] 测量，而不是从绑定器中读取）
 --------------------------------------------------------------------

 以下所有内容都存在于一个类别 [D : Category@{u u0 u0}] 上，其为 [K : D ⟶ Sets@{u0 _}]。测量事实如下：- [KanNat@{u u0 u1 u2 u3}] 和 [KanCone@{u u0 u1 u2}] 各自承载 [u <= u0] —— D 的对象在 D 的 Hom 之下 —— 因此 [kan_iso_at]、[kan_coyoneda] 和 [kan_iso_transform] 也承载；
 - [kan_cone_of_nat@{u u0 u1 u2 u3 u4}] 和 [kan_nat_of_cone@{u u0 u1 u2 u3 u4}] 则不承载。每个块限制 [u] 和 [u0] 在 [Elements K] 自身对象宇宙之下——在第一个块中为 [u2]，在第二个块中为 [u3]，这两个常量对它们的绑定量编号不同——并没有任何东西强制该宇宙位于 [u0] 之下。（从你正在查看的块中读取绑定名称：[kan_nat_of_cone] 的 [u2] 是一个不同的宇宙，承载 [u1 <= u2]。）所以这个限制是存在的，但它出现在包装阶段，而不是数学阶段：两个通道可以在一个其对象严格位于同态之上的范畴上形成，而拒绝的是在此的预层和变换的集合类型。这不是从模块中推导出来的——在一个宇宙设置下，它是由 Test/ProbeCoyoneda.v 中正控制 6 和 7 与负面 8-10 的可形成性相对照固定的，这些负面与哪个常数被命名正好不同。

 每个固定点来自哪里，以及这两者是独立的：- 右侧 (RHS)。[ConePresheaf@{u0 u1 u2 u3 u4 u5 u}] 承载 [u0 <= u4]，其索引范畴的对象宇宙位于目标范畴的同态宇宙之下（一个锥形的腿族由索引范畴的对象索引，并落在目标范畴的同态中）。这里的索引是 [Elements K]，其对象宇宙如下界由 [u] 和 [u0] 限定。链式操作得到 [u <= u0]。
 - 左侧 (LHS)。独立地：[KanNat K a] 必须是 [Sets@{u0 _}] 的一个对象，因此是 [Type@{u0}]，并且它是一类自然变换，也就是由 [obj[D] 索引的族：Type@{u}]。因此再次得到 [u <= u0]。负9将这个半部分固定在它自身上。这个限制是被陈述出来的，而不是被规避；它不是由比较引入的，它就是每一方自身的成本，并且基于相同的根本原因——一组自然变换，或一组锥，是由对象索引的一个族，因此对象必须适应 Hom-集所在的位置。这里没有声称任何事情是不可避免的，也没有试图在更粗的层次上重新表述定理。另外两个捐赠者引脚被继承并命名，以免消费者感到惊讶。Instance/Fun.v 中的 [Fun] 识别其源和目标的 hom 等级（自身模块中的 [u0 = u2]）并要求两者的 hom = proof，因此 [D, Sets] 和 [D^op, Sets] 将 D 的 hom 和 proof 等级在 [Sets] 的承载级别上连接在一起。Theory/Functor.v 中的 [Compose] 要求其三个类别共享一个 hom 和 proof 等级，这正是 [KanNat] 的组合所使用的。两个引脚都记录在 Functor/Construction/Postcompose.v 的 Universes 部分；这里未引入任何一个。

 一个工程方面的发现，记录下因为它浪费了时间
 -----------------------------------------------------[kan_coyoneda] 的两个逆定律需要一个 [id_right]，而 [kan_iso_at] 的相应定律则不需要，其原因与这个构造完全无关：Theory/Natural/Transformation.v 将 [nat_id] 的分量定义为 [fmap[F] id]，而不是 [id]。因此，函子范畴的恒等式会重新索引，目标携带一个必须解除的 [∘ id] —— 而在 [Sets] 中恒等式是 [setoid_morphism_id]，并且没有出现这样的因素。（两边都不能通过一个单独的 [reflexivity] 结束：[kan_iso_at] 的定律通过 [kan_cone_nat_cone]，这本身必须根据上文 (2) 解构 sigma 对象。）对比在于[id_right]，而不是战术。）一样
 [nat_id]事实在本树中记录了两次——在
 Functor/Representable.v，约[repr_induced_id]，以及在
 Functor/Representable/Functorial.v，关于与
 [repr_pair_iso]（该
 Functor/Hom/Yoneda/Iso.v，不在Functor/Representable.v中）。它是
 此处重申，因为读者比较了两个同构证明
 否则，下文会将非对称性取为事故。

 严格的尝试，经过审慎且被驳斥
 -------------------------------------每一次比较都首先在 [eq_refl] 进行尝试。七个被驳回，每个都有其原因诊断，所有七个都被标记为 Test/ProbeCoyoneda.v 中的转换阴性（该文件还包含上述三个可形成性阴性和十二个阳性对照）。原因，有三个，而不是七个：- 重建的 LAW 字段。[kan_nat_of_cone (kan_cone_of_nat τ) = τ] 及其组件-族和单组件变体。[Transform] 和 [SetoidMorphism] 都具有带η转换的原始投影（已测量，而非假设），因此记录相等性简化为字段相等性——而重建记录的 [naturality]、[naturality_sym] 和 [proper_morphism] 字段是该文件自身的引理，而非τ的。`≈` 的值为 [crelation]，因此没有定义性证明无关性来弥合差距。正向控制2显示底层函数在本质上确实一致，因此障碍正好位于证明处。- 缺少 sigT ETA。[kan_cone_of_nat (kan_nat_of_cone ψ)] 的腿家族是 [fun j => ψ (`1 j; `2 j)]，而 stdlib [sigT] 在这里没有 eta 规则 —— Lib/Foundation.v 的 [Set Primitive Projections] 管理这个库自己的记录，而不是 [sigT]。这个原因独立于第一个原因：它甚至在变量对象（负 4）上击败了裸露的腿家族，这就是为什么 [kan_cone_nat_cone] 在通过 [reflexivity] 关闭之前会解构对，并且正控制 3 是在对被解构后的同一句话。- Δ-BRIDGE [id_right]。两个桥接在整个记录上来回运行。在这里 sigma 没有起作用，并且数据在变量对象上在两个方向都直接返回（正控制 4 和 5），因此唯一剩下的阻碍是法律字段，它通过上文描述的 [id_right] 重建。严格成立的是：两个函子（[kan_nat_obj]、[kan_cone_obj]）的对象作用，自然同构的两个分量与逐点同构的腿的对应（[kan_coyoneda_to_component]、[kan_coyoneda_from_component]），前向通道在一对元素处的腿族（[kan_cone_of_nat_leg]），后向通道在一个元素处的分量（[kan_nat_of_cone_component]），以及Δ桥的两个腿族（[kan_transform_of_cone_component]、[kan_cone_of_transform_leg]）。公理。本模块的全部46个常量——32个命名常量加上三个同构定义的14个[Program]义务，按docs/AXIOMS.md的方法用[Print Module]枚举——报告“在全局上下文下封闭”。其中12个已连接到Makefile的[print-assumptions]门；这些名称先在整个项目树中检查过，没有冲突，这很重要，因为该门[Require]将所有内容合并到一个作用域，而后续的[Require]会悄无声息地生效。  先前技术，局限于所检索的范围  --------------------------------------Theory/Universal/Element/Elements.v 是在相同构造上的一个不同定理——通用元素是元素范畴的初始对象，其八个常数都是 [Elements_Initial] 系列——在这里既没有使用也没有推广。[rg ACone --glob '*.v']  在树上返回二十个文件——这是重要的，因为不受限制的 [rg ACone] 返回四十九个文件，差别是 CLAUDE.md、计划账本和按章节覆盖的 JSON 文件。一个（Structure/Cone.v）声明了该类；两个是此文件及其探针；一个（Theory/Diagram/Examples.v）仅在 PROSE 中提到它，在关于形状匹配的注释中，并且没有构造任何锥体。剩下的十六个——
 Adjunction/Continuity.v, Construction/Comma/{Creation,Limit}.v,
 Instance/Top/Forgetful.v, Monad/Eilenberg/Moore/Limit.v,
 Structure/{Coequalizer,Limit}.v, Structure/Equalizer/Fork.v,
 Structure/Limit/{Kan/Pointwise,Preservation,Preservation/Separation,
 Product,Weighted}.v, Structure/UniversalProperty/Limit.v,
 Theory/Adamek.v 和 Theory/Equivalence/Limit.v——它们每一个都与极限或余极限相关，但没有一个有这种形状。那是关于那个 grep 的陈述，而不是对树的调查。

 未交付
 -------------- 没有 presheaf（逆变）方向性：对于 [PElements P] 和逆变可表示对象没有说明，也没有沿对偶对象传递同构；
 - 没有将任一方与极限或 Kan 拓展进行识别，特别是没有声明 Q 是离散余纤维化（opfibration），也没有声明练习中的双射是 Structure/Limit/Kan/Pointwise.v 中逐点 Kan 公式的实例；
 - 在 K 上没有自然性：仅变化变量 a，整个过程中 K 被固定，所以两边没有作为该对偶变量的函子展示；
 - 在 [StrictCat] 中没有声明，也没有 [KanNat K] 和 [KanCone K] 两个函子的 Leibniz 相等 —— [kan_coyoneda] 是 [D^op, Sets] 中的同构，这是真正的强性；
 - 没有双射的底层类型：两个同构均为
 塞托伊德，往返行程可达`≈`;
 - Δ读数未升级为自然性陈述：[KanDelta]
 是[SetoidObject]，且从未以函子的形式表现出来
 [D^op ⟶ Sets] ，因此 [kan_iso_transform] 在 a 中是逐点的，且不是
 表现得很自然。只有 [ACone] 方面保留了自然性，这正是 [ConePresheaf] 被选为主要原因；代价是麦克莱恩自己的表达比标题强度低一级。
*)

Section Kan.

Context {D : Category}.
Context (K : D ⟶ Sets).

(*
 The passages and the Δ bridge are built by applying the record
 constructor to named lemmas, so they carry no obligation and stay
 transparent — which is what the [eq_refl] measurements below rest on.
 [Program] is used only for the three isomorphism definitions, and
 there the obligation tactic is set to [idtac] so that the goals arrive
 in a predictable shape rather than partially discharged under
 generated names. 

 --------
 这些段落和 Δ 桥是通过将记录构造器应用于命名引理构建的，因此它们不承担任何义务并保持透明——这正是下面 [eq_refl] 测量所依赖的。[Program] 仅用于三个同构定义，在那里义务策略被设置为 [idtac]，以便目标以可预测的形式出现，而不是在生成的名称下部分完成。
*)

#[local] Obligation Tactic := idtac.

(*
 Explicit spellings of the two [ACone] projections at the data of this
 file.  Both are class projections whose instance argument is found by
 typeclass search, and search cannot see which cone is meant when two
 cones over the same diagram are in scope; naming them here keeps every
 statement below unambiguous. 

 --------
 在此文件的数据中，对两个 [ACone] 投影的显式拼写。两者都是类投影，其实例参数是通过类型类搜索找到的，当同一图上的两个锥在作用域中时，搜索无法确定指的是哪一个锥；在此为它们命名可以保持下面的每条语句都是明确的。
*)

Notation leg psi j :=
  (@vertex_map (Elements K) D _ (Elements_proj K) psi j).

Notation coh psi f :=
  (@cone_coherence (Elements K) D _ (Elements_proj K) psi _ _ f).

(* * ** From a map into a representable to a cone / * ** 从映射到可表示的圆锥 *)

(*
 Cone coherence for the leg family j ↦ τ (`1 j) (`2 j).  A morphism of
 [Elements K] is a D-morphism together with a witness that it carries
 the element; naturality of τ supplies the equation at the D-morphism
 and the carried witness moves the answer onto the target element. 

 --------
 对于腿族 j ↦ τ (`1 j) (` 2 j) 的圆锥相干性。[Elements K] 的一个态射是一个 D-态射以及一个证明它携带该元素的证据；τ 的自然性在 D-态射上提供了方程，并且所携带的证据将答案移动到目标元素上。
*)

Lemma kan_cone_coherence {a : D} (tau : K ⟹ [Hom a,─])
      {x y : Elements K} (f : x ~{Elements K}~> y) :
  fmap[Elements_proj K] f ∘ transform[tau] (`1 x) (`2 x)
    ≈ transform[tau] (`1 y) (`2 y).
Proof.
  rewrite <- (`2 f).
  exact (naturality[tau] _ _ (`1 f) (`2 x)).
Qed.

Definition kan_cone_of_nat {a : D} (tau : K ⟹ [Hom a,─]) :
  ACone a (Elements_proj K) :=
  @Build_ACone (Elements K) D a (Elements_proj K)
    (fun j => transform[tau] (`1 j) (`2 j))
    (fun x y f => kan_cone_coherence tau f).

(*
 The leg at a pair is the component of τ evaluated at the element, on
 the nose. 

 --------
 一对的腿是τ在该元素上评估的组成部分，就在鼻子上。
*)
Example kan_cone_of_nat_leg {a : D} (tau : K ⟹ [Hom a,─])
        (d : D) (x : K d) :
  leg (kan_cone_of_nat tau) ((d; x) : Elements K) = transform[tau] d x
  := eq_refl.

(* * ** From a cone to a map into a representable / * ** 从圆锥到可表示的映射 *)

(*
 Two `≈`-equal elements over one object of D are DIFFERENT objects of
 [Elements K] — objects are compared by Leibniz equality — but they are
 connected by the morphism whose underlying D-morphism is the identity.
 This is the witness that makes the backward passage possible. 

 --------
 在 D 的一个对象上，两个 `≈`-相等的元素是 [Elements K] 的不同对象——对象通过莱布尼茨等式进行比较——但它们通过一个其底层 D-态射为恒等态射的态射相连。这就是使向后传递成为可能的证据。
*)

Lemma elements_same_cond {d : D} (x y : K d) (H : x ≈ y) :
  fmap[K] (id[d]) x ≈ y.
Proof. now rewrite (elements_id_cond K x). Qed.

Definition elements_same {d : D} (x y : K d) (H : x ≈ y) :
  ((d; x) : Elements K) ~{Elements K}~> (d; y) :=
  (id[d]; elements_same_cond x y H).

(*
 Respectfulness of a cone's leg family in the ELEMENT argument, derived
 from cone coherence at [elements_same] rather than assumed. 

 --------
 在 ELEMENT 参数中，锥体腿族的尊重性是由 [elements_same] 处的锥体相干性得出的，而不是假定的。
*)

Lemma kan_leg_respects {a : D} (psi : ACone a (Elements_proj K))
      {d : D} (x y : K d) (H : x ≈ y) :
  leg psi ((d; x) : Elements K) ≈ leg psi ((d; y) : Elements K).
Proof.
  pose proof (coh psi (elements_same x y H)) as Hc.
  simpl in Hc.
  rewrite <- Hc.
  now rewrite id_left.
Qed.

(*
 The naturality square of the transformation to be built, in both
 orientations.  Each is cone coherence at the chosen lift of f, whose
 image under the projection is f itself definitionally
 ([Elements_lift_over]). 

 --------
 待构建变换的自然性平方，在两个方向上。每一个都是在所选的 f 抬升下的圆锥相干性，其在投影下的像在定义上就是 f 本身 ([Elements_lift_over])。
*)

Lemma kan_nat_naturality {a : D} (psi : ACone a (Elements_proj K))
      {d d' : D} (f : d ~> d') (x : K d) :
  f ∘ leg psi ((d; x) : Elements K)
    ≈ leg psi ((d'; fmap[K] f x) : Elements K).
Proof. exact (coh psi (Elements_lift K x f)). Qed.

Lemma kan_nat_naturality_sym {a : D} (psi : ACone a (Elements_proj K))
      {d d' : D} (f : d ~> d') (x : K d) :
  leg psi ((d'; fmap[K] f x) : Elements K)
    ≈ f ∘ leg psi ((d; x) : Elements K).
Proof. symmetry; exact (coh psi (Elements_lift K x f)). Qed.

Definition kan_nat_of_cone {a : D} (psi : ACone a (Elements_proj K)) :
  K ⟹ [Hom a,─] :=
  @Build_Transform D Sets K ([Hom a,─])
    (fun d => @Build_SetoidMorphism (K d) _ (@hom D a d) _
                (fun x => leg psi ((d; x) : Elements K))
                (fun x y H => kan_leg_respects psi x y H))
    (fun d d' f => kan_nat_naturality psi f)
    (fun d d' f => kan_nat_naturality_sym psi f).

(*
 The component at d, evaluated at an element, is the leg at the pair,
 on the nose. 

 --------
 在 d 处的分量，在一个元素上评估，是该对的腿，正好如此。
*)
Example kan_nat_of_cone_component {a : D} (psi : ACone a (Elements_proj K))
        (d : D) (x : K d) :
  transform[kan_nat_of_cone psi] d x = leg psi ((d; x) : Elements K)
  := eq_refl.

(** ** The two round trips / ** 两次往返 *)

(*
 Both hold at `≈` and neither holds at [eq_refl]; the negatives are
 pinned in Test/ProbeCoyoneda.v.  The cone side must destruct the pair
 first, stdlib [sigT] having no eta rule here. 

 --------
 两者在 `≈` 上成立，而在 [eq_refl] 上都不成立；否定在 Test/ProbeCoyoneda.v 中被固定。锥体一侧必须先解构该对，stdlib [sigT] 在此没有 eta 规则。
*)

Lemma kan_nat_cone_nat {a : D} (tau : K ⟹ [Hom a,─]) :
  kan_nat_of_cone (kan_cone_of_nat tau) ≈ tau.
Proof. intros d x; reflexivity. Qed.

Lemma kan_cone_nat_cone {a : D} (psi : ACone a (Elements_proj K)) :
  @equiv _ (AConeEquiv a (Elements_proj K))
         (kan_cone_of_nat (kan_nat_of_cone psi)) psi.
Proof. intros [d x]; reflexivity. Qed.

(* * ** The two sides as functors of the apex / * ** 顶点的两个边作为函子 *)

(*
 The left-hand side is a PURE ASSEMBLY of in-tree parts: the covariant
 hom-functor of the functor category [D, Sets] taken at K, composed
 with the Yoneda embedding of D.  It is a plain [Definition] with no
 obligations, so all three functor laws are inherited. 

 --------
 左侧是一个由树内部分件组成的纯汇编：在 K 处取函子类别 [D, Sets] 的协变同态函子，并与 D 的 Yoneda 嵌入组合。它是一个简单的 [Definition]，没有任何义务，因此所有三个函子定律都被继承。
*)

Definition KanNat : D^op ⟶ Sets :=
  Curried_Hom ([D, Sets]) K ◯ Curried_Hom D.

(*
 The right-hand side is Structure/Cone.v's presheaf of cones, taken at
 the elements projection.  Also pure reuse. 

 --------
 右侧是 Structure/Cone.v 的锥体预层，取自元素投影。同时也是纯粹的重用。
*)

Definition KanCone : D^op ⟶ Sets :=
  ConePresheaf (Elements_proj K).

(*
 Both object actions are the setoids the exercise names, on the nose. 

 --------
 两个对象动作正是练习名称本身。
*)

Example kan_nat_obj (a : D) :
  KanNat a = {| carrier   := K ~{[D, Sets]}~> [Hom a,─]
              ; is_setoid := @homset ([D, Sets]) K [Hom a,─] |}
  := eq_refl.

Example kan_cone_obj (a : D) :
  KanCone a = {| carrier   := ACone a (Elements_proj K)
               ; is_setoid := AConeEquiv a (Elements_proj K) |}
  := eq_refl.

(** ** The pointwise isomorphism / ** 点对点同构 *)

Program Definition kan_iso_at (a : D) : KanNat a ≅[Sets] KanCone a := {|
  to   := {| morphism := fun tau => kan_cone_of_nat tau |};
  from := {| morphism := fun psi => kan_nat_of_cone psi |}
|}.
Next Obligation. intros a tau tau' H [d z]; exact (H d z). Qed.
Next Obligation. intros a psi psi' H d z; exact (H (d; z)). Qed.
Next Obligation. intros a psi; apply kan_cone_nat_cone. Qed.
Next Obligation. intros a tau; apply kan_nat_cone_nat. Qed.

(** ** Naturality in the apex / ** 顶点的自然性 *)

(*
 The reindexing on both sides is precomposition of every leg (resp. of
 every component's value) with g, so all four naturality obligations
 close by [reflexivity].  The two INVERSE laws do not, and the reason
 is not this construction: [nat_id]'s component is [fmap[F] id] rather
 than [id] (Theory/Natural/Transformation.v), so the identity of a
 functor category reindexes and leaves an [∘ id] behind — see the
 engineering note in the header.  In [Sets] the identity is
 [setoid_morphism_id] and [kan_iso_at]'s corresponding obligations need
 no such step. 

 --------
 两边的重新索引是将每条腿（分别是每个分量的值）与 g 进行预组合，所以所有四个自然性要求都由 [reflexivity] 完成闭合。两个逆律则不行，原因不在于这个构造：[nat_id] 的分量是 [fmap[F] id] 而不是 [id]（Theory/Natural/Transformation.v），因此函子范畴的恒等式会重新索引并留下一个 [∘ id] —— 参见头部的工程说明。在 [Sets] 中，恒等式是 [setoid_morphism_id]，而 [kan_iso_at] 的对应要求不需要这样的步骤。
*)

Program Definition kan_coyoneda : KanNat ≅[[D^op, Sets]] KanCone := {|
  to   := {| transform := fun a => to   (kan_iso_at a) |};
  from := {| transform := fun a => from (kan_iso_at a) |}
|}.
Next Obligation. intros a a' g tau [d z]; reflexivity. Qed.
Next Obligation. intros a a' g tau [d z]; reflexivity. Qed.
Next Obligation. intros a a' g psi d z; reflexivity. Qed.
Next Obligation. intros a a' g psi d z; reflexivity. Qed.
Next Obligation. intros a psi [d z]; simpl; now rewrite id_right. Qed.
Next Obligation. intros a tau d z; simpl; now rewrite id_right. Qed.

(*
 The upgrade is an upgrade: the components ARE the pointwise legs. 

 --------
 升级就是升级：组件就是逐点支撑腿。
*)

Example kan_coyoneda_to_component (a : D) :
  transform[to kan_coyoneda] a = to (kan_iso_at a) := eq_refl.

Example kan_coyoneda_from_component (a : D) :
  transform[from kan_coyoneda] a = from (kan_iso_at a) := eq_refl.

(** ** The literal Δ-reading / ** 字面Δ读法 *)

(*
 Mac Lane writes the right-hand side as Nat(Δa, Q).  A [Transform] out
 of the constant functor is the same leg family as an [ACone] with the
 coherence law read against [fmap[Δa] f = id]; the passages below cost
 exactly one [id_right] each. 

 --------
 麦克·莱恩将右侧写作 Nat(Δa, Q)。从常数函子出来的 A [Transform] 与一个 [ACone] 的腿族相同，其连贯律与 [fmap[Δa] f = id 相对应；下面的部分每部分正好花费一个 [id_right]。
*)

Lemma kan_transform_naturality {a : D} (psi : ACone a (Elements_proj K))
      {x y : Elements K} (f : x ~{Elements K}~> y) :
  fmap[Elements_proj K] f ∘ leg psi x
    ≈ leg psi y ∘ fmap[Δ[Elements K](a)] f.
Proof. rewrite id_right; exact (coh psi f). Qed.

Lemma kan_transform_naturality_sym {a : D} (psi : ACone a (Elements_proj K))
      {x y : Elements K} (f : x ~{Elements K}~> y) :
  leg psi y ∘ fmap[Δ[Elements K](a)] f
    ≈ fmap[Elements_proj K] f ∘ leg psi x.
Proof. rewrite id_right; symmetry; exact (coh psi f). Qed.

Definition kan_transform_of_cone {a : D}
           (psi : ACone a (Elements_proj K)) :
  Δ[Elements K](a) ⟹ Elements_proj K :=
  @Build_Transform (Elements K) D (Δ[Elements K](a)) (Elements_proj K)
    (fun j => leg psi j)
    (fun x y f => kan_transform_naturality psi f)
    (fun x y f => kan_transform_naturality_sym psi f).

Lemma kan_cone_of_transform_coherence {a : D}
      (theta : Δ[Elements K](a) ⟹ Elements_proj K)
      {x y : Elements K} (f : x ~{Elements K}~> y) :
  fmap[Elements_proj K] f ∘ transform[theta] x ≈ transform[theta] y.
Proof.
  rewrite <- (id_right (transform[theta] y)).
  exact (naturality[theta] _ _ f).
Qed.

Definition kan_cone_of_transform {a : D}
           (theta : Δ[Elements K](a) ⟹ Elements_proj K) :
  ACone a (Elements_proj K) :=
  @Build_ACone (Elements K) D a (Elements_proj K)
    (fun j => transform[theta] j)
    (fun x y f => kan_cone_of_transform_coherence theta f).

Example kan_transform_of_cone_component {a : D}
        (psi : ACone a (Elements_proj K)) (j : Elements K) :
  transform[kan_transform_of_cone psi] j = leg psi j := eq_refl.

Example kan_cone_of_transform_leg {a : D}
        (theta : Δ[Elements K](a) ⟹ Elements_proj K) (j : Elements K) :
  leg (kan_cone_of_transform theta) j = transform[theta] j := eq_refl.

Lemma kan_cone_transform_cone {a : D} (psi : ACone a (Elements_proj K)) :
  @equiv _ (AConeEquiv a (Elements_proj K))
         (kan_cone_of_transform (kan_transform_of_cone psi)) psi.
Proof. intro j; reflexivity. Qed.

Lemma kan_transform_cone_transform {a : D}
      (theta : Δ[Elements K](a) ⟹ Elements_proj K) :
  kan_transform_of_cone (kan_cone_of_transform theta) ≈ theta.
Proof. intro j; reflexivity. Qed.

(*
 The setoid of Δ-transformations, named so the two isomorphisms below
 can mention it without repeating the packaging. 

 --------
 Δ-变换的集合体，因此命名，使得下面的两个同构可以在不重复包装的情况下提到它。
*)

Definition KanDelta (a : D) : SetoidObject :=
  {| carrier   := Δ[Elements K](a) ~{[Elements K, D]}~> Elements_proj K
   ; is_setoid := @homset ([Elements K, D])
                          Δ[Elements K](a) (Elements_proj K) |}.

Program Definition kan_cone_transform_iso (a : D) :
  KanCone a ≅[Sets] KanDelta a := {|
  to   := {| morphism := fun psi   => kan_transform_of_cone psi |};
  from := {| morphism := fun theta => kan_cone_of_transform theta |}
|}.
Next Obligation. intros a psi psi' H j; exact (H j). Qed.
Next Obligation. intros a th th' H j; exact (H j). Qed.
Next Obligation. intros a th; apply kan_transform_cone_transform. Qed.
Next Obligation. intros a psi; apply kan_cone_transform_cone. Qed.

(*
 Mac Lane's own phrasing: Nat(K, D(a,−)) ≅ Nat(Δa, Q). 

 --------
 麦克·莱恩自己的表述：Nat(K, D(a,−)) ≅ Nat(Δa, Q)。
*)

Definition kan_iso_transform (a : D) : KanNat a ≅[Sets] KanDelta a :=
  iso_compose (kan_cone_transform_iso a) (kan_iso_at a).

End Kan.
