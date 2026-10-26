Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Limit.Product.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.

Generalizable All Variables.

(* * * Wide pullbacks, and products as wide pullbacks over a terminal object / * * 宽拉回，以及作为终对象上的宽拉回的积 *)

(*
 nLab:      https://ncatlab.org/nlab/show/wide+pullback
 nLab:      https://ncatlab.org/nlab/show/pullback
 Wikipedia: https://en.wikipedia.org/wiki/Pullback_(category_theory)

 A WIDE PULLBACK replaces the two legs of an ordinary pullback by an
 I-indexed family of them.  Given objects A i and a common codomain z
 with maps f i : A i ~> z, a wide pullback is an object P carrying
 projections p i : P ~> A i on which all the composites agree,

 ∀ i j,  f i ∘ p i ≈ f j ∘ p j,

 universal with that property: every competing family q i : Q ~> A i
 whose composites agree factors through the p i by a unique mediator.
 At I = 2 this is the ordinary pullback of a cospan; at I = 1 it is the
 identity; at I = 0 it is the terminal object (see below).

 THE HEADLINE is Riehl's observation (Category Theory in Context, 2nd
 ed., §3.5, printed p. 114 = PDF p. 134, catalogued as riehl:3.5:lem15):
 the pullback of A → * ← B over a TERMINAL object is the binary product,
 and more generally the I-indexed PRODUCT of a family is the WIDE
 PULLBACK of the maps A i → *.  Her reason is entirely about the shape of
 the condition rather than about any construction: a terminal codomain
 imposes NO commutativity condition, because any two maps into 1 agree by
 [one_unique], so a cone over that diagram is exactly an I-indexed family
 of maps and nothing more.  Her corollary — a category with pullbacks and
 a terminal object has all binary, hence all finite, products — is the
 binary case of the same remark and is a companion file,
 Structure/Pullback/Reduction.v; this file owns the WIDE generalization.

 WHERE [one_unique] IS SPENT, and it is spent TWICE, in complementary
 directions.  In [wide_pullback_product] it DISCHARGES the commutativity
 field: the goal [one ∘ p i ≈ one ∘ p j] is closed by [one_unique]
 directly, and the universal property is then [iprod_desc] with the
 competing family's hypothesis DISCARDED unused.  In the converse
 [product_wide_pullback] it MANUFACTURES that same hypothesis: to invoke
 [wpull_ump] on an arbitrary family [pi] one must supply
 [∀ i j, one ∘ pi i ≈ one ∘ pi j], and [one_unique] supplies it.  Both
 uses are single, named [apply (@one_unique C T)] steps, deliberately not
 folded into [cat] or any other automation, so that the one step carrying
 Riehl's argument is visible in the proof script.

 THE EMPTY INDEX IS A REAL BOUNDARY, AND THIS FORMULATION GETS IT RIGHT.
 With I empty the [∀ i j] condition is vacuous and the mediator's
 condition [∀ i, p i ∘ u ≈ q i] is vacuous too, so the record degenerates
 to “every object has exactly one map to P” — which is terminality.
 That is proved in BOTH directions, [wide_pullback_empty_terminal] and
 [terminal_wide_pullback_empty], and it is a biconditional at fixed data:
 over an empty index [IsWidePullback f P p] holds exactly when P is
 terminal, for the (necessarily empty) family p and ANY codomain z.  Both
 directions genuinely consume [Hempty] — the forward one to build the
 empty competing family to instantiate [wpull_ump] at, the backward one
 to make both the commutativity field and the mediator's condition
 vacuous — so neither is an artifact of the proof.

 This is worth contrasting with the sibling construction.
 Structure/Equalizer/Wide.v's empty case is a SHARPNESS OBSTRUCTION: its
 elementary record is satisfied there by [id[x]], which does NOT agree
 with the limit over the same shape, and that file proves the mismatch by
 deriving an inhabitant of an empty hom-set.  Here the empty case is
 instead a clean IDENTIFICATION.

 AN EARLIER DRAFT OF THIS HEADER EXPLAINED THAT CONTRAST BY SAYING THAT A
 WIDE FORK “CARRIES A SECOND LEG WHICH THE EMPTY CONDITION LEAVES
 UNCONSTRAINED”.  THAT IS FALSE, AND IT IS FALSE ABOUT ANOTHER FILE'S
 RECORD, SO IT IS RECORDED HERE AS BAD EVIDENCE RATHER THAN QUIETLY
 DELETED.  [IsWideEqualizer] (Structure/Equalizer/Wide.v) has exactly
 TWO fields and ONE leg [e : q ~> x]; it carries no second leg, and that
 file says three separate times that a leg-carrying record is NOT built
 there.  The second leg belongs to the CONE, and is MANUFACTURED from a
 chosen index as [fs i0 ∘ h] -- which is precisely why that development
 needs a pointed section.  The polarity of the original explanation was
 therefore inverted: the fork's LACK of a second leg is the cause, not its
 possession of one.

 What should be said instead is weaker and is the honest statement.  The
 sibling's empty case is an obstruction RELATIVE TO ITS LIMIT
 PRESENTATION.  This file builds no limit presentation at all (see NOT
 DELIVERED below), so no analogous disagreement can arise here.  The
 contrast is therefore NOT evidence that the wide-pullback notion is
 better behaved; it partly reflects that less is claimed here, and a
 wide-cospan shape would retain its codomain object at I = ∅ much as the
 fork's does.
 Nothing here needs a chosen inhabitant of I, so this file has no pointed
 section at all and no analogue of that file's [i0] hypothesis.

 STRENGTHS, MEASURED STRICT-FIRST.

 - BOTH round trips between [IsWidePullback] and the bundled
 [WidePullback] close by [eq_refl], on the WHOLE RECORD, in BOTH
 directions ([wide_pullback_predicate_round],
 [wide_pullback_bundled_round]).  Both records have primitive
 projections with eta (Lib/Foundation.v's [Set Primitive Projections]
 reaches them), so the two conversions are definitional inverses and
 not merely mutually inverse up to ≈.
 - The BINARY round trip is REFUTED at [eq_refl] on the whole record,
 and the obstruction is LOCATED rather than guessed:
 [wide_pullback_binary_commutes] shows the [is_pullback_commutes]
 FIELD does convert by [eq_refl] (the [∀ i j] condition iota-reduces
 at the literals [true] and [false]), so what blocks the record
 equality is the [is_pullback_ump] field alone, which is rebuilt
 through a fresh [Build_Unique].  The whole-record equality is
 therefore stated nowhere below; it is a negative for a [Fail] probe.
 - [wide_pullback_unique] delivers a bare [≅], exactly as its binary
 donor [pullback_unique] and its sibling [wide_equalizer_unique] do.
 It is NOT upgraded to a leg-carrying essential uniqueness in the
 manner of Structure/Limit/Unique.v.

 UNIVERSES, read from the CONSTRAINT BLOCKS and not off the binders
 (reproduce with [Set Printing Universes. Print IsWidePullback. About
 wide_pullback_product.]).  [IsWidePullback@{u u0 u1 u2}] is over
 [C : Category@{u1 u2 u2}] and [I : Type@{u}] with constraint block
 [u <= u0, u2 <= u0], where u0 is the record's own sort level.  Two
 readings matter.

 - The INDEX universe u and the OBJECT universe u1 are INDEPENDENT: u1
 occurs in no constraint at all, and u is merely BOUNDED by the sort
 level, not identified with anything.  This is not inferred from the
 binder: it is checked by two probe sections that declare the levels
 SEPARATELY and impose a STRICT inequality, [Constraint uo < ui] and
 [Constraint ui < uo], and the record elaborates under BOTH.  (An
 unannotated probe collapses the two by minimization and would have
 reported nothing.)
 - The hom and proof universes ARE identified, and that identification
 is REAL but INHERITED.  A probe declaring [Constraint uh < up]
 rejects [IsWidePullback]; the SAME probe rejects the donor
 [IsIndexedProduct] just as flatly, while a control at the same
 levels accepts the bare hom-setoid statement [f ≈ g].  So the
 identification belongs to the house's [Record … {C : Category}]
 idiom that this file shares with its donor, is not a consequence of
 the setoid on homs, and is not introduced here.  Correspondingly
 [wide_pullback_product]'s constraint block is [u <= u0, u2 <= u0] —
 the same block [IsIndexedProduct] itself carries.

 NON-VACUITY.  [Sets_wide_pullback_over_one] instantiates the headline at
 [Sets], exhibiting [Sets_iprod_obj F] with its projections as a wide
 pullback of the family [F i → 1].  Its universe constraint is INFERRED --
 there is no annotation on it, an earlier draft of this header said there
 was -- and identifies
 the index universe with the carrier universe of [Sets]; that is the
 DONOR's constraint, documented in Instance/Sets/Products.v's own header
 for [Sets_HasIndexedProducts], and the probes above show this file's
 record does not force it.  The [Instance/Sets] dependency is taken for
 this witness alone; the sibling takes [Instance/Parallel] and
 [Instance/Two] on the same footing.

 NOT DELIVERED, and the scope of each statement is this file rather than
 the tree.  No limit presentation: nothing below builds the wide-cospan
 shape category or relates [IsWidePullback] to [Limit] of a diagram over
 it, so there is no analogue here of Structure/Pullback/Limit.v's
 reconciliation and none of the sibling's limit round trips.  No
 [HasWidePullbacks] instance is built HERE (an earlier revision said the
 class was uninhabited tree-wide; Instance/Sets/SubobjectLattice.v's
 [Sets_HasWidePullbacks] now inhabits it).  No wide-pullback stability,
 pasting, or preservation statements.  No wide PUSHOUT dual.  No claim
 that the binary specialization below agrees with whatever the other
 delegate's Structure/Pullback/Reduction.v proves: the two files are
 independent and nothing here cites that one. 

 --------
 nLab:       https://ncatlab.org/nlab/show/wide+pullback 
 nLab:       https://ncatlab.org/nlab/show/pullback 
 Wikipedia:  https://en.wikipedia.org/wiki/Pullback_(category_theory) 

 广义拉回将普通拉回的两条边替换为由 I 索引的族。 给定对象 A_i 和一个公共余域 z 及映射 f_i : A_i ~> z，一个广义拉回是一个对象 P，携带投影 p_i : P ~> A_i，满足所有复合映射一致：

 ∀ i j,  f_i ∘ p_i ≈ f_j ∘ p_j,

 并且具有该性质的普遍性：每个竞争族 q_i : Q ~> A_i，其复合映射一致，都通过唯一的中介映射因子化为 p_i。 当 I = 2 时，这是余锥的普通拉回；当 I = 1 时，它是恒等映射；当 I = 0 时，它是终对象（见下文）。标题是Riehl的观察（《Category Theory in Context》，第2版，第3.5节，印刷版第114页 = PDF第134页，目录编号为riehl:3.5:lem15）：
 从A → * ← B 对一个终对象的拉回是二元积，更一般地，一个家族的I索引积是映射A_i → *的广义拉回。她的理由完全关于条件的形状，而不是任何构造：一个终余域不施加任何交换条件，因为任意两个映射到1的映射都相同，因此该图上的锥正好是一个I索引的映射家族，仅此而已。她的推论——一个具有拉回和终对象的范畴具有所有二元（因此也具有所有有限）积——是同一评论的二元情况，并且是一个伴随文件，Structure/Pullback/Reduction.v；这个文件拥有更广泛的推广。[one_unique] 被消耗，并且它被消耗两次，方向互补。在 [wide_pullback_product] 中，它释放了交换性域：目标 [one ∘ p i ≈ one ∘ p j] 由 [one_unique] 直接闭合，然后普适性属性是 [iprod_desc]，并且竞争族的假设被丢弃而未使用。相反地，在 [product_wide_pullback] 中，它生成了相同的假设：要在任意族 [pi] 上调用 [wpull_ump]，必须提供 [∀ i j, one ∘ pi i ≈ one ∘ pi j]，而 [one_unique] 提供了它。这两种用途都是单一的、命名为 [apply (@one_unique C T)] 的步骤，有意没有折叠进 [cat] 或任何其他自动化中，以便携带 Riehl 论证的那一步在证明脚本中可见。空索引是真正的边界，而这个表述是正确的。
 当 I 为空时，[∀ i j] 条件是空的，中介的
 条件 [∀ i, p i ∘ u ≈ q i] 也为空，因此记录退化为“每个对象正好有一个映射到 P”——这就是终对象性。
 这一点在两个方向上都被证明，[wide_pullback_empty_terminal] 和
 [terminal_wide_pullback_empty]，并且在固定数据下它是一个双条件：
 对于空索引 [IsWidePullback f P p]，当且仅当 P 是终对象时成立，对于（必然为空的）族 p 和任何余域 z。两个方向确实都使用了 [Hempty]——前向方向用于构建空竞争族以实例化 [wpull_ump]，反向方向用于使交换场和中介条件都为空——因此都不是证明的人工产物。这值得与同类结构进行对比。结构/均衡器/Wide.v 的空情况是一个尖锐度阻碍：它的基本记录在那里被 [id[x] 满足，而 [id[x] 与相同形状上的极限不一致，该文件通过推导空同态集的一个元素来证明这种不匹配。这里，空情况则是一个干净的识别。这个标题的早期版本通过说一个宽叉“带有一个第二条腿，而空条件没有约束它”来解释这个对比。那是错误的，而且对于另一个文件的记录也是错误的，所以这里将其记录为不好的证据，而不是悄悄删除。[IsWideEqualizer] (Structure/Equalizer/Wide.v) 恰好有两​​个字段和一条腿 [e : q ~> x]；它没有携带第二条腿，并且该文件三次明确说明在这里没有构建携带腿的记录。第二条腿属于圆锥，并且是从选定的索引制造的，作为 [fs i0 ∘ h]——这正是为什么那部分开发需要尖锐部分的原因。因此，原始解释的极性被颠倒了：叉缺少第二条腿才是原因，而不是拥有它。应该说的是更弱的，也是诚实的陈述。 该兄弟文件的空案例是相对于其限制演示的阻碍。 该文件完全没有构建限制演示（见下文的未交付部分），因此这里不会产生类似的分歧。 因此，这种对比并不能作为宽拉回概念行为更良好的证据；它部分反映了这里的声明较少，并且宽余铺展形状在 I = ∅ 时会保持其余范对象，就像叉子的情况一样。 这里不需要 I 的选定元素，因此此文件根本没有带点的截面，也没有该文件的 [i0] 假设的类比。  优势，严格优先测量。- 在整个记录上，[IsWidePullback] 和紧邻 [eq_refl] 的捆绑 [WidePullback] 之间的往返旅程都成立，双向都是如此（[wide_pullback_predicate_round]，[wide_pullback_bundled_round]）。两个记录都有基本投影（Lib/Foundation.v 的 [Set Primitive Projections] 可达它们），因此这两个转换是定义上的逆，而不仅仅是互为逆至 ≈。- 在整个记录上，二进制往返在 [eq_refl] 处被驳斥，并且障碍被定位而不是猜测：[wide_pullback_binary_commutes] 显示 [is_pullback_commutes] 字段确实通过 [eq_refl] 转换（[∀ i j] 条件在文字 [true] 和 [false] 处 iota 减少），所以阻碍记录相等的只是 [is_pullback_ump] 字段，它通过新的 [Build_Unique] 重建。因此，下文中没有说明全记录相等性；对于 [Fail] 探针来说，它是否定的。[wide_pullback_unique] 提供了一个裸 [≅]，就像它的二进制提供者 [pullback_unique] 和它的同类 [wide_equalizer_unique] 一样。它不会像 Structure/Limit/Unique.v 那样升级为带腿的基本唯一性。

 宇宙（UNIVERSES），从约束块（CONSTRAINT BLOCKS）读取，而不是从绑定器读取（可通过 [Set Printing Universes. Print IsWidePullback. About wide_pullback_product.] 重现）。[IsWidePullback@{u u0 u1 u2}] 在 [C : Category@{u1 u2 u2}] 和 [I : Type@{u}] 上面，并带有约束块 [u <= u0, u2 <= u0]，其中 u0 是该记录自身的排序级别。有两个读取方式很重要。- 索引宇宙 u 和对象宇宙 u1 是独立的：u1 完全不出现在任何约束中，而 u 仅受排序级别的限制，并未与任何东西认同。这并不是从绑定器推断出来的：它是通过两个分别声明级别并施加严格不等式的探测部分 [Constraint uo < ui] 和 [Constraint ui < uo] 来检验的，并且记录在两者下都有详细说明。（一个未标注的探测器会通过最小化将两者合并，并且不会报告任何内容。）
 - 同态和证明宇宙是被认同的，这种认同是真实的但继承而来的。一个声明 [Constraint uh < up] 的探测器会拒绝 [IsWidePullback]；同一个探测器也会同样直接拒绝捐赠者 [IsIndexedProduct]，而在相同级别的控制下，则接受裸的同态等价类声明 [f ≈ g]。所以，该标识属于这栋房子 [Record … {C : Category}] 的习语，这个文件与其捐赠者共享，它不是同态集合上的推论，也不是在此引入的。相应地，[wide_pullback_product] 的约束块是 [u <= u0, u2 <= u0]——同一个块 [IsIndexedProduct] 本身所承载的。非空性。[Sets_wide_pullback_over_one] 在 [Sets] 实例化标题，展示了 [Sets_iprod_obj F] 及其投影，作为族 [F i → 1] 的广泛回溯。它的宇宙约束是推断的——它上面没有注释，之前的草稿中这个标题说过有——并且将索引宇宙识别为 [Sets] 的承载宇宙；那是捐赠者的约束，记录在 Instance/Sets/Products.v 文件中 [Sets_HasIndexedProducts] 自身标题里，上面的探测显示此文件的记录并未强制它。[Instance/Sets] 依赖仅适用于该见证；其兄弟采用 [Instance/Parallel] 和 [Instance/Two] 处于同等地位。未交付，每个声明的范围是此文件而不是树。 无极限表示：下面没有任何内容构建宽跨度的形态类别，也没有将 [IsWidePullback] 与 [Limit] 关联到其上的图，因此这里没有 Structure/Pullback/Limit.v 的调和，也没有任何兄弟的极限往返。 此处未构建 [HasWidePullbacks] 实例（早期版本称此类在整个树中无实例；Instance/Sets/SubobjectLattice.v 的 [Sets_HasWidePullbacks] 现在实例化了它）。 没有宽拉回稳定性、粘合或保持声明。 没有宽 PUSHOUT 对偶。 未声明下面的二元特化与另一个代理的 Structure/Pullback/Reduction.v 所证明的任何内容相一致：这两个文件是独立的，此处没有引用那个文件。
*)

(* * ** The elementary universal property / * ** 基本的泛性质 *)

(*
 [P] with projections [p] is a wide pullback of the family [f] when all
 the composites into the common codomain agree and every family agreeing
 in the same way factors uniquely.  The commutativity condition
 quantifies over PAIRS of indices, exactly as [wfork_eq] does in
 Structure/Equalizer/Wide.v; no distinguished index is named, so nothing
 in this record requires I to be inhabited. 

 --------
 [P] 与投影 [p] 是族 [f] 的广义回撤，当所有复合映射到公共上同域时都一致，并且每个以相同方式一致的族唯一地分解。交换条件对索引对进行量化，正如 Structure/Equalizer/Wide.v 中的 [wfork_eq] 所做的那样；没有指定的索引被命名，因此此记录中没有任何内容要求 I 是非空的。
*)
Record IsWidePullback {C : Category} {I : Type} {A : I → C} {z : C}
  (f : ∀ i : I, A i ~> z) (P : C) (p : ∀ i : I, P ~> A i) := {
  (* every leg is carried to the common codomain in the same way / 每条腿都以相同的方式被传递到公共陪域 *)
  wpull_commutes : ∀ i j : I, f i ∘ p i ≈ f j ∘ p j;

  (* universal property: every jointly agreeing family factors uniquely / 通用性质：每一个共同同意的家族都有唯一的分解 *)
  wpull_ump {Q : C} (q : ∀ i : I, Q ~> A i)
    (Hq : ∀ i j : I, f i ∘ q i ≈ f j ∘ q j) :
    ∃! u : Q ~> P, ∀ i : I, p i ∘ u ≈ q i
}.

Arguments wpull_commutes {_ _ _ _ _ _ _} _ _ _.
Arguments wpull_ump {_ _ _ _ _ _ _} _ {_} _ _.

(** ** The bundled record / ** 捆绑记录 *)

(*
 The apex-carrying form, shaped after [Pullback] of Structure/Pullback.v
 rather than after the ∃-valued [HasWideEqualizers] of the sibling: a
 wide pullback is CHOSEN here, so consumers read the object off the
 record instead of destructing an existential. 

 --------
 携带顶点的形式，其形状是按照 Structure/Pullback.v 的 [Pullback] 而不是其同级 [HasWideEqualizers] 的 ∃ 值来决定的：这里选择了一个宽拉回，因此消费者直接从记录中读取对象，而不是解构一个存在型。
*)
Record WidePullback {C : Category} {I : Type} {A : I → C} {z : C}
  (f : ∀ i : I, A i ~> z) := {
  WPull : C;                             (* the wide pullback object / 宽拉回物体 *)
  wide_pullback_proj : ∀ i : I, WPull ~> A i;   (* the projections / 预测 *)

  wide_pullback_commutes : ∀ i j : I,
    f i ∘ wide_pullback_proj i ≈ f j ∘ wide_pullback_proj j;

  ump_wide_pullbacks : ∀ (Q : C) (q : ∀ i : I, Q ~> A i),
    (∀ i j : I, f i ∘ q i ≈ f j ∘ q j)
    → ∃! u : Q ~> WPull, ∀ i : I, wide_pullback_proj i ∘ u ≈ q i
}.

Arguments WPull {_ _ _ _ _} _.
Arguments wide_pullback_proj {_ _ _ _ _} _ _.
Arguments wide_pullback_commutes {_ _ _ _ _} _ _ _.
Arguments ump_wide_pullbacks {_ _ _ _ _} _ _ _ _.

Coercion WPull : WidePullback >-> obj.

(* Both conversions are field repackagings, mirroring [pullback_is_pullback] and [is_pullback_pullback] of Theory/Morphisms/Stability.v. / 这两种转换都是字段重新打包，镜像 [pullback_is_pullback] 和 [is_pullback_pullback] 在 Theory/Morphisms/Stability.v 中的定义。 *)

Definition wide_pullback_is_pullback {C : Category} {I : Type} {A : I → C}
  {z : C} {f : ∀ i : I, A i ~> z} (W : WidePullback f) :
  IsWidePullback f (WPull W) (wide_pullback_proj W) :=
  {| wpull_commutes := wide_pullback_commutes W
   ; wpull_ump      := fun Q q Hq => ump_wide_pullbacks W Q q Hq |}.

Definition is_wide_pullback_pullback {C : Category} {I : Type} {A : I → C}
  {z : C} {f : ∀ i : I, A i ~> z} {P : C} {p : ∀ i : I, P ~> A i}
  (W : IsWidePullback f P p) : WidePullback f :=
  {| WPull                  := P
   ; wide_pullback_proj     := p
   ; wide_pullback_commutes := wpull_commutes W
   ; ump_wide_pullbacks     := fun Q q Hq => wpull_ump W q Hq |}.

(*
 MEASURED STRICT: both composites are the identity on the nose, on the
 WHOLE record, because both records have primitive projections with eta.
 Neither is merely an equivalence up to ≈. 

 --------
 严格测量：两个复合映射在整个记录上都是精确的恒等映射，因为两个记录都有带有η的原始投影。两者都不仅仅是≈下的等价。
*)

Example wide_pullback_predicate_round {C : Category} {I : Type} {A : I → C}
  {z : C} {f : ∀ i : I, A i ~> z} {P : C} {p : ∀ i : I, P ~> A i}
  (W : IsWidePullback f P p) :
  wide_pullback_is_pullback (is_wide_pullback_pullback W) = W := eq_refl.

Example wide_pullback_bundled_round {C : Category} {I : Type} {A : I → C}
  {z : C} {f : ∀ i : I, A i ~> z} (W : WidePullback f) :
  is_wide_pullback_pullback (wide_pullback_is_pullback W) = W := eq_refl.

(*
 A category has all wide pullbacks when every family over a common
 codomain carries one.  As with [HasIndexedProducts], the index [Type] is
 a universe PARAMETER of the class and not a quantifier over every
 universe; a consumer whose index is a hom-type instantiates it there. 

 --------
 当每个在公共上域上的族都具有一个时，一个范畴具有所有的广拉回。和 [HasIndexedProducts] 一样，指标 [Type] 是该类的宇宙参数，而不是对每个宇宙的量词；其指标为同型类型的使用者在此处实例化它。
*)
Class HasWidePullbacks (C : Category) := {
  wide_pullback {I : Type} {A : I → C} {z : C} (f : ∀ i : I, A i ~> z) :
    WidePullback f
}.

Arguments wide_pullback {C _ I A z} f.

(* * ** The projections are jointly monic / * ** 投影是联合单射的 *)

(*
 Two maps into the apex agreeing after every projection are equal: both
 are the mediator of one and the same family.  As with the sibling's
 [wide_equalizer_monic], no index is ever named, so this holds for every
 index type, the empty one included — where it degenerates to the (then
 true) statement that any two maps into a terminal object agree. 

 --------
 两个进入顶点的映射在每次投影后都相等：它们都是同一个族的中介。就像兄弟的 [wide_equalizer_monic] 一样，索引从未被命名过，所以这适用于每种索引类型，包括空索引 —— 在这种情况下，它退化为（当时的）命题，即任意两个进入终端对象的映射都是相等的。
*)
Lemma wide_pullback_jointly_monic {C : Category} {I : Type} {A : I → C}
  {z : C} {f : ∀ i : I, A i ~> z} {P : C} {p : ∀ i : I, P ~> A i}
  (W : IsWidePullback f P p) {Q : C} (u v : Q ~> P)
  (Hd : ∀ i : I, p i ∘ u ≈ p i ∘ v) : u ≈ v.
Proof.
  assert (Hq : ∀ i j : I, f i ∘ (p i ∘ u) ≈ f j ∘ (p j ∘ u)).
  { intros i j.
    rewrite !comp_assoc.
    now rewrite (wpull_commutes W i j). }
  transitivity (unique_obj (wpull_ump W (fun i => p i ∘ u) Hq)).
  - symmetry.
    apply (uniqueness (wpull_ump W (fun i => p i ∘ u) Hq)).
    intro i; reflexivity.
  - apply (uniqueness (wpull_ump W (fun i => p i ∘ u) Hq)).
    intro i; symmetry; apply Hd.
Qed.

(* * ** Wide pullbacks are unique up to isomorphism / * ** 宽回撤在同构下是唯一的 *)

(*
 The binary argument verbatim, one index at a time: each apex mediates
 into the other along the other's projections, and the round trips agree
 with the canonical self-mediator, which is the identity. 

 --------
 二进制参数逐字地，一次一个索引：每个顶点沿着另一个顶点的投影相互调解，并且往返路径与标准自我调解者一致，后者就是恒等式。
*)
Lemma wide_pullback_unique {C : Category} {I : Type} {A : I → C} {z : C}
  {f : ∀ i : I, A i ~> z} {P1 P2 : C}
  {p1 : ∀ i : I, P1 ~> A i} {p2 : ∀ i : I, P2 ~> A i}
  (W1 : IsWidePullback f P1 p1) (W2 : IsWidePullback f P2 p2) : P1 ≅ P2.
Proof.
  pose proof (wpull_ump W2 p1 (wpull_commutes W1)) as D12.
  pose proof (wpull_ump W1 p2 (wpull_commutes W2)) as D21.
  pose proof (wpull_ump W1 p1 (wpull_commutes W1)) as D11.
  pose proof (wpull_ump W2 p2 (wpull_commutes W2)) as D22.
  unshelve refine {| to := unique_obj D12; from := unique_obj D21 |}.
  - transitivity (unique_obj D22).
    + symmetry.
      apply (uniqueness D22).
      intro i.
      rewrite comp_assoc, (unique_property D12 i).
      exact (unique_property D21 i).
    + apply (uniqueness D22).
      intro i; apply id_right.
  - transitivity (unique_obj D11).
    + symmetry.
      apply (uniqueness D11).
      intro i.
      rewrite comp_assoc, (unique_property D21 i).
      exact (unique_property D12 i).
    + apply (uniqueness D11).
      intro i; apply id_right.
Defined.

(* * ** The empty index: the wide pullback is the terminal object / * ** 空索引：大幅回调是终端对象 *)

(*
 Over an empty index there is exactly one family of legs into any apex,
 namely the empty function. 

 --------
 在一个空索引上，对于任何顶点恰好有一个腿族，即空函数。
*)
Definition wpull_empty_legs {C : Category} {I : Type} {A : I → C}
  (Hempty : I → False) (Q : C) : ∀ i : I, Q ~> A i.
Proof. intro i; destruct (Hempty i). Defined.

(* ... and it agrees with itself vacuously. / ... 并且它自然而然地与自己一致。 *)
Lemma wpull_empty_comm {C : Category} {I : Type} {A : I → C} {z : C}
  (f : ∀ i : I, A i ~> z) (Hempty : I → False) {Q : C}
  (q : ∀ i : I, Q ~> A i) : ∀ i j : I, f i ∘ q i ≈ f j ∘ q j.
Proof. intros i j; destruct (Hempty i). Qed.

(*
 So a wide pullback over an empty index is a terminal object: the
 mediator exists for every Q, and its defining condition being vacuous,
 EVERY map into P satisfies it and is therefore that mediator. 

 --------
 因此，在一个空指数上进行广泛回撤是一个终端对象：对于每个 Q 都存在中介物，而它的定义条件是空洞的，所以每一个指向 P 的映射都满足该条件，因此都是那个中介物。
*)
Lemma wide_pullback_empty_terminal {C : Category} {I : Type} {A : I → C}
  {z : C} {f : ∀ i : I, A i ~> z} {P : C} {p : ∀ i : I, P ~> A i}
  (Hempty : I → False) (W : IsWidePullback f P p) : IsTerminalObj P.
Proof.
  intro Q.
  pose proof (wpull_ump W (wpull_empty_legs Hempty Q)
                (wpull_empty_comm f Hempty (wpull_empty_legs Hempty Q)))
    as U.
  unshelve eapply Build_Unique.
  - exact (unique_obj U).
  - exact Logic.I.
  - intros v _.
    apply (uniqueness U).
    intro i; destruct (Hempty i).
Defined.

(*
 Conversely a terminal object is a wide pullback of the empty family over
 ANY codomain, with its (empty) family of projections.  Emptiness is used
 twice, once for each field. 

 --------
 相反，终端对象是任意余域上空族的广泛拉回，其投影的族也是空的。空性被使用了两次，每个字段各一次。
*)
Definition terminal_wide_pullback_empty {C : Category} {I : Type}
  {A : I → C} {z : C} (f : ∀ i : I, A i ~> z) {P : C}
  (p : ∀ i : I, P ~> A i) (Hempty : I → False) (H : IsTerminalObj P) :
  IsWidePullback f P p.
Proof.
  unshelve refine {| wpull_commutes := _ |}.
  - intros i j; destruct (Hempty i).
  - intros Q q Hq.
    unshelve eapply Build_Unique.
    + exact (is_terminal_one H).
    + intro i; destruct (Hempty i).
    + intros v _; apply (is_terminal_unique H).
Defined.

(* * ** Riehl's lemma: products are wide pullbacks over a terminal object / * ** 里尔引理：积是终对象上的广拉回 *)

(*
 An indexed product IS the wide pullback of the family of unique maps to
 the terminal object.  The commutativity condition is discharged by
 [one_unique] — that single step is the whole of Riehl's argument — and
 the universal property is then [iprod_desc] with the competing family's
 agreement hypothesis discarded, since a terminal codomain constrains
 nothing. 

 --------
 一个指标化积是到终对象的一族唯一映射的广义回退。交换条件由 [one_unique] 解除 —— 仅这一步就是 Riehl 论证的全部 —— 然后普遍性质就是 [iprod_desc]，同时丢弃竞争族的一致性假设，因为终余对象不会约束任何东西。
*)
Theorem wide_pullback_product {C : Category} `{T : @Terminal C}
  {I : Type} (A : I → C) (P : C) (p : ∀ i : I, P ~> A i)
  (H : IsIndexedProduct A P p) :
  IsWidePullback (fun i : I => @one C T (A i)) P p.
Proof.
  unshelve refine {| wpull_commutes := _ |}.
  - (* both composites are maps into 1, hence equal / 两个复合映射都是映射到 1，因此相等 *)
    intros i j.
    apply (@one_unique C T).
  - (* the hypothesis [Hq] is discarded: it says nothing over 1 / 假设 [Hq] 被舍弃：它对 1 毫无说明 *)
    intros Q q _.
    exact (iprod_desc H q).
Defined.

(*
 ... and conversely.  Here [one_unique] runs the other way: it is what
 MANUFACTURES the agreement hypothesis that [wpull_ump] demands of an
 arbitrary competing family, which is exactly why the two universal
 properties have the same content over a terminal codomain. 

 --------
 ...反之亦然。这里 [one_unique] 以相反的方式运行：它是制造 [wpull_ump] 对任意竞争家庭所要求的协议假设的东西，这正是为什么这两个普遍属性在终端余域上有相同内容的原因。
*)
Theorem product_wide_pullback {C : Category} `{T : @Terminal C}
  {I : Type} (A : I → C) (P : C) (p : ∀ i : I, P ~> A i)
  (W : IsWidePullback (fun i : I => @one C T (A i)) P p) :
  IsIndexedProduct A P p.
Proof.
  unshelve refine {| iprod_desc := _ |}.
  intros c pi.
  refine (wpull_ump W pi _).
  (* the condition Riehl observes to be no condition at all / 里尔观察到的条件根本不是条件 *)
  intros i j.
  apply (@one_unique C T).
Defined.

(** ** The binary specialization / ** 二进制专业化 *)

(*
 At I := bool the wide notion is the ordinary pullback.  The family and
 the two leg families are written with an explicit [return] annotation so
 that [two_fam x y true] and [two_fam x y false] reduce by iota, which is
 what lets the four-case [∀ i j] condition collapse to the single square
 and back. 

 --------
 在 I := bool 时，广义概念是普通的拉回。该族及两条腿的族用显式的 [return] 注释表示，以便 [two_fam x y true] 和 [two_fam x y false] 可以通过 iota 归约，这就是让四情况的 [∀ i j] 条件简化为单个方形并返回的原因。
*)
Definition two_fam {C : Category} (x y : C) : bool → C :=
  fun b => if b then x else y.

Definition two_maps {C : Category} {x y z : C} (f : x ~> z) (g : y ~> z) :
  ∀ b : bool, two_fam x y b ~> z :=
  fun b => if b as b' return (two_fam x y b' ~> z) then f else g.

Definition two_legs {C : Category} {x y P : C} (p1 : P ~> x) (p2 : P ~> y) :
  ∀ b : bool, P ~> two_fam x y b :=
  fun b => if b as b' return (P ~> two_fam x y b') then p1 else p2.

Theorem wide_pullback_binary {C : Category} {x y z : C}
  {f : x ~> z} {g : y ~> z} {P : C} {p1 : P ~> x} {p2 : P ~> y}
  (W : IsWidePullback (two_maps f g) P (two_legs p1 p2)) :
  IsPullback f g P p1 p2.
Proof.
  unshelve refine {| is_pullback_commutes := _ |}.
  - (* the square is the [∀ i j] condition at [true], [false] / 正方形在 [true], [false] 处是 [∀ i j] 条件 *)
    exact (wpull_commutes W true false).
  - intros Q q1 q2 Hq.
    assert (Hc : ∀ i j : bool,
              two_maps f g i ∘ two_legs q1 q2 i
                ≈ two_maps f g j ∘ two_legs q1 q2 j).
    { intros i j; destruct i, j; simpl;
        [ reflexivity | exact Hq | now symmetry | reflexivity ]. }
    pose proof (wpull_ump W (two_legs q1 q2) Hc) as U.
    unshelve eapply Build_Unique.
    + exact (unique_obj U).
    + split.
      * exact (unique_property U true).
      * exact (unique_property U false).
    + intros v [Hv1 Hv2].
      apply (uniqueness U).
      intro b; destruct b; assumption.
Defined.

Theorem binary_wide_pullback {C : Category} {x y z : C}
  {f : x ~> z} {g : y ~> z} {P : C} {p1 : P ~> x} {p2 : P ~> y}
  (H : IsPullback f g P p1 p2) :
  IsWidePullback (two_maps f g) P (two_legs p1 p2).
Proof.
  unshelve refine {| wpull_commutes := _ |}.
  - intros i j; destruct i, j; simpl;
      [ reflexivity
      | exact (is_pullback_commutes H)
      | now symmetry; exact (is_pullback_commutes H)
      | reflexivity ].
  - intros Q q Hq.
    pose proof (is_pullback_ump H Q (q true) (q false) (Hq true false)) as U.
    unshelve eapply Build_Unique.
    + exact (unique_obj U).
    + intro b; destruct b; simpl.
      * exact (fst (unique_property U)).
      * exact (snd (unique_property U)).
    + intros v Hv.
      apply (uniqueness U).
      split; [ exact (Hv true) | exact (Hv false) ].
Defined.

(*
 MEASURED STRICT, and REFUTED at the whole record: the binary round trip
 is NOT [eq_refl].  This Example localizes the obstruction to a single
 field — the square itself DOES convert, the [∀ i j] condition
 iota-reducing at the two literals — so what fails is [is_pullback_ump]
 alone, rebuilt through a fresh [Build_Unique].  The whole-record
 equality is therefore not stated here. 

 --------
 经过严格测量，并在整个记录中反驳：二进制往返转换并不是 [eq_refl]。这个示例将阻塞定位到单个字段——平方本身确实可以转换，[∀ i j] 条件在两个字面量上进行 iota 简化——所以失败的是仅 [is_pullback_ump]，通过一个新的 [Build_Unique] 重新构建。因此，整个记录的等式在此未被陈述。
*)
Example wide_pullback_binary_commutes {C : Category} {x y z : C}
  {f : x ~> z} {g : y ~> z} {P : C} {p1 : P ~> x} {p2 : P ~> y}
  (H : IsPullback f g P p1 p2) :
  is_pullback_commutes (wide_pullback_binary (binary_wide_pullback H))
  = is_pullback_commutes H := eq_refl.

(* * ** Non-vacuity: the identification at [Sets] / * ** 非空性：在 [Sets] 的识别 *)

(*
 [Sets] has all indexed products (Instance/Sets/Products.v) and a
 terminal object (Instance/Sets.v), so Riehl's lemma applies: the
 dependent-function setoid ∀ i, F i, with its projections, is a wide
 pullback of the family of unique maps F i → 1.  Nothing is reproved —
 this is [wide_pullback_product] applied to [Sets_IsIndexedProduct]. 

 --------
 [Sets] 拥有所有已索引的产品（Instance/Sets/Products.v）和一个终对象（Instance/Sets.v），因此 Riehl 的引理适用：依赖函数集合 ∀ i, F i 及其投影，是从族唯一映射 F i → 1 的广拉回。没有任何内容被重新证明——这是将 [wide_pullback_product] 应用于 [Sets_IsIndexedProduct] 的结果。
*)
Definition Sets_wide_pullback_over_one {A : Type} (F : A → obj[Sets]) :
  IsWidePullback (fun i : A => @one Sets Sets_Terminal (F i))
    (Sets_iprod_obj F) (Sets_iprod_proj F) :=
  wide_pullback_product F (Sets_iprod_obj F) (Sets_iprod_proj F)
    (Sets_IsIndexedProduct F).

(*
 ... and the converse direction is available at the same witness, so the
 two readings of that object genuinely coincide in a concrete category
 rather than only in the abstract statement. 

 --------
 ... 并且相反的方向在同一个证据处也是可用的，所以该对象的两种解读在具体范畴中真正重合，而不仅仅是在抽象表述中。
*)
Definition Sets_iprod_of_wide_pullback {A : Type} (F : A → obj[Sets]) :
  IsIndexedProduct F (Sets_iprod_obj F) (Sets_iprod_proj F) :=
  product_wide_pullback F (Sets_iprod_obj F) (Sets_iprod_proj F)
    (Sets_wide_pullback_over_one F).
