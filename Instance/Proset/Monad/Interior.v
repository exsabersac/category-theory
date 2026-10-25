Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Adjunction.
Require Import Category.Comonad.Core.
Require Import Category.Comonad.Coalgebra.
Require Import Category.Comonad.Duality.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Reflective.Idempotent.
Require Import Category.Construction.Reflective.FixedPoints.
Require Import Category.Structure.Thin.
Require Import Category.Structure.Thin.Monad.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Poset.
Require Import Category.Instance.Proset.Order.
Require Import Category.Instance.Proset.Monotone.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Proset.Monad.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

(* * * Comonads on a preorder are interior operators / * * 在前序上的余单子是内算子 *)

(*
 nLab: https://ncatlab.org/nlab/show/interior+operator
 nLab: https://ncatlab.org/nlab/show/comonad
 Book: Riehl, "Category Theory in Context", 2nd ed., SS 5.1,
 Example 5.1.7, printed p. 186, and SS 5.2, Example 5.2.6
 (begins p. 189), clause (iv) and footnotes 10–11, printed p. 190
 Book: Fong and Spivak, "Seven Sketches in Compositionality", arXiv v3,
 SS 1.4.4, footnote 8, printed p. 33
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 Springer GTM 5, 1998, SS VI.1, printed p. 139, and SS VI.2,
 printed p. 141

 WHAT THE BOOKS SAY.  Mac Lane's p. 139 defines a comonad in a category
 (display (1^op)) and the comonad ⟨FG, ε, FηG⟩ of an adjunction, and
 then asks "What is a monad in a preorder P?"; his preorder remarks
 there and on p. 141 (algebras) are about monads only.  Riehl's
 Example 5.1.7 (p. 186) adds the dual for a poset: "Dually, a comonad
 on a poset category (P, ≤) defines a kernel operator: an
 order-preserving function K so that Kp ≤ p and Kp = K²p", and names
 the interior of a subset of a space as the instance.  Example 5.2.6
 (begins p. 189), clause (iv) and footnotes 10–11, printed p. 190, says
 that "a coalgebra for the interior kernel operator is exactly an open
 subset", and its footnote 11 reads coalgebras as
 the algebras "for a monad (T, η, µ) on C^op".  Seven Sketches'
 footnote 8 (p. 33) says that for a Galois connection f ⊣ g the other
 composite g ⨟ f (that is, f after g) "satisfies the dual properties:
 (g ⨟ f)(q) ≤ q and (g ⨟ f ⨟ g ⨟ f)(q) ≅ (g ⨟ f)(q) ... This is called
 an interior operator, though we will not discuss this concept
 further".

 WHICH READING IS IMPLEMENTED.  An interior operator on P IS a closure
 operator on the reversed order: [InteriorOperator P] is
 Instance/Proset/Monad.v's [ClosureOperator] at stdlib's
 [flip_PreOrder P], and no new record is introduced.  Read back in P,
 its fields are deflation [int_defl] and the comultiplication
 inequality [int_comult], by conversion; monotonicity [int_mono] is the
 field [mono_pres] with its two points swapped.  Seven Sketches' ≅ is
 [int_idem], the [cl_idem] of the reversed order read backwards, and
 Riehl's "Kp = K²p" is [int_idem_eq] under an explicit
 [Antisymmetric] hypothesis, since the tree's [Poset] is [Proset] with
 antisymmetry discarded.  Riehl states one direction ("defines") for a
 poset; both directions are proved here, over a preorder.

 BY DUALITY, WITH NO LAW PROVED AGAIN.  The dual is obtained in three
 places, and each is measured.
 - The notion: the reversed order, as above.
 - The comonad: Theory/Monad.v defines [Comonad] as a monad at C^op,
 so [interior_comonad] is a monad on (Proset P)^op whose unit and
 multiplication families are the two fields and whose five laws are
 [I].  It is Structure/Thin/Monad.v's [thin_comonad] written out:
 the counit and comultiplication agree by [eq_refl]
 ([interior_comonad_extract], [interior_comonad_duplicate]).  It is
 not DEFINED through [thin_comonad]: that route is refused bare,
 the sort level of Structure/Thin.v's [Thin] being left in the body
 alone; pinned to u or h it adds h <= u or u <= h (measured); with
 + the thin level stays in the block only (the same reason
 Instance/Proset/Monad.v gives for [closure_monad]).
 - The correspondence, by Riehl's route: a comonad W on P is a monad
 on the reversed order.  [comonad_flip_monad W] is
 Instance/Proset/Monad.v's [closure_monad] at the interior operator
 of W, its unit is extract and its multiplication duplicate
 ([comonad_flip_ret], [comonad_flip_join]), and
 [interior_is_flip_closure] says that the interior operator of W IS
 the closure operator of that monad.  The coalgebras follow the same
 way: [wcoalgebra_iff_flip_talgebra] identifies a W-coalgebra with
 an algebra of the reversed-order monad (footnote 11 at the order
 level), and [wcoalgebra_iff_open] is then Monad.v's
 [talgebra_iff_closed] at the reversed order.  A second route is
 [wcoalgebra_iff_open_via_thin], Structure/Thin/Monad.v's
 [thin_wcoalgebra_iff], which is the monad statement at C^op.
 [open_iff_fixed] is "x ≤ Kx ≤ x" as Kx ≅ x, and under [Antisymmetric]
 [open_eq] makes a coalgebra a fixed point, Kx = x (the dual of
 Monad.v's [closed_eq]); [wlocal_iff_open] reads
 Construction/Reflective/FixedPoints.v's [WLocal_Subcategory] (extract
 invertible) as the open elements, and [proset_open_coreflective] is
 Structure/Thin/Monad.v's [thin_coreflective] at the proset: the open
 elements are coreflective, the dual of Seven Sketches Example 1.122.

 WHY THE REVERSED ORDER AND NOT (Proset P)^op.  The two categories have
 the same objects and homs by [eq_refl] (Instance/Proset/Order.v's
 [Proset_op_obj], [Proset_op_hom]), but the equation
 [(Proset P)^op = Proset (flip_PreOrder P)] is refused by conversion,
 already at the [id] field: stdlib's [flip_PreOrder] is opaque.  With
 Instance/Proset/Limit.v's transparent [op_PreOrder] in its place the
 [id] and [compose] fields agree by [eq_refl] and the equation is still
 refused, at the law fields, which Construction/Opposite.v takes from
 Proset P swapped and [Proset] takes from its own obligations.  So an
 endofunctor of (Proset P)^op is not one of the reversed order (the
 ascription is refused), and the strongest relation is Order.v's
 [Proset_op_iso]: [flip_functor W] agrees with
 [Proset_op_to P ◯ W^op ◯ Proset_op_from P] in [fobj] and [fmap] by
 [eq_refl] ([flip_functor_is_op_fobj], [flip_functor_is_op_fmap]), the
 refusal of [=] being in the law fields alone, and as functors at ≈
 ([flip_functor_is_op]).

 SEVEN SKETCHES SS 1.4.4: BOTH COMPOSITES OF ONE ADJUNCTION.  For
 [Adj : F ⊣ U] between prosets, [adj_closure Adj] is the closure
 operator of Monad/Adjunction.v's [Adjunction_Monad] (the composite U
 after F) and [adj_interior Adj] the interior operator of
 Comonad/Duality.v's [Adjunction_Comonad] (F after U); their maps are
 U (F x) and F (U y) by [eq_refl].  At Instance/Proset/Galois.v's
 truncated shift [nat_shift_adjunction k] (n - k ⊣ m + k on (ℕ, ≤))
 they are (m - k) + k and (m + k) - k by [eq_refl]; the closure is
 Monad.v's [max_closure k] ([shift_closure_is_max]) and the interior is
 the identity ([shift_interior_is_id]), so that witness is degenerate on
 the interior side.  [min_interior k] (n ↦ min n k) is not: its open
 elements are exactly the n ≤ k ([min_open_iff]), and 3 is not open for
 k = 2 ([min_three_not_open]).

 STRENGTHS, measured.
 - interior → comonad → interior: [eq_refl] on the WHOLE record
 ([interior_round_trip]), through primitive-projection eta.
 - comonad → interior → comonad: ≈ of functors with identity
 components ([comonad_round_trip], which IS Monotone.v's
 [Functor_of_monotone_of_Functor]); [fobj], [fmap], [extract] and
 [duplicate] by [eq_refl] ([comonad_round_trip_fobj],
 [comonad_round_trip_fmap], [comonad_round_trip_extract],
 [comonad_round_trip_duplicate]), so the counit and
 comultiplication come back on the nose; the refusal is in the law
 fields alone: [=] is refused by conversion.  Flipped first: with
 the functor's law fields written as transparent [I] and no [Qed],
 it is refused the same way, the law fields of a variable W being
 stuck projections.
 - [interior_is_flip_closure]: [eq_refl] on the whole record.  Since
 [comonad_flip_monad] is defined through [closure_monad], that
 equation is Monad.v's [closure_round_trip] at the interior
 operator; what makes it say something is
 [comonad_flip_monad_is_thin]: the same monad is, on the whole
 record and by [eq_refl], Structure/Thin/Monad.v's [thin_monad]
 built from extract and duplicate alone.
 - [interior_comonad] against [thin_comonad]: counit and
 comultiplication by [eq_refl]; the whole comonad is refused by
 conversion.  Flipped: with Structure/Thin.v's [Thin_Opposite] (a
 [Qed] lemma) restated with a transparent body, and nothing else
 changed, the whole equation is [eq_refl].  The refusal is that
 opacity alone.
 - [flip_functor W] against the opposite read through
 [Proset_op_iso]: [fobj] and [fmap] by [eq_refl]
 ([flip_functor_is_op_fobj], [flip_functor_is_op_fmap]), functors
 at ≈, [=] refused, the refusal in the law fields alone.
 Flipped: in a 30-file copy of its dependency closure with every
 Program obligation transparent ([Set Transparent Obligations] in
 Lib.v, [Compose]'s and [Functor_of_monotone]'s obligations
 [Defined]), it is still refused; the residue is W's
 [fmap_respects] inside stdlib's opaque
 [CMorphisms.trans_co_eq_inv_arrow_morphism_obligation_1].
 - [(Proset P)^op = Proset (op_PreOrder P)], with
 Instance/Proset/Limit.v's transparent [op_PreOrder]: refused
 structurally at [compose_respects], even in that fully transparent
 copy, where the other fields agree by [eq_refl];
 Construction/Opposite.v swaps the two hypotheses of
 [compose_respects].
 - The coalgebra structure map round-trips by [eq_refl]
 ([wcoalgebra_round]); the [to] leg of [int_idem] is [int_defl] by
 [eq_refl] ([int_idem_to]); [flip_mono] and [unflip_mono] are
 mutually inverse by [eq_refl].
 - Under antisymmetry, ≅ becomes Leibniz [=] on elements: [open_eq]
 (a coalgebra is a fixed point, the dual of Monad.v's [closed_eq])
 and [int_idem_eq].

 UNIVERSES, read off [About] with all instances printed.  No constant
 has a level that occurs in its body only.  Every constant polymorphic
 in the carrier level u that mentions the reversed order carries
 [Set < flip.u2, u <= flip.u0, u <= flip.u1] ([min_mono], whose
 carrier is [nat], carries only [Set < flip.u2]): stdlib's
 [Basics.flip] is not universe polymorphic, so
 these are its global universes, first carried here by
 [InteriorOperator] through [flip_PreOrder].  The caps
 [u <= Defs.u0, u <= Relation_Definition.u0] are stdlib's [PreOrder]
 and [relation], as in Monad.v; [int_idem_eq] and [open_eq] add
 [u <= equality.u0], first carried by Instance/Poset.v's [eq_equiv],
 as Monad.v's [closed_eq] does.  The strict bounds: [h < n] in
 [comonad_round_trip] and [flip_functor_is_op] is first carried by
 Theory/Functor.v's [Functor_Setoid] (its own [u4 < u2]), and in
 [flip_functor_is_op_fobj] and [flip_functor_is_op_fmap] by the same
 file's [Compose] ([u3 < u2]);
 [h < s] in the adjunction constants and the shift witnesses is the
 block of Theory/Adjunction.v's [Adjunction] record itself
 ([h1 < so], the level of the [Sets] hom-set isomorphism), and in
 [proset_open_coreflective] it is inherited from [thin_coreflective].
 [Adjunction_Comonad] has a level, its u4, sixth in its binder, that
 occurs in neither its type nor its block (measured); [adj_interior]
 pins it to h.  The biconditionals
 [@{u h +}] add the free level of [iffT] on their [Prop] side;
 [wcoalgebra_iff_open] names it (p) so that the level of the inner
 [talgebra_iff_closed] is the same one and not a level of the body
 alone.  [wcoalgebra_iff_open_via_thin] is a [Qed] lemma: transparent,
 it would carry [Thin]'s sort level in its body only.  In this file
 [flip] alone would be Lib's [CRelationClasses.flip]; every reversed
 relation is written [Basics.flip], the relation of [flip_PreOrder].
 This file loads both declarations of [Thin] and of [proset_thin]
 (Structure/Thin.v with Instance/Proset/Order.v, and
 Instance/Proset/Galois.v, imported for [nat_shift_adjunction];
 measured by [Locate]) and writes neither name: every thin witness is
 the term [fun _ _ _ _ => I].

 NOT DELIVERED.  No interior operator over [Props] or over spaces here
 (Instance/Props/Modal.v and Instance/Top/Interior.v); no category of
 interior operators and no functoriality in P; no statement that an
 interior operator is determined by its open elements.  The interior
 side of [nat_shift_adjunction] is the identity and is recorded as a
 degenerate witness, not as evidence. 

 --------
 nLab: https://ncatlab.org/nlab/show/interior+operator
 nLab: https://ncatlab.org/nlab/show/comonad
 书籍: Riehl, 《情境中的范畴论》, 第2版, 第5.1节, 示例5.1.7, 印刷第186页, 以及第5.2节, 示例5.2.6 (从第189页开始), 条款(iv)及脚注10–11, 印刷第190页
 书籍: Fong 和 Spivak, 《组合性中的七个草图》, arXiv v3, 第1.4.4节, 脚注8, 印刷第33页
 书籍: Mac Lane, 《为工作数学家而设的范畴论》, 第2版, Springer GTM 5, 1998, 第VI.1节, 印刷第139页, 以及第VI.2节, 印刷第141页书中所说。Mac Lane 在第 139 页中定义了一个在范畴 (display (1^op)) 上的余单子以及一个伴随对的余单子 ⟨FG, ε, FηG⟩，然后提出 “在一个偏序 P 中单子是什么？”；他在那里的偏序评论以及第 141 页（代数）中的内容仅关于单子。Riehl 的例 5.1.7（第 186 页）为偏序集添加了对偶：“对偶地，一个偏序范畴 (P, ≤) 上的余单子定义了一个核算子：一个保持顺序的函数 K，使得 Kp ≤ p 并且 Kp = K²p”，并将空间子集的内部命名为实例。例 5.2.6（第 189 页开始），第 (iv) 条款及脚注 10–11（印刷在第 190 页）指出 “内部核算子的余代数正好是开子集”，其脚注 11 将余代数视为范畴 C^op 上单子 (T, η, µ) 的代数。Seven Sketches 的脚注 8（第33) 说，对于一个 Galois 对偶 f ⊣ g，另一个复合 g ⨟ f（即 g 之后 f）“满足对偶性质：(g ⨟ f)(q) ≤ q 且 (g ⨟ f ⨟ g ⨟ f)(q) ≅ (g ⨟ f)(q) ... 这被称为内算子，尽管我们不会进一步讨论这个概念”。哪种读法被实现了。在 P 上的内部算子是逆序上的闭包算子：[InteriorOperator P] 是 Instance/Proset/Monad.v 中的 [ClosureOperator]，在 stdlib 的 [flip_PreOrder P] 中，并且没有引入新的记录。回读到 P 中，它的字段是压缩 [int_defl] 和余乘不等式 [int_comult]，通过转换；单调性 [int_mono] 是字段 [mono_pres]，其两个点交换了位置。『七个草图』的 ≅ 是 [int_idem]，逆序的 [cl_idem] 回读后的结果，而 Riehl 的“ Kp = K²p ”是在一个显式 [Antisymmetric] 假设下的 [int_idem_eq]，因为树的 [Poset] 是 [Proset] 丢弃反对称性后的结果。Riehl 为偏序集陈述了一个方向（“定义”）；这里在预序上证明了两个方向。通过对偶，没有再次证明的定律。双对偶在三个地方得到，并且每个都被测量。- 概念：倒序，如上所述。- 共范畴：Theory/Monad.v 将 [Comonad] 定义为 C^op 上的一个单子，因此 [interior_comonad] 是 (Proset P)^op 上的一个单子，其单位和乘法族是两个域，其五条定律是 [I]。它是 Structure/Thin/Monad.v 中的 [thin_comonad] 的写出：余单位和余乘法通过 [eq_refl]（[interior_comonad_extract], [interior_comonad_duplicate]）一致。它不是通过 [thin_comonad] 定义的：该路径被直接拒绝，Structure/Thin.v 的 [Thin] 的排序级别只保留在本体中；固定到 u 或 h 上，它会添加 h <= u 或 u <= h（被测量）；加上 + 时，薄层级只保留在块中（Instance/Proset/Monad.v 对 [closure_monad] 的理由相同）。按 Riehl 的路线对应：P 上的余单子 W 在逆序上是一个单子。[comonad_flip_monad W] 是 Instance/Proset/Monad.v 中 [closure_monad] 在 W 的内部算子上的实例，其单位是 extract，乘法是 duplicate（[comonad_flip_ret]，[comonad_flip_join]），而 [interior_is_flip_closure] 表示 W 的内部算子就是该单子的闭包算子。煤代数遵循同样的方式：[wcoalgebra_iff_flip_talgebra] 将 W-煤代数与逆序幺半群的代数对应（在序层的脚注11），然后 [wcoalgebra_iff_open] 是在逆序下的 Monad.v 的 [talgebra_iff_closed]。第二条途径是 [wcoalgebra_iff_open_via_thin]，Structure/Thin/Monad.v 的 [thin_wcoalgebra_iff]，它是在 C^op 上的幺半群陈述。[open_iff_fixed] 是 “x ≤ Kx ≤ x”，因为 Kx ≅ x，在 [Antisymmetric] 下，[open_eq] 使煤代数成为不动点，Kx = x（Monad.v 的 [closed_eq] 的对偶）；[wlocal_iff_open] 读取 Construction/Reflective/FixedPoints.v 的 [WLocal_Subcategory]（提取可逆部分）作为开元，而 [proset_open_coreflective] 是 Structure/Thin/Monad.v 的 [thin_coreflective] 在预序集上：开元是余反射的，是 Seven Sketches 示例 1.122 的对偶。为什么是反向顺序而不是 (Proset P)^op。根据 [eq_refl] (Instance/Proset/Order.v 的 [Proset_op_obj], [Proset_op_hom])，这两个范畴有相同的对象和 Hom，但方程 [(Proset P)^op = Proset (flip_PreOrder P)] 被转换拒绝，在 [id] 字段就已经如此：stdlib 的 [flip_PreOrder] 是不透明的。用 Instance/Proset/Limit.v 的透明 [op_PreOrder] 代替时，ZW50WZZ 和 ZW51WZZ 字段根据 [eq_refl] 一致，但在法律字段仍然被拒绝，Construction/Opposite.v 从交换的 Proset P 中获取，而 [Proset] 从其自身义务中获取。所以 (Proset P)^op 的一个端函子不是一个反向顺序的端函子（归属被拒绝），而最强的关系是 Order.v 的 [Proset_op_iso]：[flip_functor W] 在 [fobj] 和 [fmap] 中与 [Proset_op_to P ◯ W^op ◯ Proset_op_from P] 一致，通过 [eq_refl]（[flip_functor_is_op_fobj]，[flip_functor_is_op_fmap]），[=] 的拒绝仅存在于法律领域，并且作为函子在 ≈ ([flip_functor_is_op])。七个草图 SS 1.4.4：一个伴随的两个复合。对于 prosets 之间的 [Adj : F ⊣ U]，[adj_closure Adj] 是 Monad/Adjunction.v 的 [Adjunction_Monad]（F 之后的复合 U）的闭包算子，[adj_interior Adj] 是 Comonad/Duality.v 的 [Adjunction_Comonad]（U 之后的 F）的内部算子；它们的映射由 [eq_refl] 给出，分别是 U(F x) 和 F(U y)。在 Instance/Proset/Galois.v 的截断移位 [nat_shift_adjunction k]（(ℕ, ≤) 上的 n - k ⊣ m + k）上，它们分别是 (m - k) + k 和 (m + k) - k，由 [eq_refl] 给出；闭包是 Monad.v 的 [max_closure k]（[shift_closure_is_max]），内部是恒等（[shift_interior_is_id]），因此在内部方面该见证是退化的。[min_interior k]（n ↦ min n k）则不是：其开元素正好是 n ≤ k（[min_open_iff]），对于 k = 2，3 不是开元素（[min_three_not_open]）。优势，已测量。- 内部 → 上下文余子 → 内部：[eq_refl] 在整个记录上（[interior_round_trip]），通过原始投影 eta。- 上下文余子 → 内部 → 上下文余子：≈ 具有恒等分量的函子（[comonad_round_trip]，它是 Monotone.v 的 [Functor_of_monotone_of_Functor]）；[fobj]、[fmap]、[extract] 和 [duplicate] 由 [eq_refl]（[comonad_round_trip_fobj]、[comonad_round_trip_fmap]、[comonad_round_trip_extract]、[comonad_round_trip_duplicate]），因此伴随单位和余乘回到原点；拒绝仅在法则字段中：[=] 被转换拒绝。首先翻转：当函子的法则字段写为透明的 [I] 且无 [Qed] 时，也以相同方式拒绝，变量 W 的法则字段为固定投影。- [interior_is_flip_closure]：[eq_refl] 在整个记录上。由于 [comonad_flip_monad] 是通过 [closure_monad] 定义的，所以该方程是在 Monad.v 中的 [closure_round_trip] 在内部算子处；使它表达某事的是 [comonad_flip_monad_is_thin] ：相同的 monad 在整个记录上，并且通过 [eq_refl] ，由 extract 和 duplicate 单独构建的 Structure/Thin/Monad.v 中的 [thin_monad] 。- [interior_comonad] 针对 [thin_comonad] ：由 [eq_refl] 定义的 counit 和 comultiplication；整个 comonad 被转换拒绝。翻转：使用 Structure/Thin.v 的 [Thin_Opposite] （一个 [Qed] 引理）以透明体重述，并且没有其他改变，整个方程为 [eq_refl] 。拒绝是仅由不透明性引起的。- [flip_functor W] 对相对类型的通读  
 [Proset_op_iso]：[fobj] 和 [fmap] 由 [eq_refl]  
 （[flip_functor_is_op_fobj]，[flip_functor_is_op_fmap]），函子  
 在 ≈，[=] 被拒绝，该拒绝仅在法字段中。翻转：在其依赖闭包的 30 个文件副本中，每个程序义务都是透明的（[Set Transparent Obligations] 在 Lib.v 中，[Compose] 和 [Functor_of_monotone] 的义务 [Defined]），仍然被拒绝；残余是 W 的 [fmap_respects] 在 stdlib 的不透明 [CMorphisms.trans_co_eq_inv_arrow_morphism_obligation_1] 内。  
 - [(Proset P)^op = Proset (op_PreOrder P)]，配合 Instance/Proset/Limit.v 的透明 [op_PreOrder]：在 [compose_respects] 结构上被拒绝，即使在那个完全透明的副本中，其他字段通过 [eq_refl] 同意；Construction/Opposite.v 交换了 [compose_respects] 的两个假设。- 通过 [eq_refl] ([wcoalgebra_round]) 煤代数结构映射可以来回转换；[int_idem] 的 [to] 分支通过 [eq_refl] ([int_idem_to]) 为 [int_defl]；[flip_mono] 和 [unflip_mono] 通过 [eq_refl] 互为逆。- 在反对称性下，≅ 在元素上变为 Leibniz [=]：[open_eq]（一种煤代数是一个固定点，是 Monad.v 的 [closed_eq] 的对偶）和 [int_idem_eq]。宇宙（UNIVERSES），以 [About] 的所有实例读取。没有常量的等级只在其主体中出现一次。每个在承载等级 u 中多态的常量，如果提到反向顺序，则携带 [Set < flip.u2, u <= flip.u0, u <= flip.u1]（[min_mono]，其承载者是 [nat]，仅携带 [Set < flip.u2]）：stdlib 的 [Basics.flip] 不是宇宙多态的，因此这些是它的全局宇宙，最先由 [InteriorOperator] 通过 [flip_PreOrder] 携带。大写的 [u <= Defs.u0, u <= Relation_Definition.u0] 是 stdlib 的 [PreOrder] 和 [relation]，如 Monad.v 中所示；[int_idem_eq] 和 [open_eq] 添加了 [u <= equality.u0]，最先由 Instance/Poset.v 的 [eq_equiv] 携带，正如 Monad.v 的 [closed_eq] 所做的那样。严格的界限：[h < n] 在 [comonad_round_trip] 和 [flip_functor_is_op] 中首先由 Theory/Functor.v 的 [Functor_Setoid] （它自己的 [u4 < u2]）承载，在 [flip_functor_is_op_fobj] 和 [flip_functor_is_op_fmap] 中由同一文件的 [Compose] （[u3 < u2]）承载；[h < s] 在伴随常数和移位见证中是 Theory/Adjunction.v 的 [Adjunction] 记录自身（[h1 < so]，[Sets] 同态集同构的层级）的一个块，在 [proset_open_coreflective] 中它继承自 [thin_coreflective]。[Adjunction_Comonad] 有一个层级，它的 u4，是绑定器中的第六个，在其类型或块（已测量）中都未出现；[adj_interior] 将它固定为 h。双条件
 [@{u h +}] 在它们的 [Prop] 侧添加了 [iffT] 的自由级别；
 [wcoalgebra_iff_open] 将其命名为 (p)，这样内部
 [talgebra_iff_closed] 的级别与之相同，而不是仅仅是主体的级别。 [wcoalgebra_iff_open_via_thin] 是一个 [Qed] 引理：透明的，
 它只会在其主体中携带 [Thin] 的类型级别。在此文件中
 只有 [flip] 是 Lib 的 [CRelationClasses.flip]；每个反转关系都写作 [Basics.flip]，即 [flip_PreOrder] 的关系。该文件加载了 [Thin] 和 [proset_thin] 的两个声明
 （Structure/Thin.v 与 Instance/Proset/Order.v，以及
 Instance/Proset/Galois.v，为 [nat_shift_adjunction] 导入；
 由 [Locate] 测量）并且不写名称：每个纤细证据都是项 [fun _ _ _ _ => I]。未传送。在 [Props] 上或此处空间上没有内部运算符（实例/属性/模态.v 和 实例/顶/内部.v）；没有内部运算符的类别，也没有 P 的函子性；没有说明内部运算符由其开元素决定。[nat_shift_adjunction] 的内部部分是恒等映射，并被记录为退化证据，而不是作为证据。
*)

(* * ** Interior operators: closure operators on the reversed order / * ** 内部算子：在逆序上的闭包算子 *)

Definition InteriorOperator@{u} {A : Type@{u}} {R : relation A}
  (P : PreOrder R) : Type@{u} :=
  ClosureOperator@{u} (flip_PreOrder P).

(* Monotone maps for an order are monotone maps for its reverse. / 一个序的单调映射对于其逆序也是单调映射。 *)
Definition flip_mono@{u v} {A : Type@{u}} {B : Type@{v}} {R : relation A}
  {S : relation B} (f : @MonotoneFun@{u v} A R B S) :
  @MonotoneFun@{u v} A (Basics.flip R) B (Basics.flip S) :=
  {| mono_map := f; mono_pres := fun x y h => mono_pres f y x h |}.

Definition unflip_mono@{u v} {A : Type@{u}} {B : Type@{v}} {R : relation A}
  {S : relation B}
  (f : @MonotoneFun@{u v} A (Basics.flip R) B (Basics.flip S)) :
  @MonotoneFun@{u v} A R B S :=
  {| mono_map := f; mono_pres := fun x y h => mono_pres f y x h |}.

Example flip_unflip_mono@{u v} {A : Type@{u}} {B : Type@{v}}
  {R : relation A} {S : relation B}
  (f : @MonotoneFun@{u v} A (Basics.flip R) B (Basics.flip S)) :
  flip_mono (unflip_mono f) = f := eq_refl.

Example unflip_flip_mono@{u v} {A : Type@{u}} {B : Type@{v}}
  {R : relation A} {S : relation B} (f : @MonotoneFun@{u v} A R B S) :
  unflip_mono (flip_mono f) = f := eq_refl.

(* The fields of the reversed-order record, read in the original order. Each is the field itself, by conversion. / 按原始顺序读取的逆序记录的字段。每一个都是字段本身，通过转换。 *)
Definition int_defl@{u} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (j : InteriorOperator@{u} P) (x : A) : R (cl_fun j x) x :=
  cl_ext j x.

Definition int_comult@{u} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (j : InteriorOperator@{u} P) (x : A) :
  R (cl_fun j x) (cl_fun j (cl_fun j x)) :=
  cl_mult j x.

Definition int_mono@{u} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (j : InteriorOperator@{u} P) (x y : A) (h : R x y) :
  R (cl_fun j x) (cl_fun j y) :=
  mono_pres (cl_fun j) y x h.

(*
 Riehl's "K p = K² p", up to ≅ over a preorder: the isomorphism
 [cl_idem] of the reversed order, read backwards. 

 --------
 Riehl 的 “K p = K² p”，在前序下约等于 ≅ ：逆序的同构 [cl_idem]，倒过来读。
*)
Definition int_idem@{u h} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (j : InteriorOperator@{u} P) (x : A) :
  cl_fun j (cl_fun j x) ≅[Proset@{u h} P] cl_fun j x :=
  @Build_Isomorphism (Proset@{u h} P) _ _
    (from (cl_idem@{u h} j x)) (to (cl_idem@{u h} j x)) I I.

Example int_idem_to@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (j : InteriorOperator@{u} P) (x : A) :
  to (int_idem@{u h} j x) = int_defl j (cl_fun j x) := eq_refl.

(* Under antisymmetry, Riehl's equation itself. / 在反对称性下，Riehl 的方程本身。 *)
Lemma int_idem_eq@{u} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (AS : @Antisymmetric A eq eq_equiv R) (j : InteriorOperator@{u} P)
  (x : A) : cl_fun j (cl_fun j x) = cl_fun j x.
Proof. exact (AS _ _ (int_defl j (cl_fun j x)) (int_comult j x)). Qed.

(** ** The correspondence / ** 通讯 *)

Definition interior_functor@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (j : InteriorOperator@{u} P) :
  Proset@{u h} P ⟶ Proset@{u h} P :=
  Functor_of_monotone P P (unflip_mono (cl_fun j)).

(*
 Interior → comonad: at (Proset P)^op the counit and comultiplication
 families ARE the two fields, by conversion; every law is [I]. 

 --------
 内部 → comonad：在 (Proset P)^op 上，余单位和余乘法族通过转换就是这两个域；每个定律是 [I]。
*)
Definition interior_comonad@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (j : InteriorOperator@{u} P) :
  @Comonad (Proset@{u h} P) (interior_functor j) :=
  @Build_Monad ((Proset@{u h} P)^op) ((interior_functor j)^op)
    (fun x => cl_ext j x) (fun x => cl_mult j x)
    (fun _ _ _ => I) (fun _ => I) (fun _ => I) (fun _ => I)
    (fun _ _ _ => I).

(* The same data as Structure/Thin/Monad.v's [thin_comonad]. / 与 Structure/Thin/Monad.v 的 [thin_comonad] 相同的数据。 *)
Example interior_comonad_extract@{u h t} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (j : InteriorOperator@{u} P) (x : A) :
  @extract _ _ (interior_comonad@{u h} j) x
    = @extract _ _ (@thin_comonad@{t u h} (Proset@{u h} P) (fun _ _ _ _ => I)
                      (interior_functor@{u h} j) (cl_ext j) (cl_mult j)) x
  := eq_refl.

Example interior_comonad_duplicate@{u h t} {A : Type@{u}}
  {R : relation A} {P : PreOrder R} (j : InteriorOperator@{u} P) (x : A) :
  @duplicate _ _ (interior_comonad@{u h} j) x
    = @duplicate _ _ (@thin_comonad@{t u h} (Proset@{u h} P) (fun _ _ _ _ => I)
                        (interior_functor@{u h} j) (cl_ext j) (cl_mult j)) x
  := eq_refl.

(* Comonad → interior: the counit and comultiplication are the fields. / 余单子 → 内部：余单元和余乘法是字段。 *)
Definition interior_of_comonad@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} : InteriorOperator@{u} P :=
  {| cl_fun  := flip_mono (monotone_of_Functor P P W)
   ; cl_ext  := fun x => @extract _ W H x
   ; cl_mult := fun x => @duplicate _ W H x |}.

Definition comonad_interior_iff@{u h +} {A : Type@{u}} {R : relation A}
  (P : PreOrder R) :
  { W : Proset@{u h} P ⟶ Proset@{u h} P & @Comonad (Proset@{u h} P) W }
    ↔ InteriorOperator@{u} P :=
  (fun p => match p with existT _ W H => interior_of_comonad W (H := H) end,
   fun j => existT (fun W : Proset@{u h} P ⟶ Proset@{u h} P =>
                      @Comonad (Proset@{u h} P) W)
              (interior_functor j) (interior_comonad j)).

(* interior → comonad → interior is the identity on the WHOLE record. / 内核 → 共幺半群 → 内核在整个记录上是恒等的。 *)
Example interior_round_trip@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (j : InteriorOperator@{u} P) :
  interior_of_comonad@{u h} (interior_functor@{u h} j)
    (H := interior_comonad j) = j := eq_refl.

(* comonad → interior → comonad: ≈ of functors, identity components. / 余单 → 内部 → 余单：函子、大约、恒等分量。 *)
Definition comonad_round_trip@{u h m n | h < n, u <= m, h <= m +}
  {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} :
  interior_functor (interior_of_comonad W (H := H)) ≈ W :=
  Functor_of_monotone_of_Functor P P W.

Example comonad_round_trip_fobj@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) :
  fobj[interior_functor (interior_of_comonad W (H := H))] x = fobj[W] x
  := eq_refl.

Example comonad_round_trip_fmap@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x y : A) (f : R x y) :
  fmap[interior_functor (interior_of_comonad W (H := H))] f = fmap[W] f
  := eq_refl.

(* ...and the comonad it rebuilds has W's counit and comultiplication. / ...并且它重建的余单子具有 W 的余单位和余乘法。 *)
Example comonad_round_trip_extract@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) :
  @extract _ _ (interior_comonad (interior_of_comonad W (H := H))) x
    = @extract _ W H x := eq_refl.

Example comonad_round_trip_duplicate@{u h} {A : Type@{u}}
  {R : relation A} {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) :
  @duplicate _ _ (interior_comonad (interior_of_comonad W (H := H))) x
    = @duplicate _ W H x := eq_refl.

(* * ** Riehl's route: a comonad on P is a monad on the reversed order / * ** Riehl 的路线：P 上的余幺半范畴是逆序上的幺半范畴 *)

Definition flip_functor@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P) :
  Proset@{u h} (flip_PreOrder P) ⟶ Proset@{u h} (flip_PreOrder P) :=
  Functor_of_monotone (flip_PreOrder P) (flip_PreOrder P)
    (flip_mono (monotone_of_Functor P P W)).

(*
 The monad on the reversed order is Instance/Proset/Monad.v's
 [closure_monad] at the interior operator: its unit is extract and its
 multiplication duplicate. 

 --------
 在逆序上的单子是 Instance/Proset/Monad.v 中的 [closure_monad] 在内部算子处：它的单位是 extract，它的乘法是 duplicate。
*)
Definition comonad_flip_monad@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} :
  @Monad (Proset@{u h} (flip_PreOrder P)) (flip_functor W) :=
  closure_monad@{u h} (interior_of_comonad W (H := H)).

Example comonad_flip_ret@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) :
  @ret _ _ (comonad_flip_monad W (H := H)) x = @extract _ W H x
  := eq_refl.

Example comonad_flip_join@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) :
  @join _ _ (comonad_flip_monad W (H := H)) x = @duplicate _ W H x
  := eq_refl.

(* It is also Structure/Thin/Monad.v's [thin_monad] on the reversed order, on the WHOLE record. / 它也是 Structure/Thin/Monad.v 的 [thin_monad]，在反向顺序上，对整个记录。 *)
Example comonad_flip_monad_is_thin@{u h t} {A : Type@{u}}
  {R : relation A} {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} :
  comonad_flip_monad W (H := H)
    = @thin_monad@{t u h} (Proset@{u h} (flip_PreOrder P))
        (fun _ _ _ _ => I) (flip_functor W)
        (fun x => @extract _ W H x) (fun x => @duplicate _ W H x)
  := eq_refl.

(* The interior operator of W IS the closure operator of that monad. / W 的内部算子是该幺半群的闭包算子。 *)
Example interior_is_flip_closure@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} :
  interior_of_comonad W (H := H)
    = closure_of_monad (flip_functor W) (MM := comonad_flip_monad W)
  := eq_refl.

(* The same functor as W^op read through Order.v's [Proset_op_iso]. / 与 W^op 相同的函子，通过 Order.v 的 [Proset_op_iso] 阅读。 *)
Example flip_functor_is_op_fobj@{u h n | h < n +} {A : Type@{u}}
  {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P) (x : A) :
  fobj[flip_functor W] x
    = fobj[Proset_op_to P ◯ W^op ◯ Proset_op_from P] x := eq_refl.

Example flip_functor_is_op_fmap@{u h n | h < n +} {A : Type@{u}}
  {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P) (x y : A)
  (f : Basics.flip R x y) :
  fmap[flip_functor W] f
    = fmap[Proset_op_to P ◯ W^op ◯ Proset_op_from P] f := eq_refl.

Lemma flip_functor_is_op@{u h m n | h < n, u <= m, h <= m +}
  {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P) :
  flip_functor W ≈ Proset_op_to P ◯ W^op ◯ Proset_op_from P.
Proof. exists (fun x => iso_id). intros; exact I. Qed.

(* * ** Coalgebras are the open elements / * ** 煤代数是开放元素 *)

(*
 A coalgebra of W is an algebra of the reversed-order monad: the two
 records carry the same structure map, and every law is [I]. 

 --------
 W 的余代数是逆序幺半群的代数：两个记录具有相同的结构映射，并且每条定律都是 [I] 。
*)
Definition wcoalgebra_iff_flip_talgebra@{u h} {A : Type@{u}}
  {R : relation A} {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) :
  @WCoalgebra (Proset@{u h} P) W H x
    ↔ @TAlgebra (Proset@{u h} (flip_PreOrder P)) (flip_functor W)
        (comonad_flip_monad W (H := H)) x :=
  (fun c => @Build_TAlgebra (Proset@{u h} (flip_PreOrder P))
              (flip_functor W) (comonad_flip_monad W (H := H)) x
              (@w_coalg _ W H x c) I I,
   fun a => @Build_WCoalgebra (Proset@{u h} P) W H x
              (@t_alg _ _ (comonad_flip_monad W (H := H)) x a) I I).

(* So the coalgebra characterisation is Instance/Proset/Monad.v's [talgebra_iff_closed] at the reversed order. / 因此，余代数的表征是在 Instance/Proset/Monad.v 中的 [talgebra_iff_closed]，按相反的顺序。 *)
Definition wcoalgebra_iff_open@{u h p} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) :
  iffT@{h p} (@WCoalgebra (Proset@{u h} P) W H x) (R x (W x)) :=
  let (to_flip, of_flip) := wcoalgebra_iff_flip_talgebra@{u h} W (H := H) x in
  let (to_closed, of_closed) :=
    talgebra_iff_closed@{u h p} (flip_functor W)
      (MM := comonad_flip_monad W (H := H)) x in
  (fun c => to_closed (to_flip c), fun h => of_flip (of_closed h)).

Example wcoalgebra_round@{u h p} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) (h : R x (W x)) :
  match wcoalgebra_iff_open@{u h p} W (H := H) x with
  | (to_open, of_open) => to_open (of_open h)
  end = h := eq_refl.

(*
 The second route: Structure/Thin/Monad.v's [thin_wcoalgebra_iff],
 which is the monad statement at (Proset P)^op.  [Qed]: transparent,
 it carries the sort level of [Thin] in its body only. 

 --------
 第二条路线：Structure/Thin/Monad.v 的 [thin_wcoalgebra_iff]，
 这是 (Proset P)^op 上的 monad 语句。[Qed]：透明的，
 它只在其主体中携带 [Thin] 的排序级别。
*)
Lemma wcoalgebra_iff_open_via_thin@{u h +} {A : Type@{u}}
  {R : relation A} {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) :
  @WCoalgebra (Proset@{u h} P) W H x ↔ R x (W x).
Proof. exact (@thin_wcoalgebra_iff (Proset@{u h} P) (fun _ _ _ _ => I) W H x).
Qed.

(* "x ≤ Kx ≤ x": open means Kx ≅ x. / "x ≤ Kx ≤ x": 开放意味着 Kx ≅ x。 *)
Definition open_iff_fixed@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) :
  R x (W x) ↔ (W x ≅[Proset@{u h} P] x) :=
  (fun h => @Build_Isomorphism (Proset@{u h} P) _ _
              (@extract _ W H x) h I I,
   fun i => from i).

(*
 Under antisymmetry a coalgebra is a fixed point: the dual of
 Instance/Proset/Monad.v's [closed_eq]. 

 --------
 在反对称性下，余代数是一个不动点：Instance/Proset/Monad.v 的 [closed_eq] 的对偶。
*)
Lemma open_eq@{u h} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (AS : @Antisymmetric A eq eq_equiv R)
  (W : Proset@{u h} P ⟶ Proset@{u h} P) {H : @Comonad (Proset@{u h} P) W}
  (x : A) : @WCoalgebra (Proset@{u h} P) W H x → W x = x.
Proof. intro c. exact (AS _ _ (@extract _ W H x) (@w_coalg _ W H x c)). Qed.

(*
 FixedPoints.v's W-local objects (extract invertible) are the open
 ones. 

 --------
 FixedPoints.v 的 W-局部对象（提取可逆的）是开放的那些。
*)
Definition wlocal_iff_open@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) :
  sobj (Proset@{u h} P) (WLocal_Subcategory H) x ↔ R x (W x) :=
  (fun Hi => @two_sided_inverse _ _ _ _ Hi,
   fun h => @Build_IsIsomorphism ((Proset@{u h} P)^op) x (W x)
              (@extract _ W H x) h I I).

(* The coreflection onto the open elements: Structure/Thin/Monad.v's [thin_coreflective] at the proset. / 在前序集上对开放元素的核心反射：Structure/Thin/Monad.v 的 [thin_coreflective]。 *)
Definition proset_open_coreflective@{u h t s f | h < s, u <= t, h <= t +}
  {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} :=
  @thin_coreflective@{t u h s f} (Proset@{u h} P) (fun _ _ _ _ => I) W H.

(* * ** Seven Sketches SS 1.4.4: both composites of ONE adjunction / * ** 七个素描 SS 1.4.4：一个伴随的两个复合 *)

Definition adj_closure@{a b h s w | h < s +} {A : Type@{a}} {B : Type@{b}}
  {RA : relation A} {RB : relation B} {PA : PreOrder RA}
  {PB : PreOrder RB} {F : Proset@{a h} PA ⟶ Proset@{b h} PB}
  {U : Proset@{b h} PB ⟶ Proset@{a h} PA}
  (Adj : @Adjunction@{b h h a h h h h s h w} _ _ F U) :
  ClosureOperator@{a} PA :=
  closure_of_monad (U ◯ F) (MM := Adjunction_Monad@{b h a h s w} Adj).

(*
 [Adjunction_Comonad]'s level u4 (sixth in its binder) occurs in
 neither its type nor its constraints; it is pinned to h. 

 --------
 [Adjunction_Comonad] 的 u4 级别（在其绑定器中第六）既不出现在其类型中，也不出现在其约束中；它被固定到 h。
*)
Definition adj_interior@{a b h s w | h < s +} {A : Type@{a}} {B : Type@{b}}
  {RA : relation A} {RB : relation B} {PA : PreOrder RA}
  {PB : PreOrder RB} {F : Proset@{a h} PA ⟶ Proset@{b h} PB}
  {U : Proset@{b h} PB ⟶ Proset@{a h} PA}
  (Adj : @Adjunction@{b h h a h h h h s h w} _ _ F U) :
  InteriorOperator@{b} PB :=
  interior_of_comonad (F ◯ U)
    (H := Adjunction_Comonad@{b h a h s h w} Adj).

Example adj_closure_fun@{a b h s w | h < s +} {A : Type@{a}}
  {B : Type@{b}} {RA : relation A} {RB : relation B} {PA : PreOrder RA}
  {PB : PreOrder RB} {F : Proset@{a h} PA ⟶ Proset@{b h} PB}
  {U : Proset@{b h} PB ⟶ Proset@{a h} PA}
  (Adj : @Adjunction@{b h h a h h h h s h w} _ _ F U) (x : A) :
  cl_fun (adj_closure Adj) x = U (F x) := eq_refl.

Example adj_interior_fun@{a b h s w | h < s +} {A : Type@{a}}
  {B : Type@{b}} {RA : relation A} {RB : relation B} {PA : PreOrder RA}
  {PB : PreOrder RB} {F : Proset@{a h} PA ⟶ Proset@{b h} PB}
  {U : Proset@{b h} PB ⟶ Proset@{a h} PA}
  (Adj : @Adjunction@{b h h a h h h h s h w} _ _ F U) (y : B) :
  cl_fun (adj_interior Adj) y = F (U y) := eq_refl.

(* At Galois.v's truncated shift (n - k ⊣ m + k) on (ℕ, ≤). / 在 Galois.v 的截断移位 (n - k ⊣ m + k) 上的 (ℕ, ≤)。 *)
Example shift_closure_fun@{n h s w | h < s +} (k m : nat) :
  cl_fun (adj_closure@{n n h s w} (nat_shift_adjunction@{n n s w h} k)) m
    = ((m - k) + k)%nat := eq_refl.

Example shift_interior_fun@{n h s w | h < s +} (k m : nat) :
  cl_fun (adj_interior@{n n h s w} (nat_shift_adjunction@{n n s w h} k)) m
    = ((m + k) - k)%nat := eq_refl.

(* The closure is Instance/Proset/Monad.v's [max_closure k]... / 该闭包是 Instance/Proset/Monad.v 的 [max_closure k] ... *)
Lemma shift_closure_is_max@{n h s w | h < s +} (k m : nat) :
  cl_fun (adj_closure@{n n h s w} (nat_shift_adjunction@{n n s w h} k)) m
    = cl_fun (max_closure@{n} k) m.
Proof. simpl. lia. Qed.

(* ...and the interior is the identity: a degenerate witness. / ...而内在则是身份：一个堕落的见证者。 *)
Lemma shift_interior_is_id@{n h s w | h < s +} (k m : nat) :
  cl_fun (adj_interior@{n n h s w} (nat_shift_adjunction@{n n s w h} k)) m
    = m.
Proof. simpl. lia. Qed.

(* * ** A non-degenerate interior operator: n ↦ min n k / * ** 非退化的内部算子: n ↦ min n k *)

Definition min_mono@{u} (k : nat) :
  @MonotoneFun@{u u} nat (Basics.flip Nat.le) nat (Basics.flip Nat.le) :=
  {| mono_map := fun n => Nat.min n k
   ; mono_pres := fun x y (H : (y <= x)%nat) =>
       Nat.min_le_compat_r y x k H |}.

Lemma min_comult@{} (k n : nat) :
  (Nat.min n k <= Nat.min (Nat.min n k) k)%nat.
Proof. lia. Qed.

Definition min_interior@{u} (k : nat) :
  InteriorOperator@{u} Nat.le_preorder :=
  {| cl_fun  := min_mono k
   ; cl_ext  := fun n => Nat.le_min_l n k
   ; cl_mult := fun n => min_comult k n |}.

(* Its coalgebras (open elements) are exactly the n below k. / 它的余代数（开元素）恰好是小于 k 的 n。 *)
Lemma min_open_iff@{u h +} (k n : nat) :
  @WCoalgebra (Proset@{u h} Nat.le_preorder)
    (interior_functor@{u h} (min_interior@{u} k))
    (interior_comonad@{u h} (min_interior@{u} k)) n ↔ (n <= k)%nat.
Proof.
  destruct (wcoalgebra_iff_open (interior_functor (min_interior k))
              (H := interior_comonad (min_interior k)) n)
    as [to_open of_open].
  split.
  - intro c. pose proof (to_open c) as H. simpl in H. lia.
  - intro H. apply of_open. simpl. lia.
Qed.

Lemma min_three_not_open@{u h} :
  @WCoalgebra (Proset@{u h} Nat.le_preorder)
    (interior_functor@{u h} (min_interior@{u} 2%nat))
    (interior_comonad@{u h} (min_interior@{u} 2%nat)) 3%nat → False.
Proof.
  intro c. destruct (min_open_iff 2%nat 3%nat) as [to_le _].
  pose proof (to_le c). lia.
Qed.
