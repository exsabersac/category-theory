Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Product.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.One.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Construction.Slice.
Require Import Category.Structure.Terminal.

Generalizable All Variables.

(*
   * * The comma of two constant functors is the discrete category on a hom-set 

   --------
   * * 两个常量函子的逗号是一个同态集上的离散范畴
*)

(*
 Reference: Saunders Mac Lane, "Categories for the Working Mathematician",
 2nd ed., §II.6, pp. 46-47 [maclane:II.6:remark1]: the general
 comma category subsumes all the earlier cases; in the catalog's
 paraphrase (doc/plan/books/maclane/inventory/II.json, not the
 book's wording), taking S and T to be objects a and b (functors
 from 1), (T ↓ S) is the discrete category on the hom-set
 C(b, a) — the source of the historical notation (T, S) and the
 name "comma category".
 nLab:      https://ncatlab.org/nlab/show/comma+category
 nLab:      https://ncatlab.org/nlab/show/discrete+category
 Wikipedia: https://en.wikipedia.org/wiki/Comma_category

 Lawvere's original notation for the comma category was the pair (T, S),
 generalizing the hom-set notation C(b, a) that this file's theorem recovers:
 when T and S are objects — that is, functors out of the terminal category 1
 — the comma category (T, S) IS the hom-set C(b, a), regarded as a category
 with no non-trivial arrows.  The comma of the notation is where the name of
 the construction comes from, a name that Wikipedia records displeased even
 its author.  Mac Lane's remark is thus simultaneously the degenerate case of
 the definition and its etymology, which is why this file exists as a
 separate statement rather than as a parenthesis somewhere.

 ** Mac Lane's list of specializations, and where each is recorded

 The remark enumerates the specializations of (T ↓ S).  Every one of them is
 a theorem or a definition somewhere in this library; the point of this recap
 is that the list is now closed, with this file supplying the last entry.

 T = b : 1 ⟶ C, S arbitrary   the category of objects S-under b
 — [maclane:II.6:def3], the comma (=(b) ↓ S)
 as it stands; used pervasively, e.g. as the
 domain of Freyd's construction in
 Adjunction/GAFT.v and as
 [ElementsComma := =(SetsOne) ↓ K] in
 Construction/Elements.v.

 T = b, S = Id[C]              the coslice b/C
 — [Comma_Coslice], Construction/Slice.v.

 T = Id[C], S = a              the slice C/a
 — [Comma_Slice], Construction/Slice.v;
 and for a terminal a the slice is C itself,
 [Slice_Terminal] in
 Construction/Slice/Terminal.v.

 T = S = Id[C]                 the arrow category C^2
 — [Arrow := (Id[C] ↓ Id[C])],
 Construction/Arrow.v.

 T = b, S = a  (both objects)  the discrete category on C(b, a)
 — THIS FILE, [Comma_Discrete_Hom].

 Two neighbouring readings are worth naming because they are easy to confuse
 with the last row.  First, the arrow category has a functor-category
 presentation, [Two_Fun_Arrow : [_2, C] ≅[Cat] Arrow C] in Theory/Shapes.v,
 over the walking arrow [_2]; that is the C^2 of Mac Lane's notation made
 literal, and it is related to but not consumed by anything here.  Second,
 Construction/Product/Comma.v proves [Comma_Product]: when the two functors
 have terminal CODOMAIN the comma is the product category C ∏ D.  That file's
 header already contrasts itself with the present case — "this is distinct
 from the special case in which the *domains* of the two functors are 1,
 where the comma category is instead the discrete category of morphisms
 between the two selected objects" — and states it in prose only.  This file
 is the promotion of those lines (Construction/Product/Comma.v) to a
 theorem.

 ** THE PACKAGING CHOICE: setoid-discrete, not [DiscreteCat]

 "The discrete category on the hom-set C(b, a)" has to be read carefully in a
 setoid-based library, and the reading is forced by what the comma category
 actually is.  Unfold (=(b) ↓ =(a)):

 - an object is a triple (u, v, h) with u, v the unique object of 1 and
 h : b ~> a, so objects ARE the hom-set, up to two units of padding;

 - a morphism (u, v, h) ~> (u', v', h') is a pair of morphisms of 1 — again
 units, carrying no information — subject to the commuting square
 h' ∘ fmap[=(b)] _ ≈ fmap[=(a)] _ ∘ h.  Both constant functors send every
 arrow to an identity, so the square says h' ∘ id ≈ id ∘ h, i.e. h ≈ h'.

 So a morphism of the comma category is a WITNESS OF `h ≈ h'` in the
 hom-setoid, and there is one exactly when h ≈ h'.  The matching "discrete
 category" is therefore the one whose objects are the carrier of a setoid and
 whose homs are that setoid's own equivalence — [DiscreteSetoidCat] below.

 Instance/Discrete.v's [DiscreteCat A] is a DIFFERENT category: its homs are
 proofs of Rocq's `=`.  An isomorphism with it is not merely unproven here,
 it is unavailable: it would require `h ≈ h' → h = h'`, which is exactly the
 collapse of the hom-setoid to strict equality that this library declines to
 assume.  Block C makes that precise rather than leaving it as a remark; see
 below.

 Nothing in the tree could be reused for [DiscreteSetoidCat], and the reason
 is a genuine typing obstruction, not an oversight.  Instance/Proset.v's
 [Proset] builds a thin category out of a [PreOrder], and an equivalence
 relation is a preorder, so `Proset` at the hom-setoid's equivalence looks
 like the construction wanted.  But [Proset] is stated over
 `Coq.Relations.Relation_Definitions.relation`, i.e. a `Prop`-valued
 relation, whereas this library's `≈` is a `crelation` — `Type`-valued, so
 that equivalence proofs may carry computational content (Lib/Setoid.v).  The
 gap is not cosmetic: a comma morphism carries its square proof as `sigT`
 data, so building one demands the `Type`-valued witness, and a `Prop`-valued
 (or `Prop`-squashed) preorder cannot be eliminated into it.  Hence the
 construction below, which is [Proset] transposed to `crelation`s.

 The closest thing already in the tree is [Blurry A] of
 Instance/Discrete/Reconstruct.v, which is precisely [DiscreteSetoidCat] at
 the `eq` setoid — objects `A`, homs `x = y`, all parallel arrows identified.
 It was introduced there as a countermodel; the present file gives the
 general construction of which it is an instance.  It is not imported from
 there, since that file pulls in Instance/StrictCat and Eqdep_dec for
 purposes unrelated to this one.

 ** What is delivered, and at what strength

 [Comma_Discrete_Hom : (=(b) ↓ =(a)) ≅[Cat] HomDiscrete b a].  Note `≅[Cat]`
 is EQUIVALENCE of categories in this library, Cat's hom-setoid being
 [Functor_Setoid] (Instance/Cat.v); no isomorphism of categories is claimed.
 Both round trips are nevertheless as tight as the encodings allow, and the
 two are not equally tight:

 - [Comma_Hom ◯ Hom_Comma] is the identity of [HomDiscrete b a] with a
 DEFINITIONALLY identical object map (h ↦ ((ttt, ttt); h) ↦ h), so its
 natural isomorphism has [iso_id] components and its coherence clause is
 trivially true, the target being thin.

 - [Hom_Comma ◯ Comma_Hom] sends (u, v, h) to ((ttt, ttt); h), replacing the
 two unit paddings by the canonical ones.  Its components are the canonical
 comma isomorphisms [comma_const_iso], whose data is again units.  The
 object map is not the identity as a Rocq term — `u` is a variable, not
 `ttt` — although it becomes so after case analysis; no strict statement is
 claimed and none is needed.

 ** Block C: the plain [DiscreteCat] reading, and its exact price

 The functor [Comma_Discrete_eq : DiscreteCat (b ~> a) ⟶ (=(b) ↓ =(a))]
 exists with no hypothesis at all: `=` implies `≈`.  It is essentially
 surjective, again with no hypothesis.  What it is not, in general, is fully
 faithful, and this file measures the two obstructions exactly:

 [Full Comma_Discrete_eq]      ⟺  [HomStrict b a] : f ≈ g → f = g
 [Faithful Comma_Discrete_eq]  ⟺  [HomUIP b a]    : uniqueness of identity
 proofs on `b ~> a`

 Faithfulness breaks down for a structural reason worth stating: the comma
 here is THIN — all parallel morphisms are `≈`, since the only data in a
 morphism lives in 1 ([comma_const_thin]) — while [DiscreteCat]'s hom-setoid
 is strict `eq` on equality proofs.  So the hypothesis of faithfulness is
 vacuously satisfied and its conclusion is literally UIP.

 Consequently the naive expectation, that Mac Lane's remark should hold with
 [DiscreteCat] under the single hypothesis `f ≈ g → f = g`, is FALSE, and
 [comma_discrete_iso_forces_UIP] proves it: ANY isomorphism
 [DiscreteCat (b ~> a) ≅[Cat] (=(b) ↓ =(a))] in Cat entails [HomUIP b a],
 because both legs of a Cat-isomorphism are faithful unconditionally
 ([Cat_Iso_to_Faithful], Instance/Cat.v) — no hypothesis, and not specific to
 the functor built here.  So the conditional reading
 [Comma_Discrete_Hom_eq] takes BOTH [HomStrict] and [HomUIP].  This is the
 same shape as [DiscreteRigid] in Instance/Discrete/Reconstruct.v and as the
 [ObjUIP]-style hypotheses of Theory/Metacategory/General.v: an honest,
 explicitly quantified side condition, never an axiom.

 ** Block D: one hypothesis necessary, the other not droppable, both
 jointly satisfiable

 Neither hypothesis is decoration, and neither claim is left as prose.

 [HomUIP] is necessary by [comma_discrete_iso_forces_UIP] above, for any
 isomorphism whatever.  [HomStrict] is necessary too, and the witness is
 [Blur]: one object, hom-type [bool], and a hom-setoid that identifies the two
 arrows.  There [HomUIP] HOLDS ([Blur_HomUIP], Hedberg at [bool]'s decidable
 equality, axiom-free) while [HomStrict] is refutable outright
 ([Blur_HomStrict_absurd]) — and the conclusion is refutable with it:
 [Blur_no_discrete_iso] shows no isomorphism
 [DiscreteCat bool ≅[Cat] (=(ttt) ↓ =(ttt))] exists over [Blur] at all.  So
 [HomUIP] alone does not suffice, which is what makes [HomStrict] a genuine
 second hypothesis rather than a convenience of the proof.

 And the two are jointly satisfiable, so [Comma_Discrete_Hom_eq] is not a
 conditional with an empty premise: over the terminal category `1` both hold
 ([One_HomStrict] is the identity function, the hom-setoid of `1` being strict
 equality; [One_HomUIP] is Hedberg at [poly_unit]) and
 [One_Comma_Discrete_Hom_eq] is the resulting isomorphism.  That witness is
 degenerate — one object, one arrow — and is offered as an inhabitation check
 on the hypothesis pair, not as an interesting instance. 

 --------
 参考文献：Saunders Mac Lane，《为工作数学家而设的范畴》，第二版，§II.6，第46-47页  [maclane:II.6:remark1]：一般的逗号范畴包含了所有早期的情况；在目录的释义中（doc/plan/books/maclane/inventory/II.json，而不是书中的措辞），取S和T为对象a和b（来自1的函子），(T ↓ S)是关于Hom集C(b, a)的离散范畴——这也是历史符号(T, S)和“逗号范畴”名称的来源。  nLab：https://ncatlab.org/nlab/show/comma+category  nLab：https://ncatlab.org/nlab/show/discrete+category  维基百科：https://en.wikipedia.org/wiki/Comma_categoryLawvere 对逗号范畴的最初表示法是对 (T, S) 的配对，这推广了本文件定理所恢复的同态集表示法 C(b, a)：当 T 和 S 是对象时——也就是说，是从终端范畴 1 出发的函子——逗号范畴 (T, S) 就是同态集 C(b, a)，被视为一个没有非平凡箭头的范畴。这种表示法中的逗号就是该构造名称的来源，而 Wikipedia 记录此名称甚至让其作者也不满意。因此，Mac Lane 的评论同时是定义的退化情况和其词源，这就是为什么本文件存在为一个独立命题，而不是放在某个括号中的原因。

 ** Mac Lane 的专门化列表，以及每一项被记录的地方该备注列举了 (T ↓ S) 的专门化。它们中的每一个都是该库中某处的定理或定义；这一回顾的重点是，现在这个列表是封闭的，本文件提供了最后的条目。

 T = b : 1 ⟶ C, S 任意   对象 S 下的 b 的范畴
 —  [maclane:II.6:def3] ，逗号 (=(b) ↓ S)
 就当前而言；被广泛使用，例如在 Adjunction/GAFT.v 中作为 Freyd 构造的定义域，以及在 Construction/Elements.v 中作为 [ElementsComma := =(SetsOne) ↓ K]。

 T = b, S = Id [C]               余切 b/C
 —  [Comma_Coslice] ，Construction/Slice.v。T = Id [C] ，S = a              切片 C/a
 —  [Comma_Slice] ，Construction/Slice.v;
 对于终端对象 a，切片就是 C 本身，
 [Slice_Terminal] 见 Construction/Slice/Terminal.v。

 T = S = Id [C]                  箭头范畴 C^2
 —  [Arrow := (Id[C]  ↓ Id [C] )],
 Construction/Arrow.v。

 T = b, S = a  （均为对象）  C(b, a) 上的离散范畴
 — 本文件，[Comma_Discrete_Hom] 。有两个相邻的读法值得一提，因为它们容易与最后一行混淆。首先，箭头类别有一个函子类别的表示法，在 Theory/Shapes.v 中为 [Two_Fun_Arrow : [_2, C] ≅ [Cat]  Arrow C]，作用于行走箭头 [_2]；这就是 Mac Lane 符号中的 C^2 的文字化表示，它与这里的其他内容有关，但不会被消耗。其次，Construction/Product/Comma.v 证明了 [Comma_Product]：当两个函子的终端余域为终端时，逗号类别是乘积类别 C ∏ D。该文件的头部已经与当前情况形成对比——“这不同于两函子的*定义域*为 1 的特殊情况，在这种情况下逗号类别是两个选定对象之间的态射的离散类别”——并且仅以文字形式陈述。这个文件
 是将那些行（Construction/Product/Comma.v）提升为一个定理的记录。

 ** 包装选择：setoid-discrete，而不是 [DiscreteCat]

 在基于集合等价关系的库中，必须仔细阅读“对象集 C(b, a) 上的离散范畴”，其阅读方式由逗号范畴的实际结构决定。展开 (=(b) ↓ =(a))：

 - 一个对象是一个三元组 (u, v, h)，其中 u, v 是 1 的唯一对象，h : b ~> a，因此对象就是同态集，带有两个单位的填充；

 - 一个态射 (u, v, h) ~> (u', v', h') 是 1 的态射对——同样是单位，没有信息——满足交换方形条件 h' ∘ fmap [=(b)]  _ ≈ fmap [=(a)]  _ ∘ h。两个常量函子都将每个箭头映射为恒等态射，因此方形条件表示 h' ∘ id ≈ id ∘ h，即 h ≈ h'。因此，逗号范畴的一个态射是在同态集合中 `h ≈ h'` 的一个证据，并且当且仅当 h ≈ h' 时存在。匹配的“离散范畴”因此是这样的一个范畴：它的对象是一个集合等价类的承载者，而它的同态是该集合等价类自身的等价关系——如下的 [DiscreteSetoidCat]。

 Instance/Discrete.v 中的 [DiscreteCat A] 是一个不同的范畴：它的同态是 Rocq 的 `=` 的证明。与它的一个同构不仅在这里尚未被证明，而且是不可用的：它将需要 `h ≈ h' → h = h'`，这正是同态集合折叠为严格相等的那个库拒绝假设的情况。区块 C 精确说明了这一点，而不是仅仅作为备注；见下文。树中的任何内容都无法重用于 [DiscreteSetoidCat]，其原因是一个真正的类型障碍，而不是疏忽。Instance/Proset.v 的 [Proset] 从一个 [PreOrder] 构建了一个薄范畴，而等价关系是一个预序，所以在同态集等价下的 `Proset` 看起来像所需的构造。但 [Proset] 是在 `Coq.Relations.Relation_Definitions.relation` 上声明的，即一个 `Prop` 值的关系，而该库的 `≈` 是一个 `crelation` — `Type` 值，因此等价证明可能携带计算内容（Lib/Setoid.v）。这个差距不是表面的：逗号态射携带其平方证明作为 `sigT` 数据，因此构建一个需要 `Type` 值的见证，并且 `Prop` 值的（或 `Prop` 压扁的）预序不能将其消解到其中。因此，下面的构造是将 [Proset] 转换为 `crelation` 的。

 树中最接近的现有内容是 Instance/Discrete/Reconstruct.v 的 [Blurry A]，它正好是 [DiscreteSetoidCat] 在 `eq` 集合上的——对象 `A`，态射 `x = y`，所有平行箭头都已识别。它在那里被引入作为一个反例；当前文件给出了它的通用构造。它没有从那里导入，因为该文件引入 Instance/StrictCat 和 Eqdep_dec 是出于与此无关的目的。

 ** 提供的内容，以及其强度是什么[Comma_Discrete_Hom : (=(b) ↓ =(a)) ≅[Cat]  HomDiscrete b a]。注意 `≅ [Cat]ZZ ` 是该库中范畴的等价，Cat 的 hom-setoid 是 [Functor_Setoid] (Instance/Cat.v)；没有声称范畴同构。尽管如此，两次往返都是编码允许的最紧密方式，而且两者的紧密程度并不相同：

 - [Comma_Hom ◯ Hom_Comma] 是 [HomDiscrete b a] 的恒等映射，具有一个定义上相同的对象映射 (h ↦ ((ttt, ttt); h) ↦ h)，因此其自然同构的组成部分为 [iso_id]，其一致性条款显然成立，目标对象很薄。- [Hom_Comma ◯ Comma_Hom] 将 (u, v, h) 发送到 ((ttt, ttt); h)，将两个单位填充替换为规范填充。它的组成部分是规范的逗号同构 [comma_const_iso]，其数据仍然是单位。对象映射在 Rocq 项中不是恒等——`u` 是一个变量，而不是 `ttt`——尽管在情况分析之后它会变为恒等；没有严格声明，也没有必要。

 ** C 块：普通的 [DiscreteCat] 读取及其精确代价

 函子 [Comma_Discrete_eq : DiscreteCat (b ~> a) ⟶ (=(b) ↓ =(a))] 的存在完全不依赖任何假设：`=` 蕴含 `≈`。它本质上是满射的，同样不依赖任何假设。通常情况下，它不完全忠实，本文件精确测量了这两个障碍：[Full Comma_Discrete_eq]       ⟺   [HomStrict b a]  : f ≈ g → f = g
 [Faithful Comma_Discrete_eq]   ⟺   [HomUIP b a]     : 在 `b ~> a` 上身份证明的唯一性

 由于一个值得说明的结构性原因，忠实性失效：这里的逗号是 THIN — 所有平行态射都是 `≈`，因为态射中的唯一数据存在于 1（[comma_const_thin]）中 — 而 [DiscreteCat] 的同态集合论在等式证明上是严格的 `eq`。所以忠实性的假设是空洞地满足的，其结论实际上是 UIP。因此，天真的期望，即在单一假设 `f ≈ g → f = g` 下，Mac Lane 的评论应适用于 [DiscreteCat]，是错误的，而 [comma_discrete_iso_forces_UIP] 证明了这一点：任何同构 [DiscreteCat (b ~> a) ≅[Cat] (=(b) ↓ =(a))] 在 Cat 中都意味着 [HomUIP b a]，因为 Cat 同构的两条边无条件都是忠实的 ([Cat_Iso_to_Faithful]，Instance/Cat.v) — 无需假设，也不限于这里构建的函子。因此，条件解读 [Comma_Discrete_Hom_eq] 需同时考虑 [HomStrict] 和 [HomUIP]。这与 Instance/Discrete/Reconstruct.v 中的 [DiscreteRigid] 以及 Theory/Metacategory/General.v 中的 [ObjUIP] 风格假设相同：是真实的、明确量化的附加条件，而不是公理。

 ** D 块：一个假设是必要的，另一个不能舍弃，且两者可同时满足无论假设都不是装饰，也没有任何主张被保留为散文。

 如上所述，对于任意同构，[HomUIP] 是必要的。[HomStrict] 也是必要的，其见证是 [Blur]：一个对象，Hom 类型 [bool]，以及一个识别两条箭头的 Hom-集合。那里 [HomUIP] 成立（[Blur_HomUIP]，Hedberg 在 [bool] 的可判定等式下，无需公理），而 [HomStrict] 则可以直接反驳（[Blur_HomStrict_absurd]）——结论在此情况下也是可反驳的：[Blur_no_discrete_iso] 显示没有同构 [DiscreteCat bool ≅[Cat]（=(ttt) ↓ =(ttt)）] 在 [Blur] 上存在。因此，仅 [HomUIP] 并不充分，这正是使 [HomStrict] 成为真正的第二个假设，而非证明上的方便之处。这两者是可以同时满足的，因此 [Comma_Discrete_Hom_eq] 不是一个前提为空的条件命题：在终端范畴 `1` 上，两者都成立（[One_HomStrict] 是恒等函数，`1` 的 Hom-集合是严格相等；[One_HomUIP] 在 [poly_unit] 上是 Hedberg) 并且 [One_Comma_Discrete_Hom_eq] 是由此得到的同构。这个见证是退化的——一个对象，一条箭头——它被用作对假设对的存在性检查，而不是一个有趣的实例。
*)

(* * ** Block A: the discrete category on a setoid / * ** 块 A：集合类上的离散范畴 *)

(*
 [Proset] transposed from `Prop`-valued preorders to the `crelation`s this
 library's `≈` lives in: objects are the carrier, a morphism x ~> y is a
 proof of x ≈ y, identity is reflexivity and composition is transitivity.
 Like [Proset] it is THIN — the hom-setoid identifies all parallel arrows —
 so every category law is an equation between parallel morphisms and is
 discharged by the default obligation tactic.

 [Blurry A] (Instance/Discrete/Reconstruct.v) is this construction at the
 `eq` setoid; [Proset] is its `Prop`-valued analogue, unusable here for the
 reason given in the header. 

 --------
 [Proset] 是从 `Prop` 值的预序转置到 `crelation` 的，这个库的 `≈` 所在的地方：对象是承载体，态射 x ~> y 是 x ≈ y 的证明，恒等是自反性，合成是传递性。像 [Proset] 一样，它是 THIN——同态集合识别所有平行箭头——所以每个范畴法则都是平行态射之间的等式，并由默认义务策略处理。

 [Blurry A]（Instance/Discrete/Reconstruct.v）是在 `eq` 集合上的这一构造；[Proset] 是其 `Prop` 值的类似物，由于标题中给出的原因，这里无法使用。
*)
Program Definition DiscreteSetoidCat {A : Type} (S : Setoid A) : Category := {|
  obj     := A;                                (* objects are the carrier / 物体是载体 *)
  hom     := fun x y => @equiv A S x y;        (* a morphism IS a proof of ≈ / 一个态射就是 ≈ 的证明 *)
  homset  := fun _ _ => {| equiv := fun _ _ => True |};   (* thin *)
  id      := fun x => @Equivalence_Reflexive A (@equiv A S) (@setoid_equiv A S) x;
  compose := fun x y z g f =>
    @Equivalence_Transitive A (@equiv A S) (@setoid_equiv A S) x y z f g
|}.

(*
 Thinness, in the form used below: any two parallel arrows agree. 

 --------
 下面使用的形式上的‘瘦’: 任意两条平行箭头一致。
*)
Lemma DiscreteSetoidCat_thin {A : Type} (S : Setoid A)
  (x y : DiscreteSetoidCat S) (f g : x ~> y) : f ≈ g.
Proof. exact I. Qed.

(*
 The discrete category on the hom-set C(b, a) — Mac Lane's "discrete
 category on the hom-set", read at the hom-SETOID as the header explains. 

 --------
 Hom 集合 C(b, a) 上的离散范畴——Mac Lane 的“Hom 集合上的离散范畴”，如标题在 hom-SETOID 中所解释的那样。
*)
Definition HomDiscrete {C : Category} (b a : C) : Category :=
  DiscreteSetoidCat (@homset C b a).

(* * ** Block B: the comma of two constant functors / * ** 块 B：两个常量函子的逗号 *)

Section CommaConstant.

Context {C : Category}.
Context {b a : C}.

(*
 The canonical comma object attached to an arrow h : b ~> a, padded with the
 unique object of 1 on both sides. 

 --------
 连接到箭头 h : b ~> a 的典型逗号对象，在两侧都用 1 的唯一对象填充。
*)
Definition comma_const_obj (h : b ~{C}~> a) : (=(b) ↓ =(a)) := ((ttt, ttt); h).

(*
 The comma of two constant functors is THIN: the only data in one of its
 morphisms is a pair of arrows of 1, and 1 has exactly one arrow.  This is
 the engine of the file's comma-side obligations — every functor and
 isomorphism law whose goal lands IN the comma is an instance of it.  (Laws
 landing in [HomDiscrete] are discharged by that category's own trivially
 true hom-setoid instead: those goals are equations the setoid makes
 vacuous, which [comma_const_thin] cannot even be applied to by typing.) 

 --------
 两个常值函子的逗号是薄的：它的一个态射中唯一的数据是一对来自 1 的箭头，而 1 恰好有一个箭头。这是文件中逗号侧义务的引擎——每一个目标落在逗号中的函子和同构律都是它的一个实例。（落在 [HomDiscrete] 中的律则由该范畴自身的平凡真同态集合去解决：那些目标是集合准则使之变为空的方程，而 [comma_const_thin] 甚至无法通过类型应用于它们。）
*)
Lemma comma_const_thin (X Y : (=(b) ↓ =(a))) (m n : X ~> Y) : m ≈ n.
Proof.
  destruct m as [[u1 u2] Hm], n as [[v1 v2] Hn]; simpl.
  now split; destruct u1, u2, v1, v2.
Qed.

(*
 A morphism of the comma category yields the ≈ its square asserts.  The
 square is `h' ∘ fmap[=(b)] _ ≈ fmap[=(a)] _ ∘ h`, and both constant functors
 send every arrow to an identity, so it says h' ≈ h. 

 --------
 逗号范畴的一个态射产生了它的平方所断言的结果。这个平方是 `h' ∘ fmap [=(b)]ZZ  _ ≈ fmap [=(a)]ZZ  _ ∘ h`，并且两个恒等函子将每个箭头都映射到一个恒等箭头，所以它说明 h' ≈ h。
*)
Lemma comma_const_equiv {X Y : (=(b) ↓ =(a))} (m : X ~> Y) : `2 X ≈ `2 Y.
Proof.
  destruct m as [uv Hm]; simpl in *.
  rewrite id_left, id_right in Hm.
  now symmetry.
Qed.

(*
 ... and conversely, a ≈ yields a morphism; written out rather than left to
 the default obligation tactic, since this direction is the file's claim that
 a comma morphism here IS a witness of `≈`. 

 --------
 ... 相反，a ≈ 会产生一个态射；这里是写出来的，而不是留给默认的义务策略，因为这一方向是该文件声明的，即这里的逗号态射确实是 `≈` 的见证。
*)
#[local] Obligation Tactic := idtac.

Program Definition comma_const_mor {X Y : (=(b) ↓ =(a))} (e : `2 X ≈ `2 Y) :
  X ~> Y := ((ttt, ttt); _).
Next Obligation.
  intros X Y e; simpl.
  (*
 the square is `2 Y ∘ id ≈ id ∘ `2 X, both constant functors sending every
 arrow of 1 to an identity 

 --------
 这个方形是 `2 Y ∘ id ≈ id ∘ ` 2 X，两个常量函子将 1 的每条箭头都映射为恒等箭头
*)
  rewrite id_left, id_right; now symmetry.
Qed.

#[local] Obligation Tactic := cat_simpl.

(*
 Comma objects are isomorphic exactly when their arrows agree: an arrow of
 the comma IS a witness of `≈` ([comma_const_equiv] the other way), so this is
 the object-level reading of thinness. 

 --------
 当逗号对象的箭头一致时，它们是同构的：逗号的一个箭头是 `≈`（或 [comma_const_equiv] 另一方向）的见证，因此这是薄性的对象层面的解读。
*)
Program Definition comma_const_obj_iso {X Y : (=(b) ↓ =(a))} (e : `2 X ≈ `2 Y) :
  X ≅ Y := {|
  to   := comma_const_mor e;
  from := comma_const_mor (symmetry e)
|}.
Solve All Obligations with (intros; apply comma_const_thin).

(*
 Every comma object is canonically isomorphic to the canonical one on its own
 arrow; only the unit padding changes. 

 --------
 每个逗号对象在其自身箭头上都是与规范对象典型同构的；只有单位填充会改变。
*)
Program Definition comma_const_iso (X : (=(b) ↓ =(a))) :
  comma_const_obj (`2 X) ≅ X := {|
  to   := comma_const_mor (Y:=X) (reflexivity _);
  from := comma_const_mor (X:=X) (reflexivity _)
|}.
Solve All Obligations with (intros; apply comma_const_thin).

(*
 Read off the arrow: the comma of two constant functors ⟶ the hom-set. 

 --------
 读出箭头：两个恒等函子 ⟶ 的逗号到 Hom 集。
*)
Program Definition Comma_Hom : (=(b) ↓ =(a)) ⟶ HomDiscrete b a := {|
  fobj := fun X => `2 X;
  fmap := fun _ _ m => comma_const_equiv m
|}.

(* ... and back, padding an arrow into a comma object. / ...并返回，将箭头填充到逗号对象中。 *)
Program Definition Hom_Comma : HomDiscrete b a ⟶ (=(b) ↓ =(a)) := {|
  fobj := comma_const_obj;
  fmap := fun x y e => comma_const_mor (X:=comma_const_obj x)
                                       (Y:=comma_const_obj y) e
|}.
Solve All Obligations with (intros; apply comma_const_thin).

(*
 Mac Lane, §II.6, remark [maclane:II.6:remark1]: the comma category of two
 objects, regarded as functors out of 1, is the discrete category on the
 hom-set between them.  `≅[Cat]` is EQUIVALENCE of categories here
 (Instance/Cat.v); see the header for what each round trip achieves. 

 --------
 Mac Lane，第 II.6 节，备注 [maclane:II.6:remark1]：两个对象的逗号范畴，被视为从 1 出发的函子，是它们之间同态集合上的离散范畴。`≅ [Cat]ZZ ` 在这里是范畴的等价（Instance/Cat.v）；见标题了解每次往返所实现的内容。
*)
(*
 [idtac] so that BOTH clauses are written out rather than left to the default
 obligation tactic; restored immediately afterwards. 

 --------
 [idtac]  以便两个条款都被写出来，而不是依赖默认的义务策略；随后立即恢复。
*)
#[local] Obligation Tactic := idtac.

Program Definition Comma_Discrete_Hom : (=(b) ↓ =(a)) ≅[Cat] HomDiscrete b a := {|
  to   := Comma_Hom;
  from := Hom_Comma
|}.
Next Obligation.
  (*
 Comma_Hom ◯ Hom_Comma ≈ Id[HomDiscrete b a]: the identity on objects
 definitionally (h ↦ ((ttt, ttt); h) ↦ h), so [iso_id] components serve, and
 the coherence clause is trivially true, the target being thin. 

 --------
 Comma_Hom ◯ Hom_Comma ≈ Id [HomDiscrete b a] ：对象上的恒等映射
 定义上 (h ↦ ((ttt, ttt); h) ↦ h)，因此 [iso_id] 分量起作用，并且
 一致性条款显然成立，因为目标是薄的。
*)
  exists (fun _ => iso_id).
  intros x y e; exact I.
Qed.
Next Obligation.
  (*
 Hom_Comma ◯ Comma_Hom ≈ Id[(=(b) ↓ =(a))]: renormalise the unit padding.
 The coherence clause is an equation between parallel comma morphisms. 

 --------
 Hom_Comma ◯ Comma_Hom ≈ Id [(=(b) ↓ =(a))] ：重新归一化单位填充。
 相干性条款是平行逗号态射之间的一个方程。
*)
  exists comma_const_iso.
  intros X Y m.
  first [ apply comma_const_thin | (split; reflexivity) ].
Qed.

#[local] Obligation Tactic := cat_simpl.

End CommaConstant.

(*
   * ** Block C: the plain [DiscreteCat] reading and its exact price 

   --------
   * ** C区：普通 [DiscreteCat] 读取及其确切价格
*)

Section CommaDiscreteEq.

Context {C : Category}.
Context {b a : C}.

(*
 The always-available comparison: `=` implies `≈`, so the strictly discrete
 category on the hom-TYPE maps into the comma category.  Every equality proof
 goes to the canonical comma morphism on the reflexivity witness it
 transports.

 Not [DiscreteCat_Functor comma_const_obj], though the two are extensionally
 the same functor.  [Full], [Faithful] and [EssentiallySurjective] each carry
 only THREE universe parameters (measured: `About Full` reports
 `Full@{u u0 u1}`), so each identifies the hom AND proof universes of its
 source and target categories.  RECORDED CORRECTION: an earlier revision of
 this paragraph continued "[DiscreteCat_Functor] carries the `Set` pin in its
 OWN signature — its type mentions `DiscreteCat@{u Set Set}`, fixed when that
 constant was defined — so using it here would make the class demand `Set`
 for C's hom universe too, which at this abstract use site is a universe
 inconsistency, not merely a pin."  That pin is GONE: the donor was annotated
 in place at Instance/Discrete.v in the PR "algebraic carriers are sets"
 (2026-09-17), and its type now reads `DiscreteCat@{o h p} A ⟶ C` over
 `C : Category@{uo uh up}`, with no literal `Set`.  Whether the hand-built
 functor could therefore be replaced by [DiscreteCat_Functor comma_const_obj]
 here has NOT been re-measured, and the hand-built one is kept: building the
 functor by hand leaves those universes free to unify with C's, which is what
 Block C's statements need; the same consideration is why
 Instance/Discrete/Reconstruct.v's [Discrete_Compare] carries explicit
 `@{o h p}` binders rather than going through [Program]. 

 --------
 始终可用的比较：`=` 意味着 `≈`，因此同态类型上的严格离散范畴映射到逗号范畴。每一个等式证明都映射到它所传送的自反性证据上的典型逗号态射。不是 [DiscreteCat_Functor comma_const_obj]，虽然两者在扩展意义上是相同的函子。[Full]、[Faithful] 和 [EssentiallySurjective] 各自只携带三个宇宙参数（测量：`About Full` 报告 `Full@{u u0 u1}`），所以每一个都标识了其源范畴和目标范畴的同态宇宙和证明宇宙。记录的更正：该段落的早期修订版本继续写道“[DiscreteCat_Functor] 在其自身签名中携带 `Set` 引脚——其类型提到了 `DiscreteCat@{u Set Set}`，当该常量被定义时已固定——因此在这里使用它将使类在 C 的同质宇宙中也需要 `Set`，在这个抽象使用位置，这是一个宇宙不一致，而不仅仅是一个引脚。”该引脚已被移除：捐赠者在 PR “代数载体是集合”（2026-09-17）中在 Instance/Discrete.v 中被注释到位，并且它的类型现在在 `C : Category@{uo uh up}` 上显示为 `DiscreteCat@{o h p} A ⟶ C`，没有字面上的 `Set`。是否可以在此用 [DiscreteCat_Functor comma_const_obj] 替换手工构建的函子尚未重新测量，因此保留手工构建的函子：手工构建函子使那些范畴能够自由地与 C 统一，这是 Block C 的语句所需要的；同样的考虑也解释了为何 Instance/Discrete/Reconstruct.v 的 [Discrete_Compare] 带有显式的 `@{o h p}` 绑定器，而不是通过 [Program]。
*)
(*
 `=` implies `≈`: transport the reflexivity witness along the equality. 

 --------
 `=` 意味着 `≈`：沿着等式传递自反性证据。
*)
Definition discrete_eq_equiv (x y : b ~{C}~> a) (e : x = y) : x ≈ y :=
  match e in _ = z return x ≈ z with eq_refl => reflexivity x end.

Definition comma_const_eq_mor (x y : b ~{C}~> a) (e : x = y) :
  comma_const_obj x ~> comma_const_obj y :=
  comma_const_mor (X := comma_const_obj x) (Y := comma_const_obj y)
    (discrete_eq_equiv x y e).

(*
 Every functor law is an instance of [comma_const_thin]; [Proper] is a
 definitional single-field class, so its field too is supplied as a plain
 lambda rather than through [Program]. 

 --------
 每一个函子定律都是 [comma_const_thin] 的一个实例；[Proper] 是一个定义性的单字段类，所以它的字段也是作为一个普通的 lambda 提供的，而不是通过 [Program] 提供。
*)
Definition Comma_Discrete_eq : DiscreteCat (b ~{C}~> a) ⟶ (=(b) ↓ =(a)) :=
  @Build_Functor (DiscreteCat (b ~{C}~> a)) (=(b) ↓ =(a))
    comma_const_obj comma_const_eq_mor
    (fun _ _ _ _ _ => comma_const_thin _ _ _ _)
    (fun _ => comma_const_thin _ _ _ _)
    (fun _ _ _ _ _ => comma_const_thin _ _ _ _).

(* The hypothesis that would make the hom-setoid strict. / 使同态集合严格的假设。 *)
Definition HomStrict : Type := ∀ f g : b ~{C}~> a, f ≈ g → f = g.

(* ... and uniqueness of identity proofs on the hom-type. / ...以及同构类型上身份证明的唯一性。 *)
Definition HomUIP : Type := ∀ (f g : b ~{C}~> a) (p q : f = g), p = q.

(*
 Essential surjectivity is free: every comma object is the canonical one on
 its own arrow, up to the unit-renormalising isomorphism. 

 --------
 本质上的满射是自由的：每个逗号对象都是其自身箭头上的典型对象，最多只差一个单位重整同构。
*)
Program Definition Comma_Discrete_eq_ESO :
  EssentiallySurjective Comma_Discrete_eq := {|
  eso_obj := fun X => `2 X;
  eso_iso := comma_const_iso
|}.

(*
 Fullness is EXACTLY the collapse of the hom-setoid.  Forwards: a witness of
 f ≈ g is a comma morphism between the images, whose preimage is the wanted
 equality.  Backwards: the required section law is free, the comma category
 being thin. 

 --------
 满性正是同范畴集的坍塌。正向：f ≈ g 的证据是像之间的逗号态射，其原像就是所需的等式。反向：所需的截面律是免费的，因为逗号范畴是稀疏的。
*)
Theorem Comma_Discrete_eq_Full_iff : Full Comma_Discrete_eq ↔ HomStrict.
Proof.
  split.
  - intros F f g e.
    exact (@prefmap _ _ _ F f g (comma_const_mor (X:=comma_const_obj f)
                                                 (Y:=comma_const_obj g) e)).
  - intro HE.
    exact (@Build_Full _ _ Comma_Discrete_eq
             (fun f g m => HE f g (comma_const_equiv m))
             (fun f g m => comma_const_thin _ _ _ _)).
Qed.

(*
 Faithfulness is EXACTLY UIP on the hom-type.  The comma category is thin, so
 the hypothesis `fmap p ≈ fmap q` is vacuous and the conclusion `p ≈ q` is,
 in [DiscreteCat], strict equality of the two proofs. 

 --------
 忠诚性在同类类型上完全是 UIP。逗号范畴是薄的，所以假设 `fmap p ≈ fmap q` 是空的，而结论 `p ≈ q` 在 [DiscreteCat] 中是两个证明的严格相等。
*)
Theorem Comma_Discrete_eq_Faithful_iff : Faithful Comma_Discrete_eq ↔ HomUIP.
Proof.
  split.
  - intros F f g p q.
    exact (@fmap_inj _ _ _ F f g p q (comma_const_thin _ _ _ _)).
  - intro HU.
    constructor; intros f g p q _; exact (HU f g p q).
Qed.

(*
 The conditional reading, with both hypotheses.  [HomStrict] builds the
 backward functor's action and [HomUIP] discharges its three laws, each of
 which is an equation between equality proofs. 

 --------
 条件读取，同时包含两个假设。[HomStrict] 构建了反向范畴子的作用，而 [HomUIP] 解除其三个定律，每一个定律都是等式证明之间的一个方程。
*)
Definition Hom_Discrete_eq (HE : HomStrict) (HU : HomUIP) :
  HomDiscrete b a ⟶ DiscreteCat (b ~{C}~> a) :=
  @Build_Functor (HomDiscrete b a) (DiscreteCat (b ~{C}~> a))
    (fun h => h) HE
    (fun _ _ _ _ _ => HU _ _ _ _)     (* fmap_respects / fmap_遵守 *)
    (fun _ => HU _ _ _ _)             (* fmap_id *)
    (fun _ _ _ _ _ => HU _ _ _ _).    (* fmap_comp / fmap_组合 *)

(*
 The other leg, again hand-built rather than [DiscreteCat_Functor] so that no
 universe is baked in; every law is an equation in the thin [HomDiscrete]. 

 --------
 另一条腿，同样是手工制作的，而不是 [DiscreteCat_Functor]，因此没有任何宇宙被固化；每条法则都是薄薄的 [HomDiscrete] 中的一个方程。
*)
Definition Discrete_eq_Hom : DiscreteCat (b ~{C}~> a) ⟶ HomDiscrete b a :=
  @Build_Functor (DiscreteCat (b ~{C}~> a)) (HomDiscrete b a)
    (fun h => h) discrete_eq_equiv
    (fun _ _ _ _ _ => I) (fun _ => I) (fun _ _ _ _ _ => I).

#[local] Obligation Tactic := idtac.

Program Definition Discrete_HomDiscrete (HE : HomStrict) (HU : HomUIP) :
  DiscreteCat (b ~{C}~> a) ≅[Cat] HomDiscrete b a := {|
  to   := Discrete_eq_Hom;
  from := Hom_Discrete_eq HE HU
|}.
Next Obligation.
  (*
 Discrete_eq_Hom ◯ Hom_Discrete_eq ≈ Id[HomDiscrete b a]: identity on
 objects definitionally, and the target is thin. 

 --------
 Discrete_eq_Hom ◯ Hom_Discrete_eq ≈ Id [HomDiscrete b a]：在对象上按定义是恒等的，并且目标是稀薄的。
*)
  intros HE HU.
  exists (fun _ => iso_id).
  intros x y e; exact I.
Qed.
Next Obligation.
  (*
 Hom_Discrete_eq ◯ Discrete_eq_Hom ≈ Id[DiscreteCat ...]: identity on
 objects definitionally; the coherence clause is an equation between
 equality proofs in the hom-type, hence exactly [HomUIP]. 

 --------
 Hom_Discrete_eq ◯ Discrete_eq_Hom ≈ Id [DiscreteCat ...]：在对象上的定义性恒等；相干条款是同态类型中等式证明之间的等式，因此正好是 [HomUIP]。
*)
  intros HE HU.
  exists (fun _ => iso_id).
  intros x y p; apply HU.
Qed.

#[local] Obligation Tactic := cat_simpl.

(*
 Mac Lane's remark in its literal, strictly-discrete form — available exactly
 under the two explicit hypotheses, and (by the theorem after it) not for
 free. 

 --------
 Mac Lane 的评论以其字面上、严格离散的形式——仅在两个明确假设下可用，并且（根据其后的定理）不是免费的。
*)
Definition Comma_Discrete_Hom_eq (HE : HomStrict) (HU : HomUIP) :
  DiscreteCat (b ~{C}~> a) ≅[Cat] (=(b) ↓ =(a)) :=
  iso_compose (iso_sym Comma_Discrete_Hom) (Discrete_HomDiscrete HE HU).

(*
 The necessity of [HomUIP], for ANY isomorphism, not merely for the one built
 above: both legs of an isomorphism in Cat are faithful with no hypothesis
 ([Cat_Iso_to_Faithful], Instance/Cat.v), and faithfulness of a functor into
 this thin comma category is literally UIP on the hom-type.  So the plain
 [DiscreteCat] reading of Mac Lane's remark cannot be had unconditionally in
 this library. 

 --------
 对于任何同构（不仅仅是上面构建的那个同构），[HomUIP] 的必要性：Cat 中同构的两条腿在没有假设的情况下都是 faithful（[Cat_Iso_to_Faithful]，Instance/Cat.v），并且进入这个薄逗号范畴的函子的 faithful 性在同态类型上字面上就是 UIP。因此，在这个库中，Mac Lane 的评论的普通 [DiscreteCat] 读法不能无条件成立。
*)
Theorem comma_discrete_iso_forces_UIP
  (iso : DiscreteCat (b ~{C}~> a) ≅[Cat] (=(b) ↓ =(a))) : HomUIP.
Proof.
  intros f g p q.
  exact (@fmap_inj _ _ _ (Cat_Iso_to_Faithful iso) f g p q
           (comma_const_thin _ _ _ _)).
Qed.

End CommaDiscreteEq.

(*
   * ** Block D: witnesses — both hypotheses inhabited, and both necessary 

   --------
   * ** D区：证人——两种假设都有存在，并且两者都是必要的
*)

(*
 Non-vacuity of Block C is proved rather than assumed, in both directions.

 [HomUIP] alone is not enough: [Blur] below is a category whose hom-type is
 [bool], on which UIP holds by Hedberg, yet Mac Lane's remark in its plain
 [DiscreteCat] form is outright FALSE there ([Blur_no_discrete_iso]) — so
 [HomStrict] is a genuine second hypothesis, not a convenience.  The two
 hypotheses are pinned at DIFFERENT strengths, stated precisely:
 [comma_discrete_iso_forces_UIP] shows [HomUIP] NECESSARY for any such
 isomorphism (a genuine implication), while for [HomStrict] what is shown is
 that it is NOT DROPPABLE ([Blur]: the other hypothesis alone does not
 suffice) — no implication from the isomorphism to [HomStrict] is claimed.
 And the pair is simultaneously satisfiable: over the terminal
 category both hold and [Comma_Discrete_Hom_eq] applies
 ([One_Comma_Discrete_Hom_eq]). 

 --------
 块 C 的非空性在两个方向上都是被证明的，而不是假定的。

 仅靠 [HomUIP] 不够：下面的 [Blur] 是一个其同态类型为 [bool] 的范畴，UIP 在其上由 Hedberg 成立，但 Mac Lane 在其简单 [DiscreteCat] 形式中的评论在这里是完全错误的（[Blur_no_discrete_iso]）——因此 [HomStrict] 是真正的第二个假设，而不是一个方便条件。这两个假设在不同强度上被明确固定，并精确陈述：[comma_discrete_iso_forces_UIP] 显示 [HomUIP] 对于任何这样的同构是必要的（一个真正的蕴涵），而对于 [HomStrict] 所显示的是它不可放弃（[Blur]：单独的另一个假设是不够的）——并没有声称同构可以推导出 [HomStrict]。并且这对假设可以同时满足：在终范畴上，两者都成立并且 [Comma_Discrete_Hom_eq] 适用（[One_Comma_Discrete_Hom_eq]）。
*)

From Coq Require Import Eqdep_dec.

(*
 One object, two parallel arrows, and a hom-setoid that identifies them: the
 minimal category on which the hom-setoid is a genuine quotient.  Every
 category law is an equation in the trivial hom-setoid, hence free — the same
 device as Instance/Proset.v and as [Blurry] in
 Instance/Discrete/Reconstruct.v, whence the name. 

 --------
 一个对象、两条平行箭头，以及一个将它们识别的同态集合：这是同态集合是真正商的最小范畴。每个范畴定律都是平凡同态集合中的一个方程，因此是自由的——与 Instance/Proset.v 以及 Instance/Discrete/Reconstruct.v 中的 [Blurry] 使用的方式相同，因此得名。
*)
Program Definition Blur : Category := {|
  obj     := poly_unit;
  hom     := fun _ _ => bool;
  homset  := fun _ _ => {| equiv := fun _ _ => True |};
  id      := fun _ => true;
  compose := fun _ _ _ _ _ => true
|}.

(*
 Its hom-setoid does not collapse to equality: `true ≈ false` yet
 `true <> false`. 

 --------
 它的同态集不简化为等式：`true ≈ false` 但 `true <> false` 。
*)
Lemma Blur_HomStrict_absurd : @HomStrict Blur ttt ttt → False.
Proof. intro HE; discriminate (HE true false I). Qed.

(*
 But UIP on the hom-type does hold, by Hedberg's theorem at the decidable
 equality of [bool] (stdlib [UIP_dec]; no axiom). 

 --------
 但是在 hom 类型上 UIP 是成立的，根据 Hedberg 定理，在  [bool]  的可判定等式（stdlib  [UIP_dec]；无公理）下。
*)
Lemma Blur_HomUIP : @HomUIP Blur ttt ttt.
Proof.
  intros f g p q; apply UIP_dec.
  intros x y; destruct x, y; solve [ now left | right; discriminate ].
Qed.

(*
 Hence [HomUIP] does not suffice: over [Blur] no isomorphism in Cat between
 the strictly discrete category on the hom-type and the comma of the two
 constant functors exists at all.

 The argument is short.  Over [Blur] any two arrows are `≈`, so any two
 objects of the comma are isomorphic ([comma_const_obj_iso]).  A functor
 preserves isomorphisms ([fobj_iso]), so the two objects `true` and `false` of
 [DiscreteCat bool] have isomorphic images under `from ◯ to`; but in a
 [DiscreteCat] an isomorphism carries an equality of its endpoints, and the
 round trip `from ◯ to ≈ Id` identifies each image with its argument.  So
 `true = false`. 

 --------
 因此 [HomUIP] 不够：在 [Blur] 上，严格离散的 Hom 型类别与两个恒等函子组成的逗号范畴之间在 Cat 中根本不存在同构。 这个论证很简短。在 [Blur] 上，任意两条箭头都是 `≈`，因此逗号中的任意两个对象都是同构的（[comma_const_obj_iso]）。函子保持同构（[fobj_iso]），所以 [DiscreteCat bool] 中的两个对象 `true` 和 `false` 在 `from ◯ to` 下的像是同构的；但在 [DiscreteCat] 中，同构会传递端点的相等性，并且往返 `from ◯ to ≈ Id` 会将每个像识别为其原像。因此 `true = false`。
*)
Theorem Blur_no_discrete_iso :
  (DiscreteCat (ttt ~{Blur}~> ttt) ≅[Cat] (=((ttt : Blur)) ↓ =((ttt : Blur)))) → False.
Proof.
  intro iso.
  (*
 the two comma images are isomorphic, all Blur-arrows being ≈ 

 --------
 这两个逗号图像是同构的，所有模糊箭头都大致相等
*)
  pose proof (comma_const_obj_iso
                (X := to iso true) (Y := to iso false) I) as Hcomma.
  (* transport that isomorphism back along `from iso` / 沿着 `from iso` 将同构传回去 *)
  pose proof (@fobj_iso _ _ (from iso) _ _ Hcomma) as Hback.
  (* the round trip identifies `from (to x)` with `x` / 往返识别 `from (to x)` 与 `x` *)
  pose proof (`1 (iso_from_to iso) true) as Ht.
  pose proof (`1 (iso_from_to iso) false) as Hf.
  assert (Heq : (true : DiscreteCat (ttt ~{Blur}~> ttt)) = false).
  { transitivity (from iso (to iso true)).
    - exact (eq_sym (to Ht)).
    - transitivity (from iso (to iso false)).
      + exact (to Hback).
      + exact (to Hf). }
  discriminate Heq.
Qed.

(*
 [Blur] also settles the sibling file's strictness question.
 Construction/Slice/Terminal.v argues in prose that Mac Lane's "isomorphic"
 is unavailable for the slice over a terminal object — slice objects carry
 their structure morphism as data, and [one_unique] gives only `≈`.  Here
 that argument becomes a theorem: [Blur]'s trivially-true hom-setoid makes
 EVERY arrow a `one`, so `Slice Blur ttt` has two objects `(ttt; true)` and
 `(ttt; false)` where [Blur] has one object, and a strict isomorphism of
 categories would force `true = false` through its object round trip.
 (Adapted from the adversarial audit's probe, with thanks.) 

 --------
 [Blur] 也解决了兄弟文件的严格性问题。 构造/Slice/Terminal.v 以散文方式论证了 Mac Lane 的“同构”在终对象上的 slice 中不可用 —— slice 对象将其结构态射作为数据携带，而 [one_unique] 只提供了 `≈`。 在这里，这个论证成为了一个定理：[Blur] 中平凡地成立的 Hom-集合（hom-setoid）使得每个箭头都是 `one`，因此 `Slice Blur ttt` 有两个对象 `(ttt; true)` 和 `(ttt; false)`，而 [Blur] 只有一个对象，范畴的严格同构将迫使 `true = false` 经过其对象的往返。 （改编自对抗性审计的探针，谨致谢意。）
*)
Program Definition Blur_Terminal : @Terminal Blur := {|
  terminal_obj := ttt;
  one := fun _ => true
|}.

Theorem slice_terminal_not_strict :
  (@Slice Blur (@terminal_obj Blur Blur_Terminal) ≅[StrictCat] Blur) → False.
Proof.
  intro iso.
  pose proof (`1 (iso_from_to iso) ((ttt; true) : @Slice Blur ttt)) as Ht.
  pose proof (`1 (iso_from_to iso) ((ttt; false) : @Slice Blur ttt)) as Hf.
  assert (Hmid : fobj[to iso] ((ttt; true) : @Slice Blur ttt)
               = fobj[to iso] ((ttt; false) : @Slice Blur ttt)).
  { now destruct (fobj[to iso] ((ttt; true) : @Slice Blur ttt)),
                 (fobj[to iso] ((ttt; false) : @Slice Blur ttt)). }
  assert (Heq : ((ttt; true) : @Slice Blur ttt) = (ttt; false)).
  { transitivity (fobj[from iso] (fobj[to iso] ((ttt; true) : @Slice Blur ttt))).
    - exact (eq_sym Ht).
    - transitivity (fobj[from iso] (fobj[to iso] ((ttt; false) : @Slice Blur ttt))).
      + exact (f_equal (fobj[from iso]) Hmid).
      + exact Hf. }
  exact (Bool.diff_true_false
           (f_equal (fun s : @Slice Blur ttt => projT2 s) Heq)).
Qed.

(*
 The other side: over the terminal category both hypotheses hold, so
 [Comma_Discrete_Hom_eq] is not a conditional with an empty premise.  The
 hom-setoid of `1` is strict equality, so [HomStrict] is the identity, and
 [HomUIP] is Hedberg at [poly_unit]. 

 --------
 另一边：在终端范畴上，两个假设都成立，所以 [Comma_Discrete_Hom_eq] 不是具有空前提的条件。`1` 的同态集合是严格相等的，所以 [HomStrict] 是恒等映射，而 [HomUIP] 在 [poly_unit] 上是 Hedberg。
*)
Lemma One_HomStrict : @HomStrict _1 ttt ttt.
Proof. intros f g e; exact e. Qed.

Lemma One_HomUIP : @HomUIP _1 ttt ttt.
Proof.
  intros f g p q.
  apply UIP_dec.
  now intros x y; destruct x, y; left.
Qed.

Definition One_Comma_Discrete_Hom_eq :
  DiscreteCat (ttt ~{_1}~> ttt) ≅[Cat] (=((ttt : _1)) ↓ =((ttt : _1))) :=
  Comma_Discrete_Hom_eq One_HomStrict One_HomUIP.
