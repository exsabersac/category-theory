Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Arrow.Dual.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Reflective.Coreflective.

Generalizable All Variables.

(* * * Reflective subcategories from universal arrows / * * 来自泛箭头的反射子范畴 *)

(*
 nLab:  https://ncatlab.org/nlab/show/reflective+subcategory
 nLab:  https://ncatlab.org/nlab/show/universal+morphism
 Book:  Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 GTM 5, §IV.3, printed p. 91 (PDF p. 100), and the examples of
 printed p. 92 (PDF p. 101) that issue #370 collects
 Book:  Riehl, "Category Theory in Context", Dover 2016, §4.6,
 Definition 4.6.12, printed p. 169 (PDF p. 189)

 Mac Lane defines the notion on p. 91 and, in the same paragraph,
 reads it through universal arrows.  Quoted from the page image:

 "A subcategory A of B is called reflective in B when the inclusion
 functor K: A → B has a left adjoint F: B → A. ... A reflection may
 be described in terms of universal arrows: A ⊂ B is reflective if
 and only if to each b ∈ B there is an object Rb of the subcategory
 A and an arrow η_b: b → Rb such that every arrow g: b → a ∈ A has
 the form g = f ∘ η_b for a unique arrow f: Rb → a of A.  As usual,
 R is then (the object function of) a functor B → B (with values in
 A)."

 Riehl's Definition 4.6.12 is the same notion, a full subcategory
 whose inclusion has a left adjoint, which she calls the reflector or
 localization; her Example 4.6.13 is the roster of examples whose
 clauses (ii) and (iv) issue #370 also collects.

 Every concrete reflection is found that way in practice: one
 constructs the completion, the abelianization, the extension of
 scalars, one object at a time, proves its universal property, and
 only then speaks of a functor.  The general theorem that turns the
 pointwise data into an adjunction is already in the tree, as
 Theory/Universal/Arrow.v's [LeftAdjointFunctorFromUniversalArrows]
 and [AdjunctionFromUniversalArrows]; what is missing is the step from
 there into Construction/Reflective.v's record, and that step is this
 file, together with its dual into the coreflective record.  It is a
 satellite rather than part of Construction/Reflective.v because it
 needs Theory/Universal/Arrow.v, which that file does not require: the
 transitive closure of [coqdep -R . Category] over the [_CoqProject]
 files, the file itself excluded, counts 18 modules under
 Construction/Reflective.v and 31 under this file.

 WHAT IS DELIVERED.

 - [Reflective_of_UniversalArrows]: Mac Lane's "if" direction.  A full
 subcategory with a universal arrow to its inclusion at every object
 is reflective; the reflector and the adjunction are the two
 constructions of Theory/Universal/Arrow.v, unchanged.
 - [Reflective_of_UniversalArrows_obj]: the reflector sends x to the
 universal object [arrow_obj], at [eq_refl].
 - [Reflective_of_UniversalArrows_unit]: the unit at x is the
 universal arrow, up to [≈].
 - [Coreflective_of_CouniversalArrows]: the dual, Mac Lane's
 "dually" of the same page.  A full subcategory with a couniversal
 arrow from its inclusion at every object is coreflective; Theory/
 Universal/Arrow/Dual.v's [RightAdjointFunctorFromCouniversalArrows]
 and [AdjunctionFromCouniversalArrows] are fed, unchanged, to
 Construction/Reflective/Coreflective.v's covariant bridge
 [Coreflective_of_adjunction], which builds the op-typed record.
 - [Coreflective_of_CouniversalArrows_obj]: the coreflector, read back
 covariantly, sends x to the couniversal object [coarrow_obj], at
 [eq_refl]; [Coreflective_of_CouniversalArrows_counit]: the
 covariant counit at x is the couniversal arrow, up to [≈].

 STRENGTHS, MEASURED STRICT FIRST.  The object readback is [eq_refl].
 The unit is not: the adjunction's unit at x is its transpose of the
 identity, [fmap[Incl C S] id ∘ arrow], and over an abstract category
 the composite with an identity does not reduce.  An [Example] stating
 the unit [=] the arrow by [eq_refl] is refused with "cannot unify
 "unit" and "arrow"", pinned in Test/ProbeReflective370.v rather than
 here, where a negative probe line would add to [make todo].  Over a
 concrete category the composite does reduce POINTWISE, and
 Instance/Met/Uniform.v's [completionU_unit_pointwise] records that
 case at [eq_refl].  The dual is the same: the coreflector's object is
 [eq_refl], and the counit arrives as [coarrow ∘ fmap[Incl C S] id],
 the shape Dual.v's [counit_couniversal] closes up to [≈].

 UNIVERSES.  Read by [About] under [Set Printing Universes], the three
 reflective constants carry twelve universes each, the first two the
 binder's:

 Reflective_of_UniversalArrows@{o h u u0 u1 u2 u3 u4 u5 u6 u7 u8} :
 ∀ {C : Category@{o h h}} {S : Subcategory@{o h u8 h} C}, ...
 → Reflective@{u u0 u1 u2 o u8 h} S
 ( * ... |= h < u0, and non-strict bounds only * )

 The one strict bound, [h < u0], is [Reflective]'s own: [About
 Reflective] prints [u5 < u0] for its hom level [u5] and its second
 universe [u0], and the constant instantiates that record at
 [@{u u0 u1 u2 o u8 h}].  The three coreflective constants carry
 fifteen, fifteen and sixteen ([Coreflective_of_CouniversalArrows],
 its [_obj] and its [_counit]), with the same binder:

 Coreflective_of_CouniversalArrows@{o h u u0 … u11} :
 ∀ {C : Category@{o h h}} {S : Subcategory@{o h u11 h} C}, ...
 → Coreflective@{u u0 u1 u2 u3 u11 o h} S
 ( * ... |= h < u1, and non-strict bounds only * )

 and their one strict bound is [Coreflective]'s own: [About
 Coreflective] prints [u6 < u1] for its hom level [u6].  This file
 adds no bound, and no [Set] appears.

 NOT DELIVERED.

 - Mac Lane's "only if".  It holds, and it is one line over
 Adjunction/Representability.v's [adj_unit_universal]:
 [fun x => adj_unit_universal (reflective_adj R) x] is a universal
 arrow at every x, and feeding it back to
 [Reflective_of_UniversalArrows] returns R's reflector on objects at
 [eq_refl] (both measured in a scratch file, closed under the global
 context).  It is not stated here because that import adds 12
 modules to this file's closure (by the same [coqdep] count), among
 them the Yoneda development.
 - The "only if" of the coreflective dual: not stated either.
 - A couniversal readback of the arrow part of the coreflector: like
 the reflector's, it is [unique_obj] of Theory/Universal/Arrow.v's
 [Qed]-closed [ump_universal_arrows], read in the opposite
 categories. 

 --------
 nLab: https://ncatlab.org/nlab/show/reflective+subcategory
 nLab: https://ncatlab.org/nlab/show/universal+morphism
 书籍: Mac Lane, 《为工作数学家而作的范畴论》，第2版，GTM 5，第IV.3节，印刷版第91页（PDF第100页），以及印刷版第92页（PDF第101页）中#370收集的例子
 书籍: Riehl, 《上下文中的范畴论》，Dover 2016，第4.6节，定义4.6.12，印刷版第169页（PDF第189页）

 Mac Lane 在第91页定义了该概念，并在同一段落中通过通用箭头进行理解。摘自页面图片:当 B 的子类别 A 的包含函子 K: A → B 存在一个左伴随函子 F: B → A 时，A 称为 B 中的反射子类别……反射可以用泛箭头来描述：当且仅当对每个 b ∈ B 存在子类别 A 的一个对象 Rb 和一条箭头 η_b: b → Rb，使得每条箭头 g: b → a ∈ A 都可以表示为 g = f ∘ η_b，其中 f: Rb → a 在 A 中唯一时，A ⊂ B 是反射的。像往常一样，R 于是成为一个函子 B → B（取值在 A 中）的对象函数。 

 Riehl 的定义 4.6.12 是同一概念，即其包含函子拥有左伴随的满子类别，她称之为反射器或局部化；她的例子 4.6.13 列出了示例，其中第 (ii) 和 (iv) 项也在第 370 号问题中收集。在实践中，每一个具体的反射都是这样发现的：人们一次构造一个完成、阿贝尔化、标量扩张的对象，证明它的泛性质，然后才谈论函子。将逐点数据转化为伴随的通用定理已经存在于树中，如 Theory/Universal/Arrow.v 中的 [LeftAdjointFunctorFromUniversalArrows] 和 [AdjunctionFromUniversalArrows]；缺少的是从那里到 Construction/Reflective.v 的记录的这一步，而这一步正是这个文件实现的，同时还有其对偶实现到 coreflective 记录。它是一个卫星文件，而不是 Construction/Reflective.v 的一部分，因为它需要 Theory/Universal/Arrow.v，而那个文件不需要：[coqdep -R . Category] 在 [_CoqProject] 文件上的传递闭包（不包括该文件本身）在 Construction/Reflective.v 下计算为 18 个模块，而在该文件下计算为 31 个模块。

 交付内容是什么。- [Reflective_of_UniversalArrows]：Mac Lane 的“如果”方向。每个对象在其包含下都有一个通用箭头的完整子范畴是反射的；反射器和伴随是 Theory/Universal/Arrow.v 中的两个构造，未改变。 - [Reflective_of_UniversalArrows_obj]：反射器将 x 映射到 [arrow_obj] 的通用对象，在 [eq_refl] 处。 - [Reflective_of_UniversalArrows_unit]：x 处的单元是通用箭头，至 [≈] 为止。 - [Coreflective_of_CouniversalArrows]：对偶，Mac Lane 同页的“对偶地”。每个对象在其包含下都有一个共通箭头的完整子范畴是余反射的；Theory/Universal/Arrow/Dual.v 的 [RightAdjointFunctorFromCouniversalArrows] 和 [AdjunctionFromCouniversalArrows] 不变地输入 Construction/Reflective/Coreflective.v 的协变桥 [Coreflective_of_adjunction]，该桥构建 op 类型记录。-  [Coreflective_of_CouniversalArrows_obj]：余反射子，协变地读取，将 x 发送到余普遍对象 [coarrow_obj]，在 [eq_refl]；[Coreflective_of_CouniversalArrows_counit]：x 处的协变余单位是余普遍箭头，直到 [≈]。优势，严格首要测量。对象回读为 [eq_refl]。
 该单元不是：x 处的联结单元是它的恒等映射的转置，[fmap[Incl C S] id ∘ arrow]，并且在抽象范畴上与恒等映射的复合不会化简。一个 [Example] 声明单元 [=] 由 [eq_refl] 进行映射的箭头遭到拒绝，显示“无法统一 'unit' 和 'arrow'”，固定在 Test/ProbeReflective370.v 中，而不是这里，在这里一个负探针行会添加到 [make todo]。在具体范畴上，复合确实逐点化简，Instance/Met/Uniform.v 的 [completionU_unit_pointwise] 记录了 [eq_refl] 的情况。对偶情况相同：余反射器的对象是 [eq_refl]，余单元 arrives as [coarrow ∘ fmap[Incl C S] id]，Dual.v 的 [counit_couniversal] 的形状闭合为 [≈]。宇宙。由 [About] 在 [Set Printing Universes] 下阅读，三个反射常数各自承载十二个宇宙，前两个属于绑定器的：

 Reflective_of_UniversalArrows@{o h u u0 u1 u2 u3 u4 u5 u6 u7 u8} ：
 ∀ {C : Category@{o h h}} {S : Subcategory@{o h u8 h} C}, ...
 → Reflective@{u u0 u1 u2 o u8 h} S
 ( * ... |= h < u0，并且只限非严格界限 * )

 唯一严格界限 [h < u0] 是 [Reflective] 自身的：[关于 Reflective] 为其同构等级 [u5] 和其第二个宇宙 [u0] 打印 [u5 < u0]，并且该常数在 [@{u u0 u1 u2 o u8 h}] 实例化了该记录。三个余反射常数分别承载十五、十五和十六个（[Coreflective_of_CouniversalArrows]、其 [_obj] 和其 [_counit]），并使用相同的绑定器:Coreflective_of_CouniversalArrows@{o h u u0 … u11} ：
 ∀ {C : Category@{o h h}} {S : Subcategory@{o h u11 h} C}, …
 → Coreflective@{u u0 u1 u2 u3 u11 o h} S
 （* … |= h < u1，并且仅非严格界限 *）

 以及它们的一个严格界限是 [Coreflective] 自身的：[关于 Coreflective] 打印 [u6 < u1] 对应其同态等级 [u6]。此文件不添加任何界限，也没有出现 [Set]。

 未交付。- Mac Lane 的“只有当”。它成立，并且在 Adjunction/Representability.v 的 [adj_unit_universal] 上方仅一行：[fun x => adj_unit_universal (reflective_adj R) x] 是每个 x 上的一个普遍算子，将其反馈给 [Reflective_of_UniversalArrows] 会返回 R 在 [eq_refl] 上对象的反射器（都在一个临时文件中测量，在全局上下文下闭合）。这里没有说明，因为导入它会将 12 个模块添加到此文件的闭包中（按相同的 [coqdep] 计数），其中包括 Yoneda 的发展。  
 - 核反射对偶的“只有当”：也没有说明。  
 - 核反射器箭头部分的共普遍回读：像反射器一样，它是 Theory/Universal/Arrow.v 的 [Qed]-闭合 [ump_universal_arrows] 的 [unique_obj]，在相反的范畴中读取。
*)

(*
 Mac Lane §IV.3, printed p. 91: reflective when every object has a
 universal arrow to the inclusion. 

 --------
 Mac Lane §IV.3，第91页：当每个对象都有一个到包含的通用箭头时是反射性的。
*)
Definition Reflective_of_UniversalArrows@{o h +} {C : Category@{o h h}}
  {S : Subcategory C}
  (full : Construction.Subcategory.Full C S)
  (UA : ∀ x : C, UniversalArrow x (Incl C S)) : Reflective S :=
  @Build_Reflective C S full
    (LeftAdjointFunctorFromUniversalArrows (Incl C S) UA)
    (AdjunctionFromUniversalArrows (Incl C S) UA).

(* The reflection of x is the universal object, on the nose. / x的反射是普遍对象，正中要点。 *)
Example Reflective_of_UniversalArrows_obj@{o h +} {C : Category@{o h h}}
  {S : Subcategory C}
  (full : Construction.Subcategory.Full C S)
  (UA : ∀ x : C, UniversalArrow x (Incl C S)) (x : C) :
  fobj[reflector (Reflective_of_UniversalArrows full UA)] x
    = @arrow_obj C (Sub C S) x (Incl C S) (UA x) := eq_refl.

(*
 The unit is the universal arrow, up to [≈]: it arrives as the
 transpose of the identity, [fmap[Incl C S] id ∘ arrow]. 

 --------
 该单元是通用箭头，直到 [≈]：它作为单位的转置到达，[fmap[Incl C S] id ∘ 箭头。
*)
Lemma Reflective_of_UniversalArrows_unit@{o h +} {C : Category@{o h h}}
  {S : Subcategory C}
  (full : Construction.Subcategory.Full C S)
  (UA : ∀ x : C, UniversalArrow x (Incl C S)) (x : C) :
  @unit _ _ _ _ (reflective_adj (Reflective_of_UniversalArrows full UA)) x
    ≈ @arrow C (Sub C S) x (Incl C S) (UA x).
Proof. simpl. apply id_left. Qed.

(* * ** The dual: coreflective subcategories from couniversal arrows / * ** 对偶：来自余通箭的共反射子范畴 *)

(*
 Mac Lane §IV.3, printed p. 91, dually: coreflective when every object
 has a couniversal arrow from the inclusion.  Theory/Universal/Arrow/
 Dual.v assembles the right adjoint and the adjunction, and
 Construction/Reflective/Coreflective.v's covariant bridge packages
 them as the op-typed record. 

 --------
 麦克莱恩 §IV.3，第91页印刷，双重：当每个对象都有来自包含的反普遍箭头时是余反射的。Theory/Universal/Arrow/Dual.v 组装右伴随和伴随，而 Construction/Reflective/Coreflective.v 的协变桥将它们作为 op 类型记录封装。
*)
Definition Coreflective_of_CouniversalArrows@{o h +} {C : Category@{o h h}}
  {S : Subcategory C}
  (full : Construction.Subcategory.Full C S)
  (CA : ∀ x : C, CouniversalArrow x (Incl C S)) : Coreflective S :=
  Coreflective_of_adjunction full
    (RightAdjointFunctorFromCouniversalArrows (Incl C S) CA)
    (AdjunctionFromCouniversalArrows (Incl C S) CA).

(* The coreflection of x is the couniversal object, on the nose. / x 的余反射是共普遍对象，正是如此。 *)
Example Coreflective_of_CouniversalArrows_obj@{o h +}
  {C : Category@{o h h}} {S : Subcategory C}
  (full : Construction.Subcategory.Full C S)
  (CA : ∀ x : C, CouniversalArrow x (Incl C S)) (x : C) :
  fobj[coreflector (Coreflective_of_CouniversalArrows full CA)] x
    = @coarrow_obj C (Sub C S) x (Incl C S) (CA x) := eq_refl.

(* The covariant counit is the couniversal arrow, up to [≈]: it arrives as [coarrow ∘ fmap[Incl C S] id], Dual.v's [counit_couniversal]. / 协变余单元是余普遍箭，直到 [≈] ：它作为 [coarrow ∘ fmap[Incl C S] id]，Dual.v 的 [counit_couniversal] 到达。 *)
Lemma Coreflective_of_CouniversalArrows_counit@{o h +}
  {C : Category@{o h h}} {S : Subcategory C}
  (full : Construction.Subcategory.Full C S)
  (CA : ∀ x : C, CouniversalArrow x (Incl C S)) (x : C) :
  @counit _ _ _ _
    (coreflective_adj (Coreflective_of_CouniversalArrows full CA)) x
    ≈ @coarrow C (Sub C S) x (Incl C S) (CA x).
Proof. exact (counit_couniversal (Incl C S) CA x). Qed.
