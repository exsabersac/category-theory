Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.Product.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Discrete.

Generalizable All Variables.

(** * [Sets] is complete / * [Sets] 已完成 *)

(*
 nLab:      https://ncatlab.org/nlab/show/complete+category
 Wikipedia: https://en.wikipedia.org/wiki/Complete_category

 [Complete C] is [∀ (D : Category) (F : D ⟶ C), Limit F]
 (Structure/Complete.v): an oracle assigning a chosen limit to every
 diagram.  This file inhabits it at [Sets].

 THE CONSTRUCTION

 The limit of [F : D ⟶ Sets] is the setoid of COMPATIBLE FAMILIES: elements
 of the indexed product of the [F d] whose components agree along every
 arrow of [D],

 [{ x : ∀ d : D, F d & ∀ d d' (f : d ~> d'), fmap[F] f (x d) ≈ x d' }],

 with two such identified when the underlying families agree pointwise.
 The legs are evaluation at [d]; the cone coherence IS the compatibility
 constraint; the mediator out of a competing cone [N] bundles [N]'s legs at
 a point, its compatibility being [N]'s own cone coherence read at that
 point; commuting is [reflexivity] and uniqueness is the symmetry of the
 competing map's commuting equations.

 The first component is literally an element of
 [Sets_iprod_obj (fun d : D => F d)], the dependent-function setoid of
 Instance/Sets/Products.v, so the classical recipe -- a limit is the part of
 the product of all [F d] that is compatible along every arrow -- is
 realised with the product supplied by this issue's other deliverable and
 the compatibility cut performed inline.

 HOW THIS IS *NOT* PROVED, STATED PLAINLY

 It is NOT routed through the standard reduction “a category with all small
 products and equalizers has all small limits”.  That theorem does not exist
 in this development (CORRECTION (#458): since #416 it does,
 Structure/Limit/FromProducts.v's [Complete_from_products_equalizers],
 which this constant is still not routed through and which
 Instance/Top/Complete.v's [PTop_Complete_via_products] consumes at
 [PTopCat]): [Complete_HasEqualizers] (Adjunction/GAFT.v) runs
 the other way, deriving equalizers FROM completeness -- it is applied to
 this very constant, as [Sets_HasEqualizers] in Adjunction/GAFT/Sets.v --
 and no constant here builds a limit out of two products and an equalizer.
 What is written above is a direct construction; the resemblance to the
 reduction is real but informal, and the equalizer step is done by carrying
 a proof alongside the family rather than by invoking [HasEqualizers].  The
 description at
 Structure/Limit.v, “a limit is the part of the product of all F x
 whose components are compatible along every arrow of J, exactly the shape
 of the funext-free end of Instance/Sets/End.v”, is the shape this file
 follows; Instance/Sets/End.v is its closest in-tree relative.

 SMALLNESS

 [Complete@{u u0 u1 u2}] abbreviates
 [λ C : Category@{u2 u1 u1}, ∀ (D : Category@{u0 u1 u1}) (F : D ⟶ C),
 Limit F], so the diagram category's HOM universe is already forced to
 coincide with [C]'s -- the fact recorded at Adjunction/SAFT.v -- and
 its OBJECT universe [u0] is a separate parameter.  [About Sets_Complete]
 prints

 Sets_Complete@{u u0} : Complete@{u u u u0}      ( * with u < u0 * )

 so, writing [Sets@{o so}] as Instance/Sets.v does, [u] is [o] -- the
 universe of the CARRIERS of [Sets]' objects, and of its homs -- and [u0] is
 [so], where [obj[Sets]] itself lives.  The diagram category is
 [Category@{u u u}], i.e. BOTH its objects and its homs live at [o],
 strictly below [obj[Sets]].  That is the smallness side condition, and it
 is exactly what the construction needs: the compatible-family carrier
 quantifies over the objects and arrows of [D], so it fits as a [Sets]
 carrier when both sit at [o].  This is the universe-polymorphic stand-in
 for “D small relative to C” that Structure/Complete.v describes.

 WHAT THIS UNLOCKS, AND WHAT IT DOES NOT

 [Complete] is the standing hypothesis of the adjoint functor theorems
 (Adjunction/GAFT.v, Adjunction/SAFT.v) and of [Comma_Complete]
 (Construction/Comma/Limit.v).  Before this file no [Complete] or
 [Cocomplete] instance existed anywhere in the tree, and that absence was
 the last one standing between [GAFT] and an actual application: its other
 two premises were already reachable, [PreservesImageLimit] through
 [right_adjoint_PreservesImageLimit] (Construction/Comma/Limit.v, which
 covers every right adjoint) and [SolutionSet] by direct construction.
 Adjunction/GAFT/Sets.v now assembles all three and runs [GAFT] at
 [Id : Sets ⟶ Sets], and docs/INHABITATION.md lists the result among the
 witnessed ones on that basis.  Nothing in this file changes any statement
 of GAFT or SAFT; it supplies an inhabitant of one of their hypotheses.

 Two things that inhabitant does NOT do.  [GAFT]'s frozen universe context
 pins the applying instance to [Sets@{Set _}] (disclosed in the header of
 Adjunction/GAFT/Sets.v), and the functor applied to is [Id], so the
 adjoint produced is [Id] again.  (CORRECTION, #451: the first clause is
 stale.  Adjunction/GAFT/Sets.v's header records that the [Set] pin was a
 minimization artifact of Instance/Discrete.v's unannotated
 [DiscreteCat_Functor] and was lifted when that donor was annotated
 (2026-09-17): [GAFT_at_Sets_Id] now reads back at the polymorphic
 [Sets@{u0 u}].  The second clause stands.)  The application demonstrates
 that the premises are simultaneously satisfiable in-tree; it does not
 produce a new adjunction.  [SAFT] is applied only by #437's
 [saft_representable], and conditionally: it wants a [Cogenerator], a
 [SubobjectIndex] and a [SubobjectCover] besides, and none of the three
 has an in-tree inhabitant.  (CORRECTION, #451: [SubobjectIndex] has
 in-tree inhabitants at every object of every category -- Adjunction/
 SAFT.v's [empty_SubobjectIndex], and Adjunction/SAFT/WellPowered.v's
 [WellPowered_SubobjectIndex] over any well-powered witness, such as
 Instance/Sets/WellPowered.v's [Sets_WellPowered_untruncate] under its
 [Untruncate] hypothesis -- and [SubobjectCover] is REFUTED at the
 identity of [Sets] by Adjunction/SAFT/Sets.v's
 [SubobjectCover_Id_Sets_absurd].)  (CORRECTION, #452: the
 [Cogenerator] clause no longer holds either.  Instance/Sets/
 Cogenerator.v builds two small cogenerators of [Sets], under
 [Untruncate] or [IEM] ([Sets_Cogenerator_untruncate],
 [Sets_Cogenerator_IEM]), and an unconditional large one
 ([Sets_Cogenerator_large], which [cogen_prod] at [Sets_Complete]
 refuses on universes); Instance/Sets/SpecialInitial.v's [setsop_cog]
 is one of [Sets^op], unconditionally; and Adjunction/SAFT/
 InitialObject/Examples.v builds them at the thin categories
 [Subsets X] and [Indiscrete].  Under one [U : Untruncate] every
 premise of [SAFT] at [Id[Sets]] but [SubobjectCover] is therefore
 inhabited, as Adjunction/SAFT.v's header records.  Separately,
 “applied only by [saft_representable]” has not held since #451:
 Adjunction/SAFT/WellPowered.v's [SAFT_of_WellPowered] applies [SAFT]
 too, as conditionally.)

 [Cocomplete Sets] is not provided BY THIS FILE.  It is NOT missing from
 the tree, correcting what this sentence used to say: Instance/Sets/
 Cocomplete.v's [Sets_Cocomplete] is exactly the quotient of the
 disjoint union this paragraph once called unattempted.

 STATUS: axiom-free.  [Print Assumptions Sets_Complete] reports “Closed
 under the global context”; the Makefile's [print-assumptions] target
 audits it. 

 --------
 nLab：       https://ncatlab.org/nlab/show/complete+category 
 维基百科：  https://en.wikipedia.org/wiki/Complete_category 

 [Complete C] 是  [∀ (D : Category) (F : D ⟶ C), Limit F] 
 （Structure/Complete.v）：一个为每个图分配所选极限的预言器。这个文件在 [Sets] 中包含它。

 构造方法

 [F : D ⟶ Sets] 的极限是 COMPATIBLE FAMILIES 的集合：[F d] 的索引积中的元素，其分量在 [D] 的每条箭头上都一致，

 [{ x : ∀ d : D, F d & ∀ d d' (f : d ~> d'), fmap[F]  f (x d) ≈ x d' }],当基础家族在每一点上都一致时，有两个这样的被识别出来。
 腿是对 [d] 的求值；锥体相干性就是兼容性约束；竞争锥 [N] 的媒介在一点上捆绑了 [N] 的腿，其兼容性是在该点读取 [N] 自身锥体相干性；交换性是 [reflexivity]，唯一性是竞争映射交换方程的对称性。

 第一个组成部分字面上是 [Sets_iprod_obj (fun d : D => F d)] 的一个元素，即 Instance/Sets/Products.v 的依赖函数集体，所以经典方法——极限是兼容于每个箭头的所有 [F d] 的乘积部分——通过本期其他交付提供的乘积实现，并在内联中执行兼容性裁剪。这*没有*被证明，直言不讳地说它没有通过标准的约简“一个具有所有小积和等化器的范畴具有所有小极限”。该定理在此发展中不存在（更正 (#458)：自 #416 起，它确实存在，Structure/Limit/FromProducts.v 的 [Complete_from_products_equalizers] ，而此常量仍未通过它，并且 Instance/Top/Complete.v 的 [PTop_Complete_via_products] 在 [PTopCat] 被使用）：[Complete_HasEqualizers]（Adjunction/GAFT.v）以相反的方式运行，从完备性推导等化器——它正是应用于此常量，如 Adjunction/GAFT/Sets.v 中的 [Sets_HasEqualizers]——并且这里没有任何常量是通过两个积和一个等化器构建极限的。上面写的内容是直接构造；它与约化的相似性是真实的，但非正式的，并且均衡器步骤是通过在族旁边携带一个证明来完成的，而不是通过调用 [HasEqualizers]。Structure/Limit.v 中的描述，“极限是所有 F x 的积中，其分量沿 J 的每个箭头都是兼容的部分，正好是 Instance/Sets/End.v 的 funext-free end 的形状”，就是该文件遵循的形状；Instance/Sets/End.v 是其在树中最接近的相关文件。

 小性[Complete@{u u0 u1 u2}] 缩写为
 [λ C : Category@{u2 u1 u1}, ∀ (D : Category@{u0 u1 u1}) (F : D ⟶ C),
 Limit F]，因此图形范畴的 HOM 宇宙已经被迫与 [C] 的宇宙一致——这个事实记载在 Adjunction/SAFT.v ——而它的 OBJECT 宇宙 [u0] 是一个独立的参数。 [About Sets_Complete] 打印

 Sets_Complete@{u u0} : Complete@{u u u u0}      ( * 其中 u < u0 * )所以，把 [Sets@{o so}] 写作 Instance/Sets.v 中那样，[u] 是 [o] —— [Sets] 对象及其态射的载体宇宙 —— 而 [u0] 是 [so]，其中 [obj[Sets] 自身存在。图范畴是 [Category@{u u u}]，即它的对象和态射都存在于 [o]，严格位于 [obj[Sets] 之下。这就是小性侧条件，这正是构造所需要的：兼容族载体在 [D] 的对象和箭头上量化，因此当两者都位于 [o] 时，它适合作为 [Sets] 载体。这是 Structure/Complete.v 描述的“相对于 C 的 D 小”的宇宙多态替代。

 这开启了什么，以及它不能做什么[Complete] 是伴随函子定理（Adjunction/GAFT.v，Adjunction/SAFT.v）以及 [Comma_Complete]（Construction/Comma/Limit.v）的固定假设。在这个文件之前，树中任何地方都不存在 [Complete] 或 [Cocomplete] 实例，而这种缺失正是 [GAFT] 与实际应用之间的最后障碍：它的另外两个前提已经可以到达，[PreservesImageLimit] 通过 [right_adjoint_PreservesImageLimit]（Construction/Comma/Limit.v，涵盖了所有右伴随）和 [SolutionSet] 通过直接构造。Adjunction/GAFT/Sets.v 现在将三者组合并在 [Id : Sets ⟶ Sets] 上运行 [GAFT]，docs/INHABITATION.md 也在此基础上将结果列为已实例化的。在这个文件中没有改变 GAFT 或 SAFT 的任何命题；它提供了它们假设之一的一个实例。居民不会做的两件事。[GAFT] 的冻结宇宙上下文将应用实例固定在 [Sets@{Set _}]（在 Adjunction/GAFT/Sets.v 的头部中披露），并且应用的函子是 [Id]，因此产生的伴随又是 [Id]。（更正，#451：第一条子句已过时。Adjunction/GAFT/Sets.v 的头部记录了 [Set] 的固定是 Instance/Discrete.v 中未注释的 [DiscreteCat_Functor] 的一种最小化产物，当该供体被注释时被提取（2026-09-17）：[GAFT_at_Sets_Id] 现在在多态的 [Sets@{u0 u}] 上回读。第二条子句仍然有效。）该应用演示了前提在树中同时可满足；它不会生成新的伴随。[SAFT] 仅由 #437 的 [saft_representable] 应用，并且有条件地：它还需要一个 [Cogenerator]、一个 [SubobjectIndex] 和一个 [SubobjectCover]，并且这三者中没有一个有树内（in-tree）的元素。（更正，#451：[SubobjectIndex] 在每个类别的每个对象上都有树内元素——Adjunction/SAFT.v 的 [empty_SubobjectIndex]，以及 Adjunction/SAFT/WellPowered.v 在任何良幂（well-powered）证明对象上的 [WellPowered_SubobjectIndex]，例如 Instance/Sets/WellPowered.v 的 [Sets_WellPowered_untruncate] 在其 [Untruncate] 假设下——并且 [SubobjectCover] 在 [Sets] 的恒等上被 Adjunction/SAFT/Sets.v 的 [SubobjectCover_Id_Sets_absurd] 反驳。） （更正，#452：[Cogenerator] 子句也不再成立。实例/集合/
 Cogenerator.v 构建了两个小型 [Sets] 的协生成器，位于
 [Untruncate] 或 [IEM] 下（[Sets_Cogenerator_untruncate]，
 [Sets_Cogenerator_IEM]），以及一个无条件的大协生成器
 （[Sets_Cogenerator_large]，[cogen_prod] 在 [Sets_Complete] 上
 在宇宙中被拒绝）；实例/集合/SpecialInitial.v 的 [setsop_cog]
 是 [Sets^op] 之一，无条件；而 Adjunction/SAFT/
 InitialObject/Examples.v 在薄范畴 [Subsets X] 和 [Indiscrete] 上构建它们。在一个 [U : Untruncate] 下，[Id[Sets] 上 [SAFT] 的每个前提都是有效的，但 [SubobjectCover] 因此是可居住的，正如 Adjunction/SAFT.v 的标题所记录的。另行说明，“仅由 [saft_representable] 应用”自 #451 以来不再成立：Adjunction/SAFT/WellPowered.v 的 [SAFT_of_WellPowered] 也有条件地应用 [SAFT]。[Cocomplete Sets] 并未由此文件提供。它并未从树中缺失，更正这句话曾经说过的内容：Instance/Sets/Cocomplete.v 的 [Sets_Cocomplete] 恰好是本段曾称为未尝试的离散并集的商。

 状态：无公理。[Print Assumptions Sets_Complete] 报告“在全局上下文下封闭”；Makefile 的 [print-assumptions] 目标会对此进行审核。
*)

#[local] Obligation Tactic := idtac.

Section SetsLimit.

Context {D : Category}.
Context (F : D ⟶ Sets).

(* The compatibility constraint cutting the limit out of the indexed product of the [F d]: a family is compatible when its components agree along every arrow of [D]. / 当索引积的兼容性约束被切割时，[F d] : 家族是兼容的，当且仅当其分量在 [D] 的每个箭头上都一致。 *)
Definition Sets_limit_compatible (x : Sets_iprod_obj (fun d : D => F d)) :
  Type :=
  ∀ (d d' : D) (f : d ~{D}~> d'), fmap[F] f (x d) ≈ x d'.

(*
 The limit carrier: the compatible families, a sub-setoid of the carrier of
 [indexed_product (fun d => F d)] as constructed in Instance/Sets/Products.v.
 The constraint is carried alongside the family rather than quotiented away,
 so no quotient type and no [funext] is involved. 

 --------
 极限承载体：兼容的族，是在 Instance/Sets/Products.v 中构造的 [indexed_product (fun d => F d)] 承载体的一个子子集体。约束随族一起携带，而不是被商化，因此不涉及商类型，也不涉及 [funext]。
*)
Definition Sets_limit_carrier : Type :=
  { x : Sets_iprod_obj (fun d : D => F d) & Sets_limit_compatible x }.

(* Two compatible families are identified when the underlying families are: the constraint witness plays no part, exactly as in Instance/Sets/End.v. / 当基础族是以下情况时，识别出两个兼容族：约束证明不参与，就像在 Instance/Sets/End.v 中一样。 *)
Definition Sets_limit_equiv : crelation Sets_limit_carrier :=
  fun p q => `1 p ≈ `1 q.

Program Definition Sets_limit_obj : SetoidObject := {|
  carrier   := Sets_limit_carrier;
  is_setoid := {| equiv := Sets_limit_equiv |}
|}.
Next Obligation.
  constructor.
  - intros p d; reflexivity.
  - intros p q Hpq d; symmetry; exact (Hpq d).
  - intros p q r Hpq Hqr d; transitivity (`1 q d);
    [exact (Hpq d)|exact (Hqr d)].
Qed.

(* The leg at [d]: evaluate a compatible family at [d]. / 在 [d] 处的腿：在 [d] 处评估一个兼容族。 *)
Program Definition Sets_limit_leg (d : D) : Sets_limit_obj ~{Sets}~> F d := {|
  morphism := fun p => `1 p d
|}.
Next Obligation. intros d p q Hpq; exact (Hpq d). Qed.

(* The limit cone. Its coherence condition is precisely the compatibility constraint carried by each family. / 极限锥。它的相干性条件正是由每个族所携带的兼容性约束。 *)
Program Definition Sets_limit_cone : Cone F := {|
  vertex_obj := Sets_limit_obj;
  coneFrom   := {| vertex_map := Sets_limit_leg |}
|}.
Next Obligation. intros d d' f p; exact (`2 p d d' f). Qed.

(* The mediator out of a competing cone [N]: bundle the legs of [N] at a point [e] into a family, whose compatibility is [N]'s own cone coherence read at [e]. / 将来自竞争锥 [N] 的中介者：在点 [e] 将 [N] 的腿捆绑成一个族，其兼容性为 [N] 在 [e] 读取的自身锥一致性。 *)
Program Definition Sets_limit_med (N : Cone F) :
  vertex_obj[N] ~{Sets}~> Sets_limit_obj := {|
  morphism := fun e =>
    (fun d => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) d e;
     fun d d' f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) d d' f e)
|}.
Next Obligation.
  intros N e e' Hee' d.
  exact (proper_morphism (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) d) e e' Hee').
Qed.

Program Definition Sets_Limit : Limit F := {|
  limit_cone := Sets_limit_cone;
  ump_limits := fun N => {| unique_obj := Sets_limit_med N |}
|}.
Next Obligation. intros N d e; reflexivity. Qed.
Next Obligation. intros N v Hv e d; symmetry; exact (Hv d e). Qed.

End SetsLimit.

(*
 [Sets] is complete: every diagram of every shape has a limit.  See the
 header for the smallness discipline recorded on the universe context of
 this constant. 

 --------
 [Sets] 是完整的：每种形状的每个图都有一个极限。请参阅此常量的范畴上下文中记录的小巧性学科的标题。
*)
Definition Sets_Complete : @Complete Sets := fun D F => Sets_Limit F.

(* * * Mac Lane's cone-set construction / * * 马克·莱恩的圆锥集构造 *)

(*
 Mac Lane, _Categories for the Working Mathematician_, 2nd ed. (GTM 5),
 SV.1 Theorem 1 and the remark following it, printed p. 110 (PDF p. 119);
 item ids [maclane:V.1:thm1], [maclane:V.1:remark1].  Riehl, _Category
 Theory in Context_, 2nd ed., SS3.2 Definition 3.2.3 and Theorem 3.2.4,
 printed pp. 93-94.  Quoted from the rendered page, not from the OCR
 layer, which renders the cone letter nu as “Ii”.  ONE DEPARTURE FROM THE
 PAGE, forced by the lexer and disclosed rather than silent: the book
 writes the one point set as [*], so its “Cone” of that argument is
 spelled with an open paren immediately followed by a star -- which is
 exactly Coq's nested-comment opener.  Every quotation below therefore
 reads [Cone ( *, F)], with a space the book does not have.  Nothing else
 is altered.

 “Theorem 1 (Completeness of Set).  If the category J is small, any
 functor F : J-->Set has a limit which is the set Cone ( *, F) of all
 cones sigma : *-->F from the one point set * to F, while the limiting
 cone v, with

 v_j : Cone ( *, F) --> F_j,     sigma |--> sigma_j,          (2)

 is for each j that function sending each cone sigma to the element
 sigma_j in F_j.”

 and, on the same page, the sentence this file's discrete section
 discharges:

 “For example, if J is discrete, the set Cone( *, F) of J-cones is just
 the cartesian product Pi_j F_j.”

 WHAT IS DELIVERED HERE, AND WHY IT SITS BESIDE THE EXISTING PROOF

 The construction above this comment builds the limit as the setoid of
 COMPATIBLE FAMILIES.  Mac Lane builds it as the SET OF CONES from the one
 point set.  Both are limits of the same diagram, so they are canonically
 isomorphic, and neither is a re-derivation of the other: they are
 different objects.  This section adds Mac Lane's, and does not replace
 [Sets_Limit] or [Sets_Complete].  Three reasons, each measured.  First,
 [Sets_Complete] has code consumers (Adjunction/GAFT/Sets.v,
 Adjunction/Diagonal/Limit.v, Test/ProbeCocomplete329.v).  Second,
 Instance/Sets/Pullback.v's header asserts that the derived pullback apex
 “IS, on the nose, the setoid of COMPATIBLE FAMILIES” and quotes an
 accepted [eq_refl] fragment about it; redefining [Sets_Limit] would make
 that prose false without breaking any build.  Third, the two apexes are
 NOT convertible -- one is a sigma of a dependent function with a
 compatibility witness, the other an [ACone] record -- so there is
 something to compare, and the comparison is the deliverable.  It is
 [cone_apex_iso] in the sibling Instance/Sets/Cone.v, which also carries
 the remark's natural bijection; see that file's header for why the
 comparison could not live here (it costs one module of closure, and this
 file's is held fixed).

 THE APEX IS THE CONE PRESHEAF AT THE TERMINAL SETOID

 [cone_apex F] is [fobj[ConePresheaf F] 1] -- Structure/Cone.v's
 presheaf, applied at [Sets]' terminal object -- and not a re-derived
 copy.  Both of its fields are pinned by [eq_refl] below: its carrier is
 [ACone 1 F] and its setoid is [AConeEquiv 1 F].  Since [AConeEquiv]
 compares two cones by their legs and ignores the coherence proof, the
 apex is the set of Mac Lane's [sigma] with his own identification.

 THE LEGS ARE EVALUATION, AND THE PROOF SPENDS THE SINGLETON EXACTLY ONCE

 [cone_leg_at d] is display (2): it sends a cone [p] to the element
 [vertex_map p d ttt].  Its ONE obligation, and the one [cone_set_acone]
 beside it raises, are read off the argument:
 respectfulness is [AConeEquiv]'s own hypothesis at [d] and [ttt], and the
 cone coherence of [cone_set_acone] is the argument cone's own coherence
 read at [ttt].  Neither is [reflexivity]; the coherence in particular is
 not definitional.

 The mediator [cone_set_med N] is Mac Lane's [h]: it sends [e] to the cone
 [tau e].  Commuting is [reflexivity] -- the leg of [cone_set_med N e] at
 [d] evaluated at the point IS [vertex_map N d e].  UNIQUENESS is the one
 place the singleton's unique-inhabitant property is spent, in a single
 [destruct u]: [poly_unit] (Lib/Setoid.v) is an inductive with no eta,
 so a variable [u : poly_unit] is not definitionally [ttt].  That
 [destruct] IS Riehl's “restricting along each element regarded as a map
 out of the singleton”.  It is essential and not cosmetic: without it the
 goal is not closed by [symmetry; exact (Hv d e)].

 No choice principle and no extensionality: the cone type carries its
 coherence as data, as the compatible-family type above carries its
 compatibility.

 SMALLNESS, AND THE UNIVERSE COMPARISON

 [About] prints, for the two completeness witnesses side by side,

 ConeSet_Complete@{u u0} : Complete@{u u u u0}     ( * u < u0 * )
 Sets_Complete@{u u0}    : Complete@{u u u u0}     ( * u < u0 * )

 -- the same number of universes, the same binder, the same instance, and
 the same smallness side condition the header above records for
 [Sets_Complete].  Neither is more general than the other.  The blocks
 differ only in WHICH stdlib constants they cite: this one goes through
 [Sets_Terminal] and cites [eq_ind] and friends, the existing one goes
 through [sigT] and cites [Projections].

 THE DISCRETE SPECIAL CASE

 Mac Lane's own sentence, quoted above.  It is delivered against the
 compatible-family apex, whose relation to the indexed product of
 Instance/Sets/Products.v is the direct one: the three [eq_refl] Examples
 record that the limit apex IS [Sets_limit_obj] of the discrete diagram,
 that the product setoid it is cut out of IS literally [Sets_iprod_obj f],
 and that the limit legs ARE the indexed-product projections.

 THE STRENGTH IS AN ISOMORPHISM AND NOT AN EQUALITY, and the reason is not
 universes.  [Sets_limit_compatible] at a discrete shape unfolds to
 [∀ d d' (e : d = d'), fmap[F] e (x d) ≈ x d'], which is a genuine
 Pi-type, not [unit]: it is INHABITED for every family
 ([discrete_compatible], by [destruct e]) but it is not vacuous AS A TYPE.
 So the limit carrier is a sigma and the product carrier is the bare
 family, and they are different types.  The [eq_refl] form of the leg
 equation is refused at CONVERSION and is pinned in
 Test/ProbeConeSets407.v.

 [Structure/Limit/Product/Finite.v]'s [iprod_unique_iso] would give
 the same isomorphism in one term, since both sides are indexed products.
 It is deliberately NOT used: requiring that module costs this file
 twenty-one further modules of closure for twelve lines, against
 thirty-one hand-built at zero.  It is cited here rather than consumed.

 A UNIVERSE PIN, DISCLOSED -- AND IT REACHES FOUR OF THE TEN CONSTANTS,
 NOT THE SECTION.  The discrete section is written with [{A : Set}], and
 an earlier revision of this paragraph said the whole section forced it.
 Measured, by restating the section at [{A : Type}] and compiling: SIX
 constants are ACCEPTED there, the headline [discrete_iprod_iso] among
 them, along with [discrete_limit], [discrete_inner_is_iprod],
 [discrete_compatible], [discrete_forget] and [discrete_pair].  Exactly
 FOUR are refused -- [discrete_apex_is_limit_obj],
 [discrete_leg_is_proj], [discrete_iprod_iso_leg] and
 [discrete_iprod_iso_leg_inv] -- and they are exactly the four whose
 statements name Structure/Limit/Product.v's [iprod] or [iprod_proj],
 THREE of them rejected with “cannot ensure that Type is a subtype of
 Set”; the fourth, [discrete_iprod_iso_leg_inv], instead gives a plain
 unification MISMATCH (“expected to have type ?y ~{?Category}~> ?z”)
 carrying NO word-bounded [Set] at all -- a different KIND of refusal
 under this development's own taxonomy, measured by restating the six
 accepted constants at [Type] and adding each refused one alone.  An
 earlier revision of this sentence said all four were alike.

 THE MECHANISM, AND A RECORDED CORRECTION: IT IS GONE.  An earlier
 revision explained the four refusals like this: “[iprod@{u u0 u1}] is
 declared over [C : Category@{u1 Set Set}], pinning the ambient hom and
 proof universes to the literal [Set], and at [C := Sets@{o so} :
 Category@{so o o}] that collapses [Sets]' CARRIER universe [o] to
 [Set], after which [Sets_iprod_obj]'s [u <= u0] bound carries the index
 down too.  [iprod]'s own pin is visible in its printed type
 ([Limit@{u u Set u1} (DiscreteCat_Functor@{u u1 u0 Set} f)]) and takes
 BOTH donors -- [Cone] alone is accepted at levels declared apart, so it
 is the discriminating control -- with both pinned in the probe.”  The
 attribution was right and the donor has been repaired:
 [DiscreteCat_Functor] was annotated in place at Instance/Discrete.v
 in the PR “algebraic carriers are sets” (2026-09-17).  Measured after
 it, [iprod] is declared over [C : Category@{u1 u2 u2}] with no literal
 [Set], and applying it AT [Sets@{o so}] TO A [Type@{o}]-INDEXED FAMILY
 is ACCEPTED, reading
 [Limit@{o o o so} (DiscreteCat_Functor@{o o o so o o so} f) →
 obj[Sets@{o so}]] with [o < so].

 The section below is nevertheless still written uniformly at [{A : Set}],
 so that the four readbacks apply to the same [f] as the isomorphism they
 read back.  That binder is now a CHOICE, not a pin: whether the four
 [iprod]-naming constants can be restated at [{A : Type}] has NOT been
 re-measured, because the PR that removed the pin changed prose only.
 The core section above carries no [Set] at all, then or now.

 These definitions are stated at top level rather than in a [Section]
 because a section [Context] fixes its universes once, before the pin can
 propagate, and the discrete diagram is then refused inside it.

 STATUS: axiom-free.  [Print Assumptions] reports “Closed under the global
 context” for every constant below; the Makefile's [print-assumptions]
 target audits them by fully qualified name. 

 --------
 Mac Lane，《为工作中的数学家准备的范畴》，第2版 (GTM 5)，SV.1 定理1及其后的备注，印刷页110（PDF页119）；项目ID [maclane:V.1:thm1], [maclane:V.1:remark1]。Riehl，《上下文中的范畴论》，第2版，SS3.2 定义3.2.3和定理3.2.4，印刷页93-94。引用自渲染后的页面，而非OCR层，OCR将锥的字母nu显示为“Ii”。唯一一次偏离页面规范，由词法分析器强制且已披露而非省略：书中将单点集合写作[*]，因此其论证的“Cone”中括号紧跟星号——这正是Coq的嵌套注释起始标记。因此下面的每个引用都读作[Cone ( *, F)]，书中没有空格。其他内容均未更改。定理 1（集合的完备性）。如果范畴 J 是小范畴，则任何函子 F : J-->Set 都有一个极限，该极限就是从单点集合 * 到 F 的所有锥 sigma : *-->F 构成的集合 Cone( *, F)，而极限锥 v，其定义为

 v_j : Cone( *, F) --> F_j,     sigma |--> sigma_j,          (2)

 对于每一个 j，是将每个锥 sigma 映射到 F_j 中元素 sigma_j 的函数。

 同页，该文件离散部分指出的句子：

 例如，如果 J 是离散的，J-锥的集合 Cone( *, F) 就是笛卡尔积 Pi_j F_j。

 这里交付的内容是什么，以及为什么它与现有的证明并列。上述评论中的构造将极限构建为兼容族的集合。Mac Lane 将其构建为一个单点集合的圆锥集合。它们都是同一图的极限，因此它们在范畴上是同构的，而且彼此都不是从对方重新推导的：它们是不同的对象。本节添加了 Mac Lane 的构造，并不替代 [Sets_Limit] 或 [Sets_Complete]。有三个理由，每个理由都有衡量。首先，[Sets_Complete] 有代码使用者（Adjunction/GAFT/Sets.v、Adjunction/Diagonal/Limit.v、Test/ProbeCocomplete329.v）。第二，Instance/Sets/Pullback.v 的头部声明派生的拉回顶点“确切地说，是兼容族的集合”，并引用了关于它的已接受的 [eq_refl] 片段；重新定义 [Sets_Limit] 会使那段文字不正确，但不会破坏任何构建。第三，这两个顶点不可互换——一个是带有兼容性证明的依赖函数的 sigma，另一个是 [ACone] 记录——所以有东西可以比较，而比较结果是可交付的。在兄弟文件 Instance/Sets/Cone.v 中是 [cone_apex_iso]，它也包含备注中的自然双射；参见该文件的头部，了解为什么比较不能放在这里（它会消耗一个闭包模块，而这个文件的闭包是固定的）。

 顶点是终端集合同态下的圆锥预层[cone_apex F] 是 [fobj[ConePresheaf F] 1] -- Structure/Cone.v 的 presheaf，在 [Sets] 的终对象上应用 -- 而不是重新导出的副本。它的两个字段都由下面的 [eq_refl] 固定：它的载体是 [ACone 1 F]，其 setoid 是 [AConeEquiv 1 F]。由于 [AConeEquiv] 通过它们的腿比较两个圆锥，并忽略一致性证明，因此顶点是 Mac Lane 的 [sigma] 与他自己的标识集合。

 腿是求值，该证明在单元素上恰好使用一次[cone_leg_at d] 是显示（2）：它向元件 [vertex_map p d ttt] 发送了一个圆锥 [p]。它的唯一义务，以及旁边的 [cone_set_acone] 所引起的义务，是通过论证读出来的：尊重是 [AConeEquiv] 在 [d] 和 [ttt] 上自身的假设，而 [cone_set_acone] 的圆锥一致性是论证圆锥自身在 [ttt] 上的统一性。两者都不是 [reflexivity]；特别是这种一致性不是定义性的。调解者 [cone_set_med N] 是 Mac Lane 的 [h]：它将 [e] 发送到锥 [tau e]。交换性是 [reflexivity] —— [cone_set_med N e] 在 [d] 的分支在该点的值是 [vertex_map N d e]。唯一性是单例的唯一存在属性被使用的唯一地方，在单一的 [destruct u] 中：[poly_unit]（Lib/Setoid.v）是一个没有 eta 的归纳类型，所以变量 [u : poly_unit] 在定义上不是 [ttt]。[destruct] 是 Riehl 的“沿每个元素作为从单例映射的映射进行限制”。这是本质的而非装饰性的：没有它，目标无法通过 [symmetry; exact (Hv d e)] 闭合。  

 没有选择公理，也没有外延性：锥类型将其相干性作为数据携带，就像上面的兼容族类型携带其兼容性一样。  

 小性，以及宇宙比较[About] 打印，两侧的两个完备性证据并排显示，

 ConeSet_Complete@{u u0} : Complete@{u u u u0}     ( * u < u0 * )
 Sets_Complete@{u u0}    : Complete@{u u u u0}     ( * u < u0 * )

 -- 相同数量的宇宙，相同的绑定器，相同的实例，以及
 上面的标题为 [Sets_Complete] 记录的相同小性附加条件。两者
 没有一个比另一个更通用。块之间的区别仅在于它们引用的 stdlib 常量：
 这个通过 [Sets_Terminal] 并引用 [eq_ind] 及其相关，现有的通过 [sigT] 并引用 [Projections]。

 离散特殊情况上面引用的 Mac Lane 自己的句子。它是针对兼容族顶点提出的，其与 Instance/Sets/Products.v 的索引积的关系是直接的：三个 [eq_refl] 示例记录了极限顶点就是离散图的 [Sets_limit_obj]，生成的积集合确实是字面上的 [Sets_iprod_obj f]，并且极限腿就是索引积的投影。强度是一个同构，而不是相等，其原因不是宇宙。[Sets_limit_compatible] 在一个离散形状上展开为 [∀ d d' (e : d = d'), fmap[F] e (x d) ≈ x d'，这是一个真正的 Pi 型，而不是 [unit]：它对于每个族 ([discrete_compatible]，通过 [destruct e]) 都是可居住的，但作为一个类型它并非空。因此极限承载是 sigma，而积承载是裸族，它们是不同的类型。[eq_refl] 形式的腿方程在转换时被拒绝，并在 Test/ProbeConeSets407.v 中固定。[Structure/Limit/Product/Finite.v] 的 [iprod_unique_iso] 会在一个项中给出相同的同构，因为两边都是索引积。它故意没有被使用：要求该模块为此文件额外花费二十一 个闭包模块来处理十二行，而手工构建则是三十一 个且成本为零。它在这里被引用，而不是被使用。一个宇宙密码，已被披露——并且它涉及十个常数中的四个，而不是该部分。离散部分用 [{A : Set}] 编写，这段话的早期修订版表示整个部分强制了它。通过将该部分重新表述为 [{A : Type}] 并编译来测量：那里接受了六个常数，其中包括标题 [discrete_iprod_iso]，以及 [discrete_limit]、[discrete_inner_is_iprod]、[discrete_compatible]、[discrete_forget] 和 [discrete_pair]。确切地说，正好有四个被拒绝 —— [discrete_apex_is_limit_obj]、[discrete_leg_is_proj]、[discrete_iprod_iso_leg] 和 [discrete_iprod_iso_leg_inv] —— 它们正好是那些在语句中命名 Structure/Limit/Product.v 的 [iprod] 或 [iprod_proj] 的四个，其中三个被拒绝的原因是“无法确保类型是集合的子类型”；第四个 [discrete_iprod_iso_leg_inv] 则直接给出了普通的统一不匹配（“预期类型为 ?y ~{?Category}~> ?z”），完全不带 [Set]——这是在本开发自身分类下另一种拒绝类型，通过重新陈述 [Type] 的六个被接受常量并单独添加每一个被拒绝的常量来衡量。该句的早期修订版称四个都是相似的。机制，以及已记录的更正：它消失了。之前的修订是这样解释四次拒绝的：“[iprod@{u u0 u1}] 被声明覆盖 [C : Category@{u1 Set Set}]，将环境 hom 和证明宇宙固定到字面 [Set]，并在 [C := Sets@{o so} : Category@{so o o}] 处将 [Sets] 的载体宇宙 [o] 折叠到 [Set]，之后 [Sets_iprod_obj] 的 [u <= u0] 绑定也将索引向下传递。[iprod] 自身的固定在其打印类型 ([Limit@{u u Set u1} (DiscreteCat_Functor@{u u1 u0 Set} f)]) 中可见，并且接受 BOTH 供体——只有 [Cone] 在被声明为分开的级别被接受，因此它是区分控制——两者都固定在探针中。”归属是正确的，并且供体已被修复：[DiscreteCat_Functor] 已在 Instance/Discrete.v 中原地注释，在 PR “algebraic carriers are sets”（2026-09-17）中。在其之后测量，[iprod] 宣告在 [C : Category@{u1 u2 u2}] 之上且没有字面 [Set]，并且在 [Sets@{o so}] 上将其应用于 [Type@{o}] 索引的族是被接受的，读取为 [Limit@{o o o so} (DiscreteCat_Functor@{o o o so o o so} f) → obj [Sets@{o so}] ] 并带有 [o < so]。

 然而，下面的章节仍然统一写在 [{A : Set}] 上，以便四个回读适用于它们所回读的同一个 [f]。同样，该绑定器现在是一个选择，而不是一个固定点：是否可以在 [{A : Type}] 重新表述这四个 [iprod] 命名常量尚未重新测量，因为删除固定点的 PR 只更改了文字内容。上面的核心部分当时或现在都没有 [Set]。这些定义是在顶层声明的，而不是在 [Section] 中声明的，因为 [Context] 节在引脚可以传播之前一次性固定其宇宙，并且离散图在其内部随后被拒绝。

 状态：无公理。[Print Assumptions] 对以下每个常量报告“在全局上下文下封闭”；Makefile 的 [print-assumptions] 目标通过完全限定名称对它们进行审核。
*)

Section ConeSet.

Context {D : Category}.
Context (F : D ⟶ Sets).

(* Mac Lane's [Cone ( *, F)]: the cone presheaf of Structure/Cone.v evaluated at the terminal setoid. Not a copy -- the two [eq_refl] Examples below pin both fields of the [SetoidObject]. / Mac Lane 的 [Cone ( *, F)]：Structure/Cone.v 的锥预层在终结集合类上的值。不是副本——下面的两个 [eq_refl] 示例固定了 [SetoidObject] 的两个字段。 *)
Definition cone_apex : obj[Sets] :=
  fobj[ConePresheaf F] (@terminal_obj Sets Sets_Terminal).

Example cone_apex_is_ConePresheaf :
  cone_apex = fobj[ConePresheaf F] (@terminal_obj Sets Sets_Terminal)
  := eq_refl.

Example cone_apex_carrier :
  carrier cone_apex = @ACone D Sets (@terminal_obj Sets Sets_Terminal) F
  := eq_refl.

Example cone_apex_setoid :
  @is_setoid cone_apex = AConeEquiv (@terminal_obj Sets Sets_Terminal) F
  := eq_refl.

(* Display (2): [v_j : Cone ( *, F) --> F_j], [sigma |--> sigma_j]. The function sends a cone to the value of its leg at [d] on the one point. / 显示 (2)：[v_j : Cone ( *, F) --> F_j]，[sigma |--> sigma_j]。该函数将一个圆锥发送到其在 [d] 上某一点的底边值。 *)
Program Definition cone_leg_at (d : D) : cone_apex ~{Sets}~> F d := {|
  morphism := fun p => @vertex_map _ _ _ _ p d ttt
|}.
Next Obligation. intros d p q Hpq; exact (Hpq d ttt). Qed.

(* The leg IS evaluation, on the nose. / 腿部确实在评估，正中要点。 *)
Example cone_leg_at_is_evaluation (d : D) (p : cone_apex) :
  cone_leg_at d p = @vertex_map _ _ _ _ p d ttt := eq_refl.

(*
 “hence v as defined in (2) is a cone to the base F”: the coherence of
 the cone of legs is the argument cone's own coherence at the point. 

 --------
 因此，在（2）中定义的v是以底面F为底的圆锥：腿部圆锥的连贯性是论证圆锥在该点自身的连贯性。
*)
Program Definition cone_set_acone : ACone cone_apex F := {|
  vertex_map := cone_leg_at
|}.
Next Obligation.
  intros x y f p; exact (@cone_coherence _ _ _ _ p x y f ttt).
Qed.

Definition cone_set_cone : Cone F :=
  {| vertex_obj := cone_apex; coneFrom := cone_set_acone |}.

(* Mac Lane's [h]: “for each x in X, tau x is a cone to F from one point, so there is a unique function h : X --> Cone ( *, F) sending each x to tau x”. / Mac Lane 的 [h] ：“对于 X 中的每个 x，τ x 是从一个点到 F 的锥，因此存在一个唯一的函数 h : X --> Cone ( *, F) 将每个 x 发送到 τ x。” *)
Program Definition cone_set_med (N : Cone F) :
  vertex_obj[N] ~{Sets}~> cone_apex := {|
  morphism := fun e =>
    {| vertex_map := fun d => {| morphism := fun _ =>
         @vertex_map _ _ _ _ (@coneFrom _ _ _ N) d e |} |}
|}.
Next Obligation. intros N e d u v Huv; reflexivity. Qed.
Next Obligation.
  intros N e x y f u.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f e).
Qed.
Next Obligation.
  intros N e e' Hee' d u.
  exact (proper_morphism
           (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) d) e e' Hee').
Qed.

(* Commuting is definitional. / 通勤是定义性的。 *)
Lemma cone_set_med_commutes (N : Cone F) (d : D) :
  cone_leg_at d ∘ cone_set_med N
    ≈ @vertex_map _ _ _ _ (@coneFrom _ _ _ N) d.
Proof. intros e; reflexivity. Qed.

(* Uniqueness. The [destruct u] is the one use of the singleton's unique-inhabitant property in the whole construction. / 独特性。[destruct u] 是整个结构中唯一使用单例唯一居民属性的例子。 *)
Lemma cone_set_med_unique (N : Cone F)
  (v : vertex_obj[N] ~{Sets}~> cone_apex) :
  (∀ d : D, cone_leg_at d ∘ v
              ≈ @vertex_map _ _ _ _ (@coneFrom _ _ _ N) d) →
  cone_set_med N ≈ v.
Proof. intros Hv e d u; destruct u; symmetry; exact (Hv d e). Qed.

(* Theorem 1, at the apex-pinned level. / 定理1，在顶点铰支水平。 *)
Program Definition cone_set_IsALimit : IsALimit F cone_apex := {|
  limit_acone := cone_set_acone;
  ump_limit := fun N => {| unique_obj := cone_set_med N |}
|}.
Next Obligation. exact cone_set_med_commutes. Qed.
Next Obligation. intros N v Hv; exact (cone_set_med_unique N v Hv). Qed.

(* Theorem 1, bundled. / 定理 1，捆绑。 *)
Program Definition cone_set_Limit : Limit F := {|
  limit_cone := cone_set_cone;
  ump_limits := fun N => {| unique_obj := cone_set_med N |}
|}.
Next Obligation. exact cone_set_med_commutes. Qed.
Next Obligation. intros N v Hv; exact (cone_set_med_unique N v Hv). Qed.

End ConeSet.

(* Completeness of [Set], by Mac Lane's own construction. A second witness beside [Sets_Complete]; see the header for why both stand. / [Set] 的完备性，由 Mac Lane 自己构造。除了 [Sets_Complete] 之外的第二个见证；参见标题了解两者都成立的原因。 *)
Definition ConeSet_Complete : @Complete Sets := fun D F => cone_set_Limit F.

(** ** Mac Lane's discrete example / **麦克莱恩的离散例子 *)

(*
 “if J is discrete, the set Cone( *, F) of J-cones is just the cartesian
 product Pi_j F_j”.  What is proved HERE is that sentence about the
 COMPATIBLE-FAMILY apex, whose relation to the indexed product is direct.
 The object Mac Lane's sentence actually names is the cone set, and
 Instance/Sets/Cone.v's [cone_apex_discrete_iprod_iso] carries this
 across to it by one [iso_compose] with [cone_apex_iso]; that file is
 where the quoted sentence becomes a theorem about its own subject.  See
 the header for the [Set] pin four of these carry -- the isomorphism
 below is not among them -- and for why they are not in a [Section]. 

 --------
 “如果 J 是离散的，J-锥集合 Cone( *, F) 就只是笛卡尔积 Pi_j F_j”。这里证明的是关于兼容族顶点的那个句子，它与索引积的关系是直接的。Mac Lane 句子实际命名的对象是锥集合，而 Instance/Sets/Cone.v 的 [cone_apex_discrete_iprod_iso] 通过一个 [iso_compose] 与 [cone_apex_iso] 将其传递过去；该文件是所引用的句子成为关于它自身主题的定理的地方。请参阅 [Set] 引言中有关这四个携带的标记——下面的同构不在其中——以及它们为什么不在 [Section] 中。
*)

Definition discrete_limit {A : Set} (f : A → obj[Sets]) :
  Limit (DiscreteCat_Functor f) := Sets_Limit (DiscreteCat_Functor f).

(*
 The limit's apex IS the compatible-family object of the discrete
 diagram. 

 --------
 极限的顶点是离散图的相容族对象。
*)
Example discrete_apex_is_limit_obj {A : Set} (f : A → obj[Sets]) :
  iprod f (discrete_limit f)
  = Sets_limit_obj (DiscreteCat_Functor f) := eq_refl.

(* The product setoid it is cut out of IS literally [Sets_iprod_obj f]. / 它所裁切的产品集合实际上是 [Sets_iprod_obj f]。 *)
Example discrete_inner_is_iprod {A : Set} (f : A → obj[Sets]) :
  Sets_iprod_obj (fun d : DiscreteCat A => (DiscreteCat_Functor f) d)
  = Sets_iprod_obj f := eq_refl.

(* The limit legs ARE the indexed-product projections. / 极限腿是索引积的投影。 *)
Example discrete_leg_is_proj {A : Set} (f : A → obj[Sets]) (a : A) :
  iprod_proj f (discrete_limit f) a
  = Sets_limit_leg (DiscreteCat_Functor f) a := eq_refl.

(*
 The compatibility constraint is inhabited for every family at a discrete
 shape -- vacuously satisfied, but not vacuous as a type, which is why
 the agreement below is an isomorphism and not an equality. 

 --------
 对于每个在离散形状下的族，兼容性约束都是可满足的——这是虚假的满足，但作为一种类型并非空类型，这就是为什么下面的对应是同构而不是相等。
*)
Lemma discrete_compatible {A : Set} (f : A → obj[Sets])
  (x : Sets_iprod_obj (fun d : DiscreteCat A => (DiscreteCat_Functor f) d)) :
  Sets_limit_compatible (DiscreteCat_Functor f) x.
Proof. intros d d' e; destruct e; simpl; reflexivity. Qed.

Program Definition discrete_forget {A : Set} (f : A → obj[Sets]) :
  Sets_limit_obj (DiscreteCat_Functor f) ~{Sets}~> Sets_iprod_obj f := {|
  morphism := fun p => `1 p
|}.
Next Obligation. intros A f p q Hpq a; exact (Hpq a). Qed.

Program Definition discrete_pair {A : Set} (f : A → obj[Sets]) :
  Sets_iprod_obj f ~{Sets}~> Sets_limit_obj (DiscreteCat_Functor f) := {|
  morphism := fun x => (x; discrete_compatible f x)
|}.
Next Obligation. intros A f x y Hxy a; exact (Hxy a). Qed.

(* The discrete limit IS the cartesian product, up to isomorphism. / 离散极限就是笛卡尔积，至同构而言。 *)
Program Definition discrete_iprod_iso {A : Set} (f : A → obj[Sets]) :
  @Isomorphism Sets (Sets_limit_obj (DiscreteCat_Functor f))
                    (Sets_iprod_obj f) := {|
  to := discrete_forget f; from := discrete_pair f
|}.
Next Obligation. intros A f x a; reflexivity. Qed.
Next Obligation. intros A f p a; reflexivity. Qed.

(* Both leg families, at the setoid grade. The [eq_refl] form of the first is refused at CONVERSION and is pinned in the probe. / 两个腿系族，处于集合等价等级。第一个的 [eq_refl] 形式在转换时被拒绝，并在探查中被固定。 *)
Lemma discrete_iprod_iso_leg {A : Set} (f : A → obj[Sets]) (a : A) :
  Sets_iprod_proj f a ∘ to (discrete_iprod_iso f)
    ≈ iprod_proj f (discrete_limit f) a.
Proof. intros p; reflexivity. Qed.

Lemma discrete_iprod_iso_leg_inv {A : Set} (f : A → obj[Sets]) (a : A) :
  iprod_proj f (discrete_limit f) a ∘ from (discrete_iprod_iso f)
    ≈ Sets_iprod_proj f a.
Proof. intros x; reflexivity. Qed.
