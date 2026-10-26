Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Quotient.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Epi.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.Quotient.Isomorphism.

Generalizable All Variables.

(*
   * * Mac Lane's group illustration: the quotient objects of G are the
   G/N 

   --------
   * * 麦克莱恩的群示例：G 的商对象是 G/N
*)

(*
 nLab:      https://ncatlab.org/nlab/show/quotient+object
 nLab:      https://ncatlab.org/nlab/show/quotient+group
 Wikipedia: https://en.wikipedia.org/wiki/Quotient_group

 Mac Lane, “Categories for the Working Mathematician”, 2nd ed. (GTM 5),
 §V.7, book p. 126 (PDF p. 135), Definition 3, illustrates quotient
 objects with groups: a quotient object of a group G is a quotient
 G/N by a normal subgroup.  Issue #446 recorded that illustration as
 absent “the library having no group theory of that kind”.  That was
 STALE when written: Instance/Grp/Quotient.v already carried
 [Subgroup], [NormalSubgroup], [QuotientGrp], the
 projection with its epicness and [KernelNS], and
 Instance/Grp/Quotient/Isomorphism.v already carried the first
 isomorphism theorem with its triangle.  This file spends
 those donors; it adds no group theory.

 WHAT IS DELIVERED.  One direction is a line: [grp_quot_of_normal N] is
 [mk_quot (quot_proj N) (quot_proj_epic N)].  The order comes with it:
 [grp_quot_le_of_included] says that a LARGER normal subgroup gives a
 SMALLER quotient object -- N ⊆ N' implies G/N' ≤ G/N in the
 factorization preorder, the coarser quotient being the lower one --
 with the identity function as mediator, its respectfulness clause
 being exactly the inclusion of members.

 The CONVERSE is where the constructive cost sits, and the type says
 so.  [grp_quot_is_quot_by_kernel] takes a quotient object whose epi is
 SURJECTIVE ([GrpSurjective], Instance/Grp/Epi.v) and produces
 q ≈ grp_quot_of_normal (KernelNS (quot_epi q)): the first isomorphism
 theorem gives G/ker e ≅ im e, [surjective_image_iso]
 (Instance/Grp/Quotient/Isomorphism.v) gives im e ≅ Q, and the
 composite carries the projection to e ([grp_quot_kernel_triangle],
 through [first_isomorphism_triangle] and [image_factors]), which is
 what makes it an equivalence OF
 QUOTIENT OBJECTS rather than a bare isomorphism of codomains.
 Surjectivity is NOT available from [Epic] alone in this tree: in [Grp]
 “surjective implies epic” is unconditional (Instance/Grp/Epi.v)
 but the converse is the double-negation elimination that file's own
 header sets out -- the unconditional theorem is that file's
 [grp_epic_image_dense], “no element can be SHOWN to miss the image” --
 and recovering a preimage needs its [GrpImageStable].  So the
 [Epic]-only reading is stated separately and conditionally, as
 [grp_quot_is_quot_by_kernel_stable] through
 [grp_quot_surjective_of_stable] (its [grp_epic_is_surjective]).
 Instance/Grp/Epi.v onwards also shows that for an epimorphism
 that hypothesis IS the conclusion restated (its
 [surjective_gives_stable]), so the conditional form is
 honest about buying nothing for free.  This is precisely the clause
 that Instance/FinSet/QuotObj.v does NOT need, the finite search there
 being decidable.

 Non-vacuity is checked rather than assumed: A3 inside S3
 (Instance/Grp/Quotient.v) is a proper nontrivial normal subgroup
 of a nonabelian group, so [grp_quot_S3_A3] is a quotient object that
 is neither the top nor the bottom of the order, and
 [grp_quot_S3_trivial_le_A3] inhabits the order lemma at it.

 STRENGTH.  Everything is at ≈ on [QuotObj G].  [QuotObj] inherits
 [SubObj]'s setoid (Theory/Subobject.v) and has no Leibniz
 antisymmetry, so no statement here is or could be an [eq_refl]
 readback.

 THE GENERAL LEMMA IT NEEDS.  [quot_equiv_of_cod_iso] -- an
 isomorphism of codomains carrying one epi to the other gives ≈ of
 quotient objects -- is not about groups.  It was first proved in this
 file during the parallel build (as [grp_quot_equiv_of_cod_iso]) and
 was lifted into Theory/Subobject/Quotient.v at integration as a
 corollary of that file's [quot_equiv_iff_iso]; this file consumes it
 and no longer carries its own copy.

 MEASUREMENTS, each re-runnable.  10 constants (.glob heads; a first
 draft had 11, the eleventh being the general lemma since lifted), no
 [Program] so no obligations in the .vo, and all 10 report “Closed
 under the global context” under [Print Assumptions] -- including the
 ones routed through the S3 witness, whose carrier is
 [rot * bool] with decidable equality and needs no axiom.  1 [Defined]
 and 5 [Qed] (a first draft had 2 [Defined], the other being the lifted
 lemma); the [Defined] recompiles green as [Qed] (measured by
 flipping and rebuilding), and it is kept [Defined]
 because [quot_le] and `≈` on [QuotObj] are data that a consumer may
 want to read.  The requirement closure is 94 files (iterated over
 .Makefile.coq.d).  No name introduced here occurs anywhere else in the
 tree (swept over all .glob files with
 '^[a-z]+ [0-9:]+ [^ ]* NAME$', instrument-checked on [sub_le]).
 Universes, by [About], RE-MEASURED after the PR “algebraic carriers are
 sets” (2026-09-17): [grp_quot_of_normal@{u u0 u1}] binds
 [GrpObject@{u0 u0 u0}] and [Grp] as [Category@{u u0}] -- hom level
 identified with proof level, which is what [SubObj] demands and which
 [Grp] satisfies on the nose; the identification is INHERITED from
 Theory/Subobject.v and is not introduced here.  An earlier revision
 wrote [@{u u0}] for the constant and [Category@{u u0 u0}] for [Grp], and
 said “No [Set] pin”.  The constant now carries three universes (the
 [NormalSubgroup] argument's own level became visible) and its block
 gained [Set < u] -- a strict LOWER bound, entering with [Prop]'s sort
 through [PropEquiv], and NOT an identification: nothing is pinned AT
 [Set], which is what that sentence was about.

 NOT DELIVERED.  No correspondence theorem: that [quot_le] between two
 G/N is EQUIVALENT to inclusion of the normal subgroups is not stated,
 only the one direction that is cheap; the converse would need the
 mediator's action on members recovered from the factorization.  No
 lattice: the meet of two quotient objects of a group is the pushout of
 the two projections, [Grp] has pushouts (Instance/Grp/Pushout.v), and
 nothing here identifies that pushout with the quotient by the join of
 the two normal subgroups.  No coimages in [Grp^op]: the image
 factorization is in tree (Instance/Grp/Quotient/Isomorphism.v's
 [factorization]) but is not packaged as an [ImageOf] at [Grp^op], as
 it is for [Sets] and [FinSet].  No enumeration of the quotient objects
 of any finite group.  No [Print Assumptions] claim about the donors:
 the eleven verdicts below cover the constants of THIS file, and
 docs/AXIOMS.md is where the library-wide picture lives. 

 --------
 nLab:       https://ncatlab.org/nlab/show/quotient+object 
 nLab:       https://ncatlab.org/nlab/show/quotient+group 
 维基百科:  https://en.wikipedia.org/wiki/Quotient_group 

 Mac Lane, 《工作数学家的范畴论》，第二版（GTM 5），
 §V.7，第126页（PDF第135页），定义3，用群举例说明商对象：群G的商对象是一个正规子群N的商G/N。问题#446记录了这个例子为“图书馆没有那种群论”。当时这已经是过时的：Instance/Grp/Quotient.v 已经包含 
 [Subgroup] ,  [NormalSubgroup] ,  [QuotientGrp] , 投影及其满射性质 [KernelNS] , 并且 Instance/Grp/Quotient/Isomorphism.v 已经包含首同构定理及其三角形。这个文件使用了那些已有内容；它没有增加新的群论。交付的内容。一条方向是一条线：[grp_quot_of_normal N] 是 [mk_quot (quot_proj N) (quot_proj_epic N)]。订单随之而来：[grp_quot_le_of_included] 说一个较大的正规子群会给出较小的商对象——N ⊆ N' 意味着在因子化预顺序中 G/N' ≤ G/N，较粗的商位于较低的位置——中介是恒等函数，其尊重性条款正是成员的包含关系。CONVERSE 是构造成本所在之处，类型说明了这一点。[grp_quot_is_quot_by_kernel] 接受一个其 Epi 为满射的商对象 ([GrpSurjective], Instance/Grp/Epi.v)，并生成 q ≈ grp_quot_of_normal (KernelNS (quot_epi q))：第一个同构定理给出 G/ker e ≅ im e，[surjective_image_iso] (Instance/Grp/Quotient/Isomorphism.v) 给出 im e ≅ Q，而复合映射将投影映射到 e ([grp_quot_kernel_triangle], 通过 [first_isomorphism_triangle] 和 [image_factors])，这使其成为商对象的等效，而不仅仅是余域的简单同构。在这个树中，仅从 [Epic] 无法获得满射性：在 [Grp] 中，“满射意味着上射”是无条件的（Instance/Grp/Epi.v），但其逆命题是双重否定消去，该文件本身的头部已说明——无条件定理是该文件的 [grp_epic_image_dense]，“不能显示有元素未落在像中”——而恢复一个原像需要它的 [GrpImageStable]。因此，仅 [Epic] 的解释是单独且有条件地陈述的，如 [grp_quot_is_quot_by_kernel_stable] 至 [grp_quot_surjective_of_stable]（它的 [grp_epic_is_surjective]）。从 Instance/Grp/Epi.v 起也显示，对于一个上射映射，该假设是结论的重述（它的 [surjective_gives_stable]），所以有条件形式中没有白得任何东西。这正是 Instance/FinSet/QuotObj.v 不需要的条款，那里有限搜索是可判定的。非空性是被检查而不是假定的：A3 在 S3 内部（Instance/Grp/Quotient.v）是一个非阿贝尔群的适当非平凡正规子群，因此 [grp_quot_S3_A3] 是一个既不是顺序顶端也不是底端的商对象，并且 [grp_quot_S3_trivial_le_A3] 存在于顺序引理中。

 强度。一切在 [QuotObj G] 上大致相等。[QuotObj] 继承了 [SubObj] 的集合范畴（Theory/Subobject.v），且没有莱布尼茨反对称性，因此此处的陈述没有，也不可能有 [eq_refl] 的重述。它需要的一般引理。[quot_equiv_of_cod_iso] —— 一个将一个射映射到另一个的上同态同构提供了商对象的≈ —— 与群无关。它首次在此文件中于并行构建期间被证明（作为 [grp_quot_equiv_of_cod_iso]），并在集成过程中作为该文件 [quot_equiv_iff_iso] 的推论被提升到 Theory/Subobject/Quotient.v；此文件使用它，并不再保留自己的副本。测量，每个都可重新运行。10 个常量（.glob 头；最初的草稿有 11 个，第十一项是已提升的一般引理），没有 [Program]，因此在 .vo 中没有义务，并且在 [Print Assumptions] 下所有 10 个都报告“在全局上下文下闭合”——包括通过 S3 证人路由的那些，其载体是 [rot * bool]，具有可判定的等价性且不需公理。1 个 [Defined] 和 5 个 [Qed]（最初的草稿有 2 个 [Defined]，另一项是提升的引理）；[Defined] 通过翻转和重建重新编译为绿色的 [Qed]，并保持为 [Defined]，因为 [quot_le] 和 `≈` 在 [QuotObj] 上是消费者可能想读取的数据。需求闭包为 94 个文件（在 .Makefile.coq.d 上迭代）。此处引入的名称在树的其他任何地方都未出现（已在所有 .glob 文件中用 '^ [a-z] +  [0-9:] +  [^ ] * NAME$' 搜索，并在 [sub_le] 上进行了工具检查）。由 [About] 进行的宇宙测量，在 PR “代数载体是集合”（2026-09-17）之后重新测量：[grp_quot_of_normal@{u u0 u1}] 绑定 [GrpObject@{u0 u0 u0}] 和 [Grp] 为 [Category@{u u0}] -- 同伦层次与证明层次相同，这是 [SubObj] 的要求，并且 [Grp] 完全满足；这种识别是从 Theory/Subobject.v 继承的，并未在此引入。早期版本将 [@{u u0}] 用于常量，将 [Category@{u u0 u0}] 用于 [Grp]，并且写道“没有 [Set] 引脚”。该常量现在携带三个宇宙（[NormalSubgroup] 参数自身的级别变得可见），其块获得了 [Set < u] —— 一个严格的下界，通过 [PropEquiv] 以 [Prop] 的类型进入，并且不是一个同一性：没有任何东西被固定在 [Set]，这正是那句话所说的内容。未交付。对应定理：在两个 G/N 之间的 [quot_le] 等价于包含正规子群的关系未被陈述，只陈述了一个方向，这是容易的；相反的方向需要调解者对从分解中恢复的成员的作用。没有格结构：一个群的两个商对象的交是两个投影的推极限，[Grp] 有推极限（Instance/Grp/Pushout.v），但这里没有任何内容将该推极限与两个正规子群并的商联系起来。[Grp^op] 中没有余像：像分解在树上（Instance/Grp/Quotient/Isomorphism.v 的 [factorization]）但没有像 [Grp^op] 中那样作为 [ImageOf] 打包，就像 [Sets] 和 [FinSet] 那样。没有对任何有限群的商对象进行枚举。关于捐赠者没有 [Print Assumptions] 声明：
 下面的十一条裁决涵盖了本文件的常量，
 docs/AXIOMS.md 是整个库的全貌所在。
*)

(* * ** Mac Lane's illustration: the quotient objects of a group / * ** 麦克雷恩的例子：群的商对象 *)

(*
 The general lemma this file needs -- two quotient objects are
 equivalent when an isomorphism of their codomains carries one epi to
 the other -- is Theory/Subobject/Quotient.v's [quot_equiv_of_cod_iso].
 It was first proved HERE during the parallel build (as
 [grp_quot_equiv_of_cod_iso], directly by [Isomorphism_Opposite
 (iso_sym i)]) and was lifted into that file at integration as a
 corollary of [quot_equiv_iff_iso]; this file now consumes it.  The
 orientation is still the trap: [SubObj_Setoid] at [C^op] asks for an
 isomorphism IN [C^op], whose [to] is a [C]-arrow the other way round,
 so the [C]-isomorphism handed in goes from the codomain of r to the
 codomain of q. 

 --------
 这个文件需要的一般引理——当它们的上同态通过同构映射其中一个满射到另一个时，两个商对象是等价的——是 Theory/Subobject/Quotient.v 中的 [quot_equiv_of_cod_iso]。它最初在并行构建期间在此处被证明（作为 [grp_quot_equiv_of_cod_iso]，由 [Isomorphism_Opposite (iso_sym i)] 直接证明），并在集成时作为 [quot_equiv_iff_iso] 的推论被提升到该文件中；现在这个文件使用它。方向仍然是陷阱：[SubObj_Setoid] 在 [C^op] 处要求一个 [C^op] 中的同构，其 [to] 是一个相反方向的 [C] 箭头，因此给出的 [C] 同构是从 r 的上同态到 q 的上同态。
*)

(*
 Instance/Grp/Quotient.v's [QuotientGrp N] with its projection, which
 is epic because it is the identity function on
 the carrier.  This is the whole of Mac Lane's example in one line. 

 --------
 Instance/Grp/Quotient.v 的 [QuotientGrp N] 及其投影，它是一个满射，因为它是载体上的恒等函数。这就是 Mac Lane 示例的全部内容，一行概括。
*)
Definition grp_quot_of_normal {G : GrpObject} (N : NormalSubgroup G) :
  @QuotObj Grp G :=
  mk_quot (quot_proj N) (quot_proj_epic N).

(*
 The order, in the direction the factorization preorder gives it: a
 LARGER normal subgroup gives a SMALLER (coarser) quotient object.
 The mediating arrow is the identity function, and its respectfulness
 clause is exactly the inclusion of members. 

 --------
 按因式分解预序给出的方向的顺序：一个较大的正规子群会给出一个较小（更粗）的商对象。调解箭头是恒等函数，其尊重条款正是成员的包含。
*)
Lemma grp_quot_le_of_included {G : GrpObject} (N N' : NormalSubgroup G)
  (H : ∀ a : carrier G, sub_mem N a → sub_mem N' a) :
  @quot_le Grp G (grp_quot_of_normal N') (grp_quot_of_normal N).
Proof.
  unshelve eexists.
  - unshelve refine {| grp_map := {| morphism :=
      fun a : carrier (QuotientGrp N) => a : carrier (QuotientGrp N') |} |}.
    (*
 The quotient's `≈` is the truncation of [quot_rel] since the PR
 “algebraic carriers are sets” (2026-09-17): the inclusion is applied
 under it, [Prop] to [Prop]. 

 --------
 商 `≈` 是 [quot_rel] 的截断，因为 PR “代数载体是集合”（2026-09-17）：在其下应用了包含，即从 [Prop] 到 [Prop]。
*)
    + intros a b Hab.
      change (inhabited (quot_rel N a b)) in Hab.
      change (inhabited (quot_rel N' a b)).
      destruct Hab as [Hab]; exact (inhabits (H _ Hab)).
    + simpl; constructor; apply quot_rel_refl.
    + intros a b; simpl; constructor; apply quot_rel_refl.
  - intro a; simpl; constructor; apply quot_rel_refl.
Defined.

(* * ** The converse, and the hypothesis it costs / * ** 逆命题，以及它的假设所花费的代价 *)

Section Converse.

Context {G : GrpObject}.

(*
 In [Grp] a surjection is epic unconditionally
 (Instance/Grp/Epi.v) but the converse is not available
 constructively: [grp_epic_image_dense] gives only that no
 element can be SHOWN to miss the image, and Instance/Grp/Epi.v's
 header sets out why -- recovering a preimage from an epimorphism is
 the double-negation elimination its [GrpImageStable] names.
 So the theorem below is stated for a quotient object whose epi is
 surjective, and the [Epic]-only form is recorded separately as the
 conditional [grp_quot_is_quot_by_kernel_stable]. 

 --------
 在 [Grp] 中，满射在无条件下是史诗映射（Instance/Grp/Epi.v），但其逆命题在构造上不可用：[grp_epic_image_dense] 仅说明没有元素可以被展示为不在像中，而 Instance/Grp/Epi.v 的标题说明了原因——从一个史诗映射恢复原像就是它的 [GrpImageStable] 所命名的双重否定消除。因此，下面的定理是针对一个其史诗映射为满射的商对象陈述的，而 [Epic] 的唯一形式单独作为条件 [grp_quot_is_quot_by_kernel_stable] 记录。
*)
Definition grp_quot_surjective_of_stable (q : @QuotObj Grp G)
  (Hst : @GrpImageStable G (quot_cod q) (quot_epi q)) :
  GrpSurjective (quot_epi q) :=
  grp_epic_is_surjective (quot_epi q) Hst (quot_is_epic q).

(*
 The comparison: G/ker e ≅ im e ≅ Q, the first isomorphism theorem
 (Instance/Grp/Quotient/Isomorphism.v) followed by the
 identification of the image with the codomain of a surjection. 

 --------
 比较：G/ker e ≅ im e ≅ Q，第一同构定理（Instance/Grp/Quotient/Isomorphism.v），接着是将像与满射的陪域进行同一化。
*)
Definition grp_quot_kernel_iso (q : @QuotObj Grp G)
  (Hs : GrpSurjective (quot_epi q)) :
  QuotientGrp (KernelNS (quot_epi q)) ≅[Grp] quot_cod q :=
  iso_compose (surjective_image_iso (quot_epi q) Hs)
              (first_isomorphism_theorem (quot_epi q)).

(*
 ... and it carries the projection to the quotient epi, which is what
 makes it an equivalence OF QUOTIENT OBJECTS and not merely an
 isomorphism of codomains.  The two triangles are
 [first_isomorphism_triangle] and [image_factors]. 

 --------
 ... 并且它携带到商上的投影，这正是使其成为商对象的等价，而不仅仅是陪域的同构的原因。这两个三角形是 [first_isomorphism_triangle] 和 [image_factors]。
*)
Lemma grp_quot_kernel_triangle (q : @QuotObj Grp G)
  (Hs : GrpSurjective (quot_epi q)) :
  to (grp_quot_kernel_iso q Hs) ∘ quot_proj (KernelNS (quot_epi q))
    ≈ quot_epi q.
Proof.
  change (to (surjective_image_iso (quot_epi q) Hs)
            ∘ to (first_isomorphism_theorem (quot_epi q))
            ∘ quot_proj (KernelNS (quot_epi q)) ≈ quot_epi q).
  rewrite <- comp_assoc.
  rewrite (first_isomorphism_triangle (quot_epi q)).
  exact (image_factors (quot_epi q)).
Qed.

(*
 Mac Lane §V.7: the quotient objects of a group ARE the G/N.  Stated
 at ≈ on [QuotObj G], which is the strongest relation available --
 [QuotObj] inherits [SubObj]'s setoid and has no Leibniz
 antisymmetry. 

 --------
 Mac Lane §V.7：一个群的商对象就是 G/N。大约在 [QuotObj G] 上陈述，这是可用的最强关系——[QuotObj] 继承了 [SubObj] 的集合等价关系，并且没有 Leibniz 反对称性。
*)
Theorem grp_quot_is_quot_by_kernel (q : @QuotObj Grp G)
  (Hs : GrpSurjective (quot_epi q)) :
  q ≈ grp_quot_of_normal (KernelNS (quot_epi q)).
Proof.
  exact (quot_equiv_of_cod_iso q
           (grp_quot_of_normal (KernelNS (quot_epi q)))
           (grp_quot_kernel_iso q Hs) (grp_quot_kernel_triangle q Hs)).
Qed.

(*
 The same statement with the stability hypothesis in place of
 surjectivity, so that the cost of the classical reading is visible in
 the type rather than hidden in a side condition. 

 --------
 同样的陈述，只是将稳定性假设替代了满射性，因此经典解读的代价在类型中可见，而不是隐藏在附加条件中。
*)
Theorem grp_quot_is_quot_by_kernel_stable (q : @QuotObj Grp G)
  (Hst : @GrpImageStable G (quot_cod q) (quot_epi q)) :
  q ≈ grp_quot_of_normal (KernelNS (quot_epi q)).
Proof.
  exact (grp_quot_is_quot_by_kernel q (grp_quot_surjective_of_stable q Hst)).
Qed.

End Converse.

(** ** Non-vacuity / ** 非空性 *)

(*
 The correspondence is inhabited at a nondegenerate pair: A3 inside S3
 (Instance/Grp/Quotient.v) is a proper nontrivial normal subgroup
 of a nonabelian group, so [grp_quot_of_normal A3] is a quotient object
 of S3 that is neither the top nor the bottom of the order.  The two
 separations are Instance/Grp/Quotient.v's [S3_mod_A3_not_collapsed]
 and [quot_proj_A3_not_injective]; [grp_quot_S3_A3_not_collapsed]
 below is a verbatim RE-EXPORT of the first under a name that says
 what it is used for, and proves nothing new -- the constant that
 carries new content here is [grp_quot_S3_A3] itself and the order
 inhabitant [grp_quot_S3_trivial_le_A3]. 

 --------
 对应关系在一个非退化对中有元素：A3 在 S3 内部（Instance/Grp/Quotient.v）是一个非阿贝尔群的真非平凡正规子群，所以 [grp_quot_of_normal A3] 是 S3 的一个商对象，并且既不是序中的顶点也不是底点。这两个分离是 Instance/Grp/Quotient.v 的 [S3_mod_A3_not_collapsed] 和 [quot_proj_A3_not_injective]；下面的 [grp_quot_S3_A3_not_collapsed] 是对第一个的逐字重新导出，名称表明其用途，并且没有证明新的内容——这里承载新内容的常数是 [grp_quot_S3_A3] 本身以及序的元素 [grp_quot_S3_trivial_le_A3]。
*)
Definition grp_quot_S3_A3 : @QuotObj Grp S3 := grp_quot_of_normal A3.

Lemma grp_quot_S3_A3_not_collapsed :
  quot_rel A3 S3_s s3_unit → False.
Proof. exact (S3_mod_A3_not_collapsed). Qed.

(*
 The trivial normal subgroup sits below A3, so the identity quotient is
 above it in the factorization order -- the order lemma, inhabited. 

 --------
 平凡正规子群位于 A3 之下，因此单位商群在分解顺序中位于它之上——顺序引理，有元素。
*)
Lemma grp_quot_S3_trivial_le_A3 :
  @quot_le Grp S3 (grp_quot_of_normal A3) (grp_quot_of_normal (TrivialNS S3)).
Proof. exact (grp_quot_le_of_included (TrivialNS S3) A3 trivial_in_A3). Qed.
