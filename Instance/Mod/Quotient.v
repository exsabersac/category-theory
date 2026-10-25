Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Theory.Universal.Element.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   * * Submodules, the quotient module, and its universal property

   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §III.1
   Exercise 5 (printed p. 59, PDF p. 68) [maclane:III.1:ex5].
   nLab: https://ncatlab.org/nlab/show/quotient+module
   Wikipedia: https://en.wikipedia.org/wiki/Quotient_module

   For S a submodule of A, the projection p : A -> A/S is a UNIVERSAL
   ELEMENT of the functor of module homomorphisms killing S.  Mac Lane's
   point in §III.1 is that every further property of the quotient
   follows from that universality alone; this file proves the
   universality, and Instance/Mod/Quotient/Isomorphism.v draws the named
   consequences from it.

   ERRATUM, recorded here rather than only in a commit message.  Issue
   #314's "Current state in the library" section says the area is
   "Absent", that the search
   [rg -i 'submodule|quotient module|quotient ring|\bideal\b'] "finds
   only background-essay comments (Structure/Abelian.v)", that
   "no module or ring categories exist in-tree", and that there are "no
   isomorphism-theorem statements anywhere".  Measured against the
   parent commit rather than taken on the issue's word, the last three
   of those are wrong, and with them the summary word "Absent":

   - Instance/Mod.v (#258) exists and carries [RModObject],
   [RModHom], [RMod], [RMod_Forget], [RMod_Zero],
   [rmod_monic_iff_injective] and [rmod_epic_iff_surjective];
   Instance/Rng.v (#257) exists and carries [Rng], [CRng],
   [Rng_Initial_Z] and [Rng_Terminal_zero].  Both are REQUIRED by
   this file.
   - Isomorphism theorems exist: Instance/Grp/Quotient/Isomorphism.v
   (#313) carries all three for groups, with uniqueness clauses for
   the first and third.
   - The quoted [rg] does not hit Structure/Abelian.v at all.  At the
   parent commit those two lines say "R-Mod", not "submodule" or
   "ideal".  Re-run against the parent commit it returns NINETEEN
   lines: eight in Instance/Mod.v, four in Instance/Field/Frac.v,
   and one each in Theory/Coq.v, Instance/Sets.v,
   Instance/Rng/Polynomial.v, Instance/Rng/MonoidRing.v,
   Instance/Rng/GroupRing.v, Instance/Rng/Frac.v and
   Construction/Groupoid.v.  THREE of the nineteen are not about
   the subject at all -- Construction/Groupoid.v's historical
   "ideal arithmetic", Instance/Sets.v's "an ideal existence", and
   Theory/Coq.v's Coq-language "submodules".

   What IS absent, and was measured by searching for the TYPE rather
   than for a guessed name -- an anchored sweep for a [Record], [Class],
   [Inductive], [Definition] or [Structure] whose name contains
   "Submodule", "Ideal", "SubMod" or "TwoSided", over every [.v] file in
   the tree -- reads NONE.  So the interfaces are new; the categories
   they are stated over are not.

   THE ONE PLACE THE GROUP ANALOGY BREAKS, and it is the mathematical
   content of this file.  Instance/Grp/Quotient.v carries TWO records,
   [Subgroup] and [NormalSubgroup], the second adding the conjugation
   field [ns_conj], and that field is spent exactly twice, in
   [quot_rel_mul] and [quot_rel_inv].  Here there is ONE record and no
   conjugation field, because a module's addition is COMMUTATIVE:
   [RModObject] extends [AbObject] extends [CMonObject], whose
   [cmon_plus_comm] is a field, so conjugation is the identity.  That is
   not left as a remark -- [smod_conjugate_inert] and [smod_normal]
   prove it, the latter being literally [ns_conj]'s statement
   transcribed additively and discharged as a LEMMA from an arbitrary
   [Submodule].  The corresponding negative is one level down and is
   NOT restated here: Instance/Grp/Quotient.v's [S3_refl_sub_not_normal]
   exhibits a subgroup of S3 that is not normal, and no module can
   witness the same thing, there being no non-abelian module.

   ONE FEWER LAW STILL.  [Submodule] carries FOUR laws and not five
   (five fields in all, the first being membership itself): closure
   under negation is DERIVED ([smod_neg]), since -a is
   (-1)·a and the record already closes under the scalar action.  This
   is the same economy Instance/Mod.v takes for [RModHom] (which does
   not carry preservation of negation, [rmod_map_neg] being a citation
   of [ab_map_neg]) and Instance/Ab.v takes for [ab_neg_right].  It is
   available here and not in the group case for a precise reason: a
   ring has a unit and a negation, so (-1) is an available scalar.

   THE SETOID QUOTIENT.  As in Instance/Grp/Quotient.v and
   Instance/Ab.v, A/S needs no new carrier: it is A's carrier under the
   coarser relation [mquot_rel S x y := inhabited (smod_mem S (x - y))]
   (an earlier revision wrote it without the [inhabited]; see the note on
   [Submodule] above for why the truncation is there).  Elements
   of A/S are therefore elements of A and no coset object is ever
   formed.  That is convenient but it is NOT what makes the derivations
   universal; the sibling file's arguments run through
   [mquot_universal_element] and the mediator's uniqueness, and where an
   element-level step does occur it is called out there.

   RECONCILIATION WITH THE PRE-EXISTING QUOTIENT, which the issue does
   not mention and which a reader will otherwise trip over.
   Instance/Mod.v already has an [RModQuotient], built as the probe
   object for the epic half of Mac Lane's §I.7 proposition.  It is NOT a
   quotient by an arbitrary submodule and it carries NO universal
   property: it quotients N by the IMAGE of a given homomorphism
   f : M -> N, its relation being Instance/Ab.v's
   [ab_coset_eq (rm_hom f) x y := ∃ a, x ≈ y + f a] -- an earlier revision
   spelled it [{ a & x ≈ y + f a }], which it was before the PR "algebraic
   carriers are sets" (2026-09-17) truncated it.  This file does
   not introduce a second unrelated construction; it exhibits that one
   as the special case, in the strongest form the two relations allow:
   [ImageSubmod f] is the image as a [Submodule N],
   [rmod_quotient_relations_agree] is a biconditional between the two
   relations at every pair of elements, and
   [RModQuotient_is_quotient_by_image] is an isomorphism in [RMod R]
   whose two legs are the identity on elements.  The two relations are
   NOT convertible -- [∃ a, x ≈ y + f a] against
   [inhabited { a & x + (-y) ≈ f a }] -- and the shuffle between them is
   exactly the content of the biconditional; the strict form was tried and is
   pinned as a rejection probe in Test/ProbeModQuotient.v.  An earlier
   revision wrote both sides as [sigT]s; the left is now an [ex] and the
   right the truncation of a [sigT], so the two differ in sort as well as in
   shape.

   ...AND WITH [AbQuotient], which is NOT unified, for a dependency
   reason of the same shape as #313's and with the arrow pointing the
   other way.  Instance/Ab.v's [AbQuotient] is the abelian-group
   quotient by an image, and Instance/Mod.v's [RModQuotient] is built
   ON it.  Routing it through a submodule quotient would make
   Instance/Ab.v depend on Instance/Mod.v, i.e. on a category defined
   over it -- a strictly worse direction than the one #313 declined,
   since there the two files were merely unrelated.  The honest unifier
   is an [AbSubgroup] interface in Instance/Ab.v itself, of which
   [Submodule] would then be the module-level extension; that is a
   defensible change and it is deliberately not made here.  Note also
   that no bridge exists to make one a literal instance of the other.
   An earlier revision gave as the reason "an [AbObject] is not
   exhibited as a ℤ-module anywhere in the tree (Instance/Mod/Tensor.v
   records the same absence)"; since #454 Instance/Mod/Cogenerator.v's
   [Ab_to_ZMod] exhibits every [AbObject] as a ℤ-module through its own
   [zsmul] action, but it is a functor into [RMod Int_Ring], not a
   subgroup interface, so it makes neither quotient a literal instance
   of the other and the conclusion stands.  The near miss the earlier
   revision named is Instance/Rng/Mod.v's
   [ZRestrict R : RMod R ⟶ RMod Int_Ring], and it is NOT it:
   restriction of scalars along ℤ → R needs an R-module to start with,
   not a bare abelian group.

   WHAT IS DELIVERED HERE.  [Submodule] with the derived
   [smod_neg], [smod_normal] and the submodule as an object of [RMod R]
   with its monic inclusion; [QuotientMod] with the projection
   [mquot_proj]; the functor [MKillsFunctor S : RMod R ⟶ Sets] of
   homomorphisms killing S, and [mquot_universal_element], the statement
   that ⟨A/S, p⟩ is a universal element of it, over #303's
   [AUniversalElement] -- the CLASS is used directly, and none of
   Theory/Universal/Element.v's Yoneda packaging is touched, so the
   universe restriction that packaging carries (object, hom and proof
   universes identified) is not inherited; the homomorphism theorem as
   the biconditional [mod_hom_theorem]; the kernel and the image of a
   homomorphism as submodules; the degenerate submodules named and
   separated by proof; the reconciliation above; and non-vacuity at
   ℤ ⊇ 2ℤ, where the quotient is computed.

   WHAT IS NOT DELIVERED HERE.  No lattice of submodules, no sum or
   intersection of an arbitrary family (the binary sum and intersection
   the second isomorphism theorem needs are in the sibling file); no
   [HasCokernels] instance for [RMod R]; no exact sequences; no
   finitely-generated or Noetherian conditions; no comparison with
   Instance/Mod/Free.v's free module or Instance/Mod/Tensor.v's tensor
   product; and no naturality of anything in S.

   NO UNIVERSAL-ARROW PACKAGING, for the structural reason
   Instance/Grp/Quotient.v records: Theory/Universal/Element.v's
   [universal_element_arrow_subsumption] relates universal elements to
   universal arrows exactly when the functor has the shape
   d ↦ Hom(c, S d), and [MKillsFunctor S] does not -- it is the
   SUBfunctor of Hom(A, −) cut out by the killing condition, and that
   condition mentions S, which is data attached to A rather than
   something a functor out of [RMod R] supplies. 

   --------
   * * 子模、商模及其泛性质

   Mac Lane，《为工作的数学家而设的范畴》，第2版，§III.1
   练习5（印刷版第59页，PDF第68页） [maclane:III.1:ex5]。
   nLab: https://ncatlab.org/nlab/show/quotient+module
   维基百科: https://en.wikipedia.org/wiki/Quotient_module

   对于 A 的子模 S，投影 p : A -> A/S 是消去 S 的模同态函子的一
   个泛元。Mac Lane 在 §III.1 中指出，商模的每一个进一步性质都仅
   来自于这种泛性；本文件证明了这种泛性，而 Instance/Mod/Quotient/Isomorphism.v
   则从中推导出相应的结果。勘误，在这里记录，而不仅仅是在提交信息中。问题 #314 的“库中的当前状态”部分说该区域“缺失”，搜索 [rg -i 'submodule|quotient module|quotient ring|\bideal\b']“只找到背景文章评论（Structure/Abelian.v）”，并且“树中不存在模块或环类别”，以及“任何地方都没有同构定理陈述”。与父提交相比，而不是仅凭问题的描述，上述后三项都是错误的，因此总结词“缺失”也不正确。- Instance/Mod.v (#258) 存在并包含 [RModObject], [RModHom], [RMod], [RMod_Forget], [RMod_Zero], [rmod_monic_iff_injective] 和 [rmod_epic_iff_surjective]；
   Instance/Rng.v (#257) 存在并包含 [Rng], [CRng], [Rng_Initial_Z] 和 [Rng_Terminal_zero]。两者都是该文件所需。
   - 同构定理存在：Instance/Grp/Quotient/Isomorphism.v (#313) 包含对群的三个定理，并对第一个和第三个定理有唯一性条款。
   - 引号中的 [rg] 根本没有涉及 Structure/Abelian.v。在父提交中，这两行显示为 “R-Mod”，而不是 “submodule” 或 “ideal”。重新对父提交运行，它返回了十九行：Instance/Mod.v 中八行，Instance/Field/Frac.v 中四行，Theory/Coq.v、Instance/Sets.v、Instance/Rng/Polynomial.v、Instance/Rng/MonoidRing.v、Instance/Rng/GroupRing.v、Instance/Rng/Frac.v 和 Construction/Groupoid.v 各一行。在这十九行中有三行与主题完全无关——Construction/Groupoid.v 的历史“理想算术”、Instance/Sets.v 的“一个理想存在性”和 Theory/Coq.v 的 Coq 语言“子模”。什么是缺失的，通过搜索类型而不是猜测名称来测量——一个针对 [Record]、[Class]、[Inductive]、[Definition] 或 [Structure] 的固定扫描，其名称包含“Submodule”、“Ideal”、“SubMod”或“TwoSided”，在树中每个 [.v] 文件中——结果是没有。因此，接口是新的；它们所声明的类别不是新的。群类比唯一失效的地方，并且这是该文件的数学内容。Instance/Grp/Quotient.v 包含两个记录，[Subgroup] 和 [NormalSubgroup]，第二个增加了共轭字段 [ns_conj]，并且该字段正好使用了两次，在 [quot_rel_mul] 和 [quot_rel_inv] 中。这里有一个记录且没有共轭字段，因为模的加法是交换的：[RModObject] 扩展 [AbObject] 扩展 [CMonObject]，其 [cmon_plus_comm] 是一个字段，因此共轭就是恒等映射。那不是作为注释留下的——[smod_conjugate_inert] 和 [smod_normal] 证明了这一点，后者实际上是 [ns_conj] 的陈述以加法形式转录，并作为引理从任意 [Submodule] 中推出。相应的否定在下一层，这里不再重述：Instance/Grp/Quotient.v 的 [S3_refl_sub_not_normal] 展示了一个 S3 的子群，该子群不是正规子群，并且没有模块能够验证相同的事情，因为不存在非阿贝尔模块。再少一条定律。[Submodule] 包含四条定律，而不是五条（总共有五个字段，第一个是本身的成员资格）：在取反下的闭合是派生出来的（[smod_neg]），因为 -a = (-1)·a，并且该记录已经在标量作用下闭合。这与 Instance/Mod.v 对 [RModHom] 所采取的节约方式相同（它不包含保持取反性质，[rmod_map_neg] 是对 [ab_map_neg] 的引用），也与 Instance/Ab.v 对 [ab_neg_right] 所采取的方式相同。它在这里是可用的，而在群的情况下不可用，有一个明确的原因：一个环有单位元和取反，因此 (-1) 是一个可用的标量。集合商。正如在 Instance/Grp/Quotient.v 和 Instance/Ab.v 中一样，A/S 不需要新的载体：它是在较粗关系 [mquot_rel S x y := inhabited (smod_mem S (x - y))] 下的 A 的载体（早期版本在没有 [inhabited] 的情况下写过；参见上文关于 [Submodule] 的说明，解释了为什么需要截断）。因此，A/S 的元素就是 A 的元素，从未形成余类对象。这很方便，但这并不是使推导具有普适性的原因；兄弟文件中的论证贯穿 [mquot_universal_element] 和中介者的唯一性，并且当确实发生元素级步骤时，那里会特别指出。与先前存在的商的调和，问题中未提及，否则读者会因此而困惑。Instance/Mod.v 已经有一个 [RModQuotient]，它是作为 Mac Lane §I.7 命题的史诗一半的探针对象构建的。它不是任意子模的商，也不具备任何泛性质：它将 N 对一个给定同态 f : M -> N 的像取商，其关系是 Instance/Ab.v 的 [ab_coset_eq (rm_hom f) x y := ∃ a, x ≈ y + f a] ——早期版本拼写为 [{ a & x ≈ y + f a }]，在 PR “代数载体是集合”（2026-09-17）截断之前就是这样。该文件并未引入第二个无关的结构；它展示了一个作为特殊情况，在两个关系允许的最强形式下：
   [ImageSubmod f] 是作为 [Submodule N] 的像，
   [rmod_quotient_relations_agree] 是两个关系在每对元素之间的双条件，且
   [RModQuotient_is_quotient_by_image] 是 [RMod R] 中的同构，其两条分支在元素上都是恒等映射。两个关系不可互换——[∃ a, x ≈ y + f a] 与 [inhabited { a & x + (-y) ≈ f a }]——它们之间的洗牌正是双条件的内容；严格形式已被尝试并固定为 Test/ProbeModQuotient.v 中的拒绝探针。早期的修订将双方都写作 [sigT]；现在左边是 [ex]，右边是 [sigT] 的截断，因此两者在类别和形状上都有所不同。...以及 [AbQuotient]，它不是统一的，出于依赖的原因，其形状与 #313 相同，但箭头指向相反方向。Instance/Ab.v 的 [AbQuotient] 是通过像得到的阿贝尔群商，而 Instance/Mod.v 的 [RModQuotient] 是建立在其上的。通过子模块商来路由它会导致 Instance/Ab.v 依赖于 Instance/Mod.v，即依赖于在其上定义的类别——这比 #313 拒绝的方向严格更糟，因为在那里这两个文件只是无关的。真正的统一器是在 Instance/Ab.v 本身的 [AbSubgroup] 接口，其中 [Submodule] 将成为模块级扩展；这是一个可以辩护的更改，但此处故意未进行修改。此外，还要注意，没有桥接存在可以使其中一个成为另一个的字面实例。早期的修订给出的理由是“在树中的任何地方都没有将 [AbObject] 作为 ℤ-模展示出来（Instance/Mod/Tensor.v 的记录也显示同样的缺失）”；自 #454 以来，Instance/Mod/Cogenerator.v 的 [Ab_to_ZMod] 通过其自身的 [zsmul] 操作将每个 [AbObject] 展示为 ℤ-模，但它是一个进入 [RMod Int_Ring] 的函子，而不是子群接口，因此它并没有使任意一个商成为另一个的字面实例，结论仍然成立。早期修订提到的几乎符合的是 Instance/Rng/Mod.v 的 [ZRestrict R : RMod R ⟶ RMod Int_Ring]，但它不是：沿 ℤ → R 的标量限制需要一个 R-模作为起点，而不是一个裸的阿贝尔群。这里交付的是什么。[Submodule] 与派生的 [smod_neg]、[smod_normal] 以及作为 [RMod R] 对象的子模及其单射包含；[QuotientMod] 与投影 [mquot_proj]；同态函子 [MKillsFunctor S : RMod R ⟶ Sets]，消去 S，以及 [mquot_universal_element]，声明 ⟨A/S, p⟩ 是它的一个普遍元素，基于 #303 的 [AUniversalElement] —— 直接使用 CLASS，并且不触及 Theory/Universal/Element.v 的 Yoneda 封装，因此该封装所携带的宇宙限制（对象、同态和证明宇宙被识别）没有被继承；同态定理作为 [mod_hom_theorem] 的双条件；同态的核和象作为子模；变形的子模按证明命名和分离；上述调和；以及在 ℤ ⊇ 2ℤ 时非空，其中计算了商。这里没有提供的内容。没有子模的格，没有任意族的和或交（第二同构定理所需的二元和与交在同类文件中）；没有 [HasCokernels] 对 [RMod R] 的实例；没有正合序列；没有有限生成或诺特条件；没有与 Instance/Mod/Free.v 的自由模或 Instance/Mod/Tensor.v 的张量积的比较；并且在 S 中的任何事物都没有自然性。没有通用箭头包装，出于结构原因
   Instance/Grp/Quotient.v 记录：Theory/Universal/Element.v 的
   [universal_element_arrow_subsumption] 将通用元素与通用箭头精确关联，当且仅当函子形如
   d ↦ Hom(c, S d)，而 [MKillsFunctor S] 不会 —— 它是由消除条件划定的 Hom(A, −) 的子函子，该条件涉及 S，这是附加在 A 上的数据，而不是 [RMod R] 提供的函子所能提供的东西。
*)

(*
   * ** Subtraction, and the scalar action against it

   The [ab_sub] calculus is Instance/Ab/Subtract.v -- stated over
   [AbObject], because none of it is about the scalar action, and shared
   with Instance/Rng/Quotient.v so that neither file restates it and no
   ring file depends on a module file to get it.  What is new here is
   the one lemma that IS about the action. 

   --------
   * ** 减法及其对标量的作用

   [ab_sub] 演算位于 Instance/Ab/Subtract.v —— 在 [AbObject] 上陈述，因为其中没有关于标量作用的内容，并且与 Instance/Rng/Quotient.v 共享，以便两个文件都不重复陈述，而且没有环文件依赖于模块文件来获取它。这里的新内容是关于该作用的一个引理。
*)

(* The scalar action distributes over subtraction. / 标量作用在减法上分配。 *)
Lemma rm_smul_sub {R : RingObject} (M : RModObject R)
  (r : carrier (rig_setoid (ring_rig R))) (x y : carrier (cmon_setoid M)) :
  rm_smul M r (ab_sub M x y)
    ≈ ab_sub M (rm_smul M r x) (rm_smul M r y).
Proof.
  unfold ab_sub.
  rewrite rm_smul_distr_l.
  now rewrite rm_smul_neg_r.
Qed.

(*
   * ** Submodules

   A submodule is a `≈`-saturated predicate containing zero and closed
   under addition and the scalar action.  Membership is [Type]-valued,
   following Instance/Grp/Quotient.v's [Subgroup] and
   Instance/Grp/Epi.v's [GrpImage].

   AN EARLIER REVISION gave the reason as: "the library's `≈` is itself
   [Type]-valued, so a [Prop]-valued membership could not be eliminated into
   a hom-setoid equation."  That reason is GONE since the PR "algebraic
   carriers are sets" (2026-09-17): every carrier now carries [cmon_prop],
   so [pequiv_to] does exactly that elimination
   (Lib/Setoid/Propositional.v).  Membership stays [Type]-valued anyway,
   and for a different reason: the leastness theorems below and in
   Instance/Mod/Quotient/Isomorphism.v READ WITNESSES out of it -- the
   preimage in [ImageSubmod], the exponent in a torsion argument -- and
   those are data.  What DID move is the quotient RELATION [mquot_rel],
   which is now the propositional truncation of membership.

   There is deliberately NO decidability field and nothing below decides
   membership; and, as the header records, NO closure-under-negation
   field, that being [smod_neg] below. 

   --------
   * ** 子模

   子模是一个 `≈`-饱和的谓词，包含零元素，并在加法和数乘作用下封闭。  
   成员资格为 [Type] 值，根据 Instance/Grp/Quotient.v 的 [Subgroup] 和  
   Instance/Grp/Epi.v 的 [GrpImage]。早期的修订给出的理由是：“该库的 `≈` 本身是 [Type] 值，因此 [Prop] 值的成员资格不能被消除为同质等式。” 自从 PR “代数承载是集合”（2026-09-17）以后，这个理由已经不存在：现在每个承载都承载 [cmon_prop]，因此 [pequiv_to] 正好进行该消除（Lib/Setoid/Propositional.v）。无论如何，成员资格仍保持 [Type] 值，并且原因不同：下面以及 Instance/Mod/Quotient/Isomorphism.v 中的最小性定理会从中读取见证——在 [ImageSubmod] 中的原像、在扭曲论证中的指数——这些都是数据。真正移动的是商关系 [mquot_rel]，它现在是成员资格的命题截断。明确地没有可判定性字段，并且下面没有任何内容决定成员资格；正如标题所记录的，没有否定闭包字段，该字段在下面为 [smod_neg]。
*)

Record Submodule {R : RingObject} (M : RModObject R) := {
  smod_mem : carrier (cmon_setoid M) → Type;

  (* (1) ≈-saturation / (1) ≈-饱和 *)
  smod_resp : ∀ a b : carrier (cmon_setoid M),
    a ≈ b → smod_mem a → smod_mem b;
  (* (2) zero *)
  smod_zero : smod_mem (cmon_zero M);
  (* (3) closure under addition / (3) 在加法下的封闭性 *)
  smod_plus : ∀ a b : carrier (cmon_setoid M),
    smod_mem a → smod_mem b → smod_mem (cmon_plus M a b);
  (* (4) closure under the scalar action / (4) 对标量作用的封闭性 *)
  smod_smul : ∀ (r : carrier (rig_setoid (ring_rig R)))
                (a : carrier (cmon_setoid M)),
    smod_mem a → smod_mem (rm_smul M r a)
}.

Arguments smod_mem {R M} _ _.
Arguments smod_resp {R M} _ _ _ _ _.
Arguments smod_zero {R M} _.
Arguments smod_plus {R M} _ _ _ _ _.
Arguments smod_smul {R M} _ _ _ _.

(* Saturation in the argument-implicit shape the proofs below want. / 下面的证明所需要的论证隐含形式中的饱和度。 *)
Definition smod_at {R : RingObject} {M : RModObject R} (S : Submodule M)
  {a b : carrier (cmon_setoid M)} (Hab : a ≈ b) (Ha : smod_mem S a) :
  smod_mem S b := smod_resp S a b Hab Ha.

(* THE FIFTH FIELD THAT IS NOT A FIELD: closure under negation, because -a is (-1)·a. The scalar (-1) exists because R is a RING; over a rig this would have to be assumed. / 第五个不是域的“域”：关于取反的封闭性，因为 -a 等于 (-1)·a。标量 (-1) 是存在的，因为 R 是一个环；如果是在幺半环上，则必须假设其存在。 *)
Lemma smod_neg {R : RingObject} {M : RModObject R} (S : Submodule M)
  (a : carrier (cmon_setoid M)) : smod_mem S a → smod_mem S (ab_neg M a).
Proof.
  intro Ha.
  apply (smod_at S (a := rm_smul M (ring_neg R (rig_one (ring_rig R))) a)).
  - rewrite (rm_smul_neg_l M (rig_one (ring_rig R)) a).
    now rewrite (rm_smul_one M a).
  - exact (smod_smul S _ _ Ha).
Qed.

(* Closure under subtraction, the shape every proof below uses. / 减法封闭性，每个下面的证明都使用的形式。 *)
Lemma smod_sub {R : RingObject} {M : RModObject R} (S : Submodule M)
  (a b : carrier (cmon_setoid M)) :
  smod_mem S a → smod_mem S b → smod_mem S (ab_sub M a b).
Proof.
  intros Ha Hb.
  exact (smod_plus S _ _ Ha (smod_neg S _ Hb)).
Qed.

(*
   * *** Every submodule is normal, as a theorem

   Instance/Grp/Quotient.v's [NormalSubgroup] adds the field
   [ns_conj : ∀ t a, sub_mem a → sub_mem (t * a * t⁻¹)].  Transcribed
   additively that field reads [∀ t a, mem a → mem ((t + a) - t)], and
   here it is a LEMMA of an arbitrary [Submodule] -- indeed of nothing
   at all, since the conjugate is `≈`-equal to a.  This is the precise
   sense in which the normality layer has no module-level counterpart. 

   --------
   * *** 每个子模都是正规模，作为一个定理

   Instance/Grp/Quotient.v 的 [NormalSubgroup] 添加了字段 [ns_conj : ∀ t a, sub_mem a → sub_mem (t * a * t⁻¹)]。以加法方式转录，该字段读取为 [∀ t a, mem a → mem ((t + a) - t)]，而且这里它是任意 [Submodule] 的引理——实际上什么都不是，因为共轭等于 a（`≈`）。这就是正规性层没有模块级对应物的精确定义意义。
*)

Lemma smod_conjugate_inert {R : RingObject} {M : RModObject R}
  (t a : carrier (cmon_setoid M)) :
  ab_sub M (cmon_plus M t a) t ≈ a.
Proof. apply ab_sub_add_cancel. Qed.

Theorem smod_normal {R : RingObject} {M : RModObject R} (S : Submodule M)
  (t a : carrier (cmon_setoid M)) :
  smod_mem S a → smod_mem S (ab_sub M (cmon_plus M t a) t).
Proof.
  intro Ha.
  exact (smod_at S (symmetry (smod_conjugate_inert t a)) Ha).
Qed.

(* * ** The submodule as an object of [RMod R] / * ** 子模块作为 [RMod R] 的对象 *)

Definition smod_carrier {R : RingObject} {M : RModObject R}
  (S : Submodule M) : Type :=
  { a : carrier (cmon_setoid M) & smod_mem S a }.

Program Definition smod_setoid {R : RingObject} {M : RModObject R}
  (S : Submodule M) : Setoid (smod_carrier S) := {|
  equiv := fun p q => `1 p ≈ `1 q
|}.
Next Obligation.
  intros R M S; equivalence; now transitivity (`1 y).
Qed.

Definition SubmoduleMod {R : RingObject} {M : RModObject R}
  (S : Submodule M) : RModObject R.
Proof.
  unshelve notypeclasses refine {|
    rm_ab :=
      {| ab_cmon :=
           {| cmon_setoid := {| carrier := smod_carrier S
                              ; is_setoid := smod_setoid S |}
            ; cmon_zero := existT _ (cmon_zero M) (smod_zero S)
            ; cmon_plus := fun p q =>
                existT _ (cmon_plus M (`1 p) (`1 q))
                  (smod_plus S _ _ (`2 p) (`2 q))
            (*
 Only the first projection is compared, so the submodule's
 [Type]-valued membership is carried along and never inspected;
 [sigma_first_PropEquiv] is exactly that observation. 

 --------
 仅比较第一个投影，因此子模块的 [Type] 值的成员资格会随之携带，但从未被检查；[sigma_first_PropEquiv] 就是那个观察值。
*)
            ; cmon_prop :=
                sigma_first_PropEquiv (smod_setoid S)
                  (fun _ _ h => h) (fun _ _ h => h) (cmon_prop M) |}
       ; ab_neg := fun p =>
           existT _ (ab_neg M (`1 p)) (smod_neg S _ (`2 p)) |};
    rm_smul := fun r p =>
      existT _ (rm_smul M r (`1 p)) (smod_smul S r _ (`2 p))
  |}.
  - (* cmon_plus_respects / cmon_plus_respects *)
    intros p p' Hp q q' Hq; simpl in *; now rewrite Hp, Hq.
  - (* cmon_plus_assoc / cmon_plus_assoc *)
    intros p q u; simpl; apply cmon_plus_assoc.
  - (* cmon_plus_comm / cmon_plus_comm *)
    intros p q; simpl; apply cmon_plus_comm.
  - (* cmon_plus_zero_l / cmon_plus_zero_l *)
    intros p; simpl; apply cmon_plus_zero_l.
  - (* ab_neg_respects / AB 阴性尊重 *)
    intros p q Hpq; simpl in *; now rewrite Hpq.
  - (* ab_neg_left / AB阴性左 *)
    intros p; simpl; apply ab_neg_left.
  - (* rm_smul_respects / rm_smul_respects *)
    intros r s Hrs p q Hpq; simpl in *; now rewrite Hrs, Hpq.
  - (* rm_smul_distr_l / rm_smul_distr_l *)
    intros r p q; simpl; apply rm_smul_distr_l.
  - (* rm_smul_distr_r / rm_smul_distr_r *)
    intros r s p; simpl; apply rm_smul_distr_r.
  - (* rm_smul_assoc / rm_乘法_结合律 *)
    intros r s p; simpl; apply rm_smul_assoc.
  - (* rm_smul_one / rm_乘_一 *)
    intros p; simpl; apply rm_smul_one.
Defined.

(* The inclusion of a submodule: the first projection. / 子模块的包含：第一个投影。 *)
Program Definition smod_incl {R : RingObject} {M : RModObject R}
  (S : Submodule M) : SubmoduleMod S ~{RMod R}~> M := {|
  rm_hom := {| cmon_map := {| morphism := fun p : smod_carrier S => `1 p |} |}
|}.
Next Obligation. intros R M S p q Hpq; exact Hpq. Qed.
Next Obligation. intros R M S; simpl; reflexivity. Qed.
Next Obligation. intros R M S p q; simpl; reflexivity. Qed.
Next Obligation. intros R M S r p; simpl; reflexivity. Qed.

Lemma smod_incl_injective {R : RingObject} {M : RModObject R}
  (S : Submodule M) : RModInjective (smod_incl S).
Proof. intros p q Hpq; exact Hpq. Qed.

Lemma smod_incl_monic {R : RingObject} {M : RModObject R}
  (S : Submodule M) : Monic (smod_incl S).
Proof. apply rmod_injective_monic, smod_incl_injective. Qed.

(** ** The quotient relation / ** 商关系 *)

(*
 Since the PR "algebraic carriers are sets" (2026-09-17) the quotient is an
 [RModObject] and so owes [cmon_prop], which forces its equality to be a
 [Prop].  [smod_mem] STAYS [Type]-valued -- the leastness theorems below read
 witnesses out of it -- and the relation is its PROPOSITIONAL TRUNCATION.
 [inhabited] is the truncation; [pequiv_elim_inhabited]
 (Lib/Setoid/Propositional.v) is what gets back out, and the six
 congruence lemmas below each gain one [destruct … as [K]] going in and one
 [constructor] coming out. 

 --------
 自从 PR “代数承载体是集合” (2026-09-17) 后，商是一个 [RModObject]，因此欠 [cmon_prop]，这迫使它的相等性成为一个 [Prop]。[smod_mem] 保持 [Type] 值——下面的最小性定理从中读出证据——并且该关系是它的命题截断。[inhabited] 是截断；[pequiv_elim_inhabited] (Lib/Setoid/Propositional.v) 是得到的返回，而下面的六个同余引理每个都获得一个 [destruct … as [K] 进入和一个 [constructor] 出来。
*)
Definition mquot_rel {R : RingObject} {M : RModObject R} (S : Submodule M)
  (x y : carrier (cmon_setoid M)) : Prop :=
  inhabited (smod_mem S (ab_sub M x y)).

Section QuotientRelation.

Context {R : RingObject}.
Context {M : RModObject R}.
Context (S : Submodule M).

Lemma mquot_rel_of_equiv (x y : carrier (cmon_setoid M)) :
  x ≈ y → mquot_rel S x y.
Proof.
  intro Hxy; unfold mquot_rel.
  constructor.
  apply (smod_at S (a := cmon_zero M)); [| exact (smod_zero S) ].
  rewrite <- Hxy.
  symmetry; apply ab_sub_self.
Qed.

Lemma mquot_rel_refl (x : carrier (cmon_setoid M)) : mquot_rel S x x.
Proof. apply mquot_rel_of_equiv; reflexivity. Qed.

Lemma mquot_rel_sym (x y : carrier (cmon_setoid M)) :
  mquot_rel S x y → mquot_rel S y x.
Proof.
  unfold mquot_rel; intros [K].
  constructor.
  apply (smod_at S (a := ab_neg M (ab_sub M x y))).
  - apply ab_sub_neg.
  - exact (smod_neg S _ K).
Qed.

Lemma mquot_rel_trans (x y z : carrier (cmon_setoid M)) :
  mquot_rel S x y → mquot_rel S y z → mquot_rel S x z.
Proof.
  unfold mquot_rel; intros [K1] [K2].
  constructor.
  apply (smod_at S (a := cmon_plus M (ab_sub M x y) (ab_sub M y z))).
  - apply ab_sub_trans.
  - exact (smod_plus S _ _ K1 K2).
Qed.

(*
 Addition respects the relation.  Where the group case spends
 NORMALITY ([quot_rel_mul]), this spends COMMUTATIVITY, inside
 [ab_sub_plus]. 

 --------
 加法遵守该关系。当群情况消耗 NORMALITY（[quot_rel_mul]）时，它在 [ab_sub_plus] 内消耗交换律（COMMUTATIVITY）。
*)
Lemma mquot_rel_plus (x x' y y' : carrier (cmon_setoid M)) :
  mquot_rel S x x' → mquot_rel S y y' →
  mquot_rel S (cmon_plus M x y) (cmon_plus M x' y').
Proof.
  unfold mquot_rel; intros [K1] [K2].
  constructor.
  apply (smod_at S (a := cmon_plus M (ab_sub M x x') (ab_sub M y y'))).
  - apply ab_sub_plus.
  - exact (smod_plus S _ _ K1 K2).
Qed.

(*
 Negation respects the relation; again no normality, only
 [ab_sub_neg]. 

 --------
 否定尊重该关系；同样没有正规性，只有 [ab_sub_neg]。
*)
Lemma mquot_rel_neg (x x' : carrier (cmon_setoid M)) :
  mquot_rel S x x' → mquot_rel S (ab_neg M x) (ab_neg M x').
Proof.
  unfold mquot_rel; intros [K].
  constructor.
  apply (smod_at S (a := ab_neg M (ab_sub M x x'))).
  - now rewrite ab_sub_neg, ab_sub_neg_neg.
  - exact (smod_neg S _ K).
Qed.

(*
 The scalar action respects the relation.  THIS is the one place the
 submodule's fourth field is spent, and it has no counterpart in the
 group case at all. 

 --------
 标量作用遵循该关系。这是子模的第四个字段被使用的唯一地方，并且在群的情况中完全没有对应。
*)
Lemma mquot_rel_smul (r : carrier (rig_setoid (ring_rig R)))
  (x x' : carrier (cmon_setoid M)) :
  mquot_rel S x x' → mquot_rel S (rm_smul M r x) (rm_smul M r x').
Proof.
  unfold mquot_rel; intros [K].
  constructor.
  apply (smod_at S (a := rm_smul M r (ab_sub M x x'))).
  - apply rm_smul_sub.
  - exact (smod_smul S _ _ K).
Qed.

(*
 Membership IS congruence to zero, in both directions -- up to the
 truncation.

 AN EARLIER REVISION stated the right-hand side as the bare [smod_mem S x].
 Since the PR "algebraic carriers are sets" (2026-09-17) [mquot_rel] is the
 propositional truncation of membership, so the LEFT-to-right direction is
 an elimination of a [Prop] into a [Type] and is refused; the biconditional
 is stated up to [inhabited], which is the exact content.  The direction
 that loses nothing -- membership implies congruence to zero, which is what
 every consumer in the tree actually uses -- is kept separately as
 [mquot_rel_of_mem] below, with its [Type]-valued hypothesis intact. 

 --------
 成员资格在两个方向上都与零同余——直到截断为止。

 早期的修订将右侧表示为纯粹的 [smod_mem S x]。自从 PR“代数承载体是集合”（2026-09-17）以来，[mquot_rel] 是成员资格的命题截断，因此从左到右的方向是将 [Prop] 消去到 [Type] 并被拒绝；双条件在 [inhabited] 下陈述，这就是确切内容。不会丢失任何内容的方向——成员资格意味着与零同余，这正是树中每个使用者实际上使用的——被单独保留为下面的 [mquot_rel_of_mem]，并保持其 [Type] 值的假设。
*)
Lemma mquot_rel_zero_iff (x : carrier (cmon_setoid M)) :
  mquot_rel S x (cmon_zero M) ↔ inhabited (smod_mem S x).
Proof.
  split; intros [K]; unfold mquot_rel in *; constructor.
  - exact (smod_at S (ab_sub_zero_r M x) K).
  - exact (smod_at S (symmetry (ab_sub_zero_r M x)) K).
Qed.

(*
 The half of the biconditional that keeps its [Type]-valued hypothesis:
 nothing is truncated on the way in. 

 --------
 保持其 [Type] 值假设的双条件的另一半：输入过程中没有任何东西被截断。
*)
Lemma mquot_rel_of_mem (x : carrier (cmon_setoid M)) :
  smod_mem S x → mquot_rel S x (cmon_zero M).
Proof.
  intro K; unfold mquot_rel; constructor.
  exact (smod_at S (symmetry (ab_sub_zero_r M x)) K).
Qed.

Program Definition mquot_setoid : Setoid (carrier (cmon_setoid M)) := {|
  equiv := mquot_rel S
|}.
Next Obligation.
  constructor.
  - exact mquot_rel_refl.
  - exact mquot_rel_sym.
  - exact mquot_rel_trans.
Qed.

End QuotientRelation.

Arguments mquot_setoid {R M} S.

(* * ** The quotient module and its projection / * ** 商模及其投影 *)

Definition QuotientMod {R : RingObject} {M : RModObject R}
  (S : Submodule M) : RModObject R.
Proof.
  unshelve notypeclasses refine {|
    rm_ab :=
      {| ab_cmon :=
           {| cmon_setoid := {| carrier := carrier (cmon_setoid M)
                              ; is_setoid := mquot_setoid S |}
            ; cmon_zero := cmon_zero M
            ; cmon_plus := cmon_plus M
            (* [mquot_rel] IS a [Prop] relation, so it is its own mirror. / [mquot_rel] 是一种 [Prop] 关系，所以它是它自己的镜像。 *)
            ; cmon_prop :=
                @PropEquiv_of_relation _ (mquot_setoid S) (mquot_rel S)
                  (fun _ _ h => h) (fun _ _ h => h) |}
       ; ab_neg := ab_neg M |};
    rm_smul := rm_smul M
  |}.
  - (* cmon_plus_respects / cmon_plus_respects *)
    intros x x' Hx y y' Hy; now apply mquot_rel_plus.
  - (* cmon_plus_assoc / cmon_plus_assoc *)
    intros x y z; apply mquot_rel_of_equiv, cmon_plus_assoc.
  - (* cmon_plus_comm / cmon_plus_comm *)
    intros x y; apply mquot_rel_of_equiv, cmon_plus_comm.
  - (* cmon_plus_zero_l / cmon_plus_zero_l *)
    intros x; apply mquot_rel_of_equiv, cmon_plus_zero_l.
  - (* ab_neg_respects / AB 阴性尊重 *)
    intros x y Hxy; now apply mquot_rel_neg.
  - (* ab_neg_left / AB阴性左 *)
    intros x; apply mquot_rel_of_equiv, ab_neg_left.
  - (* rm_smul_respects / rm_smul_respects *)
    intros r s Hrs x y Hxy.
    apply (mquot_rel_trans S _ (rm_smul M r y)).
    + now apply mquot_rel_smul.
    + apply mquot_rel_of_equiv; now rewrite Hrs.
  - (* rm_smul_distr_l / rm_smul_distr_l *)
    intros r x y; apply mquot_rel_of_equiv, rm_smul_distr_l.
  - (* rm_smul_distr_r / rm_smul_distr_r *)
    intros r s x; apply mquot_rel_of_equiv, rm_smul_distr_r.
  - (* rm_smul_assoc / rm_乘法_结合律 *)
    intros r s x; apply mquot_rel_of_equiv, rm_smul_assoc.
  - (* rm_smul_one / rm_乘_一 *)
    intros x; apply mquot_rel_of_equiv, rm_smul_one.
Defined.

(*
 NO NOTATION for the quotient, for the reason Instance/Grp/Quotient.v
 gives: an unscoped infix [/] at level 40 would compete with the
 stdlib's scope-bound division notations in every importing file.
 [QuotientMod S] is written out. 

 --------
 商没有符号的原因，见 Instance/Grp/Quotient.v：会给出：一个未限定范围的中缀 [/] 在 40 级别会与标准库中在每个导入文件中作用域绑定的除法符号相冲突。[QuotientMod S] 已被写出。
*)

(*
 The projection: the identity function, read from the fine setoid into
 the coarse one. 

 --------
 投影：同一函数，从细集合读取到粗集合。
*)
Program Definition mquot_proj {R : RingObject} {M : RModObject R}
  (S : Submodule M) : M ~{RMod R}~> QuotientMod S := {|
  rm_hom := {| cmon_map :=
    {| morphism := fun x : carrier (cmon_setoid M) => x |} |}
|}.
Next Obligation. intros R M S x y Hxy; apply mquot_rel_of_equiv, Hxy. Qed.
Next Obligation. intros R M S; simpl; apply mquot_rel_refl. Qed.
Next Obligation. intros R M S x y; simpl; apply mquot_rel_refl. Qed.
Next Obligation. intros R M S r x; simpl; apply mquot_rel_refl. Qed.

Lemma mquot_proj_kills {R : RingObject} {M : RModObject R}
  (S : Submodule M) (x : carrier (cmon_setoid M)) :
  smod_mem S x →
  cmon_map (rm_hom (mquot_proj S)) x ≈ cmon_zero (QuotientMod S).
Proof.
  intro Hx; simpl.
  exact (mquot_rel_of_mem S x Hx).
Qed.

(*
 Conversely: the projection's kernel is exactly S, as a
 biconditional. 

 --------
 相反：投影的核正好是 S，作为一个双条件。
*)
(* Restated in lockstep with [mquot_rel_zero_iff]: the right-hand side is the truncation. [mquot_proj_kills] above keeps the [Type]-valued direction. / 与 [mquot_rel_zero_iff] 保持一致地重述：右侧是截断。上面的 [mquot_proj_kills] 保持了 [Type] 值的方向。 *)
Lemma mquot_proj_kernel {R : RingObject} {M : RModObject R}
  (S : Submodule M) (x : carrier (cmon_setoid M)) :
  cmon_map (rm_hom (mquot_proj S)) x ≈ cmon_zero (QuotientMod S)
    ↔ inhabited (smod_mem S x).
Proof. exact (mquot_rel_zero_iff S x). Qed.

Lemma mquot_proj_surjective {R : RingObject} {M : RModObject R}
  (S : Submodule M) : RModSurjective (mquot_proj S).
Proof.
  intro x; exists x; simpl; apply mquot_rel_refl.
Qed.

Lemma mquot_proj_epic {R : RingObject} {M : RModObject R}
  (S : Submodule M) : Epic (mquot_proj S).
Proof. apply rmod_surjective_epic, mquot_proj_surjective. Qed.

(* * ** The functor of homomorphisms killing S / * ** 杀死 S 的同态函子 *)

Definition MKills {R : RingObject} {M : RModObject R} (S : Submodule M)
  (K : RModObject R) : Type :=
  { h : M ~{RMod R}~> K
  & ∀ a : carrier (cmon_setoid M), smod_mem S a →
      cmon_map (rm_hom h) a ≈ cmon_zero K }.

Program Definition MKills_Setoid {R : RingObject} {M : RModObject R}
  (S : Submodule M) (K : RModObject R) : Setoid (MKills S K) := {|
  equiv := fun p q => `1 p ≈ `1 q
|}.
Next Obligation.
  intros R M S K.
  constructor.
  - intro p; reflexivity.
  - intros p q Hpq; now symmetry.
  - intros p q u Hpq Hqu; now transitivity (`1 q).
Qed.

Lemma MKills_post {R : RingObject} {M : RModObject R} (S : Submodule M)
  {K K' : RModObject R} (k : K ~{RMod R}~> K') (p : MKills S K)
  (a : carrier (cmon_setoid M)) :
  smod_mem S a → cmon_map (rm_hom (k ∘ `1 p)) a ≈ cmon_zero K'.
Proof.
  intro Ha; simpl; unfold Basics.compose.
  rewrite (`2 p a Ha).
  apply (cmon_map_zero (rm_hom k)).
Qed.

Program Definition MKillsFunctor {R : RingObject} {M : RModObject R}
  (S : Submodule M) : RMod R ⟶ Sets := {|
  fobj := fun K => {| carrier := MKills S K
                    ; is_setoid := MKills_Setoid S K |};
  fmap := fun K K' k =>
    {| morphism := fun p : MKills S K =>
         existT _ (k ∘ `1 p) (MKills_post S k p) |}
|}.
Next Obligation.
  intros R M S K K' k p q Hpq a; simpl in *.
  unfold Basics.compose.
  now rewrite (Hpq a).
Qed.
Next Obligation.
  intros R M S K K' k k' Hk p a; simpl.
  unfold Basics.compose.
  exact (Hk _).
Qed.
Next Obligation. intros R M S K p a; simpl; reflexivity. Qed.
Next Obligation. intros R M S K K' K'' k k' p a; simpl; reflexivity. Qed.

(** ** The mediating homomorphism / ** 中介同态 *)

Section Mediator.

Context {R : RingObject}.
Context {M : RModObject R}.
Context (S : Submodule M).
Context {K : RModObject R}.
Context (p : MKills S K).

(*
 Descent: a homomorphism killing S cannot tell S-congruent elements
 apart.  From S (x - y) one gets h x - h y ≈ 0, whence h x ≈ h y.  This
 is the ONE computation the quotient's universal property costs. 

 --------
 下降：一个将 S 消去的同态无法区分 S-同余的元素。从 S (x - y) 可以得到 h x - h y ≈ 0，因此 h x ≈ h y。这是商的泛性质所付出的唯一运算代价。
*)
Lemma mkills_descends (x y : carrier (cmon_setoid M)) :
  mquot_rel S x y →
  cmon_map (rm_hom (`1 p)) x ≈ cmon_map (rm_hom (`1 p)) y.
Proof.
  intro Hxy.
  apply (fst (ab_sub_eq_zero_iff K _ _)).
  rewrite <- (ab_map_sub (rm_hom (`1 p)) x y).
  (*
 [Hxy] is the TRUNCATED membership since the PR "algebraic carriers are
 sets" (2026-09-17), so it may not be destructed into this [Type]-valued
 `≈` goal directly; [pequiv_to] puts a [Prop] goal in front of the
 elimination and [pequiv_from] returns.  This is
 [pequiv_elim_inhabited] spelled out. 

 --------
 [Hxy] 自从 PR “代数载体是集合”（2026-09-17）以来就是被截断的成员，因此它可能不能直接被析构为这个 [Type] 值的 `≈` 目标；[pequiv_to] 在消去前放置了一个 [Prop] 目标，[pequiv_from] 返回。这个由 [pequiv_elim_inhabited] 详细说明。
*)
  apply (@pequiv_to _ _ (cmon_prop K)).
  destruct Hxy as [Hxy].
  apply pequiv_from.
  exact (`2 p _ Hxy).
Qed.

Program Definition mquot_med : QuotientMod S ~{RMod R}~> K := {|
  rm_hom := {| cmon_map :=
    {| morphism := fun x : carrier (cmon_setoid (QuotientMod S)) =>
                     cmon_map (rm_hom (`1 p)) x |} |}
|}.
Next Obligation. intros x y Hxy; exact (mkills_descends x y Hxy). Qed.
Next Obligation. simpl; apply (cmon_map_zero (rm_hom (`1 p))). Qed.
Next Obligation. intros x y; simpl; apply (cmon_map_plus (rm_hom (`1 p))). Qed.
Next Obligation. intros r x; simpl; apply (rm_map_smul (`1 p)). Qed.

(*
 The mediator's defining triangle holds by reflexivity, the projection
 being the identity function. 

 --------
 调解者的定义三角形通过自反性成立，投影是恒等函数。
*)
Lemma mquot_med_commutes : mquot_med ∘ mquot_proj S ≈ `1 p.
Proof. intro x; simpl; reflexivity. Qed.

Lemma mquot_med_unique (v : QuotientMod S ~{RMod R}~> K)
  (Hv : v ∘ mquot_proj S ≈ `1 p) : mquot_med ≈ v.
Proof. intro x; simpl; symmetry; exact (Hv x). Qed.

End Mediator.

Arguments mquot_med {R M} S {K} p.

(* * ** Mac Lane §III.1 Exercise 5: ⟨A/S, p⟩ is a universal element / * ** 麦克·莱恩 §III.1 练习 5：⟨A/S, p⟩ 是一个泛元 *)

Definition mquot_elem {R : RingObject} {M : RModObject R}
  (S : Submodule M) : MKills S (QuotientMod S) :=
  existT _ (mquot_proj S) (mquot_proj_kills S).

Program Definition mquot_universal_element {R : RingObject}
  {M : RModObject R} (S : Submodule M) :
  AUniversalElement (MKillsFunctor S) (QuotientMod S) := {|
  aue_elem := mquot_elem S
|}.
Next Obligation.
  intros R M S K x.
  unshelve refine {| unique_obj := mquot_med S x |}.
  - exact (mquot_med_commutes S x).
  - intros v Hv; simpl in *.
    exact (mquot_med_unique S x v Hv).
Defined.

(*
 The universal element's underlying homomorphism IS the projection, by
 convertibility -- the [eq_refl] exception to the `≈` discipline, and
 the check that the packaging did not silently rebuild it. 

 --------
 通用元素的基础同态是投影，通过可转换性 —— [eq_refl] 对 `≈` 规范的例外，以及检查包装是否没有悄悄重建它。
*)
Example mquot_universal_elem_is_proj {R : RingObject} {M : RModObject R}
  (S : Submodule M) :
  `1 (@aue_elem _ (MKillsFunctor S) (QuotientMod S)
        (mquot_universal_element S)) = mquot_proj S.
Proof. reflexivity. Qed.

Example mquot_universal_med_is_mquot_med {R : RingObject}
  {M : RModObject R} (S : Submodule M) {K : RModObject R} (x : MKills S K) :
  unique_obj (@aue_universal _ (MKillsFunctor S) (QuotientMod S)
                (mquot_universal_element S) K x)
    = mquot_med S x.
Proof. reflexivity. Qed.

(* * ** The homomorphism theorem, as a biconditional / * ** 同态定理，作为一个双条件 *)

Theorem mod_hom_theorem {R : RingObject} {M K : RModObject R}
  (S : Submodule M) (h : M ~{RMod R}~> K) :
  (∀ a : carrier (cmon_setoid M), smod_mem S a →
     cmon_map (rm_hom h) a ≈ cmon_zero K)
    ↔ (∃! u : QuotientMod S ~{RMod R}~> K, u ∘ mquot_proj S ≈ h).
Proof.
  split.
  - intro Hkill.
    pose (x := existT (fun h : M ~{RMod R}~> K =>
                         ∀ a : carrier (cmon_setoid M), smod_mem S a →
                           cmon_map (rm_hom h) a ≈ cmon_zero K) h Hkill).
    unshelve refine {| unique_obj := mquot_med S x |}.
    + exact (mquot_med_commutes S x).
    + intros v Hv.
      exact (mquot_med_unique S x v Hv).
  - intros [u Hu _] a Ha.
    transitivity (cmon_map (rm_hom u)
                    (cmon_map (rm_hom (mquot_proj S)) a)).
    + symmetry; exact (Hu a).
    + transitivity (cmon_map (rm_hom u) (cmon_zero (QuotientMod S))).
      * apply proper_morphism.
        exact (mquot_proj_kills S a Ha).
      * exact (cmon_map_zero (rm_hom u)).
Qed.

Definition mod_hom_theorem_factor {R : RingObject} {M K : RModObject R}
  (S : Submodule M) (h : M ~{RMod R}~> K)
  (Hkill : ∀ a : carrier (cmon_setoid M), smod_mem S a →
     cmon_map (rm_hom h) a ≈ cmon_zero K) :
  ∃! u : QuotientMod S ~{RMod R}~> K, u ∘ mquot_proj S ≈ h :=
  fst (mod_hom_theorem S h) Hkill.

Definition mod_hom_theorem_kills {R : RingObject} {M K : RModObject R}
  (S : Submodule M) (h : M ~{RMod R}~> K)
  (Hfac : ∃! u : QuotientMod S ~{RMod R}~> K, u ∘ mquot_proj S ≈ h) :
  ∀ a : carrier (cmon_setoid M), smod_mem S a →
    cmon_map (rm_hom h) a ≈ cmon_zero K :=
  snd (mod_hom_theorem S h) Hfac.

(*
   * ** The kernel and the image of a homomorphism, as submodules

   Instance/Mod.v already builds the kernel and the image-quotient as
   OBJECTS ([RModKernel], [RModQuotient]); neither is packaged as a
   submodule there, and neither carries a universal property. 

   --------
   * ** 同态的核与像，作为子模

   Instance/Mod.v 已经将核和像-商构建为
   对象 ( [RModKernel] ,  [RModQuotient] ); 但在此处两者都未被打包为
   子模，也都不具有泛性质。
*)

Program Definition KernelSub {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : Submodule M := {|
  smod_mem := fun a : carrier (cmon_setoid M) =>
                cmon_map (rm_hom f) a ≈ cmon_zero N
|}.
Next Obligation.
  intros R M N f a b Hab Ha; simpl in *.
  now rewrite <- Hab.
Qed.
Next Obligation.
  intros R M N f; simpl; apply (cmon_map_zero (rm_hom f)).
Qed.
Next Obligation.
  intros R M N f a b Ha Hb; simpl in *.
  rewrite (cmon_map_plus (rm_hom f)), Ha, Hb.
  apply cmon_plus_zero_l.
Qed.
Next Obligation.
  intros R M N f r a Ha; simpl in *.
  rewrite (rm_map_smul f), Ha.
  apply rm_smul_zero_r.
Qed.

Example KernelSub_mem {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) (a : carrier (cmon_setoid M)) :
  smod_mem (KernelSub f) a = (cmon_map (rm_hom f) a ≈ cmon_zero N).
Proof. reflexivity. Qed.

(*
 The submodule object of the kernel has the same carrier as
 Instance/Mod.v's [RModKernel], by convertibility. 

 --------
 内核的子模块对象具有与 Instance/Mod.v 的 [RModKernel] 相同的承载者，可通过可转换性得到。
*)
Example KernelSub_carrier_is_RModKernel {R : RingObject}
  {M N : RModObject R} (f : M ~{RMod R}~> N) :
  carrier (cmon_setoid (SubmoduleMod (KernelSub f)))
    = carrier (cmon_setoid (RModKernel f)).
Proof. reflexivity. Qed.

(* The image of f, as a submodule of the codomain. Membership carries the preimage as DATA (the tree's ∃ is [sigT]), so nothing is chosen. / f 的像，作为陪域的子模。成员资格携带原像作为数据（树的 ∃ 是 [sigT]），所以没有被选择。 *)
Program Definition ImageSubmod {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : Submodule N := {|
  smod_mem := fun b : carrier (cmon_setoid N) =>
                { a : carrier (cmon_setoid M) & cmon_map (rm_hom f) a ≈ b }
|}.
Next Obligation.
  intros R M N f b b' Hbb' [a Ha].
  exists a; now rewrite Ha.
Qed.
Next Obligation.
  intros R M N f; simpl.
  exists (cmon_zero M); apply (cmon_map_zero (rm_hom f)).
Qed.
Next Obligation.
  intros R M N f b b' [a Ha] [a' Ha'].
  exists (cmon_plus M a a').
  rewrite (cmon_map_plus (rm_hom f)).
  now rewrite Ha, Ha'.
Qed.
Next Obligation.
  intros R M N f r b [a Ha].
  exists (rm_smul M r a).
  rewrite (rm_map_smul f).
  now rewrite Ha.
Qed.

(*
   * ** Reconciliation with Instance/Mod.v's [RModQuotient]

   [RModQuotient f] is N modulo the image of f, with the relation
   [ab_coset_eq (rm_hom f) x y := { a & x ≈ y + f a }] inherited from
   Instance/Ab.v.  [QuotientMod (ImageSubmod f)] is N modulo the same
   submodule, with the relation [{ a & x - y ≈ f a }].  The two are
   logically equivalent at every pair and the shuffle between them is
   the whole content of the identification; they are NOT convertible
   (pinned as a rejection probe in Test/ProbeModQuotient.v). 

   --------
   * ** 与 Instance/Mod.v 的 [RModQuotient] 的调和  

   [RModQuotient f] 是 N 关于 f 的像的模，关系为 [ab_coset_eq (rm_hom f) x y := { a & x ≈ y + f a }]，继承自 Instance/Ab.v。[QuotientMod (ImageSubmod f)] 是 N 关于相同子模的模，关系为 [{ a & x - y ≈ f a }]。两者在每一对元素上逻辑上等价，而它们之间的混排就是识别的全部内容；它们不可转换（在 Test/ProbeModQuotient.v 中作为拒绝探针固定）。
*)

Section Reconcile.

Context {R : RingObject}.
Context {M N : RModObject R}.
Context (f : M ~{RMod R}~> N).

(*
 Both quotients have the identity function for their comparison legs,
 so every remaining obligation is reflexivity of one relation or the
 other.  The submodule argument is supplied explicitly because the
 goals arrive with [smod_mem (ImageSubmod f)] already delta-expanded to
 its sigma, which leaves nothing for unification to read it off. 

 --------
 两个商的比较分支都有恒等函数，因此每一个剩余的义务都是一个关系或另一个关系的自反性。子模块的论证是显式提供的，因为目标在 [smod_mem (ImageSubmod f)] 已经展开到其 sigma 后到达，这使得统一无法读取它。
*)
#[local] Ltac recon_refl :=
  intros; simpl;
  first [ apply (mquot_rel_refl (ImageSubmod f)) | apply ab_coset_refl ].

Theorem rmod_quotient_relations_agree (x y : carrier (cmon_setoid N)) :
  ab_coset_eq (rm_hom f) x y ↔ mquot_rel (ImageSubmod f) x y.
Proof.
  (*
 Both relations are [Prop]s since the PR "algebraic carriers are sets"
 (2026-09-17) -- the left one an [ex], the right one the [inhabited]
 truncation of the [Type]-valued membership -- so each direction is a
 [Prop]-to-[Prop] elimination and the shuffle is unchanged.  What is new
 is one [constructor] going into the truncation and one [pequiv_from]
 going into the left relation's [pequiv] body. 

 --------
 由于 PR“代数承载是集合”（2026-09-17），两种关系都是 [Prop]；左边的是 [ex]，右边的是 [inhabited] 截断的 [Type] 值成员，因此每个方向都是 [Prop] 到 [Prop] 的消去，并且顺序不变。新的是一个 [constructor] 进入截断，以及一个 [pequiv_from] 进入左边关系的 [pequiv] 主体。
*)
  split.
  - intros [a Ha]; apply pequiv_to in Ha.
    unfold mquot_rel; simpl.
    constructor.
    exists a.
    rewrite Ha.
    symmetry; apply ab_sub_add_cancel.
  - intros [Hm]; simpl in Hm.
    destruct Hm as [a Ha]; simpl in Ha.
    exists a.
    apply pequiv_from.
    rewrite Ha.
    symmetry; apply ab_add_sub_cancel.
Qed.

(*
 The identification, in [RMod R].  Both legs are the identity on
 elements; what they transport is the witness, through the
 biconditional above. 

 --------
 在 [RMod R] 中的识别。两条路线在元素上都是恒等的；它们传递的是见证，通过上面的双条件式。
*)
Program Definition RModQuotient_is_quotient_by_image :
  RModQuotient f ≅[RMod R] QuotientMod (ImageSubmod f) := {|
  to := {| rm_hom := {| cmon_map :=
    {| morphism := fun x : carrier (cmon_setoid (RModQuotient f)) => x |} |} |};
  from := {| rm_hom := {| cmon_map :=
    {| morphism := fun x : carrier (cmon_setoid (QuotientMod (ImageSubmod f)))
                   => x |} |} |}
|}.
Next Obligation.
  intros x y Hxy; exact (fst (rmod_quotient_relations_agree x y) Hxy).
Qed.
Next Obligation. recon_refl. Qed.
Next Obligation. recon_refl. Qed.
Next Obligation. recon_refl. Qed.
Next Obligation.
  intros x y Hxy; exact (snd (rmod_quotient_relations_agree x y) Hxy).
Qed.
Next Obligation. recon_refl. Qed.
Next Obligation. recon_refl. Qed.
Next Obligation. recon_refl. Qed.
Next Obligation. recon_refl. Qed.
Next Obligation. recon_refl. Qed.

(* And the projections agree under it: the identification carries Instance/Mod.v's projection to this file's. / 并且在它之下投影是一致的：该标识将 Instance/Mod.v 的投影带到此文件的投影。 *)
Lemma RModQuotient_proj_agrees :
  to RModQuotient_is_quotient_by_image ∘ rmod_quot_proj f
    ≈ mquot_proj (ImageSubmod f).
Proof. recon_refl. Qed.

End Reconcile.

(* * ** Quotients by coextensive submodules agree / * ** 由同余子模得到的商模一致 *)

Program Definition mquot_congr {R : RingObject} {M : RModObject R}
  (S S' : Submodule M)
  (H1 : ∀ a : carrier (cmon_setoid M), smod_mem S a → smod_mem S' a)
  (H2 : ∀ a : carrier (cmon_setoid M), smod_mem S' a → smod_mem S a) :
  QuotientMod S ≅[RMod R] QuotientMod S' := {|
  to := {| rm_hom := {| cmon_map :=
    {| morphism := fun x : carrier (cmon_setoid (QuotientMod S)) => x |} |} |};
  from := {| rm_hom := {| cmon_map :=
    {| morphism := fun x : carrier (cmon_setoid (QuotientMod S')) => x |} |} |}
|}.
(*
 [simpl] before the elimination: the goal is an application of the [equiv]
 projection, whose ascribed sort is [Type], and [mquot_rel] is the
 [inhabited] truncation of membership since the PR "algebraic carriers are
 sets" (2026-09-17). 

 --------
 消除前的 [simpl]：目标是 [equiv] 投影的一个应用，其归属类型是 [Type]，并且 [mquot_rel] 是 [inhabited] 的隶属截断，因为 PR“代数载体是集合”（2026-09-17）。
*)
Next Obligation.
  intros R M S S' H1 H2 x y Hxy; simpl in Hxy |- *.
  destruct Hxy as [Hxy]; constructor; exact (H1 _ Hxy).
Qed.
Next Obligation. intros R M S S' H1 H2; simpl; apply mquot_rel_refl. Qed.
Next Obligation. intros R M S S' H1 H2 x y; simpl; apply mquot_rel_refl. Qed.
Next Obligation. intros R M S S' H1 H2 r x; simpl; apply mquot_rel_refl. Qed.
Next Obligation.
  intros R M S S' H1 H2 x y Hxy; simpl in Hxy |- *.
  destruct Hxy as [Hxy]; constructor; exact (H2 _ Hxy).
Qed.
Next Obligation. intros R M S S' H1 H2; simpl; apply mquot_rel_refl. Qed.
Next Obligation. intros R M S S' H1 H2 x y; simpl; apply mquot_rel_refl. Qed.
Next Obligation. intros R M S S' H1 H2 r x; simpl; apply mquot_rel_refl. Qed.
Next Obligation. intros R M S S' H1 H2 x; simpl; apply mquot_rel_refl. Qed.
Next Obligation. intros R M S S' H1 H2 x; simpl; apply mquot_rel_refl. Qed.

(* * ** The degenerate submodules, named and separated / * ** 退化子模，已命名并分开 *)

Program Definition TrivialSub {R : RingObject} (M : RModObject R) :
  Submodule M := {|
  smod_mem := fun a : carrier (cmon_setoid M) => a ≈ cmon_zero M
|}.
Next Obligation.
  intros R M a b Hab Ha; simpl in *; now rewrite <- Hab.
Qed.
Next Obligation. intros R M; simpl; reflexivity. Qed.
Next Obligation.
  intros R M a b Ha Hb; simpl in *.
  rewrite Ha, Hb; apply cmon_plus_zero_l.
Qed.
Next Obligation.
  intros R M r a Ha; simpl in *.
  rewrite Ha; apply rm_smul_zero_r.
Qed.

Program Definition TotalSub {R : RingObject} (M : RModObject R) :
  Submodule M := {|
  smod_mem := fun _ : carrier (cmon_setoid M) => poly_unit
|}.
Next Obligation. intros R M a b Hab Ha; exact ttt. Qed.
Next Obligation. intros R M; exact ttt. Qed.
Next Obligation. intros R M a b Ha Hb; exact ttt. Qed.
Next Obligation. intros R M r a Ha; exact ttt. Qed.

(*
 Both directions survive the truncation.  The forward one is the place
 [pequiv_elim_inhabited] earns its keep: the conclusion `≈` is
 [Type]-valued, so [pequiv_to] puts a [Prop] goal in front of the
 elimination and [pequiv_from] returns.  An earlier revision was
 [exact (ab_sub_eq_zero_iff M x y)], the two relations then being the same
 [Type]. 

 --------
 两个方向都能经受截断。正向方向是 [pequiv_elim_inhabited] 发挥作用的地方：结论 `≈` 是 [Type] 值，因此 [pequiv_to] 在消除前设定了一个 [Prop] 目标，并且 [pequiv_from] 返回。早期的修订是 [exact (ab_sub_eq_zero_iff M x y)]，当时这两个关系相同 [Type]。
*)
Lemma mquot_trivial_iff {R : RingObject} (M : RModObject R)
  (x y : carrier (cmon_setoid M)) :
  mquot_rel (TrivialSub M) x y ↔ x ≈ y.
Proof.
  split.
  - intro H.
    apply (@pequiv_to _ _ (cmon_prop M)).
    destruct H as [H].
    apply pequiv_from.
    exact (fst (ab_sub_eq_zero_iff M x y) H).
  - intro H; constructor.
    exact (snd (ab_sub_eq_zero_iff M x y) H).
Qed.

Lemma mquot_total_collapses {R : RingObject} (M : RModObject R)
  (x y : carrier (cmon_setoid M)) : mquot_rel (TotalSub M) x y.
Proof. exact (inhabits ttt). Qed.

(*
   * ** Non-vacuity: ℤ modulo 2ℤ

   Everything above holds for every module, so nothing yet shows the
   quotient does not collapse.  Instance/Mod.v's [Int_RMod] (ℤ as a
   module over itself) with the even integers is the smallest witness
   with a PROPER NONTRIVIAL submodule, and ℤ's setoid is Leibniz
   equality (Theory/Algebra/Rig.v's [Z_eqT]), so every check below is a
   computation. 

   --------
   * ** 非空性：ℤ 模 2ℤ

   上述内容对每个模都适用，所以目前还没有显示商模不会塌缩。Instance/Mod.v 中的 [Int_RMod]（ℤ 作为自身的模）与偶整数是具有**适当的非平凡子模**的最小例子，并且 ℤ 的集合等价关系是莱布尼茨相等（Theory/Algebra/Rig.v 的 [Z_eqT]），因此下面的每个检查都是计算。
*)

(*
 ℤ's module operations, pinned by convertibility -- the [eq_refl]
 exception to the `≈` discipline.  These are what let [ring] and [lia]
 see the goals below: both tactics read the ring structure off the
 SYNTACTIC type of the equation and neither sees through [carrier]
 (the finding Instance/Rng/Algebras/Associative.v records for the same
 reason). 

 --------
 ℤ 的模运算，由可转换性固定——对 `≈` 规范的 [eq_refl] 例外。这些使得 [ring] 和 [lia] 能看到下面的目标：两种策略都从方程的语法类型中读取环结构，而且都无法看透 [carrier]（出于同样的原因，Instance/Rng/Algebras/Associative.v 中的记录也是如此）。
*)
Example int_zero_is_0 : cmon_zero Int_RMod = 0%Z := eq_refl.
Example int_plus_is_add (a b : Z) : cmon_plus Int_RMod a b = (a + b)%Z :=
  eq_refl.
Example int_neg_is_opp (a : Z) : ab_neg Int_RMod a = (- a)%Z := eq_refl.
Example int_smul_is_mul (r a : Z) : rm_smul Int_RMod r a = (r * a)%Z :=
  eq_refl.
Example int_sub_is_minus (a b : Z) : ab_sub Int_RMod a b = (a - b)%Z :=
  eq_refl.

Definition ZEvenMod (a : Z) : Type := { k : Z & a = (2 * k)%Z }.

Program Definition EvenSub : Submodule Int_RMod := {|
  smod_mem := ZEvenMod
|}.
Next Obligation.
  intros a b Hab [k Hk]; simpl in *.
  exists k; now subst.
Qed.
Next Obligation. exists 0%Z; reflexivity. Qed.
Next Obligation.
  intros a b [k Hk] [l Hl].
  rewrite int_plus_is_add, Hk, Hl.
  exists (k + l)%Z; ring.
Qed.
Next Obligation.
  intros r a [k Hk].
  rewrite int_smul_is_mul, Hk.
  exists (r * k)%Z; ring.
Qed.

(* 2ℤ is PROPER: 1 is not even. / 2ℤ 是严格的：1 不是偶数。 *)
Theorem EvenSub_proper : smod_mem EvenSub 1%Z → False.
Proof. intros [k Hk]; lia. Qed.

(* 2ℤ is NONTRIVIAL: it contains 2, which is not zero. / 2ℤ 是非平凡的：它包含 2，而 2 不是零。 *)
Theorem EvenSub_nontrivial :
  smod_mem EvenSub 2%Z
  * ((2%Z : carrier (cmon_setoid Int_RMod)) ≈ cmon_zero Int_RMod → False).
Proof.
  split.
  - exists 1%Z; reflexivity.
  - simpl; discriminate.
Qed.

(* THE QUOTIENT DOES NOT COLLAPSE: 1 stays apart from 0 in ℤ/2ℤ. / 商不会塌缩：1在ℤ/2ℤ中与0保持分离。 *)
Theorem Z_mod_2Z_not_collapsed : mquot_rel EvenSub 1%Z 0%Z → False.
Proof.
  intros [[k Hk]]; rewrite int_sub_is_minus in Hk; lia.
Qed.

(* But it does collapse 2 into 0, so the projection is not injective and the quotient is a genuine quotient rather than a relabelling of ℤ. / 但它确实将 2 压缩为 0，所以投影不是单射，并且商是一个真正的商，而不是 ℤ 的重新标记。 *)
Theorem Z_mod_2Z_collapses_two :
  cmon_map (rm_hom (mquot_proj EvenSub)) 2%Z
    ≈ cmon_map (rm_hom (mquot_proj EvenSub)) 0%Z.
Proof. constructor; exists 1%Z; reflexivity. Qed.

Theorem mquot_proj_EvenSub_not_injective :
  RModInjective (mquot_proj EvenSub) → False.
Proof.
  intro Hinj.
  pose proof (Hinj 2%Z 0%Z Z_mod_2Z_collapses_two) as E.
  vm_compute in E; discriminate E.
Qed.

(* The scalar action survives the quotient nondegenerately: 3·1 is congruent to 1 and not to 0. / 标量作用在商上非退化地遗存：3·1 同余于 1 而不同于 0。 *)
Example Z_mod_2Z_smul_three :
  mquot_rel EvenSub (rm_smul Int_RMod 3%Z 1%Z) 1%Z.
Proof. constructor; exists 1%Z; reflexivity. Qed.

Theorem Z_mod_2Z_smul_three_not_zero :
  mquot_rel EvenSub (rm_smul Int_RMod 3%Z 1%Z) 0%Z → False.
Proof.
  intros [[k Hk]].
  rewrite int_sub_is_minus, int_smul_is_mul in Hk.
  lia.
Qed.

(* The kernel of the projection is exactly 2ℤ, in both directions. / 投影的核在两个方向上恰好是 2ℤ。 *)
(* Restated up to the truncation, in lockstep with [mquot_proj_kernel]. / 在截断处重新表述，与 [mquot_proj_kernel] 保持同步。 *)
Lemma EvenSub_is_kernel_of_proj (a : Z) :
  smod_mem (KernelSub (mquot_proj EvenSub)) a ↔ inhabited (smod_mem EvenSub a).
Proof. exact (mquot_proj_kernel EvenSub a). Qed.
