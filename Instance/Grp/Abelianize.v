Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Adjunction.Natural.Transformation.Universal.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Epi.
Require Import Category.Instance.Grp.Center.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Abelianization.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.


(*
   * * Abelianization as a universal arrow, and the adjunction twice over

   Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
   §III.1 Exercise 3 [maclane:III.1:ex3]: the factor-commutator group
   G/[G, G] is the value at G of a left adjoint to the inclusion of
   abelian groups in groups, and the projection p_G : G → G/[G, G] is
   the universal arrow from G to that inclusion.  Riehl, “Category
   Theory in Context”, Dover 2016, §4.2 Exercise ii asks for the same
   adjunction built the OTHER way, from a unit, a counit, and the two
   triangle identities proved by hand.  Both are delivered here, and
   then related.
   nLab: https://ncatlab.org/nlab/show/abelianization

   WHAT IS CONSUMED RATHER THAN REBUILT.  Instance/Grp/Abelianization.v
   already carries the whole construction, and nothing of it is
   repeated below:

   - [AbelianizationOb] — G/[G, G] as a setoid quotient: the
   SAME carrier as G under the coarser relation [abel_eq],
   so commutativity of the quotient is the generating constructor
   [inc_comm] rather than a computation;
   - [Abelianization_Functor : Grp ⟶ Ab];
   - [Ab_to_Grp : Ab ⟶ Grp] with its object part
   [Ab_to_GrpOb] — the evident inclusion, which IS the
   forgetful functor of this exercise;
   - [abel_proj] and [abel_projection], the natural
   family of projections [Id Grp ⟹ Ab_to_Grp ◯
   Abelianization_Functor] whose components are the IDENTITY on
   elements.  That transformation IS the unit of the adjunction
   below; it is used verbatim, not re-derived;
   - [hom_to_abelian_kills] — a homomorphism into an abelian
   group kills every commutator element.  That donor file's header
   calls it “the descent germ”, and this file is what spends it:
   [abel_kills] is the single place where it is used, and every
   mediating morphism below factors through that one lemma.

   THE ISSUE'S “Current state” PARAGRAPH IS STALE.  It asserts that
   the tree has no categories of groups or abelian groups.  It has
   both: [Grp] (Instance/Grp.v) and [Ab] (Instance/Ab.v), each
   with a forgetful functor to [Sets] ([Grp_Forget], Instance/Grp.v;
   [Ab_Forget], Instance/Ab.v).  The abelianization functor and the
   inclusion have existed since Instance/Grp/Abelianization.v landed,
   and that file's own header records the adjunction as “close at hand”
   and “not built here”.  This file builds it.

   THE TWO ROUTES, AND EXACTLY HOW THEY RELATE.  This has to be stated
   carefully, because the two routes do not even produce adjunctions of
   the SAME TYPE.

   Route one is the universal-arrow plumbing of Theory/Universal/Arrow.v
   — the route Instance/Grp/Free.v and Instance/Mod/Free.v take.
   [abelianize_universal] states the universal mapping property,
   [universal_arrow_from_UMP] packages it as
   [abelianize_universal_arrow], and then
   [LeftAdjointFunctorFromUniversalArrows] and
   [AdjunctionFromUniversalArrows] produce a functor and an adjunction
   with no further proof.  But the functor they produce is the
   generic [abelianize_left], NOT [Abelianization_Functor]: the generic
   machinery defines the action on arrows by unique factorization
   through the [Qed]-opaque [ump_universal_arrows], where the donor
   file defines it as the underlying map of the homomorphism.  So
   [abelianize_adjunction] has type [abelianize_left ⊣ Ab_to_Grp].

   Route two is [Adjunction_from_Transform]
   (Adjunction/Natural/Transformation/Universal.v), fed the unit
   [abel_projection], the counit [abelianize_counit] built here, and
   both triangle identities proved by hand.  It lands exactly at
   [abelianize_adjunction_via_transform : Abelianization_Functor ⊣
   Ab_to_Grp].

   The relation between them is measured at three grades, strict
   first:

   - OBJECTS AGREE ON THE NOSE.  [abelianize_left_obj] is [eq_refl]:
   [abelianize_left G] and [Abelianization_Functor G] are the same
   term.  This is what makes the comparisons below even well
   typed — a morphism out of one is a morphism out of the other.
   - ARROWS AGREE ONLY UP TO [≈].  [abelianize_left_fmap] is proved
   from the uniqueness clause of the universal property;
   [probe_left_fmap_strict] pins the [eq_refl] REFUSAL, whose cause
   is that [ump_universal_arrows] is a [Qed] Corollary, so
   [unique_obj (ump_universal_arrows …)] reduces to nothing.
   [abelianize_left_iso] packages the two facts as an isomorphism
   in the functor category [[Grp, Ab]] whose components are
   identities.
   - THE FORWARD TRANSPOSES AGREE AT LEIBNIZ EQUALITY.
   [abelianize_routes_agree]'s first component is [eq_refl] at an
   ARBITRARY G, A and f: both routes send f to [fmap[Ab_to_Grp] f ∘
   abel_proj G], the same term.  On route one this works because
   [universal_arrow_from_UMP] stores the supplied morphism as the
   second projection of the comma object it builds, so [arrow]
   reduces to [abel_proj G] ([abelianize_arrow_is_proj], [eq_refl]).
   The BACKWARD transposes agree only up to [≈], for the same
   opacity reason, and that half is proved through the uniqueness
   clause.  The whole [SetoidMorphism] records and the whole
   adjunction records do not agree even for the forward leg
   ([probe_routes_to_record]), the residue being the rebuilt
   [proper_morphism] certificates.

   THE DIAGNOSIS IS DISCRIMINATING, NOT A BLANKET APPEAL TO OPACITY.
   Theory/Adjunction.v DERIVES [unit] and [counit] as the transposes of
   identities, so what they compute to has to be checked rather than
   assumed, and the two routes come apart exactly where predicted:

   - both routes' derived UNITS compute — [abelianize_unit_computes]
   and [abelianize_unit_computes_via_transform] are both [eq_refl],
   because the unit is a FORWARD transpose and the forward
   transposes are the same term;
   - route two's derived COUNIT computes
   ([abelianize_counit_computes_via_transform], [eq_refl]) while
   route one's does not ([probe_counit_route_one]).  Same derived
   constant, same statement shape, opposite outcomes: route two's
   backward transpose is [counit ∘ fmap[F] −] with both factors
   transparent, route one's is [unique_obj (ump_universal_arrows …)]
   and is opaque.

   WHAT THE COUNIT CONCRETELY IS.  Mac Lane §IV.2's slogan for a free
   construction — the counit sends a formal combination to the actual
   combination, exhibiting an object as a quotient of the free object
   on its own elements — DOES NOT TRANSFER to this row, and the file
   declines the analogy rather than stretching it.  Abelianization is
   not free on underlying data; it is a reflector onto a subcategory
   that is already sitting inside [Grp].  Concretely, at an abelian
   group A the relation [abel_eq (Ab_to_GrpOb A)] and A's own [≈]
   coincide — that biconditional is exactly the two respectfulness
   obligations of [abelianize_counit_iso] — so the counit component is
   the IDENTITY FUNCTION on elements
   ([abelianize_counit_computes], [eq_refl]) and is INVERTIBLE
   ([abelianize_counit_iso]) — its inverse is the same identity
   function read the other way.  In words: the counit exhibits an
   abelian group as its own abelianization.  That is the opposite
   behaviour from a free-construction counit, which is a genuine
   evaluation and in general far from invertible.  [Ab_to_Grp] is
   proved full and faithful here, so the shape is exactly that of a
   reflective subcategory — but NO [Reflective] instance is claimed:
   Construction/Reflective.v is stated over Construction/Subcategory.v's
   [Sub] inclusions and [Ab_to_Grp] is not one of those, its objects
   being [AbObject] records rather than [GrpObject]s satisfying a
   predicate.  CORRECTION (#370): a [Reflective] record is now built,
   over a different subcategory.  Instance/Grp/Abelianize/Reflective.v
   cuts the abelian groups out of [Grp] by a commutativity predicate
   ([AbGrp_Sub]), proves [Ab_Reflective_in_Grp : Reflective AbGrp_Sub],
   and relates it to this file's adjunction by the equivalence
   [Ab_AbGrp_Equivalence] of [Ab] with [AbGrp_Sub] and by factorizations
   of both its functors, [Ab_to_Grp] and [Abelianization_Functor],
   through [AbGrp_Sub].  The structural reason above still holds of
   [Ab_to_Grp] itself.

   NON-VACUITY, PROVED BY MAPPING OUT.  No induction on the
   quotienting generation [InCommutator] can yield a negative, so every
   separation below goes through a homomorphism into a concrete group.
   The witness is S₃ (Instance/Grp/TwoFunctors.v), the in-tree
   nonabelian group.  [abelianize_S3_identifies] shows the projection
   merges the commutator of the two generators with the unit, while the
   donor's [commutator_S3_nontrivial] shows those two elements are
   apart in S₃: the abelianization of S₃ is a PROPER quotient.  It is
   also not the trivial group, and that is shown BY EXERCISING THE
   UNIVERSAL PROPERTY rather than by inspection: [AbTwo] is ℤ/2 as an
   [AbObject], [ab_two_sign] is the sign character read into it, and
   the mediator [abelianize_med ab_two_sign] produced by
   [abelianize_universal] separates the class of the reflection from
   the class of the unit ([abelianize_S3_separates]), computing to
   [grp_two_one] by [eq_refl].

   UNIVERSES, read off the CONSTRAINT BLOCKS rather than the binders,
   for every constant this file declares.  Of the 63 named constants,
   SIX carry [Set] in a constraint block, and all six are S₃ witnesses:
   [ab_two_sign], [abelianize_S3_med_s], [abelianize_S3_med_unit],
   [abelianize_S3_separates], [abelianize_S3_factors] and the control
   [probe_ctl_sign].  The cause is located: their types mention
   [TwoFunctors.S3@{Set}], S₃ being carried on a [bool] component and
   [bool : Set].  It is NOT [AbTwo]'s doing — [AbTwo@{u u0 u1 u2 u3 u4
   u5}] has an empty [Set]-free block of its own, and neither is it
   Instance/Grp.v's [Grp_trivial]/[Grp_Zero] pin (disclosed in
   Instance/Grp/Quotient/Colimit.v, and lifted by #450), neither of which
   is used anywhere in this file.  Two further S₃ statements,
   [abelianize_S3_identifies] and [abelianize_S3_proper], display
   [Set] inside a universe INSTANCE ([abel_eq@{u u Set}]) while
   acquiring no [Set] CONSTRAINT: an instance is not a constraint.

   THE GENERAL DEVELOPMENT IS [Set]-FREE.  [abel_kills],
   [abelianize_med], [abelianize_universal],
   [abelianize_universal_arrow], [abelianize_left],
   [abelianize_adjunction], [abelianize_counit],
   [abelianize_transform], [abelianize_adjunction_via_transform],
   [abelianize_routes_agree], [abelianize_counit_iso],
   [abelianize_left_iso], [Ab_to_Grp_Full] and [Ab_to_Grp_Faithful]
   all have [Set]-free constraint blocks and are polymorphic in
   [Grp]'s and [Ab]'s universes.  No lift of the S₃ witnesses is
   attempted, and the pin is not claimed unavoidable.

   AXIOMS.  90/90 constants are closed under the global context: the
   63 the [.glob] records as [def] or [prf] after discarding the eight
   [Fail]-named entries, which name no constant, plus 27 [Program]
   obligations, which the [.glob] does not record at all and which
   have to be queried by their fully qualified names.

   NO EXPLICIT UNIVERSE INSTANCE IS WRITTEN ON ANY FUNCTOR OR
   ADJUNCTION in this file.  The number of universe binders [Functor]
   and [Adjunction] take differs between Coq 8.19/8.20 and Rocq 9.1, so
   such an annotation is not portable.  No universe fact needed
   guarding here either: all seven negatives below are CONVERSION
   failures and none is a formability (universe) one, so the universe
   findings above are MEASURED but not guarded, and the file says so
   rather than calling them pinned.

   WHAT IS NOT DELIVERED.
   - No [Reflective] instance, for the structural reason above, and
   no identification of [Ab] with a full subcategory of [Grp] in
   Construction/Subcategory.v's sense.  CORRECTION (#370): both are
   in Instance/Grp/Abelianize/Reflective.v, the second up to the
   equivalence [Ab_AbGrp_Equivalence] of [Ab] with [AbGrp_Sub].
   - No idempotency: [Abelianization_Functor ◯ Ab_to_Grp ≅ Id[Ab]]
   follows componentwise from [abelianize_counit_iso], but the
   natural isomorphism in [[Ab, Ab]] is not assembled, and no
   [IdempotentMonad] statement is made.  CORRECTION (#370): one is
   made for the subcategory presentation, Instance/Grp/Abelianize/
   Reflective.v's [AbGrp_IdempotentMonad]; the natural isomorphism
   in [[Ab, Ab]] is still not assembled.
   - No comparison with Construction/Reflective/Idempotent.v, and no
   Eilenberg–Moore reading.  CORRECTION (#370): both are made at
   [AbGrp_Sub] in Instance/Grp/Abelianize/Reflective.v:
   [AbGrp_IdempotentMonad] is Idempotent.v's
   [Reflective_IdempotentMonad] at [Ab_Reflective_in_Grp], and
   [AbGrp_Incl_Monadic] is Construction/Reflective/Monadic.v's
   Eilenberg–Moore equivalence there.
   - No uniqueness-up-to-unique-isomorphism corollary: it would be
   [universal_arrow_unique] instantiated here, and it is not
   instantiated.
   - Nothing about the abelianization of a FREE group, so no bridge
   to Instance/Grp/Free.v and no free-abelian-group functor.
   - The universal property is not restated as a representability
   statement, and no [Representable] instance is registered.
   - The Fail probes below live IN THIS FILE rather than in a
   Test/Probe module, because this change is confined to one file;
   they are not wired into any make target.  There are SEVEN
   negatives, all of ONE KIND (conversion — each stripped once and
   confirmed to report a genuine “cannot unify”), against 23
   positive controls and one instrument check.  Every constant the
   negatives name is rename-simulated 19/19.  The fourteen donors
   ([Abelianization_Functor], [Ab_to_GrpOb], [GrpTwo], [Ab_to_Grp],
   [Grp], [Ab], [cmon_map], [cmon_setoid], [carrier], [adj], [to],
   [from], [fmap], [counit]) were renamed throughout this file,
   which is what an upstream rename would do to it; the five local
   ones ([abelianize_left], [abelianize_adjunction],
   [abelianize_adjunction_via_transform], [abelianize_counit_hom],
   [AbTwo]) were renamed at their declaration sites only.  In
   every one of the nineteen cases a POSITIVE command breaks, so
   no negative can go vacuously green. 

   --------
   * * 作为通用箭头的阿贝尔化，以及两次的伴随关系

   Mac Lane，《为在职数学家而作的范畴论》，第二版，
   §III.1 练习 3  [maclane:III.1:ex3]：因子-换位子群
   G / [G, G] 是阿贝尔群在群中的包含的左伴随函子的在 G 上的值，投射 p_G : G → G / [G, G] 是从 G 到该包含的通用箭头。Riehl，《上下文中的范畴论》，Dover 2016，§4.2 练习 ii 要求用另一种方式构建相同的伴随，从单位元、余单位元以及手工证明的两个三角形恒等式中得到。这里都给出了，并随后进行了关联。
   nLab：https://ncatlab.org/nlab/show/abelianization

   被消耗而非重构的内容。Instance/Grp/Abelianization.v 已经包含整个构造，下面没有重复内容：- [AbelianizationOb] — G/[G, G] 作为集合等价的商：在较粗关系 [abel_eq] 下与 G 拥有相同的载体，因此商的交换性是由生成构造 [inc_comm] 而非计算得到的；
   - [Abelianization_Functor : Grp ⟶ Ab]；
   - [Ab_to_Grp : Ab ⟶ Grp] 及其对象部分 [Ab_to_GrpOb] — 显而易见的包含，它就是本练习中的遗忘函子；
   - [abel_proj] 和 [abel_projection]，自然投影族 [Id Grp ⟹ Ab_to_Grp ◯ Abelianization_Functor]，其分量在元素上是恒等映射。该变换就是下面伴随关系的单位；它是逐字使用的，而非重新推导的；
   - [hom_to_abelian_kills] — 一个映射到阿贝尔群的同态会消去每个对换元素。那个捐赠者文件的头部把它称为“下降种子”，而这个文件正是使用它的地方：
   [abel_kills] 是唯一使用它的地方，并且下面每个中介同态都通过那个引理来分解。

   该问题的“当前状态”段落已经过时。它声称该树没有群或阿贝尔群的分类。实际上它都有：[Grp]（Instance/Grp.v）和 [Ab]（Instance/Ab.v），每一个都有一个忘记函子到 [Sets]（[Grp_Forget]，Instance/Grp.v；[Ab_Forget]，Instance/Ab.v）。自从 Instance/Grp/Abelianization.v 出现以来，阿贝尔化函子和包含函子就已经存在，并且该文件自己的头部记录了这个伴随关系为“触手可及”和“这里不构建”。这个文件构建了它。这两条路线，以及它们之间的具体关系。必须小心说明，因为这两条路线甚至不会产生相同类型的伴随。

   路线一是 Theory/Universal/Arrow.v 的泛箭管道——Instance/Grp/Free.v 和 Instance/Mod/Free.v 所走的路线。[abelianize_universal] 陈述了泛映射性质，[universal_arrow_from_UMP] 将其封装为 [abelianize_universal_arrow]，然后 [LeftAdjointFunctorFromUniversalArrows] 和 [AdjunctionFromUniversalArrows] 生成了一个函子和一个伴随关系，无需进一步证明。但它们生成的函子是通用的 [abelianize_left]，而不是 [Abelianization_Functor]：通用机制通过 [Qed] 不透明的 [ump_universal_arrows] 的唯一分解来定义箭头上的作用，而 donor 文件将其定义为同态的底层映射。因此 [abelianize_adjunction] 的类型是 [abelianize_left ⊣ Ab_to_Grp]。路线二是 [Adjunction_from_Transform]（伴随/自然/变换/泛性质.v），输入单位 [abel_projection]，柯单位 [abelianize_counit] 在此处构建，并且两个三角恒等式均手工证明。它精确地到达 [abelianize_adjunction_via_transform : Abelianization_Functor ⊣ Ab_to_Grp]。

   它们之间的关系在三个等级上测量，首先是严格的：- 对象在鼻子上相同。[abelianize_left_obj] 是 [eq_refl]：[abelianize_left G] 和 [Abelianization_Functor G] 是相同的术语。这正是使下面的比较甚至类型一致的原因——一个的态射是另一个的态射。- 箭头仅在 [≈] 下相同。[abelianize_left_fmap] 是由泛性质的唯一性条款证明的；[probe_left_fmap_strict] 固定了 [eq_refl] 的拒绝，其原因是 [ump_universal_arrows] 是 [Qed] 的推论，因此 [unique_obj (ump_universal_arrows …)] 简化为无。[abelianize_left_iso] 将这两个事实打包为函子范畴 [[Grp, Ab] 中的一个同构，其分量是恒等映射。- 正向转置在莱布尼茨等式下相同。[abelianize_routes_agree] 的第一个分量是 [eq_refl] 在任意 G、A 和 f 上：两条路径都将 f 发送到 [fmap[Ab_to_Grp] f ∘ abel_proj G]，相同的项。在第一条路径上这是可行的，因为 [universal_arrow_from_UMP] 将提供的态射存储为它构建的逗号对象的第二投影，因此 [arrow] 简化为 [abel_proj G] ( [abelianize_arrow_is_proj] , [eq_refl] )。后向转置只在 [≈] 下相符，出于相同的不透明性原因，这一半通过唯一性条款进行证明。整个 [SetoidMorphism] 记录和整个伴随记录即便对于前向段 ( [probe_routes_to_record] ) 也不一致，剩余部分是重建的 [proper_morphism] 证明书。诊断是有区别的，而不是对不透明性的一概而论的诉求。
   Theory/Adjunction.v 推导出 [unit] 和 [counit] 作为恒等式的转置，因此必须检查它们计算的结果，而不能假设。正如预测的那样，两条路径在以下地方分岔：

   - 两条路径派生的单位（UNIT）计算结果——[abelianize_unit_computes] 和 [abelianize_unit_computes_via_transform] 都是 [eq_refl]，因为单位是前向转置（FORWARD transpose），且前向转置是同一个项；
   - 第二条路径派生的余单位（COUNIT）计算结果为 ([abelianize_counit_computes_via_transform], [eq_refl])，而第一条路径的余单位计算结果则不是 ([probe_counit_route_one])。相同的派生常数，相同的语句形式，但结果相反：第二条路径的后向转置（backward transpose）是 [counit ∘ fmap[F] —] 且两个因子都是透明的，第一条路径的后向转置是 [unique_obj (ump_universal_arrows …)]，并且是不透明的。计量辅单位具体是什么。Mac Lane §IV.2 对自由构造的口号——辅单位将一个形式组合发送到实际组合，将一个对象展示为其自身元素上的自由对象的商——并不适用于这一行，并且该文件拒绝这种类比而不是强行应用。阿贝尔化并不是基于底层数据的自由构造；它是一个映射器，映射到已经位于  [Grp]  内的子范畴。具体来说，对于阿贝尔群 A，关系  [abel_eq (Ab_to_GrpOb A)]  与 A 自己的  [≈]  重合——该双向条件正好对应  [abelianize_counit_iso]  的两个尊重义务——因此辅单位分量是元素上的恒等函数 ( [abelianize_counit_computes] ,  [eq_refl] )，并且是可逆的 ( [abelianize_counit_iso] )——它的逆就是将同一恒等函数反向读取。用文字来说：余单位将一个阿贝尔群显示为它自身的阿贝尔化。这与自由构造余单位的行为完全相反，后者是真正的求值，并且通常远非可逆。在这里已经证明了 [Ab_to_Grp] 是满且忠实的，所以其形式正好像一个反射子范畴——但没有声称 [Reflective] 的实例：Construction/Reflective.v 是在 Construction/Subcategory.v 的 [Sub] 包含之上声明的，而 [Ab_to_Grp] 并非其中之一，其对象是 [AbObject] 记录，而不是满足某个谓词的 [GrpObject]。修正 (#370)：现在构建了一个 [Reflective] 记录，在一个不同的子范畴上。Instance/Grp/Abelianize/Reflective.v
   通过交换性谓词 ([AbGrp_Sub]) 从 [Grp] 中切出阿贝尔群，证明 [Ab_Reflective_in_Grp : Reflective AbGrp_Sub]，并通过等价 [Ab_AbGrp_Equivalence] 将其与该文件的伴随关系联系起来，将 [Ab] 与 [AbGrp_Sub] 进行等价，并通过两个函子 [Ab_to_Grp] 和 [Abelianization_Functor] 的分解通过 [AbGrp_Sub]。上述结构原因仍然适用于 [Ab_to_Grp] 本身。非空性，通过映射证明。对商生成 [InCommutator] 的任何归纳都不能得到负数，因此以下每一种分离都通过一个同态映射到具体群。见证是 S₃（Instance/Grp/TwoFunctors.v），树内非阿贝尔群。[abelianize_S3_identifies] 显示投影将两个生成元的对合并到单位元，而供体的 [commutator_S3_nontrivial] 显示这两个元素在 S₃ 中是分开的：S₃ 的阿贝尔化是一个真商群。它也不是平凡群，这可以通过运用**泛性质**来证明，而不是通过观察得出：[AbTwo] 作为一个 [AbObject] 是 ℤ/2，[ab_two_sign] 是读入其中的符号特征，而调解器 [abelianize_med ab_two_sign] 由 [abelianize_universal] 产生，将反射类与单位类（[abelianize_S3_separates]）分开，通过 [eq_refl] 计算得到 [grp_two_one]。UNIVERSES，请读取约束块而不是绑定器，针对本文件声明的每个常量。在63个命名常量中，有六个在约束块中携带 [Set]，且这六个都是 S₃ 证据：[ab_two_sign]、[abelianize_S3_med_s]、[abelianize_S3_med_unit]、[abelianize_S3_separates]、[abelianize_S3_factors] 以及控制 [probe_ctl_sign]。原因已经定位：它们的类型提到 [TwoFunctors.S3@{Set}]，S₃ 被携带在一个 [bool] 组件上，以及 [bool : Set]。这不是 [AbTwo] 引起的——[AbTwo@{u u0 u1 u2 u3 u4 u5}] 自身有一个空的 [Set] 免费块，也不是 Instance/Grp.v 的 [Grp_trivial] / [Grp_Zero] 引脚（在 Instance/Grp/Quotient/Colimit.v 中披露，并通过 #450 提升），它们在本文件中都未被使用。另外两个 S₃ 语句，[abelianize_S3_identifies] 和 [abelianize_S3_proper]，在一个宇宙实例（[abel_eq@{u u Set}]）中显示 [Set]，同时没有获取任何 [Set] 约束：实例不是约束。

   整体发展是 [Set]-自由的。[abel_kills]、[abelianize_med]、[abelianize_universal]、[abelianize_universal_arrow]、[abelianize_left]、[abelianize_adjunction]、[abelianize_counit]、[abelianize_transform]、[abelianize_adjunction_via_transform]、[abelianize_routes_agree]、[abelianize_counit_iso]、[abelianize_left_iso]、[Ab_to_Grp_Full] 和 [Ab_to_Grp_Faithful] 都有 [Set] 自由的约束块，并且在 [Grp] 和 [Ab] 的宇宙中是多态的。S₃ 证人的提升未被尝试，并且钉点没有被认为是不可避免的。公理。90/90 常数在全局上下文下是封闭的：丢弃八个名为 [Fail] 的条目（这些条目没有命名任何常数）后，63 个 [.glob] 记录作为 [def] 或 [prf]，加上 27 个 [Program] 义务，这些义务 [.glob] 根本没有记录，必须通过它们的完全限定名称来查询。在此文件中，没有在任何函子或伴随上写明显式的宇宙实例。宇宙绑定器 [Functor] 和 [Adjunction] 的数量在 Coq 8.19/8.20 与 Rocq 9.1 之间有所不同，因此这样的注解不可移植。这里也不需要任何宇宙事实的保护：下面的七个否定都是转换失败（CONVERSION failure），没有一个是可形成性（宇宙）失败，因此上面的宇宙发现是经过测量的但未受保护，文件也说明了这一点，而不是称它们为固定的。未交付的内容。- 由于上述结构原因，没有 [Reflective] 实例，并且没有将 [Ab] 识别为 Construction/Subcategory.v 意义下的 [Grp] 的完整子类别。更正 (#370)：两者都在 Instance/Grp/Abelianize/Reflective.v 中，第二个通过 [Ab_AbGrp_Equivalence] 对 [Ab] 与 [AbGrp_Sub] 的等价关系。- 没有幂等性：[Abelianization_Functor ◯ Ab_to_Grp ≅ Id[Ab]] 从 [abelianize_counit_iso] 逐分量地推导，但 [[Ab, Ab]] 中的自然同构尚未组装，也没有给出 [IdempotentMonad] 说明。更正 (#370)：对于子类别表示，Instance/Grp/Abelianize/Reflective.v 的 [AbGrp_IdempotentMonad] 已经给出；而 [[Ab, Ab]] 中的自然同构仍未组装。- 没有与 Construction/Reflective/Idempotent.v 的比较，也没有 Eilenberg–Moore 读取。修正 (#370)：两者都在 Instance/Grp/Abelianize/Reflective.v 中的 [AbGrp_Sub] 制作：[AbGrp_IdempotentMonad] 是 Idempotent.v 的 [Reflective_IdempotentMonad] 在 [Ab_Reflective_in_Grp]，[AbGrp_Incl_Monadic] 是 Construction/Reflective/Monadic.v 那里的 Eilenberg–Moore 等价。- 没有唯一性（最多唯一同构）推论：它将在此实例化为 [universal_arrow_unique]，但没有被实例化。- 关于自由群的阿贝尔化没有任何内容，因此没有通往 Instance/Grp/Free.v 的桥梁，也没有自由阿贝尔群函子。- 通用性质没有以可表示性声明重述，也没有注册 [Representable] 实例。- 以下失败探针存在于此文件中，而不是在 Test/Probe 模块中，因为此更改仅限于一个文件；它们没有连接到任何构建目标。有七个负例，全都是同一类型（转换——每个都剥离一次，并确认报告为真正的“无法统一”），对照 23 个正例和一个仪器检查。负例中命名的每一个常量在重命名模拟中全部通过（19/19）。这十四个供体（[Abelianization_Functor]、[Ab_to_GrpOb]、[GrpTwo]、[Ab_to_Grp]、[Grp]、[Ab]、[cmon_map]、[cmon_setoid]、[carrier]、[adj]、[to]、[from]、[fmap]、[counit]）在整个文件中都被重命名了，这就是上游重命名对文件所做的操作；五个本地的（[abelianize_left]、[abelianize_adjunction]、[abelianize_adjunction_via_transform]、[abelianize_counit_hom]、[AbTwo]）仅在它们的声明位置被重命名。在这十九种情况下，每一个 POSITIVE 命令都会失败，因此没有一个 NEGATIVE 可以毫无条件地成功。
*)

(*
   * ** The descent lemma

   Everything below factors through this one step.  [Ab_to_GrpOb A] is
   abelian by construction, so [hom_to_abelian_kills] applies to any
   homomorphism into it; cancelling the inverse turns “kills
   commutators” into “respects the quotient relation”. 

   --------
   * ** 降阶引理

   下面的一切都通过这一步完成。[Ab_to_GrpOb A] 根据构造是阿贝尔群，所以 [hom_to_abelian_kills] 适用于到它的任何同态；消去逆元将“消去换元子”变为“尊重商关系”。
*)

Lemma ab_is_abelian (A : AbObject) (a b : carrier (Ab_to_GrpOb A)) :
  grp_mul (Ab_to_GrpOb A) a b ≈ grp_mul (Ab_to_GrpOb A) b a.
Proof. apply cmon_plus_comm. Qed.

(*
 [abel_eq] is the propositional truncation of [InCommutator] since the PR
 “algebraic carriers are sets” (2026-09-17), so the witness may not be
 destructed into the [Type]-valued conclusion directly.  The target is an
 [AbObject], which carries [cmon_prop], so [pequiv_to] puts a [Prop] goal in
 front of the elimination and [pequiv_from] returns.  This is the one place
 in the development where the truncation has to be opened. 

 --------
 [abel_eq] 是 [InCommutator] 的命题截断，因为 PR “代数载体是集合”（2026-09-17），所以证据可能不能直接被解构成 [Type] 值的结论。目标是一个 [AbObject]，它携带 [cmon_prop]，所以 [pequiv_to] 在消解之前放置了一个 [Prop] 目标，并且 [pequiv_from] 返回。这是在整个开发过程中唯一需要打开截断的地方。
*)
Lemma abel_kills {G : GrpObject} {A : AbObject}
  (f : G ~{Grp}~> Ab_to_GrpOb A) (a b : carrier G) :
  abel_eq G a b → grp_map f a ≈ grp_map f b.
Proof.
  intro Hab.
  apply (@pequiv_to _ _ (cmon_prop A)).
  destruct Hab as [Hab].
  apply pequiv_from.
  pose proof (hom_to_abelian_kills (ab_is_abelian A) f _ Hab) as E.
  rewrite (grp_map_mul f), (grp_map_inv f) in E.
  apply (grp_cancel_r _ (grp_inv (Ab_to_GrpOb A) (grp_map f b))).
  rewrite E.
  symmetry; apply grp_mul_inv_r.
Qed.

(*
   * The mediating homomorphism: the SAME underlying map as [f], read
   out of the quotient.  Preservation of the unit and of the operation
   are [f]'s own laws unchanged; the only new obligation is
   respectfulness, which is [abel_kills]. 

   --------
   * 中介同态：与 [f] 相同的基础映射，从商中读取。单位元和运算的保持是 [f] 自身的不变法则；唯一的新义务是尊重性，即 [abel_kills] 。
*)

Program Definition abelianize_med {G : GrpObject} {A : AbObject}
  (f : G ~{Grp}~> Ab_to_GrpOb A) : AbelianizationOb G ~{Ab}~> A := {|
  cmon_map := {| morphism := fun a : carrier G => grp_map f a |}
|}.
Next Obligation. intros G A f a b Hab; exact (abel_kills f a b Hab). Qed.
Next Obligation. intros G A f; exact (grp_map_unit f). Qed.
Next Obligation. intros G A f a b; exact (grp_map_mul f a b). Qed.

Example abelianize_med_computes {G : GrpObject} {A : AbObject}
  (f : G ~{Grp}~> Ab_to_GrpOb A) (a : carrier G) :
  cmon_map (abelianize_med f) a = grp_map f a := eq_refl.

(*
   * ** The universal arrow

   Mac Lane §III.1 Exercise 3 proper: [abel_proj G] is universal from
   G to [Ab_to_Grp].  Existence is [abelianize_med]; the factorization
   equation is [reflexivity], both sides being the same function on
   elements; uniqueness is that [abel_proj G] is the identity on
   elements, so the equation READS as the pointwise agreement being
   asked for. 

   --------
   * ** 通用箭头

   Mac Lane §III.1 练习 3 正确：[abel_proj G] 是从 G 到 [Ab_to_Grp] 的通用箭头。存在性是 [abelianize_med]；分解方程是 [reflexivity]，双方在元素上的函数相同；唯一性是 [abel_proj G] 在元素上是恒等映射，所以该方程读作所要求的逐点一致性。
*)

Theorem abelianize_universal (G : Grp) :
  ∀ (A : Ab) (f : G ~{Grp}~> Ab_to_Grp A),
    ∃! g : AbelianizationOb G ~{Ab}~> A,
      f ≈ fmap[Ab_to_Grp] g ∘ abel_proj G.
Proof.
  intros A f.
  unshelve eexists.
  - exact (abelianize_med f).
  - intro a; simpl; reflexivity.
  - intros g Hg a; simpl.
    exact (Hg a).
Defined.

(*
   * Kept transparent DELIBERATELY: [unique_obj] of it is the mediator on
   the nose, so the concrete evaluations at the end of this file
   compute.  The [Qed] alternative is what makes route one's derived
   counit opaque below, and that contrast is the point. 

   --------
   * 故意保持透明：[unique_obj] 它是鼻子上的中介，因此本文件末尾的具体评估可以计算。[Qed] 选项是导致路线一的派生余单位在下面变得不透明的原因，而这种对比就是重点。
*)
Example abelianize_universal_med (G : Grp) (A : Ab)
  (f : G ~{Grp}~> Ab_to_Grp A) :
  unique_obj (abelianize_universal G A f) = abelianize_med f := eq_refl.

(*
   * Packaged as an initial object of the comma category [=(G) ↓
   Ab_to_Grp]. 

   --------
   * 包装为逗号范畴 [=(G) ↓ Ab_to_Grp] 的初始对象。
*)
Definition abelianize_universal_arrow (G : Grp)
  : UniversalArrow G Ab_to_Grp :=
  universal_arrow_from_UMP G Ab_to_Grp (AbelianizationOb G) (abel_proj G)
    (abelianize_universal G).

(*
   * The same content in the direct encoding, where the universal object
   is named rather than projected out of a comma category. 

   --------
   * 直接编码中的相同内容，其中通用对象被命名，而不是从逗号类别中投射出来。
*)
Program Definition abelianize_AUniversalArrow (G : Grp)
  : AUniversalArrow G Ab_to_Grp (AbelianizationOb G) := {|
  universal_arrow := abel_proj G
|}.
Next Obligation.
  intros G A f.
  unshelve eexists.
  - exact (abelianize_med f).
  - intro a; simpl; reflexivity.
  - intros g Hg a; simpl.
    symmetry; exact (Hg a).
Qed.

(*
   * [universal_arrow_from_UMP] stores the supplied morphism as the
   second projection of the comma object it builds, so both readings
   are on the nose. 

   --------
   *  [universal_arrow_from_UMP] 会将提供的态射存储为它所构建的逗号对象的第二投影，因此两种读法都是准确的。
*)
Example abelianize_arrow_is_proj (G : Grp) :
  @arrow _ _ G Ab_to_Grp (abelianize_universal_arrow G) = abel_proj G
  := eq_refl.

Example abelianize_arrow_obj (G : Grp) :
  @arrow_obj _ _ G Ab_to_Grp (abelianize_universal_arrow G)
    = AbelianizationOb G := eq_refl.

Example abelianize_AUniversalArrow_arrow (G : Grp) :
  @universal_arrow _ _ G Ab_to_Grp _ (abelianize_AUniversalArrow G)
    = abel_proj G := eq_refl.

(*
   * ** Route one: the adjunction from the universal-arrow plumbing

   The functor, the adjunction and both triangle identities come out
   of Theory/Universal/Arrow.v with no further proof.  Read the type
   of [abelianize_adjunction] carefully: the LEFT ADJOINT it produces
   is the generic [abelianize_left], not [Abelianization_Functor].
   The two agree on objects definitionally and on arrows up to [≈];
   see [abelianize_left_iso] below. 

   --------
   * ** 路径一：来自通用箭头接口的伴随

   函子、伴随以及两个三角恒等式都直接来源于 Theory/Universal/Arrow.v，无需进一步证明。仔细阅读 [abelianize_adjunction] 的类型：它产生的左伴随是通用的 [abelianize_left]，而不是 [Abelianization_Functor]。两者在对象上定义上相同，在箭头上则一致到 [≈]；详见下文的 [abelianize_left_iso]。
*)

Definition abelianize_left : Grp ⟶ Ab :=
  LeftAdjointFunctorFromUniversalArrows Ab_to_Grp abelianize_universal_arrow.

Definition abelianize_adjunction : abelianize_left ⊣ Ab_to_Grp :=
  AdjunctionFromUniversalArrows Ab_to_Grp abelianize_universal_arrow.

Example abelianize_left_obj (G : Grp) :
  abelianize_left G = Abelianization_Functor G := eq_refl.

(*
   * The arrow actions agree only up to [≈], and the proof is the
   uniqueness clause of the universal property: the generic functor's
   [fmap] is BY DEFINITION the unique factorization, and the donor's
   [fmap] satisfies the same equation. 

   --------
   * 箭头操作只在 [≈] 上一致，证明依据是泛性质的唯一性条款：泛函子的 [fmap] 按定义是唯一的分解，而供体的 [fmap] 满足相同的方程。
*)
Lemma abelianize_left_fmap {G H : Grp} (f : G ~{Grp}~> H) :
  fmap[abelianize_left] f ≈ fmap[Abelianization_Functor] f.
Proof.
  apply (uniqueness (ump_universal_arrows (abelianize_universal_arrow G) _)).
  intro a; simpl; apply abel_eq_refl.
Qed.

(*
   * The two facts assembled: an isomorphism in the functor category
   whose components are identities. 

   --------
   * 汇集的两个事实：函子范畴中的同构，其分量是恒等映射。
*)
Program Definition abelianize_left_iso :
  @Isomorphism ([Grp, Ab]) abelianize_left Abelianization_Functor := {|
  to   := {| transform := fun G => @id Ab (Abelianization_Functor G) |};
  from := {| transform := fun G => @id Ab (Abelianization_Functor G) |}
|}.
Next Obligation.
  intros G H k a; simpl.
  first [ exact (abelianize_left_fmap k a)
        | exact (abel_eq_sym H _ _ (abelianize_left_fmap k a)) ].
Qed.
Next Obligation.
  intros G H k a; simpl.
  first [ exact (abelianize_left_fmap k a)
        | exact (abel_eq_sym H _ _ (abelianize_left_fmap k a)) ].
Qed.
Next Obligation.
  intros G H k a; simpl.
  first [ exact (abelianize_left_fmap k a)
        | exact (abel_eq_sym H _ _ (abelianize_left_fmap k a)) ].
Qed.
Next Obligation.
  intros G H k a; simpl.
  first [ exact (abelianize_left_fmap k a)
        | exact (abel_eq_sym H _ _ (abelianize_left_fmap k a)) ].
Qed.
Next Obligation.
  intros G a; simpl.
  first [ apply abel_eq_refl
        | exact (@fmap_id _ _ abelianize_left G a)
        | exact (abel_eq_sym G _ _ (@fmap_id _ _ abelianize_left G a)) ].
Qed.
Next Obligation.
  intros G a; simpl.
  first [ apply abel_eq_refl
        | exact (@fmap_id _ _ abelianize_left G a)
        | exact (abel_eq_sym G _ _ (@fmap_id _ _ abelianize_left G a)) ].
Qed.

(*
   * ** Route two: the counit, and the adjunction from unit and counit

   Riehl §4.2 Exercise ii.  The counit component at an abelian group A
   is the identity function on elements, read out of the coarse setoid
   [abel_eq (Ab_to_GrpOb A)] into A's own [≈].  Its one obligation is
   [abel_kills] at the identity homomorphism of [Ab_to_GrpOb A]: an
   abelian group kills its own commutators. 

   --------
   * ** 路径二：余单位，以及来自单位和余单位的伴随关系

   Riehl §4.2 练习 ii。余单位在一个阿贝尔群 A 上的分量
   是从粗集合同构 [abel_eq (Ab_to_GrpOb A)] 读取到 A 自身的 [≈] 的元素的恒等函数。它的唯一职责是
   在 [Ab_to_GrpOb A] 的恒等同态上的 [abel_kills] ：一个阿贝尔群会消去它自己的交换子。
*)

Program Definition abelianize_counit_hom (A : AbObject) :
  AbelianizationOb (Ab_to_GrpOb A) ~{Ab}~> A := {|
  cmon_map := {| morphism := fun a : carrier (cmon_setoid A) => a |}
|}.
Next Obligation.
  intros A a b Hab.
  exact (abel_kills (@id Grp (Ab_to_GrpOb A)) a b Hab).
Qed.
Next Obligation. intros A; simpl; reflexivity. Qed.
Next Obligation. intros A a b; simpl; reflexivity. Qed.

(** The counit, concretely: the identity on elements. / 余单位，具体来说：元素上的恒等映射。 *)
Example abelianize_counit_computes (A : AbObject)
  (a : carrier (cmon_setoid A)) :
  cmon_map (abelianize_counit_hom A) a = a := eq_refl.

(*
   * And it is INVERTIBLE — its inverse is the same identity map read
   the other way, which is [abel_proj (Ab_to_GrpOb A)] transcribed
   into [Ab].  This is the concrete content of the counit for this
   row: an abelian group is its own abelianization.  Contrast a free
   construction, where the counit is a genuine evaluation and is in
   general nowhere near invertible. 

   --------
   * 并且它是可逆的 —— 它的逆是将同一个恒等映射反向读取，也就是将 [abel_proj (Ab_to_GrpOb A)] 转录为 [Ab]。这就是这一行伴随元的具体内容：一个阿贝尔群就是它自己的阿贝尔化。对比自由构造，其中伴随元是真正的求值，而且通常远非可逆。
*)

Program Definition abelianize_counit_inv (A : AbObject) :
  A ~{Ab}~> AbelianizationOb (Ab_to_GrpOb A) := {|
  cmon_map := {| morphism := fun a : carrier (cmon_setoid A) => a |}
|}.
Next Obligation.
  intros A a b Hab; exact (abel_eq_of_eq (Ab_to_GrpOb A) a b Hab).
Qed.
Next Obligation. intros A; simpl; apply abel_eq_refl. Qed.
Next Obligation. intros A a b; simpl; apply abel_eq_refl. Qed.

Program Definition abelianize_counit_iso (A : AbObject) :
  AbelianizationOb (Ab_to_GrpOb A) ≅[Ab] A := {|
  to   := abelianize_counit_hom A;
  from := abelianize_counit_inv A
|}.
Next Obligation. intros A a; simpl; reflexivity. Qed.
Next Obligation. intros A a; simpl; apply abel_eq_refl. Qed.

(*
   * The counit as a natural transformation.  Both naturality squares
   have the identity on both legs, so both are [reflexivity]. 

   --------
   * 协单位作为一个自然变换。两个自然性方阵在两条边上都是恒等映射，所以两者都是 [reflexivity]。
*)
Program Definition abelianize_counit :
  Abelianization_Functor ◯ Ab_to_Grp ⟹ @Id Ab := {|
  transform := abelianize_counit_hom
|}.
Next Obligation. intros A B f a; simpl; reflexivity. Qed.
Next Obligation. intros A B f a; simpl; reflexivity. Qed.

(*
   * The unit/counit package, with BOTH TRIANGLE IDENTITIES PROVED HERE.

   The first, [ε(FX) ∘ F(ηX) ≈ id], lives in [Ab] at
   [AbelianizationOb X]: both legs are the identity function on
   [carrier X] and the ambient relation is [abel_eq X], so the
   obligation is [abel_eq_refl].  The second, [U(εX) ∘ η(UX) ≈ id],
   lives in [Grp] at [Ab_to_GrpOb X]: both legs are again the identity
   function, but the ambient relation is X's own [≈], so the
   obligation is [reflexivity].  The two triangles are therefore
   discharged by DIFFERENT tactics, which is a reminder that they are
   equations in different categories and not one statement twice. 

   --------
   * 单位/余单位包，其中两种三角恒等式在此证明。

   第一种，[ε(FX) ∘ F(ηX) ≈ id]，位于[Ab]中的[AbelianizationOb X]处：两条边都是[carrier X]上的恒等函数，而所处的环境关系是[abel_eq X]，因此义务是[abel_eq_refl]。第二种，[U(εX) ∘ η(UX) ≈ id]，位于[Grp]中的[Ab_to_GrpOb X]处：两条边同样是恒等函数，但环境关系是X自身的[≈]，因此义务是[reflexivity]。因此，这两个三角形是由不同的策略解决的，这提醒我们它们是在不同类别中的等式，而不是同一陈述重复两次。
*)
Program Definition abelianize_transform :
  Abelianization_Functor ∹ Ab_to_Grp := {|
  Transformation.unit   := abel_projection;
  Transformation.counit := abelianize_counit
|}.
Next Obligation. intros X a; simpl; apply abel_eq_refl. Qed.
Next Obligation. intros X a; simpl; reflexivity. Qed.

Definition abelianize_adjunction_via_transform
  : Abelianization_Functor ⊣ Ab_to_Grp :=
  Adjunction_from_Transform abelianize_transform.

Example abelianize_transform_unit :
  unit[abelianize_transform] = abel_projection := eq_refl.

Example abelianize_transform_counit :
  counit[abelianize_transform] = abelianize_counit := eq_refl.

(*
   * ** The two routes agree

   The FORWARD transposes are the same term at arbitrary arguments;
   the BACKWARD ones agree only up to [≈], the residue being the
   opacity of [ump_universal_arrows]. 

   --------
   * ** 两条路径一致

   正向转置在任意参数下都是相同的项；
   逆向转置仅在  [≈] 上一致，余数是 [ump_universal_arrows] 的不透明性。
*)

Example abelianize_routes_agree_to (G : Grp) (A : Ab)
  (f : Abelianization_Functor G ~{Ab}~> A) :
  to (@adj _ _ _ _ abelianize_adjunction G A) f
    = to (@adj _ _ _ _ abelianize_adjunction_via_transform G A) f
  := eq_refl.

Theorem abelianize_routes_agree (G : Grp) (A : Ab) :
  (∀ f : Abelianization_Functor G ~{Ab}~> A,
      to (@adj _ _ _ _ abelianize_adjunction G A) f
        = to (@adj _ _ _ _ abelianize_adjunction_via_transform G A) f)
  * (∀ f : G ~{Grp}~> Ab_to_Grp A,
      from (@adj _ _ _ _ abelianize_adjunction G A) f
        ≈ from (@adj _ _ _ _ abelianize_adjunction_via_transform G A) f).
Proof.
  split.
  - intro f; exact eq_refl.
  - intro f.
    apply (uniqueness (ump_universal_arrows (abelianize_universal_arrow G) f)).
    intro a; simpl; reflexivity.
Qed.

(*
   * ** The derived unit and counit

   [unit] and [counit] are DERIVED in Theory/Adjunction.v as the
   transposes of the identities, so what they compute to has to be
   checked.  Both routes' units compute, and to the projection;
   route two's counit computes and route one's does not. 

   --------
   * ** 派生单位和余单位

   [unit] 和 [counit] 在 Theory/Adjunction.v 中是作为恒等式的转置派生的，因此它们的计算结果需要检查。两个路径的单位都可以计算，并投射到结果上；第二条路径的余单位可以计算，而第一条路径的则不可以。
*)

Example abelianize_unit_computes (G : Grp) (a : carrier G) :
  grp_map (@Category.Theory.Adjunction.unit _ _ _ _
             abelianize_adjunction G) a = a := eq_refl.

Example abelianize_unit_computes_via_transform (G : Grp) (a : carrier G) :
  grp_map (@Category.Theory.Adjunction.unit _ _ _ _
             abelianize_adjunction_via_transform G) a = a := eq_refl.

Example abelianize_counit_computes_via_transform (A : Ab)
  (a : carrier (cmon_setoid A)) :
  cmon_map (@Category.Theory.Adjunction.counit _ _ _ _
             abelianize_adjunction_via_transform A) a = a := eq_refl.

(*
   * ** [Ab_to_Grp] is full and faithful

   Faithfulness is definitional — an [AbHom] IS a [CMonHom] and both
   hom-setoids compare underlying maps pointwise.  Fullness holds
   because a group homomorphism between the underlying groups of two
   abelian groups already preserves everything an [AbHom] must: the
   unit law becomes preservation of zero, the multiplication law
   preservation of the sum, and preservation of negation is
   Instance/Ab.v's theorem [ab_map_neg] rather than a further
   obligation.  Together with the adjunction and the invertible counit
   this is the shape of a reflective subcategory; see the header for
   why no [Reflective] instance is claimed.  CORRECTION (#370): over the
   subcategory [AbGrp_Sub] one is; see the header's note. 

   --------
   * ** [Ab_to_Grp] 是满且忠实的

   忠实性是定义性的 —— 一个 [AbHom] 就是一个 [CMonHom]，并且两者的同态集在点上比较底层映射。满性成立的原因是，因为两个阿贝尔群的底层群之间的群同态已经保持了 [AbHom] 必须保持的一切：单位律变为保持零，加法律变为保持和，保持取反则是 Instance/Ab.v 的定理 [ab_map_neg]，而不是额外的义务。连同伴随与可逆余单位，这就是反射子范畴的形态；请参阅标题了解为何没有声明 [Reflective] 实例。更正 (#370)：在子范畴 [AbGrp_Sub] 上是有的；参见标题注释。
*)

Program Definition Ab_to_Grp_Faithful : Faithful Ab_to_Grp := {|
  fmap_inj := fun A B f g H => H
|}.

Program Definition Ab_to_Grp_Full : Full Ab_to_Grp := {|
  prefmap := fun A B (h : Ab_to_GrpOb A ~{Grp}~> Ab_to_GrpOb B) =>
    {| cmon_map      := grp_map h
     ; cmon_map_zero := grp_map_unit h
     ; cmon_map_plus := grp_map_mul h |}
|}.
Next Obligation. intros A B h a; simpl; reflexivity. Qed.

(*
   * ** Non-vacuity over S₃

   Every separation below is obtained by mapping OUT of the quotient:
   no induction on the generation [InCommutator] could produce a
   negative.  The target is ℤ/2 read as an [AbObject]. 

   --------
   * ** 关于 S₃ 的非空性

   下面的每个分离都是通过从商映射 OUT 得到的：
   没有对生成 [InCommutator] 的归纳能够产生一个负数。
   目标是将 ℤ/2 读取为 [AbObject] 。
*)

(*
 [GrpTwo]'s `≈` is [grp_two_rel] (Instance/Grp/Epi.v), a match into
 [poly_unit] and [False].  Its [Prop] mirror is the same match into [True]
 and [False], and both implications are four-way case analyses -- so no
 [GrpObject] field is needed here, and this instance does not wait for
 phase P3.

 REMOVAL CANDIDATE, surfaced and not acted on (the PR “algebraic
 carriers are sets”, 2026-09-17).  The sentence above was written while
 [GrpObject] still had no [grp_prop] field.  It has one now, so
 [grp_prop GrpTwo] inhabits exactly what [grp_two_PropEquiv] inhabits,
 and [AbTwo]'s [cmon_prop] below takes the field rather than this hand
 instance.  [grp_two_peq] and [grp_two_PropEquiv] are KEPT, with no
 consumer in the tree, because deleting a working constant is not this
 PR's call; they are listed for John to decide. 

 --------
 [GrpTwo] 的 `≈` 是 [grp_two_rel]（实例/组/_epi.v），匹配到 [poly_unit] 和 [False]。它的 [Prop] 镜像是相同的匹配到 [True] 和 [False]，并且两者都是四向情况分析——所以这里不需要 [GrpObject] 字段，并且该实例不等待 P3 阶段。

 删除候选，已浮现但未采取行动（PR “代数载体是集合”，2026-09-17）。上面这句话是在 [GrpObject] 仍然没有 [grp_prop] 字段时写的。它现在已有一个字段，因此 [grp_prop GrpTwo] 恰好包含 [grp_two_PropEquiv] 所包含的，而 [AbTwo] 下面的 [cmon_prop] 接管了该字段，而不是这个手动实例。[grp_two_peq] 和 [grp_two_PropEquiv] 被保留，在树中没有消费者，因为删除一个有效常量不是此 PR 的任务；它们被列出供 John 决定。
*)
Definition grp_two_peq (x y : grp_two_carrier) : Prop :=
  match x, y with
  | inl _, inl _ => True
  | inr _, inr _ => True
  | _, _ => False
  end.

Definition grp_two_PropEquiv : PropEquiv (is_setoid (grp_setoid GrpTwo)).
Proof.
  unshelve refine
    (@PropEquiv_of_relation _ (is_setoid (grp_setoid GrpTwo)) grp_two_peq _ _).
  - intros [u|u] [v|v] H; simpl in *; try contradiction; exact ttt.
  - intros [u|u] [v|v] H; simpl in *; try contradiction; exact I.
Defined.

Program Definition AbTwo : AbObject := {|
  ab_cmon := {| cmon_setoid := grp_setoid GrpTwo
              ; cmon_zero   := grp_unit GrpTwo
              ; cmon_plus   := grp_mul GrpTwo
              ; cmon_prop   := grp_prop GrpTwo |}
 ; ab_neg := grp_inv GrpTwo
|}.
Solve All Obligations with
  (first [ exact (grp_mul_respects GrpTwo)
         | exact (grp_mul_assoc GrpTwo)
         | exact GrpTwo_abelian
         | exact (grp_mul_unit_l GrpTwo)
         | exact (grp_inv_Proper GrpTwo)
         | exact (grp_mul_inv_l GrpTwo) ]).

(*
   * The sign character of S₃ (Instance/Grp/Center.v), read into
   [Ab_to_GrpOb AbTwo].  The three fields are [s3_sign]'s own: [AbTwo]
   was built so that its setoid, zero and sum ARE [GrpTwo]'s, which is
   what makes this a re-wrapping rather than a second construction. 

   --------
   * S₃ 的符号特征（实例/群/中心.v），读取到 [Ab_to_GrpOb AbTwo] 中。三个字段是 [s3_sign] 自有的：[AbTwo] 的构建方式使其等价类、零元素和加法都是 [GrpTwo] 的，这正是使其成为重新封装而不是第二次构造的原因。
*)
Definition ab_two_sign : S3 ~{Grp}~> Ab_to_GrpOb AbTwo :=
  Build_GrpHom S3 (Ab_to_GrpOb AbTwo)
    (grp_map s3_sign) (grp_map_unit s3_sign) (grp_map_mul s3_sign).

(*
   * The projection MERGES: the commutator of the two generators becomes
   the unit in the abelianization. 

   --------
   * 投影合并：两个生成元的换位子在阿贝尔化中变为单位元。
*)
Lemma abelianize_S3_identifies : abel_eq S3 (gcomm S3 S3_r S3_s) s3_unit.
Proof.
  constructor.
  apply (inc_resp (a := gcomm S3 S3_r S3_s)).
  - vm_compute; reflexivity.
  - apply inc_comm.
Qed.

(*
   * …and what it merges was apart in S₃, so the abelianization of S₃ is
   a PROPER quotient.  The second half is the donor's
   [commutator_S3_nontrivial]; nothing is reproved. 

   --------
   * …而它合并的部分在 S₃ 中是分开的，因此 S₃ 的阿贝尔化是一个**适当**的商。后一半是供体的 [commutator_S3_nontrivial]；没有任何东西被重新证明。
*)
Theorem abelianize_S3_proper :
  abel_eq S3 (gcomm S3 S3_r S3_s) s3_unit *
  (gcomm S3 S3_r S3_s ≈ s3_unit → False).
Proof.
  split.
  - exact abelianize_S3_identifies.
  - exact (snd commutator_S3_nontrivial).
Qed.

(*
   * The quotient is not collapsed either, and this is shown BY
   EXERCISING THE UNIVERSAL PROPERTY: the mediator [abelianize_universal]
   produces out of the sign character separates the class of the
   reflection from the class of the unit.  Both values COMPUTE, the
   universal property having been left transparent. 

   --------
   * 商也没有坍塌，这通过行使泛性质来展示：中介 [abelianize_universal] 由符号特征产生，将反射类与单位类分开。两个值都能计算，泛性质保持透明。
*)

Example abelianize_S3_med_s :
  cmon_map (unique_obj (abelianize_universal S3 AbTwo ab_two_sign)) S3_s
    = grp_two_one := eq_refl.

Example abelianize_S3_med_unit :
  cmon_map (unique_obj (abelianize_universal S3 AbTwo ab_two_sign)) s3_unit
    = grp_two_zero := eq_refl.

Theorem abelianize_S3_separates :
  cmon_map (unique_obj (abelianize_universal S3 AbTwo ab_two_sign)) S3_s
    ≈ cmon_map (unique_obj (abelianize_universal S3 AbTwo ab_two_sign))
        s3_unit → False.
Proof. intro H; vm_compute in H; exact H. Qed.

(*
   * The mediator is genuinely a homomorphism OUT of the quotient: it is
   the unique factorization of the sign character through the
   projection, and the factorization equation is the universal
   property's own. 

   --------
   * 中介是真正的商上的同态映射：它是符号特征通过投影的唯一分解，且分解方程就是该泛性质本身。
*)
Example abelianize_S3_factors (a : carrier S3) :
  grp_map ab_two_sign a
    = grp_map (fmap[Ab_to_Grp]
                 (unique_obj (abelianize_universal S3 AbTwo ab_two_sign))
                 ∘ abel_proj S3) a := eq_refl.

(*
   * ** Boundary probes

   Each [Fail] below pins a strict identification that is REFUSED, and
   is paired with a positive control naming the same constants, so a
   rename or a definitional change breaks this file loudly instead of
   turning a negative vacuously green.  [abelianize_probe_instrument] checks
   the instrument itself.  These live here rather than in a Test/Probe
   module because this change is confined to one file; they are not
   wired into any make target. 

   --------
   * ** 边界探针

   每个下面的 [Fail] 都严格标识为拒绝（REFUSED），并且与命名相同常量的阳性对照配对，因此重命名或定义变化会明显破坏此文件，而不会让阴性结果徒然显示为绿色。[abelianize_probe_instrument] 检查仪器本身。它们存在于此处而不是 Test/Probe 模块中，因为此更改仅限于一个文件；它们没有连接到任何构建目标。
*)

Fail Example abelianize_probe_instrument : true = false := eq_refl.

(* Positive controls. / 阳性对照。 *)
Example probe_ctl_left : Grp ⟶ Ab := abelianize_left.
Example probe_ctl_functor : Grp ⟶ Ab := Abelianization_Functor.
Example probe_ctl_adj : abelianize_left ⊣ Ab_to_Grp := abelianize_adjunction.
Example probe_ctl_adj_transform : Abelianization_Functor ⊣ Ab_to_Grp :=
  abelianize_adjunction_via_transform.
Example probe_ctl_fmap (G H : Grp) (f : G ~{Grp}~> H) :
  fmap[abelianize_left] f ≈ fmap[Abelianization_Functor] f :=
  abelianize_left_fmap f.
Example probe_ctl_counit_hom (A : Ab) :
  AbelianizationOb (Ab_to_GrpOb A) ~{Ab}~> A := abelianize_counit_hom A.
Example probe_ctl_sign : S3 ~{Grp}~> Ab_to_GrpOb AbTwo := ab_two_sign.
Example probe_ctl_grptwo : GrpObject := GrpTwo.
Example probe_ctl_abtwo : AbObject := AbTwo.
Example probe_ctl_med (G : Grp) (A : Ab) (f : G ~{Grp}~> Ab_to_Grp A) :
  AbelianizationOb G ~{Ab}~> A := abelianize_med f.
Example probe_ctl_arrow (G : Grp) :
  @arrow _ _ G Ab_to_Grp (abelianize_universal_arrow G) = abel_proj G
  := eq_refl.
Example probe_ctl_aua (G : Grp) :
  AUniversalArrow G Ab_to_Grp (AbelianizationOb G) :=
  abelianize_AUniversalArrow G.
Example probe_ctl_counit_iso (A : Ab) :
  AbelianizationOb (Ab_to_GrpOb A) ≅[Ab] A := abelianize_counit_iso A.
Example probe_ctl_transform : Abelianization_Functor ∹ Ab_to_Grp :=
  abelianize_transform.
Example probe_ctl_left_iso :
  @Isomorphism ([Grp, Ab]) abelianize_left Abelianization_Functor :=
  abelianize_left_iso.
Example probe_ctl_kills {G : GrpObject} {A : AbObject}
  (f : G ~{Grp}~> Ab_to_GrpOb A) (a b : carrier G) :
  abel_eq G a b → grp_map f a ≈ grp_map f b := abel_kills f a b.
Example probe_ctl_counit_nat :
  Abelianization_Functor ◯ Ab_to_Grp ⟹ @Id Ab := abelianize_counit.
Example probe_ctl_counit_inv (A : Ab) :
  A ~{Ab}~> AbelianizationOb (Ab_to_GrpOb A) := abelianize_counit_inv A.
Example probe_ctl_full : Full Ab_to_Grp := Ab_to_Grp_Full.
Example probe_ctl_faithful : Faithful Ab_to_Grp := Ab_to_Grp_Faithful.

Example probe_control_obj (G : Grp) :
  abelianize_left G = Abelianization_Functor G := eq_refl.

Example probe_control_to (G : Grp) (A : Ab)
  (f : Abelianization_Functor G ~{Ab}~> A) :
  to (@adj _ _ _ _ abelianize_adjunction G A) f
    = to (@adj _ _ _ _ abelianize_adjunction_via_transform G A) f
  := eq_refl.

Example probe_control_counit (A : Ab) (a : carrier (cmon_setoid A)) :
  cmon_map (abelianize_counit_hom A) a = a := eq_refl.

(*
 NEGATIVE 1 (conversion).  The two left adjoints are not the same
 functor: the arrow actions differ. 

 --------
 负 1（转换）。两个左伴随不是相同的函子：箭头作用不同。
*)
Fail Example probe_left_functors :
  abelianize_left = Abelianization_Functor := eq_refl.

(*
 NEGATIVE 2 (conversion).  Located precisely: the arrow actions.
 [ump_universal_arrows] is a [Qed] Corollary, so
 [unique_obj (ump_universal_arrows …)] reduces to nothing. 

 --------
 负 2（转换）。 精确定位：箭头动作。 [ump_universal_arrows] 是 [Qed] 的推论，因此 [unique_obj (ump_universal_arrows …)] 化为无。
*)
Fail Example probe_left_fmap_strict (G H : Grp) (f : G ~{Grp}~> H) :
  fmap[abelianize_left] f = fmap[Abelianization_Functor] f := eq_refl.

(* NEGATIVE 3 (conversion). The forward transposes agree as FUNCTIONS ([probe_control_to]) but not as whole [SetoidMorphism] records: the [proper_morphism] certificates are rebuilt. / 负 3（转换）。前向换位在函数上（[probe_control_to]）一致，但在整个 [SetoidMorphism] 记录上不一致：[proper_morphism] 证书已重建。 *)
Fail Example probe_routes_to_record (G : Grp) (A : Ab) :
  to (@adj _ _ _ _ abelianize_adjunction G A)
    = to (@adj _ _ _ _ abelianize_adjunction_via_transform G A) := eq_refl.

(* NEGATIVE 4 (conversion). The backward transposes: route one's is the opaque unique factorization. / 负 4（转换）。向后的转置：某人的路径是不可透明的唯一分解。 *)
Fail Example probe_routes_from (G : Grp) (A : Ab)
  (f : G ~{Grp}~> Ab_to_Grp A) :
  from (@adj _ _ _ _ abelianize_adjunction G A) f
    = from (@adj _ _ _ _ abelianize_adjunction_via_transform G A) f
  := eq_refl.

(*
 NEGATIVE 5 (conversion).  The DISCRIMINATING one: route one's
 derived counit does not compute, while route two's does
 ([abelianize_counit_computes_via_transform]) and the named component
 does ([probe_control_counit]).  Same derived constant, same
 statement shape. 

 --------
 负5（转换）。区分的那个：路线一的派生余单元无法计算，而路线二的可以（[abelianize_counit_computes_via_transform]），命名组件也可以（[probe_control_counit]）。相同的派生常数，相同的语句形式。
*)
Fail Example probe_counit_route_one (A : Ab)
  (a : carrier (cmon_setoid A)) :
  cmon_map (@Category.Theory.Adjunction.counit _ _ _ _
              abelianize_adjunction A) a = a := eq_refl.

(*
 NEGATIVE 6 (conversion).  Route two's derived counit computes on
 elements but is not the named component as a whole record: it is
 [abelianize_counit_hom A ∘ fmap[Abelianization_Functor] id]. 

 --------
 负 6（转换）。路径二的派生余单位在元素上计算，但不是作为整体记录的命名组件：它是 [abelianize_counit_hom A ∘ fmap[Abelianization_Functor] id].
*)
Fail Example probe_derived_counit_is_named (A : Ab) :
  @Category.Theory.Adjunction.counit _ _ _ _
    abelianize_adjunction_via_transform A = abelianize_counit_hom A
  := eq_refl.

(*
 NEGATIVE 7 (conversion).  [AbTwo] was built from [GrpTwo]'s own
 setoid, unit, multiplication and inverse, so the two records agree
 on every DATA field; they still do not convert, the law fields of
 [Ab_to_GrpOb] being rebuilt [Program] obligations. 

 --------
 负 7（转换）。[AbTwo] 是从 [GrpTwo] 自身的集合、单位、乘法和逆元构建的，因此两个记录在每个 DATA 字段上都一致；它们仍然无法转换，[Ab_to_GrpOb] 的法律字段是由重建的 [Program] 义务构成的。
*)
Fail Example probe_abtwo_is_grptwo : Ab_to_GrpOb AbTwo = GrpTwo := eq_refl.
