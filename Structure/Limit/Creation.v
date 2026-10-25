Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Discrete.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

Generalizable All Variables.

(* * * Creation of limits and colimits by a functor / * * 由函子创建极限和余极限 *)

(*
 nLab:      https://ncatlab.org/nlab/show/created+limit
 nLab:      https://ncatlab.org/nlab/show/preserved+limit
 Mac Lane:  Categories for the Working Mathematician, 2nd ed. (GTM 5),
 §V.1 Definition 3 (book p. 112) and §V.4 Theorem 2
 (book p. 117)
 Riehl:     Category Theory in Context, 2nd ed., §3.4 Definition 3.4.1
 clause (iii) with the remark following it (p. 104), and
 Definition 3.4.7 (p. 105)
 Awodey:    Category Theory, 2nd ed., §5.6 Definition 5.31 (p. 119)

 CORRECTION (#467): Mac Lane's Definition on p. 112 is unnumbered (the
 page reads "Definition.", between Theorems 2 and 3 of §V.1, read from
 the page image), and it numbers its two clauses (i) and (ii); "§V.1
 Definition 3" in this header and at [CreatesLimit], and "clause (b)"
 at [creates_limiting], name that Definition and its clause (ii).  The
 on-the-nose uniqueness that UNIQUENESS OF THE LIFT below declines as a
 field is refuted for [EM_Forget] at the identity monad on [Sets], over
 the one-object shape, without axioms, by
 Monad/Eilenberg/Moore/Limit/Examples.v's [em_lift_not_unique_leibniz].

 Preservation says that a functor carries limit cones to limit cones;
 reflection says that it recognizes them; creation says that it
 CONSTRUCTS them.  Mac Lane's §V.1 Definition 3 reads: [F : A ⟶ X]
 creates the limit of [K : J ⟶ A] when, to every limiting cone
 [τ : x → F K] in [X], there is exactly one pair [(a, σ)] with
 [F a = x] and [F σ = τ], and that [σ] is a limiting cone.

 The interest of the notion is practical rather than taxonomic.  It is
 what makes "limits in an algebraic category are computed on underlying
 sets" a theorem rather than a slogan: the forgetful functor of a
 category of algebras creates limits, so the limit upstairs is the limit
 of the carriers, equipped with the one structure map that makes every
 projection a homomorphism.  That is exactly the witness shipped with
 this file — [EM_Forget] strictly creates every limit
 (Monad/Eilenberg/Moore/Limit.v) — and Mac Lane's §V.4 Theorem 2 then
 converts creation into completeness and continuity, which is how [Set],
 [Top], [Grp] and module categories are shown complete in the first
 place.

 Riehl's remark on Definition 3.4.1 is the calibration point, and this
 file follows it exactly.  Creation entails reflection outright: that is
 [creates_reflects_limits], a projection.  Creation entails preservation
 ONLY where the limit downstairs exists — with nothing limiting
 downstairs the creation clause never fires, so creation does not by
 itself give preservation.  Accordingly [creation_preserves_limit] takes
 [L : Limit (F ◯ K)] as an explicit hypothesis, and the reader can see
 in its signature which half of Riehl's remark is being used.

 Contents: the cone-level limit predicate and its conversions; the
 calculus of cone isomorphisms, including uniqueness of limits up to a
 compatible isomorphism; the image of a cone under a functor; cone-level
 preservation and reflection; the class [CreatesLimit] with Mac Lane's
 remaining two clauses derived; §V.4 Theorem 2 in both halves with the
 shape variants; the strict (Riehl 3.4.7) variant and the bridge between
 the two classes; creation under composition; and the colimit duals.

 CONE LEVEL, NOT APEX LEVEL.  The predicate [IsLimitCone] below says
 that a GIVEN cone is universal.  The library's [IsALimit]
 (Structure/Limit.v) pins only the apex and carries its own chosen
 [limit_acone], whose legs are unrelated to any cone one holds; the
 argument at Construction/Comma/Limit.v shows why that is
 genuinely too weak here.  The cone-level notion was already being
 written out by hand at three places — [PreservesImageLimit]
 (Construction/Comma/Limit.v), the leg hypothesis of
 [ff_reflect_ump] (Theory/Equivalence/Limit.v) and [rapl_ump]
 (Adjunction/Continuity.v) — so this file names an existing notion
 rather than introducing one.  The two bridges to [PreservesImageLimit]
 are identity functions and live in Construction/Comma/Creation.v; the
 leg side condition of [ff_reflect_ump] discharges by [reflexivity]
 because the legs of [FCone] ARE the image legs.  Issue #427 owns
 cone-level preservation as such; when it lands, [IsLimitCone],
 [PreservesLimitCone] and [FCone] belong next to [cone_leg] in
 Structure/Limit/Preservation.v, and [FCone] merges with [fmap_cone]
 (Theory/Equivalence/Limit.v).  They are restated here — some 35
 lines, including [cone_leg_coh] — only because that file sits above
 this layer: importing it here would compile, but it would invert the
 layering.  The name [ReflectsLimit]
 is deliberately left unused; #481 may want it.  (#481 left it unused:
 [ReflectsLimitCone] is that predicate, and Structure/Limit/
 Reflection.v quantifies it over shapes, classes of shapes and all
 diagrams.)

 THE STRICTNESS QUESTION, AND WHAT THE SETOID SETTING FORCES.  Mac
 Lane's definition asks for a pair [(a, σ)] with [F a = x] and
 [F σ = τ].  Object equality is available here (obj is a bare Type, and
 Instance/Discrete.v, Construction/Grothendieck/Strict.v and
 Theory/Category/Monoid.v all use it), so [StrictLift] states the apex
 clause with [=] and the leg clause with [≈] through [hom_rew]; that is
 Riehl's Definition 3.4.7, which she flags as an "evil" strictification
 not generally satisfied by equivalences — and indeed the apex of
 [equivalence_creates_limits] is the quasi-inverse of the given apex, in
 general only isomorphic to it.  The iso-invariant reading is the usable default and
 is the one [CreatesLimit] carries, following the same decision recorded
 at Monad/Monadicity/Beck.v for one diagram shape.  Both notions
 ship, and [StrictlyCreatesLimit_CreatesLimit] relates them in the
 derivable direction.

 UNIQUENESS OF THE LIFT.  Mac Lane's "exactly one pair" cannot be a
 FIELD here, because a field must hold at every intended instance and the
 obstruction at the two that matter is not a matter of effort: for [EM_Forget] two lifts of one
 limiting cone carry algebra structures whose actions agree only up to
 [≈], and equality of the [TAlgebra] records would additionally require
 equality of those actions and of their law proofs; the comma projection
 behaves the same way for its mediating triangle.  (In special cases the
 on-the-nose clause is inhabited — for [Id[C]] both lifts have the given
 apex — which is why it is stated below as a derived theorem rather than
 ruled out.)  Uniqueness is
 therefore a theorem rather than a field, in the form the setting
 supports and the one Monad/Monadicity/Beck.v already uses at its
 own shape: [creates_lift_unique] says any cone lying over N is
 canonically isomorphic to the created one.  With it, Mac Lane's second
 clause ([creates_limiting], the lift is itself limiting) is likewise
 derived — from the reflection field — rather than assumed, so the class
 carries three fields and no redundancy.  The reflection field is not
 derivable from the other two: relating a lift to a competing cone
 upstairs would need F full and conservative, which is why Beck.v
 carries [create_coeq_reflects] separately and needed a section of its
 own (Beck.v) to discharge it.

 CONVENTIONS.  Arguments are DIAGRAM FIRST, [CreatesLimit K F], matching
 [PreservesLimit K F] (Structure/Limit/Preservation.v) so the two
 read alike in the same statement.  None of the classes below is
 registered for instance resolution: creation witnesses are always
 passed explicitly, exactly as Structure/Limit/Preservation.v
 records for preservation.  On size: [CreatesLimit] pins J, C and D to
 one hom/proof universe just as [PreservesLimit] does, and
 [creates_limits_Complete] additionally shares one shape universe
 between its two [Complete] occurrences; the library's [Complete] carries
 no explicit smallness hypothesis (Structure/Complete.v), so
 "creates all small limits" here reads as "creates limits of every shape
 the use site's universes allow".  Creation of finite limits is out of
 scope here: the finiteness predicate on shapes is now
 [Structure/Limit/Finite.v]'s [FiniteCategory] (it postdates this file,
 which quantifies over no shape class), and [CreatesLimitsOfShape] at a
 named shape is what is offered instead.  [(F ◯ K)^op] and
 [F^op ◯ K^op] are not convertible, so the colimit side repackages cones
 field by field, following [preserves_colimit]
 (Structure/Limit/Preservation.v) and [isalimit_op_comp]
 (Theory/Equivalence/Limit.v); the covariant strict-side accessors
 are not provided, since every in-tree colimit-side creation consumer
 speaks the elementary cofork API of Structure/Coequalizer.v instead. 

 --------
 nLab：       https://ncatlab.org/nlab/show/created+limit
 nLab：       https://ncatlab.org/nlab/show/preserved+limit
 Mac Lane：  《为工作的数学家而写的范畴论》，第2版（GTM 5），
 §V.1 定义 3（书第112页）及 §V.4 定理 2（书第117页）
 Riehl：     《情境下的范畴论》，第2版，§3.4 定义 3.4.1 第（iii）条及其后的备注（第104页），以及定义 3.4.7（第105页）
 Awodey：    《范畴论》，第2版，§5.6 定义 5.31（第119页）更正 (#467)：Mac Lane 在第112页的定义没有编号（页面显示“定义。”，位于 §V.1 的定理2和定理3之间，从页面图像读取），它的两个条款编号为 (i) 和 (ii)；此标题中的“§V.1 定义3”以及在 [CreatesLimit] 的编号，以及在 [creates_limiting] 的“条款(b)”指的是该定义及其条款(ii)。下面 UNIQUENESS OF THE LIFT 拒绝作为域的精确唯一性，在 [Sets] 上的恒等 monad 对于 [EM_Forget]、在单对象图上、无公理的情况下，被 Monad/Eilenberg/Moore/Limit/Examples.v 的 [em_lift_not_unique_leibniz] 反驳。保持性表示函子将极限锥映射到极限锥；反映性表示它识别它们；创造性表示它构造它们。Mac Lane 的 §V.1 定义 3 写道：[F : A ⟶ X] 当且仅当对于 [X] 中的每一个极限锥 [τ : x → F K]，存在唯一一对 [(a, σ)] 与 [F a = x] 和 [F σ = τ]，使得 [σ] 是一个极限锥时，[F : A ⟶ X] 创造了 [K : J ⟶ A] 的极限。这一概念的趣味在于其实用性而非分类学。它解释了为什么“代数范畴中的极限是在底层集合上计算的”是一个定理而不是口号：代数范畴的遗忘函子会产生极限，因此上层的极限就是承载集合的极限，并配备一个结构映射，使每个投影都是同态。这正是随本文件提供的证据——[EM_Forget]严格地创造了每个极限（Monad/Eilenberg/Moore/Limit.v）——然后Mac Lane的§V.4定理2将创造性转化为完备性和连续性，这也是[Set]、[Top]、[Grp]及模范畴最初被证明完备的方式。Riehl 对定义 3.4.1 的评论是校准点，本文件完全遵循它。创造完全包含反思：也就是说 [creates_reflects_limits] ，一个映射。创造只在下方极限存在的情况下才包含保持——如果下方没有限制，创造条款永远不会生效，因此创造本身并不自动提供保持。因此 [creation_preserves_limit] 将 [L : Limit (F ◯ K)] 作为明确假设，读者可以在其符号中看到使用了 Riehl 评论的哪一半内容。内容：锥体级极限谓词及其转换；锥体同构的演算，包括极限在兼容同构下的唯一性；函子下的锥体像；锥体级的保持与反射；类 [CreatesLimit] 以及 Mac Lane 剩余的两个条款推导；§V.4 定理 2 的两部分及形态变体；严格 (Riehl 3.4.7) 变体及两类之间的桥梁；复合下的生成；以及余极限的对偶。锥体层，而非顶点层。下面的谓词 [IsLimitCone] 表示给定的锥体是通用的。库中的 [IsALimit] (Structure/Limit.v) 仅固定顶点，并携带其自己选择的 [limit_acone]，其腿与所持有的任何锥体无关；Construction/Comma/Limit.v 中的论证说明了为什么在这里这确实太弱。锥体层的概念已经在三个地方手工写出——ZWZ26WZZ (Construction/Comma/Limit.v)、ZWZ27WZZ (Theory/Equivalence/Limit.v) 的腿假设，以及 [rapl_ump] (Adjunction/Continuity.v)——因此这个文件引用的是一个已有的概念，而不是引入一个新概念。通向 [PreservesImageLimit] 的两个桥是恒等函数，并且位于 Construction/Comma/Creation.v；[ff_reflect_ump] 的支腿边条件由 [reflexivity] 解除，因为 [FCone] 的支腿就是图像支腿。问题 #427 因此拥有锥层级的保持；当它落地时，[IsLimitCone]、[PreservesLimitCone] 和 [FCone] 将属于 [cone_leg] 在 Structure/Limit/Preservation.v 中旁边，而 [FCone] 与 [fmap_cone]（Theory/Equivalence/Limit.v）合并。它们在这里被重述——大约 35 行，包括 [cone_leg_coh]——只是因为那个文件位于这一层之上：在这里导入它会编译，但会颠倒层次。名称 [ReflectsLimit] 是故意未使用的；#481 可能会需要它。(#481 没有使用它：
 [ReflectsLimitCone] 是那个谓词，而 Structure/Limit/Reflection.v 对其在形状、形状类别和所有图表上进行量化。)严格性问题，以及集合论设定所强制的内容。Mac Lane 的定义要求一对 [(a, σ)]，其中 [F a = x] 和 [F σ = τ]。这里可以使用对象相等（obj 是一个裸类型，并且 Instance/Discrete.v、Construction/Grothendieck/Strict.v 和 Theory/Category/Monoid.v 都使用它），所以 [StrictLift] 用 [=] 表示顶点条款，用 [≈] 通过 [hom_rew] 表示支条款；也就是 Riehl 的定义 3.4.7，她将其标记为“邪恶”的严格化，一般等价不满足——实际上 [equivalence_creates_limits] 的顶点是给定顶点的准逆，通常只与其同构。保持同构不变的理解是可用的默认方式，也是 [CreatesLimit] 所采用的方式，这一点遵循了在 Monad/Monadicity/Beck.v 中针对一个图形形状记录的相同决定。两个概念都发货，并且 [StrictlyCreatesLimit_CreatesLimit] 将它们与可推导的方向相关联。提升的唯一性。Mac Lane 的“恰好一对”在这里不能是一个域，因为一个域必须在每一个预期实例中成立，而在两个关键实例上的障碍并不是努力的问题：对于 [EM_Forget]，一个极限锥的两个提升携带代数结构，其作用仅在 [≈] 上一致，而 [TAlgebra] 记录的相等还需要这些作用及其律证明的相等；逗号投影在其中介三角形的行为也是同样的方式。（在特殊情况下，准确的子句是有解的——对于 [Id[C]，两者提升都具有给定的顶点——这就是为什么它在下面被陈述为一个派生定理而不是被排除的原因。）因此，唯一性是一个定理而不是一个域，以设置支持的形式，以及 Monad/Monadicity/Beck.v 已经在其自身形状中使用的形式：[creates_lift_unique] 表示任何位于 N 上的圆锥都是与生成的圆锥范式同构的。凭借它，Mac Lane 的第二个子句（[creates_limiting]，即提升本身是极限的）同样是派生的——来自反射域——而不是假设的，因此该类有三个域且没有冗余。反射场不能从另外两个导出：将升力与楼上的竞争锥相关联需要 F 是完备且守恒的，这就是为什么 Beck.v 会单独携带 [create_coeq_reflects] 并且需要它自己的一个截面（Beck.v）来释放它。公约。参数为 DIAGRAM FIRST、[CreatesLimit K F]，与 [PreservesLimit K F] （Structure/Limit/Preservation.v）匹配，因此在同一语句中读起来一致。下面的任何类都未注册用于实例解析：创建见证始终显式传递，完全按照 Structure/Limit/Preservation.v 的记录进行保存。关于大小：[CreatesLimit] 将 J、C 和 D 固定在一个同类/证明宇宙中，就像 [PreservesLimit] 那样，并且 [creates_limits_Complete] 额外在其两个 [Complete] 出现之间共享一个形状宇宙；库的 [Complete] 不携带明确的小型假设（Structure/Complete.v），因此这里的“创建所有小极限”可理解为“创建使用位置的宇宙允许的每种形状的极限”。这里不涉及有限极限的创建：现在形状上的有限性谓词是 [Structure/Limit/Finite.v] 的 [FiniteCategory]（它比此文件更新，该文件并未量化任何形状类），而在命名形状上的 [CreatesLimitsOfShape] 是作为替代提供的。[(F ◯ K)^op] 和 [F^op ◯ K^op] 不能相互转换，所以余极限端按字段重新打包锥，遵循 [preserves_colimit]（Structure/Limit/Preservation.v）和 [isalimit_op_comp]（Theory/Equivalence/Limit.v）；不提供协变严格端的访问器，因为每个树内余极限端的创建使用者都使用 Structure/Coequalizer.v 的基本共叉 API。
*)

(* * ** Creation of limits (the iso-invariant reading) / * ** 极限的创建（同构不变读法） *)

(*
 Mac Lane §V.1 Definition 3, in the form the setoid setting supports: a
 lift of every limiting cone downstairs, a cone isomorphism identifying
 its image with the given cone, and reflection.  The remaining two
 clauses of the book — that the lift is limiting, and that it is unique —
 are the theorems [creates_limiting] and [creates_lift_unique] below. 

 --------
 Mac Lane §V.1 定义 3，以集合化设定所支持的形式：对楼下的每一个极限锥的提升，一个锥同构将其像与给定锥识别，以及反射。书中的其余两个条款——提升是极限的，以及它是唯一的——是下面的定理 [creates_limiting] 和 [creates_lift_unique]。
*)

Class CreatesLimit {J C D : Category} (K : J ⟶ C) (F : C ⟶ D) := {
  creates_lift (N : Cone (F ◯ K)) (HN : IsLimitCone N) : Cone K;
  creates_lift_over (N : Cone (F ◯ K)) (HN : IsLimitCone N) :
    ConeIso (FCone F (creates_lift N HN)) N;
  creates_reflect (M : Cone K) : IsLimitCone (FCone F M) → IsLimitCone M
}.

(* Mac Lane's clause (b): the lift is itself a limiting cone. CORRECTION (#467): the book numbers this clause (ii). / Mac Lane 的条款 (b)：升运本身是一个限制锥。 更正 (#467)：书中将此条款编号为 (ii)。 *)

Definition creates_limiting {J C D : Category} {K : J ⟶ C} {F : C ⟶ D}
  (CR : CreatesLimit K F) (N : Cone (F ◯ K)) (HN : IsLimitCone N) :
  IsLimitCone (creates_lift N HN) :=
  creates_reflect (creates_lift N HN)
    (limitcone_transport (ConeIso_sym (creates_lift_over N HN)) HN).

(*
 Mac Lane's uniqueness clause, in the form the setting supports: any cone
 upstairs lying over N is canonically isomorphic to the created one.  This
 is the pattern of [create_coeq_unique] (Monad/Monadicity/Beck.v) one
 level up. 

 --------
 Mac Lane 的唯一性条款，在集合支持的形式中：位于 N 之上的任何圆锥都与所创建的圆锥具有典型同构。这是 [create_coeq_unique]（Monad/Monadicity/Beck.v）在上一层的模式。
*)

Definition creates_lift_unique {J C D : Category} {K : J ⟶ C} {F : C ⟶ D}
  (CR : CreatesLimit K F) (N : Cone (F ◯ K)) (HN : IsLimitCone N)
  (M : Cone K) (j : ConeIso (FCone F M) N) :
  ConeIso M (creates_lift N HN) :=
  limitcone_iso
    (creates_reflect M (limitcone_transport (ConeIso_sym j) HN))
    (creates_limiting CR N HN).

(*
 Creation entails reflection (Riehl §3.4, the remark following Definition
 3.4.1): here, definitionally. 

 --------
 创造包含反思（Riehl §3.4，定义 3.4.1 之后的注释）：在这里，从定义上讲。
*)

Definition creates_reflects_limits {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (CR : CreatesLimit K F) : ReflectsLimitCone K F :=
  @creates_reflect J C D K F CR.

(* The existence half, bundled: a limit downstairs yields a limit upstairs. / 存在的一半，捆绑在一起：楼下的极限产生了楼上的极限。 *)

Definition creates_limit_lift {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (CR : CreatesLimit K F) (L : Limit (F ◯ K)) :
  Limit K :=
  @Build_Limit J C K
    (creates_lift (@limit_cone _ _ _ L) (limit_limitcone L))
    (creates_limiting CR (@limit_cone _ _ _ L) (limit_limitcone L)).

(* * ** Mac Lane §V.4 Theorem 2, first half / * ** 马克·莱恩 §V.4 定理 2，上半部分 *)

(*
 Creation plus existence of the limit downstairs gives preservation, at
 the cone level.  The hypothesis [L] is Riehl's proviso, and it is
 load-bearing: the creation clause only fires on a limiting cone
 downstairs, so with no [Limit (F ◯ K)] there is nothing to feed it. 

 --------
 在下方极限的构造加上存在性在锥层上给出了保持性。假设 [L] 是 Riehl 的条件，它是承重的：构造条款仅在下方极限锥上触发，因此如果没有 [Limit (F ◯ K)]，就没有东西可以供给它。
*)

Theorem creation_preserves_limit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (CR : CreatesLimit K F) (L : Limit (F ◯ K)) :
  PreservesLimitCone K F.
Proof.
  intros M HM.
  (* the created lift of the given limit downstairs / 所给楼下极限产生的升力 *)
  pose (N := @limit_cone _ _ _ L).
  pose (HN := limit_limitcone L).
  pose (M' := creates_lift N HN).
  pose (HM' := creates_limiting CR N HN).
  (* M and M' are both limiting upstairs, hence isomorphic as cones / M 和 M' 都是在楼上极限，因此作为圆锥同构 *)
  pose (i := limitcone_iso HM' HM).
  (* transport limit-ness along N ≅ F M' ≅ F M / 沿 N 的传输极限 ≅ F M' ≅ F M *)
  exact (limitcone_transport
           (ConeIso_comp (FCone_iso F i)
              (ConeIso_sym (creates_lift_over N HN))) HN).
Defined.

(** ** Shape-quantified creation / ** 形状量化创作 *)

Definition CreatesLimitsOfShape (J : Category) {C D : Category} (F : C ⟶ D)
  : Type := ∀ K : J ⟶ C, CreatesLimit K F.

Definition CreatesAllLimits {C D : Category} (F : C ⟶ D) : Type :=
  ∀ (J : Category) (K : J ⟶ C), CreatesLimit K F.

(*
 "Creates products" is the discrete-shape case, over
 Instance/Discrete.v's [DiscreteCat], mirroring how
 Structure/Limit/Product.v reaches indexed products. 

 --------
 “Creates products” 是离散形状的情况，在 Instance/Discrete.v 的 [DiscreteCat] 中，反映了 Structure/Limit/Product.v 如何达到索引乘积。
*)

Definition CreatesProducts {C D : Category} (F : C ⟶ D) : Type :=
  ∀ (A : Type) (K : DiscreteCat A ⟶ C), CreatesLimit K F.

Definition CreatesAllLimits_CreatesProducts {C D : Category} {F : C ⟶ D}
  (CR : CreatesAllLimits F) : CreatesProducts F :=
  fun A K => CR (DiscreteCat A) K.

(* * ** Mac Lane §V.4 Theorem 2, second half / * ** 马克·莱恩 §V.4 定理 2，下半部分 *)

(* Creation of all limits transports completeness ... / 所有界限的创造传递了完整性... *)

Definition creates_limits_Complete {C D : Category} (F : C ⟶ D)
  (HD : @Complete D) (CR : CreatesAllLimits F) : @Complete C :=
  fun J K => creates_limit_lift (CR J K) (HD J (F ◯ K)).

(* ... and makes the functor continuous, at the cone level ... / ... 并且使函子在圆锥层面上连续 ... *)

Definition creates_limits_continuous {C D : Category} (F : C ⟶ D)
  (HD : @Complete D) (CR : CreatesAllLimits F) :
  ∀ (J : Category) (K : J ⟶ C), PreservesLimitCone K F :=
  fun J K => creation_preserves_limit (CR J K) (HD J (F ◯ K)).

(* ... hence also in the apex-only vocabulary already in the tree. / ... 因此也在树中仅出现在顶点的词汇中。 *)

Definition creates_limits_PreservesAllLimits {C D : Category} (F : C ⟶ D)
  (HD : @Complete D) (CR : CreatesAllLimits F) : PreservesAllLimits F :=
  fun J K => PreservesLimitCone_PreservesLimit
               (creates_limits_continuous F HD CR J K).

(* * ** Strict creation (Riehl §3.4 Definition 3.4.7) / * ** 严格创生（Riehl §3.4 定义 3.4.7） *)

(*
 Transport of a morphism along an equality of its domain.  Objects use
 [eq]; morphisms are still compared with [≈]. 

 --------
 沿着其定义域的相等转运一个态射。对象使用 [eq]；态射仍然使用 [≈] 进行比较。
*)

Definition hom_rew {D : Category} {d d' : D} (p : d = d') {t : D}
  (f : d ~{D}~> t) : d' ~{D}~> t :=
  match p in _ = z return z ~{D}~> t with eq_refl => f end.

(*
 The isomorphism induced by an equality of objects.  Deliberately not
 named [iso_of_eq]: that name is taken by Instance/StrictCat/ToCat.v,
 which this Structure-layer file must not import. 

 --------
 由对象相等引起的同构。故意没有命名为 [iso_of_eq]：该名称已被 Instance/StrictCat/ToCat.v 使用，而此 Structure 层文件必须不导入它。
*)

Definition obj_eq_iso {D : Category} {d d' : D} (p : d = d') : d ≅ d' :=
  match p in _ = z return d ≅ z with eq_refl => iso_id end.

Lemma hom_rew_obj_eq_iso {D : Category} {d d' : D} (p : d = d') {t : D}
  (f : d ~{D}~> t) (g : d' ~{D}~> t) :
  hom_rew p f ≈ g → g ∘ to (obj_eq_iso p) ≈ f.
Proof. destruct p; simpl; intro H. rewrite id_right. now symmetry. Qed.

(* An on-the-nose lift: the image apex is EQUAL to the given apex, and the image legs agree with the given legs up to [≈] after that transport. / 一个直接的提升：图像顶点等于给定顶点，并且图像边与给定边在经过该平移后的 [≈] 之前保持一致。 *)

Record StrictLift {J C D : Category} (K : J ⟶ C) (F : C ⟶ D)
  (N : Cone (F ◯ K)) := {
  slift_cone : Cone K;
  slift_eq   : F (vertex_obj[slift_cone]) = vertex_obj[N];
  slift_legs : ∀ x : J,
    hom_rew slift_eq (fmap[F] (cone_leg slift_cone x)) ≈ cone_leg N x
}.

Arguments slift_cone {J C D K F N} _.
Arguments slift_eq {J C D K F N} _.
Arguments slift_legs {J C D K F N} _ _.

Definition slift_iso {J C D : Category} {K : J ⟶ C} {F : C ⟶ D}
  {N : Cone (F ◯ K)} (L : StrictLift K F N) :
  F (vertex_obj[slift_cone L]) ≅ vertex_obj[N] := obj_eq_iso (slift_eq L).

Lemma slift_iso_legs {J C D : Category} {K : J ⟶ C} {F : C ⟶ D}
  {N : Cone (F ◯ K)} (L : StrictLift K F N) (x : J) :
  cone_leg N x ∘ to (slift_iso L) ≈ fmap[F] (cone_leg (slift_cone L) x).
Proof. exact (hom_rew_obj_eq_iso _ _ _ (slift_legs L x)). Qed.

(*
 Every cone upstairs is tautologically a strict lift of its own image.
 Provided for reference: it has no consumer here, the uniqueness clause
 it was intended to feed having become the derived
 [screates_lift_unique] rather than a field. 

 --------
 楼上的每一个圆锥在逻辑上都是其自身图像的严格提升。
 提供以供参考：这里没有其使用者，它原本打算支撑的唯一性条款已经变成了派生的
 [screates_lift_unique]，而不是一个字段。
*)

Definition self_lift {J C D : Category} {K : J ⟶ C} {F : C ⟶ D}
  (M : Cone K) : StrictLift K F (FCone F M) :=
  @Build_StrictLift J C D K F (FCone F M) M eq_refl (fun x => reflexivity _).

(*
 Riehl's Definition 3.4.7 asks for a UNIQUE on-the-nose lift that is
 limiting.  This class keeps the on-the-nose lift and the limiting
 clause and replaces her uniqueness clause by reflection, for the reason
 given in the header; it is therefore neither weaker nor stronger than
 the book's.  Uniqueness in the form this setting supports is
 [screates_lift_unique] below, through the bridge to [CreatesLimit]. 

 --------
 Riehl 的定义 3.4.7 要求一个独特的、直接的提升，该提升具有约束性。这个类保留了直接提升和约束条款，并用反射代替她的唯一性条款，原因如标题所述；因此，它既不比书中的定义弱，也不比书中的定义强。在此设置中支持的唯一性形式如下所示，通过到 [CreatesLimit] 的桥接：[screates_lift_unique]。
*)

Class StrictlyCreatesLimit {J C D : Category} (K : J ⟶ C) (F : C ⟶ D) := {
  screates (N : Cone (F ◯ K)) (HN : IsLimitCone N) : StrictLift K F N;
  screates_limiting (N : Cone (F ◯ K)) (HN : IsLimitCone N) :
    IsLimitCone (slift_cone (screates N HN));
  screates_reflect (M : Cone K) : IsLimitCone (FCone F M) → IsLimitCone M
}.

Definition StrictlyCreatesLimit_CreatesLimit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (SC : StrictlyCreatesLimit K F) :
  CreatesLimit K F.
Proof.
  unshelve refine {| creates_lift := fun N HN => slift_cone (screates N HN) |}.
  - intros N HN.
    exists (slift_iso (screates N HN)).
    intro x.
    exact (slift_iso_legs (screates N HN) x).
  - exact screates_reflect.
Defined.

Definition screates_lift_unique {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (SC : StrictlyCreatesLimit K F)
  (N : Cone (F ◯ K)) (HN : IsLimitCone N)
  (M : Cone K) (j : ConeIso (FCone F M) N) :
  ConeIso M (slift_cone (screates N HN)) :=
  creates_lift_unique (StrictlyCreatesLimit_CreatesLimit SC) N HN M j.

Definition StrictlyCreatesLimitsOfShape (J : Category) {C D : Category}
  (F : C ⟶ D) : Type := ∀ K : J ⟶ C, StrictlyCreatesLimit K F.

Definition StrictlyCreatesLimits {C D : Category} (F : C ⟶ D) : Type :=
  ∀ (J : Category) (K : J ⟶ C), StrictlyCreatesLimit K F.

(** ** Creation composes / ** 创造组成 *)

Section Compose.

Context {J C D E : Category}.
Context {K : J ⟶ C}.
Context {F : C ⟶ D}.
Context {G : D ⟶ E}.

Definition CreatesLimit_compose
  (CF : CreatesLimit K F) (CG : CreatesLimit (F ◯ K) G) :
  CreatesLimit K (G ◯ F).
Proof.
  unshelve refine {| creates_lift := _ |}.
  - (* the two-stage lift / 两级升力 *)
    intros N HN.
    exact (creates_lift
             (creates_lift (cone_assoc N) (islimitcone_assoc HN))
             (creates_limiting CG (cone_assoc N) (islimitcone_assoc HN))).
  - (* the comparison isomorphism / 比较同构 *)
    intros N HN; simpl.
    set (mid := creates_lift (cone_assoc N) (islimitcone_assoc HN)).
    set (Hmid := creates_limiting CG (cone_assoc N) (islimitcone_assoc HN)).
    pose (iF := creates_lift_over mid Hmid).
    pose (iG := creates_lift_over (cone_assoc N) (islimitcone_assoc HN)).
    exists (iso_compose `1 iG (fobj_iso G _ _ `1 iF)).
    intro x.
    assert (H1 : cone_leg N x ∘ to `1 iG ≈ fmap[G] (cone_leg mid x))
      by exact (`2 iG x).
    transitivity ((cone_leg N x ∘ to `1 iG) ∘ fmap[G] (to `1 iF)).
    + apply comp_assoc.
    + rewrite H1.
      transitivity (fmap[G] (cone_leg mid x ∘ to `1 iF)).
      * exact (symmetry (@fmap_comp _ _ G _ _ _ (cone_leg mid x) (to `1 iF))).
      * exact (@fmap_respects _ _ G _ _ _ _ (`2 iF x)).
  - (* reflection, one stage at a time / 反思，一次一个阶段 *)
    intros M H.
    apply (creates_reflect (F:=F)).
    apply (creates_reflect (F:=G)).
    exact (fun M0 => H (cone_assoc_inv M0)).
Defined.

End Compose.

(* * ** Creation of colimits, by duality / * ** 通过对偶性创建余极限 *)

(* The definitions cost one line each; the covariant accessors do not, because [(F ◯ K)^op] and [F^op ◯ K^op] are not convertible. / 定义每个花费一行；协变访问器则不，因为 [(F ◯ K)^op] 和 [F^op ◯ K^op] 不能相互转换。 *)

Definition CreatesColimit `(K : J ⟶ C) `(F : C ⟶ D) : Type :=
  @CreatesLimit (J^op) (C^op) (D^op) (K^op) (F^op).

Definition StrictlyCreatesColimit `(K : J ⟶ C) `(F : C ⟶ D) : Type :=
  @StrictlyCreatesLimit (J^op) (C^op) (D^op) (K^op) (F^op).

Definition CreatesAllColimits {C D : Category} (F : C ⟶ D) : Type :=
  ∀ (J : Category) (K : J ⟶ C), CreatesColimit K F.

Section Dual.

Context {J C D : Category}.
Context {K : J ⟶ C}.
Context {F : C ⟶ D}.

Definition colimit_op_comp (L : Colimit (F ◯ K)) : Limit (F^op ◯ K^op) :=
  @Build_Limit (J^op) (D^op) (F^op ◯ K^op)
    (cone_op_comp (@limit_cone _ _ _ L))
    (islimitcone_op_comp (limit_limitcone L)).

Definition creates_colimit_lift (CR : CreatesColimit K F)
  (L : Colimit (F ◯ K)) : Colimit K :=
  creates_limit_lift CR (colimit_op_comp L).

(* The dual of §V.4 Theorem 2's first half, stated in op form. / §V.4 定理 2 前半部分的对偶，以对偶形式陈述。 *)

Definition creation_preserves_colimit (CR : CreatesColimit K F)
  (L : Colimit (F ◯ K)) : PreservesLimitCone (K^op) (F^op) :=
  creation_preserves_limit CR (colimit_op_comp L).

End Dual.

Definition creates_colimits_Cocomplete {C D : Category} (F : C ⟶ D)
  (HD : @Cocomplete D) (CR : CreatesAllColimits F) : @Cocomplete C :=
  fun J K => creates_colimit_lift (CR J K) (HD J (F ◯ K)).

(* * ** Jointly created limits (Riehl §3.4 Exercise 3.4.v) / * ** 共同创建的限制 (Riehl §3.4 练习 3.4.v) *)

(*
 A FAMILY of functors [F i : C ⟶ D i] jointly creates the limit of [K]
 when a family of limiting cones over the images, one for every [i],
 lifts to a cone over [K] whose [i]-th image is the [i]-th given cone
 up to cone isomorphism, and a cone upstairs ALL of whose images are
 limiting is itself limiting.  This is [CreatesLimit] with the single
 functor replaced by a family; the two bridges below record that
 [CreatesLimit K F] is exactly the case of a one-member family.  Its
 motivating instance is the family of projections out of a product of
 categories (Construction/Product/Limit.v), which is what makes "limits
 in a product category are computed componentwise" a creation statement
 rather than a construction.  Mac Lane's remaining clauses — the lift
 is limiting, and any cone over the given family is canonically
 isomorphic to it — are derived exactly as for [CreatesLimit]. 

 --------
 一族函子 [F i : C ⟶ D i] 当一族极限锥在像上的极限（每个 [i] 对应一个锥）升华为 [K] 上的锥时共同产生 [K] 的极限，其 [i]-th 像与给定的 [i]-th 锥在锥同构意义下相同，并且一个上层锥如果其所有像都是极限锥，则它自身也是极限锥。这是 [CreatesLimit]，将单个函子替换为一族函子；下面的两个桥记录了 [CreatesLimit K F] 恰好是一族只有一个成员的情况。其动机实例是从积范畴的投影族（Construction/Product/Limit.v），这使得“积范畴中的极限按分量计算”成为一个产生声明而非构造。Mac Lane 剩下的条款——该提升是有限的，并且任何给定族上的锥都是与其典范同构的——与 [CreatesLimit] 的推导方法完全相同。
*)

Class JointlyCreateLimit {J C : Category} (K : J ⟶ C)
  {I : Type} {D : I → Category} (F : ∀ i : I, C ⟶ D i) := {
  jcreates_lift (N : ∀ i : I, Cone (F i ◯ K))
    (HN : ∀ i : I, IsLimitCone (N i)) : Cone K;
  jcreates_lift_over (N : ∀ i : I, Cone (F i ◯ K))
    (HN : ∀ i : I, IsLimitCone (N i)) (i : I) :
    ConeIso (FCone (F i) (jcreates_lift N HN)) (N i);
  jcreates_reflect (M : Cone K) :
    (∀ i : I, IsLimitCone (FCone (F i) M)) → IsLimitCone M
}.

Definition jcreates_limiting {J C : Category} {K : J ⟶ C}
  {I : Type} {D : I → Category} {F : ∀ i : I, C ⟶ D i}
  (JC : JointlyCreateLimit K F)
  (N : ∀ i : I, Cone (F i ◯ K)) (HN : ∀ i : I, IsLimitCone (N i)) :
  IsLimitCone (jcreates_lift N HN) :=
  jcreates_reflect (jcreates_lift N HN)
    (fun i => limitcone_transport
                (ConeIso_sym (jcreates_lift_over N HN i)) (HN i)).

Definition jcreates_lift_unique {J C : Category} {K : J ⟶ C}
  {I : Type} {D : I → Category} {F : ∀ i : I, C ⟶ D i}
  (JC : JointlyCreateLimit K F)
  (N : ∀ i : I, Cone (F i ◯ K)) (HN : ∀ i : I, IsLimitCone (N i))
  (M : Cone K) (j : ∀ i : I, ConeIso (FCone (F i) M) (N i)) :
  ConeIso M (jcreates_lift N HN) :=
  limitcone_iso
    (jcreates_reflect M
       (fun i => limitcone_transport (ConeIso_sym (j i)) (HN i)))
    (jcreates_limiting JC N HN).

Definition jcreates_limit_lift {J C : Category} {K : J ⟶ C}
  {I : Type} {D : I → Category} {F : ∀ i : I, C ⟶ D i}
  (JC : JointlyCreateLimit K F) (L : ∀ i : I, Limit (F i ◯ K)) : Limit K :=
  @Build_Limit J C K
    (jcreates_lift (fun i => @limit_cone _ _ _ (L i))
       (fun i => limit_limitcone (L i)))
    (jcreates_limiting JC _ _).

(*
 A single functor is a one-member family, both ways.  [unit] is the
 index; the reflection clause and the lift are literally the same data. 

 --------
 单一函子是一个单成员族，双向都是如此。[unit] 是索引；反射子句和提升实际上是相同的数据。
*)

Definition JointlyCreateLimit_of_CreatesLimit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (CR : CreatesLimit K F) :
  JointlyCreateLimit K (fun _ : unit => F) := {|
  jcreates_lift := fun N HN => creates_lift (N tt) (HN tt);
  jcreates_lift_over := fun N HN i =>
    match i as u
      return ConeIso (FCone F (creates_lift (N tt) (HN tt))) (N u)
    with tt => creates_lift_over (N tt) (HN tt) end;
  jcreates_reflect := fun M H => creates_reflect M (H tt)
|}.

Definition CreatesLimit_of_JointlyCreateLimit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D}
  (JC : JointlyCreateLimit K (fun _ : unit => F)) : CreatesLimit K F := {|
  creates_lift := fun N HN => jcreates_lift (fun _ => N) (fun _ => HN);
  creates_lift_over := fun N HN =>
    jcreates_lift_over (fun _ => N) (fun _ => HN) tt;
  creates_reflect := fun M H => jcreates_reflect M (fun _ => H)
|}.
