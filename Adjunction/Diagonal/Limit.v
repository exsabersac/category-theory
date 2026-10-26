(** * Limits and colimits as adjoints of the diagonal functor  / * 作为对角函子的伴随的极限和余极限*)

(* nLab:      https://ncatlab.org/nlab/show/diagonal+functor
   nLab:      https://ncatlab.org/nlab/show/limit
   Wikipedia: https://en.wikipedia.org/wiki/Limit_(category_theory)
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

   Mac Lane, “Categories for the Working Mathematician”, Springer GTM 5,
   2nd ed., §IV.2 (p. 87) tabulates the adjoints of the diagonal functor:
   for a fixed index category J the constant-diagram functor
   Δ = Diagonal J : C ⟶ [J, C] has a right adjoint exactly when C has all
   J-shaped limits, and a left adjoint exactly when it has all J-shaped
   colimits, so that the three functors sit in the sandwich

       colim ⊣ Δ ⊣ lim.

   Riehl, “Category Theory in Context”, Dover 2016, states the same as
   Proposition 4.6.1, with exercises 4.6.i and 4.6.ii asking respectively
   for the degenerate rows of the table (the unique functor to the point)
   and for the identification of the unit and counit with the universal
   cocone and cone.  Awodey, “Category Theory”, Oxford 2nd ed. 2010, §9.3
   runs the same argument for the special shapes, and Mac Lane's §V.2
   Exercise 3 asks for the arrow part: a natural transformation β : F ⟹ F'
   induces lim β : lim F ~> lim F', the unique arrow commuting with the two
   limiting cones.

   The content is entirely the observation that a cone over F with apex x
   IS a natural transformation Δ(x) ⟹ F -- the equivalence Wikipedia
   records under “Cone (category theory)” and which this library already
   proves as [Cone_Natural_Transform] in Structure/Cone/Const.v.  Given
   that identification, the hom-set form of the adjunction

       (Δ(x) ~{[J,C]}~> F)  ≅  (x ~{C}~> lim F)

   is literally the universal property of the limit, read as a bijection
   rather than as unique existence; naturality in both variables is the
   uniqueness clause applied twice.  Everything below is that one move,
   plus its dual, plus the bookkeeping that makes both directions of
   Riehl's proposition into a genuine biconditional.

   Why this presentation earns its keep.  The elementary statement
   “every diagram of shape J has a limit” is a family of unrelated
   universal properties; the adjoint statement packages them into a single
   functor with a single universal property, after which every general
   theorem about adjunctions applies at once -- uniqueness of adjoints,
   composition of adjunctions, and (the reason the sandwich is quoted so
   often) the fact that left adjoints preserve colimits and right adjoints
   preserve limits.  It is also the shape in which Kan introduced the
   subject: Structure/Limit/Kan/Extension.v records the other reading,
   lim F = Ran_(Erase J) F, which is the same universal property with the
   terminal category in place of the point of Cat. *)

(* What is consumed here, and what is built

   CONSUMED, not rebuilt:

     - Functor/Diagonal.v: [Diagonal] and the notation Δ[J](c).
     - Structure/Cone.v: [ACone], [Cone], [Cocone].
     - Structure/Cone/Const.v: [Cone_Natural_Transform], the hom-set
       identification on which the whole file rests.  This is its first
       consumer outside its own module (measured PRE-COMMIT: exactly ONE
       file, its own, mentioned the name; this commit makes it three,
       counting the probe).  It is [Defined], and BOTH directions are
       definitional on components -- pinned in-file as the two [eq_refl]
       Examples [cone_natural_transform_to_component] and
       [cone_natural_transform_from_component].
     - Structure/Limit.v: [Limit], [IsALimit], [Colimit].
     - Structure/Complete.v: [Complete], [Cocomplete].
     - Structure/Limit/Preservation.v: the covariant accessor layer --
       [cone_leg], [limit_leg], [limit_leg_coherence], [limit_med],
       [limit_med_commutes], [limit_med_unique], [limit_med_eq],
       [limit_is_alimit], and dually [cocone_inj], [cocone_inj_coherence],
       [IsAColimit], [colimit_inj], [colimit_inj_coherence],
       [colimit_med], [colimit_med_commutes], [colimit_med_unique],
       [colimit_med_eq], [colimit_apex], [colimit_is_acolimit].  This is
       the single largest saving in the file: it is what lets the colimit
       half be stated and proved covariantly.  Read the covariance claim
       exactly: [Colimit_Diagonal_Adjunction], [ColimitFunctor],
       [Colim_map], [colim_unit], [colimits_iff_diagonal_left_adjoint],
       [colim_unit_is_colimit_inj] and [cocone_apex] carry no [^op] in
       their types, but [Cocone_Natural_Transform] DOES -- its right-hand
       side is an [ACone] over the opposites -- so “no [^op] anywhere a
       consumer can see” would be false, and an audit caught an earlier
       draft saying it.
     - Theory/Adjunction.v: [Adjunction], [unit], [counit],
       [adj_univ_impl], [to_adj_unit], [to_adj_comp_law],
       [from_adj_comp_law], [to_adj_respects], [from_adj_respects].
     - Theory/Kan/Extension.v: [Induced], [Ran], [RightKan];
       Structure/Limit/Kan/Extension.v: [Kan_Limit].
     - Structure/Limit/Terminal.v: [Terminal_Limit].
     - Instance/One.v: [_1], [Erase]; Instance/Zero.v: [_0], [From_0].
     - Instance/Sets/Complete.v: [Sets_Complete];
       Instance/Sets/Cocomplete.v: [Sets_Cocomplete].

   BUILT here:

     - [HasLimitsOfShape J C] / [HasColimitsOfShape J C], the per-shape
       hypotheses.  These, rather than [Complete], because the adjunction
       is about ONE fixed J and taking all shapes would over-assume;
       [Complete_HasLimitsOfShape] and its dual instantiate [Complete] to
       them in one line, so nothing is lost.
     - [LimitFunctor] / [ColimitFunctor] with their arrow parts [Lim_map]
       and [Colim_map] (Mac Lane §V.2 Ex 3), each with its defining
       commuting square ([Lim_map_commutes], [Colim_map_commutes]) and its
       uniqueness clause ([Lim_map_unique], [Colim_map_unique]) as
       separately named lemmas.  All three functor laws come from
       uniqueness of the mediator; none inspects an element.
     - [Diagonal_Limit_Adjunction : Δ[J] ⊣ LimitFunctor] and
       [Colimit_Diagonal_Adjunction : ColimitFunctor ⊣ Δ[J]], both in the
       hom-set form of Theory/Adjunction.v.  The colimit statement is
       COVARIANT: no [^op] occurs in its type.
     - [Cocone_Natural_Transform], the dual of the donor lemma.  The tree
       carries only the cone orientation (measured: [Structure/Cone/Const.v]
       proves [Cone_Natural_Transform] and [Cone_Comma] and nothing else,
       and no file in the tree mentions a cocone counterpart), so it is
       built here out of [cocone_of_transform] and [transform_of_cocone],
       whose component-level round trips hold at [eq_refl] both ways.
     - Riehl Proposition 4.6.1 as a genuine biconditional in both
       variances: [limits_iff_diagonal_right_adjoint] and
       [colimits_iff_diagonal_left_adjoint].  The converse directions are
       [Diagonal_right_adjoint_HasLimits] and
       [Diagonal_left_adjoint_HasColimits], which read the limit cone off
       the counit and the colimit cocone off the unit.
     - Riehl exercise 4.6.ii: [lim_counit_is_limit_leg] and
       [colim_unit_is_colimit_inj].
     - Riehl exercise 4.6.i / Awodey §9.3: the degenerate rows, as
       [Erase_right_adjoint_iff_Terminal] and
       [Erase_left_adjoint_iff_Initial], together with the empty-shape
       corollaries [HasLimitsOfShape_0_iff_Terminal] and
       [Terminal_iff_Diagonal_0_right_adjoint].
     - The Kan comparison [lim_Ran_iso], plus the on-the-nose
       identification of Δ[J](c) with the restriction of the constant
       functor along [Erase J].
     - [Diagonal_continuous : ContinuousFunctor (Diagonal J)], added for
       Mac Lane §V.7's colimits of algebras (#450): the diagonal preserves
       every limit, computed one component at a time.  It is the
       preservation hypothesis of the adjoint functor theorem at Δ[J], and
       the section at the end of the file says how the colimit
       applications consume it. *)

(*
Strengths, measured strict-first

   TWENTY-FIVE identifications hold at Leibniz [eq] and are shipped as
   [eq_refl] Examples; two further Leibniz equalities,
   [lim_transpose_from_component] and [colim_transpose_to_component], are
   proved by [reflexivity] because they are used as rewrite rules.  The
   ones worth knowing:

     - the donor bijection is definitional on components in both
       directions (the two [cone_natural_transform_*] Examples, and their
       cocone counterparts [cocone_of_transform_inj] and
       [transform_of_cocone_component]);
     - [fobj[LimitFunctor] F] IS [vertex_obj[limit_cone (L F)]], and
       [fobj[ColimitFunctor] F] IS [colimit_apex (L F)];
     - the two transposes of each adjunction ARE the named maps
       ([lim_transpose_to_is_adj] and its three siblings), so a consumer
       who unfolds [adj] meets the construction rather than a repackaging;
     - [transform[lim_counit L F] j = lim_leg L F j ∘ id] and
       [transform[colim_unit M F] j = id ∘ colim_inj M F j];
     - [fobj[Δ[J](c)] j] and [fmap[Δ[J](c)] f] agree on the nose with the
       restriction along [Erase J] of the constant functor [1 ⟶ C];
     - the adjoint produced from a terminal object has that object as its
       value at [ttt], and conversely [terminal_obj] of the recovered
       [Terminal] IS [R ttt].

   FOUR strict attempts were made and REJECTED; each is a CONVERSION
   failure (“cannot unify”), verified by stripping the guard and reading
   the error, and each is stated here so it can be pinned as a probe:

     R1. [transform[lim_counit L F] j = lim_leg L F j] -- the counit
         component carries a residual [∘ id] (the control at
         [lim_leg L F j ∘ id] succeeds), so Riehl 4.6.ii lands at [≈] and
         not at [eq].
     R2. [transform[colim_unit M F] j = colim_inj M F j] -- dually, an
         [id ∘] residue.
     R3. [Δ[J](c) = fobj[Induced (Erase J)] (Diagonal 1 c)] as whole
         records -- both ACTIONS agree at [eq_refl] (shipped as
         [diagonal_is_induced_obj] and [diagonal_is_induced_map]); what
         differs is the three [Functor] law fields, [Compose]'s
         obligations against [Diagonal]'s.  [diagonal_induced_iso] gives
         the identity-component isomorphism instead.
     R4. [_0^op = _0] -- the empty category is not its own opposite on the
         nose (the law fields are rebuilt).  This is why the colimit
         analogue of [Terminal_Limit] is not available by instantiation;
         see the not-delivered list.

   The one place a [Qed] blocks further measurement is [Kan_Limit], which
   Structure/Limit/Kan/Extension.v closes opaquely; consequently
   [lim_Ran_iso] is opaque too (reported by [About]) and neither of its
   legs reduces, so no componentwise statement about it is available. 

--------
优势，严格优先衡量

Leibniz [eq] 拥有二十五个标识，并作为
 [eq_refl] 示例； 另外两个莱布尼茨等式，
 [lim_transpose_from_component] 和 [colim_transpose_to_component] 是
 由 [reflexivity] 证明，因为它们被用作重写规则。 的
 值得了解的：

- 供体双射在两个组件上都有定义
 方向（两个 [cone_natural_transform_*] 示例及其
 椰子对应物 [cocone_of_transform_inj] 和
 [transform_of_cocone_component]）；
 - [fobj[LimitFunctor] F] 是 [vertex_obj[limit_cone (L F)]]，并且
 [fobj[ColimitFunctor] F] 是 [colimit_apex (L F)]；
 - 每个附加的两个转置是命名的映射
 （[lim_transpose_to_is_adj] 及其三个兄弟），因此消费者
 展开[adj]的人会遇到结构而不是重新包装；
 - [transform[lim_counit L F] j = lim_leg L F j ∘ id] 和
 [transform[colim_unit M F] j = id ∘ colim_inj M F j];
 - [fobj[Δ[J](c)] j] 和 [fmap[Δ[J](c)] f] 与鼻子一致
 沿常函子 [1 ⟶ C] 的 [Erase J] 的限制；
 - 从终端对象产生的伴随物将该对象作为其
 [ttt] 处的值，反之，恢复后的 [terminal_obj] 处的值
 [Terminal] 是 [R ttt]。

进行了四次严格的尝试并被拒绝； 每个都是一个转换
 失败（“无法统一”），通过剥离防护并读取来验证
 错误，每个错误都在这里说明，以便可以将其固定为探针：

R1。 [transform[lim_counit L F] j = lim_leg L F j] -- 单位
 组件携带一个剩余的[∘ id]（控制在
 [lim_leg L F j ∘ id] 成功），因此 Riehl 4.6.ii 登陆 [≈] 并
 不在 [eq] 上。 
R2。 [transform[colim_unit M F] j = colim_inj M F j] -- 对偶，一个
 [id ∘] 残留。 
R3。 [Δ[J](c) = fobj[Induced (Erase J)] (对角线 1 c)] 整体
 记录——两个 ACTION 都在 [eq_refl] 上一致（作为
 [diagonal_is_induced_obj] 和 [diagonal_is_induced_map])； 什么
 不同的是[Functor]的三个法场，[Compose]的
 针对 [Diagonal] 的义务。 [diagonal_induced_iso] 给出
 相反，身份组件同构。 
R4。 [_0^op = _0]——空类别不是它自己的对立面
 鼻子（法场重建）。 这就是为什么 colimit
 [Terminal_Limit] 的类似物无法通过实例化获得；
 查看未交付清单。

[Qed] 阻止进一步测量的一个地方是 [Kan_Limit]，它
 Structure/Limit/Kan/Extension.v 不透明关闭； 因此
 [lim_Ran_iso] 也是不透明的（由 [About] 报告），并且它的
 腿减少了，所以没有关于它的组件声明可用。 
*)

(*
Universes, measured off BOTH the binder and the constraint block

   The two readings genuinely disagree in this file, in both directions,
   which is why both are reported.

     - [HasLimitsOfShape@{u u0 u1 u2 u3}] has a constraint block of BOUNDS
       ONLY, with no equation anywhere -- yet its BINDER reads
       [Category@{u1 u2 u2} -> Category@{u3 u2 u2} -> Type@{u}], reusing
       the single level [u2] for J's homs, J's proofs, C's homs and C's
       proofs.  A reader who checks only the block concludes “nothing is
       identified” and is wrong.
     - [LimitFunctor], [Diagonal_Limit_Adjunction], [ColimitFunctor],
       [Colimit_Diagonal_Adjunction], [lim_obj], [Lim_map],
       [Cocone_Natural_Transform], [radj_Limit] and
       [Diagonal_right_adjoint_HasLimits] run the other way: their BINDERS
       read [{J : Category@{u u0 u0}} {C : Category@{u1 u2 u2}}], which
       looks as though J's and C's hom levels are independent, while the
       BLOCK carries [u0 = u2].  So the identification of the two hom
       universes is in the block here and in the binder there.
     - The two headline biconditionals are stated over
       [J : Category@{u u u}] and [C : Category@{u0 u u}]: the index
       category's OBJECT universe additionally collapses onto the shared
       hom level, leaving only C's object universe free.  It enters at the
       PACKAGING and not in either direction: both
       [Diagonal_Limit_Adjunction] and [Diagonal_right_adjoint_HasLimits]
       keep J's object universe free of its hom universe, measured
       separately.  Which of [iffT] and [sigT] is responsible is NOT
       separated -- the packaged statement mentions both -- and nothing
       here says the collapse is unavoidable.
     - The [Erase] rows carry NO [Set].  They did when first written --
       [Terminal_Erase_Adjunction] elaborated at [C : Category@{u3 Set Set}]
       -- and the cause was located rather than guessed: the TYPE
       [Erase C ⊣ Diagonal 1 (terminal_obj)] is formable in a section
       declaring [Constraint Set < ch] (checked), and the same proof text
       compiles there, so the pin was universe minimization at an
       unannotated [Context {C : Category}] and not content.  Declaring
       [Universes eo eh ep] on the section lifts it.  Annotating
       [one_arrow_eq] alone does NOT lift it -- that was tried first and
       the pin persisted, which is what rules the obvious alternative out.
     - [HasLimitsOfShape_0_iff_Terminal] and
       [Terminal_iff_Diagonal_0_right_adjoint] DO carry [Set]:
       [C : Category@{u7 Set Set}].  This is INHERITED, not introduced --
       [Instance/Zero.v]'s own signature is
       [_0@{u u0 u1 u2 u3 u4 u5} : Category@{u Set Set}], its hom type
       being [Empty_set : Set] under an unannotated declaration -- and it
       is not repaired here.  Nothing says it is unavoidable.
     - [Sets_Diagonal_Limit_Adjunction@{u u0 u1}] is over
       [J : Category@{u1 u1 u1}], inherited from
       [Sets_Complete@{u u0} : Complete@{u u u u0}].
     - [sets_bool_lim_two_elements@{u}] carries the single constraint
       [Set < u], from [bool : Set]. 

--------
宇宙，从粘合剂和约束块上测量

在这个文件中，两种读物在两个方向上确实不一致，
 这就是两者都被报道的原因。

- [HasLimitsOfShape@{u u0 u1 u2 u3}] 有一个 BOUNDS 约束块
 只是，任何地方都没有方程式——但它的 BINDER 上写着
 [Category@{u1 u2 u2} -> Category@{u3 u2 u2} -> Type@{u}]，重复使用
 J's homs、J'sproofs、C's homs 和 C's 的单级 [u2]
 证明。 只检查该块的读者得出的结论是“没有什么是
 已识别”并且是错误的。 - XPTECT3X、[Diagonal_Limit_Adjunction]、[ColimitFunctor]、
 XPTECT6X、[lim_obj]、[Lim_map]、
 [Cocone_Natural_Transform]、[radj_Limit] 和
 [Diagonal_right_adjoint_HasLimits] 以另一种方式运行：他们的 BINDERS
 读取 [{J : Category@{u u0 u0}} {C : Category@{u1 u2 u2}}]，其中
 看起来好像 J 和 C 的 hom 电平是独立的，而
 BLOCK 搭载 [u0 = u2]。 那么这两个hom的识别
 宇宙在这里的块里，那里的活页夹里。
- 两个标题双条件句已陈述完毕
 [J : Category@{u u u}] 和 [C : Category@{u0 u u}]：索引
 类别的 OBJECT 宇宙另外折叠到共享
 hom 级别，仅留下 C 的对象宇宙自由。 它进入于
 包装且不在任一方向：两者
 [Diagonal_Limit_Adjunction] 和 [Diagonal_right_adjoint_HasLimits]
 保持 J 的物体宇宙与其本位宇宙无关，已测量
 分别。 [iffT] 和 [sigT] 中哪一个负责？ 
分开——打包的声明提到了两者——但什么也没提到
 这里说崩溃是不可避免的。 - [Erase] 行不包含 [Set]。
他们在第一次写作时就这样做了——
 [Terminal_Erase_Adjunction] 在 [C : Category@{u3 Set Set}] 上详细阐述
 -- 原因是定位而不是猜测：类型
 [Erase C ⊣ Diagonal 1 (terminal_obj)] 可分段成型
 声明 [Constraint Set < ch]（选中），以及相同的证明文本
 在那里编译，所以引脚是宇宙最小化
 未注释的 [Context {C : Category}] 并且不是内容。 声明
 部分上的 [Universes eo eh ep] 将其抬起。 注释
 [one_arrow_eq] 单独无法解除它——这是首先尝试过的，
 该引脚仍然存在，这就是排除明显替代方案的原因。 - [HasLimitsOfShape_0_iff_Terminal] 和
 [Terminal_iff_Diagonal_0_right_adjoint] DO 携带 [Set]：
 [C : Category@{u7 Set Set}]。 这是继承的，不是引入的——
 [Instance/Zero.v]自己的签名是
 [_0@{u u0 u1 u2 u3 u4 u5} : Category@{u Set Set}]，其 hom 类型
 在未注释的声明下是 [Empty_set : Set] ——并且它
 这里没有修复。 没有什么说这是不可避免的。
- [Sets_Diagonal_Limit_Adjunction@{u u0 u1}] 结束
 [J : Category@{u1 u1 u1}]，继承自
 [Sets_Complete@{u u0} : Complete@{u u u u0}]。 - [sets_bool_lim_two_elements@{u}] 带有单一约束
 [Set < u]，来自 [bool : Set]。 
*)

(*
Non-vacuity

   [Sets] is both complete and cocomplete in tree, so the whole sandwich
   is inhabited there at every shape:
   [Sets_Diagonal_Limit_Adjunction] and [Sets_Colimit_Diagonal_Adjunction].
   That the witness is not degenerate is proved rather than asserted.
   [lim_one_iso] shows that over ANY C with limits of shape [1] the limit
   apex is isomorphic to the value of the diagram at the point; instantiated
   at [Sets] with the constant diagram at the two-element discrete setoid,
   [sets_bool_lim_two_elements] exhibits two elements of the limit apex
   that are provably not [≈]-equal, so the limit functor does not collapse
   its argument to a subsingleton.  The two elements are obtained by
   transporting [true] and [false] backwards along the isomorphism, and
   the separation is discharged by [discriminate] on the underlying
   [bool]; no induction on a limit construction could yield a negative. 

--------
非空性

 [Sets] 在树上既是完整的又是协完整的，所以整个三明治
 那里居住着各种形状的人：
 [Sets_Diagonal_Limit_Adjunction] 和 [Sets_Colimit_Diagonal_Adjunction]。 
证人并未堕落是被证明而不是被断言。 
[lim_one_iso] 表明，对于具有形状限制的任何 C，[1] 的限制
 顶点与图中该点的值同构； 实例化
 在 [Sets] 上，具有二元离散集合常数图，
 [sets_bool_lim_two_elements] 展现极限顶点的两个要素
 证明不等于 [≈]，因此极限函子不会崩溃
 它的参数是一个子单例。 这两个元素通过以下方式获得
 沿着同构向后传输 [true] 和 [false]，并且
 [discriminate] 在底层上释放分离
 [bool]； 对极限构造的归纳不会产生负值。 
*)

(*
What is NOT delivered

     - No naturality for the Kan comparison.  [lim_Ran_iso] is a FAMILY of
       isomorphisms [lim F ≅ Ran (Erase J) F ttt], not a natural
       isomorphism of functors.  AN EARLIER DRAFT OF THIS BULLET STATED
       THE OBSTRUCTION WRONGLY IN BOTH CLAUSES; an audit refuted each, and
       what follows is the measured position.  An evaluation functor DOES
       exist: Theory/Shapes.v's [One_Eval : [_1, C] ⟶ C], whose
       constraint block contains no [Set] and leaves C's three levels
       free.  And [Sets] DOES meet [Category@{o Set Set}] --
       [Check (@One_Fun_iso Sets)] SUCCEEDS, universe polymorphism
       instantiating it at [Sets@{Set _}], the same trap Theory/Size.v's
       erratum records for [Check (Cat : obj[Cat])] -- so “which [Sets]
       does not meet” was false.  What stands: the transport needs the
       OTHER variance, [C ⟶ [1, C]], since
       [Induced (Erase J) : [1,C] ⟶ [J,C]], and both in-tree candidates
       for that direction ([One_Const], [One_Fun_iso]) ARE pinned at
       [Category@{_ Set Set}]; and [Kan_Limit] is [Qed], so [lim_Ran_iso]
       is opaque (confirmed by [About]) and no componentwise access
       exists.  The transport was NOT attempted; neither obstruction is
       claimed unavoidable.
     - No colimit counterpart of the Kan comparison: the tree has no
       [Kan_Colimit], so nothing relates [ColimitFunctor] to [Lan].
     - NO RESTRICTED LIMIT FUNCTOR, and the source issue asks for it in
       its own checkbox: the limit functor on the FULL SUBCATEGORY of
       [[J, C]] spanned by the diagrams that have limits -- the form
       Riehl uses for Corollary 3.3.3, and the one that does NOT require C
       to have all J-shaped limits.  Everything here takes
       [HasLimitsOfShape J C] as a hypothesis, so that checkbox is NOT
       discharged.  Theory/Equivalence/Colimit.v's [limit_induced] is the
       nearest thing in tree -- it needs only the two limits handed to it
       -- but it is a morphism between two supplied limits, not a functor
       on a subcategory, and nothing assembles it into one.
     - No dual of [Terminal_Limit].  Structure/Limit/Terminal.v proves
       only the limit half, and the obvious instantiation does not
       typecheck because [_0^op] is not [_0] (rejection R4 above).  So
       there is no [HasColimitsOfShape 0 C ↔ Initial C] and no
       [Initial_iff_Diagonal_0_left_adjoint]; the initial-object row is
       delivered only in its [Erase] form.
     - No identification of [[0, C]] with [1], hence [Δ[0]] is NOT shown
       to be [Erase C]; the two degenerate readings are connected only
       through [Terminal C], via the composite
       [Terminal_iff_Diagonal_0_right_adjoint].
     - No uniqueness of the adjoint: [left_adjoint_iso] and
       [right_adjoint_iso] are not instantiated, so nothing here says
       [LimitFunctor] is THE right adjoint up to natural isomorphism.
     - No reflection or creation results, and no instantiation of
       RAPL/LAPC at this sandwich.  An earlier revision of this bullet also
       said “no preservation results”; since #450 the file proves that the
       diagonal preserves limits ([Diagonal_continuous]).  Preservation of
       COLIMITS by the diagonal, its dual, is not stated.
     - [LimitFunctor] and [ColimitFunctor] are plain [Definition]s, not
       registered [Instance]s: they take a [HasLimitsOfShape] parameter,
       which is not a class, so resolution could never produce it.
     - The round trips of [Cocone_Natural_Transform] are not proved at the
       level of the packaged bijection -- only the component-level
       identities, which are [eq_refl].  The donor lemma is in the same
       position.
     - The non-vacuity witness lives at the shape [1] only.  Nothing here
       exhibits a non-degenerate limit over a shape with more than one
       object, and the colimit side has no element-level witness at all.
     - No functoriality of [LimitFunctor] in the shape [J], no comparison
       with Instance/Cones/Limit.v's [Limit_Cones], and no connection to
       Structure/Limit/Unique.v. 

--------
未交付的内容

- Kan 比较不自然。 [lim_Ran_iso] 是一个家族
 同构 [lim F ≅ Ran (Erase J) F ttt]，不是自然的
 函子的同构。 该项目符号的早期草案指出
 两个条款中的妨碍都是错误的； 审计驳斥了每一项，并且
 接下来是测量的位置。 求值函子确实如此
 存在：Theory/Shapes.v 的 [One_Eval : [_1, C] ⟶ C]，其
 约束块不包含 [Set] 并保留 C 的三个级别
 免费。 [Sets] 确实满足 [Category@{o Set Set}] --
 [Check (@One_Fun_iso Sets)] 成功，宇宙多态性
 在 [Sets@{Set _}] 实例化它，与 Theory/Size.v 的陷阱相同
 [Check (Cat : obj[Cat] 的勘误记录）] - 所以“哪个 [Sets]
 不满足”是错误的。
代表什么：运输需要
 其他方差，[C ⟶ [1, C]]，因为
 [Induced (Erase J) : [1,C] ⟶ [J,C]]，以及树内候选者
 对于该方向（[One_Const]、[One_Fun_iso]）固定在
 [Category@{_ Set Set}]； [Kan_Limit] 是 [Qed]，所以 [lim_Ran_iso]
 是不透明的（由 [About] 确认）并且没有组件访问
 存在。 未尝试传输； 两者都不是障碍
 声称不可避免。 - Kan 比较没有 colimit 对应项：树没有
 [Kan_Colimit]，因此 [ColimitFunctor] 与 [Lan] 没有任何关系。 - 没有 RESTRICTED LIMIT FUNCTOR，并且源问题要求它在
 它自己的复选框：完整子类别上的极限函子
 [[J, C]] 由有限制的图跨越 - 形式
 Riehl 用于推论 3.3.3，并且不需要 C
 具有所有 J 形限制。
这里的一切都需要
 [HasLimitsOfShape J C] 作为假设，因此该复选框不是
 出院了。 Theory/Equivalence/Colimit.v 的 [limit_induced] 是
 树中最近的东西——它只需要传递给它的两个限制
 -- 但它是两个提供的极限之间的态射，而不是函子
 放在一个子类别上，没有任何东西可以将其组合成一个子类别。 - 没有 [Terminal_Limit] 的双重功能。 Structure/Limit/Terminal.v 证明
 只有极限的一半，并且明显的实例化并没有
 类型检查，因为 [_0^op] 不是 [_0]（上面拒绝 R4）。 所以
 没有 [HasColimitsOfShape 0 C ↔ Initial C] 也没有
 XPTECT30X； 初始对象行是
 仅以 [Erase] 形式提供。
- 无法识别 [[0, C]] 与 [1]，因此未显示 [Δ[0]]
 成为 [Erase C]； 两个简并读数仅相连
 通过 [Terminal C]，通过复合材料
 XPTECT37X。 - 伴随项没有唯一性：[left_adjoint_iso] 和
 [right_adjoint_iso] 没有实例化，所以这里什么也没说
 [LimitFunctor] 是自然同构的右伴随。 - 没有反射或创建结果，也没有实例化
 RAPL/LAPC 在这个三明治上。 该项目符号的早期修订版也
 说“没有保存结果”； 从#450开始，该文件证明
 对角线保留限制 ([Diagonal_continuous])。 保存
 没有说明对角线的 COLIMITS，它的对偶。
- [LimitFunctor] 和 [ColimitFunctor] 是普通 [Definition]，而不是
 注册 [Instance]：它们采用 [HasLimitsOfShape] 参数，
 它不是一个类，因此解析永远无法产生它。 - [Cocone_Natural_Transform] 的往返行程未在
 打包双射的级别——仅组件级别
 身份，即 [eq_refl]。 捐赠者引理在同一个
 位置。 - 非真空见证人仅存在于 [1] 形状中。 这里什么都没有
 对具有多个形状的形状表现出非简并极限
 对象，并且 colimit 方根本没有元素级见证。 - [J] 形状中没有 [LimitFunctor] 的功能，没有比较
 与 Instance/Cones/Limit.v 的 [Limit_Cones]，并且没有连接到
 结构/限制/唯一.v. 
*)

(*
Axiom status and counts

   177/177 constants report “Closed under the global context”.  Method:
   [Print Module Category.Adjunction.Diagonal.Limit] enumerates 177 names
   (90 printed as [Definition], 87 as [Parameter], the latter being the
   display convention for [Qed] constants, not axioms); the file declares
   no [Record], [Class] or [Inductive], so there is no unlisted [Build_*]
   constructor, and the count includes the 60 [Program] obligations that a
   [.glob] sweep does not record -- the [.glob] shows 117 names, and
   177 - 117 = 60 is exactly the number of [_obligation_] entries in the
   module listing.  Each name was queried by its FULLY QUALIFIED name.
   One measurement anomaly is recorded rather than hidden: a single run of
   all 177 queries reports 176 occurrences of the message, while nine
   chunked runs of at most 20 queries each report exactly one per query
   and cover every name once (20*8 + 17 = 177), as do two halves of 89 and
   88; the chunked counts are the reliable ones.

   The 177 is the count before #450.  The section added for #450 brings
   eight more ([diag_eval_cone], [diag_med], [diag_med_commutes],
   [diag_med_unique], [Diagonal_continuous] and three [Program]
   obligations), so [Print Module] now enumerates 185 names; each of the
   eight was queried by its fully qualified name and reports “Closed under
   the global context”. 

--------
Axiom 状态和计数

177/177常量报告“在全局背景下关闭”。 方法：
 [Print Module Category.Adjunction.Diagonal.Limit] 枚举 177 个名称
 （90 打印为 [Definition]，87 打印为 [Parameter]，后者是
 [Qed] 常量的显示约定，而不是公理）； 该文件声明
 没有 [Record]、[Class] 或 [Inductive]，因此没有未列出的 [Build_*]
 构造函数，计数包括 60 个 [Program] 义务
 [.glob] 扫描不记录 - [.glob] 显示 117 个名称，并且
 177 - 117 = 60 正是 [_obligation_] 条目的数量
 模块列表。 每个名称均按其完全限定名称进行查询。 
记录而不是隐藏一个测量异常：单次运行
 所有 177 个查询报告了该消息的 176 次出现，而 9 次
 最多 20 个查询的分块运行，每个查询只报告一个
 并将每个名字覆盖一次 (20*8 + 17 = 177)，就像 89 的两半和
 88； 分块计数是可靠的。

177 是#450 之前的计数。 为 #450 添加的部分带来了
 另外八个（[diag_eval_cone]、[diag_med]、[diag_med_commutes]、
 [diag_med_unique]、[Diagonal_continuous] 和三个 [Program]
 义务），因此 [Print Module] 现在枚举了 185 个名称； 每个
 八号通过其完全限定名称进行查询并报告“已关闭”
 全球背景”。 
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Kan.Extension.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Cone.Const.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Kan.Extension.
Require Import Category.Structure.Limit.Terminal.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Fun.
Require Import Category.Instance.One.
Require Import Category.Instance.Zero.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Cocomplete.

Generalizable All Variables.

(** * Shape-indexed limit and colimit hypotheses  / * 形状索引极限和余极限假设*)

Definition HasLimitsOfShape (J C : Category) : Type := ∀ F : J ⟶ C, Limit F.

Definition HasColimitsOfShape (J C : Category) : Type :=
  ∀ F : J ⟶ C, Colimit F.

Definition Complete_HasLimitsOfShape {C : Category} (H : @Complete C)
  (J : Category) : HasLimitsOfShape J C := H J.

Definition Cocomplete_HasColimitsOfShape {C : Category} (H : @Cocomplete C)
  (J : Category) : HasColimitsOfShape J C := H J.

(** * The limit functor and the adjunction Δ ⊣ lim  / * 极限函子和附加 Δ ⊣ lim*)

Section LimitAdjunction.

Context {J C : Category}.
Context (L : HasLimitsOfShape J C).

Definition lim_obj (F : J ⟶ C) : C := vertex_obj[@limit_cone J C F (L F)].

Definition lim_alimit (F : J ⟶ C) : IsALimit F (lim_obj F) :=
  limit_is_alimit (L F).

Definition lim_leg (F : J ⟶ C) (j : J) : lim_obj F ~{C}~> F j :=
  limit_leg (lim_alimit F) j.

Lemma lim_leg_coherence (F : J ⟶ C) {x y : J} (f : x ~{J}~> y) :
  fmap[F] f ∘ lim_leg F x ≈ lim_leg F y.
Proof. exact (limit_leg_coherence (lim_alimit F) f). Qed.

Definition lim_med {F : J ⟶ C} (N : Cone F) :
  vertex_obj[N] ~{C}~> lim_obj F := limit_med (lim_alimit F) N.

Lemma lim_med_commutes {F : J ⟶ C} (N : Cone F) (j : J) :
  lim_leg F j ∘ lim_med N ≈ cone_leg N j.
Proof. exact (limit_med_commutes (lim_alimit F) N j). Qed.

Lemma lim_med_unique {F : J ⟶ C} (N : Cone F)
  (u : vertex_obj[N] ~{C}~> lim_obj F) :
  (∀ j : J, lim_leg F j ∘ u ≈ cone_leg N j) → lim_med N ≈ u.
Proof. exact (limit_med_unique (lim_alimit F) N u). Qed.

Lemma lim_med_eq {F : J ⟶ C} (N : Cone F)
  (u v : vertex_obj[N] ~{C}~> lim_obj F) :
  (∀ j : J, lim_leg F j ∘ u ≈ cone_leg N j) →
  (∀ j : J, lim_leg F j ∘ v ≈ cone_leg N j) → u ≈ v.
Proof. exact (limit_med_eq (lim_alimit F) N u v). Qed.

(** ** The action on natural transformations  / ** 对自然转化的作用*)

Program Definition Lim_cone {F G : J ⟶ C} (b : F ⟹ G) : Cone G := {|
  vertex_obj := lim_obj F;
  coneFrom := {| vertex_map := fun j => transform[b] j ∘ lim_leg F j |}
|}.
Next Obligation.
  rewrite comp_assoc, naturality, <- comp_assoc, lim_leg_coherence.
  reflexivity.
Qed.

Definition Lim_map {F G : J ⟶ C} (b : F ⟹ G) : lim_obj F ~{C}~> lim_obj G :=
  lim_med (Lim_cone b).

Lemma Lim_map_commutes {F G : J ⟶ C} (b : F ⟹ G) (j : J) :
  lim_leg G j ∘ Lim_map b ≈ transform[b] j ∘ lim_leg F j.
Proof. exact (lim_med_commutes (Lim_cone b) j). Qed.

Lemma Lim_map_unique {F G : J ⟶ C} (b : F ⟹ G)
  (u : lim_obj F ~{C}~> lim_obj G) :
  (∀ j : J, lim_leg G j ∘ u ≈ transform[b] j ∘ lim_leg F j) → Lim_map b ≈ u.
Proof. exact (lim_med_unique (Lim_cone b) u). Qed.

Program Definition LimitFunctor : [J, C] ⟶ C := {|
  fobj := lim_obj;
  fmap := fun _ _ b => Lim_map b
|}.
Next Obligation.
  proper.
  symmetry.
  apply Lim_map_unique; intro j.
  rewrite Lim_map_commutes.
  now rewrite (X j).
Qed.
Next Obligation.
  apply Lim_map_unique; intro j.
  simpl.
  now rewrite id_right, fmap_id, id_left.
Qed.
Next Obligation.
  apply Lim_map_unique; intro j.
  rewrite comp_assoc, Lim_map_commutes.
  rewrite <- comp_assoc, Lim_map_commutes.
  now rewrite comp_assoc.
Qed.

(** ** The hom-set bijection Δ(x) ⟹ F  ≅  x ~> lim F  / ** 本集双射 Δ(x) ⟹ F ≅ x ~> lim F*)

Program Definition lim_precone {F : J ⟶ C} {x : C}
  (h : x ~{C}~> lim_obj F) : ACone x F := {|
  vertex_map := fun j => lim_leg F j ∘ h
|}.
Next Obligation. now rewrite comp_assoc, lim_leg_coherence. Qed.

Definition lim_transpose_from {F : J ⟶ C} {x : C}
  (h : x ~{C}~> lim_obj F) : Δ[J](x) ⟹ F :=
  snd (Cone_Natural_Transform F x) (lim_precone h).

Definition lim_transpose_cone {F : J ⟶ C} {x : C}
  (t : Δ[J](x) ⟹ F) : Cone F :=
  {| vertex_obj := x; coneFrom := fst (Cone_Natural_Transform F x) t |}.

Definition lim_transpose_to {F : J ⟶ C} {x : C}
  (t : Δ[J](x) ⟹ F) : x ~{C}~> lim_obj F := lim_med (lim_transpose_cone t).

Lemma lim_transpose_to_commutes {F : J ⟶ C} {x : C}
  (t : Δ[J](x) ⟹ F) (j : J) :
  lim_leg F j ∘ lim_transpose_to t ≈ transform[t] j.
Proof. exact (lim_med_commutes (lim_transpose_cone t) j). Qed.

Lemma lim_transpose_to_unique {F : J ⟶ C} {x : C}
  (t : Δ[J](x) ⟹ F) (u : x ~{C}~> lim_obj F) :
  (∀ j : J, lim_leg F j ∘ u ≈ transform[t] j) → lim_transpose_to t ≈ u.
Proof. exact (lim_med_unique (lim_transpose_cone t) u). Qed.

Lemma lim_transpose_from_component {F : J ⟶ C} {x : C}
  (h : x ~{C}~> lim_obj F) (j : J) :
  transform[lim_transpose_from h] j = lim_leg F j ∘ h.
Proof. reflexivity. Qed.

(**
The donor's bijection is definitional on components, in both
    directions; the whole construction rests on these two. 

--------
捐助者的双射是在组件上定义的，在两个方面
 方向； 整个结构取决于这两个人。 
*)

Example cone_natural_transform_to_component {F : J ⟶ C} {x : C}
  (t : Δ[J](x) ⟹ F) (j : J) :
  @vertex_map J C x F (fst (Cone_Natural_Transform F x) t) j
    = transform[t] j := eq_refl.

Example cone_natural_transform_from_component {F : J ⟶ C} {x : C}
  (a : ACone x F) (j : J) :
  transform[snd (Cone_Natural_Transform F x) a] j
    = @vertex_map J C x F a j := eq_refl.

Program Definition lim_adj_iso (x : C) (F : J ⟶ C) :
  @Isomorphism Sets
    {| carrier   := @hom ([J, C]) (Δ[J](x)) F
     ; is_setoid := @homset ([J, C]) (Δ[J](x)) F |}
    {| carrier   := @hom C x (lim_obj F)
     ; is_setoid := @homset C x (lim_obj F) |} := {|
  to   := {| morphism := fun t => lim_transpose_to t |};
  from := {| morphism := fun h => lim_transpose_from h |}
|}.
Next Obligation.
  proper.
  apply lim_transpose_to_unique; intro j.
  rewrite lim_transpose_to_commutes.
  now rewrite (X j).
Qed.
Next Obligation.
  apply lim_transpose_to_unique; intro j.
  now rewrite lim_transpose_from_component.
Qed.
Next Obligation.
  apply lim_transpose_to_commutes.
Qed.

Program Definition Diagonal_Limit_Adjunction : @Diagonal C J ⊣ LimitFunctor :=
  {| adj := lim_adj_iso |}.
Next Obligation.
  apply lim_transpose_to_unique; intro j.
  rewrite comp_assoc, lim_transpose_to_commutes.
  reflexivity.
Qed.
Next Obligation.
  apply lim_transpose_to_unique; intro j.
  rewrite comp_assoc, Lim_map_commutes.
  rewrite <- comp_assoc, lim_transpose_to_commutes.
  reflexivity.
Qed.
Next Obligation.
  rewrite !comp_assoc, Lim_map_commutes.
  reflexivity.
Qed.

(** ** Riehl §4.6 exercise ii: the counit is the limiting cone  / ** Riehl §4.6 练习 ii：单位是极限锥体*)

Definition lim_counit (F : J ⟶ C) : Δ[J](lim_obj F) ⟹ F :=
  @counit ([J, C]) C (@Diagonal C J) LimitFunctor
          Diagonal_Limit_Adjunction F.

Example lim_counit_component_strict (F : J ⟶ C) (j : J) :
  transform[lim_counit F] j = lim_leg F j ∘ id := eq_refl.

Lemma lim_counit_is_limit_leg (F : J ⟶ C) (j : J) :
  transform[lim_counit F] j ≈ lim_leg F j.
Proof. rewrite lim_counit_component_strict; now rewrite id_right. Qed.

(** ** Readbacks against the donor vocabulary  / ** 针对捐赠者词汇的重读*)

Example lim_obj_is_limit_apex (F : J ⟶ C) :
  fobj[LimitFunctor] F = vertex_obj[@limit_cone J C F (L F)] := eq_refl.

Example lim_leg_is_limit_leg (F : J ⟶ C) (j : J) :
  lim_leg F j = limit_leg (lim_alimit F) j := eq_refl.

Example lim_med_is_limit_med {F : J ⟶ C} (N : Cone F) :
  lim_med N = limit_med (lim_alimit F) N := eq_refl.

Example Lim_map_is_fmap {F G : J ⟶ C} (b : F ⟹ G) :
  fmap[LimitFunctor] b = Lim_map b := eq_refl.

Example lim_transpose_to_is_adj {F : J ⟶ C} {x : C} (t : Δ[J](x) ⟹ F) :
  to (@adj ([J, C]) C (@Diagonal C J) LimitFunctor
           Diagonal_Limit_Adjunction x F) t = lim_transpose_to t := eq_refl.

Example lim_transpose_from_is_adj {F : J ⟶ C} {x : C}
  (h : x ~{C}~> lim_obj F) :
  from (@adj ([J, C]) C (@Diagonal C J) LimitFunctor
             Diagonal_Limit_Adjunction x F) h = lim_transpose_from h
  := eq_refl.

End LimitAdjunction.

(** * The colimit functor and the adjunction colim ⊣ Δ  / * colimit 函子和附加项 colim ⊣ Δ*)

Section ColimitAdjunction.

Context {J C : Category}.
Context (L : HasColimitsOfShape J C).

Definition colim_obj (F : J ⟶ C) : C := colimit_apex (L F).

Definition colim_acolimit (F : J ⟶ C) : IsAColimit F (colim_obj F) :=
  colimit_is_acolimit (L F).

Definition colim_inj (F : J ⟶ C) (j : J) : F j ~{C}~> colim_obj F :=
  colimit_inj (colim_acolimit F) j.

Lemma colim_inj_coherence (F : J ⟶ C) {x y : J} (f : x ~{J}~> y) :
  colim_inj F y ∘ fmap[F] f ≈ colim_inj F x.
Proof. exact (colimit_inj_coherence (colim_acolimit F) f). Qed.

Definition colim_med {F : J ⟶ C} (N : Cocone F) :
  colim_obj F ~{C}~> vertex_obj[N] := colimit_med (colim_acolimit F) N.

Lemma colim_med_commutes {F : J ⟶ C} (N : Cocone F) (j : J) :
  colim_med N ∘ colim_inj F j ≈ cocone_inj N j.
Proof. exact (colimit_med_commutes (colim_acolimit F) N j). Qed.

Lemma colim_med_unique {F : J ⟶ C} (N : Cocone F)
  (u : colim_obj F ~{C}~> vertex_obj[N]) :
  (∀ j : J, u ∘ colim_inj F j ≈ cocone_inj N j) → colim_med N ≈ u.
Proof. exact (colimit_med_unique (colim_acolimit F) N u). Qed.

Lemma colim_med_eq {F : J ⟶ C} (N : Cocone F)
  (u v : colim_obj F ~{C}~> vertex_obj[N]) :
  (∀ j : J, u ∘ colim_inj F j ≈ cocone_inj N j) →
  (∀ j : J, v ∘ colim_inj F j ≈ cocone_inj N j) → u ≈ v.
Proof. exact (colimit_med_eq (colim_acolimit F) N u v). Qed.

(** ** Building cocones covariantly  / ** 协变地构建 cocones*)

Program Definition Cocone_of {F : J ⟶ C} (c : C)
  (i : ∀ j : J, F j ~{C}~> c)
  (Hi : ∀ (x y : J) (f : x ~{J}~> y), i y ∘ fmap[F] f ≈ i x) : Cocone F := {|
  vertex_obj := c;
  coneFrom := {| vertex_map := i |}
|}.

Example cocone_of_inj {F : J ⟶ C} (c : C) i Hi (j : J) :
  cocone_inj (@Cocone_of F c i Hi) j = i j := eq_refl.

(** ** The dual of [Cone_Natural_Transform]  / ** [Cone_Natural_Transform] 的双重*)

Program Definition cocone_of_transform {F : J ⟶ C} {N : C}
  (t : F ⟹ Δ[J](N)) : Cocone F :=
  Cocone_of N (fun j => transform[t] j) _.
Next Obligation.
  pose proof (@naturality_sym J C F (Δ[J](N)) t x y f) as HN.
  rewrite HN.
  apply id_left.
Qed.

Definition cocone_apex {F : J ⟶ C} (N : Cocone F) : C :=
  @vertex_obj (J^op) (C^op) (F^op) N.

Program Definition transform_of_cocone {F : J ⟶ C} (N : Cocone F) :
  F ⟹ Δ[J](cocone_apex N) := {|
  transform := fun j => cocone_inj N j
|}.
Next Obligation.
  rewrite (cocone_inj_coherence N f); apply id_left.
Qed.
Next Obligation.
  rewrite (cocone_inj_coherence N f); symmetry; apply id_left.
Qed.

Example cocone_of_transform_inj {F : J ⟶ C} {N : C}
  (t : F ⟹ Δ[J](N)) (j : J) :
  cocone_inj (cocone_of_transform t) j = transform[t] j := eq_refl.

Example transform_of_cocone_component {F : J ⟶ C} (N : Cocone F) (j : J) :
  transform[transform_of_cocone N] j = cocone_inj N j := eq_refl.

Lemma Cocone_Natural_Transform (F : J ⟶ C) (N : C) :
  (F ⟹ Δ[J](N)) ↔ @ACone (J^op) (C^op) N (F^op).
Proof.
  split; intro t.
  - exact (@coneFrom (J^op) (C^op) (F^op) (cocone_of_transform t)).
  - exact (transform_of_cocone (@Build_Cone (J^op) (C^op) (F^op) N t)).
Defined.

(** ** The action on natural transformations  / ** 对自然转化的作用*)

Program Definition Colim_cocone {F G : J ⟶ C} (b : F ⟹ G) : Cocone F :=
  Cocone_of (colim_obj G) (fun j => colim_inj G j ∘ transform[b] j) _.
Next Obligation.
  pose proof (@naturality J C F G b x y f) as HN.
  rewrite <- comp_assoc, <- HN.
  now rewrite comp_assoc, colim_inj_coherence.
Qed.

Definition Colim_map {F G : J ⟶ C} (b : F ⟹ G) :
  colim_obj F ~{C}~> colim_obj G := colim_med (Colim_cocone b).

Lemma Colim_map_commutes {F G : J ⟶ C} (b : F ⟹ G) (j : J) :
  Colim_map b ∘ colim_inj F j ≈ colim_inj G j ∘ transform[b] j.
Proof. exact (colim_med_commutes (Colim_cocone b) j). Qed.

Lemma Colim_map_unique {F G : J ⟶ C} (b : F ⟹ G)
  (u : colim_obj F ~{C}~> colim_obj G) :
  (∀ j : J, u ∘ colim_inj F j ≈ colim_inj G j ∘ transform[b] j) →
  Colim_map b ≈ u.
Proof. exact (colim_med_unique (Colim_cocone b) u). Qed.

Program Definition ColimitFunctor : [J, C] ⟶ C := {|
  fobj := colim_obj;
  fmap := fun _ _ b => Colim_map b
|}.
Next Obligation.
  proper.
  symmetry.
  apply Colim_map_unique; intro j.
  rewrite Colim_map_commutes.
  now rewrite (X j).
Qed.
Next Obligation.
  apply Colim_map_unique; intro j.
  simpl.
  now rewrite id_left, fmap_id, id_right.
Qed.
Next Obligation.
  apply Colim_map_unique; intro j.
  rewrite <- comp_assoc, Colim_map_commutes.
  rewrite comp_assoc, Colim_map_commutes.
  now rewrite <- comp_assoc.
Qed.

(** ** The hom-set bijection colim F ~> y  ≅  F ⟹ Δ(y)  / ** 本集双射 colim F ~> y ≅ F ⟹ Δ(y)*)

Program Definition colim_transpose_to {F : J ⟶ C} {y : C}
  (u : colim_obj F ~{C}~> y) : F ⟹ Δ[J](y) := {|
  transform := fun j => u ∘ colim_inj F j
|}.
Next Obligation.
  now rewrite <- comp_assoc, (colim_inj_coherence F f), id_left.
Qed.
Next Obligation.
  now rewrite <- comp_assoc, (colim_inj_coherence F f), id_left.
Qed.

Definition colim_transpose_from {F : J ⟶ C} {y : C} (t : F ⟹ Δ[J](y)) :
  colim_obj F ~{C}~> y := colim_med (cocone_of_transform t).

Lemma colim_transpose_from_commutes {F : J ⟶ C} {y : C}
  (t : F ⟹ Δ[J](y)) (j : J) :
  colim_transpose_from t ∘ colim_inj F j ≈ transform[t] j.
Proof. exact (colim_med_commutes (cocone_of_transform t) j). Qed.

Lemma colim_transpose_from_unique {F : J ⟶ C} {y : C}
  (t : F ⟹ Δ[J](y)) (u : colim_obj F ~{C}~> y) :
  (∀ j : J, u ∘ colim_inj F j ≈ transform[t] j) → colim_transpose_from t ≈ u.
Proof. exact (colim_med_unique (cocone_of_transform t) u). Qed.

Lemma colim_transpose_to_component {F : J ⟶ C} {y : C}
  (u : colim_obj F ~{C}~> y) (j : J) :
  transform[colim_transpose_to u] j = u ∘ colim_inj F j.
Proof. reflexivity. Qed.

Program Definition colim_adj_iso (F : J ⟶ C) (y : C) :
  @Isomorphism Sets
    {| carrier   := @hom C (colim_obj F) y
     ; is_setoid := @homset C (colim_obj F) y |}
    {| carrier   := @hom ([J, C]) F (Δ[J](y))
     ; is_setoid := @homset ([J, C]) F (Δ[J](y)) |} := {|
  to   := {| morphism := fun u => colim_transpose_to u |};
  from := {| morphism := fun t => colim_transpose_from t |}
|}.
Next Obligation.
  proper.
  apply colim_transpose_from_unique; intro j.
  rewrite colim_transpose_from_commutes.
  now rewrite (X j).
Qed.
Next Obligation. apply colim_transpose_from_commutes. Qed.
Next Obligation.
  apply colim_transpose_from_unique; intro j.
  now rewrite colim_transpose_to_component.
Qed.

Program Definition Colimit_Diagonal_Adjunction :
  ColimitFunctor ⊣ @Diagonal C J := {| adj := colim_adj_iso |}.
Next Obligation.
  rewrite <- comp_assoc, Colim_map_commutes.
  now rewrite comp_assoc.
Qed.
Next Obligation.
  apply colim_transpose_from_unique; intro j.
  rewrite <- comp_assoc, Colim_map_commutes.
  now rewrite comp_assoc, colim_transpose_from_commutes.
Qed.
Next Obligation.
  apply colim_transpose_from_unique; intro j.
  now rewrite <- comp_assoc, colim_transpose_from_commutes.
Qed.

(** ** Riehl §4.6 exercise ii: the unit is the colimiting cocone  / ** Riehl §4.6 练习 ii：单位是共界可果*)

Definition colim_unit (F : J ⟶ C) : F ⟹ Δ[J](colim_obj F) :=
  @unit C ([J, C]) ColimitFunctor (@Diagonal C J)
        Colimit_Diagonal_Adjunction F.

Example colim_unit_component_strict (F : J ⟶ C) (j : J) :
  transform[colim_unit F] j = id ∘ colim_inj F j := eq_refl.

Lemma colim_unit_is_colimit_inj (F : J ⟶ C) (j : J) :
  transform[colim_unit F] j ≈ colim_inj F j.
Proof. rewrite colim_unit_component_strict; now rewrite id_left. Qed.

(** ** Readbacks against the donor vocabulary  / ** 针对捐赠者词汇的重读*)

Example colim_obj_is_colimit_apex (F : J ⟶ C) :
  fobj[ColimitFunctor] F = colimit_apex (L F) := eq_refl.

Example colim_inj_is_colimit_inj (F : J ⟶ C) (j : J) :
  colim_inj F j = colimit_inj (colim_acolimit F) j := eq_refl.

Example colim_med_is_colimit_med {F : J ⟶ C} (N : Cocone F) :
  colim_med N = colimit_med (colim_acolimit F) N := eq_refl.

Example Colim_map_is_fmap {F G : J ⟶ C} (b : F ⟹ G) :
  fmap[ColimitFunctor] b = Colim_map b := eq_refl.

Example colim_transpose_to_is_adj {F : J ⟶ C} {y : C}
  (u : colim_obj F ~{C}~> y) :
  to (@adj C ([J, C]) ColimitFunctor (@Diagonal C J)
           Colimit_Diagonal_Adjunction F y) u = colim_transpose_to u
  := eq_refl.

Example colim_transpose_from_is_adj {F : J ⟶ C} {y : C}
  (t : F ⟹ Δ[J](y)) :
  from (@adj C ([J, C]) ColimitFunctor (@Diagonal C J)
             Colimit_Diagonal_Adjunction F y) t = colim_transpose_from t
  := eq_refl.

End ColimitAdjunction.

(** * Riehl §4.6 Proposition 4.6.1, the converse directions  / * Riehl §4.6 命题 4.6.1，相反的方向*)

Section RightAdjointGivesLimits.

Context {J C : Category}.
Context {R : [J, C] ⟶ C}.
Context (A : @Diagonal C J ⊣ R).

Definition radj_counit (F : J ⟶ C) : Δ[J](R F) ⟹ F :=
  @counit ([J, C]) C (@Diagonal C J) R A F.

Definition radj_transpose {x : C} {F : J ⟶ C} (t : Δ[J](x) ⟹ F) :
  x ~{C}~> R F := to (@adj ([J, C]) C (@Diagonal C J) R A x F) t.

Lemma radj_transpose_commutes {x : C} {F : J ⟶ C}
  (t : Δ[J](x) ⟹ F) (j : J) :
  transform[radj_counit F] j ∘ radj_transpose t ≈ transform[t] j.
Proof.
  pose proof (snd (@adj_univ_impl ([J, C]) C (@Diagonal C J) R A x F t
                     (radj_transpose t)) (reflexivity _)) as HU.
  symmetry; exact (HU j).
Qed.

Lemma radj_transpose_unique {x : C} {F : J ⟶ C}
  (t : Δ[J](x) ⟹ F) (v : x ~{C}~> R F) :
  (∀ j : J, transform[radj_counit F] j ∘ v ≈ transform[t] j) →
  radj_transpose t ≈ v.
Proof.
  intro Hv.
  apply (fst (@adj_univ_impl ([J, C]) C (@Diagonal C J) R A x F t v)).
  intro j; symmetry; exact (Hv j).
Qed.

Program Definition radj_cone (F : J ⟶ C) : Cone F := {|
  vertex_obj := R F;
  coneFrom := fst (Cone_Natural_Transform F (R F)) (radj_counit F)
|}.

Program Definition radj_Limit (F : J ⟶ C) : Limit F := {|
  limit_cone := radj_cone F
|}.
Next Obligation.
  unshelve econstructor.
  - exact (radj_transpose
             (snd (Cone_Natural_Transform F (vertex_obj[N]))
                  (@coneFrom J C F N))).
  - intro j; apply radj_transpose_commutes.
  - intros v Hv; apply radj_transpose_unique; exact Hv.
Qed.

Definition Diagonal_right_adjoint_HasLimits : HasLimitsOfShape J C :=
  radj_Limit.

End RightAdjointGivesLimits.

Section LeftAdjointGivesColimits.

Context {J C : Category}.
Context {K : [J, C] ⟶ C}.
Context (A : K ⊣ @Diagonal C J).

Definition ladj_unit (F : J ⟶ C) : F ⟹ Δ[J](K F) :=
  @unit C ([J, C]) K (@Diagonal C J) A F.

Definition ladj_transpose {F : J ⟶ C} {y : C} (t : F ⟹ Δ[J](y)) :
  K F ~{C}~> y := from (@adj C ([J, C]) K (@Diagonal C J) A F y) t.

Lemma ladj_transpose_commutes {F : J ⟶ C} {y : C}
  (t : F ⟹ Δ[J](y)) (j : J) :
  ladj_transpose t ∘ transform[ladj_unit F] j ≈ transform[t] j.
Proof.
  pose proof (@to_adj_unit C ([J, C]) K (@Diagonal C J) A F y
                (ladj_transpose t)) as H1.
  pose proof (@from_adj_comp_law C ([J, C]) K (@Diagonal C J) A F y t) as H2.
  rewrite <- (H1 j); exact (H2 j).
Qed.

Lemma ladj_transpose_unique {F : J ⟶ C} {y : C}
  (t : F ⟹ Δ[J](y)) (v : K F ~{C}~> y) :
  (∀ j : J, v ∘ transform[ladj_unit F] j ≈ transform[t] j) →
  ladj_transpose t ≈ v.
Proof.
  intro Hv.
  pose proof (@to_adj_unit C ([J, C]) K (@Diagonal C J) A F y v) as H1.
  assert (Ht : to (@adj C ([J, C]) K (@Diagonal C J) A F y) v ≈ t).
  { intro j; rewrite (H1 j); exact (Hv j). }
  transitivity (from (@adj C ([J, C]) K (@Diagonal C J) A F y)
                     (to (@adj C ([J, C]) K (@Diagonal C J) A F y) v)).
  - apply from_adj_respects; symmetry; exact Ht.
  - apply to_adj_comp_law.
Qed.

Program Definition ladj_Colimit (F : J ⟶ C) : Colimit F := {|
  limit_cone := cocone_of_transform (ladj_unit F)
|}.
Next Obligation.
  unshelve econstructor.
  - exact (ladj_transpose (transform_of_cocone N)).
  - intro j; apply ladj_transpose_commutes.
  - intros v Hv; apply ladj_transpose_unique; exact Hv.
Qed.

Definition Diagonal_left_adjoint_HasColimits : HasColimitsOfShape J C :=
  ladj_Colimit.

End LeftAdjointGivesColimits.

Theorem limits_iff_diagonal_right_adjoint (J C : Category) :
  HasLimitsOfShape J C ↔ { R : [J, C] ⟶ C & @Diagonal C J ⊣ R }.
Proof.
  split.
  - intro L; exists (LimitFunctor L); exact (Diagonal_Limit_Adjunction L).
  - intros [R A]; exact (Diagonal_right_adjoint_HasLimits A).
Defined.

Theorem colimits_iff_diagonal_left_adjoint (J C : Category) :
  HasColimitsOfShape J C ↔ { K : [J, C] ⟶ C & K ⊣ @Diagonal C J }.
Proof.
  split.
  - intro L; exists (ColimitFunctor L); exact (Colimit_Diagonal_Adjunction L).
  - intros [K A]; exact (Diagonal_left_adjoint_HasColimits A).
Defined.

(** * Awodey §9.3 / Riehl §4.6 exercise i: the degenerate rows  / * Awodey §9.3 / Riehl §4.6 练习 i：退化行*)

Lemma one_arrow_eq@{u} (a b : poly_unit@{u}) : a = b.
Proof. now destruct a, b. Qed.

Section EraseAdjunctions.

(*
The universe binders are declared explicitly: written against an
   unannotated [Context {C : Category}] the two definitions below minimize
   C's hom and proof universes to [Set] (measured), which the statement
   itself does not require. 

--------
宇宙绑定器被显式声明：针对
 未注释的 [Context {C : Category}] 下面的两个定义最小化
 C 的 hom 和证明宇宙到 [Set]（测量），其中声明
 本身并不需要。 
*)
Universes eo eh ep.
Context {C : Category@{eo eh ep}}.

Program Definition Terminal_Erase_Adjunction (T : @Terminal C) :
  Erase C ⊣ @Diagonal C _1 (@terminal_obj C T) := {|
  adj := fun x y =>
    {| to   := {| morphism := fun _ => @one C T x |}
     ; from := {| morphism := fun _ => ttt |} |}
|}.
Next Obligation. first [ apply one_unique | apply one_arrow_eq ]. Qed.
Next Obligation. first [ apply one_unique | apply one_arrow_eq ]. Qed.
Next Obligation. first [ apply one_unique | apply one_arrow_eq ]. Qed.

Program Definition Initial_Erase_Adjunction (I : @Initial C) :
  @Diagonal C _1 (@initial_obj C I) ⊣ Erase C := {|
  adj := fun x y =>
    {| to   := {| morphism := fun _ => ttt |}
     ; from := {| morphism := fun _ => @zero C I y |} |}
|}.
Next Obligation. first [ apply zero_unique | apply one_arrow_eq ]. Qed.
Next Obligation. first [ apply zero_unique | apply one_arrow_eq ]. Qed.
Next Obligation. first [ apply zero_unique | apply one_arrow_eq ]. Qed.

End EraseAdjunctions.

Program Definition Erase_right_adjoint_Terminal {C : Category} {R : _1 ⟶ C}
  (A : Erase C ⊣ R) : @Terminal C := {|
  terminal_obj := R ttt;
  one := fun x => to (@adj _1 C (Erase C) R A x ttt) ttt
|}.
Next Obligation.
  rewrite <- (@from_adj_comp_law _1 C (Erase C) R A x ttt f).
  rewrite <- (@from_adj_comp_law _1 C (Erase C) R A x ttt g).
  apply to_adj_respects, one_arrow_eq.
Qed.

Program Definition Erase_left_adjoint_Initial {C : Category} {K : _1 ⟶ C}
  (A : K ⊣ Erase C) : @Initial C := {|
  terminal_obj := K ttt;
  one := fun x => from (@adj C _1 K (Erase C) A ttt x) ttt
|}.
Next Obligation.
  rewrite <- (@to_adj_comp_law C _1 K (Erase C) A ttt x f).
  rewrite <- (@to_adj_comp_law C _1 K (Erase C) A ttt x g).
  apply from_adj_respects, one_arrow_eq.
Qed.

Theorem Erase_right_adjoint_iff_Terminal (C : Category) :
  @Terminal C ↔ { R : _1 ⟶ C & Erase C ⊣ R }.
Proof.
  split.
  - intro T.
    exists (@Diagonal C _1 (@terminal_obj C T)).
    exact (Terminal_Erase_Adjunction T).
  - intros [R A]; exact (Erase_right_adjoint_Terminal A).
Defined.

Theorem Erase_left_adjoint_iff_Initial (C : Category) :
  @Initial C ↔ { K : _1 ⟶ C & K ⊣ Erase C }.
Proof.
  split.
  - intro I.
    exists (@Diagonal C _1 (@initial_obj C I)).
    exact (Initial_Erase_Adjunction I).
  - intros [K A]; exact (Erase_left_adjoint_Initial A).
Defined.

(** The adjoint's value at the unique object IS the (co)terminal object.  / 唯一对象处的伴随值是（共）终端对象。*)

Example Erase_right_adjoint_value {C : Category} {R : _1 ⟶ C}
  (A : Erase C ⊣ R) :
  @terminal_obj C (Erase_right_adjoint_Terminal A) = R ttt := eq_refl.

Example Erase_left_adjoint_value {C : Category} {K : _1 ⟶ C}
  (A : K ⊣ Erase C) :
  @initial_obj C (Erase_left_adjoint_Initial A) = K ttt := eq_refl.

Example Terminal_Erase_value {C : Category} (T : @Terminal C) :
  fobj[@Diagonal C _1 (@terminal_obj C T)] ttt = @terminal_obj C T := eq_refl.

Example Initial_Erase_value {C : Category} (I : @Initial C) :
  fobj[@Diagonal C _1 (@initial_obj C I)] ttt = @initial_obj C I := eq_refl.

(** The empty shape: limits of shape 0 are exactly terminal objects.  / 空形状：形状 0 的界限正是终端对象。*)

Theorem HasLimitsOfShape_0_iff_Terminal (C : Category) :
  HasLimitsOfShape 0 C ↔ @Terminal C.
Proof.
  split.
  - intro H; exact (fst (Terminal_Limit C (From_0 C)) (H (From_0 C))).
  - intros T F; exact (snd (Terminal_Limit C F) T).
Defined.

Corollary Terminal_iff_Diagonal_0_right_adjoint (C : Category) :
  @Terminal C ↔ { R : [0, C] ⟶ C & @Diagonal C 0 ⊣ R }.
Proof.
  split.
  - intro T.
    exact (fst (limits_iff_diagonal_right_adjoint 0 C)
               (snd (HasLimitsOfShape_0_iff_Terminal C) T)).
  - intro H.
    exact (fst (HasLimitsOfShape_0_iff_Terminal C)
               (snd (limits_iff_diagonal_right_adjoint 0 C) H)).
Defined.

(** * Comparison with the right Kan extension along Erase J  / * 与沿 Erase J 的右 Kan 扩展进行比较*)

Section KanComparison.

Context {J C : Category}.

(**
The diagonal is the restriction along [Erase J] of the constant
    functor [1 ⟶ C], on both actions and on the nose. 

--------
对角线是常数沿 [Erase J] 的限制
 函子 [1 ⟶ C]，在动作和鼻子上。 
*)

Example diagonal_is_induced_obj (c : C) (j : J) :
  fobj[Δ[J](c)] j
    = fobj[fobj[@Induced J _1 (Erase J) C] (@Diagonal C _1 c)] j := eq_refl.

Example diagonal_is_induced_map (c : C) (x y : J) (f : x ~{J}~> y) :
  fmap[Δ[J](c)] f
    = fmap[fobj[@Induced J _1 (Erase J) C] (@Diagonal C _1 c)] f := eq_refl.

Program Definition diagonal_induced_iso (c : C) :
  @Isomorphism ([J, C]) (Δ[J](c))
    (fobj[@Induced J _1 (Erase J) C] (@Diagonal C _1 c)) := {|
  to   := {| transform := fun _ => id |};
  from := {| transform := fun _ => id |}
|}.

Context (L : HasLimitsOfShape J C).
Context `{RK : @RightKan J _1 (Erase J) C}.

Corollary lim_Ran_iso (F : J ⟶ C) : lim_obj L F ≅ Ran (Erase J) F ttt.
Proof. exact (@Kan_Limit J C F (L F) RK). Qed.

End KanComparison.

(** * Non-vacuity: the shape 1, and the sandwich at Sets  / * 非空：形状 1，以及 Sets 中的三明治*)

Section OneShapeLimit.

Context {C : Category}.
Context (L : HasLimitsOfShape _1 C).

Program Definition lim_one_acone (F : _1 ⟶ C) : ACone (F ttt) F := {|
  vertex_map := fun x => match x as x' return (F ttt ~{C}~> F x') with
                         | ttt => id
                         end
|}.
Next Obligation.
  destruct x, y, f.
  pose proof (@fmap_id _1 C F ttt) as HI; simpl in HI.
  now rewrite HI, id_left.
Qed.

Definition lim_one_cone (F : _1 ⟶ C) : Cone F :=
  {| vertex_obj := F ttt; coneFrom := lim_one_acone F |}.

Program Definition lim_one_iso (F : _1 ⟶ C) : lim_obj L F ≅ F ttt := {|
  to   := lim_leg L F ttt;
  from := lim_med L (lim_one_cone F)
|}.
Next Obligation. exact (lim_med_commutes L (lim_one_cone F) ttt). Qed.
Next Obligation.
  apply (lim_med_eq L (@limit_cone _1 C F (L F))); intro j; destruct j.
  - rewrite comp_assoc, (lim_med_commutes L (lim_one_cone F) ttt).
    now rewrite id_left.
  - now rewrite id_right.
Qed.

End OneShapeLimit.

Definition Sets_HasLimitsOfShape (J : Category) : HasLimitsOfShape J Sets :=
  Complete_HasLimitsOfShape Sets_Complete J.

Definition Sets_HasColimitsOfShape (J : Category) :
  HasColimitsOfShape J Sets :=
  Cocomplete_HasColimitsOfShape Sets_Cocomplete J.

Definition Sets_Diagonal_Limit_Adjunction (J : Category) :
  @Diagonal Sets J ⊣ LimitFunctor (Sets_HasLimitsOfShape J) :=
  Diagonal_Limit_Adjunction (Sets_HasLimitsOfShape J).

Definition Sets_Colimit_Diagonal_Adjunction (J : Category) :
  ColimitFunctor (Sets_HasColimitsOfShape J) ⊣ @Diagonal Sets J :=
  Colimit_Diagonal_Adjunction (Sets_HasColimitsOfShape J).

Definition DiagBoolSet : Sets :=
  {| carrier := bool; is_setoid := eq_Setoid bool |}.

Definition SetsBoolDiagram : _1 ⟶ Sets := @Diagonal Sets _1 DiagBoolSet.

Definition sets_bool_lim_iso :
  lim_obj (Sets_HasLimitsOfShape _1) SetsBoolDiagram ≅ DiagBoolSet :=
  lim_one_iso (Sets_HasLimitsOfShape _1) SetsBoolDiagram.

Lemma sets_bool_lim_two_elements :
  { a : carrier (lim_obj (Sets_HasLimitsOfShape _1) SetsBoolDiagram)
  & { b : carrier (lim_obj (Sets_HasLimitsOfShape _1) SetsBoolDiagram)
    & a ≈ b → False } }.
Proof.
  exists (from sets_bool_lim_iso true).
  exists (from sets_bool_lim_iso false).
  intro H.
  pose proof (iso_to_from sets_bool_lim_iso true) as H1.
  pose proof (iso_to_from sets_bool_lim_iso false) as H2.
  simpl in H1, H2.
  assert (Hb : (true : carrier DiagBoolSet) ≈ false).
  { transitivity (to sets_bool_lim_iso (from sets_bool_lim_iso true)).
    - symmetry; exact H1.
    - transitivity (to sets_bool_lim_iso (from sets_bool_lim_iso false)).
      + apply (proper_morphism (to sets_bool_lim_iso)); exact H.
      + exact H2. }
  discriminate Hb.
Qed.

(** ** The diagonal preserves limits  / ** 对角线保留限制*)

(* Δ[J] : C ⟶ [J, C] sends a limit cone over G : I ⟶ C to a limit cone
   over Δ[J] ◯ G, for every shape I and with no hypothesis on C.  The proof
   is the observation that limits in the functor category are computed one
   component at a time: evaluating a cone M over Δ[J] ◯ G at j ∈ J gives
   an ordinary cone over G ([diag_eval_cone]); its mediator into the given
   limit is the j-th component of the mediating transformation
   ([diag_med]), whose naturality square is closed by uniqueness of the
   mediator at the source component.

   This is the preservation hypothesis the adjoint functor theorem asks of
   the diagonal.  With it, Adjunction/GAFT.v's [GAFT] applied to Δ[J]
   produces a left adjoint of the diagonal, and
   [Diagonal_left_adjoint_HasColimits] above reads the J-shaped colimits
   off that adjunction: the route by which Instance/Grp/Colimit.v,
   Instance/Rng/Colimit.v and Instance/Variety/Colimit.v build colimits
   of algebras (Mac Lane §V.7, Exercises 1, 2 and 4).

   The explicit binders on [Diagonal_continuous] matter.  Written bare,
   minimization collapses J to [Category@{u u u}], one level for its
   objects, homs and C's homs; with the binders J's object universe stays
   free below the shared hom level ([jo <= h]), which is what the colimit
   applications need.  J's hom universe cannot be separated from C's:
   [Fun] identifies them. *)

Section DiagonalContinuous.

Context {C J : Category}.
Context {I : Category} (G : I ⟶ C) (N : Cone G) (HN : IsLimitCone N).
Context (M : Cone (@Diagonal C J ◯ G)).

Program Definition diag_eval_cone (j : J) : Cone G := {|
  vertex_obj := fobj[vertex_obj[M]] j;
  coneFrom := {| vertex_map := fun x => transform[cone_leg M x] j |}
|}.
Next Obligation.
  pose proof (@cone_coherence _ _ _ _ (@coneFrom _ _ _ M) x y f j) as Hc.
  simpl in Hc; rewrite <- Hc; reflexivity.
Qed.

Program Definition diag_med :
  vertex_obj[M] ~{[J, C]}~> fobj[@Diagonal C J] (vertex_obj[N]) := {|
  transform := fun j => unique_obj (HN (diag_eval_cone j))
|}.
Next Obligation.
  rewrite id_left.
  apply (uniqueness (HN (diag_eval_cone x))).
  intro i; simpl.
  rewrite comp_assoc.
  rewrite (unique_property (HN (diag_eval_cone y)) i); simpl.
  pose proof (naturality[cone_leg M i] x y f) as Hn; simpl in Hn.
  rewrite <- Hn; apply id_left.
Qed.
Next Obligation.
  rewrite id_left.
  symmetry.
  apply (uniqueness (HN (diag_eval_cone x))).
  intro i; simpl.
  rewrite comp_assoc.
  rewrite (unique_property (HN (diag_eval_cone y)) i); simpl.
  pose proof (naturality[cone_leg M i] x y f) as Hn; simpl in Hn.
  rewrite <- Hn; apply id_left.
Qed.

Lemma diag_med_commutes (i : I) :
  fmap[@Diagonal C J] (cone_leg N i) ∘ diag_med ≈ cone_leg M i.
Proof.
  intro j; simpl.
  exact (unique_property (HN (diag_eval_cone j)) i).
Qed.

Lemma diag_med_unique
  (v : vertex_obj[M] ~{[J, C]}~> fobj[@Diagonal C J] (vertex_obj[N])) :
  (∀ i : I, fmap[@Diagonal C J] (cone_leg N i) ∘ v ≈ cone_leg M i) →
  diag_med ≈ v.
Proof.
  intros Hv j; simpl.
  apply (uniqueness (HN (diag_eval_cone j))).
  intro i; exact (Hv i j).
Qed.

End DiagonalContinuous.

Definition Diagonal_continuous@{jo h o +}
  {C : Category@{o h h}} {J : Category@{jo h h}} :
  ContinuousFunctor (@Diagonal C J).
Proof.
  intros I G N HN M.
  unshelve refine {| unique_obj := diag_med G N HN M |}.
  - exact (diag_med_commutes G N HN M).
  - exact (diag_med_unique G N HN M).
Defined.
