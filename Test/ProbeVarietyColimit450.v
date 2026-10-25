(**
* Probe for the setoid variety's colimits by the adjoint functor
      theorem (issue #450)

    Pins the measured boundaries of Instance/Variety/Colimit.v (Mac Lane
    §V.7 Exercise 4 and §IX.1 Exercise 2, on [SVariety E]) and of
    Instance/Variety/Limit.v (completeness, and the forgetful functor's
    continuity), together with the refusal Instance/Variety/Spanning.v's
    header quotes for its [variety_solution_set].  Groups, rings, Riehl's
    presentation and disjointness are Test/ProbeAlgColimit450.v's.

    THE IMPORT LIST is Instance/Variety/Colimit.v's thirty lines verbatim
    and in order, then the three lines Instance/Variety/Limit.v adds, the
    one Instance/Variety/Free.v adds and the four
    Instance/Variety/Spanning.v adds (measured by comparing their
    [Require] lines), then Instance/Discrete.v and Instance/Two/Discrete.v
    for the shapes, then the two target modules not already listed.

    NOT DUPLICATED HERE.  That [tree_equiv] is [Prop]-valued since #450,
    and so eliminates only into [Prop], is pinned by
    Test/ProbeVarietyFree441.v's n4 ([p450_tree_equiv_elim_Type], an
    induction into a [Type]-sorted goal, beside the same script into a
    [Prop]-sorted goal as its control); that probe was extended when
    Instance/Variety/Free.v changed, and a second copy here would guard
    nothing more.

    DISCIPLINE, as in Test/ProbeAlgColimit450.v.  The instrument was
    checked both ways: the refutation of an absent name is refused for
    that reason, and wrapping the control [p450v_colim_bool] in a
    refutation, in a copy of this file, stops the build with the report
    that the guarded command had been accepted.  Every negative sits
    beside a positive control, every negative other than the name-absence
    instrument is an [Example] or a [Definition] (the instrument is a
    [Check] of a name that does not exist, which no evar can supply), and
    each was stripped of its refutation keyword in a copy of this WHOLE
    file, one at a time, and classified by its error.
    Quotations hold under this file's import list; a universe the stripped
    copy names after itself and a serial number is written <anon>.  The
    quotations are Rocq 9.1's.  Under Coq 8.20.1 every stripped copy is
    refused with the same kind, and the file compiles on Coq 8.19.2 and
    8.20.1.

    KINDS.  Six refutations, counted as the lines that open with the
    refutation keyword: NAME-ABSENCE (the instrument), CONVERSION (N1, N2)
    and UNIVERSE (N3, N4, N5).

    AN INSTRUMENT TRAP, MET AND AVOIDED.  N3 was first written inside the
    [Section] whose [Context] declares [E].  Stripped there, it was refused
    with "universe inconsistency: Cannot enforce Set = <anon>" and no
    "because" clause: [E]'s carrier universe was a section universe, and
    the refusal came from its rigidity, which refuses [Set] whatever the
    bounds.  Such a refutation would stand even with no [Set < carrier]
    anywhere.  N3, N4 and N5 are therefore top-level definitions with their
    own binders, and their stripped errors name the bound.

    N1 (CONVERSION).  The initial algebra the theorem produces is a
    different object, its carrier not the closed terms [UA.Tree S False]
    by [eq_refl] ([GAFT] is moreover [Qed], so the carrier has no readback
    at all):
      The term "eq_refl" has type "soa_obj (projT1 0) = soa_obj (projT1 0)"
      while it is expected to have type "soa_obj (projT1 0) = UA.Tree S
      False" (cannot unify "carrier (soa_obj (projT1 0))" and "UA.Tree S
      False").
    ([0] is the notation for [initial_obj].)  The controls are the same
    equation at [SVariety_Initial], where it IS [eq_refl] -- the free
    algebra on the empty set, whose carrier is the closed terms, and which
    IS [Free_Variety E] at [Sets]'s initial object by [eq_refl] -- and
    [SVariety_Initial_agrees], the isomorphism between the two.

    N2 (CONVERSION).  Mac Lane's own route to the free algebra,
    [Free_Variety_via_GAFT], agrees with Instance/Variety/Free.v's
    [Free_Variety_Functor] up to `≈` and no further:
      (cannot unify "projT1 (Free_Variety_via_GAFT E)" and
      "Free_Variety_Functor E").
    The control is [Free_Variety_via_GAFT_agrees] at exactly that
    statement as `≈`.

    N3 (UNIVERSE).  [SVariety_colim_via_GAFT E Two_Discrete] is refused:
      The term "Two_Discrete" has type "Category@{<anon> Set Set}" while it
      is expected to have type "Category@{<anon> <anon> <anon>}" (universe
      inconsistency: Cannot enforce Set = <anon> because Set < <anon>).
    The controls are [DiscreteCat bool] and [DiscreteCat (Fin.t 2)].
    This is the shape discipline the target's header states -- a shape's
    homs AT the carrier universe -- and the reason its coproduct comes
    through Structure/Limit/Finite.v's bridges.

    N4 (UNIVERSE).  At J : Category@{Set Set Set}, the control
    [Diagonal_SVariety_solution_set E D] ELABORATES, and [About] reads its
    D at [SVariety] with the carrier and hom universes at [Set] and the
    index at a universe above [Set]; [SVariety_colim_via_GAFT E J] is
    refused:
      The term "J" has type "Category@{Set Set Set}" while it is expected
      to have type "Category@{<anon> <anon> <anon>}" (universe
      inconsistency: Cannot enforce Set = <anon> because Set < <anon>).
    The second control, [p450v_gaft_partial_at_set], applies [GAFT] at
    the same diagonal to every argument BUT the solution set
    ([SVariety_Complete E] and [Continuous_PreservesImageLimit
    Diagonal_continuous]), and it is accepted too.  So the variety's
    [Set < carrier] is imposed where [GAFT] puts the solution set's index
    at the carrier universe, not by the solution set itself nor by the
    completeness or the continuity; the same attribution holds for groups
    and rings (N4 and N5 of Test/ProbeAlgColimit450.v, with the same two
    controls), and Instance/Variety/Colimit.v's header makes it.
    [soa_prop] is what keeps the kernel index carrier-sized, and the index
    of [Prop]-valued relations sits above [Set]; the bound lands on the
    carrier only once [GAFT] identifies the two.

    N5 (UNIVERSE).  [GAFT] refuses Instance/Variety/Spanning.v's
    [variety_solution_set], whose index is a Σ over the OBJECTS of
    [SVariety E] (Structure/Complete.v's size note, item 3), with the real
    completeness and continuity as its other arguments:
      The term "variety_solution_set E" has type
      "∀ X : obj[Sets@{a b}], SolutionSet@{c b c a} (SVariety_Forget E) X"
      while it is expected to have type
      "∀ d : obj[Sets@{a b}], SolutionSet@{a b d a} (SVariety_Forget E) d"
      (universe inconsistency: Cannot enforce d = a because a < e <= d).
    That is the stripped text with each <anon> renamed to one letter and
    the [SVariety_Forget] instances elided.  The first slot of
    [SolutionSet] is the index and the third the object universe of
    [SVariety E]; the spanning family repeats one universe [c] in both,
    its index being a Σ over objects, while [GAFT] wants the index AT the
    carrier [a] and the object universe at [d], and the carrier sits
    strictly below the object universe ([a < e <= d]).  The shape is the
    one Spanning.v quotes from a scratch file.  The controls: the
    congruence-indexed [SVariety_Forget_solution_set] is accepted by the
    same call, and [variety_solution_set E] itself elaborates.

    CONTROLS WITHOUT A NEGATIVE.  The route, by [eq_refl]:
    [SVariety_colim_via_GAFT E J] IS [GAFT] at the diagonal with
    [SVariety_Complete], [Continuous_PreservesImageLimit
    Diagonal_continuous] and [Diagonal_SVariety_solution_set]; its index IS
    [VCongIdx] and its members ARE the quotients [VQ_alg];
    [SVariety_coequalizers_via_GAFT] (Exercise 4) IS Finite.v's bridge over
    [SVariety_Cocomplete_via_GAFT]; [Free_Variety_via_GAFT] IS [GAFT] at
    the forgetful functor with the congruence index [FCongIdx].  §IX.1
    Exercise 2: the category is never empty ([SVariety_Terminal]); the
    emptiness of the initial algebra is [SVariety_initial_empty_iff] and
    [closed_terms_empty_iff]; "inhabited ⇒ some constant" is
    [dec_closed_term_constant] under decidable arities, and its uniform
    form implies weak excluded middle
    ([closed_term_constant_implies_WLEM]).  The Leibniz boundary is
    [leibniz_coequalizers_iff_quotients].  The non-vacuity constants at
    #440's [CommEq], a presentation built without extensionality, are
    [CommMagma_Cocartesian] and [CommMagma_coequalizers].

--------
* 通过伴随定理（问题 #450）探测集合等价类的余极限

固定 Instance/Variety/Colimit.v（Mac Lane §V.7 练习 4 和 §IX.1 练习 2，在 [SVariety E] 上）和 Instance/Variety/Limit.v（完备性，以及遗忘函子的一致性）的测量边界，以及 Instance/Variety/Spanning.v 拒绝其 [variety_solution_set] 的头部引用。群、环、Riehl 的表示及不相交性属于 Test/ProbeAlgColimit450.v。

导入列表是 Instance/Variety/Colimit.v 的三十行逐字原样且按顺序排列，然后是 Instance/Variety/Limit.v 添加的三行，Instance/Variety/Free.v 添加的一行，以及 Instance/Variety/Spanning.v 添加的四行（通过比较它们的 [Require] 行来衡量），然后是 Instance/Discrete.v 和 Instance/Two/Discrete.v 的形状部分，最后是两个尚未列出的目标模块。

此处未重复。自 #450 起，[tree_equiv] 的值为 [Prop]，因此仅消去为 [Prop]，被 Test/ProbeVarietyFree441.v 的 n4 固定（[p450_tree_equiv_elim_Type]，是对 [Type] 排序目标的归纳，旁边同一脚本对 [Prop] 排序目标作为其控制）；当 Instance/Variety/Free.v 发生更改时，该探针已被扩展，此处的第二份副本不会再额外保护任何内容。

纪律，如在 Test/ProbeAlgColimit450.v 中。该工具被双向检查：由于该原因，拒绝一个不存在名称的反驳，并且在该文件的一个副本中将控制 [p450v_colim_bool] 包裹在反驳中，会导致构建停止，并报告受保护的命令已被接受。每个否定都位于一个正控制旁边，除了名称缺失工具外的每个否定都是 [Example] 或 [Definition]（该工具是一个不存在名称的 [Check]，没有任何 evar 能提供），并且每个工具在该 WHOLE 文件的副本中都逐一去掉了它的反驳关键字，并按其错误进行了分类。引用在该文件的导入列表下成立；被去掉的副本命名为它自己和一个序列号的宇宙写作 <anon>。这些引用是 Rocq 9.1 的。在 Coq 8.20.1 下，每个被去掉的副本都会以相同的类型被拒绝，而该文件可以在 Coq 8.19.2 和 8.20.1 上编译。

种类。六种反驳，被计算为以反驳关键词开头的行：NAME-ABSENCE（工具）、CONVERSION（N1，N2）和UNIVERSE（N3，N4，N5）。

一个仪器陷阱，已遇到并避开。N3 最初写在 [Section] 里面，而 [Context] 声明了 [E]。在那里被剥离后，它被拒绝，并显示“宇宙不一致：无法强制 Set = <匿名>”，而没有“因为”子句：[E] 的载体宇宙是一个区段宇宙，这种拒绝来自它的刚性，无论边界如何，它都会拒绝 [Set]。即使在任何地方没有 [Set < carrier]，这种反驳也仍然成立。因此，N3、N4 和 N5 是具有自己绑定器的顶层定义，它们剥离后的错误会指明该绑定。

N1（转换）。定理生成的初代数是一个不同的对象，其承载体不是由 [UA.Tree S False] 通过 [eq_refl] 的闭合项（此外，[GAFT] 是 [Qed]，因此承载体根本没有回读）：
      术语 "eq_refl" 的类型是 "soa_obj (projT1 0) = soa_obj (projT1 0)"
      而期望的类型是 "soa_obj (projT1 0) = UA.Tree S False"（无法统一 "carrier (soa_obj (projT1 0))" 与 "UA.Tree S False"）。
    （[0] 是 [initial_obj] 的表示法。）控制是在 [SVariety_Initial] 的相同方程，其中它是 [eq_refl] —— 空集上的自由代数，其承载体是闭合项，并且由 [eq_refl] 在 [Sets] 的初始对象处是 [Free_Variety E] —— 以及 [SVariety_Initial_agrees]，即两者之间的同构。

N2（转换）。Mac Lane 自身到自由代数的路线，[Free_Variety_via_GAFT]，与 Instance/Variety/Free.v 的 [Free_Variety_Functor] 在 `≈` 之上是一致的，但不能再进一步：
  （无法统一 "projT1 (Free_Variety_via_GAFT E)" 和 "Free_Variety_Functor E"）。
控制正好在该语句处为 `≈`，即 [Free_Variety_via_GAFT_agrees]。

N3（宇宙）。[SVariety_colim_via_GAFT E Two_Discrete] 被拒绝：
      术语 "Two_Discrete" 的类型为 "Category@{<anon> Set Set}"，而期望的类型为 "Category@{<anon> <anon> <anon>}"（宇宙不一致：无法强制 Set = <anon>，因为 Set < <anon>）。
    控制是 [DiscreteCat bool] 和 [DiscreteCat (Fin.t 2)]。
    这是目标头文件声明的形状约束——形状的 hom 在载体宇宙——以及其余积通过 Structure/Limit/Finite.v 的桥接的原因。

N4（宇宙）。在 J：Category@{Set Set Set} 上，控制 [Diagonal_SVariety_solution_set E D] 进行展开，并且 [About] 在 [SVariety] 读取其 D，同时载体和同类宇宙在 [Set]，索引在 [Set] 之上的宇宙；[SVariety_colim_via_GAFT E J] 被拒绝：
      术语“J”的类型是“Category@{Set Set Set}”，而期望的类型是“Category@{<anon> <anon> <anon>}”（宇宙不一致：无法强制 Set = <anon>，因为 Set < <anon>）。第二个控制 [p450v_gaft_partial_at_set] 对相同对角线上的每个参数应用 [GAFT]，但不包括解集（[SVariety_Complete E] 和 [Continuous_PreservesImageLimit Diagonal_continuous]），并且也被接受。
所以这个品种的 [Set < carrier] 是在 [GAFT] 将解集的指标施加到载体宇宙时施加的，而不是由解集本身或由完备性或连续性施加；对于群和环（Test/ProbeAlgColimit450.v 的 N4 和 N5，有同样的两个控制）也是如此，Instance/Variety/Colimit.v 的标题也说明了这一点。[soa_prop] 是保持核指标为载体尺寸的原因，而 [Prop] 值的关系的指标位于 [Set] 之上；一旦 [GAFT] 确定两者，界才落在载体上。

N5 (宇宙). [GAFT] 拒绝 Instance/Variety/Spanning.v 的 [variety_solution_set]，其索引是 [SVariety E]（Structure/Complete.v 的 size 注释，第 3 项）对象的 Σ，总完整性和连续性作为其其他参数：
      术语 "variety_solution_set E" 的类型为
      "∀ X : obj[Sets@{a b}], SolutionSet@{c b c a} (SVariety_Forget E) X"
      而期望的类型为
      "∀ d : obj[Sets@{a b}], SolutionSet@{a b d a} (SVariety_Forget E) d"
      （宇宙不一致：无法强制 d = a 因为 a < e <= d）。这就是剥离文本，每个 <anon> 被重命名为一个字母并且 [SVariety_Forget] 实例已省略。
[SolutionSet] 的第一个槽是索引，第三个槽是 [SVariety E] 的对象宇宙；跨越族在两者中重复了一个宇宙 [c]，其索引是对象的 Σ，而 [GAFT] 想要在载体 [a] 上有索引，在 [d] 上有对象宇宙，并且载体严格位于对象宇宙之下（[a < e <= d]）。形状是 Spanning.v 从一个草稿文件中引用的。控件：同余索引的 [SVariety_Forget_solution_set] 被同一个调用接受，而 [variety_solution_set E] 本身进行展开。

无负控制。该路线，由 [eq_refl]：
    [SVariety_colim_via_GAFT E J] 在 [SVariety_Complete] 的对角线上是 [GAFT]，[Continuous_PreservesImageLimit Diagonal_continuous] 和 [Diagonal_SVariety_solution_set]；它的指数是 [VCongIdx]，成员是商 [VQ_alg]；
    [SVariety_coequalizers_via_GAFT]（练习 4）是 Finite.v 跨越 [SVariety_Cocomplete_via_GAFT] 的桥；[Free_Variety_via_GAFT] 在忘记函子下是 [GAFT]，且同余指数为 [FCongIdx]。§IX.1
    练习 2：该范畴从不为空（[SVariety_Terminal]）；初始代数的空性是 [SVariety_initial_empty_iff] 和 [closed_terms_empty_iff]；“有元 ⇒ 某个常数”在可判定元数下为 [dec_closed_term_constant]，其统一形式蕴含弱排中律 ([closed_term_constant_implies_WLEM])。
    莱布尼茨边界是 [leibniz_coequalizers_iff_quotients]。#440 处非空常数的 [CommEq]，是一个构建在不依赖外延性的演示，它们是 [CommMagma_Cocartesian] 和 [CommMagma_coequalizers]。
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Finite.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Comp.
Require Import Category.Instance.Variety.
Require Import Category.Instance.Variety.Free.
Require Import Category.Instance.Variety.Limit.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Adjunction.SpanningArrow.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Instance.Variety.Spanning.
Require Import Category.Instance.Variety.Colimit.

Generalizable All Variables.

Module UA := Category.Instance.Comp.UniversalAlgebra.

(** ** Instrument: the refutation keyword is live / ** 工具：反驳关键词是实时的 *)

Fail Check probe450_variety_absent_name.

(** ** A. The headlines at their stated types, and the route by [eq_refl] / ** A. 按其指定类型的标题，以及由 [eq_refl] 指定的路线 *)

Section Headlines.

Context {S : UA.OpSignature} (E : UA.EqSignature S).

Check (SVariety_Complete E : @Complete (SVariety E)).
Check (SVariety_Forget_continuous E : ContinuousFunctor (SVariety_Forget E)).
Check (SVariety_colim_via_GAFT E : ∀ J : Category,
  { L : [J, SVariety E] ⟶ SVariety E & L ⊣ @Diagonal (SVariety E) J }).
Check (SVariety_Cocomplete_via_GAFT E : @Cocomplete (SVariety E)).
Check (SVariety_Cocartesian_via_GAFT E : @Cocartesian (SVariety E)).
Check (SVariety_coequalizers_via_GAFT E : HasCoequalizers (SVariety E)).
Check (SVariety_Initial_via_GAFT E : @Initial (SVariety E)).
Check (SVariety_Terminal E : @Terminal (SVariety E)).
Check (SVariety_Initial E : @Initial (SVariety E)).
Check (Free_Variety_via_GAFT E :
  { F : Sets ⟶ SVariety E & F ⊣ SVariety_Forget E }).

Example p450v_colim_is_GAFT (J : Category) :
  SVariety_colim_via_GAFT E J
    = GAFT (@Diagonal (SVariety E) J) (SVariety_Complete E)
           (Continuous_PreservesImageLimit Diagonal_continuous)
           (@Diagonal_SVariety_solution_set S E J) := eq_refl.

(* The index IS the type of cocone congruences on the term algebra. / 该指标是项代数上余圆锥同余的类型。 *)
Example p450v_index (J : Category) (D : J ⟶ SVariety E) :
  sol_index (Diagonal_SVariety_solution_set E D) = VCongIdx E D := eq_refl.

Example p450v_member (J : Category) (D : J ⟶ SVariety E)
  (i : VCongIdx E D) :
  sol_obj (Diagonal_SVariety_solution_set E D) i = VQ_alg E D i := eq_refl.

(*
Exercise 4's coequalizers are Structure/Limit/Finite.v's bridges over
   the AFT colimits.

--------
练习4的共同余子是 Structure/Limit/Finite.v 中跨越 AFT 余极限的桥梁。
*)
Example p450v_coequalizers_bridge :
  SVariety_coequalizers_via_GAFT E
    = HasCoequalizers_of_HasEqualizers_op
        (FinitelyComplete_HasEqualizers
           (FinitelyCocomplete_FinitelyComplete_op
              (Cocomplete_FinitelyCocomplete
                 (SVariety_Cocomplete_via_GAFT E)))) := eq_refl.

(* Mac Lane's own route to the free algebra, at the congruence index. / Mac Lane's own route to the free algebra, at the congruence index. / 麦克莱恩自己到自由代数的路径，在同余指数处。 *)
Example p450v_free_is_GAFT :
  Free_Variety_via_GAFT E
    = GAFT (SVariety_Forget E) (SVariety_Complete E)
           (Continuous_PreservesImageLimit (SVariety_Forget_continuous E))
           (SVariety_Forget_solution_set E) := eq_refl.

Example p450v_free_index (X : Sets) :
  sol_index (SVariety_Forget_solution_set E X) = FCongIdx E X := eq_refl.

(** ** N1 (CONVERSION): the AFT initial object's carrier does not reduce / ** N1（转换）：AFT初始对象的承载器不会减少 *)

(* CONTROL: the initial algebra IS the free algebra on the empty set... / 控制：初始代数是空集上的自由代数… *)
Example p450v_initial_is_free :
  @initial_obj (SVariety E) (SVariety_Initial E)
    = Free_Variety E (@initial_obj Sets _) := eq_refl.

(* CONTROL: ...and its carrier IS the closed terms. / 控制：……而它的载体就是封闭项。 *)
Example p450v_initial_carrier :
  carrier (soa_obj (`1 (@initial_obj (SVariety E) (SVariety_Initial E))))
    = UA.Tree S False := eq_refl.

(* CONTROL: the two initial objects agree, as data. / 控制：两个初始对象作为数据是一致的。 *)
Check (SVariety_Initial_agrees E :
  @initial_obj (SVariety E) (SVariety_Initial E)
    ≅ @initial_obj (SVariety E) (SVariety_Initial_via_GAFT E)).

Fail Example p450v_n1_aft_initial_carrier :
  carrier (soa_obj (`1 (@initial_obj (SVariety E)
                                     (SVariety_Initial_via_GAFT E))))
    = UA.Tree S False := eq_refl.

(** ** N2 (CONVERSION): the free algebra from [GAFT] is `≈`, no more / ** N2（转换）：来自 [GAFT] 的自由代数是 `≈`，仅此而已 *)

(* CONTROL: the agreement that holds. / 控制：有效的协议。 *)
Check (Free_Variety_via_GAFT_agrees E :
  projT1 (Free_Variety_via_GAFT E) ≈ Free_Variety_Functor E).

Fail Example p450v_n2_aft_free_is_free :
  projT1 (Free_Variety_via_GAFT E) = Free_Variety_Functor E := eq_refl.

(** ** IX.1 Exercise 2: emptiness, and the category is never empty / ** IX.1 练习 2：空性，并且类别从不为空 *)

Check (SVariety_initial_empty_iff E :
  (carrier (soa_obj (`1 (@initial_obj (SVariety E) (SVariety_Initial E))))
     → False) ↔
  ({ o : UA.operation S & UA.arity o → False } → False)).
Check (closed_terms_empty_iff S :
  (UA.Tree S False → False) ↔
  (∀ o : UA.operation S, (UA.arity o → False) → False)).
Check (@dec_closed_term_constant S :
  (∀ o : UA.operation S, (UA.arity o → False) + UA.arity o) →
  UA.Tree S False → { o : UA.operation S & UA.arity o → False }).

End Headlines.

Check (closed_term_constant_implies_WLEM :
  (∀ S : UA.OpSignature,
     UA.Tree S False → { o : UA.operation S & UA.arity o → False }) →
  ∀ P : Prop, (P → False) + ((P → False) → False)).
Check (leibniz_coequalizers_iff_quotients :
  HasCoequalizers (Variety NoEq) ↔ QuotElim).

(* Non-vacuity at a presentation built without extensionality. / 在没有外延性的构造展示中的非空性。 *)
Check (CommMagma_Cocartesian : @Cocartesian (SVariety CommEq)).
Check (CommMagma_coequalizers : HasCoequalizers (SVariety CommEq)).

(**
** N3 (UNIVERSE): [Two_Discrete] is refused as a shape

    Stated at the top level with its own binders, not in the section
    above: there [E]'s carrier universe would be a section universe, and
    the refusal would stop at that rigidity, before the [Set < carrier]
    bound it is meant to exercise.

--------
** N3（宇宙）：[Two_Discrete] 被拒绝作为一种形状

    在顶层使用它自己的绑定器声明，而不是在上面的部分中：在那里 [E] 的承载宇宙将是一个部分宇宙，而拒绝将停在该刚性处，在它要施加约束的 [Set < carrier] 之前。
*)

(* CONTROLS: discrete two-object shapes whose homs are free. / 控制：离散的双物体形状，其同类项是自由的。 *)
Definition p450v_colim_bool {S : UA.OpSignature} (E : UA.EqSignature S) :=
  SVariety_colim_via_GAFT E (DiscreteCat bool).
Definition p450v_colim_fin2 {S : UA.OpSignature} (E : UA.EqSignature S) :=
  SVariety_colim_via_GAFT E (DiscreteCat (Fin.t 2)).

Fail Definition p450v_n3_two_discrete {S : UA.OpSignature}
  (E : UA.EqSignature S) := SVariety_colim_via_GAFT E Two_Discrete.

(**
** N4 (UNIVERSE): at a [Set] carrier the solution set elaborates and
    [GAFT] does not

--------
** N4（宇宙）：在 [Set] 运载工具上，解集会展开，而 [GAFT] 不会
*)

(*
CONTROL: the diagonal solution set with the shape's homs, and hence the
   algebras' carrier, at [Set].

--------
控制：在 [Set] 处，带有形状同态的对角解集，因此也是代数的载体。
*)
Definition p450v_sols_at_set {S : UA.OpSignature} (E : UA.EqSignature S)
  (J : Category@{Set Set Set}) (D : J ⟶ SVariety E) :=
  Diagonal_SVariety_solution_set E D.

(*
CONTROL: [GAFT] at the same diagonal with every argument but the
   solution set, so that neither completeness nor continuity is what a
   [Set] carrier refuses.

--------
控制：[GAFT] 与除了解集之外的每个参数都在同一对角线上，因此无论是完整性还是连续性，都不是 [Set] 承载者所拒绝的。
*)
Definition p450v_gaft_partial_at_set {S : UA.OpSignature}
  (E : UA.EqSignature S) (J : Category@{Set Set Set}) :=
  GAFT (@Diagonal (SVariety E) J) (SVariety_Complete E)
       (Continuous_PreservesImageLimit Diagonal_continuous).

Fail Definition p450v_n4_colim_at_set {S : UA.OpSignature}
  (E : UA.EqSignature S) (J : Category@{Set Set Set}) :=
  SVariety_colim_via_GAFT E J.

(** ** N5 (UNIVERSE): [GAFT] refuses the spanning solution set / ** N5（宇宙）：[GAFT] 拒绝跨接解集 *)

(* CONTROL: the same call at the congruence-indexed family. / 控制：在一致性索引家庭上的同一次呼叫。 *)
Definition p450v_gaft_congruences {S : UA.OpSignature}
  (E : UA.EqSignature S) :=
  GAFT (SVariety_Forget E) (SVariety_Complete E)
       (Continuous_PreservesImageLimit (SVariety_Forget_continuous E))
       (SVariety_Forget_solution_set E).

(* CONTROL: the spanning family itself elaborates. / 控制：跨越家庭本身进行详细说明。 *)
Definition p450v_spanning {S : UA.OpSignature} (E : UA.EqSignature S) :=
  variety_solution_set E.

Fail Definition p450v_n5_gaft_spanning {S : UA.OpSignature}
  (E : UA.EqSignature S) :=
  GAFT (SVariety_Forget E) (SVariety_Complete E)
       (Continuous_PreservesImageLimit (SVariety_Forget_continuous E))
       (variety_solution_set E).

(** ** Guard block / ** 防守格挡 *)

Check @SVGen.
Check @IsVCong.
Check @VCongIdx.
Check @VQ_alg.
Check @vq_leg.
Check @vq_arr.
Check @vker.
Check @vker_cong.
Check @vker_idx.
Check @vker_med.
Check @Diagonal_SVariety_solution_set.
Check @IsFCong.
Check @FCongIdx.
Check @FQ_alg.
Check @fker_med.
Check @SVariety_Forget_solution_set.
Check @SVariety_Complete.
Check @SVariety_Forget_continuous.
Check @svariety_complete_carrier.
Check @WLEM_sig.
Check @WLEM_term.
Check @NoOp.
Check @NoEq.
Check @QuotElim.
Check @leibniz_coequalizers_give_quotients.
Check @quotients_give_leibniz_coequalizers.
Check @soa_prop.
Check @tree_equiv.
Check @variety_solution_set.
Check @Diagonal_continuous.
